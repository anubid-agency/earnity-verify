/**
 * earnity-verify — Cloudflare Worker
 * Phone verification service for Earnity (earnityug.com)
 *
 * Deploy: paste this file into the Cloudflare dashboard editor.
 * Bindings: DB (D1), HASH_SALT, TURNSTILE_SECRET, AT_API_KEY,
 *           FIREBASE_PROJECT_ID, AT_USERNAME, INTERNAL_KEY
 */

const JWKS_URL =
  'https://www.googleapis.com/service_accounts/v1/jwk/securetoken@system.gserviceaccount.com';
const TURNSTILE_URL = 'https://challenges.cloudflare.com/turnstile/v0/siteverify';
const AT_URL = 'https://api.africastalking.com/version1/messaging';
const ALLOWED_HOST = 'earnityug.com';

const OTP_TTL_SECONDS = 300;
const OTP_MAX_ATTEMPTS = 5;
const OTP_RESEND_SECONDS = 60;
const RATE_WINDOW_SECONDS = 86400;
const RATE_PHONE_PER_DAY = 5;
const RATE_USER_PER_DAY = 10;
const RATE_IP_PER_DAY = 20;
const ADD_PHONE_HOLD_SECONDS = 86400;
const RECENT_LOGIN_SECONDS = 300;
const MAX_ACTIVE_PHONES = 2;
const MAX_BODY_BYTES = 4096;
const CLOCK_SKEW_SECONDS = 60;
const JWKS_CACHE_SECONDS = 3600;
const KEY_CACHE_MS = 3600_000;
const MAX_TURNSTILE_TOKEN_LENGTH = 2048;
const MAX_SUB_LENGTH = 128;
const MAX_INTERNAL_USER_ID_LENGTH = 128;

const enc = new TextEncoder();

let jwksMem = { keys: null, expires: 0 };
const keyMem = new Map();
let hmacKeyCache = { salt: null, key: null };

class HttpError extends Error {
  constructor(status, code, extra) {
    super(code);
    this.status = status;
    this.code = code;
    this.extra = extra;
  }
}

/* ------------------------------------------------------------------ */
/* Helpers                                                            */
/* ------------------------------------------------------------------ */

function json(data, status, cors) {
  return new Response(JSON.stringify(data), {
    status,
    headers: {
      'Content-Type': 'application/json; charset=utf-8',
      'Cache-Control': 'no-store',
      'X-Content-Type-Options': 'nosniff',
      ...cors,
    },
  });
}

function corsHeaders(origin) {
  if (!origin) return { Vary: 'Origin' };
  return {
    'Access-Control-Allow-Origin': origin,
    'Access-Control-Allow-Methods': 'GET, POST, OPTIONS',
    'Access-Control-Allow-Headers': 'Authorization, Content-Type',
    'Access-Control-Max-Age': '86400',
    Vary: 'Origin',
  };
}

function isAllowedOrigin(origin) {
  if (!origin) return true;
  try {
    const u = new URL(origin);
    return (
      u.protocol === 'https:' &&
      (u.hostname === ALLOWED_HOST || u.hostname.endsWith('.' + ALLOWED_HOST))
    );
  } catch {
    return false;
  }
}

function isEarnityHostname(hostname) {
  return (
    typeof hostname === 'string' &&
    (hostname === ALLOWED_HOST || hostname.endsWith('.' + ALLOWED_HOST))
  );
}

function assertEnv(env, names) {
  for (const name of names) {
    if (!env[name]) {
      console.error('missing_env', { name });
      throw new HttpError(500, 'server_misconfigured');
    }
  }
}

function retryAfter(timestamp, now, windowSeconds) {
  return Math.max(1, Math.ceil(Number(timestamp) + windowSeconds - now));
}

function maskPhone(phone) {
  return phone.slice(0, 5) + '****' + phone.slice(-4);
}

function normalizePhone(input) {
  if (typeof input !== 'string') return null;
  let s = input.trim().replace(/[\s\-().]/g, '');
  if (s.startsWith('00')) s = '+' + s.slice(2);
  if (/^07\d{8}$/.test(s)) return '+256' + s.slice(1);
  if (/^2567\d{8}$/.test(s)) return '+' + s;
  if (/^\+2567\d{8}$/.test(s)) return s;
  return null;
}

function generateId(prefix) {
  const rand = crypto.getRandomValues(new Uint8Array(8));
  return (
    prefix +
    Date.now().toString(36) +
    Array.from(rand)
      .map((b) => b.toString(16).padStart(2, '0'))
      .join('')
  );
}

function generateOtp() {
  const max = 1_000_000;
  const limit = Math.floor(0x1_0000_0000 / max) * max;
  const buf = new Uint32Array(1);
  let x;
  do {
    crypto.getRandomValues(buf);
    x = buf[0];
  } while (x >= limit);
  return String(x % max).padStart(6, '0');
}

function bufToHex(buf) {
  return Array.from(new Uint8Array(buf))
    .map((b) => b.toString(16).padStart(2, '0'))
    .join('');
}

function b64urlDecode(input) {
  let s = input.replace(/-/g, '+').replace(/_/g, '/');
  while (s.length % 4) s += '=';
  const bin = atob(s);
  const bytes = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
  return bytes;
}

function timingSafeEqual(a, b) {
  const len = Math.max(a.length, b.length);
  let diff = a.length ^ b.length;
  for (let i = 0; i < len; i++) {
    diff |= (a.charCodeAt(i) || 0) ^ (b.charCodeAt(i) || 0);
  }
  return diff === 0;
}

async function readJson(request) {
  const ct = (request.headers.get('content-type') || '').toLowerCase();
  if (ct !== 'application/json' && !ct.startsWith('application/json;')) {
    throw new HttpError(415, 'unsupported_media_type');
  }

  const len = Number(request.headers.get('content-length') || '0');
  if (Number.isFinite(len) && len > MAX_BODY_BYTES) {
    throw new HttpError(413, 'payload_too_large');
  }

  const text = await request.text();
  if (enc.encode(text).length > MAX_BODY_BYTES) {
    throw new HttpError(413, 'payload_too_large');
  }

  let data;
  try {
    data = JSON.parse(text);
  } catch {
    throw new HttpError(400, 'invalid_json');
  }
  if (!data || typeof data !== 'object' || Array.isArray(data)) {
    throw new HttpError(400, 'invalid_json');
  }
  return data;
}

async function hmacHex(env, message) {
  let key = hmacKeyCache.key;
  if (!key || hmacKeyCache.salt !== env.HASH_SALT) {
    key = await crypto.subtle.importKey(
      'raw',
      enc.encode(env.HASH_SALT),
      { name: 'HMAC', hash: 'SHA-256' },
      false,
      ['sign']
    );
    hmacKeyCache = { salt: env.HASH_SALT, key };
  }
  const sig = await crypto.subtle.sign('HMAC', key, enc.encode(message));
  return bufToHex(sig);
}

/* ------------------------------------------------------------------ */
/* Firebase ID token verification                                     */
/* ------------------------------------------------------------------ */

async function getJwks(env, force) {
  const now = Date.now();
  if (!force && jwksMem.keys && jwksMem.expires > now) return jwksMem.keys;

  const res = await fetch(
    JWKS_URL,
    force
      ? { cache: 'no-store', cf: { cacheTtl: 0, cacheEverything: false } }
      : { cf: { cacheTtl: JWKS_CACHE_SECONDS, cacheEverything: true } }
  );

  if (!res.ok) throw new Error('jwks_fetch_failed');
  const data = await res.json();
  if (!Array.isArray(data.keys)) throw new Error('jwks_invalid');

  jwksMem = {
    keys: data.keys,
    expires: now + JWKS_CACHE_SECONDS * 1000,
  };
  return data.keys;
}

async function importJwk(jwk) {
  const cached = keyMem.get(jwk.kid);
  if (cached && cached.expires > Date.now()) return cached.key;

  const key = await crypto.subtle.importKey(
    'jwk',
    jwk,
    { name: 'RSASSA-PKCS1-v1_5', hash: 'SHA-256' },
    false,
    ['verify']
  );
  keyMem.set(jwk.kid, { key, expires: Date.now() + KEY_CACHE_MS });
  return key;
}

async function getKey(kid, env) {
  let keys = await getJwks(env, false);
  let jwk = keys.find((k) => k.kid === kid);

  if (!jwk) {
    keys = await getJwks(env, true);
    jwk = keys.find((k) => k.kid === kid);
  }

  if (!jwk) throw new Error('key_not_found');
  return importJwk(jwk);
}

async function verifyFirebaseToken(token, env, now) {
  const parts = token.split('.');
  if (parts.length !== 3) throw new Error('malformed');

  const [headerPart, payloadPart, sigPart] = parts;

  const header = JSON.parse(new TextDecoder().decode(b64urlDecode(headerPart)));
  if (header.alg !== 'RS256' || typeof header.kid !== 'string') {
    throw new Error('alg');
  }

  const payload = JSON.parse(new TextDecoder().decode(b64urlDecode(payloadPart)));
  const key = await getKey(header.kid, env);

  const data = enc.encode(`${headerPart}.${payloadPart}`);
  const sig = b64urlDecode(sigPart);

  const valid = await crypto.subtle.verify(
    { name: 'RSASSA-PKCS1-v1_5' },
    key,
    sig,
    data
  );
  if (!valid) throw new Error('signature');

  if (typeof payload.exp !== 'number' || !Number.isFinite(payload.exp) || payload.exp <= now) {
    throw new Error('exp');
  }
  if (
    typeof payload.iat !== 'number' ||
    !Number.isFinite(payload.iat) ||
    payload.iat > now + CLOCK_SKEW_SECONDS
  ) {
    throw new Error('iat');
  }
  if (
    typeof payload.auth_time !== 'number' ||
    !Number.isFinite(payload.auth_time) ||
    payload.auth_time > now + CLOCK_SKEW_SECONDS
  ) {
    throw new Error('auth_time');
  }
  if (payload.aud !== env.FIREBASE_PROJECT_ID) throw new Error('aud');
  if (payload.iss !== `https://securetoken.google.com/${env.FIREBASE_PROJECT_ID}`) {
    throw new Error('iss');
  }
  if (
    typeof payload.sub !== 'string' ||
    !payload.sub ||
    payload.sub.length > MAX_SUB_LENGTH
  ) {
    throw new Error('sub');
  }

  return payload;
}

async function requireAuth(request, env, now) {
  const auth = request.headers.get('Authorization');
  if (!auth) throw new HttpError(401, 'unauthorized');

  const match = auth.match(/^Bearer\s+(.+)$/i);
  if (!match) throw new HttpError(401, 'unauthorized');

  let payload;
  try {
    payload = await verifyFirebaseToken(match[1], env, now);
  } catch {
    throw new HttpError(401, 'invalid_token');
  }

  const user = await env.DB.prepare(
    'SELECT id, status FROM users WHERE firebase_uid = ? LIMIT 1'
  )
    .bind(payload.sub)
    .first();

  if (!user) throw new HttpError(404, 'not_registered');
  if (user.status === 'blocked') throw new HttpError(403, 'account_blocked');

  return { user, payload };
}

/* ------------------------------------------------------------------ */
/* Turnstile                                                          */
/* ------------------------------------------------------------------ */

async function verifyTurnstile(env, token, ip) {
  const body = new URLSearchParams();
  body.set('secret', env.TURNSTILE_SECRET);
  body.set('response', token);
  if (ip) body.set('remoteip', ip);

  let res;
  try {
    res = await fetch(TURNSTILE_URL, {
      method: 'POST',
      headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
      body: body.toString(),
    });
  } catch {
    return false;
  }

  if (!res.ok) return false;

  let data;
  try {
    data = await res.json();
  } catch {
    return false;
  }

  if (data.success !== true) return false;
  return isEarnityHostname(data.hostname);
}

/* ------------------------------------------------------------------ */
/* Africa's Talking                                                   */
/* ------------------------------------------------------------------ */

async function sendSms(env, phone, message) {
  const body = new URLSearchParams();
  body.set('username', env.AT_USERNAME);
  body.set('to', phone);
  body.set('message', message);

  const res = await fetch(AT_URL, {
    method: 'POST',
    headers: {
      apiKey: env.AT_API_KEY,
      Accept: 'application/json',
      'Content-Type': 'application/x-www-form-urlencoded',
    },
    body: body.toString(),
  });

  if (!res.ok) {
    console.error('at_http_error', { status: res.status });
    return false;
  }

  let data;
  try {
    data = await res.json();
  } catch {
    return false;
  }

  const recipient = data?.SMSMessageData?.Recipients?.[0];
  const statusCode = Number(recipient?.statusCode);

  if (statusCode === 100 || statusCode === 101) return true;

  console.error('at_status_error', { status_code: statusCode });
  return false;
}

/* ------------------------------------------------------------------ */
/* Audit helper                                                       */
/* ------------------------------------------------------------------ */

function auditStmt(env, id, actorId, action, targetType, targetId, metadata, ipHash, now) {
  return env.DB.prepare(
    `INSERT INTO audit_log
       (id, actor_user_id, action, target_type, target_id, metadata, ip_hash, created_at)
     VALUES (?, ?, ?, ?, ?, ?, ?, ?)`
  ).bind(
    id,
    actorId,
    action,
    targetType,
    targetId,
    JSON.stringify(metadata),
    ipHash,
    now
  );
}

/* ------------------------------------------------------------------ */
/* POST /phone/request-code                                           */
/* ------------------------------------------------------------------ */

async function handleRequestCode(request, env, now, cors) {
  assertEnv(env, [
    'DB',
    'HASH_SALT',
    'TURNSTILE_SECRET',
    'AT_API_KEY',
    'FIREBASE_PROJECT_ID',
    'AT_USERNAME',
  ]);

  const { user, payload } = await requireAuth(request, env, now);
  const body = await readJson(request);

  const purpose = body.purpose;
  if (purpose !== 'verify_phone' && purpose !== 'add_phone') {
    throw new HttpError(400, 'invalid_purpose');
  }

  const phone = normalizePhone(body.phone);
  if (!phone) throw new HttpError(400, 'invalid_phone');

  if (
    typeof body.turnstile_token !== 'string' ||
    body.turnstile_token.length === 0 ||
    body.turnstile_token.length > MAX_TURNSTILE_TOKEN_LENGTH
  ) {
    throw new HttpError(400, 'invalid_turnstile');
  }

  if (purpose === 'add_phone' && now - payload.auth_time > RECENT_LOGIN_SECONDS) {
    throw new HttpError(403, 'recent_login_required');
  }

  const state = await env.DB.prepare(
    `SELECT
       (SELECT COUNT(*) FROM user_phones
         WHERE user_id = ? AND verified_at IS NOT NULL AND removed_at IS NULL) AS verified_count,
       (SELECT COUNT(*) FROM user_phones
         WHERE user_id = ? AND removed_at IS NULL) AS active_count`
  )
    .bind(user.id, user.id)
    .first();

  const verifiedCount = Number(state?.verified_count || 0);
  const activeCount = Number(state?.active_count || 0);

  if (purpose === 'verify_phone' && verifiedCount > 0) {
    throw new HttpError(409, 'already_verified');
  }
  if (purpose === 'add_phone') {
    if (verifiedCount === 0) throw new HttpError(400, 'primary_number_required');
    if (activeCount >= MAX_ACTIVE_PHONES) {
      throw new HttpError(409, 'phone_limit_reached');
    }
  }

  const ip = request.headers.get('CF-Connecting-IP') || '';
  const ipHash = await hmacHex(env, 'ip:' + ip);
  const ua = request.headers.get('User-Agent') || '';
  const uaHash = ua ? await hmacHex(env, 'ua:' + ua) : null;

  const since = now - RATE_WINDOW_SECONDS;

  const rate = await env.DB.prepare(
    `SELECT
       (SELECT COUNT(*) FROM phone_otps
         WHERE phone_e164 = ? AND created_at > ?) AS phone_count,
       (SELECT MIN(created_at) FROM phone_otps
         WHERE phone_e164 = ? AND created_at > ?) AS phone_oldest,
       (SELECT COUNT(*) FROM phone_otps
         WHERE user_id = ? AND created_at > ?) AS user_count,
       (SELECT MIN(created_at) FROM phone_otps
         WHERE user_id = ? AND created_at > ?) AS user_oldest,
       (SELECT COUNT(*) FROM phone_otps
         WHERE ip_hash = ? AND created_at > ?) AS ip_count,
       (SELECT MIN(created_at) FROM phone_otps
         WHERE ip_hash = ? AND created_at > ?) AS ip_oldest,
       (SELECT created_at FROM phone_otps
         WHERE user_id = ? ORDER BY created_at DESC LIMIT 1) AS last_user_created`
  )
    .bind(
      phone,
      since,
      phone,
      since,
      user.id,
      since,
      user.id,
      since,
      ipHash,
      since,
      ipHash,
      since,
      user.id
    )
    .first();

  if (rate?.last_user_created && now - Number(rate.last_user_created) < OTP_RESEND_SECONDS) {
    throw new HttpError(429, 'rate_limited', {
      retry_after: retryAfter(rate.last_user_created, now, OTP_RESEND_SECONDS),
    });
  }

  if (Number(rate?.phone_count || 0) >= RATE_PHONE_PER_DAY) {
    throw new HttpError(429, 'rate_limited', {
      retry_after: retryAfter(rate.phone_oldest, now, RATE_WINDOW_SECONDS),
    });
  }
  if (Number(rate?.user_count || 0) >= RATE_USER_PER_DAY) {
    throw new HttpError(429, 'rate_limited', {
      retry_after: retryAfter(rate.user_oldest, now, RATE_WINDOW_SECONDS),
    });
  }
  if (Number(rate?.ip_count || 0) >= RATE_IP_PER_DAY) {
    throw new HttpError(429, 'rate_limited', {
      retry_after: retryAfter(rate.ip_oldest, now, RATE_WINDOW_SECONDS),
    });
  }

  const turnstileOk = await verifyTurnstile(env, body.turnstile_token, ip);
  if (!turnstileOk) throw new HttpError(403, 'turnstile_failed');

  const existingOwner = await env.DB.prepare(
    `SELECT user_id FROM user_phones
     WHERE phone_e164 = ? AND verified_at IS NOT NULL AND removed_at IS NULL
     LIMIT 1`
  )
    .bind(phone)
    .first();

  if (existingOwner) {
    if (existingOwner.user_id === user.id) {
      throw new HttpError(409, 'phone_already_verified');
    }

    // Do not reveal that another user owns this number.
    const decoyId = generateId('otp_');
    const decoyCode = generateOtp();
    const decoyHash = await hmacHex(env, `otp:${decoyId}:${phone}:${decoyCode}`);
    const auditId = generateId('aud_');

    const meta = { purpose, phone: maskPhone(phone) };
    if (uaHash) meta.ua_hash = uaHash;

    await env.DB.batch([
      env.DB.prepare(
        `UPDATE phone_otps SET used_at = ?
         WHERE user_id = ? AND phone_e164 = ? AND purpose = ? AND used_at IS NULL`
      ).bind(now, user.id, phone, purpose),
      env.DB.prepare(
        `INSERT INTO phone_otps
           (id, user_id, phone_e164, purpose, code_hash, expires_at,
            attempts, max_attempts, used_at, ip_hash, created_at)
         VALUES (?, ?, ?, ?, ?, ?, 0, ?, ?, ?, ?)`
      ).bind(
        decoyId,
        user.id,
        phone,
        purpose,
        decoyHash,
        now + OTP_TTL_SECONDS,
        OTP_MAX_ATTEMPTS,
        now,
        ipHash,
        now
      ),
      auditStmt(
        env,
        auditId,
        user.id,
        'phone_already_owned',
        'phone',
        maskPhone(phone),
        meta,
        ipHash,
        now
      ),
    ]);

    return json(
      { sent: true, expires_in: OTP_TTL_SECONDS, resend_after: OTP_RESEND_SECONDS },
      200,
      cors
    );
  }

  const otpId = generateId('otp_');
  const code = generateOtp();
  const codeHash = await hmacHex(env, `otp:${otpId}:${phone}:${code}`);

  await env.DB.batch([
    env.DB.prepare(
      `UPDATE phone_otps SET used_at = ?
       WHERE user_id = ? AND phone_e164 = ? AND purpose = ? AND used_at IS NULL`
    ).bind(now, user.id, phone, purpose),
    env.DB.prepare(
      `INSERT INTO phone_otps
         (id, user_id, phone_e164, purpose, code_hash, expires_at,
          attempts, max_attempts, used_at, ip_hash, created_at)
       VALUES (?, ?, ?, ?, ?, ?, 0, ?, NULL, ?, ?)`
    ).bind(
      otpId,
      user.id,
      phone,
      purpose,
      codeHash,
      now + OTP_TTL_SECONDS,
      OTP_MAX_ATTEMPTS,
      ipHash,
      now
    ),
  ]);

  const message = `Earnity: your verification code is ${code}. It expires in 5 minutes. Never share it with anyone.`;

  let sent = false;
  try {
    sent = await sendSms(env, phone, message);
  } catch {
    sent = false;
  }

  if (!sent) {
    const meta = { purpose, phone: maskPhone(phone) };
    if (uaHash) meta.ua_hash = uaHash;

    try {
      await env.DB.batch([
        env.DB.prepare(
          'UPDATE phone_otps SET used_at = ? WHERE id = ? AND used_at IS NULL'
        ).bind(now, otpId),
        auditStmt(
          env,
          generateId('aud_'),
          user.id,
          'phone_sms_failed',
          'phone',
          maskPhone(phone),
          meta,
          ipHash,
          now
        ),
      ]);
    } catch {
      // best effort
    }

    throw new HttpError(502, 'sms_failed');
  }

  return json(
    { sent: true, expires_in: OTP_TTL_SECONDS, resend_after: OTP_RESEND_SECONDS },
    200,
    cors
  );
}

/* ------------------------------------------------------------------ */
/* POST /phone/verify                                                 */
/* ------------------------------------------------------------------ */

async function handleVerify(request, env, now, cors) {
  assertEnv(env, ['DB', 'HASH_SALT', 'FIREBASE_PROJECT_ID']);

  const { user } = await requireAuth(request, env, now);
  const body = await readJson(request);

  const purpose = body.purpose;
  if (purpose !== 'verify_phone' && purpose !== 'add_phone') {
    throw new HttpError(400, 'invalid_purpose');
  }

  const phone = normalizePhone(body.phone);
  if (!phone) throw new HttpError(400, 'invalid_phone');

  if (typeof body.code !== 'string' || !/^\d{6}$/.test(body.code)) {
    throw new HttpError(400, 'invalid_code');
  }

  const ip = request.headers.get('CF-Connecting-IP') || '';
  const ipHash = await hmacHex(env, 'ip:' + ip);
  const ua = request.headers.get('User-Agent') || '';
  const uaHash = ua ? await hmacHex(env, 'ua:' + ua) : null;

  // Atomically increment attempts before comparing.
  const otpRes = await env.DB.prepare(
    `UPDATE phone_otps
     SET attempts = attempts + 1
     WHERE id = (
       SELECT id FROM phone_otps
       WHERE user_id = ? AND phone_e164 = ? AND purpose = ?
         AND used_at IS NULL AND expires_at > ?
       ORDER BY created_at DESC
       LIMIT 1
     )
     RETURNING id, attempts, max_attempts, code_hash, phone_e164, user_id, purpose`
  )
    .bind(user.id, phone, purpose, now)
    .run();

  const otp = otpRes.results?.[0];
  if (!otp) throw new HttpError(400, 'invalid_or_expired_code');

  if (Number(otp.attempts) > Number(otp.max_attempts)) {
    await env.DB.prepare('UPDATE phone_otps SET used_at = ? WHERE id = ?')
      .bind(now, otp.id)
      .run();
    throw new HttpError(429, 'too_many_attempts');
  }

  const expectedHash = await hmacHex(env, `otp:${otp.id}:${phone}:${body.code}`);

  if (!timingSafeEqual(expectedHash, otp.code_hash)) {
    const attemptsLeft = Math.max(0, Number(otp.max_attempts) - Number(otp.attempts));
    throw new HttpError(400, 'invalid_or_expired_code', {
      attempts_left: attemptsLeft,
    });
  }

  const isPrimary = purpose === 'verify_phone' ? 1 : 0;
  const payoutHoldUntil = isPrimary ? null : now + ADD_PHONE_HOLD_SECONDS;

  const newPhoneRowId = generateId('uph_');
  const auditId = generateId('aud_');
  const meta = {
    purpose,
    phone: maskPhone(phone),
    is_primary: isPrimary === 1,
    payout_hold_until: payoutHoldUntil,
  };
  if (uaHash) meta.ua_hash = uaHash;

  let batchResults;
  try {
    batchResults = await env.DB.batch([
      // 1. Mark the OTP used, but only if it is still unused.
      env.DB.prepare(
        'UPDATE phone_otps SET used_at = ? WHERE id = ? AND used_at IS NULL'
      ).bind(now, otp.id),

      // 2. Reactivate an existing unverified active row for this user+phone.
      //    Enforce business rules (verify_phone: no other verified;
      //    add_phone: must have another verified) inside the statement.
      env.DB.prepare(
        `UPDATE user_phones
         SET verified_at = ?, is_primary = ?, payout_hold_until = ?
         WHERE user_id = ? AND phone_e164 = ? AND removed_at IS NULL AND verified_at IS NULL
           AND EXISTS (SELECT 1 FROM phone_otps WHERE id = ? AND used_at = ?)
           AND (
             (? = 'verify_phone' AND NOT EXISTS (
               SELECT 1 FROM user_phones
               WHERE user_id = ? AND phone_e164 != ?
                 AND verified_at IS NOT NULL AND removed_at IS NULL
             ))
             OR
             (? = 'add_phone' AND EXISTS (
               SELECT 1 FROM user_phones
               WHERE user_id = ? AND phone_e164 != ?
                 AND verified_at IS NOT NULL AND removed_at IS NULL
             ))
           )`
      ).bind(
        now,
        isPrimary,
        payoutHoldUntil,
        user.id,
        phone,
        otp.id,
        now,
        purpose,
        user.id,
        phone,
        purpose,
        user.id,
        phone
      ),

      // 3. Insert a new row only if no active row already exists for this user+phone.
      //    Enforce business rules at write time so parallel requests cannot
      //    exceed the phone limits.
      env.DB.prepare(
        `INSERT INTO user_phones
           (id, user_id, phone_e164, is_primary, verified_at, added_at, payout_hold_until, removed_at)
         SELECT ?, ?, ?, ?, ?, ?, ?, NULL
         WHERE NOT EXISTS (
           SELECT 1 FROM user_phones
           WHERE user_id = ? AND phone_e164 = ? AND removed_at IS NULL
         )
         AND EXISTS (SELECT 1 FROM phone_otps WHERE id = ? AND used_at = ?)
         AND (SELECT COUNT(*) FROM user_phones
              WHERE user_id = ? AND removed_at IS NULL) < ?
         AND (
           (? = 'verify_phone' AND NOT EXISTS (
             SELECT 1 FROM user_phones
             WHERE user_id = ? AND verified_at IS NOT NULL AND removed_at IS NULL
           ))
           OR
           (? = 'add_phone' AND EXISTS (
             SELECT 1 FROM user_phones
             WHERE user_id = ? AND verified_at IS NOT NULL AND removed_at IS NULL
           ))
         )`
      ).bind(
        newPhoneRowId,
        user.id,
        phone,
        isPrimary,
        now,
        now,
        payoutHoldUntil,
        user.id,
        phone,
        otp.id,
        now,
        user.id,
        MAX_ACTIVE_PHONES,
        purpose,
        user.id,
        purpose,
        user.id
      ),

      // 4. Audit only if the OTP was successfully marked used.
      env.DB.prepare(
        `INSERT INTO audit_log
           (id, actor_user_id, action, target_type, target_id, metadata, ip_hash, created_at)
         SELECT ?, ?, ?, ?, ?, ?, ?, ?
         WHERE EXISTS (SELECT 1 FROM phone_otps WHERE id = ? AND used_at = ?)`
      ).bind(
        auditId,
        user.id,
        'phone_verified',
        'phone',
        maskPhone(phone),
        JSON.stringify(meta),
        ipHash,
        now,
        otp.id,
        now
      ),

      // 5. Bug fix: set users.phone_verified_at (only if it was null).
      env.DB.prepare(
        `UPDATE users SET phone_verified_at = ?, updated_at = ?
         WHERE id = ? AND phone_verified_at IS NULL
           AND EXISTS (SELECT 1 FROM phone_otps WHERE id = ? AND used_at = ?)`
      ).bind(now, now, user.id, otp.id, now),
    ]);
  } catch (err) {
    const msg = String(err?.message || '');
    if (msg.includes('UNIQUE') || msg.includes('constraint')) {
      throw new HttpError(409, 'phone_unavailable');
    }
    throw err;
  }

  // If the OTP was already consumed by a parallel request, the batch did nothing.
  if ((batchResults[0]?.meta?.changes ?? 0) !== 1) {
    throw new HttpError(400, 'invalid_or_expired_code');
  }

  // If neither update nor insert changed a row, the number is no longer available.
  const phoneWrites =
    (batchResults[1]?.meta?.changes ?? 0) +
    (batchResults[2]?.meta?.changes ?? 0);
  if (phoneWrites === 0) {
    throw new HttpError(409, 'phone_unavailable');
  }

  return json(
    {
      verified: true,
      phone,
      is_primary: isPrimary === 1,
      payout_hold_until: payoutHoldUntil,
    },
    200,
    cors
  );
}

/* ------------------------------------------------------------------ */
/* GET /phone                                                         */
/* ------------------------------------------------------------------ */

async function handleGetPhone(request, env, now, cors) {
  assertEnv(env, ['DB', 'HASH_SALT', 'FIREBASE_PROJECT_ID']);

  const { user } = await requireAuth(request, env, now);

  const rows = await env.DB.prepare(
    `SELECT phone_e164, is_primary, verified_at, payout_hold_until
     FROM user_phones
     WHERE user_id = ? AND verified_at IS NOT NULL AND removed_at IS NULL
     ORDER BY is_primary DESC, added_at ASC`
  )
    .bind(user.id)
    .all();

  const phones = (rows.results || []).map((r) => ({
    phone: maskPhone(r.phone_e164),
    role: Number(r.is_primary) === 1 ? 'primary' : 'backup',
    verified_at: r.verified_at,
    payout_hold_until: r.payout_hold_until,
  }));

  let holdUntil = null;
  for (const p of phones) {
    if (p.payout_hold_until && Number(p.payout_hold_until) > now) {
      if (holdUntil === null || Number(p.payout_hold_until) > holdUntil) {
        holdUntil = Number(p.payout_hold_until);
      }
    }
  }

  return json(
    {
      phones,
      payout_hold_active: holdUntil !== null,
      payout_hold_until: holdUntil,
    },
    200,
    cors
  );
}

/* ------------------------------------------------------------------ */
/* POST /phone/make-primary                                           */
/* ------------------------------------------------------------------ */

async function handleMakePrimary(request, env, now, cors) {
  assertEnv(env, ['DB', 'HASH_SALT', 'FIREBASE_PROJECT_ID']);

  const { user, payload } = await requireAuth(request, env, now);
  const body = await readJson(request);

  const phone = normalizePhone(body.phone);
  if (!phone) throw new HttpError(400, 'invalid_phone');

  if (now - payload.auth_time > RECENT_LOGIN_SECONDS) {
    throw new HttpError(403, 'recent_login_required');
  }

  const target = await env.DB.prepare(
    `SELECT id, is_primary FROM user_phones
     WHERE user_id = ? AND phone_e164 = ? AND verified_at IS NOT NULL AND removed_at IS NULL
     LIMIT 1`
  )
    .bind(user.id, phone)
    .first();

  if (!target) throw new HttpError(404, 'phone_not_found');
  if (Number(target.is_primary) === 1) throw new HttpError(409, 'already_primary');

  const ip = request.headers.get('CF-Connecting-IP') || '';
  const ipHash = await hmacHex(env, 'ip:' + ip);
  const ua = request.headers.get('User-Agent') || '';
  const uaHash = ua ? await hmacHex(env, 'ua:' + ua) : null;

  const holdUntil = now + ADD_PHONE_HOLD_SECONDS;
  const meta = {
    new_primary: maskPhone(phone),
    payout_hold_until: holdUntil,
  };
  if (uaHash) meta.ua_hash = uaHash;

  let results;
  try {
    results = await env.DB.batch([
      // 1. Demote current primary (never the target itself — already checked).
      env.DB.prepare(
        `UPDATE user_phones SET is_primary = 0
         WHERE user_id = ? AND is_primary = 1 AND removed_at IS NULL
           AND phone_e164 != ?`
      ).bind(user.id, phone),

      // 2. Promote the target.
      env.DB.prepare(
        `UPDATE user_phones SET is_primary = 1, payout_hold_until = ?
         WHERE user_id = ? AND phone_e164 = ?
           AND verified_at IS NOT NULL AND removed_at IS NULL
           AND is_primary = 0`
      ).bind(holdUntil, user.id, phone),

      // 3. Audit.
      auditStmt(
        env,
        generateId('aud_'),
        user.id,
        'phone_make_primary',
        'phone',
        maskPhone(phone),
        meta,
        ipHash,
        now
      ),
    ]);
  } catch (err) {
    const msg = String(err?.message || '');
    if (msg.includes('UNIQUE') || msg.includes('constraint')) {
      throw new HttpError(409, 'phone_unavailable');
    }
    throw err;
  }

  if ((results[1]?.meta?.changes ?? 0) !== 1) {
    throw new HttpError(404, 'phone_not_found');
  }

  return json(
    { primary: maskPhone(phone), payout_hold_until: holdUntil },
    200,
    cors
  );
}

/* ------------------------------------------------------------------ */
/* POST /phone/remove                                                 */
/* ------------------------------------------------------------------ */

async function handleRemovePhone(request, env, now, cors) {
  assertEnv(env, ['DB', 'HASH_SALT', 'FIREBASE_PROJECT_ID']);

  const { user, payload } = await requireAuth(request, env, now);
  const body = await readJson(request);

  const phone = normalizePhone(body.phone);
  if (!phone) throw new HttpError(400, 'invalid_phone');

  if (now - payload.auth_time > RECENT_LOGIN_SECONDS) {
    throw new HttpError(403, 'recent_login_required');
  }

  const target = await env.DB.prepare(
    `SELECT id, is_primary FROM user_phones
     WHERE user_id = ? AND phone_e164 = ? AND removed_at IS NULL
     LIMIT 1`
  )
    .bind(user.id, phone)
    .first();

  if (!target) throw new HttpError(404, 'phone_not_found');

  const counts = await env.DB.prepare(
    `SELECT COUNT(*) AS active_verified FROM user_phones
     WHERE user_id = ? AND verified_at IS NOT NULL AND removed_at IS NULL`
  )
    .bind(user.id)
    .first();

  if (Number(counts?.active_verified || 0) < 2) {
    throw new HttpError(409, 'cannot_remove_only_number');
  }

  const ip = request.headers.get('CF-Connecting-IP') || '';
  const ipHash = await hmacHex(env, 'ip:' + ip);
  const ua = request.headers.get('User-Agent') || '';
  const uaHash = ua ? await hmacHex(env, 'ua:' + ua) : null;

  const isPrimary = Number(target.is_primary) === 1;

  if (!isPrimary) {
    // ---------------- Backup removal ----------------
    const meta = { phone: maskPhone(phone) };
    if (uaHash) meta.ua_hash = uaHash;

    const results = await env.DB.batch([
      env.DB.prepare(
        `UPDATE user_phones SET removed_at = ?, is_primary = 0
         WHERE user_id = ? AND phone_e164 = ? AND removed_at IS NULL AND is_primary = 0
           AND (SELECT COUNT(*) FROM user_phones
                WHERE user_id = ? AND verified_at IS NOT NULL AND removed_at IS NULL) >= 2`
      ).bind(now, user.id, phone, user.id),
      auditStmt(
        env,
        generateId('aud_'),
        user.id,
        'phone_removed',
        'phone',
        maskPhone(phone),
        meta,
        ipHash,
        now
      ),
    ]);

    if ((results[0]?.meta?.changes ?? 0) !== 1) {
      throw new HttpError(409, 'cannot_remove_only_number');
    }

    return json(
      { removed: true, new_primary: null, payout_hold_until: null },
      200,
      cors
    );
  }

  // ---------------- Primary removal ----------------
  const newPrimaryRow = await env.DB.prepare(
    `SELECT phone_e164 FROM user_phones
     WHERE user_id = ? AND phone_e164 != ?
       AND verified_at IS NOT NULL AND removed_at IS NULL
       AND is_primary = 0
     ORDER BY added_at ASC LIMIT 1`
  )
    .bind(user.id, phone)
    .first();

  if (!newPrimaryRow) {
    throw new HttpError(409, 'cannot_remove_only_number');
  }

  const holdUntil = now + ADD_PHONE_HOLD_SECONDS;
  const newPrimaryMasked = maskPhone(newPrimaryRow.phone_e164);
  const meta = {
    phone: maskPhone(phone),
    new_primary: newPrimaryMasked,
    payout_hold_until: holdUntil,
  };
  if (uaHash) meta.ua_hash = uaHash;

  const results = await env.DB.batch([
    // 1. Remove the current primary (guarded by the "≥2 verified active" rule).
    env.DB.prepare(
      `UPDATE user_phones SET removed_at = ?, is_primary = 0
       WHERE user_id = ? AND phone_e164 = ? AND removed_at IS NULL AND is_primary = 1
         AND (SELECT COUNT(*) FROM user_phones
              WHERE user_id = ? AND verified_at IS NOT NULL AND removed_at IS NULL) >= 2`
    ).bind(now, user.id, phone, user.id),

    // 2. Promote the backup (only if no other primary exists right now).
    env.DB.prepare(
      `UPDATE user_phones SET is_primary = 1, payout_hold_until = ?
       WHERE user_id = ? AND phone_e164 = ?
         AND verified_at IS NOT NULL AND removed_at IS NULL
         AND is_primary = 0
         AND NOT EXISTS (
           SELECT 1 FROM user_phones
           WHERE user_id = ? AND is_primary = 1 AND removed_at IS NULL
         )`
    ).bind(holdUntil, user.id, newPrimaryRow.phone_e164, user.id),

    // 3. Audit.
    auditStmt(
      env,
      generateId('aud_'),
      user.id,
      'phone_removed_primary',
      'phone',
      maskPhone(phone),
      meta,
      ipHash,
      now
    ),
  ]);

  if (
    (results[0]?.meta?.changes ?? 0) !== 1 ||
    (results[1]?.meta?.changes ?? 0) !== 1
  ) {
    throw new HttpError(409, 'cannot_remove_only_number');
  }

  return json(
    {
      removed: true,
      new_primary: newPrimaryMasked,
      payout_hold_until: holdUntil,
    },
    200,
    cors
  );
}

/* ------------------------------------------------------------------ */
/* POST /internal/phone-status  (service-to-service, no Firebase)     */
/* ------------------------------------------------------------------ */

async function handleInternalPhoneStatus(request, env, now) {
  // Browsers always send Origin on cross-origin requests; reject outright
  // so a leaked key in a page bundle can never be used from a browser.
  if (request.headers.get('Origin')) {
    return json({ error: 'forbidden' }, 403, {});
  }

  assertEnv(env, ['DB', 'INTERNAL_KEY']);

  const providedKey = request.headers.get('X-Internal-Key') || '';
  if (!timingSafeEqual(providedKey, env.INTERNAL_KEY)) {
    // Same body for missing and wrong so nothing is leaked.
    return json({ error: 'unauthorized' }, 401, {});
  }

  let body;
  try {
    body = await readJson(request);
  } catch (err) {
    if (err instanceof HttpError) {
      return json({ error: err.code }, err.status, {});
    }
    return json({ error: 'invalid_json' }, 400, {});
  }

  const userId = body.user_id;
  if (
    typeof userId !== 'string' ||
    userId.length === 0 ||
    userId.length >= MAX_INTERNAL_USER_ID_LENGTH
  ) {
    return json({ error: 'invalid_user_id' }, 400, {});
  }

  const row = await env.DB.prepare(
    `SELECT
       (SELECT COUNT(*) FROM user_phones
         WHERE user_id = ? AND verified_at IS NOT NULL AND removed_at IS NULL) AS verified_count,
       (SELECT MAX(payout_hold_until) FROM user_phones
         WHERE user_id = ? AND removed_at IS NULL) AS max_hold`
  )
    .bind(userId, userId)
    .first();

  const phoneVerified = Number(row?.verified_count || 0) > 0;
  const maxHold = row?.max_hold != null ? Number(row.max_hold) : null;
  const payoutHoldActive = maxHold !== null && maxHold > now;

  return json(
    {
      phone_verified: phoneVerified,
      payout_hold_active: payoutHoldActive,
      payout_hold_until: payoutHoldActive ? maxHold : null,
    },
    200,
    {}
  );
}

/* ------------------------------------------------------------------ */
/* Worker entrypoint                                                  */
/* ------------------------------------------------------------------ */

export default {
  async fetch(request, env) {
    const now = Math.floor(Date.now() / 1000);
    const origin = request.headers.get('Origin');

    if (origin && !isAllowedOrigin(origin)) {
      return json({ error: 'origin_not_allowed' }, 403, {});
    }

    const cors = corsHeaders(origin);
    const url = new URL(request.url);

    // Internal service endpoint: reject any request that carries an Origin
    // header (i.e. was made from a browser) with no CORS headers.
    if (url.pathname === '/internal/phone-status' && origin) {
      return json({ error: 'forbidden' }, 403, {});
    }

    if (request.method === 'OPTIONS') {
      return new Response(null, {
        status: 204,
        headers: {
          ...cors,
          'Cache-Control': 'no-store',
          'X-Content-Type-Options': 'nosniff',
        },
      });
    }

    try {
      if (url.pathname === '/health' && request.method === 'GET') {
        return json(
          { ok: true, service: 'earnity-verify', time: now },
          200,
          cors
        );
      }

      if (url.pathname === '/phone/request-code' && request.method === 'POST') {
        return await handleRequestCode(request, env, now, cors);
      }

      if (url.pathname === '/phone/verify' && request.method === 'POST') {
        return await handleVerify(request, env, now, cors);
      }

      if (url.pathname === '/phone' && request.method === 'GET') {
        return await handleGetPhone(request, env, now, cors);
      }

      if (url.pathname === '/phone/make-primary' && request.method === 'POST') {
        return await handleMakePrimary(request, env, now, cors);
      }

      if (url.pathname === '/phone/remove' && request.method === 'POST') {
        return await handleRemovePhone(request, env, now, cors);
      }

      if (
        url.pathname === '/internal/phone-status' &&
        request.method === 'POST'
      ) {
        return await handleInternalPhoneStatus(request, env, now);
      }

      if (
        url.pathname === '/health' ||
        url.pathname === '/phone/request-code' ||
        url.pathname === '/phone/verify' ||
        url.pathname === '/phone' ||
        url.pathname === '/phone/make-primary' ||
        url.pathname === '/phone/remove' ||
        url.pathname === '/internal/phone-status'
      ) {
        return json({ error: 'method_not_allowed' }, 405, cors);
      }

      return json({ error: 'not_found' }, 404, cors);
    } catch (err) {
      if (err instanceof HttpError) {
        return json(
          { error: err.code, ...(err.extra || {}) },
          err.status,
          cors
        );
      }
      console.error('unhandled_error', { name: err?.name });
      return json({ error: 'server_error' }, 500, cors);
    }
  },
};
