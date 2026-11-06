/* Chair board page: fetch board.enc.json, get the key with WebCrypto, decrypt, render.
 * Two access modes, told apart by the envelope's kdf: "none" (link mode, the raw key rides in the
 * URL fragment #k=<base64url>, which a browser never sends to a server) and "PBKDF2-SHA256"
 * (passphrase mode). Passphrase normalization, KDF parameters, key id and AAD must stay identical
 * to chairboard/crypto.py. All text reaches the DOM through textContent / text nodes, never
 * innerHTML. */
(function () {
  "use strict";

  var ENVELOPE_URL = "board.enc.json";
  var AAD = "chairboard-v1";
  var KEY_DB = "chairboard-v1";
  var KEY_STORE = "keys";
  var KEY_MAX_AGE_MS = 12 * 3600 * 1000;
  var KDF_NONE = "none";
  var KDF_PBKDF2 = "PBKDF2-SHA256";
  var KID_RE = /^[0-9a-f]{16}$/;
  var URL_B64_RE = /^[A-Za-z0-9_-]+$/;
  var LINK_KEY_BYTES = 32;
  var MIN_ITER = 600000;
  var MAX_ITER = 10000000;
  var STALE_MS = 24 * 3600 * 1000;
  var REFRESH_MS = 5 * 60 * 1000;
  var MIN_CHECK_MS = 30 * 1000;
  var OLD_DAYS = 14;
  var STEPS = ["Scheduled", "Received", "In progress", "Pending registrar", "Done"];
  var WAIT_LABELS = { "Registrar": "Registrar \u00b7 SIS update" };

  var ERR_WRONG = "That passphrase didn't open the board. Check the spaces and try again.";
  var ERR_LOAD = "The board couldn't be loaded. Check your connection and try again.";
  var ERR_SECURE = "This page needs a secure (https) connection to open.";
  var ERR_FORMAT = "This board uses a newer format than this page understands. Reload and try again.";
  var ERR_ROTATED = "The passphrase was changed. Enter the new one.";
  var ERR_LINK_NONE = "Open this board from the link Ryan sent you.";
  var ERR_LINK_CHANGED = "This board's link was changed. Use the new link.";
  var ERR_LINK_BAD = "This link looks incomplete. Open the board from the full link you were sent.";
  var ERR_LINK_OPEN = "The board couldn't be opened with this link. Use the link you were sent.";

  // Mirrored by tests/chairboard/test_crypto.py (parsed out of this block); keep it valid JSON.
  // BEGIN NORMALIZE_CASES
  var NORMALIZE_CASES = [
    ["  Hello   World ", "hello world"],
    ["CORRECT\tHorse\nBattery\r\nStaple", "correct horse battery staple"],
    ["a\u00a0b\u3000c", "a b c"],
    ["a\u2003\u2003b", "a b"],
    ["\ufeffbom   first", "bom first"],
    ["x\u001cy", "x\u001cy"],
    ["\ufb01nd", "find"],
    ["\uff26\uff55\uff4c\uff4c\uff57\uff49\uff44\uff54\uff48", "fullwidth"],
    ["cafe\u0301", "caf\u00e9"],
    ["\u00c5NGSTR\u00d6M", "\u00e5ngstr\u00f6m"],
    ["\u03a3\u0391\u03a3", "\u03c3\u03b1\u03c2"],
    ["\u0130", "i\u0307"],
    ["   ", ""],
    ["", ""]
  ];
  // END NORMALIZE_CASES

  // Mirrored by tests/chairboard/test_crypto.py::test_known_answer_vector.
  var KAT = {
    passphrase: "Correct  Horse Battery STAPLE ",
    plaintext: "{\"v\":1,\"kat\":\"chairboard\"}",
    envelope: {
      v: 1,
      kdf: "PBKDF2-SHA256",
      iter: 600000,
      salt: "AAECAwQFBgcICQoLDA0ODw==",
      iv: "ZGVmZ2hpamtsbW5v",
      aad: "chairboard-v1",
      ct: "8cL5oIY61EfquGnHSTHfsKX/x+diXUYu0smgtOy2tEFI8YNYRDs4HqmN",
      published_at: "2026-10-22T00:00:00+00:00"
    }
  };

  // Mirrored by tests/chairboard/test_crypto.py::test_link_key_known_answer_vector.
  var KAT_LINK = {
    fragment: "ICEiIyQlJicoKSorLC0uLzAxMjM0NTY3ODk6Ozw9Pj8",
    plaintext: "{\"v\":1,\"kat\":\"chairboard\"}",
    envelope: {
      v: 1,
      kdf: "none",
      kid: "72dbb7336c767800",
      iv: "ZGVmZ2hpamtsbW5v",
      aad: "chairboard-v1",
      ct: "zk/48eWA2O+3Nav6sDX9BajrlxxRqxwp4T10oBv4ZS2j7+ptmNJ8lLwf",
      published_at: "2026-10-22T00:00:00+00:00"
    }
  };

  var WS_RE = /[\t\n\v\f\r \u00a0\u1680\u2000-\u200a\u2028\u2029\u202f\u205f\u3000\ufeff]+/g;

  function normalizePassphrase(s) {
    return String(s).normalize("NFKC").toLowerCase().replace(WS_RE, " ").replace(/^ | $/g, "");
  }

  function b64ToBytes(s) {
    var bin = atob(s);
    var out = new Uint8Array(bin.length);
    for (var i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
    return out;
  }

  function fail(kind, message) {
    var err = new Error(message);
    err.kind = kind;
    return err;
  }

  function b64urlToBytes(s) {
    if (!URL_B64_RE.test(s)) throw new Error("not base64url");
    var std = s.replace(/-/g, "+").replace(/_/g, "/");
    while (std.length % 4) std += "=";
    return b64ToBytes(std);
  }

  function checkEnvelope(env) {
    if (!env || typeof env !== "object") throw fail("format", "envelope is not an object");
    if (env.v !== 1) throw fail("format", "unsupported envelope version");
    if (env.kdf !== KDF_PBKDF2 && env.kdf !== KDF_NONE) throw fail("format", "unsupported kdf");
    if (env.aad !== AAD) throw fail("format", "unexpected aad");
    if (typeof env.iv !== "string" || typeof env.ct !== "string") {
      throw fail("format", "envelope fields must be strings");
    }
    if (env.kdf === KDF_NONE) {
      if ("salt" in env || "iter" in env) throw fail("format", "a link-key envelope carries no salt or iter");
      if (typeof env.kid !== "string" || !KID_RE.test(env.kid)) throw fail("format", "envelope kid is invalid");
    } else {
      if (!Number.isInteger(env.iter) || env.iter < MIN_ITER || env.iter > MAX_ITER) {
        throw fail("format", "iteration count out of range");
      }
      if (typeof env.salt !== "string") throw fail("format", "envelope fields must be strings");
    }
    var salt = null;
    var iv, ct;
    try {
      if (env.kdf === KDF_PBKDF2) salt = b64ToBytes(env.salt);
      iv = b64ToBytes(env.iv);
      ct = b64ToBytes(env.ct);
    } catch (e) {
      throw fail("format", "envelope is not valid base64");
    }
    if ((salt && salt.length !== 16) || iv.length !== 12 || ct.length < 16) {
      throw fail("format", "envelope field lengths are wrong");
    }
    return { salt: salt, iv: iv, ct: ct };
  }

  function requireSubtle() {
    if (!globalThis.crypto || !globalThis.crypto.subtle) throw fail("secure", ERR_SECURE);
    return globalThis.crypto.subtle;
  }

  async function deriveKey(passphrase, salt, iterations) {
    var subtle = requireSubtle();
    var base = await subtle.importKey(
      "raw", new TextEncoder().encode(normalizePassphrase(passphrase)), "PBKDF2", false, ["deriveKey"]
    );
    return subtle.deriveKey(
      { name: "PBKDF2", hash: "SHA-256", salt: salt, iterations: iterations },
      base,
      { name: "AES-GCM", length: 256 },
      false,
      ["decrypt"]
    );
  }

  // First 16 hex characters of SHA-256(key): the envelope's kid, so a stale link can be told from a
  // broken one without trying to decrypt.
  async function keyId(bytes) {
    var digest = new Uint8Array(await requireSubtle().digest("SHA-256", bytes));
    var hex = "";
    for (var i = 0; i < 8; i++) hex += (digest[i] < 16 ? "0" : "") + digest[i].toString(16);
    return hex;
  }

  // The #k= value to a non-extractable AES-GCM key, after checking it is the board's key (kid).
  async function linkKeyFromText(text, kid) {
    var bytes;
    try {
      bytes = b64urlToBytes(text);
    } catch (e) {
      throw fail("link", ERR_LINK_BAD);
    }
    if (bytes.length !== LINK_KEY_BYTES) throw fail("link", ERR_LINK_BAD);
    if ((await keyId(bytes)) !== kid) throw fail("link", ERR_LINK_CHANGED);
    return requireSubtle().importKey("raw", bytes, { name: "AES-GCM" }, false, ["decrypt"]);
  }

  async function decryptWithKey(key, parts) {
    var plain = await requireSubtle().decrypt(
      { name: "AES-GCM", iv: parts.iv, additionalData: new TextEncoder().encode(AAD) },
      key,
      parts.ct
    );
    return new TextDecoder("utf-8", { fatal: true }).decode(plain);
  }

  async function chairboardSelfTest() {
    var failures = [];
    NORMALIZE_CASES.forEach(function (c) {
      var got = normalizePassphrase(c[0]);
      if (got !== c[1]) failures.push({ input: c[0], expected: c[1], got: got });
    });
    var parts = checkEnvelope(KAT.envelope);
    var key = await deriveKey(KAT.passphrase, parts.salt, KAT.envelope.iter);
    var katOk = false;
    try {
      katOk = (await decryptWithKey(key, parts)) === KAT.plaintext;
    } catch (e) {
      katOk = false;
    }
    var normalizedKey = await deriveKey(normalizePassphrase(KAT.passphrase), parts.salt, KAT.envelope.iter);
    var sameKey = false;
    try {
      sameKey = (await decryptWithKey(normalizedKey, parts)) === KAT.plaintext;
    } catch (e) {
      sameKey = false;
    }
    var wrongRejected = false;
    try {
      var wrong = await deriveKey("not the passphrase", parts.salt, KAT.envelope.iter);
      await decryptWithKey(wrong, parts);
    } catch (e) {
      wrongRejected = true;
    }

    var linkParts = checkEnvelope(KAT_LINK.envelope);
    var linkKey = await linkKeyFromText(KAT_LINK.fragment, KAT_LINK.envelope.kid);
    var linkOk = false;
    try {
      linkOk = (await decryptWithKey(linkKey, linkParts)) === KAT_LINK.plaintext;
    } catch (e) {
      linkOk = false;
    }
    var linkKidOk = (await keyId(b64urlToBytes(KAT_LINK.fragment))) === KAT_LINK.envelope.kid;
    var linkWrongRejected = false;
    try {
      var wrongBytes = new Uint8Array(LINK_KEY_BYTES);
      var wrongKey = await requireSubtle().importKey("raw", wrongBytes, { name: "AES-GCM" }, false, ["decrypt"]);
      await decryptWithKey(wrongKey, linkParts);
    } catch (e) {
      linkWrongRejected = true;
    }
    var linkMismatchRejected = false;
    try {
      await linkKeyFromText(KAT_LINK.fragment, "0000000000000000");
    } catch (e) {
      linkMismatchRejected = e.kind === "link";
    }

    var result = {
      ok: failures.length === 0 && katOk && sameKey && wrongRejected && key.extractable === false &&
        linkOk && linkKidOk && linkWrongRejected && linkMismatchRejected && linkKey.extractable === false,
      normalization: { total: NORMALIZE_CASES.length, failures: failures },
      knownAnswer: katOk,
      normalizationIdempotentForKey: sameKey,
      keyNotExtractable: key.extractable === false,
      wrongPassphraseRejected: wrongRejected,
      linkKnownAnswer: linkOk,
      linkKeyId: linkKidOk,
      linkWrongKeyRejected: linkWrongRejected,
      linkKidMismatchRejected: linkMismatchRejected,
      linkKeyNotExtractable: linkKey.extractable === false
    };
    if (globalThis.console) console.log("chairboardSelfTest", JSON.stringify(result));
    return result;
  }
  globalThis.chairboardSelfTest = chairboardSelfTest;

  if (typeof document === "undefined") return;

  // ---- page ----------------------------------------------------------------------------------

  var $ = function (id) { return document.getElementById(id); };
  var state = {
    source: null, payload: null, published: null, filter: "All", opener: null,
    key: null, kdf: null, salt: null, kid: null, publishedAt: null, openId: null, lastCheck: 0,
    refreshing: false
  };
  var timersStarted = false;

  function el(tag, props) {
    var node = document.createElement(tag);
    if (props) {
      Object.keys(props).forEach(function (k) {
        var v = props[k];
        if (v === null || v === undefined || v === false) return;
        if (k === "class") node.className = v;
        else if (k === "text") node.textContent = v;
        else node.setAttribute(k, v === true ? "" : String(v));
      });
    }
    for (var i = 2; i < arguments.length; i++) {
      var kid = arguments[i];
      if (kid === null || kid === undefined || kid === false) continue;
      if (Array.isArray(kid)) kid.forEach(function (k) { if (k) node.append(k); });
      else node.append(kid);
    }
    return node;
  }

  function str(v) { return v === null || v === undefined ? "" : String(v); }

  function parseDate(iso) {
    if (!iso) return null;
    var d = new Date(iso);
    return isNaN(d.getTime()) ? null : d;
  }

  function fmtDate(iso) {
    var d = parseDate(iso);
    if (!d) return "";
    var opts = { month: "short", day: "numeric" };
    if (d.getFullYear() !== new Date().getFullYear()) opts.year = "numeric";
    return d.toLocaleDateString("en-US", opts);
  }

  function ago(d) {
    var m = Math.max(0, Math.round((Date.now() - d.getTime()) / 60000));
    if (m < 1) return "just now";
    if (m < 60) return m + " min ago";
    if (m < 1440) return Math.round(m / 60) + " h ago";
    var days = Math.round(m / 1440);
    return days + (days === 1 ? " day ago" : " days ago");
  }

  function daysSince(iso) {
    var d = parseDate(iso);
    return d ? Math.max(0, Math.floor((Date.now() - d.getTime()) / 86400000)) : null;
  }

  function stepOf(t) {
    var n = Math.floor(Number(t.step));
    return isNaN(n) ? 0 : Math.min(STEPS.length - 1, Math.max(0, n));
  }

  function stepLabel(t) { return str(t.step_label) || STEPS[stepOf(t)]; }

  function waitText(t) {
    var who = str(t.waiting_on);
    var text = "Waiting on " + (WAIT_LABELS[who] || who);
    var since = fmtDate(t.waiting_since);
    return since ? text + " \u00b7 since " + since : text;
  }

  function inStageDays(t) {
    var d = daysSince(t.waiting_on && t.waiting_since ? t.waiting_since : t.last_activity_at || t.opened_at);
    return d === null ? 0 : d;
  }

  function track(t) {
    var step = stepOf(t);
    var waiting = !!t.waiting_on;
    var segs = STEPS.map(function (_, i) {
      var cls = "seg";
      if (i < step) cls += " on";
      else if (i === step) cls += waiting ? " paused" : " now";
      return el("span", { class: cls });
    });
    var label = "Step " + (step + 1) + " of " + STEPS.length + ": " + stepLabel(t) + (waiting ? ", waiting on " + str(t.waiting_on) : "");
    var bar = el("div", { class: "track st" + step + (waiting ? " wait" : ""), role: "img", "aria-label": label }, segs);
    var tl = el("div", { class: "tlabel" },
      el("b", { text: stepLabel(t) }),
      waiting ? el("span", { class: "wait-chip", text: waitText(t) }) : null,
      t.outcome === "declined" ? el("span", { class: "outcome declined", text: "Declined" }) : null
    );
    return [bar, tl];
  }

  function rowFor(t, done) {
    var meta = [str(t.kind), str(t.requester), str(t.term_label)].filter(Boolean).join(" \u00b7 ");
    var days = inStageDays(t);
    var age;
    if (done) {
      var verb = t.closed_at ? "closed" : "done";
      var when = fmtDate(t.done_at || t.closed_at);
      age = el("span", { class: "age", text: when ? verb + " " + when : verb });
    } else {
      age = el("span", {
        class: "age" + (days >= OLD_DAYS ? " old" : ""),
        text: days === 0 ? "today" : days + (days === 1 ? " day" : " days")
      });
    }
    return el("button", { class: "row", type: "button", "data-id": str(t.id) },
      el("span", { class: "id", text: str(t.ref) }),
      el("span", { class: "main" },
        el("span", { class: "t", text: str(t.title) }),
        str(t.summary) ? el("span", { class: "sum", text: str(t.summary) }) : null,
        el("span", { class: "m", text: meta })
      ),
      el("span", { class: "trk" }, track(t)),
      age
    );
  }

  function visible(list, subject) {
    return list.filter(function (t) { return subject === "All" || t.subject === subject; });
  }

  function render() {
    var payload = state.payload;
    var board = payload.board || {};
    var tickets = (Array.isArray(payload.tickets) ? payload.tickets : []).filter(function (t) { return t && typeof t === "object"; });
    var subjects = Array.isArray(payload.subjects) ? payload.subjects.map(str) : [];
    if (!subjects.length) {
      tickets.forEach(function (t) { if (t.subject && subjects.indexOf(t.subject) < 0) subjects.push(str(t.subject)); });
    }
    if (state.filter !== "All" && subjects.indexOf(state.filter) < 0) state.filter = "All";

    $("title").textContent = str(board.title) || "Schedule Requests";
    document.title = str(board.title) || "Schedule Requests";
    $("dept").textContent = str(board.department_label);
    $("note").textContent = str(board.note);
    updateFresh();

    $("filters").replaceChildren.apply($("filters"), ["All"].concat(subjects).map(function (s) {
      return el("button", { class: "chip", type: "button", "aria-pressed": s === state.filter ? "true" : "false", "data-subject": s, text: s });
    }));

    var open = visible(tickets.filter(function (t) { return stepOf(t) < STEPS.length - 1; }), state.filter).sort(function (a, b) {
      return stepOf(b) - stepOf(a) || inStageDays(b) - inStageDays(a);
    });
    var done = visible(tickets.filter(function (t) { return stepOf(t) >= STEPS.length - 1; }), state.filter).sort(function (a, b) {
      return str(b.done_at || b.closed_at).localeCompare(str(a.done_at || a.closed_at));
    });
    state.byId = {};
    tickets.forEach(function (t) { state.byId[str(t.id)] = t; });

    fill($("openlist"), open.map(function (t) { return rowFor(t, false); }), "Nothing in process.");
    fill($("donelist"), done.map(function (t) { return rowFor(t, true); }), "Nothing closed yet this term.");
    $("n-open").textContent = open.length;
    $("n-done").textContent = done.length;
    $("st-open").textContent = open.length;
    $("st-wait").textContent = open.filter(function (t) { return t.waiting_on; }).length;
    $("st-done").textContent = done.length;
  }

  function fill(container, rows, emptyText) {
    container.replaceChildren.apply(container, rows.length ? rows : [el("div", { class: "empty", text: emptyText })]);
  }

  function updateFresh() {
    var chip = $("fresh");
    if (!state.published) {
      chip.textContent = "";
      chip.hidden = true;
      return;
    }
    chip.hidden = false;
    chip.textContent = "updated " + ago(state.published);
    chip.classList.toggle("stale", Date.now() - state.published.getTime() > STALE_MS);
  }

  function kv(term, value, extra) {
    if (!value) return [];
    return [el("dt", { text: term }), el("dd", null, value, extra ? el("span", { class: "em", text: extra }) : null)];
  }

  function changeItem(c) {
    var from = str(c.from);
    var to = str(c.to);
    var detail = str(c.field) + ": ";
    var line = from ? [detail + from, el("span", { class: "arrow", text: "\u2192" }), to] : [detail + to];
    return el("li", null,
      el("b", { text: str(c.target) }), el("br"), line,
      el("span", { class: "where", text: "Where: " + str(c.where) }),
      c.status ? el("span", { class: "where", text: "Status: " + str(c.status) }) : null
    );
  }

  function openDrawer(t, opener, quiet) {
    var a = $("drawer");
    state.opener = opener || null;
    state.openId = str(t.id);
    var scroll = quiet ? a.scrollTop : 0;
    var changes = Array.isArray(t.changes) ? t.changes : [];
    var messages = Array.isArray(t.messages) ? t.messages : [];
    var history = Array.isArray(t.history) ? t.history : [];
    var closeBtn = el("button", { class: "close", type: "button", id: "cl", text: "Close" });
    var kids = [
      closeBtn,
      el("div", { class: "ref", text: str(t.ref) }),
      el("h3", { text: str(t.title) }),
      str(t.summary) ? el("p", { class: "sum", text: str(t.summary) }) : null,
      track(t),
      el("dl", { class: "kv" },
        kv("Type", str(t.kind)),
        kv("Course", str(t.course)),
        kv("Term", str(t.term_label)),
        kv("Requested by", str(t.requester), str(t.requester_email)),
        kv("Received", fmtDate(t.opened_at)),
        kv(t.closed_at || !t.done_at ? "Closed" : "Done", fmtDate(t.done_at || t.closed_at))
      )
    ];
    if (changes.length) {
      kids.push(el("h4", { text: "What's changing" }), el("ul", { class: "chg" }, changes.map(changeItem)));
    }
    if (messages.length) {
      kids.push(el("h4", { text: "Messages" }), el("ul", { class: "msgs" }, messages.map(function (m) {
        var inbound = m.dir === "in";
        var who = str(m.who);
        var head = [fmtDate(m.at), who ? who + (inbound ? " wrote" : " replied") : ""].filter(Boolean).join(" \u00b7 ");
        return el("li", { class: inbound ? "in" : "out" }, el("small", { text: head }), str(m.excerpt));
      })));
    }
    kids.push(el("h4", { text: "History" }), el("ol", { class: "steps" }, history.map(function (h) {
      var s = h.state === "done" || h.state === "now" ? h.state : "todo";
      var when = fmtDate(h.at);
      var note = s === "done" ? (when ? "done " + when : "done") : s === "now" ? "current step" : "to do";
      return el("li", { class: s }, el("span", null, str(h.label), el("small", { text: note })));
    })));
    a.replaceChildren.apply(a, [].concat.apply([], kids).filter(Boolean));
    a.classList.add("open");
    a.setAttribute("aria-hidden", "false");
    closeBtn.addEventListener("click", closeDrawer);
    a.scrollTop = scroll;
    if (!quiet) closeBtn.focus();
  }

  function closeDrawer() {
    var a = $("drawer");
    if (!a.classList.contains("open")) return;
    a.classList.remove("open");
    a.setAttribute("aria-hidden", "true");
    if (state.opener && state.opener.isConnected) state.opener.focus();
    state.opener = null;
    state.openId = null;
  }

  function showBoard(payload, publishedAt) {
    state.payload = payload;
    state.published = parseDate(payload.generated_at) || parseDate(publishedAt);
    $("lock").hidden = true;
    $("app").hidden = false;
    render();
    startTimers();
  }

  function startTimers() {
    if (timersStarted) return;
    timersStarted = true;
    setInterval(updateFresh, 60000);
    setInterval(function () { if (!document.hidden) refresh(); }, REFRESH_MS);
    document.addEventListener("visibilitychange", function () { if (!document.hidden) refresh(); });
  }

  // kind "pass" shows the passphrase form, "link" shows the (input-less) link message.
  function showLock(kind, message) {
    $("app").hidden = true;
    $("lock").hidden = false;
    $("loaderr").textContent = "";
    $("retry").hidden = true;
    $("passlock").hidden = kind !== "pass";
    $("linklock").hidden = kind !== "link";
    if (kind === "link") $("linkmsg").textContent = message || ERR_LINK_NONE;
    else $("lockerr").textContent = message || "";
  }

  function showLoadError(message) {
    $("passlock").hidden = true;
    $("linklock").hidden = true;
    $("loaderr").textContent = message;
    $("retry").hidden = false;
  }

  function lockOut(message, kind) {
    closeDrawer();
    forgetKey();
    state.key = null;
    state.salt = null;
    state.kid = null;
    showLock(kind, message);
    if (kind === "pass") $("pass").focus();
  }

  function restoreDrawer() {
    if (state.openId === null) return;
    var t = state.byId && state.byId[state.openId];
    if (!t) {
      closeDrawer();
      return;
    }
    var rows = Array.prototype.slice.call(document.querySelectorAll(".row"));
    var row = rows.filter(function (r) { return r.getAttribute("data-id") === state.openId; })[0] || null;
    openDrawer(t, row, true);
  }

  // ---- loading and unlocking -----------------------------------------------------------------

  async function fetchBoard() {
    var res;
    try {
      res = await fetch(ENVELOPE_URL, { cache: "no-store" });
    } catch (e) {
      throw fail("load", ERR_LOAD);
    }
    if (!res.ok) throw fail("load", ERR_LOAD);
    var env;
    try {
      env = await res.json();
    } catch (e) {
      throw fail("load", ERR_LOAD);
    }
    return { env: env, parts: checkEnvelope(env) };
  }

  function acceptPayload(payload, publishedAt) {
    if (!payload || payload.v !== 1) throw fail("format", ERR_FORMAT);
    showBoard(payload, publishedAt);
  }

  // The key is cached as a non-extractable CryptoKey in IndexedDB (structured clone), so script on
  // the page can use it but never read its bytes; the passphrase and the raw link key are never
  // stored. The record is keyed by the envelope's salt (passphrase mode, valid 12 hours) or kid
  // (link mode, no expiry), both fixed until the passphrase or link is rotated, so it stays valid
  // across republishes and stops matching only on rotation.
  function openKeyDb() {
    return new Promise(function (resolve, reject) {
      var idb = globalThis.indexedDB;
      if (!idb) { reject(new Error("IndexedDB is unavailable")); return; }
      var req;
      try {
        req = idb.open(KEY_DB, 1);
      } catch (e) {
        reject(e);
        return;
      }
      req.onupgradeneeded = function () { req.result.createObjectStore(KEY_STORE); };
      req.onsuccess = function () { resolve(req.result); };
      req.onerror = function () { reject(req.error); };
      req.onblocked = function () { reject(new Error("IndexedDB is blocked")); };
    });
  }

  // work(store) returns an object of IDBRequests; resolves to the same keys holding each .result.
  function keyStoreTx(mode, work) {
    return openKeyDb().then(function (db) {
      return new Promise(function (resolve, reject) {
        var tx, reqs;
        try {
          tx = db.transaction(KEY_STORE, mode);
          reqs = work(tx.objectStore(KEY_STORE));
        } catch (e) {
          db.close();
          reject(e);
          return;
        }
        tx.oncomplete = function () {
          db.close();
          var out = {};
          Object.keys(reqs).forEach(function (k) { out[k] = reqs[k].result; });
          resolve(out);
        };
        tx.onerror = tx.onabort = function () {
          db.close();
          reject(tx.error || new Error("key store failed"));
        };
      });
    });
  }

  function rememberKey(id, kind, key) {
    return keyStoreTx("readwrite", function (store) {
      return { cleared: store.clear(), saved: store.put({ id: id, kind: kind, key: key, at: Date.now() }, id) };
    }).catch(function () { /* no IndexedDB or the key cannot be stored: ask for the passphrase next visit */ });
  }

  function forgetKey() {
    return keyStoreTx("readwrite", function (store) {
      return { cleared: store.clear() };
    }).catch(function () { /* ignore */ });
  }

  function usableKey(rec, id, kind) {
    var key = rec && rec.key;
    return !!(rec && rec.id === id && rec.kind === kind && typeof rec.at === "number" && key &&
      globalThis.CryptoKey && key instanceof globalThis.CryptoKey &&
      key.extractable === false && key.algorithm && key.algorithm.name === "AES-GCM" &&
      (kind === "link" || Date.now() - rec.at <= KEY_MAX_AGE_MS));
  }

  async function cachedKey(id, kind) {
    var found;
    try {
      found = await keyStoreTx("readonly", function (store) {
        return { hit: store.get(id), any: store.count() };
      });
    } catch (e) {
      return { key: null, mismatch: false };
    }
    if (!found.hit) return { key: null, mismatch: found.any > 0 };
    if (!usableKey(found.hit, id, kind)) {
      await forgetKey();
      return { key: null, mismatch: false };
    }
    return { key: found.hit.key, mismatch: false };
  }

  function adopt(source, key, payload) {
    acceptPayload(payload, source.env.published_at);
    state.source = source;
    state.key = key;
    state.kdf = source.env.kdf;
    state.salt = source.env.salt;
    state.kid = source.env.kid;
    state.publishedAt = source.env.published_at;
  }

  async function restoreKey(source) {
    var found = await cachedKey(source.env.salt, "pass");
    if (!found.key) {
      if (found.mismatch) {
        await forgetKey();
        $("lockerr").textContent = ERR_ROTATED;
      }
      return false;
    }
    try {
      adopt(source, found.key, JSON.parse(await decryptWithKey(found.key, source.parts)));
      return true;
    } catch (e) {
      await forgetKey();
      $("lockerr").textContent = ERR_ROTATED;
      return false;
    }
  }

  async function unlock(passphrase) {
    var source = await fetchBoard();
    if (source.env.kdf !== KDF_PBKDF2) throw fail("format", ERR_FORMAT);
    state.source = source;
    var key = await deriveKey(passphrase, source.parts.salt, source.env.iter);
    var text;
    try {
      text = await decryptWithKey(key, source.parts);
    } catch (e) {
      throw fail("passphrase", ERR_WRONG);
    }
    adopt(source, key, JSON.parse(text));
    await rememberKey(source.env.salt, "pass", key);
  }

  async function adoptWithKey(source, key) {
    var text;
    try {
      text = await decryptWithKey(key, source.parts);
    } catch (e) {
      throw fail("link", ERR_LINK_OPEN);
    }
    adopt(source, key, JSON.parse(text));
  }

  // The #k= fragment is read, never rewritten or stripped, so the bookmark keeps working.
  function linkKeyText() {
    var parts = String(globalThis.location.hash || "").replace(/^#/, "").split("&");
    for (var i = 0; i < parts.length; i++) {
      if (parts[i].indexOf("k=") === 0) return parts[i].slice(2);
    }
    return null;
  }

  async function openLinkBoard(source) {
    var kid = source.env.kid;
    showLock("link", ERR_LINK_NONE);
    var text = linkKeyText();
    if (text !== null) {
      try {
        var key = await linkKeyFromText(text, kid);
        await adoptWithKey(source, key);
        await rememberKey(kid, "link", key);
      } catch (e) {
        showLock("link", e && e.kind ? e.message : ERR_LINK_OPEN);
      }
      return;
    }
    var found = await cachedKey(kid, "link");
    if (found.key) {
      try {
        await adoptWithKey(source, found.key);
      } catch (e) {
        await forgetKey();
        showLock("link", ERR_LINK_OPEN);
      }
      return;
    }
    if (found.mismatch) {
      await forgetKey();
      showLock("link", ERR_LINK_CHANGED);
      return;
    }
    showLock("link", ERR_LINK_NONE);
  }

  async function refresh() {
    if (state.refreshing || !state.source || $("app").hidden) return;
    var now = Date.now();
    if (now - state.lastCheck < MIN_CHECK_MS) return;
    state.lastCheck = now;
    state.refreshing = true;
    try {
      var source = await fetchBoard();
      var sameKey = source.env.kdf === state.kdf && source.env.salt === state.salt &&
        source.env.kid === state.kid;
      if (sameKey && source.env.published_at === state.publishedAt) return;
      var text = null;
      if (state.key && sameKey) {
        try {
          text = await decryptWithKey(state.key, source.parts);
        } catch (e) {
          text = null;
        }
      }
      if (text === null) {
        // A link-mode board with the same kid that will not decrypt is a torn or stale response:
        // keep showing the current board rather than sending the Chair back to the link.
        if (sameKey && source.env.kdf === KDF_NONE) return;
        state.source = source;
        if (source.env.kdf === KDF_NONE) lockOut(ERR_LINK_CHANGED, "link");
        else lockOut(ERR_ROTATED, "pass");
        return;
      }
      adopt(source, state.key, JSON.parse(text));
      restoreDrawer();
    } catch (e) {
      /* offline or a bad response: keep showing the current board; the freshness chip shows its age */
    } finally {
      state.refreshing = false;
    }
  }

  async function onSubmit(ev) {
    ev.preventDefault();
    var err = $("lockerr");
    var go = $("go");
    err.textContent = "";
    go.disabled = true;
    var label = go.textContent;
    go.textContent = "Opening\u2026";
    try {
      await unlock($("pass").value);
      $("pass").value = "";
    } catch (e) {
      err.textContent = e && e.kind ? e.message : ERR_FORMAT;
      if (e && e.kind === "load") state.source = null;
    } finally {
      go.disabled = false;
      go.textContent = label;
    }
  }

  async function boot() {
    $("lockform").addEventListener("submit", onSubmit);
    $("filters").addEventListener("click", function (ev) {
      var b = ev.target.closest("[data-subject]");
      if (!b) return;
      state.filter = b.getAttribute("data-subject");
      render();
    });
    function onRow(ev) {
      var b = ev.target.closest(".row");
      if (!b) return;
      var t = state.byId && state.byId[b.getAttribute("data-id")];
      if (t) openDrawer(t, b);
    }
    $("openlist").addEventListener("click", onRow);
    $("donelist").addEventListener("click", onRow);
    document.addEventListener("keydown", function (ev) { if (ev.key === "Escape") closeDrawer(); });

    $("retry").addEventListener("click", function () { globalThis.location.reload(); });
    // Pasting a new link into a tab that already shows this page only changes the fragment, which
    // the browser treats as same-page navigation: reload so the new key is read.
    globalThis.addEventListener("hashchange", function () { globalThis.location.reload(); });

    try {
      state.source = await fetchBoard();
    } catch (e) {
      showLoadError(e && e.kind ? e.message : ERR_LOAD);
      return;
    }
    if (state.source.env.kdf === KDF_NONE) {
      await openLinkBoard(state.source);
      return;
    }
    showLock("pass", "");
    await restoreKey(state.source);
  }

  boot();
})();
