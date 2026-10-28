(() => {
"use strict";

/* ---------- text helpers ---------- */
const TOK = /[\p{L}\p{N}’'–-]+|\s+|[^\p{L}\p{N}\s]/gu;
const STOP = new Set("the a an and or but of to in on at for with as by is are was were be been his her he him she it its that this which who whom from into than then so not no if do does did has have had would could should will can there their they them what when where how".split(" "));
const opts = { thr: 0.35, quotes: true, collapse: false, lh: 1.9 };

const normQ = s => s.replace(/[“”„]/g, '"').replace(/[‘’]/g, "'").replace(/[–—]/g, "-");
const tokens = s => s.match(TOK) || [];
const isWord = t => /[\p{L}\p{N}]/u.test(t);
const key = t => /^\s+$/.test(t) ? " " : (opts.quotes ? normQ(t) : t);
const wordsOf = s => (normQ(s).toLowerCase().match(/[\p{L}\p{N}]+/gu) || []);
const wc = s => wordsOf(s).length;
const esc = s => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
const sameText = (a, b) => tokens(a).map(key).join("") === tokens(b).map(key).join("");

function paras(text) {
  return text.replace(/\r/g, "").split(/\n+/).map(s => s.trim()).filter(Boolean);
}

const ABBR = /\b(Mr|Mrs|Ms|Dr|St|Jr|Sr|vs|etc|e\.g|i\.e|cf|ed|pp)\.$/i;
function splitSentences(p) {
  const out = [];
  let start = 0, q = false, qAt = 0;
  for (let i = 0; i < p.length; i++) {
    const c = p[i];
    if (c === '"') { q = !q; qAt = i; }
    else if (c === "“") { q = true; qAt = i; }
    else if (c === "”") q = false;
    if (q && i - qAt > 300) q = false; // unbalanced quote safety
    if (!".!?".includes(c)) continue;
    let j = i + 1, q2 = q;
    while (j < p.length && "\"”’')]".includes(p[j])) {
      if (p[j] === '"' || p[j] === "”") q2 = false;
      j++;
    }
    if (j < p.length && !/\s/.test(p[j])) continue;
    let k = j; while (k < p.length && /\s/.test(p[k])) k++;
    if (k >= p.length) break;
    if (q2) continue;
    if (!/[\p{Lu}\p{N}“"‘(\[]/u.test(p[k])) continue;
    if (c === "." && ABBR.test(p.slice(start, i + 1))) continue;
    out.push(p.slice(start, j).trim());
    start = k; q = false; i = k - 1;
  }
  const tail = p.slice(start).trim();
  if (tail) out.push(tail);
  return out;
}

function lcsLen(a, b) {
  if (!a.length || !b.length) return 0;
  let prev = new Int32Array(b.length + 1), cur = new Int32Array(b.length + 1);
  for (let i = 1; i <= a.length; i++) {
    for (let j = 1; j <= b.length; j++) {
      cur[j] = a[i - 1] === b[j - 1] ? prev[j - 1] + 1 : Math.max(prev[j], cur[j - 1]);
    }
    [prev, cur] = [cur, prev];
  }
  return prev[b.length];
}
const sentSim = (wa, wb) => (wa.length && wb.length) ? 2 * lcsLen(wa, wb) / (wa.length + wb.length) : 0;

function bag(s) {
  const m = new Map(); let n = 0;
  for (const w of wordsOf(s)) { if (STOP.has(w)) continue; m.set(w, (m.get(w) || 0) + 1); n++; }
  return { m, n };
}
function paraSim(A, B) {
  if (!A.n || !B.n) return 0;
  let inter = 0;
  for (const [w, c] of A.m) { const d = B.m.get(w); if (d) inter += Math.min(c, d); }
  return 2 * inter / (A.n + B.n);
}

/* Monotonic alignment: maximise total similarity of matched pairs above a threshold. */
function align(n, m, simFn, thr) {
  const W = m + 1, dp = new Float64Array((n + 1) * W), S = new Float64Array(n * m);
  for (let i = 1; i <= n; i++) for (let j = 1; j <= m; j++) {
    const s = simFn(i - 1, j - 1); S[(i - 1) * m + j - 1] = s;
    let best = Math.max(dp[(i - 1) * W + j], dp[i * W + j - 1]);
    if (s >= thr) best = Math.max(best, dp[(i - 1) * W + j - 1] + s);
    dp[i * W + j] = best;
  }
  const out = []; let i = n, j = m;
  while (i > 0 || j > 0) {
    if (i > 0 && j > 0) {
      const s = S[(i - 1) * m + j - 1];
      if (s >= thr && Math.abs(dp[i * W + j] - (dp[(i - 1) * W + j - 1] + s)) < 1e-9) { out.push({ a: i - 1, b: j - 1, s }); i--; j--; continue; }
    }
    if (i > 0 && (j === 0 || Math.abs(dp[i * W + j] - dp[(i - 1) * W + j]) < 1e-9)) { out.push({ a: i - 1 }); i--; }
    else { out.push({ b: j - 1 }); j--; }
  }
  out.reverse();
  // inside each run of unmatched items, put deletions before insertions
  const res = []; let run = [];
  const flush = () => { res.push(...run.filter(o => o.b == null), ...run.filter(o => o.a == null)); run = []; };
  for (const o of out) { if (o.a != null && o.b != null) { flush(); res.push(o); } else run.push(o); }
  flush();
  return res;
}

/* ---------- word-level diff inside a matched sentence ---------- */
function diffTokens(A, B) {
  const ka = A.map(key), kb = B.map(key), n = A.length, m = B.length, W = m + 1;
  const dp = new Int32Array((n + 1) * W);
  for (let i = n - 1; i >= 0; i--) for (let j = m - 1; j >= 0; j--) {
    dp[i * W + j] = ka[i] === kb[j] ? dp[(i + 1) * W + j + 1] + 1 : Math.max(dp[(i + 1) * W + j], dp[i * W + j + 1]);
  }
  const segs = []; let i = 0, j = 0;
  const pushEq = t => { const l = segs[segs.length - 1]; if (l && l.t === "eq") l.toks.push(t); else segs.push({ t: "eq", toks: [t] }); };
  const chg = () => { const l = segs[segs.length - 1]; if (l && l.t === "chg") return l; const s = { t: "chg", del: [], ins: [] }; segs.push(s); return s; };
  while (i < n || j < m) {
    if (i < n && j < m && ka[i] === kb[j]) { pushEq(B[j]); i++; j++; }
    else if (i < n && (j >= m || dp[(i + 1) * W + j] >= dp[i * W + j + 1])) { chg().del.push(A[i]); i++; }
    else { chg().ins.push(B[j]); j++; }
  }
  return segs;
}
const wcount = toks => toks.filter(isWord).length;
const chgSize = s => Math.max(wcount(s.del), wcount(s.ins));

// Merge short unchanged runs between two changes into one change.
function cleanup(segs) {
  let changed = true;
  while (changed) {
    changed = false;
    for (let k = 1; k < segs.length - 1; k++) {
      const s = segs[k], p = segs[k - 1], nx = segs[k + 1];
      if (s.t !== "eq" || p.t !== "chg" || nx.t !== "chg") continue;
      const w = wcount(s.toks), around = chgSize(p) + chgSize(nx);
      if (w <= 2 || (w <= 4 && w * 3 < around)) {
        p.del.push(...s.toks, ...nx.del);
        p.ins.push(...s.toks, ...nx.ins);
        segs.splice(k, 2); changed = true; break;
      }
    }
  }
  return segs;
}

function renderChg(d, n) {
  let dt = d.join(""), it = n.join(""), lead = "", trail = "";
  if (dt && it) {
    const l1 = dt.match(/^\s*/)[0], l2 = it.match(/^\s*/)[0];
    if (l1 && l2) { lead = " "; dt = dt.slice(l1.length); it = it.slice(l2.length); }
    const t1 = dt.match(/\s*$/)[0], t2 = it.match(/\s*$/)[0];
    if (t1 && t2) { trail = " "; dt = dt.slice(0, dt.length - t1.length); it = it.slice(0, it.length - t2.length); }
  }
  return esc(lead) + (dt ? `<del>${esc(dt)}</del>` : "") + (it ? `<ins>${esc(it)}</ins>` : "") + esc(trail);
}

function wholeReplace(a, b, st) {
  st.del += wc(a); st.ins += wc(b);
  return `<del>${esc(a)}</del> <ins>${esc(b)}</ins>`;
}

function diffSentence(a, b, st) {
  if (sameText(a, b)) return esc(b);
  const segs = cleanup(diffTokens(tokens(a), tokens(b)));
  const eqW = segs.filter(s => s.t === "eq").reduce((x, s) => x + wcount(s.toks), 0);
  if (eqW / Math.max(wc(a), wc(b), 1) < 0.35) return wholeReplace(a, b, st);
  let html = "";
  for (const s of segs) {
    if (s.t === "eq") html += esc(s.toks.join(""));
    else { st.del += wcount(s.del); st.ins += wcount(s.ins); html += renderChg(s.del, s.ins); }
  }
  return html;
}

function diffPara(a, b, st) {
  const SA = splitSentences(a), SB = splitSentences(b);
  const WA = SA.map(wordsOf), WB = SB.map(wordsOf);
  const ops = align(SA.length, SB.length, (i, j) => sentSim(WA[i], WB[j]), opts.thr);
  const parts = []; let pd = [], pi = [];
  const flush = () => {
    if (!pd.length && !pi.length) return;
    const d = pd.join(" "), n = pi.join(" ");
    st.del += wc(d); st.ins += wc(n);
    parts.push((d ? `<del>${esc(d)}</del>` : "") + (d && n ? " " : "") + (n ? `<ins>${esc(n)}</ins>` : ""));
    pd = []; pi = [];
  };
  for (const o of ops) {
    if (o.a != null && o.b != null) { flush(); parts.push(diffSentence(SA[o.a], SB[o.b], st)); }
    else if (o.a != null) pd.push(SA[o.a]);
    else pi.push(SB[o.b]);
  }
  flush();
  return parts.join(" ");
}

/* ---------- whole document ---------- */
function compare(A, B) {
  const PA = paras(A), PB = paras(B);
  const st = { del: 0, ins: 0, changed: 0, total: PB.length };
  if (!PA.length && !PB.length) return { html: "", st };
  const bA = PA.map(bag), bB = PB.map(bag);
  const ops = align(PA.length, PB.length, (i, j) => sameText(PA[i], PB[j]) ? 2 : paraSim(bA[i], bB[j]), 0.25);

  // pick up paragraphs that moved out of order
  const freeOld = new Set(ops.filter(o => o.b == null).map(o => o.a));
  const movedFrom = new Map(), movedTo = new Map();
  for (const o of ops) {
    if (o.a != null) continue;
    let best = -1, bs = 0.35;
    for (const i of freeOld) { const s = sameText(PA[i], PB[o.b]) ? 2 : paraSim(bA[i], bB[o.b]); if (s >= bs) { bs = s; best = i; } }
    if (best >= 0) { freeOld.delete(best); movedFrom.set(o.b, best); movedTo.set(best, o.b); }
  }

  const blocks = [];
  for (const o of ops) {
    if (o.a != null && o.b != null) {
      if (sameText(PA[o.a], PB[o.b])) blocks.push({ k: "same", lbl: `¶${o.b + 1}`, tip: `Paragraph ${o.b + 1}, unchanged`, html: esc(PB[o.b]) });
      else { st.changed++; blocks.push({ k: "chg", lbl: `¶${o.b + 1}`, tip: `Paragraph ${o.b + 1}`, html: diffPara(PA[o.a], PB[o.b], st) }); }
    } else if (o.a != null) {
      if (movedTo.has(o.a)) blocks.push({ k: "note", lbl: "↕", tip: "Moved paragraph", html: `This paragraph moved to ¶ ${movedTo.get(o.a) + 1}.` });
      else { st.del += wc(PA[o.a]); blocks.push({ k: "del", lbl: `<b>−</b>${o.a + 1}`, tip: `Paragraph ${o.a + 1} of the original, deleted`, html: `<del>${esc(PA[o.a])}</del>` }); }
    } else {
      st.changed++;
      if (movedFrom.has(o.b)) {
        const a = PA[movedFrom.get(o.b)];
        blocks.push({ k: "mv", lbl: `¶${o.b + 1}`, tip: `Paragraph ${o.b + 1}, moved here from ¶ ${movedFrom.get(o.b) + 1} of the original`, html: sameText(a, PB[o.b]) ? esc(PB[o.b]) : diffPara(a, PB[o.b], st) });
      } else { st.ins += wc(PB[o.b]); blocks.push({ k: "ins", lbl: `<b>+</b>${o.b + 1}`, tip: `Paragraph ${o.b + 1}, new`, html: `<ins>${esc(PB[o.b])}</ins>` }); }
    }
  }

  const one = b => `<div class="blk k-${b.k}"><div class="lbl" data-tip="${b.tip}">${b.lbl}</div><p class="txt">${b.html}</p></div>`;
  let html = "", run = [];
  const flushSame = () => {
    if (!run.length) return;
    if (opts.collapse) html += `<details class="same"><summary>${run.length} unchanged paragraph${run.length > 1 ? "s" : ""}</summary>${run.map(one).join("")}</details>`;
    else html += run.map(one).join("");
    run = [];
  };
  for (const b of blocks) { if (b.k === "same") run.push(b); else { flushSame(); html += one(b); } }
  flushSame();
  return { html, st };
}

/* ---------- UI ---------- */
const $ = id => document.getElementById(id);
const elOld = $("old"), elNew = $("new"), out = $("out");
const STORE = "track-changes-diff-checker-v2";

function save() {
  try { localStorage.setItem(STORE, JSON.stringify({ old: elOld.value, nw: elNew.value, ...opts })); } catch (e) {}
}
function restore() {
  try {
    const d = JSON.parse(localStorage.getItem(STORE) || "null");
    if (d && (d.old || d.nw)) {
      elOld.value = d.old || ""; elNew.value = d.nw || "";
      if (typeof d.thr === "number") opts.thr = d.thr;
      if (typeof d.quotes === "boolean") opts.quotes = d.quotes;
      if (typeof d.collapse === "boolean") opts.collapse = d.collapse;
      if ([1.6, 1.9, 2.2].includes(d.lh)) opts.lh = d.lh;
      return true;
    }
  } catch (e) {}
  return false;
}
function applySpacing() {
  out.style.setProperty("--lh", opts.lh);
  document.querySelectorAll("#lh-menu [data-lh]").forEach(b => b.setAttribute("aria-checked", +b.dataset.lh === opts.lh));
}
function syncControls() {
  applySpacing();
  $("thr").value = Math.round(opts.thr * 100);
  $("thr-v").textContent = Math.round(opts.thr * 100) + "%";
  $("quotes").checked = opts.quotes;
  $("collapse").checked = opts.collapse;
}

function render() {
  $("c-old").textContent = wc(elOld.value).toLocaleString() + " words";
  $("c-new").textContent = wc(elNew.value).toLocaleString() + " words";
  const { html, st } = compare(elOld.value, elNew.value);
  out.innerHTML = html || `<p class="empty">Paste the original and the revised text to see the changes.</p>`;
  $("stats").innerHTML = html
    ? `<span class="d">−${st.del.toLocaleString()} words</span><span class="i">+${st.ins.toLocaleString()} words</span><span>${st.changed} of ${st.total} paragraphs changed</span>`
    : "";
  save();
}

let timer = 0;
const later = () => { clearTimeout(timer); timer = setTimeout(render, 250); };
elOld.addEventListener("input", later);
elNew.addEventListener("input", later);
$("thr").addEventListener("input", e => { opts.thr = +e.target.value / 100; $("thr-v").textContent = e.target.value + "%"; later(); });
$("quotes").addEventListener("change", e => { opts.quotes = e.target.checked; render(); });
$("collapse").addEventListener("change", e => { opts.collapse = e.target.checked; render(); });
$("b-swap").addEventListener("click", () => { [elOld.value, elNew.value] = [elNew.value, elOld.value]; render(); });
$("b-clear").addEventListener("click", () => { elOld.value = ""; elNew.value = ""; render(); elOld.focus(); });
const lhMenu = $("lh-menu");
function setMenu(open) { lhMenu.hidden = !open; $("b-lh").setAttribute("aria-expanded", open); }
$("b-lh").addEventListener("click", () => setMenu(lhMenu.hidden));
lhMenu.addEventListener("click", e => {
  const b = e.target.closest("[data-lh]"); if (!b) return;
  opts.lh = +b.dataset.lh; applySpacing(); save(); setMenu(false);
});
document.addEventListener("click", e => { if (!e.target.closest(".lh-wrap")) setMenu(false); });
document.addEventListener("keydown", e => { if (e.key === "Escape" && !lhMenu.hidden) { setMenu(false); $("b-lh").focus(); } });

const isDark = () => document.documentElement.dataset.theme
  ? document.documentElement.dataset.theme === "dark"
  : matchMedia("(prefers-color-scheme: dark)").matches;
const SUN = `<svg viewBox="0 0 16 16" width="16" height="16" aria-hidden="true"><g fill="none" stroke="currentColor" stroke-width="1.5" stroke-linecap="round"><circle cx="8" cy="8" r="3"/><path d="M8 1v1.5M8 13.5V15M1 8h1.5M13.5 8H15M3 3l1 1M12 12l1 1M3 13l1-1M12 4l1-1"/></g></svg>`;
const MOON = `<svg viewBox="0 0 16 16" width="16" height="16" aria-hidden="true"><path d="M13.5 9.5A5.5 5.5 0 0 1 6.5 2.5a5.5 5.5 0 1 0 7 7z" fill="none" stroke="currentColor" stroke-width="1.5" stroke-linejoin="round"/></svg>`;
const themeLabel = () => {
  const b = $("b-theme"), label = isDark() ? "Switch to light mode" : "Switch to dark mode";
  b.innerHTML = isDark() ? SUN : MOON;
  b.dataset.tip = label; b.setAttribute("aria-label", label);
};
$("b-theme").addEventListener("click", () => {
  const t = isDark() ? "light" : "dark";
  document.documentElement.dataset.theme = t;
  try { localStorage.setItem("theme", t); } catch (e) {}
  themeLabel();
});
matchMedia("(prefers-color-scheme: dark)").addEventListener("change", themeLabel);
themeLabel();

const ws = document.querySelector(".workspace"), split = $("split");
const SPLIT_DEFAULT = 42;
function setSplit(pct, keep = true) {
  pct = Math.min(75, Math.max(20, pct));
  ws.style.setProperty("--split", pct + "%");
  split.setAttribute("aria-valuenow", Math.round(pct));
  if (keep) try { localStorage.setItem("split", pct); } catch (e) {}
}
split.addEventListener("pointerdown", e => {
  split.setPointerCapture(e.pointerId);
  split.classList.add("drag"); document.body.classList.add("resizing");
});
split.addEventListener("pointermove", e => {
  if (!split.hasPointerCapture(e.pointerId)) return;
  const r = ws.getBoundingClientRect();
  setSplit((e.clientX - r.left) / r.width * 100);
});
const endDrag = () => { split.classList.remove("drag"); document.body.classList.remove("resizing"); };
split.addEventListener("pointerup", endDrag);
split.addEventListener("pointercancel", endDrag);
split.addEventListener("dblclick", () => setSplit(SPLIT_DEFAULT));
split.addEventListener("keydown", e => {
  const step = e.key === "ArrowLeft" ? -2 : e.key === "ArrowRight" ? 2 : 0;
  if (!step) return;
  e.preventDefault();
  setSplit(parseFloat(ws.style.getPropertyValue("--split")) + step);
});
try { setSplit(parseFloat(localStorage.getItem("split")) || SPLIT_DEFAULT, false); } catch (e) { setSplit(SPLIT_DEFAULT, false); }

const tip = document.createElement("div");
tip.className = "tip"; tip.setAttribute("role", "tooltip");
document.body.appendChild(tip);
let tipTimer = 0, tipLast = 0;
function showTip(el) {
  tip.textContent = el.dataset.tip;
  const r = el.getBoundingClientRect(), t = tip.getBoundingClientRect();
  const left = Math.min(Math.max(8, r.left + r.width / 2 - t.width / 2), innerWidth - t.width - 8);
  const below = r.bottom + 6 + t.height <= innerHeight - 8 || innerHeight - r.bottom >= r.top;
  const top = Math.max(8, below ? r.bottom + 6 : r.top - 6 - t.height);
  tip.style.left = left + "px"; tip.style.top = top + "px";
  tip.classList.add("on");
}
function hideTip() { clearTimeout(tipTimer); if (tip.classList.contains("on")) tipLast = Date.now(); tip.classList.remove("on"); }
// Delegated so labels rendered later get tooltips too.
function tipOver(e) {
  const el = e.target.closest("[data-tip]");
  if (!el || el.contains(e.relatedTarget)) return;
  clearTimeout(tipTimer);
  tipTimer = setTimeout(() => showTip(el), Date.now() - tipLast < 400 ? 0 : 450);
}
function tipOut(e) {
  const el = e.target.closest("[data-tip]");
  if (el && !el.contains(e.relatedTarget)) hideTip();
}
document.addEventListener("mouseover", tipOver);
document.addEventListener("focusin", tipOver);
document.addEventListener("mouseout", tipOut);
document.addEventListener("focusout", tipOut);
document.addEventListener("pointerdown", hideTip);

function toast(msg) { $("toast").textContent = msg; clearTimeout(toast.t); toast.t = setTimeout(() => $("toast").textContent = "", 4000); }

$("b-copy").addEventListener("click", async () => {
  const clone = out.cloneNode(true);
  clone.querySelectorAll("details").forEach(d => { d.querySelector("summary")?.remove(); d.replaceWith(...d.childNodes); });
  clone.querySelectorAll(".lbl").forEach(x => x.remove());
  clone.querySelectorAll(".k-note").forEach(x => x.remove());
  clone.querySelectorAll("del").forEach(x => x.setAttribute("style", "background:#ffdddd;color:#b30000;text-decoration:line-through"));
  clone.querySelectorAll("ins").forEach(x => x.setAttribute("style", "background:#d4edda;color:#155724;text-decoration:none"));
  const ps = [...clone.querySelectorAll("p.txt")];
  if (!ps.length) { toast("Nothing to copy yet."); return; }
  const html = ps.map(p => `<p style="font-family:Georgia,serif;line-height:1.6">${p.innerHTML}</p>`).join("");
  const text = ps.map(p => p.textContent).join("\n\n");
  try {
    await navigator.clipboard.write([new ClipboardItem({
      "text/html": new Blob([html], { type: "text/html" }),
      "text/plain": new Blob([text], { type: "text/plain" })
    })]);
    toast("Copied. Paste into Google Docs and the colors come with it.");
  } catch (e) {
    const box = document.createElement("div");
    box.contentEditable = "true"; box.innerHTML = html;
    box.style.cssText = "position:fixed;left:-9999px;top:0";
    document.body.appendChild(box);
    const r = document.createRange(); r.selectNodeContents(box);
    const sel = getSelection(); sel.removeAllRanges(); sel.addRange(r);
    let ok = false; try { ok = document.execCommand("copy"); } catch (e2) {}
    sel.removeAllRanges(); box.remove();
    toast(ok ? "Copied. Paste into Google Docs and the colors come with it." : "Copy was blocked. Select the changes and copy them manually.");
  }
});

restore();
syncControls();
render();
})();
