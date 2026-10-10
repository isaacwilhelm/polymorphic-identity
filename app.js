// Results explorer for the logic of polymorphic identity.
// Reasoning: unit propagation over the clauses given by data.js (sound, not complete),
// plus the models in data.js as witnesses of non-derivability and consistency.

(function () {
  const D = window.PIDATA;
  const P = Object.fromEntries(D.principles.map(p => [p.id, p]));
  const tag = id => P[id].tag;
  const lit = (id, pos) => (pos ? id : "¬" + id);   // literal key
  const litText = (id, pos) => (pos ? tag(id) : "¬" + tag(id));

  // ------------------------------------------------------------------ clauses
  // A clause is a disjunction of literals [{id, pos}], with a source.
  const clauses = [];
  D.pimTheorems.forEach(t => clauses.push({ lits: [{ id: t.to, pos: true }], kind: "thm", info: t }));
  D.rules.forEach(r => clauses.push({
    lits: r.from.map(id => ({ id, pos: false })).concat([{ id: r.to, pos: true }]), kind: "rule", info: r }));
  D.inconsistent.forEach(s => clauses.push({ lits: s.set.map(id => ({ id, pos: false })), kind: "incons", info: s }));

  // Unit propagation. `start` is a list of {id, pos, why}. Returns {val, why, conflict}.
  function propagate(start) {
    const val = {}, why = {};
    let conflict = null;
    const assign = (id, pos, reason) => {
      if (id in val) {
        if (val[id] !== pos && !conflict) conflict = { id, reason, other: why[id] };
        return false;
      }
      val[id] = pos; why[id] = reason; return true;
    };
    start.forEach(s => assign(s.id, s.pos, s.why));
    let changed = true;
    while (changed && !conflict) {
      changed = false;
      for (const c of clauses) {
        let unassigned = null, nUn = 0, sat = false;
        for (const l of c.lits) {
          if (!(l.id in val)) { nUn++; unassigned = l; }
          else if (val[l.id] === l.pos) { sat = true; break; }
        }
        if (sat) continue;
        const used = c.lits.filter(l => l.id in val).map(l => ({ id: l.id, pos: val[l.id] }));
        if (nUn === 0) { conflict = { clause: c, used }; break; }
        if (nUn === 1) {
          assign(unassigned.id, unassigned.pos, { clause: c, used });
          changed = true;
        }
      }
    }
    return { val, why, conflict };
  }

  // ------------------------------------------------------------------ models (filled in by propagation)
  const models = D.models.map(m => {
    const start = Object.entries(m.values).map(([id, v]) =>
      ({ id, pos: v[0], why: { model: true, src: v[1], added: !!v[2] } }));
    const r = propagate(start);
    if (r.conflict) console.error("Model " + m.id + " conflicts with the rules:", r.conflict);
    return Object.assign({}, m, { val: r.val, why: r.why });
  });

  // ------------------------------------------------------------------ state
  // sel: id -> true (assumed) | false (negation assumed)
  const state = { logic: "PI", sel: {}, focus: null, opened: [], showThms: false, sortMode: "subject" };
  try { const m = localStorage.getItem("pi-sortmode2"); if (["topic", "dims", "subject"].includes(m)) state.sortMode = m; } catch (e) {}
  try { state.showThms = localStorage.getItem("pi-showthms") === "1"; } catch (e) {}

  function readHash() {
    const h = decodeURIComponent(location.hash.replace(/^#/, ""));
    if (!h) return;
    const parts = h.split(",").filter(Boolean);
    state.sel = {};
    state.logic = "PI";
    parts.forEach(p => {
      if (p === "PI-") state.logic = "PI-";
      else if (p === "PI") state.logic = "PI";
      else if (p === "PIC") state.logic = "PIC";
      else if (p.startsWith("!") && P[p.slice(1)]) state.sel[p.slice(1)] = false;
      else if (P[p]) state.sel[p] = true;
    });
  }
  function writeHash() {
    const parts = [state.logic].concat(Object.entries(state.sel).map(([id, v]) => (v ? id : "!" + id)));
    history.replaceState(null, "", "#" + encodeURIComponent(parts.join(",")).replace(/%2C/g, ","));
  }

  function assumptions() {
    const a = Object.entries(state.sel).map(([id, pos]) => ({ id, pos, why: { assumed: true } }));
    if (state.logic === "PI" || state.logic === "PIC") {
      const baseIds = state.logic === "PIC" ? ["LLeq", "Class"] : ["LLeq"];
      a.splice(0, a.length, ...a.filter(x => !baseIds.includes(x.id)));
      baseIds.slice().reverse().forEach(id => a.unshift({ id, pos: true, why: { assumed: true, base: true } }));
    }
    return a;
  }
  const isLocked = id => (state.logic === "PI" && id === "LLeq") || (state.logic === "PIC" && (id === "LLeq" || id === "Class"));
  const logicName = () => (state.logic === "PIC" ? "PIᶜ" : state.logic === "PI" ? "PI" : "PI⁻");

  // ------------------------------------------------------------------ analysis
  function modelSatisfies(m, lits) {
    return lits.every(l => m.val[l.id] === l.pos);
  }

  function analyse() { return analyseWith(assumptions()); }
  function analyseWith(A) {
    const base = propagate(A);
    const out = { A, base, status: {} };
    if (base.conflict) { out.inconsistent = true; return out; }
    const assumedIds = new Set(A.map(a => a.id));
    for (const p of D.principles) {
      if (assumedIds.has(p.id)) continue;
      const s = { id: p.id };
      if (base.val[p.id] === true) { s.kind = "follows"; s.proof = { res: base, target: p.id }; }
      else if (base.val[p.id] === false) { s.kind = "refuted"; s.proof = { res: base, target: p.id }; }
      else {
        const withNeg = propagate(A.concat([{ id: p.id, pos: false, why: { hyp: true } }]));
        const withPos = propagate(A.concat([{ id: p.id, pos: true, why: { hyp: true } }]));
        if (withNeg.conflict) { s.kind = "follows"; s.refutation = withNeg; }
        else if (withPos.conflict) { s.kind = "refuted"; s.refutation = withPos; }
        else {
          s.counter = models.find(m => modelSatisfies(m, A) && m.val[p.id] === false);
          s.witness = models.find(m => modelSatisfies(m, A) && m.val[p.id] === true);
          s.kind = s.counter && s.witness ? "independent"
                 : s.witness ? "consistent"
                 : s.counter ? "notderivable" : "open";
        }
      }
      out.status[p.id] = s;
    }
    return out;
  }

  // ------------------------------------------------------------------ explanations
  const LEANBASE = "https://github.com/isaacwilhelm/polymorphic-identity/blob/main/lean/";
  function leanURL(name) {
    const e = (window.LEANINDEX || {})[name];
    return e ? `${LEANBASE}${e[0]}#L${e[1]}` : null;
  }
  function leanBadge(name, label) {
    const u = name && leanURL(name);
    if (!u) return "";
    return `<a class="leanb" href="${u}" target="_blank" rel="noopener" title="Checked in Lean: PIF.${name}">${label || "Lean ✓"}</a>`;
  }
  // Where a result was first recorded is not shown on the site.
  function srcBadge() { return ""; }
  function describeClause(c) {
    const i = c.info;
    if (c.kind === "thm") return `PI⁻ proves ${tag(i.to)}`;
    if (c.kind === "rule") return `${i.from.map(tag).join(" + ")} ⊢ ${tag(i.to)}`;
    return `${i.set.map(tag).join(" + ")} are jointly inconsistent`;
  }
  function stepHTML(id, pos, reason) {
    if (!reason) return "";
    if (reason.assumed) return "";
    if (reason.hyp) return `<li><b>${litText(id, pos)}</b> <span class="by">supposed, for reductio</span></li>`;
    const c = reason.clause;
    const used = reason.used.map(u => litText(u.id, u.pos)).join(", ");
    let how;
    if (c.kind === "thm") how = "a theorem of PI⁻";
    else if (c.kind === "rule" && pos && c.info.to === id) how = `from ${used}`;
    else if (c.kind === "rule") how = `from ${used}, by contraposition of ${describeClause(c)}`;
    else how = `from ${used}, since ${describeClause(c)}`;
    const note = c.info.note ? `<div class="stepnote">${c.info.note}</div>` : "";
    return `<li><b>${litText(id, pos)}</b> <span class="by">${how}</span> ${srcBadge(c.info.src, c.info.added)} ${leanBadge(c.info.lean)}${note}</li>`;
  }
  // Collect the steps that lead to the given literals, in order.
  function traceSteps(res, roots) {
    const seen = new Set(), steps = [];
    const visit = (id) => {
      if (seen.has(id)) return;
      seen.add(id);
      const r = res.why[id];
      if (r && r.used) r.used.forEach(u => visit(u.id));
      steps.push(stepHTML(id, res.val[id], r));
    };
    roots.forEach(visit);
    return steps.filter(Boolean);
  }
  function proofHTML(res, target) {
    const steps = traceSteps(res, [target]);
    return `<ol class="steps">${steps.join("")}</ol>`;
  }
  function refutationHTML(res) {
    const c = res.conflict;
    let roots, last;
    if (c.clause) {
      roots = c.used.map(u => u.id);
      last = `<li class="contra"><b>⊥</b> <span class="by">since ${describeClause(c.clause)}</span> ${srcBadge(c.clause.info.src, c.clause.info.added)} ${leanBadge(c.clause.info.lean)}${c.clause.info.note ? `<div class="stepnote">${c.clause.info.note}</div>` : ""}</li>`;
    } else {
      roots = [c.id];
      if (c.reason && c.reason.used) roots = roots.concat(c.reason.used.map(u => u.id));
      const pos = res.val[c.id];
      last = stepHTML(c.id, !pos, c.reason) + `<li class="contra"><b>⊥</b> <span class="by">since both ${tag(c.id)} and ¬${tag(c.id)} have been reached</span></li>`;
    }
    return `<ol class="steps">${traceSteps(res, roots).join("")}${last}</ol>`;
  }
  function modelHTML(m, id) {
    const w = m.why[id];
    let reason;
    if (w && w.model) reason = "by the construction of the model";
    else if (w) reason = `follows in the model: ${w.used.map(u => litText(u.id, u.pos)).join(", ")} with ${describeClause(w.clause)} ${srcBadge(w.clause.info.src, w.clause.info.added)}`;
    const assumed = assumptions().map(a => litText(a.id, a.pos)).join(", ");
    const lv = w && w.model && m.lean ? leanBadge(m.lean[id]) : "";
    const lm = m.lean ? leanBadge(m.lean.model, "Lean ✓ model") : "";
    const ln = m.leanNote ? `<div class="mline subtle">Lean: ${m.leanNote}</div>` : "";
    return `<div class="model"><div class="mname">${m.name} ${lm}</div><div class="mdesc">${m.desc}</div>
      <div class="mline">Here ${tag(id)} is <b>${m.val[id] ? "true" : "false"}</b> — ${reason} ${lv}</div>
      <div class="mline subtle">and every assumption (${assumed || "PI⁻"}) is true.</div>${ln}</div>`;
  }

  const KIND = {
    follows:      { label: "Follows", cls: "k-follows", desc: "derivable from the selection" },
    independent:  { label: "Independent", cls: "k-indep", desc: "consistent with the selection, but not derivable from it" },
    consistent:   { label: "Consistent", cls: "k-cons", desc: "consistent with the selection; whether it follows is open" },
    notderivable: { label: "Does not follow", cls: "k-notder", desc: "not derivable; whether it is consistent with the selection is open" },
    refuted:      { label: "Inconsistent", cls: "k-refuted", desc: "inconsistent with the selection (its negation follows)" },
    open:         { label: "Open", cls: "k-open", desc: "not settled by the results recorded here" },
  };
  const ORDER = ["follows", "independent", "consistent", "notderivable", "open", "refuted"];

  // ------------------------------------------------------------------ rendering: checklist
  const $ = s => document.querySelector(s);
  function tex(s, display) {
    try { return katex.renderToString(s, { displayMode: !!display, throwOnError: false, trust: true, strict: false, macros: MACROS }); }
    catch (e) { return s; }
  }
  const MACROS = { "\\TA": "\\htmlClass{tq}{\\mathbb{A}}", "\\TE": "\\htmlClass{tq}{\\mathbb{E}}" };

  // How many open principles a set of assumptions settles, in a given logic.
  function settleScore(logic, ids) {
    const saved = { logic: state.logic, sel: state.sel };
    state.logic = logic; state.sel = {};
    try {
      const base = analyse();
      const kind = (an, b) => an.status[b] ? an.status[b].kind : "";
      const cand = D.principles.filter(p => p.group !== "The logic" && !p.theorem && !["follows", "refuted"].includes(kind(base, p.id))).map(p => p.id);
      const an = analyseWith(base.A.concat(ids.map(id => ({ id, pos: true, why: { assumed: true } }))));
      if (an.inconsistent) return null;
      const rest = cand.filter(b => !ids.includes(b));
      return { n: rest.filter(b => ["follows", "refuted"].includes(kind(an, b))).length, m: rest.length };
    } finally { state.logic = saved.logic; state.sel = saved.sel; }
  }

  let checklistLogic = null;
  function checklistGroups() {
    const shown = D.principles.filter(p => p.group !== "The logic" && !p.theorem);
    const byId = Object.fromEntries(shown.map(p => [p.id, p]));
    if (state.sortMode === "topic") {
      const groups = [];
      shown.forEach(p => {
        let g = groups.find(g => g.name === p.group);
        if (!g) groups.push(g = { name: p.group, items: [] });
        g.items.push(p);
      });
      return groups;
    }
    const spec = D.sortings[state.sortMode === "subject" ? "subject" : "dims"];
    const used = new Set();
    const groups = spec.map(g => {
      const plain = g.ids.filter(id => byId[id]).map(id => (used.add(id), byId[id]));
      const modal = (g.modal || []).filter(id => byId[id]).map(id => (used.add(id), byId[id]));
      return { name: g.name, items: plain.concat(modal), sep: modal.length && state.sortMode === "subject" ? plain.length : -1 };
    });
    const rest = shown.filter(p => !used.has(p.id));
    if (rest.length) groups.push({ name: "Other", items: rest });
    if (state.sortMode === "power") {
      groups.forEach(g => {
        g.items.forEach(p => { const sc = settleScore(state.logic, [p.id]); p._power = sc ? sc.n : -1; });
        g.items.sort((a, b) => b._power - a._power);
      });
    }
    return groups;
  }

  function renderChecklist() {
    const box = $("#checklist");
    checklistLogic = state.logic;
    const groups = checklistGroups();
    box.innerHTML = groups.map(g => `
      <div class="group"><div class="gname">${g.name}</div>
      ${g.items.map((p, i) => `${i === g.sep ? `<div class="msep" title="Principles stated with □">modal principles</div>` : ""}
        <div class="item" data-id="${p.id}">
          <div class="tri" role="radiogroup" aria-label="${p.tag}">
            <button class="t-yes" data-v="yes" title="Assume ${p.tag}" aria-label="Assume ${p.tag}">✓</button>
            <button class="t-no" data-v="no" title="Assume the negation of ${p.tag}" aria-label="Assume not ${p.tag}">¬</button>
          </div>
          <button class="pname" title="Show details">${p.tag}</button>
          ${state.sortMode === "power" && p._power > 0 ? `<span class="power" title="Open principles settled by adding ${p.tag} alone, in ${logicName()}">${p._power}</span>` : ""}
        </div>`).join("")}
      </div>`).join("");
    box.querySelectorAll(".item").forEach(el => {
      const id = el.dataset.id;
      el.querySelectorAll(".tri button").forEach(b => b.addEventListener("click", () => {
        if (isLocked(id)) return;
        const want = b.dataset.v === "yes";
        if (state.sel[id] === want) delete state.sel[id]; else state.sel[id] = want;
        state.focus = state.focus === id ? null : state.focus;
        update();
      }));
      el.querySelector(".pname").addEventListener("click", () => {
        if (!$("#strength").hidden) { strengthFocus = id; renderStrength(); } else openPrinciple(id);
      });
    });
  }
  function syncChecklist() {
    document.querySelectorAll("#checklist .item").forEach(el => {
      const id = el.dataset.id;
      const v = isLocked(id) ? true : state.sel[id];
      el.classList.toggle("on-yes", v === true);
      el.classList.toggle("on-no", v === false);
      el.classList.toggle("locked", isLocked(id));
      el.classList.toggle("focus", state.focus === id);
      el.querySelector(".t-yes").setAttribute("aria-pressed", v === true);
      el.querySelector(".t-no").setAttribute("aria-pressed", v === false);
      el.querySelector(".t-yes").title = isLocked(id) ? (id === "Class" ? "Classicism is part of PIᶜ. Switch to PI or PI⁻ to drop it." : "LL≡ is an axiom of " + logicName() + ". Switch to PI⁻ to drop it.") : "Assume " + tag(id);
    });
    document.querySelectorAll(".logic button[data-logic]").forEach(b => b.setAttribute("aria-pressed", b.dataset.logic === state.logic));
  }

  // ------------------------------------------------------------------ rendering: graph
  const NS = "http://www.w3.org/2000/svg";
  let W, H, CX, CY, RX, RY;
  function setDims() {
    const narrow = (svg.parentNode.clientWidth || window.innerWidth) < 640;
    [W, H, RX, RY] = narrow ? [420, 800, 148, 340] : [1000, 700, 400, 280];
    CX = W / 2; CY = H / 2;
    svg.setAttribute("viewBox", `0 0 ${W} ${H}`);
    // Sample the ellipse, measuring length in "node units": labels are ~90 wide and ~34 tall,
    // so equal steps in this metric keep neighbouring nodes from overlapping in either direction.
    ring = []; let acc = 0, px = null, py = null;
    for (let i = 0; i <= 1440; i++) {
      const a = -Math.PI / 2 + (2 * Math.PI * i) / 1440;
      const x = CX + RX * Math.cos(a), y = CY + RY * Math.sin(a);
      if (px !== null) acc += Math.hypot((x - px) / 90, (y - py) / 34);
      ring.push({ x, y, s: acc }); px = x; py = y;
    }
    return narrow;
  }
  let ring = [];
  function ringPoint(f) {
    const target = f * ring[ring.length - 1].s;
    let lo = 0, hi = ring.length - 1;
    while (lo < hi) { const mid = (lo + hi) >> 1; if (ring[mid].s < target) lo = mid + 1; else hi = mid; }
    return ring[lo];
  }
  const nodeEls = {};
  let svg, edgeLayer, nodeLayer, hubG;

  function el(name, attrs, parent) {
    const e = document.createElementNS(NS, name);
    for (const k in attrs) e.setAttribute(k, attrs[k]);
    if (parent) parent.appendChild(e);
    return e;
  }
  function initGraph() {
    svg = $("#graph");
    setDims();
    const defs = el("defs", {}, svg);
    [["follows", "var(--c-follows)"], ["refuted", "var(--c-refuted)"], ["indep", "var(--c-indep)"], ["cons", "var(--c-cons)"]].forEach(([k, c]) => {
      const m = el("marker", { id: "arr-" + k, viewBox: "0 0 10 10", refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: "auto-start-reverse" }, defs);
      el("path", { d: "M0,0 L10,5 L0,10 z", fill: c }, m);
    });
    edgeLayer = el("g", { class: "edges" }, svg);
    hubG = el("g", { class: "hub" }, svg);
    nodeLayer = el("g", { class: "nodes" }, svg);
    D.principles.forEach(p => {
      const g = el("g", { class: "node", tabindex: 0, role: "button", "aria-label": p.tag }, nodeLayer);
      const r = el("rect", { rx: 13, ry: 13, height: 26 }, g);
      const t = el("text", { "text-anchor": "middle", y: 4.5 }, g);
      t.textContent = p.tag;
      const edge = el("path", { class: "edge" }, edgeLayer);
      g.addEventListener("click", () => openPrinciple(p.id));
      g.addEventListener("keydown", e => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); openPrinciple(p.id); } });
      g.addEventListener("mouseenter", () => { g.classList.add("hover"); edge.classList.add("hover"); });
      g.addEventListener("mouseleave", () => { g.classList.remove("hover"); edge.classList.remove("hover"); });
      nodeEls[p.id] = { g, r, t, edge, x: CX, y: CY };
    });
    let narrow = setDims();
    window.addEventListener("resize", () => {
      const was = narrow; narrow = setDims();
      if (was !== narrow) { D.principles.forEach(p => { nodeEls[p.id].x = CX; nodeEls[p.id].y = CY; }); update(); }
    });
  }

  function hubBox(lines) {
    const w = Math.max(150, ...lines.map(l => l.length * 7.4 + 30));
    const h = 26 + lines.length * 19;
    return { w, h, x: CX - w / 2, y: CY - h / 2 };
  }

  // Place a node at (x, y) and draw its edge from the hub's border to the node's border.
  function place(ne, x, y, hb) {
    ne.x = x; ne.y = y;
    ne.g.setAttribute("transform", `translate(${x.toFixed(1)},${y.toFixed(1)})`);
    const dx = x - CX, dy = y - CY;
    const tHub = Math.min((hb.w / 2 + 4) / Math.abs(dx || 1e-9), (hb.h / 2 + 4) / Math.abs(dy || 1e-9));
    const tNode = 1 - Math.min((ne.w / 2 + 3) / Math.abs(dx || 1e-9), 16 / Math.abs(dy || 1e-9));
    const show = ["follows", "independent", "consistent", "refuted"].includes(ne.kind) && tNode > tHub;
    ne.edge.setAttribute("d", show
      ? `M${(CX + dx * tHub).toFixed(1)},${(CY + dy * tHub).toFixed(1)} L${(CX + dx * tNode).toFixed(1)},${(CY + dy * tNode).toFixed(1)}`
      : "");
  }
  let animId = 0;
  function animate(pos, hb) {
    const id = ++animId, t0 = performance.now(), dur = 450;
    const reduce = window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches;
    const step = now => {
      if (id !== animId) return;
      let k = reduce || document.hidden ? 1 : Math.min(1, (now - t0) / dur);
      const e = k < 0.5 ? 2 * k * k : 1 - Math.pow(-2 * k + 2, 2) / 2;
      for (const pid in pos) {
        const q = pos[pid];
        place(nodeEls[pid], q.x0 + (q.x1 - q.x0) * e, q.y0 + (q.y1 - q.y0) * e, hb);
      }
      if (k < 1) requestAnimationFrame(step);
    };
    if (document.hidden) step(t0 + dur); else { requestAnimationFrame(step); setTimeout(() => step(t0 + dur + 1), dur + 150); }
  }

  function renderGraph(an) {
    // hub
    hubG.innerHTML = "";
    const lines = an.A.filter(a => !(a.why.base && a.id === "Class"))
      .map(a => (a.why.base ? (state.logic === "PIC" ? "PIᶜ (= PI + Classicism)" : "PI (= PI⁻ + LL≡)") : litText(a.id, a.pos)));
    if (state.logic === "PI-") lines.unshift("PI⁻");
    const hb = hubBox(lines);
    el("rect", { x: hb.x, y: hb.y, width: hb.w, height: hb.h, rx: 10, class: an.inconsistent ? "hubrect bad" : "hubrect" }, hubG);
    lines.forEach((l, i) => {
      const t = el("text", { x: CX, y: hb.y + 22 + i * 19, "text-anchor": "middle", class: i === 0 ? "hubtitle" : "" }, hubG);
      t.textContent = l;
    });

    // targets placed around an ellipse, grouped by status
    const assumed = new Set(an.A.map(a => a.id));
    // theorems of the base logic are shown only on request
    if (!state.showThms) {
      const baseAn = analyseWith(an.A.filter(a => a.why.base));
      if (!baseAn.inconsistent) Object.entries(baseAn.status).forEach(([id, st]) => { if (st.kind === "follows") assumed.add(id); });
    }
    const targets = D.principles.filter(p => !assumed.has(p.id));
    const groupOf = id => an.inconsistent ? "none" : an.status[id].kind;
    const sorted = an.inconsistent ? targets
      : targets.slice().sort((a, b) => ORDER.indexOf(groupOf(a.id)) - ORDER.indexOf(groupOf(b.id)));
    const n = sorted.length;
    const gap = 0.5;                         // extra slots between status groups
    let slots = 0, prev = null;
    const slotOf = sorted.map(p => { const g = groupOf(p.id); if (prev !== null && g !== prev) slots += gap; prev = g; return slots++; });
    const total = Math.max(slots + (n > 1 ? gap : 0), 1);

    const targetsPos = {};
    D.principles.forEach(p => {
      const ne = nodeEls[p.id];
      if (assumed.has(p.id)) { ne.g.style.display = "none"; ne.edge.style.display = "none"; ne.hidden = true; return; }
      if (ne.hidden) { ne.x = CX; ne.y = CY; }   // re-entering nodes grow out of the hub
      ne.hidden = false;
      ne.g.style.display = ""; ne.edge.style.display = "";
      const i = sorted.indexOf(p);
      const pt = ringPoint((slotOf[i] + 0.5) / total);
      const w = Math.max(54, p.tag.length * 8.2 + 22);
      ne.w = w;
      ne.r.setAttribute("width", w); ne.r.setAttribute("x", -w / 2); ne.r.setAttribute("y", -13);
      const kind = an.inconsistent ? "none" : an.status[p.id].kind;
      ne.kind = kind;
      ne.g.setAttribute("class", "node " + (KIND[kind] ? KIND[kind].cls : "k-none") + (state.focus === p.id ? " focus" : ""));
      ne.edge.setAttribute("class", "edge " + (KIND[kind] ? KIND[kind].cls : "") + (state.focus === p.id ? " focus" : ""));
      const mk = { follows: "follows", refuted: "refuted", independent: "indep", consistent: "cons" }[kind];
      if (mk) ne.edge.setAttribute("marker-end", `url(#arr-${mk})`); else ne.edge.removeAttribute("marker-end");
      targetsPos[p.id] = { x0: ne.x, y0: ne.y, x1: pt.x, y1: pt.y };
    });
    animate(targetsPos, hb);

    // summary counts
    const counts = {};
    if (!an.inconsistent) Object.entries(an.status).forEach(([id, s]) => { if (!assumed.has(id)) counts[s.kind] = (counts[s.kind] || 0) + 1; });
    $("#legend").innerHTML = ORDER.map(k => `
      <span class="lg ${KIND[k].cls}" title="${KIND[k].desc}"><svg width="34" height="10" aria-hidden="true"><line x1="1" y1="5" x2="33" y2="5"/></svg>${KIND[k].label}<b>${counts[k] || 0}</b></span>`).join("");
    $("#banner").innerHTML = an.inconsistent
      ? `<div class="bad"><b>The selected principles are jointly inconsistent.</b> ${refutationHTML(an.base)}</div>` : "";
  }

  // ------------------------------------------------------------------ rendering: details
  function openPrinciple(id) {
    state.focus = id;
    state.opened = [id].concat(state.opened.filter(x => x !== id));
    update();
    scrollToDetails();
  }
  // One box per principle clicked on (newest first), then the axioms of the base logic.
  function renderDetails(an) {
    const box = $("#details");
    box.innerHTML = "";
    state.opened.forEach(id => box.appendChild(principleCard(an, id)));
    const lc = document.createElement("div");
    lc.className = "details logiccard";
    lc.innerHTML = (state.opened.length ? "" : `<div class="hint">Click any principle (in the list or the graph) to see its statement and <em>why</em> it has the status shown: the derivation, or the model that shows it does not follow. Each principle you click on gets its own box here.</div>`) +
      `<div class="dhead"><h3>The axioms of ${logicName()}</h3><button class="linkbtn" type="button">Axioms and rules common to all three logics</button></div>` +
      identityHTML(state.logic);
    lc.querySelector(".linkbtn").addEventListener("click", openCommon);
    box.appendChild(lc);
  }
  function principleCard(an, id) {
    const card = document.createElement("div");
    card.className = "details" + (state.focus === id ? " current" : "");
    const p = P[id];
    const assumedLit = an.A.find(a => a.id === id);
    let body;
    if (assumedLit) {
      body = `<p class="st">${assumedLit.why.base ? "An axiom of PI." : "Currently " + (assumedLit.pos ? "assumed." : "assumed false (its negation is assumed).")}</p>`;
    } else if (an.inconsistent) {
      body = `<p class="st">The selection is inconsistent, so everything follows from it.</p>`;
    } else {
      const s = an.status[id];
      const k = KIND[s.kind];
      body = `<p class="st"><span class="pill ${k.cls}">${k.label}</span> ${k.desc}.</p>`;
      if (s.kind === "follows") {
        body += `<h4>Derivation</h4>` + (s.proof ? proofHTML(s.proof.res, id) : refutationHTML(s.refutation));
      } else if (s.kind === "refuted") {
        body += `<h4>Why it is inconsistent with the selection</h4>` + (s.proof ? proofHTML(s.proof.res, id) : refutationHTML(s.refutation));
      } else {
        if (s.counter) body += `<h4>Does not follow: a countermodel</h4>` + modelHTML(s.counter, id);
        if (s.witness) body += `<h4>Consistent: a model</h4>` + modelHTML(s.witness, id);
        if (!s.counter) body += `<p class="openq">No model recorded here shows that ${p.tag} fails while the selection holds.</p>`;
        if (!s.witness) body += `<p class="openq">No model recorded here shows ${p.tag} true together with the selection.</p>`;
      }
    }
    const lock = isLocked(id);
    const cur = state.sel[id];
    card.innerHTML = `
      <div class="dhead"><h3>${p.tag}</h3><span class="dgroup">${p.group}</span><button class="dclose" aria-label="Close ${p.tag}" title="Close">✕</button></div>
      <div class="formula">${tex(p.tex, true)}</div>
      <p class="gloss">${p.gloss} ${p.lean ? leanBadge(p.lean, "Lean definition") : ""}</p>
      ${body}
      <div class="dactions">
        <button data-a="yes" ${lock ? "disabled" : ""} aria-pressed="${cur === true || lock}">${cur === true ? "Stop assuming it" : "Assume it"}</button>
        <button data-a="no" ${lock ? "disabled" : ""} aria-pressed="${cur === false}">${cur === false ? "Stop assuming its negation" : "Assume its negation"}</button>
      </div>`;
    card.querySelector(".dclose").addEventListener("click", () => {
      state.opened = state.opened.filter(x => x !== id);
      if (state.focus === id) state.focus = state.opened[0] || null;
      update();
    });
    card.querySelectorAll(".dactions button").forEach(b => b.addEventListener("click", () => {
      const want = b.dataset.a === "yes";
      if (state.sel[id] === want) delete state.sel[id]; else state.sel[id] = want;
      update();
    }));
    return card;
  }
  function scrollToDetails() {
    if (window.innerWidth < 900) $("#details").scrollIntoView({ behavior: "smooth", block: "start" });
  }

  // ------------------------------------------------------------------ strength tab (Hasse diagram)
  // Sources (theorem numbers) used in a derivation or refutation.
  function sourcesOf(s) {
    const res = s.proof ? s.proof.res : s.refutation;
    const clausesUsed = [], seen = new Set();
    const visit = id => {
      if (seen.has(id)) return; seen.add(id);
      const w = res.why[id];
      if (w && w.clause) { clausesUsed.push(w.clause); w.used.forEach(u => visit(u.id)); }
    };
    if (s.proof) visit(s.id);
    else {
      const c = res.conflict;
      if (c.clause) { clausesUsed.push(c.clause); c.used.forEach(u => visit(u.id)); }
      else { visit(c.id); if (c.reason && c.reason.clause) { clausesUsed.push(c.reason.clause); c.reason.used.forEach(u => visit(u.id)); } }
    }
    const out = new Map();
    clausesUsed.forEach(c => c.info.src !== "immediate" && out.set(c.info.src, c.info.added));
    if (!out.size) return "";
    return [...out.entries()].map(([k, a]) => srcBadge(k, a)).join(" ");
  }
  function baseLabel() {
    const sel = Object.entries(state.sel).filter(([id]) => !isLocked(id)).map(([id, v]) => litText(id, v));
    return logicName() + (sel.length ? " + " + sel.join(" + ") : "");
  }

  function strengthData() {
    const A0 = assumptions();
    const base = analyseWith(A0);
    if (base.inconsistent) return { inconsistent: true };
    const cand = D.principles.filter(p => base.status[p.id] && !["follows", "refuted"].includes(base.status[p.id].kind)).map(p => p.id);
    const given = {};      // given[a][b] = status of b given base + a
    cand.forEach(a => { given[a] = analyseWith(A0.concat([{ id: a, pos: true, why: { assumed: true } }])).status; });
    const imp = (a, b) => a === b || (given[a][b] && given[a][b].kind === "follows");
    // equivalence classes
    const cls = [], clsOf = {};
    cand.forEach(a => {
      const c = cls.find(c => imp(a, c[0]) && imp(c[0], a));
      if (c) c.push(a); else cls.push([a]);
    });
    cls.forEach((c, i) => c.forEach(a => clsOf[a] = i));
    const above = (i, j) => i !== j && imp(cls[i][0], cls[j][0]);   // class i implies class j
    // covering relation among classes
    const covers = cls.map((_, i) => cls.map((_, j) => j).filter(j => above(i, j) &&
      !cls.some((_, k) => k !== i && k !== j && above(i, k) && above(k, j))));
    // layers: the base is layer 0
    const layer = [];
    const L = i => layer[i] !== undefined ? layer[i] : (layer[i] = 1 + Math.max(0, ...covers[i].map(L)));
    cls.forEach((_, i) => L(i));
    return { base, given, cls, clsOf, covers, layer, imp, refutedByBase: D.principles.filter(p => base.status[p.id] && base.status[p.id].kind === "refuted").map(p => p.id) };
  }

  let strengthFocus = null;
  function renderStrength() {
    const box = $("#strengthMain");
    const S = strengthData();
    const head = `<div class="shead"><p>Each box is a principle, or a group of principles that are equivalent. An arrow from one box to another means that the first implies the second, given <b>${baseLabel()}</b> (the leftmost box, which also contains every principle that follows from it outright). Stronger principles are further to the right. Change the base logic or the assumptions on the left and this diagram updates.</p>
      <p class="skey"><span><svg width="34" height="10"><line x1="1" y1="5" x2="31" y2="5" class="se strict" marker-end="url(#sarr-strict)"/></svg> strictly stronger: the converse is known to fail</span>
      <span><svg width="34" height="10"><line x1="1" y1="5" x2="31" y2="5" class="se unk" marker-end="url(#sarr-unk)"/></svg> stronger; whether the converse holds is open</span></p></div>`;
    if (S.inconsistent) { box.innerHTML = head + `<div class="bad">The current assumptions are inconsistent.</div>`; return; }
    const { cls, covers, layer, given, base } = S;
    // geometry: the layers are columns, from the base on the left to the strongest principles on the right
    const wOf = t => Math.max(60, t.length * 7.6 + 26);
    // a box lists equivalent principles one per line, and the base lists its assumptions one per line
    const linesOf = k => (k === BASE ? baseText.split(" + ").map((t, n) => (n ? "+ " + t : t)) : cls[k].map((id, n) => (n ? "⟺ " : "") + tag(id)));
    const nL = Math.max(0, ...layer) + 1;
    const cols = Array.from({ length: nL }, () => []);
    cls.forEach((c, i) => cols[layer[i]].push(i));
    const BASE = -1;
    const baseText = baseLabel();
    // the edges, from each class to the classes it covers (or to the base)
    const E = [];
    cls.forEach((c, i) => (covers[i].length ? covers[i] : [BASE]).forEach(j => E.push({ i, j })));
    const indeg = {}, outdeg = {};
    E.forEach(({ i, j }) => { outdeg[i] = (outdeg[i] || 0) + 1; indeg[j] = (indeg[j] || 0) + 1; });
    const wid = k => Math.max(...linesOf(k).map(wOf));
    // bubbles are tall enough for their lines to meet them apart
    const hgt = k => Math.max(28, 17 * linesOf(k).length + 11, 9 * Math.max(indeg[k] || 0, outdeg[k] || 0) + 12);
    const gapY = 14, gapX = 84, padX = 20, padY = 24;
    const colW = l => Math.max(...(l === 0 ? [wid(BASE)] : cols[l].map(wid)));
    const colH = l => (l === 0 ? [BASE] : cols[l]).reduce((s, k) => s + hgt(k) + gapY, -gapY);
    const H = padY * 2 + Math.max(...Array.from({ length: nL }, (_, l) => colH(l)));
    const xcol = [];
    let xc = padX;
    for (let l = 0; l < nL; l++) { xcol[l] = xc + colW(l) / 2; xc += colW(l) + gapX; }
    const W = xc - gapX + padX;
    const ypos = {};
    ypos[BASE] = H / 2;
    const above = cls.map(() => []);
    cls.forEach((c, i) => covers[i].forEach(j => above[j].push(i)));
    const place = l => { let y = (H - colH(l)) / 2; cols[l].forEach(i => { const h = hgt(i); ypos[i] = y + h / 2; y += h + gapY; }); };
    const avg = (ks, d) => { const v = ks.map(j => ypos[j]).filter(v => v !== undefined); return v.length ? v.reduce((x, y) => x + y) / v.length : d; };
    // order each column by the average height of what it covers, then sweep back and forth so that boxes sit near their neighbours
    for (let l = 1; l < nL; l++) { cols[l].sort((a, b) => avg(covers[a], H / 2) - avg(covers[b], H / 2)); place(l); }
    for (let it = 0; it < 4; it++) {
      for (let l = nL - 2; l >= 1; l--) { cols[l].sort((a, b) => avg(above[a], ypos[a]) - avg(above[b], ypos[b])); place(l); }
      for (let l = 2; l < nL; l++) { cols[l].sort((a, b) => avg(covers[a], ypos[a]) - avg(covers[b], ypos[b])); place(l); }
    }
    const lay = k => (k === BASE ? 0 : layer[k]);
    const xpos = k => xcol[lay(k)];
    let svgEdges = "", svgNodes = "";
    const edge = (x1, y1, x2, y2, strict, key) => {
      svgEdges += `<line class="se ${strict ? "strict" : "unk"}" data-k="${key}" x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}" marker-end="url(#sarr-${strict ? "strict" : "unk"})"/>`;
      if (!strict) svgEdges += `<text class="sq" x="${(x1 + x2) / 2}" y="${(y1 + y2) / 2 - 5}">?</text>`;
    };
    // base-level status of a principle: is it known not to follow from the base?
    const strictOverBase = i => !!base.status[cls[i][0]].counter;
    // converse known to fail: some member of the upper class fails given the lower class
    const strictPair = (i, j) => { const s = given[cls[j][0]][cls[i][0]]; return !!(s && s.counter); };
    // spread the ends of the lines along the left side of the source and the right side of the target
    const spread = (k, n, idx) => { const span = Math.max(0, hgt(k) - 12); return n <= 1 ? ypos[k] : ypos[k] - span / 2 + span * idx / (n - 1); };
    const outs = {}, ins = {};
    E.forEach(e => { (outs[e.i] = outs[e.i] || []).push(e); (ins[e.j] = ins[e.j] || []).push(e); });
    Object.values(outs).forEach(l => l.sort((a, b) => ypos[a.j] - ypos[b.j]));
    Object.values(ins).forEach(l => l.sort((a, b) => ypos[a.i] - ypos[b.i]));
    E.forEach(e => {
      const y1 = spread(e.i, outs[e.i].length, outs[e.i].indexOf(e));
      const y2 = spread(e.j, ins[e.j].length, ins[e.j].indexOf(e));
      const strict = e.j === BASE ? strictOverBase(e.i) : strictPair(e.i, e.j);
      edge(xpos(e.i) - wid(e.i) / 2, y1, xpos(e.j) + wid(e.j) / 2 + 2, y2, strict, e.i + ">" + (e.j === BASE ? "base" : e.j));
    });
    const node = (k, key, cl) => {
      const w = wid(k), h = hgt(k), ls = linesOf(k);
      const text = ls.map((t, n) => `<tspan x="0" y="${4.5 + 17 * (n - (ls.length - 1) / 2)}">${t}</tspan>`).join("");
      svgNodes += `<g class="sn ${cl}" data-k="${key}" tabindex="0" role="button" transform="translate(${xpos(k)},${ypos[k]})"><rect x="${-w / 2}" y="${-h / 2}" width="${w}" height="${h}" rx="13"/><text text-anchor="middle">${text}</text></g>`;
    };
    node(BASE, "base", "basenode" + (strengthFocus === "base" ? " focus" : ""));
    cls.forEach((c, i) => node(i, i, strengthFocus === c[0] ? "focus" : ""));
    box.innerHTML = head + `<div class="sbox"><svg viewBox="0 0 ${W} ${H}" style="width:100%;min-width:${Math.min(W, 700)}px;max-width:${W}px"><defs>
      <marker id="sarr-strict" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="4.5" markerHeight="4.5" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="sm strict"/></marker>
      <marker id="sarr-unk" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="4.5" markerHeight="4.5" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" class="sm unk"/></marker></defs>${svgEdges}${svgNodes}</svg></div><div id="sdetails" class="details"></div>`;
    box.querySelectorAll(".sn").forEach(g => {
      const go = () => { const k = g.dataset.k; strengthFocus = k === "base" ? null : cls[+k][0]; renderStrength(); };
      g.addEventListener("click", go);
      g.addEventListener("keydown", e => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); go(); } });
    });
    renderStrengthDetails(S);
  }

  function renderStrengthDetails(S) {
    const box = $("#sdetails");
    const a = strengthFocus;
    if (!a || S.clsOf[a] === undefined) {
      const ref = S.refutedByBase.length ? `<p>Inconsistent with the base, so not shown: ${S.refutedByBase.map(tag).join(", ")}.</p>` : "";
      box.innerHTML = `<div class="hint">Click a box to see exactly where it sits: what it implies and what implies it (and whether strictly), and what it is incomparable with.</div>${ref}`;
      return;
    }
    const { given, base, cls, clsOf, imp } = S;
    const me = cls[clsOf[a]];
    const others = cls.filter(c => c !== me);
    const cm = s => {
      if (!s || !s.counter) return null;
      const w = s.counter.why[s.id];   // why the principle has its value in that model
      const why = w && w.model ? srcBadge(w.src.length > 40 ? w.src.split(/[;(:]/)[0].trim() : w.src, w.added) : srcBadge(s.counter.src);
      return `countermodel ${s.counter.name} ${why}`;
    };
    const line = (txt) => `<li>${txt}</li>`;
    const below = [], aboveL = [], incomp = [], unknown = [];
    // the base
    const bs = base.status[a];
    below.push(line(`<b>Strictly stronger than the base</b> ${baseLabel()}: ${baseLabel()} ⊬ ${tag(a)}, ${cm(bs) || ""}`.replace(/, $/, "")));
    if (!bs.counter) below.pop(), below.push(line(`Stronger than the base ${baseLabel()}; <i>whether ${baseLabel()} proves ${tag(a)} is open.</i>`));
    others.forEach(c => {
      const b = c[0];
      const ab = given[a][b], ba = given[b][a];
      const bl = c.map(tag).join(" ⟺ ");
      if (imp(a, b)) {
        below.push(line(`<b>${ba.counter ? "Strictly stronger" : "Stronger"} than ${bl}</b>: ${tag(a)} ⊢ ${tag(b)} ${sourcesOf(ab)}${ba.counter ? `; ${tag(b)} ⊬ ${tag(a)}, ${cm(ba)}` : `; <i>whether ${tag(b)} ⊢ ${tag(a)} is open</i>`}`));
      } else if (imp(b, a)) {
        aboveL.push(line(`<b>${ab.counter ? "Strictly weaker" : "Weaker"} than ${bl}</b>: ${tag(b)} ⊢ ${tag(a)} ${sourcesOf(ba)}${ab.counter ? `; ${tag(a)} ⊬ ${tag(b)}, ${cm(ab)}` : `; <i>whether ${tag(a)} ⊢ ${tag(b)} is open</i>`}`));
      } else if (ab.kind === "refuted" || ba.kind === "refuted") {
        incomp.push(line(`<b>Inconsistent with ${bl}</b> (given the base) ${sourcesOf(ab.kind === "refuted" ? ab : ba)}`));
      } else if (ab.counter && ba.counter) {
        incomp.push(line(`<b>Incomparable with ${bl}</b>: ${tag(a)} ⊬ ${tag(b)} (${cm(ab)}); ${tag(b)} ⊬ ${tag(a)} (${cm(ba)})`));
      } else {
        const parts = [];
        parts.push(ab.counter ? `${tag(a)} ⊬ ${tag(b)} (${cm(ab)})` : `whether ${tag(a)} ⊢ ${tag(b)} is open`);
        parts.push(ba.counter ? `${tag(b)} ⊬ ${tag(a)} (${cm(ba)})` : `whether ${tag(b)} ⊢ ${tag(a)} is open`);
        unknown.push(line(`<b>${bl}</b>: ${parts.join("; ")}`));
      }
    });
    const sec = (t, l) => l.length ? `<h4>${t}</h4><ul class="clist">${l.join("")}</ul>` : "";
    box.innerHTML = `<div class="dhead"><h3>${me.map(tag).join(" ⟺ ")}</h3><span class="dgroup">given ${baseLabel()}</span></div>
      ${me.length > 1 ? `<p>These are equivalent given the base.</p>` : ""}
      ${sec("Implied by", aboveL)}${sec("Implies", below)}${sec("Incomparable or inconsistent", incomp)}${sec("Partly unsettled", unknown)}`;
  }

  // ------------------------------------------------------------------ catalogue tab
  function renderCatalogue() {
    const pr = D.principles.map(p => `<tr><td class="ctag">${p.tag}</td><td>${tex(p.tex)}<div class="cg">${p.gloss}</div></td></tr>`).join("");
    const thms = D.pimTheorems.map(t => `<li>PI⁻ ⊢ <b>${tag(t.to)}</b> ${srcBadge(t.src)} ${leanBadge(t.lean)} <span class="cn">${t.note || ""}</span></li>`).join("");
    const rl = D.rules.map(r => `<li>PI⁻ + ${r.from.map(tag).join(" + ")} ⊢ <b>${tag(r.to)}</b> ${srcBadge(r.src, r.added)} ${leanBadge(r.lean) || '<span class="cn">(not yet checked in Lean)</span>'} <span class="cn">${r.note || ""}</span></li>`).join("");
    const inc = D.inconsistent.map(s => `<li>PI⁻ + ${s.set.map(tag).join(" + ")} ⊢ ⊥ ${srcBadge(s.src, s.added)} ${leanBadge(s.lean)} <span class="cn">${s.note || ""}</span></li>`).join("");
    const md = models.map(m => {
      const vals = D.principles.filter(p => p.id in m.val).map(p => {
        const w = m.why[p.id];
        const stated = w && w.model;
        const ln = stated && m.lean && m.lean[p.id] && window.LEANINDEX && (m.lean[p.id] in window.LEANINDEX);
        const inner = `${m.val[p.id] ? "" : "¬"}${p.tag}${ln ? " ✓" : ""}`;
        const title = (stated ? "by the construction of the model" : "follows in this model by the rules") + (ln ? " — checked in Lean: PIF." + m.lean[p.id] : "");
        const cls = `mv ${m.val[p.id] ? "t" : "f"}${stated ? "" : " derived"}`;
        return ln ? `<a class="${cls}" href="${leanURL(m.lean[p.id])}" target="_blank" rel="noopener" title="${title}">${inner}</a>`
                  : `<span class="${cls}" title="${title}">${inner}</span>`;
      }).join(" ");
      const lm = m.lean ? leanBadge(m.lean.model, "Lean ✓ model") : "";
      const ln = m.leanNote ? `<div class="mdesc"><i>Lean:</i> ${m.leanNote}</div>` : "";
      return `<div class="mcard"><div class="mname">${m.name} ${srcBadge(m.src)} ${lm}</div><div class="mdesc">${m.desc}</div>${ln}<div class="mvals">${vals}</div></div>`;
    }).join("");
    const other = D.otherResults.map(o => `<li><b>${o.title}.</b> ${o.text} ${srcBadge(o.src)}</li>`).join("");
    $("#catalogue").innerHTML = `
      <section class="nonew"><h2>The base logics</h2><h3>Common to all three</h3>${commonHTML()}${["PI-", "PI", "PIC"].map(k => `<h3>${D.logicSpec.logics[k].name}</h3>${identityHTML(k, k !== "PI-")}`).join("")}</section>
      <section class="nonew"><h2>Principles</h2><table class="ctable">${pr}</table></section>
      <section class="nonew"><h2>Theorems of PI⁻</h2><ul class="clist">${thms}</ul></section>
      <section><h2>Derivations</h2><ul class="clist">${rl}</ul></section>
      <section><h2>Inconsistencies</h2><ul class="clist">${inc}</ul></section>
      <section><h2>Models</h2><p>All are models of PI⁻; those in which LL≡ is true are models of PI. Faded entries are not part of the construction of the model, but follow in it from the derivations above. Entries marked ✓ are checked in Lean: click one to see the proof.</p>${md}</section>
      <section class="nonew"><h2>Other results</h2><ul class="clist">${other}</ul></section>`;
  }

  // ------------------------------------------------------------------ base logics
  const secHTML = (sec, badge) => {
    const rows = sec.items.map(it => `<tr><td class="ctag">${it.tag}</td><td>${tex(it.tex, true)}${it.side ? `<div class="cg">${it.side}</div>` : ""}</td></tr>`).join("");
    return `<section class="lsec${badge ? " ladded" : ""}"><h4>${sec.title}${badge ? ` <span class="lbadge">${badge}</span>` : ""}</h4><table class="ctable">${rows}</table></section>`;
  };
  // the axioms and rules shared by PI⁻, PI and PIᶜ
  function commonHTML() {
    return `<p class="lblurb">PI⁻, PI and PIᶜ all have these axioms and rules. They differ only in their axioms for identity.</p>
      <details class="llang"><summary>The language</summary><p>${D.logicSpec.language}</p></details>` +
      D.logicSpec.sections.filter(sec => sec.common).map(sec => secHTML(sec)).join("");
  }
  // the identity axioms of one logic; with onlyNew, just those it adds
  function identityHTML(key, onlyNew) {
    const L = D.logicSpec.logics[key];
    const lvName = lv => D.logicSpec.logics[lv].name;
    return `<p class="lblurb">${L.blurb}</p>` + D.logicSpec.sections
      .filter(sec => !sec.common && (onlyNew ? sec.level === key : L.levels.includes(sec.level)))
      .map(sec => secHTML(sec, sec.level !== "PI-" && !onlyNew ? "added in " + lvName(sec.level) : "")).join("");
  }
  function syncThmToggle() {
    const b = $("#togglethms");
    b.setAttribute("aria-pressed", state.showThms);
    b.textContent = (state.showThms ? "Hide" : "Show") + " the theorems of " + logicName() + " in the graph";
  }
  function openCommon() { $("#logicbody").innerHTML = commonHTML(); $("#logicdlg").showModal(); }

  // ------------------------------------------------------------------ main
  // ------------------------------------------------------------------ rendering: collections
  const LOGIC_NAMES = { PIC: "PIᶜ", PI: "PI", "PI-": "PI⁻" };
  function renderCollections() {
    const box = $("#collections");
    if (!box || !D.collections) return;
    box.innerHTML = `<h2 class="colh">Collections</h2>` + D.collections.map((g, gi) => `
      <div class="cgroup"><div class="gname">${g.group}</div>
        ${g.note ? `<p class="cnote">${g.note}</p>` : ""}
        ${g.items.map((c, ci) => {
          const sc = settleScore(c.logic, c.sel);
          const score = sc ? `<span class="cscore" title="Open principles settled, of those left open by ${LOGIC_NAMES[c.logic]}">settles ${sc.n} of ${sc.m}</span>` : "";
          return `<button class="coll" data-g="${gi}" data-c="${ci}" type="button">
            <span class="clogic">${LOGIC_NAMES[c.logic]}</span>
            <span class="cprins">${c.sel.map(tag).join(" + ")}${c.target ? ` <b class="ctarget">⇒ ${tag(c.target)}</b>` : ""}</span>
            ${score}
            ${c.note ? `<span class="cdesc">${c.note}</span>` : ""}
          </button>`;
        }).join("")}
      </div>`).join("");
    box.querySelectorAll(".coll").forEach(b => b.addEventListener("click", () => {
      const c = D.collections[+b.dataset.g].items[+b.dataset.c];
      if (b.classList.contains("on")) {
        // clicking the active collection again clears it
        state.sel = {}; state.focus = null; state.opened = [];
      } else {
        state.logic = c.logic;
        state.sel = Object.fromEntries(c.sel.map(id => [id, true]));
        state.focus = c.target || null;
        state.opened = c.target ? [c.target] : [];
      }
      update();
    }));
  }
  function syncCollections() {
    document.querySelectorAll("#collections .coll").forEach(b => {
      const c = D.collections[+b.dataset.g].items[+b.dataset.c];
      const ids = Object.entries(state.sel).filter(([id, v]) => v === true && !isLocked(id)).map(([id]) => id).sort();
      const neg = Object.values(state.sel).some(v => v === false);
      const on = state.logic === c.logic && !neg && ids.join() === c.sel.slice().sort().join();
      b.classList.toggle("on", on);
      b.setAttribute("aria-pressed", on);
      b.title = on ? "Click again to clear this selection" : "Select these principles in " + LOGIC_NAMES[c.logic];
    });
  }

  function update() {
    writeHash();
    const an = analyse();
    if (state.sortMode === "power" && checklistLogic !== state.logic) renderChecklist();
    syncChecklist();
    syncCollections();
    syncThmToggle();
    renderGraph(an);
    renderDetails(an);
    if (!$("#strength").hidden) renderStrength();
  }

  function init() {
    readHash();
    renderChecklist();
    renderCollections();
    const sortSel = $("#sortmode");
    if (sortSel) {
      sortSel.value = state.sortMode;
      sortSel.addEventListener("change", () => {
        state.sortMode = sortSel.value;
        try { localStorage.setItem("pi-sortmode2", state.sortMode); } catch (e) {}
        renderChecklist();
        update();
      });
    }
    initGraph();
    document.querySelectorAll(".logic button[data-logic]").forEach(b => b.addEventListener("click", () => {
      state.logic = b.dataset.logic;
      update();
    }));
    $("#showlogic").addEventListener("click", openCommon);
    $("#togglethms").addEventListener("click", () => {
      state.showThms = !state.showThms;
      try { localStorage.setItem("pi-showthms", state.showThms ? "1" : "0"); } catch (e) {}
      update();
    });
    $("#logicdlg .lclose").addEventListener("click", () => $("#logicdlg").close());
    $("#logicdlg").addEventListener("click", e => { if (e.target.id === "logicdlg") e.target.close(); });
    $("#reset").addEventListener("click", () => { state.sel = {}; state.focus = null; state.opened = []; update(); });
    document.querySelectorAll(".tabs button").forEach(b => b.addEventListener("click", () => {
      document.querySelectorAll(".tabs button").forEach(x => x.setAttribute("aria-selected", x === b));
      document.querySelectorAll(".tabpanel").forEach(x => x.hidden = x.id !== b.dataset.tab);
      const side = $("aside.side");
      const right = $("#collections");
      if (b.dataset.tab === "strength") { $("#strength .layout").prepend(side); if (right) $("#strength .layout").append(right); renderStrength(); }
      if (b.dataset.tab === "explorer") { $("#explorer .layout").prepend(side); if (right) $("#explorer .layout").append(right); }
    }));
    renderCatalogue();
    window.__pi = { analyse, analyseWith, state, update, models, strengthData };
    window.addEventListener("hashchange", () => { readHash(); update(); });
    update();
  }
  if (window.katex) init(); else window.addEventListener("load", init);
})();
