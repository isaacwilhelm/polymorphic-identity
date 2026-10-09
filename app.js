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
  const state = { logic: "PI", sel: {}, focus: null };

  function readHash() {
    const h = decodeURIComponent(location.hash.replace(/^#/, ""));
    if (!h) return;
    const parts = h.split(",").filter(Boolean);
    state.sel = {};
    state.logic = "PI";
    parts.forEach(p => {
      if (p === "PI-") state.logic = "PI-";
      else if (p === "PI") state.logic = "PI";
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
    if (state.logic === "PI") {
      a.splice(0, a.length, ...a.filter(x => x.id !== "LLeq"));
      a.unshift({ id: "LLeq", pos: true, why: { assumed: true, base: true } });
    }
    return a;
  }
  const isLocked = id => state.logic === "PI" && id === "LLeq";

  // ------------------------------------------------------------------ analysis
  function modelSatisfies(m, lits) {
    return lits.every(l => m.val[l.id] === l.pos);
  }

  function analyse() {
    const A = assumptions();
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
  function srcBadge(src, added) {
    return `<span class="src${added ? " added" : ""}" title="${added ? "Observed when building this site; not stated in the notes. Please check." : D.SOURCE}">${src}${added ? " ◆" : ""}</span>`;
  }
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
    return `<li><b>${litText(id, pos)}</b> <span class="by">${how}</span> ${srcBadge(c.info.src, c.info.added)}${note}</li>`;
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
      last = `<li class="contra"><b>⊥</b> <span class="by">since ${describeClause(c.clause)}</span> ${srcBadge(c.clause.info.src, c.clause.info.added)}${c.clause.info.note ? `<div class="stepnote">${c.clause.info.note}</div>` : ""}</li>`;
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
    if (w && w.model) reason = `${srcBadge(w.src, w.added)}`;
    else if (w) reason = `follows in the model: ${w.used.map(u => litText(u.id, u.pos)).join(", ")} with ${describeClause(w.clause)} ${srcBadge(w.clause.info.src, w.clause.info.added)}`;
    const assumed = assumptions().map(a => litText(a.id, a.pos)).join(", ");
    return `<div class="model"><div class="mname">${m.name}</div><div class="mdesc">${m.desc}</div>
      <div class="mline">Here ${tag(id)} is <b>${m.val[id] ? "true" : "false"}</b> — ${reason}</div>
      <div class="mline subtle">and every assumption (${assumed || "PI⁻"}) is true.</div></div>`;
  }

  const KIND = {
    follows:      { label: "Follows", cls: "k-follows", desc: "derivable from the selection" },
    independent:  { label: "Independent", cls: "k-indep", desc: "consistent with the selection, but not derivable from it" },
    consistent:   { label: "Consistent", cls: "k-cons", desc: "consistent with the selection; whether it follows is open" },
    notderivable: { label: "Does not follow", cls: "k-notder", desc: "not derivable; whether it is consistent with the selection is open" },
    refuted:      { label: "Inconsistent", cls: "k-refuted", desc: "inconsistent with the selection (its negation follows)" },
    open:         { label: "Open", cls: "k-open", desc: "neither settled by the results in the notes" },
  };
  const ORDER = ["follows", "independent", "consistent", "notderivable", "open", "refuted"];

  // ------------------------------------------------------------------ rendering: checklist
  const $ = s => document.querySelector(s);
  function tex(s, display) {
    try { return katex.renderToString(s, { displayMode: !!display, throwOnError: false, trust: true, strict: false, macros: MACROS }); }
    catch (e) { return s; }
  }
  const MACROS = { "\\TA": "\\htmlClass{tq}{\\mathbb{A}}", "\\TE": "\\htmlClass{tq}{\\mathbb{E}}" };

  function renderChecklist() {
    const box = $("#checklist");
    const groups = [];
    D.principles.forEach(p => {
      let g = groups.find(g => g.name === p.group);
      if (!g) groups.push(g = { name: p.group, items: [] });
      g.items.push(p);
    });
    box.innerHTML = groups.map(g => `
      <div class="group"><div class="gname">${g.name}</div>
      ${g.items.map(p => `
        <div class="item" data-id="${p.id}">
          <div class="tri" role="radiogroup" aria-label="${p.tag}">
            <button class="t-yes" data-v="yes" title="Assume ${p.tag}" aria-label="Assume ${p.tag}">✓</button>
            <button class="t-no" data-v="no" title="Assume the negation of ${p.tag}" aria-label="Assume not ${p.tag}">¬</button>
          </div>
          <button class="pname" title="Show details">${p.tag}</button>
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
      el.querySelector(".pname").addEventListener("click", () => { state.focus = id; update(); scrollToDetails(); });
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
      el.querySelector(".t-yes").title = isLocked(id) ? "LL≡ is an axiom of PI. Switch to PI⁻ to drop it." : "Assume " + tag(id);
    });
    document.querySelectorAll(".logic button").forEach(b => b.setAttribute("aria-pressed", b.dataset.logic === state.logic));
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
      g.addEventListener("click", () => { state.focus = p.id; update(); scrollToDetails(); });
      g.addEventListener("keydown", e => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); state.focus = p.id; update(); scrollToDetails(); } });
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
    if (document.hidden) step(t0 + dur); else requestAnimationFrame(step);
  }

  function renderGraph(an) {
    // hub
    hubG.innerHTML = "";
    const lines = an.A.map(a => (a.why.base ? "PI (= PI⁻ + LL≡)" : litText(a.id, a.pos)));
    if (state.logic === "PI-") lines.unshift("PI⁻");
    const hb = hubBox(lines);
    el("rect", { x: hb.x, y: hb.y, width: hb.w, height: hb.h, rx: 10, class: an.inconsistent ? "hubrect bad" : "hubrect" }, hubG);
    lines.forEach((l, i) => {
      const t = el("text", { x: CX, y: hb.y + 22 + i * 19, "text-anchor": "middle", class: i === 0 ? "hubtitle" : "" }, hubG);
      t.textContent = l;
    });

    // targets placed around an ellipse, grouped by status
    const assumed = new Set(an.A.map(a => a.id));
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
    if (!an.inconsistent) Object.values(an.status).forEach(s => counts[s.kind] = (counts[s.kind] || 0) + 1);
    $("#legend").innerHTML = ORDER.map(k => `
      <span class="lg ${KIND[k].cls}" title="${KIND[k].desc}"><svg width="34" height="10" aria-hidden="true"><line x1="1" y1="5" x2="33" y2="5"/></svg>${KIND[k].label}<b>${counts[k] || 0}</b></span>`).join("");
    $("#banner").innerHTML = an.inconsistent
      ? `<div class="bad"><b>The selected principles are jointly inconsistent.</b> ${refutationHTML(an.base)}</div>` : "";
  }

  // ------------------------------------------------------------------ rendering: details
  function renderDetails(an) {
    const box = $("#details");
    const id = state.focus;
    if (!id) {
      box.innerHTML = `<div class="hint">Click any principle (in the list or the graph) to see its statement and <em>why</em> it has the status shown: the derivation, or the model that shows it does not follow.</div>`;
      return;
    }
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
        if (!s.counter) body += `<p class="openq">No model in the notes shows that ${p.tag} fails while the selection holds.</p>`;
        if (!s.witness) body += `<p class="openq">No model in the notes shows ${p.tag} true together with the selection.</p>`;
      }
    }
    const lock = isLocked(id);
    const cur = state.sel[id];
    box.innerHTML = `
      <div class="dhead"><h3>${p.tag}</h3><span class="dgroup">${p.group}</span></div>
      <div class="formula">${tex(p.tex, true)}</div>
      <p class="gloss">${p.gloss}</p>
      ${body}
      <div class="dactions">
        <button data-a="yes" ${lock ? "disabled" : ""} aria-pressed="${cur === true || lock}">${cur === true ? "Stop assuming it" : "Assume it"}</button>
        <button data-a="no" ${lock ? "disabled" : ""} aria-pressed="${cur === false}">${cur === false ? "Stop assuming its negation" : "Assume its negation"}</button>
      </div>`;
    box.querySelectorAll(".dactions button").forEach(b => b.addEventListener("click", () => {
      const want = b.dataset.a === "yes";
      if (state.sel[id] === want) delete state.sel[id]; else state.sel[id] = want;
      update();
    }));
  }
  function scrollToDetails() {
    if (window.innerWidth < 900) $("#details").scrollIntoView({ behavior: "smooth", block: "start" });
  }

  // ------------------------------------------------------------------ catalogue tab
  function renderCatalogue() {
    const pr = D.principles.map(p => `<tr><td class="ctag">${p.tag}</td><td>${tex(p.tex)}<div class="cg">${p.gloss}</div></td></tr>`).join("");
    const base = D.baseAxioms.map(a => `<tr><td class="ctag">${a.tag}</td><td>${tex(a.tex)}</td></tr>`).join("");
    const thms = D.pimTheorems.map(t => `<li>PI⁻ ⊢ <b>${tag(t.to)}</b> ${srcBadge(t.src)} <span class="cn">${t.note || ""}</span></li>`).join("");
    const rl = D.rules.map(r => `<li>PI⁻ + ${r.from.map(tag).join(" + ")} ⊢ <b>${tag(r.to)}</b> ${srcBadge(r.src, r.added)} <span class="cn">${r.note || ""}</span></li>`).join("");
    const inc = D.inconsistent.map(s => `<li>PI⁻ + ${s.set.map(tag).join(" + ")} ⊢ ⊥ ${srcBadge(s.src, s.added)} <span class="cn">${s.note || ""}</span></li>`).join("");
    const md = models.map(m => {
      const vals = D.principles.filter(p => p.id in m.val).map(p => {
        const w = m.why[p.id];
        const stated = w && w.model;
        return `<span class="mv ${m.val[p.id] ? "t" : "f"}${stated ? "" : " derived"}" title="${stated ? w.src : "follows in this model by the rules"}">${m.val[p.id] ? "" : "¬"}${p.tag}${w && w.added ? " ◆" : ""}</span>`;
      }).join(" ");
      return `<div class="mcard"><div class="mname">${m.name} ${srcBadge(m.src)}</div><div class="mdesc">${m.desc}</div><div class="mvals">${vals}</div></div>`;
    }).join("");
    const other = D.otherResults.map(o => `<li><b>${o.title}.</b> ${o.text} ${srcBadge(o.src)}</li>`).join("");
    $("#catalogue").innerHTML = `
      <section><h2>The base logic</h2>
        <p>PI⁻ consists of the propositional, quantifier, and β-conversion axioms, the rules MP, Gen∀ and Gen𝔸, and these identity axioms. PI adds LL≡.</p>
        <table class="ctable">${base}</table></section>
      <section><h2>Principles</h2><table class="ctable">${pr}</table></section>
      <section><h2>Theorems of PI⁻</h2><ul class="clist">${thms}</ul></section>
      <section><h2>Derivations</h2><ul class="clist">${rl}</ul></section>
      <section><h2>Inconsistencies</h2><ul class="clist">${inc}</ul></section>
      <section><h2>Models</h2><p>All are models of PI⁻; those in which LL≡ is true are models of PI. Faded entries are not stated in the notes but follow in the model from the derivations above.</p>${md}</section>
      <section><h2>Other results</h2><ul class="clist">${other}</ul></section>`;
  }

  // ------------------------------------------------------------------ main
  function update() {
    writeHash();
    const an = analyse();
    syncChecklist();
    renderGraph(an);
    renderDetails(an);
  }

  function init() {
    readHash();
    renderChecklist();
    initGraph();
    document.querySelectorAll(".logic button").forEach(b => b.addEventListener("click", () => {
      state.logic = b.dataset.logic;
      update();
    }));
    $("#reset").addEventListener("click", () => { state.sel = {}; state.focus = null; update(); });
    document.querySelectorAll(".tabs button").forEach(b => b.addEventListener("click", () => {
      document.querySelectorAll(".tabs button").forEach(x => x.setAttribute("aria-selected", x === b));
      document.querySelectorAll(".tabpanel").forEach(x => x.hidden = x.id !== b.dataset.tab);
    }));
    renderCatalogue();
    window.__pi = { analyse, state, update, models };
    window.addEventListener("hashchange", () => { readHash(); update(); });
    update();
  }
  if (window.katex) init(); else window.addEventListener("load", init);
})();
