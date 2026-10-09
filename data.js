// Data for the Polymorphic Identity results explorer.
//
// Source: Isaac Wilhelm, "Formal Results" (Draft 5, 2026-10-08), the companion note to
// "Identification Across Types" / "Polymorphic Identity". Theorem numbers are the numbers
// in the compiled PDF of that draft.
//
// HOW TO EDIT
//   principles     – the principles shown in the checklist and in the graph.
//   pimTheorems    – principles which PI^- proves outright (no extra premises).
//   rules          – derivations: given PI^- together with `from`, the principle `to` follows.
//                    (PI is PI^- plus LL≡, so a result stated "for PI" lists "LLeq" in `from`.)
//   inconsistent   – sets of principles which, given PI^-, prove ⊥.
//   models         – models of PI^-, with the principles known to be true (T) or false (F) in
//                    them. Values implied by the rules are filled in automatically.
//   `added: true`  – marks a fact that is not stated in the notes but was observed when this
//                    site was built (each is a one-line argument, given in `note`). Check these.

const SOURCE = "Formal Results, Draft 5";

const principles = [
  // ---------------------------------------------------------------- the logic
  { id: "LLeq", tag: "LL≡", group: "The logic",
    tex: String.raw`\TA\alpha\,\forall_{\alpha}x\,\forall_{\alpha}y\,\big(x\equiv_{\alpha}y\rightarrow\forall_{\alpha\to t}F\,(Fx\rightarrow Fy)\big)`,
    gloss: "Leibniz's law within each type. PI is PI⁻ plus this axiom." },

  // ---------------------------------------------------------------- basic theory
  { id: "SymA", tag: "Sym≈", group: "Basic theory",
    tex: String.raw`\TA\alpha\,\TA\beta\,(\alpha\approx\beta\rightarrow\beta\approx\alpha)`,
    gloss: "Identity among types is symmetric." },
  { id: "TransA", tag: "Trans≈", group: "Basic theory",
    tex: String.raw`\TA\alpha\,\TA\beta\,\TA\gamma\,\big((\alpha\approx\beta\wedge\beta\approx\gamma)\rightarrow\alpha\approx\gamma\big)`,
    gloss: "Identity among types is transitive." },
  { id: "Link", tag: "Link", group: "Basic theory",
    tex: String.raw`\TA\alpha\,\TA\beta\,\big(\alpha\approx\beta\rightarrow\forall_{\alpha}x\,\exists_{\beta}y\,(x\equiv_{\alpha,\beta}y)\big)`,
    gloss: "When types are identical, their corresponding items are identical." },
  { id: "Bridge", tag: "LL≡/≈", group: "Basic theory",
    tex: String.raw`\TA\alpha\,\TA\beta\,\forall_{\alpha}x\,\forall_{\beta}y\,\big((x\equiv_{\alpha,\beta}y\wedge\alpha\approx\beta)\rightarrow(P_{\alpha}x\rightarrow P_{\beta}y)\big)`,
    gloss: "Bridge principle: identified items of identical types share every polymorphic property (schema in P)." },
  { id: "WCong", tag: "WCong", group: "Basic theory",
    tex: String.raw`\TA\alpha\TA\beta\TA\gamma\TA\delta\,\forall f\,\forall g\,\forall x\,\forall y\,\big((\alpha\approx\beta\wedge\gamma\approx\delta\wedge f\equiv_{\alpha\to\gamma,\beta\to\delta}g\wedge x\equiv_{\alpha,\beta}y)\rightarrow fx\equiv_{\gamma,\delta}gy\big)`,
    gloss: "Within-type congruence: congruence with application, restricted to identical types." },
  { id: "Cantor", tag: "Cantor", group: "Basic theory",
    tex: String.raw`\TA\alpha\,\exists_{\alpha\to t}G\,\forall_{\alpha}y\,(G\not\equiv_{\alpha\to t,\alpha}y)`,
    gloss: "There are more properties of items of a type than items of that type." },
  { id: "TopBot", tag: "⊤≢⊥", group: "Basic theory",
    tex: String.raw`\top\not\equiv_{t}\bot`,
    gloss: "The true and the false proposition are distinct." },

  // ---------------------------------------------------------------- Disjoint and objects vs. properties
  { id: "Disjoint", tag: "Disjoint", group: "Objects and properties",
    tex: String.raw`\TA\alpha\,\TA\beta\,\big(\neg(\alpha\approx\beta)\to\forall_{\alpha}x\,\forall_{\beta}y\,(x\not\equiv_{\alpha,\beta}y)\big)`,
    gloss: "Items of distinct types are distinct." },
  { id: "Slogan", tag: "Slogan", group: "Objects and properties",
    tex: String.raw`\forall_{e}x\,\TA\beta\,\forall_{\beta\to t}y\,(x\not\equiv_{e,\beta\to t}y)`,
    gloss: "No object is identical to a property." },

  // ---------------------------------------------------------------- distinctly polymorphic
  { id: "Twin", tag: "Twin", group: "Distinctly polymorphic",
    tex: String.raw`\TA\alpha\,\forall_{\alpha}x\,\TE\beta\,\big(\neg(\alpha\approx\beta)\wedge\exists_{\beta}y\,(x\equiv_{\alpha,\beta}y)\big)`,
    gloss: "Every item is identical to an item of some other type. Not expressible in the simply typed fragment (Thm 9)." },

  // ---------------------------------------------------------------- Leibniz
  { id: "LLPoly", tag: "LL≡-Poly", group: "Leibniz's law",
    tex: String.raw`\TA\alpha\,\TA\beta\,\forall_{\alpha}x\,\forall_{\beta}y\,\big(x\equiv_{\alpha,\beta}y\rightarrow(P_{\alpha}x\rightarrow P_{\beta}y)\big)`,
    gloss: "Polymorphic Leibniz's law (schema in polymorphic predicates P)." },

  // ---------------------------------------------------------------- congruence
  { id: "Cong", tag: "Cong", group: "Congruence",
    tex: String.raw`\TA\alpha\TA\beta\TA\gamma\TA\delta\,\forall_{\alpha\to\gamma}f\,\forall_{\beta\to\delta}g\,\forall_{\alpha}x\,\forall_{\beta}y\,\big((f\equiv_{\alpha\to\gamma,\beta\to\delta}g\wedge x\equiv_{\alpha,\beta}y)\rightarrow fx\equiv_{\gamma,\delta}gy\big)`,
    gloss: "Polymorphic Congruence: identified functions take identified values at identified arguments, whatever the types." },
  { id: "PCong", tag: "PCong", group: "Congruence",
    tex: String.raw`\TA\alpha\TA\gamma\TA\delta\,\forall_{\alpha\to\gamma}f\,\forall_{\alpha\to\delta}g\,\forall_{\alpha}x\,\big(f\equiv_{\alpha\to\gamma,\alpha\to\delta}g\rightarrow fx\equiv_{\gamma,\delta}gx\big)`,
    gloss: "Partial Polymorphic Congruence: identified functions with the same domain take identified values." },
  { id: "Inj", tag: "Inj≈", group: "Congruence",
    tex: String.raw`\TA\alpha\TA\beta\TA\gamma\TA\delta\,\big((\alpha\to\gamma)\approx(\beta\to\delta)\rightarrow(\alpha\approx\beta\wedge\gamma\approx\delta)\big)`,
    gloss: "A function type determines its domain and the type of its values." },
  { id: "Recovery", tag: "Recovery", group: "Congruence",
    tex: String.raw`\TA\alpha\TA\beta\TA\gamma\TA\delta\,\big(((\alpha\to\gamma)\approx(\beta\to\delta)\wedge\alpha\approx\beta)\rightarrow\gamma\approx\delta\big)`,
    gloss: "Function types with identical domains are identical only if their value types are." },
  { id: "Truth", tag: "Truth", group: "Congruence",
    tex: String.raw`\forall_{t}p\,\forall_{t}q\,\big(p\equiv_{t}q\rightarrow(p\rightarrow q)\big)`,
    gloss: "Leibniz's law for propositions, with respect to truth." },

  // ---------------------------------------------------------------- haecceitism
  { id: "Hae", tag: "Haecceitism", group: "Haecceitism",
    tex: String.raw`\TA\alpha\,\forall_{\alpha}x\,\big(x\equiv_{\alpha,\alpha\to t}\lambda y{:}\alpha.(y\equiv_{\alpha}x)\big)`,
    gloss: "Each item is identical to its own haecceity." },

  // ---------------------------------------------------------------- individuation of types
  { id: "Ext", tag: "Ext≈", group: "Individuation of types",
    tex: String.raw`\TA\alpha\,\TA\beta\,\big((\alpha\sqsubseteq\beta\wedge\beta\sqsubseteq\alpha)\rightarrow\alpha\approx\beta\big)`,
    gloss: "Extensionality for types, where α ⊑ β abbreviates ∀ₐx∃ᵦy(x ≡ y)." },
  { id: "Int", tag: "Int≈", group: "Individuation of types",
    tex: String.raw`\TA\alpha\,\TA\beta\,\big((\Box(\alpha\sqsubseteq\beta)\wedge\Box(\beta\sqsubseteq\alpha))\rightarrow\alpha\approx\beta\big)`,
    gloss: "Intensional individuation of types (□φ abbreviates φ ≡ₜ ⊤). Stated for reference; nothing is proved about it yet." },
];

// The identity axioms of PI^- (always assumed), shown for reference.
const baseAxioms = [
  { tag: "Ref≡", tex: String.raw`\TA\alpha\,\forall_{\alpha}x\,(x\equiv_{\alpha}x)` },
  { tag: "Sym≡", tex: String.raw`\TA\alpha\,\TA\beta\,\forall_{\alpha}x\,\forall_{\beta}y\,(x\equiv_{\alpha,\beta}y\to y\equiv_{\beta,\alpha}x)` },
  { tag: "Trans≡", tex: String.raw`\TA\alpha\TA\beta\TA\gamma\,\forall x\forall y\forall z\,\big((x\equiv_{\alpha,\beta}y\wedge y\equiv_{\beta,\gamma}z)\to x\equiv_{\alpha,\gamma}z\big)` },
  { tag: "Ref≈", tex: String.raw`\TA\alpha\,(\alpha\approx\alpha)` },
  { tag: "LL≈", tex: String.raw`\TA\alpha\,\TA\beta\,\big(\alpha\approx\beta\rightarrow(Q\alpha\rightarrow Q\beta)\big)` },
];

// Principles PI^- proves outright.
const pimTheorems = [
  { to: "SymA",  src: "Lemma 9", note: "The proof uses only Ref≈ and LL≈." },
  { to: "TransA", src: "Lemma 9", note: "The proof uses only Ref≈ and LL≈." },
  { to: "Link",  src: "Thm 2", note: "The proof uses Ref≡ and LL≈, not LL≡." },
];

// Derivations. Each says: PI^- + from ⊢ to.
const rules = [
  { from: ["LLeq"], to: "Bridge", src: "Thm 3",
    note: "LL≡ cannot be dropped: PI⁻ does not prove every instance (Thm 12)." },
  { from: ["LLeq"], to: "WCong", src: "Thm 4" },
  { from: ["LLeq"], to: "Cantor", src: "Thm 6", note: "The proof is analogous to the Russell–Myhill paradox." },
  { from: ["LLeq"], to: "TopBot", src: "Lemma 13" },
  { from: ["LLeq"], to: "Truth", src: "immediate", note: "Truth is the instance of LL≡ at type t with λp.p for F." },
  { from: ["LLPoly"], to: "Disjoint", src: "Thm 11", note: "This half of Thm 11 uses only Ref≈ and LL≈, so holds given PI⁻ (remark after Thm 11)." },
  { from: ["Disjoint", "LLeq"], to: "LLPoly", src: "Thm 11", note: "This half uses Thm 3, hence LL≡; that use cannot be avoided (Thm 12)." },
  { from: ["Hae", "Cantor"], to: "Twin", src: "Thm 26", note: "Stated for PI; the proof uses Haecceitism and Cor 6 (no type is identical to the type of its properties), which follows from Cantor." },
  { from: ["Cong"], to: "PCong", src: "Thm 27(a)", note: "PCong is the instance of Cong with α for β and x for y, given Ref≡." },
  { from: ["Inj"], to: "Recovery", src: "remark after Thm 21" },
  { from: ["LLeq", "LLPoly", "Recovery"], to: "Cong", src: "Thm 20" },
  { from: ["LLeq", "LLPoly", "Cong"], to: "Recovery", src: "Thm 20" },
  { from: ["Cong", "Truth"], to: "LLeq", src: "Thm 22" },
];

// Sets of principles which, given PI^-, are inconsistent.
const inconsistent = [
  { set: ["LLeq", "Hae", "Cong"], src: "Thm 25",
    note: "Given PI, Haecceitism and Polymorphic Congruence are incompatible. (Additional Results, 2026-10-09: given PI and Cong, a type whose items and whose constant property are identical to their haecceities has exactly one item.)" },
  { set: ["Twin", "Disjoint"], src: "remark after Thm 9",
    note: "Twin identifies each item with an item of a type not identical to its own, which Disjoint forbids (types are non-empty)." },
];

// Models. All are models of PI^-; those with LLeq: true are models of PI.
// HF⁺ is the non-empty hereditarily finite sets; ∼ is an identification (Def 'identifications').
const models = [
  { id: "M0", name: "𝔐(HF⁺, ∼₀), E = 1",
    desc: "Within each type, ≡ is identity of sets; nothing is identified across types; ≈ is identity of sets. ",
    src: "Lemma 5; Thms 7, 8, 19, 29; Lemma 11(a)",
    values: {
      LLeq: [true, "Lemma 5"], Disjoint: [true, "Thm 7"], LLPoly: [true, "Thm 19"], Cong: [true, "Thm 19"],
      Inj: [true, "Thm 19"], Ext: [true, "Thm 29"], Twin: [false, "Lemma 11(a)"],
      Slogan: [true, "Thm 8(a): Disjoint holds, and E = 1 is not a function space, so e is identical to no type β→t"],
    } },
  { id: "M0e", name: "𝔐(HF⁺, ∼₀), E = 2→2",
    desc: "As 𝔐(HF⁺, ∼₀), but the type of entities is interpreted as the set of functions from 2 to 2, the value of t→t.",
    src: "Thm 8(b)",
    values: {
      LLeq: [true, "Lemma 5"], Disjoint: [true, "Thm 7"], LLPoly: [true, "Thm 19"], Cong: [true, "Thm 19"],
      Inj: [true, "Thm 19"], Ext: [true, "Thm 29"], Twin: [false, "Lemma 11(a)"],
      Slogan: [false, "With t for β: each item of e is the very same set as an item of t→t, so ∼₀ identifies them", true],
    } },
  { id: "M1", name: "𝔐(HF⁺, ∼₁), E = 1",
    desc: "Identifies ∅ ∈ 1 with ∅ ∈ 2, and nothing else across types.",
    src: "Thm 13 and the remark after it",
    values: {
      LLeq: [true, "Lemma 5"], Disjoint: [false, "remark after Thm 13"], LLPoly: [false, "Thm 13"],
      Ext: [true, "Thm 29"], Inj: [true, "≈ is identity of sets, and a function space determines its domain and value set (§3.3)"]
    } },
  { id: "Mh", name: "𝔐(HF⁺, ∼ₕ)",
    desc: "The haecceitist identification: each item a of A is identified with its haecceity χₐ ∈ A→2.",
    src: "Thms 24, 28(b), 29; Lemma 11(a)",
    values: {
      LLeq: [true, "Lemma 5"], Hae: [true, "Thm 24"], Twin: [true, "Lemma 11(a)"],
      PCong: [true, "Thm 28(b)"], Cong: [false, "Thm 28(b)"], Ext: [true, "Thm 29"],
      Inj: [true, "≈ is identity of sets, and a function space determines its domain and value set (§3.3)"],
    } },
  { id: "Mp", name: "𝔐(HF⁺, ∼ₚ), E = 1",
    desc: "Identifies one function in 1→2 with one function in 1→3, whose values are not identified.",
    src: "Thm 28(a)",
    values: {
      LLeq: [true, "Lemma 5"], PCong: [false, "Thm 28(a)"],
      Inj: [true, "≈ is identity of sets (§3.3)"],
      Disjoint: [false, "It identifies items of the distinct types 1→2 and 1→3", true],
    } },
  { id: "MD", name: "𝔐_D (a model of PI⁻ only)",
    desc: "E = {0,1,2}; ≈ is identity of sets; within type E, 0 and 1 are identified; within E→2, χ and ζ are identified; nothing across types.",
    src: "Thm 12",
    values: {
      LLeq: [false, "Thm 12 (0 ≡ 1 at type E, but χ separates them)"], Disjoint: [true, "Thm 12"],
      LLPoly: [false, "Thm 12"], Bridge: [false, "Thm 12"], Inj: [true, "≈ is identity of sets (§3.3)"],
    } },
  { id: "ME", name: "𝔐_E (a model of PI⁻ only)",
    desc: "E = {0,1,2}; ≈ is identity of sets; within type E, 0 and 1 are identified; nothing else.",
    src: "Thm 28(c)",
    values: {
      LLeq: [false, "Thm 28(c)"], PCong: [true, "Thm 28(c)"], WCong: [false, "Thm 28(c)"],
      Inj: [true, "≈ is identity of sets (§3.3)"],
      Disjoint: [true, "≡ relates only items of one and the same type", true],
    } },
  { id: "Mtot", name: "𝔐_tot (a model of PI⁻ only)",
    desc: "The total interpretation: any two items of the same type are identified; nothing across types; ≈ is identity of sets.",
    src: "Def 13; Thms 14, 17; remark after Thm 29",
    values: {
      LLeq: [false, "after Def 13"], LLPoly: [true, "Thm 14"], Cong: [true, "Thm 17"],
      TopBot: [false, "after Def 13 (⊤ ≡ₜ ⊥ is true)"], Truth: [false, "after Def 13 (LL≡ fails at t with λp.p for F)"],
      Ext: [true, "remark after Thm 29"], Inj: [true, "≈ is identity of sets (§3.3)"],
    } },
  { id: "Mfn", name: "𝔐_fn (a model of PI⁻ only)",
    desc: "≈ is identity of sets; any two items of the same function space are identified; nothing else.",
    src: "Thm 15",
    values: {
      LLeq: [false, "Thm 15"], LLPoly: [true, "Thm 15"], WCong: [false, "Thm 15"],
      Inj: [true, "≈ is identity of sets (§3.3)"],
    } },
  { id: "Mk", name: "𝔐_κ",
    desc: "≈ holds between X and Y when there is a suitable homomorphism from X to Y; it identifies 1→C with 1→D without identifying C and D.",
    src: "Thm 16 and the remark after it",
    values: {
      LLeq: [true, "Thm 16"], LLPoly: [true, "Thm 16"], Cong: [false, "Thm 16"], Inj: [false, "remark after Thm 16"],
    } },
  { id: "Mr", name: "𝔐_ρ",
    desc: "Identifies each item with its images under bijections which replace the type 1 by 1→1 throughout.",
    src: "Thm 18",
    values: {
      LLeq: [true, "Thm 18"], Cong: [true, "Thm 18"], Disjoint: [false, "Thm 18"], LLPoly: [false, "Thm 18"],
    } },
  { id: "Mcard", name: "𝔐_card",
    desc: "≈ is equality of cardinality; items are identified across equinumerous types via fixed bijections.",
    src: "Thm 21 and the remark after it",
    values: {
      LLeq: [true, "Thm 21"], LLPoly: [true, "remark after Thm 21"], Cong: [true, "remark after Thm 21"],
      Recovery: [true, "remark after Thm 21"], Inj: [false, "Thm 21"],
    } },
];

// Results which do not fit the graph (they concern other languages, or are about expressibility).
const otherResults = [
  { title: "Soundness and consistency", src: "Thm 1; Cor 2; Lemma 5",
    text: "PI is sound for its models, and consistent. Every identification on HF⁺ yields a model of PI. The same holds for PI⁻." },
  { title: "Identity within a type", src: "Prop 1",
    text: "For each type σ, PI proves reflexivity, symmetry, and transitivity of ≡_σ." },
  { title: "Shared properties", src: "Prop 2",
    text: "If a polymorphic predicate is identified with itself across types, the items it is true of share a property (PI)." },
  { title: "Corollaries of Cantor", src: "Cors 4–6",
    text: "PI proves (Ex), that some item of some type is identical to no entity; (QT), the negation of the 'Quinean thesis' that every item is identical to an entity; and that no type is identical to the type of its properties." },
  { title: "The item Link provides is unique", src: "Cor 3",
    text: "PI⁻ proves that if x is identical to both y and z, of one type, then y ≡ z." },
  { title: "Disjoint and the slogan", src: "Thm 8",
    text: "PI + Disjoint + ∀β ¬(e ≈ β→t) proves (Slogan); PI does not prove ∀β ¬(e ≈ β→t)." },
  { title: "Simply typed congruence", src: "Thm 5",
    text: "In a classical simply typed logic with reflexivity and Leibniz's law at each type, (SCong) holds." },
  { title: "Simply typed Leibniz's law", src: "Thm 23",
    text: "In a classical simply typed logic with reflexivity, (SCong), and (STruth), Leibniz's law (SLL) holds at each type." },
  { title: "Cross-type Leibniz from Cong", src: "Prop 3",
    text: "PI and Cong imply: if x ≡ y and F ≡ G (across types), then Fx → Gy." },
  { title: "Twin is not simply typed", src: "Thm 9; Cor 7",
    text: "No set of simply typed sentences has exactly the models of PI + Twin, or of PI + ¬Twin. No instance ∀σ x ∃τ y (x ≡ y) with ⟦σ⟧ ≠ ⟦τ⟧ follows from PI + Twin." },
  { title: "Phys", src: "Thm 10",
    text: "(Phys), that everything is identical to something physical of some type, is consistent with PI and independent of it, and no set of simply typed sentences (with 𝒫) has exactly the models of PI + Phys." },
  { title: "Where PCong sits", src: "Thm 27(b); remark after Thm 28",
    text: "Given PI, PCong is equivalent to Cong with α ≈ β added to the antecedent. The mirror-image weakening (Cong with γ ≈ δ added) is inconsistent with PI + Haecceitism." },
  { title: "Infinite types", src: "§12",
    text: "Models of PI with infinite types (over a set type universe) exist just in case there is a strongly inaccessible cardinal; given one, every result here holds with an axiom of infinity added." },
];

window.PIDATA = { SOURCE, principles, baseAxioms, pimTheorems, rules, inconsistent, models, otherResults };
