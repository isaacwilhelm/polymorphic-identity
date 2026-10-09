# PI in Lean: the foundation

`PIFoundation.lean` is a deep embedding of the logic of polymorphic identity:

1. the language (categories, contexts, terms), with renaming and substitution;
2. models (type universes and frames) and the semantic value of every term;
3. the substitution lemmas connecting the two;
4. β-conversion;
5. the proof system PI⁻ (and PI = PI⁻ + LL≡), with the **soundness theorem**
   (`Frame.soundness`, `Frame.soundness_PI`): whatever PI derives is true in every model;
6. **consistency** of PI (`PI_consistent`), via the diagonal model;
7. the **invariance lemma** in relational (parametricity) form (`Invariance.fundamental`), with its
   consequences: when LL≈ holds (`Invariance.llTeq_valid`, Lemma 8(b) of *Formal Results*) and when
   LL≡-Poly holds (`Invariance.llPoly_valid`, Lemma 8(a)); checked on the diagonal model (`diag_LLPoly`).

To check it, install Lean (https://lean-lang.org) and run

    lean PIFoundation.lean

No output means every proof checks. It uses no `sorry` and only Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). GitHub re-checks it on every push
(`.github/workflows/lean.yml`).

Next milestones: the models of *Formal Results* (𝔐_κ, 𝔐_card, 𝔐_ρ, the identifications ∼₀, ∼₁,
∼ₕ, …), and the derivations as PI proofs.
