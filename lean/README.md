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

8. the **principles** of *Formal Results* as sentences (§10), each with a lemma stating what it
   says in an arbitrary model (§11);
9. the **twelve models** of *Formal Results* (§13), each proved to be a model of PI⁻ (or PI), with
   every truth value the site records for it. 𝔐_κ, 𝔐_card and 𝔐_ρ are simpler constructions
   than the paper's, with the same pattern of truth values.

The website shows a "Lean ✓" badge on every result checked here; `tools/check_lean_refs.py`
verifies that each badge names a real declaration.

10. `PIDerivations.lean`: the derivations and inconsistencies of *Formal Results*, written out as
    formal PI proofs, and the new results found while building the site.
11. `PISchemas.lean`: the two schemas, Theorem 3 (`d_Bridge`: LL≡ proves LL≡/≈ for every
    polymorphic predicate `P`) and the second half of Theorem 11 (`d_LLPoly_of_Disjoint`).

12. `PIExplore.lean`: further models of PI⁻ (𝔐_all, 𝔐_can, 𝔐_cant, 𝔐_D,twin), further values for
    𝔐_D, 𝔐_E, 𝔐_tot, 𝔐_fn, LL≡/≈ from invariance (`Invariance.bridge_valid`), and two derivations
    (Truth ⊢ ⊤≢⊥, Cong ⊢ WCong).
13. `PIHae.lean`: *haecceity towers*, a general construction of models in which every item is
    identified with its haecceity, and three models built with it (𝔐_hae,p, 𝔐_hae⁻, 𝔐_hae,κ).

14. `PITagged.lean`: a broader semantics, in which propositions are pairs of a truth value and a
    tag; the soundness proof is repeated for it, and the model 𝔐_int (Int≈ true, Ext≈ false) is
    built in it.

The files form a Lake project: run `lake build` in this folder.
