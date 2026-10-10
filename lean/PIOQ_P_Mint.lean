import PIBF

/-!
# The remaining profile of `𝔐_int`

The model `MiF` of `PITagged.lean`: tagged propositions, in which every quantified proposition
(over items or over types) carries the tag `false`, and the other logical constants give the tag
`true`. Identity at `t` is identity of tagged propositions, so `□φ` (that is, `φ ≡_t ⊤`) is true just
when `φ` is true and has the tag `true`. So `□` of a quantified proposition is always false:

* ND× holds, since `¬(x ≡ y)` has the tag `true`;
* TCBF and CBF hold vacuously, since their antecedents `□𝔸α φ` and `□∀x F x` are false;
* TBF, BF, TNec and Nec fail, since their consequents (or the formula itself) put a quantified
  proposition under `□`.
-/
set_option autoImplicit false

namespace PIF
namespace Tg
open Tm

/-- `□φ` implies that `φ` has the tag `true`. -/
theorem Mint_box_tag {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MiF.U.TEnv n) (env : MiF.U.Env Γ ρ)
    (h : MiF.Holds (boxF φ) ρ env) : (MiF.eval φ ρ env).2 = true :=
  congrArg Prod.snd (eq_of_heq ((MiF.holds_eqv_t _ _ _ _).mp h).2)

/-! ## Necessity of distinctness across types -/

theorem Mint_NDX : MiF.Valid NDX := by
  intro ρ env a b
  refine (MiF.holds_all _ _ _ _).mpr fun x => (MiF.holds_all _ _ _ _).mpr fun y h => ?_
  exact (MiF.holds_eqv_t _ _ _ _).mpr
    ⟨rfl, heq_of_eq (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl)⟩

/-! ## Barcan formulas for the type quantifiers, and Type Necessitism -/

/-- `𝔸α ⊤` is type-quantified, so it has the tag `false` and is not identical to `⊤`. -/
theorem Mint_not_TBF : ¬ ∀ χ, TBFSch χ → MiF.Valid χ := fun h => by
  have h0 := h _ ⟨topF, rfl⟩ (fun i => i.elim0) ()
  have hb := (MiF.holds_imp _ _ _ _).mp h0 (fun _ => (MiF.holds_eqv_t _ _ _ _).mpr ⟨rfl, HEq.rfl⟩)
  exact Bool.noConfusion (Mint_box_tag _ _ _ hb : false = true)

theorem Mint_TCBF : ∀ χ, TCBFSch χ → MiF.Valid χ := by
  rintro χ ⟨φ, rfl⟩ ρ env hb
  exact Bool.noConfusion (Mint_box_tag _ _ _ hb : false = true)

theorem Mint_not_TNec : ¬ MiF.Valid TNec := fun h => by
  have hb := (MiF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e
  exact Bool.noConfusion (Mint_box_tag _ _ _ hb : false = true)

/-! ## Barcan formulas for the item quantifiers, and Necessitism -/

theorem Mint_tr_BF : MiF.Tr BF ↔
    ∀ a (G : univI.El a → TV), (∀ x, MiF.eqv .t .t (G x) ((¬ ∀ p : TV, p.1 : Prop), true)) →
      MiF.eqv .t .t ((∀ x, (G x).1 : Prop), false) ((¬ ∀ p : TV, p.1 : Prop), true) := Iff.rfl

theorem Mint_tr_CBF : MiF.Tr CBF ↔
    ∀ a (G : univI.El a → TV), MiF.eqv .t .t ((∀ x, (G x).1 : Prop), false) ((¬ ∀ p : TV, p.1 : Prop), true) →
      ∀ x, MiF.eqv .t .t (G x) ((¬ ∀ p : TV, p.1 : Prop), true) := Iff.rfl

theorem Mint_tr_Nec : MiF.Tr Nec ↔
    ∀ a (x : univI.El a), MiF.eqv .t .t ((∃ y, MiF.eqv a a x y : Prop), false)
      ((¬ ∀ p : TV, p.1 : Prop), true) := Iff.rfl

/-- `∀x ⊤` is quantified, so it has the tag `false`: `□⊤` holds of every entity, but `□∀x ⊤` is false. -/
theorem Mint_not_BF : ¬ MiF.Valid BF := fun h => by
  have h1 := Mint_tr_BF.mp ((MiF.valid_iff_tr _).mp h) .e (fun _ => ((¬ ∀ p : TV, p.1 : Prop), true))
    (fun _ => ⟨rfl, HEq.rfl⟩)
  exact Bool.noConfusion (congrArg Prod.snd (eq_of_heq h1.2) : false = true)

theorem Mint_CBF : MiF.Valid CBF := (MiF.valid_iff_tr _).mpr <| Mint_tr_CBF.mpr fun _ _ h =>
  absurd (congrArg Prod.snd (eq_of_heq h.2)) Bool.false_ne_true

/-- `∃y (x ≡ y)` is quantified, so it has the tag `false` and is not identical to `⊤`. -/
theorem Mint_not_Nec : ¬ MiF.Valid Nec := fun h => by
  have h1 := Mint_tr_Nec.mp ((MiF.valid_iff_tr _).mp h) .e (show univI.El .e from ())
  exact Bool.noConfusion (congrArg Prod.snd (eq_of_heq h1.2) : false = true)

end Tg
end PIF
