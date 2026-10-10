import PIBF
set_option autoImplicit false

/-!
# Open questions: the profile of `𝔐_hae⁻`

The haecceity tower `Mhm` of `PIHae.lean`, over `E = 1`: every property of the entity has the root of
the entity, the haecceity of an item has the root of the item, and every other item is its own root.
Items are identified just in case their roots agree, and `≈` is identity of types.

At `t` every proposition is its own root, so `≡_t` is identity: Truth, ⊤≢⊥ and T hold. The entity and
all its properties share a root: so Cantor fails at `e`, and `e` and `e→t` cover each other without
being the same type (Ext≈, and so Int≈, fail). The empty and the universal property of the entity are
identified, but differ in their properties: so IdId fails (and with it Classicism), and the polymorphic
predicate "has a property identified with `λH.∀x Hx`" refutes LL≡/≈. The constant functions on
entities with values the empty and the universal property have identified values everywhere, but each
is its own root: so PExt fails.
-/

namespace PIF

section MhmP
attribute [local instance] Classical.propDecidable

/-! ## Roots -/

theorem Mhm_hr_e (x : unitUniv.El .e) : hr ovHM .e x = ⟨.e, ()⟩ := by
  show ovHM .e x = _
  unfold ovHM
  split
  · next h => cases h
  · rfl

/-- An item of `e→(e→t)` is its own root. -/
theorem Mhm_hr_eet (f : unitUniv.El (.arr .e (.arr .e .t))) :
    hr ovHM (.arr .e (.arr .e .t)) f = ⟨.arr .e (.arr .e .t), f⟩ := by
  show ovHM _ f = _
  unfold ovHM
  split
  · next h => injection h with _ h2; cases h2
  · rfl

/-- An item of `(e→t)→t` is either true of the empty property and has the root of the entity
(when it is a haecceity), or is its own root. -/
theorem Mhm_hr_ett (G : unitUniv.El (.arr (.arr .e .t) .t)) :
    (G (fun _ => False) ∧ hr ovHM (.arr (.arr .e .t) .t) G = ⟨.e, ()⟩) ∨
      hr ovHM (.arr (.arr .e .t) .t) G = ⟨.arr (.arr .e .t) .t, G⟩ := by
  rw [hr_arr_t]
  split
  · next h =>
    exact Or.inl ⟨(congrFun (Classical.choose_spec h) _).mpr ((hrHM_et _).trans (hrHM_et _).symm),
      hrHM_et _⟩
  · refine Or.inr ?_
    unfold ovHM
    split
    · next h => injection h with h1 _; cases h1
    · rfl

theorem Mhm_eqv_t (p q : Prop) : Mhm.eqv .t .t p q ↔ p = q :=
  ⟨fun h => by
    have h' : hr ovHM .t p = hr ovHM .t q := h
    rw [hrHM_t, hrHM_t] at h'
    exact eq_of_heq (Sigma.mk.inj h').2,
   fun h => h ▸ MhmD.refl _⟩

/-- The empty and the universal property of the entity are identified. -/
theorem Mhm_FT : Mhm.eqv (.arr .e .t) (.arr .e .t) (fun _ => False : unitUniv.El (.arr .e .t)) (fun _ => True) :=
  (hrHM_et _).trans (hrHM_et _).symm

/-! ## Propositions -/

theorem Mhm_Truth : Mhm.Valid Truth :=
  (Mhm.valid_iff_tr _).mpr <| Mhm.tr_Truth.mpr fun _ _ h hp => cast ((Mhm_eqv_t _ _).mp h) hp

theorem Mhm_TopBot : Mhm.Valid TopBot :=
  (Mhm.valid_iff_tr _).mpr <| Mhm.tr_TopBot.mpr fun h => by
    have e : (¬ ∀ p : Prop, p) = (∀ p : Prop, p) := (Mhm_eqv_t _ _).mp h
    exact (cast e (fun hall => hall False)) False

/-- IdId fails: the empty and the universal property of the entity are identified, but differ in
their properties. -/
theorem Mhm_not_IdId : ¬ Mhm.Valid IdId := fun h => by
  have := Mhm.tr_IdId.mp ((Mhm.valid_iff_tr _).mp h) (.arr .e .t) (fun _ => False) (fun _ => True)
  have e := (Mhm_eqv_t _ _).mp this
  exact cast e Mhm_FT (fun g => ¬ g ()) id trivial

/-! ## Identification across types -/

/-- Cantor fails at `e`: every property of the entity is identified with the entity. -/
theorem Mhm_not_Cantor : ¬ Mhm.Valid Cantor := fun h => by
  obtain ⟨G, hG⟩ := Mhm.tr_Cantor.mp ((Mhm.valid_iff_tr _).mp h) .e
  exact hG () ((hrHM_et G).trans (Mhm_hr_e ()).symm)

/-- Ext≈ fails: `e` and `e→t` cover each other, but are different types. -/
theorem Mhm_not_ExtT : ¬ Mhm.Valid ExtT := fun h => by
  have := Mhm.tr_ExtT.mp ((Mhm.valid_iff_tr _).mp h) .e (.arr .e .t)
    ⟨fun x => ⟨fun _ => True, (Mhm_hr_e x).trans (hrHM_et _).symm⟩,
     fun y => ⟨(), (Mhm_hr_e ()).trans (hrHM_et y).symm⟩⟩
  cases this

theorem Mhm_not_IntT : ¬ Mhm.Valid IntT := fun h => Mhm_not_ExtT ((Mhm.IntT_iff_ExtT Mhm_eqv_t).mp h)

/-! ## PExt -/

/-- PExt fails: the constant functions on entities with values the empty and the universal property
have identified values everywhere, but each is its own root. -/
theorem Mhm_not_PExt : ¬ Mhm.Valid PExt := fun h => by
  have := Mhm.tr_PExt.mp ((Mhm.valid_iff_tr _).mp h) .e (.arr .e .t) (.arr .e .t)
    (fun _ _ => False) (fun _ _ => True) (fun _ => Mhm_FT)
  have e := (Mhm_hr_eet (fun _ _ => False)).symm.trans
    ((this : hr ovHM (.arr .e (.arr .e .t)) (fun _ _ => False) =
      hr ovHM (.arr .e (.arr .e .t)) (fun _ _ => True)).trans (Mhm_hr_eet (fun _ _ => True)))
  exact cast (congrFun (congrFun (eq_of_heq (Sigma.mk.inj e).2) ()) ()).symm trivial

/-! ## LL≡/≈ -/

open Tm in
/-- The polymorphic predicate `λγ.λz:γ. ∃_{γ→t} F (F z ∧ F ≡_{γ→t,(e→t)→t} λH:e→t.∀_e x (H x))`. -/
def Mhm_PredK : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (ex tv0.pred (conj (.app (.var .here) (.var (.there .here)))
    (eqv tv0.pred tyE.pred.pred (.var .here)
      (.lam tyE.pred (all tyE (.app (.var (.there .here)) (.var .here))))))))

theorem Mhm_tr_Bridge : Mhm.Tr (Bridge Mhm_PredK) ↔ ∀ a b (x : Mhm.U.El a) (y : Mhm.U.El b),
    Mhm.eqv a b x y ∧ Mhm.teq a b →
    (∃ F : Mhm.U.El a → Prop, F x ∧
      Mhm.eqv (.arr a .t) (.arr (.arr .e .t) .t) F (fun H : Mhm.U.El (.arr .e .t) => ∀ z, H z)) →
    (∃ F : Mhm.U.El b → Prop, F y ∧
      Mhm.eqv (.arr b .t) (.arr (.arr .e .t) .t) F (fun H : Mhm.U.El (.arr .e .t) => ∀ z, H z)) := Iff.rfl

/-- LL≡/≈ fails: the universal property of the entity has a property identified with
`λH.∀x Hx` (namely that one), and the empty property does not. -/
theorem Mhm_not_Bridge : ¬ Mhm.Valid (Bridge Mhm_PredK) := fun h => by
  obtain ⟨F, hF, hFK⟩ := Mhm_tr_Bridge.mp ((Mhm.valid_iff_tr _).mp h) (.arr .e .t) (.arr .e .t)
    (fun _ => True) (fun _ => False) ⟨Mhm_FT.symm, rfl⟩
    ⟨fun H => ∀ z, H z, fun _ => trivial, MhmD.refl _⟩
  have hFK' : hr ovHM (.arr (.arr .e .t) .t) F =
      hr ovHM (.arr (.arr .e .t) .t) (fun H : unitUniv.El (.arr .e .t) => ∀ z, H z) := hFK
  rcases Mhm_hr_ett (fun H : unitUniv.El (.arr .e .t) => ∀ z, H z) with ⟨hK, _⟩ | hK
  · exact hK ()
  · rcases Mhm_hr_ett F with ⟨_, hF1⟩ | hF1
    · cases congrArg Sigma.fst (hF1.symm.trans (hFK'.trans hK))
    · have e : F = fun H : unitUniv.El (.arr .e .t) => ∀ z, H z :=
        eq_of_heq (Sigma.mk.inj (hF1.symm.trans (hFK'.trans hK))).2
      subst e
      exact hF ()

/-! ### By soundness -/

theorem Mhm_of_prov {S : Fm Ctx.nil → Prop} (hS : ∀ ψ, S ψ → Mhm.Valid ψ) {φ : Fm Ctx.nil}
    (h : Prov S Ctx.nil φ) : Mhm.Valid φ :=
  Mhm.soundness Mhm_model hS h

/-- Classicism fails, since it proves IdId (in PI⁻). -/
theorem Mhm_not_Class : ¬ ∀ χ, ClassSch χ → Mhm.Valid χ := fun h =>
  Mhm_not_IdId (Mhm_of_prov h (d_IdId_of_Class (S := ClassSch) (fun _ hc => hc)))

theorem Mhm_TAx : Mhm.Valid TAx :=
  Mhm_of_prov (S := (· = Truth)) (fun _ h => h ▸ Mhm_Truth) (d_TAx_of_Truth rfl)

end MhmP

end PIF
