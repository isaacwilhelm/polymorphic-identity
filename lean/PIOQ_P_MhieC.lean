import PIBF

/-!
# The profile of `𝔐_hae,ie`

In `𝔐_hae,ie` (`Wd.MhieF`), items are identified at a world just in case they have the same root,
or the world is the actual one and their roots are the entity and the item of `D`. `≈` is identity
of types, the same at every world.

* Inj≈, Recovery and ND≈ hold, since `≈` is rigid identity of types.
* TBF and BF hold, since identity of propositions (at the actual world) is identity.
* PCong holds: two functions with a common domain never have roots which are the entity and the
  item of `D`, so if they are identified they have the same root, which forces them to have the
  same type, so they are equal.
* PExt fails: `λx.e₀` and `λx.(haecceity of e₀)` agree, up to `≡`, at every argument, but have
  different types and are their own roots.
-/
set_option autoImplicit false

namespace PIF
open Tm

namespace Wd
open Classical

/-- Identity of propositions, at the actual world, is identity. -/
theorem MhieC_hb : ∀ p q, MhieF.eqv .t .t p q MhieF.U.w0 ↔ p = q :=
  fun _ _ => ⟨fun h => MhieC_eq _ _ _ _ h, fun h => h ▸ Or.inl rfl⟩

/-! ## `≈` is rigid identity of types -/

theorem MhieC_Inj : MhieF.Valid Inj := MhieF.Inj_of fun _ _ _ => Iff.rfl

theorem MhieC_tr_Recovery : MhieF.Tr Recovery ↔ ∀ a b c d, MhieF.teq (.arr a c) (.arr b d) MhieF.U.w0 ∧
    MhieF.teq a b MhieF.U.w0 → MhieF.teq c d MhieF.U.w0 := Iff.rfl

theorem MhieC_Recovery : MhieF.Valid Recovery :=
  (MhieF.valid_iff_tr _).mpr <| MhieC_tr_Recovery.mpr fun a b c d ⟨h, _⟩ => by
    have h' : Code.arr a c = Code.arr b d := h
    exact (Code.arr.inj h').2

theorem MhieC_NDTeq : MhieF.Valid NDTeq := MhieF.NDTeq_of (fun _ => Or.inl rfl) fun _ _ _ => Iff.rfl

/-! ## The Barcan formulas -/

theorem MhieC_TBF : ∀ χ, TBFSch χ → MhieF.Valid χ := MhieF.TBF_of MhieC_hb

theorem MhieC_BF : MhieF.Valid BF := MhieF.BF_of MhieC_hb

/-! ## PCong holds -/

/-- An item of a function type is its own root, or is a haecceity whose root is no bigger than
its domain. -/
theorem MhieC_root_arr (a c : CHI) (f : univHI.El (.arr a c)) :
    rootI (.arr a c) f = ⟨.arr a c, f⟩ ∨ (c = .t ∧ PIF.csz (rootI (.arr a c) f).1 ≤ PIF.csz a) := by
  cases c with
  | t =>
    by_cases hf : ∃ z, f = hcyI a z
    · obtain ⟨z, rfl⟩ := hf
      refine Or.inr ⟨rfl, ?_⟩
      rw [rootI_hcy]
      exact rootI_le a z
    · exact Or.inl (rootI_not a f hf)
  | e => exact Or.inl rfl
  | base _ => exact Or.inl rfl
  | arr _ _ => exact Or.inl rfl

/-- The bottoms of two function types with a common domain are not `e` and `D`. -/
theorem MhieC_foot_arr (a c d : CHI) (h1 : foot (.arr a c) = .e) (h2 : foot (.arr a d) = .base ()) :
    False := by
  cases c with
  | t =>
    cases d with
    | t =>
      have h1' : foot a = .e := h1
      have h2' : foot a = .base () := h2
      rw [h1'] at h2'
      exact nomatch h2'
    | e => exact nomatch h2
    | base _ => exact nomatch h2
    | arr _ _ => exact nomatch h2
  | e => exact nomatch h1
  | base _ => exact nomatch h1
  | arr _ _ => exact nomatch h1

/-- Two functions with a common domain never have roots which are the entity and the item of `D`. -/
theorem MhieC_no_cross (a c d : CHI) (f : univHI.El (.arr a c)) (g : univHI.El (.arr a d)) :
    ¬ crossI (rootI (.arr a c) f) (rootI (.arr a d) g) := fun h => by
  have f1 := foot_rootI (.arr a c) f
  have f2 := foot_rootI (.arr a d) g
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at f1
    rw [h2] at f2
    exact MhieC_foot_arr a c d f1.symm f2.symm
  · rw [h1] at f1
    rw [h2] at f2
    exact MhieC_foot_arr a d c f2.symm f1.symm

theorem MhieC_tr_PCong : MhieF.Tr PCong ↔ ∀ (a c d : CHI) (f : univHI.El (.arr a c))
    (g : univHI.El (.arr a d)) (x : univHI.El a),
    MhieF.eqv (.arr a c) (.arr a d) f g univHI.w0 → MhieF.eqv c d (f x) (g x) univHI.w0 := Iff.rfl

theorem MhieC_PCong : MhieF.Valid PCong :=
  (MhieF.valid_iff_tr _).mpr <| MhieC_tr_PCong.mpr fun a c d f g _ h => by
    rcases h with h | ⟨_, hc⟩
    · by_cases ecd : c = d
      · subst ecd
        have efg : f = g := rootI_inj _ f g h
        subst efg
        exact Or.inl rfl
      · exfalso
        rcases MhieC_root_arr a c f with e1 | ⟨ec, l1⟩ <;> rcases MhieC_root_arr a d g with e2 | ⟨ed, l2⟩
        · have e3 := congrArg Sigma.fst (e1.symm.trans (h.trans e2))
          exact ecd (Code.arr.inj e3).2
        · have e3 : PIF.csz (rootI (.arr a d) g).1 = PIF.csz a + PIF.csz c + 1 :=
            congrArg (fun r : (Σ b : CHI, univHI.El b) => PIF.csz r.1) (h.symm.trans e1)
          omega
        · have e3 : PIF.csz (rootI (.arr a c) f).1 = PIF.csz a + PIF.csz d + 1 :=
            congrArg (fun r : (Σ b : CHI, univHI.El b) => PIF.csz r.1) (h.trans e2)
          omega
        · exact ecd (ec.trans ed.symm)
    · exact absurd hc (MhieC_no_cross a c d f g)

/-! ## PExt fails -/

theorem MhieC_not_PExt : ¬ MhieF.Valid PExt := fun h => by
  have h0 := MhieF.tr_PExt.mp ((MhieF.valid_iff_tr _).mp h) .e .e (.arr .e .t)
    (fun _ => ()) (fun _ => hcyI .e ()) (fun _ => Or.inl (rootI_hcy .e ()).symm)
  rcases h0 with e | ⟨_, hc⟩
  · have e' : (Code.arr .e .e : CHI) = .arr .e (.arr .e .t) := congrArg Sigma.fst e
    exact nomatch (Code.arr.inj e').2
  · exact MhieC_no_cross .e .e (.arr .e .t) _ _ hc

end Wd

end PIF
