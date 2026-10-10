import PIBF

/-!
# The profile of `𝔐_hae,ie,d`

In `𝔐_hae,ie,d` (`Wd.MhieDF`), at the actual world items are identified just in case they have the
same root; only at the other world are the entity and the item of `D` (and their haecceities)
identified. `≈` is identity of types, the same at every world.

* Inj≈, Recovery and ND≈ hold, since `≈` is rigid identity of types.
* TBF and BF hold, since identity of propositions is identity.
* PCong holds: at the actual world, identified functions with a common domain have the same root,
  which forces them to have the same type, so they are equal.
* Ext≈ holds: if each item of `α` has the root of an item of `β` and vice versa, then `α = β`.
  Int≈ follows, by LL≡.
* PExt fails: `λx.e₀` and `λx.(haecceity of e₀)` agree, up to `≡`, at every argument, but have
  different types and are their own roots.
-/
set_option autoImplicit false

namespace PIF
open Tm

namespace Wd
open Classical

/-- Identity of propositions, at the actual world, is identity. -/
theorem MhieD_hb : ∀ p q, MhieDF.eqv .t .t p q MhieDF.U.w0 ↔ p = q :=
  fun _ _ => ⟨fun h => MhieD_eq _ _ _ _ h, fun h => h ▸ Or.inl rfl⟩

/-! ## `≈` is rigid identity of types -/

theorem MhieD_Inj : MhieDF.Valid Inj := MhieDF.Inj_of fun _ _ _ => Iff.rfl

theorem MhieD_tr_Recovery : MhieDF.Tr Recovery ↔ ∀ a b c d, MhieDF.teq (.arr a c) (.arr b d) MhieDF.U.w0 ∧
    MhieDF.teq a b MhieDF.U.w0 → MhieDF.teq c d MhieDF.U.w0 := Iff.rfl

theorem MhieD_Recovery : MhieDF.Valid Recovery :=
  (MhieDF.valid_iff_tr _).mpr <| MhieD_tr_Recovery.mpr fun a b c d ⟨h, _⟩ => by
    have h' : Code.arr a c = Code.arr b d := h
    exact (Code.arr.inj h').2

theorem MhieD_NDTeq : MhieDF.Valid NDTeq := MhieDF.NDTeq_of (fun _ => Or.inl rfl) fun _ _ _ => Iff.rfl

/-! ## The Barcan formulas -/

theorem MhieD_TBF : ∀ χ, TBFSch χ → MhieDF.Valid χ := MhieDF.TBF_of MhieD_hb

theorem MhieD_BF : MhieDF.Valid BF := MhieDF.BF_of MhieD_hb

/-! ## PCong holds -/

/-- An item of a function type is its own root, or is a haecceity whose root is no bigger than
its domain. -/
theorem MhieD_root_arr (a c : CHI) (f : univHI.El (.arr a c)) :
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

theorem MhieD_tr_PCong : MhieDF.Tr PCong ↔ ∀ (a c d : CHI) (f : univHI.El a → univHI.El c)
    (g : univHI.El a → univHI.El d) x,
    MhieDF.eqv (.arr a c) (.arr a d) f g MhieDF.U.w0 → MhieDF.eqv c d (f x) (g x) MhieDF.U.w0 := Iff.rfl

theorem MhieD_PCong : MhieDF.Valid PCong :=
  (MhieDF.valid_iff_tr _).mpr <| MhieD_tr_PCong.mpr fun a c d f g _ h => by
    rcases h with h | ⟨hw, _⟩
    · by_cases ecd : c = d
      · subst ecd
        have efg : f = g := rootI_inj (.arr a c) f g h
        subst efg
        exact Or.inl rfl
      · exfalso
        rcases MhieD_root_arr a c f with e1 | ⟨ec, l1⟩ <;> rcases MhieD_root_arr a d g with e2 | ⟨ed, l2⟩
        · have e3 := congrArg Sigma.fst (e1.symm.trans (h.trans e2))
          exact ecd (Code.arr.inj e3).2
        · have k : (Code.arr a c : CHI) = (rootI (.arr a d) g).1 := congrArg Sigma.fst (e1.symm.trans h)
          have l := Nat.le_trans (Nat.le_of_eq (congrArg PIF.csz k)) l2
          simp only [PIF.csz] at l
          omega
        · have k : (Code.arr a d : CHI) = (rootI (.arr a c) f).1 := congrArg Sigma.fst (e2.symm.trans h.symm)
          have l := Nat.le_trans (Nat.le_of_eq (congrArg PIF.csz k)) l1
          simp only [PIF.csz] at l
          omega
        · exact ecd (ec.trans ed.symm)
    · exact absurd hw (fun e => Bool.noConfusion e)

/-! ## PExt fails -/

theorem MhieD_not_PExt : ¬ MhieDF.Valid PExt := fun h => by
  have h0 := MhieDF.tr_PExt.mp ((MhieDF.valid_iff_tr _).mp h) .e .e (.arr .e .t)
    (fun _ => ()) (fun _ => hcyI .e ()) (fun _ => Or.inl (rootI_hcy .e ()).symm)
  rcases h0 with e | ⟨hw, _⟩
  · have e' : (Code.arr .e .e : CHI) = .arr .e (.arr .e .t) := congrArg Sigma.fst e
    exact nomatch (Code.arr.inj e').2
  · exact absurd hw (fun e => Bool.noConfusion e)

/-! ## Ext≈ and Int≈ hold -/

theorem MhieD_ExtT : MhieDF.Valid ExtT :=
  (MhieDF.valid_iff_tr _).mpr <| MhieDF.tr_ExtT.mpr fun a b ⟨h1, h2⟩ => by
    have k1 : ∀ x : univHI.El a, ∃ y : univHI.El b, rootI a x = rootI b y := fun x => by
      obtain ⟨y, hy⟩ := h1 x
      rcases hy with e | ⟨hw, _⟩
      · exact ⟨y, e⟩
      · exact absurd hw (fun e => Bool.noConfusion e)
    have k2 : ∀ y : univHI.El b, ∃ x : univHI.El a, rootI b y = rootI a x := fun y => by
      obtain ⟨x, hx⟩ := h2 y
      rcases hx with e | ⟨hw, _⟩
      · exact ⟨x, e.symm⟩
      · exact absurd hw (fun e => Bool.noConfusion e)
    have l1 := sub_le a b k1
    have l2 := sub_le b a k2
    exact l1.2 (Nat.le_antisymm l1.1 l2.1)

theorem MhieD_IntT : MhieDF.Valid IntT :=
  MhieDF.soundness (Ax := fun χ => χ = LLEqv ∨ χ = ExtT) MhieD_model
    (fun _ h => by
      rcases h with rfl | rfl
      · exact MhieD_LLEqv
      · exact MhieD_ExtT)
    (Derive.d_IntT_of_ExtT (Or.inl rfl) (Or.inr rfl))

end Wd

end PIF
