import PIBF
set_option autoImplicit false

/-!
# The profile of `𝔐_hae,c`

In `𝔐_hae,c` (`Wd.MhaeCF`), there are two worlds and one entity; items are identified, at every
world, just in case they have the same root (got by stripping off haecceities). `≈` is identity of
types, the same at every world.

* Inj≈, Recovery and ND≈ hold, since `≈` is rigid identity of types.
* TBF holds, since identity of propositions is identity.
* PCong holds: identified functions with a common domain have the same root, which forces them to
  have the same type, so they are equal.
* PExt fails: `λx.e₀ : e→e` and `λx.(haecceity of e₀) : e→(e→t)` agree, up to `≡`, at every
  argument, but have different types and are their own roots.
* Ext≈ holds: if each item of `α` has the root of an item of `β` and vice versa, then `α = β`.
  Int≈ follows, by LL≡.
-/

namespace PIF
open Tm

namespace Wd
open Classical

/-! ## Roots -/

theorem MhaeC_root_not (a : Code Empty) (f : univHC.El (.arr a .t)) (hf : ¬ ∃ z, f = hcy a z) :
    root (.arr a .t) f = ⟨.arr a .t, f⟩ := by
  show (if h : ∃ z, f = hcy a z then root a (Classical.choose h) else ⟨.arr a .t, f⟩) = _
  split
  · exact absurd ‹_› hf
  · rfl

/-- An item either is its own root, or has a root of a smaller type. -/
theorem MhaeC_root_lt : ∀ (a : Code Empty) (x : univHC.El a),
    root a x = ⟨a, x⟩ ∨ Wd.csz (root a x).1 < Wd.csz a
  | .e, _ => Or.inl rfl
  | .t, _ => Or.inl rfl
  | .base b, _ => b.elim
  | .arr _ .e, _ => Or.inl rfl
  | .arr _ (.base b), _ => b.elim
  | .arr _ (.arr _ _), _ => Or.inl rfl
  | .arr a .t, f => by
    by_cases hf : ∃ z, f = hcy a z
    · obtain ⟨z, rfl⟩ := hf
      refine Or.inr ?_
      have k : Wd.csz (root (.arr a .t) (hcy a z)).1 = Wd.csz (root a z).1 :=
        congrArg (fun r : (Σ b : Code Empty, univHC.El b) => Wd.csz r.1) (root_hcy a z)
      have k2 : Wd.csz (Code.arr a .t : Code Empty) = Wd.csz a + 0 + 1 := rfl
      have l := root_sz a z
      omega
    · exact Or.inl (MhaeC_root_not a f hf)

/-- Every type has an item which is its own root. -/
theorem MhaeC_own_item : ∀ a : Code Empty, ∃ x : univHC.El a, root a x = ⟨a, x⟩
  | .e => ⟨(), rfl⟩
  | .t => ⟨fun _ => True, rfl⟩
  | .base b => b.elim
  | .arr _ .e => ⟨fun _ => (), rfl⟩
  | .arr _ (.base b) => b.elim
  | .arr a (.arr c d) => ⟨Classical.choice (Univ.El_nonempty (U := univHC) (.arr a (.arr c d))), rfl⟩
  | .arr a .t => ⟨fun _ _ => False,
      MhaeC_root_not a _ fun ⟨z, hz⟩ => cast (congrFun (congrFun hz z) true).symm rfl⟩

/-- If every item of `a` has the root of an item of `b`, then `a` is no bigger than `b`. -/
theorem MhaeC_sub_le (a b : Code Empty) (h : ∀ x : univHC.El a, ∃ y : univHC.El b, root a x = root b y) :
    Wd.csz a ≤ Wd.csz b ∧ (Wd.csz a = Wd.csz b → a = b) := by
  obtain ⟨x, hx⟩ := MhaeC_own_item a
  obtain ⟨y, hy⟩ := h x
  rw [hx] at hy
  have l := root_sz b y
  rw [← hy] at l
  refine ⟨l, fun e => ?_⟩
  rcases MhaeC_root_lt b y with e2 | e2
  · rw [e2] at hy; exact congrArg Sigma.fst hy
  · rw [← hy] at e2; simp only at e2; omega

/-- An item of a function type is its own root, or is a haecceity whose root is no bigger than
its domain. -/
theorem MhaeC_root_arr (a c : Code Empty) (f : univHC.El (.arr a c)) :
    root (.arr a c) f = ⟨.arr a c, f⟩ ∨ (c = .t ∧ Wd.csz (root (.arr a c) f).1 ≤ Wd.csz a) := by
  cases c with
  | t =>
    by_cases hf : ∃ z, f = hcy a z
    · obtain ⟨z, rfl⟩ := hf
      refine Or.inr ⟨rfl, ?_⟩
      rw [root_hcy]
      exact root_sz a z
    · exact Or.inl (MhaeC_root_not a f hf)
  | e => exact Or.inl rfl
  | base b => exact b.elim
  | arr _ _ => exact Or.inl rfl

/-! ## `≈` is rigid identity of types -/

theorem MhaeC_Inj : MhaeCF.Valid Inj := MhaeCF.Inj_of fun _ _ _ => Iff.rfl

theorem MhaeC_tr_Recovery : MhaeCF.Tr Recovery ↔ ∀ a b c d, MhaeCF.teq (.arr a c) (.arr b d) MhaeCF.U.w0 ∧
    MhaeCF.teq a b MhaeCF.U.w0 → MhaeCF.teq c d MhaeCF.U.w0 := Iff.rfl

theorem MhaeC_Recovery : MhaeCF.Valid Recovery :=
  (MhaeCF.valid_iff_tr _).mpr <| MhaeC_tr_Recovery.mpr fun a b c d ⟨h, _⟩ => by
    have h' : Code.arr a c = Code.arr b d := h
    exact (Code.arr.inj h').2

theorem MhaeC_NDTeq : MhaeCF.Valid NDTeq := MhaeCF.NDTeq_of (fun _ => rfl) fun _ _ _ => Iff.rfl

/-! ## TBF -/

theorem MhaeC_TBF : ∀ χ, TBFSch χ → MhaeCF.Valid χ :=
  MhaeCF.TBF_of fun p q => ⟨MhaeC_eq .t p q _, fun h => h ▸ rfl⟩

/-! ## PCong holds -/

theorem MhaeC_tr_PCong : MhaeCF.Tr PCong ↔ ∀ (a c d : Code Empty) (f : univHC.El (.arr a c))
    (g : univHC.El (.arr a d)) (x : univHC.El a),
    MhaeCF.eqv (.arr a c) (.arr a d) f g univHC.w0 → MhaeCF.eqv c d (f x) (g x) univHC.w0 := Iff.rfl

theorem MhaeC_PCong : MhaeCF.Valid PCong :=
  (MhaeCF.valid_iff_tr _).mpr <| MhaeC_tr_PCong.mpr fun a c d f g _ h => by
    have h' : root (.arr a c) f = root (.arr a d) g := h
    by_cases ecd : c = d
    · subst ecd
      have efg : f = g := root_inj _ f g h'
      subst efg
      exact rfl
    · exfalso
      rcases MhaeC_root_arr a c f with e1 | ⟨ec, l1⟩ <;> rcases MhaeC_root_arr a d g with e2 | ⟨ed, l2⟩
      · have e3 := congrArg Sigma.fst (e1.symm.trans (h'.trans e2))
        exact ecd (Code.arr.inj e3).2
      · have e3 : Wd.csz (root (.arr a d) g).1 = Wd.csz a + Wd.csz c + 1 :=
          congrArg (fun r : (Σ b : Code Empty, univHC.El b) => Wd.csz r.1) (h'.symm.trans e1)
        omega
      · have e3 : Wd.csz (root (.arr a c) f).1 = Wd.csz a + Wd.csz d + 1 :=
          congrArg (fun r : (Σ b : Code Empty, univHC.El b) => Wd.csz r.1) (h'.trans e2)
        omega
      · exact ecd (ec.trans ed.symm)

/-! ## PExt fails -/

/-- `λx.e₀ : e→e` and `λx.(haecceity of e₀) : e→(e→t)` agree, up to `≡`, at every argument, but
have different types and are their own roots. -/
theorem MhaeC_not_PExt : ¬ MhaeCF.Valid PExt := fun h => by
  have h0 := MhaeCF.tr_PExt.mp ((MhaeCF.valid_iff_tr _).mp h) .e .e (.arr .e .t)
    (fun _ => ()) (fun _ => hcy .e ()) (fun _ => (root_hcy .e ()).symm)
  have h1 : root (.arr .e .e) (fun _ => ()) = root (.arr .e (.arr .e .t)) (fun _ => hcy .e ()) := h0
  have e' : (Code.arr .e .e : Code Empty) = .arr .e (.arr .e .t) := congrArg Sigma.fst h1
  exact nomatch (Code.arr.inj e').2

/-! ## Ext≈ and Int≈ hold -/

theorem MhaeC_ExtT : MhaeCF.Valid ExtT :=
  (MhaeCF.valid_iff_tr _).mpr <| MhaeCF.tr_ExtT.mpr fun a b ⟨h1, h2⟩ => by
    have k1 : ∀ x : univHC.El a, ∃ y : univHC.El b, root a x = root b y := h1
    have k2 : ∀ y : univHC.El b, ∃ x : univHC.El a, root b y = root a x := fun y => by
      obtain ⟨x, hx⟩ := h2 y
      have hx' : root a x = root b y := hx
      exact ⟨x, hx'.symm⟩
    have l1 := MhaeC_sub_le a b k1
    have l2 := MhaeC_sub_le b a k2
    exact l1.2 (Nat.le_antisymm l1.1 l2.1)

theorem MhaeC_IntT : MhaeCF.Valid IntT :=
  MhaeCF.soundness (Ax := fun χ => χ = LLEqv ∨ χ = ExtT) MhaeC_model
    (fun _ h => by
      rcases h with rfl | rfl
      · exact MhaeC_LLEqv
      · exact MhaeC_ExtT)
    (Derive.d_IntT_of_ExtT (Or.inl rfl) (Or.inr rfl))

end Wd

end PIF
