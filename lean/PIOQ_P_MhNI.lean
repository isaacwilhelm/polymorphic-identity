import PIBF

/-!
# The rest of the profile of `𝔐_hae,ni`

Two worlds, one entity; items are identified, at both worlds, just in case they have the same root
(got by stripping off haecceities); at the actual world `≈` is identity of types, and at the other
world no type is `≈` anything. Identity of propositions is identity, so `□φ` is true just when `φ`
is true at both worlds.
-/
set_option autoImplicit false

namespace PIF
namespace Wd
open Classical

/-! ## Roots -/

/-- An item of a type other than `α → t` is its own root. -/
theorem MhNI_root_nt (a c : Code Empty) (hc : c ≠ .t) (f : univHC.El (.arr a c)) :
    root (.arr a c) f = ⟨.arr a c, f⟩ := by
  cases c with
  | e => rfl
  | t => exact absurd rfl hc
  | base b => exact b.elim
  | arr c d => rfl

/-- The root of an item is the item itself, or of a smaller type. -/
theorem MhNI_root_lt : ∀ (a : Code Empty) (x : univHC.El a), root a x = ⟨a, x⟩ ∨ csz (root a x).1 < csz a
  | .e, _ => Or.inl rfl
  | .t, _ => Or.inl rfl
  | .base b, _ => b.elim
  | .arr a .e, _ => Or.inl rfl
  | .arr a (.base b), _ => b.elim
  | .arr a (.arr c d), _ => Or.inl rfl
  | .arr a .t, f => by
    unfold root
    split
    · rename_i h
      have := root_sz a (Classical.choose h)
      refine Or.inr ?_
      simp only [csz]
      omega
    · exact Or.inl rfl

/-- Every type has an item that is its own root. -/
theorem MhNI_selfroot : ∀ (a : Code Empty), ∃ x : univHC.El a, root a x = ⟨a, x⟩
  | .e => ⟨(), rfl⟩
  | .t => ⟨fun _ => True, rfl⟩
  | .base b => b.elim
  | .arr a .e => ⟨fun _ => (), rfl⟩
  | .arr a (.base b) => b.elim
  | .arr a (.arr c d) => ⟨Classical.choice (Univ.El_nonempty (U := univHC) (.arr a (.arr c d))), rfl⟩
  | .arr a .t => ⟨fun _ _ => False, by
      show (if h : ∃ z, (fun _ _ => False) = hcy a z then root a (Classical.choose h)
        else ⟨.arr a .t, fun _ _ => False⟩) = _
      split
      · rename_i h
        exfalso
        obtain ⟨z, hz⟩ := h
        have e : False = (z = z) := congrFun (congrFun hz z) true
        exact cast e.symm rfl
      · rfl⟩

/-- Functions identified with each other have the same type of values. -/
theorem MhNI_arr_cod (a c d : Code Empty) (f : univHC.El (.arr a c)) (g : univHC.El (.arr a d))
    (h : root (.arr a c) f = root (.arr a d) g) : c = d := by
  by_cases hc : c = .t <;> by_cases hd : d = .t
  · exact hc.trans hd.symm
  · subst hc
    rw [MhNI_root_nt a d hd g] at h
    rcases MhNI_root_lt (.arr a .t) f with e | e
    · rw [e] at h
      exact (Code.arr.inj (congrArg Sigma.fst h)).2
    · rw [h] at e
      simp only [csz] at e
      omega
  · subst hd
    rw [MhNI_root_nt a c hc f] at h
    rcases MhNI_root_lt (.arr a .t) g with e | e
    · rw [e] at h
      exact (Code.arr.inj (congrArg Sigma.fst h)).2
    · rw [← h] at e
      simp only [csz] at e
      omega
  · rw [MhNI_root_nt a c hc f, MhNI_root_nt a d hd g] at h
    exact (Code.arr.inj (congrArg Sigma.fst h)).2

/-- Types with the same roots of items are the same. -/
theorem MhNI_ext_core (a b : Code Empty) (h1 : ∀ x : univHC.El a, ∃ y : univHC.El b, root a x = root b y)
    (h2 : ∀ y : univHC.El b, ∃ x : univHC.El a, root a x = root b y) : a = b := by
  obtain ⟨xa, hxa⟩ := MhNI_selfroot a
  obtain ⟨xb, hxb⟩ := MhNI_selfroot b
  obtain ⟨y, hy⟩ := h1 xa
  obtain ⟨x, hx⟩ := h2 xb
  rw [hxa] at hy
  rw [hxb] at hx
  have l1 := root_sz b y
  rw [← hy] at l1
  have l2 := root_sz a x
  rw [hx] at l2
  rcases MhNI_root_lt b y with e | e
  · rw [e] at hy
    exact congrArg Sigma.fst hy
  · rw [← hy] at e
    simp only at l1 l2 e
    omega

/-! ## Identity of propositions, and `□` -/

theorem MhNI_hb : ∀ p q, MhNI.eqv .t .t p q MhNI.U.w0 ↔ p = q :=
  fun _ _ => ⟨fun h => root_inj _ _ _ h, fun h => h ▸ rfl⟩

theorem MhNI_eqv_top {n : Nat} {Γ : Ctx n} (ρ : MhNI.U.TEnv n) (env : MhNI.U.Env Γ ρ) (p : MhNI.U.El .t) :
    MhNI.eqv .t .t p (MhNI.eval (topF : Fm Γ) ρ env) MhNI.U.w0 ↔ p = fun _ => True := by
  rw [MhNI.eval_topF]
  exact MhNI_hb _ _

/-- `□φ` is true just when `φ` is true at both worlds. -/
theorem MhNI_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MhNI.U.TEnv n) (env : MhNI.U.Env Γ ρ) :
    MhNI.Holds (boxF φ) ρ env ↔ ∀ w, MhNI.HoldsAt φ ρ env w := by
  refine (MhNI.holdsAt_eqv_t φ topF ρ env _).trans ?_
  refine (MhNI_eqv_top ρ env _).trans ⟨fun e w => cast (congrFun e w).symm trivial, fun h => ?_⟩
  exact funext fun w => propext ⟨fun _ => trivial, fun _ => h w⟩

/-! ## Valid -/

theorem MhNI_Bool : ∀ φ, BoolSch φ → MhNI.Valid φ := MhNI.bool_valid fun _ => rfl

theorem MhNI_tr_PCong : MhNI.Tr PCong ↔ ∀ a c d (f : MhNI.U.El a → MhNI.U.El c) (g : MhNI.U.El a → MhNI.U.El d) x,
    MhNI.eqv (.arr a c) (.arr a d) f g MhNI.U.w0 → MhNI.eqv c d (f x) (g x) MhNI.U.w0 := Iff.rfl

theorem MhNI_PCong : MhNI.Valid PCong :=
  (MhNI.valid_iff_tr _).mpr <| MhNI_tr_PCong.mpr fun a c d f g x h => by
    have ecd : c = d := MhNI_arr_cod a c d f g h
    subst ecd
    have efg : f = g := root_inj (.arr a c) f g h
    subst efg
    rfl

theorem MhNI_Inj : MhNI.Valid Inj :=
  (MhNI.valid_iff_tr _).mpr <| MhNI.tr_Inj.mpr fun a b c d h => by
    have e : Code.arr a c = Code.arr b d := h.1
    injection e with e1 e2
    exact ⟨⟨e1, rfl⟩, ⟨e2, rfl⟩⟩

theorem MhNI_tr_Recovery : MhNI.Tr Recovery ↔ ∀ a b c d, MhNI.teq (.arr a c) (.arr b d) MhNI.U.w0 ∧
    MhNI.teq a b MhNI.U.w0 → MhNI.teq c d MhNI.U.w0 := Iff.rfl

theorem MhNI_Recovery : MhNI.Valid Recovery :=
  (MhNI.valid_iff_tr _).mpr <| MhNI_tr_Recovery.mpr fun a b c d ⟨h, _⟩ => by
    have e : Code.arr a c = Code.arr b d := h.1
    exact ⟨(Code.arr.inj e).2, rfl⟩

theorem MhNI_ExtT : MhNI.Valid ExtT :=
  (MhNI.valid_iff_tr _).mpr <| MhNI.tr_ExtT.mpr fun a b ⟨h1, h2⟩ => ⟨MhNI_ext_core a b h1 h2, rfl⟩

theorem MhNI_IntT : MhNI.Valid IntT := by
  intro ρ env
  refine (MhNI.holds_tall _ _ _).mpr fun a => (MhNI.holds_tall _ _ _).mpr fun b => ?_
  refine (MhNI.holds_imp _ _ _ _).mpr fun h => (MhNI.holds_teq _ _ _ _).mpr ?_
  have hs := (MhNI_box _ _ _).mp ((MhNI.holds_conj _ _ _ _).mp h).1 MhNI.U.w0
  have hp := (MhNI_box _ _ _).mp ((MhNI.holds_conj _ _ _ _).mp h).2 MhNI.U.w0
  refine ⟨MhNI_ext_core a b (fun x => ?_) (fun y => ?_), rfl⟩
  · obtain ⟨y, hy⟩ := (MhNI.holds_ex _ _ _ _).mp ((MhNI.holds_all _ _ _ _).mp hs x)
    exact ⟨y, (MhNI.holds_eqv _ _ _ _ _ _).mp hy⟩
  · obtain ⟨x, hx⟩ := (MhNI.holds_ex _ _ _ _).mp ((MhNI.holds_all _ _ _ _).mp hp y)
    exact ⟨x, (MhNI.holds_eqv _ _ _ _ _ _).mp hx⟩

theorem MhNI_NDTeq : MhNI.Valid NDTeq :=
  (MhNI.valid_iff_tr _).mpr <| MhNI.tr_NDTeq.mpr fun a b h => by
    have e : (fun w => ¬ MhNI.teq a b w) = MhNI.eval (topF : Fm Ctx.nil) (fun i => i.elim0) () := by
      refine Eq.trans ?_ (MhNI.eval_topF (Γ := Ctx.nil) _ _).symm
      funext w
      exact propext ⟨fun _ => trivial, fun _ hw => h ⟨hw.1, rfl⟩⟩
    exact (MhNI_hb _ _).mpr e

theorem MhNI_IdId : MhNI.Valid IdId := by
  intro ρ env
  refine (MhNI.holds_tall _ _ _).mpr fun a => ?_
  refine (MhNI.holds_all _ _ _ _).mpr fun x => (MhNI.holds_all _ _ _ _).mpr fun y => ?_
  have key : ∀ w, MhNI.HoldsAt (RD.Ex : Fm (((Ctx.nil.text).ext tv0).ext tv0)) (scons a ρ) ((env, x), y) w ↔
      MhNI.HoldsAt (RD.Ax' : Fm (((Ctx.nil.text).ext tv0).ext tv0)) (scons a ρ) ((env, x), y) w := by
    intro w
    refine (MhNI.holdsAt_eqv _ _ _ _ _ _ w).trans ⟨fun h => ?_, fun h => ?_⟩
    · have e : x = y := root_inj a x y h
      subst e
      exact (MhNI.holdsAt_all _ _ _ _ w).mpr fun G => (MhNI.holdsAt_imp _ _ _ _ w).mpr id
    · have hG := (MhNI.holdsAt_imp _ _ _ _ w).mp ((MhNI.holdsAt_all _ _ _ _ w).mp h (fun z _ => z = x)) rfl
      have e : y = x := hG
      subst e
      rfl
  exact (MhNI.holdsAt_eqv_t _ _ _ _ _).mpr ((MhNI_hb _ _).mpr (funext fun w => propext (key w)))

theorem MhNI_TBF : ∀ χ, TBFSch χ → MhNI.Valid χ := MhNI.TBF_of MhNI_hb

theorem MhNI_TCBF : ∀ χ, TCBFSch χ → MhNI.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MhNI.holds_imp _ _ _ _).mpr fun h => ?_
  exact (MhNI.holds_tall _ _ _).mpr fun a => (MhNI_box _ _ _).mpr fun w =>
    (MhNI.holdsAt_tall _ _ _ w).mp ((MhNI_box _ _ _).mp h w) a

theorem MhNI_BF : MhNI.Valid BF := MhNI.BF_of MhNI_hb
theorem MhNI_CBF : MhNI.Valid CBF := MhNI.CBF_of MhNI_hb
theorem MhNI_Nec : MhNI.Valid Nec := MhNI.Nec_of MhNI_hb fun _ _ _ => rfl

/-! ## Refuted -/

/-- The identity function on entities and the haecceity map agree at each entity, but are
of different types and are their own roots. -/
theorem MhNI_not_PExt : ¬ MhNI.Valid PExt := fun h => by
  have h0 := MhNI.tr_PExt.mp ((MhNI.valid_iff_tr _).mp h) .e .e (.arr .e .t) (fun x => x) (fun x => hcy .e x)
    (fun x => (root_hcy .e x).symm)
  have e : (Code.arr .e .e : Code Empty) = .arr .e (.arr .e .t) := congrArg Sigma.fst h0
  have e2 := (Code.arr.inj e).2
  cases e2

/-- At the other world no type is `≈` anything, so `𝔼β (e ≈ β)` is not necessary. -/
theorem MhNI_not_TNec : ¬ MhNI.Valid TNec := fun h => by
  have h0 := (MhNI.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e
  obtain ⟨b, hb⟩ := (MhNI_box _ _ _).mp h0 false
  exact Bool.false_ne_true ((MhNI.holdsAt_teq (Γ := Ctx.nil.text.text) tv1 tv0 (scons b (scons .e fun i => i.elim0)) () false).mp hb).2

end Wd
end PIF
