import PIBF

/-!
# The rest of the profile of `𝔐_hae,e`

The model `MhEF` of `lean/PIModalX2.lean`: two worlds, one entity. Items are identified at the actual
world just in case they have the same root (got by stripping off haecceities, where the haecceity of
`z` is the property of being `z` at the actual world); at the other world nothing is identified with
anything. `≈` is identity of types, at both worlds.

Identity of propositions (at the actual world) is identity, so `□φ` is true just when `φ` is true at
both worlds.
-/
set_option autoImplicit false

namespace PIF
namespace Wd
open Classical

/-! ## Roots -/

/-- An item of a type other than `α → t` is its own root. -/
theorem MhE_root_nt (a c : Code Empty) (hc : c ≠ .t) (f : univHC.El (.arr a c)) :
    rootE (.arr a c) f = ⟨.arr a c, f⟩ := by
  cases c with
  | e => rfl
  | t => exact absurd rfl hc
  | base b => exact b.elim
  | arr c d => rfl

/-- Every type has an item that is its own root. -/
theorem MhE_selfroot : ∀ (a : Code Empty), ∃ x : univHC.El a, rootE a x = ⟨a, x⟩
  | .e => ⟨(), rfl⟩
  | .t => ⟨fun _ => True, rfl⟩
  | .base b => b.elim
  | .arr a .e => ⟨fun _ => (), rfl⟩
  | .arr a (.base b) => b.elim
  | .arr a (.arr c d) => ⟨Classical.choice (Univ.El_nonempty (U := univHC) (.arr a (.arr c d))), rfl⟩
  | .arr a .t => ⟨fun _ _ => False, groot_not univHC.El hcyE a _ fun ⟨z, hz⟩ => by
      have e : False = (z = z ∧ true = true) := congrFun (congrFun hz z) true
      exact cast e.symm ⟨rfl, rfl⟩⟩

/-- An item is its own root, or its root lies at a smaller type. -/
theorem MhE_root_lt (a : Code Empty) (x : univHC.El a) :
    rootE a x = ⟨a, x⟩ ∨ PIF.csz (rootE a x).1 < PIF.csz a :=
  groot_lt univHC.El hcyE a x

/-- If the root of `x : α` is `y : β`, then `β` is `α` or a smaller type. -/
theorem MhE_root_eq_cases (a : Code Empty) (x : univHC.El a) (b : Code Empty) (y : univHC.El b)
    (h : rootE a x = ⟨b, y⟩) : a = b ∨ PIF.csz b < PIF.csz a := by
  rcases MhE_root_lt a x with e | e
  · exact Or.inl (congrArg Sigma.fst (e.symm.trans h))
  · exact Or.inr (Nat.lt_of_le_of_lt
      (Nat.le_of_eq (congrArg (fun p : (Σ c : Code Empty, univHC.El c) => PIF.csz p.1) h).symm) e)

/-- Functions with the same root have the same type of values. -/
theorem MhE_arr_cod (a c d : Code Empty) (f : univHC.El (.arr a c)) (g : univHC.El (.arr a d))
    (h : rootE (.arr a c) f = rootE (.arr a d) g) : c = d := by
  by_cases hc : c = .t <;> by_cases hd : d = .t
  · exact hc.trans hd.symm
  · subst hc
    have := PIF.csz_pos d
    rcases MhE_root_eq_cases _ f _ g (h.trans (MhE_root_nt a d hd g)) with e | e
    · exact (Code.arr.inj e).2
    · simp only [PIF.csz] at e
      omega
  · subst hd
    have := PIF.csz_pos c
    rcases MhE_root_eq_cases _ g _ f ((MhE_root_nt a c hc f).symm.trans h).symm with e | e
    · exact (Code.arr.inj e).2.symm
    · simp only [PIF.csz] at e
      omega
  · exact (Code.arr.inj (congrArg Sigma.fst
      ((MhE_root_nt a c hc f).symm.trans (h.trans (MhE_root_nt a d hd g))))).2

/-- Types whose items have the same roots are the same. -/
theorem MhE_ext_core (a b : Code Empty) (h1 : ∀ x : univHC.El a, ∃ y : univHC.El b, rootE a x = rootE b y)
    (h2 : ∀ y : univHC.El b, ∃ x : univHC.El a, rootE a x = rootE b y) : a = b := by
  obtain ⟨xa, hxa⟩ := MhE_selfroot a
  obtain ⟨xb, hxb⟩ := MhE_selfroot b
  obtain ⟨y, hy⟩ := h1 xa
  obtain ⟨x, hx⟩ := h2 xb
  rcases MhE_root_eq_cases b y a xa (hy.symm.trans hxa) with e1 | e1
  · exact e1.symm
  · rcases MhE_root_eq_cases a x b xb (hx.trans hxb) with e2 | e2
    · exact e2
    · omega

/-! ## `□` -/

/-- `□φ` is true just when `φ` is true at both worlds. -/
theorem MhE_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MhEF.U.TEnv n) (env : MhEF.U.Env Γ ρ) :
    MhEF.Holds (boxF φ) ρ env ↔ ∀ w, MhEF.HoldsAt φ ρ env w := by
  refine (MhEF.holdsAt_eqv_t φ topF ρ env _).trans ((MhE_hb _ _).trans ?_)
  rw [MhEF.eval_topF]
  exact ⟨fun e w => cast (congrFun e w).symm trivial,
    fun h => funext fun w => propext ⟨fun _ => trivial, fun _ => h w⟩⟩

/-! ## Valid -/

theorem MhE_tr_PCong : MhEF.Tr PCong ↔ ∀ a c d (f : MhEF.U.El a → MhEF.U.El c) (g : MhEF.U.El a → MhEF.U.El d) x,
    MhEF.eqv (.arr a c) (.arr a d) f g MhEF.U.w0 → MhEF.eqv c d (f x) (g x) MhEF.U.w0 := Iff.rfl

/-- Functions identified with each other have the same root, so the same type, so are the same. -/
theorem MhE_PCong : MhEF.Valid PCong :=
  (MhEF.valid_iff_tr _).mpr <| MhE_tr_PCong.mpr fun a c d f g x h => by
    have ecd : c = d := MhE_arr_cod a c d f g h.1
    subst ecd
    have efg : f = g := groot_inj hcyE_inj (Code.arr a c) f g h.1
    subst efg
    exact ⟨rfl, rfl⟩

theorem MhE_Inj : MhEF.Valid Inj := MhEF.Inj_of fun _ _ _ => Iff.rfl

theorem MhE_tr_Recovery : MhEF.Tr Recovery ↔ ∀ a b c d, MhEF.teq (.arr a c) (.arr b d) MhEF.U.w0 ∧
    MhEF.teq a b MhEF.U.w0 → MhEF.teq c d MhEF.U.w0 := Iff.rfl

theorem MhE_Recovery : MhEF.Valid Recovery :=
  (MhEF.valid_iff_tr _).mpr <| MhE_tr_Recovery.mpr fun a b c d ⟨h, _⟩ => by
    have e : Code.arr a c = Code.arr b d := h
    exact (Code.arr.inj e).2

theorem MhE_ExtT : MhEF.Valid ExtT :=
  (MhEF.valid_iff_tr _).mpr <| MhEF.tr_ExtT.mpr fun a b ⟨h1, h2⟩ =>
    MhE_ext_core a b (fun x => (h1 x).elim fun y hy => ⟨y, hy.1⟩) (fun y => (h2 y).elim fun x hx => ⟨x, hx.1⟩)

/-- At the other world nothing is identified with anything, so `□(α ⊑ β)` is always false. -/
theorem MhE_IntT : MhEF.Valid IntT := by
  intro ρ env
  refine (MhEF.holds_tall _ _ _).mpr fun a => (MhEF.holds_tall _ _ _).mpr fun b => ?_
  refine (MhEF.holds_imp _ _ _ _).mpr fun h => ?_
  have hs := (MhE_box _ _ _).mp ((MhEF.holds_conj _ _ _ _).mp h).1 false
  obtain ⟨x⟩ := Univ.El_nonempty (U := univHC) a
  obtain ⟨y, hy⟩ := (MhEF.holdsAt_ex _ _ _ _ _).mp ((MhEF.holdsAt_all _ _ _ _ _).mp hs x)
  exact absurd ((MhEF.holdsAt_eqv _ _ _ _ _ _ _).mp hy).2 Bool.false_ne_true

theorem MhE_NITeq : MhEF.Valid NITeq :=
  (MhEF.valid_iff_tr _).mpr <| MhEF.tr_NITeq.mpr fun a b h => (MhE_hb _ _).mpr <| by
    refine Eq.trans ?_ (MhEF.eval_topF (Γ := Ctx.nil) _ _).symm
    funext w
    exact propext ⟨fun _ => trivial, fun _ => h⟩

theorem MhE_NDTeq : MhEF.Valid NDTeq := MhEF.NDTeq_of (fun _ => ⟨rfl, rfl⟩) fun _ _ _ => Iff.rfl

theorem MhE_Bool : ∀ φ, BoolSch φ → MhEF.Valid φ := MhEF.bool_valid fun _ => ⟨rfl, rfl⟩

theorem MhE_TBF : ∀ χ, TBFSch χ → MhEF.Valid χ := MhEF.TBF_of MhE_hb

theorem MhE_TCBF : ∀ χ, TCBFSch χ → MhEF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MhEF.holds_imp _ _ _ _).mpr fun h => ?_
  exact (MhEF.holds_tall _ _ _).mpr fun a => (MhE_box _ _ _).mpr fun w =>
    (MhEF.holdsAt_tall _ _ _ w).mp ((MhE_box _ _ _).mp h w) a

/-- `≈` is identity of types at both worlds, so every type is necessarily some type. -/
theorem MhE_TNec : MhEF.Valid TNec := by
  intro ρ env
  refine (MhEF.holds_tall _ _ _).mpr fun a => (MhE_box _ _ _).mpr fun w => ?_
  exact ⟨a, (MhEF.holdsAt_teq (Γ := Ctx.nil.text.text) tv1 tv0 (scons a (scons a ρ)) env w).mpr rfl⟩

/-! ## Refuted -/

/-- The identity function on entities and the haecceity map agree at each entity, but are of
different types and are their own roots. -/
theorem MhE_not_PExt : ¬ MhEF.Valid PExt := fun h => by
  have h0 := MhEF.tr_PExt.mp ((MhEF.valid_iff_tr _).mp h) .e .e (.arr .e .t) (fun x => x) (fun x => hcyE .e x)
    (fun x => ⟨(groot_hcy hcyE_inj .e x).symm, rfl⟩)
  have e : (Code.arr .e .e : Code Empty) = .arr .e (.arr .e .t) := congrArg Sigma.fst h0.1
  have e2 := (Code.arr.inj e).2
  cases e2

/-- At the other world the entity is not identified with itself, while it has all its properties
there; so `(x ≡ x)` and `∀F(Fx → Fx)` differ. -/
theorem MhE_not_IdId : ¬ MhEF.Valid IdId := fun h => by
  have h0 := (MhEF.holds_all _ _ _ _).mp ((MhEF.holds_all _ _ _ _).mp
    ((MhEF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have e := (MhE_hb _ _).mp ((MhEF.holdsAt_eqv_t _ _ _ _ _).mp h0)
  have hA : MhEF.HoldsAt (RD.Ax' : Fm (((Ctx.nil.text).ext tv0).ext tv0))
      (scons .e fun i => i.elim0) (((), ()), ()) false :=
    (MhEF.holdsAt_all _ _ _ _ false).mpr fun _ => (MhEF.holdsAt_imp _ _ _ _ false).mpr id
  have hE : MhEF.HoldsAt (RD.Ex : Fm (((Ctx.nil.text).ext tv0).ext tv0))
      (scons .e fun i => i.elim0) (((), ()), ()) false := cast (congrFun e false).symm hA
  exact Bool.false_ne_true ((MhEF.holdsAt_eqv _ _ _ _ _ _ false).mp hE).2

end Wd
end PIF
