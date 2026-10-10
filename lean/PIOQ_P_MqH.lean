import PIBF
set_option autoImplicit false

/-!
# Open questions: the profile of `𝔐_q,hae`

`𝔐_q,hae` (`MqHF`, defined in `PIHaeQs`) has propositions sets of two worlds, items identified,
rigidly, just in case they have the same root (haecceity towers `rootQ`), `≈` rigid identity of
codes, the connectives and item quantifiers acting world by world, and at the other world every
type-universal claim false and every type-existential claim true.

Since `≡` and `≈` are rigid and the item quantifiers act world by world, every claim built from
them without type quantifiers has the same value at both worlds; so ND≈, BF, CBF and Nec hold. A
type-existential claim is true at the other world anyway, and at the actual world every type is
`≈` itself, so TNec holds. Functions with the same domain and the same root have the same
codomain, so PCong holds, while an entity and its haecceity give a counterexample to PExt. `≈` is
identity of codes, so Inj≈ and Recovery hold. Within the tower every type has an item that is its
own root, and roots never have larger codes, so coextensive types are the same type: Ext≈ and Int≈
hold.
-/

namespace PIF
namespace Al
open Tm

/-! ## Facts about roots -/

/-- The root of an item of `α→β` is the item itself, unless `β` is `t` and the root lies at a code
no larger than `α`. -/
theorem MqH_root_arr (a b : Code Empty) (f : univQ.El (.arr a b)) :
    (rootQ (.arr a b) f).1 = .arr a b ∨ (b = .t ∧ csz (rootQ (.arr a b) f).1 ≤ csz a) := by
  cases b with
  | t =>
    by_cases h : ∃ z, f = hcyQ a z
    · obtain ⟨z, rfl⟩ := h
      refine Or.inr ⟨rfl, ?_⟩
      have e : csz (rootQ (.arr a .t) (hcyQ a z)).1 = csz (rootQ a z).1 :=
        congrArg (fun r => csz r.1) (groot_hcy hcyQ_inj a z)
      exact Nat.le_trans (Nat.le_of_eq e) (groot_le _ _ a z)
    · exact Or.inl (congrArg Sigma.fst (groot_not univQ.El hcyQ a f h))
  | e => exact Or.inl rfl
  | base x => exact x.elim
  | arr c d => exact Or.inl rfl

/-- The root of an item has the item's code, or a smaller one. -/
theorem MqH_root (c : Code Empty) (x : univQ.El c) : (rootQ c x).1 = c ∨ csz (rootQ c x).1 < csz c :=
  (groot_lt univQ.El hcyQ c x).elim (fun h => Or.inl (congrArg Sigma.fst h)) Or.inr

/-- Functions with the same domain and the same root have the same codomain. -/
theorem MqH_cod {a b c : Code Empty} (f : univQ.El (.arr a b)) (g : univQ.El (.arr a c))
    (h : rootQ (.arr a b) f = rootQ (.arr a c) g) : b = c := by
  have hs := congrArg Sigma.fst h
  rcases MqH_root_arr a b f with h1 | ⟨h1, h2⟩ <;> rcases MqH_root_arr a c g with h3 | ⟨h3, h4⟩
  · exact (Code.arr.inj (h1.symm.trans (hs.trans h3))).2
  · have h5 : csz (Code.arr a b) ≤ csz a := Nat.le_trans (Nat.le_of_eq (congrArg csz (h1.symm.trans hs))) h4
    have h6 : csz a + csz b + 1 ≤ csz a := h5
    omega
  · have h5 : csz (Code.arr a c) ≤ csz a := Nat.le_trans (Nat.le_of_eq (congrArg csz (h3.symm.trans hs.symm))) h2
    have h6 : csz a + csz c + 1 ≤ csz a := h5
    omega
  · exact h1.trans h3.symm

/-- Every type has an item which is its own root. -/
theorem MqH_own : ∀ c : Code Empty, ∃ x : univQ.El c, (rootQ c x).1 = c
  | .arr a .t => by
    refine ⟨fun _ _ => False, ?_⟩
    have hn : ¬ ∃ z, (fun _ _ => False : univQ.El (.arr a .t)) = hcyQ a z := fun ⟨z, hz⟩ =>
      cast (congrFun (congrFun hz z) true).symm rfl
    exact congrArg Sigma.fst (groot_not univQ.El hcyQ a _ hn)
  | .e => ⟨(), rfl⟩
  | .t => ⟨fun _ => True, rfl⟩
  | .base b => b.elim
  | .arr a .e => ⟨Classical.choice (Univ.El_nonempty (U := univQ) (.arr a .e)), rfl⟩
  | .arr _ (.base b) => b.elim
  | .arr a (.arr c d) => ⟨Classical.choice (Univ.El_nonempty (U := univQ) (.arr a (.arr c d))), rfl⟩

/-- Types each of whose items has the same root as an item of the other are the same type. -/
theorem MqH_ext_core (a b : Code Empty)
    (hs : ∀ x : univQ.El a, ∃ y : univQ.El b, rootQ a x = rootQ b y)
    (hp : ∀ y : univQ.El b, ∃ x : univQ.El a, rootQ a x = rootQ b y) : a = b := by
  obtain ⟨x0, hx0⟩ := MqH_own a
  obtain ⟨y0, hy0⟩ := MqH_own b
  obtain ⟨y, hy⟩ := hs x0
  obtain ⟨x, hx⟩ := hp y0
  have c1 : (rootQ b y).1 = a := (congrArg Sigma.fst hy).symm.trans hx0
  have c2 : (rootQ a x).1 = b := (congrArg Sigma.fst hx).trans hy0
  rcases MqH_root b y with r1 | r1 <;> rcases MqH_root a x with r2 | r2
  · exact c1.symm.trans r1
  · exact c1.symm.trans r1
  · exact (c2.symm.trans r2).symm
  · rw [c1] at r1
    rw [c2] at r2
    exact absurd (Nat.lt_trans r1 r2) (Nat.lt_irrefl _)

/-! ## Truth conditions -/

theorem MqH_tr_PCong : MqHF.Holds PCong (fun i => i.elim0) () ↔
    ∀ (a b c : Code Empty) (f : univQ.El a → univQ.El b) (g : univQ.El a → univQ.El c) (x : univQ.El a),
      rootQ (.arr a b) f = rootQ (.arr a c) g → rootQ b (f x) = rootQ c (g x) :=
  Iff.rfl

theorem MqH_tr_PExt : MqHF.Holds PExt (fun i => i.elim0) () ↔
    ∀ (a b c : Code Empty) (f : univQ.El a → univQ.El b) (g : univQ.El a → univQ.El c),
      (∀ x, rootQ b (f x) = rootQ c (g x)) → rootQ (.arr a b) f = rootQ (.arr a c) g :=
  Iff.rfl

theorem MqH_tr_ExtT : MqHF.Holds ExtT (fun i => i.elim0) () ↔
    ∀ (a b : Code Empty), ((∀ x : univQ.El a, ∃ y : univQ.El b, rootQ a x = rootQ b y) ∧
      (∀ y : univQ.El b, ∃ x : univQ.El a, rootQ a x = rootQ b y)) → a = b :=
  Iff.rfl

/-! ## Valid principles -/

theorem MqH_PCong : MqHF.Valid PCong :=
  (MqHF.valid_iff_tr _).mpr (MqH_tr_PCong.mpr fun a b _ f g _ h => by
    have hbc := MqH_cod f g h
    subst hbc
    have hfg := groot_inj hcyQ_inj (.arr a b) f g h
    subst hfg
    rfl)

theorem MqH_Inj : MqHF.Valid Inj := by
  intro ρ env
  refine (MqHF.holds_tall _ _ _).mpr fun a => (MqHF.holds_tall _ _ _).mpr fun b => ?_
  refine (MqHF.holds_tall _ _ _).mpr fun c => (MqHF.holds_tall _ _ _).mpr fun d => ?_
  refine (MqHF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (MqHF.holds_teq _ _ _ _).mp h
  injection h' with hab hcd
  exact (MqHF.holds_conj _ _ _ _).mpr ⟨(MqHF.holds_teq _ _ _ _).mpr hab, (MqHF.holds_teq _ _ _ _).mpr hcd⟩

theorem MqH_Recovery : MqHF.Valid Recovery := by
  intro ρ env
  refine (MqHF.holds_tall _ _ _).mpr fun a => (MqHF.holds_tall _ _ _).mpr fun b => ?_
  refine (MqHF.holds_tall _ _ _).mpr fun c => (MqHF.holds_tall _ _ _).mpr fun d => ?_
  refine (MqHF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (MqHF.holds_teq _ _ _ _).mp ((MqHF.holds_conj _ _ _ _).mp h).1
  exact (MqHF.holds_teq _ _ _ _).mpr (Code.arr.inj h').2

theorem MqH_ExtT : MqHF.Valid ExtT :=
  (MqHF.valid_iff_tr _).mpr (MqH_tr_ExtT.mpr fun a b ⟨hs, hp⟩ => MqH_ext_core a b hs hp)

/-- `□(α ⊑ β)` implies `α ⊑ β`, so Int≈ follows as Ext≈ does. -/
theorem MqH_IntT : MqHF.Valid IntT := by
  intro ρ env
  refine (MqHF.holds_tall _ _ _).mpr fun a => (MqHF.holds_tall _ _ _).mpr fun b => ?_
  refine (MqHF.holds_imp _ _ _ _).mpr fun h => ?_
  have hc := (MqHF.holds_conj _ _ _ _).mp h
  have e1 := ((MqH_eqT _ _).mp ((MqHF.holds_eqv_t _ _ _ _).mp hc.1)).trans
    (MqH_top (Γ := Ctx.nil.text.text) _ _)
  have e2 := ((MqH_eqT _ _).mp ((MqHF.holds_eqv_t _ _ _ _).mp hc.2)).trans
    (MqH_top (Γ := Ctx.nil.text.text) _ _)
  have hs : ∀ x : univQ.El a, ∃ y : univQ.El b, rootQ a x = rootQ b y :=
    cast (congrFun e1 true).symm trivial
  have hp : ∀ y : univQ.El b, ∃ x : univQ.El a, rootQ a x = rootQ b y :=
    cast (congrFun e2 true).symm trivial
  exact (MqHF.holds_teq _ _ _ _).mpr (MqH_ext_core a b hs hp)

theorem MqH_NDTeq : MqHF.Valid NDTeq := by
  intro ρ env
  refine (MqHF.holds_tall _ _ _).mpr fun a => (MqHF.holds_tall _ _ _).mpr fun b => ?_
  refine (MqHF.holds_imp _ _ _ _).mpr fun h => ?_
  refine (MqHF.holds_eqv_t _ _ _ _).mpr ((MqH_eqT _ _).mpr ?_)
  refine Eq.trans ?_ (MqH_top (Γ := Ctx.nil.text.text) _ _).symm
  funext w
  refine propext ⟨fun _ => trivial, fun _ hw => (MqHF.holds_neg _ _ _).mp h ?_⟩
  have e := MqHF.eval_teq (Γ := Ctx.nil.text.text) tv1 tv0 (scons b (scons a ρ)) env
  have hw' := congrFun e w ▸ hw
  exact cast (congrFun e true).symm hw'

/-- `𝔼β (α ≈ β)` is true at the actual world, witnessed by `α`, and at the other world anyway. -/
theorem MqH_TNec : MqHF.Valid TNec := by
  intro ρ env
  refine (MqHF.holds_tall _ _ _).mpr fun a => ?_
  refine (MqHF.holds_eqv_t _ _ _ _).mpr ((MqH_eqT _ _).mpr ?_)
  refine Eq.trans ?_ (MqH_top (Γ := Ctx.nil.text) _ _).symm
  funext w
  cases w
  · exact propext ⟨fun _ => trivial, fun _ => trivial⟩
  · refine propext ⟨fun _ => trivial, fun _ => ⟨a, ?_⟩⟩
    have e := MqHF.eval_teq (Γ := Ctx.nil.text.text) tv1 tv0 (scons a (scons a ρ)) env
    exact cast (congrFun e true).symm rfl

theorem MqH_BF : MqHF.Valid BF := by
  intro ρ env
  refine (MqHF.holds_tall _ _ _).mpr fun a => (MqHF.holds_all _ _ _ _).mpr fun F => ?_
  refine (MqHF.holds_imp _ _ _ _).mpr fun h => ?_
  have e : ∀ x, MqHF.eval (Tm.app (.var (.there .here)) (.var .here) : Fm (((Ctx.nil.text).ext tv0.pred).ext tv0))
      (scons a ρ) ((env, F), x) = fun _ => True := fun x =>
    ((MqH_eqT _ _).mp ((MqHF.holds_eqv_t _ _ _ _).mp ((MqHF.holds_all _ _ _ _).mp h x))).trans
      (MqH_top (Γ := ((Ctx.nil.text).ext tv0.pred).ext tv0) _ _)
  refine (MqHF.holds_eqv_t _ _ _ _).mpr ((MqH_eqT _ _).mpr ?_)
  refine (MqHF.eval_all (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here))
    (scons a ρ) (env, F)).trans ?_
  refine Eq.trans ?_ (MqH_top (Γ := (Ctx.nil.text).ext tv0.pred) _ _).symm
  funext w
  exact propext ⟨fun _ => trivial, fun _ x => cast (congrFun (e _) w).symm trivial⟩

theorem MqH_CBF : MqHF.Valid CBF := by
  intro ρ env
  refine (MqHF.holds_tall _ _ _).mpr fun a => (MqHF.holds_all _ _ _ _).mpr fun F => ?_
  refine (MqHF.holds_imp _ _ _ _).mpr fun h => ?_
  have e := ((MqH_eqT _ _).mp ((MqHF.holds_eqv_t _ _ _ _).mp h)).trans
    (MqH_top (Γ := (Ctx.nil.text).ext tv0.pred) _ _)
  have e2 := (MqHF.eval_all (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here))
    (scons a ρ) (env, F)).symm.trans e
  refine (MqHF.holds_all _ _ _ _).mpr fun x => ?_
  refine (MqHF.holds_eqv_t _ _ _ _).mpr ((MqH_eqT _ _).mpr ?_)
  refine Eq.trans ?_ (MqH_top (Γ := ((Ctx.nil.text).ext tv0.pred).ext tv0) _ _).symm
  funext w
  exact propext ⟨fun _ => trivial, fun _ => (cast (congrFun e2 w).symm trivial : ∀ y, _) x⟩

/-- `∃y (x ≡ y)` is true at both worlds, witnessed by `x` itself. -/
theorem MqH_Nec : MqHF.Valid Nec := by
  intro ρ env
  refine (MqHF.holds_tall _ _ _).mpr fun a => (MqHF.holds_all _ _ _ _).mpr fun x => ?_
  refine (MqHF.holds_eqv_t _ _ _ _).mpr ((MqH_eqT _ _).mpr ?_)
  refine Eq.trans ?_ (MqH_top (Γ := (Ctx.nil.text).ext tv0) _ _).symm
  funext w
  exact propext ⟨fun _ => trivial, fun _ => ⟨x, rfl⟩⟩

/-! ## Refuted principles -/

/-- A function `e→e` and a function `e→(e→t)` with pointwise identical values: the constant
function to the entity, and the constant function to its haecceity. -/
theorem MqH_not_PExt : ¬ MqHF.Valid PExt := fun h => by
  have h1 := MqH_tr_PExt.mp ((MqHF.valid_iff_tr _).mp h) .e .e (.arr .e .t) (fun _ => ())
    (fun _ => hcyQ .e ()) (fun _ => (groot_hcy hcyQ_inj .e ()).symm)
  have h2 : (Code.arr .e .e : Code Empty) = .arr .e (.arr .e .t) := congrArg Sigma.fst h1
  exact nomatch h2

end Al
end PIF
