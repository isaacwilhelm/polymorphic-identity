import PIBF
set_option autoImplicit false

/-!
# Open questions: the profile of `𝔐_hw,C`

`𝔐_hw,C` (`MhwC`, defined in `PIBarcanModels`) is the haecceity tower of `𝔐_hw`, with
propositions pairs of a set of two worlds and a tag, and the type quantifiers treated as in
`𝔐_q,C`: at the other world type-universal claims are true and type-existential ones false.

Identity of items holds only at the actual world and has tag `false`, while `⊤` has tag `true`;
so no identity is necessary. A true negated identity is true at both worlds, with tag `true`,
so it is `⊤`. Identity of types is identity at the actual world and difference at the other
world. Within the tower every type has an item that is its own root, and roots never have
larger codes, so coextensive types are the same type.
-/

namespace PIF
namespace Al

/-! ## Facts about roots -/

theorem MhwC_teq_iff (a b : Code univH.Base) : MhwC.U.V (MhwC.teq a b) ↔ a = b :=
  show (if true = true then a = b else a ≠ b) ↔ a = b by simp

/-- The root of an item of `α→β` is the item itself, unless `β` is `t` and the root is the root of
an item of `α`. -/
theorem MhwC_hrW_arr (a b : Code univH.Base) (f : univH.El (.arr a b)) :
    (hrW (.arr a b) f).1 = .arr a b ∨ (b = .t ∧ csz (hrW (.arr a b) f).1 ≤ csz a) := by
  cases b with
  | t =>
    rw [hrW_arr_t]
    split
    · exact Or.inr ⟨rfl, hrW_le a _⟩
    · exact Or.inl rfl
  | e => exact Or.inl rfl
  | base x => exact x.elim
  | arr c d => exact Or.inl rfl

/-- Functions with the same domain and the same root have the same codomain. -/
theorem MhwC_hrW_cod {a b c : Code univH.Base} (f : univH.El (.arr a b)) (g : univH.El (.arr a c))
    (h : hrW (.arr a b) f = hrW (.arr a c) g) : b = c := by
  have hs := congrArg Sigma.fst h
  rcases MhwC_hrW_arr a b f with h1 | ⟨h1, h2⟩ <;> rcases MhwC_hrW_arr a c g with h3 | ⟨h3, h4⟩
  · exact (Code.arr.inj (h1.symm.trans (hs.trans h3))).2
  · have h5 : csz (Code.arr a b) ≤ csz a := by rw [← h1, hs]; exact h4
    have h6 : csz a + csz b + 1 ≤ csz a := h5
    omega
  · have h5 : csz (Code.arr a c) ≤ csz a := by rw [← h3, ← hs]; exact h2
    have h6 : csz a + csz c + 1 ≤ csz a := h5
    omega
  · exact h1.trans h3.symm

/-- The root of an item has the item's code, or a smaller one. -/
theorem MhwC_root : ∀ (c : Code univH.Base) (x : univH.El c), (hrW c x).1 = c ∨ csz (hrW c x).1 < csz c
  | .arr a .t, G => by
    rw [hrW_arr_t]
    split
    · exact Or.inr (Nat.lt_of_le_of_lt (hrW_le a _)
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.succ_le_succ (Nat.le_add_right _ _))))
    · exact Or.inl rfl
  | .e, _ => Or.inl rfl
  | .t, _ => Or.inl rfl
  | .base b, _ => b.elim
  | .arr _ .e, _ => Or.inl rfl
  | .arr _ (.base b), _ => b.elim
  | .arr _ (.arr _ _), _ => Or.inl rfl

theorem MhwC_own_t (a : Code univH.Base) (G : univH.El (.arr a .t)) (hG : ∀ y, (G y).2 = true) :
    (hrW (.arr a .t) G).1 = .arr a .t := by
  rw [hrW_arr_t]
  split
  · next h =>
    obtain ⟨x, hx⟩ := h
    exact Bool.noConfusion ((hG x).symm.trans (congrArg Prod.snd (congrFun hx x)))
  · rfl

/-- Every type has an item which is its own root. -/
theorem MhwC_own : ∀ c : Code univH.Base, ∃ x : univH.El c, (hrW c x).1 = c
  | .arr a .t => ⟨fun _ => ((fun _ => True), true), MhwC_own_t a _ fun _ => rfl⟩
  | .e => ⟨(), rfl⟩
  | .t => ⟨((fun _ => True), true), rfl⟩
  | .base b => b.elim
  | .arr a .e => ⟨Classical.choice (Univ.El_nonempty (U := univH) (.arr a .e)), rfl⟩
  | .arr _ (.base b) => b.elim
  | .arr a (.arr c d) => ⟨Classical.choice (Univ.El_nonempty (U := univH) (.arr a (.arr c d))), rfl⟩

/-! ## Truth conditions -/

theorem MhwC_tr_PCong : MhwC.Holds PCong (fun i => i.elim0) () ↔
    ∀ (a b c : Code Empty) (f : univH.El a → univH.El b) (g : univH.El a → univH.El c) (x : univH.El a),
      (hrW (.arr a b) f = hrW (.arr a c) g ∧ true = true) → (hrW b (f x) = hrW c (g x) ∧ true = true) :=
  Iff.rfl

theorem MhwC_tr_PExt : MhwC.Holds PExt (fun i => i.elim0) () ↔
    ∀ (a b c : Code Empty) (f : univH.El a → univH.El b) (g : univH.El a → univH.El c),
      (∀ x, hrW b (f x) = hrW c (g x) ∧ true = true) → (hrW (.arr a b) f = hrW (.arr a c) g ∧ true = true) :=
  Iff.rfl

theorem MhwC_tr_ExtT : MhwC.Holds ExtT (fun i => i.elim0) () ↔
    ∀ (a b : Code Empty), ((∀ x : univH.El a, ∃ y : univH.El b, hrW a x = hrW b y ∧ true = true) ∧
      (∀ y : univH.El b, ∃ x : univH.El a, hrW a x = hrW b y ∧ true = true)) →
      (if true = true then a = b else a ≠ b) :=
  Iff.rfl

/-! ## Valid principles -/

theorem MhwC_PCong : MhwC.Valid PCong :=
  (MhwC.valid_iff_tr _).mpr (MhwC_tr_PCong.mpr fun a b _ f g _ h => by
    have hbc := MhwC_hrW_cod f g h.1
    subst hbc
    have hfg := hrW_inj (.arr a b) f g h.1
    subst hfg
    exact ⟨rfl, rfl⟩)

theorem MhwC_Inj : MhwC.Valid Inj := by
  intro ρ env
  refine (MhwC.holds_tall _ _ _).mpr fun a => (MhwC.holds_tall _ _ _).mpr fun b => ?_
  refine (MhwC.holds_tall _ _ _).mpr fun c => (MhwC.holds_tall _ _ _).mpr fun d => ?_
  refine (MhwC.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (MhwC_teq_iff _ _).mp ((MhwC.holds_teq _ _ _ _).mp h)
  injection h' with hab hcd
  exact (MhwC.holds_conj _ _ _ _).mpr ⟨(MhwC.holds_teq _ _ _ _).mpr ((MhwC_teq_iff _ _).mpr hab),
    (MhwC.holds_teq _ _ _ _).mpr ((MhwC_teq_iff _ _).mpr hcd)⟩

theorem MhwC_Recovery : MhwC.Valid Recovery := by
  intro ρ env
  refine (MhwC.holds_tall _ _ _).mpr fun a => (MhwC.holds_tall _ _ _).mpr fun b => ?_
  refine (MhwC.holds_tall _ _ _).mpr fun c => (MhwC.holds_tall _ _ _).mpr fun d => ?_
  refine (MhwC.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d :=
    (MhwC_teq_iff _ _).mp ((MhwC.holds_teq _ _ _ _).mp ((MhwC.holds_conj _ _ _ _).mp h).1)
  exact (MhwC.holds_teq _ _ _ _).mpr ((MhwC_teq_iff _ _).mpr (Code.arr.inj h').2)

theorem MhwC_ExtT : MhwC.Valid ExtT :=
  (MhwC.valid_iff_tr _).mpr (MhwC_tr_ExtT.mpr fun a b ⟨hs, hp⟩ => by
    refine (MhwC_teq_iff a b).mpr ?_
    obtain ⟨x0, hx0⟩ := MhwC_own a
    obtain ⟨y0, hy0⟩ := MhwC_own b
    obtain ⟨y, hy⟩ := hs x0
    obtain ⟨x, hx⟩ := hp y0
    have c1 : (hrW b y).1 = a := (congrArg Sigma.fst hy.1).symm.trans hx0
    have c2 : (hrW a x).1 = b := (congrArg Sigma.fst hx.1).trans hy0
    rcases MhwC_root b y with r1 | r1 <;> rcases MhwC_root a x with r2 | r2
    · exact c1.symm.trans r1
    · exact c1.symm.trans r1
    · exact (c2.symm.trans r2).symm
    · rw [c1] at r1
      rw [c2] at r2
      exact absurd (Nat.lt_trans r1 r2) (Nat.lt_irrefl _))

/-- `□(α ⊑ β)` never holds, since no identity holds at the other world. -/
theorem MhwC_IntT : MhwC.Valid IntT := by
  intro ρ env
  refine (MhwC.holds_tall _ _ _).mpr fun a => (MhwC.holds_tall _ _ _).mpr fun b => ?_
  refine (MhwC.holds_imp _ _ _ _).mpr fun h => ?_
  have hs := ((MhwC.holds_conj _ _ _ _).mp h).1
  have e := (hrW_inj .t _ _ ((MhwC.holds_eqv_t _ _ _ _).mp hs).1).trans
    (MhwG_top _ _ (Γ := Ctx.nil.text.text) _ _)
  have h3 : (MhwC.eval (subT : Fm (Ctx.nil.text.text)) (scons b (scons a ρ)) env).1 false :=
    cast (congrFun (congrArg Prod.fst e) false).symm trivial
  have x0 := Classical.choice (Univ.El_nonempty (U := MhwC.U) a)
  obtain ⟨_, hy⟩ := h3 x0
  exact Bool.noConfusion (And.right hy)

/-- A true negated identity is true at both worlds, with tag `true`: it is `⊤`. -/
theorem MhwC_NDX : MhwC.Valid NDX := by
  intro ρ env
  refine (MhwC.holds_tall _ _ _).mpr fun a => (MhwC.holds_tall _ _ _).mpr fun b => ?_
  refine (MhwC.holds_all _ _ _ _).mpr fun x => (MhwC.holds_all _ _ _ _).mpr fun y => ?_
  refine (MhwC.holds_imp _ _ _ _).mpr fun hn => ?_
  refine (MhwC.holds_eqv_t _ _ _ _).mpr ⟨congrArg (hrW .t) ?_, rfl⟩
  refine Eq.trans ?_ (MhwG_top _ _ (Γ := ((Ctx.nil.text.text).ext tv1).ext tv0) _ _).symm
  refine Prod.ext (funext fun w => propext ⟨fun _ => trivial, fun _ hw => ?_⟩) rfl
  cases w
  · exact Bool.noConfusion (And.right hw)
  · exact (MhwC.holds_neg _ _ _).mp hn hw

theorem MhwC_TBF : ∀ χ, TBFSch χ → MhwC.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MhwC.holds_imp _ _ _ _).mpr fun h => ?_
  refine (MhwC.holds_eqv_t _ _ _ _).mpr ⟨congrArg (hrW .t) ?_, rfl⟩
  refine Eq.trans ?_ (MhwG_top _ _ (Γ := Ctx.nil) _ _).symm
  refine Prod.ext (funext fun w => ?_) rfl
  cases w
  · exact propext ⟨fun _ => trivial, fun _ => trivial⟩
  · refine propext ⟨fun _ => trivial, fun _ a => ?_⟩
    have e := (hrW_inj .t _ _ ((MhwC.holds_eqv_t _ _ _ _).mp ((MhwC.holds_tall _ _ _).mp h a)).1).trans
      (MhwG_top _ _ (Γ := Ctx.nil.text) _ _)
    exact cast (congrFun (congrArg Prod.fst e) true).symm trivial

theorem MhwC_BF : MhwC.Valid BF := by
  intro ρ env
  refine (MhwC.holds_tall _ _ _).mpr fun a => (MhwC.holds_all _ _ _ _).mpr fun F => ?_
  refine (MhwC.holds_imp _ _ _ _).mpr fun h => ?_
  have e : ∀ x, MhwC.eval (Tm.app (.var (.there .here)) (.var .here) : Fm (((Ctx.nil.text).ext tv0.pred).ext tv0))
      (scons a ρ) ((env, F), x) = ((fun _ => True), true) := fun x =>
    (hrW_inj .t _ _ ((MhwC.holds_eqv_t _ _ _ _).mp ((MhwC.holds_all _ _ _ _).mp h x)).1).trans
      (MhwG_top _ _ (Γ := ((Ctx.nil.text).ext tv0.pred).ext tv0) _ _)
  refine (MhwC.holds_eqv_t _ _ _ _).mpr ⟨congrArg (hrW .t) ?_, rfl⟩
  refine (MhwC.eval_all (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here))
    (scons a ρ) (env, F)).trans ?_
  refine Eq.trans ?_ (MhwG_top _ _ (Γ := (Ctx.nil.text).ext tv0.pred) _ _).symm
  refine Prod.ext (funext fun w => propext ⟨fun _ => trivial, fun _ x => ?_⟩) rfl
  exact cast (congrFun (congrArg Prod.fst (e x)) w).symm trivial

/-! ## Refuted principles -/

/-- A function `e→e` and a function `e→(e→t)` with pointwise identical values: the constant
function to the entity, and the constant function to its haecceity. -/
theorem MhwC_not_PExt : ¬ MhwC.Valid PExt := fun h => by
  have h1 := MhwC_tr_PExt.mp ((MhwC.valid_iff_tr _).mp h) .e .e (.arr .e .t) (fun _ => ())
    (fun _ => fun y => ((fun w => hrW .e y = hrW .e () ∧ w = true), false))
    (fun _ => ⟨(hrW_hae .e ()).symm, rfl⟩)
  have h2 : (Code.arr .e .e : Code Empty) = .arr .e (.arr .e .t) := congrArg Sigma.fst h1.1
  exact nomatch h2

theorem MhwC_not_NIEqv : ¬ MhwC.Valid NIEqv := fun h => by
  have h0 := (MhwC.holds_all _ _ _ _).mp ((MhwC.holds_all _ _ _ _).mp
    ((MhwC.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have hb := (MhwC.holds_imp _ _ _ _).mp h0 ((MhwC.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, rfl⟩)
  have e := hrW_inj .t _ _ ((MhwC.holds_eqv_t _ _ _ _).mp hb).1
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

theorem MhwC_not_NIX : ¬ MhwC.Valid NIX := fun h => by
  have h0 := (MhwC.holds_all _ _ _ _).mp ((MhwC.holds_all _ _ _ _).mp
    ((MhwC.holds_tall _ _ _).mp ((MhwC.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e) ()) ()
  have hb := (MhwC.holds_imp _ _ _ _).mp h0 ((MhwC.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, rfl⟩)
  have e := hrW_inj .t _ _ ((MhwC.holds_eqv_t _ _ _ _).mp hb).1
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

theorem MhwC_not_NITeq : ¬ MhwC.Valid NITeq := fun h => by
  have h0 := (MhwC.holds_tall _ _ _).mp ((MhwC.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e
  have hb := (MhwC.holds_imp _ _ _ _).mp h0 ((MhwC.holds_teq _ _ _ _).mpr
    (show (if true = true then (Code.e : Code Empty) = Code.e else (Code.e : Code Empty) ≠ Code.e) by simp))
  have e := (hrW_inj .t _ _ ((MhwC.holds_eqv_t _ _ _ _).mp hb).1).trans
    (MhwG_top _ _ (Γ := Ctx.nil.text.text) _ _)
  have e2 := congrFun (congrArg Prod.fst e) false
  exact (cast e2.symm trivial : if false = true then (Code.e : Code Empty) = .e else (Code.e : Code Empty) ≠ .e)
    (by simp) |>.elim

theorem MhwC_not_NDTeq : ¬ MhwC.Valid NDTeq := fun h => by
  have h0 := (MhwC.holds_tall _ _ _).mp ((MhwC.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .t
  have hn : MhwC.Holds (Tm.neg (Tm.teq tv1 tv0) : Fm Ctx.nil.text.text) (scons .t (scons .e fun i => i.elim0)) () :=
    (MhwC.holds_neg _ _ _).mpr fun ht =>
      nomatch ((MhwC.holds_teq _ _ _ _).mp ht : if true = true then (Code.e : Code Empty) = .t else _)
  have hb := (MhwC.holds_imp _ _ _ _).mp h0 hn
  have e := (hrW_inj .t _ _ ((MhwC.holds_eqv_t _ _ _ _).mp hb).1).trans
    (MhwG_top _ _ (Γ := Ctx.nil.text.text) _ _)
  have e2 := congrFun (congrArg Prod.fst e) false
  exact (cast e2.symm trivial : ¬ (if false = true then (Code.e : Code Empty) = .t else (Code.e : Code Empty) ≠ .t))
    (by simp)

theorem MhwC_not_DNeg : ¬ MhwC.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MhwC.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) ((fun _ => True), false)
  have e := hrW_inj .t _ _ ((MhwC.holds_eqv_t _ _ _ _).mp h0).1
  exact Bool.noConfusion (congrArg Prod.snd e : true = false)

theorem MhwC_not_Bool : ¬ ∀ φ, BoolSch φ → MhwC.Valid φ := fun h => MhwC_not_DNeg (h _ DNeg_bool)

theorem MhwC_not_IdId : ¬ MhwC.Valid IdId := fun h => by
  have h0 := (MhwC.holds_all _ _ _ _).mp ((MhwC.holds_all _ _ _ _).mp
    ((MhwC.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have e := hrW_inj .t _ _ ((MhwC.holds_eqv_t _ _ _ _).mp h0).1
  have e2 := congrArg Prod.snd ((MhwC.eval_eqv _ _ _ _ _ _).symm.trans (e.trans (MhwC.eval_all _ _ _ _)))
  exact Bool.noConfusion (e2 : false = true)

/-- `□∀x F x` holds when every `F x` is true at both worlds, but `□ F x` fails when `F x` has tag
`false`. -/
theorem MhwC_not_CBF : ¬ MhwC.Valid CBF := fun h => by
  have h0 := (MhwC.holds_all _ _ _ _).mp ((MhwC.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ => ((fun _ => True), false))
  have hv : MhwC.eval (Tm.all tv0 (Tm.app (.var (.there .here)) (.var .here)) : Fm ((Ctx.nil.text).ext tv0.pred))
      (scons .e fun i => i.elim0) ((), fun _ => ((fun _ => True), false)) = ((fun _ => True), true) :=
    Prod.ext (funext fun _ => propext ⟨fun _ => trivial, fun _ _ => trivial⟩) rfl
  have hp : MhwC.Holds (boxF (Tm.all tv0 (Tm.app (.var (.there .here)) (.var .here))) : Fm ((Ctx.nil.text).ext tv0.pred))
      (scons .e fun i => i.elim0) ((), fun _ => ((fun _ => True), false)) :=
    (MhwC.holds_eqv_t _ _ _ _).mpr
      ⟨congrArg (hrW .t) (hv.trans (MhwG_top _ _ (Γ := (Ctx.nil.text).ext tv0.pred) _ _).symm), rfl⟩
  have hb := (MhwC.holds_all _ _ _ _).mp ((MhwC.holds_imp _ _ _ _).mp h0 hp) ()
  have e := hrW_inj .t _ _ ((MhwC.holds_eqv_t _ _ _ _).mp hb).1
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

/-- `∃y (x ≡ y)` is false at the other world. -/
theorem MhwC_not_Nec : ¬ MhwC.Valid Nec := fun h => by
  have hb := (MhwC.holds_all _ _ _ _).mp ((MhwC.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  have e := (hrW_inj .t _ _ ((MhwC.holds_eqv_t _ _ _ _).mp hb).1).trans
    (MhwG_top _ _ (Γ := (Ctx.nil.text).ext tv0) _ _)
  have h3 : (MhwC.eval (Tm.ex tv0 (Tm.eqv tv0 tv0 (.var (.there .here)) (.var .here)) : Fm ((Ctx.nil.text).ext tv0))
      (scons .e fun i => i.elim0) ((), ())).1 false :=
    cast (congrFun (congrArg Prod.fst e) false).symm trivial
  obtain ⟨_, hy⟩ := h3
  exact Bool.noConfusion (And.right hy)

end Al
end PIF
