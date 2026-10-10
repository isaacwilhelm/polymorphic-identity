import PIBF

/-!
# Open questions: the profile of `𝔐_hw,A`

The haecceity tower of `𝔐_hw` (`lean/PIAlgModels.lean`): propositions are pairs of a set of two
worlds and a tag; identity of items is sameness of root at the actual world (`true`), and fails at
the other world (`false`), with tag `false`; `≈` is identity at the actual world and difference at the
other world; the connectives and item quantifiers act world by world with tag `true`. The type
quantifiers are as in `𝔐_q,A` (`lean/PIBarcanModels.lean`, `MhwA`): at the other world, `𝔸` is false
and `𝔼` is true.

So `□φ` holds just in case the value of `φ` is true at both worlds with tag `true`.
-/
set_option autoImplicit false

namespace PIF
namespace Al
open Tm

/-! ## Basic facts -/

theorem MhwA_V_teq (a b : Code Empty) : MhwA.U.V (MhwA.teq a b) ↔ a = b :=
  show (if true = true then a = b else a ≠ b) ↔ a = b by simp

/-- `□φ` holds just in case `φ` has the value of `⊤`: true at both worlds, with tag `true`. -/
theorem MhwA_holds_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MhwA.U.TEnv n) (env : MhwA.U.Env Γ ρ) :
    MhwA.Holds (boxF φ) ρ env ↔ MhwA.eval φ ρ env = ((fun _ => True), true) :=
  (MhwA.holds_eqv_t _ _ _ _).trans
    ⟨fun h => (hrW_inj .t _ _ h.1).trans (MhwG_top _ _ ρ env),
     fun h => ⟨congrArg (hrW .t) (h.trans (MhwG_top _ _ ρ env).symm), rfl⟩⟩

theorem MhwA_cast_ex_eq {c : Code Empty} {A' : Type} (hA : MhwA.U.El c = A')
    (h : ((MhwA.U.El c → MhwA.U.P) → MhwA.U.P) = ((A' → MhwA.U.P) → MhwA.U.P)) (Q : A' → MhwA.U.P) :
    cast h (fun R => MhwA.ex c R) Q = MhwA.ex c (fun x => Q (cast hA x)) := by
  subst hA; rfl

/-- The value of an existential quantification. -/
theorem MhwA_eval_ex {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MhwA.U.TEnv n)
    (env : MhwA.U.Env Γ ρ) :
    MhwA.eval (Tm.ex σ φ) ρ env = MhwA.ex (MhwA.U.code σ.1 ρ) (fun x => MhwA.eval φ ρ (env, cast (Univ.El_code ρ σ.2) x)) :=
  MhwA_cast_ex_eq (Univ.El_code ρ σ.2) _ _


/-! ## Identity of types -/

theorem MhwA_Inj : MhwA.Valid Inj := by
  intro ρ env
  refine (MhwA.holds_tall _ _ _).mpr fun a => (MhwA.holds_tall _ _ _).mpr fun b => ?_
  refine (MhwA.holds_tall _ _ _).mpr fun c => (MhwA.holds_tall _ _ _).mpr fun d => ?_
  refine (MhwA.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (MhwA_V_teq _ _).mp ((MhwA.holds_teq _ _ _ _).mp h)
  injection h' with hab hcd
  exact (MhwA.holds_conj _ _ _ _).mpr ⟨(MhwA.holds_teq _ _ _ _).mpr ((MhwA_V_teq _ _).mpr hab),
    (MhwA.holds_teq _ _ _ _).mpr ((MhwA_V_teq _ _).mpr hcd)⟩

theorem MhwA_Recovery : MhwA.Valid Recovery := by
  intro ρ env
  refine (MhwA.holds_tall _ _ _).mpr fun a => (MhwA.holds_tall _ _ _).mpr fun b => ?_
  refine (MhwA.holds_tall _ _ _).mpr fun c => (MhwA.holds_tall _ _ _).mpr fun d => ?_
  refine (MhwA.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d :=
    (MhwA_V_teq _ _).mp ((MhwA.holds_teq _ _ _ _).mp ((MhwA.holds_conj _ _ _ _).mp h).1)
  exact (MhwA.holds_teq _ _ _ _).mpr ((MhwA_V_teq _ _).mpr (Code.arr.inj h').2)

/-! ## Necessity of identity and distinctness -/

theorem MhwA_not_NIEqv : ¬ MhwA.Valid NIEqv := fun h => by
  have h0 := (MhwA.holds_all _ _ _ _).mp ((MhwA.holds_all _ _ _ _).mp
    ((MhwA.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have hb := (MhwA_holds_box _ _ _).mp ((MhwA.holds_imp _ _ _ _).mp h0 ((MhwA.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, rfl⟩))
  exact Bool.noConfusion (congrArg Prod.snd hb : false = true)

theorem MhwA_not_NIX : ¬ MhwA.Valid NIX := fun h => by
  have h0 := (MhwA.holds_all _ _ _ _).mp ((MhwA.holds_all _ _ _ _).mp ((MhwA.holds_tall _ _ _).mp
    ((MhwA.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e) ()) ()
  have hb := (MhwA_holds_box _ _ _).mp ((MhwA.holds_imp _ _ _ _).mp h0 ((MhwA.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, rfl⟩))
  exact Bool.noConfusion (congrArg Prod.snd hb : false = true)

theorem MhwA_NDX : MhwA.Valid NDX := by
  intro ρ env
  refine (MhwA.holds_tall _ _ _).mpr fun _ => (MhwA.holds_tall _ _ _).mpr fun _ => ?_
  refine (MhwA.holds_all _ _ _ _).mpr fun _ => (MhwA.holds_all _ _ _ _).mpr fun _ => ?_
  refine (MhwA.holds_imp _ _ _ _).mpr fun hn => (MhwA_holds_box _ _ _).mpr ?_
  have hn' := (MhwA.holds_neg _ _ _).mp hn
  exact Prod.ext (funext fun _ => propext ⟨fun _ => trivial, fun _ hw => hn' ⟨hw.1, rfl⟩⟩) rfl

theorem MhwA_not_NITeq : ¬ MhwA.Valid NITeq := fun h => by
  have h0 := (MhwA.holds_tall _ _ _).mp ((MhwA.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e
  have hb := (MhwA_holds_box _ _ _).mp ((MhwA.holds_imp _ _ _ _).mp h0
    ((MhwA.holds_teq _ _ _ _).mpr ((MhwA_V_teq _ _).mpr rfl)))
  have e2 := congrFun (congrArg Prod.fst hb) false
  exact (cast e2.symm trivial : if false = true then (Code.e : Code Empty) = .e else (Code.e : Code Empty) ≠ .e)
    (by simp) |>.elim

theorem MhwA_not_NDTeq : ¬ MhwA.Valid NDTeq := fun h => by
  have h0 := (MhwA.holds_tall _ _ _).mp ((MhwA.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .t
  have hn : MhwA.Holds (Tm.neg (Tm.teq tv1 tv0) : Fm Ctx.nil.text.text) (scons .t (scons .e fun i => i.elim0)) () :=
    (MhwA.holds_neg _ _ _).mpr fun ht => nomatch ((MhwA_V_teq _ _).mp ((MhwA.holds_teq _ _ _ _).mp ht))
  have hb := (MhwA_holds_box _ _ _).mp ((MhwA.holds_imp _ _ _ _).mp h0 hn)
  have e2 := congrFun (congrArg Prod.fst hb) false
  exact (cast e2.symm trivial : ¬ (if false = true then (Code.e : Code Empty) = .t else (Code.e : Code Empty) ≠ .t))
    (by simp)

/-! ## Booleanism, the Identity Identity, Classicism -/

theorem MhwA_not_DNeg : ¬ MhwA.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MhwA.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) ((fun _ => True), false)
  have e := hrW_inj .t _ _ ((MhwA.holds_eqv_t _ _ _ _).mp h0).1
  exact Bool.noConfusion (congrArg Prod.snd e : true = false)

theorem MhwA_not_Bool : ¬ ∀ φ, BoolSch φ → MhwA.Valid φ := fun h => MhwA_not_DNeg (h _ DNeg_bool)

theorem MhwA_not_IdId : ¬ MhwA.Valid IdId := fun h => by
  have h0 := (MhwA.holds_all _ _ _ _).mp ((MhwA.holds_all _ _ _ _).mp
    ((MhwA.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have e := hrW_inj .t _ _ ((MhwA.holds_eqv_t _ _ _ _).mp h0).1
  have e2 := congrArg Prod.snd ((MhwA.eval_eqv _ _ _ _ _ _).symm.trans (e.trans (MhwA.eval_all _ _ _ _)))
  exact Bool.noConfusion (e2 : false = true)

theorem MhwA_not_Class : ¬ ∀ χ, ClassSch χ → MhwA.Valid χ := fun h =>
  MhwA_not_Bool fun φ hφ => MhwA.soundness (MhwG_model _ _) h (d_Bool_of_Class (S := ClassSch) (fun _ hc => hc) φ hφ)

/-! ## Barcan formulas and Type Necessitism -/

theorem MhwA_TCBF : ∀ χ, TCBFSch χ → MhwA.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MhwA.holds_imp _ _ _ _).mpr fun h => ?_
  have e := (MhwA_holds_box _ _ _).mp h
  exact (cast (congrFun (congrArg Prod.fst e) false).symm trivial : False).elim

theorem MhwA_TNec : MhwA.Valid TNec := by
  intro ρ env
  refine (MhwA.holds_tall _ _ _).mpr fun a => (MhwA_holds_box _ _ _).mpr ?_
  refine Prod.ext (funext fun w => ?_) rfl
  cases w
  · exact propext ⟨fun _ => trivial, fun _ => trivial⟩
  · exact propext ⟨fun _ => trivial, fun _ => ⟨a, (MhwA_V_teq a a).mpr rfl⟩⟩

theorem MhwA_BF : MhwA.Valid BF := by
  intro ρ env
  refine (MhwA.holds_tall _ _ _).mpr fun a => (MhwA.holds_all _ _ _ _).mpr fun F => ?_
  refine (MhwA.holds_imp _ _ _ _).mpr fun h => (MhwA_holds_box _ _ _).mpr ?_
  refine (MhwA.eval_all _ _ _ _).trans ?_
  refine Prod.ext (funext fun w => propext ⟨fun _ => trivial, fun _ x => ?_⟩) rfl
  have e := (MhwA_holds_box _ _ _).mp ((MhwA.holds_all _ _ _ _).mp h x)
  exact cast (congrFun (congrArg Prod.fst e) w).symm trivial

theorem MhwA_not_CBF : ¬ MhwA.Valid CBF := fun h => by
  have h0 := (MhwA.holds_all _ _ _ _).mp ((MhwA.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ => ((fun _ => True), false))
  have hb : MhwA.Holds (boxF (all tv0 (Tm.app (.var (.there .here)) (.var .here))) : Fm ((Ctx.nil.text).ext tv0.pred))
      (scons .e fun i => i.elim0) ((), fun _ => ((fun _ => True), false)) := by
    refine (MhwA_holds_box _ _ _).mpr ((MhwA.eval_all _ _ _ _).trans ?_)
    exact Prod.ext (funext fun _ => propext ⟨fun _ => trivial, fun _ _ => trivial⟩) rfl
  have h1 := (MhwA.holds_imp _ _ _ _).mp h0 hb
  have e := (MhwA_holds_box _ _ _).mp ((MhwA.holds_all _ _ _ _).mp h1 ())
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

theorem MhwA_not_Nec : ¬ MhwA.Valid Nec := fun h => by
  have h0 := (MhwA.holds_all _ _ _ _).mp ((MhwA.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  have e := (MhwA_eval_ex _ _ _ _).symm.trans ((MhwA_holds_box _ _ _).mp h0)
  obtain ⟨_, hy⟩ := (cast (congrFun (congrArg Prod.fst e) false).symm trivial :
    ∃ y : Unit, (hrW .e () = hrW .e y ∧ false = true))
  exact Bool.noConfusion hy.2

/-! ## Roots -/

/-- Each item is its own root, or has a root whose code is smaller than its own. -/
theorem MhwA_hrW_own_or_lt : ∀ (c : Code Empty) (x : univH.El c), hrW c x = ⟨c, x⟩ ∨ csz (hrW c x).1 < csz c
  | .arr a .t, G => by
    have hG := hrW_arr_t a G
    split at hG
    · refine Or.inr (Nat.lt_of_le_of_lt (Nat.le_of_eq (congrArg (fun r : RW => csz r.1) hG)) ?_)
      exact Nat.lt_of_le_of_lt (hrW_le a _)
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.succ_le_succ (Nat.le_add_right _ _)))
    · exact Or.inl hG
  | .e, _ => Or.inl rfl
  | .t, _ => Or.inl rfl
  | .base b, _ => b.elim
  | .arr _ .e, _ => Or.inl rfl
  | .arr _ (.base b), _ => b.elim
  | .arr _ (.arr _ _), _ => Or.inl rfl

/-- Each type has an item that is its own root. -/
theorem MhwA_own : ∀ c : Code Empty, ∃ x : univH.El c, hrW c x = ⟨c, x⟩
  | .arr a .t => by
    refine ⟨fun _ => ((fun _ => True), true), ?_⟩
    have hG := hrW_arr_t a (fun _ => ((fun _ => True), true))
    split at hG
    · rename_i h
      obtain ⟨x, hx⟩ := h
      exact Bool.noConfusion (congrArg Prod.snd (congrFun hx x) : true = false)
    · exact hG
  | .e => ⟨(), rfl⟩
  | .t => ⟨((fun _ => True), true), rfl⟩
  | .base b => b.elim
  | .arr _ .e => ⟨fun _ => (), rfl⟩
  | .arr _ (.base b) => b.elim
  | .arr _ (.arr _ _) => ⟨Classical.choice (Univ.El_nonempty (U := univH) _), rfl⟩

/-- A function is its own root, or it is a predicate whose root has a code no larger than its domain. -/
theorem MhwA_hrW_arr (a b : Code Empty) (f : univH.El (.arr a b)) :
    hrW (.arr a b) f = ⟨.arr a b, f⟩ ∨ (b = .t ∧ csz (hrW (.arr a b) f).1 ≤ csz a) := by
  cases b with
  | t =>
    have hG := hrW_arr_t a f
    split at hG
    · exact Or.inr ⟨rfl, Nat.le_trans (Nat.le_of_eq (congrArg (fun r : RW => csz r.1) hG)) (hrW_le a _)⟩
    · exact Or.inl hG
  | e => exact Or.inl rfl
  | base x => exact x.elim
  | arr _ _ => exact Or.inl rfl

/-- Functions on the same domain with the same root are identical. -/
theorem MhwA_hrW_arr_eq (a b c : Code Empty) (f : univH.El (.arr a b)) (g : univH.El (.arr a c))
    (h : hrW (.arr a b) f = hrW (.arr a c) g) : b = c ∧ HEq f g := by
  have big : ∀ d : Code Empty, csz a < csz (Code.arr a d) := fun d => by
    show csz a < csz a + csz d + 1
    omega
  rcases MhwA_hrW_arr a b f with hf | ⟨hb, hf⟩ <;> rcases MhwA_hrW_arr a c g with hg | ⟨hc, hg⟩
  · have e := hf.symm.trans (h.trans hg)
    exact ⟨(Code.arr.inj (Sigma.mk.inj e).1).2, (Sigma.mk.inj e).2⟩
  · rw [← h, hf] at hg
    exact absurd hg (Nat.not_le_of_lt (big b))
  · rw [h, hg] at hf
    exact absurd hf (Nat.not_le_of_lt (big c))
  · subst hb
    subst hc
    exact ⟨rfl, heq_of_eq (hrW_inj _ f g h)⟩

/-! ## Congruence and extensionality -/

theorem MhwA_PCong : MhwA.Valid PCong := by
  intro ρ env
  refine (MhwA.holds_tall _ _ _).mpr fun a => (MhwA.holds_tall _ _ _).mpr fun b =>
    (MhwA.holds_tall _ _ _).mpr fun c => ?_
  refine (MhwA.holds_all _ _ _ _).mpr fun f => (MhwA.holds_all _ _ _ _).mpr fun g =>
    (MhwA.holds_all _ _ _ _).mpr fun x => ?_
  refine (MhwA.holds_imp _ _ _ _).mpr fun h => (MhwA.holds_eqv _ _ _ _ _ _).mpr ⟨?_, rfl⟩
  obtain ⟨ebc, hfg⟩ := MhwA_hrW_arr_eq a b c f g ((MhwA.holds_eqv _ _ _ _ _ _).mp h).1
  subst ebc
  have ef : f = g := eq_of_heq hfg
  subst ef
  rfl

theorem MhwA_not_PExt : ¬ MhwA.Valid PExt := fun h => by
  have h0 := (MhwA.holds_tall _ _ _).mp ((MhwA.holds_tall _ _ _).mp ((MhwA.holds_tall _ _ _).mp
    (h (fun i => i.elim0) ()) .e) .e) (.arr .e .t)
  have h1 := (MhwA.holds_all _ _ _ _).mp ((MhwA.holds_all _ _ _ _).mp h0 (fun _ : Unit => ()))
    (fun _ : Unit => fun y : Unit => (((fun w => hrW .e y = hrW .e () ∧ w = true), false) : univH.P))
  have h2 := (MhwA.holds_imp _ _ _ _).mp h1 ((MhwA.holds_all _ _ _ _).mpr fun _ =>
    (MhwA.holds_eqv _ _ _ _ _ _).mpr ⟨(hrW_hae .e ()).symm, rfl⟩)
  have h3 := ((MhwA.holds_eqv _ _ _ _ _ _).mp h2).1
  have h4 := congrArg Sigma.fst h3
  injection h4 with _ h5
  exact nomatch h5

/-! ## Extensionality and intensionality of types -/

theorem MhwA_ExtT : MhwA.Valid ExtT := by
  intro ρ env
  refine (MhwA.holds_tall _ _ _).mpr fun a => (MhwA.holds_tall _ _ _).mpr fun b => ?_
  refine (MhwA.holds_imp _ _ _ _).mpr fun h => (MhwA.holds_teq _ _ _ _).mpr ((MhwA_V_teq _ _).mpr ?_)
  have hs := (MhwA.holds_conj _ _ _ _).mp h
  obtain ⟨xa, hxa⟩ := MhwA_own a
  obtain ⟨xb, hxb⟩ := MhwA_own b
  obtain ⟨y, hy⟩ := (MhwA.holds_ex _ _ _ _).mp ((MhwA.holds_all _ _ _ _).mp hs.1 xa)
  obtain ⟨x, hx⟩ := (MhwA.holds_ex _ _ _ _).mp ((MhwA.holds_all _ _ _ _).mp hs.2 xb)
  have e1 : hrW a xa = hrW b y := ((MhwA.holds_eqv _ _ _ _ _ _).mp hy).1
  have e2 : hrW a x = hrW b xb := ((MhwA.holds_eqv _ _ _ _ _ _).mp hx).1
  rcases MhwA_hrW_own_or_lt b y with h1 | h1
  · exact congrArg Sigma.fst (hxa.symm.trans (e1.trans h1))
  rcases MhwA_hrW_own_or_lt a x with h2 | h2
  · exact congrArg Sigma.fst (h2.symm.trans (e2.trans hxb))
  rw [← e1, hxa] at h1
  rw [e2, hxb] at h2
  have c1 : csz a < csz b := h1
  have c2 : csz b < csz a := h2
  omega

/-- `□(α ⊑ β)` is never true: at the other world, nothing is identified with anything. -/
theorem MhwA_IntT : MhwA.Valid IntT := by
  intro ρ env
  refine (MhwA.holds_tall _ _ _).mpr fun a => (MhwA.holds_tall _ _ _).mpr fun _ => ?_
  refine (MhwA.holds_imp _ _ _ _).mpr fun h => ?_
  have e := (MhwA.eval_all _ _ _ _).symm.trans ((MhwA_holds_box _ _ _).mp ((MhwA.holds_conj _ _ _ _).mp h).1)
  have h1 := cast (congrFun (congrArg Prod.fst e) false).symm trivial
  have x0 := Classical.choice (Univ.El_nonempty (U := MhwA.U) a)
  obtain ⟨_, hy⟩ := Eq.mp (congrFun (congrArg Prod.fst (MhwA_eval_ex _ _ _ _)) false) (h1 x0)
  exact Bool.noConfusion hy.2

end Al
end PIF
