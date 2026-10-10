import PIBF
set_option autoImplicit false

/-!
# More about `𝔐_hw`

In `𝔐_hw` (`MhwF`, `PIAlgModels.lean`) a proposition is a pair of a set of two worlds (the actual
one `true`, and `false`) and a tag. Identity of items is sameness of root at the actual world and
fails at the other world, with tag `false`; `≈` is identity at the actual world and difference at
the other world; the connectives and quantifiers act world by world, with tag `true`. `□φ`, that
is `φ ≡ ⊤`, says that the value of `φ` is `⊤` itself: true at both worlds, with tag `true`.

Valid: Inj≈, Recovery, Ext≈, Int≈ (vacuously: `□(α ⊑ β)` is never true), ND×, PCong, TBF, TCBF,
BF. Refuted: PExt, CBF, Nec.
-/

namespace PIF
namespace Al

/-! ## Basic facts -/

theorem Mhw_teq_V (a b : Code MhwF.U.Base) : MhwF.U.V (MhwF.teq a b) ↔ a = b := by
  show (if true = true then a = b else a ≠ b) ↔ a = b
  simp

/-- `□φ` holds just when the value of `φ` is `⊤`. -/
theorem Mhw_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MhwF.U.TEnv n) (env : MhwF.U.Env Γ ρ) :
    MhwF.Holds (boxF φ) ρ env ↔ MhwF.eval φ ρ env = ((fun _ => True), true) := by
  refine (MhwF.holds_eqv_t _ _ _ _).trans ⟨fun h => ?_, fun h => ⟨?_, rfl⟩⟩
  · exact (hrW_inj .t _ _ h.1).trans (Mhw_topF _ _)
  · exact congrArg (hrW .t) (h.trans (Mhw_topF _ _).symm)

theorem Mhw_at_all {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MhwF.U.TEnv n)
    (env : MhwF.U.Env Γ ρ) (w : Bool) :
    (MhwF.eval (Tm.all σ φ) ρ env).1 w ↔ ∀ v : MhwF.U.CatVal σ.1 ρ, (MhwF.eval φ ρ (env, v)).1 w := by
  rw [MhwF.eval_all]
  refine Invariance.forall_heq (Univ.El_code ρ σ.2) fun x v hxv => ?_
  have e : cast (Univ.El_code ρ σ.2) x = v := eq_of_heq ((cast_heq _ _).trans hxv)
  subst e
  exact Iff.rfl

theorem Mhw_all_tag {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MhwF.U.TEnv n)
    (env : MhwF.U.Env Γ ρ) : (MhwF.eval (Tm.all σ φ) ρ env).2 = true := by
  rw [MhwF.eval_all]
  rfl

theorem Mhw_cast_ex_eq {c : Code MhwF.U.Base} {A' : Type} (hA : MhwF.U.El c = A')
    (h : ((MhwF.U.El c → MhwF.U.P) → MhwF.U.P) = ((A' → MhwF.U.P) → MhwF.U.P)) (Q : A' → MhwF.U.P) :
    cast h (fun R => MhwF.ex c R) Q = MhwF.ex c (fun x => Q (cast hA x)) := by
  subst hA; rfl

theorem Mhw_eval_ex {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MhwF.U.TEnv n)
    (env : MhwF.U.Env Γ ρ) :
    MhwF.eval (Tm.ex σ φ) ρ env =
      MhwF.ex (MhwF.U.code σ.1 ρ) (fun x => MhwF.eval φ ρ (env, cast (Univ.El_code ρ σ.2) x)) :=
  Mhw_cast_ex_eq (Univ.El_code ρ σ.2) _ _

theorem Mhw_at_ex {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MhwF.U.TEnv n)
    (env : MhwF.U.Env Γ ρ) (w : Bool) :
    (MhwF.eval (Tm.ex σ φ) ρ env).1 w ↔ ∃ v : MhwF.U.CatVal σ.1 ρ, (MhwF.eval φ ρ (env, v)).1 w := by
  rw [Mhw_eval_ex]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, hx⟩
  · rintro ⟨v, hv⟩
    refine ⟨cast (Univ.El_code ρ σ.2).symm v, ?_⟩
    show (MhwF.eval φ ρ (env, cast (Univ.El_code ρ σ.2) (cast (Univ.El_code ρ σ.2).symm v))).1 w
    rw [cast_cast]
    exact hv

theorem Mhw_eqv_false {n : Nat} {Γ : Ctx n} (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1) (ρ : MhwF.U.TEnv n)
    (env : MhwF.U.Env Γ ρ) : ¬ (MhwF.eval (Tm.eqv σ τ x y) ρ env).1 false := by
  rw [MhwF.eval_eqv]
  exact fun h => Bool.noConfusion h.2

theorem Mhw_eqv_tag {n : Nat} {Γ : Ctx n} (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1) (ρ : MhwF.U.TEnv n)
    (env : MhwF.U.Env Γ ρ) : (MhwF.eval (Tm.eqv σ τ x y) ρ env).2 = false := by
  rw [MhwF.eval_eqv]
  rfl

/-! ## Roots -/

/-- The root of a function is the function itself, unless it is a haecceity, whose root is the
root of an item of its argument type. -/
theorem Mhw_hrW_arr (a d : Code univH.Base) (f : univH.El (.arr a d)) :
    hrW (.arr a d) f = ⟨.arr a d, f⟩ ∨ (d = .t ∧ csz (hrW (.arr a d) f).1 ≤ csz a) := by
  cases d with
  | t =>
    rw [hrW_arr_t]
    split
    · exact Or.inr ⟨rfl, hrW_le a _⟩
    · exact Or.inl rfl
  | e => exact Or.inl rfl
  | base b => exact b.elim
  | arr _ _ => exact Or.inl rfl

/-- Every item is its own root, or has a root of smaller code. -/
theorem Mhw_hrW_cases : ∀ (c : Code univH.Base) (x : univH.El c), hrW c x = ⟨c, x⟩ ∨ csz (hrW c x).1 < csz c
  | .e, _ => Or.inl rfl
  | .t, _ => Or.inl rfl
  | .base b, _ => b.elim
  | .arr a d, f => (Mhw_hrW_arr a d f).imp id fun h => by
      have : csz a < csz (Code.arr a d) := by show csz a < csz a + csz d + 1; omega
      exact Nat.lt_of_le_of_lt h.2 this

/-- Every type has an item which is its own root. -/
theorem Mhw_fix : ∀ c : Code univH.Base, ∃ x : univH.El c, hrW c x = ⟨c, x⟩
  | .e => ⟨(), rfl⟩
  | .t => ⟨((fun _ => True), true), rfl⟩
  | .base b => b.elim
  | .arr a .t => by
    refine ⟨(fun _ => ((fun _ => True), true) : univH.El (.arr a .t)), (hrW_arr_t a _).trans ?_⟩
    split
    · next h =>
      obtain ⟨x, hx⟩ := h
      exact Bool.noConfusion (congrArg Prod.snd (congrFun hx x))
    · rfl
  | .arr a .e => ⟨fun _ => (), rfl⟩
  | .arr _ (.base b) => b.elim
  | .arr a (.arr c d) => by
    obtain ⟨y⟩ := Univ.El_nonempty (U := univH) (.arr c d)
    exact ⟨fun _ => y, rfl⟩

/-- Two functions with the same argument type and the same root are the same function. -/
theorem Mhw_arr_same {a b c : Code univH.Base} {f : univH.El (.arr a b)} {g : univH.El (.arr a c)}
    (h : hrW (.arr a b) f = hrW (.arr a c) g) : b = c ∧ HEq f g := by
  rcases Mhw_hrW_arr a b f with hf | ⟨hb, hf⟩ <;> rcases Mhw_hrW_arr a c g with hg | ⟨hc, hg⟩
  · rw [hf, hg] at h
    obtain ⟨h1, h2⟩ := Sigma.mk.inj h
    exact ⟨(Code.arr.inj h1).2, h2⟩
  · rw [← h, hf] at hg
    exact absurd hg (Nat.not_le.mpr (by show csz a < csz a + csz b + 1; omega))
  · rw [h, hg] at hf
    exact absurd hf (Nat.not_le.mpr (by show csz a < csz a + csz c + 1; omega))
  · subst hb; subst hc
    exact ⟨rfl, heq_of_eq (hrW_inj _ _ _ h)⟩

/-! ## Identity of types -/

theorem Mhw_Inj : MhwF.Valid Inj := by
  intro ρ env
  refine (MhwF.holds_tall _ _ _).mpr fun a => (MhwF.holds_tall _ _ _).mpr fun b => ?_
  refine (MhwF.holds_tall _ _ _).mpr fun c => (MhwF.holds_tall _ _ _).mpr fun d => ?_
  refine (MhwF.holds_imp _ _ _ _).mpr fun h => (MhwF.holds_conj _ _ _ _).mpr ⟨?_, ?_⟩
  · have h' : Code.arr a c = Code.arr b d := (Mhw_teq_V _ _).mp ((MhwF.holds_teq _ _ _ _).mp h)
    exact (MhwF.holds_teq _ _ _ _).mpr ((Mhw_teq_V _ _).mpr (Code.arr.inj h').1)
  · have h' : Code.arr a c = Code.arr b d := (Mhw_teq_V _ _).mp ((MhwF.holds_teq _ _ _ _).mp h)
    exact (MhwF.holds_teq _ _ _ _).mpr ((Mhw_teq_V _ _).mpr (Code.arr.inj h').2)

theorem Mhw_Recovery : MhwF.Valid Recovery := by
  intro ρ env
  refine (MhwF.holds_tall _ _ _).mpr fun a => (MhwF.holds_tall _ _ _).mpr fun b => ?_
  refine (MhwF.holds_tall _ _ _).mpr fun c => (MhwF.holds_tall _ _ _).mpr fun d => ?_
  refine (MhwF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d :=
    (Mhw_teq_V _ _).mp ((MhwF.holds_teq _ _ _ _).mp ((MhwF.holds_conj _ _ _ _).mp h).1)
  exact (MhwF.holds_teq _ _ _ _).mpr ((Mhw_teq_V _ _).mpr (Code.arr.inj h').2)

theorem Mhw_ExtT : MhwF.Valid ExtT := by
  intro ρ env
  refine (MhwF.holds_tall _ _ _).mpr fun a => (MhwF.holds_tall _ _ _).mpr fun b => ?_
  refine (MhwF.holds_imp _ _ _ _).mpr fun h => (MhwF.holds_teq _ _ _ _).mpr ((Mhw_teq_V _ _).mpr ?_)
  obtain ⟨hs, hp⟩ := (MhwF.holds_conj _ _ _ _).mp h
  obtain ⟨x0, hx0⟩ := Mhw_fix a
  obtain ⟨y0, hy0⟩ := Mhw_fix b
  obtain ⟨y, hy⟩ := (MhwF.holds_ex _ _ _ _).mp ((MhwF.holds_all _ _ _ _).mp hs x0)
  obtain ⟨x, hx⟩ := (MhwF.holds_ex _ _ _ _).mp ((MhwF.holds_all _ _ _ _).mp hp y0)
  have e1 : hrW a x0 = hrW b y := ((MhwF.holds_eqv _ _ _ _ _ _).mp hy).1
  have e2 : hrW a x = hrW b y0 := ((MhwF.holds_eqv _ _ _ _ _ _).mp hx).1
  rw [hx0] at e1
  rw [hy0] at e2
  have l2 : csz b ≤ csz a := Nat.le_trans (Nat.le_of_eq (congrArg (fun p : RW => csz p.1) e2).symm) (hrW_le a x)
  rcases Mhw_hrW_cases b y with hb | hb
  · exact congrArg Sigma.fst (e1.trans hb)
  · rw [← e1] at hb
    exact absurd hb (Nat.not_lt.mpr l2)

theorem Mhw_IntT : MhwF.Valid IntT := by
  intro ρ env
  refine (MhwF.holds_tall _ _ _).mpr fun a => (MhwF.holds_tall _ _ _).mpr fun b => ?_
  refine (MhwF.holds_imp _ _ _ _).mpr fun h => ?_
  have e := (Mhw_box _ _ _).mp ((MhwF.holds_conj _ _ _ _).mp h).1
  have hf : (MhwF.eval (subT : Fm (Ctx.nil.text.text)) (scons b (scons a ρ)) env).1 false := by
    rw [e]; trivial
  obtain ⟨x0⟩ := Univ.El_nonempty (U := univH) a
  obtain ⟨y, hy⟩ := (Mhw_at_ex _ _ _ _ false).mp ((Mhw_at_all _ _ _ _ false).mp hf x0)
  exact (Mhw_eqv_false _ _ _ _ _ _ hy).elim

/-! ## Necessity of distinctness across types -/

theorem Mhw_NDX : MhwF.Valid NDX := by
  intro ρ env
  refine (MhwF.holds_tall _ _ _).mpr fun a => (MhwF.holds_tall _ _ _).mpr fun b => ?_
  refine (MhwF.holds_all _ _ _ _).mpr fun x => (MhwF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MhwF.holds_imp _ _ _ _).mpr fun hn => (Mhw_box _ _ _).mpr ?_
  refine Prod.ext (funext fun w => propext ⟨fun _ => trivial, fun _ => ?_⟩) rfl
  cases w
  · exact Mhw_eqv_false _ _ _ _ _ _
  · exact (MhwF.holds_neg _ _ _).mp hn

/-! ## PCong and PExt -/

theorem Mhw_PCong : MhwF.Valid PCong := by
  intro ρ env
  refine (MhwF.holds_tall _ _ _).mpr fun a => (MhwF.holds_tall _ _ _).mpr fun b => ?_
  refine (MhwF.holds_tall _ _ _).mpr fun c => ?_
  refine (MhwF.holds_all _ _ _ _).mpr fun f => (MhwF.holds_all _ _ _ _).mpr fun g => ?_
  refine (MhwF.holds_all _ _ _ _).mpr fun x => (MhwF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : hrW (.arr a b) f = hrW (.arr a c) g := ((MhwF.holds_eqv _ _ _ _ _ _).mp h).1
  obtain ⟨hbc, hfg⟩ := Mhw_arr_same h'
  subst hbc
  have e : f = g := eq_of_heq hfg
  subst e
  exact (MhwF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, rfl⟩

/-- PExt fails: the constant function to the entity and the constant function to its haecceity
agree in value everywhere (by Haecceitism), but have different types of values. -/
theorem Mhw_not_PExt : ¬ MhwF.Valid PExt := fun h => by
  have h0 := (MhwF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e
  have h1 := (MhwF.holds_tall _ _ _).mp h0 .e
  have h2 := (MhwF.holds_tall _ _ _).mp h1 (.arr .e .t)
  have h3 := (MhwF.holds_all _ _ _ _).mp ((MhwF.holds_all _ _ _ _).mp h2 (fun _ => ()))
    (fun _ => fun y => ((fun w => hrW .e y = hrW .e () ∧ w = true), false))
  have h4 := (MhwF.holds_imp _ _ _ _).mp h3 ((MhwF.holds_all _ _ _ _).mpr fun _ =>
    (MhwF.holds_eqv _ _ _ _ _ _).mpr ⟨(hrW_hae .e ()).symm, rfl⟩)
  have e : Code.arr (.e : Code univH.Base) .e = .arr .e (.arr .e .t) :=
    congrArg Sigma.fst ((MhwF.holds_eqv _ _ _ _ _ _).mp h4).1
  nomatch e

/-! ## The Barcan formulas, and Necessitism -/

theorem Mhw_TBF : ∀ χ, TBFSch χ → MhwF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MhwF.holds_imp _ _ _ _).mpr fun h => (Mhw_box _ _ _).mpr ?_
  refine Prod.ext (funext fun w => propext ⟨fun _ => trivial, fun _ a => ?_⟩) rfl
  have e := (Mhw_box _ _ _).mp ((MhwF.holds_tall _ _ _).mp h a)
  exact cast (congrArg (fun p => p.1 w) e).symm trivial

theorem Mhw_BF : MhwF.Valid BF := by
  intro ρ env
  refine (MhwF.holds_tall _ _ _).mpr fun a => (MhwF.holds_all _ _ _ _).mpr fun F => ?_
  refine (MhwF.holds_imp _ _ _ _).mpr fun h => (Mhw_box _ _ _).mpr ?_
  refine Prod.ext (funext fun w => propext ⟨fun _ => trivial, fun _ => (Mhw_at_all _ _ _ _ w).mpr fun x => ?_⟩) ?_
  · have e := (Mhw_box _ _ _).mp ((MhwF.holds_all _ _ _ _).mp h x)
    exact cast (congrArg (fun p => p.1 w) e).symm trivial
  · exact Mhw_all_tag _ _ _ _

/-- CBF fails: a property true of everything at both worlds, but whose values have the tag `false`. -/
theorem Mhw_not_CBF : ¬ MhwF.Valid CBF := fun h => by
  have h0 := (MhwF.holds_all _ _ _ _).mp ((MhwF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ => ((fun _ => True), false))
  have h1 := (MhwF.holds_imp _ _ _ _).mp h0 ((Mhw_box _ _ _).mpr (by
    refine Prod.ext (funext fun w => propext ⟨fun _ => trivial, fun _ => (Mhw_at_all _ _ _ _ w).mpr fun _ => trivial⟩) ?_
    exact Mhw_all_tag _ _ _ _))
  have e := (Mhw_box _ _ _).mp ((MhwF.holds_all _ _ _ _).mp h1 ())
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

/-- Nec fails: nothing is identified with anything at the other world. -/
theorem Mhw_not_Nec : ¬ MhwF.Valid Nec := fun h => by
  have h0 := (MhwF.holds_all _ _ _ _).mp ((MhwF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  have e := congrArg (fun p => p.1 false) ((Mhw_box _ _ _).mp h0)
  obtain ⟨y, hy⟩ := (Mhw_at_ex _ _ _ _ false).mp (cast e.symm trivial)
  exact Mhw_eqv_false _ _ _ _ _ _ hy

/-! ## TCBF, by a logical relation

Every value of a constant is *good*: if it is true at the other world, it has the tag `true`. A
logical relation shows that the value of every closed formula is good. So if `𝔸α φ` is true at
both worlds, each instance of `φ` is true at both worlds, and so has the tag `true`: it is `⊤`. -/

section Good
variable (Gt : MhwF.U.P → Prop)

/-- Goodness at each code. -/
def Mhw_GC : (c : Code MhwF.U.Base) → MhwF.U.El c → Prop
  | .e, _ => True
  | .t, p => Gt p
  | .base _, _ => True
  | .arr a c, f => ∀ x, Mhw_GC a x → Mhw_GC c (f x)

/-- Goodness at each category. -/
def Mhw_GK : {n : Nat} → (K : Cat n) → (ρ : MhwF.U.TEnv n) → MhwF.U.CatVal K ρ → Prop
  | _, .e, _, _ => True
  | _, .t, _, p => Gt p
  | _, .var i, ρ, x => Mhw_GC Gt (ρ i) x
  | _, .arr K L, ρ, f => ∀ u, Mhw_GK K ρ u → Mhw_GK L ρ (f u)
  | _, .pi K, ρ, G => ∀ a, Mhw_GK K (scons a ρ) (G a)

theorem Mhw_GC_heq {c c' : Code MhwF.U.Base} (hc : c = c') (x : MhwF.U.El c) (y : MhwF.U.El c')
    (h : HEq x y) : Mhw_GC Gt c x ↔ Mhw_GC Gt c' y := by
  subst hc; cases h; exact Iff.rfl

theorem Mhw_GK_GC {n : Nat} (K : Cat n) : ∀ (_ : K.Simple) (ρ : MhwF.U.TEnv n) (u : MhwF.U.CatVal K ρ)
    (x : MhwF.U.El (MhwF.U.code K ρ)), HEq u x → (Mhw_GK Gt K ρ u ↔ Mhw_GC Gt (MhwF.U.code K ρ) x) := by
  induction K with
  | e => intro _ ρ u x hx; cases hx; exact Iff.rfl
  | t => intro _ ρ u x hx; cases hx; exact Iff.rfl
  | var i => intro _ ρ u x hx; cases hx; exact Iff.rfl
  | arr a b iha ihb =>
    intro hK ρ u x hx
    refine Invariance.forall_heq (Univ.El_code ρ hK.1).symm fun v y hvy => ?_
    refine imp_congr (iha hK.1 ρ v y hvy) (ihb hK.2 ρ _ _ ?_)
    exact heq_app (Univ.El_code ρ hK.1).symm (Univ.El_code ρ hK.2).symm hx hvy
  | pi _ _ => intro hK; exact hK.elim

theorem Mhw_GK_ren {n : Nat} (K : Cat n) : ∀ {m : Nat} (r : Fin n → Fin m) (ρ : MhwF.U.TEnv m)
    (ρ₂ : MhwF.U.TEnv n), (∀ i, ρ (r i) = ρ₂ i) → ∀ (v : MhwF.U.CatVal (K.ren r) ρ) (w : MhwF.U.CatVal K ρ₂),
    HEq v w → (Mhw_GK Gt (K.ren r) ρ v ↔ Mhw_GK Gt K ρ₂ w) := by
  induction K with
  | e => intro m r ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | t => intro m r ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | var i => intro m r ρ ρ₂ hρ v w hv; exact Mhw_GC_heq Gt (hρ i) v w hv
  | arr a b iha ihb =>
    intro m r ρ ρ₂ hρ v w hv
    refine Invariance.forall_heq (Univ.CatVal_ren a r ρ ρ₂ hρ) fun u y huy => ?_
    refine imp_congr (iha r ρ ρ₂ hρ u y huy) (ihb r ρ ρ₂ hρ _ _ ?_)
    exact heq_app (Univ.CatVal_ren a r ρ ρ₂ hρ) (Univ.CatVal_ren b r ρ ρ₂ hρ) hv huy
  | pi K ih =>
    intro m r ρ ρ₂ hρ v w hv
    refine forall_congr' fun a => ?_
    exact ih (liftR r) (scons a ρ) (scons a ρ₂) (fin_cases rfl (fun i => hρ i)) _ _
      (heq_dapp (fun a => Univ.CatVal_ren K (liftR r) (scons a ρ) (scons a ρ₂)
        (fin_cases rfl (fun i => hρ i))) hv rfl)

theorem Mhw_GK_sub {n : Nat} (K : Cat n) : ∀ {m : Nat} (s : Fin n → Ty m) (ρ : MhwF.U.TEnv m)
    (ρ₂ : MhwF.U.TEnv n), (∀ i, MhwF.U.code (s i).1 ρ = ρ₂ i) →
    ∀ (v : MhwF.U.CatVal (K.sub s) ρ) (w : MhwF.U.CatVal K ρ₂),
    HEq v w → (Mhw_GK Gt (K.sub s) ρ v ↔ Mhw_GK Gt K ρ₂ w) := by
  induction K with
  | e => intro m s ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | t => intro m s ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | var i =>
    intro m s ρ ρ₂ hρ v w hv
    exact (Mhw_GK_GC Gt (s i).1 (s i).2 ρ v (cast (Univ.El_code ρ (s i).2).symm v) (cast_heq _ v).symm).trans
      (Mhw_GC_heq Gt (hρ i) _ w ((cast_heq _ v).trans hv))
  | arr a b iha ihb =>
    intro m s ρ ρ₂ hρ v w hv
    refine Invariance.forall_heq (Univ.CatVal_sub a s ρ ρ₂ hρ) fun u y huy => ?_
    refine imp_congr (iha s ρ ρ₂ hρ u y huy) (ihb s ρ ρ₂ hρ _ _ ?_)
    exact heq_app (Univ.CatVal_sub a s ρ ρ₂ hρ) (Univ.CatVal_sub b s ρ ρ₂ hρ) hv huy
  | pi K ih =>
    intro m s ρ ρ₂ hρ v w hv
    have hl : ∀ a, ∀ i, MhwF.U.code (liftT s i).1 (scons a ρ) = scons a ρ₂ i := fun a =>
      fin_cases rfl (fun i => by
        show MhwF.U.code ((s i).1.ren fs) (scons a ρ) = ρ₂ i
        rw [Univ.code_ren]; exact hρ i)
    refine forall_congr' fun a => ?_
    exact ih (liftT s) (scons a ρ) (scons a ρ₂) (hl a) _ _
      (heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ) (scons a ρ₂) (hl a)) hv rfl)

/-- Good values for the term variables of a context. -/
def Mhw_EG : {n : Nat} → (Γ : Ctx n) → (ρ : MhwF.U.TEnv n) → MhwF.U.Env Γ ρ → Prop
  | _, .nil, _, _ => True
  | _, .ext Γ σ, ρ, env => Mhw_EG Γ ρ env.1 ∧ Mhw_GK Gt σ.1 ρ env.2
  | _, .text Γ, ρ, env => Mhw_EG Γ (fun i => ρ (fs i)) env

theorem Mhw_lookup_good {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) :
    ∀ (ρ : MhwF.U.TEnv n) (env : MhwF.U.Env Γ ρ), Mhw_EG Gt Γ ρ env → Mhw_GK Gt K ρ (MhwF.U.lookup x ρ env) := by
  induction x with
  | here => intro ρ env h; exact h.2
  | there y ih => intro ρ env h; exact ih ρ env.1 h.1
  | tthere y ih =>
    intro ρ env h
    exact (Mhw_GK_ren Gt _ fs ρ (fun i => ρ (fs i)) (fun _ => rfl) _ _ (MhwF.lookup_tthere y ρ env)).mpr
      (ih _ env h)

/-- **The fundamental lemma**: if every constant is good, every term is good under good values
for its variables. -/
theorem Mhw_fund (hc : ∀ {n : Nat} {K : Cat n} (c : Const n K) (ρ : MhwF.U.TEnv n),
      Mhw_GK Gt K ρ (MhwF.constVal c ρ))
    {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) : ∀ (ρ : MhwF.U.TEnv n) (env : MhwF.U.Env Γ ρ),
    Mhw_EG Gt Γ ρ env → Mhw_GK Gt K ρ (MhwF.eval M ρ env) := by
  induction M with
  | var x => intro ρ env h; exact Mhw_lookup_good Gt x ρ env h
  | const c => intro ρ _ _; exact hc c ρ
  | app f a ihf iha => intro ρ env h; exact ihf ρ env h _ (iha ρ env h)
  | lam σ b ih => intro ρ env h u hu; exact ih ρ (env, u) ⟨h, hu⟩
  | tlam b ih => intro ρ env h a; exact ih (scons a ρ) env h
  | tapp f σ ih =>
    intro ρ env h
    exact (Mhw_GK_sub Gt _ (inst σ) ρ (scons (MhwF.U.code σ.1 ρ) ρ) (fin_cases rfl (fun _ => rfl)) _ _
      (MhwF.heq_eval_tapp f σ ρ env)).mpr (ih ρ env h (MhwF.U.code σ.1 ρ))

end Good

/-- A proposition is good if, when it is true at the other world, it has the tag `true`. -/
def Mhw_Gt (p : MhwF.U.P) : Prop := p.1 false → p.2 = true

theorem Mhw_const_good {n : Nat} {K : Cat n} (c : Const n K) (ρ : MhwF.U.TEnv n) :
    Mhw_GK Mhw_Gt K ρ (MhwF.constVal c ρ) := by
  cases c with
  | neg => intro _ _ _; rfl
  | imp => intro _ _ _ _ _; rfl
  | and => intro _ _ _ _ _; rfl
  | or => intro _ _ _ _ _; rfl
  | iff => intro _ _ _ _ _; rfl
  | all => intro _ _ _ _; rfl
  | ex => intro _ _ _ _; rfl
  | tall => intro _ _ _; rfl
  | tex => intro _ _ _; rfl
  | eqv => intro _ _ _ _ _ _ h; exact h.2
  | teq => intro _ _ _; rfl

/-- The value of every closed formula (with one free type variable) is good. -/
theorem Mhw_closed_good (φ : Fm Ctx.nil.text) (a : Code MhwF.U.Base) (ρ : MhwF.U.TEnv 0)
    (env : MhwF.U.Env Ctx.nil ρ) : Mhw_Gt (MhwF.eval φ (scons a ρ) env) :=
  Mhw_fund Mhw_Gt Mhw_const_good φ (scons a ρ) env trivial

theorem Mhw_TCBF : ∀ χ, TCBFSch χ → MhwF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MhwF.holds_imp _ _ _ _).mpr fun h => (MhwF.holds_tall _ _ _).mpr fun a => (Mhw_box _ _ _).mpr ?_
  have e := (Mhw_box _ _ _).mp h
  have hw : ∀ w, (MhwF.eval φ (scons a ρ) env).1 w := fun w =>
    (cast (congrArg (fun p => p.1 w) e).symm trivial : ∀ a, (MhwF.eval φ (scons a ρ) env).1 w) a
  exact Prod.ext (funext fun w => propext ⟨fun _ => trivial, fun _ => hw w⟩)
    (Mhw_closed_good φ a ρ env (hw false))

end Al
end PIF
