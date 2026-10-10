import PIBF
set_option autoImplicit false

/-!
# Open questions: the profile of `𝔐_ii`

`𝔐_ii` (`lean/PIAlgModels.lean`, `MiiF`): propositions are pairs of a truth value and a tag; the
values of `≡` and of the quantifiers have tag `false`, those of `≈` and of the connectives tag
`true`. There is one entity, and identity is identity (`a = b ∧ HEq x y`).

Since `⊤` is a negation, its value is `(True, true)`; so `□φ` (that is, `φ ≡ ⊤`) holds just in case
`φ` is true and its value has tag `true`. Hence a true sentence whose main operator is a connective
or `≈` is necessary, while no sentence whose main operator is `≡` or a quantifier is.
-/

namespace PIF
namespace Al
open Tm

/-! ## Basic facts -/

theorem Mii_topF {n : Nat} {Γ : Ctx n} (ρ : MiiF.U.TEnv n) (env : MiiF.U.Env Γ ρ) :
    MiiF.eval (topF : Fm Γ) ρ env = (True, true) :=
  Prod.ext (propext ⟨fun _ => trivial, fun _ => MiiF.holds_topF ρ env ⟨(False, true), id⟩⟩) rfl

/-- `□φ` holds just in case `φ` has the value of `⊤`: true, with tag `true`. -/
theorem Mii_holds_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MiiF.U.TEnv n) (env : MiiF.U.Env Γ ρ) :
    MiiF.Holds (boxF φ) ρ env ↔ MiiF.eval φ ρ env = (True, true) :=
  (MiiF.holds_eqv_t _ _ _ _).trans ⟨fun h => (eq_of_heq h.2).trans (Mii_topF ρ env),
    fun h => ⟨rfl, heq_of_eq (h.trans (Mii_topF ρ env).symm)⟩⟩

theorem Mii_eq_top {p : Prop × Bool} (h1 : p.1) (h2 : p.2 = true) : p = (True, true) :=
  Prod.ext (propext ⟨fun _ => trivial, fun _ => h1⟩) h2

/-- A formula whose value has tag `false` is not necessary. -/
theorem Mii_not_box_of_snd {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MiiF.U.TEnv n) (env : MiiF.U.Env Γ ρ)
    (h : (MiiF.eval φ ρ env).2 = false) : ¬ MiiF.Holds (boxF φ) ρ env := fun hb =>
  Bool.noConfusion (h.symm.trans (congrArg Prod.snd ((Mii_holds_box φ ρ env).mp hb)) : false = true)

theorem Mii_cast_ex_eq {c : Code Empty} {A' : Type} (hA : MiiF.U.El c = A')
    (h : ((MiiF.U.El c → MiiF.U.P) → MiiF.U.P) = ((A' → MiiF.U.P) → MiiF.U.P)) (Q : A' → MiiF.U.P) :
    cast h (fun R => MiiF.ex c R) Q = MiiF.ex c (fun x => Q (cast hA x)) := by
  subst hA; rfl

/-- The value of an existential quantification. -/
theorem Mii_eval_ex {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MiiF.U.TEnv n)
    (env : MiiF.U.Env Γ ρ) :
    MiiF.eval (Tm.ex σ φ) ρ env = MiiF.ex (MiiF.U.code σ.1 ρ) (fun x => MiiF.eval φ ρ (env, cast (Univ.El_code ρ σ.2) x)) :=
  Mii_cast_ex_eq (Univ.El_code ρ σ.2) _ _

theorem Mii_snd_all {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MiiF.U.TEnv n)
    (env : MiiF.U.Env Γ ρ) : (MiiF.eval (Tm.all σ φ) ρ env).2 = false :=
  congrArg Prod.snd (MiiF.eval_all σ φ ρ env)

theorem Mii_snd_ex {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MiiF.U.TEnv n)
    (env : MiiF.U.Env Γ ρ) : (MiiF.eval (Tm.ex σ φ) ρ env).2 = false :=
  congrArg Prod.snd (Mii_eval_ex σ φ ρ env)

/-! ## Identity across types -/

theorem Mii_Disjoint : MiiF.Valid Disjoint := by
  intro ρ env
  refine (MiiF.holds_tall _ _ _).mpr fun _ => (MiiF.holds_tall _ _ _).mpr fun _ => ?_
  refine (MiiF.holds_imp _ _ _ _).mpr fun hn => ?_
  refine (MiiF.holds_all _ _ _ _).mpr fun _ => (MiiF.holds_all _ _ _ _).mpr fun _ => ?_
  refine (MiiF.holds_neg _ _ _).mpr fun hxy => ?_
  exact (MiiF.holds_neg _ _ _).mp hn ((MiiF.holds_teq _ _ _ _).mpr ((MiiF.holds_eqv _ _ _ _ _ _).mp hxy).1)

theorem Mii_Slogan : MiiF.Valid Slogan := by
  intro ρ env
  refine (MiiF.holds_all _ _ _ _).mpr fun _ => (MiiF.holds_tall _ _ _).mpr fun b => ?_
  refine (MiiF.holds_all _ _ _ _).mpr fun _ => (MiiF.holds_neg _ _ _).mpr fun hxy => ?_
  have h := ((MiiF.holds_eqv _ _ _ _ _ _).mp hxy).1
  exact nomatch (show (Code.e : Code Empty) = .arr b .t from h)

theorem Mii_not_Twin : ¬ MiiF.Valid Twin := fun h => by
  have h0 := (MiiF.holds_all _ _ _ _).mp ((MiiF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  obtain ⟨_, hb⟩ := (MiiF.holds_tex _ _ _).mp h0
  have hc := (MiiF.holds_conj _ _ _ _).mp hb
  obtain ⟨_, hy⟩ := (MiiF.holds_ex _ _ _ _).mp hc.2
  exact (MiiF.holds_neg _ _ _).mp hc.1 ((MiiF.holds_teq _ _ _ _).mpr ((MiiF.holds_eqv _ _ _ _ _ _).mp hy).1)

theorem Mii_not_Hae : ¬ MiiF.Valid Hae := fun h => by
  have h0 := (MiiF.holds_all _ _ _ _).mp ((MiiF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  have e := ((MiiF.holds_eqv _ _ _ _ _ _).mp h0).1
  exact Code.arr_ne_left (Code.e : Code Empty) .t e.symm

/-- Every instance of LL≡-Poly, parameters allowed: identified items are the same item of the same type. -/
theorem Mii_LLPoly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : MiiF.Valid (LLPoly P) := by
  intro ρ env
  refine (MiiF.holds_tall _ _ _).mpr fun a => (MiiF.holds_tall _ _ _).mpr fun b => ?_
  refine (MiiF.holds_all _ _ _ _).mpr fun x => (MiiF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MiiF.holds_imp _ _ _ _).mpr fun hxy => (MiiF.holds_imp _ _ _ _).mpr fun hPx => ?_
  obtain ⟨hab, hxy'⟩ := (MiiF.holds_eqv _ _ _ _ _ _).mp hxy
  have hab' : a = b := hab
  subst hab'
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (hxy'.trans (cast_heq _ _)))
  subst e
  exact hPx

/-! ## Congruence and extensionality -/

theorem Mii_Cong : MiiF.Valid Cong := by
  intro ρ env
  refine (MiiF.holds_tall _ _ _).mpr fun a => (MiiF.holds_tall _ _ _).mpr fun b =>
    (MiiF.holds_tall _ _ _).mpr fun c => (MiiF.holds_tall _ _ _).mpr fun d => ?_
  refine (MiiF.holds_all _ _ _ _).mpr fun f => (MiiF.holds_all _ _ _ _).mpr fun g =>
    (MiiF.holds_all _ _ _ _).mpr fun x => (MiiF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MiiF.holds_imp _ _ _ _).mpr fun h => ?_
  have hc := (MiiF.holds_conj _ _ _ _).mp h
  obtain ⟨e1, hfg⟩ := (MiiF.holds_eqv _ _ _ _ _ _).mp hc.1
  obtain ⟨_, hxy⟩ := (MiiF.holds_eqv _ _ _ _ _ _).mp hc.2
  have e1' : (Code.arr a c : Code Empty) = Code.arr b d := e1
  injection e1' with ea ec
  subst ea; subst ec
  have ef : f = g := eq_of_heq ((cast_heq _ _).symm.trans (hfg.trans (cast_heq _ _)))
  have ex : x = y := eq_of_heq ((cast_heq _ _).symm.trans (hxy.trans (cast_heq _ _)))
  subst ef; subst ex
  exact (MiiF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩

theorem Mii_PCong : MiiF.Valid PCong := by
  intro ρ env
  refine (MiiF.holds_tall _ _ _).mpr fun a => (MiiF.holds_tall _ _ _).mpr fun c =>
    (MiiF.holds_tall _ _ _).mpr fun d => ?_
  refine (MiiF.holds_all _ _ _ _).mpr fun f => (MiiF.holds_all _ _ _ _).mpr fun g =>
    (MiiF.holds_all _ _ _ _).mpr fun _ => ?_
  refine (MiiF.holds_imp _ _ _ _).mpr fun h => ?_
  obtain ⟨e1, hfg⟩ := (MiiF.holds_eqv _ _ _ _ _ _).mp h
  have e1' : (Code.arr a c : Code Empty) = Code.arr a d := e1
  injection e1' with _ ec
  subst ec
  have ef : f = g := eq_of_heq ((cast_heq _ _).symm.trans (hfg.trans (cast_heq _ _)))
  subst ef
  exact (MiiF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩

theorem Mii_PExt : MiiF.Valid PExt := by
  intro ρ env
  refine (MiiF.holds_tall _ _ _).mpr fun a => (MiiF.holds_tall _ _ _).mpr fun c =>
    (MiiF.holds_tall _ _ _).mpr fun d => ?_
  refine (MiiF.holds_all _ _ _ _).mpr fun f => (MiiF.holds_all _ _ _ _).mpr fun g => ?_
  refine (MiiF.holds_imp _ _ _ _).mpr fun h => ?_
  have hp : ∀ x, _ := fun x => (MiiF.holds_eqv _ _ _ _ _ _).mp ((MiiF.holds_all _ _ _ _).mp h x)
  have x0 := Classical.choice (Univ.El_nonempty (U := MiiF.U) a)
  have ecd : c = d := (hp x0).1
  subst ecd
  have ef : f = g := funext fun x => eq_of_heq ((cast_heq _ _).symm.trans ((hp x).2.trans (cast_heq _ _)))
  subst ef
  exact (MiiF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩

/-! ## Identity of types -/

theorem Mii_Inj : MiiF.Valid Inj := by
  intro ρ env
  refine (MiiF.holds_tall _ _ _).mpr fun a => (MiiF.holds_tall _ _ _).mpr fun b => ?_
  refine (MiiF.holds_tall _ _ _).mpr fun c => (MiiF.holds_tall _ _ _).mpr fun d => ?_
  refine (MiiF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (MiiF.holds_teq _ _ _ _).mp h
  injection h' with hab hcd
  exact (MiiF.holds_conj _ _ _ _).mpr ⟨(MiiF.holds_teq _ _ _ _).mpr hab, (MiiF.holds_teq _ _ _ _).mpr hcd⟩

theorem Mii_Recovery : MiiF.Valid Recovery := by
  intro ρ env
  refine (MiiF.holds_tall _ _ _).mpr fun a => (MiiF.holds_tall _ _ _).mpr fun b => ?_
  refine (MiiF.holds_tall _ _ _).mpr fun c => (MiiF.holds_tall _ _ _).mpr fun d => ?_
  refine (MiiF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (MiiF.holds_teq _ _ _ _).mp ((MiiF.holds_conj _ _ _ _).mp h).1
  exact (MiiF.holds_teq _ _ _ _).mpr (Code.arr.inj h').2

theorem Mii_ExtT : MiiF.Valid ExtT := by
  intro ρ env
  refine (MiiF.holds_tall _ _ _).mpr fun a => (MiiF.holds_tall _ _ _).mpr fun _ => ?_
  refine (MiiF.holds_imp _ _ _ _).mpr fun h => (MiiF.holds_teq _ _ _ _).mpr ?_
  have hs := ((MiiF.holds_conj _ _ _ _).mp h).1
  have x0 := Classical.choice (Univ.El_nonempty (U := MiiF.U) a)
  obtain ⟨_, hy⟩ := (MiiF.holds_ex _ _ _ _).mp ((MiiF.holds_all _ _ _ _).mp hs x0)
  exact ((MiiF.holds_eqv _ _ _ _ _ _).mp hy).1

/-- Int≈ holds vacuously: `□(α ⊑ β)` is never true, since `α ⊑ β` is a quantification. -/
theorem Mii_IntT : MiiF.Valid IntT := by
  intro ρ env
  refine (MiiF.holds_tall _ _ _).mpr fun _ => (MiiF.holds_tall _ _ _).mpr fun _ => ?_
  exact (MiiF.holds_imp _ _ _ _).mpr fun h =>
    absurd ((MiiF.holds_conj _ _ _ _).mp h).1 (Mii_not_box_of_snd _ _ _ (Mii_snd_all _ _ _ _))

/-! ## Necessity of identity and distinctness -/

theorem Mii_NITeq : MiiF.Valid NITeq := by
  intro ρ env
  refine (MiiF.holds_tall _ _ _).mpr fun _ => (MiiF.holds_tall _ _ _).mpr fun _ => ?_
  exact (MiiF.holds_imp _ _ _ _).mpr fun h =>
    (Mii_holds_box _ _ _).mpr (Mii_eq_top h
      (congrArg Prod.snd (MiiF.eval_teq (Γ := Ctx.nil.text.text) tv1 tv0 _ env)))

theorem Mii_NDTeq : MiiF.Valid NDTeq := by
  intro ρ env
  refine (MiiF.holds_tall _ _ _).mpr fun _ => (MiiF.holds_tall _ _ _).mpr fun _ => ?_
  exact (MiiF.holds_imp _ _ _ _).mpr fun h => (Mii_holds_box _ _ _).mpr (Mii_eq_top h rfl)

theorem Mii_NDX : MiiF.Valid NDX := by
  intro ρ env
  refine (MiiF.holds_tall _ _ _).mpr fun _ => (MiiF.holds_tall _ _ _).mpr fun _ => ?_
  refine (MiiF.holds_all _ _ _ _).mpr fun _ => (MiiF.holds_all _ _ _ _).mpr fun _ => ?_
  exact (MiiF.holds_imp _ _ _ _).mpr fun h => (Mii_holds_box _ _ _).mpr (Mii_eq_top h rfl)

/-! ## Barcan formulas, Type Necessitism, Necessitism -/

theorem Mii_not_TBF : ¬ ∀ χ, TBFSch χ → MiiF.Valid χ := fun h => by
  have h0 := h (TBFI (topF : Fm Ctx.nil.text)) ⟨_, rfl⟩ (fun i => i.elim0) ()
  have h1 := (MiiF.holds_imp _ _ _ _).mp h0
    ((MiiF.holds_tall _ _ _).mpr fun _ => (Mii_holds_box _ _ _).mpr (Mii_topF _ _))
  exact Mii_not_box_of_snd _ _ _ (by exact rfl) h1

theorem Mii_TCBF : ∀ χ, TCBFSch χ → MiiF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  exact (MiiF.holds_imp _ _ _ _).mpr fun h => absurd h (Mii_not_box_of_snd _ ρ env rfl)

theorem Mii_not_TNec : ¬ MiiF.Valid TNec := fun h =>
  Mii_not_box_of_snd _ _ _ (by exact rfl) ((MiiF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)

theorem Mii_not_BF : ¬ MiiF.Valid BF := fun h => by
  have h0 := (MiiF.holds_all _ _ _ _).mp ((MiiF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ => (True, true))
  have h1 := (MiiF.holds_imp _ _ _ _).mp h0 ((MiiF.holds_all _ _ _ _).mpr fun _ => (Mii_holds_box _ _ _).mpr rfl)
  exact Mii_not_box_of_snd _ _ _ (Mii_snd_all _ _ _ _) h1

theorem Mii_CBF : MiiF.Valid CBF := by
  intro ρ env
  refine (MiiF.holds_tall _ _ _).mpr fun _ => (MiiF.holds_all _ _ _ _).mpr fun _ => ?_
  exact (MiiF.holds_imp _ _ _ _).mpr fun h => absurd h (Mii_not_box_of_snd _ _ _ (Mii_snd_all _ _ _ _))

theorem Mii_not_Nec : ¬ MiiF.Valid Nec := fun h =>
  Mii_not_box_of_snd _ _ _ (Mii_snd_ex _ _ _ _)
    ((MiiF.holds_all _ _ _ _).mp ((MiiF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ())

end Al
end PIF
