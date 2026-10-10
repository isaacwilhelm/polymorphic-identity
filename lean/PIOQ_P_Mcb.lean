import PIBF
set_option autoImplicit false

/-!
# Open questions: the profile of `𝔐_cb`

`𝔐_cb` (`lean/PIBarcanModels.lean`, `MbF`): propositions are truth values with a tag; the values
of `≈` have tag `false`, the values of `≡`, of the connectives and of the quantifiers tag `true`.
`E = 1`, and identity is identity.

So `□φ` (that is, `φ ≡ ⊤`) holds just in case `φ` is true with tag `true`. Every compound formula
other than a type identity has tag `true`; so the necessity of identity and of distinctness hold,
but not that of type identity, and a proposition `(True, false)` (a value of a variable) refutes
Booleanism and CBF.
-/

namespace PIF
namespace Al
open Tm

/-! ## Basic facts -/

/-- `□φ` holds just in case `φ` has the value of `⊤`. -/
theorem Mcb_holds_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MbF.U.TEnv n) (env : MbF.U.Env Γ ρ) :
    MbF.Holds (boxF φ) ρ env ↔ MbF.eval φ ρ env = (True, true) :=
  (MbF.holds_eqv_t _ _ _ _).trans
    ⟨fun h => (eq_of_heq h.2).trans (Mb_top ρ env), fun h => ⟨rfl, heq_of_eq (h.trans (Mb_top ρ env).symm)⟩⟩

theorem Mcb_holds_of_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MbF.U.TEnv n) (env : MbF.U.Env Γ ρ)
    (h : MbF.Holds (boxF φ) ρ env) : MbF.Holds φ ρ env :=
  cast (congrArg Prod.fst ((Mcb_holds_box φ ρ env).mp h)).symm trivial

/-- For a formula whose value has tag `true`, `□φ` holds just in case `φ` does. -/
theorem Mcb_box_of_tag {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MbF.U.TEnv n) (env : MbF.U.Env Γ ρ)
    (ht : (MbF.eval φ ρ env).2 = true) : MbF.Holds (boxF φ) ρ env ↔ MbF.Holds φ ρ env :=
  ⟨Mcb_holds_of_box φ ρ env, fun h => (Mcb_holds_box φ ρ env).mpr (Prod.ext (propext (iff_true_intro h)) ht)⟩

theorem Mcb_tag_eqv {n : Nat} {Γ : Ctx n} (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1) (ρ : MbF.U.TEnv n)
    (env : MbF.U.Env Γ ρ) : (MbF.eval (Tm.eqv σ τ x y) ρ env).2 = true :=
  congrArg Prod.snd (MbF.eval_eqv σ τ x y ρ env)

theorem Mcb_tag_neg {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MbF.U.TEnv n) (env : MbF.U.Env Γ ρ) :
    (MbF.eval (Tm.neg φ) ρ env).2 = true := rfl

theorem Mcb_tag_all {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MbF.U.TEnv n)
    (env : MbF.U.Env Γ ρ) : (MbF.eval (Tm.all σ φ) ρ env).2 = true :=
  congrArg Prod.snd (MbF.eval_all σ φ ρ env)

theorem Mcb_cast_ex_eq {c : Code Empty} {A' : Type} (hA : MbF.U.El c = A')
    (h : ((MbF.U.El c → MbF.U.P) → MbF.U.P) = ((A' → MbF.U.P) → MbF.U.P)) (Q : A' → MbF.U.P) :
    cast h (fun R => MbF.ex c R) Q = MbF.ex c (fun x => Q (cast hA x)) := by
  subst hA; rfl

theorem Mcb_tag_ex {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MbF.U.TEnv n)
    (env : MbF.U.Env Γ ρ) : (MbF.eval (Tm.ex σ φ) ρ env).2 = true :=
  congrArg Prod.snd (Mcb_cast_ex_eq (Univ.El_code ρ σ.2) _ _)

/-! ## Identity across types -/

theorem Mcb_Disjoint : MbF.Valid Disjoint := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => (MbF.holds_tall _ _ _).mpr fun b => ?_
  refine (MbF.holds_imp _ _ _ _).mpr fun hn => ?_
  refine (MbF.holds_all _ _ _ _).mpr fun x => (MbF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MbF.holds_neg _ _ _).mpr fun hxy => ?_
  exact (MbF.holds_neg _ _ _).mp hn ((MbF.holds_teq _ _ _ _).mpr ((MbF.holds_eqv _ _ _ _ _ _).mp hxy).1)

theorem Mcb_Slogan : MbF.Valid Slogan := by
  intro ρ env
  refine (MbF.holds_all _ _ _ _).mpr fun x => (MbF.holds_tall _ _ _).mpr fun b => ?_
  refine (MbF.holds_all _ _ _ _).mpr fun y => (MbF.holds_neg _ _ _).mpr fun hxy => ?_
  have h := ((MbF.holds_eqv _ _ _ _ _ _).mp hxy).1
  exact nomatch (show (Code.e : Code Empty) = .arr b .t from h)

theorem Mcb_not_Twin : ¬ MbF.Valid Twin := fun h => by
  have h0 := (MbF.holds_all _ _ _ _).mp ((MbF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  obtain ⟨b, hb⟩ := (MbF.holds_tex _ _ _).mp h0
  have hc := (MbF.holds_conj _ _ _ _).mp hb
  obtain ⟨_, hy⟩ := (MbF.holds_ex _ _ _ _).mp hc.2
  have e := ((MbF.holds_eqv _ _ _ _ _ _).mp hy).1
  exact (MbF.holds_neg _ _ _).mp hc.1 ((MbF.holds_teq _ _ _ _).mpr e)

theorem Mcb_not_Hae : ¬ MbF.Valid Hae := fun h => by
  have h0 := (MbF.holds_all _ _ _ _).mp ((MbF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  have e := ((MbF.holds_eqv _ _ _ _ _ _).mp h0).1
  exact Code.arr_ne_left (Code.e : Code Empty) .t e.symm

theorem Mcb_LLPoly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : MbF.Valid (LLPoly P) := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => (MbF.holds_tall _ _ _).mpr fun b => ?_
  refine (MbF.holds_all _ _ _ _).mpr fun x => (MbF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MbF.holds_imp _ _ _ _).mpr fun hxy => (MbF.holds_imp _ _ _ _).mpr fun hPx => ?_
  obtain ⟨hab, hxy'⟩ := (MbF.holds_eqv _ _ _ _ _ _).mp hxy
  have hG : HEq (MbF.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y)) (MbF.eval P ρ env) :=
    (heq_of_eq ((MbF.eval_wk _ _ _ _ _).trans (MbF.eval_wk _ _ _ _ _))).trans
      ((MbF.eval_twk P.twk b (scons a ρ) env).trans (MbF.eval_twk P a ρ env))
  have h1 : MbF.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (scons b (scons a ρ)) ((env, x), y) =
      MbF.eval P ρ env a :=
    eq_of_heq ((MbF.heq_eval_tapp (K := Cat.arr (Cat.var fz) Cat.t) ((P.twk.twk.wk tv1).wk tv0) tv1
      (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => MbF.U.El c → MbF.U.P) (Q := fun c => MbF.U.El c → MbF.U.P) (fun _ => rfl) hG rfl))
  have h0 : MbF.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (scons b (scons a ρ)) ((env, x), y) =
      MbF.eval P ρ env b :=
    eq_of_heq ((MbF.heq_eval_tapp (K := Cat.arr (Cat.var fz) Cat.t) ((P.twk.twk.wk tv1).wk tv0) tv0
      (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => MbF.U.El c → MbF.U.P) (Q := fun c => MbF.U.El c → MbF.U.P) (fun _ => rfl) hG rfl))
  show MbF.U.V (MbF.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (scons b (scons a ρ)) ((env, x), y) y)
  have hPx' : MbF.U.V (MbF.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (scons b (scons a ρ)) ((env, x), y) x) :=
    hPx
  rw [h1] at hPx'
  rw [h0]
  have hab' : a = b := hab
  subst hab'
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (hxy'.trans (cast_heq _ _)))
  exact e ▸ hPx'

/-! ## Identity of types -/

theorem Mcb_Inj : MbF.Valid Inj := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => (MbF.holds_tall _ _ _).mpr fun b => ?_
  refine (MbF.holds_tall _ _ _).mpr fun c => (MbF.holds_tall _ _ _).mpr fun d => ?_
  refine (MbF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (MbF.holds_teq _ _ _ _).mp h
  injection h' with hab hcd
  exact (MbF.holds_conj _ _ _ _).mpr ⟨(MbF.holds_teq _ _ _ _).mpr hab, (MbF.holds_teq _ _ _ _).mpr hcd⟩

theorem Mcb_Recovery : MbF.Valid Recovery := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => (MbF.holds_tall _ _ _).mpr fun b => ?_
  refine (MbF.holds_tall _ _ _).mpr fun c => (MbF.holds_tall _ _ _).mpr fun d => ?_
  refine (MbF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (MbF.holds_teq _ _ _ _).mp ((MbF.holds_conj _ _ _ _).mp h).1
  exact (MbF.holds_teq _ _ _ _).mpr (Code.arr.inj h').2

theorem Mcb_ExtT : MbF.Valid ExtT := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => (MbF.holds_tall _ _ _).mpr fun b => ?_
  refine (MbF.holds_imp _ _ _ _).mpr fun h => (MbF.holds_teq _ _ _ _).mpr ?_
  have hs := ((MbF.holds_conj _ _ _ _).mp h).1
  have x0 := Classical.choice (Univ.El_nonempty (U := MbF.U) a)
  obtain ⟨_, hy⟩ := (MbF.holds_ex _ _ _ _).mp ((MbF.holds_all _ _ _ _).mp hs x0)
  exact ((MbF.holds_eqv _ _ _ _ _ _).mp hy).1

theorem Mcb_IntT : MbF.Valid IntT := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => (MbF.holds_tall _ _ _).mpr fun b => ?_
  refine (MbF.holds_imp _ _ _ _).mpr fun h => (MbF.holds_teq _ _ _ _).mpr ?_
  have hs := Mcb_holds_of_box _ _ _ ((MbF.holds_conj _ _ _ _).mp h).1
  have x0 := Classical.choice (Univ.El_nonempty (U := MbF.U) a)
  obtain ⟨_, hy⟩ := (MbF.holds_ex _ _ _ _).mp ((MbF.holds_all _ _ _ _).mp hs x0)
  exact ((MbF.holds_eqv _ _ _ _ _ _).mp hy).1

/-! ## Congruence and extensionality -/

theorem Mcb_Cong : MbF.Valid Cong := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => (MbF.holds_tall _ _ _).mpr fun b =>
    (MbF.holds_tall _ _ _).mpr fun c => (MbF.holds_tall _ _ _).mpr fun d => ?_
  refine (MbF.holds_all _ _ _ _).mpr fun f => (MbF.holds_all _ _ _ _).mpr fun g =>
    (MbF.holds_all _ _ _ _).mpr fun x => (MbF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MbF.holds_imp _ _ _ _).mpr fun h => ?_
  have hc := (MbF.holds_conj _ _ _ _).mp h
  obtain ⟨e1, hfg⟩ := (MbF.holds_eqv _ _ _ _ _ _).mp hc.1
  obtain ⟨_, hxy⟩ := (MbF.holds_eqv _ _ _ _ _ _).mp hc.2
  have e1' : (Code.arr a c : Code Empty) = Code.arr b d := e1
  injection e1' with ea ec
  subst ea; subst ec
  have ef : f = g := eq_of_heq ((cast_heq _ _).symm.trans (hfg.trans (cast_heq _ _)))
  have ex : x = y := eq_of_heq ((cast_heq _ _).symm.trans (hxy.trans (cast_heq _ _)))
  subst ef; subst ex
  exact (MbF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩

theorem Mcb_PCong : MbF.Valid PCong := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => (MbF.holds_tall _ _ _).mpr fun c =>
    (MbF.holds_tall _ _ _).mpr fun d => ?_
  refine (MbF.holds_all _ _ _ _).mpr fun f => (MbF.holds_all _ _ _ _).mpr fun g =>
    (MbF.holds_all _ _ _ _).mpr fun x => ?_
  refine (MbF.holds_imp _ _ _ _).mpr fun h => ?_
  obtain ⟨e1, hfg⟩ := (MbF.holds_eqv _ _ _ _ _ _).mp h
  have e1' : (Code.arr a c : Code Empty) = Code.arr a d := e1
  injection e1' with _ ec
  subst ec
  have ef : f = g := eq_of_heq ((cast_heq _ _).symm.trans (hfg.trans (cast_heq _ _)))
  subst ef
  exact (MbF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩

theorem Mcb_PExt : MbF.Valid PExt := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => (MbF.holds_tall _ _ _).mpr fun c =>
    (MbF.holds_tall _ _ _).mpr fun d => ?_
  refine (MbF.holds_all _ _ _ _).mpr fun f => (MbF.holds_all _ _ _ _).mpr fun g => ?_
  refine (MbF.holds_imp _ _ _ _).mpr fun h => ?_
  have hp : ∀ x, _ := fun x => (MbF.holds_eqv _ _ _ _ _ _).mp ((MbF.holds_all _ _ _ _).mp h x)
  have x0 := Classical.choice (Univ.El_nonempty (U := MbF.U) a)
  have ecd : c = d := (hp x0).1
  subst ecd
  have ef : f = g := funext fun x => eq_of_heq ((cast_heq _ _).symm.trans ((hp x).2.trans (cast_heq _ _)))
  subst ef
  exact (MbF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩

/-! ## Modal principles -/

theorem Mcb_NIEqv : MbF.Valid NIEqv := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => ?_
  refine (MbF.holds_all _ _ _ _).mpr fun x => (MbF.holds_all _ _ _ _).mpr fun y => ?_
  exact (MbF.holds_imp _ _ _ _).mpr fun hxy => (Mcb_box_of_tag _ _ _ (Mcb_tag_eqv _ _ _ _ _ _)).mpr hxy

theorem Mcb_not_NITeq : ¬ MbF.Valid NITeq := fun h => by
  have h0 := (MbF.holds_tall _ _ _).mp ((MbF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e
  have h1 := (Mcb_holds_box _ _ _).mp ((MbF.holds_imp _ _ _ _).mp h0 ((MbF.holds_teq _ _ _ _).mpr rfl))
  exact Bool.noConfusion (congrArg Prod.snd ((MbF.eval_teq _ _ _ _).symm.trans h1) : false = true)

theorem Mcb_NDTeq : MbF.Valid NDTeq := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => (MbF.holds_tall _ _ _).mpr fun b => ?_
  exact (MbF.holds_imp _ _ _ _).mpr fun h => (Mcb_box_of_tag _ _ _ (Mcb_tag_neg _ _ _)).mpr h

theorem Mcb_NIX : MbF.Valid NIX := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => (MbF.holds_tall _ _ _).mpr fun b => ?_
  refine (MbF.holds_all _ _ _ _).mpr fun x => (MbF.holds_all _ _ _ _).mpr fun y => ?_
  exact (MbF.holds_imp _ _ _ _).mpr fun h => (Mcb_box_of_tag _ _ _ (Mcb_tag_eqv _ _ _ _ _ _)).mpr h

theorem Mcb_NDX : MbF.Valid NDX := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => (MbF.holds_tall _ _ _).mpr fun b => ?_
  refine (MbF.holds_all _ _ _ _).mpr fun x => (MbF.holds_all _ _ _ _).mpr fun y => ?_
  exact (MbF.holds_imp _ _ _ _).mpr fun h => (Mcb_box_of_tag _ _ _ (Mcb_tag_neg _ _ _)).mpr h

theorem Mcb_IdId : MbF.Valid IdId := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => ?_
  refine (MbF.holds_all _ _ _ _).mpr fun x => (MbF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MbF.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine (MbF.eval_eqv _ _ _ _ _ _).trans (Eq.trans ?_ (MbF.eval_all _ _ _ _).symm)
  refine Prod.ext (propext ⟨fun h G hG => ?_, fun h => ?_⟩) rfl
  · have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.2.trans (cast_heq _ _)))
    subst e; exact hG
  · have hy : HEq y x := h (fun z => (HEq z x, true)) (by exact HEq.rfl)
    exact ⟨rfl, (cast_heq _ _).trans (hy.symm.trans (cast_heq _ _).symm)⟩

theorem Mcb_not_DNeg : ¬ MbF.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MbF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (True, false)
  have e := eq_of_heq ((MbF.holds_eqv_t _ _ _ _).mp h0).2
  exact Bool.noConfusion (congrArg Prod.snd e : true = false)

theorem Mcb_not_Bool : ¬ ∀ φ, BoolSch φ → MbF.Valid φ := fun h => Mcb_not_DNeg (h _ DNeg_bool)

theorem Mcb_BF : MbF.Valid BF := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => (MbF.holds_all _ _ _ _).mpr fun F => ?_
  refine (MbF.holds_imp _ _ _ _).mpr fun h => (Mcb_box_of_tag _ _ _ (Mcb_tag_all _ _ _ _)).mpr ?_
  exact (MbF.holds_all _ _ _ _).mpr fun x => Mcb_holds_of_box _ _ _ ((MbF.holds_all _ _ _ _).mp h x)

theorem Mcb_not_CBF : ¬ MbF.Valid CBF := fun h => by
  have h0 := (MbF.holds_all _ _ _ _).mp ((MbF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ => (True, false))
  have h1 := (MbF.holds_imp _ _ _ _).mp h0 ((Mcb_box_of_tag _ _ _ (Mcb_tag_all _ _ _ _)).mpr
    ((MbF.holds_all _ _ _ _).mpr fun _ => trivial))
  have h2 := (Mcb_holds_box _ _ _).mp ((MbF.holds_all _ _ _ _).mp h1 ())
  exact Bool.noConfusion (congrArg Prod.snd h2 : false = true)

theorem Mcb_Nec : MbF.Valid Nec := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => (MbF.holds_all _ _ _ _).mpr fun x => ?_
  refine (Mcb_box_of_tag _ _ _ (Mcb_tag_ex _ _ _ _)).mpr ((MbF.holds_ex _ _ _ _).mpr ⟨x, ?_⟩)
  exact (MbF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩

end Al
end PIF
