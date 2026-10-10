import PIBF
set_option autoImplicit false

/-!
# Open questions: `𝔐_cl` and its variant `𝔐_cl,I`

`𝔐_cl` (defined in `PIAlgModels`) has propositions `Option Bool`, with `none` the one truth;
identity is identity, the connectives take values `mkA`, the quantifiers values `qA`. Since there
is exactly one true proposition and identity is identity, `□φ` (that is, `φ ≡ ⊤`) holds just in
case `φ` does; and since identity is rigid, coextensive types are the same type.

`𝔐_cl,I` is exactly `𝔐_cl` except that the quantifiers also take values `mkA`: so every false
compound proposition is `some true`, and only a propositional variable can take the value
`some false`. Then both sides of the Identity Identity are `mkA` of equivalent conditions, hence
equal; but `¬¬(some false) = some true ≠ some false`, so Booleanism fails, and `some true` and
`some false` are both false but distinct, so PropExt fails.
-/

namespace PIF
namespace Al

/-! ## `𝔐_cl` -/

theorem Mcl_Disjoint : MclF.Valid Disjoint := by
  intro ρ env
  refine (MclF.holds_tall _ _ _).mpr fun a => (MclF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclF.holds_imp _ _ _ _).mpr fun hn => ?_
  refine (MclF.holds_all _ _ _ _).mpr fun x => (MclF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MclF.holds_neg _ _ _).mpr fun hxy => ?_
  exact (MclF.holds_neg _ _ _).mp hn ((MclF.holds_teq _ _ _ _).mpr
    ((mkA_V _).mpr ((mkA_V _).mp ((MclF.holds_eqv _ _ _ _ _ _).mp hxy)).1))

theorem Mcl_Slogan : MclF.Valid Slogan := by
  intro ρ env
  refine (MclF.holds_all _ _ _ _).mpr fun x => (MclF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclF.holds_all _ _ _ _).mpr fun y => (MclF.holds_neg _ _ _).mpr fun hxy => ?_
  have h := ((mkA_V _).mp ((MclF.holds_eqv _ _ _ _ _ _).mp hxy)).1
  exact nomatch (show (Code.e : Code Empty) = .arr b .t from h)

theorem Mcl_Inj : MclF.Valid Inj := by
  intro ρ env
  refine (MclF.holds_tall _ _ _).mpr fun a => (MclF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclF.holds_tall _ _ _).mpr fun c => (MclF.holds_tall _ _ _).mpr fun d => ?_
  refine (MclF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (mkA_V _).mp ((MclF.holds_teq _ _ _ _).mp h)
  injection h' with hab hcd
  exact (MclF.holds_conj _ _ _ _).mpr ⟨(MclF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr hab),
    (MclF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr hcd)⟩

theorem Mcl_Recovery : MclF.Valid Recovery := by
  intro ρ env
  refine (MclF.holds_tall _ _ _).mpr fun a => (MclF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclF.holds_tall _ _ _).mpr fun c => (MclF.holds_tall _ _ _).mpr fun d => ?_
  refine (MclF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d :=
    (mkA_V _).mp ((MclF.holds_teq _ _ _ _).mp ((MclF.holds_conj _ _ _ _).mp h).1)
  injection h' with _ hcd
  exact (MclF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr hcd)

theorem Mcl_ExtT : MclF.Valid ExtT := by
  intro ρ env
  refine (MclF.holds_tall _ _ _).mpr fun a => (MclF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclF.holds_imp _ _ _ _).mpr fun h => (MclF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr ?_)
  have hs := ((MclF.holds_conj _ _ _ _).mp h).1
  have x0 := Classical.choice (Univ.El_nonempty (U := MclF.U) a)
  obtain ⟨_, hy⟩ := (MclF.holds_ex _ _ _ _).mp ((MclF.holds_all _ _ _ _).mp hs x0)
  exact ((mkA_V _).mp ((MclF.holds_eqv _ _ _ _ _ _).mp hy)).1

/-- In `𝔐_cl`, `□φ` holds just in case `φ` does. -/
private theorem Mcl_holds_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MclF.U.TEnv n) (env : MclF.U.Env Γ ρ) :
    MclF.Holds (boxF φ) ρ env ↔ MclF.Holds φ ρ env := by
  refine (MclF.holds_eqv_t _ _ _ _).trans ⟨fun h => ?_, fun h => (mkA_V _).mpr ⟨rfl, heq_of_eq ?_⟩⟩
  · exact (eq_of_heq ((mkA_V _).mp h).2).trans (Mcl_topF ρ env)
  · exact (show MclF.eval φ ρ env = none from h).trans (Mcl_topF ρ env).symm

theorem Mcl_IntT : MclF.Valid IntT := by
  intro ρ env
  refine (MclF.holds_tall _ _ _).mpr fun a => (MclF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclF.holds_imp _ _ _ _).mpr fun h => (MclF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr ?_)
  have hs := (Mcl_holds_box _ _ _).mp ((MclF.holds_conj _ _ _ _).mp h).1
  have x0 := Classical.choice (Univ.El_nonempty (U := MclF.U) a)
  obtain ⟨_, hy⟩ := (MclF.holds_ex _ _ _ _).mp ((MclF.holds_all _ _ _ _).mp hs x0)
  exact ((mkA_V _).mp ((MclF.holds_eqv _ _ _ _ _ _).mp hy)).1

theorem Mcl_NIEqv : MclF.Valid NIEqv := by
  intro ρ env
  refine (MclF.holds_tall _ _ _).mpr fun a => ?_
  refine (MclF.holds_all _ _ _ _).mpr fun x => (MclF.holds_all _ _ _ _).mpr fun y => ?_
  exact (MclF.holds_imp _ _ _ _).mpr fun hxy => (Mcl_holds_box _ _ _).mpr hxy

theorem Mcl_NITeq : MclF.Valid NITeq := by
  intro ρ env
  refine (MclF.holds_tall _ _ _).mpr fun a => (MclF.holds_tall _ _ _).mpr fun b => ?_
  exact (MclF.holds_imp _ _ _ _).mpr fun h => (Mcl_holds_box _ _ _).mpr h

/-! ## `𝔐_cl,I`: `𝔐_cl` with the quantifiers taking values `mkA` -/

/-- As `𝔐_cl`, except that the values of the quantifiers are given by `mkA`, so that every false
value of a connective, a quantifier, `≡` or `≈` is `some true`. -/
noncomputable def MclIF : Frame where
  U := univA
  eqv := fun a b x y => mkA (a = b ∧ HEq x y)
  teq := fun a b => mkA (a = b)
  neg := fun p => mkA (¬ p = none)
  imp := fun p q => mkA (p = none → q = none)
  cnj := fun p q => mkA (p = none ∧ q = none)
  dsj := fun p q => mkA (p = none ∨ q = none)
  bic := fun p q => mkA (p = none ↔ q = none)
  all := fun _ f => mkA (∀ x, f x = none)
  ex := fun _ f => mkA (∃ x, f x = none)
  tall := fun Q => mkA (∀ a, Q a = none)
  tex := fun Q => mkA (∃ a, Q a = none)
  hneg := fun _ => mkA_V _
  himp := fun _ _ => mkA_V _
  hcnj := fun _ _ => mkA_V _
  hdsj := fun _ _ => mkA_V _
  hbic := fun _ _ => mkA_V _
  hall := fun _ _ => mkA_V _
  hex := fun _ _ => mkA_V _
  htall := fun _ => mkA_V _
  htex := fun _ => mkA_V _

theorem MclI_model : MclIF.IsModelPIm :=
  MclIF.model_of_equiv (fun _ _ => mkA_V _) (fun _ _ => (mkA_V _).mpr ⟨rfl, HEq.rfl⟩)
    (fun _ _ _ _ h => (mkA_V _).mpr (((mkA_V _).mp h).elim fun e h' => ⟨e.symm, h'.symm⟩))
    (fun _ _ _ _ _ _ h1 h2 => (mkA_V _).mpr (((mkA_V _).mp h1).elim fun e1 h1' =>
      ((mkA_V _).mp h2).elim fun e2 h2' => ⟨e1.trans e2, h1'.trans h2'⟩))

theorem MclI_topF {n : Nat} {Γ : Ctx n} (ρ : MclIF.U.TEnv n) (env : MclIF.U.Env Γ ρ) :
    MclIF.eval (topF : Fm Γ) ρ env = none :=
  MclIF.holds_topF ρ env ⟨some true, fun h => nomatch (h : (some true : Option Bool) = none)⟩

/-- In `𝔐_cl,I`, `□φ` holds just in case `φ` does. -/
theorem MclI_holds_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MclIF.U.TEnv n) (env : MclIF.U.Env Γ ρ) :
    MclIF.Holds (boxF φ) ρ env ↔ MclIF.Holds φ ρ env := by
  refine (MclIF.holds_eqv_t _ _ _ _).trans ⟨fun h => ?_, fun h => (mkA_V _).mpr ⟨rfl, heq_of_eq ?_⟩⟩
  · exact (eq_of_heq ((mkA_V _).mp h).2).trans (MclI_topF ρ env)
  · exact (show MclIF.eval φ ρ env = none from h).trans (MclI_topF ρ env).symm

theorem MclI_LLEqv : MclIF.Valid LLEqv := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => ?_
  refine (MclIF.holds_all _ _ _ _).mpr fun x => (MclIF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MclIF.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (MclIF.holds_all _ _ _ _).mpr fun G => (MclIF.holds_imp _ _ _ _).mpr fun hGx => ?_
  have h := ((mkA_V _).mp ((MclIF.holds_eqv _ _ _ _ _ _).mp hxy)).2
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.trans (cast_heq _ _)))
  subst e
  exact hGx

theorem MclI_Collapse : MclIF.Valid Collapse := by
  intro ρ env
  refine (MclIF.holds_all _ _ _ _).mpr fun p => (MclIF.holds_imp _ _ _ _).mpr fun hp => ?_
  exact (MclI_holds_box _ _ _).mpr hp

theorem MclI_not_PropExt : ¬ MclIF.Valid PropExt := fun h => by
  have h0 := (MclIF.holds_all _ _ _ _).mp ((MclIF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (some true))
    (some false)
  have h1 := (MclIF.holds_imp _ _ _ _).mp h0 ((MclIF.holds_iff _ _ _ _).mpr
    (Iff.intro (fun (h : (some true : Option Bool) = none) => nomatch h)
      (fun (h : (some false : Option Bool) = none) => nomatch h)))
  have e := (mkA_V _).mp ((MclIF.holds_eqv_t _ _ _ _).mp h1)
  have e2 : (some true : Option Bool) = some false := eq_of_heq e.2
  cases e2

theorem MclI_IdId : MclIF.Valid IdId := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => ?_
  refine (MclIF.holds_all _ _ _ _).mpr fun x => (MclIF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MclIF.holds_eqv_t _ _ _ _).mpr ((mkA_V _).mpr ⟨rfl, heq_of_eq ?_⟩)
  refine (MclIF.eval_eqv _ _ _ _ _ _).trans (Eq.trans ?_ (MclIF.eval_all
    (Γ := ((Ctx.nil.text).ext tv0).ext tv0) tv0.pred
    (Tm.imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))
    (scons a ρ) ((env, x), y)).symm)
  refine congrArg mkA (propext ⟨fun h G => ?_, fun h => ?_⟩)
  · have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.2.trans (cast_heq _ _)))
    subst e
    exact (mkA_V _).mpr id
  · have hG := (mkA_V _).mp (h (fun z => mkA (HEq z x))) (mkA_pos HEq.rfl)
    have hy : HEq y x := (mkA_V _).mp hG
    exact ⟨rfl, (cast_heq _ _).trans (hy.symm.trans (cast_heq _ _).symm)⟩

theorem MclI_not_DNeg : ¬ MclIF.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MclIF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (some false)
  have e := eq_of_heq ((mkA_V _).mp ((MclIF.holds_eqv_t _ _ _ _).mp h0)).2
  have e1 : MclIF.neg (some false) = none := mkA_pos (fun h => nomatch (h : (some false : Option Bool) = none))
  have e2 : MclIF.neg none = some true := mkA_neg (fun h => h rfl)
  have e3 : MclIF.eval (Tm.neg (Tm.neg (.var .here)) : Fm (Ctx.nil.ext tyT)) (fun i => i.elim0) ((), some false) = some true := by
    show MclIF.neg (MclIF.neg (some false)) = some true
    rw [e1, e2]
  rw [e3] at e
  exact Bool.noConfusion (Option.some.inj e)

theorem MclI_not_Bool : ¬ ∀ φ, BoolSch φ → MclIF.Valid φ := fun h => MclI_not_DNeg (h _ DNeg_bool)

theorem MclI_Disjoint : MclIF.Valid Disjoint := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclIF.holds_imp _ _ _ _).mpr fun hn => ?_
  refine (MclIF.holds_all _ _ _ _).mpr fun x => (MclIF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MclIF.holds_neg _ _ _).mpr fun hxy => ?_
  exact (MclIF.holds_neg _ _ _).mp hn ((MclIF.holds_teq _ _ _ _).mpr
    ((mkA_V _).mpr ((mkA_V _).mp ((MclIF.holds_eqv _ _ _ _ _ _).mp hxy)).1))

theorem MclI_Slogan : MclIF.Valid Slogan := by
  intro ρ env
  refine (MclIF.holds_all _ _ _ _).mpr fun x => (MclIF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclIF.holds_all _ _ _ _).mpr fun y => (MclIF.holds_neg _ _ _).mpr fun hxy => ?_
  have h := ((mkA_V _).mp ((MclIF.holds_eqv _ _ _ _ _ _).mp hxy)).1
  exact nomatch (show (Code.e : Code Empty) = .arr b .t from h)

theorem MclI_Inj : MclIF.Valid Inj := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclIF.holds_tall _ _ _).mpr fun c => (MclIF.holds_tall _ _ _).mpr fun d => ?_
  refine (MclIF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (mkA_V _).mp ((MclIF.holds_teq _ _ _ _).mp h)
  injection h' with hab hcd
  exact (MclIF.holds_conj _ _ _ _).mpr ⟨(MclIF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr hab),
    (MclIF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr hcd)⟩

theorem MclI_Recovery : MclIF.Valid Recovery := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclIF.holds_tall _ _ _).mpr fun c => (MclIF.holds_tall _ _ _).mpr fun d => ?_
  refine (MclIF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d :=
    (mkA_V _).mp ((MclIF.holds_teq _ _ _ _).mp ((MclIF.holds_conj _ _ _ _).mp h).1)
  injection h' with _ hcd
  exact (MclIF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr hcd)

theorem MclI_ExtT : MclIF.Valid ExtT := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclIF.holds_imp _ _ _ _).mpr fun h => (MclIF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr ?_)
  have hs := ((MclIF.holds_conj _ _ _ _).mp h).1
  have x0 := Classical.choice (Univ.El_nonempty (U := MclIF.U) a)
  obtain ⟨_, hy⟩ := (MclIF.holds_ex _ _ _ _).mp ((MclIF.holds_all _ _ _ _).mp hs x0)
  exact ((mkA_V _).mp ((MclIF.holds_eqv _ _ _ _ _ _).mp hy)).1

theorem MclI_IntT : MclIF.Valid IntT := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclIF.holds_imp _ _ _ _).mpr fun h => (MclIF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr ?_)
  have hs := (MclI_holds_box _ _ _).mp ((MclIF.holds_conj _ _ _ _).mp h).1
  have x0 := Classical.choice (Univ.El_nonempty (U := MclIF.U) a)
  obtain ⟨_, hy⟩ := (MclIF.holds_ex _ _ _ _).mp ((MclIF.holds_all _ _ _ _).mp hs x0)
  exact ((mkA_V _).mp ((MclIF.holds_eqv _ _ _ _ _ _).mp hy)).1

theorem MclI_NIEqv : MclIF.Valid NIEqv := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => ?_
  refine (MclIF.holds_all _ _ _ _).mpr fun x => (MclIF.holds_all _ _ _ _).mpr fun y => ?_
  exact (MclIF.holds_imp _ _ _ _).mpr fun hxy => (MclI_holds_box _ _ _).mpr hxy

theorem MclI_NITeq : MclIF.Valid NITeq := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_tall _ _ _).mpr fun b => ?_
  exact (MclIF.holds_imp _ _ _ _).mpr fun h => (MclI_holds_box _ _ _).mpr h

/-! ### Further facts about `𝔐_cl,I` -/

theorem MclI_Cong : MclIF.Valid Cong := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_tall _ _ _).mpr fun b =>
    (MclIF.holds_tall _ _ _).mpr fun c => (MclIF.holds_tall _ _ _).mpr fun d => ?_
  refine (MclIF.holds_all _ _ _ _).mpr fun f => (MclIF.holds_all _ _ _ _).mpr fun g =>
    (MclIF.holds_all _ _ _ _).mpr fun x => (MclIF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MclIF.holds_imp _ _ _ _).mpr fun h => ?_
  have hc := (MclIF.holds_conj _ _ _ _).mp h
  obtain ⟨e1, hfg⟩ := (mkA_V _).mp ((MclIF.holds_eqv _ _ _ _ _ _).mp hc.1)
  obtain ⟨_, hxy⟩ := (mkA_V _).mp ((MclIF.holds_eqv _ _ _ _ _ _).mp hc.2)
  have e1' : (Code.arr a c : Code Empty) = Code.arr b d := e1
  injection e1' with ea ec
  subst ea; subst ec
  have ef : f = g := eq_of_heq ((cast_heq _ _).symm.trans (hfg.trans (cast_heq _ _)))
  have ex : x = y := eq_of_heq ((cast_heq _ _).symm.trans (hxy.trans (cast_heq _ _)))
  subst ef; subst ex
  exact (MclIF.holds_eqv _ _ _ _ _ _).mpr ((mkA_V _).mpr ⟨rfl, HEq.rfl⟩)

theorem MclI_WCong : MclIF.Valid WCong := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_tall _ _ _).mpr fun b =>
    (MclIF.holds_tall _ _ _).mpr fun c => (MclIF.holds_tall _ _ _).mpr fun d => ?_
  refine (MclIF.holds_all _ _ _ _).mpr fun f => (MclIF.holds_all _ _ _ _).mpr fun g =>
    (MclIF.holds_all _ _ _ _).mpr fun x => (MclIF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MclIF.holds_imp _ _ _ _).mpr fun h => ?_
  have hc := (MclIF.holds_conj _ _ _ _).mp ((MclIF.holds_conj _ _ _ _).mp h).2
  obtain ⟨e1, hfg⟩ := (mkA_V _).mp ((MclIF.holds_eqv _ _ _ _ _ _).mp hc.1)
  obtain ⟨_, hxy⟩ := (mkA_V _).mp ((MclIF.holds_eqv _ _ _ _ _ _).mp hc.2)
  have e1' : (Code.arr a c : Code Empty) = Code.arr b d := e1
  injection e1' with ea ec
  subst ea; subst ec
  have ef : f = g := eq_of_heq ((cast_heq _ _).symm.trans (hfg.trans (cast_heq _ _)))
  have ex : x = y := eq_of_heq ((cast_heq _ _).symm.trans (hxy.trans (cast_heq _ _)))
  subst ef; subst ex
  exact (MclIF.holds_eqv _ _ _ _ _ _).mpr ((mkA_V _).mpr ⟨rfl, HEq.rfl⟩)

theorem MclI_PCong : MclIF.Valid PCong := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_tall _ _ _).mpr fun c =>
    (MclIF.holds_tall _ _ _).mpr fun d => ?_
  refine (MclIF.holds_all _ _ _ _).mpr fun f => (MclIF.holds_all _ _ _ _).mpr fun g =>
    (MclIF.holds_all _ _ _ _).mpr fun x => ?_
  refine (MclIF.holds_imp _ _ _ _).mpr fun h => ?_
  obtain ⟨e1, hfg⟩ := (mkA_V _).mp ((MclIF.holds_eqv _ _ _ _ _ _).mp h)
  have e1' : (Code.arr a c : Code Empty) = Code.arr a d := e1
  injection e1' with _ ec
  subst ec
  have ef : f = g := eq_of_heq ((cast_heq _ _).symm.trans (hfg.trans (cast_heq _ _)))
  subst ef
  exact (MclIF.holds_eqv _ _ _ _ _ _).mpr ((mkA_V _).mpr ⟨rfl, HEq.rfl⟩)

theorem MclI_PExt : MclIF.Valid PExt := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_tall _ _ _).mpr fun c =>
    (MclIF.holds_tall _ _ _).mpr fun d => ?_
  refine (MclIF.holds_all _ _ _ _).mpr fun f => (MclIF.holds_all _ _ _ _).mpr fun g => ?_
  refine (MclIF.holds_imp _ _ _ _).mpr fun h => ?_
  have hp : ∀ x, _ := fun x => (mkA_V _).mp ((MclIF.holds_eqv _ _ _ _ _ _).mp ((MclIF.holds_all _ _ _ _).mp h x))
  have x0 := Classical.choice (Univ.El_nonempty (U := MclIF.U) a)
  have ecd : c = d := (hp x0).1
  subst ecd
  have ef : f = g := funext fun x => eq_of_heq ((cast_heq _ _).symm.trans ((hp x).2.trans (cast_heq _ _)))
  subst ef
  exact (MclIF.holds_eqv _ _ _ _ _ _).mpr ((mkA_V _).mpr ⟨rfl, HEq.rfl⟩)

theorem MclI_Truth : MclIF.Valid Truth := by
  intro ρ env
  refine (MclIF.holds_all _ _ _ _).mpr fun p => (MclIF.holds_all _ _ _ _).mpr fun q => ?_
  refine (MclIF.holds_imp _ _ _ _).mpr fun h => (MclIF.holds_imp _ _ _ _).mpr fun hp => ?_
  have e : p = q := eq_of_heq ((mkA_V _).mp ((MclIF.holds_eqv_t _ _ _ _).mp h)).2
  subst e
  exact hp

theorem MclI_TopBot : MclIF.Valid TopBot := by
  intro ρ env
  refine (MclIF.holds_neg _ _ _).mpr fun h => ?_
  have e := eq_of_heq ((mkA_V _).mp ((MclIF.holds_eqv_t _ _ _ _).mp h)).2
  have hb : MclIF.Holds (botF : Fm Ctx.nil) ρ env := e.symm.trans (MclI_topF ρ env)
  exact nomatch ((MclIF.holds_all tyT (.var .here) ρ env).mp hb (some true) : (some true : Option Bool) = none)

theorem MclI_Cantor : MclIF.Valid Cantor := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_ex _ _ _ _).mpr ⟨fun _ => none, ?_⟩
  refine (MclIF.holds_all _ _ _ _).mpr fun y => (MclIF.holds_neg _ _ _).mpr fun h => ?_
  exact Code.arr_ne_left a .t ((mkA_V _).mp ((MclIF.holds_eqv _ _ _ _ _ _).mp h)).1

theorem MclI_not_Twin : ¬ MclIF.Valid Twin := fun h => by
  have h0 := (MclIF.holds_all _ _ _ _).mp ((MclIF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  obtain ⟨b, hb⟩ := (MclIF.holds_tex _ _ _).mp h0
  have hc := (MclIF.holds_conj _ _ _ _).mp hb
  obtain ⟨_, hy⟩ := (MclIF.holds_ex _ _ _ _).mp hc.2
  have e := ((mkA_V _).mp ((MclIF.holds_eqv _ _ _ _ _ _).mp hy)).1
  exact (MclIF.holds_neg _ _ _).mp hc.1 ((MclIF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr e))

theorem MclI_not_Hae : ¬ MclIF.Valid Hae := fun h => by
  have h0 := (MclIF.holds_all _ _ _ _).mp ((MclIF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  have e := ((mkA_V _).mp ((MclIF.holds_eqv _ _ _ _ _ _).mp h0)).1
  exact Code.arr_ne_left (Code.e : Code Empty) .t e.symm

theorem MclI_TAx : MclIF.Valid TAx := by
  intro ρ env
  exact (MclIF.holds_all _ _ _ _).mpr fun p => (MclIF.holds_imp _ _ _ _).mpr fun h => (MclI_holds_box _ _ _).mp h

theorem MclI_NDTeq : MclIF.Valid NDTeq := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_tall _ _ _).mpr fun b => ?_
  exact (MclIF.holds_imp _ _ _ _).mpr fun h => (MclI_holds_box _ _ _).mpr h

theorem MclI_NIX : MclIF.Valid NIX := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclIF.holds_all _ _ _ _).mpr fun x => (MclIF.holds_all _ _ _ _).mpr fun y => ?_
  exact (MclIF.holds_imp _ _ _ _).mpr fun h => (MclI_holds_box _ _ _).mpr h

theorem MclI_NDX : MclIF.Valid NDX := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclIF.holds_all _ _ _ _).mpr fun x => (MclIF.holds_all _ _ _ _).mpr fun y => ?_
  exact (MclIF.holds_imp _ _ _ _).mpr fun h => (MclI_holds_box _ _ _).mpr h

theorem MclI_TBF : ∀ χ, TBFSch χ → MclIF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MclIF.holds_imp _ _ _ _).mpr fun h => (MclI_holds_box _ _ _).mpr ?_
  exact (MclIF.holds_tall _ _ _).mpr fun a => (MclI_holds_box _ _ _).mp ((MclIF.holds_tall _ _ _).mp h a)

theorem MclI_TCBF : ∀ χ, TCBFSch χ → MclIF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MclIF.holds_imp _ _ _ _).mpr fun h => (MclIF.holds_tall _ _ _).mpr fun a => ?_
  exact (MclI_holds_box _ _ _).mpr ((MclIF.holds_tall _ _ _).mp ((MclI_holds_box _ _ _).mp h) a)

theorem MclI_TNec : MclIF.Valid TNec := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclI_holds_box _ _ _).mpr ?_
  exact (MclIF.holds_tex _ _ _).mpr ⟨a, (MclIF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr rfl)⟩

theorem MclI_BF : MclIF.Valid BF := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_all _ _ _ _).mpr fun F => ?_
  refine (MclIF.holds_imp _ _ _ _).mpr fun h => (MclI_holds_box _ _ _).mpr ?_
  exact (MclIF.holds_all _ _ _ _).mpr fun x => (MclI_holds_box _ _ _).mp ((MclIF.holds_all _ _ _ _).mp h x)

theorem MclI_CBF : MclIF.Valid CBF := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_all _ _ _ _).mpr fun F => ?_
  refine (MclIF.holds_imp _ _ _ _).mpr fun h => (MclIF.holds_all _ _ _ _).mpr fun x => ?_
  exact (MclI_holds_box _ _ _).mpr ((MclIF.holds_all _ _ _ _).mp ((MclI_holds_box _ _ _).mp h) x)

theorem MclI_Nec : MclIF.Valid Nec := by
  intro ρ env
  refine (MclIF.holds_tall _ _ _).mpr fun a => (MclIF.holds_all _ _ _ _).mpr fun x => ?_
  refine (MclI_holds_box _ _ _).mpr ((MclIF.holds_ex _ _ _ _).mpr ⟨x, ?_⟩)
  exact (MclIF.holds_eqv _ _ _ _ _ _).mpr ((mkA_V _).mpr ⟨rfl, HEq.rfl⟩)

theorem MclI_Choice : MclIF.Valid Choice := MclIF.Choice_valid

theorem MclI_not_Class : ¬ ∀ χ, ClassSch χ → MclIF.Valid χ := fun h =>
  MclI_not_Bool fun φ hφ => MclIF.soundness MclI_model h (d_Bool_of_Class (S := ClassSch) (fun _ hc => hc) φ hφ)

end Al
end PIF
