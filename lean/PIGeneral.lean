import PIFoundation

/-!
# General models

Henkin-style general models for PI (see the note *General Models for PI*). A general model has a
set of types, closed under an arrow operation which need not be free; a non-empty domain of items for
each type; an application operation; a truth valuation on the items of type `t`; and an evaluation,
which gives each term of a simple type a value, subject to conditions on variables, application,
renaming (coincidence), substitution, β-conversion, and the truth conditions of the logical
constants. Here: the definition, and soundness.
-/
set_option autoImplicit false

namespace PIF
namespace Gen

/-- The structure of a general model, without its evaluation. -/
structure Struct where
  T : Type
  eT : T
  tT : T
  arr : T → T → T
  D : T → Type
  ne : ∀ A, Nonempty (D A)
  app : ∀ {A B : T}, D (arr A B) → D A → D B
  V : D tT → Prop

namespace Struct
variable (G : Struct)

/-- The type denoted by a category (junk for non-types). -/
def tc {n : Nat} : Cat n → (Fin n → G.T) → G.T
  | .e, _ => G.eT
  | .t, _ => G.tT
  | .var i, ρ => ρ i
  | .arr K L, ρ => G.arr (tc K ρ) (tc L ρ)
  | .pi _, _ => G.eT

variable {G}

theorem tc_ren {n : Nat} (K : Cat n) : ∀ {m : Nat} (r : Fin n → Fin m) (ρ' : Fin m → G.T) (ρ : Fin n → G.T),
    (∀ i, ρ' (r i) = ρ i) → G.tc (K.ren r) ρ' = G.tc K ρ := by
  induction K with
  | e => intros; rfl
  | t => intros; rfl
  | var i => intro m r ρ' ρ h; exact h i
  | arr a b iha ihb => intro m r ρ' ρ h; show G.arr _ _ = G.arr _ _; rw [iha r ρ' ρ h, ihb r ρ' ρ h]
  | pi _ _ => intros; rfl

theorem tc_sub {n : Nat} (K : Cat n) : ∀ {m : Nat} (s : Fin n → Ty m) (ρ' : Fin m → G.T) (ρ : Fin n → G.T),
    (∀ i, G.tc (s i).1 ρ' = ρ i) → G.tc (K.sub s) ρ' = G.tc K ρ := by
  induction K with
  | e => intros; rfl
  | t => intros; rfl
  | var i => intro m s ρ' ρ h; exact h i
  | arr a b iha ihb => intro m s ρ' ρ h; show G.arr _ _ = G.arr _ _; rw [iha s ρ' ρ h, ihb s ρ' ρ h]
  | pi _ _ => intros; rfl

variable (G)

/-- Values for the term variables of a context. -/
def Env {n : Nat} : Ctx n → (Fin n → G.T) → Type
  | .nil, _ => Unit
  | .ext Γ σ, ρ => Env Γ ρ × G.D (G.tc σ.1 ρ)
  | .text Γ, ρ => Env Γ (fun i => ρ (fs i))

def lookup {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) : (ρ : Fin n → G.T) → G.Env Γ ρ → G.D (G.tc K ρ) :=
  match x with
  | .here => fun _ env => env.2
  | .there y => fun ρ env => lookup y ρ env.1
  | .tthere (K := K') y => fun ρ env =>
      cast (congrArg G.D (tc_ren K' fs ρ (fun i => ρ (fs i)) (fun _ => rfl))).symm (lookup y (fun i => ρ (fs i)) env)

variable {G}

theorem lookup_castK {n : Nat} {Γ : Ctx n} {K K' : Cat n} (h : K = K') (x : Var Γ K) (ρ : Fin n → G.T)
    (env : G.Env Γ ρ) : HEq (G.lookup (Var.castK h x) ρ env) (G.lookup x ρ env) := by
  subst h; rfl

theorem lookup_tthere {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) (ρ : Fin (n+1) → G.T)
    (env : G.Env (.text Γ) ρ) : HEq (G.lookup (.tthere x) ρ env) (G.lookup x (fun i => ρ (fs i)) env) :=
  cast_heq _ _

variable (G)

/-- Pull the values of a renamed context back along the renaming. -/
def pullEnv : {n : Nat} → (Γ : Ctx n) → {m : Nat} → {r : Fin n → Fin m} → {Δ : Ctx m} →
    TRen r Γ Δ → (ρ' : Fin m → G.T) → G.Env Δ ρ' → G.Env Γ (fun i => ρ' (r i))
  | _, .nil, _, _, _, _, _, _ => ()
  | _, .ext Γ σ, _, r, _, ρr, ρ', env' =>
      (pullEnv Γ (fun x => ρr (.there x)) ρ' env',
       cast (congrArg G.D (tc_ren σ.1 r ρ' _ (fun _ => rfl))) (G.lookup (ρr .here) ρ' env'))
  | _, .text Γ, _, r, _, ρr, ρ', env' =>
      pullEnv Γ (r := fun i => r (fs i)) (fun x => Var.castK (Cat.ren_ren _ _ _) (ρr (.tthere x))) ρ' env'

variable {G}

theorem lookup_pull {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) :
    ∀ {m : Nat} {r : Fin n → Fin m} {Δ : Ctx m} (ρr : TRen r Γ Δ) (ρ' : Fin m → G.T) (env' : G.Env Δ ρ'),
      HEq (G.lookup (ρr x) ρ' env') (G.lookup x _ (G.pullEnv Γ ρr ρ' env')) := by
  induction x with
  | here => intro m r Δ ρr ρ' env'; exact (cast_heq _ _).symm
  | there y ih => intro m r Δ ρr ρ' env'; exact ih (fun x => ρr (.there x)) ρ' env'
  | tthere y ih =>
    intro m r Δ ρr ρ' env'
    refine HEq.trans ?_ (lookup_tthere y (fun i => ρ' (r i)) (G.pullEnv _ ρr ρ' env')).symm
    exact (lookup_castK _ _ _ _).symm.trans
      (ih (r := fun i => r (fs i)) (fun x => Var.castK (Cat.ren_ren _ _ _) (ρr (.tthere x))) ρ' env')

end Struct

theorem Cat.simple_t {n : Nat} : (Cat.t : Cat n).Simple := trivial

/-- Variables have simple categories. -/
theorem var_simple {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) : K.Simple := by
  induction x with
  | here => exact (by assumption : Ty _).2
  | there _ ih => exact ih
  | tthere _ ih => exact Cat.Simple_ren fs ih

/-- A general model: a structure together with an evaluation satisfying (E1) to (E6). -/
structure GModel extends Struct where
  ev : ∀ {n : Nat} {Γ : Ctx n} {K : Cat n}, K.Simple → Tm Γ K → (ρ : Fin n → T) → toStruct.Env Γ ρ → D (toStruct.tc K ρ)
  /-- (E1) variables -/
  ev_var : ∀ {n : Nat} {Γ : Ctx n} {K : Cat n} (h : K.Simple) (x : Var Γ K) ρ env,
    ev h (.var x) ρ env = toStruct.lookup x ρ env
  /-- (E2) application -/
  ev_app : ∀ {n : Nat} {Γ : Ctx n} {K L : Cat n} (hK : K.Simple) (hL : L.Simple) (f : Tm Γ (.arr K L)) (a : Tm Γ K) ρ env,
    ev hL (.app f a) ρ env = app (ev (K := .arr K L) ⟨hK, hL⟩ f ρ env) (ev hK a ρ env)
  /-- (E3) coincidence, in the form of invariance under renaming -/
  ev_ren : ∀ {n : Nat} {Γ : Ctx n} {K : Cat n} (h : K.Simple) (M : Tm Γ K) {m : Nat} {r : Fin n → Fin m} {Δ : Ctx m}
    (ρr : TRen r Γ Δ) (ρ' : Fin m → T) (env' : toStruct.Env Δ ρ') (ρ : Fin n → T) (env : toStruct.Env Γ ρ),
    (∀ i, ρ' (r i) = ρ i) → (∀ {L : Cat n} (x : Var Γ L), HEq (toStruct.lookup (ρr x) ρ' env') (toStruct.lookup x ρ env)) →
    HEq (ev (Cat.Simple_ren r h) (M.ren ρr) ρ' env') (ev h M ρ env)
  /-- (E4) substitution -/
  ev_sub : ∀ {n : Nat} {Γ : Ctx n} {K : Cat n} (h : K.Simple) (M : Tm Γ K) {m : Nat} {s : Fin n → Ty m} {Δ : Ctx m}
    (σs : TSub s Γ Δ) (ρ' : Fin m → T) (env' : toStruct.Env Δ ρ') (ρ : Fin n → T) (env : toStruct.Env Γ ρ),
    (∀ i, toStruct.tc (s i).1 ρ' = ρ i) →
    (∀ {L : Cat n} (x : Var Γ L), HEq (ev (Cat.Simple_sub s (var_simple x)) (σs x) ρ' env') (toStruct.lookup x ρ env)) →
    HEq (ev (Cat.Simple_sub s h) (M.sub σs) ρ' env') (ev h M ρ env)
  /-- (E5) β-conversion -/
  ev_beta : ∀ {n : Nat} {Γ : Ctx n} {K : Cat n} (h : K.Simple) {M N : Tm Γ K}, BetaEq M N → ∀ ρ env,
    ev h M ρ env = ev h N ρ env
  /-- (E6) truth conditions -/
  t_neg : ∀ {n : Nat} {Γ : Ctx n} (φ : Fm Γ) ρ env, V (ev Cat.simple_t φ.neg ρ env) ↔ ¬ V (ev Cat.simple_t φ ρ env)
  t_imp : ∀ {n : Nat} {Γ : Ctx n} (φ ψ : Fm Γ) ρ env,
    V (ev Cat.simple_t (φ.imp ψ) ρ env) ↔ (V (ev Cat.simple_t φ ρ env) → V (ev Cat.simple_t ψ ρ env))
  t_conj : ∀ {n : Nat} {Γ : Ctx n} (φ ψ : Fm Γ) ρ env,
    V (ev Cat.simple_t (φ.conj ψ) ρ env) ↔ (V (ev Cat.simple_t φ ρ env) ∧ V (ev Cat.simple_t ψ ρ env))
  t_disj : ∀ {n : Nat} {Γ : Ctx n} (φ ψ : Fm Γ) ρ env,
    V (ev Cat.simple_t (φ.disj ψ) ρ env) ↔ (V (ev Cat.simple_t φ ρ env) ∨ V (ev Cat.simple_t ψ ρ env))
  t_iff : ∀ {n : Nat} {Γ : Ctx n} (φ ψ : Fm Γ) ρ env,
    V (ev Cat.simple_t (φ.iff ψ) ρ env) ↔ (V (ev Cat.simple_t φ ρ env) ↔ V (ev Cat.simple_t ψ ρ env))
  t_all : ∀ {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) ρ env,
    V (ev Cat.simple_t (Tm.all σ φ) ρ env) ↔ ∀ v, V (ev Cat.simple_t φ ρ (env, v))
  t_ex : ∀ {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) ρ env,
    V (ev Cat.simple_t (Tm.ex σ φ) ρ env) ↔ ∃ v, V (ev Cat.simple_t φ ρ (env, v))
  t_tall : ∀ {n : Nat} {Γ : Ctx n} (φ : Fm (.text Γ)) ρ env,
    V (ev Cat.simple_t (Tm.tall φ) ρ env) ↔ ∀ A, V (ev Cat.simple_t φ (scons A ρ) env)
  t_tex : ∀ {n : Nat} {Γ : Ctx n} (φ : Fm (.text Γ)) ρ env,
    V (ev Cat.simple_t (Tm.tex φ) ρ env) ↔ ∃ A, V (ev Cat.simple_t φ (scons A ρ) env)

namespace GModel
variable (G : GModel)

/-- Truth of a formula under a valuation. -/
abbrev Holds {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : Fin n → G.T) (env : G.Env Γ ρ) : Prop := G.V (G.ev Cat.simple_t φ ρ env)

def Valid {n : Nat} {Γ : Ctx n} (φ : Fm Γ) : Prop := ∀ ρ env, G.Holds φ ρ env

/-- A general model of PI⁻: the closed identity axioms other than LL≡ are valid, and so is every
instance of LL≈. -/
structure IsModelPIm : Prop where
  refEqv : G.Valid RefEqv
  symEqv : G.Valid SymEqv
  transEqv : G.Valid TransEqv
  refTeq : G.Valid RefTeq
  llTeq : ∀ {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)), G.Valid (LLTeq Q)

theorem ev_castK {n : Nat} {Γ : Ctx n} {K K' : Cat n} (e : K = K') (h : K'.Simple) (h' : K.Simple) (M : Tm Γ K)
    (ρ : Fin n → G.T) (env : G.Env Γ ρ) : HEq (G.ev h (Tm.castK e M) ρ env) (G.ev h' M ρ env) := by
  subst e; rfl

theorem ev_wk {n : Nat} {Γ : Ctx n} (L : Ty n) (φ : Fm Γ) (ρ : Fin n → G.T) (env : G.Env Γ ρ) (v : G.D (G.tc L.1 ρ)) :
    G.Holds (φ.wk L) ρ (env, v) ↔ G.Holds φ ρ env := by
  have := (G.ev_castK (Γ := .ext Γ L) (Cat.ren_id _) Cat.simple_t (Cat.Simple_ren _ Cat.simple_t) (φ.ren (wkRen L)) ρ (env, v)).trans
    (G.ev_ren Cat.simple_t φ (wkRen L) ρ (env, v) ρ env (fun _ => rfl) (fun _ => Struct.lookup_castK _ _ _ _))
  exact Iff.of_eq (congrArg G.V (eq_of_heq this))

theorem ev_twk {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (A : G.T) (ρ : Fin n → G.T) (env : G.Env Γ ρ) :
    G.Holds φ.twk (scons A ρ) env ↔ G.Holds φ ρ env :=
  Iff.of_eq (congrArg G.V (eq_of_heq
    (G.ev_ren Cat.simple_t φ (twkRen Γ) (scons A ρ) env ρ env (fun _ => rfl) (fun x => Struct.lookup_tthere x _ _))))

theorem ev_subst0 {n : Nat} {Γ : Ctx n} {σ : Ty n} (φ : Fm (.ext Γ σ)) (κ : Tm Γ σ.1) (ρ : Fin n → G.T)
    (env : G.Env Γ ρ) : G.Holds (φ.subst0 κ) ρ env ↔ G.Holds φ ρ (env, G.ev σ.2 κ ρ env) := by
  refine Iff.of_eq (congrArg G.V (eq_of_heq ((G.ev_castK _ Cat.simple_t Cat.simple_t _ ρ env).trans
    (G.ev_sub Cat.simple_t φ (sub0 κ) ρ env ρ _ (fun _ => rfl) ?_))))
  intro L x
  cases x with
  | here => exact G.ev_castK _ _ _ _ _ _
  | there y => exact (G.ev_castK _ _ (var_simple y) _ _ _).trans (heq_of_eq (G.ev_var _ y ρ env))

theorem ev_tinst {n : Nat} {Γ : Ctx n} (φ : Fm (.text Γ)) (σ : Ty n) (ρ : Fin n → G.T) (env : G.Env Γ ρ) :
    G.Holds (φ.tinst σ) ρ env ↔ G.Holds φ (scons (G.tc σ.1 ρ) ρ) env := by
  refine Iff.of_eq (congrArg G.V (eq_of_heq
    (G.ev_sub Cat.simple_t φ (tsub0 Γ σ) ρ env (scons (G.tc σ.1 ρ) ρ) env (fin_cases rfl (fun _ => rfl)) ?_)))
  intro L x
  cases x with
  | tthere y =>
    exact (G.ev_castK _ _ (var_simple y) _ _ _).trans ((heq_of_eq (G.ev_var _ y ρ env)).trans
      (Struct.lookup_tthere y (scons (G.tc σ.1 ρ) ρ) env).symm)

theorem holds_inst {n : Nat} {Γ : Ctx n} {k : Nat} (P : PF k) (as : Fin k → Fm Γ) (ρ : Fin n → G.T)
    (env : G.Env Γ ρ) : G.Holds (P.inst as) ρ env ↔ P.evalP (fun i => G.Holds (as i) ρ env) := by
  induction P with
  | atom i => exact Iff.rfl
  | neg P ih => exact (G.t_neg _ ρ env).trans (not_congr ih)
  | imp P Q ihP ihQ => exact (G.t_imp _ _ ρ env).trans (imp_congr ihP ihQ)
  | conj P Q ihP ihQ => exact (G.t_conj _ _ ρ env).trans (and_congr ihP ihQ)
  | disj P Q ihP ihQ => exact (G.t_disj _ _ ρ env).trans (or_congr ihP ihQ)
  | iff P Q ihP ihQ => exact (G.t_iff _ _ ρ env).trans (iff_congr ihP ihQ)

/-- **Soundness** for general models. -/
theorem soundness {Ax : Fm Ctx.nil → Prop} (hM : G.IsModelPIm) (hAx : ∀ φ, Ax φ → G.Valid φ)
    {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : Prov Ax Γ φ) : G.Valid φ := by
  induction h with
  | taut P as hP => intro ρ env; exact (G.holds_inst P as ρ env).mpr (hP _)
  | instAll σ φ κ =>
    intro ρ env
    exact (G.t_imp _ _ ρ env).mpr fun h => (G.ev_subst0 φ κ ρ env).mpr ((G.t_all σ φ ρ env).mp h _)
  | distAll σ φ ψ =>
    intro ρ env
    refine (G.t_imp _ _ ρ env).mpr fun h => (G.t_imp _ _ ρ env).mpr fun hφ => (G.t_all σ ψ ρ env).mpr fun v => ?_
    exact (G.t_imp _ _ ρ _).mp ((G.t_all σ _ ρ env).mp h v) ((G.ev_wk σ φ ρ env v).mpr hφ)
  | dualEx σ φ =>
    intro ρ env
    refine (G.t_iff _ _ ρ env).mpr ((G.t_ex σ φ ρ env).trans ?_)
    refine Iff.trans ?_ (G.t_neg _ ρ env).symm
    refine Iff.trans ?_ (not_congr (G.t_all σ _ ρ env)).symm
    constructor
    · rintro ⟨v, hv⟩ h; exact (G.t_neg _ ρ _).mp (h v) hv
    · intro h; exact Classical.byContradiction fun hn => h fun v => (G.t_neg _ ρ _).mpr fun hv => hn ⟨v, hv⟩
  | instTAll φ σ =>
    intro ρ env
    exact (G.t_imp _ _ ρ env).mpr fun h => (G.ev_tinst φ σ ρ env).mpr ((G.t_tall φ ρ env).mp h _)
  | distTAll φ ψ =>
    intro ρ env
    refine (G.t_imp _ _ ρ env).mpr fun h => (G.t_imp _ _ ρ env).mpr fun hφ => (G.t_tall ψ ρ env).mpr fun A => ?_
    exact (G.t_imp _ _ _ _).mp ((G.t_tall _ ρ env).mp h A) ((G.ev_twk φ A ρ env).mpr hφ)
  | dualTEx φ =>
    intro ρ env
    refine (G.t_iff _ _ ρ env).mpr ((G.t_tex φ ρ env).trans ?_)
    refine Iff.trans ?_ (G.t_neg _ ρ env).symm
    refine Iff.trans ?_ (not_congr (G.t_tall _ ρ env)).symm
    constructor
    · rintro ⟨A, hA⟩ h; exact (G.t_neg _ _ _).mp (h A) hA
    · intro h; exact Classical.byContradiction fun hn => h fun A => (G.t_neg _ _ _).mpr fun hA => hn ⟨A, hA⟩
  | beta h => intro ρ env; exact (G.t_iff _ _ ρ env).mpr (Iff.of_eq (congrArg G.V (G.ev_beta Cat.simple_t h ρ env)))
  | refEqv => exact hM.refEqv
  | symEqv => exact hM.symEqv
  | transEqv => exact hM.transEqv
  | refTeq => exact hM.refTeq
  | llTeq Q => exact hM.llTeq Q
  | ax h => exact hAx _ h
  | mp _ _ ih1 ih2 => intro ρ env; exact (G.t_imp _ _ ρ env).mp (ih2 ρ env) (ih1 ρ env)
  | genAll σ _ ih => intro ρ env; exact (G.t_all σ _ ρ env).mpr fun v => ih ρ (env, v)
  | genTAll _ ih => intro ρ env; exact (G.t_tall _ ρ env).mpr fun A => ih (scons A ρ) env
  | ren ρr _ ih =>
    intro ρ' env'
    exact cast (congrArg G.V (eq_of_heq (G.ev_ren Cat.simple_t _ ρr ρ' env' _ (G.pullEnv _ ρr ρ' env') (fun _ => rfl)
      (fun x => Struct.lookup_pull x ρr ρ' env')))).symm (ih _ _)
  | strengthen σ _ ih =>
    intro ρ env
    exact (G.ev_wk σ _ ρ env (Classical.choice (G.ne _))).mp (ih ρ _)
  | tstrengthen _ ih =>
    intro ρ env
    exact (G.ev_twk _ G.eT ρ env).mp (ih (scons G.eT ρ) env)

theorem soundness_PI {S : Fm Ctx.nil → Prop} (hM : G.IsModelPIm) (hLL : G.Valid LLEqv)
    (hS : ∀ φ, S φ → G.Valid φ) {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : PI S Γ φ) : G.Valid φ :=
  G.soundness hM (fun ψ hψ => hψ.elim (fun e => e ▸ hLL) (hS ψ)) h

end GModel

end Gen
end PIF
