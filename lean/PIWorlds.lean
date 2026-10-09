import PIModal

/-!
# Propositions as sets of worlds

Here the items of type `t` are functions from a non-empty set `W` of worlds to truth values, with
a distinguished actual world `w₀`. The connectives and quantifiers act world by world; the values
of `≡` and `≈` are arbitrary such functions, so identity may hold at some worlds and not others.
A formula is true when its value is true at `w₀`. This file repeats the semantics and the soundness
proof for these models. In them `□φ` (that is, `φ ≡_t ⊤`) can be false while `φ` is true.
-/
set_option autoImplicit false

namespace PIF
namespace Wd

structure Univ where
  W : Type
  w0 : W
  E : Type
  Base : Type
  B : Base → Type
  neE : Nonempty E
  neB : ∀ b, Nonempty (B b)

/-- The set a code names. -/
def Univ.El (U : Univ) : Code U.Base → Type
  | .e => U.E
  | .t => U.W → Prop
  | .base b => U.B b
  | .arr a c => U.El a → U.El c

structure Frame where
  U : Univ
  /-- the value of `≡`, at each pair of members of the universe -/
  eqv : (a b : Code U.Base) → U.El a → U.El b → U.W → Prop
  /-- the value of `≈` -/
  teq : Code U.Base → Code U.Base → U.W → Prop

namespace Univ
variable (U : Univ)

/-- Valuations of type variables. -/
abbrev TEnv (n : Nat) := Fin n → Code U.Base

/-- The semantic value of a category. -/
def CatVal {n : Nat} : Cat n → U.TEnv n → Type
  | .e, _ => U.E
  | .t, _ => U.W → Prop
  | .var i, ρ => U.El (ρ i)
  | .arr K L, ρ => CatVal K ρ → CatVal L ρ
  | .pi K, ρ => (a : Code U.Base) → CatVal K (scons a ρ)

/-- The code of a type. -/
def code {n : Nat} : Cat n → U.TEnv n → Code U.Base
  | .e, _ => .e
  | .t, _ => .t
  | .var i, ρ => ρ i
  | .arr K L, ρ => .arr (code K ρ) (code L ρ)
  | .pi _, _ => .e

variable {U}

theorem El_code {n : Nat} {K : Cat n} (ρ : U.TEnv n) (h : K.Simple) : U.El (U.code K ρ) = U.CatVal K ρ := by
  induction K with
  | e => rfl
  | t => rfl
  | var i => rfl
  | arr a b iha ihb => simp only [code, El, CatVal, iha ρ h.1, ihb ρ h.2]
  | pi K _ => exact h.elim

theorem code_ren {n : Nat} (K : Cat n) : ∀ {m : Nat} (r : Fin n → Fin m) (ρ : U.TEnv m),
    U.code (K.ren r) ρ = U.code K (fun i => ρ (r i)) := by
  induction K with
  | e => intros; rfl
  | t => intros; rfl
  | var i => intros; rfl
  | arr a b iha ihb => intro m r ρ; simp only [Cat.ren, code, iha, ihb]
  | pi K _ => intros; rfl

theorem code_sub {n : Nat} (K : Cat n) : ∀ {m : Nat} (s : Fin n → Ty m) (ρ : U.TEnv m),
    U.code (K.sub s) ρ = U.code K (fun i => U.code (s i).1 ρ) := by
  induction K with
  | e => intros; rfl
  | t => intros; rfl
  | var i => intros; rfl
  | arr a b iha ihb => intro m s ρ; simp only [Cat.sub, code, iha, ihb]
  | pi K _ => intros; rfl

theorem pi_congr {X : Type} {P Q : X → Type} (h : ∀ a, P a = Q a) : ((a : X) → P a) = ((a : X) → Q a) := by
  have : P = Q := funext h
  subst this; rfl

theorem CatVal_ren {n : Nat} (K : Cat n) : ∀ {m : Nat} (r : Fin n → Fin m) (ρ' : U.TEnv m) (ρ : U.TEnv n),
    (∀ i, ρ' (r i) = ρ i) → U.CatVal (K.ren r) ρ' = U.CatVal K ρ := by
  induction K with
  | e => intros; rfl
  | t => intros; rfl
  | var i => intro m r ρ' ρ h; simp only [Cat.ren, CatVal, h]
  | arr a b iha ihb => intro m r ρ' ρ h; simp only [Cat.ren, CatVal, iha r ρ' ρ h, ihb r ρ' ρ h]
  | pi K ih =>
    intro m r ρ' ρ h
    exact pi_congr fun a => ih (liftR r) (scons a ρ') (scons a ρ) (fin_cases rfl (fun i => h i))

theorem CatVal_sub {n : Nat} (K : Cat n) : ∀ {m : Nat} (s : Fin n → Ty m) (ρ' : U.TEnv m) (ρ : U.TEnv n),
    (∀ i, U.code (s i).1 ρ' = ρ i) → U.CatVal (K.sub s) ρ' = U.CatVal K ρ := by
  induction K with
  | e => intros; rfl
  | t => intros; rfl
  | var i => intro m s ρ' ρ h; show U.CatVal (s i).1 ρ' = U.El (ρ i); rw [← h i, El_code ρ' (s i).2]
  | arr a b iha ihb => intro m s ρ' ρ h; simp only [Cat.sub, CatVal, iha s ρ' ρ h, ihb s ρ' ρ h]
  | pi K ih =>
    intro m s ρ' ρ h
    refine pi_congr fun a => ih (liftT s) (scons a ρ') (scons a ρ) (fin_cases rfl (fun i => ?_))
    show U.code ((s i).1.ren fs) (scons a ρ') = ρ i
    rw [code_ren]; exact h i

theorem El_nonempty : ∀ c : Code U.Base, Nonempty (U.El c)
  | .e => U.neE
  | .t => ⟨fun _ => True⟩
  | .base b => U.neB b
  | .arr _ c => let ⟨y⟩ := El_nonempty c; ⟨fun _ => y⟩

theorem CatVal_nonempty {n : Nat} (K : Cat n) : ∀ ρ : U.TEnv n, Nonempty (U.CatVal K ρ) := by
  induction K with
  | e => intro; exact U.neE
  | t => intro; exact ⟨fun _ => True⟩
  | var i => intro ρ; exact El_nonempty (ρ i)
  | arr a b _ ihb => intro ρ; exact let ⟨y⟩ := ihb ρ; ⟨fun _ => y⟩
  | pi K ih => intro ρ; exact ⟨fun a => Classical.choice (ih (scons a ρ))⟩

/-- Values for the term variables of a context. -/
def Env {n : Nat} : Ctx n → U.TEnv n → Type
  | .nil, _ => Unit
  | .ext Γ σ, ρ => Env Γ ρ × U.CatVal σ.1 ρ
  | .text Γ, ρ => Env Γ (fun i => ρ (fs i))

def lookup {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) : (ρ : U.TEnv n) → U.Env Γ ρ → U.CatVal K ρ :=
  match x with
  | .here => fun _ env => env.2
  | .there y => fun ρ env => lookup y ρ env.1
  | .tthere (K := K') y => fun ρ env =>
      cast (CatVal_ren K' fs ρ (fun i => ρ (fs i)) (fun _ => rfl)).symm (lookup y (fun i => ρ (fs i)) env)

/-- The truth value of a proposition at a world. -/
def ap {n : Nat} {ρ : U.TEnv n} (x : U.CatVal Cat.t ρ) (w : U.W) : Prop := x w

theorem tapp_eq {n : Nat} (K : Cat (n+1)) (σ : Ty n) (ρ : U.TEnv n) :
    U.CatVal K (scons (U.code σ.1 ρ) ρ) = U.CatVal (K.sub (inst σ)) ρ :=
  (CatVal_sub K (inst σ) ρ _ (fin_cases rfl (fun _ => rfl))).symm

end Univ

namespace Frame
variable (F : Frame)

/-- The values of the constants. -/
def constVal {n : Nat} {K : Cat n} (c : Const n K) (ρ : F.U.TEnv n) : F.U.CatVal K ρ :=
  match c with
  | .neg => fun p w => ¬ p w
  | .imp => fun p q w => p w → q w
  | .and => fun p q w => p w ∧ q w
  | .or => fun p q w => p w ∨ q w
  | .iff => fun p q w => p w ↔ q w
  | .all => fun _ P w => ∀ x, P x w
  | .ex => fun _ P w => ∃ x, P x w
  | .tall => fun Q w => ∀ a, Q a w
  | .tex => fun Q w => ∃ a, Q a w
  | .eqv => fun a b x y => F.eqv a b x y
  | .teq => fun a b => F.teq a b

/-- The semantic value of a term, given values for its type variables and its term variables. -/
def eval {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) : (ρ : F.U.TEnv n) → F.U.Env Γ ρ → F.U.CatVal K ρ :=
  match M with
  | .var x => fun ρ env => F.U.lookup x ρ env
  | .const c => fun ρ _ => F.constVal c ρ
  | .app f a => fun ρ env => eval f ρ env (eval a ρ env)
  | .lam _ b => fun ρ env v => eval b ρ (env, v)
  | .tlam b => fun ρ env a => eval b (scons a ρ) env
  | .tapp (K := K) f σ => fun ρ env => cast (F.U.tapp_eq K σ ρ) (eval f ρ env (F.U.code σ.1 ρ))

/-- The truth value of a formula at a world, under a valuation. -/
abbrev HoldsAt {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) : Prop :=
  F.U.ap (F.eval φ ρ env) w

/-- The truth value of a formula, at the actual world, under a valuation. -/
abbrev Holds {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) : Prop :=
  F.U.ap (F.eval φ ρ env) F.U.w0

/-- A formula is *valid* in a frame when it is true under every valuation of its variables. -/
def Valid {n : Nat} {Γ : Ctx n} (φ : Fm Γ) : Prop := ∀ ρ env, F.Holds φ ρ env

end Frame

/-! ## 5. The semantic substitution lemmas -/

section HEqLemmas

theorem heq_app {A A' B B' : Type} (hA : A = A') (hB : B = B') {f : A → B} {f' : A' → B'}
    {a : A} {a' : A'} (hf : HEq f f') (ha : HEq a a') : HEq (f a) (f' a') := by
  subst hA; subst hB; rw [eq_of_heq hf, eq_of_heq ha]

theorem heq_funext {A A' B B' : Type} (hA : A = A') (hB : B = B') {f : A → B} {g : A' → B'}
    (h : ∀ a a', HEq a a' → HEq (f a) (g a')) : HEq f g := by
  subst hA; subst hB; exact heq_of_eq (funext fun a => eq_of_heq (h a a HEq.rfl))

theorem heq_pifun {X : Type} {P Q : X → Type} (hPQ : ∀ a, P a = Q a) {f : (a : X) → P a}
    {g : (a : X) → Q a} (h : ∀ a, HEq (f a) (g a)) : HEq f g := by
  have : P = Q := funext hPQ
  subst this; exact heq_of_eq (funext fun a => eq_of_heq (h a))

theorem heq_dapp {X : Type} {P Q : X → Type} (hPQ : ∀ a, P a = Q a) {f : (a : X) → P a}
    {g : (a : X) → Q a} (hf : HEq f g) {a a' : X} (ha : a = a') : HEq (f a) (g a') := by
  have : P = Q := funext hPQ
  subst this; subst ha; rw [eq_of_heq hf]

end HEqLemmas

namespace Frame
variable (F : Frame)

theorem eval_castK {n : Nat} {Γ : Ctx n} {K K' : Cat n} (h : K = K') (M : Tm Γ K) (ρ : F.U.TEnv n)
    (env : F.U.Env Γ ρ) : HEq (F.eval (Tm.castK h M) ρ env) (F.eval M ρ env) := by
  subst h; rfl

theorem lookup_castK {n : Nat} {Γ : Ctx n} {K K' : Cat n} (h : K = K') (x : Var Γ K) (ρ : F.U.TEnv n)
    (env : F.U.Env Γ ρ) : HEq (F.U.lookup (Var.castK h x) ρ env) (F.U.lookup x ρ env) := by
  subst h; rfl

theorem lookup_tthere {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) (ρ : F.U.TEnv (n+1))
    (env : F.U.Env (.text Γ) ρ) : HEq (F.U.lookup (.tthere x) ρ env) (F.U.lookup x (fun i => ρ (fs i)) env) :=
  cast_heq _ _

theorem constVal_ren {n m : Nat} (r : Fin n → Fin m) {K : Cat n} (c : Const n K) (ρ' : F.U.TEnv m) (ρ : F.U.TEnv n)
    (_hρ : ∀ i, ρ' (r i) = ρ i) : HEq (F.constVal (c.ren r) ρ') (F.constVal c ρ) := by
  cases c <;> rfl

theorem constVal_sub {n m : Nat} (s : Fin n → Ty m) {K : Cat n} (c : Const n K) (ρ' : F.U.TEnv m) (ρ : F.U.TEnv n) :
    HEq (F.constVal (c.sub s) ρ') (F.constVal c ρ) := by
  cases c <;> rfl

/-- Renaming does not change semantic values, given matching valuations. -/
theorem eval_ren {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) :
    ∀ {m : Nat} {r : Fin n → Fin m} {Δ : Ctx m} (ρr : TRen r Γ Δ) (ρ' : F.U.TEnv m) (env' : F.U.Env Δ ρ')
      (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ), (∀ i, ρ' (r i) = ρ i) →
      (∀ {L : Cat n} (x : Var Γ L), HEq (F.U.lookup (ρr x) ρ' env') (F.U.lookup x ρ env)) →
      HEq (F.eval (M.ren ρr) ρ' env') (F.eval M ρ env) := by
  induction M with
  | var x => intro m r Δ ρr ρ' env' ρ env _ hx; exact hx x
  | const c => intro m r Δ ρr ρ' env' ρ env hρ _; exact F.constVal_ren r c ρ' ρ hρ
  | app f a ihf iha =>
    intro m r Δ ρr ρ' env' ρ env hρ hx
    exact heq_app (Univ.CatVal_ren _ r ρ' ρ hρ) (Univ.CatVal_ren _ r ρ' ρ hρ)
      (ihf ρr ρ' env' ρ env hρ hx) (iha ρr ρ' env' ρ env hρ hx)
  | lam σ b ih =>
    intro m r Δ ρr ρ' env' ρ env hρ hx
    refine heq_funext (Univ.CatVal_ren _ r ρ' ρ hρ) (Univ.CatVal_ren _ r ρ' ρ hρ) fun v' v hv => ?_
    refine ih (ρr.lift σ) ρ' (env', v') ρ (env, v) hρ ?_
    intro L x
    cases x with
    | here => exact hv
    | there y => exact hx y
  | tlam b ih =>
    intro m r Δ ρr ρ' env' ρ env hρ hx
    refine heq_pifun (fun a => Univ.CatVal_ren _ (liftR r) (scons a ρ') (scons a ρ)
      (fin_cases rfl (fun i => hρ i))) fun a => ?_
    refine ih ρr.tlift (scons a ρ') env' (scons a ρ) env (fin_cases rfl (fun i => hρ i)) ?_
    intro L x
    cases x with
    | tthere y =>
      exact (F.lookup_castK _ _ _ _).trans ((F.lookup_tthere (ρr y) (scons a ρ') env').trans
        ((hx y).trans (F.lookup_tthere y (scons a ρ) env).symm))
  | tapp f σ ih =>
    intro m r Δ ρr ρ' env' ρ env hρ hx
    refine (F.eval_castK _ _ _ _).trans ((cast_heq _ _).trans ((HEq.trans ?_ (cast_heq _ _).symm)))
    refine heq_dapp (fun a => Univ.CatVal_ren _ (liftR r) (scons a ρ') (scons a ρ)
      (fin_cases rfl (fun i => hρ i))) (ih ρr ρ' env' ρ env hρ hx) ?_
    show F.U.code (σ.1.ren r) ρ' = F.U.code σ.1 ρ
    rw [Univ.code_ren]; exact congrArg _ (funext hρ)

theorem eval_wk {n : Nat} {Γ : Ctx n} {K : Cat n} (L : Ty n) (M : Tm Γ K) (ρ : F.U.TEnv n)
    (env : F.U.Env Γ ρ) (v : F.U.CatVal L.1 ρ) : F.eval (M.wk L) (ρ) (env, v) = F.eval M ρ env :=
  eq_of_heq ((F.eval_castK _ _ _ _).trans (F.eval_ren M (wkRen L) ρ (env, v) ρ env (fun _ => rfl)
    (fun _ => F.lookup_castK _ _ _ _)))

theorem eval_twk {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) (a : Code F.U.Base) (ρ : F.U.TEnv n)
    (env : F.U.Env Γ ρ) : HEq (F.eval M.twk (scons a ρ) env) (F.eval M ρ env) :=
  F.eval_ren M (twkRen Γ) (scons a ρ) env ρ env (fun _ => rfl) (fun x => F.lookup_tthere x _ _)

/-- Substitution: the value of `M` with terms substituted for its variables is the value of `M`
with the values of those terms assigned to its variables. -/
theorem eval_sub {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) :
    ∀ {m : Nat} {s : Fin n → Ty m} {Δ : Ctx m} (σs : TSub s Γ Δ) (ρ' : F.U.TEnv m) (env' : F.U.Env Δ ρ')
      (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ), (∀ i, F.U.code (s i).1 ρ' = ρ i) →
      (∀ {L : Cat n} (x : Var Γ L), HEq (F.eval (σs x) ρ' env') (F.U.lookup x ρ env)) →
      HEq (F.eval (M.sub σs) ρ' env') (F.eval M ρ env) := by
  induction M with
  | var x => intro m s Δ σs ρ' env' ρ env _ hx; exact hx x
  | const c => intro m s Δ σs ρ' env' ρ env _ _; exact F.constVal_sub s c ρ' ρ
  | app f a ihf iha =>
    intro m s Δ σs ρ' env' ρ env hρ hx
    exact heq_app (Univ.CatVal_sub _ s ρ' ρ hρ) (Univ.CatVal_sub _ s ρ' ρ hρ)
      (ihf σs ρ' env' ρ env hρ hx) (iha σs ρ' env' ρ env hρ hx)
  | lam σ b ih =>
    intro m s Δ σs ρ' env' ρ env hρ hx
    refine heq_funext (Univ.CatVal_sub _ s ρ' ρ hρ) (Univ.CatVal_sub _ s ρ' ρ hρ) fun v' v hv => ?_
    refine ih (σs.lift σ) ρ' (env', v') ρ (env, v) hρ ?_
    intro L x
    cases x with
    | here => exact hv
    | there y => exact (heq_of_eq (F.eval_wk _ _ _ _ _)).trans (hx y)
  | tlam b ih =>
    intro m s Δ σs ρ' env' ρ env hρ hx
    have hρ' : ∀ (a : Code F.U.Base) i, F.U.code (liftT s i).1 (scons a ρ') = scons a ρ i := fun a =>
      fin_cases rfl (fun i => by
        show F.U.code ((s i).1.ren fs) (scons a ρ') = ρ i
        rw [Univ.code_ren]; exact hρ i)
    refine heq_pifun (fun a => Univ.CatVal_sub _ (liftT s) (scons a ρ') (scons a ρ) (hρ' a)) fun a => ?_
    refine ih σs.tlift (scons a ρ') env' (scons a ρ) env (hρ' a) ?_
    intro L x
    cases x with
    | tthere y =>
      exact (F.eval_castK _ _ _ _).trans ((F.eval_twk _ a ρ' env').trans
        ((hx y).trans (F.lookup_tthere y (scons a ρ) env).symm))
  | tapp f σ ih =>
    intro m s Δ σs ρ' env' ρ env hρ hx
    have hρ' : ∀ (a : Code F.U.Base) i, F.U.code (liftT s i).1 (scons a ρ') = scons a ρ i := fun a =>
      fin_cases rfl (fun i => by
        show F.U.code ((s i).1.ren fs) (scons a ρ') = ρ i
        rw [Univ.code_ren]; exact hρ i)
    refine (F.eval_castK _ _ _ _).trans ((cast_heq _ _).trans ((HEq.trans ?_ (cast_heq _ _).symm)))
    refine heq_dapp (fun a => Univ.CatVal_sub _ (liftT s) (scons a ρ') (scons a ρ) (hρ' a))
      (ih σs ρ' env' ρ env hρ hx) ?_
    show F.U.code (σ.1.sub s) ρ' = F.U.code σ.1 ρ
    rw [Univ.code_sub]; exact congrArg _ (funext hρ)

theorem eval_subst0 {n : Nat} {Γ : Ctx n} {σ : Ty n} {L : Cat n} (M : Tm (.ext Γ σ) L) (N : Tm Γ σ.1)
    (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) : F.eval (M.subst0 N) ρ env = F.eval M ρ (env, F.eval N ρ env) := by
  refine eq_of_heq ((F.eval_castK _ _ _ _).trans (F.eval_sub M (sub0 N) ρ env ρ _ (fun _ => rfl) ?_))
  intro L x
  cases x with
  | here => exact F.eval_castK _ _ _ _
  | there y => exact F.eval_castK _ _ _ _

theorem eval_tinst {n : Nat} {Γ : Ctx n} {K : Cat (n+1)} (M : Tm (.text Γ) K) (σ : Ty n)
    (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    HEq (F.eval (M.tinst σ) ρ env) (F.eval M (scons (F.U.code σ.1 ρ) ρ) env) := by
  refine F.eval_sub M (tsub0 Γ σ) ρ env (scons (F.U.code σ.1 ρ) ρ) env (fin_cases rfl (fun _ => rfl)) ?_
  intro L x
  cases x with
  | tthere y => exact (F.eval_castK _ _ _ _).trans (F.lookup_tthere y (scons (F.U.code σ.1 ρ) ρ) env).symm

end Frame

namespace Frame
variable (F : Frame)

theorem eval_step {n : Nat} {Γ : Ctx n} {K : Cat n} {M N : Tm Γ K} (h : Step M N) :
    ∀ ρ env, F.eval M ρ env = F.eval N ρ env := by
  induction h with
  | beta b a => intro ρ env; exact (F.eval_subst0 b a ρ env).symm
  | tbeta b σ => intro ρ env; exact eq_of_heq ((cast_heq _ _).trans (F.eval_tinst b σ ρ env).symm)
  | appL a _ ih => intro ρ env; simp only [eval]; rw [ih ρ env]
  | appR f _ ih => intro ρ env; simp only [eval]; rw [ih ρ env]
  | lam σ _ ih => intro ρ env; exact funext fun v => ih ρ (env, v)
  | tlam _ ih => intro ρ env; exact funext fun a => ih (scons a ρ) env
  | tapp σ _ ih => intro ρ env; simp only [eval]; rw [ih ρ env]

theorem eval_betaEq {n : Nat} {Γ : Ctx n} {K : Cat n} {M N : Tm Γ K} (h : BetaEq M N) :
    ∀ ρ env, F.eval M ρ env = F.eval N ρ env := by
  induction h with
  | refl => intros; rfl
  | step h => exact F.eval_step h
  | symm _ ih => intro ρ env; exact (ih ρ env).symm
  | trans _ _ ih1 ih2 => intro ρ env; exact (ih1 ρ env).trans (ih2 ρ env)

end Frame

/-! ### Soundness -/

namespace Frame
variable (F : Frame)

section EvalLemmas
variable {n : Nat} {Γ : Ctx n}

theorem cast_forall {W A A' : Type} (hA : A = A') (h : ((A → W → Prop) → W → Prop) = ((A' → W → Prop) → W → Prop))
    (P : A' → W → Prop) (w : W) : cast h (fun Q : A → W → Prop => fun w => ∀ x, Q x w) P w ↔ ∀ x, P x w := by
  subst hA; rw [cast_eq]

theorem cast_exists {W A A' : Type} (hA : A = A') (h : ((A → W → Prop) → W → Prop) = ((A' → W → Prop) → W → Prop))
    (P : A' → W → Prop) (w : W) : cast h (fun Q : A → W → Prop => fun w => ∃ x, Q x w) P w ↔ ∃ x, P x w := by
  subst hA; rw [cast_eq]

theorem eval_tapp {K : Cat (n+1)} (f : Tm Γ (.pi K)) (σ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.eval (Tm.tapp f σ) ρ env = cast (F.U.tapp_eq K σ ρ) (F.eval f ρ env (F.U.code σ.1 ρ)) := rfl

theorem heq_eval_tapp {K : Cat (n+1)} (f : Tm Γ (.pi K)) (σ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    HEq (F.eval (Tm.tapp f σ) ρ env) (F.eval f ρ env (F.U.code σ.1 ρ)) :=
  (heq_of_eq (F.eval_tapp f σ ρ env)).trans (cast_heq _ _)

theorem holdsAt_all (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (Tm.all σ φ) ρ env w ↔ ∀ v : F.U.CatVal σ.1 ρ, F.HoldsAt φ ρ (env, v) w :=
  cast_forall (Univ.El_code ρ σ.2) _ _ _

theorem holdsAt_ex (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (Tm.ex σ φ) ρ env w ↔ ∃ v : F.U.CatVal σ.1 ρ, F.HoldsAt φ ρ (env, v) w :=
  cast_exists (Univ.El_code ρ σ.2) _ _ _

theorem holds_all (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.all σ φ) ρ env ↔ ∀ v : F.U.CatVal σ.1 ρ, F.Holds φ ρ (env, v) :=
  F.holdsAt_all σ φ ρ env _

theorem holds_ex (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.ex σ φ) ρ env ↔ ∃ v : F.U.CatVal σ.1 ρ, F.Holds φ ρ (env, v) :=
  F.holdsAt_ex σ φ ρ env _

theorem holds_tall (φ : Fm (.text Γ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.tall φ) ρ env ↔ ∀ a, F.Holds φ (scons a ρ) env := Iff.rfl

theorem holds_tex (φ : Fm (.text Γ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.tex φ) ρ env ↔ ∃ a, F.Holds φ (scons a ρ) env := Iff.rfl

theorem holds_imp (φ ψ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (φ.imp ψ) ρ env ↔ (F.Holds φ ρ env → F.Holds ψ ρ env) := Iff.rfl
theorem holds_neg (φ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds φ.neg ρ env ↔ ¬ F.Holds φ ρ env := Iff.rfl
theorem holds_conj (φ ψ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (φ.conj ψ) ρ env ↔ (F.Holds φ ρ env ∧ F.Holds ψ ρ env) := Iff.rfl
theorem holds_disj (φ ψ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (φ.disj ψ) ρ env ↔ (F.Holds φ ρ env ∨ F.Holds ψ ρ env) := Iff.rfl
theorem holds_iff (φ ψ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (φ.iff ψ) ρ env ↔ (F.Holds φ ρ env ↔ F.Holds ψ ρ env) := Iff.rfl

theorem holds_inst {k : Nat} (P : PF k) (as : Fin k → Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (P.inst as) ρ env ↔ P.evalP (fun i => F.Holds (as i) ρ env) := by
  induction P with
  | atom i => exact Iff.rfl
  | neg P ih => exact not_congr ih
  | imp P Q ihP ihQ => exact imp_congr ihP ihQ
  | conj P Q ihP ihQ => exact and_congr ihP ihQ
  | disj P Q ihP ihQ => exact or_congr ihP ihQ
  | iff P Q ihP ihQ => exact iff_congr ihP ihQ

theorem app2_heq {A A' B B' C : Type} (hA : A = A') (hB : B = B') {f : A → B → C} {g : A' → B' → C}
    (h : HEq f g) (x : A) (y : B) : f x y = g (cast hA x) (cast hB y) := by
  subst hA; subst hB; rw [eq_of_heq h]; rfl

/-- The value of `≡_{σ,τ}`. -/
theorem eval_eqvConst (σ τ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    HEq (F.eval (Tm.castK (Tm.eqv_cat σ τ) (Tm.tapp (Tm.tapp (Tm.const (Γ := Γ) Const.eqv) σ) τ)) ρ env)
      (fun x y => F.eqv (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) x y) := by
  refine (F.eval_castK _ _ _ _).trans ((cast_heq _ _).trans ?_)
  refine heq_dapp (Q := fun b => F.U.El (F.U.code σ.1 ρ) → F.U.El b → F.U.W → Prop) (fun b => ?_)
    (cast_heq _ _) rfl
  refine Univ.CatVal_sub _ _ _ (scons b (scons (F.U.code σ.1 ρ) ρ)) (fin_cases rfl (fun i => ?_))
  show F.U.code (((inst σ) i).1.ren fs) (scons b ρ) = _
  rw [Univ.code_ren]
  exact fin_cases (P := fun i => F.U.code (inst σ i).1 ρ = scons (F.U.code σ.1 ρ) ρ i) rfl (fun _ => rfl) i

/-- The value of `x ≡_{σ,τ} y`. -/
theorem eval_eqv (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.eval (Tm.eqv σ τ x y) ρ env =
      F.eqv (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) (cast (Univ.El_code ρ σ.2).symm (F.eval x ρ env))
        (cast (Univ.El_code ρ τ.2).symm (F.eval y ρ env)) :=
  (app2_heq (A := F.U.CatVal σ.1 ρ) (B := F.U.CatVal τ.1 ρ)
    (f := F.eval (Tm.castK (Tm.eqv_cat σ τ) (Tm.tapp (Tm.tapp (Tm.const Const.eqv) σ) τ)) ρ env)
    (Univ.El_code ρ σ.2).symm (Univ.El_code ρ τ.2).symm (F.eval_eqvConst σ τ ρ env) _ _)

/-- The truth value of `x ≡_{σ,τ} y`. -/
theorem holdsAt_eqv (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (Tm.eqv σ τ x y) ρ env w ↔
      F.eqv (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) (cast (Univ.El_code ρ σ.2).symm (F.eval x ρ env))
        (cast (Univ.El_code ρ τ.2).symm (F.eval y ρ env)) w :=
  Iff.of_eq (congrFun (F.eval_eqv σ τ x y ρ env) w)

theorem holds_eqv (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.eqv σ τ x y) ρ env ↔
      F.eqv (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) (cast (Univ.El_code ρ σ.2).symm (F.eval x ρ env))
        (cast (Univ.El_code ρ τ.2).symm (F.eval y ρ env)) F.U.w0 :=
  F.holdsAt_eqv σ τ x y ρ env _

/-- The value of `σ ≈ τ`. -/
theorem eval_teq (σ τ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.eval (Tm.teq σ τ) ρ env = F.teq (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) := by
  have h1 : HEq (F.eval (Tm.tapp (Tm.const (Γ := Γ) Const.teq) σ) ρ env) (fun b => F.teq (F.U.code σ.1 ρ) b) :=
    F.heq_eval_tapp _ σ ρ env
  have h2 : HEq (F.eval (Tm.teq (Γ := Γ) σ τ) ρ env)
      (F.eval (Tm.tapp (Tm.const (Γ := Γ) Const.teq) σ) ρ env (F.U.code τ.1 ρ)) := F.heq_eval_tapp _ τ ρ env
  exact eq_of_heq (h2.trans (heq_dapp (Q := fun _ => F.U.W → Prop) (fun _ => rfl) h1 rfl))

theorem holdsAt_teq (σ τ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (Tm.teq σ τ) ρ env w ↔ F.teq (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) w :=
  Iff.of_eq (congrFun (F.eval_teq σ τ ρ env) w)

theorem holds_teq (σ τ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.teq σ τ) ρ env ↔ F.teq (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) F.U.w0 :=
  F.holdsAt_teq σ τ ρ env _

end EvalLemmas

/-- Pull the values of a renamed context back along the renaming. -/
def pullEnv : {n : Nat} → (Γ : Ctx n) → {m : Nat} → {r : Fin n → Fin m} → {Δ : Ctx m} →
    TRen r Γ Δ → (ρ' : F.U.TEnv m) → F.U.Env Δ ρ' → F.U.Env Γ (fun i => ρ' (r i))
  | _, .nil, _, _, _, _, _, _ => ()
  | _, .ext Γ σ, _, r, _, ρr, ρ', env' =>
      (pullEnv Γ (fun x => ρr (.there x)) ρ' env',
       cast (Univ.CatVal_ren σ.1 r ρ' _ (fun _ => rfl)) (F.U.lookup (ρr .here) ρ' env'))
  | _, .text Γ, _, r, _, ρr, ρ', env' =>
      pullEnv Γ (r := fun i => r (fs i)) (fun x => Var.castK (Cat.ren_ren _ _ _) (ρr (.tthere x))) ρ' env'

theorem lookup_pull {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) :
    ∀ {m : Nat} {r : Fin n → Fin m} {Δ : Ctx m} (ρr : TRen r Γ Δ) (ρ' : F.U.TEnv m) (env' : F.U.Env Δ ρ'),
      HEq (F.U.lookup (ρr x) ρ' env') (F.U.lookup x _ (F.pullEnv Γ ρr ρ' env')) := by
  induction x with
  | here => intro m r Δ ρr ρ' env'; exact (cast_heq _ _).symm
  | there y ih => intro m r Δ ρr ρ' env'; exact ih (fun x => ρr (.there x)) ρ' env'
  | tthere y ih =>
    intro m r Δ ρr ρ' env'
    refine HEq.trans ?_ (F.lookup_tthere y (fun i => ρ' (r i)) (F.pullEnv _ ρr ρ' env')).symm
    exact (F.lookup_castK _ _ _ _).symm.trans
      (ih (r := fun i => r (fs i)) (fun x => Var.castK (Cat.ren_ren _ _ _) (ρr (.tthere x))) ρ' env')

theorem holds_of_heq {n m : Nat} {Γ : Ctx n} {Δ : Ctx m} {φ : Fm Γ} {ψ : Fm Δ} {ρ : F.U.TEnv n}
    {ρ' : F.U.TEnv m} {env : F.U.Env Γ ρ} {env' : F.U.Env Δ ρ'} (h : HEq (F.eval φ ρ env) (F.eval ψ ρ' env')) :
    F.Holds φ ρ env = F.Holds ψ ρ' env' :=
  congrArg (fun f : F.U.CatVal Cat.t ρ => F.U.ap f F.U.w0) (eq_of_heq h)

/-- What a frame must satisfy to be a model of PI⁻: the identity axioms other than LL≡ are true,
and every instance of LL≈ is valid. -/
structure IsModelPIm : Prop where
  refEqv : F.Valid RefEqv
  symEqv : F.Valid SymEqv
  transEqv : F.Valid TransEqv
  refTeq : F.Valid RefTeq
  llTeq : ∀ {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)), F.Valid (LLTeq Q)

/-- **Soundness.** Whatever PI⁻ + `Ax` derives is valid in every model of PI⁻ in which the
sentences `Ax` are true. -/
theorem soundness {Ax : Fm Ctx.nil → Prop} (hM : F.IsModelPIm) (hAx : ∀ φ, Ax φ → F.Valid φ)
    {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : Prov Ax Γ φ) : F.Valid φ := by
  induction h with
  | taut P as hP => intro ρ env; exact (F.holds_inst P as ρ env).mpr (hP _)
  | instAll σ φ κ =>
    intro ρ env h
    show F.Holds (φ.subst0 κ) ρ env
    unfold Holds; rw [eval_subst0]; exact (F.holds_all σ φ ρ env).mp h _
  | distAll σ φ ψ =>
    intro ρ env h hφ
    refine (F.holds_all σ ψ ρ env).mpr fun v => ?_
    have h' := (F.holds_all σ _ ρ env).mp h v
    have hw : F.Holds (φ.wk σ) ρ (env, v) := by unfold Holds; rw [eval_wk]; exact hφ
    exact h' hw
  | dualEx σ φ =>
    intro ρ env
    refine (F.holds_ex σ φ ρ env).trans ?_
    refine Iff.trans ?_ (not_congr (F.holds_all σ φ.neg ρ env)).symm
    constructor
    · rintro ⟨v, hv⟩ h; exact h v hv
    · intro h; exact Classical.byContradiction fun hn => h fun v hv => hn ⟨v, hv⟩
  | instTAll φ σ =>
    intro ρ env h
    exact cast ((congrArg (fun f : F.U.W → Prop => f F.U.w0)) (eq_of_heq (F.eval_tinst φ σ ρ env))).symm (h (F.U.code σ.1 ρ))
  | distTAll φ ψ =>
    intro ρ env h hφ a
    exact h a (cast ((congrArg (fun f : F.U.W → Prop => f F.U.w0)) (eq_of_heq (F.eval_twk φ a ρ env))).symm hφ)
  | dualTEx φ =>
    intro ρ env
    show (∃ a, F.Holds φ (scons a ρ) env) ↔ ¬ ∀ a, ¬ F.Holds φ (scons a ρ) env
    constructor
    · rintro ⟨a, ha⟩ h; exact h a ha
    · intro h; exact Classical.byContradiction fun hn => h fun a ha => hn ⟨a, ha⟩
  | beta h => intro ρ env; exact Iff.of_eq ((congrArg (fun f : F.U.W → Prop => f F.U.w0)) (F.eval_betaEq h ρ env))
  | refEqv => exact hM.refEqv
  | symEqv => exact hM.symEqv
  | transEqv => exact hM.transEqv
  | refTeq => exact hM.refTeq
  | llTeq Q => exact hM.llTeq Q
  | ax h => exact hAx _ h
  | mp _ _ ih1 ih2 => intro ρ env; exact ih2 ρ env (ih1 ρ env)
  | genAll σ _ ih => intro ρ env; exact (F.holds_all σ _ ρ env).mpr fun v => ih ρ (env, v)
  | genTAll _ ih => intro ρ env a; exact ih (scons a ρ) env
  | ren ρr _ ih =>
    intro ρ' env'
    exact cast (F.holds_of_heq (F.eval_ren _ ρr ρ' env' _ (F.pullEnv _ ρr ρ' env') (fun _ => rfl)
      (fun x => F.lookup_pull x ρr ρ' env'))).symm (ih _ _)
  | strengthen σ _ ih =>
    intro ρ env
    have v := Classical.choice (Univ.CatVal_nonempty σ.1 ρ)
    have := ih ρ (env, v)
    unfold Holds at this
    rwa [eval_wk] at this
  | tstrengthen _ ih =>
    intro ρ env
    exact cast (F.holds_of_heq (F.eval_twk _ .e ρ env)) (ih (scons .e ρ) env)

/-- A model of PI: a model of PI⁻ in which LL≡ is true. -/
theorem soundness_PI {S : Fm Ctx.nil → Prop} (hM : F.IsModelPIm) (hLL : F.Valid LLEqv)
    (hS : ∀ φ, S φ → F.Valid φ) {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : PI S Γ φ) : F.Valid φ :=
  F.soundness hM (fun ψ hψ => hψ.elim (fun e => e ▸ hLL) (hS ψ)) h

/-- `⊥` is false in every frame. -/
theorem not_valid_bot : ¬ F.Valid Bot := fun h =>
  (F.holds_all (Γ := Ctx.nil) tyT _ (fun i => i.elim0) ()).mp (h _ ()) (fun _ => False)

/-- So a theory with a model is consistent. -/
theorem consistent_of_model {Ax : Fm Ctx.nil → Prop} (hM : F.IsModelPIm) (hAx : ∀ φ, Ax φ → F.Valid φ) :
    ¬ Prov Ax Ctx.nil Bot := fun h => F.not_valid_bot (F.soundness hM hAx h)

/-- A frame in which `≈` implies identity of codes validates every instance of LL≈. -/
theorem llTeq_of_teq_eq (hteq : ∀ a b, F.teq a b F.U.w0 → a = b) {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)) :
    F.Valid (LLTeq Q) := by
  intro ρ env a b hab
  have hab' : a = b := hteq _ _ ((F.holds_teq (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env).mp hab)
  subst hab'
  intro hq
  have e1 : HEq (F.eval (Tm.tapp Q.twk.twk tv1) (scons a (scons a ρ)) env)
      (F.eval Q.twk.twk (scons a (scons a ρ)) env a) := F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv1 (scons a (scons a ρ)) env
  have e2 : HEq (F.eval (Tm.tapp Q.twk.twk tv0) (scons a (scons a ρ)) env)
      (F.eval Q.twk.twk (scons a (scons a ρ)) env a) := F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv0 (scons a (scons a ρ)) env
  exact cast ((congrArg (fun f : F.U.W → Prop => f F.U.w0)) (eq_of_heq (e1.trans e2.symm))) hq

end Frame


namespace Frame
variable (F : Frame)

/-- A frame in which `≈` is identity and `≡` is an equivalence relation is a model of PI⁻. -/
theorem model_of_equiv (hteq : ∀ a b, F.teq a b F.U.w0 ↔ a = b) (hr : ∀ a x, F.eqv a a x x F.U.w0)
    (hs : ∀ a b x y, F.eqv a b x y F.U.w0 → F.eqv b a y x F.U.w0)
    (ht : ∀ a b c x y z, F.eqv a b x y F.U.w0 → F.eqv b c y z F.U.w0 → F.eqv a c x z F.U.w0) : F.IsModelPIm where
  refEqv := by
    intro ρ env a
    exact (F.holds_all _ _ _ _).mpr fun v => (F.holds_eqv _ _ _ _ _ _).mpr (hr _ _)
  symEqv := by
    intro ρ env a b
    refine (F.holds_all _ _ _ _).mpr fun x => (F.holds_all _ _ _ _).mpr fun y h => ?_
    exact (F.holds_eqv _ _ _ _ _ _).mpr (hs _ _ _ _ ((F.holds_eqv _ _ _ _ _ _).mp h))
  transEqv := by
    intro ρ env a b c
    refine (F.holds_all _ _ _ _).mpr fun x => (F.holds_all _ _ _ _).mpr fun y =>
      (F.holds_all _ _ _ _).mpr fun z h => ?_
    have h1 := (F.holds_eqv (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv2 tv1
      (.var (.there (.there .here))) (.var (.there .here)) (scons c (scons b (scons a ρ))) (((env, x), y), z)).mp h.1
    have h2 := (F.holds_eqv (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv1 tv0
      (.var (.there .here)) (.var .here) (scons c (scons b (scons a ρ))) (((env, x), y), z)).mp h.2
    exact (F.holds_eqv _ _ _ _ _ _).mpr (ht _ _ _ _ _ _ h1 h2)
  refTeq := by
    intro ρ env a
    exact (F.holds_teq _ _ _ _).mpr ((hteq _ _).mpr rfl)
  llTeq := fun Q => F.llTeq_of_teq_eq (fun _ _ h => (hteq _ _).mp h) Q

end Frame


/-! ## General facts -/

namespace Frame
variable (F : Frame)

theorem holdsAt_neg {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt φ.neg ρ env w ↔ ¬ F.HoldsAt φ ρ env w := Iff.rfl

theorem holdsAt_imp {n : Nat} {Γ : Ctx n} (φ ψ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (φ.imp ψ) ρ env w ↔ (F.HoldsAt φ ρ env w → F.HoldsAt ψ ρ env w) := Iff.rfl

theorem holdsAt_eqv_t {n : Nat} {Γ : Ctx n} (x y : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (Tm.eqv tyT tyT x y) ρ env w ↔ F.eqv .t .t (F.eval x ρ env) (F.eval y ρ env) w :=
  F.holdsAt_eqv tyT tyT x y ρ env w

theorem eval_botF {n : Nat} {Γ : Ctx n} (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.eval (botF : Fm Γ) ρ env = fun _ => False :=
  funext fun w => propext ⟨fun h => (F.holdsAt_all (Γ := Γ) tyT (.var .here) ρ env w).mp h (fun _ => False),
    fun h => h.elim⟩

theorem eval_topF {n : Nat} {Γ : Ctx n} (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.eval (topF : Fm Γ) ρ env = fun _ => True :=
  funext fun w => propext ⟨fun _ => trivial, fun _ h => by
    have e := congrFun (F.eval_botF (Γ := Γ) ρ env) w
    exact (cast e h : False)⟩

theorem holdsAt_inst {n : Nat} {Γ : Ctx n} {k : Nat} (P : PF k) (as : Fin k → Fm Γ) (ρ : F.U.TEnv n)
    (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (P.inst as) ρ env w ↔ P.evalP (fun i => F.HoldsAt (as i) ρ env w) := by
  induction P with
  | atom i => exact Iff.rfl
  | neg P ih => exact not_congr ih
  | imp P Q ihP ihQ => exact imp_congr ihP ihQ
  | conj P Q ihP ihQ => exact and_congr ihP ihQ
  | disj P Q ihP ihQ => exact or_congr ihP ihQ
  | iff P Q ihP ihQ => exact iff_congr ihP ihQ

theorem holds_closeAll : ∀ (k : Nat) (φ : Fm (ctxT k)) (ρ : F.U.TEnv 0),
    (∀ env : F.U.Env (ctxT k) ρ, F.Holds φ ρ env) → ∀ env0 : F.U.Env Ctx.nil ρ, F.Holds (closeAll k φ) ρ env0
  | 0, _, _, h, env0 => h env0
  | k + 1, φ, ρ, h, env0 =>
    holds_closeAll k (Tm.all tyT φ) ρ (fun env => (F.holds_all tyT φ ρ env).mpr fun v => h (env, v)) env0

/-- Booleanism holds in every frame in which each proposition is identified with itself. -/
theorem bool_valid (hr : ∀ x, F.eqv .t .t x x F.U.w0) : ∀ φ, BoolSch φ → F.Valid φ := by
  rintro _ ⟨k, P, Q, hT, rfl⟩ ρ env0
  refine F.holds_closeAll k _ ρ (fun env => ?_) env0
  have e : F.eval (P.inst (varsT k)) ρ env = F.eval (Q.inst (varsT k)) ρ env :=
    funext fun w => propext ((F.holdsAt_inst P _ ρ env w).trans ((hT _).trans (F.holdsAt_inst Q _ ρ env w).symm))
  refine (F.holdsAt_eqv_t _ _ ρ env _).mpr ?_
  rw [e]; exact hr _

end Frame

/-! ## Models with rigid or contingent identity -/

abbrev univW (W : Type) (w0 : W) : Univ :=
  { W := W, w0 := w0, E := Unit, Base := Empty, B := Empty.elim, neE := ⟨()⟩, neB := fun b => b.elim }

/-- Data for a model in which items are identified with themselves at the worlds where `Ee` holds,
and types are identified as `Te` says. -/
structure RD where
  W : Type
  w0 : W
  Ee : W → Prop
  Te : Code Empty → Code Empty → W → Prop
  hE : Ee w0
  hT : ∀ a b, Te a b w0 ↔ a = b

namespace RD
variable (D : RD)

def frame : Frame where
  U := univW D.W D.w0
  eqv := fun a b x y w => a = b ∧ HEq x y ∧ D.Ee w
  teq := D.Te

theorem model : D.frame.IsModelPIm :=
  D.frame.model_of_equiv D.hT (fun _ _ => ⟨rfl, HEq.rfl, D.hE⟩)
    (fun _ _ _ _ h => ⟨h.1.symm, h.2.1.symm, h.2.2⟩)
    (fun _ _ _ _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2⟩)

theorem holds_eqv_t {n : Nat} {Γ : Ctx n} (x y : Fm Γ) (ρ : D.frame.U.TEnv n) (env : D.frame.U.Env Γ ρ) :
    D.frame.Holds (Tm.eqv tyT tyT x y) ρ env ↔ D.frame.eqv .t .t (D.frame.eval x ρ env) (D.frame.eval y ρ env) D.w0 :=
  D.frame.holdsAt_eqv_t x y ρ env _

theorem LLEqv_valid : D.frame.Valid LLEqv := by
  intro ρ env
  refine (D.frame.holds_tall _ _ _).mpr fun a => ?_
  refine (D.frame.holds_all _ _ _ _).mpr fun x => (D.frame.holds_all _ _ _ _).mpr fun y => ?_
  refine (D.frame.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (D.frame.holds_all _ _ _ _).mpr fun G => (D.frame.holds_imp _ _ _ _).mpr fun hGx => ?_
  have h := ((D.frame.holds_eqv _ _ _ _ _ _).mp hxy).2.1
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.trans (cast_heq _ _)))
  subst e
  exact hGx

theorem Truth_valid : D.frame.Valid Truth := by
  intro ρ env
  refine (D.frame.holds_all _ _ _ _).mpr fun p => (D.frame.holds_all _ _ _ _).mpr fun q => ?_
  refine (D.frame.holds_imp _ _ _ _).mpr fun h => (D.frame.holds_imp _ _ _ _).mpr fun hp => ?_
  have e := eq_of_heq ((D.holds_eqv_t _ _ _ _).mp h).2.1
  exact cast (congrArg (fun f => D.frame.U.ap (n := 0) (ρ := ρ) f D.w0) e) hp

theorem Bool_valid : ∀ φ, BoolSch φ → D.frame.Valid φ := D.frame.bool_valid fun _ => ⟨rfl, HEq.rfl, D.hE⟩

theorem holds_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : D.frame.U.TEnv n) (env : D.frame.U.Env Γ ρ) :
    D.frame.Holds (boxF φ) ρ env ↔ ∀ w, D.frame.HoldsAt φ ρ env w := by
  refine (D.frame.holdsAt_eqv_t φ topF ρ env D.w0).trans ?_
  rw [D.frame.eval_topF]
  constructor
  · rintro ⟨_, h, _⟩ w
    show D.frame.U.ap (D.frame.eval φ ρ env) w
    rw [eq_of_heq h]; exact trivial
  · intro h; exact ⟨rfl, heq_of_eq (funext fun w => propext ⟨fun _ => trivial, fun _ => h w⟩), D.hE⟩

theorem Disjoint_valid : D.frame.Valid Disjoint := by
  intro ρ env
  refine (D.frame.holds_tall _ _ _).mpr fun a => (D.frame.holds_tall _ _ _).mpr fun b => ?_
  refine (D.frame.holds_imp _ _ _ _).mpr fun hn => ?_
  refine (D.frame.holds_all _ _ _ _).mpr fun x => (D.frame.holds_all _ _ _ _).mpr fun y => ?_
  refine (D.frame.holds_neg _ _ _).mpr fun hxy => ?_
  have hab := ((D.frame.holds_eqv _ _ _ _ _ _).mp hxy).1
  exact (D.frame.holds_neg _ _ _).mp hn ((D.frame.holds_teq _ _ _ _).mpr ((D.hT _ _).mpr hab))

theorem NIEqv_valid (hEall : ∀ w, D.Ee w) : D.frame.Valid NIEqv := by
  intro ρ env
  refine (D.frame.holds_tall _ _ _).mpr fun a => ?_
  refine (D.frame.holds_all _ _ _ _).mpr fun x => (D.frame.holds_all _ _ _ _).mpr fun y => ?_
  refine (D.frame.holds_imp _ _ _ _).mpr fun hxy => ?_
  have h := (D.frame.holds_eqv _ _ _ _ _ _).mp hxy
  exact (D.holds_box _ _ _).mpr fun w => (D.frame.holdsAt_eqv _ _ _ _ _ _ w).mpr ⟨rfl, h.2.1, hEall w⟩

theorem not_NIEqv (w1 : D.W) (h1 : ¬ D.Ee w1) : ¬ D.frame.Valid NIEqv := fun h => by
  have h0 := (D.frame.holds_all _ _ _ _).mp ((D.frame.holds_all _ _ _ _).mp
    ((D.frame.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have hb := (D.frame.holds_imp _ _ _ _).mp h0 ((D.frame.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl, D.hE⟩)
  exact h1 ((D.frame.holdsAt_eqv _ _ _ _ _ _ w1).mp ((D.holds_box _ _ _).mp hb w1)).2.2

theorem NITeq_valid (hall : ∀ a b w, D.Te a b D.w0 → D.Te a b w) : D.frame.Valid NITeq := by
  intro ρ env
  refine (D.frame.holds_tall _ _ _).mpr fun a => (D.frame.holds_tall _ _ _).mpr fun b => ?_
  refine (D.frame.holds_imp _ _ _ _).mpr fun h => ?_
  have h' := (D.frame.holds_teq _ _ _ _).mp h
  exact (D.holds_box _ _ _).mpr fun w => (D.frame.holdsAt_teq _ _ _ _ w).mpr (hall a b w h')

theorem not_NITeq (a : Code Empty) (w1 : D.W) (h1 : ¬ D.Te a a w1) : ¬ D.frame.Valid NITeq := fun h => by
  have h0 := (D.frame.holds_tall _ _ _).mp ((D.frame.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) a) a
  have hb := (D.frame.holds_imp _ _ _ _).mp h0 ((D.frame.holds_teq _ _ _ _).mpr ((D.hT a a).mpr rfl))
  exact h1 ((D.frame.holdsAt_teq _ _ _ _ w1).mp ((D.holds_box _ _ _).mp hb w1))

theorem NDTeq_valid (hall : ∀ a b w, D.Te a b w → a = b) : D.frame.Valid NDTeq := by
  intro ρ env
  refine (D.frame.holds_tall _ _ _).mpr fun a => (D.frame.holds_tall _ _ _).mpr fun b => ?_
  refine (D.frame.holds_imp _ _ _ _).mpr fun hn => ?_
  refine (D.holds_box _ _ _).mpr fun w => (D.frame.holdsAt_neg _ _ _ w).mpr fun ht => ?_
  have := hall a b w ((D.frame.holdsAt_teq _ _ _ _ w).mp ht)
  exact (D.frame.holds_neg _ _ _).mp hn ((D.frame.holds_teq _ _ _ _).mpr ((D.hT a b).mpr this))

theorem not_NDTeq (a b : Code Empty) (w1 : D.W) (hab : a ≠ b) (h1 : D.Te a b w1) : ¬ D.frame.Valid NDTeq := fun h => by
  have h0 := (D.frame.holds_tall _ _ _).mp ((D.frame.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) a) b
  have hb := (D.frame.holds_imp _ _ _ _).mp h0
    ((D.frame.holds_neg _ _ _).mpr fun ht => hab ((D.hT a b).mp ((D.frame.holds_teq _ _ _ _).mp ht)))
  exact (D.frame.holdsAt_neg _ _ _ w1).mp ((D.holds_box _ _ _).mp hb w1) ((D.frame.holdsAt_teq _ _ _ _ w1).mpr h1)

theorem not_Collapse (w1 : D.W) (h1 : w1 ≠ D.w0) : ¬ D.frame.Valid Collapse := fun h => by
  have h0 := (D.frame.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (fun w => w = D.w0)
  have hb := (D.frame.holds_imp _ _ _ _).mp h0 (show D.w0 = D.w0 from rfl)
  exact h1 ((D.holds_box _ _ _).mp hb w1)

theorem not_PropExt (w1 : D.W) (h1 : w1 ≠ D.w0) : ¬ D.frame.Valid PropExt := fun h => by
  have h0 := (D.frame.holds_all _ _ _ _).mp ((D.frame.holds_all _ _ _ _).mp (h (fun i => i.elim0) ())
    (fun w => w = D.w0)) (fun _ => True)
  have hb := (D.frame.holds_imp _ _ _ _).mp h0
    ((D.frame.holds_iff _ _ _ _).mpr ⟨fun _ => trivial, fun _ => (show D.w0 = D.w0 from rfl)⟩)
  have e := eq_of_heq ((D.holds_eqv_t _ _ _ _).mp hb).2.1
  exact h1 (cast (congrFun e w1).symm trivial)

abbrev Ex : Fm (((Ctx.nil.text).ext tv0).ext tv0) := Tm.eqv tv0 tv0 (.var (.there .here)) (.var .here)
abbrev Ax' : Fm (((Ctx.nil.text).ext tv0).ext tv0) := Tm.all tv0.pred (Tm.imp (.app (.var .here) (.var (.there (.there .here))))
  (.app (.var .here) (.var (.there .here))))

theorem IdId_valid (hEall : ∀ w, D.Ee w) : D.frame.Valid IdId := by
  intro ρ env
  refine (D.frame.holds_tall _ _ _).mpr fun a => ?_
  refine (D.frame.holds_all _ _ _ _).mpr fun x => (D.frame.holds_all _ _ _ _).mpr fun y => ?_
  have key : ∀ w, D.frame.HoldsAt Ex (scons a ρ) ((env, x), y) w ↔ D.frame.HoldsAt Ax' (scons a ρ) ((env, x), y) w := by
    intro w
    refine (D.frame.holdsAt_eqv _ _ _ _ _ _ w).trans ⟨fun h => ?_, fun h => ?_⟩
    · have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.2.1.trans (cast_heq _ _)))
      subst e
      exact (D.frame.holdsAt_all _ _ _ _ w).mpr fun G => (D.frame.holdsAt_imp _ _ _ _ w).mpr id
    · have hG := (D.frame.holdsAt_imp _ _ _ _ w).mp ((D.frame.holdsAt_all _ _ _ _ w).mp h (fun z _ => z = x)) rfl
      have e : y = x := hG
      subst e
      exact ⟨rfl, HEq.rfl, hEall w⟩
  exact (D.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq (funext fun w => propext (key w)), D.hE⟩

theorem not_IdId (w1 : D.W) (h1 : ¬ D.Ee w1) : ¬ D.frame.Valid IdId := fun h => by
  have h0 := (D.frame.holds_all _ _ _ _).mp ((D.frame.holds_all _ _ _ _).mp
    ((D.frame.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have e := eq_of_heq ((D.holds_eqv_t _ _ _ _).mp h0).2.1
  have hA : D.frame.HoldsAt (Ax' : Fm (((Ctx.nil.text).ext tv0).ext tv0)) (scons .e (fun i => i.elim0)) (((), ()), ()) w1 :=
    (D.frame.holdsAt_all _ _ _ _ w1).mpr fun G => (D.frame.holdsAt_imp _ _ _ _ w1).mpr id
  have hE : D.frame.HoldsAt (Ex : Fm (((Ctx.nil.text).ext tv0).ext tv0)) (scons .e (fun i => i.elim0)) (((), ()), ()) w1 :=
    cast (congrFun e w1).symm hA
  exact h1 ((D.frame.holdsAt_eqv _ _ _ _ _ _ w1).mp hE).2.2

end RD


/-! ## The models -/

/-- `𝔐_w`: two worlds, and identity of items and of types holds rigidly. -/
def DW : RD where
  W := Bool
  w0 := true
  Ee := fun _ => True
  Te := fun a b _ => a = b
  hE := trivial
  hT := fun _ _ => Iff.rfl

theorem Mw_model : DW.frame.IsModelPIm := DW.model
theorem Mw_LLEqv : DW.frame.Valid LLEqv := DW.LLEqv_valid
theorem Mw_Truth : DW.frame.Valid Truth := DW.Truth_valid
theorem Mw_Bool : ∀ φ, BoolSch φ → DW.frame.Valid φ := DW.Bool_valid
theorem Mw_IdId : DW.frame.Valid IdId := DW.IdId_valid fun _ => trivial
theorem Mw_NIEqv : DW.frame.Valid NIEqv := DW.NIEqv_valid fun _ => trivial
theorem Mw_NITeq : DW.frame.Valid NITeq := DW.NITeq_valid fun _ _ _ h => h
theorem Mw_NDTeq : DW.frame.Valid NDTeq := DW.NDTeq_valid fun _ _ _ h => h
theorem Mw_Disjoint : DW.frame.Valid Disjoint := DW.Disjoint_valid
theorem Mw_not_Collapse : ¬ DW.frame.Valid Collapse := DW.not_Collapse false Bool.false_ne_true
theorem Mw_not_PropExt : ¬ DW.frame.Valid PropExt := DW.not_PropExt false Bool.false_ne_true

/-- `𝔐_nd`: at the other world, all types are identified. -/
def DND : RD where
  W := Bool
  w0 := true
  Ee := fun _ => True
  Te := fun a b w => w = true → a = b
  hE := trivial
  hT := fun _ _ => ⟨fun h => h rfl, fun h _ => h⟩

theorem Mnd_model : DND.frame.IsModelPIm := DND.model
theorem Mnd_LLEqv : DND.frame.Valid LLEqv := DND.LLEqv_valid
theorem Mnd_Truth : DND.frame.Valid Truth := DND.Truth_valid
theorem Mnd_Bool : ∀ φ, BoolSch φ → DND.frame.Valid φ := DND.Bool_valid
theorem Mnd_IdId : DND.frame.Valid IdId := DND.IdId_valid fun _ => trivial
theorem Mnd_NIEqv : DND.frame.Valid NIEqv := DND.NIEqv_valid fun _ => trivial
theorem Mnd_NITeq : DND.frame.Valid NITeq := DND.NITeq_valid fun _ _ _ h _ => h rfl
theorem Mnd_not_NDTeq : ¬ DND.frame.Valid NDTeq :=
  DND.not_NDTeq .e .t false (fun h => nomatch h) (fun h => (Bool.false_ne_true h).elim)

/-- `𝔐_ni`: at the other world, no type is identified with anything. -/
def DNI : RD where
  W := Bool
  w0 := true
  Ee := fun _ => True
  Te := fun a b w => a = b ∧ w = true
  hE := trivial
  hT := fun _ _ => ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

theorem Mni_model : DNI.frame.IsModelPIm := DNI.model
theorem Mni_LLEqv : DNI.frame.Valid LLEqv := DNI.LLEqv_valid
theorem Mni_Truth : DNI.frame.Valid Truth := DNI.Truth_valid
theorem Mni_Bool : ∀ φ, BoolSch φ → DNI.frame.Valid φ := DNI.Bool_valid
theorem Mni_IdId : DNI.frame.Valid IdId := DNI.IdId_valid fun _ => trivial
theorem Mni_NIEqv : DNI.frame.Valid NIEqv := DNI.NIEqv_valid fun _ => trivial
theorem Mni_NDTeq : DNI.frame.Valid NDTeq := DNI.NDTeq_valid fun _ _ _ h => h.1
theorem Mni_not_NITeq : ¬ DNI.frame.Valid NITeq := DNI.not_NITeq .e false fun h => Bool.false_ne_true h.2

/-- `𝔐_ie`: at the other world, no item is identified with anything. -/
def DIE : RD where
  W := Bool
  w0 := true
  Ee := fun w => w = true
  Te := fun a b _ => a = b
  hE := rfl
  hT := fun _ _ => Iff.rfl

theorem Mie_model : DIE.frame.IsModelPIm := DIE.model
theorem Mie_LLEqv : DIE.frame.Valid LLEqv := DIE.LLEqv_valid
theorem Mie_Truth : DIE.frame.Valid Truth := DIE.Truth_valid
theorem Mie_Bool : ∀ φ, BoolSch φ → DIE.frame.Valid φ := DIE.Bool_valid
theorem Mie_NITeq : DIE.frame.Valid NITeq := DIE.NITeq_valid fun _ _ _ h => h
theorem Mie_NDTeq : DIE.frame.Valid NDTeq := DIE.NDTeq_valid fun _ _ _ h => h
theorem Mie_not_NIEqv : ¬ DIE.frame.Valid NIEqv := DIE.not_NIEqv false Bool.false_ne_true
theorem Mie_not_IdId : ¬ DIE.frame.Valid IdId := DIE.not_IdId false Bool.false_ne_true

/-! ### `𝔐_col`: Collapse without PropExt≡

Two worlds; all propositions true at the actual world are identified, and nothing else is
identified with anything but itself. -/

def Sc : (c : Code Empty) → (univW Bool true).El c → Prop
  | .t, x => x true
  | _, _ => False

def McolF : Frame where
  U := univW Bool true
  eqv := fun a b x y _ => a = b ∧ (HEq x y ∨ (Sc a x ∧ Sc b y))
  teq := fun a b _ => a = b

theorem Mcol_model : McolF.IsModelPIm :=
  McolF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => ⟨rfl, Or.inl HEq.rfl⟩)
    (fun _ _ _ _ h => ⟨h.1.symm, h.2.elim (fun e => Or.inl e.symm) (fun ⟨p, q⟩ => Or.inr ⟨q, p⟩)⟩)
    (fun a b c x y z h1 h2 => by
      obtain ⟨hab, e1⟩ := h1
      obtain ⟨hbc, e2⟩ := h2
      subst hab; subst hbc
      refine ⟨rfl, ?_⟩
      rcases e1 with e1 | ⟨s1, s2⟩ <;> rcases e2 with e2 | ⟨s3, s4⟩
      · exact Or.inl (e1.trans e2)
      · exact Or.inr ⟨eq_of_heq e1 ▸ s3, s4⟩
      · exact Or.inr ⟨s1, eq_of_heq e2 ▸ s2⟩
      · exact Or.inr ⟨s1, s4⟩)

theorem Mcol_Collapse : McolF.Valid Collapse := by
  intro ρ env
  refine (McolF.holds_all _ _ _ _).mpr fun p => (McolF.holds_imp _ _ _ _).mpr fun hp => ?_
  refine (McolF.holdsAt_eqv_t _ _ _ _ _).mpr ⟨rfl, Or.inr ⟨hp, ?_⟩⟩
  exact cast (congrFun (McolF.eval_topF (Γ := Ctx.nil.ext tyT) ρ (env, p)) true).symm trivial

theorem Mcol_Truth : McolF.Valid Truth := by
  intro ρ env
  refine (McolF.holds_all _ _ _ _).mpr fun p => (McolF.holds_all _ _ _ _).mpr fun q => ?_
  refine (McolF.holds_imp _ _ _ _).mpr fun h => (McolF.holds_imp _ _ _ _).mpr fun hp => ?_
  rcases ((McolF.holdsAt_eqv_t _ _ _ _ _).mp h).2 with e | ⟨_, hq⟩
  · exact cast (congrArg (fun f => McolF.U.ap (n := 0) (ρ := ρ) f true) (eq_of_heq e)) hp
  · exact hq

theorem Mcol_Bool : ∀ φ, BoolSch φ → McolF.Valid φ := McolF.bool_valid fun _ => ⟨rfl, Or.inl HEq.rfl⟩

theorem Mcol_not_PropExt : ¬ McolF.Valid PropExt := fun h => by
  have h0 := (McolF.holds_all _ _ _ _).mp ((McolF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ())
    (fun _ => False)) (fun w => w = false)
  have hb := (McolF.holds_imp _ _ _ _).mp h0
    ((McolF.holds_iff _ _ _ _).mpr ⟨fun h => h.elim, fun h => Bool.noConfusion (h : true = false)⟩)
  rcases ((McolF.holdsAt_eqv_t _ _ _ _ _).mp hb).2 with e | ⟨s, _⟩
  · exact cast (congrFun (eq_of_heq e) false).symm rfl
  · exact s

end Wd


/-! ## The new principles in the tagged models -/

namespace Tg

/-- In `𝔐_int`, `¬¬p` and `p` differ in their tags, so Booleanism fails. -/
theorem Mi_not_DNeg : ¬ MiF.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MiF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (True, false)
  have e := eq_of_heq ((MiF.holds_eqv_t _ _ _ _).mp h0).2
  exact Bool.noConfusion (congrArg Prod.snd e : true = false)

theorem Mi_not_Bool : ¬ ∀ φ, BoolSch φ → MiF.Valid φ := fun h => Mi_not_DNeg (h _ DNeg_bool)

/-- In `𝔐_int`, `x ≡ y` is not quantified and `∀F(Fx → Fy)` is, so they are never identical. -/
theorem Mi_not_IdId : ¬ MiF.Valid IdId := fun h => by
  have h0 := (MiF.holds_all _ _ _ _).mp ((MiF.holds_all _ _ _ _).mp
    ((MiF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have e := eq_of_heq ((MiF.holds_eqv_t _ _ _ _).mp h0).2
  have h1 := congrArg Prod.snd e
  have h2 := MiF.eval_all_snd (Γ := ((Ctx.nil.text).ext tv0).ext tv0) tv0.pred
    (Tm.imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))
    (scons .e fun i => i.elim0) (((), ()), ())
  exact Bool.noConfusion (h1.trans h2 : true = false)

/-- In `𝔐_it`, a false proposition with tag `true` is identified with `⊤`, so T fails. -/
theorem Mit_not_TAx : ¬ MitF.Valid TAx := fun h => by
  have h0 := (MitF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (False, true)
  exact (MitF.holds_imp _ _ _ _).mp h0 ((MitF.holds_eqv_t _ _ _ _).mpr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)

/-- In `𝔐_tb`, only `⊤` itself is identified with `⊤`, so T holds (although Truth fails). -/
theorem Mtb_TAx : MtbF.Valid TAx := by
  intro ρ env
  refine (MtbF.holds_all _ _ _ _).mpr fun p => (MtbF.holds_imp _ _ _ _).mpr fun hb => ?_
  rcases ((MtbF.holds_eqv_t _ _ _ _).mp hb).2 with e | ⟨_, s⟩
  · have e' := eq_of_heq e
    show p.1
    rw [show p = MtbF.eval (topF : Fm (Ctx.nil.ext tyT)) ρ (env, p) from e']
    exact (MtbF.holds_neg _ _ _).mpr fun hb' => (MtbF.holds_all _ _ _ _).mp hb' (False, true)
  · exact Bool.noConfusion (s : true = false)

end Tg

end PIF
