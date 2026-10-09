import PIWorlds

/-!
# An algebraic semantics

The most general semantics with full function spaces used on this site. The items of type `t` form
an arbitrary non-empty set `P` with a truth predicate `V`; each frame supplies the operations for
the connectives and quantifiers, and the values of `≡` and `≈`, subject only to the truth
conditions (`V (neg p) ↔ ¬ V p`, `V (all a f) ↔ ∀ x, V (f x)`, and so on). A formula is true when its
value satisfies `V`. The semantics of the notes, the tagged semantics, and the sets-of-worlds
semantics are special cases. This file repeats the soundness proof for these models.
-/
set_option autoImplicit false

namespace PIF
namespace Al

structure Univ where
  P : Type
  V : P → Prop
  p0 : P
  E : Type
  Base : Type
  B : Base → Type
  neE : Nonempty E
  neB : ∀ b, Nonempty (B b)

/-- The set a code names. -/
def Univ.El (U : Univ) : Code U.Base → Type
  | .e => U.E
  | .t => U.P
  | .base b => U.B b
  | .arr a c => U.El a → U.El c

structure Frame where
  U : Univ
  /-- the value of `≡`, at each pair of members of the universe -/
  eqv : (a b : Code U.Base) → U.El a → U.El b → U.P
  /-- the value of `≈` -/
  teq : Code U.Base → Code U.Base → U.P
  neg : U.P → U.P
  imp : U.P → U.P → U.P
  cnj : U.P → U.P → U.P
  dsj : U.P → U.P → U.P
  bic : U.P → U.P → U.P
  all : (a : Code U.Base) → (U.El a → U.P) → U.P
  ex : (a : Code U.Base) → (U.El a → U.P) → U.P
  tall : (Code U.Base → U.P) → U.P
  tex : (Code U.Base → U.P) → U.P
  hneg : ∀ p, U.V (neg p) ↔ ¬ U.V p
  himp : ∀ p q, U.V (imp p q) ↔ (U.V p → U.V q)
  hcnj : ∀ p q, U.V (cnj p q) ↔ (U.V p ∧ U.V q)
  hdsj : ∀ p q, U.V (dsj p q) ↔ (U.V p ∨ U.V q)
  hbic : ∀ p q, U.V (bic p q) ↔ (U.V p ↔ U.V q)
  hall : ∀ a f, U.V (all a f) ↔ ∀ x, U.V (f x)
  hex : ∀ a f, U.V (ex a f) ↔ ∃ x, U.V (f x)
  htall : ∀ Q, U.V (tall Q) ↔ ∀ a, U.V (Q a)
  htex : ∀ Q, U.V (tex Q) ↔ ∃ a, U.V (Q a)

namespace Univ
variable (U : Univ)

/-- Valuations of type variables. -/
abbrev TEnv (n : Nat) := Fin n → Code U.Base

/-- The semantic value of a category. -/
def CatVal {n : Nat} : Cat n → U.TEnv n → Type
  | .e, _ => U.E
  | .t, _ => U.P
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
  | .t => ⟨U.p0⟩
  | .base b => U.neB b
  | .arr _ c => let ⟨y⟩ := El_nonempty c; ⟨fun _ => y⟩

theorem CatVal_nonempty {n : Nat} (K : Cat n) : ∀ ρ : U.TEnv n, Nonempty (U.CatVal K ρ) := by
  induction K with
  | e => intro; exact U.neE
  | t => intro; exact ⟨U.p0⟩
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

theorem tapp_eq {n : Nat} (K : Cat (n+1)) (σ : Ty n) (ρ : U.TEnv n) :
    U.CatVal K (scons (U.code σ.1 ρ) ρ) = U.CatVal (K.sub (inst σ)) ρ :=
  (CatVal_sub K (inst σ) ρ _ (fin_cases rfl (fun _ => rfl))).symm

end Univ

namespace Frame
variable (F : Frame)

/-- The values of the constants. -/
def constVal {n : Nat} {K : Cat n} (c : Const n K) (ρ : F.U.TEnv n) : F.U.CatVal K ρ :=
  match c with
  | .neg => F.neg
  | .imp => F.imp
  | .and => F.cnj
  | .or => F.dsj
  | .iff => F.bic
  | .all => fun a P => F.all a P
  | .ex => fun a P => F.ex a P
  | .tall => F.tall
  | .tex => F.tex
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

/-- The truth value of a formula under a valuation. -/
def Holds {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) : Prop := F.U.V (F.eval φ ρ env)

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

theorem holds_of_heq {m : Nat} {Δ : Ctx m} {φ : Fm Γ} {ψ : Fm Δ} {ρ : F.U.TEnv n} {ρ' : F.U.TEnv m}
    {env : F.U.Env Γ ρ} {env' : F.U.Env Δ ρ'} (h : HEq (F.eval φ ρ env) (F.eval ψ ρ' env')) :
    F.Holds φ ρ env = F.Holds ψ ρ' env' :=
  congrArg (fun p : F.U.P => F.U.V p) (eq_of_heq h)

theorem cast_all {c : Code F.U.Base} {A' : Type} (hA : F.U.El c = A') (h : ((F.U.El c → F.U.P) → F.U.P) = ((A' → F.U.P) → F.U.P))
    (Q : A' → F.U.P) : F.U.V (cast h (fun R => F.all c R) Q) ↔ ∀ x, F.U.V (Q x) := by
  subst hA; rw [cast_eq]; exact F.hall c Q

theorem cast_ex {c : Code F.U.Base} {A' : Type} (hA : F.U.El c = A') (h : ((F.U.El c → F.U.P) → F.U.P) = ((A' → F.U.P) → F.U.P))
    (Q : A' → F.U.P) : F.U.V (cast h (fun R => F.ex c R) Q) ↔ ∃ x, F.U.V (Q x) := by
  subst hA; rw [cast_eq]; exact F.hex c Q

theorem holds_all (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.all σ φ) ρ env ↔ ∀ v : F.U.CatVal σ.1 ρ, F.Holds φ ρ (env, v) :=
  F.cast_all (Univ.El_code ρ σ.2) _ _

theorem holds_ex (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.ex σ φ) ρ env ↔ ∃ v : F.U.CatVal σ.1 ρ, F.Holds φ ρ (env, v) :=
  F.cast_ex (Univ.El_code ρ σ.2) _ _

theorem holds_tall (φ : Fm (.text Γ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.tall φ) ρ env ↔ ∀ a, F.Holds φ (scons a ρ) env := F.htall _
theorem holds_tex (φ : Fm (.text Γ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.tex φ) ρ env ↔ ∃ a, F.Holds φ (scons a ρ) env := F.htex _
theorem holds_imp (φ ψ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (φ.imp ψ) ρ env ↔ (F.Holds φ ρ env → F.Holds ψ ρ env) := F.himp _ _
theorem holds_neg (φ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds φ.neg ρ env ↔ ¬ F.Holds φ ρ env := F.hneg _
theorem holds_conj (φ ψ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (φ.conj ψ) ρ env ↔ (F.Holds φ ρ env ∧ F.Holds ψ ρ env) := F.hcnj _ _
theorem holds_disj (φ ψ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (φ.disj ψ) ρ env ↔ (F.Holds φ ρ env ∨ F.Holds ψ ρ env) := F.hdsj _ _
theorem holds_iff (φ ψ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (φ.iff ψ) ρ env ↔ (F.Holds φ ρ env ↔ F.Holds ψ ρ env) := F.hbic _ _

theorem holds_inst {k : Nat} (P : PF k) (as : Fin k → Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (P.inst as) ρ env ↔ P.evalP (fun i => F.Holds (as i) ρ env) := by
  induction P with
  | atom i => exact Iff.rfl
  | neg P ih => exact (F.holds_neg _ ρ env).trans (not_congr ih)
  | imp P Q ihP ihQ => exact (F.holds_imp _ _ ρ env).trans (imp_congr ihP ihQ)
  | conj P Q ihP ihQ => exact (F.holds_conj _ _ ρ env).trans (and_congr ihP ihQ)
  | disj P Q ihP ihQ => exact (F.holds_disj _ _ ρ env).trans (or_congr ihP ihQ)
  | iff P Q ihP ihQ => exact (F.holds_iff _ _ ρ env).trans (iff_congr ihP ihQ)

theorem app2_heq {A A' B B' C : Type} (hA : A = A') (hB : B = B') {f : A → B → C} {g : A' → B' → C}
    (h : HEq f g) (x : A) (y : B) : f x y = g (cast hA x) (cast hB y) := by
  subst hA; subst hB; rw [eq_of_heq h]; rfl

theorem eval_tapp {K : Cat (n+1)} (f : Tm Γ (.pi K)) (σ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.eval (Tm.tapp f σ) ρ env = cast (F.U.tapp_eq K σ ρ) (F.eval f ρ env (F.U.code σ.1 ρ)) := rfl

theorem heq_eval_tapp {K : Cat (n+1)} (f : Tm Γ (.pi K)) (σ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    HEq (F.eval (Tm.tapp f σ) ρ env) (F.eval f ρ env (F.U.code σ.1 ρ)) :=
  (heq_of_eq (F.eval_tapp f σ ρ env)).trans (cast_heq _ _)

/-- The value of `≡_{σ,τ}`. -/
theorem eval_eqvConst (σ τ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    HEq (F.eval (Tm.castK (Tm.eqv_cat σ τ) (Tm.tapp (Tm.tapp (Tm.const (Γ := Γ) Const.eqv) σ) τ)) ρ env)
      (fun x y => F.eqv (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) x y) := by
  refine (F.eval_castK _ _ _ _).trans ((cast_heq _ _).trans ?_)
  refine heq_dapp (Q := fun b => F.U.El (F.U.code σ.1 ρ) → F.U.El b → F.U.P) (fun b => ?_)
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
  app2_heq (A := F.U.CatVal σ.1 ρ) (B := F.U.CatVal τ.1 ρ)
    (f := F.eval (Tm.castK (Tm.eqv_cat σ τ) (Tm.tapp (Tm.tapp (Tm.const Const.eqv) σ) τ)) ρ env)
    (Univ.El_code ρ σ.2).symm (Univ.El_code ρ τ.2).symm (F.eval_eqvConst σ τ ρ env) _ _

theorem holds_eqv (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.eqv σ τ x y) ρ env ↔
      F.U.V (F.eqv (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) (cast (Univ.El_code ρ σ.2).symm (F.eval x ρ env))
        (cast (Univ.El_code ρ τ.2).symm (F.eval y ρ env))) :=
  Iff.of_eq (congrArg F.U.V (F.eval_eqv σ τ x y ρ env))

theorem eval_eqv_t (x y : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.eval (Tm.eqv tyT tyT x y) ρ env = F.eqv .t .t (F.eval x ρ env) (F.eval y ρ env) :=
  F.eval_eqv tyT tyT x y ρ env

theorem holds_eqv_t (x y : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.eqv tyT tyT x y) ρ env ↔ F.U.V (F.eqv .t .t (F.eval x ρ env) (F.eval y ρ env)) :=
  F.holds_eqv tyT tyT x y ρ env

/-- The value of `σ ≈ τ`. -/
theorem eval_teq (σ τ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.eval (Tm.teq σ τ) ρ env = F.teq (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) := by
  have h1 : HEq (F.eval (Tm.tapp (Tm.const (Γ := Γ) Const.teq) σ) ρ env) (fun b => F.teq (F.U.code σ.1 ρ) b) :=
    F.heq_eval_tapp _ σ ρ env
  have h2 : HEq (F.eval (Tm.teq (Γ := Γ) σ τ) ρ env)
      (F.eval (Tm.tapp (Tm.const (Γ := Γ) Const.teq) σ) ρ env (F.U.code τ.1 ρ)) := F.heq_eval_tapp _ τ ρ env
  exact eq_of_heq (h2.trans (heq_dapp (Q := fun _ => F.U.P) (fun _ => rfl) h1 rfl))

theorem holds_teq (σ τ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.teq σ τ) ρ env ↔ F.U.V (F.teq (F.U.code σ.1 ρ) (F.U.code τ.1 ρ)) :=
  Iff.of_eq (congrArg F.U.V (F.eval_teq σ τ ρ env))

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

/-- What a frame must satisfy to be a model of PI⁻. -/
structure IsModelPIm : Prop where
  refEqv : F.Valid RefEqv
  symEqv : F.Valid SymEqv
  transEqv : F.Valid TransEqv
  refTeq : F.Valid RefTeq
  llTeq : ∀ {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)), F.Valid (LLTeq Q)

/-- **Soundness.** -/
theorem soundness {Ax : Fm Ctx.nil → Prop} (hM : F.IsModelPIm) (hAx : ∀ φ, Ax φ → F.Valid φ)
    {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : Prov Ax Γ φ) : F.Valid φ := by
  induction h with
  | taut P as hP => intro ρ env; exact (F.holds_inst P as ρ env).mpr (hP _)
  | instAll σ φ κ =>
    intro ρ env
    refine (F.holds_imp _ _ ρ env).mpr fun h => ?_
    unfold Holds; rw [eval_subst0]; exact (F.holds_all σ φ ρ env).mp h _
  | distAll σ φ ψ =>
    intro ρ env
    refine (F.holds_imp _ _ ρ env).mpr fun h => (F.holds_imp _ _ ρ env).mpr fun hφ => ?_
    refine (F.holds_all σ ψ ρ env).mpr fun v => ?_
    have h' := (F.holds_imp _ _ _ _).mp ((F.holds_all σ _ ρ env).mp h v)
    have hw : F.Holds (φ.wk σ) ρ (env, v) := by unfold Holds; rw [eval_wk]; exact hφ
    exact h' hw
  | dualEx σ φ =>
    intro ρ env
    refine (F.holds_iff _ _ ρ env).mpr ?_
    refine (F.holds_ex σ φ ρ env).trans ?_
    refine Iff.trans ?_ (F.holds_neg _ ρ env).symm
    refine Iff.trans ?_ (not_congr (F.holds_all σ φ.neg ρ env)).symm
    constructor
    · rintro ⟨v, hv⟩ h; exact (F.holds_neg _ _ _).mp (h v) hv
    · intro h; exact Classical.byContradiction fun hn => h fun v => (F.holds_neg _ _ _).mpr fun hv => hn ⟨v, hv⟩
  | instTAll φ σ =>
    intro ρ env
    refine (F.holds_imp _ _ ρ env).mpr fun h => ?_
    exact cast (F.holds_of_heq (F.eval_tinst φ σ ρ env)).symm ((F.holds_tall _ _ _).mp h (F.U.code σ.1 ρ))
  | distTAll φ ψ =>
    intro ρ env
    refine (F.holds_imp _ _ ρ env).mpr fun h => (F.holds_imp _ _ ρ env).mpr fun hφ => ?_
    refine (F.holds_tall _ _ _).mpr fun a => ?_
    exact (F.holds_imp _ _ _ _).mp ((F.holds_tall _ _ _).mp h a) (cast (F.holds_of_heq (F.eval_twk φ a ρ env)).symm hφ)
  | dualTEx φ =>
    intro ρ env
    refine (F.holds_iff _ _ ρ env).mpr ?_
    refine (F.holds_tex _ _ _).trans ?_
    refine Iff.trans ?_ (F.holds_neg _ ρ env).symm
    refine Iff.trans ?_ (not_congr (F.holds_tall _ ρ env)).symm
    constructor
    · rintro ⟨a, ha⟩ h; exact (F.holds_neg _ _ _).mp (h a) ha
    · intro h; exact Classical.byContradiction fun hn => h fun a => (F.holds_neg _ _ _).mpr fun ha => hn ⟨a, ha⟩
  | beta h =>
    intro ρ env
    exact (F.holds_iff _ _ ρ env).mpr (Iff.of_eq (congrArg F.U.V (F.eval_betaEq h ρ env)))
  | refEqv => exact hM.refEqv
  | symEqv => exact hM.symEqv
  | transEqv => exact hM.transEqv
  | refTeq => exact hM.refTeq
  | llTeq Q => exact hM.llTeq Q
  | ax h => exact hAx _ h
  | mp _ _ ih1 ih2 => intro ρ env; exact (F.holds_imp _ _ ρ env).mp (ih2 ρ env) (ih1 ρ env)
  | genAll σ _ ih => intro ρ env; exact (F.holds_all σ _ ρ env).mpr fun v => ih ρ (env, v)
  | genTAll _ ih => intro ρ env; exact (F.holds_tall _ _ _).mpr fun a => ih (scons a ρ) env
  | ren ρr _ ih =>
    intro ρ' env'
    exact cast (F.holds_of_heq (F.eval_ren _ ρr ρ' env' _ (F.pullEnv _ ρr ρ' env') (fun _ => rfl)
      (fun x => F.lookup_pull x ρr ρ' env'))).symm (ih _ _)
  | strengthen σ _ ih =>
    intro ρ env
    have v := Classical.choice (Univ.CatVal_nonempty σ.1 ρ)
    have := ih ρ (env, v)
    unfold Holds at this; rw [eval_wk] at this
    exact this
  | tstrengthen _ ih =>
    intro ρ env
    exact cast (F.holds_of_heq (F.eval_twk _ .e ρ env)) (ih (scons .e ρ) env)

theorem soundness_PI {S : Fm Ctx.nil → Prop} (hM : F.IsModelPIm) (hLL : F.Valid LLEqv)
    (hS : ∀ φ, S φ → F.Valid φ) {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : PI S Γ φ) : F.Valid φ :=
  F.soundness hM (fun ψ hψ => hψ.elim (fun e => e ▸ hLL) (hS ψ)) h

/-- `⊥` is false in every frame. -/
theorem not_valid_bot (hV : ∃ p, ¬ F.U.V p) : ¬ F.Valid Bot := fun h => by
  obtain ⟨p, hp⟩ := hV
  exact hp ((F.holds_all (Γ := Ctx.nil) tyT _ (fun i => i.elim0) ()).mp (h _ ()) p)

/-- A frame in which `≈` implies identity of codes validates every instance of LL≈. -/
theorem llTeq_of_teq_eq (hteq : ∀ a b, F.U.V (F.teq a b) → a = b) {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)) :
    F.Valid (LLTeq Q) := by
  intro ρ env
  refine (F.holds_tall _ _ _).mpr fun a => (F.holds_tall _ _ _).mpr fun b => ?_
  refine (F.holds_imp _ _ _ _).mpr fun hab => ?_
  have hab' : a = b := hteq _ _ ((F.holds_teq (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env).mp hab)
  subst hab'
  refine (F.holds_imp _ _ _ _).mpr fun hq => ?_
  have e1 : HEq (F.eval (Tm.tapp Q.twk.twk tv1) (scons a (scons a ρ)) env)
      (F.eval Q.twk.twk (scons a (scons a ρ)) env a) := F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv1 (scons a (scons a ρ)) env
  have e2 : HEq (F.eval (Tm.tapp Q.twk.twk tv0) (scons a (scons a ρ)) env)
      (F.eval Q.twk.twk (scons a (scons a ρ)) env a) := F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv0 (scons a (scons a ρ)) env
  exact cast (F.holds_of_heq (e1.trans e2.symm)) hq

/-- A frame in which `≈` is identity and `≡` is an equivalence relation is a model of PI⁻. -/
theorem model_of_equiv (hteq : ∀ a b, F.U.V (F.teq a b) ↔ a = b) (hr : ∀ a x, F.U.V (F.eqv a a x x))
    (hs : ∀ a b x y, F.U.V (F.eqv a b x y) → F.U.V (F.eqv b a y x))
    (ht : ∀ a b c x y z, F.U.V (F.eqv a b x y) → F.U.V (F.eqv b c y z) → F.U.V (F.eqv a c x z)) : F.IsModelPIm where
  refEqv := by
    intro ρ env
    refine (F.holds_tall _ _ _).mpr fun a => ?_
    exact (F.holds_all _ _ _ _).mpr fun v => (F.holds_eqv _ _ _ _ _ _).mpr (hr _ _)
  symEqv := by
    intro ρ env
    refine (F.holds_tall _ _ _).mpr fun a => (F.holds_tall _ _ _).mpr fun b => ?_
    refine (F.holds_all _ _ _ _).mpr fun x => (F.holds_all _ _ _ _).mpr fun y => ?_
    refine (F.holds_imp _ _ _ _).mpr fun h => ?_
    exact (F.holds_eqv _ _ _ _ _ _).mpr (hs _ _ _ _ ((F.holds_eqv _ _ _ _ _ _).mp h))
  transEqv := by
    intro ρ env
    refine (F.holds_tall _ _ _).mpr fun a => (F.holds_tall _ _ _).mpr fun b => (F.holds_tall _ _ _).mpr fun c => ?_
    refine (F.holds_all _ _ _ _).mpr fun x => (F.holds_all _ _ _ _).mpr fun y => (F.holds_all _ _ _ _).mpr fun z => ?_
    refine (F.holds_imp _ _ _ _).mpr fun h => ?_
    have h' := (F.holds_conj _ _ _ _).mp h
    exact (F.holds_eqv _ _ _ _ _ _).mpr (ht _ _ _ _ _ _ ((F.holds_eqv _ _ _ _ _ _).mp h'.1)
      ((F.holds_eqv _ _ _ _ _ _).mp h'.2))
  refTeq := by
    intro ρ env
    exact (F.holds_tall _ _ _).mpr fun a => (F.holds_teq _ _ _ _).mpr ((hteq _ _).mpr rfl)
  llTeq := fun Q => F.llTeq_of_teq_eq (fun _ _ h => (hteq _ _).mp h) Q

theorem valid_iff_tr (φ : Fm Ctx.nil) : F.Valid φ ↔ F.Holds φ (fun i => i.elim0) () := by
  constructor
  · intro h; exact h _ _
  · intro h ρ env
    have : ρ = (fun i => i.elim0) := funext fun i => i.elim0
    subst this; exact h

end Frame

end Al
end PIF
