import PIHae

/-!
# Propositions finer than truth values

In the semantics of `PIFoundation.lean`, as in *Formal Results*, the items of type `t` are the two
truth values. Here they are pairs `(p, b)` of a truth value `p` and a tag `b`, which records whether
the proposition is quantified. The logical constants act on truth values as before, and give `true`
as the tag, except that the quantifiers give `false`. A sentence is true when its value has first
component true. This file repeats the semantics and the soundness proof for this broader class of
models: everything carries over unchanged, since the proof system never looks at tags.

The point: in such a model, a true quantified sentence `φ` need not be identical to `⊤`, so `□φ`
(that is, `φ ≡_t ⊤`) can be false while `φ` is true. So Int≈ and Ext≈ can come apart.
-/
set_option autoImplicit false

namespace PIF
namespace Tg

/-- Propositions: a truth value with a tag. -/
abbrev TV := Prop × Bool

structure Univ where
  E : Type
  Base : Type
  B : Base → Type
  neE : Nonempty E
  neB : ∀ b, Nonempty (B b)

/-- The set a code names. -/
def Univ.El (U : Univ) : Code U.Base → Type
  | .e => U.E
  | .t => TV
  | .base b => U.B b
  | .arr a c => U.El a → U.El c

structure Frame where
  U : Univ
  /-- the value of `≡`, at each pair of members of the universe -/
  eqv : (a b : Code U.Base) → U.El a → U.El b → Prop
  /-- the value of `≈` -/
  teq : Code U.Base → Code U.Base → Prop
  /-- the tag of a proposition quantified over a type -/
  qtag : Code U.Base → Bool

namespace Univ
variable (U : Univ)

/-- Valuations of type variables. -/
abbrev TEnv (n : Nat) := Fin n → Code U.Base

/-- The semantic value of a category. -/
def CatVal {n : Nat} : Cat n → U.TEnv n → Type
  | .e, _ => U.E
  | .t, _ => TV
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
  | .t => ⟨(True, true)⟩
  | .base b => U.neB b
  | .arr _ c => let ⟨y⟩ := El_nonempty c; ⟨fun _ => y⟩

theorem CatVal_nonempty {n : Nat} (K : Cat n) : ∀ ρ : U.TEnv n, Nonempty (U.CatVal K ρ) := by
  induction K with
  | e => intro; exact U.neE
  | t => intro; exact ⟨(True, true)⟩
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
  | .neg => fun p => (¬ p.1, true)
  | .imp => fun p q => (p.1 → q.1, true)
  | .and => fun p q => (p.1 ∧ q.1, true)
  | .or => fun p q => (p.1 ∨ q.1, true)
  | .iff => fun p q => (p.1 ↔ q.1, true)
  | .all => fun a P => (∀ x, (P x).1, F.qtag a)
  | .ex => fun a P => (∃ x, (P x).1, F.qtag a)
  | .tall => fun Q => (∀ a, (Q a).1, false)
  | .tex => fun Q => (∃ a, (Q a).1, false)
  | .eqv => fun a b x y => (F.eqv a b x y, true)
  | .teq => fun a b => (F.teq a b, true)

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
abbrev Holds {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) : Prop := (F.eval φ ρ env).1

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

theorem cast_forall {A A' : Type} (hA : A = A') (h : ((A → TV) → TV) = ((A' → TV) → TV)) (b : Bool)
    (P : A' → TV) : (cast h (fun Q : A → TV => ((∀ x, (Q x).1 : Prop), b)) P).1 ↔ ∀ x, (P x).1 := by
  subst hA; rw [cast_eq]

theorem cast_exists {A A' : Type} (hA : A = A') (h : ((A → TV) → TV) = ((A' → TV) → TV)) (b : Bool)
    (P : A' → TV) : (cast h (fun Q : A → TV => ((∃ x, (Q x).1 : Prop), b)) P).1 ↔ ∃ x, (P x).1 := by
  subst hA; rw [cast_eq]

theorem cast_forall_snd {A A' : Type} (hA : A = A') (h : ((A → TV) → TV) = ((A' → TV) → TV)) (b : Bool)
    (P : A' → TV) : (cast h (fun Q : A → TV => ((∀ x, (Q x).1 : Prop), b)) P).2 = b := by
  subst hA; rw [cast_eq]

theorem eval_tapp {K : Cat (n+1)} (f : Tm Γ (.pi K)) (σ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.eval (Tm.tapp f σ) ρ env = cast (F.U.tapp_eq K σ ρ) (F.eval f ρ env (F.U.code σ.1 ρ)) := rfl

theorem heq_eval_tapp {K : Cat (n+1)} (f : Tm Γ (.pi K)) (σ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    HEq (F.eval (Tm.tapp f σ) ρ env) (F.eval f ρ env (F.U.code σ.1 ρ)) :=
  (heq_of_eq (F.eval_tapp f σ ρ env)).trans (cast_heq _ _)

theorem holds_all (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.all σ φ) ρ env ↔ ∀ v : F.U.CatVal σ.1 ρ, F.Holds φ ρ (env, v) :=
  cast_forall (Univ.El_code ρ σ.2) _ _ _

theorem holds_ex (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.ex σ φ) ρ env ↔ ∃ v : F.U.CatVal σ.1 ρ, F.Holds φ ρ (env, v) :=
  cast_exists (Univ.El_code ρ σ.2) _ _ _

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
      (fun x y => (F.eqv (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) x y, true)) := by
  refine (F.eval_castK _ _ _ _).trans ((cast_heq _ _).trans ?_)
  refine heq_dapp (Q := fun b => F.U.El (F.U.code σ.1 ρ) → F.U.El b → TV) (fun b => ?_)
    (cast_heq _ _) rfl
  refine Univ.CatVal_sub _ _ _ (scons b (scons (F.U.code σ.1 ρ) ρ)) (fin_cases rfl (fun i => ?_))
  show F.U.code (((inst σ) i).1.ren fs) (scons b ρ) = _
  rw [Univ.code_ren]
  exact fin_cases (P := fun i => F.U.code (inst σ i).1 ρ = scons (F.U.code σ.1 ρ) ρ i) rfl (fun _ => rfl) i

/-- The truth value of `x ≡_{σ,τ} y`. -/
theorem holds_eqv (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.eqv σ τ x y) ρ env ↔
      F.eqv (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) (cast (Univ.El_code ρ σ.2).symm (F.eval x ρ env))
        (cast (Univ.El_code ρ τ.2).symm (F.eval y ρ env)) :=
  Iff.of_eq (congrArg Prod.fst (app2_heq (A := F.U.CatVal σ.1 ρ) (B := F.U.CatVal τ.1 ρ)
    (f := F.eval (Tm.castK (Tm.eqv_cat σ τ) (Tm.tapp (Tm.tapp (Tm.const Const.eqv) σ) τ)) ρ env)
    (Univ.El_code ρ σ.2).symm (Univ.El_code ρ τ.2).symm (F.eval_eqvConst σ τ ρ env) _ _))

/-- The truth value of `σ ≈ τ`. -/
theorem holds_teq (σ τ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.teq σ τ) ρ env ↔ F.teq (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) := by
  have h1 : HEq (F.eval (Tm.tapp (Tm.const (Γ := Γ) Const.teq) σ) ρ env) (fun b => (F.teq (F.U.code σ.1 ρ) b, true)) :=
    F.heq_eval_tapp _ σ ρ env
  have h2 : HEq (F.eval (Tm.teq (Γ := Γ) σ τ) ρ env)
      (F.eval (Tm.tapp (Tm.const (Γ := Γ) Const.teq) σ) ρ env (F.U.code τ.1 ρ)) := F.heq_eval_tapp _ τ ρ env
  exact Iff.of_eq (congrArg Prod.fst (eq_of_heq (h2.trans (heq_dapp (Q := fun _ => TV) (fun _ => rfl) h1 rfl))))

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
    exact cast (congrArg Prod.fst (eq_of_heq (F.eval_tinst φ σ ρ env))).symm (h (F.U.code σ.1 ρ))
  | distTAll φ ψ =>
    intro ρ env h hφ a
    exact h a (cast (congrArg Prod.fst (eq_of_heq (F.eval_twk φ a ρ env))).symm hφ)
  | dualTEx φ =>
    intro ρ env
    show (∃ a, F.Holds φ (scons a ρ) env) ↔ ¬ ∀ a, ¬ F.Holds φ (scons a ρ) env
    constructor
    · rintro ⟨a, ha⟩ h; exact h a ha
    · intro h; exact Classical.byContradiction fun hn => h fun a ha => hn ⟨a, ha⟩
  | beta h => intro ρ env; exact Iff.of_eq (congrArg Prod.fst (F.eval_betaEq h ρ env))
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
    exact cast (congrArg Prod.fst (eq_of_heq (F.eval_ren _ ρr ρ' env' _ (F.pullEnv _ ρr ρ' env') (fun _ => rfl)
      (fun x => F.lookup_pull x ρr ρ' env')))).symm (ih _ _)
  | strengthen σ _ ih =>
    intro ρ env
    have v := Classical.choice (Univ.CatVal_nonempty σ.1 ρ)
    have := ih ρ (env, v)
    unfold Holds at this
    rwa [eval_wk] at this
  | tstrengthen _ ih =>
    intro ρ env
    exact cast (congrArg Prod.fst (eq_of_heq (F.eval_twk _ .e ρ env))) (ih (scons .e ρ) env)

/-- A model of PI: a model of PI⁻ in which LL≡ is true. -/
theorem soundness_PI {S : Fm Ctx.nil → Prop} (hM : F.IsModelPIm) (hLL : F.Valid LLEqv)
    (hS : ∀ φ, S φ → F.Valid φ) {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : PI S Γ φ) : F.Valid φ :=
  F.soundness hM (fun ψ hψ => hψ.elim (fun e => e ▸ hLL) (hS ψ)) h

/-- `⊥` is false in every frame. -/
theorem not_valid_bot : ¬ F.Valid Bot := fun h =>
  (F.holds_all (Γ := Ctx.nil) tyT _ (fun i => i.elim0) ()).mp (h _ ()) (False, true)

/-- So a theory with a model is consistent. -/
theorem consistent_of_model {Ax : Fm Ctx.nil → Prop} (hM : F.IsModelPIm) (hAx : ∀ φ, Ax φ → F.Valid φ) :
    ¬ Prov Ax Ctx.nil Bot := fun h => F.not_valid_bot (F.soundness hM hAx h)

/-- A frame in which `≈` implies identity of codes validates every instance of LL≈. -/
theorem llTeq_of_teq_eq (hteq : ∀ a b, F.teq a b → a = b) {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)) :
    F.Valid (LLTeq Q) := by
  intro ρ env a b hab
  have hab' : a = b := hteq _ _ ((F.holds_teq _ _ _ _).mp hab)
  subst hab'
  intro hq
  have e1 : HEq (F.eval (Tm.tapp Q.twk.twk tv1) (scons a (scons a ρ)) env)
      (F.eval Q.twk.twk (scons a (scons a ρ)) env a) := F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv1 (scons a (scons a ρ)) env
  have e2 : HEq (F.eval (Tm.tapp Q.twk.twk tv0) (scons a (scons a ρ)) env)
      (F.eval Q.twk.twk (scons a (scons a ρ)) env a) := F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv0 (scons a (scons a ρ)) env
  exact cast (congrArg Prod.fst (eq_of_heq (e1.trans e2.symm))) hq

end Frame


/-! ## A model of PI in which Int≈ is true and Ext≈ is false

`E = 1`, with a duplicate `d` of `e` (also with one item). `≈` is identity of types, and an item is
identified with an item just in case they are the same item of `e` or `d`, or the same item of types
built alike from `e`, `d`, and `t` (so the entity is identified with the item of `d`). Ext≈ fails,
since `e` and `d` have identified items but are distinct. Int≈ holds: `α ⊑ β` is a quantified
proposition, so it is never identical to `⊤`, and so `□(α ⊑ β)` is always false. -/

namespace Frame
variable (F : Frame)

theorem eval_all_snd {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    (F.eval (Tm.all σ φ) ρ env).2 = F.qtag (F.U.code σ.1 ρ) :=
  cast_forall_snd (Univ.El_code ρ σ.2) _ _ _

end Frame

/-- The duplicate types: `true` for a copy of `e`, `false` for a copy of `t`. -/
def BI : Bool → Type
  | true => Unit
  | false => TV

theorem BI_ne : ∀ b, Nonempty (BI b)
  | true => ⟨(show Unit from ())⟩
  | false => ⟨(show TV from (True, true))⟩

def univI : Univ := { E := Unit, Base := Bool, B := BI, neE := ⟨()⟩, neB := BI_ne }

/-- The duplicates are sent to `e` and `t`. -/
def kI : Code Bool → Code Bool
  | .base true => .e
  | .base false => .t
  | .arr a c => .arr (kI a) (kI c)
  | c => c

def MiF : Frame where
  U := univI
  eqv := fun a b x y => kI a = kI b ∧ HEq x y
  teq := fun a b => a = b
  qtag := fun _ => false

theorem Mi_model : MiF.IsModelPIm where
  refEqv := by
    intro ρ env a
    exact (MiF.holds_all _ _ _ _).mpr fun v => (MiF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩
  symEqv := by
    intro ρ env a b
    refine (MiF.holds_all _ _ _ _).mpr fun x => (MiF.holds_all _ _ _ _).mpr fun y h => ?_
    have h' := (MiF.holds_eqv _ _ _ _ _ _).mp h
    exact (MiF.holds_eqv _ _ _ _ _ _).mpr ⟨h'.1.symm, h'.2.symm⟩
  transEqv := by
    intro ρ env a b c
    refine (MiF.holds_all _ _ _ _).mpr fun x => (MiF.holds_all _ _ _ _).mpr fun y =>
      (MiF.holds_all _ _ _ _).mpr fun z h => ?_
    have h1 := (MiF.holds_eqv _ _ _ _ _ _).mp ((MiF.holds_conj _ _ _ _).mp h).1
    have h2 := (MiF.holds_eqv _ _ _ _ _ _).mp ((MiF.holds_conj _ _ _ _).mp h).2
    exact (MiF.holds_eqv _ _ _ _ _ _).mpr ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  refTeq := by
    intro ρ env a
    exact (MiF.holds_teq _ _ _ _).mpr rfl
  llTeq := fun Q => MiF.llTeq_of_teq_eq (fun _ _ h => h) Q

theorem Mi_LLEqv : MiF.Valid LLEqv := by
  intro ρ env a
  refine (MiF.holds_all _ _ _ _).mpr fun x => (MiF.holds_all _ _ _ _).mpr fun y hxy => ?_
  refine (MiF.holds_all _ _ _ _).mpr fun G hGx => ?_
  have h := ((MiF.holds_eqv _ _ _ _ _ _).mp hxy).2
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.trans (cast_heq _ _)))
  subst e
  exact hGx

theorem Mi_not_ExtT : ¬ MiF.Valid ExtT := fun h => by
  have := h (fun i => i.elim0) () .e (.base true)
  have hc : MiF.Holds (Tm.conj (subT (Γ := (Ctx.nil.text).text)) supT)
      (scons (Code.base true) (scons .e (fun i => i.elim0))) () := by
    refine (MiF.holds_conj _ _ _ _).mpr ⟨?_, ?_⟩
    · refine (MiF.holds_all _ _ _ _).mpr fun x => (MiF.holds_ex _ _ _ _).mpr ⟨(), ?_⟩
      refine (MiF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, ?_⟩
      exact (cast_heq _ _).trans (HEq.trans (by cases x; rfl) (cast_heq _ _).symm)
    · refine (MiF.holds_all _ _ _ _).mpr fun y => (MiF.holds_ex _ _ _ _).mpr ⟨(), ?_⟩
      refine (MiF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, ?_⟩
      exact (cast_heq _ _).trans (HEq.trans (by cases y; rfl) (cast_heq _ _).symm)
  have ht := (MiF.holds_teq _ _ _ _).mp (this hc)
  cases ht

theorem Mi_IntT : MiF.Valid IntT := by
  intro ρ env a b hc
  have h1 := (MiF.holds_eqv _ _ _ _ _ _).mp ((MiF.holds_conj _ _ _ _).mp hc).1
  have h2 := (cast_heq _ _).symm.trans (h1.2.trans (cast_heq _ _))
  have e := congrArg Prod.snd (eq_of_heq h2)
  have hs : (MiF.eval (subT (Γ := (Ctx.nil.text).text)) (scons b (scons a ρ)) env).2 = false :=
    MiF.eval_all_snd _ _ _ _
  exact (Bool.false_ne_true (hs.symm.trans (e.trans rfl))).elim


/-! ## Truth, `⊤ ≢ ⊥`, and Int≈ in PI⁻ -/

namespace Frame
variable (F : Frame)

/-- `≡` at type `t`, without casts. -/
theorem holds_eqv_t {n : Nat} {Γ : Ctx n} (x y : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.eqv tyT tyT x y) ρ env ↔ F.eqv .t .t (F.eval x ρ env) (F.eval y ρ env) :=
  F.holds_eqv tyT tyT x y ρ env

/-- A frame in which `≈` is identity and `≡` is an equivalence relation is a model of PI⁻. -/
theorem model_of_equiv (hteq : ∀ a b, F.teq a b ↔ a = b) (hr : ∀ a x, F.eqv a a x x)
    (hs : ∀ a b x y, F.eqv a b x y → F.eqv b a y x)
    (ht : ∀ a b c x y z, F.eqv a b x y → F.eqv b c y z → F.eqv a c x z) : F.IsModelPIm where
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
    have h1 := (F.holds_eqv _ _ _ _ _ _).mp ((F.holds_conj _ _ _ _).mp h).1
    have h2 := (F.holds_eqv _ _ _ _ _ _).mp ((F.holds_conj _ _ _ _).mp h).2
    exact (F.holds_eqv _ _ _ _ _ _).mpr (ht _ _ _ _ _ _ h1 h2)
  refTeq := by
    intro ρ env a
    exact (F.holds_teq _ _ _ _).mpr ((hteq _ _).mpr rfl)
  llTeq := fun Q => F.llTeq_of_teq_eq (fun _ _ h => (hteq _ _).mp h) Q

end Frame

abbrev univU : Univ := { E := Unit, Base := Empty, B := Empty.elim, neE := ⟨()⟩, neB := fun b => b.elim }

/-- Identification within types: identical items, or two items of a distinguished class. -/
def clsEqv (S : (c : Code univU.Base) → univU.El c → Prop) (a b : Code univU.Base) (x : univU.El a) (y : univU.El b) : Prop :=
  a = b ∧ (HEq x y ∨ (S a x ∧ S b y))

theorem clsEqv_refl (S : (c : Code univU.Base) → univU.El c → Prop) (a : Code univU.Base) (x : univU.El a) : clsEqv S a a x x :=
  ⟨rfl, Or.inl HEq.rfl⟩
theorem clsEqv_symm (S : (c : Code univU.Base) → univU.El c → Prop) (a b : Code univU.Base) (x : univU.El a) (y : univU.El b)
    (h : clsEqv S a b x y) : clsEqv S b a y x :=
  ⟨h.1.symm, h.2.elim (fun e => Or.inl e.symm) (fun ⟨p, q⟩ => Or.inr ⟨q, p⟩)⟩
theorem clsEqv_trans (S : (c : Code univU.Base) → univU.El c → Prop) (a b c : Code univU.Base) (x : univU.El a)
    (y : univU.El b) (z : univU.El c) (h1 : clsEqv S a b x y) (h2 : clsEqv S b c y z) : clsEqv S a c x z := by
  obtain ⟨hab, e1⟩ := h1
  obtain ⟨hbc, e2⟩ := h2
  subst hab; subst hbc
  refine ⟨rfl, ?_⟩
  rcases e1 with e1 | ⟨s1, s2⟩ <;> rcases e2 with e2 | ⟨s3, s4⟩
  · exact Or.inl (e1.trans e2)
  · exact Or.inr ⟨eq_of_heq e1 ▸ s3, s4⟩
  · exact Or.inr ⟨s1, eq_of_heq e2 ▸ s2⟩
  · exact Or.inr ⟨s1, s4⟩

/-! ### `𝔐_tb`: `⊤ ≢ ⊥` without Truth

All quantified propositions, true or false, are identified with each other; nothing else is
identified with anything but itself. `⊤` is not quantified, so `⊤ ≢ ⊥`. -/

def Stb : (c : Code univU.Base) → univU.El c → Prop
  | .t, x => x.2 = false
  | _, _ => False

abbrev MtbF : Frame where
  U := univU
  eqv := clsEqv Stb
  teq := fun a b => a = b
  qtag := fun _ => false

theorem Mtb_model : MtbF.IsModelPIm :=
  MtbF.model_of_equiv (fun _ _ => Iff.rfl) (clsEqv_refl Stb) (clsEqv_symm Stb) (clsEqv_trans Stb)

theorem Mtb_TopBot : MtbF.Valid TopBot := by
  intro ρ env h
  have h' := (MtbF.holds_eqv_t _ _ _ _).mp h
  rcases h'.2 with e | ⟨s, _⟩
  · have := congrArg Prod.snd (eq_of_heq e)
    exact Bool.noConfusion (this.trans (MtbF.eval_all_snd _ _ _ _) : true = false)
  · exact Bool.noConfusion (s : true = false)

theorem Mtb_not_Truth : ¬ MtbF.Valid Truth := fun h => by
  have h1 := (MtbF.holds_all _ _ _ _).mp ((MtbF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (True, false)) (False, false)
  exact h1 ((MtbF.holds_eqv_t _ _ _ _).mpr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩) trivial

/-! ### `𝔐_it`: Int≈ without `⊤ ≢ ⊥` or Truth

Propositions quantified over `t` share their tag with `⊤`, and all propositions with that tag are
identified with each other; so `⊤ ≡ ⊥`. Since `α ⊑ β` is quantified over `α`, `□(α ⊑ β)` holds just
in case `α` is `t`; so the antecedent of Int≈ holds only when `α` and `β` are both `t`. -/

def Sit : (c : Code univU.Base) → univU.El c → Prop
  | .t, x => x.2 = true
  | _, _ => False

abbrev MitF : Frame where
  U := univU
  eqv := clsEqv Sit
  teq := fun a b => a = b
  qtag := fun a => decide (a = .t)

theorem Mit_model : MitF.IsModelPIm :=
  MitF.model_of_equiv (fun _ _ => Iff.rfl) (clsEqv_refl Sit) (clsEqv_symm Sit) (clsEqv_trans Sit)

theorem Mit_not_TopBot : ¬ MitF.Valid TopBot := fun h =>
  h (fun i => i.elim0) () ((MitF.holds_eqv_t _ _ _ _).mpr ⟨rfl, Or.inr ⟨rfl, MitF.eval_all_snd _ _ _ _⟩⟩)

theorem Mit_not_Truth : ¬ MitF.Valid Truth := fun h => by
  have h1 := (MitF.holds_all _ _ _ _).mp ((MitF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (True, true)) (False, true)
  exact h1 ((MitF.holds_eqv_t _ _ _ _).mpr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩) trivial

/-- If `□φ`, for `φ` quantified over `σ`, then `σ` is `t`. -/
theorem Mit_box {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MitF.U.TEnv n) (env : MitF.U.Env Γ ρ)
    (h : MitF.Holds (boxF (Tm.all σ φ)) ρ env) : MitF.U.code σ.1 ρ = .t := by
  have h1 := ((MitF.holds_eqv_t _ _ _ _).mp h).2
  have hs : (MitF.eval (Tm.all σ φ) ρ env).2 = true := by
    rcases h1 with e | ⟨s, _⟩
    · exact (congrArg Prod.snd (eq_of_heq e)).trans rfl
    · exact s
  rw [MitF.eval_all_snd] at hs
  exact of_decide_eq_true hs

theorem Mit_IntT : MitF.Valid IntT := by
  intro ρ env a b hc
  have ha := Mit_box _ _ _ _ ((MitF.holds_conj _ _ _ _).mp hc).1
  have hb := Mit_box _ _ _ _ ((MitF.holds_conj _ _ _ _).mp hc).2
  exact (MitF.holds_teq _ _ _ _).mpr (ha.trans hb.symm)

end Tg
end PIF
