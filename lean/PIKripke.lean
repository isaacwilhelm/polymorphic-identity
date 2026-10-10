import PIClassModels

/-!
# Kripke models

Worlds come with an accessibility relation `R`, a preorder. Propositions are sets of worlds, and two
propositions count as identical at a world just in case they agree at every world it can see. At
the other types, each base type carries an equivalence relation at each world (growing coarser
along `R`), and functions are related at `w` when, at every world `v` that `w` can see, they take
`v`-related arguments to `v`-related values. The quantifier `∀_σ` ranges, at a world, over the
items related to themselves there; the type quantifier ranges over a domain of types which can grow
along `R`. A formula is true when it is true at the actual world `w₀`.

Soundness holds at every world, for valuations admissible there; so provably equivalent formulas
express the same proposition, and every such model of PI is a model of Classicism. In these models
`□φ` can be true at one world and false at another, Necessity of Distinctness can fail, and so can
the Barcan formula for types.
-/
set_option autoImplicit false

namespace PIF
namespace Kr

open Wd (heq_app heq_funext heq_pifun heq_dapp)

structure Univ where
  W : Type
  w0 : W
  R : W → W → Prop
  Rrefl : ∀ w, R w w
  Rtrans : ∀ u v w, R u v → R v w → R u w
  E : Type
  Base : Type
  B : Base → Type
  neE : Nonempty E
  neB : ∀ b, Nonempty (B b)
  /-- identity of entities, and of items of the base types, at each world -/
  re : W → E → E → Prop
  rb : W → (b : Base) → B b → B b → Prop
  re_refl : ∀ w x, re w x x
  re_symm : ∀ w x y, re w x y → re w y x
  re_trans : ∀ w x y z, re w x y → re w y z → re w x z
  re_mono : ∀ w v x y, R w v → re w x y → re v x y
  rb_refl : ∀ w b x, rb w b x x
  rb_symm : ∀ w b x y, rb w b x y → rb w b y x
  rb_trans : ∀ w b x y z, rb w b x y → rb w b y z → rb w b x z
  rb_mono : ∀ w v b x y, R w v → rb w b x y → rb v b x y
  /-- the types that exist at each world -/
  D : W → Code Base → Prop
  D_e : ∀ w, D w .e
  D_t : ∀ w, D w .t
  D_arr : ∀ w a c, D w a → D w c → D w (.arr a c)
  D_mono : ∀ w v a, R w v → D w a → D v a

/-- The set a code names. -/
def Univ.El (U : Univ) : Code U.Base → Type
  | .e => U.E
  | .t => U.W → Prop
  | .base b => U.B b
  | .arr a c => U.El a → U.El c

/-- Identity at a world, at each type. -/
def Univ.rel (U : Univ) : (a : Code U.Base) → U.W → U.El a → U.El a → Prop
  | .e => U.re
  | .t => fun w p q => ∀ v, U.R w v → (p v ↔ q v)
  | .base b => fun w => U.rb w b
  | .arr a c => fun w f g => ∀ v, U.R w v → ∀ x y, U.rel a v x y → U.rel c v (f x) (g y)

namespace Univ
variable (U : Univ)

theorem rel_mono : ∀ (a : Code U.Base) (w v : U.W) (x y : U.El a), U.R w v → U.rel a w x y → U.rel a v x y
  | .e, w, v, x, y, h, hx => U.re_mono w v x y h hx
  | .t, _, _, _, _, h, hx => fun u hu => hx u (U.Rtrans _ _ _ h hu)
  | .base b, w, v, x, y, h, hx => U.rb_mono w v b x y h hx
  | .arr _ _, _, _, _, _, h, hx => fun u hu => hx u (U.Rtrans _ _ _ h hu)

theorem rel_symm : ∀ (a : Code U.Base) (w : U.W) (x y : U.El a), U.rel a w x y → U.rel a w y x
  | .e, w, x, y, h => U.re_symm w x y h
  | .t, _, _, _, h => fun v hv => (h v hv).symm
  | .base b, w, x, y, h => U.rb_symm w b x y h
  | .arr a c, _, _, _, h => fun v hv x y hxy => rel_symm c v _ _ (h v hv y x (rel_symm a v x y hxy))

theorem rel_trans : ∀ (a : Code U.Base) (w : U.W) (x y z : U.El a), U.rel a w x y → U.rel a w y z → U.rel a w x z
  | .e, w, x, y, z, h1, h2 => U.re_trans w x y z h1 h2
  | .t, _, _, _, _, h1, h2 => fun v hv => (h1 v hv).trans (h2 v hv)
  | .base b, w, x, y, z, h1, h2 => U.rb_trans w b x y z h1 h2
  | .arr a c, _, _, _, _, h1, h2 => fun v hv x y hxy =>
      rel_trans c v _ _ _ (h1 v hv x x (rel_trans a v x y x hxy (rel_symm U a v x y hxy))) (h2 v hv x y hxy)

theorem rel_refl_left (a : Code U.Base) (w : U.W) (x y : U.El a) (h : U.rel a w x y) : U.rel a w x x :=
  U.rel_trans a w x y x h (U.rel_symm a w x y h)

theorem rel_refl_right (a : Code U.Base) (w : U.W) (x y : U.El a) (h : U.rel a w x y) : U.rel a w y y :=
  U.rel_trans a w y x y (U.rel_symm a w x y h) h

/-- Each type has an item related to itself at every world. -/
theorem adm_nonempty : ∀ a : Code U.Base, ∃ x : U.El a, ∀ w, U.rel a w x x
  | .e => let ⟨x⟩ := U.neE; ⟨x, fun w => U.re_refl w x⟩
  | .t => ⟨fun _ => True, fun _ _ _ => Iff.rfl⟩
  | .base b => let ⟨x⟩ := U.neB b; ⟨x, fun w => U.rb_refl w b x⟩
  | .arr _ c => let ⟨y, hy⟩ := adm_nonempty c; ⟨fun _ => y, fun _ v _ _ _ _ => hy v⟩

end Univ

structure Frame where
  U : Univ
  /-- the value of `≡`, at each pair of members of the universe -/
  eqv : (a b : Code U.Base) → U.El a → U.El b → U.W → Prop
  /-- the value of `≈` -/
  teq : Code U.Base → Code U.Base → U.W → Prop
  /-- `≡` respects identity at each world -/
  eqv_resp : ∀ u a b x x' y y', U.rel a u x x' → U.rel b u y y' → (eqv a b x y u ↔ eqv a b x' y' u)

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
  | .all => fun a P w => ∀ x, F.U.rel a w x x → P x w
  | .ex => fun a P w => ∃ x, F.U.rel a w x x ∧ P x w
  | .tall => fun Q w => ∀ a, F.U.D w a → Q a w
  | .tex => fun Q w => ∃ a, F.U.D w a ∧ Q a w
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


namespace Frame
variable (F : Frame)

theorem eval_tapp {n : Nat} {Γ : Ctx n} {K : Cat (n+1)} (f : Tm Γ (.pi K)) (σ : Ty n) (ρ : F.U.TEnv n)
    (env : F.U.Env Γ ρ) : F.eval (Tm.tapp f σ) ρ env = cast (F.U.tapp_eq K σ ρ) (F.eval f ρ env (F.U.code σ.1 ρ)) := rfl

theorem heq_eval_tapp {n : Nat} {Γ : Ctx n} {K : Cat (n+1)} (f : Tm Γ (.pi K)) (σ : Ty n) (ρ : F.U.TEnv n)
    (env : F.U.Env Γ ρ) : HEq (F.eval (Tm.tapp f σ) ρ env) (F.eval f ρ env (F.U.code σ.1 ρ)) :=
  (heq_of_eq (F.eval_tapp f σ ρ env)).trans (cast_heq _ _)

end Frame

/-! ## The fundamental lemma

A Kripke version of the invariance lemma: a frame carries families of *admissible relations*
between members of its type universe, each admissible from some world on, and every term is
related to itself. With the identity relations themselves, this says that the value of every term
respects identity at every world; with relations between distinct types, it shows that types which
are interchangeable at a world cannot be told apart there. -/

/-- A family of admissible relations for a frame. -/
structure KInv (F : Frame) where
  Adm : F.U.W → (a a' : Code F.U.Base) → (F.U.W → F.U.El a → F.U.El a' → Prop) → Prop
  amono : ∀ {w v : F.U.W} {a a' : Code F.U.Base} {S : F.U.W → F.U.El a → F.U.El a' → Prop},
    Adm w a a' S → F.U.R w v → Adm v a a' S
  smono : ∀ {w : F.U.W} {a a' : Code F.U.Base} {S : F.U.W → F.U.El a → F.U.El a' → Prop},
    Adm w a a' S → ∀ u u' x x', F.U.R w u → F.U.R u u' → S u x x' → S u' x x'
  refl : ∀ w a, Adm w a a (F.U.rel a)
  arrow : ∀ {w : F.U.W} {a a' c c' : Code F.U.Base} {S : F.U.W → F.U.El a → F.U.El a' → Prop}
    {T : F.U.W → F.U.El c → F.U.El c' → Prop}, Adm w a a' S → Adm w c c' T →
    Adm w (.arr a c) (.arr a' c') (fun v f f' => ∀ u, F.U.R v u → ∀ x x', S u x x' → T u (f x) (f' x'))
  total : ∀ {w : F.U.W} {a a' : Code F.U.Base} {S : F.U.W → F.U.El a → F.U.El a' → Prop},
    Adm w a a' S → ∀ u, F.U.R w u → ∀ x, F.U.rel a u x x → ∃ x', F.U.rel a' u x' x' ∧ S u x x'
  onto : ∀ {w : F.U.W} {a a' : Code F.U.Base} {S : F.U.W → F.U.El a → F.U.El a' → Prop},
    Adm w a a' S → ∀ u, F.U.R w u → ∀ x', F.U.rel a' u x' x' → ∃ x, F.U.rel a u x x ∧ S u x x'
  teq : ∀ {w : F.U.W} {a a' b b' : Code F.U.Base} {S : F.U.W → F.U.El a → F.U.El a' → Prop}
    {T : F.U.W → F.U.El b → F.U.El b' → Prop}, Adm w a a' S → Adm w b b' T →
    ∀ u, F.U.R w u → (F.teq a b u ↔ F.teq a' b' u)
  eqv : ∀ {w : F.U.W} {a a' b b' : Code F.U.Base} {S : F.U.W → F.U.El a → F.U.El a' → Prop}
    {T : F.U.W → F.U.El b → F.U.El b' → Prop}, Adm w a a' S → Adm w b b' T →
    ∀ u, F.U.R w u → ∀ x x' y y', S u x x' → T u y y' → (F.eqv a b x y u ↔ F.eqv a' b' x' y' u)

namespace KInv
variable {F : Frame} (I : KInv F)
set_option linter.unusedVariables false

abbrev RelV {n : Nat} (ρ ρ' : F.U.TEnv n) := ∀ i, F.U.W → F.U.El (ρ i) → F.U.El (ρ' i) → Prop

def RScons {n : Nat} {ρ ρ' : F.U.TEnv n} {a a' : Code F.U.Base} (S : F.U.W → F.U.El a → F.U.El a' → Prop)
    (Rs : RelV ρ ρ') : RelV (scons a ρ) (scons a' ρ')
  | ⟨0, _⟩ => S
  | ⟨k+1, h⟩ => Rs ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- The logical relation at each category, at each world. -/
def Rel : {n : Nat} → (K : Cat n) → (ρ ρ' : F.U.TEnv n) → RelV ρ ρ' → F.U.W →
    F.U.CatVal K ρ → F.U.CatVal K ρ' → Prop
  | _, .e, _, _, _ => F.U.re
  | _, .t, _, _, _ => fun w p q => ∀ v, F.U.R w v → (p v ↔ q v)
  | _, .var i, _, _, Rs => Rs i
  | _, .arr K L, ρ, ρ', Rs => fun w f f' =>
      ∀ v, F.U.R w v → ∀ u u', Rel K ρ ρ' Rs v u u' → Rel L ρ ρ' Rs v (f u) (f' u')
  | _, .pi K, ρ, ρ', Rs => fun w G G' => ∀ v, F.U.R w v → ∀ a a' (S : F.U.W → F.U.El a → F.U.El a' → Prop),
      I.Adm v a a' S → Rel K (scons a ρ) (scons a' ρ') (RScons S Rs) v (G a) (G' a')

/-- The same relation at a type, on the sets its code names. -/
def RelE {n : Nat} : (K : Cat n) → (ρ ρ' : F.U.TEnv n) → RelV ρ ρ' → F.U.W →
    F.U.El (F.U.code K ρ) → F.U.El (F.U.code K ρ') → Prop
  | .e, _, _, _ => F.U.re
  | .t, _, _, _ => fun w p q => ∀ v, F.U.R w v → (p v ↔ q v)
  | .var i, _, _, Rs => Rs i
  | .arr K L, ρ, ρ', Rs => fun w f f' =>
      ∀ v, F.U.R w v → ∀ x x', RelE K ρ ρ' Rs v x x' → RelE L ρ ρ' Rs v (f x) (f' x')
  | .pi _, _, _, _ => fun _ x y => x = y

theorem adm_RelE {n : Nat} (K : Cat n) : ∀ (w : F.U.W) (ρ ρ' : F.U.TEnv n) (Rs : RelV ρ ρ'),
    (∀ i, I.Adm w (ρ i) (ρ' i) (Rs i)) → K.Simple →
    I.Adm w (F.U.code K ρ) (F.U.code K ρ') (RelE K ρ ρ' Rs) := by
  induction K with
  | e => intro w _ _ _ _ _; exact I.refl w .e
  | t => intro w _ _ _ _ _; exact I.refl w .t
  | var i => intro w ρ ρ' Rs hRs _; exact hRs i
  | arr a b iha ihb => intro w ρ ρ' Rs hRs hK; exact I.arrow (iha w ρ ρ' Rs hRs hK.1) (ihb w ρ ρ' Rs hRs hK.2)
  | pi _ _ => intro _ _ _ _ _ hK; exact hK.elim

theorem forall_heq {A A' : Type} (h : A = A') {P : A → Prop} {Q : A' → Prop}
    (hPQ : ∀ a a', HEq a a' → (P a ↔ Q a')) : (∀ a, P a) ↔ (∀ a', Q a') := by
  subst h
  exact ⟨fun h a => (hPQ a a HEq.rfl).mp (h a), fun h a => (hPQ a a HEq.rfl).mpr (h a)⟩

theorem Rel_RelE {n : Nat} (K : Cat n) : ∀ (hK : K.Simple) (ρ ρ' : F.U.TEnv n) (Rs : RelV ρ ρ') (w : F.U.W)
    (u : F.U.CatVal K ρ) (u' : F.U.CatVal K ρ')
    (x : F.U.El (F.U.code K ρ)) (x' : F.U.El (F.U.code K ρ')), HEq u x → HEq u' x' →
    (I.Rel K ρ ρ' Rs w u u' ↔ RelE K ρ ρ' Rs w x x') := by
  induction K with
  | e => intro _ ρ ρ' Rs w u u' x x' hx hx'; cases hx; cases hx'; exact Iff.rfl
  | t => intro _ ρ ρ' Rs w u u' x x' hx hx'; cases hx; cases hx'; exact Iff.rfl
  | var i => intro _ ρ ρ' Rs w u u' x x' hx hx'; cases hx; cases hx'; exact Iff.rfl
  | arr a b iha ihb =>
    intro hK ρ ρ' Rs w u u' x x' hx hx'
    refine forall_congr' fun v => imp_congr Iff.rfl ?_
    refine forall_heq (Univ.El_code ρ hK.1).symm fun z y hzy => ?_
    refine forall_heq (Univ.El_code ρ' hK.1).symm fun z' y' hzy' => ?_
    refine imp_congr (iha hK.1 ρ ρ' Rs v z z' y y' hzy hzy') (ihb hK.2 ρ ρ' Rs v _ _ _ _ ?_ ?_)
    · exact heq_app (Univ.El_code ρ hK.1).symm (Univ.El_code ρ hK.2).symm hx hzy
    · exact heq_app (Univ.El_code ρ' hK.1).symm (Univ.El_code ρ' hK.2).symm hx' hzy'
  | pi _ _ => intro hK; exact hK.elim

theorem Rel_ren {n : Nat} (K : Cat n) : ∀ {m : Nat} (r : Fin n → Fin m) (ρ ρ' : F.U.TEnv m)
    (Rs : RelV ρ ρ') (ρ₂ ρ₂' : F.U.TEnv n) (Rs₂ : RelV ρ₂ ρ₂')
    (hρ : ∀ i, ρ (r i) = ρ₂ i) (hρ' : ∀ i, ρ' (r i) = ρ₂' i)
    (hR : ∀ i w x x' y y', HEq x y → HEq x' y' → (Rs (r i) w x x' ↔ Rs₂ i w y y')) (w : F.U.W)
    (v : F.U.CatVal (K.ren r) ρ) (v' : F.U.CatVal (K.ren r) ρ') (z : F.U.CatVal K ρ₂) (z' : F.U.CatVal K ρ₂'),
    HEq v z → HEq v' z' → (I.Rel (K.ren r) ρ ρ' Rs w v v' ↔ I.Rel K ρ₂ ρ₂' Rs₂ w z z') := by
  induction K with
  | e => intro m r ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ _ w v v' z z' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | t => intro m r ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ _ w v v' z z' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | var i => intro m r ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ hR w v v' z z' hv hv'; exact hR i w v v' z z' hv hv'
  | arr a b iha ihb =>
    intro m r ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR w v v' z z' hv hv'
    refine forall_congr' fun u => imp_congr Iff.rfl ?_
    refine forall_heq (Univ.CatVal_ren a r ρ ρ₂ hρ) fun q y hqy => ?_
    refine forall_heq (Univ.CatVal_ren a r ρ' ρ₂' hρ') fun q' y' hqy' => ?_
    refine imp_congr (iha r ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR u q q' y y' hqy hqy')
      (ihb r ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR u _ _ _ _ ?_ ?_)
    · exact heq_app (Univ.CatVal_ren a r ρ ρ₂ hρ) (Univ.CatVal_ren b r ρ ρ₂ hρ) hv hqy
    · exact heq_app (Univ.CatVal_ren a r ρ' ρ₂' hρ') (Univ.CatVal_ren b r ρ' ρ₂' hρ') hv' hqy'
  | pi K ih =>
    intro m r ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR w v v' z z' hv hv'
    refine forall_congr' fun u => imp_congr Iff.rfl ?_
    refine forall_congr' fun a => forall_congr' fun a' => forall_congr' fun S => imp_congr Iff.rfl ?_
    refine ih (liftR r) (scons a ρ) (scons a' ρ') (RScons S Rs) (scons a ρ₂) (scons a' ρ₂') (RScons S Rs₂)
      (fin_cases rfl (fun i => hρ i)) (fin_cases rfl (fun i => hρ' i)) ?_ u _ _ _ _ ?_ ?_
    · refine fin_cases ?_ (fun i => fun w x x' y y' hx hx' => hR i w x x' y y' hx hx')
      intro w x x' y y' hx hx'; cases hx; cases hx'; exact Iff.rfl
    · exact heq_dapp (fun a => Univ.CatVal_ren K (liftR r) (scons a ρ) (scons a ρ₂)
        (fin_cases rfl (fun i => hρ i))) hv rfl
    · exact heq_dapp (fun a => Univ.CatVal_ren K (liftR r) (scons a ρ') (scons a ρ₂')
        (fin_cases rfl (fun i => hρ' i))) hv' rfl

theorem Rel_sub {n : Nat} (K : Cat n) : ∀ {m : Nat} (s : Fin n → Ty m) (ρ ρ' : F.U.TEnv m)
    (Rs : RelV ρ ρ') (ρ₂ ρ₂' : F.U.TEnv n) (Rs₂ : RelV ρ₂ ρ₂')
    (hρ : ∀ i, F.U.code (s i).1 ρ = ρ₂ i) (hρ' : ∀ i, F.U.code (s i).1 ρ' = ρ₂' i)
    (hR : ∀ i w (x : F.U.CatVal (s i).1 ρ) (x' : F.U.CatVal (s i).1 ρ') y y', HEq x y → HEq x' y' →
      (I.Rel (s i).1 ρ ρ' Rs w x x' ↔ Rs₂ i w y y')) (w : F.U.W)
    (v : F.U.CatVal (K.sub s) ρ) (v' : F.U.CatVal (K.sub s) ρ') (z : F.U.CatVal K ρ₂) (z' : F.U.CatVal K ρ₂'),
    HEq v z → HEq v' z' → (I.Rel (K.sub s) ρ ρ' Rs w v v' ↔ I.Rel K ρ₂ ρ₂' Rs₂ w z z') := by
  induction K with
  | e => intro m s ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ _ w v v' z z' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | t => intro m s ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ _ w v v' z z' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | var i => intro m s ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ hR w v v' z z' hv hv'; exact hR i w v v' z z' hv hv'
  | arr a b iha ihb =>
    intro m s ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR w v v' z z' hv hv'
    refine forall_congr' fun u => imp_congr Iff.rfl ?_
    refine forall_heq (Univ.CatVal_sub a s ρ ρ₂ hρ) fun q y hqy => ?_
    refine forall_heq (Univ.CatVal_sub a s ρ' ρ₂' hρ') fun q' y' hqy' => ?_
    refine imp_congr (iha s ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR u q q' y y' hqy hqy')
      (ihb s ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR u _ _ _ _ ?_ ?_)
    · exact heq_app (Univ.CatVal_sub a s ρ ρ₂ hρ) (Univ.CatVal_sub b s ρ ρ₂ hρ) hv hqy
    · exact heq_app (Univ.CatVal_sub a s ρ' ρ₂' hρ') (Univ.CatVal_sub b s ρ' ρ₂' hρ') hv' hqy'
  | pi K ih =>
    intro m s ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR w v v' z z' hv hv'
    have hl : ∀ (a : Code F.U.Base) (ρ ρ₂ : _) , (∀ i, F.U.code (s i).1 ρ = ρ₂ i) →
        ∀ i, F.U.code (liftT s i).1 (scons a ρ) = scons a ρ₂ i := fun a ρ ρ₂ h =>
      fin_cases rfl (fun i => by
        show F.U.code ((s i).1.ren fs) (scons a ρ) = ρ₂ i
        rw [Univ.code_ren]; exact h i)
    refine forall_congr' fun u => imp_congr Iff.rfl ?_
    refine forall_congr' fun a => forall_congr' fun a' => forall_congr' fun S => imp_congr Iff.rfl ?_
    refine ih (liftT s) (scons a ρ) (scons a' ρ') (RScons S Rs) (scons a ρ₂) (scons a' ρ₂') (RScons S Rs₂)
      (hl a ρ ρ₂ hρ) (hl a' ρ' ρ₂' hρ') ?_ u _ _ _ _ ?_ ?_
    · refine fin_cases ?_ (fun i => ?_)
      · intro w x x' y y' hx hx'; cases hx; cases hx'; exact Iff.rfl
      · intro w x x' y y' hx hx'
        refine (I.Rel_ren (s i).1 fs (scons a ρ) (scons a' ρ') (RScons S Rs) ρ ρ' Rs (fun _ => rfl)
          (fun _ => rfl) (fun j w z z' q q' hz hz' => by cases hz; cases hz'; exact Iff.rfl) w
          x x' (cast (Univ.CatVal_ren (s i).1 fs (scons a ρ) ρ (fun _ => rfl)) x)
          (cast (Univ.CatVal_ren (s i).1 fs (scons a' ρ') ρ' (fun _ => rfl)) x')
          (cast_heq _ _).symm (cast_heq _ _).symm).trans ?_
        exact hR i w _ _ y y' ((cast_heq _ _).trans hx) ((cast_heq _ _).trans hx')
    · exact heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ) (scons a ρ₂) (hl a ρ ρ₂ hρ)) hv rfl
    · exact heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ') (scons a ρ₂') (hl a ρ' ρ₂' hρ')) hv' rfl

/-- The logical relation persists along `R`. -/
theorem Rel_mono {n : Nat} (K : Cat n) (ρ ρ' : F.U.TEnv n) (Rs : RelV ρ ρ') (w v : F.U.W)
    (hRs : ∀ i, I.Adm w (ρ i) (ρ' i) (Rs i)) (hv : F.U.R w v) (x : F.U.CatVal K ρ) (x' : F.U.CatVal K ρ')
    (h : I.Rel K ρ ρ' Rs w x x') : I.Rel K ρ ρ' Rs v x x' := by
  cases K with
  | e => exact F.U.re_mono w v x x' hv h
  | t => exact fun u hu => h u (F.U.Rtrans _ _ _ hv hu)
  | var i => exact I.smono (hRs i) w v x x' (F.U.Rrefl w) hv h
  | arr K L => exact fun u hu => h u (F.U.Rtrans _ _ _ hv hu)
  | pi K => exact fun u hu => h u (F.U.Rtrans _ _ _ hv hu)

/-- Related values for the term variables of a context. -/
def EnvRel : {n : Nat} → (Γ : Ctx n) → (ρ ρ' : F.U.TEnv n) → RelV ρ ρ' → F.U.W →
    F.U.Env Γ ρ → F.U.Env Γ ρ' → Prop
  | _, .nil, _, _, _, _ => fun _ _ => True
  | _, .ext Γ σ, ρ, ρ', Rs, w => fun env env' => EnvRel Γ ρ ρ' Rs w env.1 env'.1 ∧ I.Rel σ.1 ρ ρ' Rs w env.2 env'.2
  | _, .text Γ, ρ, ρ', Rs, w => fun env env' =>
      EnvRel Γ (fun i => ρ (fs i)) (fun i => ρ' (fs i)) (fun i => Rs (fs i)) w env env'

theorem EnvRel_mono {n : Nat} (Γ : Ctx n) : ∀ (ρ ρ' : F.U.TEnv n) (Rs : RelV ρ ρ') (w v : F.U.W),
    (∀ i, I.Adm w (ρ i) (ρ' i) (Rs i)) → F.U.R w v → ∀ env env',
    I.EnvRel Γ ρ ρ' Rs w env env' → I.EnvRel Γ ρ ρ' Rs v env env' := by
  induction Γ with
  | nil => intros; trivial
  | ext Γ σ ih =>
    intro ρ ρ' Rs w v hRs hv env env' h
    exact ⟨ih ρ ρ' Rs w v hRs hv _ _ h.1, I.Rel_mono σ.1 ρ ρ' Rs w v hRs hv _ _ h.2⟩
  | text Γ ih =>
    intro ρ ρ' Rs w v hRs hv env env' h
    exact ih _ _ _ w v (fun i => hRs (fs i)) hv env env' h

theorem lookup_rel {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) : ∀ (ρ ρ' : F.U.TEnv n)
    (Rs : RelV ρ ρ') (w : F.U.W) (env : F.U.Env Γ ρ) (env' : F.U.Env Γ ρ'),
    I.EnvRel Γ ρ ρ' Rs w env env' → I.Rel K ρ ρ' Rs w (F.U.lookup x ρ env) (F.U.lookup x ρ' env') := by
  induction x with
  | here => intro ρ ρ' Rs w env env' h; exact h.2
  | there y ih => intro ρ ρ' Rs w env env' h; exact ih ρ ρ' Rs w env.1 env'.1 h.1
  | tthere y ih =>
    intro ρ ρ' Rs w env env' h
    refine (I.Rel_ren _ fs ρ ρ' Rs (fun i => ρ (fs i)) (fun i => ρ' (fs i)) (fun i => Rs (fs i))
      (fun _ => rfl) (fun _ => rfl) (fun i w x x' y y' hx hx' => by cases hx; cases hx'; exact Iff.rfl)
      w _ _ _ _ (F.lookup_tthere y ρ env) (F.lookup_tthere y ρ' env')).mpr ?_
    exact ih _ _ _ w env env' h

theorem const_rel {n : Nat} {K : Cat n} (c : Const n K) (ρ ρ' : F.U.TEnv n) (Rs : RelV ρ ρ') (w : F.U.W) :
    I.Rel K ρ ρ' Rs w (F.constVal c ρ) (F.constVal c ρ') := by
  cases c with
  | neg => intro v _ p p' hp u hu; exact not_congr (hp u hu)
  | imp => intro v _ p p' hp v2 hv2 q q' hq u hu; exact imp_congr (hp u (F.U.Rtrans _ _ _ hv2 hu)) (hq u hu)
  | and => intro v _ p p' hp v2 hv2 q q' hq u hu; exact and_congr (hp u (F.U.Rtrans _ _ _ hv2 hu)) (hq u hu)
  | or => intro v _ p p' hp v2 hv2 q q' hq u hu; exact or_congr (hp u (F.U.Rtrans _ _ _ hv2 hu)) (hq u hu)
  | iff => intro v _ p p' hp v2 hv2 q q' hq u hu; exact iff_congr (hp u (F.U.Rtrans _ _ _ hv2 hu)) (hq u hu)
  | all =>
    intro v _ a a' S hS v2 hv2 P P' hP u hu
    have hvu : F.U.R v u := F.U.Rtrans _ _ _ hv2 hu
    constructor
    · intro h x' hx'
      obtain ⟨x, hx, hxx⟩ := I.onto hS u hvu x' hx'
      exact (hP u hu x x' hxx u (F.U.Rrefl u)).mp (h x hx)
    · intro h x hx
      obtain ⟨x', hx', hxx⟩ := I.total hS u hvu x hx
      exact (hP u hu x x' hxx u (F.U.Rrefl u)).mpr (h x' hx')
  | ex =>
    intro v _ a a' S hS v2 hv2 P P' hP u hu
    have hvu : F.U.R v u := F.U.Rtrans _ _ _ hv2 hu
    constructor
    · rintro ⟨x, hx, h⟩
      obtain ⟨x', hx', hxx⟩ := I.total hS u hvu x hx
      exact ⟨x', hx', (hP u hu x x' hxx u (F.U.Rrefl u)).mp h⟩
    · rintro ⟨x', hx', h⟩
      obtain ⟨x, hx, hxx⟩ := I.onto hS u hvu x' hx'
      exact ⟨x, hx, (hP u hu x x' hxx u (F.U.Rrefl u)).mpr h⟩
  | tall =>
    intro v _ Q Q' hQ u hu
    exact forall_congr' fun a => imp_congr Iff.rfl ((hQ u hu a a _ (I.refl u a)) u (F.U.Rrefl u))
  | tex =>
    intro v _ Q Q' hQ u hu
    exact exists_congr fun a => and_congr Iff.rfl ((hQ u hu a a _ (I.refl u a)) u (F.U.Rrefl u))
  | eqv =>
    intro v _ a a' S hS v2 hv2 b b' T hT v3 hv3 x x' hx v4 hv4 y y' hy u hu
    have hS2 := I.amono hS hv2
    exact I.eqv hS2 hT u (F.U.Rtrans _ _ _ hv3 (F.U.Rtrans _ _ _ hv4 hu)) x x' y y'
      (I.smono hS2 v3 u x x' hv3 (F.U.Rtrans _ _ _ hv4 hu) hx)
      (I.smono hT v4 u y y' (F.U.Rtrans _ _ _ hv3 hv4) hu hy)
  | teq =>
    intro v _ a a' S hS v2 hv2 b b' T hT u hu
    exact I.teq (I.amono hS hv2) hT u hu

/-- **The fundamental lemma**: every term is related to itself, under related values for its
variables. -/
theorem fundamental {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) : ∀ (ρ ρ' : F.U.TEnv n)
    (Rs : RelV ρ ρ') (w : F.U.W), (∀ i, I.Adm w (ρ i) (ρ' i) (Rs i)) →
    ∀ (env : F.U.Env Γ ρ) (env' : F.U.Env Γ ρ'), I.EnvRel Γ ρ ρ' Rs w env env' →
    I.Rel K ρ ρ' Rs w (F.eval M ρ env) (F.eval M ρ' env') := by
  induction M with
  | var x => intro ρ ρ' Rs w _ env env' h; exact I.lookup_rel x ρ ρ' Rs w env env' h
  | const c => intro ρ ρ' Rs w _ _ _ _; exact I.const_rel c ρ ρ' Rs w
  | app f a ihf iha =>
    intro ρ ρ' Rs w hRs env env' h
    exact ihf ρ ρ' Rs w hRs env env' h w (F.U.Rrefl w) _ _ (iha ρ ρ' Rs w hRs env env' h)
  | lam σ b ih =>
    intro ρ ρ' Rs w hRs env env' h v hv u u' hu
    exact ih ρ ρ' Rs v (fun i => I.amono (hRs i) hv) (env, u) (env', u')
      ⟨I.EnvRel_mono _ ρ ρ' Rs w v hRs hv env env' h, hu⟩
  | tlam b ih =>
    intro ρ ρ' Rs w hRs env env' h v hv a a' S hS
    exact ih (scons a ρ) (scons a' ρ') (RScons S Rs) v (fin_cases hS (fun i => I.amono (hRs i) hv)) env env'
      (I.EnvRel_mono _ ρ ρ' Rs w v hRs hv env env' h)
  | tapp f σ ih =>
    intro ρ ρ' Rs w hRs env env' h
    have hf := ih ρ ρ' Rs w hRs env env' h w (F.U.Rrefl w) (F.U.code σ.1 ρ) (F.U.code σ.1 ρ') (RelE σ.1 ρ ρ' Rs)
      (I.adm_RelE σ.1 w ρ ρ' Rs hRs σ.2)
    refine (I.Rel_sub _ (inst σ) ρ ρ' Rs (scons (F.U.code σ.1 ρ) ρ) (scons (F.U.code σ.1 ρ') ρ')
      (RScons (RelE σ.1 ρ ρ' Rs) Rs) (fin_cases rfl (fun _ => rfl)) (fin_cases rfl (fun _ => rfl)) ?_
      w _ _ _ _ (F.heq_eval_tapp f σ ρ env) (F.heq_eval_tapp f σ ρ' env')).mpr hf
    refine fin_cases ?_ (fun i => ?_)
    · intro w x x' y y' hx hx'; exact I.Rel_RelE σ.1 σ.2 ρ ρ' Rs w x x' y y' hx hx'
    · intro w x x' y y' hx hx'; cases hx; cases hx'; exact Iff.rfl

end KInv

/-! ## Admissible valuations, and soundness at every world -/

namespace Frame
variable (F : Frame)

/-- The identity relations form a family of admissible relations. -/
def hom : KInv F where
  Adm := fun _ a a' S => ∃ h : a' = a, HEq S (F.U.rel a)
  amono := fun h _ => h
  smono := by
    intro w a a' S hA u u' x x' _ hu h
    obtain ⟨rfl, hS⟩ := hA
    have e := eq_of_heq hS; subst e
    exact F.U.rel_mono _ u u' x x' hu h
  refl := fun _ _ => ⟨rfl, HEq.rfl⟩
  arrow := by
    intro w a a' c c' S T hA hB
    obtain ⟨rfl, hS⟩ := hA; obtain ⟨rfl, hT⟩ := hB
    have e1 := eq_of_heq hS; have e2 := eq_of_heq hT; subst e1; subst e2
    exact ⟨rfl, HEq.rfl⟩
  total := by
    intro w a a' S hA u _ x hx
    obtain ⟨rfl, hS⟩ := hA
    have e := eq_of_heq hS; subst e
    exact ⟨x, hx, hx⟩
  onto := by
    intro w a a' S hA u _ x hx
    obtain ⟨rfl, hS⟩ := hA
    have e := eq_of_heq hS; subst e
    exact ⟨x, hx, hx⟩
  teq := by
    intro w a a' b b' S T hA hB u _
    obtain ⟨rfl, _⟩ := hA; obtain ⟨rfl, _⟩ := hB
    exact Iff.rfl
  eqv := by
    intro w a a' b b' S T hA hB u _ x x' y y' hx hy
    obtain ⟨rfl, hS⟩ := hA; obtain ⟨rfl, hT⟩ := hB
    have e1 := eq_of_heq hS; have e2 := eq_of_heq hT; subst e1; subst e2
    exact F.eqv_resp u _ _ x x' y y' hx hy

/-- The identity relations, for the type variables. -/
abbrev homRs {n : Nat} (ρ : F.U.TEnv n) : KInv.RelV (F := F) ρ ρ := fun i => F.U.rel (ρ i)

theorem homRs_adm {n : Nat} (ρ : F.U.TEnv n) (w : F.U.W) : ∀ i, F.hom.Adm w (ρ i) (ρ i) (F.homRs ρ i) :=
  fun i => F.hom.refl w (ρ i)

/-- A valuation of the term variables is admissible at a world when each value is identical to
itself there. -/
abbrev EnvAdm {n : Nat} (Γ : Ctx n) (ρ : F.U.TEnv n) (w : F.U.W) (env : F.U.Env Γ ρ) : Prop :=
  F.hom.EnvRel Γ ρ ρ (F.homRs ρ) w env env

theorem RelE_hom {n : Nat} (K : Cat n) : ∀ (_ : K.Simple) (ρ : F.U.TEnv n) (w : F.U.W) x y,
    KInv.RelE (F := F) K ρ ρ (F.homRs ρ) w x y ↔ F.U.rel (F.U.code K ρ) w x y := by
  induction K with
  | e => intros; exact Iff.rfl
  | t => intros; exact Iff.rfl
  | var i => intros; exact Iff.rfl
  | arr a b iha ihb =>
    intro hK ρ w f g
    exact forall_congr' fun v => imp_congr Iff.rfl (forall_congr' fun x => forall_congr' fun y =>
      imp_congr (iha hK.1 ρ v x y) (ihb hK.2 ρ v _ _))
  | pi _ _ => intro hK; exact hK.elim

/-- Identity, at a type, on its semantic values. -/
theorem relV_iff {n : Nat} (σ : Ty n) (ρ : F.U.TEnv n) (w : F.U.W) (u u' : F.U.CatVal σ.1 ρ) :
    F.hom.Rel σ.1 ρ ρ (F.homRs ρ) w u u' ↔
      F.U.rel (F.U.code σ.1 ρ) w (cast (Univ.El_code ρ σ.2).symm u) (cast (Univ.El_code ρ σ.2).symm u') :=
  (F.hom.Rel_RelE σ.1 σ.2 ρ ρ (F.homRs ρ) w u u' (cast (Univ.El_code ρ σ.2).symm u)
    (cast (Univ.El_code ρ σ.2).symm u') (cast_heq _ _).symm (cast_heq _ _).symm).trans
    (F.RelE_hom σ.1 σ.2 ρ w _ _)

/-- The value of a term, under an admissible valuation, is identical to itself. -/
theorem adm_eval {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) (ρ : F.U.TEnv n) (w : F.U.W)
    (env : F.U.Env Γ ρ) (h : F.EnvAdm Γ ρ w env) : F.hom.Rel K ρ ρ (F.homRs ρ) w (F.eval M ρ env) (F.eval M ρ env) :=
  F.hom.fundamental M ρ ρ (F.homRs ρ) w (F.homRs_adm ρ w) env env h

theorem EnvAdm_mono {n : Nat} {Γ : Ctx n} (ρ : F.U.TEnv n) (w v : F.U.W) (hv : F.U.R w v) (env : F.U.Env Γ ρ)
    (h : F.EnvAdm Γ ρ w env) : F.EnvAdm Γ ρ v env :=
  F.hom.EnvRel_mono Γ ρ ρ (F.homRs ρ) w v (F.homRs_adm ρ w) hv env env h

theorem D_code {n : Nat} (K : Cat n) (w : F.U.W) (ρ : F.U.TEnv n) (hρ : ∀ i, F.U.D w (ρ i)) (hK : K.Simple) :
    F.U.D w (F.U.code K ρ) := by
  induction K with
  | e => exact F.U.D_e w
  | t => exact F.U.D_t w
  | var i => exact hρ i
  | arr a b iha ihb => exact F.U.D_arr w _ _ (iha ρ hρ hK.1) (ihb ρ hρ hK.2)
  | pi _ _ => exact hK.elim

section EvalLemmas
variable {n : Nat} {Γ : Ctx n}

theorem cast_forallR {W A A' : Type} (hA : A = A') (r : W → A → A → Prop)
    (h : ((A → W → Prop) → W → Prop) = ((A' → W → Prop) → W → Prop)) (P : A' → W → Prop) (w : W) :
    cast h (fun Q : A → W → Prop => fun w => ∀ x, r w x x → Q x w) P w ↔
      ∀ x : A', r w (cast hA.symm x) (cast hA.symm x) → P x w := by
  subst hA; rw [cast_eq]; exact Iff.rfl

theorem cast_existsR {W A A' : Type} (hA : A = A') (r : W → A → A → Prop)
    (h : ((A → W → Prop) → W → Prop) = ((A' → W → Prop) → W → Prop)) (P : A' → W → Prop) (w : W) :
    cast h (fun Q : A → W → Prop => fun w => ∃ x, r w x x ∧ Q x w) P w ↔
      ∃ x : A', r w (cast hA.symm x) (cast hA.symm x) ∧ P x w := by
  subst hA; rw [cast_eq]; exact Iff.rfl

theorem holdsAt_all (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (Tm.all σ φ) ρ env w ↔ ∀ v : F.U.CatVal σ.1 ρ,
      F.U.rel (F.U.code σ.1 ρ) w (cast (Univ.El_code ρ σ.2).symm v) (cast (Univ.El_code ρ σ.2).symm v) →
      F.HoldsAt φ ρ (env, v) w :=
  cast_forallR (Univ.El_code ρ σ.2) _ _ _ _

theorem holdsAt_ex (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (Tm.ex σ φ) ρ env w ↔ ∃ v : F.U.CatVal σ.1 ρ,
      F.U.rel (F.U.code σ.1 ρ) w (cast (Univ.El_code ρ σ.2).symm v) (cast (Univ.El_code ρ σ.2).symm v) ∧
      F.HoldsAt φ ρ (env, v) w :=
  cast_existsR (Univ.El_code ρ σ.2) _ _ _ _

theorem holdsAt_tall (φ : Fm (.text Γ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (Tm.tall φ) ρ env w ↔ ∀ a, F.U.D w a → F.HoldsAt φ (scons a ρ) env w := Iff.rfl

theorem holdsAt_tex (φ : Fm (.text Γ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (Tm.tex φ) ρ env w ↔ ∃ a, F.U.D w a ∧ F.HoldsAt φ (scons a ρ) env w := Iff.rfl

theorem holdsAt_imp (φ ψ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (φ.imp ψ) ρ env w ↔ (F.HoldsAt φ ρ env w → F.HoldsAt ψ ρ env w) := Iff.rfl
theorem holdsAt_neg (φ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt φ.neg ρ env w ↔ ¬ F.HoldsAt φ ρ env w := Iff.rfl
theorem holdsAt_conj (φ ψ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (φ.conj ψ) ρ env w ↔ (F.HoldsAt φ ρ env w ∧ F.HoldsAt ψ ρ env w) := Iff.rfl
theorem holdsAt_iff (φ ψ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (φ.iff ψ) ρ env w ↔ (F.HoldsAt φ ρ env w ↔ F.HoldsAt ψ ρ env w) := Iff.rfl

theorem holdsAt_inst {k : Nat} (P : PF k) (as : Fin k → Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (P.inst as) ρ env w ↔ P.evalP (fun i => F.HoldsAt (as i) ρ env w) := by
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

theorem eval_eqv (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.eval (Tm.eqv σ τ x y) ρ env =
      F.eqv (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) (cast (Univ.El_code ρ σ.2).symm (F.eval x ρ env))
        (cast (Univ.El_code ρ τ.2).symm (F.eval y ρ env)) :=
  (app2_heq (A := F.U.CatVal σ.1 ρ) (B := F.U.CatVal τ.1 ρ)
    (f := F.eval (Tm.castK (Tm.eqv_cat σ τ) (Tm.tapp (Tm.tapp (Tm.const Const.eqv) σ) τ)) ρ env)
    (Univ.El_code ρ σ.2).symm (Univ.El_code ρ τ.2).symm (F.eval_eqvConst σ τ ρ env) _ _)

theorem holdsAt_eqv (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (Tm.eqv σ τ x y) ρ env w ↔
      F.eqv (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) (cast (Univ.El_code ρ σ.2).symm (F.eval x ρ env))
        (cast (Univ.El_code ρ τ.2).symm (F.eval y ρ env)) w :=
  Iff.of_eq (congrFun (F.eval_eqv σ τ x y ρ env) w)

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

theorem EnvAdm_pull {n : Nat} (Γ : Ctx n) : ∀ {m : Nat} {r : Fin n → Fin m} {Δ : Ctx m} (ρr : TRen r Γ Δ)
    (ρ' : F.U.TEnv m) (w : F.U.W) (env' : F.U.Env Δ ρ'), F.EnvAdm Δ ρ' w env' →
    F.EnvAdm Γ (fun i => ρ' (r i)) w (F.pullEnv Γ ρr ρ' env') := by
  induction Γ with
  | nil => intros; trivial
  | ext Γ σ ih =>
    intro m r Δ ρr ρ' w env' h
    refine ⟨ih (fun x => ρr (.there x)) ρ' w env' h, ?_⟩
    have hl := F.hom.lookup_rel (ρr .here) ρ' ρ' (F.homRs ρ') w env' env' h
    exact (F.hom.Rel_ren σ.1 r ρ' ρ' (F.homRs ρ') (fun i => ρ' (r i)) (fun i => ρ' (r i)) (F.homRs _)
      (fun _ => rfl) (fun _ => rfl) (fun i w x x' y y' hx hx' => by cases hx; cases hx'; exact Iff.rfl) w
      _ _ _ _ (cast_heq _ _).symm (cast_heq _ _).symm).mp hl
  | text Γ ih =>
    intro m r Δ ρr ρ' w env' h
    exact ih (r := fun i => r (fs i)) (fun x => Var.castK (Cat.ren_ren _ _ _) (ρr (.tthere x))) ρ' w env' h

theorem holdsAt_of_heq {n m : Nat} {Γ : Ctx n} {Δ : Ctx m} {φ : Fm Γ} {ψ : Fm Δ} {ρ : F.U.TEnv n}
    {ρ' : F.U.TEnv m} {env : F.U.Env Γ ρ} {env' : F.U.Env Δ ρ'} (h : HEq (F.eval φ ρ env) (F.eval ψ ρ' env'))
    (w : F.U.W) : F.HoldsAt φ ρ env w = F.HoldsAt ψ ρ' env' w :=
  congrArg (fun f : F.U.CatVal Cat.t ρ => F.U.ap f w) (eq_of_heq h)

/-- Truth at every world, under every valuation admissible there. -/
def ValidAt {n : Nat} {Γ : Ctx n} (φ : Fm Γ) : Prop :=
  ∀ w ρ, (∀ i, F.U.D w (ρ i)) → ∀ env, F.EnvAdm Γ ρ w env → F.HoldsAt φ ρ env w

/-- Truth at the actual world, under every valuation admissible there. -/
def Valid {n : Nat} {Γ : Ctx n} (φ : Fm Γ) : Prop :=
  ∀ ρ, (∀ i, F.U.D F.U.w0 (ρ i)) → ∀ env, F.EnvAdm Γ ρ F.U.w0 env → F.HoldsAt φ ρ env F.U.w0

/-- The identity axioms of PI⁻ hold at every world. -/
structure IsModelAt : Prop where
  refEqv : F.ValidAt RefEqv
  symEqv : F.ValidAt SymEqv
  transEqv : F.ValidAt TransEqv
  refTeq : F.ValidAt RefTeq
  llTeq : ∀ {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)), F.ValidAt (LLTeq Q)

theorem adm_of_rel {n : Nat} (σ : Ty n) (ρ : F.U.TEnv n) (w : F.U.W) (v : F.U.CatVal σ.1 ρ)
    (h : F.U.rel (F.U.code σ.1 ρ) w (cast (Univ.El_code ρ σ.2).symm v) (cast (Univ.El_code ρ σ.2).symm v)) :
    F.hom.Rel σ.1 ρ ρ (F.homRs ρ) w v v := (F.relV_iff σ ρ w v v).mpr h

/-- **Soundness at every world.** -/
theorem soundnessAt {Ax : Fm Ctx.nil → Prop} (hM : F.IsModelAt) (hAx : ∀ φ, Ax φ → F.ValidAt φ)
    {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : Prov Ax Γ φ) : F.ValidAt φ := by
  induction h with
  | taut P as hP => intro w ρ _ env _; exact (F.holdsAt_inst P as ρ env w).mpr (hP _)
  | instAll σ φ κ =>
    intro w ρ _ env henv h
    show F.HoldsAt (φ.subst0 κ) ρ env w
    unfold HoldsAt; rw [eval_subst0]
    exact (F.holdsAt_all σ φ ρ env w).mp h _ ((F.relV_iff σ ρ w _ _).mp (F.adm_eval κ ρ w env henv))
  | distAll σ φ ψ =>
    intro w ρ _ env _ h hφ
    refine (F.holdsAt_all σ ψ ρ env w).mpr fun v hv => ?_
    have h' := (F.holdsAt_all σ _ ρ env w).mp h v hv
    have hw : F.HoldsAt (φ.wk σ) ρ (env, v) w := by unfold HoldsAt; rw [eval_wk]; exact hφ
    exact h' hw
  | dualEx σ φ =>
    intro w ρ _ env _
    refine (F.holdsAt_ex σ φ ρ env w).trans ?_
    refine Iff.trans ?_ (not_congr (F.holdsAt_all σ φ.neg ρ env w)).symm
    constructor
    · rintro ⟨v, hv, h⟩ h'; exact h' v hv h
    · intro h; exact Classical.byContradiction fun hn => h fun v hv h' => hn ⟨v, hv, h'⟩
  | instTAll φ σ =>
    intro w ρ hρ env _ h
    exact cast ((congrArg (fun f : F.U.W → Prop => f w)) (eq_of_heq (F.eval_tinst φ σ ρ env))).symm
      (h (F.U.code σ.1 ρ) (F.D_code σ.1 w ρ hρ σ.2))
  | distTAll φ ψ =>
    intro w ρ _ env _ h hφ a ha
    exact h a ha (cast ((congrArg (fun f : F.U.W → Prop => f w)) (eq_of_heq (F.eval_twk φ a ρ env))).symm hφ)
  | dualTEx φ =>
    intro w ρ _ env _
    show (∃ a, F.U.D w a ∧ F.HoldsAt φ (scons a ρ) env w) ↔ ¬ ∀ a, F.U.D w a → ¬ F.HoldsAt φ (scons a ρ) env w
    constructor
    · rintro ⟨a, ha, h⟩ h'; exact h' a ha h
    · intro h; exact Classical.byContradiction fun hn => h fun a ha h' => hn ⟨a, ha, h'⟩
  | beta h => intro w ρ _ env _; exact Iff.of_eq ((congrArg (fun f : F.U.W → Prop => f w)) (F.eval_betaEq h ρ env))
  | refEqv => exact hM.refEqv
  | symEqv => exact hM.symEqv
  | transEqv => exact hM.transEqv
  | refTeq => exact hM.refTeq
  | llTeq Q => exact hM.llTeq Q
  | ax h => exact hAx _ h
  | mp _ _ ih1 ih2 => intro w ρ hρ env henv; exact ih2 w ρ hρ env henv (ih1 w ρ hρ env henv)
  | genAll σ _ ih =>
    intro w ρ hρ env henv
    exact (F.holdsAt_all σ _ ρ env w).mpr fun v hv => ih w ρ hρ (env, v) ⟨henv, F.adm_of_rel σ ρ w v hv⟩
  | genTAll _ ih => intro w ρ hρ env henv a ha; exact ih w (scons a ρ) (fin_cases ha hρ) env henv
  | ren ρr _ ih =>
    intro w ρ' hρ' env' henv'
    exact cast (F.holdsAt_of_heq (F.eval_ren _ ρr ρ' env' _ (F.pullEnv _ ρr ρ' env') (fun _ => rfl)
      (fun x => F.lookup_pull x ρr ρ' env')) w).symm
      (ih w _ (fun i => hρ' _) _ (F.EnvAdm_pull _ ρr ρ' w env' henv'))
  | strengthen σ _ ih =>
    intro w ρ hρ env henv
    obtain ⟨x, hx⟩ := F.U.adm_nonempty (F.U.code σ.1 ρ)
    have hv : F.U.rel (F.U.code σ.1 ρ) w (cast (Univ.El_code ρ σ.2).symm (cast (Univ.El_code ρ σ.2) x))
        (cast (Univ.El_code ρ σ.2).symm (cast (Univ.El_code ρ σ.2) x)) := by
      rw [cast_cast, cast_eq]; exact hx w
    have := ih w ρ hρ (env, cast (Univ.El_code ρ σ.2) x) ⟨henv, F.adm_of_rel σ ρ w _ hv⟩
    unfold HoldsAt at this
    rwa [eval_wk] at this
  | tstrengthen _ ih =>
    intro w ρ hρ env henv
    exact cast (F.holdsAt_of_heq (F.eval_twk _ .e ρ env) w) (ih w (scons .e ρ) (fin_cases (F.U.D_e w) hρ) env henv)

end Frame

end Kr
end PIF
