/-!
# The logic of polymorphic identity, PI: a deep embedding

Isaac Wilhelm, *Formal Results* (Draft 5) and the paper on polymorphic identity.

This file writes out, as data, the language of PI (a fragment of the predicative calculus of
constructions), its proof system, and its models; it then proves that the proof system is
**sound**: whatever PI proves is true in every model. Unlike the earlier shallow embedding
(`Drafts/Lean/PolymorphicIdentity.lean`), derivations here are derivations in PI itself, and
models are arbitrary interpretations of `≡` and `≈`; nothing forces `≈` to be identity.

With soundness in hand, a model in which a principle is false shows that PI does not prove it.
That is how the independence results of *Formal Results* will be checked, in later files.

Contents
1. Categories (the types `σ` and the kinds `Πα:∗.K`), with renaming and substitution.
2. Contexts, variables, constants, and terms, intrinsically typed.
3. Renaming and substitution of terms.
4. Models: type universes, frames, and the semantic value of every term.
5. The semantic substitution lemmas.
6. β-conversion.
7. The proof system PI (and PI⁻), and its soundness.
8. Consistency: PI has a model.
9. Invariance (parametricity): the fundamental lemma, and when LL≈ and LL≡-Poly hold.

No Mathlib. Checked with Lean 4.34.1: `lean PIFoundation.lean` prints nothing when every proof
checks.

## Representation choices (and where they depart from the paper)

* **Types are kept in normal form.** By lemma `normaltypes`(a) of *Formal Results*, every type is
  β-equivalent to a simple normal type, built from `e`, `t`, and type variables by `→`. So types
  are represented only in that form, and type-level λ-abstraction (type operators such as
  `λα:∗.α→t`) is left out. The categories are the simple normal types together with the kinds
  `Πα:∗.K` and arrows between categories (for instance `(Πα:∗.t)→t`, the category of `𝔸`).
* **Bound variables are de Bruijn indices**, so terms differing only in bound variables are
  literally equal, which is the paper's convention that such terms are identified.
* **Terms are intrinsically typed**: a term is indexed by its context and its category, so only
  well-formed terms exist.
* **Term variables have types**, as in the paper (the term variables of lemma `normaltypes`(b));
  terms of a `Π`-category arise only as constants, type abstractions, and their applications.
* **Variables live in contexts.** The paper gives each variable a fixed type. Here a derivation
  is of a formula in a context, and three structural rules (renaming, and discarding an unused
  term or type variable) do the work that the fixed typing does implicitly. Discarding a variable
  is sound because every type is non-empty, which is the role non-emptiness plays in the paper.
* **The connectives `∧`, `∨`, `↔` are constants**, as in the paper. The propositional axioms are
  all instances of tautologies, which is what "all instances of the axioms of classical
  propositional logic" amounts to.
-/

set_option autoImplicit false

namespace PIF

universe u

/-! ## 1. Categories -/

/-- The first element of `Fin (n+1)`. -/
def fz {n : Nat} : Fin (n+1) := ⟨0, Nat.succ_pos n⟩
/-- The successor map `Fin n → Fin (n+1)`. -/
def fs {n : Nat} (i : Fin n) : Fin (n+1) := ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩

/-- Extend a function on `Fin n` to `Fin (n+1)` by giving it the value `a` at `fz`. -/
def scons {α : Sort u} {n : Nat} (a : α) (f : Fin n → α) : Fin (n+1) → α
  | ⟨0, _⟩ => a
  | ⟨k+1, h⟩ => f ⟨k, Nat.lt_of_succ_lt_succ h⟩

@[simp] theorem scons_fz {α : Sort u} {n : Nat} (a : α) (f : Fin n → α) : scons a f fz = a := rfl
@[simp] theorem scons_fs {α : Sort u} {n : Nat} (a : α) (f : Fin n → α) (i : Fin n) :
    scons a f (fs i) = f i := rfl

/-- Proof by cases on an element of `Fin (n+1)`. -/
theorem fin_cases {n : Nat} {P : Fin (n+1) → Prop} (h0 : P fz) (hs : ∀ i, P (fs i)) : ∀ i, P i
  | ⟨0, _⟩ => h0
  | ⟨k+1, h⟩ => hs ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- Categories with `n` free type variables. `e` and `t` are the types of entities and of
propositions; `var i` is a type variable (a de Bruijn index); `arr K L` is `K → L`; and `pi K` is
`Πα:∗.K`, binding the type variable `fz` in `K`. -/
inductive Cat : Nat → Type where
  | e {n : Nat} : Cat n
  | t {n : Nat} : Cat n
  | var {n : Nat} : Fin n → Cat n
  | arr {n : Nat} : Cat n → Cat n → Cat n
  | pi {n : Nat} : Cat (n+1) → Cat n

namespace Cat

/-- A category is a *type* (has category `∗`) when it contains no `Π`. -/
def Simple {n : Nat} : Cat n → Prop
  | e => True
  | t => True
  | var _ => True
  | arr a b => a.Simple ∧ b.Simple
  | pi _ => False

end Cat

/-- Types: the categories which are types. Type quantifiers range over these, and only these
can be substituted for a type variable; that is the predicativity of the calculus. -/
abbrev Ty (n : Nat) := {K : Cat n // K.Simple}

/-- Lift a renaming of type variables under a binder. -/
def liftR {n m : Nat} (r : Fin n → Fin m) : Fin (n+1) → Fin (m+1) := scons fz (fun i => fs (r i))

namespace Cat

/-- Renaming of type variables. -/
def ren {n m : Nat} (r : Fin n → Fin m) : Cat n → Cat m
  | e => e
  | t => t
  | var i => var (r i)
  | arr a b => arr (a.ren r) (b.ren r)
  | pi K => pi (K.ren (liftR r))

theorem ren_congr {n : Nat} (K : Cat n) : ∀ {m : Nat} {r r' : Fin n → Fin m},
    (∀ i, r i = r' i) → K.ren r = K.ren r' := by
  induction K with
  | e => intros; rfl
  | t => intros; rfl
  | var i => intro m r r' h; simp only [ren, h]
  | arr a b iha ihb => intro m r r' h; simp only [ren, iha h, ihb h]
  | pi K ih =>
    intro m r r' h
    simp only [ren]
    congr 1
    exact ih (fin_cases rfl (fun i => by simp [liftR, h]))

theorem ren_ren {n : Nat} (K : Cat n) : ∀ {m k : Nat} (r : Fin n → Fin m) (r' : Fin m → Fin k),
    (K.ren r).ren r' = K.ren (fun i => r' (r i)) := by
  induction K with
  | e => intros; rfl
  | t => intros; rfl
  | var i => intros; rfl
  | arr a b iha ihb => intro m k r r'; simp only [ren, iha, ihb]
  | pi K ih =>
    intro m k r r'
    simp only [ren, ih]
    congr 1
    exact ren_congr K (fin_cases rfl (fun i => rfl))

theorem ren_id {n : Nat} (K : Cat n) : K.ren (fun i => i) = K := by
  induction K with
  | e => rfl
  | t => rfl
  | var i => rfl
  | arr a b iha ihb => simp only [ren, iha, ihb]
  | pi K ih =>
    simp only [ren]
    congr 1
    rw [ren_congr K (r' := fun i => i) (fin_cases rfl (fun i => rfl))]
    exact ih

theorem Simple_ren {n : Nat} {K : Cat n} : ∀ {m : Nat} (r : Fin n → Fin m), K.Simple → (K.ren r).Simple := by
  induction K with
  | e => intros; trivial
  | t => intros; trivial
  | var i => intros; trivial
  | arr a b iha ihb => intro m r h; exact ⟨iha r h.1, ihb r h.2⟩
  | pi K _ => intro m r h; exact h.elim

end Cat

/-- The type variable `i`, as a type. -/
def tvar {n : Nat} (i : Fin n) : Ty n := ⟨Cat.var i, trivial⟩

def Ty.ren {n m : Nat} (σ : Ty n) (r : Fin n → Fin m) : Ty m := ⟨σ.1.ren r, Cat.Simple_ren r σ.2⟩

/-- Lift a substitution of types for type variables under a binder. -/
def liftT {n m : Nat} (s : Fin n → Ty m) : Fin (n+1) → Ty (m+1) := scons (tvar fz) (fun i => (s i).ren fs)

namespace Cat

/-- Simultaneous substitution of types for type variables. -/
def sub {n m : Nat} (s : Fin n → Ty m) : Cat n → Cat m
  | e => e
  | t => t
  | var i => (s i).1
  | arr a b => arr (a.sub s) (b.sub s)
  | pi K => pi (K.sub (liftT s))

theorem sub_congr {n : Nat} (K : Cat n) : ∀ {m : Nat} {s s' : Fin n → Ty m},
    (∀ i, (s i).1 = (s' i).1) → K.sub s = K.sub s' := by
  induction K with
  | e => intros; rfl
  | t => intros; rfl
  | var i => intro m s s' h; exact h i
  | arr a b iha ihb => intro m s s' h; simp only [sub, iha h, ihb h]
  | pi K ih =>
    intro m s s' h
    simp only [sub]
    congr 1
    exact ih (fin_cases rfl (fun i => by simp only [liftT, scons_fs, Ty.ren, h]))

theorem Simple_sub {n : Nat} {K : Cat n} : ∀ {m : Nat} (s : Fin n → Ty m), K.Simple → (K.sub s).Simple := by
  induction K with
  | e => intros; trivial
  | t => intros; trivial
  | var i => intro m s _; exact (s i).2
  | arr a b iha ihb => intro m s h; exact ⟨iha s h.1, ihb s h.2⟩
  | pi K _ => intro m s h; exact h.elim

theorem sub_ren {n : Nat} (K : Cat n) : ∀ {m k : Nat} (r : Fin n → Fin m) (s : Fin m → Ty k),
    (K.ren r).sub s = K.sub (fun i => s (r i)) := by
  induction K with
  | e => intros; rfl
  | t => intros; rfl
  | var i => intros; rfl
  | arr a b iha ihb => intro m k r s; simp only [ren, sub, iha, ihb]
  | pi K ih =>
    intro m k r s
    simp only [ren, sub, ih]
    congr 1
    exact sub_congr K (fin_cases rfl (fun i => rfl))

theorem ren_sub {n : Nat} (K : Cat n) : ∀ {m k : Nat} (s : Fin n → Ty m) (r : Fin m → Fin k),
    (K.sub s).ren r = K.sub (fun i => (s i).ren r) := by
  induction K with
  | e => intros; rfl
  | t => intros; rfl
  | var i => intros; rfl
  | arr a b iha ihb => intro m k s r; simp only [ren, sub, iha, ihb]
  | pi K ih =>
    intro m k s r
    simp only [ren, sub, ih]
    congr 1
    refine sub_congr K (fin_cases rfl (fun i => ?_))
    show (((s i).1.ren fs).ren (liftR r)) = ((s i).1.ren r).ren fs
    rw [ren_ren, ren_ren]
    rfl

theorem sub_sub {n : Nat} (K : Cat n) : ∀ {m k : Nat} (s : Fin n → Ty m) (s' : Fin m → Ty k),
    (K.sub s).sub s' = K.sub (fun i => ⟨((s i).1).sub s', Simple_sub s' (s i).2⟩) := by
  induction K with
  | e => intros; rfl
  | t => intros; rfl
  | var i => intros; rfl
  | arr a b iha ihb => intro m k s s'; simp only [sub, iha, ihb]
  | pi K ih =>
    intro m k s s'
    simp only [sub, ih]
    congr 1
    refine sub_congr K (fin_cases rfl (fun i => ?_))
    show (((s i).1.ren fs).sub (liftT s')) = ((s i).1.sub s').ren fs
    rw [sub_ren, ren_sub]
    rfl

theorem sub_var {n : Nat} (K : Cat n) : K.sub tvar = K := by
  induction K with
  | e => rfl
  | t => rfl
  | var i => rfl
  | arr a b iha ihb => simp only [sub, iha, ihb]
  | pi K ih =>
    simp only [sub]
    congr 1
    exact (sub_congr K (s := liftT tvar) (s' := tvar) (fin_cases rfl (fun i => rfl))).trans ih

end Cat

def Ty.sub {n m : Nat} (σ : Ty n) (s : Fin n → Ty m) : Ty m := ⟨σ.1.sub s, Cat.Simple_sub s σ.2⟩

/-- Single substitution: `σ` for the type variable `fz`. -/
def inst {n : Nat} (σ : Ty n) : Fin (n+1) → Ty n := scons σ tvar

/-- Shifting a category by `fs` and then instantiating `fz` gives it back. -/
theorem Cat.ren_fs_inst {n : Nat} (K : Cat n) (σ : Ty n) : (K.ren fs).sub (inst σ) = K := by
  rw [Cat.sub_ren]; exact Cat.sub_var K

/-! ## 2. Contexts, variables, constants, and terms -/

/-- Contexts. `ext Γ σ` adds a term variable of type `σ`; `text Γ` adds a type variable,
which becomes the type variable `fz`, the older ones being shifted by `fs`. As in the paper,
every term variable has a type (a simple normal type) as its category. -/
inductive Ctx : Nat → Type where
  | nil : Ctx 0
  | ext {n : Nat} : Ctx n → Ty n → Ctx n
  | text {n : Nat} : Ctx n → Ctx (n+1)

/-- Variables, as positions in a context, with their categories. -/
inductive Var : {n : Nat} → Ctx n → Cat n → Type where
  | here {n : Nat} {Γ : Ctx n} {σ : Ty n} : Var (.ext Γ σ) σ.1
  | there {n : Nat} {Γ : Ctx n} {K : Cat n} {σ : Ty n} : Var Γ K → Var (.ext Γ σ) K
  | tthere {n : Nat} {Γ : Ctx n} {K : Cat n} : Var Γ K → Var (.text Γ) (K.ren fs)

/-- The constants of PI and their categories (table in §1 of *Formal Results*). -/
inductive Const : (n : Nat) → Cat n → Type where
  | neg {n : Nat} : Const n (.arr .t .t)
  | imp {n : Nat} : Const n (.arr .t (.arr .t .t))
  | and {n : Nat} : Const n (.arr .t (.arr .t .t))
  | or {n : Nat} : Const n (.arr .t (.arr .t .t))
  | iff {n : Nat} : Const n (.arr .t (.arr .t .t))
  /-- `∀ : Πα:∗.(α→t)→t` -/
  | all {n : Nat} : Const n (.pi (.arr (.arr (.var fz) .t) .t))
  /-- `∃ : Πα:∗.(α→t)→t` -/
  | ex {n : Nat} : Const n (.pi (.arr (.arr (.var fz) .t) .t))
  /-- `𝔸 : (Πα:∗.t)→t` -/
  | tall {n : Nat} : Const n (.arr (.pi .t) .t)
  /-- `𝔼 : (Πα:∗.t)→t` -/
  | tex {n : Nat} : Const n (.arr (.pi .t) .t)
  /-- `≡ : Πα:∗.Πβ:∗.α→β→t` -/
  | eqv {n : Nat} : Const n (.pi (.pi (.arr (.var (fs fz)) (.arr (.var fz) .t))))
  /-- `≈ : Πα:∗.Πβ:∗.t` -/
  | teq {n : Nat} : Const n (.pi (.pi .t))

def Const.ren {n m : Nat} (r : Fin n → Fin m) : {K : Cat n} → Const n K → Const m (K.ren r)
  | _, .neg => .neg
  | _, .imp => .imp
  | _, .and => .and
  | _, .or => .or
  | _, .iff => .iff
  | _, .all => .all
  | _, .ex => .ex
  | _, .tall => .tall
  | _, .tex => .tex
  | _, .eqv => .eqv
  | _, .teq => .teq

def Const.sub {n m : Nat} (s : Fin n → Ty m) : {K : Cat n} → Const n K → Const m (K.sub s)
  | _, .neg => .neg
  | _, .imp => .imp
  | _, .and => .and
  | _, .or => .or
  | _, .iff => .iff
  | _, .all => .all
  | _, .ex => .ex
  | _, .tall => .tall
  | _, .tex => .tex
  | _, .eqv => .eqv
  | _, .teq => .teq

/-- Terms in context `Γ` of category `K`. A *formula* is a term of category `t`; a *sentence* is a
formula in the empty context. `tapp M σ` applies a term of category `Πα:∗.K` to the type `σ`. -/
inductive Tm : {n : Nat} → Ctx n → Cat n → Type where
  | var {n : Nat} {Γ : Ctx n} {K : Cat n} : Var Γ K → Tm Γ K
  | const {n : Nat} {Γ : Ctx n} {K : Cat n} : Const n K → Tm Γ K
  | app {n : Nat} {Γ : Ctx n} {K L : Cat n} : Tm Γ (.arr K L) → Tm Γ K → Tm Γ L
  | lam {n : Nat} {Γ : Ctx n} (σ : Ty n) {L : Cat n} : Tm (.ext Γ σ) L → Tm Γ (.arr σ.1 L)
  | tlam {n : Nat} {Γ : Ctx n} {K : Cat (n+1)} : Tm (.text Γ) K → Tm Γ (.pi K)
  | tapp {n : Nat} {Γ : Ctx n} {K : Cat (n+1)} : Tm Γ (.pi K) → (σ : Ty n) → Tm Γ (K.sub (inst σ))

/-- Formulas. -/
abbrev Fm {n : Nat} (Γ : Ctx n) := Tm Γ .t

/-- Change the category index of a variable along an equation. -/
def Var.castK {n : Nat} {Γ : Ctx n} {K K' : Cat n} (h : K = K') (x : Var Γ K) : Var Γ K' := h ▸ x

/-- Change the category index of a term along an equation. -/
def Tm.castK {n : Nat} {Γ : Ctx n} {K K' : Cat n} (h : K = K') (M : Tm Γ K) : Tm Γ K' := h ▸ M

/-! ## 3. Renaming and substitution of terms -/

/-- A renaming of term variables from `Γ` to `Δ`, along a renaming `r` of type variables. -/
def TRen {n m : Nat} (r : Fin n → Fin m) (Γ : Ctx n) (Δ : Ctx m) : Type :=
  ∀ {K : Cat n}, Var Γ K → Var Δ (K.ren r)

theorem Cat.ren_fs_liftR {n m : Nat} (K : Cat n) (r : Fin n → Fin m) :
    (K.ren r).ren fs = (K.ren fs).ren (liftR r) := by
  rw [Cat.ren_ren, Cat.ren_ren]; rfl

def TRen.lift {n m : Nat} {r : Fin n → Fin m} {Γ : Ctx n} {Δ : Ctx m} (ρ : TRen r Γ Δ) (σ : Ty n) :
    TRen r (.ext Γ σ) (.ext Δ (σ.ren r)) := fun {_} x =>
  match x with
  | .here => .here
  | .there x => .there (ρ x)

def TRen.tlift {n m : Nat} {r : Fin n → Fin m} {Γ : Ctx n} {Δ : Ctx m} (ρ : TRen r Γ Δ) :
    TRen (liftR r) (.text Γ) (.text Δ) := fun {_} x =>
  match x with
  | .tthere (K := K) x => Var.castK (Cat.ren_fs_liftR K r) (Var.tthere (ρ x))

theorem Cat.tapp_ren {n m : Nat} (K : Cat (n+1)) (σ : Ty n) (r : Fin n → Fin m) :
    (K.ren (liftR r)).sub (inst (σ.ren r)) = (K.sub (inst σ)).ren r := by
  rw [Cat.sub_ren, Cat.ren_sub]
  exact Cat.sub_congr K (fin_cases rfl (fun i => rfl))

/-- Renaming of terms. -/
def Tm.ren {n m : Nat} {r : Fin n → Fin m} {Γ : Ctx n} {Δ : Ctx m} (ρ : TRen r Γ Δ) :
    {K : Cat n} → Tm Γ K → Tm Δ (K.ren r)
  | _, .var x => .var (ρ x)
  | _, .const c => .const (c.ren r)
  | _, .app f a => .app (f.ren ρ) (a.ren ρ)
  | _, .lam σ b => .lam (σ.ren r) (b.ren (ρ.lift σ))
  | _, .tlam b => .tlam (b.ren ρ.tlift)
  | _, .tapp (K := K) f σ => Tm.castK (Cat.tapp_ren K σ r) (Tm.tapp (f.ren ρ) (σ.ren r))

/-- The renaming which adds a term variable at the front. -/
def wkRen {n : Nat} {Γ : Ctx n} (L : Ty n) : TRen (fun i => i) Γ (.ext Γ L) := fun {K} x =>
  Var.castK (Cat.ren_id K).symm (Var.there x)

/-- Weakening: a term in `Γ` is a term in `Γ` extended by one more term variable. -/
def Tm.wk {n : Nat} {Γ : Ctx n} {K : Cat n} (L : Ty n) (M : Tm Γ K) : Tm (.ext Γ L) K :=
  Tm.castK (Cat.ren_id K) (M.ren (wkRen L))

/-- The renaming which adds a type variable at the front. -/
def twkRen {n : Nat} (Γ : Ctx n) : TRen fs Γ (.text Γ) := fun x => .tthere x

/-- Type weakening. -/
def Tm.twk {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) : Tm (.text Γ) (K.ren fs) := M.ren (twkRen Γ)

/-- A substitution of terms for the term variables of `Γ`, along a substitution `s` of types for
type variables. -/
def TSub {n m : Nat} (s : Fin n → Ty m) (Γ : Ctx n) (Δ : Ctx m) : Type :=
  ∀ {K : Cat n}, Var Γ K → Tm Δ (K.sub s)

def TSub.lift {n m : Nat} {s : Fin n → Ty m} {Γ : Ctx n} {Δ : Ctx m} (σs : TSub s Γ Δ) (σ : Ty n) :
    TSub s (.ext Γ σ) (.ext Δ (σ.sub s)) := fun {_} x =>
  match x with
  | .here => .var .here
  | .there x => (σs x).wk _

theorem Cat.sub_fs_liftT {n m : Nat} (K : Cat n) (s : Fin n → Ty m) :
    (K.sub s).ren fs = (K.ren fs).sub (liftT s) := by
  rw [Cat.ren_sub, Cat.sub_ren]; rfl

def TSub.tlift {n m : Nat} {s : Fin n → Ty m} {Γ : Ctx n} {Δ : Ctx m} (σs : TSub s Γ Δ) :
    TSub (liftT s) (.text Γ) (.text Δ) := fun {_} x =>
  match x with
  | .tthere (K := K) x => Tm.castK (Cat.sub_fs_liftT K s) (σs x).twk

theorem Cat.tapp_sub {n m : Nat} (K : Cat (n+1)) (σ : Ty n) (s : Fin n → Ty m) :
    (K.sub (liftT s)).sub (inst (σ.sub s)) = (K.sub (inst σ)).sub s := by
  rw [Cat.sub_sub, Cat.sub_sub]
  refine Cat.sub_congr K (fin_cases rfl (fun i => ?_))
  show ((s i).1.ren fs).sub (inst (σ.sub s)) = (s i).1
  exact Cat.ren_fs_inst _ _

/-- Substitution in terms. -/
def Tm.sub {n m : Nat} {s : Fin n → Ty m} {Γ : Ctx n} {Δ : Ctx m} (σs : TSub s Γ Δ) :
    {K : Cat n} → Tm Γ K → Tm Δ (K.sub s)
  | _, .var x => σs x
  | _, .const c => .const (c.sub s)
  | _, .app f a => .app (f.sub σs) (a.sub σs)
  | _, .lam σ b => .lam (σ.sub s) (b.sub (σs.lift σ))
  | _, .tlam b => .tlam (b.sub σs.tlift)
  | _, .tapp (K := K) f σ => Tm.castK (Cat.tapp_sub K σ s) (Tm.tapp (f.sub σs) (σ.sub s))

/-- The substitution sending `here` to `N` and every other variable to itself. -/
def sub0 {n : Nat} {Γ : Ctx n} {σ : Ty n} (N : Tm Γ σ.1) : TSub tvar (.ext Γ σ) Γ := fun {_} x =>
  match x with
  | .here => Tm.castK (Cat.sub_var σ.1).symm N
  | .there y => Tm.castK (Cat.sub_var _).symm (.var y)

/-- Substituting `N` for the term variable `here`. -/
def Tm.subst0 {n : Nat} {Γ : Ctx n} {σ : Ty n} {L : Cat n} (M : Tm (.ext Γ σ) L) (N : Tm Γ σ.1) : Tm Γ L :=
  Tm.castK (Cat.sub_var L) (M.sub (sub0 N))

/-- The substitution sending each variable of `text Γ` back to itself in `Γ`, with `σ` for `fz`. -/
def tsub0 {n : Nat} (Γ : Ctx n) (σ : Ty n) : TSub (inst σ) (.text Γ) Γ := fun {_} x =>
  match x with
  | .tthere (K := K') y => Tm.castK (Cat.ren_fs_inst K' σ).symm (.var y)

/-- Substituting the type `σ` for the type variable `fz`. -/
def Tm.tinst {n : Nat} {Γ : Ctx n} {K : Cat (n+1)} (M : Tm (.text Γ) K) (σ : Ty n) : Tm Γ (K.sub (inst σ)) :=
  M.sub (tsub0 Γ σ)

/-! ## 4. Models

A *type universe* has a set `E` of entities, the set `Prop` of truth values for `t` (classical,
since Lean's logic is used classically below), and some further sets `B b` for `b : Base`; its
members are the sets built from these by `→`, named by *codes*. Type variables take codes as
values. Every member is non-empty. A *frame* adds interpretations of `≡` and `≈`. -/

/-- Codes for the members of a type universe. -/
inductive Code (Base : Type) : Type where
  | e : Code Base
  | t : Code Base
  | base : Base → Code Base
  | arr : Code Base → Code Base → Code Base
  deriving DecidableEq

structure Univ where
  E : Type
  Base : Type
  B : Base → Type
  neE : Nonempty E
  neB : ∀ b, Nonempty (B b)

/-- The set a code names. -/
def Univ.El (U : Univ) : Code U.Base → Type
  | .e => U.E
  | .t => Prop
  | .base b => U.B b
  | .arr a c => U.El a → U.El c

structure Frame where
  U : Univ
  /-- the value of `≡`, at each pair of members of the universe -/
  eqv : (a b : Code U.Base) → U.El a → U.El b → Prop
  /-- the value of `≈` -/
  teq : Code U.Base → Code U.Base → Prop

namespace Univ
variable (U : Univ)

/-- Valuations of type variables. -/
abbrev TEnv (n : Nat) := Fin n → Code U.Base

/-- The semantic value of a category. -/
def CatVal {n : Nat} : Cat n → U.TEnv n → Type
  | .e, _ => U.E
  | .t, _ => Prop
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
  | .t => ⟨True⟩
  | .base b => U.neB b
  | .arr _ c => let ⟨y⟩ := El_nonempty c; ⟨fun _ => y⟩

theorem CatVal_nonempty {n : Nat} (K : Cat n) : ∀ ρ : U.TEnv n, Nonempty (U.CatVal K ρ) := by
  induction K with
  | e => intro; exact U.neE
  | t => intro; exact ⟨True⟩
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
  | .neg => fun p => ¬ p
  | .imp => fun p q => p → q
  | .and => fun p q => p ∧ q
  | .or => fun p q => p ∨ q
  | .iff => fun p q => p ↔ q
  | .all => fun _ P => ∀ x, P x
  | .ex => fun _ P => ∃ x, P x
  | .tall => fun Q => ∀ a, Q a
  | .tex => fun Q => ∃ a, Q a
  | .eqv => fun a b => F.eqv a b
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
abbrev Holds {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) : Prop := F.eval φ ρ env

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

/-! ## 6. β-conversion -/

/-- One step of β-reduction, anywhere in a term: `(λx:K.b) a ↦ b[a/x]` and `(λα:∗.b) σ ↦ b[σ/α]`. -/
inductive Step : {n : Nat} → {Γ : Ctx n} → {K : Cat n} → Tm Γ K → Tm Γ K → Prop where
  | beta {n : Nat} {Γ : Ctx n} {σ : Ty n} {L : Cat n} (b : Tm (.ext Γ σ) L) (a : Tm Γ σ.1) :
      Step (.app (.lam σ b) a) (b.subst0 a)
  | tbeta {n : Nat} {Γ : Ctx n} {K : Cat (n+1)} (b : Tm (.text Γ) K) (σ : Ty n) :
      Step (.tapp (.tlam b) σ) (b.tinst σ)
  | appL {n : Nat} {Γ : Ctx n} {K L : Cat n} {f f' : Tm Γ (.arr K L)} (a : Tm Γ K) :
      Step f f' → Step (.app f a) (.app f' a)
  | appR {n : Nat} {Γ : Ctx n} {K L : Cat n} (f : Tm Γ (.arr K L)) {a a' : Tm Γ K} :
      Step a a' → Step (.app f a) (.app f a')
  | lam {n : Nat} {Γ : Ctx n} (σ : Ty n) {L : Cat n} {b b' : Tm (.ext Γ σ) L} :
      Step b b' → Step (.lam σ b) (.lam σ b')
  | tlam {n : Nat} {Γ : Ctx n} {K : Cat (n+1)} {b b' : Tm (.text Γ) K} :
      Step b b' → Step (.tlam b) (.tlam b')
  | tapp {n : Nat} {Γ : Ctx n} {K : Cat (n+1)} {f f' : Tm Γ (.pi K)} (σ : Ty n) :
      Step f f' → Step (.tapp f σ) (.tapp f' σ)

/-- β-equivalence: the equivalence relation generated by `Step`. -/
inductive BetaEq {n : Nat} {Γ : Ctx n} {K : Cat n} : Tm Γ K → Tm Γ K → Prop where
  | refl (M : Tm Γ K) : BetaEq M M
  | step {M N : Tm Γ K} : Step M N → BetaEq M N
  | symm {M N : Tm Γ K} : BetaEq M N → BetaEq N M
  | trans {M N P : Tm Γ K} : BetaEq M N → BetaEq N P → BetaEq M P

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

/-! ## 7. The proof system -/

namespace Tm
variable {n : Nat} {Γ : Ctx n}

def neg (φ : Fm Γ) : Fm Γ := .app (.const .neg) φ
def imp (φ ψ : Fm Γ) : Fm Γ := .app (.app (.const .imp) φ) ψ
def conj (φ ψ : Fm Γ) : Fm Γ := .app (.app (.const .and) φ) ψ
def disj (φ ψ : Fm Γ) : Fm Γ := .app (.app (.const .or) φ) ψ
def iff (φ ψ : Fm Γ) : Fm Γ := .app (.app (.const .iff) φ) ψ
/-- `∀_σ x φ` -/
def all (σ : Ty n) (φ : Fm (.ext Γ σ)) : Fm Γ := .app (.tapp (.const .all) σ) (.lam σ φ)
/-- `∃_σ x φ` -/
def ex (σ : Ty n) (φ : Fm (.ext Γ σ)) : Fm Γ := .app (.tapp (.const .ex) σ) (.lam σ φ)
/-- `𝔸α φ` -/
def tall (φ : Fm (.text Γ)) : Fm Γ := .app (.const .tall) (.tlam φ)
/-- `𝔼α φ` -/
def tex (φ : Fm (.text Γ)) : Fm Γ := .app (.const .tex) (.tlam φ)

theorem eqv_cat (σ τ : Ty n) :
    ((Cat.arr (.var (fs fz)) (.arr (.var fz) .t)).sub (liftT (inst σ))).sub (inst τ) = .arr σ.1 (.arr τ.1 .t) := by
  show Cat.arr ((σ.1.ren fs).sub (inst τ)) (.arr τ.1 .t) = _
  rw [Cat.ren_fs_inst]

/-- `x ≡_{σ,τ} y` -/
def eqv (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1) : Fm Γ :=
  .app (.app (Tm.castK (eqv_cat σ τ) (.tapp (.tapp (.const .eqv) σ) τ)) x) y
/-- `σ ≈ τ` -/
def teq (σ τ : Ty n) : Fm Γ := .tapp (.tapp (.const .teq) σ) τ

end Tm

/-- Propositional formulas in `k` atoms, for the propositional axioms. -/
inductive PF (k : Nat) : Type where
  | atom : Fin k → PF k
  | neg : PF k → PF k
  | imp : PF k → PF k → PF k
  | conj : PF k → PF k → PF k
  | disj : PF k → PF k → PF k
  | iff : PF k → PF k → PF k

namespace PF
variable {k : Nat}

def evalP (v : Fin k → Prop) : PF k → Prop
  | atom i => v i
  | neg P => ¬ P.evalP v
  | imp P Q => P.evalP v → Q.evalP v
  | conj P Q => P.evalP v ∧ Q.evalP v
  | disj P Q => P.evalP v ∨ Q.evalP v
  | iff P Q => P.evalP v ↔ Q.evalP v

/-- A tautology: true under every assignment of truth values to its atoms. -/
def Taut (P : PF k) : Prop := ∀ v : Fin k → Prop, P.evalP v

/-- The instance of `P` with the formula `as i` for the atom `i`. -/
def inst {n : Nat} {Γ : Ctx n} (as : Fin k → Fm Γ) : PF k → Fm Γ
  | atom i => as i
  | neg P => (P.inst as).neg
  | imp P Q => (P.inst as).imp (Q.inst as)
  | conj P Q => (P.inst as).conj (Q.inst as)
  | disj P Q => (P.inst as).disj (Q.inst as)
  | iff P Q => (P.inst as).iff (Q.inst as)

end PF

section Axioms

/-- Type variables in a context with `n` of them: `tv0` is the innermost. -/
abbrev tv0 {n : Nat} : Ty (n+1) := tvar fz
abbrev tv1 {n : Nat} : Ty (n+2) := tvar (fs fz)
abbrev tv2 {n : Nat} : Ty (n+3) := tvar (fs (fs fz))

/-- The type `σ → t`. -/
def Ty.pred {n : Nat} (σ : Ty n) : Ty n := ⟨.arr σ.1 .t, ⟨σ.2, trivial⟩⟩

open Tm

/-- (Ref≡) `𝔸α ∀_α x (x ≡_α x)` -/
def RefEqv : Fm Ctx.nil :=
  tall (all tv0 (eqv tv0 tv0 (.var .here) (.var .here)))

/-- (Sym≡) `𝔸α 𝔸β ∀_α x ∀_β y (x ≡_{α,β} y → y ≡_{β,α} x)` -/
def SymEqv : Fm Ctx.nil :=
  tall (tall (all tv1 (all tv0 (imp (eqv tv1 tv0 (.var (.there .here)) (.var .here))
                                     (eqv tv0 tv1 (.var .here) (.var (.there .here)))))))

/-- (Trans≡) `𝔸α 𝔸β 𝔸γ ∀_α x ∀_β y ∀_γ z ((x ≡ y ∧ y ≡ z) → x ≡ z)` -/
def TransEqv : Fm Ctx.nil :=
  tall (tall (tall (all tv2 (all tv1 (all tv0
    (imp (conj (eqv tv2 tv1 (.var (.there (.there .here))) (.var (.there .here)))
               (eqv tv1 tv0 (.var (.there .here)) (.var .here)))
         (eqv tv2 tv0 (.var (.there (.there .here))) (.var .here))))))))

/-- (LL≡) `𝔸α ∀_α x ∀_α y (x ≡_α y → ∀_{α→t} F (F x → F y))` -/
def LLEqv : Fm Ctx.nil :=
  tall (all tv0 (all tv0 (imp (eqv tv0 tv0 (.var (.there .here)) (.var .here))
    (all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here))))
                       (.app (.var .here) (.var (.there .here))))))))

/-- (Ref≈) `𝔸α (α ≈ α)` -/
def RefTeq : Fm Ctx.nil := tall (teq tv0 tv0)

/-- (LL≈), the instance for `Q` of category `Πγ:∗.t`: `𝔸α 𝔸β (α ≈ β → (Q α → Q β))`. -/
def LLTeq {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)) : Fm Γ :=
  tall (tall (imp (teq tv1 tv0) (imp (.tapp Q.twk.twk tv1) (.tapp Q.twk.twk tv0))))

/-- The types `t` and `e`. -/
def tyT {n : Nat} : Ty n := ⟨.t, trivial⟩
def tyE {n : Nat} : Ty n := ⟨.e, trivial⟩

/-- (LL≡-Poly), the instance for a polymorphic predicate `P` of category `Πγ:∗.γ→t`:
`𝔸α 𝔸β ∀_α x ∀_β y (x ≡_{α,β} y → (P_α x → P_β y))`. -/
def LLPoly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : Fm Γ :=
  let P' := (P.twk.twk.wk tv1).wk tv0
  tall (tall (all tv1 (all tv0 (imp (eqv tv1 tv0 (.var (.there .here)) (.var .here))
    (imp (.app (.tapp P' tv1) (.var (.there .here))) (.app (.tapp P' tv0) (.var .here)))))))

/-- `⊥`, that is `∀_t p (p)`. -/
def Bot : Fm Ctx.nil := all tyT (.var .here)

end Axioms

/-- Derivability in PI⁻ together with the extra sentences `Ax`. A derivation is of a formula in a
context. The axioms are those of §2 of *Formal Results*, apart from LL≡; the three structural rules
at the end account for the paper's fixed typing of variables. -/
inductive Prov (Ax : Fm Ctx.nil → Prop) : {n : Nat} → (Γ : Ctx n) → Fm Γ → Prop where
  /-- the propositional axioms: every instance of a tautology -/
  | taut {n : Nat} {Γ : Ctx n} {k : Nat} (P : PF k) (as : Fin k → Fm Γ) : P.Taut → Prov Ax Γ (P.inst as)
  /-- (Inst∀) -/
  | instAll {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (κ : Tm Γ σ.1) :
      Prov Ax Γ ((Tm.all σ φ).imp (φ.subst0 κ))
  /-- (Dist∀) -/
  | distAll {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm Γ) (ψ : Fm (.ext Γ σ)) :
      Prov Ax Γ ((Tm.all σ ((φ.wk σ).imp ψ)).imp (φ.imp (Tm.all σ ψ)))
  /-- (Dual∃) -/
  | dualEx {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) :
      Prov Ax Γ ((Tm.ex σ φ).iff (Tm.all σ φ.neg).neg)
  /-- (Inst𝔸) -/
  | instTAll {n : Nat} {Γ : Ctx n} (φ : Fm (.text Γ)) (σ : Ty n) :
      Prov Ax Γ ((Tm.tall φ).imp (φ.tinst σ))
  /-- (Dist𝔸) -/
  | distTAll {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ψ : Fm (.text Γ)) :
      Prov Ax Γ ((Tm.tall (φ.twk.imp ψ)).imp (φ.imp (Tm.tall ψ)))
  /-- (Dual𝔼) -/
  | dualTEx {n : Nat} {Γ : Ctx n} (φ : Fm (.text Γ)) :
      Prov Ax Γ ((Tm.tex φ).iff (Tm.tall φ.neg).neg)
  /-- (β) -/
  | beta {n : Nat} {Γ : Ctx n} {φ ψ : Fm Γ} : BetaEq φ ψ → Prov Ax Γ (φ.iff ψ)
  | refEqv : Prov Ax .nil RefEqv
  | symEqv : Prov Ax .nil SymEqv
  | transEqv : Prov Ax .nil TransEqv
  | refTeq : Prov Ax .nil RefTeq
  /-- (LL≈), every instance -/
  | llTeq {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)) : Prov Ax Γ (LLTeq Q)
  /-- the extra axioms -/
  | ax {φ : Fm .nil} : Ax φ → Prov Ax .nil φ
  /-- (MP) -/
  | mp {n : Nat} {Γ : Ctx n} {φ ψ : Fm Γ} : Prov Ax Γ φ → Prov Ax Γ (φ.imp ψ) → Prov Ax Γ ψ
  /-- (Gen∀) -/
  | genAll {n : Nat} {Γ : Ctx n} (σ : Ty n) {φ : Fm (.ext Γ σ)} : Prov Ax (.ext Γ σ) φ → Prov Ax Γ (Tm.all σ φ)
  /-- (Gen𝔸) -/
  | genTAll {n : Nat} {Γ : Ctx n} {φ : Fm (.text Γ)} : Prov Ax (.text Γ) φ → Prov Ax Γ (Tm.tall φ)
  /-- renaming variables (weakening, exchange, contraction) -/
  | ren {n m : Nat} {Γ : Ctx n} {Δ : Ctx m} {r : Fin n → Fin m} (ρr : TRen r Γ Δ) {φ : Fm Γ} :
      Prov Ax Γ φ → Prov Ax Δ (φ.ren ρr)
  /-- discarding a term variable that does not occur -/
  | strengthen {n : Nat} {Γ : Ctx n} (σ : Ty n) {φ : Fm Γ} : Prov Ax (.ext Γ σ) (φ.wk σ) → Prov Ax Γ φ
  /-- discarding a type variable that does not occur -/
  | tstrengthen {n : Nat} {Γ : Ctx n} {φ : Fm Γ} : Prov Ax (.text Γ) φ.twk → Prov Ax Γ φ

/-- PI⁻ together with the sentences `S`. -/
abbrev PIm (S : Fm Ctx.nil → Prop) {n : Nat} (Γ : Ctx n) (φ : Fm Γ) : Prop := Prov S Γ φ
/-- PI together with the sentences `S`: PI⁻ with LL≡ as a further axiom. -/
abbrev PI (S : Fm Ctx.nil → Prop) {n : Nat} (Γ : Ctx n) (φ : Fm Γ) : Prop :=
  Prov (fun ψ => ψ = LLEqv ∨ S ψ) Γ φ

/-! ### Soundness -/

namespace Frame
variable (F : Frame)

section EvalLemmas
variable {n : Nat} {Γ : Ctx n}

theorem cast_forall {A A' : Type} (hA : A = A') (h : ((A → Prop) → Prop) = ((A' → Prop) → Prop))
    (P : A' → Prop) : cast h (fun Q : A → Prop => ∀ x, Q x) P ↔ ∀ x, P x := by
  subst hA; rw [cast_eq]

theorem cast_exists {A A' : Type} (hA : A = A') (h : ((A → Prop) → Prop) = ((A' → Prop) → Prop))
    (P : A' → Prop) : cast h (fun Q : A → Prop => ∃ x, Q x) P ↔ ∃ x, P x := by
  subst hA; rw [cast_eq]

theorem eval_tapp {K : Cat (n+1)} (f : Tm Γ (.pi K)) (σ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.eval (Tm.tapp f σ) ρ env = cast (F.U.tapp_eq K σ ρ) (F.eval f ρ env (F.U.code σ.1 ρ)) := rfl

theorem heq_eval_tapp {K : Cat (n+1)} (f : Tm Γ (.pi K)) (σ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    HEq (F.eval (Tm.tapp f σ) ρ env) (F.eval f ρ env (F.U.code σ.1 ρ)) :=
  (heq_of_eq (F.eval_tapp f σ ρ env)).trans (cast_heq _ _)

theorem holds_all (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.all σ φ) ρ env ↔ ∀ v : F.U.CatVal σ.1 ρ, F.Holds φ ρ (env, v) :=
  cast_forall (Univ.El_code ρ σ.2) _ _

theorem holds_ex (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.ex σ φ) ρ env ↔ ∃ v : F.U.CatVal σ.1 ρ, F.Holds φ ρ (env, v) :=
  cast_exists (Univ.El_code ρ σ.2) _ _

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

theorem app2_heq {A A' B B' : Type} (hA : A = A') (hB : B = B') {f : A → B → Prop} {g : A' → B' → Prop}
    (h : HEq f g) (x : A) (y : B) : f x y = g (cast hA x) (cast hB y) := by
  subst hA; subst hB; rw [eq_of_heq h]; rfl

/-- The value of `≡_{σ,τ}`. -/
theorem eval_eqvConst (σ τ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    HEq (F.eval (Tm.castK (Tm.eqv_cat σ τ) (Tm.tapp (Tm.tapp (Tm.const (Γ := Γ) Const.eqv) σ) τ)) ρ env)
      (F.eqv (F.U.code σ.1 ρ) (F.U.code τ.1 ρ)) := by
  refine (F.eval_castK _ _ _ _).trans ((cast_heq _ _).trans ?_)
  refine heq_dapp (Q := fun b => F.U.El (F.U.code σ.1 ρ) → F.U.El b → Prop) (fun b => ?_)
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
  Iff.of_eq (app2_heq (A := F.U.CatVal σ.1 ρ) (B := F.U.CatVal τ.1 ρ)
    (f := F.eval (Tm.castK (Tm.eqv_cat σ τ) (Tm.tapp (Tm.tapp (Tm.const Const.eqv) σ) τ)) ρ env)
    (Univ.El_code ρ σ.2).symm (Univ.El_code ρ τ.2).symm (F.eval_eqvConst σ τ ρ env) _ _)

/-- The truth value of `σ ≈ τ`. -/
theorem holds_teq (σ τ : Ty n) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.teq σ τ) ρ env ↔ F.teq (F.U.code σ.1 ρ) (F.U.code τ.1 ρ) := by
  have h1 : HEq (F.eval (Tm.tapp (Tm.const (Γ := Γ) Const.teq) σ) ρ env) (F.teq (F.U.code σ.1 ρ)) :=
    F.heq_eval_tapp _ σ ρ env
  have h2 : HEq (F.eval (Tm.teq (Γ := Γ) σ τ) ρ env)
      (F.eval (Tm.tapp (Tm.const (Γ := Γ) Const.teq) σ) ρ env (F.U.code τ.1 ρ)) := F.heq_eval_tapp _ τ ρ env
  exact Iff.of_eq (eq_of_heq (h2.trans (heq_dapp (Q := fun _ => Prop) (fun _ => rfl) h1 rfl)))

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
    exact cast (eq_of_heq (F.eval_tinst φ σ ρ env)).symm (h (F.U.code σ.1 ρ))
  | distTAll φ ψ =>
    intro ρ env h hφ a
    exact h a (cast (eq_of_heq (F.eval_twk φ a ρ env)).symm hφ)
  | dualTEx φ =>
    intro ρ env
    show (∃ a, F.Holds φ (scons a ρ) env) ↔ ¬ ∀ a, ¬ F.Holds φ (scons a ρ) env
    constructor
    · rintro ⟨a, ha⟩ h; exact h a ha
    · intro h; exact Classical.byContradiction fun hn => h fun a ha => hn ⟨a, ha⟩
  | beta h => intro ρ env; exact Iff.of_eq (F.eval_betaEq h ρ env)
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
    exact cast (eq_of_heq (F.eval_ren _ ρr ρ' env' _ (F.pullEnv _ ρr ρ' env') (fun _ => rfl)
      (fun x => F.lookup_pull x ρr ρ' env'))).symm (ih _ _)
  | strengthen σ _ ih =>
    intro ρ env
    have v := Classical.choice (Univ.CatVal_nonempty σ.1 ρ)
    have := ih ρ (env, v)
    unfold Holds at this
    rwa [eval_wk] at this
  | tstrengthen _ ih =>
    intro ρ env
    exact cast (eq_of_heq (F.eval_twk _ .e ρ env)) (ih (scons .e ρ) env)

/-- A model of PI: a model of PI⁻ in which LL≡ is true. -/
theorem soundness_PI {S : Fm Ctx.nil → Prop} (hM : F.IsModelPIm) (hLL : F.Valid LLEqv)
    (hS : ∀ φ, S φ → F.Valid φ) {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : PI S Γ φ) : F.Valid φ :=
  F.soundness hM (fun ψ hψ => hψ.elim (fun e => e ▸ hLL) (hS ψ)) h

/-- `⊥` is false in every frame. -/
theorem not_valid_bot : ¬ F.Valid Bot := fun h =>
  (F.holds_all (Γ := Ctx.nil) tyT _ (fun i => i.elim0) ()).mp (h _ ()) False

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
  exact cast (eq_of_heq (e1.trans e2.symm)) hq

end Frame

/-! ## 8. Consistency: the diagonal model

The type universe has one entity; `≡` relates an item only to itself, at one and the same type,
and `≈` is identity of types. This is the model `𝔐(HF⁺, ∼₀)` of *Formal Results*,
in miniature. -/

def unitUniv : Univ where
  E := Unit
  Base := Empty
  B := fun b => b.elim
  neE := ⟨()⟩
  neB := fun b => b.elim

def diag : Frame where
  U := unitUniv
  eqv := fun a b x y => a = b ∧ HEq x y
  teq := fun a b => a = b

theorem diag_model : diag.IsModelPIm where
  refEqv := by
    intro ρ env a
    exact (diag.holds_all _ _ _ _).mpr fun v => (diag.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩
  symEqv := by
    intro ρ env a b
    refine (diag.holds_all _ _ _ _).mpr fun x => (diag.holds_all _ _ _ _).mpr fun y => ?_
    intro h
    obtain ⟨e, hxy⟩ := (diag.holds_eqv _ _ _ _ _ _).mp h
    exact (diag.holds_eqv _ _ _ _ _ _).mpr ⟨e.symm, hxy.symm⟩
  transEqv := by
    intro ρ env a b c
    refine (diag.holds_all _ _ _ _).mpr fun x => (diag.holds_all _ _ _ _).mpr fun y =>
      (diag.holds_all _ _ _ _).mpr fun z => ?_
    intro h
    obtain ⟨e1, h1⟩ := (diag.holds_eqv _ _ _ _ _ _).mp h.1
    obtain ⟨e2, h2⟩ := (diag.holds_eqv _ _ _ _ _ _).mp h.2
    exact (diag.holds_eqv _ _ _ _ _ _).mpr ⟨e1.trans e2, h1.trans h2⟩
  refTeq := by
    intro ρ env a
    exact (diag.holds_teq _ _ _ _).mpr rfl
  llTeq := fun Q => diag.llTeq_of_teq_eq (fun _ _ h => h) Q

theorem diag_LLEqv : diag.Valid LLEqv := by
  intro ρ env a
  refine (diag.holds_all _ _ _ _).mpr fun x => (diag.holds_all _ _ _ _).mpr fun y => ?_
  intro h
  have h' := (diag.holds_eqv _ _ _ _ _ _).mp h
  have hxy : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h'.2.trans (cast_heq _ _)))
  subst hxy
  exact (diag.holds_all _ _ _ _).mpr fun _ hF => hF

/-- **PI is consistent**: it does not derive `⊥`. -/
theorem PI_consistent : ¬ PI (fun _ => False) Ctx.nil Bot :=
  diag.consistent_of_model diag_model (fun _ hψ => hψ.elim (fun e => e ▸ diag_LLEqv) False.elim)

/-! ## 9. Invariance (parametricity)

*Formal Results*, Definition 12 and Lemma 7 (invariance): if a model carries a family of bijections
between members of its type universe which respects `→`, `≡`, and `≈`, then no sentence can tell
related items apart. Here the lemma is proved in the relational form of Reynolds' parametricity
theorem: a model carries a family of *admissible relations* between members of its type universe,
and every term is related to itself. The graph of each bijection in a family of bijections is an
admissible relation, so the paper's lemma is a special case. Two consequences, the analogue of
Lemma 8 of *Formal Results*, give conditions under which LL≈ and LL≡-Poly hold; they are what is
needed for models such as `𝔐_κ`, `𝔐_card`, `𝔐_tot`, and `𝔐_fn`. -/

/-- A family of admissible relations for a frame. -/
structure Invariance (F : Frame) where
  Adm : (a a' : Code F.U.Base) → (F.U.El a → F.U.El a' → Prop) → Prop
  /-- (i) identity is admissible -/
  refl : ∀ a, Adm a a (fun x y => x = y)
  /-- (ii) admissible relations are closed under `→` -/
  arrow : ∀ {a a' c c' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop} {S : F.U.El c → F.U.El c' → Prop},
    Adm a a' R → Adm c c' S → Adm (.arr a c) (.arr a' c') (fun f f' => ∀ u u', R u u' → S (f u) (f' u'))
  /-- admissible relations are total and onto (as the graph of a bijection is) -/
  total : ∀ {a a' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop}, Adm a a' R → ∀ u, ∃ u', R u u'
  onto : ∀ {a a' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop}, Adm a a' R → ∀ u', ∃ u, R u u'
  /-- (iii) `≈` and `≡` respect admissible relations -/
  teq : ∀ {a a' b b' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop} {S : F.U.El b → F.U.El b' → Prop},
    Adm a a' R → Adm b b' S → (F.teq a b ↔ F.teq a' b')
  eqv : ∀ {a a' b b' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop} {S : F.U.El b → F.U.El b' → Prop},
    Adm a a' R → Adm b b' S → ∀ u u' v v', R u u' → S v v' → (F.eqv a b u v ↔ F.eqv a' b' u' v')

namespace Invariance
variable {F : Frame} (I : Invariance F)
set_option linter.unusedVariables false

/-- Relations for the type variables, extended by `R` for the new variable `fz`. -/
def RScons {n : Nat} {ρ ρ' : F.U.TEnv n} {a a' : Code F.U.Base} (R : F.U.El a → F.U.El a' → Prop)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) :
    ∀ i : Fin (n+1), F.U.El (scons a ρ i) → F.U.El (scons a' ρ' i) → Prop
  | ⟨0, _⟩ => R
  | ⟨k+1, h⟩ => Rs ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- The logical relation at each category: equality at `e`, `↔` at `t`, the given relations at
type variables, preservation at `→`, and preservation under every admissible relation at `Π`. -/
def Rel : {n : Nat} → (K : Cat n) → (ρ ρ' : F.U.TEnv n) → (∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) →
    F.U.CatVal K ρ → F.U.CatVal K ρ' → Prop
  | _, .e, _, _, _ => fun x y => x = y
  | _, .t, _, _, _ => fun p q => (p ↔ q)
  | _, .var i, _, _, Rs => Rs i
  | _, .arr K L, ρ, ρ', Rs => fun f f' => ∀ u u', Rel K ρ ρ' Rs u u' → Rel L ρ ρ' Rs (f u) (f' u')
  | _, .pi K, ρ, ρ', Rs => fun G G' => ∀ a a' (R : F.U.El a → F.U.El a' → Prop), I.Adm a a' R →
      Rel K (scons a ρ) (scons a' ρ') (RScons R Rs) (G a) (G' a')

/-- The same relation at a type, on the sets its code names. -/
def RelE {n : Nat} : (K : Cat n) → (ρ ρ' : F.U.TEnv n) → (∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) →
    F.U.El (F.U.code K ρ) → F.U.El (F.U.code K ρ') → Prop
  | .e, _, _, _ => fun x y => x = y
  | .t, _, _, _ => fun p q => (p ↔ q)
  | .var i, _, _, Rs => Rs i
  | .arr K L, ρ, ρ', Rs => fun f f' => ∀ x x', RelE K ρ ρ' Rs x x' → RelE L ρ ρ' Rs (f x) (f' x')
  | .pi _, _, _, _ => fun x y => x = y

theorem adm_iff : I.Adm .t .t (fun p q => (p ↔ q)) := by
  have h : (fun p q : Prop => (p ↔ q)) = (fun p q : Prop => p = q) :=
    funext fun p => funext fun q => propext ⟨propext, fun h => h ▸ Iff.rfl⟩
  have := I.refl .t
  exact h ▸ this

theorem adm_RelE {n : Nat} (K : Cat n) : ∀ (ρ ρ' : F.U.TEnv n) (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop),
    (∀ i, I.Adm (ρ i) (ρ' i) (Rs i)) → K.Simple →
    I.Adm (F.U.code K ρ) (F.U.code K ρ') (RelE K ρ ρ' Rs) := by
  induction K with
  | e => intros; exact I.refl _
  | t => intros; exact I.adm_iff
  | var i => intro ρ ρ' Rs hRs _; exact hRs i
  | arr a b iha ihb => intro ρ ρ' Rs hRs hK; exact I.arrow (iha ρ ρ' Rs hRs hK.1) (ihb ρ ρ' Rs hRs hK.2)
  | pi _ _ => intro _ _ _ _ hK; exact hK.elim

/-! ### Transporting quantifiers along equations between types -/

theorem forall_heq {A A' : Type} (h : A = A') {P : A → Prop} {Q : A' → Prop}
    (hPQ : ∀ a a', HEq a a' → (P a ↔ Q a')) : (∀ a, P a) ↔ (∀ a', Q a') := by
  subst h
  exact ⟨fun h a => (hPQ a a HEq.rfl).mp (h a), fun h a => (hPQ a a HEq.rfl).mpr (h a)⟩

theorem cast_app {A A' B B' : Type} (hA : A = A') (hB : B = B') (h : (A → B) = (A' → B')) (f : A → B)
    (x : A') : HEq ((cast h f) x) (f (cast hA.symm x)) := by
  subst hA; subst hB; rfl

theorem Rel_RelE {n : Nat} (K : Cat n) : ∀ (hK : K.Simple) (ρ ρ' : F.U.TEnv n)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) (u : F.U.CatVal K ρ) (u' : F.U.CatVal K ρ')
    (x : F.U.El (F.U.code K ρ)) (x' : F.U.El (F.U.code K ρ')), HEq u x → HEq u' x' →
    (I.Rel K ρ ρ' Rs u u' ↔ RelE K ρ ρ' Rs x x') := by
  induction K with
  | e => intro _ ρ ρ' Rs u u' x x' hx hx'; cases hx; cases hx'; exact Iff.rfl
  | t => intro _ ρ ρ' Rs u u' x x' hx hx'; cases hx; cases hx'; exact Iff.rfl
  | var i => intro _ ρ ρ' Rs u u' x x' hx hx'; cases hx; cases hx'; exact Iff.rfl
  | arr a b iha ihb =>
    intro hK ρ ρ' Rs u u' x x' hx hx'
    refine forall_heq (Univ.El_code ρ hK.1).symm fun v y hvy => ?_
    refine forall_heq (Univ.El_code ρ' hK.1).symm fun v' y' hvy' => ?_
    refine imp_congr (iha hK.1 ρ ρ' Rs v v' y y' hvy hvy') (ihb hK.2 ρ ρ' Rs _ _ _ _ ?_ ?_)
    · exact heq_app (Univ.El_code ρ hK.1).symm (Univ.El_code ρ hK.2).symm hx hvy
    · exact heq_app (Univ.El_code ρ' hK.1).symm (Univ.El_code ρ' hK.2).symm hx' hvy'
  | pi _ _ => intro hK; exact hK.elim

/-! ### Renaming and substitution for the logical relation -/

theorem Rel_ren {n : Nat} (K : Cat n) : ∀ {m : Nat} (r : Fin n → Fin m) (ρ ρ' : F.U.TEnv m)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) (ρ₂ ρ₂' : F.U.TEnv n)
    (Rs₂ : ∀ i, F.U.El (ρ₂ i) → F.U.El (ρ₂' i) → Prop)
    (hρ : ∀ i, ρ (r i) = ρ₂ i) (hρ' : ∀ i, ρ' (r i) = ρ₂' i)
    (hR : ∀ i x x' y y', HEq x y → HEq x' y' → (Rs (r i) x x' ↔ Rs₂ i y y'))
    (v : F.U.CatVal (K.ren r) ρ) (v' : F.U.CatVal (K.ren r) ρ') (w : F.U.CatVal K ρ₂) (w' : F.U.CatVal K ρ₂'),
    HEq v w → HEq v' w' → (I.Rel (K.ren r) ρ ρ' Rs v v' ↔ I.Rel K ρ₂ ρ₂' Rs₂ w w') := by
  induction K with
  | e => intro m r ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ _ v v' w w' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | t => intro m r ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ _ v v' w w' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | var i => intro m r ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ hR v v' w w' hv hv'; exact hR i v v' w w' hv hv'
  | arr a b iha ihb =>
    intro m r ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR v v' w w' hv hv'
    refine forall_heq (Univ.CatVal_ren a r ρ ρ₂ hρ) fun u y huy => ?_
    refine forall_heq (Univ.CatVal_ren a r ρ' ρ₂' hρ') fun u' y' huy' => ?_
    refine imp_congr (iha r ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR u u' y y' huy huy')
      (ihb r ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR _ _ _ _ ?_ ?_)
    · exact heq_app (Univ.CatVal_ren a r ρ ρ₂ hρ) (Univ.CatVal_ren b r ρ ρ₂ hρ) hv huy
    · exact heq_app (Univ.CatVal_ren a r ρ' ρ₂' hρ') (Univ.CatVal_ren b r ρ' ρ₂' hρ') hv' huy'
  | pi K ih =>
    intro m r ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR v v' w w' hv hv'
    refine forall_congr' fun a => forall_congr' fun a' => forall_congr' fun R => imp_congr Iff.rfl ?_
    refine ih (liftR r) (scons a ρ) (scons a' ρ') (RScons R Rs) (scons a ρ₂) (scons a' ρ₂') (RScons R Rs₂)
      (fin_cases rfl (fun i => hρ i)) (fin_cases rfl (fun i => hρ' i)) ?_ _ _ _ _ ?_ ?_
    · refine fin_cases ?_ (fun i => fun x x' y y' hx hx' => hR i x x' y y' hx hx')
      intro x x' y y' hx hx'; cases hx; cases hx'; exact Iff.rfl
    · exact heq_dapp (fun a => Univ.CatVal_ren K (liftR r) (scons a ρ) (scons a ρ₂)
        (fin_cases rfl (fun i => hρ i))) hv rfl
    · exact heq_dapp (fun a => Univ.CatVal_ren K (liftR r) (scons a ρ') (scons a ρ₂')
        (fin_cases rfl (fun i => hρ' i))) hv' rfl

theorem Rel_sub {n : Nat} (K : Cat n) : ∀ {m : Nat} (s : Fin n → Ty m) (ρ ρ' : F.U.TEnv m)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) (ρ₂ ρ₂' : F.U.TEnv n)
    (Rs₂ : ∀ i, F.U.El (ρ₂ i) → F.U.El (ρ₂' i) → Prop)
    (hρ : ∀ i, F.U.code (s i).1 ρ = ρ₂ i) (hρ' : ∀ i, F.U.code (s i).1 ρ' = ρ₂' i)
    (hR : ∀ i (x : F.U.CatVal (s i).1 ρ) (x' : F.U.CatVal (s i).1 ρ') y y', HEq x y → HEq x' y' →
      (I.Rel (s i).1 ρ ρ' Rs x x' ↔ Rs₂ i y y'))
    (v : F.U.CatVal (K.sub s) ρ) (v' : F.U.CatVal (K.sub s) ρ') (w : F.U.CatVal K ρ₂) (w' : F.U.CatVal K ρ₂'),
    HEq v w → HEq v' w' → (I.Rel (K.sub s) ρ ρ' Rs v v' ↔ I.Rel K ρ₂ ρ₂' Rs₂ w w') := by
  induction K with
  | e => intro m s ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ _ v v' w w' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | t => intro m s ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ _ v v' w w' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | var i => intro m s ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ hR v v' w w' hv hv'; exact hR i v v' w w' hv hv'
  | arr a b iha ihb =>
    intro m s ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR v v' w w' hv hv'
    refine forall_heq (Univ.CatVal_sub a s ρ ρ₂ hρ) fun u y huy => ?_
    refine forall_heq (Univ.CatVal_sub a s ρ' ρ₂' hρ') fun u' y' huy' => ?_
    refine imp_congr (iha s ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR u u' y y' huy huy')
      (ihb s ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR _ _ _ _ ?_ ?_)
    · exact heq_app (Univ.CatVal_sub a s ρ ρ₂ hρ) (Univ.CatVal_sub b s ρ ρ₂ hρ) hv huy
    · exact heq_app (Univ.CatVal_sub a s ρ' ρ₂' hρ') (Univ.CatVal_sub b s ρ' ρ₂' hρ') hv' huy'
  | pi K ih =>
    intro m s ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR v v' w w' hv hv'
    have hl : ∀ (a : Code F.U.Base) (ρ ρ₂ : _) , (∀ i, F.U.code (s i).1 ρ = ρ₂ i) →
        ∀ i, F.U.code (liftT s i).1 (scons a ρ) = scons a ρ₂ i := fun a ρ ρ₂ h =>
      fin_cases rfl (fun i => by
        show F.U.code ((s i).1.ren fs) (scons a ρ) = ρ₂ i
        rw [Univ.code_ren]; exact h i)
    refine forall_congr' fun a => forall_congr' fun a' => forall_congr' fun R => imp_congr Iff.rfl ?_
    refine ih (liftT s) (scons a ρ) (scons a' ρ') (RScons R Rs) (scons a ρ₂) (scons a' ρ₂') (RScons R Rs₂)
      (hl a ρ ρ₂ hρ) (hl a' ρ' ρ₂' hρ') ?_ _ _ _ _ ?_ ?_
    · refine fin_cases ?_ (fun i => ?_)
      · intro x x' y y' hx hx'; cases hx; cases hx'; exact Iff.rfl
      · intro x x' y y' hx hx'
        refine (I.Rel_ren (s i).1 fs (scons a ρ) (scons a' ρ') (RScons R Rs) ρ ρ' Rs (fun _ => rfl)
          (fun _ => rfl) (fun j z z' q q' hz hz' => by cases hz; cases hz'; exact Iff.rfl)
          x x' (cast (Univ.CatVal_ren (s i).1 fs (scons a ρ) ρ (fun _ => rfl)) x)
          (cast (Univ.CatVal_ren (s i).1 fs (scons a' ρ') ρ' (fun _ => rfl)) x')
          (cast_heq _ _).symm (cast_heq _ _).symm).trans ?_
        exact hR i _ _ y y' ((cast_heq _ _).trans hx) ((cast_heq _ _).trans hx')
    · exact heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ) (scons a ρ₂) (hl a ρ ρ₂ hρ)) hv rfl
    · exact heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ') (scons a ρ₂') (hl a ρ' ρ₂' hρ')) hv' rfl

/-! ### The fundamental lemma -/

/-- Related values for the term variables of a context. -/
def EnvRel : {n : Nat} → (Γ : Ctx n) → (ρ ρ' : F.U.TEnv n) → (∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) →
    F.U.Env Γ ρ → F.U.Env Γ ρ' → Prop
  | _, .nil, _, _, _ => fun _ _ => True
  | _, .ext Γ σ, ρ, ρ', Rs => fun env env' => EnvRel Γ ρ ρ' Rs env.1 env'.1 ∧ I.Rel σ.1 ρ ρ' Rs env.2 env'.2
  | _, .text Γ, ρ, ρ', Rs => fun env env' =>
      EnvRel Γ (fun i => ρ (fs i)) (fun i => ρ' (fs i)) (fun i => Rs (fs i)) env env'

theorem lookup_rel {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) : ∀ (ρ ρ' : F.U.TEnv n)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) (env : F.U.Env Γ ρ) (env' : F.U.Env Γ ρ'),
    I.EnvRel Γ ρ ρ' Rs env env' → I.Rel K ρ ρ' Rs (F.U.lookup x ρ env) (F.U.lookup x ρ' env') := by
  induction x with
  | here => intro ρ ρ' Rs env env' h; exact h.2
  | there y ih => intro ρ ρ' Rs env env' h; exact ih ρ ρ' Rs env.1 env'.1 h.1
  | tthere y ih =>
    intro ρ ρ' Rs env env' h
    refine (I.Rel_ren _ fs ρ ρ' Rs (fun i => ρ (fs i)) (fun i => ρ' (fs i)) (fun i => Rs (fs i))
      (fun _ => rfl) (fun _ => rfl) (fun i x x' y y' hx hx' => by cases hx; cases hx'; exact Iff.rfl)
      _ _ _ _ (F.lookup_tthere y ρ env) (F.lookup_tthere y ρ' env')).mpr ?_
    exact ih _ _ _ env env' h

theorem const_rel {n : Nat} {K : Cat n} (c : Const n K) (ρ ρ' : F.U.TEnv n)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) :
    I.Rel K ρ ρ' Rs (F.constVal c ρ) (F.constVal c ρ') := by
  cases c with
  | neg => intro p p' hp; exact not_congr hp
  | imp => intro p p' hp q q' hq; exact imp_congr hp hq
  | and => intro p p' hp q q' hq; exact and_congr hp hq
  | or => intro p p' hp q q' hq; exact or_congr hp hq
  | iff => intro p p' hp q q' hq; exact iff_congr hp hq
  | all =>
    intro a a' R hR P P' hP
    constructor
    · intro h x'; obtain ⟨x, hx⟩ := I.onto hR x'; exact (hP x x' hx).mp (h x)
    · intro h x; obtain ⟨x', hx⟩ := I.total hR x; exact (hP x x' hx).mpr (h x')
  | ex =>
    intro a a' R hR P P' hP
    constructor
    · rintro ⟨x, hx⟩; obtain ⟨x', hxx⟩ := I.total hR x; exact ⟨x', (hP x x' hxx).mp hx⟩
    · rintro ⟨x', hx⟩; obtain ⟨x, hxx⟩ := I.onto hR x'; exact ⟨x, (hP x x' hxx).mpr hx⟩
  | tall =>
    intro Q Q' hQ
    exact ⟨fun h a => (hQ a a _ (I.refl a)).mp (h a), fun h a => (hQ a a _ (I.refl a)).mpr (h a)⟩
  | tex =>
    intro Q Q' hQ
    exact ⟨fun ⟨a, h⟩ => ⟨a, (hQ a a _ (I.refl a)).mp h⟩, fun ⟨a, h⟩ => ⟨a, (hQ a a _ (I.refl a)).mpr h⟩⟩
  | eqv =>
    intro a a' R hR b b' S hS u u' hu v v' hv
    exact I.eqv hR hS u u' v v' hu hv
  | teq =>
    intro a a' R hR b b' S hS
    exact I.teq hR hS

/-- **The fundamental lemma** (invariance): every term is related to itself, under related values
for its variables. -/
theorem fundamental {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) : ∀ (ρ ρ' : F.U.TEnv n)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop), (∀ i, I.Adm (ρ i) (ρ' i) (Rs i)) →
    ∀ (env : F.U.Env Γ ρ) (env' : F.U.Env Γ ρ'), I.EnvRel Γ ρ ρ' Rs env env' →
    I.Rel K ρ ρ' Rs (F.eval M ρ env) (F.eval M ρ' env') := by
  induction M with
  | var x => intro ρ ρ' Rs _ env env' h; exact I.lookup_rel x ρ ρ' Rs env env' h
  | const c => intro ρ ρ' Rs _ _ _ _; exact I.const_rel c ρ ρ' Rs
  | app f a ihf iha =>
    intro ρ ρ' Rs hRs env env' h
    exact ihf ρ ρ' Rs hRs env env' h _ _ (iha ρ ρ' Rs hRs env env' h)
  | lam σ b ih =>
    intro ρ ρ' Rs hRs env env' h u u' hu
    exact ih ρ ρ' Rs hRs (env, u) (env', u') ⟨h, hu⟩
  | tlam b ih =>
    intro ρ ρ' Rs hRs env env' h a a' R hR
    exact ih (scons a ρ) (scons a' ρ') (RScons R Rs) (fin_cases hR (fun i => hRs i)) env env' h
  | tapp f σ ih =>
    intro ρ ρ' Rs hRs env env' h
    have hf := ih ρ ρ' Rs hRs env env' h (F.U.code σ.1 ρ) (F.U.code σ.1 ρ') (RelE σ.1 ρ ρ' Rs)
      (I.adm_RelE σ.1 ρ ρ' Rs hRs σ.2)
    refine (I.Rel_sub _ (inst σ) ρ ρ' Rs (scons (F.U.code σ.1 ρ) ρ) (scons (F.U.code σ.1 ρ') ρ')
      (RScons (RelE σ.1 ρ ρ' Rs) Rs) (fin_cases rfl (fun _ => rfl)) (fin_cases rfl (fun _ => rfl)) ?_
      _ _ _ _ (F.heq_eval_tapp f σ ρ env) (F.heq_eval_tapp f σ ρ' env')).mpr hf
    refine fin_cases ?_ (fun i => ?_)
    · intro x x' y y' hx hx'; exact I.Rel_RelE σ.1 σ.2 ρ ρ' Rs x x' y y' hx hx'
    · intro x x' y y' hx hx'; cases hx; cases hx'; exact Iff.rfl

/-! ### Consequences -/

/-- With identity relations, the logical relation at a type is identity. -/
theorem Rel_eq {n : Nat} (K : Cat n) : ∀ (_ : K.Simple) (ρ : F.U.TEnv n) (u u' : F.U.CatVal K ρ),
    I.Rel K ρ ρ (fun _ x y => x = y) u u' ↔ u = u' := by
  induction K with
  | e => intros; exact Iff.rfl
  | t => intros; exact ⟨propext, fun h => h ▸ Iff.rfl⟩
  | var i => intros; exact Iff.rfl
  | arr a b iha ihb =>
    intro hK ρ u u'
    constructor
    · intro h; funext x; exact (ihb hK.2 ρ _ _).mp (h x x ((iha hK.1 ρ x x).mpr rfl))
    · intro h x x' hx; rw [(iha hK.1 ρ x x').mp hx, h]; exact (ihb hK.2 ρ _ _).mpr rfl
  | pi _ _ => intro hK; exact hK.elim

theorem envRel_refl {n : Nat} (Γ : Ctx n) : ∀ (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ),
    I.EnvRel Γ ρ ρ (fun _ x y => x = y) env env := by
  induction Γ with
  | nil => intros; trivial
  | ext Γ σ ih => intro ρ env; exact ⟨ih ρ env.1, (I.Rel_eq σ.1 σ.2 ρ _ _).mpr rfl⟩
  | text Γ ih => intro ρ env; exact ih (fun i => ρ (fs i)) env

/-- A term of category `Πγ:∗.t` takes the same value at types related by an admissible relation. -/
theorem pi_t_invariant {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ)
    {a b : Code F.U.Base} {R : F.U.El a → F.U.El b → Prop} (hR : I.Adm a b R) :
    F.eval Q ρ env a ↔ F.eval Q ρ env b :=
  I.fundamental Q ρ ρ _ (fun i => I.refl (ρ i)) env env (I.envRel_refl Γ ρ env) a b R hR

/-- **LL≈ holds** in a frame with a family of admissible relations, if types identified by `≈` are
related by some admissible relation (*Formal Results*, Lemma 8(b)). -/
theorem llTeq_valid (hteq : ∀ a b, F.teq a b → ∃ R, I.Adm a b R) {n : Nat} {Γ : Ctx n}
    (Q : Tm Γ (.pi .t)) : F.Valid (LLTeq Q) := by
  intro ρ env a b hab hq
  obtain ⟨R, hR⟩ := hteq a b ((F.holds_teq _ _ _ _).mp hab)
  have hG : HEq (F.eval Q.twk.twk (scons b (scons a ρ)) env) (F.eval Q ρ env) :=
    (F.eval_twk Q.twk b (scons a ρ) env).trans (F.eval_twk Q a ρ env)
  have h1 : HEq (F.eval (Tm.tapp Q.twk.twk tv1) (scons b (scons a ρ)) env) (F.eval Q ρ env a) :=
    (F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv1 (scons b (scons a ρ)) env).trans
      (heq_dapp (P := fun _ => Prop) (Q := fun _ => Prop) (fun _ => rfl) hG rfl)
  have h0 : HEq (F.eval (Tm.tapp Q.twk.twk tv0) (scons b (scons a ρ)) env) (F.eval Q ρ env b) :=
    (F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv0 (scons b (scons a ρ)) env).trans
      (heq_dapp (P := fun _ => Prop) (Q := fun _ => Prop) (fun _ => rfl) hG rfl)
  exact cast (eq_of_heq h0).symm ((I.pi_t_invariant Q ρ env hR).mp (cast (eq_of_heq h1) hq))

/-- **LL≡-Poly holds** in a frame with a family of admissible relations, if any two identified
items are related by some admissible relation (*Formal Results*, Lemma 8(a)). -/
theorem llPoly_valid (hE : ∀ a b u v, F.eqv a b u v → ∃ R, I.Adm a b R ∧ R u v) {n : Nat} {Γ : Ctx n}
    (P : Tm Γ (.pi (.arr (.var fz) .t))) : F.Valid (LLPoly P) := by
  intro ρ env a b
  refine (F.holds_all _ _ _ _).mpr fun x => (F.holds_all _ _ _ _).mpr fun y => ?_
  intro hxy hPx
  obtain ⟨R, hR, hRxy⟩ := hE a b _ _ ((F.holds_eqv _ _ _ _ _ _).mp hxy)
  have hrel := I.fundamental P ρ ρ _ (fun i => I.refl (ρ i)) env env (I.envRel_refl Γ ρ env) a b R hR _ _ hRxy
  have hG : HEq (F.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y)) (F.eval P ρ env) :=
    (heq_of_eq ((F.eval_wk _ _ _ _ _).trans (F.eval_wk _ _ _ _ _))).trans
      ((F.eval_twk P.twk b (scons a ρ) env).trans (F.eval_twk P a ρ env))
  have h1 : F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (scons b (scons a ρ)) ((env, x), y) = F.eval P ρ env a :=
    eq_of_heq ((F.heq_eval_tapp (K := Cat.arr (Cat.var fz) Cat.t) ((P.twk.twk.wk tv1).wk tv0) tv1 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => F.U.El c → Prop) (Q := fun c => F.U.El c → Prop) (fun _ => rfl) hG rfl))
  have h0 : F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (scons b (scons a ρ)) ((env, x), y) = F.eval P ρ env b :=
    eq_of_heq ((F.heq_eval_tapp (K := Cat.arr (Cat.var fz) Cat.t) ((P.twk.twk.wk tv1).wk tv0) tv0 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => F.U.El c → Prop) (Q := fun c => F.U.El c → Prop) (fun _ => rfl) hG rfl))
  show F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (scons b (scons a ρ)) ((env, x), y) y
  have hPx' : F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (scons b (scons a ρ)) ((env, x), y) x := hPx
  rw [h1] at hPx'
  rw [h0]
  exact hrel.mp hPx'

end Invariance

/-- A frame with a family of admissible relations relating any two types identified by `≈` is a
model of PI⁻ as soon as the four closed identity axioms are true in it. -/
theorem Frame.isModelPIm_of_invariance (F : Frame) (I : Invariance F)
    (hteq : ∀ a b, F.teq a b → ∃ R, I.Adm a b R)
    (h1 : F.Valid RefEqv) (h2 : F.Valid SymEqv) (h3 : F.Valid TransEqv) (h4 : F.Valid RefTeq) :
    F.IsModelPIm :=
  ⟨h1, h2, h3, h4, fun Q => I.llTeq_valid hteq Q⟩

/-- Admissible relations for the diagonal model: identity, at each type. -/
def diagInv : Invariance diag where
  Adm := fun a a' R => a = a' ∧ ∀ x y, R x y ↔ HEq x y
  refl := fun _ => ⟨rfl, fun x y => ⟨fun h => h ▸ HEq.rfl, eq_of_heq⟩⟩
  arrow := by
    rintro a a' c c' R S ⟨rfl, hR⟩ ⟨rfl, hS⟩
    refine ⟨rfl, fun f f' => ⟨fun h => heq_of_eq (funext fun u => eq_of_heq ((hS _ _).mp (h u u ((hR u u).mpr HEq.rfl)))), ?_⟩⟩
    intro h u u' hu
    have e1 := eq_of_heq h
    have e2 := eq_of_heq ((hR u u').mp hu)
    subst e1; subst e2; exact (hS _ _).mpr HEq.rfl
  total := by rintro a a' R ⟨rfl, hR⟩ u; exact ⟨u, (hR u u).mpr HEq.rfl⟩
  onto := by rintro a a' R ⟨rfl, hR⟩ u; exact ⟨u, (hR u u).mpr HEq.rfl⟩
  teq := by rintro a a' b b' R S ⟨rfl, _⟩ ⟨rfl, _⟩; exact Iff.rfl
  eqv := by
    rintro a a' b b' R S ⟨rfl, hR⟩ ⟨rfl, hS⟩ u u' v v' hu hv
    have e1 := eq_of_heq ((hR u u').mp hu)
    have e2 := eq_of_heq ((hS v v').mp hv)
    subst e1; subst e2; exact Iff.rfl

/-- Every instance of LL≡-Poly is true in the diagonal model (cf. *Formal Results*, Thm 19), by
the invariance lemma. -/
theorem diag_LLPoly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : diag.Valid (LLPoly P) :=
  diagInv.llPoly_valid (fun a b u v h => by
    obtain ⟨e, huv⟩ := h
    subst e
    exact ⟨fun x y => HEq x y, ⟨rfl, fun _ _ => Iff.rfl⟩, huv⟩) P

/-! ## 10. The principles of *Formal Results*, as sentences -/

section Principles
open Tm

abbrev tv3 {n : Nat} : Ty (n+4) := tvar (fs (fs (fs fz)))

/-- The type `σ → τ`. -/
def Ty.arrow {n : Nat} (σ τ : Ty n) : Ty n := ⟨.arr σ.1 τ.1, ⟨σ.2, τ.2⟩⟩

/-- `⊥` and `⊤` in any context. -/
def botF {n : Nat} {Γ : Ctx n} : Fm Γ := all tyT (.var .here)
def topF {n : Nat} {Γ : Ctx n} : Fm Γ := neg botF

/-- (Sym≈) -/
def SymTeq : Fm Ctx.nil := tall (tall (imp (teq tv1 tv0) (teq tv0 tv1)))
/-- (Trans≈) -/
def TransTeq : Fm Ctx.nil :=
  tall (tall (tall (imp (conj (teq tv2 tv1) (teq tv1 tv0)) (teq tv2 tv0))))
/-- (Link) `𝔸α𝔸β(α ≈ β → ∀_α x ∃_β y (x ≡ y))` -/
def Link : Fm Ctx.nil :=
  tall (tall (imp (teq tv1 tv0) (all tv1 (ex tv0 (eqv tv1 tv0 (.var (.there .here)) (.var .here))))))
/-- (Disjoint) `𝔸α𝔸β(¬(α ≈ β) → ∀_α x ∀_β y ¬(x ≡ y))` -/
def Disjoint : Fm Ctx.nil :=
  tall (tall (imp (neg (teq tv1 tv0)) (all tv1 (all tv0 (neg (eqv tv1 tv0 (.var (.there .here)) (.var .here)))))))
/-- (Slogan) `∀_e x 𝔸β ∀_{β→t} y ¬(x ≡ y)` -/
def Slogan : Fm Ctx.nil :=
  all tyE (tall (all tv0.pred (neg (eqv tyE tv0.pred (.var (.there (.tthere .here))) (.var .here)))))
/-- (Twin) `𝔸α ∀_α x 𝔼β (¬(α ≈ β) ∧ ∃_β y (x ≡ y))` -/
def Twin : Fm Ctx.nil :=
  tall (all tv0 (tex (conj (neg (teq tv1 tv0)) (ex tv0 (eqv tv1 tv0 (.var (.there (.tthere .here))) (.var .here))))))
/-- (Haecceitism) `𝔸α ∀_α x (x ≡_{α,α→t} λy:α.(y ≡_α x))` -/
def Hae : Fm Ctx.nil :=
  tall (all tv0 (eqv tv0 tv0.pred (.var .here) (.lam tv0 (eqv tv0 tv0 (.var .here) (.var (.there .here))))))
/-- (Cong) -/
def Cong : Fm Ctx.nil :=
  tall (tall (tall (tall (all (tv3.arrow tv1) (all (tv2.arrow tv0) (all tv3 (all tv2
    (imp (conj (eqv (tv3.arrow tv1) (tv2.arrow tv0) (.var (.there (.there (.there .here)))) (.var (.there (.there .here))))
               (eqv tv3 tv2 (.var (.there .here)) (.var .here)))
         (eqv tv1 tv0 (.app (.var (.there (.there (.there .here)))) (.var (.there .here)))
                      (.app (.var (.there (.there .here))) (.var .here)))))))))))
/-- (WCong) -/
def WCong : Fm Ctx.nil :=
  tall (tall (tall (tall (all (tv3.arrow tv1) (all (tv2.arrow tv0) (all tv3 (all tv2
    (imp (conj (conj (teq tv3 tv2) (teq tv1 tv0))
               (conj (eqv (tv3.arrow tv1) (tv2.arrow tv0) (.var (.there (.there (.there .here)))) (.var (.there (.there .here))))
                     (eqv tv3 tv2 (.var (.there .here)) (.var .here))))
         (eqv tv1 tv0 (.app (.var (.there (.there (.there .here)))) (.var (.there .here)))
                      (.app (.var (.there (.there .here))) (.var .here)))))))))))
/-- (PCong) -/
def PCong : Fm Ctx.nil :=
  tall (tall (tall (all (tv2.arrow tv1) (all (tv2.arrow tv0) (all tv2
    (imp (eqv (tv2.arrow tv1) (tv2.arrow tv0) (.var (.there (.there .here))) (.var (.there .here)))
         (eqv tv1 tv0 (.app (.var (.there (.there .here))) (.var .here)) (.app (.var (.there .here)) (.var .here)))))))))
/-- (Inj≈) -/
def Inj : Fm Ctx.nil :=
  tall (tall (tall (tall (imp (teq (tv3.arrow tv1) (tv2.arrow tv0)) (conj (teq tv3 tv2) (teq tv1 tv0))))))
/-- (Recovery) -/
def Recovery : Fm Ctx.nil :=
  tall (tall (tall (tall (imp (conj (teq (tv3.arrow tv1) (tv2.arrow tv0)) (teq tv3 tv2)) (teq tv1 tv0)))))
/-- (Truth) `∀_t p ∀_t q (p ≡_t q → (p → q))` -/
def Truth : Fm Ctx.nil :=
  all tyT (all tyT (imp (eqv tyT tyT (.var (.there .here)) (.var .here)) (imp (.var (.there .here)) (.var .here))))
/-- (Cantor) `𝔸α ∃_{α→t} G ∀_α y ¬(G ≡ y)` -/
def Cantor : Fm Ctx.nil :=
  tall (ex tv0.pred (all tv0 (neg (eqv tv0.pred tv0 (.var (.there .here)) (.var .here)))))
/-- `⊤ ≢_t ⊥` -/
def TopBot : Fm Ctx.nil := neg (eqv tyT tyT topF botF)
/-- `α ⊑ β`, that is `∀_α x ∃_β y (x ≡ y)`, for the two innermost type variables. -/
def subT {n : Nat} {Γ : Ctx (n+2)} : Fm Γ := all tv1 (ex tv0 (eqv tv1 tv0 (.var (.there .here)) (.var .here)))
def supT {n : Nat} {Γ : Ctx (n+2)} : Fm Γ := all tv0 (ex tv1 (eqv tv1 tv0 (.var .here) (.var (.there .here))))
/-- (Ext≈) -/
def ExtT : Fm Ctx.nil := tall (tall (imp (conj subT supT) (teq tv1 tv0)))
/-- `□φ`, that is `φ ≡_t ⊤`. -/
def boxF {n : Nat} {Γ : Ctx n} (φ : Fm Γ) : Fm Γ := eqv tyT tyT φ topF
/-- (Int≈) -/
def IntT : Fm Ctx.nil := tall (tall (imp (conj (boxF subT) (boxF supT)) (teq tv1 tv0)))

/-- (LL≡/≈), the instance for a polymorphic predicate `P`. -/
def Bridge {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : Fm Γ :=
  let P' := (P.twk.twk.wk tv1).wk tv0
  tall (tall (all tv1 (all tv0 (imp (conj (eqv tv1 tv0 (.var (.there .here)) (.var .here)) (teq tv1 tv0))
    (imp (.app (.tapp P' tv1) (.var (.there .here))) (.app (.tapp P' tv0) (.var .here)))))))

/-- The polymorphic predicate `λγ:∗.λz:γ.(γ ≈ e)` (*Formal Results*, Thm 13). -/
def PredE : Tm Ctx.nil (.pi (.arr (.var fz) .t)) := .tlam (.lam tv0 (teq tv0 tyE))

/-- The predicate `R` of *Formal Results*, Thm 12:
`λγ:∗.λz:γ.∃_{γ→t}F (F z ∧ ∃_{γ→t}G (F ≡ G ∧ ¬ G z))`. -/
def PredR : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (ex tv0.pred (conj (.app (.var .here) (.var (.there .here)))
    (ex tv0.pred (conj (eqv tv0.pred tv0.pred (.var (.there .here)) (.var .here))
      (neg (.app (.var .here) (.var (.there (.there .here))))))))))

end Principles

/-! ## 11. What the principles say in a frame

Each lemma below is proved by `Iff.rfl`: the truth condition of the sentence, computed by Lean,
*is* the displayed statement. -/

namespace Frame
variable (F : Frame)

/-- Truth of a sentence in a frame. -/
def Tr (φ : Fm Ctx.nil) : Prop := F.Holds φ (fun i => i.elim0) ()

theorem valid_iff_tr (φ : Fm Ctx.nil) : F.Valid φ ↔ F.Tr φ := by
  constructor
  · intro h; exact h _ _
  · intro h ρ env
    have : ρ = (fun i => i.elim0) := funext fun i => i.elim0
    subst this; exact h

/-- `R z` for the predicate `R` of Thm 12. -/
def Rf (a : Code F.U.Base) (z : F.U.El a) : Prop :=
  ∃ P : F.U.El a → Prop, P z ∧ ∃ G : F.U.El a → Prop, F.eqv (.arr a .t) (.arr a .t) P G ∧ ¬ G z

theorem tr_RefEqv : F.Tr RefEqv ↔ ∀ a (x : F.U.El a), F.eqv a a x x := Iff.rfl
theorem tr_SymEqv : F.Tr SymEqv ↔ ∀ a b (x : F.U.El a) (y : F.U.El b), F.eqv a b x y → F.eqv b a y x := Iff.rfl
theorem tr_TransEqv : F.Tr TransEqv ↔ ∀ a b c (x : F.U.El a) (y : F.U.El b) (z : F.U.El c),
    F.eqv a b x y ∧ F.eqv b c y z → F.eqv a c x z := Iff.rfl
theorem tr_RefTeq : F.Tr RefTeq ↔ ∀ a, F.teq a a := Iff.rfl
theorem tr_LLEqv : F.Tr LLEqv ↔ ∀ a (x y : F.U.El a), F.eqv a a x y → ∀ P : F.U.El a → Prop, P x → P y := Iff.rfl
theorem tr_SymTeq : F.Tr SymTeq ↔ ∀ a b, F.teq a b → F.teq b a := Iff.rfl
theorem tr_TransTeq : F.Tr TransTeq ↔ ∀ a b c, F.teq a b ∧ F.teq b c → F.teq a c := Iff.rfl
theorem tr_Link : F.Tr Link ↔ ∀ a b, F.teq a b → ∀ x : F.U.El a, ∃ y : F.U.El b, F.eqv a b x y := Iff.rfl
theorem tr_Disjoint : F.Tr Disjoint ↔ ∀ a b, ¬ F.teq a b → ∀ (x : F.U.El a) (y : F.U.El b), ¬ F.eqv a b x y := Iff.rfl
theorem tr_Slogan : F.Tr Slogan ↔ ∀ x : F.U.E, ∀ b (y : F.U.El b → Prop), ¬ F.eqv .e (.arr b .t) x y := Iff.rfl
theorem tr_Twin : F.Tr Twin ↔ ∀ a (x : F.U.El a), ∃ b, ¬ F.teq a b ∧ ∃ y : F.U.El b, F.eqv a b x y := Iff.rfl
theorem tr_Hae : F.Tr Hae ↔ ∀ a (x : F.U.El a), F.eqv a (.arr a .t) x (fun y => F.eqv a a y x) := Iff.rfl
theorem tr_Cong : F.Tr Cong ↔ ∀ a b c d (f : F.U.El a → F.U.El c) (g : F.U.El b → F.U.El d) x y,
    F.eqv (.arr a c) (.arr b d) f g ∧ F.eqv a b x y → F.eqv c d (f x) (g y) := Iff.rfl
theorem tr_WCong : F.Tr WCong ↔ ∀ a b c d (f : F.U.El a → F.U.El c) (g : F.U.El b → F.U.El d) x y,
    (F.teq a b ∧ F.teq c d) ∧ (F.eqv (.arr a c) (.arr b d) f g ∧ F.eqv a b x y) → F.eqv c d (f x) (g y) := Iff.rfl
theorem tr_PCong : F.Tr PCong ↔ ∀ a c d (f : F.U.El a → F.U.El c) (g : F.U.El a → F.U.El d) x,
    F.eqv (.arr a c) (.arr a d) f g → F.eqv c d (f x) (g x) := Iff.rfl
theorem tr_Inj : F.Tr Inj ↔ ∀ a b c d, F.teq (.arr a c) (.arr b d) → F.teq a b ∧ F.teq c d := Iff.rfl
theorem tr_Recovery : F.Tr Recovery ↔ ∀ a b c d, F.teq (.arr a c) (.arr b d) ∧ F.teq a b → F.teq c d := Iff.rfl
theorem tr_Truth : F.Tr Truth ↔ ∀ p q : Prop, F.eqv .t .t p q → p → q := Iff.rfl
theorem tr_Cantor : F.Tr Cantor ↔ ∀ a, ∃ G : F.U.El a → Prop, ∀ y : F.U.El a, ¬ F.eqv (.arr a .t) a G y := Iff.rfl
theorem tr_TopBot : F.Tr TopBot ↔ ¬ F.eqv .t .t (¬ ∀ p : Prop, p) (∀ p : Prop, p) := Iff.rfl
theorem tr_ExtT : F.Tr ExtT ↔ ∀ a b, ((∀ x : F.U.El a, ∃ y : F.U.El b, F.eqv a b x y) ∧
    (∀ y : F.U.El b, ∃ x : F.U.El a, F.eqv a b x y)) → F.teq a b := Iff.rfl
theorem tr_LLPolyE : F.Tr (LLPoly PredE) ↔
    ∀ a b (x : F.U.El a) (y : F.U.El b), F.eqv a b x y → F.teq a .e → F.teq b .e := Iff.rfl
theorem tr_LLPolyR : F.Tr (LLPoly PredR) ↔
    ∀ a b (x : F.U.El a) (y : F.U.El b), F.eqv a b x y → F.Rf a x → F.Rf b y := Iff.rfl
theorem tr_BridgeR : F.Tr (Bridge PredR) ↔
    ∀ a b (x : F.U.El a) (y : F.U.El b), F.eqv a b x y ∧ F.teq a b → F.Rf a x → F.Rf b y := Iff.rfl

/-- A frame is a model of PI⁻ when `≡` is an equivalence relation, `≈` is reflexive, and LL≈ holds. -/
theorem isModel_of (h1 : ∀ a (x : F.U.El a), F.eqv a a x x)
    (h2 : ∀ a b (x : F.U.El a) (y : F.U.El b), F.eqv a b x y → F.eqv b a y x)
    (h3 : ∀ a b c (x : F.U.El a) (y : F.U.El b) (z : F.U.El c), F.eqv a b x y ∧ F.eqv b c y z → F.eqv a c x z)
    (h4 : ∀ a, F.teq a a) (hLL : ∀ {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)), F.Valid (LLTeq Q)) :
    F.IsModelPIm :=
  ⟨(F.valid_iff_tr _).mpr h1, (F.valid_iff_tr _).mpr h2, (F.valid_iff_tr _).mpr h3,
    (F.valid_iff_tr _).mpr h4, hLL⟩

end Frame

/-! ## 12. Two ways of building models -/

theorem fun_heq_iff {A A' C C' : Type} (hA : A = A') (hC : C = C') {R : A → A' → Prop} {S : C → C' → Prop}
    (hR : ∀ x y, R x y ↔ HEq x y) (hS : ∀ x y, S x y ↔ HEq x y) (f : A → C) (f' : A' → C') :
    (∀ u u', R u u' → S (f u) (f' u')) ↔ HEq f f' := by
  subst hA; subst hC
  constructor
  · intro h; exact heq_of_eq (funext fun u => eq_of_heq ((hS _ _).mp (h u u ((hR u u).mpr HEq.rfl))))
  · intro h u u' hu
    have e1 := eq_of_heq h
    have e2 := eq_of_heq ((hR u u').mp hu)
    subst e1; subst e2; exact (hS _ _).mpr HEq.rfl

/-- **Key models.** Types are identified (`≈`) when their `T`-keys agree; an item of one type is
identified (`≡`) with an item of another when their `K`-keys agree and they are the same value.
`T` must be at least as fine as `K`, and compatible with `→`. -/
structure KeyData where
  U : Univ
  T : Code U.Base → Code U.Base
  K : Code U.Base → Code U.Base
  hK : ∀ a b, K a = K b → U.El a = U.El b
  hTK : ∀ a b, T a = T b → K a = K b
  hT : ∀ a a' c c', T a = T a' → T c = T c' → T (.arr a c) = T (.arr a' c')

namespace KeyData
variable (D : KeyData)

def frame : Frame where
  U := D.U
  eqv := fun a b x y => D.K a = D.K b ∧ HEq x y
  teq := fun a b => D.T a = D.T b

/-- Admissible relations: identity between types with the same `T`-key. -/
def inv : Invariance D.frame where
  Adm := fun a a' R => D.T a = D.T a' ∧ ∀ x y, R x y ↔ HEq x y
  refl := fun _ => ⟨rfl, fun _ _ => ⟨fun h => h ▸ HEq.rfl, eq_of_heq⟩⟩
  arrow := by
    rintro a a' c c' R S ⟨h1, hR⟩ ⟨h2, hS⟩
    exact ⟨D.hT _ _ _ _ h1 h2, fun f f' =>
      fun_heq_iff (D.hK _ _ (D.hTK _ _ h1)) (D.hK _ _ (D.hTK _ _ h2)) hR hS f f'⟩
  total := by
    rintro a a' R ⟨h, hR⟩ u
    exact ⟨cast (D.hK _ _ (D.hTK _ _ h)) u, (hR _ _).mpr (cast_heq _ _).symm⟩
  onto := by
    rintro a a' R ⟨h, hR⟩ u
    exact ⟨cast (D.hK _ _ (D.hTK _ _ h)).symm u, (hR _ _).mpr (cast_heq _ _)⟩
  teq := by
    rintro a a' b b' R S ⟨h1, -⟩ ⟨h2, -⟩
    show D.T a = D.T b ↔ D.T a' = D.T b'
    rw [h1, h2]
  eqv := by
    rintro a a' b b' R S ⟨h1, hR⟩ ⟨h2, hS⟩ u u' v v' hu hv
    show (D.K a = D.K b ∧ HEq u v) ↔ (D.K a' = D.K b' ∧ HEq u' v')
    rw [D.hTK _ _ h1, D.hTK _ _ h2]
    have hu' := (hR u u').mp hu
    have hv' := (hS v v').mp hv
    exact ⟨fun ⟨h, huv⟩ => ⟨h, hu'.symm.trans (huv.trans hv')⟩, fun ⟨h, huv⟩ => ⟨h, hu'.trans (huv.trans hv'.symm)⟩⟩

theorem model : D.frame.IsModelPIm :=
  D.frame.isModel_of (fun _ _ => ⟨rfl, HEq.rfl⟩) (fun _ _ _ _ ⟨h, e⟩ => ⟨h.symm, e.symm⟩)
    (fun _ _ _ _ _ _ ⟨⟨h1, e1⟩, ⟨h2, e2⟩⟩ => ⟨h1.trans h2, e1.trans e2⟩) (fun _ => rfl)
    (fun Q => D.inv.llTeq_valid (fun _ _ h => ⟨fun x y => HEq x y, h, fun _ _ => Iff.rfl⟩) Q)

theorem LLEqv_valid : D.frame.Valid LLEqv :=
  (D.frame.valid_iff_tr _).mpr <| D.frame.tr_LLEqv.mpr fun _ _ _ ⟨_, h⟩ _ hP => eq_of_heq h ▸ hP

/-- If `K` is as fine as `T`, every instance of LL≡-Poly holds. -/
theorem LLPoly_valid (hKT : ∀ a b, D.K a = D.K b → D.T a = D.T b) {n : Nat} {Γ : Ctx n}
    (P : Tm Γ (.pi (.arr (.var fz) .t))) : D.frame.Valid (LLPoly P) :=
  D.inv.llPoly_valid (fun _ _ _ _ ⟨hk, huv⟩ => ⟨fun x y => HEq x y, ⟨hKT _ _ hk, fun _ _ => Iff.rfl⟩, huv⟩) P

theorem Disjoint_valid (hKT : ∀ a b, D.K a = D.K b → D.T a = D.T b) : D.frame.Valid Disjoint :=
  (D.frame.valid_iff_tr _).mpr <| D.frame.tr_Disjoint.mpr fun _ _ hab _ _ ⟨hk, _⟩ => hab (hKT _ _ hk)

theorem ExtT_valid (hKT : ∀ a b, D.K a = D.K b → D.T a = D.T b) : D.frame.Valid ExtT :=
  (D.frame.valid_iff_tr _).mpr <| D.frame.tr_ExtT.mpr fun a _ ⟨h1, _⟩ =>
    let ⟨_, hk, _⟩ := h1 (Classical.choice (Univ.El_nonempty a)); hKT _ _ hk

theorem not_Twin (hKT : ∀ a b, D.K a = D.K b → D.T a = D.T b) : ¬ D.frame.Valid Twin := fun h =>
  let ⟨_, hab, _, hk, _⟩ := D.frame.tr_Twin.mp ((D.frame.valid_iff_tr _).mp h) .e
    (Classical.choice (Univ.El_nonempty (U := D.U) .e))
  hab (hKT _ _ hk)

theorem Cong_valid (hrec : ∀ a b c d, D.K (.arr a c) = D.K (.arr b d) → D.K a = D.K b → D.K c = D.K d) :
    D.frame.Valid Cong :=
  (D.frame.valid_iff_tr _).mpr <| D.frame.tr_Cong.mpr fun _ _ _ _ _ _ _ _ ⟨⟨h1, hf⟩, ⟨h2, hx⟩⟩ =>
    ⟨hrec _ _ _ _ h1 h2, heq_app (D.hK _ _ h2) (D.hK _ _ (hrec _ _ _ _ h1 h2)) hf hx⟩

end KeyData

/-- **Identification models** (*Formal Results*, Definition 11): `≈` is identity of types, and `≡`
is an equivalence relation on items. -/
structure IdentData where
  U : Univ
  rel : (Σ c, U.El c) → (Σ c, U.El c) → Prop
  refl : ∀ p, rel p p
  symm : ∀ {p q}, rel p q → rel q p
  trans : ∀ {p q r}, rel p q → rel q r → rel p r

/-- A permutation, with its inverse. -/
structure Perm (A : Type) where
  f : A → A
  g : A → A
  fg : ∀ x, f (g x) = x
  gf : ∀ x, g (f x) = x

def Perm.idp {A : Type} : Perm A := ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

def Perm.arrow {A C : Type} (θ : Perm A) (φ : Perm C) : Perm (A → C) where
  f := fun h x => φ.f (h (θ.g x))
  g := fun h x => φ.g (h (θ.f x))
  fg := fun h => funext fun x => by simp only [θ.fg, φ.fg]
  gf := fun h => funext fun x => by simp only [θ.gf, φ.gf]

section Swap
open Classical

/-- The permutation exchanging `u` and `v`. -/
noncomputable def swapF {A : Type} (u v x : A) : A := if x = u then v else if x = v then u else x

theorem swapF_u {A : Type} (u v : A) : swapF u v u = v := by simp [swapF]

theorem swapF_swapF {A : Type} (u v x : A) : swapF u v (swapF u v x) = x := by
  unfold swapF
  by_cases h1 : x = u
  · subst h1
    by_cases h2 : v = x
    · subst h2; simp
    · simp [h2]
  · by_cases h2 : x = v
    · subst h2; simp [h1]
    · simp [h1, h2]

noncomputable def Perm.swap {A : Type} (u v : A) : Perm A :=
  ⟨swapF u v, swapF u v, swapF_swapF u v, swapF_swapF u v⟩

end Swap

namespace IdentData
variable (D : IdentData)

def frame : Frame where
  U := D.U
  eqv := fun a b x y => D.rel ⟨a, x⟩ ⟨b, y⟩
  teq := fun a b => a = b

theorem model : D.frame.IsModelPIm :=
  D.frame.isModel_of (fun _ _ => D.refl _) (fun _ _ _ _ h => D.symm h)
    (fun _ _ _ _ _ _ ⟨h1, h2⟩ => D.trans h1 h2) (fun _ => rfl)
    (fun Q => D.frame.llTeq_of_teq_eq (fun _ _ h => h) Q)

theorem LLEqv_valid (hw : ∀ c (x y : D.U.El c), D.rel ⟨c, x⟩ ⟨c, y⟩ → x = y) : D.frame.Valid LLEqv :=
  (D.frame.valid_iff_tr _).mpr <| D.frame.tr_LLEqv.mpr fun _ _ _ h _ hP => hw _ _ _ h ▸ hP

theorem Inj_valid : D.frame.Valid Inj :=
  (D.frame.valid_iff_tr _).mpr <| D.frame.tr_Inj.mpr fun _ _ _ _ h => by
    injection h with h1 h2; exact ⟨h1, h2⟩

/-- Admissible relations from a family of permutations of the members of the type universe,
closed under `→` and respected by `≡` (*Formal Results*, Definition 12, with `≈` identity). -/
def permInv (allowed : (a : Code D.U.Base) → Perm (D.U.El a) → Prop)
    (hid : ∀ a, allowed a Perm.idp)
    (harr : ∀ a c θ φ, allowed a θ → allowed c φ → allowed (.arr a c) (Perm.arrow θ φ))
    (hrel : ∀ a b (θ : Perm (D.U.El a)) (φ : Perm (D.U.El b)) x y, allowed a θ → allowed b φ →
      (D.rel ⟨a, x⟩ ⟨b, y⟩ ↔ D.rel ⟨a, θ.f x⟩ ⟨b, φ.f y⟩)) : Invariance D.frame where
  Adm := fun a a' R => ∃ _ : a = a', ∃ θ : Perm (D.U.El a), allowed a θ ∧ ∀ x y, R x y ↔ HEq (θ.f x) y
  refl := fun a => ⟨rfl, Perm.idp, hid a, fun _ _ => ⟨fun h => h ▸ HEq.rfl, eq_of_heq⟩⟩
  arrow := by
    rintro a a' c c' R S ⟨rfl, θ, hθ, hR⟩ ⟨rfl, φ, hφ, hS⟩
    refine ⟨rfl, Perm.arrow θ φ, harr _ _ _ _ hθ hφ, fun f f' => ⟨fun h => ?_, fun h u u' hu => ?_⟩⟩
    · refine heq_of_eq (funext fun u' => ?_)
      have := h (θ.g u') u' ((hR _ _).mpr (heq_of_eq (θ.fg u')))
      exact eq_of_heq ((hS _ _).mp this)
    · have e := eq_of_heq h
      have e2 := eq_of_heq ((hR u u').mp hu)
      subst e2; subst e
      refine (hS _ _).mpr (heq_of_eq ?_)
      show φ.f (f u) = φ.f (f (θ.g (θ.f u)))
      exact congrArg (fun z => φ.f (f z)) (θ.gf u).symm
  total := by
    rintro a a' R ⟨rfl, θ, -, hR⟩ u
    exact ⟨θ.f u, (hR _ _).mpr HEq.rfl⟩
  onto := by
    rintro a a' R ⟨rfl, θ, -, hR⟩ u
    exact ⟨θ.g u, (hR _ _).mpr (heq_of_eq (θ.fg u))⟩
  teq := by
    rintro a a' b b' R S ⟨rfl, -⟩ ⟨rfl, -⟩
    exact Iff.rfl
  eqv := by
    rintro a a' b b' R S ⟨rfl, θ, hθ, hR⟩ ⟨rfl, φ, hφ, hS⟩ u u' v v' hu hv
    have e1 := eq_of_heq ((hR _ _).mp hu)
    have e2 := eq_of_heq ((hS _ _).mp hv)
    subst e1; subst e2
    exact hrel _ _ _ _ _ _ hθ hφ

theorem LLPoly_perm (allowed : (a : Code D.U.Base) → Perm (D.U.El a) → Prop)
    (hid : ∀ a, allowed a Perm.idp)
    (harr : ∀ a c θ φ, allowed a θ → allowed c φ → allowed (.arr a c) (Perm.arrow θ φ))
    (hrel : ∀ a b (θ : Perm (D.U.El a)) (φ : Perm (D.U.El b)) x y, allowed a θ → allowed b φ →
      (D.rel ⟨a, x⟩ ⟨b, y⟩ ↔ D.rel ⟨a, θ.f x⟩ ⟨b, φ.f y⟩))
    (hcrit : ∀ a b (x : D.U.El a) (y : D.U.El b), D.rel ⟨a, x⟩ ⟨b, y⟩ →
      ∃ _ : a = b, ∃ θ : Perm (D.U.El a), allowed a θ ∧ HEq (θ.f x) y)
    {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : D.frame.Valid (LLPoly P) :=
  (D.permInv allowed hid harr hrel).llPoly_valid (fun a b u v huv =>
    let ⟨h, θ, hθ, hx⟩ := hcrit a b u v huv
    ⟨fun x y => HEq (θ.f x) y, ⟨h, θ, hθ, fun _ _ => Iff.rfl⟩, hx⟩) P

end IdentData

/-! ## 13. The models of *Formal Results*

Each model is rebuilt over a type universe of codes. Where the paper's model uses facts about
particular hereditarily finite sets (for instance that `E = 2→2` is the very same set as the value
of `t→t`), the Lean model makes the corresponding identification explicit, by a map on codes. In
three cases (`𝔐_κ`, `𝔐_card`, `𝔐_ρ`) the Lean model is a simpler construction which has the same
pattern of true and false principles, and so establishes the same independence results. -/

section Models
open Frame

theorem sigma_fst_ne {U : Univ} {a b : Code U.Base} {x : U.El a} {y : U.El b}
    (h : (⟨a, x⟩ : Σ c, U.El c) = ⟨b, y⟩) (hab : a ≠ b) : False := hab (congrArg Sigma.fst h)

theorem arr_congr {B : Type} {a a' c c' : Code B} (h1 : a = a') (h2 : c = c') : Code.arr a c = Code.arr a' c' := by
  subst h1; subst h2; rfl

/-- Universes used below. -/
def univPP : Univ := { E := Prop → Prop, Base := Empty, B := Empty.elim, neE := ⟨fun p => p⟩, neB := fun b => b.elim }
def univK : Univ := { E := Unit, Base := Unit, B := fun _ => Prop, neE := ⟨()⟩, neB := fun _ => ⟨True⟩ }
def univC : Univ := { E := Unit, Base := Bool, B := fun _ => Unit, neE := ⟨()⟩, neB := fun _ => ⟨()⟩ }
def univR : Univ := { E := Unit, Base := Unit, B := fun _ => Unit, neE := ⟨()⟩, neB := fun _ => ⟨()⟩ }
def univP : Univ := { E := Unit, Base := Unit, B := fun _ => Fin 3, neE := ⟨()⟩, neB := fun _ => ⟨0⟩ }
def univ3 : Univ := { E := Fin 3, Base := Empty, B := Empty.elim, neE := ⟨0⟩, neB := fun b => b.elim }

/-! ### 𝔐(HF⁺, ∼₀) with `E = 1`: nothing is identified across types. -/

def M0D : KeyData where
  U := unitUniv
  T := id
  K := id
  hK := fun _ _ h => congrArg unitUniv.El h
  hTK := fun _ _ h => h
  hT := fun _ _ _ _ h1 h2 => arr_congr h1 h2

abbrev M0 : Frame := M0D.frame
theorem M0_model : M0.IsModelPIm := M0D.model
theorem M0_LLEqv : M0.Valid LLEqv := M0D.LLEqv_valid
theorem M0_Disjoint : M0.Valid Disjoint := M0D.Disjoint_valid (fun _ _ h => h)
theorem M0_LLPoly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : M0.Valid (LLPoly P) :=
  M0D.LLPoly_valid (fun _ _ h => h) P
theorem M0_Cong : M0.Valid Cong := M0D.Cong_valid (fun _ _ _ _ h _ => by injection h)
theorem M0_Inj : M0.Valid Inj :=
  (M0.valid_iff_tr _).mpr <| M0.tr_Inj.mpr fun _ _ _ _ h => by injection h with h1 h2; exact ⟨h1, h2⟩
theorem M0_ExtT : M0.Valid ExtT := M0D.ExtT_valid (fun _ _ h => h)
theorem M0_not_Twin : ¬ M0.Valid Twin := M0D.not_Twin (fun _ _ h => h)
theorem M0_Slogan : M0.Valid Slogan :=
  (M0.valid_iff_tr _).mpr <| M0.tr_Slogan.mpr fun _ _ _ ⟨h, _⟩ => by cases h

/-! ### 𝔐(HF⁺, ∼₀) with `E = 2→2`: the type of entities is the type `t→t`. -/

def norm0e : Code Empty → Code Empty
  | .e => .arr .t .t
  | .t => .t
  | .base b => b.elim
  | .arr a c => .arr (norm0e a) (norm0e c)

theorem El_norm0e : ∀ a, univPP.El (norm0e a) = univPP.El a
  | .e => rfl
  | .t => rfl
  | .base b => b.elim
  | .arr a c => by
    show (univPP.El (norm0e a) → univPP.El (norm0e c)) = (univPP.El a → univPP.El c)
    rw [El_norm0e a, El_norm0e c]

def M0eD : KeyData where
  U := univPP
  T := norm0e
  K := norm0e
  hK := fun a b h => (El_norm0e a).symm.trans ((congrArg univPP.El h).trans (El_norm0e b))
  hTK := fun _ _ h => h
  hT := fun _ _ _ _ h1 h2 => by show Code.arr _ _ = Code.arr _ _; rw [h1, h2]

abbrev M0e : Frame := M0eD.frame
theorem M0e_model : M0e.IsModelPIm := M0eD.model
theorem M0e_LLEqv : M0e.Valid LLEqv := M0eD.LLEqv_valid
theorem M0e_Disjoint : M0e.Valid Disjoint := M0eD.Disjoint_valid (fun _ _ h => h)
theorem M0e_LLPoly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : M0e.Valid (LLPoly P) :=
  M0eD.LLPoly_valid (fun _ _ h => h) P
theorem M0e_Cong : M0e.Valid Cong := M0eD.Cong_valid (fun _ _ _ _ h _ => by injection h)
theorem M0e_Inj : M0e.Valid Inj :=
  (M0e.valid_iff_tr _).mpr <| M0e.tr_Inj.mpr fun _ _ _ _ h => by injection h with h1 h2; exact ⟨h1, h2⟩
theorem M0e_ExtT : M0e.Valid ExtT := M0eD.ExtT_valid (fun _ _ h => h)
theorem M0e_not_Twin : ¬ M0e.Valid Twin := M0eD.not_Twin (fun _ _ h => h)
theorem M0e_not_Slogan : ¬ M0e.Valid Slogan := fun h =>
  M0e.tr_Slogan.mp ((M0e.valid_iff_tr _).mp h) (fun p => p) .t (fun p => p) ⟨rfl, HEq.rfl⟩

/-! ### `𝔐_κ`: the function types `e→t` and `e→D` are identified, but `t` and `D` are not. -/

def specialK (x y : Code Unit) : Code Unit := if x = .e ∧ y = .base () then .arr .e .t else .arr x y

def normK : Code Unit → Code Unit
  | .e => .e
  | .t => .t
  | .base u => .base u
  | .arr a c => specialK (normK a) (normK c)

theorem El_specialK (x y : Code Unit) : univK.El (specialK x y) = (univK.El x → univK.El y) := by
  unfold specialK
  split
  · next h => obtain ⟨rfl, rfl⟩ := h; rfl
  · rfl

theorem El_normK : ∀ a, univK.El (normK a) = univK.El a
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => (El_specialK _ _).trans (by rw [El_normK a, El_normK c]; rfl)

def MkD : KeyData where
  U := univK
  T := normK
  K := normK
  hK := fun a b h => (El_normK a).symm.trans ((congrArg univK.El h).trans (El_normK b))
  hTK := fun _ _ h => h
  hT := fun _ _ _ _ h1 h2 => by show specialK _ _ = specialK _ _; rw [h1, h2]

abbrev Mk : Frame := MkD.frame
theorem Mk_model : Mk.IsModelPIm := MkD.model
theorem Mk_LLEqv : Mk.Valid LLEqv := MkD.LLEqv_valid
theorem Mk_LLPoly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : Mk.Valid (LLPoly P) :=
  MkD.LLPoly_valid (fun _ _ h => h) P
theorem Mk_not_Inj : ¬ Mk.Valid Inj := fun h =>
  absurd (Mk.tr_Inj.mp ((Mk.valid_iff_tr _).mp h) .e .e .t (.base ())
    (show normK (.arr .e .t) = normK (.arr .e (.base ())) by decide)).2
    (show ¬ normK .t = normK (.base ()) by decide)
theorem Mk_not_Cong : ¬ Mk.Valid Cong := fun h =>
  absurd (Mk.tr_Cong.mp ((Mk.valid_iff_tr _).mp h) .e .e .t (.base ()) (fun _ => True) (fun _ => True) () ()
    ⟨⟨show normK (.arr .e .t) = normK (.arr .e (.base ())) by decide, HEq.rfl⟩, ⟨rfl, HEq.rfl⟩⟩).1
    (show ¬ normK .t = normK (.base ()) by decide)

/-! ### `𝔐_card`: `B→t` is identified with `A→t` though `A` and `B` are not identified. -/

def specialC (x y : Code Bool) : Code Bool :=
  if x = .base false ∧ y = .t then .arr (.base true) .t else .arr x y

def normC : Code Bool → Code Bool
  | .e => .e
  | .t => .t
  | .base u => .base u
  | .arr a c => specialC (normC a) (normC c)

theorem El_specialC (x y : Code Bool) : univC.El (specialC x y) = (univC.El x → univC.El y) := by
  unfold specialC
  split
  · next h => obtain ⟨rfl, rfl⟩ := h; rfl
  · rfl

theorem El_normC : ∀ a, univC.El (normC a) = univC.El a
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => (El_specialC _ _).trans (by rw [El_normC a, El_normC c]; rfl)

theorem specialC_inj {x y y' : Code Bool} (h : specialC x y = specialC x y') : y = y' := by
  unfold specialC at h
  split at h <;> split at h
  · next h1 h2 => exact h1.2.trans h2.2.symm
  · next h1 _ => injection h with h3 _; rw [h1.1] at h3; injection h3 with h4; cases h4
  · next _ h2 => injection h with h3 _; rw [h2.1] at h3; injection h3 with h4; cases h4
  · injection h with _ h4

def McardD : KeyData where
  U := univC
  T := normC
  K := normC
  hK := fun a b h => (El_normC a).symm.trans ((congrArg univC.El h).trans (El_normC b))
  hTK := fun _ _ h => h
  hT := fun _ _ _ _ h1 h2 => by show specialC _ _ = specialC _ _; rw [h1, h2]

theorem normC_rec (a b c d : Code Bool) (h1 : normC (.arr a c) = normC (.arr b d)) (h2 : normC a = normC b) :
    normC c = normC d := by
  change specialC (normC a) (normC c) = specialC (normC b) (normC d) at h1
  rw [h2] at h1
  exact specialC_inj h1

abbrev Mcard : Frame := McardD.frame
theorem Mcard_model : Mcard.IsModelPIm := McardD.model
theorem Mcard_LLEqv : Mcard.Valid LLEqv := McardD.LLEqv_valid
theorem Mcard_LLPoly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : Mcard.Valid (LLPoly P) :=
  McardD.LLPoly_valid (fun _ _ h => h) P
theorem Mcard_Cong : Mcard.Valid Cong := McardD.Cong_valid normC_rec
theorem Mcard_Recovery : Mcard.Valid Recovery :=
  (Mcard.valid_iff_tr _).mpr <| Mcard.tr_Recovery.mpr fun a b c d ⟨h1, h2⟩ => normC_rec a b c d h1 h2
theorem Mcard_not_Inj : ¬ Mcard.Valid Inj := fun h =>
  absurd (Mcard.tr_Inj.mp ((Mcard.valid_iff_tr _).mp h) (.base false) (.base true) .t .t
    (show normC (.arr (.base false) .t) = normC (.arr (.base true) .t) by decide)).1
    (show ¬ normC (.base false) = normC (.base true) by decide)

/-! ### `𝔐_ρ`: an entity is identified with an item of a type not identical to `e`, and
congruence still holds. -/

def normR : Code Unit → Code Unit
  | .e => .e
  | .t => .t
  | .base _ => .e
  | .arr a c => .arr (normR a) (normR c)

theorem El_normR : ∀ a, univR.El (normR a) = univR.El a
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => by
    show (univR.El (normR a) → univR.El (normR c)) = (univR.El a → univR.El c)
    rw [El_normR a, El_normR c]

def MrD : KeyData where
  U := univR
  T := id
  K := normR
  hK := fun a b h => (El_normR a).symm.trans ((congrArg univR.El h).trans (El_normR b))
  hTK := fun _ _ h => congrArg normR h
  hT := fun _ _ _ _ h1 h2 => arr_congr h1 h2

abbrev Mr : Frame := MrD.frame
theorem Mr_model : Mr.IsModelPIm := MrD.model
theorem Mr_LLEqv : Mr.Valid LLEqv := MrD.LLEqv_valid
theorem Mr_Cong : Mr.Valid Cong := MrD.Cong_valid (fun _ _ _ _ h _ => by injection h)
theorem Mr_not_Disjoint : ¬ Mr.Valid Disjoint := fun h =>
  Mr.tr_Disjoint.mp ((Mr.valid_iff_tr _).mp h) .e (.base ()) (show ¬ (Code.e : Code Unit) = .base () by decide)
    () () ⟨rfl, HEq.rfl⟩
theorem Mr_not_LLPoly : ¬ Mr.Valid (LLPoly PredE) := fun h =>
  absurd (Mr.tr_LLPolyE.mp ((Mr.valid_iff_tr _).mp h) .e (.base ()) () () ⟨rfl, HEq.rfl⟩ rfl)
    (show ¬ (Code.base () : Code Unit) = .e by decide)

/-! ### Identifications given by a pair of items: `∼₁` and `∼ₚ`. -/

/-- The identification generated by one pair of items of distinct types. -/
def pairIdent (U : Univ) (p0 q0 : Σ c, U.El c) (hne : p0.1 ≠ q0.1) : IdentData where
  U := U
  rel := fun p q => p = q ∨ (p = p0 ∧ q = q0) ∨ (p = q0 ∧ q = p0)
  refl := fun _ => Or.inl rfl
  symm := by
    rintro p q (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h2, h1⟩)
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
  trans := by
    have hne' : p0 ≠ q0 := fun h => hne (congrArg Sigma.fst h)
    rintro p q r (h | ⟨h1, h2⟩ | ⟨h1, h2⟩) (h' | ⟨h1', h2'⟩ | ⟨h1', h2'⟩)
    · exact Or.inl (h.trans h')
    · exact Or.inr (Or.inl ⟨h.trans h1', h2'⟩)
    · exact Or.inr (Or.inr ⟨h.trans h1', h2'⟩)
    · exact Or.inr (Or.inl ⟨h1, h'.symm.trans h2⟩)
    · exact absurd (h2.symm.trans h1') (Ne.symm hne')
    · exact Or.inl (h1.trans h2'.symm)
    · exact Or.inr (Or.inr ⟨h1, h'.symm.trans h2⟩)
    · exact Or.inl (h1.trans h2'.symm)
    · exact absurd (h2.symm.trans h1') hne'

theorem pairIdent_within (U : Univ) (p0 q0 : Σ c, U.El c) (hne : p0.1 ≠ q0.1) (c : Code U.Base)
    (x y : U.El c) (h : (pairIdent U p0 q0 hne).rel ⟨c, x⟩ ⟨c, y⟩) : x = y := by
  rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact eq_of_heq (Sigma.mk.inj h).2
  · have e1 : c = p0.1 := congrArg Sigma.fst h1
    have e2 : c = q0.1 := congrArg Sigma.fst h2
    exact absurd (e1.symm.trans e2) hne
  · have e1 : c = q0.1 := congrArg Sigma.fst h1
    have e2 : c = p0.1 := congrArg Sigma.fst h2
    exact absurd (e2.symm.trans e1) hne

/-- `∼₁`, with `E = 1`: the entity is identified with the falsehood. -/
def M1D : IdentData := pairIdent unitUniv ⟨.e, ()⟩ ⟨.t, False⟩ (show ¬ (Code.e : Code Empty) = .t by decide)

abbrev M1 : Frame := M1D.frame
theorem M1_model : M1.IsModelPIm := M1D.model
theorem M1_LLEqv : M1.Valid LLEqv := M1D.LLEqv_valid (pairIdent_within _ _ _ _)
theorem M1_Inj : M1.Valid Inj := M1D.Inj_valid
theorem M1_not_Disjoint : ¬ M1.Valid Disjoint := fun h =>
  M1.tr_Disjoint.mp ((M1.valid_iff_tr _).mp h) .e .t (show ¬ (Code.e : Code Empty) = .t by decide) () False
    (Or.inr (Or.inl ⟨rfl, rfl⟩))
theorem M1_not_LLPoly : ¬ M1.Valid (LLPoly PredE) := fun h =>
  absurd (M1.tr_LLPolyE.mp ((M1.valid_iff_tr _).mp h) .e .t () False (Or.inr (Or.inl ⟨rfl, rfl⟩)) rfl)
    (show ¬ (Code.t : Code Empty) = .e by decide)

theorem true_ne_false_heq (h : (⟨.t, True⟩ : Σ c, unitUniv.El c) = ⟨.t, False⟩) : False := by
  have e : True = False := eq_of_heq (Sigma.mk.inj h).2
  exact e ▸ trivial

theorem M1_ExtT : M1.Valid ExtT := by
  refine (M1.valid_iff_tr _).mpr <| M1.tr_ExtT.mpr fun a b ⟨h1, h2⟩ => Classical.byContradiction fun hab => ?_
  obtain ⟨y0, hr⟩ := h1 (Classical.choice (Univ.El_nonempty (U := unitUniv) a))
  rcases hr with h | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact hab (congrArg Sigma.fst h)
  · have ha' := congrArg Sigma.fst ha
    have hb' := congrArg Sigma.fst hb
    simp only at ha' hb'
    subst ha'; subst hb'
    obtain ⟨x, hx⟩ := h2 True
    rcases hx with h | ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hab (congrArg Sigma.fst h)
    · exact true_ne_false_heq h4
    · exact sigma_fst_ne h3 (show (Code.e : Code Empty) ≠ .t by decide)
  · have ha' := congrArg Sigma.fst ha
    have hb' := congrArg Sigma.fst hb
    simp only at ha' hb'
    subst ha'; subst hb'
    obtain ⟨y, hy⟩ := h1 True
    rcases hy with h | ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hab (congrArg Sigma.fst h)
    · exact sigma_fst_ne h3 (show (Code.t : Code Empty) ≠ .e by decide)
    · exact true_ne_false_heq h3

/-- `∼ₚ`, with `E = 1`: a function in `1→2` is identified with a function in `1→3` whose values
are not identified. -/
def f0p : univP.El (.arr .e .t) := fun _ => True
def g0p : univP.El (.arr .e (.base ())) := fun _ => (2 : Fin 3)
def MpD : IdentData := pairIdent univP ⟨.arr .e .t, f0p⟩ ⟨.arr .e (.base ()), g0p⟩
  (show ¬ (Code.arr .e .t : Code Unit) = .arr .e (.base ()) by decide)

abbrev Mp : Frame := MpD.frame
theorem Mp_model : Mp.IsModelPIm := MpD.model
theorem Mp_LLEqv : Mp.Valid LLEqv := MpD.LLEqv_valid (pairIdent_within _ _ _ _)
theorem Mp_Inj : Mp.Valid Inj := MpD.Inj_valid
theorem Mp_not_Disjoint : ¬ Mp.Valid Disjoint := fun h =>
  Mp.tr_Disjoint.mp ((Mp.valid_iff_tr _).mp h) (.arr .e .t) (.arr .e (.base ()))
    (show ¬ (Code.arr .e .t : Code Unit) = .arr .e (.base ()) by decide) f0p g0p
    (Or.inr (Or.inl ⟨rfl, rfl⟩))
theorem Mp_not_PCong : ¬ Mp.Valid PCong := fun h => by
  have := Mp.tr_PCong.mp ((Mp.valid_iff_tr _).mp h) .e .t (.base ()) f0p g0p () (Or.inr (Or.inl ⟨rfl, rfl⟩))
  rcases this with h | ⟨h3, _⟩ | ⟨h3, _⟩
  · exact sigma_fst_ne h (show (Code.t : Code Unit) ≠ .base () by decide)
  · exact sigma_fst_ne h3 (show (Code.t : Code Unit) ≠ .arr .e .t by decide)
  · exact sigma_fst_ne h3 (show (Code.t : Code Unit) ≠ .arr .e (.base ()) by decide)

/-! ### Identifications within each type: `𝔐_D`, `𝔐_E`, `𝔐_tot`, `𝔐_fn`.

In each, items are identified only with items of the same type; within a type, all items in a
distinguished class `S` are identified with each other. -/

def classIdent (U : Univ) (S : (c : Code U.Base) → U.El c → Prop) : IdentData where
  U := U
  rel := fun p q => p.1 = q.1 ∧ (HEq p.2 q.2 ∨ (S p.1 p.2 ∧ S q.1 q.2))
  refl := fun _ => ⟨rfl, Or.inl HEq.rfl⟩
  symm := fun ⟨h, h'⟩ => ⟨h.symm, h'.elim (fun e => Or.inl e.symm) (fun ⟨a, b⟩ => Or.inr ⟨b, a⟩)⟩
  trans := by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩ ⟨hab, h1⟩ ⟨hbc, h2⟩
    simp only at hab hbc
    subst hab; subst hbc
    refine ⟨rfl, ?_⟩
    rcases h1 with e1 | ⟨s1, s2⟩ <;> rcases h2 with e2 | ⟨s3, s4⟩
    · exact Or.inl (e1.trans e2)
    · exact Or.inr ⟨eq_of_heq e1 ▸ s3, s4⟩
    · exact Or.inr ⟨s1, eq_of_heq e2 ▸ s2⟩
    · exact Or.inr ⟨s1, s4⟩

theorem classIdent_Disjoint (U : Univ) (S : (c : Code U.Base) → U.El c → Prop) :
    (classIdent U S).frame.Valid Disjoint :=
  ((classIdent U S).frame.valid_iff_tr _).mpr <| (classIdent U S).frame.tr_Disjoint.mpr
    fun _ _ hab _ _ h => hab h.1

def chi0 : Fin 3 → Prop := fun v => v = 0
def zeta0 : Fin 3 → Prop := fun _ => False

/-- `𝔐_D` (Thm 12): `0 ∼ 1` at `e`, and `χ ∼ ζ` at `e→t`. -/
def SD : (c : Code Empty) → univ3.El c → Prop
  | .e, v => v = (0 : Fin 3) ∨ v = (1 : Fin 3)
  | .arr .e .t, v => v = chi0 ∨ v = zeta0
  | _, _ => False

def MDD : IdentData := classIdent univ3 SD
abbrev MD : Frame := MDD.frame
theorem MD_model : MD.IsModelPIm := MDD.model
theorem MD_Disjoint : MD.Valid Disjoint := classIdent_Disjoint univ3 SD
theorem MD_Inj : MD.Valid Inj := MDD.Inj_valid
theorem MD_not_LLEqv : ¬ MD.Valid LLEqv := fun h =>
  absurd (MD.tr_LLEqv.mp ((MD.valid_iff_tr _).mp h) .e (0 : Fin 3) (1 : Fin 3) ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩
    (fun (v : Fin 3) => v = 0) rfl) (by decide)

theorem MD_R0 : MD.Rf .e (0 : Fin 3) := ⟨chi0, rfl, zeta0, ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩, id⟩
theorem MD_not_R1 : ¬ MD.Rf .e (1 : Fin 3) := by
  rintro ⟨P, hP, G, ⟨_, hPG⟩, hG⟩
  rcases hPG with h | ⟨hS, _⟩
  · have e : P = G := eq_of_heq h
    exact hG (e ▸ hP)
  · rcases hS with rfl | rfl
    · have e : (1 : Fin 3) = 0 := hP
      exact absurd e (by decide)
    · exact hP

theorem MD_not_LLPoly : ¬ MD.Valid (LLPoly PredR) := fun h =>
  MD_not_R1 (MD.tr_LLPolyR.mp ((MD.valid_iff_tr _).mp h) .e .e (0 : Fin 3) (1 : Fin 3)
    ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩ MD_R0)
theorem MD_not_Bridge : ¬ MD.Valid (Bridge PredR) := fun h =>
  MD_not_R1 (MD.tr_BridgeR.mp ((MD.valid_iff_tr _).mp h) .e .e (0 : Fin 3) (1 : Fin 3)
    ⟨⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩, rfl⟩ MD_R0)

/-- `𝔐_E` (Thm 28(c)): `0 ∼ 1` at `e`, and nothing else. -/
def SE : (c : Code Empty) → univ3.El c → Prop
  | .e, v => v = (0 : Fin 3) ∨ v = (1 : Fin 3)
  | _, _ => False

def MED : IdentData := classIdent univ3 SE
abbrev ME : Frame := MED.frame
theorem ME_model : ME.IsModelPIm := MED.model
theorem ME_Disjoint : ME.Valid Disjoint := classIdent_Disjoint univ3 SE
theorem ME_Inj : ME.Valid Inj := MED.Inj_valid
theorem ME_not_LLEqv : ¬ ME.Valid LLEqv := fun h =>
  absurd (ME.tr_LLEqv.mp ((ME.valid_iff_tr _).mp h) .e (0 : Fin 3) (1 : Fin 3) ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩
    (fun (v : Fin 3) => v = 0) rfl) (by decide)
theorem ME_PCong : ME.Valid PCong := by
  refine (ME.valid_iff_tr _).mpr <| ME.tr_PCong.mpr fun a c d f g x ⟨h, hfg⟩ => ?_
  injection h with _ hcd
  subst hcd
  rcases hfg with hfg | ⟨hS, _⟩
  · have e : f = g := eq_of_heq hfg
    subst e; exact ⟨rfl, Or.inl HEq.rfl⟩
  · exact hS.elim
theorem ME_not_WCong : ¬ ME.Valid WCong := fun h => by
  have := ME.tr_WCong.mp ((ME.valid_iff_tr _).mp h) .e .e .t .t chi0 chi0 (0 : Fin 3) (1 : Fin 3)
    ⟨⟨rfl, rfl⟩, ⟨⟨rfl, Or.inl HEq.rfl⟩, ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩⟩⟩
  rcases this.2 with h' | ⟨h', _⟩
  · have e : chi0 0 = chi0 1 := eq_of_heq h'
    have e2 : chi0 1 := e ▸ (show chi0 0 from rfl)
    have e3 : (1 : Fin 3) = 0 := e2
    exact absurd e3 (by decide)
  · exact h'

/-- `𝔐_tot` (Def 13): any two items of the same type are identified. -/
def Mtot0 : IdentData := classIdent unitUniv (fun _ _ => True)
abbrev Mtot : Frame := Mtot0.frame
theorem Mtot_model : Mtot.IsModelPIm := Mtot0.model
theorem Mtot_Inj : Mtot.Valid Inj := Mtot0.Inj_valid
theorem Mtot_not_LLEqv : ¬ Mtot.Valid LLEqv := fun h =>
  Mtot.tr_LLEqv.mp ((Mtot.valid_iff_tr _).mp h) .t True False ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩ (fun p => p) trivial
theorem Mtot_not_Truth : ¬ Mtot.Valid Truth := fun h =>
  Mtot.tr_Truth.mp ((Mtot.valid_iff_tr _).mp h) True False ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩ trivial
theorem Mtot_not_TopBot : ¬ Mtot.Valid TopBot := fun h =>
  Mtot.tr_TopBot.mp ((Mtot.valid_iff_tr _).mp h) ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩
theorem Mtot_Cong : Mtot.Valid Cong :=
  (Mtot.valid_iff_tr _).mpr <| Mtot.tr_Cong.mpr fun _ _ _ _ _ _ _ _ ⟨⟨h, _⟩, _⟩ => by
    injection h with _ hcd; exact ⟨hcd, Or.inr ⟨trivial, trivial⟩⟩
theorem Mtot_ExtT : Mtot.Valid ExtT :=
  (Mtot.valid_iff_tr _).mpr <| Mtot.tr_ExtT.mpr fun a _ ⟨h1, _⟩ =>
    (h1 (Classical.choice (Univ.El_nonempty (U := unitUniv) a))).elim fun _ h => h.1
theorem Mtot_LLPoly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : Mtot.Valid (LLPoly P) :=
  Mtot0.LLPoly_perm (fun _ _ => True) (fun _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => ⟨fun ⟨h, _⟩ => ⟨h, Or.inr ⟨trivial, trivial⟩⟩, fun ⟨h, _⟩ => ⟨h, Or.inr ⟨trivial, trivial⟩⟩⟩)
    (fun a b x y ⟨h, _⟩ => by
      simp only at h
      subst h
      exact ⟨rfl, Perm.swap x y, trivial, heq_of_eq (swapF_u x y)⟩) P

/-- `𝔐_fn` (Thm 15): any two items of the same function type are identified. -/
def isArr {B : Type} : Code B → Prop
  | .arr _ _ => True
  | _ => False

def Mfn0 : IdentData := classIdent unitUniv (fun c _ => isArr c)
abbrev Mfn : Frame := Mfn0.frame
theorem Mfn_model : Mfn.IsModelPIm := Mfn0.model
theorem Mfn_Inj : Mfn.Valid Inj := Mfn0.Inj_valid
theorem Mfn_not_LLEqv : ¬ Mfn.Valid LLEqv := fun h =>
  Mfn.tr_LLEqv.mp ((Mfn.valid_iff_tr _).mp h) (.arr .e .t) (fun _ => False) (fun _ => True)
    ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩ (fun g => ¬ g ()) id trivial
theorem Mfn_not_WCong : ¬ Mfn.Valid WCong := fun h => by
  have := Mfn.tr_WCong.mp ((Mfn.valid_iff_tr _).mp h) .e .e .t .t (fun _ => False) (fun _ => True) () ()
    ⟨⟨rfl, rfl⟩, ⟨⟨rfl, Or.inr ⟨trivial, trivial⟩⟩, ⟨rfl, Or.inl HEq.rfl⟩⟩⟩
  rcases this.2 with h' | ⟨h', _⟩
  · have e : False = True := eq_of_heq h'
    exact e.symm ▸ trivial
  · exact h'
theorem Mfn_LLPoly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : Mfn.Valid (LLPoly P) := by
  refine Mfn0.LLPoly_perm (fun a θ => isArr a ∨ ∀ x, θ.f x = x) (fun _ => Or.inr fun _ => rfl)
    (fun _ _ _ _ _ _ => Or.inl trivial) ?_ ?_ P
  · intro a b θ φ x y hθ hφ
    show (a = b ∧ (HEq x y ∨ (isArr a ∧ isArr b))) ↔ (a = b ∧ (HEq (θ.f x) (φ.f y) ∨ (isArr a ∧ isArr b)))
    by_cases hab : a = b
    · subst hab
      by_cases ha : isArr a
      · exact ⟨fun _ => ⟨rfl, Or.inr ⟨ha, ha⟩⟩, fun _ => ⟨rfl, Or.inr ⟨ha, ha⟩⟩⟩
      · rw [hθ.resolve_left ha x, hφ.resolve_left ha y]
    · exact ⟨fun h => absurd h.1 hab, fun h => absurd h.1 hab⟩
  · intro a b x y ⟨h, hxy⟩
    simp only at h
    subst h
    rcases hxy with hxy | ⟨ha, _⟩
    · exact ⟨rfl, Perm.idp, Or.inr fun _ => rfl, hxy⟩
    · exact ⟨rfl, Perm.swap x y, Or.inl ha, heq_of_eq (swapF_u x y)⟩

/-! ### 𝔐(HF⁺, ∼ₕ): each item is identified with its haecceity (*Formal Results*, Thm 24). -/

abbrev Item := Σ c, unitUniv.El c

/-- The haecceity of an item: `(c, x) ↦ (c→t, λy. y = x)`. -/
def hh (p : Item) : Item := ⟨.arr p.1 .t, fun y => y = p.2⟩

/-- `n` steps along the chain of haecceities. -/
def hn : Nat → Item → Item
  | 0, p => p
  | n+1, p => hh (hn n p)

def csize : Code Empty → Nat
  | .e => 1
  | .t => 1
  | .base _ => 1
  | .arr a c => csize a + csize c + 1

theorem csize_hn (n : Nat) (p : Item) : csize (hn n p).1 = csize p.1 + 2 * n := by
  induction n with
  | zero => rfl
  | succ k ih => show csize (hn k p).1 + csize Code.t + 1 = _; rw [ih]; simp only [csize]; omega

theorem hh_inj {p q : Item} (h : hh p = hh q) : p = q := by
  obtain ⟨a, x⟩ := p
  obtain ⟨b, y⟩ := q
  have h1 : Code.arr a .t = Code.arr b .t := congrArg Sigma.fst h
  injection h1 with h1
  subst h1
  have h2 : (fun z => z = x) = (fun z => z = y) := eq_of_heq (Sigma.mk.inj h).2
  have h3 : (x = x) = (x = y) := congrFun h2 x
  have h4 : x = y := h3 ▸ rfl
  rw [h4]

theorem hn_inj (n : Nat) {p q : Item} (h : hn n p = hn n q) : p = q := by
  induction n with
  | zero => exact h
  | succ k ih => exact ih (hh_inj h)

theorem hn_add (m n : Nat) (p : Item) : hn (m + n) p = hn m (hn n p) := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ k ih => rw [Nat.succ_add]; show hh (hn (k + n) p) = hh (hn k (hn n p)); rw [ih]

/-- `∼ₕ`: two items are identified when they lie on one chain of haecceities. -/
def relH (p q : Item) : Prop := ∃ m n, hn m p = hn n q

theorem hn_cancel {m n : Nat} {p q : Item} (h : hn m p = hn n q) (hmn : n ≤ m) : hn (m - n) p = q := by
  have : hn n (hn (m - n) p) = hn n q := by rw [← hn_add, Nat.add_sub_cancel' hmn]; exact h
  exact hn_inj n this

theorem relH_cases {p q : Item} (h : relH p q) :
    p = q ∨ (∃ k, q = hn (k+1) p) ∨ (∃ k, p = hn (k+1) q) := by
  obtain ⟨m, n, h⟩ := h
  rcases Nat.lt_trichotomy m n with hlt | heq | hgt
  · right; right
    refine ⟨n - m - 1, ?_⟩
    rw [show n - m - 1 + 1 = n - m by omega]
    exact (hn_cancel h.symm (Nat.le_of_lt hlt)).symm
  · subst heq; left; exact hn_inj m h
  · right; left
    refine ⟨m - n - 1, ?_⟩
    rw [show m - n - 1 + 1 = m - n by omega]
    exact (hn_cancel h (Nat.le_of_lt hgt)).symm

theorem relH_size {p q : Item} (k : Nat) (h : q = hn (k+1) p) : csize q.1 = csize p.1 + 2 * (k+1) := by
  rw [h, csize_hn]

def MhD : IdentData where
  U := unitUniv
  rel := relH
  refl := fun _ => ⟨0, 0, rfl⟩
  symm := fun ⟨m, n, h⟩ => ⟨n, m, h.symm⟩
  trans := fun ⟨m, n, h1⟩ ⟨k, l, h2⟩ => ⟨k + m, n + l, by
    rw [hn_add, h1, ← hn_add, Nat.add_comm k n, hn_add, h2, ← hn_add]⟩

theorem relH_within (c : Code Empty) (x y : unitUniv.El c) (h : relH ⟨c, x⟩ ⟨c, y⟩) : x = y := by
  rcases relH_cases h with h | ⟨k, h⟩ | ⟨k, h⟩
  · exact eq_of_heq (Sigma.mk.inj h).2
  · have := relH_size k h; simp only at this; omega
  · have := relH_size k h; simp only at this; omega

/-- A haecceity is never the constantly false property. -/
theorem not_hh_false {D D' : Code Empty} (hD : D = D') (w : unitUniv.El D')
    (h : HEq (fun _ : unitUniv.El D => False) (fun y : unitUniv.El D' => y = w)) : False := by
  subst hD
  have e := congrFun (eq_of_heq h) w
  exact (e ▸ rfl : False)

abbrev Mh : Frame := MhD.frame
theorem Mh_model : Mh.IsModelPIm := MhD.model
theorem Mh_LLEqv : Mh.Valid LLEqv := MhD.LLEqv_valid relH_within
theorem Mh_Inj : Mh.Valid Inj := MhD.Inj_valid

theorem Mh_Hae : Mh.Valid Hae := by
  refine (Mh.valid_iff_tr _).mpr <| Mh.tr_Hae.mpr fun a x => ?_
  have e : (fun y => relH ⟨a, y⟩ ⟨a, x⟩) = (fun y => y = x) :=
    funext fun y => propext ⟨relH_within a y x, fun h => h ▸ ⟨0, 0, rfl⟩⟩
  show relH ⟨a, x⟩ ⟨.arr a .t, fun y => relH ⟨a, y⟩ ⟨a, x⟩⟩
  rw [e]
  exact ⟨1, 0, rfl⟩

theorem Mh_Twin : Mh.Valid Twin := by
  refine (Mh.valid_iff_tr _).mpr <| Mh.tr_Twin.mpr fun a x => ⟨.arr a .t, fun h => ?_, fun y => y = x, ⟨1, 0, rfl⟩⟩
  have := congrArg csize (h : a = .arr a .t)
  simp only [csize] at this
  omega

theorem Mh_PCong : Mh.Valid PCong := by
  refine (Mh.valid_iff_tr _).mpr <| Mh.tr_PCong.mpr fun a c d f g x hfg => ?_
  rcases relH_cases hfg with h | ⟨k, h⟩ | ⟨k, h⟩
  · have h1 : Code.arr a c = Code.arr a d := congrArg Sigma.fst h
    injection h1 with _ hcd
    subst hcd
    have e : f = g := eq_of_heq (Sigma.mk.inj h).2
    subst e
    exact ⟨0, 0, rfl⟩
  · have h1 : Code.arr a d = Code.arr (hn k ⟨.arr a c, f⟩).1 .t := congrArg Sigma.fst h
    injection h1 with h2 _
    have := congrArg csize h2
    rw [csize_hn] at this
    simp only [csize] at this
    omega
  · have h1 : Code.arr a c = Code.arr (hn k ⟨.arr a d, g⟩).1 .t := congrArg Sigma.fst h
    injection h1 with h2 _
    have := congrArg csize h2
    rw [csize_hn] at this
    simp only [csize] at this
    omega

theorem Mh_not_Cong : ¬ Mh.Valid Cong := fun h => by
  let f : Prop → Prop := fun _ => True
  have := Mh.tr_Cong.mp ((Mh.valid_iff_tr _).mp h) .t (.arr .t .t) .t .t f (fun Y => Y = f) False
    (fun z => z = False) ⟨⟨1, 0, rfl⟩, ⟨1, 0, rfl⟩⟩
  have e : True = ((fun z : Prop => z = False) = f) := relH_within .t _ _ this
  have e2 : (fun z : Prop => z = False) = f := e ▸ trivial
  have e3 : (True = False) = True := congrFun e2 True
  exact (e3.symm ▸ trivial : True = False) ▸ trivial

theorem Mh_ExtT : Mh.Valid ExtT := by
  refine (Mh.valid_iff_tr _).mpr <| Mh.tr_ExtT.mpr fun a b ⟨h1, h2⟩ => Classical.byContradiction fun hab => ?_
  obtain ⟨y0, r0⟩ := h1 (Classical.choice (Univ.El_nonempty (U := unitUniv) a))
  rcases relH_cases r0 with h | ⟨k, h⟩ | ⟨k, h⟩
  · exact hab (congrArg Sigma.fst h)
  · -- `b` is a type of properties, of larger size than `a`.
    have hs := relH_size k h
    simp only at hs
    have hb : b = .arr (hn k ⟨a, _⟩).1 .t := congrArg Sigma.fst h
    obtain ⟨x1, r1⟩ := h2 (cast (congrArg unitUniv.El hb).symm (fun _ => False))
    rcases relH_cases r1 with h' | ⟨j, h'⟩ | ⟨j, h'⟩
    · exact hab (congrArg Sigma.fst h')
    · have hb' : b = .arr (hn j ⟨a, x1⟩).1 .t := congrArg Sigma.fst h'
      have hsnd := (Sigma.mk.inj h').2
      have hbb := hb.symm.trans hb'
      injection hbb with hD
      refine not_hh_false hD (hn j ⟨a, x1⟩).2 ?_
      exact (cast_heq _ _).symm.trans hsnd
    · have := relH_size j h'
      simp only at this
      omega
  · -- `a` is a type of properties, of larger size than `b`.
    have hs := relH_size k h
    simp only at hs
    have ha : a = .arr (hn k ⟨b, _⟩).1 .t := congrArg Sigma.fst h
    obtain ⟨y1, r1⟩ := h1 (cast (congrArg unitUniv.El ha).symm (fun _ => False))
    rcases relH_cases r1 with h' | ⟨j, h'⟩ | ⟨j, h'⟩
    · exact hab (congrArg Sigma.fst h')
    · have := relH_size j h'
      simp only at this
      omega
    · have ha' : a = .arr (hn j ⟨b, y1⟩).1 .t := congrArg Sigma.fst h'
      have hsnd := (Sigma.mk.inj h').2
      have haa := ha.symm.trans ha'
      injection haa with hD
      refine not_hh_false hD (hn j ⟨b, y1⟩).2 ?_
      exact (cast_heq _ _).symm.trans hsnd

/-! ### Further facts and models found while exploring (not stated in *Formal Results*) -/

theorem KeyData.Slogan_valid (D : KeyData) (h : ∀ b, D.K .e ≠ D.K (.arr b .t)) : D.frame.Valid Slogan :=
  (D.frame.valid_iff_tr _).mpr <| D.frame.tr_Slogan.mpr fun _ b _ ⟨hk, _⟩ => h b hk

theorem Mr_not_ExtT : ¬ Mr.Valid ExtT := fun h =>
  absurd (Mr.tr_ExtT.mp ((Mr.valid_iff_tr _).mp h) .e (.base ())
    ⟨fun _ => ⟨(), rfl, HEq.rfl⟩, fun _ => ⟨(), rfl, HEq.rfl⟩⟩) (show ¬ (Code.e : Code Unit) = .base () by decide)

theorem Mk_not_PCong : ¬ Mk.Valid PCong := fun h =>
  absurd (Mk.tr_PCong.mp ((Mk.valid_iff_tr _).mp h) .e .t (.base ()) (fun _ => True) (fun _ => True) ()
    ⟨show normK (.arr .e .t) = normK (.arr .e (.base ())) by decide, HEq.rfl⟩).1
    (show ¬ normK .t = normK (.base ()) by decide)
theorem Mk_Disjoint : Mk.Valid Disjoint := MkD.Disjoint_valid (fun _ _ h => h)
theorem Mk_ExtT : Mk.Valid ExtT := MkD.ExtT_valid (fun _ _ h => h)
theorem Mk_Slogan : Mk.Valid Slogan := MkD.Slogan_valid fun b h => by
  change Code.e = specialK (normK b) .t at h
  unfold specialK at h; split at h <;> cases h
theorem Mcard_Disjoint : Mcard.Valid Disjoint := McardD.Disjoint_valid (fun _ _ h => h)
theorem Mcard_ExtT : Mcard.Valid ExtT := McardD.ExtT_valid (fun _ _ h => h)

theorem M1_Slogan : M1.Valid Slogan :=
  (M1.valid_iff_tr _).mpr <| M1.tr_Slogan.mpr fun _ b _ h => by
    rcases h with h | ⟨_, h2⟩ | ⟨h1, _⟩
    · exact sigma_fst_ne h (fun e => by cases e)
    · exact sigma_fst_ne h2 (fun e => by cases e)
    · exact sigma_fst_ne h1 (fun e => by cases e)

theorem Mp_Slogan : Mp.Valid Slogan :=
  (Mp.valid_iff_tr _).mpr <| Mp.tr_Slogan.mpr fun _ b _ h => by
    rcases h with h | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact sigma_fst_ne h (fun e => by cases e)
    · exact sigma_fst_ne h1 (fun e => by cases e)
    · exact sigma_fst_ne h1 (fun e => by cases e)

/-! #### The twin model: every type has a duplicate, with the same items. -/

def Btw : Bool → Type
  | true => Unit
  | false => Prop

theorem Btw_ne : ∀ b, Nonempty (Btw b)
  | true => ⟨()⟩
  | false => ⟨True⟩

def univTw : Univ := { E := Unit, Base := Bool, B := Btw, neE := ⟨()⟩, neB := Btw_ne }

/-- `base true` duplicates `e`, and `base false` duplicates `t`. -/
def normTw : Code Bool → Code Bool
  | .e => .e
  | .t => .t
  | .base true => .e
  | .base false => .t
  | .arr a c => .arr (normTw a) (normTw c)

theorem El_normTw : ∀ a, univTw.El (normTw a) = univTw.El a
  | .e => rfl
  | .t => rfl
  | .base true => rfl
  | .base false => rfl
  | .arr a c => by
    show (univTw.El (normTw a) → univTw.El (normTw c)) = (univTw.El a → univTw.El c)
    rw [El_normTw a, El_normTw c]

/-- The duplicate of a type. -/
def twinC : Code Bool → Code Bool
  | .e => .base true
  | .t => .base false
  | .base true => .e
  | .base false => .t
  | .arr a c => .arr (twinC a) c

theorem normTw_twin : ∀ a, normTw (twinC a) = normTw a
  | .e => rfl
  | .t => rfl
  | .base true => rfl
  | .base false => rfl
  | .arr a c => by show Code.arr (normTw (twinC a)) (normTw c) = _; rw [normTw_twin a]; rfl

theorem twin_ne : ∀ a, twinC a ≠ a
  | .e => fun h => by cases h
  | .t => fun h => by cases h
  | .base true => fun h => by cases h
  | .base false => fun h => by cases h
  | .arr a c => fun h => by injection h with h1; exact twin_ne a h1

def MtwD : KeyData where
  U := univTw
  T := id
  K := normTw
  hK := fun a b h => (El_normTw a).symm.trans ((congrArg univTw.El h).trans (El_normTw b))
  hTK := fun _ _ h => congrArg normTw h
  hT := fun _ _ _ _ h1 h2 => arr_congr h1 h2

abbrev Mtw : Frame := MtwD.frame
theorem Mtw_model : Mtw.IsModelPIm := MtwD.model
theorem Mtw_LLEqv : Mtw.Valid LLEqv := MtwD.LLEqv_valid
theorem Mtw_Cong : Mtw.Valid Cong := MtwD.Cong_valid (fun _ _ _ _ h _ => by injection h)
theorem Mtw_Inj : Mtw.Valid Inj :=
  (Mtw.valid_iff_tr _).mpr <| Mtw.tr_Inj.mpr fun _ _ _ _ h => by injection h with h1 h2; exact ⟨h1, h2⟩
theorem Mtw_Twin : Mtw.Valid Twin :=
  (Mtw.valid_iff_tr _).mpr <| Mtw.tr_Twin.mpr fun a x =>
    ⟨twinC a, fun h => twin_ne a h.symm,
     cast (MtwD.hK _ _ (normTw_twin a).symm) x, (normTw_twin a).symm, (cast_heq _ _).symm⟩
theorem Mtw_Slogan : Mtw.Valid Slogan := MtwD.Slogan_valid fun _ h => by cases h
theorem Mtw_not_Disjoint : ¬ Mtw.Valid Disjoint := fun h =>
  Mtw.tr_Disjoint.mp ((Mtw.valid_iff_tr _).mp h) .e (.base true) (fun e => by cases e) () () ⟨rfl, HEq.rfl⟩
theorem Mtw_not_ExtT : ¬ Mtw.Valid ExtT := fun h =>
  absurd (Mtw.tr_ExtT.mp ((Mtw.valid_iff_tr _).mp h) .e (.base true)
    ⟨fun _ => ⟨(), rfl, HEq.rfl⟩, fun _ => ⟨(), rfl, HEq.rfl⟩⟩) (fun e => by cases e)
theorem Mtw_not_Hae : ¬ Mtw.Valid Hae := fun h => by
  have := (Mtw.tr_Hae.mp ((Mtw.valid_iff_tr _).mp h) .e ()).1
  cases this

/-! #### A model of Cong in which Recovery fails. -/

/-- `normKt` collapses `D` onto `t`, so items of `D` and of `t` are identified; `≈` is given by
`normK`, which identifies `e→D` with `e→t` but not `D` with `t`. -/
def normKt : Code Unit → Code Unit
  | .e => .e
  | .t => .t
  | .base _ => .t
  | .arr a c => .arr (normKt a) (normKt c)

theorem El_normKt : ∀ a, univK.El (normKt a) = univK.El a
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => by
    show (univK.El (normKt a) → univK.El (normKt c)) = (univK.El a → univK.El c)
    rw [El_normKt a, El_normKt c]

theorem normKt_normK : ∀ a, normKt (normK a) = normKt a
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => by
    show normKt (specialK (normK a) (normK c)) = Code.arr (normKt a) (normKt c)
    rw [← normKt_normK a, ← normKt_normK c]
    unfold specialK
    split
    · next h => obtain ⟨h1, h2⟩ := h; rw [h1, h2]; rfl
    · rfl

def MrecD : KeyData where
  U := univK
  T := normK
  K := normKt
  hK := fun a b h => (El_normKt a).symm.trans ((congrArg univK.El h).trans (El_normKt b))
  hTK := fun a b h => (normKt_normK a).symm.trans ((congrArg normKt h).trans (normKt_normK b))
  hT := fun _ _ _ _ h1 h2 => by show specialK _ _ = specialK _ _; rw [h1, h2]

abbrev Mrec : Frame := MrecD.frame
theorem Mrec_model : Mrec.IsModelPIm := MrecD.model
theorem Mrec_LLEqv : Mrec.Valid LLEqv := MrecD.LLEqv_valid
theorem Mrec_Cong : Mrec.Valid Cong := MrecD.Cong_valid (fun _ _ _ _ h _ => by injection h)
theorem Mrec_not_Recovery : ¬ Mrec.Valid Recovery := fun h =>
  absurd (Mrec.tr_Recovery.mp ((Mrec.valid_iff_tr _).mp h) .e .e .t (.base ())
    ⟨show normK (.arr .e .t) = normK (.arr .e (.base ())) by decide, rfl⟩)
    (show ¬ normK .t = normK (.base ()) by decide)
theorem Mrec_not_Inj : ¬ Mrec.Valid Inj := fun h =>
  absurd (Mrec.tr_Inj.mp ((Mrec.valid_iff_tr _).mp h) .e .e .t (.base ())
    (show normK (.arr .e .t) = normK (.arr .e (.base ())) by decide)).2
    (show ¬ normK .t = normK (.base ()) by decide)
theorem Mrec_Slogan : Mrec.Valid Slogan := MrecD.Slogan_valid fun _ h => by cases h
theorem Mrec_not_Disjoint : ¬ Mrec.Valid Disjoint := fun h =>
  Mrec.tr_Disjoint.mp ((Mrec.valid_iff_tr _).mp h) .t (.base ()) (show ¬ normK .t = normK (.base ()) by decide)
    True True ⟨rfl, HEq.rfl⟩

/-! #### Int≈ and Ext≈ -/

theorem Frame.tr_IntT (F : Frame) : F.Tr IntT ↔ ∀ a b,
    (F.eqv .t .t (∀ x : F.U.El a, ∃ y : F.U.El b, F.eqv a b x y) (¬ ∀ p : Prop, p) ∧
     F.eqv .t .t (∀ y : F.U.El b, ∃ x : F.U.El a, F.eqv a b x y) (¬ ∀ p : Prop, p)) → F.teq a b := Iff.rfl

/-- Where `≡` at `t` is identity of truth values (as in every model of PI here), Int≈ and Ext≈ agree. -/
theorem Frame.IntT_iff_ExtT (F : Frame) (h : ∀ p q : Prop, F.eqv .t .t p q ↔ p = q) : F.Valid IntT ↔ F.Valid ExtT := by
  have key : ∀ P : Prop, F.eqv .t .t P (¬ ∀ p : Prop, p) ↔ P := fun P =>
    (h _ _).trans ⟨fun e => e ▸ (fun hall => hall False), fun hP => propext ⟨fun _ hall => hall False, fun _ => hP⟩⟩
  rw [F.valid_iff_tr, F.valid_iff_tr, F.tr_IntT, F.tr_ExtT]
  exact ⟨fun H a b hab => H a b ⟨(key _).mpr hab.1, (key _).mpr hab.2⟩,
         fun H a b hab => H a b ⟨(key _).mp hab.1, (key _).mp hab.2⟩⟩

theorem KeyData.eqv_t (D : KeyData) (p q : Prop) : D.frame.eqv .t .t p q ↔ p = q :=
  ⟨fun ⟨_, h⟩ => eq_of_heq h, fun h => ⟨rfl, h ▸ HEq.rfl⟩⟩

theorem IdentData.eqv_t (D : IdentData) (hw : ∀ c (x y : D.U.El c), D.rel ⟨c, x⟩ ⟨c, y⟩ → x = y) (p q : Prop) :
    D.frame.eqv .t .t p q ↔ p = q := ⟨hw .t p q, fun h => h ▸ D.refl _⟩

theorem M0_IntT : M0.Valid IntT := (M0.IntT_iff_ExtT M0D.eqv_t).mpr M0_ExtT
theorem M0e_IntT : M0e.Valid IntT := (M0e.IntT_iff_ExtT M0eD.eqv_t).mpr M0e_ExtT
theorem Mk_IntT : Mk.Valid IntT := (Mk.IntT_iff_ExtT MkD.eqv_t).mpr Mk_ExtT
theorem Mcard_IntT : Mcard.Valid IntT := (Mcard.IntT_iff_ExtT McardD.eqv_t).mpr Mcard_ExtT
theorem Mr_not_IntT : ¬ Mr.Valid IntT := fun h => Mr_not_ExtT ((Mr.IntT_iff_ExtT MrD.eqv_t).mp h)
theorem Mtw_not_IntT : ¬ Mtw.Valid IntT := fun h => Mtw_not_ExtT ((Mtw.IntT_iff_ExtT MtwD.eqv_t).mp h)
theorem M1_IntT : M1.Valid IntT := (M1.IntT_iff_ExtT (M1D.eqv_t (pairIdent_within _ _ _ _))).mpr M1_ExtT
theorem Mh_IntT : Mh.Valid IntT := (Mh.IntT_iff_ExtT (MhD.eqv_t relH_within)).mpr Mh_ExtT

/-- In `𝔐_tot` (a model of PI⁻ only) every `□φ` is true, so Int≈ fails although Ext≈ holds. -/
theorem Mtot_not_IntT : ¬ Mtot.Valid IntT := fun h =>
  absurd (Mtot.tr_IntT.mp ((Mtot.valid_iff_tr _).mp h) .e .t
    ⟨⟨rfl, Or.inr ⟨trivial, trivial⟩⟩, ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩⟩) (fun e => by cases e)

/-! #### Twins with the `𝔐_κ` collapse: Twin holds while PCong, Inj≈, and Recovery fail. -/

/-- Base types: duplicates of `e` and `t`, a second two-element type `D`, and a duplicate of `D`. -/
inductive B4 : Type where
  | de | dt | D | dD
  deriving DecidableEq

def B4El : B4 → Type
  | .de => Unit
  | .dt => Prop
  | .D => Prop
  | .dD => Prop

theorem B4El_ne : ∀ b, Nonempty (B4El b)
  | .de => ⟨()⟩
  | .dt => ⟨True⟩
  | .D => ⟨True⟩
  | .dD => ⟨True⟩

def univT2 : Univ := { E := Unit, Base := B4, B := B4El, neE := ⟨()⟩, neB := B4El_ne }

/-- The `𝔐_κ` step: `e → D` is sent to `e → t`. -/
def spT (x y : Code B4) : Code B4 := if x = .e ∧ y = .base .D then .arr .e .t else .arr x y

def normT2 : Code B4 → Code B4
  | .e => .e
  | .t => .t
  | .base b => .base b
  | .arr a c => spT (normT2 a) (normT2 c)

def dedup : B4 → Code B4
  | .de => .e
  | .dt => .t
  | .D => .base .D
  | .dD => .base .D

def normK2 : Code B4 → Code B4
  | .e => .e
  | .t => .t
  | .base b => dedup b
  | .arr a c => spT (normK2 a) (normK2 c)

theorem El_spT (x y : Code B4) : univT2.El (spT x y) = (univT2.El x → univT2.El y) := by
  unfold spT; split
  · next h => obtain ⟨rfl, rfl⟩ := h; rfl
  · rfl

theorem El_normT2 : ∀ a, univT2.El (normT2 a) = univT2.El a
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => (El_spT _ _).trans (by rw [El_normT2 a, El_normT2 c]; rfl)

theorem El_dedup : ∀ b, univT2.El (dedup b) = univT2.El (.base b)
  | .de => rfl
  | .dt => rfl
  | .D => rfl
  | .dD => rfl

theorem El_normK2 : ∀ a, univT2.El (normK2 a) = univT2.El a
  | .e => rfl
  | .t => rfl
  | .base b => El_dedup b
  | .arr a c => (El_spT _ _).trans (by rw [El_normK2 a, El_normK2 c]; rfl)

theorem normK2_normT2 : ∀ a, normK2 (normT2 a) = normK2 a
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => by
    show normK2 (spT (normT2 a) (normT2 c)) = spT (normK2 a) (normK2 c)
    rw [← normK2_normT2 a, ← normK2_normT2 c]
    unfold spT
    split
    · next h => obtain ⟨h1, h2⟩ := h; rw [h1, h2]; rfl
    · rfl

theorem spT_inj_left {x x' y : Code B4} (h : spT x y = spT x' y) : x = x' := by
  unfold spT at h
  split at h <;> split at h
  · next h1 h2 => exact h1.1.trans h2.1.symm
  · next h1 h2 => injection h with h3 h4; rw [h1.2] at h4; cases h4
  · next h1 h2 => injection h with h3 h4; rw [h2.2] at h4; cases h4
  · injection h

def twin2 : Code B4 → Code B4
  | .e => .base .de
  | .t => .base .dt
  | .base .de => .e
  | .base .dt => .t
  | .base .D => .base .dD
  | .base .dD => .base .D
  | .arr a c => .arr (twin2 a) c

theorem normK2_twin : ∀ a, normK2 (twin2 a) = normK2 a
  | .e => rfl
  | .t => rfl
  | .base .de => rfl
  | .base .dt => rfl
  | .base .D => rfl
  | .base .dD => rfl
  | .arr a c => by show spT (normK2 (twin2 a)) (normK2 c) = _; rw [normK2_twin a]; rfl

theorem normT2_twin_ne : ∀ a, normT2 (twin2 a) ≠ normT2 a
  | .e => fun h => by cases h
  | .t => fun h => by cases h
  | .base .de => fun h => by cases h
  | .base .dt => fun h => by cases h
  | .base .D => fun h => by cases h
  | .base .dD => fun h => by cases h
  | .arr a c => fun h => normT2_twin_ne a (spT_inj_left h)

def Mt2D : KeyData where
  U := univT2
  T := normT2
  K := normK2
  hK := fun a b h => (El_normK2 a).symm.trans ((congrArg univT2.El h).trans (El_normK2 b))
  hTK := fun a b h => (normK2_normT2 a).symm.trans ((congrArg normK2 h).trans (normK2_normT2 b))
  hT := fun _ _ _ _ h1 h2 => by show spT _ _ = spT _ _; rw [h1, h2]

abbrev Mt2 : Frame := Mt2D.frame
theorem Mt2_model : Mt2.IsModelPIm := Mt2D.model
theorem Mt2_LLEqv : Mt2.Valid LLEqv := Mt2D.LLEqv_valid
theorem Mt2_Twin : Mt2.Valid Twin :=
  (Mt2.valid_iff_tr _).mpr <| Mt2.tr_Twin.mpr fun a x =>
    ⟨twin2 a, fun h => normT2_twin_ne a h.symm,
     cast (Mt2D.hK _ _ (normK2_twin a).symm) x, (normK2_twin a).symm, (cast_heq _ _).symm⟩
theorem Mt2_not_PCong : ¬ Mt2.Valid PCong := fun h =>
  absurd (Mt2.tr_PCong.mp ((Mt2.valid_iff_tr _).mp h) .e .t (.base .D) (fun _ => True) (fun _ => True) ()
    ⟨show normK2 (.arr .e .t) = normK2 (.arr .e (.base .D)) by decide, HEq.rfl⟩).1
    (show ¬ normK2 .t = normK2 (.base .D) by decide)
theorem Mt2_not_Inj : ¬ Mt2.Valid Inj := fun h =>
  absurd (Mt2.tr_Inj.mp ((Mt2.valid_iff_tr _).mp h) .e .e .t (.base .D)
    (show normT2 (.arr .e .t) = normT2 (.arr .e (.base .D)) by decide)).2
    (show ¬ normT2 .t = normT2 (.base .D) by decide)
theorem Mt2_not_Recovery : ¬ Mt2.Valid Recovery := fun h =>
  absurd (Mt2.tr_Recovery.mp ((Mt2.valid_iff_tr _).mp h) .e .e .t (.base .D)
    ⟨show normT2 (.arr .e .t) = normT2 (.arr .e (.base .D)) by decide, rfl⟩)
    (show ¬ normT2 .t = normT2 (.base .D) by decide)
theorem Mt2_not_Disjoint : ¬ Mt2.Valid Disjoint := fun h =>
  Mt2.tr_Disjoint.mp ((Mt2.valid_iff_tr _).mp h) .e (.base .de) (show ¬ normT2 .e = normT2 (.base .de) by decide)
    () () ⟨rfl, HEq.rfl⟩

end Models

/-! ## A first derivation

From (Ref≡) and (Inst𝔸), with `e` for `α`, PI⁻ proves `∀_e x (x ≡_e x)`. The derivation is a
term of type `Prov`; Lean checks that each step is an instance of a rule. -/

example (S : Fm Ctx.nil → Prop) :
    PIm S Ctx.nil ((Tm.all tv0 (Tm.eqv tv0 tv0 (.var .here) (.var .here))).tinst tyE) :=
  Prov.mp Prov.refEqv (Prov.instTAll _ tyE)

/-- And so `∀_e x (x ≡_e x)` is true in every model of PI⁻, by soundness. -/
example (F : Frame) (hM : F.IsModelPIm) :
    F.Valid ((Tm.all (Γ := Ctx.nil.text) tv0 (Tm.eqv tv0 tv0 (.var .here) (.var .here))).tinst tyE) :=
  F.soundness hM (Ax := fun _ => False) (fun _ h => h.elim) (Prov.mp Prov.refEqv (Prov.instTAll _ tyE))

end PIF
