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

/-- Contexts. `ext Γ K` adds a term variable of category `K`; `text Γ` adds a type variable,
which becomes the type variable `fz`, the older ones being shifted by `fs`. -/
inductive Ctx : Nat → Type where
  | nil : Ctx 0
  | ext {n : Nat} : Ctx n → Cat n → Ctx n
  | text {n : Nat} : Ctx n → Ctx (n+1)

/-- Variables, as positions in a context, with their categories. -/
inductive Var : {n : Nat} → Ctx n → Cat n → Type where
  | here {n : Nat} {Γ : Ctx n} {K : Cat n} : Var (.ext Γ K) K
  | there {n : Nat} {Γ : Ctx n} {K L : Cat n} : Var Γ K → Var (.ext Γ L) K
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
  | lam {n : Nat} {Γ : Ctx n} (K : Cat n) {L : Cat n} : Tm (.ext Γ K) L → Tm Γ (.arr K L)
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

def TRen.lift {n m : Nat} {r : Fin n → Fin m} {Γ : Ctx n} {Δ : Ctx m} (ρ : TRen r Γ Δ) (K : Cat n) :
    TRen r (.ext Γ K) (.ext Δ (K.ren r)) := fun {_} x =>
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
  | _, .lam K b => .lam (K.ren r) (b.ren (ρ.lift K))
  | _, .tlam b => .tlam (b.ren ρ.tlift)
  | _, .tapp (K := K) f σ => Tm.castK (Cat.tapp_ren K σ r) (Tm.tapp (f.ren ρ) (σ.ren r))

/-- The renaming which adds a term variable at the front. -/
def wkRen {n : Nat} {Γ : Ctx n} (L : Cat n) : TRen (fun i => i) Γ (.ext Γ L) := fun {K} x =>
  Var.castK (Cat.ren_id K).symm (Var.there x)

/-- Weakening: a term in `Γ` is a term in `Γ` extended by one more term variable. -/
def Tm.wk {n : Nat} {Γ : Ctx n} {K : Cat n} (L : Cat n) (M : Tm Γ K) : Tm (.ext Γ L) K :=
  Tm.castK (Cat.ren_id K) (M.ren (wkRen L))

/-- The renaming which adds a type variable at the front. -/
def twkRen {n : Nat} (Γ : Ctx n) : TRen fs Γ (.text Γ) := fun x => .tthere x

/-- Type weakening. -/
def Tm.twk {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) : Tm (.text Γ) (K.ren fs) := M.ren (twkRen Γ)

/-- A substitution of terms for the term variables of `Γ`, along a substitution `s` of types for
type variables. -/
def TSub {n m : Nat} (s : Fin n → Ty m) (Γ : Ctx n) (Δ : Ctx m) : Type :=
  ∀ {K : Cat n}, Var Γ K → Tm Δ (K.sub s)

def TSub.lift {n m : Nat} {s : Fin n → Ty m} {Γ : Ctx n} {Δ : Ctx m} (σs : TSub s Γ Δ) (K : Cat n) :
    TSub s (.ext Γ K) (.ext Δ (K.sub s)) := fun {_} x =>
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
  | _, .lam K b => .lam (K.sub s) (b.sub (σs.lift K))
  | _, .tlam b => .tlam (b.sub σs.tlift)
  | _, .tapp (K := K) f σ => Tm.castK (Cat.tapp_sub K σ s) (Tm.tapp (f.sub σs) (σ.sub s))

/-- The substitution sending `here` to `N` and every other variable to itself. -/
def sub0 {n : Nat} {Γ : Ctx n} {K : Cat n} (N : Tm Γ K) : TSub tvar (.ext Γ K) Γ := fun {_} x =>
  match x with
  | .here => Tm.castK (Cat.sub_var K).symm N
  | .there y => Tm.castK (Cat.sub_var _).symm (.var y)

/-- Substituting `N` for the term variable `here`. -/
def Tm.subst0 {n : Nat} {Γ : Ctx n} {K L : Cat n} (M : Tm (.ext Γ K) L) (N : Tm Γ K) : Tm Γ L :=
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
  | .ext Γ K, ρ => Env Γ ρ × U.CatVal K ρ
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
  | lam K b ih =>
    intro m r Δ ρr ρ' env' ρ env hρ hx
    refine heq_funext (Univ.CatVal_ren _ r ρ' ρ hρ) (Univ.CatVal_ren _ r ρ' ρ hρ) fun v' v hv => ?_
    refine ih (ρr.lift K) ρ' (env', v') ρ (env, v) hρ ?_
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

theorem eval_wk {n : Nat} {Γ : Ctx n} {K : Cat n} (L : Cat n) (M : Tm Γ K) (ρ : F.U.TEnv n)
    (env : F.U.Env Γ ρ) (v : F.U.CatVal L ρ) : F.eval (M.wk L) (ρ) (env, v) = F.eval M ρ env :=
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
  | lam K b ih =>
    intro m s Δ σs ρ' env' ρ env hρ hx
    refine heq_funext (Univ.CatVal_sub _ s ρ' ρ hρ) (Univ.CatVal_sub _ s ρ' ρ hρ) fun v' v hv => ?_
    refine ih (σs.lift K) ρ' (env', v') ρ (env, v) hρ ?_
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

theorem eval_subst0 {n : Nat} {Γ : Ctx n} {K L : Cat n} (M : Tm (.ext Γ K) L) (N : Tm Γ K)
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
  | beta {n : Nat} {Γ : Ctx n} {K L : Cat n} (b : Tm (.ext Γ K) L) (a : Tm Γ K) :
      Step (.app (.lam K b) a) (b.subst0 a)
  | tbeta {n : Nat} {Γ : Ctx n} {K : Cat (n+1)} (b : Tm (.text Γ) K) (σ : Ty n) :
      Step (.tapp (.tlam b) σ) (b.tinst σ)
  | appL {n : Nat} {Γ : Ctx n} {K L : Cat n} {f f' : Tm Γ (.arr K L)} (a : Tm Γ K) :
      Step f f' → Step (.app f a) (.app f' a)
  | appR {n : Nat} {Γ : Ctx n} {K L : Cat n} (f : Tm Γ (.arr K L)) {a a' : Tm Γ K} :
      Step a a' → Step (.app f a) (.app f a')
  | lam {n : Nat} {Γ : Ctx n} (K : Cat n) {L : Cat n} {b b' : Tm (.ext Γ K) L} :
      Step b b' → Step (.lam K b) (.lam K b')
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
  | lam K _ ih => intro ρ env; exact funext fun v => ih ρ (env, v)
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
def all (σ : Ty n) (φ : Fm (.ext Γ σ.1)) : Fm Γ := .app (.tapp (.const .all) σ) (.lam σ.1 φ)
/-- `∃_σ x φ` -/
def ex (σ : Ty n) (φ : Fm (.ext Γ σ.1)) : Fm Γ := .app (.tapp (.const .ex) σ) (.lam σ.1 φ)
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

/-- The type `t`. -/
def tyT {n : Nat} : Ty n := ⟨.t, trivial⟩

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
  | instAll {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ.1)) (κ : Tm Γ σ.1) :
      Prov Ax Γ ((Tm.all σ φ).imp (φ.subst0 κ))
  /-- (Dist∀) -/
  | distAll {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm Γ) (ψ : Fm (.ext Γ σ.1)) :
      Prov Ax Γ ((Tm.all σ ((φ.wk σ.1).imp ψ)).imp (φ.imp (Tm.all σ ψ)))
  /-- (Dual∃) -/
  | dualEx {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ.1)) :
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
  | genAll {n : Nat} {Γ : Ctx n} (σ : Ty n) {φ : Fm (.ext Γ σ.1)} : Prov Ax (.ext Γ σ.1) φ → Prov Ax Γ (Tm.all σ φ)
  /-- (Gen𝔸) -/
  | genTAll {n : Nat} {Γ : Ctx n} {φ : Fm (.text Γ)} : Prov Ax (.text Γ) φ → Prov Ax Γ (Tm.tall φ)
  /-- renaming variables (weakening, exchange, contraction) -/
  | ren {n m : Nat} {Γ : Ctx n} {Δ : Ctx m} {r : Fin n → Fin m} (ρr : TRen r Γ Δ) {φ : Fm Γ} :
      Prov Ax Γ φ → Prov Ax Δ (φ.ren ρr)
  /-- discarding a term variable that does not occur -/
  | strengthen {n : Nat} {Γ : Ctx n} (K : Cat n) {φ : Fm Γ} : Prov Ax (.ext Γ K) (φ.wk K) → Prov Ax Γ φ
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

theorem holds_all (σ : Ty n) (φ : Fm (.ext Γ σ.1)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.Holds (Tm.all σ φ) ρ env ↔ ∀ v : F.U.CatVal σ.1 ρ, F.Holds φ ρ (env, v) :=
  cast_forall (Univ.El_code ρ σ.2) _ _

theorem holds_ex (σ : Ty n) (φ : Fm (.ext Γ σ.1)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
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
  | _, .ext Γ K, _, r, _, ρr, ρ', env' =>
      (pullEnv Γ (fun x => ρr (.there x)) ρ' env',
       cast (Univ.CatVal_ren K r ρ' _ (fun _ => rfl)) (F.U.lookup (ρr .here) ρ' env'))
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
    have hw : F.Holds (φ.wk σ.1) ρ (env, v) := by unfold Holds; rw [eval_wk]; exact hφ
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
  | strengthen K _ ih =>
    intro ρ env
    have v := Classical.choice (Univ.CatVal_nonempty K ρ)
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

The type universe has one entity; `≡` is identity (of an item with itself, across codes naming
the same set), and `≈` is identity of codes. This is the model `𝔐(HF⁺, ∼₀)` of *Formal Results*,
in miniature. -/

def unitUniv : Univ where
  E := Unit
  Base := Empty
  B := fun b => b.elim
  neE := ⟨()⟩
  neB := fun b => b.elim

def diag : Frame where
  U := unitUniv
  eqv := fun _ _ x y => HEq x y
  teq := fun a b => a = b

theorem diag_model : diag.IsModelPIm where
  refEqv := by
    intro ρ env a
    exact (diag.holds_all _ _ _ _).mpr fun v => (diag.holds_eqv _ _ _ _ _ _).mpr HEq.rfl
  symEqv := by
    intro ρ env a b
    refine (diag.holds_all _ _ _ _).mpr fun x => (diag.holds_all _ _ _ _).mpr fun y => ?_
    intro h
    exact (diag.holds_eqv _ _ _ _ _ _).mpr ((diag.holds_eqv _ _ _ _ _ _).mp h).symm
  transEqv := by
    intro ρ env a b c
    refine (diag.holds_all _ _ _ _).mpr fun x => (diag.holds_all _ _ _ _).mpr fun y =>
      (diag.holds_all _ _ _ _).mpr fun z => ?_
    intro h
    exact (diag.holds_eqv _ _ _ _ _ _).mpr
      (((diag.holds_eqv _ _ _ _ _ _).mp h.1).trans ((diag.holds_eqv _ _ _ _ _ _).mp h.2))
  refTeq := by
    intro ρ env a
    exact (diag.holds_teq _ _ _ _).mpr rfl
  llTeq := fun Q => diag.llTeq_of_teq_eq (fun _ _ h => h) Q

theorem diag_LLEqv : diag.Valid LLEqv := by
  intro ρ env a
  refine (diag.holds_all _ _ _ _).mpr fun x => (diag.holds_all _ _ _ _).mpr fun y => ?_
  intro h
  have h' := (diag.holds_eqv _ _ _ _ _ _).mp h
  have hxy : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h'.trans (cast_heq _ _)))
  subst hxy
  exact (diag.holds_all _ _ _ _).mpr fun _ hF => hF

/-- **PI is consistent**: it does not derive `⊥`. -/
theorem PI_consistent : ¬ PI (fun _ => False) Ctx.nil Bot :=
  diag.consistent_of_model diag_model (fun _ hψ => hψ.elim (fun e => e ▸ diag_LLEqv) False.elim)

/-! ## A first derivation

From (Ref≡) and (Inst𝔸), with `e` for `α`, PI⁻ proves `∀_e x (x ≡_e x)`. The derivation is a
term of type `Prov`; Lean checks that each step is an instance of a rule. -/

/-- The type `e`. -/
def tyE {n : Nat} : Ty n := ⟨.e, trivial⟩

example (S : Fm Ctx.nil → Prop) :
    PIm S Ctx.nil ((Tm.all tv0 (Tm.eqv tv0 tv0 (.var .here) (.var .here))).tinst tyE) :=
  Prov.mp Prov.refEqv (Prov.instTAll _ tyE)

/-- And so `∀_e x (x ≡_e x)` is true in every model of PI⁻, by soundness. -/
example (F : Frame) (hM : F.IsModelPIm) :
    F.Valid ((Tm.all (Γ := Ctx.nil.text) tv0 (Tm.eqv tv0 tv0 (.var .here) (.var .here))).tinst tyE) :=
  F.soundness hM (Ax := fun _ => False) (fun _ h => h.elim) (Prov.mp Prov.refEqv (Prov.instTAll _ tyE))

end PIF
