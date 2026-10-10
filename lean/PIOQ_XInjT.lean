import PIBF
set_option autoImplicit false

/-!
# `𝔐_wt,κ`: a model of PI in which Inj≈ and Recovery fail, with tagged propositions at two worlds

The algebraic semantics (`lean/PIAlg.lean`). Propositions are pairs of a set of two worlds (the
actual world `true` and another world `false`) and a tag; a proposition is true when it is true at
the actual world, and `□φ` (that is, `φ ≡ ⊤`) is true just in case `φ` is true at both worlds with
tag `true`. There is one entity, and one base type `D` whose items are propositions, like those of
`t`.

* `≈`: as in `𝔐_hae,κ` (`Mhk`, `lean/PIHae.lean`), types are compared after `D` in codomain
  position is replaced by `t`. So `e → t ≈ e → D`, while `t` and `D` are distinct: Inj≈ and
  Recovery fail. At the other world every type is `≈` every type; the tag is `false`.
* `≡`: at the actual world, items are identified when their types agree once every `D` is replaced
  by `t`, and they are the same item (so `t` and `D` share their items, and Ext≈, Int≈, Disjoint
  and LL≡-Poly fail). At the other world, everything is identified with everything; the tag is
  `false` (so NI≡, NI×, ND×, the Identity Identity, Booleanism and Classicism fail).
* The connectives act world by world, with tag `true`. At the other world, an existential
  quantification (over items or over types) is false (so Nec and TNec fail), and a universal one
  is true just in case all of its instances are true at the actual world and not all of them are
  `⊤` (so BF, CBF, TBF and TCBF fail).

LL≈ (and LL≡/≈, for every polymorphic predicate with parameters) holds by an invariance lemma for
the algebraic semantics, proved below, for the relations "same `≈`-normal form, and the same
item". Within a type, identity at the actual world is identity, so LL≡ holds.

The full profile. Valid: LL≡, LL≡/≈, Cong, WCong, PCong→, PCong←, Slogan, Truth, ⊤≢⊥, Cantor, T and
Functional Choice. Refuted: everything else: Classicism, Inj≈, Recovery, Disjoint, Twin,
Haecceitism, LL≡-Poly, PropExt≡, Ext≈, Int≈, Collapse, NI≡, NI≈, ND≈, NI×, ND×, Booleanism, the
Identity Identity, TBF, TCBF, TNec, BF, CBF and Nec.
-/

namespace PIF
namespace Al
open Tm

/-! ## Invariance for the algebraic semantics -/

/-- A family of admissible relations for an algebraic frame, which `≈`, `≡` and the item
quantifiers respect. -/
structure XIT_Inv (F : Frame) where
  Adm : (a a' : Code F.U.Base) → (F.U.El a → F.U.El a' → Prop) → Prop
  refl : ∀ a, Adm a a (fun x y => x = y)
  arrow : ∀ {a a' c c' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop} {S : F.U.El c → F.U.El c' → Prop},
    Adm a a' R → Adm c c' S → Adm (.arr a c) (.arr a' c') (fun f f' => ∀ u u', R u u' → S (f u) (f' u'))
  teq : ∀ {a a' b b' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop} {S : F.U.El b → F.U.El b' → Prop},
    Adm a a' R → Adm b b' S → F.teq a b = F.teq a' b'
  eqv : ∀ {a a' b b' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop} {S : F.U.El b → F.U.El b' → Prop},
    Adm a a' R → Adm b b' S → ∀ u u' v v', R u u' → S v v' → F.eqv a b u v = F.eqv a' b' u' v'
  all : ∀ {a a' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop}, Adm a a' R →
    ∀ (P : F.U.El a → F.U.P) (P' : F.U.El a' → F.U.P), (∀ u u', R u u' → P u = P' u') → F.all a P = F.all a' P'
  ex : ∀ {a a' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop}, Adm a a' R →
    ∀ (P : F.U.El a → F.U.P) (P' : F.U.El a' → F.U.P), (∀ u u', R u u' → P u = P' u') → F.ex a P = F.ex a' P'

section XIT_Invariance
variable {F : Frame}

/-- Relations for the type variables, extended by `R` for the new variable `fz`. -/
def XIT_RScons {n : Nat} {ρ ρ' : F.U.TEnv n} {a a' : Code F.U.Base} (R : F.U.El a → F.U.El a' → Prop)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) :
    ∀ i : Fin (n+1), F.U.El (scons a ρ i) → F.U.El (scons a' ρ' i) → Prop
  | ⟨0, _⟩ => R
  | ⟨k+1, h⟩ => Rs ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- The logical relation at each category: equality at `e` and `t`, the given relations at type
variables, preservation at `→`, and preservation under every admissible relation at `Π`. -/
def XIT_Rel (I : XIT_Inv F) : {n : Nat} → (K : Cat n) → (ρ ρ' : F.U.TEnv n) →
    (∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) → F.U.CatVal K ρ → F.U.CatVal K ρ' → Prop
  | _, .e, _, _, _ => fun x y => x = y
  | _, .t, _, _, _ => fun p q => p = q
  | _, .var i, _, _, Rs => Rs i
  | _, .arr K L, ρ, ρ', Rs => fun f f' => ∀ u u', XIT_Rel I K ρ ρ' Rs u u' → XIT_Rel I L ρ ρ' Rs (f u) (f' u')
  | _, .pi K, ρ, ρ', Rs => fun G G' => ∀ a a' (R : F.U.El a → F.U.El a' → Prop), I.Adm a a' R →
      XIT_Rel I K (scons a ρ) (scons a' ρ') (XIT_RScons R Rs) (G a) (G' a')

/-- The same relation at a type, on the sets its code names. -/
def XIT_RelE {n : Nat} : (K : Cat n) → (ρ ρ' : F.U.TEnv n) → (∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) →
    F.U.El (F.U.code K ρ) → F.U.El (F.U.code K ρ') → Prop
  | .e, _, _, _ => fun x y => x = y
  | .t, _, _, _ => fun p q => p = q
  | .var i, _, _, Rs => Rs i
  | .arr K L, ρ, ρ', Rs => fun f f' => ∀ x x', XIT_RelE K ρ ρ' Rs x x' → XIT_RelE L ρ ρ' Rs (f x) (f' x')
  | .pi _, _, _, _ => fun x y => x = y

theorem XIT_adm_RelE (I : XIT_Inv F) {n : Nat} (K : Cat n) : ∀ (ρ ρ' : F.U.TEnv n)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop),
    (∀ i, I.Adm (ρ i) (ρ' i) (Rs i)) → K.Simple →
    I.Adm (F.U.code K ρ) (F.U.code K ρ') (XIT_RelE K ρ ρ' Rs) := by
  induction K with
  | e => intros; exact I.refl _
  | t => intros; exact I.refl _
  | var i => intro ρ ρ' Rs hRs _; exact hRs i
  | arr a b iha ihb => intro ρ ρ' Rs hRs hK; exact I.arrow (iha ρ ρ' Rs hRs hK.1) (ihb ρ ρ' Rs hRs hK.2)
  | pi _ _ => intro _ _ _ _ hK; exact hK.elim

theorem XIT_Rel_RelE (I : XIT_Inv F) {n : Nat} (K : Cat n) : ∀ (_ : K.Simple) (ρ ρ' : F.U.TEnv n)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) (u : F.U.CatVal K ρ) (u' : F.U.CatVal K ρ')
    (x : F.U.El (F.U.code K ρ)) (x' : F.U.El (F.U.code K ρ')), HEq u x → HEq u' x' →
    (XIT_Rel I K ρ ρ' Rs u u' ↔ XIT_RelE K ρ ρ' Rs x x') := by
  induction K with
  | e => intro _ ρ ρ' Rs u u' x x' hx hx'; cases hx; cases hx'; exact Iff.rfl
  | t => intro _ ρ ρ' Rs u u' x x' hx hx'; cases hx; cases hx'; exact Iff.rfl
  | var i => intro _ ρ ρ' Rs u u' x x' hx hx'; cases hx; cases hx'; exact Iff.rfl
  | arr a b iha ihb =>
    intro hK ρ ρ' Rs u u' x x' hx hx'
    refine Invariance.forall_heq (Univ.El_code ρ hK.1).symm fun v y hvy => ?_
    refine Invariance.forall_heq (Univ.El_code ρ' hK.1).symm fun v' y' hvy' => ?_
    refine imp_congr (iha hK.1 ρ ρ' Rs v v' y y' hvy hvy') (ihb hK.2 ρ ρ' Rs _ _ _ _ ?_ ?_)
    · exact heq_app (Univ.El_code ρ hK.1).symm (Univ.El_code ρ hK.2).symm hx hvy
    · exact heq_app (Univ.El_code ρ' hK.1).symm (Univ.El_code ρ' hK.2).symm hx' hvy'
  | pi _ _ => intro hK; exact hK.elim

theorem XIT_Rel_ren (I : XIT_Inv F) {n : Nat} (K : Cat n) : ∀ {m : Nat} (r : Fin n → Fin m) (ρ ρ' : F.U.TEnv m)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) (ρ₂ ρ₂' : F.U.TEnv n)
    (Rs₂ : ∀ i, F.U.El (ρ₂ i) → F.U.El (ρ₂' i) → Prop)
    (_ : ∀ i, ρ (r i) = ρ₂ i) (_ : ∀ i, ρ' (r i) = ρ₂' i)
    (_ : ∀ i x x' y y', HEq x y → HEq x' y' → (Rs (r i) x x' ↔ Rs₂ i y y'))
    (v : F.U.CatVal (K.ren r) ρ) (v' : F.U.CatVal (K.ren r) ρ') (w : F.U.CatVal K ρ₂) (w' : F.U.CatVal K ρ₂'),
    HEq v w → HEq v' w' → (XIT_Rel I (K.ren r) ρ ρ' Rs v v' ↔ XIT_Rel I K ρ₂ ρ₂' Rs₂ w w') := by
  induction K with
  | e => intro m r ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ _ v v' w w' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | t => intro m r ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ _ v v' w w' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | var i => intro m r ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ hR v v' w w' hv hv'; exact hR i v v' w w' hv hv'
  | arr a b iha ihb =>
    intro m r ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR v v' w w' hv hv'
    refine Invariance.forall_heq (Univ.CatVal_ren a r ρ ρ₂ hρ) fun u y huy => ?_
    refine Invariance.forall_heq (Univ.CatVal_ren a r ρ' ρ₂' hρ') fun u' y' huy' => ?_
    refine imp_congr (iha r ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR u u' y y' huy huy')
      (ihb r ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR _ _ _ _ ?_ ?_)
    · exact heq_app (Univ.CatVal_ren a r ρ ρ₂ hρ) (Univ.CatVal_ren b r ρ ρ₂ hρ) hv huy
    · exact heq_app (Univ.CatVal_ren a r ρ' ρ₂' hρ') (Univ.CatVal_ren b r ρ' ρ₂' hρ') hv' huy'
  | pi K ih =>
    intro m r ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR v v' w w' hv hv'
    refine forall_congr' fun a => forall_congr' fun a' => forall_congr' fun R => imp_congr Iff.rfl ?_
    refine ih (liftR r) (scons a ρ) (scons a' ρ') (XIT_RScons R Rs) (scons a ρ₂) (scons a' ρ₂')
      (XIT_RScons R Rs₂) (fin_cases rfl (fun i => hρ i)) (fin_cases rfl (fun i => hρ' i)) ?_ _ _ _ _ ?_ ?_
    · refine fin_cases ?_ (fun i => fun x x' y y' hx hx' => hR i x x' y y' hx hx')
      intro x x' y y' hx hx'; cases hx; cases hx'; exact Iff.rfl
    · exact heq_dapp (fun a => Univ.CatVal_ren K (liftR r) (scons a ρ) (scons a ρ₂)
        (fin_cases rfl (fun i => hρ i))) hv rfl
    · exact heq_dapp (fun a => Univ.CatVal_ren K (liftR r) (scons a ρ') (scons a ρ₂')
        (fin_cases rfl (fun i => hρ' i))) hv' rfl

theorem XIT_Rel_sub (I : XIT_Inv F) {n : Nat} (K : Cat n) : ∀ {m : Nat} (s : Fin n → Ty m) (ρ ρ' : F.U.TEnv m)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) (ρ₂ ρ₂' : F.U.TEnv n)
    (Rs₂ : ∀ i, F.U.El (ρ₂ i) → F.U.El (ρ₂' i) → Prop)
    (_ : ∀ i, F.U.code (s i).1 ρ = ρ₂ i) (_ : ∀ i, F.U.code (s i).1 ρ' = ρ₂' i)
    (_ : ∀ i (x : F.U.CatVal (s i).1 ρ) (x' : F.U.CatVal (s i).1 ρ') y y', HEq x y → HEq x' y' →
      (XIT_Rel I (s i).1 ρ ρ' Rs x x' ↔ Rs₂ i y y'))
    (v : F.U.CatVal (K.sub s) ρ) (v' : F.U.CatVal (K.sub s) ρ') (w : F.U.CatVal K ρ₂) (w' : F.U.CatVal K ρ₂'),
    HEq v w → HEq v' w' → (XIT_Rel I (K.sub s) ρ ρ' Rs v v' ↔ XIT_Rel I K ρ₂ ρ₂' Rs₂ w w') := by
  induction K with
  | e => intro m s ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ _ v v' w w' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | t => intro m s ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ _ v v' w w' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | var i => intro m s ρ ρ' Rs ρ₂ ρ₂' Rs₂ _ _ hR v v' w w' hv hv'; exact hR i v v' w w' hv hv'
  | arr a b iha ihb =>
    intro m s ρ ρ' Rs ρ₂ ρ₂' Rs₂ hρ hρ' hR v v' w w' hv hv'
    refine Invariance.forall_heq (Univ.CatVal_sub a s ρ ρ₂ hρ) fun u y huy => ?_
    refine Invariance.forall_heq (Univ.CatVal_sub a s ρ' ρ₂' hρ') fun u' y' huy' => ?_
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
    refine ih (liftT s) (scons a ρ) (scons a' ρ') (XIT_RScons R Rs) (scons a ρ₂) (scons a' ρ₂')
      (XIT_RScons R Rs₂) (hl a ρ ρ₂ hρ) (hl a' ρ' ρ₂' hρ') ?_ _ _ _ _ ?_ ?_
    · refine fin_cases ?_ (fun i => ?_)
      · intro x x' y y' hx hx'; cases hx; cases hx'; exact Iff.rfl
      · intro x x' y y' hx hx'
        refine (XIT_Rel_ren I (s i).1 fs (scons a ρ) (scons a' ρ') (XIT_RScons R Rs) ρ ρ' Rs (fun _ => rfl)
          (fun _ => rfl) (fun j z z' q q' hz hz' => by cases hz; cases hz'; exact Iff.rfl)
          x x' (cast (Univ.CatVal_ren (s i).1 fs (scons a ρ) ρ (fun _ => rfl)) x)
          (cast (Univ.CatVal_ren (s i).1 fs (scons a' ρ') ρ' (fun _ => rfl)) x')
          (cast_heq _ _).symm (cast_heq _ _).symm).trans ?_
        exact hR i _ _ y y' ((cast_heq _ _).trans hx) ((cast_heq _ _).trans hx')
    · exact heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ) (scons a ρ₂) (hl a ρ ρ₂ hρ)) hv rfl
    · exact heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ') (scons a ρ₂') (hl a ρ' ρ₂' hρ')) hv' rfl

/-- Related values for the term variables of a context. -/
def XIT_EnvRel (I : XIT_Inv F) : {n : Nat} → (Γ : Ctx n) → (ρ ρ' : F.U.TEnv n) →
    (∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) → F.U.Env Γ ρ → F.U.Env Γ ρ' → Prop
  | _, .nil, _, _, _ => fun _ _ => True
  | _, .ext Γ σ, ρ, ρ', Rs => fun env env' =>
      XIT_EnvRel I Γ ρ ρ' Rs env.1 env'.1 ∧ XIT_Rel I σ.1 ρ ρ' Rs env.2 env'.2
  | _, .text Γ, ρ, ρ', Rs => fun env env' =>
      XIT_EnvRel I Γ (fun i => ρ (fs i)) (fun i => ρ' (fs i)) (fun i => Rs (fs i)) env env'

theorem XIT_lookup_rel (I : XIT_Inv F) {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) : ∀ (ρ ρ' : F.U.TEnv n)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) (env : F.U.Env Γ ρ) (env' : F.U.Env Γ ρ'),
    XIT_EnvRel I Γ ρ ρ' Rs env env' → XIT_Rel I K ρ ρ' Rs (F.U.lookup x ρ env) (F.U.lookup x ρ' env') := by
  induction x with
  | here => intro ρ ρ' Rs env env' h; exact h.2
  | there y ih => intro ρ ρ' Rs env env' h; exact ih ρ ρ' Rs env.1 env'.1 h.1
  | tthere y ih =>
    intro ρ ρ' Rs env env' h
    refine (XIT_Rel_ren I _ fs ρ ρ' Rs (fun i => ρ (fs i)) (fun i => ρ' (fs i)) (fun i => Rs (fs i))
      (fun _ => rfl) (fun _ => rfl) (fun i x x' y y' hx hx' => by cases hx; cases hx'; exact Iff.rfl)
      _ _ _ _ (F.lookup_tthere y ρ env) (F.lookup_tthere y ρ' env')).mpr ?_
    exact ih _ _ _ env env' h

theorem XIT_const_rel (I : XIT_Inv F) {n : Nat} {K : Cat n} (c : Const n K) (ρ ρ' : F.U.TEnv n)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) :
    XIT_Rel I K ρ ρ' Rs (F.constVal c ρ) (F.constVal c ρ') := by
  cases c with
  | neg => intro p p' hp; subst hp; rfl
  | imp => intro p p' hp q q' hq; subst hp; subst hq; rfl
  | and => intro p p' hp q q' hq; subst hp; subst hq; rfl
  | or => intro p p' hp q q' hq; subst hp; subst hq; rfl
  | iff => intro p p' hp q q' hq; subst hp; subst hq; rfl
  | all => intro a a' R hR P P' hP; exact I.all hR P P' hP
  | ex => intro a a' R hR P P' hP; exact I.ex hR P P' hP
  | tall =>
    intro Q Q' hQ
    have e : Q = Q' := funext fun a => hQ a a _ (I.refl a)
    subst e; rfl
  | tex =>
    intro Q Q' hQ
    have e : Q = Q' := funext fun a => hQ a a _ (I.refl a)
    subst e; rfl
  | eqv =>
    intro a a' R hR b b' S hS u u' hu v v' hv
    exact I.eqv hR hS u u' v v' hu hv
  | teq =>
    intro a a' R hR b b' S hS
    exact I.teq hR hS

/-- **The fundamental lemma** (invariance), for the algebraic semantics. -/
theorem XIT_fundamental (I : XIT_Inv F) {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) : ∀ (ρ ρ' : F.U.TEnv n)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop), (∀ i, I.Adm (ρ i) (ρ' i) (Rs i)) →
    ∀ (env : F.U.Env Γ ρ) (env' : F.U.Env Γ ρ'), XIT_EnvRel I Γ ρ ρ' Rs env env' →
    XIT_Rel I K ρ ρ' Rs (F.eval M ρ env) (F.eval M ρ' env') := by
  induction M with
  | var x => intro ρ ρ' Rs _ env env' h; exact XIT_lookup_rel I x ρ ρ' Rs env env' h
  | const c => intro ρ ρ' Rs _ _ _ _; exact XIT_const_rel I c ρ ρ' Rs
  | app f a ihf iha =>
    intro ρ ρ' Rs hRs env env' h
    exact ihf ρ ρ' Rs hRs env env' h _ _ (iha ρ ρ' Rs hRs env env' h)
  | lam σ b ih =>
    intro ρ ρ' Rs hRs env env' h u u' hu
    exact ih ρ ρ' Rs hRs (env, u) (env', u') ⟨h, hu⟩
  | tlam b ih =>
    intro ρ ρ' Rs hRs env env' h a a' R hR
    exact ih (scons a ρ) (scons a' ρ') (XIT_RScons R Rs) (fin_cases hR (fun i => hRs i)) env env' h
  | tapp f σ ih =>
    intro ρ ρ' Rs hRs env env' h
    have hf := ih ρ ρ' Rs hRs env env' h (F.U.code σ.1 ρ) (F.U.code σ.1 ρ') (XIT_RelE σ.1 ρ ρ' Rs)
      (XIT_adm_RelE I σ.1 ρ ρ' Rs hRs σ.2)
    refine (XIT_Rel_sub I _ (inst σ) ρ ρ' Rs (scons (F.U.code σ.1 ρ) ρ) (scons (F.U.code σ.1 ρ') ρ')
      (XIT_RScons (XIT_RelE σ.1 ρ ρ' Rs) Rs) (fin_cases rfl (fun _ => rfl)) (fin_cases rfl (fun _ => rfl)) ?_
      _ _ _ _ (F.heq_eval_tapp f σ ρ env) (F.heq_eval_tapp f σ ρ' env')).mpr hf
    refine fin_cases ?_ (fun i => ?_)
    · intro x x' y y' hx hx'; exact XIT_Rel_RelE I σ.1 σ.2 ρ ρ' Rs x x' y y' hx hx'
    · intro x x' y y' hx hx'; cases hx; cases hx'; exact Iff.rfl

/-- With identity relations, the logical relation at a type is identity. -/
theorem XIT_Rel_eq (I : XIT_Inv F) {n : Nat} (K : Cat n) : ∀ (_ : K.Simple) (ρ : F.U.TEnv n)
    (u u' : F.U.CatVal K ρ), XIT_Rel I K ρ ρ (fun _ x y => x = y) u u' ↔ u = u' := by
  induction K with
  | e => intros; exact Iff.rfl
  | t => intros; exact Iff.rfl
  | var i => intros; exact Iff.rfl
  | arr a b iha ihb =>
    intro hK ρ u u'
    constructor
    · intro h; funext x; exact (ihb hK.2 ρ _ _).mp (h x x ((iha hK.1 ρ x x).mpr rfl))
    · intro h x x' hx; rw [(iha hK.1 ρ x x').mp hx, h]; exact (ihb hK.2 ρ _ _).mpr rfl
  | pi _ _ => intro hK; exact hK.elim

theorem XIT_envRel_refl (I : XIT_Inv F) {n : Nat} (Γ : Ctx n) : ∀ (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ),
    XIT_EnvRel I Γ ρ ρ (fun _ x y => x = y) env env := by
  induction Γ with
  | nil => intros; trivial
  | ext Γ σ ih => intro ρ env; exact ⟨ih ρ env.1, (XIT_Rel_eq I σ.1 σ.2 ρ _ _).mpr rfl⟩
  | text Γ ih => intro ρ env; exact ih (fun i => ρ (fs i)) env

/-- A term of category `Πγ:∗.t` takes the same value at types related by an admissible relation. -/
theorem XIT_pi_t_invariant (I : XIT_Inv F) {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)) (ρ : F.U.TEnv n)
    (env : F.U.Env Γ ρ) {a b : Code F.U.Base} {R : F.U.El a → F.U.El b → Prop} (hR : I.Adm a b R) :
    F.eval Q ρ env a = F.eval Q ρ env b :=
  XIT_fundamental I Q ρ ρ _ (fun i => I.refl (ρ i)) env env (XIT_envRel_refl I Γ ρ env) a b R hR

/-- **LL≈ holds** in an algebraic frame with a family of admissible relations, if types identified
by `≈` are related by some admissible relation. -/
theorem XIT_llTeq_valid (I : XIT_Inv F) (hteq : ∀ a b, F.U.V (F.teq a b) → ∃ R, I.Adm a b R) {n : Nat}
    {Γ : Ctx n} (Q : Tm Γ (.pi .t)) : F.Valid (LLTeq Q) := by
  intro ρ env
  refine (F.holds_tall _ _ _).mpr fun a => (F.holds_tall _ _ _).mpr fun b => ?_
  refine (F.holds_imp _ _ _ _).mpr fun hab => (F.holds_imp _ _ _ _).mpr fun hq => ?_
  obtain ⟨R, hR⟩ := hteq a b ((F.holds_teq (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env).mp hab)
  have hG : HEq (F.eval Q.twk.twk (scons b (scons a ρ)) env) (F.eval Q ρ env) :=
    (F.eval_twk Q.twk b (scons a ρ) env).trans (F.eval_twk Q a ρ env)
  have h1 : HEq (F.eval (Tm.tapp Q.twk.twk tv1) (scons b (scons a ρ)) env) (F.eval Q ρ env a) :=
    (F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv1 (scons b (scons a ρ)) env).trans
      (heq_dapp (P := fun _ => F.U.P) (Q := fun _ => F.U.P) (fun _ => rfl) hG rfl)
  have h0 : HEq (F.eval (Tm.tapp Q.twk.twk tv0) (scons b (scons a ρ)) env) (F.eval Q ρ env b) :=
    (F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv0 (scons b (scons a ρ)) env).trans
      (heq_dapp (P := fun _ => F.U.P) (Q := fun _ => F.U.P) (fun _ => rfl) hG rfl)
  have e : F.eval (Tm.tapp Q.twk.twk tv0) (scons b (scons a ρ)) env =
      F.eval (Tm.tapp Q.twk.twk tv1) (scons b (scons a ρ)) env :=
    (eq_of_heq h0).trans ((XIT_pi_t_invariant I Q ρ env hR).symm.trans (eq_of_heq h1).symm)
  show F.U.V (F.eval (Tm.tapp Q.twk.twk tv0) (scons b (scons a ρ)) env)
  rw [e]
  exact hq

/-- **LL≡/≈ holds** in an algebraic frame with a family of admissible relations, if any two
identified items of types identified by `≈` are related by some admissible relation. -/
theorem XIT_bridge_valid (I : XIT_Inv F)
    (hE : ∀ a b u v, F.U.V (F.eqv a b u v) → F.U.V (F.teq a b) → ∃ R, I.Adm a b R ∧ R u v) {n : Nat}
    {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : F.Valid (Bridge P) := by
  intro ρ env
  refine (F.holds_tall _ _ _).mpr fun a => (F.holds_tall _ _ _).mpr fun b => ?_
  refine (F.holds_all _ _ _ _).mpr fun x => (F.holds_all _ _ _ _).mpr fun y => ?_
  refine (F.holds_imp _ _ _ _).mpr fun hc => (F.holds_imp _ _ _ _).mpr fun hPx => ?_
  obtain ⟨hxy, hab⟩ := (F.holds_conj _ _ _ _).mp hc
  obtain ⟨R, hR, hRxy⟩ := hE a b _ _ ((F.holds_eqv _ _ _ _ _ _).mp hxy) ((F.holds_teq _ _ _ _).mp hab)
  have hrel := XIT_fundamental I P ρ ρ _ (fun i => I.refl (ρ i)) env env (XIT_envRel_refl I Γ ρ env) a b R hR
    _ _ hRxy
  have hG : HEq (F.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y)) (F.eval P ρ env) :=
    (heq_of_eq ((F.eval_wk _ _ _ _ _).trans (F.eval_wk _ _ _ _ _))).trans
      ((F.eval_twk P.twk b (scons a ρ) env).trans (F.eval_twk P a ρ env))
  have h1 : F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (scons b (scons a ρ)) ((env, x), y) =
      F.eval P ρ env a :=
    eq_of_heq ((F.heq_eval_tapp (K := Cat.arr (Cat.var fz) Cat.t) ((P.twk.twk.wk tv1).wk tv0) tv1
      (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => F.U.El c → F.U.P) (Q := fun c => F.U.El c → F.U.P) (fun _ => rfl) hG rfl))
  have h0 : F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (scons b (scons a ρ)) ((env, x), y) =
      F.eval P ρ env b :=
    eq_of_heq ((F.heq_eval_tapp (K := Cat.arr (Cat.var fz) Cat.t) ((P.twk.twk.wk tv1).wk tv0) tv0
      (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => F.U.El c → F.U.P) (Q := fun c => F.U.El c → F.U.P) (fun _ => rfl) hG rfl))
  show F.U.V (F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (scons b (scons a ρ)) ((env, x), y) y)
  have hPx' : F.U.V (F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (scons b (scons a ρ)) ((env, x), y) x) := hPx
  rw [h1] at hPx'
  rw [h0]
  exact cast (congrArg F.U.V hrel) hPx'

end XIT_Invariance

/-! ## The model -/

/-- Propositions: a set of two worlds (the actual world `true`, and `false`), and a tag. -/
abbrev XIT_P : Type := (Bool → Prop) × Bool

/-- `⊤`: true at both worlds, with tag `true`. -/
def XIT_top : XIT_P := ((fun _ => True), true)

def XIT_U : Univ where
  P := XIT_P
  V := fun p => p.1 true
  p0 := XIT_top
  E := Unit
  Base := Unit
  B := fun _ => XIT_P
  neE := ⟨()⟩
  neB := fun _ => ⟨XIT_top⟩

abbrev XIT_C : Type := Code Unit

/-- `D` in codomain position becomes `t`. -/
def XIT_cod : XIT_C → XIT_C
  | .base _ => .t
  | c => c

/-- The `≈`-normal form of a type: `D` in codomain position becomes `t`, all the way down. -/
def XIT_Tn : XIT_C → XIT_C
  | .arr a c => .arr (XIT_Tn a) (XIT_cod (XIT_Tn c))
  | c => c

/-- The key of a type for identity of items: every `D` becomes `t`. -/
def XIT_K : XIT_C → XIT_C
  | .base _ => .t
  | .arr a c => .arr (XIT_K a) (XIT_K c)
  | c => c

theorem XIT_El_cod : ∀ c : XIT_C, XIT_U.El (XIT_cod c) = XIT_U.El c
  | .base _ => rfl
  | .e => rfl
  | .t => rfl
  | .arr _ _ => rfl

theorem XIT_El_Tn : ∀ c : XIT_C, XIT_U.El (XIT_Tn c) = XIT_U.El c
  | .arr a c => by
    show (XIT_U.El (XIT_Tn a) → XIT_U.El (XIT_cod (XIT_Tn c))) = (XIT_U.El a → XIT_U.El c)
    rw [XIT_El_cod, XIT_El_Tn a, XIT_El_Tn c]
  | .base _ => rfl
  | .e => rfl
  | .t => rfl

theorem XIT_El_K : ∀ c : XIT_C, XIT_U.El (XIT_K c) = XIT_U.El c
  | .arr a c => by
    show (XIT_U.El (XIT_K a) → XIT_U.El (XIT_K c)) = (XIT_U.El a → XIT_U.El c)
    rw [XIT_El_K a, XIT_El_K c]
  | .base _ => rfl
  | .e => rfl
  | .t => rfl

theorem XIT_K_cod : ∀ c : XIT_C, XIT_K (XIT_cod c) = XIT_K c
  | .base _ => rfl
  | .e => rfl
  | .t => rfl
  | .arr _ _ => rfl

theorem XIT_K_Tn : ∀ c : XIT_C, XIT_K (XIT_Tn c) = XIT_K c
  | .arr a c => by
    show Code.arr (XIT_K (XIT_Tn a)) (XIT_K (XIT_cod (XIT_Tn c))) = Code.arr (XIT_K a) (XIT_K c)
    rw [XIT_K_cod, XIT_K_Tn a, XIT_K_Tn c]
  | .base _ => rfl
  | .e => rfl
  | .t => rfl

theorem XIT_El_of_Tn {a a' : XIT_C} (h : XIT_Tn a = XIT_Tn a') : XIT_U.El a = XIT_U.El a' :=
  (XIT_El_Tn a).symm.trans ((congrArg XIT_U.El h).trans (XIT_El_Tn a'))

theorem XIT_El_of_K {a a' : XIT_C} (h : XIT_K a = XIT_K a') : XIT_U.El a = XIT_U.El a' :=
  (XIT_El_K a).symm.trans ((congrArg XIT_U.El h).trans (XIT_El_K a'))

theorem XIT_K_of_Tn {a a' : XIT_C} (h : XIT_Tn a = XIT_Tn a') : XIT_K a = XIT_K a' :=
  (XIT_K_Tn a).symm.trans ((congrArg XIT_K h).trans (XIT_K_Tn a'))

theorem XIT_K_e : ∀ b : XIT_C, XIT_K b = .e → b = .e
  | .e, _ => rfl
  | .t, h => by cases h
  | .base _, h => by cases h
  | .arr _ _, h => by cases h

/-- The frame. -/
def XIT_F : Frame where
  U := XIT_U
  eqv := fun a b x y => ((fun w => cond w (XIT_K a = XIT_K b ∧ HEq x y) True), false)
  teq := fun a b => ((fun w => cond w (XIT_Tn a = XIT_Tn b) True), false)
  neg := fun p => ((fun w => ¬ p.1 w), true)
  imp := fun p q => ((fun w => p.1 w → q.1 w), true)
  cnj := fun p q => ((fun w => p.1 w ∧ q.1 w), true)
  dsj := fun p q => ((fun w => p.1 w ∨ q.1 w), true)
  bic := fun p q => ((fun w => p.1 w ↔ q.1 w), true)
  all := fun _ f => ((fun w => cond w (∀ x, (f x).1 true) ((∀ x, (f x).1 true) ∧ ¬ ∀ x, f x = XIT_top)), true)
  ex := fun _ f => ((fun w => cond w (∃ x, (f x).1 true) False), true)
  tall := fun Q => ((fun w => cond w (∀ a, (Q a).1 true) ((∀ a, (Q a).1 true) ∧ ¬ ∀ a, Q a = XIT_top)), true)
  tex := fun Q => ((fun w => cond w (∃ a, (Q a).1 true) False), true)
  hneg := fun _ => Iff.rfl
  himp := fun _ _ => Iff.rfl
  hcnj := fun _ _ => Iff.rfl
  hdsj := fun _ _ => Iff.rfl
  hbic := fun _ _ => Iff.rfl
  hall := fun _ _ => Iff.rfl
  hex := fun _ _ => Iff.rfl
  htall := fun _ => Iff.rfl
  htex := fun _ => Iff.rfl

theorem XIT_forall_iff {A A' : Type} (e : A = A') (P : A → XIT_P) (P' : A' → XIT_P)
    (hP : ∀ x x', HEq x x' → P x = P' x') (Φ : XIT_P → Prop) : (∀ x, Φ (P x)) ↔ (∀ x', Φ (P' x')) := by
  subst e
  have e : P = P' := funext fun x => hP x x HEq.rfl
  subst e
  exact Iff.rfl

theorem XIT_exists_iff {A A' : Type} (e : A = A') (P : A → XIT_P) (P' : A' → XIT_P)
    (hP : ∀ x x', HEq x x' → P x = P' x') (Φ : XIT_P → Prop) : (∃ x, Φ (P x)) ↔ (∃ x', Φ (P' x')) := by
  subst e
  have e : P = P' := funext fun x => hP x x HEq.rfl
  subst e
  exact Iff.rfl

/-- The admissible relations: between types with the same `≈`-normal form, sameness of item. -/
def XIT_I : XIT_Inv XIT_F where
  Adm := fun a a' R => XIT_Tn a = XIT_Tn a' ∧ ∀ x y, R x y ↔ HEq x y
  refl := fun _ => ⟨rfl, fun _ _ => ⟨fun h => h ▸ HEq.rfl, eq_of_heq⟩⟩
  arrow := by
    rintro a a' c c' R S ⟨h1, hR⟩ ⟨h2, hS⟩
    refine ⟨?_, fun f f' => fun_heq_iff (XIT_El_of_Tn h1) (XIT_El_of_Tn h2) hR hS f f'⟩
    show Code.arr (XIT_Tn a) (XIT_cod (XIT_Tn c)) = Code.arr (XIT_Tn a') (XIT_cod (XIT_Tn c'))
    rw [h1, h2]
  teq := by
    rintro a a' b b' R S ⟨h1, -⟩ ⟨h2, -⟩
    show ((fun w => cond w (XIT_Tn a = XIT_Tn b) True), false) =
      (((fun w => cond w (XIT_Tn a' = XIT_Tn b') True), false) : XIT_P)
    rw [h1, h2]
  eqv := by
    rintro a a' b b' R S ⟨h1, hR⟩ ⟨h2, hS⟩ u u' v v' hu hv
    have hu' := (hR u u').mp hu
    have hv' := (hS v v').mp hv
    refine Prod.ext (funext fun w => ?_) rfl
    cases w
    · rfl
    · show (XIT_K a = XIT_K b ∧ HEq u v) = (XIT_K a' = XIT_K b' ∧ HEq u' v')
      rw [XIT_K_of_Tn h1, XIT_K_of_Tn h2]
      exact propext (and_congr Iff.rfl ⟨fun h => hu'.symm.trans (h.trans hv'),
        fun h => hu'.trans (h.trans hv'.symm)⟩)
  all := by
    rintro a a' R ⟨h, hR⟩ P P' hP
    have hP' : ∀ x x', HEq x x' → P x = P' x' := fun x x' hx => hP x x' ((hR x x').mpr hx)
    have e1 := XIT_forall_iff (XIT_El_of_Tn h) P P' hP' (fun p => p.1 true)
    have e2 := XIT_forall_iff (XIT_El_of_Tn h) P P' hP' (fun p => p = XIT_top)
    refine Prod.ext (funext fun w => ?_) rfl
    cases w
    · exact propext (and_congr e1 (not_congr e2))
    · exact propext e1
  ex := by
    rintro a a' R ⟨h, hR⟩ P P' hP
    have hP' : ∀ x x', HEq x x' → P x = P' x' := fun x x' hx => hP x x' ((hR x x').mpr hx)
    have e1 := XIT_exists_iff (XIT_El_of_Tn h) P P' hP' (fun p => p.1 true)
    refine Prod.ext (funext fun w => ?_) rfl
    cases w
    · rfl
    · exact propext e1

/-- **The model theorem**: the frame is a model of PI⁻. -/
theorem XIT_model : XIT_F.IsModelPIm where
  refEqv := by
    intro ρ env
    refine (XIT_F.holds_tall _ _ _).mpr fun a => ?_
    exact (XIT_F.holds_all _ _ _ _).mpr fun v => (XIT_F.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩
  symEqv := by
    intro ρ env
    refine (XIT_F.holds_tall _ _ _).mpr fun a => (XIT_F.holds_tall _ _ _).mpr fun b => ?_
    refine (XIT_F.holds_all _ _ _ _).mpr fun x => (XIT_F.holds_all _ _ _ _).mpr fun y => ?_
    refine (XIT_F.holds_imp _ _ _ _).mpr fun h => ?_
    have h' := (XIT_F.holds_eqv _ _ _ _ _ _).mp h
    exact (XIT_F.holds_eqv _ _ _ _ _ _).mpr ⟨h'.1.symm, h'.2.symm⟩
  transEqv := by
    intro ρ env
    refine (XIT_F.holds_tall _ _ _).mpr fun a => (XIT_F.holds_tall _ _ _).mpr fun b =>
      (XIT_F.holds_tall _ _ _).mpr fun c => ?_
    refine (XIT_F.holds_all _ _ _ _).mpr fun x => (XIT_F.holds_all _ _ _ _).mpr fun y =>
      (XIT_F.holds_all _ _ _ _).mpr fun z => ?_
    refine (XIT_F.holds_imp _ _ _ _).mpr fun h => ?_
    have h' := (XIT_F.holds_conj _ _ _ _).mp h
    have h1 := (XIT_F.holds_eqv _ _ _ _ _ _).mp h'.1
    have h2 := (XIT_F.holds_eqv _ _ _ _ _ _).mp h'.2
    exact (XIT_F.holds_eqv _ _ _ _ _ _).mpr ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  refTeq := by
    intro ρ env
    exact (XIT_F.holds_tall _ _ _).mpr fun a => (XIT_F.holds_teq _ _ _ _).mpr rfl
  llTeq := fun Q => XIT_llTeq_valid XIT_I (fun _ _ h => ⟨fun x y => HEq x y, h, fun _ _ => Iff.rfl⟩) Q

/-- LL≡ holds: within a type, identity at the actual world is identity. -/
theorem XIT_LLEqv : XIT_F.Valid LLEqv := by
  intro ρ env
  refine (XIT_F.holds_tall _ _ _).mpr fun a => ?_
  refine (XIT_F.holds_all _ _ _ _).mpr fun x => (XIT_F.holds_all _ _ _ _).mpr fun y => ?_
  refine (XIT_F.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (XIT_F.holds_all _ _ _ _).mpr fun G => (XIT_F.holds_imp _ _ _ _).mpr fun hGx => ?_
  have e : x = y := eq_of_heq ((XIT_F.holds_eqv _ _ _ _ _ _).mp hxy).2
  subst e
  exact hGx

/-- Whatever PI proves is valid. -/
theorem XIT_of_prov {φ : Fm Ctx.nil} (h : Prov (· = LLEqv) Ctx.nil φ) : XIT_F.Valid φ :=
  XIT_F.soundness XIT_model (fun χ (e : χ = LLEqv) => e ▸ XIT_LLEqv) h

/-- `⊤` has the value `XIT_top`. -/
theorem XIT_top_eq {n : Nat} {Γ : Ctx n} (ρ : XIT_F.U.TEnv n) (env : XIT_F.U.Env Γ ρ) :
    XIT_F.eval (topF : Fm Γ) ρ env = XIT_top := by
  refine Prod.ext (funext fun w => ?_) rfl
  cases w
  · exact propext ⟨fun _ => trivial, fun _ h => (h.1 ((fun _ => False), true) : False)⟩
  · exact propext ⟨fun _ => trivial, fun _ h => (h ((fun _ => False), true) : False)⟩

/-- `□φ` holds just in case `φ` has the value of `⊤`: true at both worlds, with tag `true`. -/
theorem XIT_holds_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : XIT_F.U.TEnv n) (env : XIT_F.U.Env Γ ρ) :
    XIT_F.Holds (boxF φ) ρ env ↔ XIT_F.eval φ ρ env = XIT_top :=
  (XIT_F.holds_eqv_t _ _ _ _).trans
    ⟨fun h => (eq_of_heq h.2).trans (XIT_top_eq ρ env),
     fun h => ⟨rfl, heq_of_eq (h.trans (XIT_top_eq ρ env).symm)⟩⟩

theorem XIT_cast_ex_eq {c : Code XIT_F.U.Base} {A' : Type} (hA : XIT_F.U.El c = A')
    (h : ((XIT_F.U.El c → XIT_F.U.P) → XIT_F.U.P) = ((A' → XIT_F.U.P) → XIT_F.U.P)) (Q : A' → XIT_F.U.P) :
    cast h (fun R => XIT_F.ex c R) Q = XIT_F.ex c (fun x => Q (cast hA x)) := by
  subst hA; rfl

/-- The value of an existential quantification. -/
theorem XIT_eval_ex {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : XIT_F.U.TEnv n)
    (env : XIT_F.U.Env Γ ρ) :
    XIT_F.eval (Tm.ex σ φ) ρ env =
      XIT_F.ex (XIT_F.U.code σ.1 ρ) (fun x => XIT_F.eval φ ρ (env, cast (Univ.El_code ρ σ.2) x)) :=
  XIT_cast_ex_eq (Univ.El_code ρ σ.2) _ _

/-! ## Identity of types -/

theorem XIT_not_Inj : ¬ XIT_F.Valid Inj := fun h => by
  have h0 := (XIT_F.holds_tall _ _ _).mp ((XIT_F.holds_tall _ _ _).mp ((XIT_F.holds_tall _ _ _).mp
    ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e) .t) (.base ())
  have h1 := (XIT_F.holds_imp _ _ _ _).mp h0 ((XIT_F.holds_teq _ _ _ _).mpr rfl)
  have h2 : (Code.t : XIT_C) = .base () := (XIT_F.holds_teq _ _ _ _).mp ((XIT_F.holds_conj _ _ _ _).mp h1).2
  cases h2

theorem XIT_not_Recovery : ¬ XIT_F.Valid Recovery := fun h => by
  have h0 := (XIT_F.holds_tall _ _ _).mp ((XIT_F.holds_tall _ _ _).mp ((XIT_F.holds_tall _ _ _).mp
    ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e) .t) (.base ())
  have h1 := (XIT_F.holds_imp _ _ _ _).mp h0 ((XIT_F.holds_conj _ _ _ _).mpr
    ⟨(XIT_F.holds_teq _ _ _ _).mpr rfl, (XIT_F.holds_teq _ _ _ _).mpr rfl⟩)
  have h2 : (Code.t : XIT_C) = .base () := (XIT_F.holds_teq _ _ _ _).mp h1
  cases h2

/-! ## Necessity of identity and distinctness -/

theorem XIT_not_NIEqv : ¬ XIT_F.Valid NIEqv := fun h => by
  have h0 := (XIT_F.holds_all _ _ _ _).mp ((XIT_F.holds_all _ _ _ _).mp
    ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have hb := (XIT_holds_box _ _ _).mp ((XIT_F.holds_imp _ _ _ _).mp h0
    ((XIT_F.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩))
  exact Bool.noConfusion (congrArg Prod.snd hb : false = true)

theorem XIT_not_NIX : ¬ XIT_F.Valid NIX := fun h => by
  have h0 := (XIT_F.holds_all _ _ _ _).mp ((XIT_F.holds_all _ _ _ _).mp ((XIT_F.holds_tall _ _ _).mp
    ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e) ()) ()
  have hb := (XIT_holds_box _ _ _).mp ((XIT_F.holds_imp _ _ _ _).mp h0
    ((XIT_F.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩))
  exact Bool.noConfusion (congrArg Prod.snd hb : false = true)

theorem XIT_not_NITeq : ¬ XIT_F.Valid NITeq := fun h => by
  have h0 := (XIT_F.holds_tall _ _ _).mp ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e
  have hb := (XIT_holds_box _ _ _).mp ((XIT_F.holds_imp _ _ _ _).mp h0 ((XIT_F.holds_teq _ _ _ _).mpr rfl))
  exact Bool.noConfusion (congrArg Prod.snd hb : false = true)

theorem XIT_not_NDTeq : ¬ XIT_F.Valid NDTeq := fun h => by
  have h0 := (XIT_F.holds_tall _ _ _).mp ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .t
  have hn : XIT_F.Holds (Tm.neg (Tm.teq tv1 tv0) : Fm Ctx.nil.text.text)
      (scons .t (scons .e fun i => i.elim0)) () :=
    (XIT_F.holds_neg _ _ _).mpr fun ht => by
      have h2 : (Code.e : XIT_C) = .t := (XIT_F.holds_teq _ _ _ _).mp ht
      cases h2
  have hb := (XIT_holds_box _ _ _).mp ((XIT_F.holds_imp _ _ _ _).mp h0 hn)
  exact (cast (congrFun (congrArg Prod.fst hb) false).symm trivial : ¬ True) trivial

theorem XIT_not_NDX : ¬ XIT_F.Valid NDX := fun h => by
  have h0 := (XIT_F.holds_all _ _ _ _).mp ((XIT_F.holds_all _ _ _ _).mp ((XIT_F.holds_tall _ _ _).mp
    ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) .t) XIT_top) ((fun _ => True), false)
  have hb := (XIT_holds_box _ _ _).mp ((XIT_F.holds_imp _ _ _ _).mp h0 ((XIT_F.holds_neg _ _ _).mpr
    fun he => Bool.noConfusion
      (congrArg Prod.snd (eq_of_heq ((XIT_F.holds_eqv _ _ _ _ _ _).mp he).2) : true = false)))
  exact (cast (congrFun (congrArg Prod.fst hb) false).symm trivial : ¬ True) trivial

/-! ## Booleanism, the Identity Identity, Classicism -/

theorem XIT_not_DNeg : ¬ XIT_F.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (XIT_F.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) ((fun _ => True), false)
  have e := eq_of_heq ((XIT_F.holds_eqv_t _ _ _ _).mp h0).2
  exact Bool.noConfusion (congrArg Prod.snd e : true = false)

theorem XIT_not_Bool : ¬ ∀ φ, BoolSch φ → XIT_F.Valid φ := fun h => XIT_not_DNeg (h _ DNeg_bool)

theorem XIT_not_IdId : ¬ XIT_F.Valid IdId := fun h => by
  have h0 := (XIT_F.holds_all _ _ _ _).mp ((XIT_F.holds_all _ _ _ _).mp
    ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have e := eq_of_heq ((XIT_F.holds_eqv_t _ _ _ _).mp h0).2
  have e2 := congrArg Prod.snd ((XIT_F.eval_eqv _ _ _ _ _ _).symm.trans (e.trans (XIT_F.eval_all _ _ _ _)))
  exact Bool.noConfusion (e2 : false = true)

theorem XIT_not_Class : ¬ ∀ χ, ClassSch χ → XIT_F.Valid χ := fun h =>
  XIT_not_Bool fun φ hφ => XIT_F.soundness XIT_model h (d_Bool_of_Class (S := ClassSch) (fun _ hc => hc) φ hφ)

/-! ## Barcan formulas and necessitism -/

theorem XIT_not_TBF : ¬ ∀ χ, TBFSch χ → XIT_F.Valid χ := fun h => by
  have h0 := h _ ⟨topF, rfl⟩ (fun i => i.elim0) ()
  have hb := (XIT_F.holds_imp _ _ _ _).mp h0 ((XIT_F.holds_tall _ _ _).mpr fun _ =>
    (XIT_holds_box _ _ _).mpr (XIT_top_eq _ _))
  have e := (XIT_holds_box _ _ _).mp hb
  have e2 : (∀ a : Code Unit, (XIT_F.eval (topF : Fm Ctx.nil.text) (scons a fun i => i.elim0) ()).1 true) ∧
      ¬ ∀ a : Code Unit, XIT_F.eval (topF : Fm Ctx.nil.text) (scons a fun i => i.elim0) () = XIT_top :=
    cast (congrFun (congrArg Prod.fst e) false).symm trivial
  exact e2.2 fun _ => XIT_top_eq _ _

theorem XIT_not_TCBF : ¬ ∀ χ, TCBFSch χ → XIT_F.Valid χ := fun h => by
  have h0 := h _ ⟨Tm.tex (Tm.teq tv1 tv0), rfl⟩ (fun i => i.elim0) ()
  have hp : XIT_F.Holds (boxF (Tm.tall (Tm.tex (Tm.teq tv1 tv0))) : Fm Ctx.nil) (fun i => i.elim0) () := by
    refine (XIT_holds_box _ _ _).mpr (Prod.ext (funext fun w => ?_) rfl)
    cases w
    · refine propext ⟨fun _ => trivial, fun _ => ⟨fun a => ⟨a, rfl⟩, fun hall => ?_⟩⟩
      exact (cast (congrFun (congrArg Prod.fst (hall .e)) false).symm trivial : False)
    · exact propext ⟨fun _ => trivial, fun _ a => ⟨a, rfl⟩⟩
  have hb := (XIT_F.holds_tall _ _ _).mp ((XIT_F.holds_imp _ _ _ _).mp h0 hp) .e
  have e := (XIT_holds_box _ _ _).mp hb
  exact (cast (congrFun (congrArg Prod.fst e) false).symm trivial : False)

theorem XIT_not_TNec : ¬ XIT_F.Valid TNec := fun h => by
  have hb := (XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e
  have e := (XIT_holds_box _ _ _).mp hb
  exact (cast (congrFun (congrArg Prod.fst e) false).symm trivial : False)

theorem XIT_not_BF : ¬ XIT_F.Valid BF := fun h => by
  have h0 := (XIT_F.holds_all _ _ _ _).mp ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ => XIT_top)
  have h1 := (XIT_F.holds_imp _ _ _ _).mp h0 ((XIT_F.holds_all _ _ _ _).mpr fun _ =>
    (XIT_holds_box _ _ _).mpr rfl)
  have e := (XIT_F.eval_all _ _ _ _).symm.trans ((XIT_holds_box _ _ _).mp h1)
  have e2 : (∀ _ : Unit, True) ∧ ¬ ∀ _ : Unit, XIT_top = XIT_top :=
    cast (congrFun (congrArg Prod.fst e) false).symm trivial
  exact e2.2 fun _ => rfl

theorem XIT_not_CBF : ¬ XIT_F.Valid CBF := fun h => by
  have h0 := (XIT_F.holds_all _ _ _ _).mp ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ => ((fun _ => True), false))
  have hb : XIT_F.Holds (boxF (all tv0 (Tm.app (.var (.there .here)) (.var .here))) :
      Fm ((Ctx.nil.text).ext tv0.pred)) (scons .e fun i => i.elim0) ((), fun _ => ((fun _ => True), false)) := by
    refine (XIT_holds_box _ _ _).mpr ((XIT_F.eval_all _ _ _ _).trans ?_)
    refine Prod.ext (funext fun w => ?_) rfl
    cases w
    · exact propext ⟨fun _ => trivial, fun _ => ⟨fun _ => trivial, fun hall =>
        Bool.noConfusion (congrArg Prod.snd (hall ()) : false = true)⟩⟩
    · exact propext ⟨fun _ => trivial, fun _ _ => trivial⟩
  have h1 := (XIT_F.holds_imp _ _ _ _).mp h0 hb
  have e := (XIT_holds_box _ _ _).mp ((XIT_F.holds_all _ _ _ _).mp h1 ())
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

theorem XIT_not_Nec : ¬ XIT_F.Valid Nec := fun h => by
  have h0 := (XIT_F.holds_all _ _ _ _).mp ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  have e := (XIT_eval_ex _ _ _ _).symm.trans ((XIT_holds_box _ _ _).mp h0)
  exact (cast (congrFun (congrArg Prod.fst e) false).symm trivial : False)

/-! ## T and Collapse -/

theorem XIT_TAx : XIT_F.Valid TAx := by
  intro ρ env
  refine (XIT_F.holds_all _ _ _ _).mpr fun p => (XIT_F.holds_imp _ _ _ _).mpr fun hp => ?_
  have e : p = XIT_top := (XIT_holds_box _ _ _).mp hp
  show p.1 true
  rw [e]
  trivial

theorem XIT_not_Collapse : ¬ XIT_F.Valid Collapse := fun h => by
  have h0 := (XIT_F.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) ((fun w => w = true), true)
  have e := (XIT_holds_box _ _ _).mp ((XIT_F.holds_imp _ _ _ _).mp h0 rfl)
  exact Bool.noConfusion (cast (congrFun (congrArg Prod.fst e) false).symm trivial : false = true)

theorem XIT_not_PropExt : ¬ XIT_F.Valid PropExt := fun h => by
  have h0 := (XIT_F.holds_all _ _ _ _).mp ((XIT_F.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) XIT_top)
    ((fun _ => True), false)
  have h1 := (XIT_F.holds_imp _ _ _ _).mp h0
    ((XIT_F.holds_iff _ _ _ _).mpr ⟨fun _ => trivial, fun _ => trivial⟩)
  exact Bool.noConfusion
    (congrArg Prod.snd (eq_of_heq ((XIT_F.holds_eqv_t _ _ _ _).mp h1).2) : true = false)

/-! ## Identity across types -/

theorem XIT_not_Disjoint : ¬ XIT_F.Valid Disjoint := fun h => by
  have h0 := (XIT_F.holds_tall _ _ _).mp ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) (.base ())
  have h1 := (XIT_F.holds_imp _ _ _ _).mp h0 ((XIT_F.holds_neg _ _ _).mpr fun ht => by
    have h2 : (Code.t : XIT_C) = .base () := (XIT_F.holds_teq _ _ _ _).mp ht
    cases h2)
  exact (XIT_F.holds_neg _ _ _).mp ((XIT_F.holds_all _ _ _ _).mp ((XIT_F.holds_all _ _ _ _).mp h1 XIT_top)
    XIT_top) ((XIT_F.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩)

theorem XIT_Slogan : XIT_F.Valid Slogan := by
  intro ρ env
  refine (XIT_F.holds_all _ _ _ _).mpr fun _ => (XIT_F.holds_tall _ _ _).mpr fun b => ?_
  refine (XIT_F.holds_all _ _ _ _).mpr fun _ => (XIT_F.holds_neg _ _ _).mpr fun he => ?_
  have h2 : (Code.e : XIT_C) = .arr (XIT_K b) .t := ((XIT_F.holds_eqv _ _ _ _ _ _).mp he).1
  cases h2

theorem XIT_not_Twin : ¬ XIT_F.Valid Twin := fun h => by
  have h0 := (XIT_F.holds_all _ _ _ _).mp ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  obtain ⟨b, hb⟩ := (XIT_F.holds_tex _ _ _).mp h0
  have hb' := (XIT_F.holds_conj _ _ _ _).mp hb
  obtain ⟨y, hy⟩ := (XIT_F.holds_ex _ _ _ _).mp hb'.2
  have hk : (Code.e : XIT_C) = XIT_K b := ((XIT_F.holds_eqv _ _ _ _ _ _).mp hy).1
  have hbe := XIT_K_e b hk.symm
  subst hbe
  exact (XIT_F.holds_neg _ _ _).mp hb'.1 ((XIT_F.holds_teq _ _ _ _).mpr rfl)

theorem XIT_not_Hae : ¬ XIT_F.Valid Hae := fun h => by
  have h0 := (XIT_F.holds_all _ _ _ _).mp ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  have h2 : (Code.e : XIT_C) = .arr .e .t := ((XIT_F.holds_eqv _ _ _ _ _ _).mp h0).1
  cases h2

/-- The polymorphic predicate `λγ:∗.λz:γ.(γ ≈ t)`. -/
def XIT_PredT : Tm Ctx.nil (.pi (.arr (.var fz) .t)) := .tlam (.lam tv0 (teq tv0 tyT))

/-- LL≡-Poly fails: `⊤`, as an item of `t`, is identified with `⊤` as an item of `D`. -/
theorem XIT_not_LLPoly : ¬ XIT_F.Valid (LLPoly XIT_PredT) := fun h => by
  have h1 := (XIT_F.holds_all _ _ _ _).mp ((XIT_F.holds_all _ _ _ _).mp ((XIT_F.holds_tall _ _ _).mp
    ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) (.base ())) XIT_top) XIT_top
  have h2 := (XIT_F.holds_imp _ _ _ _).mp ((XIT_F.holds_imp _ _ _ _).mp h1
    ((XIT_F.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩)) rfl
  have h3 : (Code.base () : XIT_C) = .t := h2
  cases h3

/-- LL≡/≈ holds, for every polymorphic predicate (with parameters). -/
theorem XIT_Bridge {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : XIT_F.Valid (Bridge P) :=
  XIT_bridge_valid XIT_I (fun _ _ _ _ he ht => ⟨fun x y => HEq x y, ⟨ht, fun _ _ => Iff.rfl⟩, he.2⟩) P

/-! ## Congruence and extensionality -/

theorem XIT_Cong : XIT_F.Valid Cong := by
  intro ρ env
  refine (XIT_F.holds_tall _ _ _).mpr fun a => (XIT_F.holds_tall _ _ _).mpr fun b => ?_
  refine (XIT_F.holds_tall _ _ _).mpr fun c => (XIT_F.holds_tall _ _ _).mpr fun d => ?_
  refine (XIT_F.holds_all _ _ _ _).mpr fun f => (XIT_F.holds_all _ _ _ _).mpr fun g => ?_
  refine (XIT_F.holds_all _ _ _ _).mpr fun x => (XIT_F.holds_all _ _ _ _).mpr fun y => ?_
  refine (XIT_F.holds_imp _ _ _ _).mpr fun hc => ?_
  obtain ⟨hfg, hxy⟩ := (XIT_F.holds_conj _ _ _ _).mp hc
  have h1 : XIT_K (.arr a c) = XIT_K (.arr b d) ∧ HEq f g := (XIT_F.holds_eqv _ _ _ _ _ _).mp hfg
  have h2 : XIT_K a = XIT_K b ∧ HEq x y := (XIT_F.holds_eqv _ _ _ _ _ _).mp hxy
  have hcd : XIT_K c = XIT_K d := (Code.arr.inj h1.1).2
  exact (XIT_F.holds_eqv _ _ _ _ _ _).mpr ⟨hcd, heq_app (XIT_El_of_K h2.1) (XIT_El_of_K hcd) h1.2 h2.2⟩

theorem XIT_PCong : XIT_F.Valid PCong := by
  intro ρ env
  refine (XIT_F.holds_tall _ _ _).mpr fun a => (XIT_F.holds_tall _ _ _).mpr fun c =>
    (XIT_F.holds_tall _ _ _).mpr fun d => ?_
  refine (XIT_F.holds_all _ _ _ _).mpr fun f => (XIT_F.holds_all _ _ _ _).mpr fun g =>
    (XIT_F.holds_all _ _ _ _).mpr fun x => ?_
  refine (XIT_F.holds_imp _ _ _ _).mpr fun h => ?_
  have h1 : XIT_K (.arr a c) = XIT_K (.arr a d) ∧ HEq f g := (XIT_F.holds_eqv _ _ _ _ _ _).mp h
  have hcd : XIT_K c = XIT_K d := (Code.arr.inj h1.1).2
  exact (XIT_F.holds_eqv _ _ _ _ _ _).mpr ⟨hcd, heq_app rfl (XIT_El_of_K hcd) h1.2 HEq.rfl⟩

theorem XIT_heq_fun {A C D : Type} (e : C = D) (f : A → C) (g : A → D) (h : ∀ x, HEq (f x) (g x)) :
    HEq f g := by
  subst e
  exact heq_of_eq (funext fun x => eq_of_heq (h x))

theorem XIT_PExt : XIT_F.Valid PExt := by
  intro ρ env
  refine (XIT_F.holds_tall _ _ _).mpr fun a => (XIT_F.holds_tall _ _ _).mpr fun c =>
    (XIT_F.holds_tall _ _ _).mpr fun d => ?_
  refine (XIT_F.holds_all _ _ _ _).mpr fun f => (XIT_F.holds_all _ _ _ _).mpr fun g => ?_
  refine (XIT_F.holds_imp _ _ _ _).mpr fun h => ?_
  have hx : ∀ x, XIT_K c = XIT_K d ∧ HEq (f x) (g x) := fun x =>
    (XIT_F.holds_eqv _ _ _ _ _ _).mp ((XIT_F.holds_all _ _ _ _).mp h x)
  have x0 := Classical.choice (Univ.El_nonempty (U := XIT_F.U) a)
  have hcd : XIT_K c = XIT_K d := (hx x0).1
  refine (XIT_F.holds_eqv _ _ _ _ _ _).mpr ⟨?_, XIT_heq_fun (XIT_El_of_K hcd) f g fun x => (hx x).2⟩
  show Code.arr (XIT_K a) (XIT_K c) = Code.arr (XIT_K a) (XIT_K d)
  rw [hcd]

/-! ## Extensionality and intensionality of types -/

theorem XIT_not_ExtT : ¬ XIT_F.Valid ExtT := fun h => by
  have h0 := (XIT_F.holds_tall _ _ _).mp ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) (.base ())
  have hc := (XIT_F.holds_imp _ _ _ _).mp h0 ((XIT_F.holds_conj _ _ _ _).mpr
    ⟨(XIT_F.holds_all _ _ _ _).mpr fun x => (XIT_F.holds_ex _ _ _ _).mpr ⟨x, (XIT_F.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩⟩,
     (XIT_F.holds_all _ _ _ _).mpr fun x => (XIT_F.holds_ex _ _ _ _).mpr ⟨x, (XIT_F.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩⟩⟩)
  have h2 : (Code.t : XIT_C) = .base () := (XIT_F.holds_teq _ _ _ _).mp hc
  cases h2

theorem XIT_not_IntT : ¬ XIT_F.Valid IntT := fun h => by
  have h0 := (XIT_F.holds_tall _ _ _).mp ((XIT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) (.base ())
  have hs : XIT_F.Holds (boxF subT : Fm Ctx.nil.text.text) (scons (.base ()) (scons .t fun i => i.elim0)) () := by
    refine (XIT_holds_box _ _ _).mpr ?_
    unfold subT
    refine (XIT_F.eval_all _ _ _ _).trans ?_
    refine Prod.ext (funext fun w => ?_) rfl
    cases w
    · refine propext ⟨fun _ => trivial, fun _ => ⟨fun x => ?_, fun hall => ?_⟩⟩
      · exact ⟨x, rfl, HEq.rfl⟩
      · exact (cast (congrFun (congrArg Prod.fst (hall XIT_top)) false).symm trivial : False)
    · exact propext ⟨fun _ => trivial, fun _ x => ⟨x, rfl, HEq.rfl⟩⟩
  have hs' : XIT_F.Holds (boxF supT : Fm Ctx.nil.text.text) (scons (.base ()) (scons .t fun i => i.elim0)) () := by
    refine (XIT_holds_box _ _ _).mpr ?_
    unfold supT
    refine (XIT_F.eval_all _ _ _ _).trans ?_
    refine Prod.ext (funext fun w => ?_) rfl
    cases w
    · refine propext ⟨fun _ => trivial, fun _ => ⟨fun x => ?_, fun hall => ?_⟩⟩
      · exact ⟨x, rfl, HEq.rfl⟩
      · exact (cast (congrFun (congrArg Prod.fst (hall XIT_top)) false).symm trivial : False)
    · exact propext ⟨fun _ => trivial, fun _ x => ⟨x, rfl, HEq.rfl⟩⟩
  have hc := (XIT_F.holds_imp _ _ _ _).mp h0 ((XIT_F.holds_conj _ _ _ _).mpr ⟨hs, hs'⟩)
  have h2 : (Code.t : XIT_C) = .base () := (XIT_F.holds_teq _ _ _ _).mp hc
  cases h2

/-! ## Consequences of PI -/

theorem XIT_Truth : XIT_F.Valid Truth := XIT_of_prov (Derive.d_Truth rfl)
theorem XIT_TopBot : XIT_F.Valid TopBot := XIT_of_prov (Derive.d_TopBot rfl)
theorem XIT_Cantor : XIT_F.Valid Cantor := XIT_of_prov (Derive.d_Cantor rfl)
theorem XIT_WCong : XIT_F.Valid WCong := XIT_of_prov (Derive.d_WCong rfl)
theorem XIT_Choice : XIT_F.Valid Choice := XIT_F.Choice_valid

end Al
end PIF
