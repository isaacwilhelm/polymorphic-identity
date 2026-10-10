import PIBF
set_option autoImplicit false

/-!
# `𝔐_⊤⊥,w`: a model of PI⁻ with two worlds in which `⊤ ≡ ⊥`, every identity is contingent, and
Inj≈ fails

The semantics with worlds (`lean/PIWorlds.lean`): two worlds, the actual world `true` and another
world `false`; propositions are sets of worlds. There is one entity, and one base type `d`, whose
items are sets of worlds, like those of `t`.

* The `≈`-key of a type replaces `e → d` (anywhere inside it) by `e → t`. At the actual world two
  types are `≈` just in case they have the same key; at the other world, just in case they do not.
  So `e → t ≈ e → d` while `t` and `d` are distinct: Inj≈ and Recovery fail.
* At the actual world, items are identified just in case their types have the same key and they
  are the same value; in addition the propositions `⊤` and `⊥` are identified. At the other world,
  items are identified just in case they are not identified at the actual world.
* So every identity and every distinctness, of items or of types, is contingent; and `□φ` (that is,
  `φ ≡ ⊤`) holds just in case `φ` is `⊤` or `⊥`.

LL≈ holds by an invariance lemma for this semantics, proved below for the relations "same key, and
the same value". `⊤ ≡ ⊥` refutes ⊤≢⊥, Truth and T; the function `λp. p ∧ (actual)` refutes WCong;
the constant function `λx.⊤`, of types `e → t` and `e → d`, refutes PCong→; and the predicate
"some property identical to `λp.p` holds of `z`" refutes LL≡/≈.
-/

namespace PIF
namespace Wd
open Tm

/-! ## Invariance for the semantics with worlds -/

/-- A family of admissible relations for a frame with worlds, which `≈` and `≡` respect. -/
structure XTB_Inv (F : Frame) where
  Adm : (a a' : Code F.U.Base) → (F.U.El a → F.U.El a' → Prop) → Prop
  refl : ∀ a, Adm a a (fun x y => x = y)
  arrow : ∀ {a a' c c' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop} {S : F.U.El c → F.U.El c' → Prop},
    Adm a a' R → Adm c c' S → Adm (.arr a c) (.arr a' c') (fun f f' => ∀ u u', R u u' → S (f u) (f' u'))
  total : ∀ {a a' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop}, Adm a a' R → ∀ u, ∃ u', R u u'
  onto : ∀ {a a' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop}, Adm a a' R → ∀ u', ∃ u, R u u'
  teq : ∀ {a a' b b' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop} {S : F.U.El b → F.U.El b' → Prop},
    Adm a a' R → Adm b b' S → F.teq a b = F.teq a' b'
  eqv : ∀ {a a' b b' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop} {S : F.U.El b → F.U.El b' → Prop},
    Adm a a' R → Adm b b' S → ∀ u u' v v', R u u' → S v v' → F.eqv a b u v = F.eqv a' b' u' v'

section XTB_Invariance
variable {F : Frame}

/-- Relations for the type variables, extended by `R` for the new variable `fz`. -/
def XTB_RScons {n : Nat} {ρ ρ' : F.U.TEnv n} {a a' : Code F.U.Base} (R : F.U.El a → F.U.El a' → Prop)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) :
    ∀ i : Fin (n+1), F.U.El (scons a ρ i) → F.U.El (scons a' ρ' i) → Prop
  | ⟨0, _⟩ => R
  | ⟨k+1, h⟩ => Rs ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- The logical relation: equality at `e` and at `t`, the given relations at type variables,
preservation at `→`, and preservation under every admissible relation at `Π`. -/
def XTB_Rel (I : XTB_Inv F) : {n : Nat} → (K : Cat n) → (ρ ρ' : F.U.TEnv n) →
    (∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) → F.U.CatVal K ρ → F.U.CatVal K ρ' → Prop
  | _, .e, _, _, _ => fun x y => x = y
  | _, .t, _, _, _ => fun p q => p = q
  | _, .var i, _, _, Rs => Rs i
  | _, .arr K L, ρ, ρ', Rs => fun f f' => ∀ u u', XTB_Rel I K ρ ρ' Rs u u' → XTB_Rel I L ρ ρ' Rs (f u) (f' u')
  | _, .pi K, ρ, ρ', Rs => fun G G' => ∀ a a' (R : F.U.El a → F.U.El a' → Prop), I.Adm a a' R →
      XTB_Rel I K (scons a ρ) (scons a' ρ') (XTB_RScons R Rs) (G a) (G' a')

end XTB_Invariance

/-- The same relation at a type, on the sets its code names. -/
def XTB_RelE (F : Frame) {n : Nat} : (K : Cat n) → (ρ ρ' : F.U.TEnv n) →
    (∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) → F.U.El (F.U.code K ρ) → F.U.El (F.U.code K ρ') → Prop
  | .e, _, _, _ => fun x y => x = y
  | .t, _, _, _ => fun p q => p = q
  | .var i, _, _, Rs => Rs i
  | .arr K L, ρ, ρ', Rs => fun f f' => ∀ x x', XTB_RelE F K ρ ρ' Rs x x' → XTB_RelE F L ρ ρ' Rs (f x) (f' x')
  | .pi _, _, _, _ => fun x y => x = y

section XTB_Invariance2
variable {F : Frame}

theorem XTB_adm_RelE (I : XTB_Inv F) {n : Nat} (K : Cat n) : ∀ (ρ ρ' : F.U.TEnv n)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop),
    (∀ i, I.Adm (ρ i) (ρ' i) (Rs i)) → K.Simple →
    I.Adm (F.U.code K ρ) (F.U.code K ρ') (XTB_RelE F K ρ ρ' Rs) := by
  induction K with
  | e => intros; exact I.refl _
  | t => intros; exact I.refl _
  | var i => intro ρ ρ' Rs hRs _; exact hRs i
  | arr a b iha ihb => intro ρ ρ' Rs hRs hK; exact I.arrow (iha ρ ρ' Rs hRs hK.1) (ihb ρ ρ' Rs hRs hK.2)
  | pi _ _ => intro _ _ _ _ hK; exact hK.elim

theorem XTB_Rel_RelE (I : XTB_Inv F) {n : Nat} (K : Cat n) : ∀ (_ : K.Simple) (ρ ρ' : F.U.TEnv n)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) (u : F.U.CatVal K ρ) (u' : F.U.CatVal K ρ')
    (x : F.U.El (F.U.code K ρ)) (x' : F.U.El (F.U.code K ρ')), HEq u x → HEq u' x' →
    (XTB_Rel I K ρ ρ' Rs u u' ↔ XTB_RelE F K ρ ρ' Rs x x') := by
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

theorem XTB_Rel_ren (I : XTB_Inv F) {n : Nat} (K : Cat n) : ∀ {m : Nat} (r : Fin n → Fin m) (ρ ρ' : F.U.TEnv m)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) (ρ₂ ρ₂' : F.U.TEnv n)
    (Rs₂ : ∀ i, F.U.El (ρ₂ i) → F.U.El (ρ₂' i) → Prop)
    (_ : ∀ i, ρ (r i) = ρ₂ i) (_ : ∀ i, ρ' (r i) = ρ₂' i)
    (_ : ∀ i x x' y y', HEq x y → HEq x' y' → (Rs (r i) x x' ↔ Rs₂ i y y'))
    (v : F.U.CatVal (K.ren r) ρ) (v' : F.U.CatVal (K.ren r) ρ') (w : F.U.CatVal K ρ₂) (w' : F.U.CatVal K ρ₂'),
    HEq v w → HEq v' w' → (XTB_Rel I (K.ren r) ρ ρ' Rs v v' ↔ XTB_Rel I K ρ₂ ρ₂' Rs₂ w w') := by
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
    refine ih (liftR r) (scons a ρ) (scons a' ρ') (XTB_RScons R Rs) (scons a ρ₂) (scons a' ρ₂') (XTB_RScons R Rs₂)
      (fin_cases rfl (fun i => hρ i)) (fin_cases rfl (fun i => hρ' i)) ?_ _ _ _ _ ?_ ?_
    · refine fin_cases ?_ (fun i => fun x x' y y' hx hx' => hR i x x' y y' hx hx')
      intro x x' y y' hx hx'; cases hx; cases hx'; exact Iff.rfl
    · exact heq_dapp (fun a => Univ.CatVal_ren K (liftR r) (scons a ρ) (scons a ρ₂)
        (fin_cases rfl (fun i => hρ i))) hv rfl
    · exact heq_dapp (fun a => Univ.CatVal_ren K (liftR r) (scons a ρ') (scons a ρ₂')
        (fin_cases rfl (fun i => hρ' i))) hv' rfl

theorem XTB_Rel_sub (I : XTB_Inv F) {n : Nat} (K : Cat n) : ∀ {m : Nat} (s : Fin n → Ty m) (ρ ρ' : F.U.TEnv m)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) (ρ₂ ρ₂' : F.U.TEnv n)
    (Rs₂ : ∀ i, F.U.El (ρ₂ i) → F.U.El (ρ₂' i) → Prop)
    (_ : ∀ i, F.U.code (s i).1 ρ = ρ₂ i) (_ : ∀ i, F.U.code (s i).1 ρ' = ρ₂' i)
    (_ : ∀ i (x : F.U.CatVal (s i).1 ρ) (x' : F.U.CatVal (s i).1 ρ') y y', HEq x y → HEq x' y' →
      (XTB_Rel I (s i).1 ρ ρ' Rs x x' ↔ Rs₂ i y y'))
    (v : F.U.CatVal (K.sub s) ρ) (v' : F.U.CatVal (K.sub s) ρ') (w : F.U.CatVal K ρ₂) (w' : F.U.CatVal K ρ₂'),
    HEq v w → HEq v' w' → (XTB_Rel I (K.sub s) ρ ρ' Rs v v' ↔ XTB_Rel I K ρ₂ ρ₂' Rs₂ w w') := by
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
    refine ih (liftT s) (scons a ρ) (scons a' ρ') (XTB_RScons R Rs) (scons a ρ₂) (scons a' ρ₂') (XTB_RScons R Rs₂)
      (hl a ρ ρ₂ hρ) (hl a' ρ' ρ₂' hρ') ?_ _ _ _ _ ?_ ?_
    · refine fin_cases ?_ (fun i => ?_)
      · intro x x' y y' hx hx'; cases hx; cases hx'; exact Iff.rfl
      · intro x x' y y' hx hx'
        refine (XTB_Rel_ren I (s i).1 fs (scons a ρ) (scons a' ρ') (XTB_RScons R Rs) ρ ρ' Rs (fun _ => rfl)
          (fun _ => rfl) (fun j z z' q q' hz hz' => by cases hz; cases hz'; exact Iff.rfl)
          x x' (cast (Univ.CatVal_ren (s i).1 fs (scons a ρ) ρ (fun _ => rfl)) x)
          (cast (Univ.CatVal_ren (s i).1 fs (scons a' ρ') ρ' (fun _ => rfl)) x')
          (cast_heq _ _).symm (cast_heq _ _).symm).trans ?_
        exact hR i _ _ y y' ((cast_heq _ _).trans hx) ((cast_heq _ _).trans hx')
    · exact heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ) (scons a ρ₂) (hl a ρ ρ₂ hρ)) hv rfl
    · exact heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ') (scons a ρ₂') (hl a ρ' ρ₂' hρ')) hv' rfl

/-- Related values for the term variables of a context. -/
def XTB_EnvRel (I : XTB_Inv F) : {n : Nat} → (Γ : Ctx n) → (ρ ρ' : F.U.TEnv n) →
    (∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) → F.U.Env Γ ρ → F.U.Env Γ ρ' → Prop
  | _, .nil, _, _, _ => fun _ _ => True
  | _, .ext Γ σ, ρ, ρ', Rs => fun env env' => XTB_EnvRel I Γ ρ ρ' Rs env.1 env'.1 ∧ XTB_Rel I σ.1 ρ ρ' Rs env.2 env'.2
  | _, .text Γ, ρ, ρ', Rs => fun env env' =>
      XTB_EnvRel I Γ (fun i => ρ (fs i)) (fun i => ρ' (fs i)) (fun i => Rs (fs i)) env env'

theorem XTB_lookup_rel (I : XTB_Inv F) {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) : ∀ (ρ ρ' : F.U.TEnv n)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) (env : F.U.Env Γ ρ) (env' : F.U.Env Γ ρ'),
    XTB_EnvRel I Γ ρ ρ' Rs env env' → XTB_Rel I K ρ ρ' Rs (F.U.lookup x ρ env) (F.U.lookup x ρ' env') := by
  induction x with
  | here => intro ρ ρ' Rs env env' h; exact h.2
  | there y ih => intro ρ ρ' Rs env env' h; exact ih ρ ρ' Rs env.1 env'.1 h.1
  | tthere y ih =>
    intro ρ ρ' Rs env env' h
    refine (XTB_Rel_ren I _ fs ρ ρ' Rs (fun i => ρ (fs i)) (fun i => ρ' (fs i)) (fun i => Rs (fs i))
      (fun _ => rfl) (fun _ => rfl) (fun i x x' y y' hx hx' => by cases hx; cases hx'; exact Iff.rfl)
      _ _ _ _ (F.lookup_tthere y ρ env) (F.lookup_tthere y ρ' env')).mpr ?_
    exact ih _ _ _ env env' h

theorem XTB_const_rel (I : XTB_Inv F) {n : Nat} {K : Cat n} (c : Const n K) (ρ ρ' : F.U.TEnv n)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) :
    XTB_Rel I K ρ ρ' Rs (F.constVal c ρ) (F.constVal c ρ') := by
  cases c with
  | neg => intro p p' hp; subst hp; rfl
  | imp => intro p p' hp q q' hq; subst hp; subst hq; rfl
  | and => intro p p' hp q q' hq; subst hp; subst hq; rfl
  | or => intro p p' hp q q' hq; subst hp; subst hq; rfl
  | iff => intro p p' hp q q' hq; subst hp; subst hq; rfl
  | all =>
    intro a a' R hR P P' hP
    refine funext fun w => propext ⟨fun h x' => ?_, fun h x => ?_⟩
    · obtain ⟨x, hx⟩ := I.onto hR x'
      exact (congrFun (hP x x' hx) w).mp (h x)
    · obtain ⟨x', hx⟩ := I.total hR x
      exact (congrFun (hP x x' hx) w).mpr (h x')
  | ex =>
    intro a a' R hR P P' hP
    refine funext fun w => propext ⟨fun ⟨x, hx⟩ => ?_, fun ⟨x', hx⟩ => ?_⟩
    · obtain ⟨x', hxx⟩ := I.total hR x
      exact ⟨x', (congrFun (hP x x' hxx) w).mp hx⟩
    · obtain ⟨x, hxx⟩ := I.onto hR x'
      exact ⟨x, (congrFun (hP x x' hxx) w).mpr hx⟩
  | tall =>
    intro Q Q' hQ
    exact funext fun w => propext ⟨fun h a => (congrFun (hQ a a _ (I.refl a)) w).mp (h a),
      fun h a => (congrFun (hQ a a _ (I.refl a)) w).mpr (h a)⟩
  | tex =>
    intro Q Q' hQ
    exact funext fun w => propext ⟨fun ⟨a, h⟩ => ⟨a, (congrFun (hQ a a _ (I.refl a)) w).mp h⟩,
      fun ⟨a, h⟩ => ⟨a, (congrFun (hQ a a _ (I.refl a)) w).mpr h⟩⟩
  | eqv =>
    intro a a' R hR b b' S hS u u' hu v v' hv
    exact I.eqv hR hS u u' v v' hu hv
  | teq =>
    intro a a' R hR b b' S hS
    exact I.teq hR hS

/-- **The fundamental lemma**: every term is related to itself, under related values for its
variables. -/
theorem XTB_fundamental (I : XTB_Inv F) {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) : ∀ (ρ ρ' : F.U.TEnv n)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop), (∀ i, I.Adm (ρ i) (ρ' i) (Rs i)) →
    ∀ (env : F.U.Env Γ ρ) (env' : F.U.Env Γ ρ'), XTB_EnvRel I Γ ρ ρ' Rs env env' →
    XTB_Rel I K ρ ρ' Rs (F.eval M ρ env) (F.eval M ρ' env') := by
  induction M with
  | var x => intro ρ ρ' Rs _ env env' h; exact XTB_lookup_rel I x ρ ρ' Rs env env' h
  | const c => intro ρ ρ' Rs _ _ _ _; exact XTB_const_rel I c ρ ρ' Rs
  | app f a ihf iha =>
    intro ρ ρ' Rs hRs env env' h
    exact ihf ρ ρ' Rs hRs env env' h _ _ (iha ρ ρ' Rs hRs env env' h)
  | lam σ b ih =>
    intro ρ ρ' Rs hRs env env' h u u' hu
    exact ih ρ ρ' Rs hRs (env, u) (env', u') ⟨h, hu⟩
  | tlam b ih =>
    intro ρ ρ' Rs hRs env env' h a a' R hR
    exact ih (scons a ρ) (scons a' ρ') (XTB_RScons R Rs) (fin_cases hR (fun i => hRs i)) env env' h
  | tapp f σ ih =>
    intro ρ ρ' Rs hRs env env' h
    have hf := ih ρ ρ' Rs hRs env env' h (F.U.code σ.1 ρ) (F.U.code σ.1 ρ') (XTB_RelE F σ.1 ρ ρ' Rs)
      (XTB_adm_RelE I σ.1 ρ ρ' Rs hRs σ.2)
    refine (XTB_Rel_sub I _ (inst σ) ρ ρ' Rs (scons (F.U.code σ.1 ρ) ρ) (scons (F.U.code σ.1 ρ') ρ')
      (XTB_RScons (XTB_RelE F σ.1 ρ ρ' Rs) Rs) (fin_cases rfl (fun _ => rfl)) (fin_cases rfl (fun _ => rfl)) ?_
      _ _ _ _ (F.heq_eval_tapp f σ ρ env) (F.heq_eval_tapp f σ ρ' env')).mpr hf
    refine fin_cases ?_ (fun i => ?_)
    · intro x x' y y' hx hx'; exact XTB_Rel_RelE I σ.1 σ.2 ρ ρ' Rs x x' y y' hx hx'
    · intro x x' y y' hx hx'; cases hx; cases hx'; exact Iff.rfl

/-- With identity relations, the logical relation at a type is identity. -/
theorem XTB_Rel_eq (I : XTB_Inv F) {n : Nat} (K : Cat n) : ∀ (_ : K.Simple) (ρ : F.U.TEnv n)
    (u u' : F.U.CatVal K ρ), XTB_Rel I K ρ ρ (fun _ x y => x = y) u u' ↔ u = u' := by
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

theorem XTB_envRel_refl (I : XTB_Inv F) {n : Nat} (Γ : Ctx n) : ∀ (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ),
    XTB_EnvRel I Γ ρ ρ (fun _ x y => x = y) env env := by
  induction Γ with
  | nil => intros; trivial
  | ext Γ σ ih => intro ρ env; exact ⟨ih ρ env.1, (XTB_Rel_eq I σ.1 σ.2 ρ _ _).mpr rfl⟩
  | text Γ ih => intro ρ env; exact ih (fun i => ρ (fs i)) env

/-- A term of category `Πγ:∗.t` takes the same value at types related by an admissible relation. -/
theorem XTB_pi_t_invariant (I : XTB_Inv F) {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)) (ρ : F.U.TEnv n)
    (env : F.U.Env Γ ρ) {a b : Code F.U.Base} {R : F.U.El a → F.U.El b → Prop} (hR : I.Adm a b R) :
    F.eval Q ρ env a = F.eval Q ρ env b :=
  XTB_fundamental I Q ρ ρ _ (fun i => I.refl (ρ i)) env env (XTB_envRel_refl I Γ ρ env) a b R hR

/-- **LL≈ holds** when types identified by `≈` at the actual world are related by an admissible
relation. -/
theorem XTB_llTeq_valid (I : XTB_Inv F) (hteq : ∀ a b, F.teq a b F.U.w0 → ∃ R, I.Adm a b R) {n : Nat}
    {Γ : Ctx n} (Q : Tm Γ (.pi .t)) : F.Valid (LLTeq Q) := by
  intro ρ env a b hab hq
  obtain ⟨R, hR⟩ := hteq a b ((F.holds_teq (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env).mp hab)
  have hG : HEq (F.eval Q.twk.twk (scons b (scons a ρ)) env) (F.eval Q ρ env) :=
    (F.eval_twk Q.twk b (scons a ρ) env).trans (F.eval_twk Q a ρ env)
  have h1 : HEq (F.eval (Tm.tapp Q.twk.twk tv1) (scons b (scons a ρ)) env) (F.eval Q ρ env a) :=
    (F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv1 (scons b (scons a ρ)) env).trans
      (heq_dapp (P := fun _ => F.U.W → Prop) (Q := fun _ => F.U.W → Prop) (fun _ => rfl) hG rfl)
  have h0 : HEq (F.eval (Tm.tapp Q.twk.twk tv0) (scons b (scons a ρ)) env) (F.eval Q ρ env b) :=
    (F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv0 (scons b (scons a ρ)) env).trans
      (heq_dapp (P := fun _ => F.U.W → Prop) (Q := fun _ => F.U.W → Prop) (fun _ => rfl) hG rfl)
  have e := congrFun ((eq_of_heq h1).trans ((XTB_pi_t_invariant I Q ρ env hR).trans (eq_of_heq h0).symm)) F.U.w0
  exact cast e hq

end XTB_Invariance2

/-! ## The universe and the keys -/

/-- Two worlds, the actual world `true`; one entity; one base type `d`, whose items are sets of
worlds. -/
def XTB_U : Univ where
  W := Bool
  w0 := true
  E := Unit
  Base := Unit
  B := fun _ => Bool → Prop
  neE := ⟨()⟩
  neB := fun _ => ⟨fun _ => True⟩

/-- The base type `d`. -/
abbrev XTB_d : Code Unit := .base ()

/-- The key step: `e → d` goes to `e → t`. -/
def XTB_sp (x y : Code Unit) : Code Unit := if x = .e ∧ y = XTB_d then .arr .e .t else .arr x y

/-- The `≈`-key of a type. -/
def XTB_T : Code Unit → Code Unit
  | .e => .e
  | .t => .t
  | .base b => .base b
  | .arr a c => XTB_sp (XTB_T a) (XTB_T c)

theorem XTB_sp_arr (x y : Code Unit) : ∃ p q, XTB_sp x y = .arr p q := by
  unfold XTB_sp
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem XTB_sp_t (x : Code Unit) : XTB_sp x .t = .arr x .t := by
  unfold XTB_sp
  split
  · next h => exact absurd h.2 (by decide)
  · rfl

theorem XTB_T_arr (a c : Code Unit) : ∃ p q, XTB_T (.arr a c) = .arr p q := XTB_sp_arr _ _

theorem XTB_T_eq_t : ∀ a : Code Unit, XTB_T a = .t → a = .t
  | .e, h => absurd h (by decide)
  | .t, _ => rfl
  | .base _, h => by cases h
  | .arr a c, h => by
    obtain ⟨p, q, e⟩ := XTB_T_arr a c
    rw [e] at h
    cases h

theorem XTB_arr_ne : ∀ x : Code Unit, ∀ c, Code.arr x c ≠ x := by
  intro x
  induction x with
  | e => intro c h; cases h
  | t => intro c h; cases h
  | base _ => intro c h; cases h
  | arr y z ihy _ =>
    intro c h
    injection h with h1 _
    exact ihy z h1

/-- No type has the key of the type of its properties. -/
theorem XTB_T_pred_ne (a : Code Unit) : XTB_T (.arr a .t) ≠ XTB_T a := fun h => by
  have e : XTB_T (.arr a .t) = .arr (XTB_T a) .t := XTB_sp_t (XTB_T a)
  exact XTB_arr_ne (XTB_T a) .t (e.symm.trans h)

theorem XTB_El_sp (x y : Code Unit) : XTB_U.El (XTB_sp x y) = XTB_U.El (.arr x y) := by
  unfold XTB_sp
  split
  · next h => obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl
  · rfl

theorem XTB_El_T : ∀ a, XTB_U.El (XTB_T a) = XTB_U.El a
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => by
    show XTB_U.El (XTB_sp (XTB_T a) (XTB_T c)) = (XTB_U.El a → XTB_U.El c)
    rw [XTB_El_sp]
    show (XTB_U.El (XTB_T a) → XTB_U.El (XTB_T c)) = _
    rw [XTB_El_T a, XTB_El_T c]

theorem XTB_El_of_T {a b : Code Unit} (h : XTB_T a = XTB_T b) : XTB_U.El a = XTB_U.El b :=
  (XTB_El_T a).symm.trans ((congrArg XTB_U.El h).trans (XTB_El_T b))

/-! ## The frame -/

/-- `⊤` or `⊥`, as a proposition. -/
def XTB_tb (a : Code Unit) (x : XTB_U.El a) : Prop :=
  a = .t ∧ (HEq x (fun _ : Bool => True) ∨ HEq x (fun _ : Bool => False))

/-- Identity at the actual world: the same key, and the same value, or `⊤` and `⊥`. -/
def XTB_E (a b : Code Unit) (x : XTB_U.El a) (y : XTB_U.El b) : Prop :=
  XTB_T a = XTB_T b ∧ (HEq x y ∨ (XTB_tb a x ∧ XTB_tb b y))

/-- `P` at the actual world, and its negation at the other world. -/
def XTB_at (w : Bool) (P : Prop) : Prop := (w = true ↔ P)

theorem XTB_at_true {P : Prop} : XTB_at true P ↔ P := ⟨fun h => h.mp rfl, fun h => ⟨fun _ => h, fun _ => rfl⟩⟩

theorem XTB_at_false {P : Prop} : XTB_at false P ↔ ¬ P :=
  ⟨fun h hp => Bool.false_ne_true (h.mpr hp), fun h => ⟨fun e => absurd e Bool.false_ne_true, fun hp => absurd hp h⟩⟩

def XTB_F : Frame where
  U := XTB_U
  eqv := fun a b x y w => XTB_at w (XTB_E a b x y)
  teq := fun a b w => XTB_at w (XTB_T a = XTB_T b)

theorem XTB_tb_heq {a b : Code Unit} {x : XTB_U.El a} {y : XTB_U.El b} (hT : XTB_T a = XTB_T b) (h : HEq x y)
    (hy : XTB_tb b y) : XTB_tb a x := by
  obtain ⟨hb, hy2⟩ := hy
  subst hb
  exact ⟨XTB_T_eq_t a hT, hy2.imp (fun h' => h.trans h') (fun h' => h.trans h')⟩

theorem XTB_E_refl (a : Code Unit) (x : XTB_U.El a) : XTB_E a a x x := ⟨rfl, Or.inl HEq.rfl⟩

theorem XTB_E_symm {a b : Code Unit} {x : XTB_U.El a} {y : XTB_U.El b} (h : XTB_E a b x y) : XTB_E b a y x :=
  ⟨h.1.symm, h.2.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.2, h.1⟩)⟩

theorem XTB_E_trans {a b c : Code Unit} {x : XTB_U.El a} {y : XTB_U.El b} {z : XTB_U.El c}
    (h1 : XTB_E a b x y) (h2 : XTB_E b c y z) : XTB_E a c x z := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  rcases h1.2 with hxy | ⟨hx, hy⟩
  · rcases h2.2 with hyz | ⟨hy, hz⟩
    · exact Or.inl (hxy.trans hyz)
    · exact Or.inr ⟨XTB_tb_heq h1.1 hxy hy, hz⟩
  · rcases h2.2 with hyz | ⟨_, hz⟩
    · exact Or.inr ⟨hx, XTB_tb_heq h2.1.symm hyz.symm hy⟩
    · exact Or.inr ⟨hx, hz⟩

theorem XTB_E_iff {a a' b b' : Code Unit} (ha : XTB_T a = XTB_T a') (hb : XTB_T b = XTB_T b')
    {u : XTB_U.El a} {u' : XTB_U.El a'} {v : XTB_U.El b} {v' : XTB_U.El b'} (hu : HEq u u') (hv : HEq v v') :
    XTB_E a b u v ↔ XTB_E a' b' u' v' := by
  unfold XTB_E
  rw [ha, hb]
  refine and_congr Iff.rfl (or_congr ⟨fun h => hu.symm.trans (h.trans hv), fun h => hu.trans (h.trans hv.symm)⟩ ?_)
  exact and_congr ⟨XTB_tb_heq ha.symm hu.symm, XTB_tb_heq ha hu⟩ ⟨XTB_tb_heq hb.symm hv.symm, XTB_tb_heq hb hv⟩

/-! ## The model -/

/-- The admissible relations: between types with the same key, the same value. -/
def XTB_I : XTB_Inv XTB_F where
  Adm := fun a a' R => XTB_T a = XTB_T a' ∧ ∀ x x', R x x' ↔ HEq x x'
  refl := fun _ => ⟨rfl, fun _ _ => ⟨heq_of_eq, eq_of_heq⟩⟩
  arrow := by
    intro a a' c c' R S hR hS
    obtain ⟨h1, h2⟩ := hR
    obtain ⟨k1, k2⟩ := hS
    refine ⟨by show XTB_sp (XTB_T a) (XTB_T c) = XTB_sp (XTB_T a') (XTB_T c'); rw [h1, k1], fun f f' => ?_⟩
    exact fun_heq_iff (XTB_El_of_T h1) (XTB_El_of_T k1) h2 k2 f f'
  total := fun hR x => ⟨cast (XTB_El_of_T hR.1) x, (hR.2 _ _).mpr (cast_heq _ _).symm⟩
  onto := fun hR x' => ⟨cast (XTB_El_of_T hR.1).symm x', (hR.2 _ _).mpr (cast_heq _ _)⟩
  teq := by
    intro a a' b b' R S hR hS
    funext w
    exact congrArg (XTB_at w) (by rw [hR.1, hS.1])
  eqv := by
    intro a a' b b' R S hR hS u u' v v' hu hv
    funext w
    exact congrArg (XTB_at w) (propext (XTB_E_iff hR.1 hS.1 ((hR.2 u u').mp hu) ((hS.2 v v').mp hv)))

theorem XTB_model : XTB_F.IsModelPIm where
  refEqv := by
    intro ρ env a
    exact (XTB_F.holds_all _ _ _ _).mpr fun v => (XTB_F.holds_eqv _ _ _ _ _ _).mpr (XTB_at_true.mpr (XTB_E_refl _ _))
  symEqv := by
    intro ρ env a b
    refine (XTB_F.holds_all _ _ _ _).mpr fun x => (XTB_F.holds_all _ _ _ _).mpr fun y h => ?_
    exact (XTB_F.holds_eqv _ _ _ _ _ _).mpr (XTB_at_true.mpr (XTB_E_symm (XTB_at_true.mp ((XTB_F.holds_eqv _ _ _ _ _ _).mp h))))
  transEqv := by
    intro ρ env a b c
    refine (XTB_F.holds_all _ _ _ _).mpr fun x => (XTB_F.holds_all _ _ _ _).mpr fun y =>
      (XTB_F.holds_all _ _ _ _).mpr fun z h => ?_
    have h1 := (XTB_F.holds_eqv (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv2 tv1
      (.var (.there (.there .here))) (.var (.there .here)) (scons c (scons b (scons a ρ))) (((env, x), y), z)).mp h.1
    have h2 := (XTB_F.holds_eqv (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv1 tv0
      (.var (.there .here)) (.var .here) (scons c (scons b (scons a ρ))) (((env, x), y), z)).mp h.2
    exact (XTB_F.holds_eqv _ _ _ _ _ _).mpr (XTB_at_true.mpr (XTB_E_trans (XTB_at_true.mp h1) (XTB_at_true.mp h2)))
  refTeq := by
    intro ρ env a
    exact (XTB_F.holds_teq _ _ _ _).mpr (XTB_at_true.mpr rfl)
  llTeq := fun Q => XTB_llTeq_valid XTB_I (fun _ _ h => ⟨fun x y => HEq x y, XTB_at_true.mp h, fun _ _ => Iff.rfl⟩) Q

/-! ## Basic facts -/

abbrev XTB_top : Bool → Prop := fun _ => True
abbrev XTB_bot : Bool → Prop := fun _ => False
/-- The proposition true at the actual world only. -/
abbrev XTB_act : Bool → Prop := fun w => w = true

/-- Identity of propositions at the actual world: the same set of worlds, or each `⊤` or `⊥`. -/
theorem XTB_eqv_t (p q : Bool → Prop) :
    XTB_F.eqv .t .t p q true ↔ (p = q ∨ ((p = XTB_top ∨ p = XTB_bot) ∧ (q = XTB_top ∨ q = XTB_bot))) := by
  refine XTB_at_true.trans ⟨fun h => ?_, fun h => ?_⟩
  · rcases h.2 with h' | ⟨hp, hq⟩
    · exact Or.inl (eq_of_heq h')
    · exact Or.inr ⟨hp.2.imp eq_of_heq eq_of_heq, hq.2.imp eq_of_heq eq_of_heq⟩
  · rcases h with h' | ⟨hp, hq⟩
    · exact ⟨rfl, Or.inl (heq_of_eq h')⟩
    · exact ⟨rfl, Or.inr ⟨⟨rfl, hp.imp heq_of_eq heq_of_eq⟩, ⟨rfl, hq.imp heq_of_eq heq_of_eq⟩⟩⟩

/-- `⊤ ≡ ⊥` at the actual world. -/
theorem XTB_topbot : XTB_F.eqv .t .t XTB_top XTB_bot true :=
  (XTB_eqv_t _ _).mpr (Or.inr ⟨Or.inl rfl, Or.inr rfl⟩)

/-- A proposition is identified with `⊤` just in case it is `⊤` or `⊥`. -/
theorem XTB_box_iff (p : Bool → Prop) : XTB_F.eqv .t .t p XTB_top true ↔ (p = XTB_top ∨ p = XTB_bot) := by
  refine (XTB_eqv_t _ _).trans ⟨fun h => ?_, fun h => Or.inr ⟨h, Or.inl rfl⟩⟩
  rcases h with h | ⟨h, _⟩
  · exact Or.inl h
  · exact h

/-- The same, with `⊤` given as the value of a formula. -/
theorem XTB_box_top {n : Nat} {Γ : Ctx n} (ρ : XTB_F.U.TEnv n) (env : XTB_F.U.Env Γ ρ) (p : Bool → Prop) :
    XTB_F.eqv .t .t p (XTB_F.eval (topF : Fm Γ) ρ env) true ↔ (p = XTB_top ∨ p = XTB_bot) := by
  rw [XTB_F.eval_topF]
  exact XTB_box_iff p

theorem XTB_topbot_eval {n : Nat} {Γ : Ctx n} (ρ : XTB_F.U.TEnv n) (env : XTB_F.U.Env Γ ρ) :
    XTB_F.eqv .t .t (XTB_F.eval (topF : Fm Γ) ρ env) (XTB_F.eval (botF : Fm Γ) ρ env) true := by
  rw [XTB_F.eval_topF, XTB_F.eval_botF]
  exact XTB_topbot

/-- `□φ` holds just in case `φ` is `⊤` or `⊥`. -/
theorem XTB_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : XTB_F.U.TEnv n) (env : XTB_F.U.Env Γ ρ) :
    XTB_F.Holds (boxF φ) ρ env ↔ (XTB_F.eval φ ρ env = XTB_top ∨ XTB_F.eval φ ρ env = XTB_bot) := by
  refine (XTB_F.holdsAt_eqv_t φ topF ρ env _).trans ?_
  rw [XTB_F.eval_topF]
  exact XTB_box_iff _

/-- A proposition true at exactly one of the two worlds is neither `⊤` nor `⊥`. -/
theorem XTB_cont (f : Bool → Prop) (h : f true ↔ ¬ f false) : ¬ (f = XTB_top ∨ f = XTB_bot) := by
  rintro (e | e)
  · have h1 : f true := (congrFun e true).mpr trivial
    have h2 : f false := (congrFun e false).mpr trivial
    exact h.mp h1 h2
  · have h1 : ¬ f true := fun x => (congrFun e true).mp x
    have h2 : ¬ f false := fun x => (congrFun e false).mp x
    exact h1 (h.mpr h2)

/-- Every identity and distinctness is contingent. -/
theorem XTB_cont_at (P : Prop) : ¬ ((fun w => XTB_at w P) = XTB_top ∨ (fun w => XTB_at w P) = XTB_bot) :=
  XTB_cont _ ⟨fun h hf => XTB_at_false.mp hf (XTB_at_true.mp h),
    fun h => XTB_at_true.mpr (Classical.byContradiction fun hp => h (XTB_at_false.mpr hp))⟩

theorem XTB_cont_nat (P : Prop) : ¬ ((fun w => ¬ XTB_at w P) = XTB_top ∨ (fun w => ¬ XTB_at w P) = XTB_bot) :=
  XTB_cont _ ⟨fun h hf => hf (XTB_at_false.mpr fun hp => h (XTB_at_true.mpr hp)),
    fun h ht => h (fun hf => XTB_at_false.mp hf (XTB_at_true.mp ht))⟩

theorem XTB_act_cont : ¬ (XTB_act = XTB_top ∨ XTB_act = XTB_bot) :=
  XTB_cont _ ⟨fun _ h2 => Bool.false_ne_true h2, fun _ => rfl⟩

/-! ## ⊤≢⊥, Truth, T -/

/-- ⊤≢⊥ fails: `⊤` and `⊥` are identified. -/
theorem XTB_not_TopBot : ¬ XTB_F.Valid TopBot := fun h => by
  have h0 := h (fun i => i.elim0) ()
  exact (XTB_F.holds_neg _ _ _).mp h0 ((XTB_F.holdsAt_eqv_t _ _ _ _ _).mpr (XTB_topbot_eval (Γ := Ctx.nil) _ _))

theorem XTB_not_Truth : ¬ XTB_F.Valid Truth := fun h => by
  have h0 : ∀ p q : Bool → Prop, XTB_F.eqv .t .t p q true → p true → q true := h (fun i => i.elim0) ()
  exact h0 XTB_top XTB_bot XTB_topbot trivial

/-- T fails: `⊥` is identified with `⊤`, so necessary, but false. -/
theorem XTB_not_TAx : ¬ XTB_F.Valid TAx := fun h => by
  have h0 := (XTB_F.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) XTB_bot
  exact (XTB_F.holds_imp _ _ _ _).mp h0 ((XTB_box _ _ _).mpr (Or.inr rfl))

/-- LL≡ fails, since it proves ⊤≢⊥. -/
theorem XTB_not_LLEqv : ¬ XTB_F.Valid LLEqv := fun h =>
  XTB_not_TopBot (XTB_F.soundness XTB_model (fun χ (e : χ = LLEqv) => e ▸ h) (Derive.d_TopBot rfl))

/-! ## Congruence -/

/-- `λp. p ∧ (actual)`. -/
abbrev XTB_f : (Bool → Prop) → Bool → Prop := fun p w => p w ∧ w = true

theorem XTB_tr_WCong : XTB_F.Tr WCong ↔ ∀ a b c d (f : XTB_U.El a → XTB_U.El c) (g : XTB_U.El b → XTB_U.El d) x y,
    (XTB_F.teq a b true ∧ XTB_F.teq c d true) ∧ (XTB_F.eqv (.arr a c) (.arr b d) f g true ∧ XTB_F.eqv a b x y true) →
    XTB_F.eqv c d (f x) (g y) true := Iff.rfl

/-- WCong fails: `⊤ ≡ ⊥`, but `λp. p ∧ (actual)` sends them to the proposition true at the actual
world only, and to `⊥`. -/
theorem XTB_not_WCong : ¬ XTB_F.Valid WCong := fun h => by
  have h0 := XTB_tr_WCong.mp ((XTB_F.valid_iff_tr _).mp h) .t .t .t .t XTB_f XTB_f XTB_top XTB_bot
    ⟨⟨XTB_at_true.mpr rfl, XTB_at_true.mpr rfl⟩, ⟨XTB_at_true.mpr (XTB_E_refl _ _), XTB_topbot⟩⟩
  rcases (XTB_eqv_t _ _).mp h0 with e | ⟨e | e, _⟩
  · exact ((congrFun e true).mp (And.intro trivial rfl)).1
  · exact Bool.false_ne_true ((congrFun e false).mpr trivial).2
  · exact (congrFun e true).mp (And.intro trivial rfl)

theorem XTB_not_Cong : ¬ XTB_F.Valid Cong := fun h => by
  have h0 := XTB_F.tr_Cong.mp ((XTB_F.valid_iff_tr _).mp h) .t .t .t .t XTB_f XTB_f XTB_top XTB_bot
    ⟨XTB_at_true.mpr (XTB_E_refl _ _), XTB_topbot⟩
  rcases (XTB_eqv_t _ _).mp h0 with e | ⟨e | e, _⟩
  · exact ((congrFun e true).mp (And.intro trivial rfl)).1
  · exact Bool.false_ne_true ((congrFun e false).mpr trivial).2
  · exact (congrFun e true).mp (And.intro trivial rfl)

theorem XTB_tr_PCong : XTB_F.Tr PCong ↔ ∀ a c d (f : XTB_U.El a → XTB_U.El c) (g : XTB_U.El a → XTB_U.El d) x,
    XTB_F.eqv (.arr a c) (.arr a d) f g true → XTB_F.eqv c d (f x) (g x) true := Iff.rfl

/-- PCong→ fails: `λx.⊤`, of type `e → t`, is identified with `λx.⊤`, of type `e → d`; but `t` and
`d` have different keys, so their values are not identified. -/
theorem XTB_not_PCong : ¬ XTB_F.Valid PCong := fun h => by
  have h0 := XTB_tr_PCong.mp ((XTB_F.valid_iff_tr _).mp h) .e .t XTB_d (fun _ => XTB_top) (fun _ => XTB_top) ()
    (XTB_at_true.mpr ⟨by decide, Or.inl HEq.rfl⟩)
  exact absurd (XTB_at_true.mp h0).1 (by decide)

/-- PCong← fails: `λx.⊤` and `λx.⊥` agree up to identity at each argument, but are not identified. -/
theorem XTB_not_PExt : ¬ XTB_F.Valid PExt := fun h => by
  have h0 := XTB_F.tr_PExt.mp ((XTB_F.valid_iff_tr _).mp h) .e .t .t (fun _ => XTB_top) (fun _ => XTB_bot)
    (fun _ => XTB_topbot)
  rcases (XTB_at_true.mp h0).2 with e | ⟨he, _⟩
  · exact (congrFun (congrFun (eq_of_heq e) ()) true).mp trivial
  · cases he.1

/-! ## Identity of types -/

/-- Inj≈ fails: `e → t ≈ e → d`, but not `t ≈ d`. -/
theorem XTB_not_Inj : ¬ XTB_F.Valid Inj := fun h => by
  have h0 := XTB_F.tr_Inj.mp ((XTB_F.valid_iff_tr _).mp h) .e .e .t XTB_d (XTB_at_true.mpr (by decide))
  exact absurd (XTB_at_true.mp h0.2) (by decide)

theorem XTB_tr_Recovery : XTB_F.Tr Recovery ↔ ∀ a b c d, XTB_F.teq (.arr a c) (.arr b d) true ∧
    XTB_F.teq a b true → XTB_F.teq c d true := Iff.rfl

theorem XTB_not_Recovery : ¬ XTB_F.Valid Recovery := fun h => by
  have h0 := XTB_tr_Recovery.mp ((XTB_F.valid_iff_tr _).mp h) .e .e .t XTB_d
    ⟨XTB_at_true.mpr (by decide), XTB_at_true.mpr rfl⟩
  exact absurd (XTB_at_true.mp h0) (by decide)

/-! ## Identification across types -/

theorem XTB_Disjoint : XTB_F.Valid Disjoint :=
  (XTB_F.valid_iff_tr _).mpr <| XTB_F.tr_Disjoint.mpr fun _ _ h _ _ hxy =>
    h (XTB_at_true.mpr (XTB_at_true.mp hxy).1)

theorem XTB_Slogan : XTB_F.Valid Slogan :=
  (XTB_F.valid_iff_tr _).mpr <| XTB_F.tr_Slogan.mpr fun _ b _ hxy => by
    obtain ⟨p, q, e⟩ := XTB_T_arr b .t
    have h1 := (XTB_at_true.mp hxy).1.trans e
    cases h1

theorem XTB_tr_Twin : XTB_F.Tr Twin ↔ ∀ a (x : XTB_U.El a), ∃ b, ¬ XTB_F.teq a b true ∧
    ∃ y : XTB_U.El b, XTB_F.eqv a b x y true := Iff.rfl

theorem XTB_not_Twin : ¬ XTB_F.Valid Twin := fun h => by
  obtain ⟨_, hb, _, hy⟩ := XTB_tr_Twin.mp ((XTB_F.valid_iff_tr _).mp h) .e ()
  exact hb (XTB_at_true.mpr (XTB_at_true.mp hy).1)

theorem XTB_tr_Hae : XTB_F.Tr Hae ↔
    ∀ a (x : XTB_U.El a), XTB_F.eqv a (.arr a .t) x (fun y => XTB_F.eqv a a y x) true := Iff.rfl

theorem XTB_not_Hae : ¬ XTB_F.Valid Hae := fun h =>
  XTB_T_pred_ne .e (XTB_at_true.mp (XTB_tr_Hae.mp ((XTB_F.valid_iff_tr _).mp h) .e ())).1.symm

theorem XTB_tr_Cantor : XTB_F.Tr Cantor ↔
    ∀ a, ∃ G : XTB_U.El a → Bool → Prop, ∀ y : XTB_U.El a, ¬ XTB_F.eqv (.arr a .t) a G y true := Iff.rfl

theorem XTB_Cantor : XTB_F.Valid Cantor :=
  (XTB_F.valid_iff_tr _).mpr <| XTB_tr_Cantor.mpr fun a =>
    ⟨fun _ => XTB_top, fun _ hy => XTB_T_pred_ne a (XTB_at_true.mp hy).1⟩

theorem XTB_ExtT : XTB_F.Valid ExtT :=
  (XTB_F.valid_iff_tr _).mpr <| XTB_F.tr_ExtT.mpr fun a _ h => by
    obtain ⟨x⟩ := Univ.El_nonempty (U := XTB_U) a
    obtain ⟨_, hy⟩ := h.1 x
    exact XTB_at_true.mpr (XTB_at_true.mp hy).1

/-- Int≈ holds: if `α` and `β` have different keys, then `α ⊑ β` is false at the actual world and
true at the other, so it is not necessary. -/
theorem XTB_IntT : XTB_F.Valid IntT := by
  intro ρ env
  refine (XTB_F.holds_tall _ _ _).mpr fun a => (XTB_F.holds_tall _ _ _).mpr fun b => ?_
  refine (XTB_F.holds_imp _ _ _ _).mpr fun h => ?_
  refine (XTB_F.holds_teq _ _ _ _).mpr (XTB_at_true.mpr ?_)
  refine Classical.byContradiction fun hab => ?_
  have h1 := (XTB_box _ _ _).mp ((XTB_F.holds_conj _ _ _ _).mp h).1
  have e : XTB_F.eval (subT : Fm (Ctx.nil.text.text)) (scons b (scons a ρ)) env =
      fun w => ∀ x : XTB_U.El a, ∃ y : XTB_U.El b, XTB_at w (XTB_E a b x y) := rfl
  rw [e] at h1
  obtain ⟨x0⟩ := Univ.El_nonempty (U := XTB_U) a
  obtain ⟨y0⟩ := Univ.El_nonempty (U := XTB_U) b
  rcases h1 with e1 | e1
  · obtain ⟨_, hy⟩ := (congrFun e1 true).mpr trivial x0
    exact hab (XTB_at_true.mp hy).1
  · exact (congrFun e1 false).mp (fun _ => ⟨y0, XTB_at_false.mpr fun hE => hab hE.1⟩)

/-! ## Necessity of identity and distinctness -/

/-- NI≡ fails: the entity is identified with itself at the actual world only. -/
theorem XTB_not_NIEqv : ¬ XTB_F.Valid NIEqv := fun h => by
  have h0 := XTB_F.tr_NIEqv.mp ((XTB_F.valid_iff_tr _).mp h) .e () () (XTB_at_true.mpr (XTB_E_refl _ _))
  exact XTB_cont_at (XTB_E .e .e () ()) ((XTB_box_top (Γ := Ctx.nil) _ _ _).mp h0)

theorem XTB_not_NIX : ¬ XTB_F.Valid NIX := fun h => by
  have h0 := XTB_F.tr_NIX.mp ((XTB_F.valid_iff_tr _).mp h) .e .e () () (XTB_at_true.mpr (XTB_E_refl _ _))
  exact XTB_cont_at (XTB_E .e .e () ()) ((XTB_box_top (Γ := Ctx.nil) _ _ _).mp h0)

/-- NI≈ fails: `e ≈ e` at the actual world only. -/
theorem XTB_not_NITeq : ¬ XTB_F.Valid NITeq := fun h => by
  have h0 := XTB_F.tr_NITeq.mp ((XTB_F.valid_iff_tr _).mp h) .e .e (XTB_at_true.mpr rfl)
  exact XTB_cont_at (XTB_T .e = XTB_T .e) ((XTB_box_top (Γ := Ctx.nil) _ _ _).mp h0)

/-- ND≈ fails: `e ≈ t` at the other world. -/
theorem XTB_not_NDTeq : ¬ XTB_F.Valid NDTeq := fun h => by
  have h0 := XTB_F.tr_NDTeq.mp ((XTB_F.valid_iff_tr _).mp h) .e .t (fun h1 => by cases (XTB_at_true.mp h1))
  exact XTB_cont_nat (XTB_T .e = XTB_T .t) ((XTB_box_top (Γ := Ctx.nil) _ _ _).mp h0)

/-- ND× fails: the entity and `⊤` are identified at the other world. -/
theorem XTB_not_NDX : ¬ XTB_F.Valid NDX := fun h => by
  have h0 := XTB_F.tr_NDX.mp ((XTB_F.valid_iff_tr _).mp h) .e .t () XTB_top
    (fun h1 => by cases (XTB_at_true.mp h1).1)
  exact XTB_cont_nat (XTB_E .e .t () XTB_top) ((XTB_box_top (Γ := Ctx.nil) _ _ _).mp h0)

/-! ## Grain -/

theorem XTB_not_Collapse : ¬ XTB_F.Valid Collapse := fun h => by
  have h0 := (XTB_F.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) XTB_act
  exact XTB_act_cont ((XTB_box _ _ _).mp ((XTB_F.holds_imp _ _ _ _).mp h0 rfl))

theorem XTB_tr_PropExt : XTB_F.Tr PropExt ↔ ∀ p q : Bool → Prop, (p true ↔ q true) → XTB_F.eqv .t .t p q true :=
  Iff.rfl

theorem XTB_not_PropExt : ¬ XTB_F.Valid PropExt := fun h =>
  XTB_act_cont ((XTB_box_iff _).mp (XTB_tr_PropExt.mp ((XTB_F.valid_iff_tr _).mp h) XTB_act XTB_top
    ⟨fun _ => trivial, fun _ => rfl⟩))

theorem XTB_Bool : ∀ φ, BoolSch φ → XTB_F.Valid φ :=
  XTB_F.bool_valid fun p => XTB_at_true.mpr (XTB_E_refl .t p)

theorem XTB_tr_IdId : XTB_F.Tr IdId ↔ ∀ a (x y : XTB_U.El a), XTB_F.eqv .t .t (XTB_F.eqv a a x y)
    (fun w => ∀ G : XTB_U.El a → Bool → Prop, G x w → G y w) true := Iff.rfl

/-- The Identity Identity fails: that the entity is itself is true at the actual world only, while
`∀F(F x → F x)` is `⊤`. -/
theorem XTB_not_IdId : ¬ XTB_F.Valid IdId := fun h => by
  have h0 := XTB_tr_IdId.mp ((XTB_F.valid_iff_tr _).mp h) .e () ()
  rcases (XTB_eqv_t _ _).mp h0 with e | ⟨hp, _⟩
  · have h1 := (congrFun e false).mpr (fun _ hG => hG)
    exact XTB_at_false.mp h1 (XTB_E_refl _ _)
  · exact XTB_cont_at (XTB_E .e .e () ()) hp

/-! ## Barcan formulas -/

theorem XTB_TBF : ∀ χ, TBFSch χ → XTB_F.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (XTB_F.holds_imp _ _ _ _).mpr fun h => (XTB_box _ _ _).mpr ?_
  have h' : ∀ a, XTB_F.eval φ (scons a ρ) env = XTB_top ∨ XTB_F.eval φ (scons a ρ) env = XTB_bot :=
    fun a => (XTB_box _ _ _).mp ((XTB_F.holds_tall _ _ _).mp h a)
  by_cases hex : ∃ a, XTB_F.eval φ (scons a ρ) env = XTB_bot
  · obtain ⟨a, ha⟩ := hex
    exact Or.inr (funext fun w => propext ⟨fun hw => (congrFun ha w).mp (hw a), False.elim⟩)
  · exact Or.inl (funext fun w => propext ⟨fun _ => trivial, fun _ a =>
      (congrFun ((h' a).resolve_right fun hb => hex ⟨a, hb⟩) w).mpr trivial⟩)

/-- TCBF fails: `𝔸α(α ≈ e)` is `⊥`, so necessary; but `e ≈ e` is not necessary. -/
theorem XTB_not_TCBF : ¬ ∀ χ, TCBFSch χ → XTB_F.Valid χ := fun h => by
  have h0 := h (TCBFI (Tm.teq tv0 tyE : Fm Ctx.nil.text)) ⟨_, rfl⟩ (fun i => i.elim0) ()
  have hb : XTB_F.Holds (boxF (Tm.tall (Tm.teq tv0 tyE : Fm Ctx.nil.text))) (fun i => i.elim0) () := by
    refine (XTB_box _ _ _).mpr (Or.inr (funext fun w => propext ⟨fun hw => ?_, False.elim⟩))
    cases w
    · exact (XTB_at_false (P := XTB_T .e = XTB_T .e)).mp (hw .e) rfl
    · exact absurd ((XTB_at_true (P := XTB_T .t = XTB_T .e)).mp (hw .t)) (by decide)
  have h1 := (XTB_F.holds_tall _ _ _).mp ((XTB_F.holds_imp _ _ _ _).mp h0 hb) .e
  exact XTB_cont_at (XTB_T .e = XTB_T .e) ((XTB_box _ _ _).mp h1)

/-- Type Necessitism: at each world, every type is `≈` some type (itself at the actual world, a
type with another key at the other world). -/
theorem XTB_TNec : XTB_F.Valid TNec := by
  intro ρ env
  refine (XTB_F.holds_tall _ _ _).mpr fun a => (XTB_box _ _ _).mpr
    (Or.inl (funext fun w => propext ⟨fun _ => trivial, fun _ => ?_⟩))
  cases w
  · by_cases ha : XTB_T a = .e
    · exact Exists.intro .t ((XTB_at_false (P := XTB_T a = XTB_T .t)).mpr fun h1 => by
        rw [ha] at h1; cases h1)
    · exact Exists.intro .e ((XTB_at_false (P := XTB_T a = XTB_T .e)).mpr fun h1 => ha h1)
  · exact Exists.intro a ((XTB_at_true (P := XTB_T a = XTB_T a)).mpr rfl)

theorem XTB_BF : XTB_F.Valid BF :=
  (XTB_F.valid_iff_tr _).mpr <| XTB_F.tr_BF.mpr fun a G h => by
    have h' : ∀ x, G x = XTB_top ∨ G x = XTB_bot := fun x => (XTB_box_top _ _ _).mp (h x)
    refine (XTB_box_top _ _ _).mpr ?_
    by_cases hex : ∃ x, G x = XTB_bot
    · obtain ⟨x, hx⟩ := hex
      exact Or.inr (funext fun w => propext ⟨fun hw => (congrFun hx w).mp (hw x), False.elim⟩)
    · exact Or.inl (funext fun w => propext ⟨fun _ => trivial, fun _ x =>
        (congrFun ((h' x).resolve_right fun hb => hex ⟨x, hb⟩) w).mpr trivial⟩)

/-- CBF fails: every proposition is `⊥` somewhere, so `∀p p` is `⊥`, and necessary; but the
proposition true at the actual world only is not necessary. -/
theorem XTB_not_CBF : ¬ XTB_F.Valid CBF := fun h => by
  have h0 := XTB_F.tr_CBF.mp ((XTB_F.valid_iff_tr _).mp h) .t (fun p => p)
    ((XTB_box_top _ _ _).mpr (Or.inr (funext fun w => propext ⟨fun hw => hw XTB_bot, False.elim⟩))) XTB_act
  exact XTB_act_cont ((XTB_box_top _ _ _).mp h0)

/-- Necessitism fails: at the other world the entity is identified with nothing. -/
theorem XTB_not_Nec : ¬ XTB_F.Valid Nec := fun h => by
  have h0 := XTB_F.tr_Nec.mp ((XTB_F.valid_iff_tr _).mp h) .e ()
  refine XTB_cont _ ⟨fun _ h2 => ?_, fun _ => ⟨(), XTB_at_true.mpr (XTB_E_refl _ _)⟩⟩ ((XTB_box_top _ _ _).mp h0)
  obtain ⟨y, hy⟩ := h2
  exact XTB_at_false.mp hy (XTB_E_refl .e y)

theorem XTB_Choice : XTB_F.Valid Choice := XTB_F.Choice_valid

/-! ## Classicism -/

/-- Classicism fails, since it proves NI≈. -/
theorem XTB_not_Class : ¬ ∀ χ, ClassSch χ → XTB_F.Valid χ := fun h =>
  XTB_not_NITeq (XTB_F.soundness XTB_model h (d_NITeq_of_Class (S := ClassSch) (fun _ hc => hc)))

/-! ## Leibniz's law across identified types -/

/-- The polymorphic predicate `λγ.λz:γ. ∃_{γ→t} F (F ≡_{γ→t,t→t} λp:t.p ∧ F z)`. -/
def XTB_PredT : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (ex tv0.pred (conj (eqv tv0.pred tyT.pred (.var .here) (.lam tyT (.var .here)))
    (.app (.var .here) (.var (.there .here))))))

/-- The body of `XTB_PredT`. -/
def XTB_PredT_body : Fm ((Ctx.nil.text).ext tv0) :=
  ex tv0.pred (conj (eqv tv0.pred tyT.pred (.var .here) (.lam tyT (.var .here)))
    (.app (.var .here) (.var (.there .here))))

/-- At `t`, `XTB_PredT` holds of exactly the propositions true at the actual world: only `λp.p` is
identified with `λp.p`. -/
theorem XTB_PredT_t (z : Bool → Prop) :
    XTB_F.Holds XTB_PredT_body (scons .t (fun i => i.elim0)) ((), z) ↔ z true := by
  refine (XTB_F.holds_ex _ _ _ _).trans ⟨fun ⟨G, hG⟩ => ?_, fun hz => ⟨fun p => p, ?_⟩⟩
  · obtain ⟨h1, h2⟩ := (XTB_F.holds_conj _ _ _ _).mp hG
    have e := XTB_at_true.mp ((XTB_F.holds_eqv _ _ _ _ _ _).mp h1)
    rcases e.2 with e' | ⟨he, _⟩
    · have e'' : G = fun p => p := eq_of_heq ((cast_heq _ _).symm.trans (e'.trans (cast_heq _ _)))
      subst e''
      exact h2
    · cases he.1
  · exact (XTB_F.holds_conj _ _ _ _).mpr
      ⟨(XTB_F.holds_eqv _ _ _ _ _ _).mpr (XTB_at_true.mpr (XTB_E_refl _ _)), hz⟩

/-- LL≡/≈ fails for `XTB_PredT`: `⊤` and `⊥` are identified items of type `t`, but `XTB_PredT`
holds of `⊤` and not of `⊥`. -/
theorem XTB_not_Bridge : ¬ XTB_F.Valid (Bridge XTB_PredT) := fun h => by
  have h0 := (XTB_F.holds_tall _ _ _).mp ((XTB_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) .t
  have h1 := (XTB_F.holds_all _ _ _ _).mp ((XTB_F.holds_all _ _ _ _).mp h0 XTB_top) XTB_bot
  have hx : XTB_F.Holds XTB_PredT_body (scons .t (fun i => i.elim0)) ((), XTB_top) := (XTB_PredT_t _).mpr trivial
  have h2 := (XTB_F.holds_imp _ _ _ _).mp ((XTB_F.holds_imp _ _ _ _).mp h1 ((XTB_F.holds_conj _ _ _ _).mpr
    ⟨(XTB_F.holds_eqv _ _ _ _ _ _).mpr XTB_topbot, (XTB_F.holds_teq _ _ _ _).mpr (XTB_at_true.mpr rfl)⟩)) hx
  have h3 : XTB_F.Holds XTB_PredT_body (scons .t (fun i => i.elim0)) ((), XTB_bot) := h2
  exact (XTB_PredT_t _).mp h3

/-- LL≡-Poly fails, for the same predicate. -/
theorem XTB_not_LLPoly : ¬ XTB_F.Valid (LLPoly XTB_PredT) := fun h => by
  have h0 := (XTB_F.holds_tall _ _ _).mp ((XTB_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) .t
  have h1 := (XTB_F.holds_all _ _ _ _).mp ((XTB_F.holds_all _ _ _ _).mp h0 XTB_top) XTB_bot
  have hx : XTB_F.Holds XTB_PredT_body (scons .t (fun i => i.elim0)) ((), XTB_top) := (XTB_PredT_t _).mpr trivial
  have h2 := (XTB_F.holds_imp _ _ _ _).mp ((XTB_F.holds_imp _ _ _ _).mp h1
    ((XTB_F.holds_eqv _ _ _ _ _ _).mpr XTB_topbot)) hx
  have h3 : XTB_F.Holds XTB_PredT_body (scons .t (fun i => i.elim0)) ((), XTB_bot) := h2
  exact (XTB_PredT_t _).mp h3

end Wd
end PIF
