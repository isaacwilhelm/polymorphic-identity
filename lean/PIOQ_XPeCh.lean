import PIBF
set_option autoImplicit false

/-!
# Relation-preserving functions: PropExt≡ without Functional Choice

A new semantics. Propositions are truth values and the type universe is the standard one, but an
*item* of a type is a member of its set which is related to itself by two logical relations, one
for each of two indices. At the actual index (`true`) the relation is identity: equality of
entities, material equivalence of propositions. At the other index (`false`) every two
propositions are related, and entities are related just in case they are equal. At a function
type, at either index, two functions are related when they take related items to related values.
The quantifier `∀_σ` ranges over the items of `σ`; the type quantifier over all types. Items are
identified (`≡`) when they have the same type and are related at the actual index; `≈` is
identity of types.

Since every constant is related to itself at both indices, so is the value of every term
(the fundamental lemma below), and the proof system is sound for this semantics. Identity of
propositions is material equivalence, so PropExt≡ (and with it Collapse and ND×) holds, and so
does Classicism. But an item of `t → e` must send `⊤` and `⊥`, which are related at the other
index, to related, that is equal, entities: it is constant. So the total relation
`R p y := (y ↔ p)` contains no function, and Functional Choice fails.

The model `𝔐_pe,¬ch` (`XPC_U`: two entities, no further base types) is a model of PIᶜ
(`XPC_M_model`) in which PropExt≡ holds; so PIᶜ + PropExt≡ does not prove Functional Choice
(`XPC_PIc_PropExt_not_Choice`). Nothing is identified across types and `≈` is identity of types,
so of the principles settled in §11, all hold there except Twin, Haecceitism and Functional
Choice.
-/

namespace PIF
open Tm

/-! ## 1. The relations at the two indices, on the members of the universe -/

/-- The relation at index `j` at each type (`true` is the actual index). At a function type,
functions are related when they send related items to related values. -/
def XPC_rel (U : Univ) : (a : Code U.Base) → Bool → U.El a → U.El a → Prop
  | .e, _ => fun x y => x = y
  | .t, j => fun p q => j = true → (p ↔ q)
  | .base _, _ => fun x y => x = y
  | .arr a c, j => fun f g => ∀ x y, (∀ k, XPC_rel U a k x x) → (∀ k, XPC_rel U a k y y) →
      XPC_rel U a j x y → XPC_rel U c j (f x) (g y)

/-- An item of a type: a member of its set related to itself at both indices. -/
def XPC_adm (U : Univ) (a : Code U.Base) (x : U.El a) : Prop := ∀ k, XPC_rel U a k x x

theorem XPC_rel_symm (U : Univ) : ∀ (a : Code U.Base) (j : Bool) (x y : U.El a),
    XPC_rel U a j x y → XPC_rel U a j y x
  | .e, _, _, _, h => Eq.symm h
  | .t, _, _, _, h => fun hj => (h hj).symm
  | .base _, _, _, _, h => Eq.symm h
  | .arr a c, j, _, _, h => fun x y hx hy hxy =>
      XPC_rel_symm U c j _ _ (h y x hy hx (XPC_rel_symm U a j x y hxy))

theorem XPC_rel_trans (U : Univ) : ∀ (a : Code U.Base) (j : Bool) (x y z : U.El a),
    XPC_rel U a j x y → XPC_rel U a j y z → XPC_rel U a j x z
  | .e, _, _, _, _, h1, h2 => Eq.trans h1 h2
  | .t, _, _, _, _, h1, h2 => fun hj => (h1 hj).trans (h2 hj)
  | .base _, _, _, _, _, h1, h2 => Eq.trans h1 h2
  | .arr _ c, j, _, _, _, h1, h2 => fun x y hx hy hxy =>
      XPC_rel_trans U c j _ _ _ (h1 x y hx hy hxy) (h2 y y hy hy (hy j))

/-- Every type has an item. -/
theorem XPC_adm_ne (U : Univ) : ∀ a : Code U.Base, ∃ x : U.El a, ∀ k, XPC_rel U a k x x
  | .e => let ⟨x⟩ := U.neE; ⟨x, fun _ => rfl⟩
  | .t => ⟨True, fun _ _ => Iff.rfl⟩
  | .base b => let ⟨x⟩ := U.neB b; ⟨x, fun _ => rfl⟩
  | .arr _ c => let ⟨y, hy⟩ := XPC_adm_ne U c; ⟨fun _ => y, fun k _ _ _ _ _ => hy k⟩

theorem XPC_rel_congr (U : Univ) {a b : Code U.Base} (h : a = b) (j : Bool) {x x' : U.El a}
    {y y' : U.El b} (hx : HEq x y) (hx' : HEq x' y') : XPC_rel U a j x x' ↔ XPC_rel U b j y y' := by
  subst h; cases hx; cases hx'; exact Iff.rfl

/-! ## 2. The relations at each category -/

/-- The relation at index `j` at each category, on its semantic values. -/
def XPC_Rel (U : Univ) : {n : Nat} → (K : Cat n) → (ρ : U.TEnv n) → Bool →
    U.CatVal K ρ → U.CatVal K ρ → Prop
  | _, .e, _, _ => fun x y => x = y
  | _, .t, _, j => fun p q => j = true → (p ↔ q)
  | _, .var i, ρ, j => XPC_rel U (ρ i) j
  | _, .arr K L, ρ, j => fun f g => ∀ x y, (∀ k, XPC_Rel U K ρ k x x) → (∀ k, XPC_Rel U K ρ k y y) →
      XPC_Rel U K ρ j x y → XPC_Rel U L ρ j (f x) (g y)
  | _, .pi K, ρ, j => fun G G' => ∀ a, XPC_Rel U K (scons a ρ) j (G a) (G' a)

theorem XPC_Rel_code (U : Univ) {n : Nat} (K : Cat n) : K.Simple → ∀ (ρ : U.TEnv n) (j : Bool)
    (u u' : U.CatVal K ρ) (x x' : U.El (U.code K ρ)), HEq u x → HEq u' x' →
    (XPC_Rel U K ρ j u u' ↔ XPC_rel U (U.code K ρ) j x x') := by
  induction K with
  | e => intro _ ρ j u u' x x' hx hx'; cases hx; cases hx'; exact Iff.rfl
  | t => intro _ ρ j u u' x x' hx hx'; cases hx; cases hx'; exact Iff.rfl
  | var i => intro _ ρ j u u' x x' hx hx'; cases hx; cases hx'; exact Iff.rfl
  | arr a b iha ihb =>
    intro hK ρ j u u' x x' hx hx'
    refine Invariance.forall_heq (Univ.El_code ρ hK.1).symm fun v y hvy => ?_
    refine Invariance.forall_heq (Univ.El_code ρ hK.1).symm fun v' y' hvy' => ?_
    refine imp_congr (forall_congr' fun k => iha hK.1 ρ k v v y y hvy hvy)
      (imp_congr (forall_congr' fun k => iha hK.1 ρ k v' v' y' y' hvy' hvy')
        (imp_congr (iha hK.1 ρ j v v' y y' hvy hvy') (ihb hK.2 ρ j _ _ _ _ ?_ ?_)))
    · exact heq_app (Univ.El_code ρ hK.1).symm (Univ.El_code ρ hK.2).symm hx hvy
    · exact heq_app (Univ.El_code ρ hK.1).symm (Univ.El_code ρ hK.2).symm hx' hvy'
  | pi _ _ => intro hK; exact hK.elim

theorem XPC_Rel_ren (U : Univ) {n : Nat} (K : Cat n) : ∀ {m : Nat} (r : Fin n → Fin m)
    (ρ' : U.TEnv m) (ρ : U.TEnv n), (∀ i, ρ' (r i) = ρ i) → ∀ (j : Bool)
    (v v' : U.CatVal (K.ren r) ρ') (z z' : U.CatVal K ρ), HEq v z → HEq v' z' →
    (XPC_Rel U (K.ren r) ρ' j v v' ↔ XPC_Rel U K ρ j z z') := by
  induction K with
  | e => intro m r ρ' ρ _ j v v' z z' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | t => intro m r ρ' ρ _ j v v' z z' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | var i => intro m r ρ' ρ hρ j v v' z z' hv hv'; exact XPC_rel_congr U (hρ i) j hv hv'
  | arr a b iha ihb =>
    intro m r ρ' ρ hρ j v v' z z' hv hv'
    refine Invariance.forall_heq (Univ.CatVal_ren a r ρ' ρ hρ) fun q y hqy => ?_
    refine Invariance.forall_heq (Univ.CatVal_ren a r ρ' ρ hρ) fun q' y' hqy' => ?_
    refine imp_congr (forall_congr' fun k => iha r ρ' ρ hρ k q q y y hqy hqy)
      (imp_congr (forall_congr' fun k => iha r ρ' ρ hρ k q' q' y' y' hqy' hqy')
        (imp_congr (iha r ρ' ρ hρ j q q' y y' hqy hqy') (ihb r ρ' ρ hρ j _ _ _ _ ?_ ?_)))
    · exact heq_app (Univ.CatVal_ren a r ρ' ρ hρ) (Univ.CatVal_ren b r ρ' ρ hρ) hv hqy
    · exact heq_app (Univ.CatVal_ren a r ρ' ρ hρ) (Univ.CatVal_ren b r ρ' ρ hρ) hv' hqy'
  | pi K ih =>
    intro m r ρ' ρ hρ j v v' z z' hv hv'
    refine forall_congr' fun a => ih (liftR r) (scons a ρ') (scons a ρ)
      (fin_cases rfl (fun i => hρ i)) j _ _ _ _ ?_ ?_
    · exact heq_dapp (fun a => Univ.CatVal_ren K (liftR r) (scons a ρ') (scons a ρ)
        (fin_cases rfl (fun i => hρ i))) hv rfl
    · exact heq_dapp (fun a => Univ.CatVal_ren K (liftR r) (scons a ρ') (scons a ρ)
        (fin_cases rfl (fun i => hρ i))) hv' rfl

theorem XPC_Rel_sub (U : Univ) {n : Nat} (K : Cat n) : ∀ {m : Nat} (s : Fin n → Ty m)
    (ρ' : U.TEnv m) (ρ : U.TEnv n), (∀ i, U.code (s i).1 ρ' = ρ i) → ∀ (j : Bool)
    (v v' : U.CatVal (K.sub s) ρ') (z z' : U.CatVal K ρ), HEq v z → HEq v' z' →
    (XPC_Rel U (K.sub s) ρ' j v v' ↔ XPC_Rel U K ρ j z z') := by
  induction K with
  | e => intro m s ρ' ρ _ j v v' z z' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | t => intro m s ρ' ρ _ j v v' z z' hv hv'; cases hv; cases hv'; exact Iff.rfl
  | var i =>
    intro m s ρ' ρ hρ j v v' z z' hv hv'
    exact (XPC_Rel_code U (s i).1 (s i).2 ρ' j v v' (cast (Univ.El_code ρ' (s i).2).symm v)
      (cast (Univ.El_code ρ' (s i).2).symm v') (cast_heq _ _).symm (cast_heq _ _).symm).trans
      (XPC_rel_congr U (hρ i) j ((cast_heq _ _).trans hv) ((cast_heq _ _).trans hv'))
  | arr a b iha ihb =>
    intro m s ρ' ρ hρ j v v' z z' hv hv'
    refine Invariance.forall_heq (Univ.CatVal_sub a s ρ' ρ hρ) fun q y hqy => ?_
    refine Invariance.forall_heq (Univ.CatVal_sub a s ρ' ρ hρ) fun q' y' hqy' => ?_
    refine imp_congr (forall_congr' fun k => iha s ρ' ρ hρ k q q y y hqy hqy)
      (imp_congr (forall_congr' fun k => iha s ρ' ρ hρ k q' q' y' y' hqy' hqy')
        (imp_congr (iha s ρ' ρ hρ j q q' y y' hqy hqy') (ihb s ρ' ρ hρ j _ _ _ _ ?_ ?_)))
    · exact heq_app (Univ.CatVal_sub a s ρ' ρ hρ) (Univ.CatVal_sub b s ρ' ρ hρ) hv hqy
    · exact heq_app (Univ.CatVal_sub a s ρ' ρ hρ) (Univ.CatVal_sub b s ρ' ρ hρ) hv' hqy'
  | pi K ih =>
    intro m s ρ' ρ hρ j v v' z z' hv hv'
    have hl : ∀ (a : Code U.Base) i, U.code (liftT s i).1 (scons a ρ') = scons a ρ i := fun a =>
      fin_cases rfl (fun i => by
        show U.code ((s i).1.ren fs) (scons a ρ') = ρ i
        rw [Univ.code_ren]; exact hρ i)
    refine forall_congr' fun a => ih (liftT s) (scons a ρ') (scons a ρ) (hl a) j _ _ _ _ ?_ ?_
    · exact heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ') (scons a ρ) (hl a)) hv rfl
    · exact heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ') (scons a ρ) (hl a)) hv' rfl

/-- Every category has an item. -/
theorem XPC_Rel_ne (U : Univ) {n : Nat} (K : Cat n) : ∀ ρ : U.TEnv n,
    ∃ v : U.CatVal K ρ, ∀ k, XPC_Rel U K ρ k v v := by
  induction K with
  | e => intro _; exact let ⟨x⟩ := U.neE; ⟨x, fun _ => rfl⟩
  | t => intro _; exact ⟨True, fun _ _ => Iff.rfl⟩
  | var i => intro ρ; exact XPC_adm_ne U (ρ i)
  | arr _ _ _ ihb => intro ρ; exact let ⟨y, hy⟩ := ihb ρ; ⟨fun _ => y, fun k _ _ _ _ _ => hy k⟩
  | pi K ih =>
    intro ρ
    exact ⟨fun a => Classical.choose (ih (scons a ρ)), fun k a => Classical.choose_spec (ih (scons a ρ)) k⟩


/-! ## 3. The values of the constants and of terms -/

/-- Identity: items are identified when they have the same type and are related at the actual
index. -/
def XPC_eqv (U : Univ) (a b : Code U.Base) (x : U.El a) (y : U.El b) : Prop :=
  ∃ h : a = b, XPC_rel U b true (cast (congrArg U.El h) x) y

/-- The values of the constants. The item quantifiers range over items. -/
def XPC_constVal (U : Univ) {n : Nat} {K : Cat n} (c : Const n K) (ρ : U.TEnv n) : U.CatVal K ρ :=
  match c with
  | .neg => fun p => ¬ p
  | .imp => fun p q => p → q
  | .and => fun p q => p ∧ q
  | .or => fun p q => p ∨ q
  | .iff => fun p q => p ↔ q
  | .all => fun a P => ∀ x, XPC_adm U a x → P x
  | .ex => fun a P => ∃ x, XPC_adm U a x ∧ P x
  | .tall => fun Q => ∀ a, Q a
  | .tex => fun Q => ∃ a, Q a
  | .eqv => fun a b x y => XPC_eqv U a b x y
  | .teq => fun a b => a = b

/-- The semantic value of a term. -/
def XPC_eval (U : Univ) {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) :
    (ρ : U.TEnv n) → U.Env Γ ρ → U.CatVal K ρ :=
  match M with
  | .var x => fun ρ env => U.lookup x ρ env
  | .const c => fun ρ _ => XPC_constVal U c ρ
  | .app f a => fun ρ env => XPC_eval U f ρ env (XPC_eval U a ρ env)
  | .lam _ b => fun ρ env v => XPC_eval U b ρ (env, v)
  | .tlam b => fun ρ env a => XPC_eval U b (scons a ρ) env
  | .tapp (K := K) f σ => fun ρ env => cast (U.tapp_eq K σ ρ) (XPC_eval U f ρ env (U.code σ.1 ρ))

/-- The truth value of a formula. -/
abbrev XPC_Holds (U : Univ) {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : U.TEnv n) (env : U.Env Γ ρ) : Prop :=
  XPC_eval U φ ρ env

/-! ## 4. The substitution lemmas, and β -/

section Subst
variable (U : Univ)

theorem XPC_eval_castK {n : Nat} {Γ : Ctx n} {K K' : Cat n} (h : K = K') (M : Tm Γ K) (ρ : U.TEnv n)
    (env : U.Env Γ ρ) : HEq (XPC_eval U (Tm.castK h M) ρ env) (XPC_eval U M ρ env) := by
  subst h; rfl

theorem XPC_lookup_castK {n : Nat} {Γ : Ctx n} {K K' : Cat n} (h : K = K') (x : Var Γ K) (ρ : U.TEnv n)
    (env : U.Env Γ ρ) : HEq (U.lookup (Var.castK h x) ρ env) (U.lookup x ρ env) := by
  subst h; rfl

theorem XPC_lookup_tthere {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) (ρ : U.TEnv (n+1))
    (env : U.Env (.text Γ) ρ) : HEq (U.lookup (.tthere x) ρ env) (U.lookup x (fun i => ρ (fs i)) env) :=
  cast_heq _ _

theorem XPC_constVal_ren {n m : Nat} (r : Fin n → Fin m) {K : Cat n} (c : Const n K) (ρ' : U.TEnv m)
    (ρ : U.TEnv n) : HEq (XPC_constVal U (c.ren r) ρ') (XPC_constVal U c ρ) := by
  cases c <;> rfl

theorem XPC_constVal_sub {n m : Nat} (s : Fin n → Ty m) {K : Cat n} (c : Const n K) (ρ' : U.TEnv m)
    (ρ : U.TEnv n) : HEq (XPC_constVal U (c.sub s) ρ') (XPC_constVal U c ρ) := by
  cases c <;> rfl

theorem XPC_eval_ren {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) :
    ∀ {m : Nat} {r : Fin n → Fin m} {Δ : Ctx m} (ρr : TRen r Γ Δ) (ρ' : U.TEnv m) (env' : U.Env Δ ρ')
      (ρ : U.TEnv n) (env : U.Env Γ ρ), (∀ i, ρ' (r i) = ρ i) →
      (∀ {L : Cat n} (x : Var Γ L), HEq (U.lookup (ρr x) ρ' env') (U.lookup x ρ env)) →
      HEq (XPC_eval U (M.ren ρr) ρ' env') (XPC_eval U M ρ env) := by
  induction M with
  | var x => intro m r Δ ρr ρ' env' ρ env _ hx; exact hx x
  | const c => intro m r Δ ρr ρ' env' ρ env _ _; exact XPC_constVal_ren U r c ρ' ρ
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
      exact (XPC_lookup_castK U _ _ _ _).trans ((XPC_lookup_tthere U (ρr y) (scons a ρ') env').trans
        ((hx y).trans (XPC_lookup_tthere U y (scons a ρ) env).symm))
  | tapp f σ ih =>
    intro m r Δ ρr ρ' env' ρ env hρ hx
    refine (XPC_eval_castK U _ _ _ _).trans ((cast_heq _ _).trans ((HEq.trans ?_ (cast_heq _ _).symm)))
    refine heq_dapp (fun a => Univ.CatVal_ren _ (liftR r) (scons a ρ') (scons a ρ)
      (fin_cases rfl (fun i => hρ i))) (ih ρr ρ' env' ρ env hρ hx) ?_
    show U.code (σ.1.ren r) ρ' = U.code σ.1 ρ
    rw [Univ.code_ren]; exact congrArg _ (funext hρ)

theorem XPC_eval_wk {n : Nat} {Γ : Ctx n} {K : Cat n} (L : Ty n) (M : Tm Γ K) (ρ : U.TEnv n)
    (env : U.Env Γ ρ) (v : U.CatVal L.1 ρ) : XPC_eval U (M.wk L) ρ (env, v) = XPC_eval U M ρ env :=
  eq_of_heq ((XPC_eval_castK U _ _ _ _).trans (XPC_eval_ren U M (wkRen L) ρ (env, v) ρ env (fun _ => rfl)
    (fun _ => XPC_lookup_castK U _ _ _ _)))

theorem XPC_eval_twk {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) (a : Code U.Base) (ρ : U.TEnv n)
    (env : U.Env Γ ρ) : HEq (XPC_eval U M.twk (scons a ρ) env) (XPC_eval U M ρ env) :=
  XPC_eval_ren U M (twkRen Γ) (scons a ρ) env ρ env (fun _ => rfl) (fun x => XPC_lookup_tthere U x _ _)

theorem XPC_eval_sub {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) :
    ∀ {m : Nat} {s : Fin n → Ty m} {Δ : Ctx m} (σs : TSub s Γ Δ) (ρ' : U.TEnv m) (env' : U.Env Δ ρ')
      (ρ : U.TEnv n) (env : U.Env Γ ρ), (∀ i, U.code (s i).1 ρ' = ρ i) →
      (∀ {L : Cat n} (x : Var Γ L), HEq (XPC_eval U (σs x) ρ' env') (U.lookup x ρ env)) →
      HEq (XPC_eval U (M.sub σs) ρ' env') (XPC_eval U M ρ env) := by
  induction M with
  | var x => intro m s Δ σs ρ' env' ρ env _ hx; exact hx x
  | const c => intro m s Δ σs ρ' env' ρ env _ _; exact XPC_constVal_sub U s c ρ' ρ
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
    | there y => exact (heq_of_eq (XPC_eval_wk U _ _ _ _ _)).trans (hx y)
  | tlam b ih =>
    intro m s Δ σs ρ' env' ρ env hρ hx
    have hρ' : ∀ (a : Code U.Base) i, U.code (liftT s i).1 (scons a ρ') = scons a ρ i := fun a =>
      fin_cases rfl (fun i => by
        show U.code ((s i).1.ren fs) (scons a ρ') = ρ i
        rw [Univ.code_ren]; exact hρ i)
    refine heq_pifun (fun a => Univ.CatVal_sub _ (liftT s) (scons a ρ') (scons a ρ) (hρ' a)) fun a => ?_
    refine ih σs.tlift (scons a ρ') env' (scons a ρ) env (hρ' a) ?_
    intro L x
    cases x with
    | tthere y =>
      exact (XPC_eval_castK U _ _ _ _).trans ((XPC_eval_twk U _ a ρ' env').trans
        ((hx y).trans (XPC_lookup_tthere U y (scons a ρ) env).symm))
  | tapp f σ ih =>
    intro m s Δ σs ρ' env' ρ env hρ hx
    have hρ' : ∀ (a : Code U.Base) i, U.code (liftT s i).1 (scons a ρ') = scons a ρ i := fun a =>
      fin_cases rfl (fun i => by
        show U.code ((s i).1.ren fs) (scons a ρ') = ρ i
        rw [Univ.code_ren]; exact hρ i)
    refine (XPC_eval_castK U _ _ _ _).trans ((cast_heq _ _).trans ((HEq.trans ?_ (cast_heq _ _).symm)))
    refine heq_dapp (fun a => Univ.CatVal_sub _ (liftT s) (scons a ρ') (scons a ρ) (hρ' a))
      (ih σs ρ' env' ρ env hρ hx) ?_
    show U.code (σ.1.sub s) ρ' = U.code σ.1 ρ
    rw [Univ.code_sub]; exact congrArg _ (funext hρ)

theorem XPC_eval_subst0 {n : Nat} {Γ : Ctx n} {σ : Ty n} {L : Cat n} (M : Tm (.ext Γ σ) L) (N : Tm Γ σ.1)
    (ρ : U.TEnv n) (env : U.Env Γ ρ) :
    XPC_eval U (M.subst0 N) ρ env = XPC_eval U M ρ (env, XPC_eval U N ρ env) := by
  refine eq_of_heq ((XPC_eval_castK U _ _ _ _).trans (XPC_eval_sub U M (sub0 N) ρ env ρ _ (fun _ => rfl) ?_))
  intro L x
  cases x with
  | here => exact XPC_eval_castK U _ _ _ _
  | there y => exact XPC_eval_castK U _ _ _ _

theorem XPC_eval_tinst {n : Nat} {Γ : Ctx n} {K : Cat (n+1)} (M : Tm (.text Γ) K) (σ : Ty n)
    (ρ : U.TEnv n) (env : U.Env Γ ρ) :
    HEq (XPC_eval U (M.tinst σ) ρ env) (XPC_eval U M (scons (U.code σ.1 ρ) ρ) env) := by
  refine XPC_eval_sub U M (tsub0 Γ σ) ρ env (scons (U.code σ.1 ρ) ρ) env (fin_cases rfl (fun _ => rfl)) ?_
  intro L x
  cases x with
  | tthere y => exact (XPC_eval_castK U _ _ _ _).trans (XPC_lookup_tthere U y (scons (U.code σ.1 ρ) ρ) env).symm

theorem XPC_eval_step {n : Nat} {Γ : Ctx n} {K : Cat n} {M N : Tm Γ K} (h : Step M N) :
    ∀ ρ env, XPC_eval U M ρ env = XPC_eval U N ρ env := by
  induction h with
  | beta b a => intro ρ env; exact (XPC_eval_subst0 U b a ρ env).symm
  | tbeta b σ => intro ρ env; exact eq_of_heq ((cast_heq _ _).trans (XPC_eval_tinst U b σ ρ env).symm)
  | appL a _ ih => intro ρ env; simp only [XPC_eval]; rw [ih ρ env]
  | appR f _ ih => intro ρ env; simp only [XPC_eval]; rw [ih ρ env]
  | lam σ _ ih => intro ρ env; exact funext fun v => ih ρ (env, v)
  | tlam _ ih => intro ρ env; exact funext fun a => ih (scons a ρ) env
  | tapp σ _ ih => intro ρ env; simp only [XPC_eval]; rw [ih ρ env]

theorem XPC_eval_betaEq {n : Nat} {Γ : Ctx n} {K : Cat n} {M N : Tm Γ K} (h : BetaEq M N) :
    ∀ ρ env, XPC_eval U M ρ env = XPC_eval U N ρ env := by
  induction h with
  | refl => intros; rfl
  | step h => exact XPC_eval_step U h
  | symm _ ih => intro ρ env; exact (ih ρ env).symm
  | trans _ _ ih1 ih2 => intro ρ env; exact (ih1 ρ env).trans (ih2 ρ env)

theorem XPC_heq_eval_tapp {n : Nat} {Γ : Ctx n} {K : Cat (n+1)} (f : Tm Γ (.pi K)) (σ : Ty n)
    (ρ : U.TEnv n) (env : U.Env Γ ρ) :
    HEq (XPC_eval U (Tm.tapp f σ) ρ env) (XPC_eval U f ρ env (U.code σ.1 ρ)) :=
  cast_heq _ _

end Subst


/-! ## 5. Truth conditions -/

section Holds
variable (U : Univ) {n : Nat} {Γ : Ctx n}

theorem XPC_cast_forall {A A' : Type} (hA : A = A') (r : A → Prop)
    (h : ((A → Prop) → Prop) = ((A' → Prop) → Prop)) (P : A' → Prop) :
    cast h (fun Q : A → Prop => ∀ x, r x → Q x) P ↔ ∀ x : A', r (cast hA.symm x) → P x := by
  subst hA; rw [cast_eq]; exact Iff.rfl

theorem XPC_cast_exists {A A' : Type} (hA : A = A') (r : A → Prop)
    (h : ((A → Prop) → Prop) = ((A' → Prop) → Prop)) (P : A' → Prop) :
    cast h (fun Q : A → Prop => ∃ x, r x ∧ Q x) P ↔ ∃ x : A', r (cast hA.symm x) ∧ P x := by
  subst hA; rw [cast_eq]; exact Iff.rfl

theorem XPC_holds_all (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : U.TEnv n) (env : U.Env Γ ρ) :
    XPC_Holds U (Tm.all σ φ) ρ env ↔ ∀ v : U.CatVal σ.1 ρ,
      XPC_adm U (U.code σ.1 ρ) (cast (Univ.El_code ρ σ.2).symm v) → XPC_Holds U φ ρ (env, v) :=
  XPC_cast_forall (Univ.El_code ρ σ.2) _ _ _

theorem XPC_holds_ex (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : U.TEnv n) (env : U.Env Γ ρ) :
    XPC_Holds U (Tm.ex σ φ) ρ env ↔ ∃ v : U.CatVal σ.1 ρ,
      XPC_adm U (U.code σ.1 ρ) (cast (Univ.El_code ρ σ.2).symm v) ∧ XPC_Holds U φ ρ (env, v) :=
  XPC_cast_exists (Univ.El_code ρ σ.2) _ _ _

theorem XPC_holds_tall (φ : Fm (.text Γ)) (ρ : U.TEnv n) (env : U.Env Γ ρ) :
    XPC_Holds U (Tm.tall φ) ρ env ↔ ∀ a, XPC_Holds U φ (scons a ρ) env := Iff.rfl
theorem XPC_holds_tex (φ : Fm (.text Γ)) (ρ : U.TEnv n) (env : U.Env Γ ρ) :
    XPC_Holds U (Tm.tex φ) ρ env ↔ ∃ a, XPC_Holds U φ (scons a ρ) env := Iff.rfl
theorem XPC_holds_imp (φ ψ : Fm Γ) (ρ : U.TEnv n) (env : U.Env Γ ρ) :
    XPC_Holds U (φ.imp ψ) ρ env ↔ (XPC_Holds U φ ρ env → XPC_Holds U ψ ρ env) := Iff.rfl
theorem XPC_holds_neg (φ : Fm Γ) (ρ : U.TEnv n) (env : U.Env Γ ρ) :
    XPC_Holds U φ.neg ρ env ↔ ¬ XPC_Holds U φ ρ env := Iff.rfl
theorem XPC_holds_conj (φ ψ : Fm Γ) (ρ : U.TEnv n) (env : U.Env Γ ρ) :
    XPC_Holds U (φ.conj ψ) ρ env ↔ (XPC_Holds U φ ρ env ∧ XPC_Holds U ψ ρ env) := Iff.rfl
theorem XPC_holds_iff (φ ψ : Fm Γ) (ρ : U.TEnv n) (env : U.Env Γ ρ) :
    XPC_Holds U (φ.iff ψ) ρ env ↔ (XPC_Holds U φ ρ env ↔ XPC_Holds U ψ ρ env) := Iff.rfl

theorem XPC_holds_inst {k : Nat} (P : PF k) (as : Fin k → Fm Γ) (ρ : U.TEnv n) (env : U.Env Γ ρ) :
    XPC_Holds U (P.inst as) ρ env ↔ P.evalP (fun i => XPC_Holds U (as i) ρ env) := by
  induction P with
  | atom i => exact Iff.rfl
  | neg P ih => exact not_congr ih
  | imp P Q ihP ihQ => exact imp_congr ihP ihQ
  | conj P Q ihP ihQ => exact and_congr ihP ihQ
  | disj P Q ihP ihQ => exact or_congr ihP ihQ
  | iff P Q ihP ihQ => exact iff_congr ihP ihQ

theorem XPC_eval_eqvConst (σ τ : Ty n) (ρ : U.TEnv n) (env : U.Env Γ ρ) :
    HEq (XPC_eval U (Tm.castK (Tm.eqv_cat σ τ) (Tm.tapp (Tm.tapp (Tm.const (Γ := Γ) Const.eqv) σ) τ)) ρ env)
      (XPC_eqv U (U.code σ.1 ρ) (U.code τ.1 ρ)) := by
  refine (XPC_eval_castK U _ _ _ _).trans ((cast_heq _ _).trans ?_)
  refine heq_dapp (Q := fun b => U.El (U.code σ.1 ρ) → U.El b → Prop) (fun b => ?_)
    (cast_heq _ _) rfl
  refine Univ.CatVal_sub _ _ _ (scons b (scons (U.code σ.1 ρ) ρ)) (fin_cases rfl (fun i => ?_))
  show U.code (((inst σ) i).1.ren fs) (scons b ρ) = _
  rw [Univ.code_ren]
  exact fin_cases (P := fun i => U.code (inst σ i).1 ρ = scons (U.code σ.1 ρ) ρ i) rfl (fun _ => rfl) i

theorem XPC_holds_eqv (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1) (ρ : U.TEnv n) (env : U.Env Γ ρ) :
    XPC_Holds U (Tm.eqv σ τ x y) ρ env ↔
      XPC_eqv U (U.code σ.1 ρ) (U.code τ.1 ρ) (cast (Univ.El_code ρ σ.2).symm (XPC_eval U x ρ env))
        (cast (Univ.El_code ρ τ.2).symm (XPC_eval U y ρ env)) :=
  Iff.of_eq (Frame.app2_heq (A := U.CatVal σ.1 ρ) (B := U.CatVal τ.1 ρ)
    (f := XPC_eval U (Tm.castK (Tm.eqv_cat σ τ) (Tm.tapp (Tm.tapp (Tm.const Const.eqv) σ) τ)) ρ env)
    (Univ.El_code ρ σ.2).symm (Univ.El_code ρ τ.2).symm (XPC_eval_eqvConst U σ τ ρ env) _ _)

theorem XPC_holds_teq (σ τ : Ty n) (ρ : U.TEnv n) (env : U.Env Γ ρ) :
    XPC_Holds U (Tm.teq σ τ) ρ env ↔ U.code σ.1 ρ = U.code τ.1 ρ := by
  have h1 : HEq (XPC_eval U (Tm.tapp (Tm.const (Γ := Γ) Const.teq) σ) ρ env)
      (fun b => U.code σ.1 ρ = b) := XPC_heq_eval_tapp U _ σ ρ env
  have h2 : HEq (XPC_eval U (Tm.teq (Γ := Γ) σ τ) ρ env)
      (XPC_eval U (Tm.tapp (Tm.const (Γ := Γ) Const.teq) σ) ρ env (U.code τ.1 ρ)) :=
    XPC_heq_eval_tapp U _ τ ρ env
  exact Iff.of_eq (eq_of_heq (h2.trans (heq_dapp (Q := fun _ => Prop) (fun _ => rfl) h1 rfl)))

theorem XPC_holds_of_heq {m : Nat} {Δ : Ctx m} {φ : Fm Γ} {ψ : Fm Δ} {ρ : U.TEnv n}
    {ρ' : U.TEnv m} {env : U.Env Γ ρ} {env' : U.Env Δ ρ'}
    (h : HEq (XPC_eval U φ ρ env) (XPC_eval U ψ ρ' env')) : XPC_Holds U φ ρ env = XPC_Holds U ψ ρ' env' :=
  eq_of_heq h

end Holds

theorem XPC_eqv_resp (U : Univ) {a b : Code U.Base} (x x' : U.El a) (y y' : U.El b)
    (hx : XPC_rel U a true x x') (hy : XPC_rel U b true y y') : XPC_eqv U a b x y ↔ XPC_eqv U a b x' y' := by
  constructor
  · rintro ⟨h, hr⟩
    subst h
    exact ⟨rfl, XPC_rel_trans U _ true _ _ _ (XPC_rel_trans U _ true _ _ _ (XPC_rel_symm U _ true _ _ hx) hr) hy⟩
  · rintro ⟨h, hr⟩
    subst h
    exact ⟨rfl, XPC_rel_trans U _ true _ _ _ (XPC_rel_trans U _ true _ _ _ hx hr) (XPC_rel_symm U _ true _ _ hy)⟩

theorem XPC_eqv_symm (U : Univ) {a b : Code U.Base} {x : U.El a} {y : U.El b} :
    XPC_eqv U a b x y → XPC_eqv U b a y x := by
  rintro ⟨h, hr⟩; subst h; exact ⟨rfl, XPC_rel_symm U _ true _ _ hr⟩

theorem XPC_eqv_trans (U : Univ) {a b c : Code U.Base} {x : U.El a} {y : U.El b} {z : U.El c} :
    XPC_eqv U a b x y → XPC_eqv U b c y z → XPC_eqv U a c x z := by
  rintro ⟨h1, r1⟩ ⟨h2, r2⟩; subst h1; subst h2; exact ⟨rfl, XPC_rel_trans U _ true _ _ _ r1 r2⟩

theorem XPC_eqv_same (U : Univ) (a : Code U.Base) (x y : U.El a) :
    XPC_eqv U a a x y ↔ XPC_rel U a true x y :=
  ⟨fun ⟨_, hr⟩ => by rwa [cast_eq] at hr, fun h => ⟨rfl, h⟩⟩

/-! ## 6. The fundamental lemma -/

section Fundamental
variable (U : Univ)

/-- Related values for the term variables of a context. -/
def XPC_EnvRel : {n : Nat} → (Γ : Ctx n) → (ρ : U.TEnv n) → Bool → U.Env Γ ρ → U.Env Γ ρ → Prop
  | _, .nil, _, _ => fun _ _ => True
  | _, .ext Γ σ, ρ, j => fun env env' => XPC_EnvRel Γ ρ j env.1 env'.1 ∧ XPC_Rel U σ.1 ρ j env.2 env'.2
  | _, .text Γ, ρ, j => fun env env' => XPC_EnvRel Γ (fun i => ρ (fs i)) j env env'

/-- An admissible valuation: its values are items. -/
abbrev XPC_EnvAdm {n : Nat} (Γ : Ctx n) (ρ : U.TEnv n) (env : U.Env Γ ρ) : Prop :=
  ∀ k, XPC_EnvRel U Γ ρ k env env

theorem XPC_lookup_rel {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) : ∀ (ρ : U.TEnv n) (j : Bool)
    (env env' : U.Env Γ ρ), XPC_EnvRel U Γ ρ j env env' →
    XPC_Rel U K ρ j (U.lookup x ρ env) (U.lookup x ρ env') := by
  induction x with
  | here => intro ρ j env env' h; exact h.2
  | there y ih => intro ρ j env env' h; exact ih ρ j env.1 env'.1 h.1
  | tthere y ih =>
    intro ρ j env env' h
    refine (XPC_Rel_ren U _ fs ρ (fun i => ρ (fs i)) (fun _ => rfl) j _ _ _ _
      (XPC_lookup_tthere U y ρ env) (XPC_lookup_tthere U y ρ env')).mpr ?_
    exact ih _ j env env' h

theorem XPC_const_rel {n : Nat} {K : Cat n} (c : Const n K) (ρ : U.TEnv n) (j : Bool) :
    XPC_Rel U K ρ j (XPC_constVal U c ρ) (XPC_constVal U c ρ) := by
  cases c with
  | neg => intro p p' _ _ hp hj; exact not_congr (hp hj)
  | imp => intro p p' _ _ hp q q' _ _ hq hj; exact imp_congr (hp hj) (hq hj)
  | and => intro p p' _ _ hp q q' _ _ hq hj; exact and_congr (hp hj) (hq hj)
  | or => intro p p' _ _ hp q q' _ _ hq hj; exact or_congr (hp hj) (hq hj)
  | iff => intro p p' _ _ hp q q' _ _ hq hj; exact iff_congr (hp hj) (hq hj)
  | all =>
    intro a P P' _ _ hP hj
    exact forall_congr' fun x => forall_congr' fun hx => hP x x hx hx (hx j) hj
  | ex =>
    intro a P P' _ _ hP hj
    exact exists_congr fun x => and_congr_right fun hx => hP x x hx hx (hx j) hj
  | tall => intro Q Q' _ _ hQ hj; exact forall_congr' fun a => hQ a hj
  | tex => intro Q Q' _ _ hQ hj; exact exists_congr fun a => hQ a hj
  | eqv =>
    intro a b x x' _ _ hx y y' _ _ hy hj
    subst hj
    exact XPC_eqv_resp U x x' y y' hx hy
  | teq => intro a b _; exact Iff.rfl

/-- **The fundamental lemma**: under admissible valuations related at an index, the values of a
term are related at that index. -/
theorem XPC_fundamental {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) : ∀ (ρ : U.TEnv n) (j : Bool)
    (env env' : U.Env Γ ρ), XPC_EnvAdm U Γ ρ env → XPC_EnvAdm U Γ ρ env' → XPC_EnvRel U Γ ρ j env env' →
    XPC_Rel U K ρ j (XPC_eval U M ρ env) (XPC_eval U M ρ env') := by
  induction M with
  | var x => intro ρ j env env' _ _ h; exact XPC_lookup_rel U x ρ j env env' h
  | const c => intro ρ j _ _ _ _ _; exact XPC_const_rel U c ρ j
  | app f a ihf iha =>
    intro ρ j env env' hA hA' h
    exact ihf ρ j env env' hA hA' h _ _ (fun k => iha ρ k env env hA hA (hA k))
      (fun k => iha ρ k env' env' hA' hA' (hA' k)) (iha ρ j env env' hA hA' h)
  | lam σ b ih =>
    intro ρ j env env' hA hA' h u u' hu hu' huu
    exact ih ρ j (env, u) (env', u') (fun k => ⟨hA k, hu k⟩) (fun k => ⟨hA' k, hu' k⟩) ⟨h, huu⟩
  | tlam b ih =>
    intro ρ j env env' hA hA' h a
    exact ih (scons a ρ) j env env' hA hA' h
  | tapp f σ ih =>
    intro ρ j env env' hA hA' h
    have hf := ih ρ j env env' hA hA' h (U.code σ.1 ρ)
    exact (XPC_Rel_sub U _ (inst σ) ρ (scons (U.code σ.1 ρ) ρ) (fin_cases rfl (fun _ => rfl)) j _ _ _ _
      (XPC_heq_eval_tapp U f σ ρ env) (XPC_heq_eval_tapp U f σ ρ env')).mpr hf

/-- The value of a term, under an admissible valuation, is an item. -/
theorem XPC_adm_eval {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) (ρ : U.TEnv n) (env : U.Env Γ ρ)
    (h : XPC_EnvAdm U Γ ρ env) : ∀ k, XPC_Rel U K ρ k (XPC_eval U M ρ env) (XPC_eval U M ρ env) :=
  fun k => XPC_fundamental U M ρ k env env h h (h k)

theorem XPC_adm_iff {n : Nat} (σ : Ty n) (ρ : U.TEnv n) (v : U.CatVal σ.1 ρ) :
    XPC_adm U (U.code σ.1 ρ) (cast (Univ.El_code ρ σ.2).symm v) ↔ ∀ k, XPC_Rel U σ.1 ρ k v v :=
  forall_congr' fun k =>
    (XPC_Rel_code U σ.1 σ.2 ρ k v v _ _ (cast_heq _ _).symm (cast_heq _ _).symm).symm

end Fundamental


/-! ## 7. Soundness -/

section Soundness
variable (U : Univ)

/-- Pull the values of a renamed context back along the renaming. -/
def XPC_pullEnv : {n : Nat} → (Γ : Ctx n) → {m : Nat} → {r : Fin n → Fin m} → {Δ : Ctx m} →
    TRen r Γ Δ → (ρ' : U.TEnv m) → U.Env Δ ρ' → U.Env Γ (fun i => ρ' (r i))
  | _, .nil, _, _, _, _, _, _ => ()
  | _, .ext Γ σ, _, r, _, ρr, ρ', env' =>
      (XPC_pullEnv Γ (fun x => ρr (.there x)) ρ' env',
       cast (Univ.CatVal_ren σ.1 r ρ' _ (fun _ => rfl)) (U.lookup (ρr .here) ρ' env'))
  | _, .text Γ, _, r, _, ρr, ρ', env' =>
      XPC_pullEnv Γ (r := fun i => r (fs i)) (fun x => Var.castK (Cat.ren_ren _ _ _) (ρr (.tthere x))) ρ' env'

theorem XPC_lookup_pull {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) :
    ∀ {m : Nat} {r : Fin n → Fin m} {Δ : Ctx m} (ρr : TRen r Γ Δ) (ρ' : U.TEnv m) (env' : U.Env Δ ρ'),
      HEq (U.lookup (ρr x) ρ' env') (U.lookup x _ (XPC_pullEnv U Γ ρr ρ' env')) := by
  induction x with
  | here => intro m r Δ ρr ρ' env'; exact (cast_heq _ _).symm
  | there y ih => intro m r Δ ρr ρ' env'; exact ih (fun x => ρr (.there x)) ρ' env'
  | tthere y ih =>
    intro m r Δ ρr ρ' env'
    refine HEq.trans ?_ (XPC_lookup_tthere U y (fun i => ρ' (r i)) (XPC_pullEnv U _ ρr ρ' env')).symm
    exact (XPC_lookup_castK U _ _ _ _).symm.trans
      (ih (r := fun i => r (fs i)) (fun x => Var.castK (Cat.ren_ren _ _ _) (ρr (.tthere x))) ρ' env')

theorem XPC_EnvRel_pull {n : Nat} (Γ : Ctx n) : ∀ {m : Nat} {r : Fin n → Fin m} {Δ : Ctx m}
    (ρr : TRen r Γ Δ) (ρ' : U.TEnv m) (j : Bool) (env1 env2 : U.Env Δ ρ'), XPC_EnvRel U Δ ρ' j env1 env2 →
    XPC_EnvRel U Γ (fun i => ρ' (r i)) j (XPC_pullEnv U Γ ρr ρ' env1) (XPC_pullEnv U Γ ρr ρ' env2) := by
  induction Γ with
  | nil => intros; trivial
  | ext Γ σ ih =>
    intro m r Δ ρr ρ' j env1 env2 h
    refine ⟨ih (fun x => ρr (.there x)) ρ' j env1 env2 h, ?_⟩
    have hl := XPC_lookup_rel U (ρr .here) ρ' j env1 env2 h
    exact (XPC_Rel_ren U σ.1 r ρ' (fun i => ρ' (r i)) (fun _ => rfl) j _ _ _ _
      (cast_heq _ _).symm (cast_heq _ _).symm).mp hl
  | text Γ ih =>
    intro m r Δ ρr ρ' j env1 env2 h
    exact ih (r := fun i => r (fs i)) (fun x => Var.castK (Cat.ren_ren _ _ _) (ρr (.tthere x))) ρ' j env1 env2 h

/-- A formula is valid when it is true under every admissible valuation. -/
def XPC_Valid {n : Nat} {Γ : Ctx n} (φ : Fm Γ) : Prop :=
  ∀ ρ env, XPC_EnvAdm U Γ ρ env → XPC_Holds U φ ρ env

theorem XPC_refEqv : XPC_Valid U RefEqv := by
  intro ρ env _
  refine (XPC_holds_tall U _ _ _).mpr fun a => (XPC_holds_all U _ _ _ _).mpr fun x hx => ?_
  exact (XPC_holds_eqv U _ _ _ _ _ _).mpr ((XPC_eqv_same U _ _ _).mpr (hx true))

theorem XPC_symEqv : XPC_Valid U SymEqv := by
  intro ρ env _
  refine (XPC_holds_tall U _ _ _).mpr fun a => (XPC_holds_tall U _ _ _).mpr fun b => ?_
  refine (XPC_holds_all U _ _ _ _).mpr fun x _ => (XPC_holds_all U _ _ _ _).mpr fun y _ => ?_
  refine (XPC_holds_imp U _ _ _ _).mpr fun h => ?_
  exact (XPC_holds_eqv U _ _ _ _ _ _).mpr (XPC_eqv_symm U ((XPC_holds_eqv U _ _ _ _ _ _).mp h))

theorem XPC_transEqv : XPC_Valid U TransEqv := by
  intro ρ env _
  refine (XPC_holds_tall U _ _ _).mpr fun a => (XPC_holds_tall U _ _ _).mpr fun b =>
    (XPC_holds_tall U _ _ _).mpr fun c => ?_
  refine (XPC_holds_all U _ _ _ _).mpr fun x _ => (XPC_holds_all U _ _ _ _).mpr fun y _ =>
    (XPC_holds_all U _ _ _ _).mpr fun z _ => ?_
  refine (XPC_holds_imp U _ _ _ _).mpr fun h => ?_
  have h1 := (XPC_holds_eqv U (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv2 tv1
    (.var (.there (.there .here))) (.var (.there .here)) (scons c (scons b (scons a ρ))) (((env, x), y), z)).mp h.1
  have h2 := (XPC_holds_eqv U (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv1 tv0
    (.var (.there .here)) (.var .here) (scons c (scons b (scons a ρ))) (((env, x), y), z)).mp h.2
  exact (XPC_holds_eqv U _ _ _ _ _ _).mpr (XPC_eqv_trans U h1 h2)

theorem XPC_refTeq : XPC_Valid U RefTeq := by
  intro ρ env _
  exact (XPC_holds_tall U _ _ _).mpr fun _ => (XPC_holds_teq U _ _ _ _).mpr rfl

theorem XPC_llTeq {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)) : XPC_Valid U (LLTeq Q) := by
  intro ρ env _
  refine (XPC_holds_tall U _ _ _).mpr fun a => (XPC_holds_tall U _ _ _).mpr fun b => ?_
  refine (XPC_holds_imp U _ _ _ _).mpr fun hab => ?_
  have hab' : a = b := (XPC_holds_teq U (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env).mp hab
  subst hab'
  refine (XPC_holds_imp U _ _ _ _).mpr fun hq => ?_
  have e1 : HEq (XPC_eval U (Tm.tapp Q.twk.twk tv1) (scons a (scons a ρ)) env)
      (XPC_eval U Q.twk.twk (scons a (scons a ρ)) env a) :=
    XPC_heq_eval_tapp U (K := Cat.t) Q.twk.twk tv1 (scons a (scons a ρ)) env
  have e2 : HEq (XPC_eval U (Tm.tapp Q.twk.twk tv0) (scons a (scons a ρ)) env)
      (XPC_eval U Q.twk.twk (scons a (scons a ρ)) env a) :=
    XPC_heq_eval_tapp U (K := Cat.t) Q.twk.twk tv0 (scons a (scons a ρ)) env
  exact cast (XPC_holds_of_heq U (e1.trans e2.symm)) hq

/-- **Soundness**: whatever PI⁻ derives from sentences valid in this semantics is valid. -/
theorem XPC_soundness {Ax : Fm Ctx.nil → Prop} (hAx : ∀ φ, Ax φ → XPC_Valid U φ)
    {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : Prov Ax Γ φ) : XPC_Valid U φ := by
  induction h with
  | taut P as hP => intro ρ env _; exact (XPC_holds_inst U P as ρ env).mpr (hP _)
  | instAll σ φ κ =>
    intro ρ env henv h
    show XPC_Holds U (φ.subst0 κ) ρ env
    unfold XPC_Holds; rw [XPC_eval_subst0]
    exact (XPC_holds_all U σ φ ρ env).mp h _ ((XPC_adm_iff U σ ρ _).mpr (XPC_adm_eval U κ ρ env henv))
  | distAll σ φ ψ =>
    intro ρ env _ h hφ
    refine (XPC_holds_all U σ ψ ρ env).mpr fun v hv => ?_
    have h' := (XPC_holds_all U σ _ ρ env).mp h v hv
    have hw : XPC_Holds U (φ.wk σ) ρ (env, v) := by unfold XPC_Holds; rw [XPC_eval_wk]; exact hφ
    exact h' hw
  | dualEx σ φ =>
    intro ρ env _
    refine (XPC_holds_ex U σ φ ρ env).trans ?_
    refine Iff.trans ?_ (not_congr (XPC_holds_all U σ φ.neg ρ env)).symm
    constructor
    · rintro ⟨v, hv, h⟩ h'; exact h' v hv h
    · intro h; exact Classical.byContradiction fun hn => h fun v hv h' => hn ⟨v, hv, h'⟩
  | instTAll φ σ =>
    intro ρ env _ h
    exact cast (eq_of_heq (XPC_eval_tinst U φ σ ρ env)).symm (h (U.code σ.1 ρ))
  | distTAll φ ψ =>
    intro ρ env _ h hφ a
    exact h a (cast (eq_of_heq (XPC_eval_twk U φ a ρ env)).symm hφ)
  | dualTEx φ =>
    intro ρ env _
    show (∃ a, XPC_Holds U φ (scons a ρ) env) ↔ ¬ ∀ a, ¬ XPC_Holds U φ (scons a ρ) env
    constructor
    · rintro ⟨a, ha⟩ h; exact h a ha
    · intro h; exact Classical.byContradiction fun hn => h fun a ha => hn ⟨a, ha⟩
  | beta h => intro ρ env _; exact Iff.of_eq (XPC_eval_betaEq U h ρ env)
  | refEqv => exact XPC_refEqv U
  | symEqv => exact XPC_symEqv U
  | transEqv => exact XPC_transEqv U
  | refTeq => exact XPC_refTeq U
  | llTeq Q => exact XPC_llTeq U Q
  | ax h => exact hAx _ h
  | mp _ _ ih1 ih2 => intro ρ env henv; exact ih2 ρ env henv (ih1 ρ env henv)
  | genAll σ _ ih =>
    intro ρ env henv
    exact (XPC_holds_all U σ _ ρ env).mpr fun v hv =>
      ih ρ (env, v) fun k => ⟨henv k, (XPC_adm_iff U σ ρ v).mp hv k⟩
  | genTAll _ ih => intro ρ env henv a; exact ih (scons a ρ) env henv
  | ren ρr _ ih =>
    intro ρ' env' henv'
    exact cast (XPC_holds_of_heq U (XPC_eval_ren U _ ρr ρ' env' _ (XPC_pullEnv U _ ρr ρ' env') (fun _ => rfl)
      (fun x => XPC_lookup_pull U x ρr ρ' env'))).symm
      (ih _ _ fun k => XPC_EnvRel_pull U _ ρr ρ' k env' env' (henv' k))
  | strengthen σ _ ih =>
    intro ρ env henv
    obtain ⟨v, hv⟩ := XPC_Rel_ne U σ.1 ρ
    have := ih ρ (env, v) fun k => ⟨henv k, hv k⟩
    unfold XPC_Holds at this
    rwa [XPC_eval_wk] at this
  | tstrengthen _ ih =>
    intro ρ env henv
    exact cast (XPC_holds_of_heq U (XPC_eval_twk U _ .e ρ env)) (ih (scons .e ρ) env henv)

/-- `⊥` is not valid. -/
theorem XPC_not_valid_bot : ¬ XPC_Valid U Bot := fun h =>
  (XPC_holds_all U (Γ := Ctx.nil) tyT _ (fun i => i.elim0) ()).mp (h _ () fun _ => trivial) False
    (fun _ _ => Iff.rfl)

end Soundness


/-! ## 8. LL≡, Classicism, PropExt≡, and the principles of identity across types

These hold over every universe. -/

section Principles
variable (U : Univ)

theorem XPC_LLEqv : XPC_Valid U LLEqv := by
  intro ρ env _
  refine (XPC_holds_tall U _ _ _).mpr fun a => ?_
  refine (XPC_holds_all U _ _ _ _).mpr fun x hx => (XPC_holds_all U _ _ _ _).mpr fun y hy => ?_
  refine (XPC_holds_imp U _ _ _ _).mpr fun hxy => ?_
  refine (XPC_holds_all U _ _ _ _).mpr fun G hG => (XPC_holds_imp U _ _ _ _).mpr fun hGx => ?_
  have hxy' : XPC_rel U a true x y := (XPC_eqv_same U _ _ _).mp ((XPC_holds_eqv U _ _ _ _ _ _).mp hxy)
  exact (hG true x y hx hy hxy' rfl).mp hGx

theorem XPC_valid_closeCtx : ∀ {n : Nat} (Γ : Ctx n) (χ : Fm Γ),
    (∀ ρ env, XPC_EnvAdm U Γ ρ env → XPC_Holds U χ ρ env) → XPC_Valid U (closeCtx Γ χ)
  | _, .nil, _, h => h
  | _, .ext Γ σ, χ, h => XPC_valid_closeCtx Γ (Tm.all σ χ) fun ρ env henv =>
      (XPC_holds_all U σ χ ρ env).mpr fun v hv => h ρ (env, v) fun k => ⟨henv k, (XPC_adm_iff U σ ρ v).mp hv k⟩
  | _, .text Γ, χ, h => XPC_valid_closeCtx Γ (Tm.tall χ) fun ρ env henv =>
      (XPC_holds_tall U χ ρ env).mpr fun a => h (scons a ρ) env henv

/-- Every theorem of PI is valid. -/
theorem XPC_sound_PI {n : Nat} {Γ : Ctx n} {θ : Fm Γ} (h : PIP Γ θ) : XPC_Valid U θ :=
  XPC_soundness U (fun χ (e : χ = LLEqv) => e ▸ XPC_LLEqv U) h

/-- **Classicism**: PI-provably equivalent formulas, and properties, are identified. -/
theorem XPC_Class : ∀ χ, ClassSch χ → XPC_Valid U χ := by
  rintro _ (⟨n, Γ, φ, ψ, hp, rfl⟩ | ⟨n, Γ, σ, φ, ψ, hp, rfl⟩)
  · refine XPC_valid_closeCtx U Γ _ fun ρ env henv => ?_
    exact (XPC_holds_eqv U tyT tyT φ ψ ρ env).mpr ⟨rfl, fun _ => XPC_sound_PI U hp ρ env henv⟩
  · refine XPC_valid_closeCtx U Γ _ fun ρ env henv => ?_
    refine (XPC_holds_eqv U σ.pred σ.pred _ _ ρ env).mpr ((XPC_eqv_same U _ _ _).mpr ?_)
    refine (XPC_Rel_code U σ.pred.1 σ.pred.2 ρ true _ _ _ _ (cast_heq _ _).symm (cast_heq _ _).symm).mp ?_
    intro x y hx hy hxy _
    have hf := XPC_fundamental U (Tm.lam σ φ) ρ true env env henv henv (henv true) x y hx hy hxy rfl
    exact hf.trans (XPC_sound_PI U hp ρ (env, y) fun k => ⟨henv k, hy k⟩)

/-- **PropExt≡**: identity of propositions is material equivalence. -/
theorem XPC_PropExt : XPC_Valid U PropExt := by
  intro ρ env _
  refine (XPC_holds_all U _ _ _ _).mpr fun p _ => (XPC_holds_all U _ _ _ _).mpr fun q _ => ?_
  refine (XPC_holds_imp U _ _ _ _).mpr fun h => ?_
  exact (XPC_holds_eqv U _ _ _ _ _ _).mpr ⟨rfl, fun _ => h⟩

theorem XPC_Disjoint : XPC_Valid U Disjoint := by
  intro ρ env _
  refine (XPC_holds_tall U _ _ _).mpr fun a => (XPC_holds_tall U _ _ _).mpr fun b => ?_
  refine (XPC_holds_imp U _ _ _ _).mpr fun hn => ?_
  refine (XPC_holds_all U _ _ _ _).mpr fun x _ => (XPC_holds_all U _ _ _ _).mpr fun y _ => ?_
  refine (XPC_holds_neg U _ _ _).mpr fun he => ?_
  obtain ⟨h, _⟩ := (XPC_holds_eqv U _ _ _ _ _ _).mp he
  exact (XPC_holds_neg U _ _ _).mp hn ((XPC_holds_teq U _ _ _ _).mpr h)

theorem XPC_Slogan : XPC_Valid U Slogan := by
  intro ρ env _
  refine (XPC_holds_all U _ _ _ _).mpr fun x _ => (XPC_holds_tall U _ _ _).mpr fun b => ?_
  refine (XPC_holds_all U _ _ _ _).mpr fun y _ => (XPC_holds_neg U _ _ _).mpr fun he => ?_
  obtain ⟨h, _⟩ := (XPC_holds_eqv U _ _ _ _ _ _).mp he
  have h' : (Code.e : Code U.Base) = .arr b .t := h
  nomatch h'

theorem XPC_Inj : XPC_Valid U Inj := by
  intro ρ env _
  refine (XPC_holds_tall U _ _ _).mpr fun a => (XPC_holds_tall U _ _ _).mpr fun b =>
    (XPC_holds_tall U _ _ _).mpr fun c => (XPC_holds_tall U _ _ _).mpr fun d => ?_
  refine (XPC_holds_imp U _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code U.Base) = .arr b d := (XPC_holds_teq U _ _ _ _).mp h
  exact (XPC_holds_conj U _ _ _ _).mpr ⟨(XPC_holds_teq U _ _ _ _).mpr (Code.arr.inj e).1,
    (XPC_holds_teq U _ _ _ _).mpr (Code.arr.inj e).2⟩

theorem XPC_PCong : XPC_Valid U PCong := by
  intro ρ env _
  refine (XPC_holds_tall U _ _ _).mpr fun a => (XPC_holds_tall U _ _ _).mpr fun c =>
    (XPC_holds_tall U _ _ _).mpr fun d => ?_
  refine (XPC_holds_all U _ _ _ _).mpr fun f _ => (XPC_holds_all U _ _ _ _).mpr fun g _ =>
    (XPC_holds_all U _ _ _ _).mpr fun x hx => ?_
  refine (XPC_holds_imp U _ _ _ _).mpr fun hfg => ?_
  have hfg' : XPC_eqv U (.arr a c) (.arr a d) f g := (XPC_holds_eqv U _ _ _ _ _ _).mp hfg
  obtain ⟨h, _⟩ := id hfg'
  have hcd : c = d := (Code.arr.inj h).2
  subst hcd
  have hr' := (XPC_eqv_same U (.arr a c) f g).mp hfg'
  exact (XPC_holds_eqv U _ _ _ _ _ _).mpr ((XPC_eqv_same U c _ _).mpr (hr' x x hx hx (hx true)))

theorem XPC_PExt : XPC_Valid U PExt := by
  intro ρ env _
  refine (XPC_holds_tall U _ _ _).mpr fun a => (XPC_holds_tall U _ _ _).mpr fun c =>
    (XPC_holds_tall U _ _ _).mpr fun d => ?_
  refine (XPC_holds_all U _ _ _ _).mpr fun f hf => (XPC_holds_all U _ _ _ _).mpr fun g _ => ?_
  refine (XPC_holds_imp U _ _ _ _).mpr fun hall => ?_
  have hpt : ∀ x : U.El a, XPC_adm U a x → XPC_eqv U c d (f x) (g x) := fun x hx =>
    (XPC_holds_eqv U _ _ _ _ _ _).mp ((XPC_holds_all U _ _ _ _).mp hall x hx)
  obtain ⟨x0, hx0⟩ := XPC_adm_ne U a
  obtain ⟨hcd, _⟩ := hpt x0 hx0
  subst hcd
  refine (XPC_holds_eqv U _ _ _ _ _ _).mpr ⟨rfl, ?_⟩
  intro x y hx hy hxy
  exact XPC_rel_trans U _ true _ _ _ (hf true x y hx hy hxy) ((XPC_eqv_same U _ _ _).mp (hpt y hy))

theorem XPC_Cong : XPC_Valid U Cong := by
  intro ρ env _
  refine (XPC_holds_tall U _ _ _).mpr fun a => (XPC_holds_tall U _ _ _).mpr fun b =>
    (XPC_holds_tall U _ _ _).mpr fun c => (XPC_holds_tall U _ _ _).mpr fun d => ?_
  refine (XPC_holds_all U _ _ _ _).mpr fun f _ => (XPC_holds_all U _ _ _ _).mpr fun g _ =>
    (XPC_holds_all U _ _ _ _).mpr fun x hx => (XPC_holds_all U _ _ _ _).mpr fun y hy => ?_
  refine (XPC_holds_imp U _ _ _ _).mpr fun h => ?_
  obtain ⟨h1, h2⟩ := (XPC_holds_conj U _ _ _ _).mp h
  have h1' : XPC_eqv U (.arr a c) (.arr b d) f g := (XPC_holds_eqv U _ _ _ _ _ _).mp h1
  have h2' : XPC_eqv U a b x y := (XPC_holds_eqv U _ _ _ _ _ _).mp h2
  obtain ⟨e1, _⟩ := id h1'
  have hab : a = b := (Code.arr.inj e1).1
  have hcd : c = d := (Code.arr.inj e1).2
  subst hab
  subst hcd
  have r1' := (XPC_eqv_same U (.arr a c) f g).mp h1'
  have r2' := (XPC_eqv_same U a x y).mp h2'
  exact (XPC_holds_eqv U _ _ _ _ _ _).mpr ((XPC_eqv_same U c _ _).mpr (r1' x y hx hy r2'))

end Principles


/-! ## 9. LL≡-Poly and LL≡/≈, for every polymorphic predicate, with parameters -/

section Poly
variable (U : Univ)

theorem XPC_evalP {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : U.TEnv n)
    (env : U.Env Γ ρ) (a b : Code U.Base) (x : U.El a) (y : U.El b) :
    HEq (XPC_eval U ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y)) (XPC_eval U P ρ env) :=
  (heq_of_eq ((XPC_eval_wk U _ _ _ _ _).trans (XPC_eval_wk U _ _ _ _ _))).trans
    ((XPC_eval_twk U P.twk b (scons a ρ) env).trans (XPC_eval_twk U P a ρ env))

theorem XPC_evalP1 {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : U.TEnv n)
    (env : U.Env Γ ρ) (a b : Code U.Base) (x : U.El a) (y : U.El b) :
    XPC_Holds U (.app (.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (.var (.there .here))) (scons b (scons a ρ))
      ((env, x), y) ↔ XPC_eval U P ρ env a x := by
  have h1 : HEq (XPC_eval U (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (scons b (scons a ρ)) ((env, x), y))
      (XPC_eval U P ρ env a) :=
    (XPC_heq_eval_tapp U ((P.twk.twk.wk tv1).wk tv0) tv1 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => U.El c → Prop) (Q := fun c => U.El c → Prop)
        (fun _ => rfl) (XPC_evalP U P ρ env a b x y) rfl)
  exact Iff.of_eq (congrFun (eq_of_heq h1) x)

theorem XPC_evalP0 {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : U.TEnv n)
    (env : U.Env Γ ρ) (a b : Code U.Base) (x : U.El a) (y : U.El b) :
    XPC_Holds U (.app (.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (.var .here)) (scons b (scons a ρ))
      ((env, x), y) ↔ XPC_eval U P ρ env b y := by
  have h1 : HEq (XPC_eval U (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (scons b (scons a ρ)) ((env, x), y))
      (XPC_eval U P ρ env b) :=
    (XPC_heq_eval_tapp U ((P.twk.twk.wk tv1).wk tv0) tv0 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => U.El c → Prop) (Q := fun c => U.El c → Prop)
        (fun _ => rfl) (XPC_evalP U P ρ env a b x y) rfl)
  exact Iff.of_eq (congrFun (eq_of_heq h1) y)

/-- LL≡-Poly holds, for every polymorphic predicate, with parameters. -/
theorem XPC_LLPoly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : XPC_Valid U (LLPoly P) := by
  intro ρ env henv
  refine (XPC_holds_tall U _ _ _).mpr fun a => (XPC_holds_tall U _ _ _).mpr fun b => ?_
  refine (XPC_holds_all U _ _ _ _).mpr fun x hx => (XPC_holds_all U _ _ _ _).mpr fun y hy => ?_
  refine (XPC_holds_imp U _ _ _ _).mpr fun h => (XPC_holds_imp U _ _ _ _).mpr fun hPx => ?_
  have h' : XPC_eqv U a b x y := (XPC_holds_eqv U _ _ _ _ _ _).mp h
  obtain ⟨eab, _⟩ := id h'
  subst eab
  have hxy := (XPC_eqv_same U a x y).mp h'
  have hP := XPC_adm_eval U P ρ env henv true a x y hx hy hxy rfl
  exact (XPC_evalP0 U P ρ env a a x y).mpr (hP.mp ((XPC_evalP1 U P ρ env a a x y).mp hPx))

/-- LL≡/≈ holds, for every polymorphic predicate, with parameters. -/
theorem XPC_Bridge {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : XPC_Valid U (Bridge P) := by
  intro ρ env henv
  refine (XPC_holds_tall U _ _ _).mpr fun a => (XPC_holds_tall U _ _ _).mpr fun b => ?_
  refine (XPC_holds_all U _ _ _ _).mpr fun x hx => (XPC_holds_all U _ _ _ _).mpr fun y hy => ?_
  refine (XPC_holds_imp U _ _ _ _).mpr fun h => (XPC_holds_imp U _ _ _ _).mpr fun hPx => ?_
  have h' : XPC_eqv U a b x y := (XPC_holds_eqv U _ _ _ _ _ _).mp ((XPC_holds_conj U _ _ _ _).mp h).1
  obtain ⟨eab, _⟩ := id h'
  subst eab
  have hxy := (XPC_eqv_same U a x y).mp h'
  have hP := XPC_adm_eval U P ρ env henv true a x y hx hy hxy rfl
  exact (XPC_evalP0 U P ρ env a a x y).mpr (hP.mp ((XPC_evalP1 U P ρ env a a x y).mp hPx))

end Poly

/-! ## 10. The model `𝔐_pe,¬ch`

Two entities. An item of `t → e` sends any two propositions, which are related at the other index,
to equal entities; so it is constant. -/

/-- The universe: entities are booleans, and there are no further base types. -/
def XPC_U : Univ where
  E := Bool
  Base := Empty
  B := fun b => b.elim
  neE := ⟨true⟩
  neB := fun b => b.elim

/-- The relation `R p y`: `y` is `true` just in case `p`. -/
def XPC_R : XPC_U.El (.arr .t (.arr .e .t)) := fun (p : Prop) (y : Bool) => (y = true ↔ p)

theorem XPC_R_adm : XPC_adm XPC_U (.arr .t (.arr .e .t)) XPC_R := by
  intro k p q _ _ hpq y y' _ _ hyy' hk
  have e : y = y' := hyy'
  subst e
  exact iff_congr Iff.rfl (hpq hk)

/-- Every item of `t → e` is constant. -/
theorem XPC_const_of_adm (f : XPC_U.El (.arr .t .e)) (hf : XPC_adm XPC_U (.arr .t .e) f) (p q : Prop) :
    f p = f q :=
  hf false p q (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun h => Bool.noConfusion h)

/-- **Functional Choice fails**: `R` relates every proposition to an entity, but no item of
`t → e` chooses one for each, since such items are constant. -/
theorem XPC_M_not_Choice : ¬ XPC_Valid XPC_U Choice := fun hv => by
  have h := hv (fun i => i.elim0) () (fun _ => trivial)
  have h1 := (XPC_holds_all XPC_U _ _ _ _).mp ((XPC_holds_tall XPC_U _ _ _).mp
    ((XPC_holds_tall XPC_U _ _ _).mp h .t) .e) XPC_R XPC_R_adm
  have h2 := (XPC_holds_imp XPC_U _ _ _ _).mp h1 ((XPC_holds_all XPC_U _ _ _ _).mpr fun p _ => by
    refine (XPC_holds_ex XPC_U _ _ _ _).mpr ?_
    rcases Classical.em (p : Prop) with hp | hp
    · exact ⟨true, fun _ => rfl, show (true = true ↔ p) from ⟨fun _ => hp, fun _ => rfl⟩⟩
    · exact ⟨false, fun _ => rfl,
        show (false = true ↔ p) from ⟨fun e => Bool.noConfusion e, fun h => absurd h hp⟩⟩)
  obtain ⟨f, hf, h3⟩ := (XPC_holds_ex XPC_U _ _ _ _).mp h2
  have hc := XPC_const_of_adm f hf
  have h4 : f True = true ↔ True := (XPC_holds_all XPC_U _ _ _ _).mp h3 True (fun _ _ => Iff.rfl)
  have h5 : f False = true ↔ False := (XPC_holds_all XPC_U _ _ _ _).mp h3 False (fun _ _ => Iff.rfl)
  exact h5.mp ((hc _ _).symm.trans (h4.mpr trivial))


/-! ## 11. The profile of `𝔐_pe,¬ch` -/

/-- **`𝔐_pe,¬ch` is a model of PIᶜ**: every theorem of PI + Classicism is valid. -/
theorem XPC_M_model {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : Prov (fun χ => ClassSch χ ∨ χ = LLEqv) Γ φ) :
    XPC_Valid XPC_U φ :=
  XPC_soundness XPC_U (fun χ hχ => hχ.elim (XPC_Class XPC_U χ) (fun e => e ▸ XPC_LLEqv XPC_U)) h

/-- Whatever PI⁻ derives from sentences valid here is valid here. -/
theorem XPC_M_of_prov {φ : Fm Ctx.nil} (h : Prov (fun χ => XPC_Valid XPC_U χ) Ctx.nil φ) :
    XPC_Valid XPC_U φ :=
  XPC_soundness XPC_U (fun _ h => h) h

theorem XPC_M_LLEqv : XPC_Valid XPC_U LLEqv := XPC_LLEqv XPC_U
theorem XPC_M_Class : ∀ χ, ClassSch χ → XPC_Valid XPC_U χ := XPC_Class XPC_U
theorem XPC_M_PropExt : XPC_Valid XPC_U PropExt := XPC_PropExt XPC_U
theorem XPC_M_Disjoint : XPC_Valid XPC_U Disjoint := XPC_Disjoint XPC_U
theorem XPC_M_Slogan : XPC_Valid XPC_U Slogan := XPC_Slogan XPC_U
theorem XPC_M_Inj : XPC_Valid XPC_U Inj := XPC_Inj XPC_U
theorem XPC_M_PCong : XPC_Valid XPC_U PCong := XPC_PCong XPC_U
theorem XPC_M_PExt : XPC_Valid XPC_U PExt := XPC_PExt XPC_U
theorem XPC_M_Cong : XPC_Valid XPC_U Cong := XPC_Cong XPC_U
theorem XPC_M_LLPoly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) :
    XPC_Valid XPC_U (LLPoly P) := XPC_LLPoly XPC_U P
theorem XPC_M_Bridge {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) :
    XPC_Valid XPC_U (Bridge P) := XPC_Bridge XPC_U P

theorem XPC_M_Collapse : XPC_Valid XPC_U Collapse := XPC_M_of_prov (d_Collapse_of_PropExt XPC_M_PropExt)
theorem XPC_M_NIX : XPC_Valid XPC_U NIX := XPC_M_of_prov (d_NIX_of_Collapse XPC_M_Collapse)
theorem XPC_M_NDX : XPC_Valid XPC_U NDX := XPC_M_of_prov (d_NDX_of_Collapse XPC_M_Collapse)
theorem XPC_M_NIEqv : XPC_Valid XPC_U NIEqv := XPC_M_of_prov (d_NIEqv_of_Collapse XPC_M_Collapse)
theorem XPC_M_NITeq : XPC_Valid XPC_U NITeq := XPC_M_of_prov (d_NITeq_of_Collapse XPC_M_Collapse)
theorem XPC_M_NDTeq : XPC_Valid XPC_U NDTeq := XPC_M_of_prov (d_NDTeq_of_Collapse XPC_M_Collapse)
theorem XPC_M_Bool : ∀ φ, BoolSch φ → XPC_Valid XPC_U φ := fun φ h =>
  XPC_M_of_prov (d_Bool_of_PropExt XPC_M_PropExt φ h)
theorem XPC_M_IdId : XPC_Valid XPC_U IdId := XPC_M_of_prov (d_IdId_of_PropExt XPC_M_PropExt XPC_M_LLEqv)
theorem XPC_M_TBF : ∀ χ, TBFSch χ → XPC_Valid XPC_U χ := fun χ h =>
  XPC_M_of_prov (d_TBF_of_PropExt XPC_M_PropExt χ h)
theorem XPC_M_TCBF : ∀ χ, TCBFSch χ → XPC_Valid XPC_U χ := fun χ h =>
  XPC_M_of_prov (d_TCBF_of_PropExt XPC_M_PropExt χ h)
theorem XPC_M_TNec : XPC_Valid XPC_U TNec := XPC_M_of_prov (d_TNec XPC_M_Collapse)
theorem XPC_M_Truth : XPC_Valid XPC_U Truth := XPC_M_of_prov (Derive.d_Truth XPC_M_LLEqv)
theorem XPC_M_TopBot : XPC_Valid XPC_U TopBot := XPC_M_of_prov (Derive.d_TopBot XPC_M_LLEqv)
theorem XPC_M_Cantor : XPC_Valid XPC_U Cantor := XPC_M_of_prov (Derive.d_Cantor XPC_M_LLEqv)
theorem XPC_M_WCong : XPC_Valid XPC_U WCong := XPC_M_of_prov (Derive.d_WCong XPC_M_LLEqv)
theorem XPC_M_TAx : XPC_Valid XPC_U TAx := XPC_M_of_prov (d_TAx_of_Truth XPC_M_Truth)
theorem XPC_M_BF : XPC_Valid XPC_U BF := XPC_M_of_prov (d_BF_of_Collapse XPC_M_Collapse XPC_M_TAx)
theorem XPC_M_CBF : XPC_Valid XPC_U CBF := XPC_M_of_prov (d_CBF_of_Collapse XPC_M_Collapse XPC_M_TAx)
theorem XPC_M_Nec : XPC_Valid XPC_U Nec := XPC_M_of_prov (d_Nec_of_Collapse XPC_M_Collapse)
theorem XPC_M_Recovery : XPC_Valid XPC_U Recovery := XPC_M_of_prov (Derive.d_Recovery XPC_M_Inj)
theorem XPC_M_ExtT : XPC_Valid XPC_U ExtT := XPC_M_of_prov (Derive.d_ExtT_of_Disjoint XPC_M_Disjoint)
theorem XPC_M_IntT : XPC_Valid XPC_U IntT := XPC_M_of_prov (Derive.d_IntT_of_ExtT XPC_M_LLEqv XPC_M_ExtT)

/-- Twin fails: with Disjoint it is inconsistent. -/
theorem XPC_M_not_Twin : ¬ XPC_Valid XPC_U Twin := fun hT =>
  XPC_not_valid_bot XPC_U (XPC_M_of_prov (Derive.d_Twin_Disjoint hT XPC_M_Disjoint))

/-- Haecceitism fails: with Disjoint it is inconsistent. -/
theorem XPC_M_not_Hae : ¬ XPC_Valid XPC_U Hae := fun hH =>
  XPC_not_valid_bot XPC_U (XPC_M_of_prov (d_Hae_Disjoint hH XPC_M_Disjoint))

/-- **PIᶜ together with PropExt≡ does not prove Functional Choice.** -/
theorem XPC_PIc_PropExt_not_Choice :
    ¬ Prov (fun χ => ClassSch χ ∨ χ = LLEqv ∨ χ = PropExt) Ctx.nil Choice := fun h =>
  XPC_M_not_Choice (XPC_soundness XPC_U (fun χ hχ => hχ.elim (XPC_Class XPC_U χ)
    (fun h' => h'.elim (fun e => e ▸ XPC_LLEqv XPC_U) (fun e => e ▸ XPC_PropExt XPC_U))) h)

end PIF
