import PIBF
set_option autoImplicit false

/-!
# `𝔐_swap`: LL≡-Poly and PCong without Cong, in PI⁻

Two entities, `E = {true, false}`; no further base types. `≈` is identity of types. The two
entities are identified with each other; every other item is identified only with itself.

The swap of the two entities lifts to every type (identity at `t`, conjugation at `→`), and `≡`
and `≈` are invariant under it. So no sentence tells the two entities apart, and every closed
instance of LL≡-Poly is true. That is proved here by a variant of the invariance lemma of
`PIFoundation.lean` in which the logical relation at `e` is a given relation (the graph of the
swap) rather than identity. Instances of LL≡-Poly with free variables can fail, since a free
variable may name a property that tells the two entities apart (`Mswap_not_LLPoly_open`).

PCong holds, since functions are identified only with themselves; Cong fails: `λz.(z = true)`
is identified with itself and `true ≡ false`, but `true = true` and `false = true` are distinct
propositions.
-/

namespace PIF

/-! ## Invariance with a relation at `e` -/

namespace SwInv

/-- A family of admissible relations for a frame, with a relation `RE` between entities, which
need not be identity. Unlike `Invariance`, identity need not be admissible. -/
structure InvB (F : Frame) where
  RE : F.U.E → F.U.E → Prop
  Adm : (a a' : Code F.U.Base) → (F.U.El a → F.U.El a' → Prop) → Prop
  admE : Adm .e .e RE
  admT : Adm .t .t (fun p q => (p ↔ q))
  some : ∀ a, ∃ R, Adm a a R
  arrow : ∀ {a a' c c' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop} {S : F.U.El c → F.U.El c' → Prop},
    Adm a a' R → Adm c c' S → Adm (.arr a c) (.arr a' c') (fun f f' => ∀ u u', R u u' → S (f u) (f' u'))
  total : ∀ {a a' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop}, Adm a a' R → ∀ u, ∃ u', R u u'
  onto : ∀ {a a' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop}, Adm a a' R → ∀ u', ∃ u, R u u'
  teq : ∀ {a a' b b' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop} {S : F.U.El b → F.U.El b' → Prop},
    Adm a a' R → Adm b b' S → (F.teq a b ↔ F.teq a' b')
  eqv : ∀ {a a' b b' : Code F.U.Base} {R : F.U.El a → F.U.El a' → Prop} {S : F.U.El b → F.U.El b' → Prop},
    Adm a a' R → Adm b b' S → ∀ u u' v v', R u u' → S v v' → (F.eqv a b u v ↔ F.eqv a' b' u' v')

namespace InvB
variable {F : Frame} (I : InvB F)

/-- The logical relation at each category: `RE` at `e`, `↔` at `t`, the given relations at type
variables, preservation at `→`, and preservation under every admissible relation at `Π`. -/
def Rel : {n : Nat} → (K : Cat n) → (ρ ρ' : F.U.TEnv n) → (∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) →
    F.U.CatVal K ρ → F.U.CatVal K ρ' → Prop
  | _, .e, _, _, _ => I.RE
  | _, .t, _, _, _ => fun p q => (p ↔ q)
  | _, .var i, _, _, Rs => Rs i
  | _, .arr K L, ρ, ρ', Rs => fun f f' => ∀ u u', Rel K ρ ρ' Rs u u' → Rel L ρ ρ' Rs (f u) (f' u')
  | _, .pi K, ρ, ρ', Rs => fun G G' => ∀ a a' (R : F.U.El a → F.U.El a' → Prop), I.Adm a a' R →
      Rel K (scons a ρ) (scons a' ρ') (Invariance.RScons R Rs) (G a) (G' a')

/-- The same relation at a type, on the sets its code names. -/
def RelE {n : Nat} : (K : Cat n) → (ρ ρ' : F.U.TEnv n) → (∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) →
    F.U.El (F.U.code K ρ) → F.U.El (F.U.code K ρ') → Prop
  | .e, _, _, _ => I.RE
  | .t, _, _, _ => fun p q => (p ↔ q)
  | .var i, _, _, Rs => Rs i
  | .arr K L, ρ, ρ', Rs => fun f f' => ∀ x x', RelE K ρ ρ' Rs x x' → RelE L ρ ρ' Rs (f x) (f' x')
  | .pi _, _, _, _ => fun x y => x = y

theorem adm_RelE {n : Nat} (K : Cat n) : ∀ (ρ ρ' : F.U.TEnv n) (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop),
    (∀ i, I.Adm (ρ i) (ρ' i) (Rs i)) → K.Simple →
    I.Adm (F.U.code K ρ) (F.U.code K ρ') (I.RelE K ρ ρ' Rs) := by
  induction K with
  | e => intros; exact I.admE
  | t => intros; exact I.admT
  | var i => intro ρ ρ' Rs hRs _; exact hRs i
  | arr a b iha ihb => intro ρ ρ' Rs hRs hK; exact I.arrow (iha ρ ρ' Rs hRs hK.1) (ihb ρ ρ' Rs hRs hK.2)
  | pi _ _ => intro _ _ _ _ hK; exact hK.elim

theorem Rel_RelE {n : Nat} (K : Cat n) : ∀ (_ : K.Simple) (ρ ρ' : F.U.TEnv n)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) (u : F.U.CatVal K ρ) (u' : F.U.CatVal K ρ')
    (x : F.U.El (F.U.code K ρ)) (x' : F.U.El (F.U.code K ρ')), HEq u x → HEq u' x' →
    (I.Rel K ρ ρ' Rs u u' ↔ I.RelE K ρ ρ' Rs x x') := by
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

theorem Rel_ren {n : Nat} (K : Cat n) : ∀ {m : Nat} (r : Fin n → Fin m) (ρ ρ' : F.U.TEnv m)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) (ρ₂ ρ₂' : F.U.TEnv n)
    (Rs₂ : ∀ i, F.U.El (ρ₂ i) → F.U.El (ρ₂' i) → Prop)
    (_ : ∀ i, ρ (r i) = ρ₂ i) (_ : ∀ i, ρ' (r i) = ρ₂' i)
    (_ : ∀ i x x' y y', HEq x y → HEq x' y' → (Rs (r i) x x' ↔ Rs₂ i y y'))
    (v : F.U.CatVal (K.ren r) ρ) (v' : F.U.CatVal (K.ren r) ρ') (w : F.U.CatVal K ρ₂) (w' : F.U.CatVal K ρ₂'),
    HEq v w → HEq v' w' → (I.Rel (K.ren r) ρ ρ' Rs v v' ↔ I.Rel K ρ₂ ρ₂' Rs₂ w w') := by
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
    refine ih (liftR r) (scons a ρ) (scons a' ρ') (Invariance.RScons R Rs) (scons a ρ₂) (scons a' ρ₂')
      (Invariance.RScons R Rs₂) (fin_cases rfl (fun i => hρ i)) (fin_cases rfl (fun i => hρ' i)) ?_ _ _ _ _ ?_ ?_
    · refine fin_cases ?_ (fun i => fun x x' y y' hx hx' => hR i x x' y y' hx hx')
      intro x x' y y' hx hx'; cases hx; cases hx'; exact Iff.rfl
    · exact heq_dapp (fun a => Univ.CatVal_ren K (liftR r) (scons a ρ) (scons a ρ₂)
        (fin_cases rfl (fun i => hρ i))) hv rfl
    · exact heq_dapp (fun a => Univ.CatVal_ren K (liftR r) (scons a ρ') (scons a ρ₂')
        (fin_cases rfl (fun i => hρ' i))) hv' rfl

theorem Rel_sub {n : Nat} (K : Cat n) : ∀ {m : Nat} (s : Fin n → Ty m) (ρ ρ' : F.U.TEnv m)
    (Rs : ∀ i, F.U.El (ρ i) → F.U.El (ρ' i) → Prop) (ρ₂ ρ₂' : F.U.TEnv n)
    (Rs₂ : ∀ i, F.U.El (ρ₂ i) → F.U.El (ρ₂' i) → Prop)
    (_ : ∀ i, F.U.code (s i).1 ρ = ρ₂ i) (_ : ∀ i, F.U.code (s i).1 ρ' = ρ₂' i)
    (_ : ∀ i (x : F.U.CatVal (s i).1 ρ) (x' : F.U.CatVal (s i).1 ρ') y y', HEq x y → HEq x' y' →
      (I.Rel (s i).1 ρ ρ' Rs x x' ↔ Rs₂ i y y'))
    (v : F.U.CatVal (K.sub s) ρ) (v' : F.U.CatVal (K.sub s) ρ') (w : F.U.CatVal K ρ₂) (w' : F.U.CatVal K ρ₂'),
    HEq v w → HEq v' w' → (I.Rel (K.sub s) ρ ρ' Rs v v' ↔ I.Rel K ρ₂ ρ₂' Rs₂ w w') := by
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
    refine ih (liftT s) (scons a ρ) (scons a' ρ') (Invariance.RScons R Rs) (scons a ρ₂) (scons a' ρ₂')
      (Invariance.RScons R Rs₂) (hl a ρ ρ₂ hρ) (hl a' ρ' ρ₂' hρ') ?_ _ _ _ _ ?_ ?_
    · refine fin_cases ?_ (fun i => ?_)
      · intro x x' y y' hx hx'; cases hx; cases hx'; exact Iff.rfl
      · intro x x' y y' hx hx'
        refine (I.Rel_ren (s i).1 fs (scons a ρ) (scons a' ρ') (Invariance.RScons R Rs) ρ ρ' Rs (fun _ => rfl)
          (fun _ => rfl) (fun j z z' q q' hz hz' => by cases hz; cases hz'; exact Iff.rfl)
          x x' (cast (Univ.CatVal_ren (s i).1 fs (scons a ρ) ρ (fun _ => rfl)) x)
          (cast (Univ.CatVal_ren (s i).1 fs (scons a' ρ') ρ' (fun _ => rfl)) x')
          (cast_heq _ _).symm (cast_heq _ _).symm).trans ?_
        exact hR i _ _ y y' ((cast_heq _ _).trans hx) ((cast_heq _ _).trans hx')
    · exact heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ) (scons a ρ₂) (hl a ρ ρ₂ hρ)) hv rfl
    · exact heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ') (scons a ρ₂') (hl a ρ' ρ₂' hρ')) hv' rfl

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
    constructor
    · intro h a; obtain ⟨R, hR⟩ := I.some a; exact (hQ a a R hR).mp (h a)
    · intro h a; obtain ⟨R, hR⟩ := I.some a; exact (hQ a a R hR).mpr (h a)
  | tex =>
    intro Q Q' hQ
    constructor
    · rintro ⟨a, h⟩; obtain ⟨R, hR⟩ := I.some a; exact ⟨a, (hQ a a R hR).mp h⟩
    · rintro ⟨a, h⟩; obtain ⟨R, hR⟩ := I.some a; exact ⟨a, (hQ a a R hR).mpr h⟩
  | eqv =>
    intro a a' R hR b b' S hS u u' hu v v' hv
    exact I.eqv hR hS u u' v v' hu hv
  | teq =>
    intro a a' R hR b b' S hS
    exact I.teq hR hS

/-- **The fundamental lemma**, with a relation at `e`: every term is related to itself, under
related values for its variables. -/
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
    exact ih (scons a ρ) (scons a' ρ') (Invariance.RScons R Rs) (fin_cases hR (fun i => hRs i)) env env' h
  | tapp f σ ih =>
    intro ρ ρ' Rs hRs env env' h
    have hf := ih ρ ρ' Rs hRs env env' h (F.U.code σ.1 ρ) (F.U.code σ.1 ρ') (I.RelE σ.1 ρ ρ' Rs)
      (I.adm_RelE σ.1 ρ ρ' Rs hRs σ.2)
    refine (I.Rel_sub _ (inst σ) ρ ρ' Rs (scons (F.U.code σ.1 ρ) ρ) (scons (F.U.code σ.1 ρ') ρ')
      (Invariance.RScons (I.RelE σ.1 ρ ρ' Rs) Rs) (fin_cases rfl (fun _ => rfl)) (fin_cases rfl (fun _ => rfl)) ?_
      _ _ _ _ (F.heq_eval_tapp f σ ρ env) (F.heq_eval_tapp f σ ρ' env')).mpr hf
    refine fin_cases ?_ (fun i => ?_)
    · intro x x' y y' hx hx'; exact I.Rel_RelE σ.1 σ.2 ρ ρ' Rs x x' y y' hx hx'
    · intro x x' y y' hx hx'; cases hx; cases hx'; exact Iff.rfl

/-- **Closed instances of LL≡-Poly hold** in a frame with such a family of admissible relations,
if any two identified items are either the same item or related by some admissible relation. -/
theorem llPoly_closed (hE : ∀ a b u v, F.eqv a b u v → (a = b ∧ HEq u v) ∨ ∃ R, I.Adm a b R ∧ R u v)
    (P : Tm Ctx.nil (.pi (.arr (.var fz) .t))) : F.Valid (LLPoly P) := by
  intro ρ env a b
  refine (F.holds_all _ _ _ _).mpr fun x => (F.holds_all _ _ _ _).mpr fun y => ?_
  intro hxy hPx
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
  rcases hE a b _ _ ((F.holds_eqv _ _ _ _ _ _).mp hxy) with ⟨hab, hxy'⟩ | ⟨R, hR, hRxy⟩
  · subst hab
    have e : x = y := eq_of_heq hxy'
    subst e
    exact hPx'
  · have hrel := I.fundamental P ρ ρ (fun i => i.elim0) (fun i => i.elim0) env env trivial a b R hR _ _ hRxy
    exact hrel.mp hPx'

end InvB

end SwInv

/-! ## The model -/

section Mswap
open Tm

/-- Two entities, and no further base types. -/
def univSw : Univ where
  E := Bool
  Base := Empty
  B := fun b => b.elim
  neE := ⟨true⟩
  neB := fun b => b.elim

/-- The swap of the two entities, lifted to every type: identity at `t`, conjugation at `→`. -/
def swc : (c : Code Empty) → univSw.El c → univSw.El c
  | .e => fun x => (Bool.not x : Bool)
  | .t => fun p => p
  | .base b => b.elim
  | .arr a c => fun f x => swc c (f (swc a x))

theorem swc_swc : ∀ (c : Code Empty) (x : univSw.El c), swc c (swc c x) = x
  | .e, x => Bool.not_not x
  | .t, _ => rfl
  | .base b, _ => b.elim
  | .arr a c, f => funext fun x => by
      show swc c (swc c (f (swc a (swc a x)))) = f x
      rw [swc_swc a x, swc_swc c]

/-- The items identified with something other than themselves: the two entities. -/
def swC (p : Σ c : Code Empty, univSw.El c) : Prop := p.1 = .e

def MswapD : IdentData where
  U := univSw
  rel := fun p q => p = q ∨ (swC p ∧ swC q)
  refl := fun _ => Or.inl rfl
  symm := fun h => h.elim (fun e => Or.inl e.symm) (fun ⟨a, b⟩ => Or.inr ⟨b, a⟩)
  trans := by
    rintro p q r (rfl | ⟨_, hq⟩) (rfl | ⟨hq', hr⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hq', hr⟩
    · exact Or.inr ⟨by assumption, hq⟩
    · exact Or.inr ⟨by assumption, hr⟩

abbrev Mswap : Frame := MswapD.frame

theorem Mswap_model : Mswap.IsModelPIm := MswapD.model

theorem Mswap_sigma_iff {a : Code Empty} (u v : univSw.El a) :
    (⟨a, u⟩ : Σ c : Code Empty, univSw.El c) = ⟨a, v⟩ ↔ u = v :=
  ⟨fun h => eq_of_heq (Sigma.mk.inj h).2, fun h => h ▸ rfl⟩

/-- Identified items have the same type. -/
theorem Mswap_eqv_teq {a b : Code Empty} {u : univSw.El a} {v : univSw.El b} (h : Mswap.eqv a b u v) : a = b := by
  rcases h with h | ⟨ha, hb⟩
  · exact congrArg Sigma.fst h
  · exact (show a = .e from ha).trans (show b = .e from hb).symm

/-- Away from `e`, identification is identity. -/
theorem Mswap_eqv_ne {a b : Code Empty} {u : univSw.El a} {v : univSw.El b} (hne : a ≠ .e)
    (h : Mswap.eqv a b u v) : (⟨a, u⟩ : Σ c : Code Empty, univSw.El c) = ⟨b, v⟩ := by
  rcases h with h | ⟨ha, _⟩
  · exact h
  · exact absurd ha hne

theorem Mswap_eqv_t (p q : Prop) : Mswap.eqv .t .t p q ↔ p = q :=
  ⟨fun h => (Mswap_sigma_iff (a := .t) p q).mp (Mswap_eqv_ne (fun h => by cases h) h),
   fun h => h ▸ Or.inl rfl⟩

/-- `≡` is invariant under the swap. -/
theorem Mswap_eqv_swc (a b : Code Empty) (u : univSw.El a) (v : univSw.El b) :
    Mswap.eqv a b u v ↔ Mswap.eqv a b (swc a u) (swc b v) := by
  show (_ ∨ _) ↔ (_ ∨ _)
  refine or_congr ?_ Iff.rfl
  by_cases hab : a = b
  · subst hab
    refine (Mswap_sigma_iff u v).trans (Iff.trans ?_ (Mswap_sigma_iff (swc a u) (swc a v)).symm)
    exact ⟨fun h => h ▸ rfl,
      fun h => (swc_swc a u).symm.trans ((congrArg (swc a) h).trans (swc_swc a v))⟩
  · exact ⟨fun h => absurd (congrArg Sigma.fst h) hab, fun h => absurd (congrArg Sigma.fst h) hab⟩

/-- Admissible relations: the graph of the swap, at each type. -/
def MswapI : SwInv.InvB Mswap where
  RE := fun x y => swc .e x = y
  Adm := fun a a' R => ∃ _ : a = a', ∀ x y, R x y ↔ HEq (swc a x) y
  admE := ⟨rfl, fun _ _ => ⟨heq_of_eq, eq_of_heq⟩⟩
  admT := ⟨rfl, fun _ _ => ⟨fun h => heq_of_eq (propext h), fun h => Iff.of_eq (eq_of_heq h)⟩⟩
  some := fun _ => ⟨_, rfl, fun _ _ => Iff.rfl⟩
  arrow := by
    rintro a a' c c' R S ⟨rfl, hR⟩ ⟨rfl, hS⟩
    refine ⟨rfl, fun f f' => ⟨fun h => heq_of_eq (funext fun x => ?_), fun h u u' hu => ?_⟩⟩
    · show swc c (f (swc a x)) = f' x
      exact eq_of_heq ((hS _ _).mp (h (swc a x) x ((hR _ _).mpr (heq_of_eq (swc_swc a x)))))
    · have e := eq_of_heq h
      have e2 := eq_of_heq ((hR u u').mp hu)
      subst e; subst e2
      refine (hS _ _).mpr (heq_of_eq ?_)
      show swc c (f u) = swc c (f (swc a (swc a u)))
      exact congrArg (fun z => swc c (f z)) (swc_swc a u).symm
  total := by
    rintro a a' R ⟨rfl, hR⟩ u
    exact ⟨swc a u, (hR _ _).mpr HEq.rfl⟩
  onto := by
    rintro a a' R ⟨rfl, hR⟩ u
    exact ⟨swc a u, (hR _ _).mpr (heq_of_eq (swc_swc a u))⟩
  teq := by
    rintro a a' b b' R S ⟨rfl, -⟩ ⟨rfl, -⟩
    exact Iff.rfl
  eqv := by
    rintro a a' b b' R S ⟨rfl, hR⟩ ⟨rfl, hS⟩ u u' v v' hu hv
    have e1 := eq_of_heq ((hR _ _).mp hu)
    have e2 := eq_of_heq ((hS _ _).mp hv)
    subst e1; subst e2
    exact Mswap_eqv_swc a b u v

/-- **Every closed instance of LL≡-Poly is true**: identified items are either the same item, or
the two entities, which the swap exchanges. -/
theorem Mswap_LLPoly (P : Tm Ctx.nil (.pi (.arr (.var fz) .t))) : Mswap.Valid (LLPoly P) :=
  MswapI.llPoly_closed (fun a b u v h => by
    rcases h with h | ⟨ha, hb⟩
    · exact Or.inl ⟨congrArg Sigma.fst h, (Sigma.mk.inj h).2⟩
    · change a = .e at ha
      change b = .e at hb
      subst ha; subst hb
      revert u v
      show ∀ u v : Bool, _
      intro u v
      cases u <;> cases v
      · exact Or.inl ⟨rfl, HEq.rfl⟩
      · exact Or.inr ⟨_, ⟨rfl, fun _ _ => Iff.rfl⟩, HEq.rfl⟩
      · exact Or.inr ⟨_, ⟨rfl, fun _ _ => Iff.rfl⟩, HEq.rfl⟩
      · exact Or.inl ⟨rfl, HEq.rfl⟩) P

/-- Every closed instance of LL≡/≈ is true: LL≡-Poly proves it, instance by instance. -/
theorem Mswap_Bridge (P : Tm Ctx.nil (.pi (.arr (.var fz) .t))) : Mswap.Valid (Bridge P) :=
  Mswap.soundness Mswap_model (Ax := (· = LLPoly P)) (fun _ h => h ▸ Mswap_LLPoly P)
    (d_Bridge_of_LLPoly (S := (· = LLPoly P)) P rfl)

/-! ### An instance of LL≡-Poly with a free variable fails -/

/-- The context `G0 : e→t`. -/
abbrev ΓG0 : Ctx 0 := Ctx.nil.ext tyE.pred

/-- `λγ.λx:γ.∀_{γ→t}F (F ≡_{γ→t,e→t} G0 → F x)`: at `γ = e`, this is `G0` itself. -/
def PG0 : Tm ΓG0 (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (all tv0.pred (imp (eqv tv0.pred tyE.pred (.var .here) (.var (.there (.there (.tthere .here)))))
    (.app (.var .here) (.var (.there .here))))))

theorem Mswap_holds_PG0 (G0 : Bool → Prop) :
    Mswap.Holds (LLPoly PG0) (fun i => i.elim0) ((), G0) ↔
      ∀ (a b : Code Empty) (x : univSw.El a) (y : univSw.El b), Mswap.eqv a b x y →
        (∀ F : univSw.El a → Prop, Mswap.eqv (.arr a .t) (.arr .e .t) F G0 → F x) →
        (∀ F : univSw.El b → Prop, Mswap.eqv (.arr b .t) (.arr .e .t) F G0 → F y) := Iff.rfl

/-- **LL≡-Poly with a free variable fails**: with `G0 := λz.(z = true)`, `P_e` is `G0`, which holds
of `true` but not of `false`, although `true ≡ false`. -/
theorem Mswap_not_LLPoly_open : ¬ Mswap.Valid (LLPoly PG0) := fun h => by
  have h1 := (Mswap_holds_PG0 (fun z => z = true)).mp (h (fun i => i.elim0) ((), fun z => z = true))
    .e .e true false (Or.inr ⟨rfl, rfl⟩)
    (fun F hF => by
      have e : F = (fun z => z = true) :=
        (Mswap_sigma_iff (a := .arr .e .t) F _).mp (Mswap_eqv_ne (fun h => by cases h) hF)
      subst e
      exact rfl)
    (fun z => z = true) (Or.inl rfl)
  exact Bool.noConfusion (h1 : false = true)

theorem Mswap_holds_BridgePG0 (G0 : Bool → Prop) :
    Mswap.Holds (Bridge PG0) (fun i => i.elim0) ((), G0) ↔
      ∀ (a b : Code Empty) (x : univSw.El a) (y : univSw.El b), Mswap.eqv a b x y ∧ a = b →
        (∀ F : univSw.El a → Prop, Mswap.eqv (.arr a .t) (.arr .e .t) F G0 → F x) →
        (∀ F : univSw.El b → Prop, Mswap.eqv (.arr b .t) (.arr .e .t) F G0 → F y) := Iff.rfl

/-- So does the same instance of LL≡/≈, since `true` and `false` have the same type. -/
theorem Mswap_not_Bridge_open : ¬ Mswap.Valid (Bridge PG0) := fun h => by
  have h1 := (Mswap_holds_BridgePG0 (fun z => z = true)).mp (h (fun i => i.elim0) ((), fun z => z = true))
    .e .e true false ⟨Or.inr ⟨rfl, rfl⟩, rfl⟩
    (fun F hF => by
      have e : F = (fun z => z = true) :=
        (Mswap_sigma_iff (a := .arr .e .t) F _).mp (Mswap_eqv_ne (fun h => by cases h) hF)
      subst e
      exact rfl)
    (fun z => z = true) (Or.inl rfl)
  exact Bool.noConfusion (h1 : false = true)

/-! ### The other principles -/

theorem Mswap_Inj : Mswap.Valid Inj := MswapD.Inj_valid

theorem Mswap_Disjoint : Mswap.Valid Disjoint :=
  (Mswap.valid_iff_tr _).mpr <| Mswap.tr_Disjoint.mpr fun _ _ hab _ _ h => hab (Mswap_eqv_teq h)

/-- PCong holds: functions are identified only with themselves. -/
theorem Mswap_PCong : Mswap.Valid PCong :=
  (Mswap.valid_iff_tr _).mpr <| Mswap.tr_PCong.mpr fun a c d f g x h => by
    have e := Mswap_eqv_ne (fun h => by cases h) h
    have e1 : Code.arr a c = Code.arr a d := congrArg Sigma.fst e
    injection e1 with _ hcd
    subst hcd
    have hfg : f = g := eq_of_heq (Sigma.mk.inj e).2
    subst hfg
    exact Or.inl rfl

/-- Cong fails: `λz.(z = true)` is identified with itself, and `true ≡ false`, but
`true = true` and `false = true` are distinct propositions. -/
theorem Mswap_not_Cong : ¬ Mswap.Valid Cong := fun h => by
  have := Mswap.tr_Cong.mp ((Mswap.valid_iff_tr _).mp h) .e .e .t .t (fun z => z = true) (fun z => z = true)
    true false ⟨Or.inl rfl, Or.inr ⟨rfl, rfl⟩⟩
  have e := (Mswap_eqv_t _ _).mp this
  exact Bool.noConfusion (cast e rfl : false = true)

theorem Mswap_not_WCong : ¬ Mswap.Valid WCong := fun h => by
  have := Mswap.tr_WCong.mp ((Mswap.valid_iff_tr _).mp h) .e .e .t .t (fun z => z = true) (fun z => z = true)
    true false ⟨⟨rfl, rfl⟩, ⟨Or.inl rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
  have e := (Mswap_eqv_t _ _).mp this
  exact Bool.noConfusion (cast e rfl : false = true)

theorem Mswap_not_LLEqv : ¬ Mswap.Valid LLEqv := fun h => by
  have := Mswap.tr_LLEqv.mp ((Mswap.valid_iff_tr _).mp h) .e true false (Or.inr ⟨rfl, rfl⟩) (fun z => z = true) rfl
  exact Bool.noConfusion (this : false = true)

/-- PExt fails: the identity and negation on `e` agree up to `≡` at every argument, but are
distinct functions. -/
theorem Mswap_not_PExt : ¬ Mswap.Valid PExt := fun h => by
  have := Mswap.tr_PExt.mp ((Mswap.valid_iff_tr _).mp h) .e .e .e (fun z => z) (fun z => (Bool.not z : Bool))
    (fun _ => Or.inr ⟨rfl, rfl⟩)
  have e : (fun z : Bool => z) = (fun z : Bool => Bool.not z) :=
    (Mswap_sigma_iff (a := .arr .e .e) _ _).mp (Mswap_eqv_ne (fun h => by cases h) this)
  exact Bool.noConfusion (congrFun e true : true = false)

theorem Mswap_Truth : Mswap.Valid Truth :=
  (Mswap.valid_iff_tr _).mpr <| Mswap.tr_Truth.mpr fun p q h hp => (Mswap_eqv_t p q).mp h ▸ hp

theorem Mswap_TopBot : Mswap.Valid TopBot := (Mswap.valid_iff_tr _).mpr <| Mswap.tr_TopBot.mpr fun h => by
  have e := (Mswap_eqv_t _ _).mp h
  exact (e ▸ (fun hall : ∀ p : Prop, p => hall False) : ¬ ∀ p : Prop, p) (e ▸ (fun hall => hall False))

theorem Mswap_Slogan : Mswap.Valid Slogan :=
  (Mswap.valid_iff_tr _).mpr <| Mswap.tr_Slogan.mpr fun _ _ _ h => by
    have := Mswap_eqv_teq h
    cases this

theorem Mswap_Cantor : Mswap.Valid Cantor :=
  (Mswap.valid_iff_tr _).mpr <| Mswap.tr_Cantor.mpr fun a =>
    ⟨fun _ => True, fun _ h => Code.arr_ne_left a .t (Mswap_eqv_teq h)⟩

theorem Mswap_not_Twin : ¬ Mswap.Valid Twin := fun h => by
  obtain ⟨_, hb, _, hy⟩ := Mswap.tr_Twin.mp ((Mswap.valid_iff_tr _).mp h) .e true
  exact hb (Mswap_eqv_teq hy)

theorem Mswap_not_Hae : ¬ Mswap.Valid Hae := fun h => by
  have := Mswap.tr_Hae.mp ((Mswap.valid_iff_tr _).mp h) .e true
  exact Code.arr_ne_left .e .t (Mswap_eqv_teq this).symm

theorem Mswap_ExtT : Mswap.Valid ExtT :=
  (Mswap.valid_iff_tr _).mpr <| Mswap.tr_ExtT.mpr fun a _ ⟨h1, _⟩ =>
    (h1 (Classical.choice (Univ.El_nonempty (U := univSw) a))).elim fun _ h => Mswap_eqv_teq h

theorem Mswap_Recovery : Mswap.Valid Recovery :=
  (Mswap.valid_iff_tr _).mpr <| Mswap.tr_Recovery.mpr fun _ _ _ _ ⟨h, _⟩ => by
    injection h

theorem Mswap_IntT : Mswap.Valid IntT := (Mswap.IntT_iff_ExtT Mswap_eqv_t).mpr Mswap_ExtT

theorem Mswap_PropExt : Mswap.Valid PropExt := Mswap.PropExt_valid Mswap_model

theorem Mswap_Collapse : Mswap.Valid Collapse := Mswap.Collapse_valid Mswap_model

theorem Mswap_Choice : Mswap.Valid Choice := Mswap.Choice_valid

/-- IdId fails: `true ≡ false` is true, but `true` and `false` differ in their properties. -/
theorem Mswap_not_IdId : ¬ Mswap.Valid IdId := fun h => by
  have := Mswap.tr_IdId.mp ((Mswap.valid_iff_tr _).mp h) .e true false
  have e := (Mswap_eqv_t _ _).mp this
  have h2 := cast e (Or.inr ⟨rfl, rfl⟩) (fun z => z = true) rfl
  exact Bool.noConfusion (h2 : false = true)

/-! ### Modal principles, by soundness from PropExt, Collapse and Truth -/

theorem Mswap_of_prov {S : Fm Ctx.nil → Prop} (hS : ∀ ψ, S ψ → Mswap.Valid ψ) {φ : Fm Ctx.nil}
    (h : Prov S Ctx.nil φ) : Mswap.Valid φ :=
  Mswap.soundness Mswap_model hS h

/-- Classicism fails, since it proves IdId (in PI). -/
theorem Mswap_not_Class : ¬ ∀ χ, ClassSch χ → Mswap.Valid χ := fun h =>
  Mswap_not_IdId (Mswap_of_prov h (d_IdId_of_Class (S := ClassSch) (fun _ hc => hc)))

theorem Mswap_TAx : Mswap.Valid TAx :=
  Mswap_of_prov (S := (· = Truth)) (fun _ h => h ▸ Mswap_Truth) (d_TAx_of_Truth rfl)

theorem Mswap_NIEqv : Mswap.Valid NIEqv :=
  Mswap_of_prov (S := (· = Collapse)) (fun _ h => h ▸ Mswap_Collapse) (d_NIEqv_of_Collapse rfl)

theorem Mswap_NITeq : Mswap.Valid NITeq :=
  Mswap_of_prov (S := (· = Collapse)) (fun _ h => h ▸ Mswap_Collapse) (d_NITeq_of_Collapse rfl)

theorem Mswap_NDTeq : Mswap.Valid NDTeq :=
  Mswap_of_prov (S := (· = Collapse)) (fun _ h => h ▸ Mswap_Collapse) (d_NDTeq_of_Collapse rfl)

theorem Mswap_NIX : Mswap.Valid NIX :=
  Mswap_of_prov (S := (· = Collapse)) (fun _ h => h ▸ Mswap_Collapse) (d_NIX_of_Collapse rfl)

theorem Mswap_NDX : Mswap.Valid NDX :=
  Mswap_of_prov (S := (· = Collapse)) (fun _ h => h ▸ Mswap_Collapse) (d_NDX_of_Collapse rfl)

theorem Mswap_TNec : Mswap.Valid TNec :=
  Mswap_of_prov (S := (· = Collapse)) (fun _ h => h ▸ Mswap_Collapse) (d_TNec rfl)

theorem Mswap_Nec : Mswap.Valid Nec :=
  Mswap_of_prov (S := (· = Collapse)) (fun _ h => h ▸ Mswap_Collapse) (d_Nec_of_Collapse rfl)

theorem Mswap_Bool : ∀ φ, BoolSch φ → Mswap.Valid φ := fun φ hφ =>
  Mswap_of_prov (S := (· = PropExt)) (fun _ h => h ▸ Mswap_PropExt) (d_Bool_of_PropExt (S := (· = PropExt)) rfl φ hφ)

theorem Mswap_TBF : ∀ χ, TBFSch χ → Mswap.Valid χ := fun χ hχ =>
  Mswap_of_prov (S := (· = PropExt)) (fun _ h => h ▸ Mswap_PropExt) (d_TBF_of_PropExt (S := (· = PropExt)) rfl χ hχ)

theorem Mswap_TCBF : ∀ χ, TCBFSch χ → Mswap.Valid χ := fun χ hχ =>
  Mswap_of_prov (S := (· = PropExt)) (fun _ h => h ▸ Mswap_PropExt) (d_TCBF_of_PropExt (S := (· = PropExt)) rfl χ hχ)

theorem Mswap_BF : Mswap.Valid BF :=
  Mswap_of_prov (S := fun ψ => ψ = Collapse ∨ ψ = TAx)
    (fun _ h => h.elim (fun e => e ▸ Mswap_Collapse) (fun e => e ▸ Mswap_TAx))
    (d_BF_of_Collapse (Or.inl rfl) (Or.inr rfl))

theorem Mswap_CBF : Mswap.Valid CBF :=
  Mswap_of_prov (S := fun ψ => ψ = Collapse ∨ ψ = TAx)
    (fun _ h => h.elim (fun e => e ▸ Mswap_Collapse) (fun e => e ▸ Mswap_TAx))
    (d_CBF_of_Collapse (Or.inl rfl) (Or.inr rfl))

end Mswap

end PIF
