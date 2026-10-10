import PIBF
set_option autoImplicit false

/-!
# `𝔐_p,tag`: PCong→, Int≈ and Ext≈ fail, with almost every modal principle

An algebraic model of PI (`lean/PIAlg.lean`). A proposition is a truth value with a tag (a
number). There is one entity, and a base type `d` with one item. Identity of items is sameness of
*root*: the item of `d` has the entity as its root, the only function from entities to items of
`d` has as its root the constant function from entities to the proposition `(True, 0)`, and every
other item is its own root. So within a type identity is identity (LL≡ holds), `e` and `d` are
coextensive although distinct (Ext≈ fails), and identified functions with values of different
types take non-identified values (PCong→ fails).

Tags: `⊤` has tag `0`. `≡` gives tag `1`, `≈` tag `2`, `∃` tag `5`, `𝔼` tag `7`, the binary
connectives tag `8`; a negation keeps tag `0` and otherwise gets tag `3`. A universal
quantification (over items or over types) gets tag `4` (resp. `6`) when every instance is `⊤`
itself, and otherwise tag `0`. Since `□φ` is `φ ≡ ⊤`, and identity of propositions is equality,
`□φ` says that the value of `φ` is `(True, 0)`.

Valid: LL≡ (so this is a model of PI), LL≡/≈ (with parameters), WCong, Cantor, ⊤≢⊥, Slogan, Inj≈,
Recovery, Truth, T, Functional Choice. Refuted: Classicism, Disjoint, Twin, LL≡-Poly, Cong, PCong→,
PCong←, Haecceitism, PropExt≡, Ext≈, Int≈, Collapse, NI≡, NI≈, ND≈, NI×, ND×, Booleanism, the
Identity Identity, TBF, TCBF, TNec, BF, CBF, Nec.
-/

namespace PIF
namespace Al

/-! ## The frame -/

/-- Propositions are truth values with a numeric tag; one entity; a base type with one item. -/
abbrev XPT_U : Univ where
  P := Prop × Nat
  V := fun p => p.1
  p0 := (True, 0)
  E := Unit
  Base := Unit
  B := fun _ => Unit
  neE := ⟨()⟩
  neB := fun _ => ⟨()⟩

abbrev XPT_R := Σ c : Code XPT_U.Base, XPT_U.El c

/-- The proposition `⊤`. -/
def XPT_top : XPT_U.P := (True, 0)

/-- The constant function from entities to `⊤`. -/
def XPT_f0 : XPT_U.El (.arr .e .t) := fun _ => XPT_top

/-- Roots. -/
def XPT_r : (c : Code XPT_U.Base) → XPT_U.El c → XPT_R
  | .base _, _ => ⟨.e, ()⟩
  | .arr .e (.base _), _ => ⟨.arr .e .t, XPT_f0⟩
  | c, x => ⟨c, x⟩

/-- The tag of a negation. -/
def XPT_ntag (n : Nat) : Nat := if n = 0 then 0 else 3

open Classical in
/-- Universal quantification over items. -/
noncomputable def XPT_all (a : Code XPT_U.Base) (f : XPT_U.El a → XPT_U.P) : XPT_U.P :=
  if ∀ x, f x = XPT_top then (True, 4) else (∀ x, (f x).1, 0)

open Classical in
/-- Universal quantification over types. -/
noncomputable def XPT_tall (Q : Code XPT_U.Base → XPT_U.P) : XPT_U.P :=
  if ∀ a, Q a = XPT_top then (True, 6) else (∀ a, (Q a).1, 0)

theorem XPT_all_cases (a : Code XPT_U.Base) (f : XPT_U.El a → XPT_U.P) :
    (XPT_all a f = (True, 4) ∧ ∀ x, f x = XPT_top) ∨
      (XPT_all a f = (∀ x, (f x).1, 0) ∧ ¬ ∀ x, f x = XPT_top) := by
  by_cases h : ∀ x, f x = XPT_top
  · exact Or.inl ⟨ite_eq_left h, h⟩
  · exact Or.inr ⟨ite_eq_right h, h⟩

theorem XPT_tall_cases (Q : Code XPT_U.Base → XPT_U.P) :
    (XPT_tall Q = (True, 6) ∧ ∀ a, Q a = XPT_top) ∨
      (XPT_tall Q = (∀ a, (Q a).1, 0) ∧ ¬ ∀ a, Q a = XPT_top) := by
  by_cases h : ∀ a, Q a = XPT_top
  · exact Or.inl ⟨ite_eq_left h, h⟩
  · exact Or.inr ⟨ite_eq_right h, h⟩

theorem XPT_all_V (a : Code XPT_U.Base) (f : XPT_U.El a → XPT_U.P) :
    (XPT_all a f).1 ↔ ∀ x, (f x).1 := by
  rcases XPT_all_cases a f with ⟨e, h⟩ | ⟨e, _⟩
  · rw [e]; exact ⟨fun _ x => cast (congrArg Prod.fst (h x)).symm trivial, fun _ => trivial⟩
  · rw [e]

theorem XPT_tall_V (Q : Code XPT_U.Base → XPT_U.P) : (XPT_tall Q).1 ↔ ∀ a, (Q a).1 := by
  rcases XPT_tall_cases Q with ⟨e, h⟩ | ⟨e, _⟩
  · rw [e]; exact ⟨fun _ a => cast (congrArg Prod.fst (h a)).symm trivial, fun _ => trivial⟩
  · rw [e]

noncomputable abbrev XPT_F : Frame where
  U := XPT_U
  eqv := fun a b x y => (XPT_r a x = XPT_r b y, 1)
  teq := fun a b => (a = b, 2)
  neg := fun p => (¬ p.1, XPT_ntag p.2)
  imp := fun p q => (p.1 → q.1, 8)
  cnj := fun p q => (p.1 ∧ q.1, 8)
  dsj := fun p q => (p.1 ∨ q.1, 8)
  bic := fun p q => (p.1 ↔ q.1, 8)
  all := XPT_all
  ex := fun _ f => (∃ x, (f x).1, 5)
  tall := XPT_tall
  tex := fun Q => (∃ a, (Q a).1, 7)
  hneg := fun _ => Iff.rfl
  himp := fun _ _ => Iff.rfl
  hcnj := fun _ _ => Iff.rfl
  hdsj := fun _ _ => Iff.rfl
  hbic := fun _ _ => Iff.rfl
  hall := XPT_all_V
  hex := fun _ _ => Iff.rfl
  htall := XPT_tall_V
  htex := fun _ => Iff.rfl

theorem XPT_model : XPT_F.IsModelPIm :=
  XPT_F.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ _ _ h => Eq.symm h)
    (fun _ _ _ _ _ _ h1 h2 => Eq.trans h1 h2)

/-! ## Roots -/

/-- Within a type, items with the same root are the same item. -/
theorem XPT_r_inj : ∀ (c : Code XPT_U.Base) (x y : XPT_U.El c), XPT_r c x = XPT_r c y → x = y
  | .e, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .t, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .base _, _, _, _ => rfl
  | .arr .e (.base _), _, _, _ => funext fun _ => rfl
  | .arr .e .e, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr .e .t, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr .e (.arr _ _), _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr .t _, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr (.base _) _, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr (.arr _ _) _, _, _, h => eq_of_heq (Sigma.mk.inj h).2

/-- The root of an item is of its own type, or of type `e`, or of type `e → t`. -/
theorem XPT_r_fst : ∀ (c : Code XPT_U.Base) (x : XPT_U.El c),
    (XPT_r c x).1 = c ∨ (XPT_r c x).1 = .e ∨ (XPT_r c x).1 = .arr .e .t
  | .e, _ => Or.inl rfl
  | .t, _ => Or.inl rfl
  | .base _, _ => Or.inr (Or.inl rfl)
  | .arr .e (.base _), _ => Or.inr (Or.inr rfl)
  | .arr .e .e, _ => Or.inl rfl
  | .arr .e .t, _ => Or.inl rfl
  | .arr .e (.arr _ _), _ => Or.inl rfl
  | .arr .t _, _ => Or.inl rfl
  | .arr (.base _) _, _ => Or.inl rfl
  | .arr (.arr _ _) _, _ => Or.inl rfl

/-- Properties are their own roots. -/
theorem XPT_r_pred : ∀ (b : Code XPT_U.Base) (y : XPT_U.El (.arr b .t)), XPT_r (.arr b .t) y = ⟨.arr b .t, y⟩
  | .e, _ => rfl
  | .t, _ => rfl
  | .base _, _ => rfl
  | .arr _ _, _ => rfl

/-! ## Evaluation -/

theorem XPT_eqvT (p q : XPT_F.U.P) : XPT_F.U.V (XPT_F.eqv .t .t p q) ↔ p = q :=
  ⟨fun h => eq_of_heq (Sigma.mk.inj (h : (⟨.t, p⟩ : XPT_R) = ⟨.t, q⟩)).2, fun h => h ▸ rfl⟩

theorem XPT_LLEqv : XPT_F.Valid LLEqv := by
  intro ρ env
  refine (XPT_F.holds_tall _ _ _).mpr fun a => ?_
  refine (XPT_F.holds_all _ _ _ _).mpr fun x => (XPT_F.holds_all _ _ _ _).mpr fun y => ?_
  refine (XPT_F.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (XPT_F.holds_all _ _ _ _).mpr fun G => (XPT_F.holds_imp _ _ _ _).mpr fun hGx => ?_
  have e : x = y := XPT_r_inj a _ _ ((XPT_F.holds_eqv _ _ _ _ _ _).mp hxy)
  subst e
  exact hGx

theorem XPT_botF_tag {n : Nat} {Γ : Ctx n} (ρ : XPT_F.U.TEnv n) (env : XPT_F.U.Env Γ ρ) :
    (XPT_F.eval (botF : Fm Γ) ρ env).2 = 0 := by
  show (XPT_F.eval (Tm.all tyT (.var .here) : Fm Γ) ρ env).2 = 0
  rw [XPT_F.eval_all]
  show (XPT_all _ _).2 = 0
  rcases XPT_all_cases (XPT_F.U.code tyT.1 ρ)
    (fun x => XPT_F.eval (.var .here : Fm (Γ.ext tyT)) ρ (env, cast (Univ.El_code ρ tyT.2) x)) with ⟨_, h⟩ | ⟨e, _⟩
  · exact (cast (congrArg Prod.fst (h ((False, 0) : Prop × Nat))).symm trivial : False).elim
  · exact congrArg Prod.snd e

theorem XPT_topF {n : Nat} {Γ : Ctx n} (ρ : XPT_F.U.TEnv n) (env : XPT_F.U.Env Γ ρ) :
    XPT_F.eval (topF : Fm Γ) ρ env = XPT_top :=
  Prod.ext (propext ⟨fun _ => trivial, fun _ => XPT_F.holds_topF ρ env ⟨((False : Prop), 0), id⟩⟩)
    (congrArg XPT_ntag (XPT_botF_tag ρ env))

/-- `□φ` holds just when the value of `φ` is `⊤`. -/
theorem XPT_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : XPT_F.U.TEnv n) (env : XPT_F.U.Env Γ ρ) :
    XPT_F.Holds (boxF φ) ρ env ↔ XPT_F.eval φ ρ env = XPT_top :=
  (XPT_F.holds_eqv_t _ _ _ _).trans ((XPT_eqvT _ _).trans (by rw [XPT_topF]; exact Iff.rfl))

/-- A formula whose value has a nonzero tag is not necessary. -/
theorem XPT_not_box_of {n : Nat} {Γ : Ctx n} {φ : Fm Γ} {ρ : XPT_F.U.TEnv n} {env : XPT_F.U.Env Γ ρ}
    (hb : XPT_F.Holds (boxF φ) ρ env) {k : Nat} (h : (XPT_F.eval φ ρ env).2 = k) (hk : k ≠ 0) : False :=
  hk (h.symm.trans (congrArg Prod.snd ((XPT_box φ ρ env).mp hb)))

theorem XPT_cast_ex_eq {c : Code XPT_F.U.Base} {A' : Type} (hA : XPT_F.U.El c = A')
    (h : ((XPT_F.U.El c → XPT_F.U.P) → XPT_F.U.P) = ((A' → XPT_F.U.P) → XPT_F.U.P)) (Q : A' → XPT_F.U.P) :
    cast h (fun R => XPT_F.ex c R) Q = XPT_F.ex c (fun x => Q (cast hA x)) := by
  subst hA; rfl

theorem XPT_eval_ex {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : XPT_F.U.TEnv n)
    (env : XPT_F.U.Env Γ ρ) :
    XPT_F.eval (Tm.ex σ φ) ρ env =
      XPT_F.ex (XPT_F.U.code σ.1 ρ) (fun x => XPT_F.eval φ ρ (env, cast (Univ.El_code ρ σ.2) x)) :=
  XPT_cast_ex_eq (Univ.El_code ρ σ.2) _ _

theorem XPT_ex_tag {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : XPT_F.U.TEnv n)
    (env : XPT_F.U.Env Γ ρ) : (XPT_F.eval (Tm.ex σ φ) ρ env).2 = 5 := by
  rw [XPT_eval_ex]

theorem XPT_eqv_tag {n : Nat} {Γ : Ctx n} (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1) (ρ : XPT_F.U.TEnv n)
    (env : XPT_F.U.Env Γ ρ) : (XPT_F.eval (Tm.eqv σ τ x y) ρ env).2 = 1 := by
  rw [XPT_F.eval_eqv]

theorem XPT_teq_tag {n : Nat} {Γ : Ctx n} (σ τ : Ty n) (ρ : XPT_F.U.TEnv n) (env : XPT_F.U.Env Γ ρ) :
    (XPT_F.eval (Tm.teq σ τ : Fm Γ) ρ env).2 = 2 := by
  rw [XPT_F.eval_teq]

theorem XPT_neg_tag {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : XPT_F.U.TEnv n) (env : XPT_F.U.Env Γ ρ) :
    (XPT_F.eval (Tm.neg φ) ρ env).2 = XPT_ntag (XPT_F.eval φ ρ env).2 := rfl

/-- A universal quantification all of whose instances are `⊤` has tag `4`. -/
theorem XPT_eval_all_of_top {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : XPT_F.U.TEnv n)
    (env : XPT_F.U.Env Γ ρ) (h : ∀ v, XPT_F.eval φ ρ (env, v) = XPT_top) :
    XPT_F.eval (Tm.all σ φ) ρ env = (True, 4) := by
  rw [XPT_F.eval_all]
  show XPT_all _ _ = _
  rcases XPT_all_cases (XPT_F.U.code σ.1 ρ) (fun x => XPT_F.eval φ ρ (env, cast (Univ.El_code ρ σ.2) x))
    with ⟨e, _⟩ | ⟨_, h2⟩
  · exact e
  · exact absurd (fun _ => h _) h2

/-- A true universal quantification whose instances all have nonzero tags is `⊤`. -/
theorem XPT_eval_all_top {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : XPT_F.U.TEnv n)
    (env : XPT_F.U.Env Γ ρ) (hne : ∀ v, (XPT_F.eval φ ρ (env, v)).2 ≠ 0)
    (hall : XPT_F.Holds (Tm.all σ φ) ρ env) : XPT_F.eval (Tm.all σ φ) ρ env = XPT_top := by
  have hall' := (XPT_F.holds_all _ _ _ _).mp hall
  rw [XPT_F.eval_all]
  show XPT_all _ _ = _
  rcases XPT_all_cases (XPT_F.U.code σ.1 ρ) (fun x => XPT_F.eval φ ρ (env, cast (Univ.El_code ρ σ.2) x))
    with ⟨_, h⟩ | ⟨e, _⟩
  · obtain ⟨x0⟩ := Univ.El_nonempty (U := XPT_F.U) (XPT_F.U.code σ.1 ρ)
    exact absurd (congrArg Prod.snd (h x0)) (hne _)
  · exact e.trans (Prod.ext (propext ⟨fun _ => trivial, fun _ _ => hall' _⟩) rfl)

/-- The tag of a universal quantification is `0` or `4`. -/
theorem XPT_all_tag_ne {n : Nat} {Γ : Ctx n} {σ : Ty n} {φ : Fm (.ext Γ σ)} {ρ : XPT_F.U.TEnv n}
    {env : XPT_F.U.Env Γ ρ} {k : Nat} (h : (XPT_F.eval (Tm.all σ φ) ρ env).2 = k) (h0 : k ≠ 0) (h4 : k ≠ 4) :
    False := by
  rw [XPT_F.eval_all] at h
  rcases XPT_all_cases (XPT_F.U.code σ.1 ρ) (fun x => XPT_F.eval φ ρ (env, cast (Univ.El_code ρ σ.2) x))
    with ⟨e, _⟩ | ⟨e, _⟩
  · exact h4 (h.symm.trans (congrArg Prod.snd e))
  · exact h0 (h.symm.trans (congrArg Prod.snd e))

theorem XPT_tall_top (Q : Code XPT_U.Base → XPT_U.P) (h : ∀ a, Q a = XPT_top) : XPT_tall Q = (True, 6) := by
  rcases XPT_tall_cases Q with ⟨e, _⟩ | ⟨_, h2⟩
  · exact e
  · exact absurd h h2

/-! ## What PI proves -/

theorem XPT_of_prov {φ : Fm Ctx.nil} (h : Prov (· = LLEqv) Ctx.nil φ) : XPT_F.Valid φ :=
  XPT_F.soundness XPT_model (fun χ (e : χ = LLEqv) => e ▸ XPT_LLEqv) h

theorem XPT_Truth : XPT_F.Valid Truth := XPT_of_prov (Derive.d_Truth rfl)
theorem XPT_TopBot : XPT_F.Valid TopBot := XPT_of_prov (Derive.d_TopBot rfl)
theorem XPT_Cantor : XPT_F.Valid Cantor := XPT_of_prov (Derive.d_Cantor rfl)
theorem XPT_WCong : XPT_F.Valid WCong := XPT_of_prov (Derive.d_WCong rfl)

theorem XPT_TAx : XPT_F.Valid TAx :=
  XPT_F.soundness XPT_model (fun χ (e : χ = Truth) => e ▸ XPT_Truth) (d_TAx_of_Truth rfl)

theorem XPT_Choice : XPT_F.Valid Choice := XPT_F.Choice_valid

/-- LL≡/≈, for every polymorphic predicate, with parameters: identified items of one type are the
same item. -/
theorem XPT_Bridge {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : XPT_F.Valid (Bridge P) := by
  intro ρ env
  refine (XPT_F.holds_tall _ _ _).mpr fun a => (XPT_F.holds_tall _ _ _).mpr fun b => ?_
  refine (XPT_F.holds_all _ _ _ _).mpr fun x => (XPT_F.holds_all _ _ _ _).mpr fun y => ?_
  refine (XPT_F.holds_imp _ _ _ _).mpr fun h => (XPT_F.holds_imp _ _ _ _).mpr fun hPx => ?_
  obtain ⟨hxy, hab⟩ := (XPT_F.holds_conj _ _ _ _).mp h
  have hab' : a = b := (XPT_F.holds_teq _ _ _ _).mp hab
  subst hab'
  have e : x = y := XPT_r_inj a _ _ ((XPT_F.holds_eqv _ _ _ _ _ _).mp hxy)
  subst e
  exact hPx

/-! ## Identity across types -/

theorem XPT_Slogan : XPT_F.Valid Slogan := by
  intro ρ env
  refine (XPT_F.holds_all _ _ _ _).mpr fun _ => (XPT_F.holds_tall _ _ _).mpr fun b => ?_
  refine (XPT_F.holds_all _ _ _ _).mpr fun _ => (XPT_F.holds_neg _ _ _).mpr fun hxy => ?_
  have h : XPT_r .e _ = XPT_r (.arr b .t) _ := (XPT_F.holds_eqv _ _ _ _ _ _).mp hxy
  have e : (Code.e : Code XPT_U.Base) = .arr b .t := congrArg Sigma.fst (h.trans (XPT_r_pred _ _))
  exact nomatch e

/-- The entity and the item of `d` are identified, although `e` and `d` are distinct. -/
theorem XPT_not_Disjoint : ¬ XPT_F.Valid Disjoint := fun h => by
  have h0 := (XPT_F.holds_tall _ _ _).mp ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) (.base ())
  have h1 := (XPT_F.holds_imp _ _ _ _).mp h0 ((XPT_F.holds_neg _ _ _).mpr fun ht =>
    nomatch ((XPT_F.holds_teq _ _ _ _).mp ht : (Code.e : Code XPT_U.Base) = .base ()))
  have h2 := (XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_all _ _ _ _).mp h1 ()) ()
  exact (XPT_F.holds_neg _ _ _).mp h2 ((XPT_F.holds_eqv _ _ _ _ _ _).mpr rfl)

/-- LL≡-Poly fails, for `λγ.λz:γ.(γ ≈ e)`. -/
theorem XPT_not_LLPoly : ¬ XPT_F.Valid (LLPoly PredE) := fun h => by
  have h0 := (XPT_F.holds_tall _ _ _).mp ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) (.base ())
  have h1 := (XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_all _ _ _ _).mp h0 ()) ()
  have h2 := (XPT_F.holds_imp _ _ _ _).mp ((XPT_F.holds_imp _ _ _ _).mp h1 ((XPT_F.holds_eqv _ _ _ _ _ _).mpr rfl))
    (rfl : (Code.e : Code XPT_U.Base) = .e)
  exact nomatch (h2 : (Code.base () : Code XPT_U.Base) = .e)

/-- A proposition is identified only with itself. -/
theorem XPT_not_Twin : ¬ XPT_F.Valid Twin := fun h => by
  have h0 := (XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) XPT_top
  obtain ⟨b, hb⟩ := (XPT_F.holds_tex _ _ _).mp h0
  have hc := (XPT_F.holds_conj _ _ _ _).mp hb
  obtain ⟨y, hy⟩ := (XPT_F.holds_ex _ _ _ _).mp hc.2
  have e : XPT_r .t _ = XPT_r b _ := (XPT_F.holds_eqv _ _ _ _ _ _).mp hy
  have e1 : (Code.t : Code XPT_U.Base) = (XPT_r b _).1 := congrArg Sigma.fst e
  rcases XPT_r_fst b _ with h1 | h1 | h1
  · exact (XPT_F.holds_neg _ _ _).mp hc.1 ((XPT_F.holds_teq _ _ _ _).mpr (e1.trans h1))
  · exact nomatch (e1.trans h1)
  · exact nomatch (e1.trans h1)

theorem XPT_not_Hae : ¬ XPT_F.Valid Hae := fun h => by
  have h0 := (XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  have e : XPT_r .e _ = XPT_r (.arr .e .t) _ := (XPT_F.holds_eqv _ _ _ _ _ _).mp h0
  have e1 : (Code.e : Code XPT_U.Base) = .arr .e .t := congrArg Sigma.fst (e.trans (XPT_r_pred _ _))
  exact nomatch e1

/-! ## Congruence and extensionality -/

/-- The constant function from entities to `⊤` and the function from entities to items of `d` are
identified; but their values at the entity are not. -/
theorem XPT_not_PCong : ¬ XPT_F.Valid PCong := fun h => by
  have h0 := (XPT_F.holds_tall _ _ _).mp ((XPT_F.holds_tall _ _ _).mp
    ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .t) (.base ())
  have h1 := (XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_all _ _ _ _).mp
    ((XPT_F.holds_all _ _ _ _).mp h0 XPT_f0) (fun _ => ())) ()
  have h2 := (XPT_F.holds_imp _ _ _ _).mp h1 ((XPT_F.holds_eqv _ _ _ _ _ _).mpr rfl)
  have e : XPT_r .t _ = XPT_r (.base ()) _ := (XPT_F.holds_eqv _ _ _ _ _ _).mp h2
  have e1 : (Code.t : Code XPT_U.Base) = .e := congrArg Sigma.fst e
  exact nomatch e1

theorem XPT_not_Cong : ¬ XPT_F.Valid Cong := fun h => by
  have h0 := (XPT_F.holds_tall _ _ _).mp ((XPT_F.holds_tall _ _ _).mp ((XPT_F.holds_tall _ _ _).mp
    ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e) .t) (.base ())
  have h1 := (XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_all _ _ _ _).mp
    ((XPT_F.holds_all _ _ _ _).mp h0 XPT_f0) (fun _ => ())) ()) ()
  have h2 := (XPT_F.holds_imp _ _ _ _).mp h1 ((XPT_F.holds_conj _ _ _ _).mpr
    ⟨(XPT_F.holds_eqv _ _ _ _ _ _).mpr rfl, (XPT_F.holds_eqv _ _ _ _ _ _).mpr rfl⟩)
  have e : XPT_r .t _ = XPT_r (.base ()) _ := (XPT_F.holds_eqv _ _ _ _ _ _).mp h2
  have e1 : (Code.t : Code XPT_U.Base) = .e := congrArg Sigma.fst e
  exact nomatch e1

/-- The identity function on entities and the function from entities to items of `d` agree in
value everywhere, but are not identified. -/
theorem XPT_not_PExt : ¬ XPT_F.Valid PExt := fun h => by
  have h0 := (XPT_F.holds_tall _ _ _).mp ((XPT_F.holds_tall _ _ _).mp
    ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e) (.base ())
  have h1 := (XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_all _ _ _ _).mp h0 (fun x => x)) (fun _ => ())
  have h2 := (XPT_F.holds_imp _ _ _ _).mp h1 ((XPT_F.holds_all _ _ _ _).mpr fun _ =>
    (XPT_F.holds_eqv _ _ _ _ _ _).mpr rfl)
  have e : XPT_r (.arr .e .e) _ = XPT_r (.arr .e (.base ())) _ := (XPT_F.holds_eqv _ _ _ _ _ _).mp h2
  have e1 : (Code.arr .e .e : Code XPT_U.Base) = .arr .e .t := congrArg Sigma.fst e
  exact nomatch e1

/-! ## Identity of types -/

theorem XPT_Inj : XPT_F.Valid Inj := by
  intro ρ env
  refine (XPT_F.holds_tall _ _ _).mpr fun a => (XPT_F.holds_tall _ _ _).mpr fun b => ?_
  refine (XPT_F.holds_tall _ _ _).mpr fun c => (XPT_F.holds_tall _ _ _).mpr fun d => ?_
  refine (XPT_F.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (XPT_F.holds_teq _ _ _ _).mp h
  injection h' with hab hcd
  exact (XPT_F.holds_conj _ _ _ _).mpr ⟨(XPT_F.holds_teq _ _ _ _).mpr hab, (XPT_F.holds_teq _ _ _ _).mpr hcd⟩

theorem XPT_Recovery : XPT_F.Valid Recovery := by
  intro ρ env
  refine (XPT_F.holds_tall _ _ _).mpr fun a => (XPT_F.holds_tall _ _ _).mpr fun b => ?_
  refine (XPT_F.holds_tall _ _ _).mpr fun c => (XPT_F.holds_tall _ _ _).mpr fun d => ?_
  refine (XPT_F.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (XPT_F.holds_teq _ _ _ _).mp ((XPT_F.holds_conj _ _ _ _).mp h).1
  exact (XPT_F.holds_teq _ _ _ _).mpr (Code.arr.inj h').2

/-- `e` and `d` are coextensive, but distinct. -/
theorem XPT_not_ExtT : ¬ XPT_F.Valid ExtT := fun h => by
  have h0 := (XPT_F.holds_tall _ _ _).mp ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) (.base ())
  have h1 := (XPT_F.holds_imp _ _ _ _).mp h0 ((XPT_F.holds_conj _ _ _ _).mpr ⟨
    (XPT_F.holds_all _ _ _ _).mpr fun _ => (XPT_F.holds_ex _ _ _ _).mpr ⟨(), (XPT_F.holds_eqv _ _ _ _ _ _).mpr rfl⟩,
    (XPT_F.holds_all _ _ _ _).mpr fun _ => (XPT_F.holds_ex _ _ _ _).mpr ⟨(), (XPT_F.holds_eqv _ _ _ _ _ _).mpr rfl⟩⟩)
  exact nomatch ((XPT_F.holds_teq _ _ _ _).mp h1 : (Code.e : Code XPT_U.Base) = .base ())

/-- `e ⊑ d` is a true universal quantification of existential quantifications, so it is `⊤`; and
likewise `d ⊑ e`. So `e` and `d` are necessarily coextensive, but distinct. -/
theorem XPT_not_IntT : ¬ XPT_F.Valid IntT := fun h => by
  have h0 := (XPT_F.holds_tall _ _ _).mp ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) (.base ())
  have h1 := (XPT_F.holds_imp _ _ _ _).mp h0 ((XPT_F.holds_conj _ _ _ _).mpr ⟨
    (XPT_box _ _ _).mpr (XPT_eval_all_top _ _ _ _ (fun _ e => (by decide : (5 : Nat) ≠ 0) ((XPT_ex_tag _ _ _ _).symm.trans e))
      ((XPT_F.holds_all _ _ _ _).mpr fun _ => (XPT_F.holds_ex _ _ _ _).mpr ⟨(), (XPT_F.holds_eqv _ _ _ _ _ _).mpr rfl⟩)),
    (XPT_box _ _ _).mpr (XPT_eval_all_top _ _ _ _ (fun _ e => (by decide : (5 : Nat) ≠ 0) ((XPT_ex_tag _ _ _ _).symm.trans e))
      ((XPT_F.holds_all _ _ _ _).mpr fun _ => (XPT_F.holds_ex _ _ _ _).mpr ⟨(), (XPT_F.holds_eqv _ _ _ _ _ _).mpr rfl⟩))⟩)
  exact nomatch ((XPT_F.holds_teq _ _ _ _).mp h1 : (Code.e : Code XPT_U.Base) = .base ())

/-! ## Necessity -/

theorem XPT_not_Collapse : ¬ XPT_F.Valid Collapse := fun h => by
  have h0 := (XPT_F.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) ((True, 1) : Prop × Nat)
  exact XPT_not_box_of ((XPT_F.holds_imp _ _ _ _).mp h0 trivial) (k := 1) rfl (by decide)

theorem XPT_not_PropExt : ¬ XPT_F.Valid PropExt := fun h => by
  have h0 := (XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) XPT_top)
    ((True, 1) : Prop × Nat)
  have h1 := (XPT_F.holds_imp _ _ _ _).mp h0 ((XPT_F.holds_iff _ _ _ _).mpr ⟨fun _ => trivial, fun _ => trivial⟩)
  have e := (XPT_eqvT _ _).mp ((XPT_F.holds_eqv_t _ _ _ _).mp h1)
  exact (by decide : (0 : Nat) ≠ 1) (congrArg Prod.snd e)

theorem XPT_not_NIEqv : ¬ XPT_F.Valid NIEqv := fun h => by
  have h0 := (XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_all _ _ _ _).mp
    ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  exact XPT_not_box_of ((XPT_F.holds_imp _ _ _ _).mp h0 ((XPT_F.holds_eqv _ _ _ _ _ _).mpr rfl))
    (XPT_eqv_tag _ _ _ _ _ _) (by decide)

theorem XPT_not_NIX : ¬ XPT_F.Valid NIX := fun h => by
  have h0 := (XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_all _ _ _ _).mp
    ((XPT_F.holds_tall _ _ _).mp ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e) ()) ()
  exact XPT_not_box_of ((XPT_F.holds_imp _ _ _ _).mp h0 ((XPT_F.holds_eqv _ _ _ _ _ _).mpr rfl))
    (XPT_eqv_tag _ _ _ _ _ _) (by decide)

theorem XPT_not_NDX : ¬ XPT_F.Valid NDX := fun h => by
  have h0 := (XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_all _ _ _ _).mp
    ((XPT_F.holds_tall _ _ _).mp ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .t) ()) XPT_top
  have h1 := (XPT_F.holds_imp _ _ _ _).mp h0 ((XPT_F.holds_neg _ _ _).mpr fun hxy => by
    have e : XPT_r .e _ = XPT_r .t _ := (XPT_F.holds_eqv _ _ _ _ _ _).mp hxy
    have e1 : (Code.e : Code XPT_U.Base) = .t := congrArg Sigma.fst e
    exact nomatch e1)
  exact XPT_not_box_of h1 ((XPT_neg_tag _ _ _).trans (congrArg XPT_ntag (XPT_eqv_tag _ _ _ _ _ _))) (by decide)

theorem XPT_not_NITeq : ¬ XPT_F.Valid NITeq := fun h => by
  have h0 := (XPT_F.holds_tall _ _ _).mp ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e
  exact XPT_not_box_of ((XPT_F.holds_imp _ _ _ _).mp h0 ((XPT_F.holds_teq _ _ _ _).mpr rfl))
    (XPT_teq_tag _ _ _ _) (by decide)

theorem XPT_not_NDTeq : ¬ XPT_F.Valid NDTeq := fun h => by
  have h0 := (XPT_F.holds_tall _ _ _).mp ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .t
  have h1 := (XPT_F.holds_imp _ _ _ _).mp h0 ((XPT_F.holds_neg _ _ _).mpr fun ht =>
    nomatch ((XPT_F.holds_teq _ _ _ _).mp ht : (Code.e : Code XPT_U.Base) = .t))
  exact XPT_not_box_of h1 ((XPT_neg_tag _ _ _).trans (congrArg XPT_ntag (XPT_teq_tag _ _ _ _))) (by decide)

/-! ## Booleanism and the Identity Identity -/

theorem XPT_not_DNeg : ¬ XPT_F.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (XPT_F.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) ((True, 1) : Prop × Nat)
  have e := (XPT_eqvT _ _).mp ((XPT_F.holds_eqv_t _ _ _ _).mp h0)
  exact (by decide : (3 : Nat) ≠ 1) (congrArg Prod.snd e)

theorem XPT_not_Bool : ¬ ∀ φ, BoolSch φ → XPT_F.Valid φ := fun h => XPT_not_DNeg (h _ DNeg_bool)

theorem XPT_not_Class : ¬ ∀ χ, ClassSch χ → XPT_F.Valid χ := fun h =>
  XPT_not_Bool fun φ hφ => XPT_F.soundness XPT_model h (d_Bool_of_Class (S := ClassSch) (fun _ hc => hc) φ hφ)

/-- `x ≡ y` has tag `1`; a universal quantification has tag `0` or `4`. -/
theorem XPT_not_IdId : ¬ XPT_F.Valid IdId := fun h => by
  have h0 := (XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_all _ _ _ _).mp
    ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have e := (XPT_eqvT _ _).mp ((XPT_F.holds_eqv_t _ _ _ _).mp h0)
  exact XPT_all_tag_ne ((congrArg Prod.snd e).symm.trans (XPT_eqv_tag _ _ _ _ _ _)) (by decide) (by decide)

/-! ## The Barcan formulas, and Necessitism -/

/-- `𝔸α ⊤` has tag `6`, so it is not `⊤`. -/
theorem XPT_not_TBF : ¬ ∀ χ, TBFSch χ → XPT_F.Valid χ := fun h => by
  have h0 := h (TBFI (topF : Fm Ctx.nil.text)) ⟨_, rfl⟩ (fun i => i.elim0) ()
  have h1 := (XPT_F.holds_imp _ _ _ _).mp h0
    ((XPT_F.holds_tall _ _ _).mpr fun _ => (XPT_box _ _ _).mpr (XPT_topF _ _))
  exact XPT_not_box_of h1 (congrArg Prod.snd (XPT_tall_top _ fun _ => XPT_topF _ _)) (by decide)

/-- `𝔸α (α ≈ α)` is a true type quantification whose instances have tag `2`, so it is `⊤`; but
`e ≈ e` is not. -/
theorem XPT_not_TCBF : ¬ ∀ χ, TCBFSch χ → XPT_F.Valid χ := fun h => by
  have h0 := h (TCBFI (Tm.teq tv0 tv0 : Fm Ctx.nil.text)) ⟨_, rfl⟩ (fun i => i.elim0) ()
  have hb : XPT_F.Holds (boxF (Tm.tall (Tm.teq tv0 tv0 : Fm Ctx.nil.text))) (fun i => i.elim0) () := by
    refine (XPT_box _ _ _).mpr ?_
    rcases XPT_tall_cases (fun a => XPT_F.eval (Tm.teq tv0 tv0 : Fm Ctx.nil.text) (scons a fun i => i.elim0) ())
      with ⟨_, h1⟩ | ⟨e, _⟩
    · exact ((by decide : (2 : Nat) ≠ 0) ((XPT_teq_tag (Γ := Ctx.nil.text) tv0 tv0 (scons .e fun i => i.elim0) ()).symm.trans
        (congrArg Prod.snd (h1 .e)))).elim
    · exact e.trans (Prod.ext (propext ⟨fun _ => trivial, fun _ a =>
        (XPT_F.holds_teq (Γ := Ctx.nil.text) tv0 tv0 (scons a fun i => i.elim0) ()).mpr rfl⟩) rfl)
  have h1 := (XPT_F.holds_tall _ _ _).mp ((XPT_F.holds_imp _ _ _ _).mp h0 hb) .e
  exact XPT_not_box_of h1 (XPT_teq_tag _ _ _ _) (by decide)

theorem XPT_not_TNec : ¬ XPT_F.Valid TNec := fun h =>
  XPT_not_box_of ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) (k := 7) rfl (by decide)

/-- `∀x ⊤` has tag `4`, so it is not `⊤`. -/
theorem XPT_not_BF : ¬ XPT_F.Valid BF := fun h => by
  have h0 := (XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ => XPT_top)
  have h1 := (XPT_F.holds_imp _ _ _ _).mp h0 ((XPT_F.holds_all _ _ _ _).mpr fun _ => (XPT_box _ _ _).mpr rfl)
  exact XPT_not_box_of h1 (congrArg Prod.snd (XPT_eval_all_of_top _ _ _ _ fun _ => rfl)) (by decide)

/-- Let `F` take the entity to the truth `(True, 1)`. Then `∀x F x` is `⊤`, but `F` of the entity is not. -/
theorem XPT_not_CBF : ¬ XPT_F.Valid CBF := fun h => by
  have h0 := (XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ => ((True, 1) : Prop × Nat))
  have h1 := (XPT_F.holds_imp _ _ _ _).mp h0 ((XPT_box _ _ _).mpr
    (XPT_eval_all_top _ _ _ _ (fun _ e => (by decide : (1 : Nat) ≠ 0) e)
      ((XPT_F.holds_all _ _ _ _).mpr fun _ => trivial)))
  exact XPT_not_box_of ((XPT_F.holds_all _ _ _ _).mp h1 ()) (k := 1) rfl (by decide)

theorem XPT_not_Nec : ¬ XPT_F.Valid Nec := fun h =>
  XPT_not_box_of ((XPT_F.holds_all _ _ _ _).mp ((XPT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ())
    (XPT_ex_tag _ _ _ _) (by decide)

end Al
end PIF
