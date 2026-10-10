import PIBF
set_option autoImplicit false

/-!
# Open questions: `𝔐_IdB`, the Identity Identity and `⊤ ≢ ⊥` without T

An algebraic model of PI⁻. Propositions are pairs of a truth value and a tag in `{0, 1, 2}`: the
values of the connectives have tag `0`, the values of `≡` and `≈` tag `1`, and the values of the
quantifiers tag `2`. Entities are the two booleans. Items of different types are never
identified; at `e` any two entities are identified; at `t`, two propositions are identified just
in case both have tag `0` or neither does; at every other type, identity is identity.

So `x ≡ y` (tag `1`) and `∀F(F x → F y)` (tag `2`) are always identified, and the Identity
Identity holds; `⊤` (a negation, tag `0`) and `⊥` (a quantification, tag `2`) are not, so
`⊤ ≢ ⊥` holds; but the false proposition `(False, 0)` is identified with `⊤`, so T fails.
Since `□φ` is `φ ≡ ⊤`, `□φ` holds just in case the value of `φ` has tag `0`.

Valid: the Identity Identity, `⊤ ≢ ⊥`, Disjoint, Slogan, Cantor, Inj≈, Recovery, Ext≈, Int≈ (vacuously:
`□(α ⊑ β)` is never true), PCong, ND≈, ND×, TCBF, CBF, Choice.
Refuted: T, Truth, LL≡, LL≡/≈ and LL≡-Poly (for `MIdB_PredT`), Collapse, NI≡, NI≈, NI×, TBF, TNec,
BF, Nec, Booleanism, PropExt, Classicism, Haecceitism, Twin, Cong, WCong, PExt.
-/

namespace PIF
namespace Al

def univMIdB : Univ where
  P := Prop × Fin 3
  V := fun p => p.1
  p0 := (True, 0)
  E := Bool
  Base := Empty
  B := Empty.elim
  neE := ⟨true⟩
  neB := fun b => b.elim

/-- The identity relation at each type: everything at `e`; sameness of tag class (`0` against
`1, 2`) at `t`; identity at every other type. -/
def MIdB_idR : (c : Code Empty) → univMIdB.El c → univMIdB.El c → Prop
  | .e, _, _ => True
  | .t, x, y => x = y ∨ (x.2 ≠ 0 ∧ y.2 ≠ 0) ∨ (x.2 = 0 ∧ y.2 = 0)
  | .base b, _, _ => b.elim
  | .arr _ _, f, g => f = g

/-- Identity across types: the types are the same, and the items are related at that type. -/
def MIdB_R (a b : Code Empty) (x : univMIdB.El a) (y : univMIdB.El b) : Prop :=
  ∃ h : a = b, MIdB_idR b (cast (congrArg univMIdB.El h) x) y

def MIdBF : Frame where
  U := univMIdB
  eqv := fun a b x y => (MIdB_R a b x y, 1)
  teq := fun a b => (a = b, 1)
  neg := fun p => (¬ p.1, 0)
  imp := fun p q => (p.1 → q.1, 0)
  cnj := fun p q => (p.1 ∧ q.1, 0)
  dsj := fun p q => (p.1 ∨ q.1, 0)
  bic := fun p q => (p.1 ↔ q.1, 0)
  all := fun _ f => (∀ x, (f x).1, 2)
  ex := fun _ f => (∃ x, (f x).1, 2)
  tall := fun Q => (∀ a, (Q a).1, 2)
  tex := fun Q => (∃ a, (Q a).1, 2)
  hneg := fun _ => Iff.rfl
  himp := fun _ _ => Iff.rfl
  hcnj := fun _ _ => Iff.rfl
  hdsj := fun _ _ => Iff.rfl
  hbic := fun _ _ => Iff.rfl
  hall := fun _ _ => Iff.rfl
  hex := fun _ _ => Iff.rfl
  htall := fun _ => Iff.rfl
  htex := fun _ => Iff.rfl

/-! ## The identity relation -/

theorem MIdB_idR_t_iff (x y : Prop × Fin 3) : MIdB_idR .t x y ↔ (x.2 = 0 ↔ y.2 = 0) := by
  constructor
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · subst h; exact Iff.rfl
    · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    · exact ⟨fun _ => h2, fun _ => h1⟩
  · intro h
    by_cases hx : x.2 = 0
    · exact Or.inr (Or.inr ⟨hx, h.mp hx⟩)
    · exact Or.inr (Or.inl ⟨hx, fun hy => hx (h.mpr hy)⟩)

theorem MIdB_idR_refl : ∀ (c : Code Empty) (x : univMIdB.El c), MIdB_idR c x x
  | .e, _ => trivial
  | .t, _ => Or.inl rfl
  | .base b, _ => b.elim
  | .arr _ _, _ => rfl

theorem MIdB_idR_symm : ∀ (c : Code Empty) (x y : univMIdB.El c), MIdB_idR c x y → MIdB_idR c y x
  | .e, _, _, _ => trivial
  | .t, x, y, h => (MIdB_idR_t_iff y x).mpr ((MIdB_idR_t_iff x y).mp h).symm
  | .base b, _, _, _ => b.elim
  | .arr _ _, _, _, h => Eq.symm h

theorem MIdB_idR_trans : ∀ (c : Code Empty) (x y z : univMIdB.El c),
    MIdB_idR c x y → MIdB_idR c y z → MIdB_idR c x z
  | .e, _, _, _, _, _ => trivial
  | .t, x, y, z, h1, h2 =>
    (MIdB_idR_t_iff x z).mpr (((MIdB_idR_t_iff x y).mp h1).trans ((MIdB_idR_t_iff y z).mp h2))
  | .base b, _, _, _, _, _ => b.elim
  | .arr _ _, _, _, _, h1, h2 => Eq.trans h1 h2

theorem MIdB_R_refl (a : Code Empty) (x : univMIdB.El a) : MIdB_R a a x x := ⟨rfl, MIdB_idR_refl a x⟩

theorem MIdB_R_symm {a b : Code Empty} {x : univMIdB.El a} {y : univMIdB.El b} (h : MIdB_R a b x y) :
    MIdB_R b a y x := by
  obtain ⟨e, h⟩ := h
  subst e
  exact ⟨rfl, MIdB_idR_symm _ _ _ h⟩

theorem MIdB_R_trans {a b c : Code Empty} {x : univMIdB.El a} {y : univMIdB.El b} {z : univMIdB.El c}
    (h1 : MIdB_R a b x y) (h2 : MIdB_R b c y z) : MIdB_R a c x z := by
  obtain ⟨e1, h1⟩ := h1
  obtain ⟨e2, h2⟩ := h2
  subst e1; subst e2
  exact ⟨rfl, MIdB_idR_trans _ _ _ _ h1 h2⟩

/-- Identified items have the same type. -/
theorem MIdB_R_eq {a b : Code Empty} {x : univMIdB.El a} {y : univMIdB.El b} (h : MIdB_R a b x y) : a = b :=
  Exists.elim h fun e _ => e

theorem MIdB_model : MIdBF.IsModelPIm :=
  MIdBF.model_of_equiv (fun _ _ => Iff.rfl) (fun a x => MIdB_R_refl a x) (fun _ _ _ _ h => MIdB_R_symm h)
    (fun _ _ _ _ _ _ h1 h2 => MIdB_R_trans h1 h2)

/-- At `t`, two propositions are identified just in case both have tag `0` or neither does. -/
theorem MIdB_eqvT (p q : Prop × Fin 3) : MIdBF.U.V (MIdBF.eqv .t .t p q) ↔ (p.2 = 0 ↔ q.2 = 0) :=
  ⟨fun h => Exists.elim h fun _ h' => (MIdB_idR_t_iff p q).mp h', fun h => ⟨rfl, (MIdB_idR_t_iff p q).mpr h⟩⟩

theorem MIdB_ne10 : (1 : Fin 3) ≠ 0 := by decide
theorem MIdB_ne20 : (2 : Fin 3) ≠ 0 := by decide

/-! ## `⊤`, `⊥` and `□` -/

theorem MIdB_top {n : Nat} {Γ : Ctx n} (ρ : MIdBF.U.TEnv n) (env : MIdBF.U.Env Γ ρ) :
    @Eq (Prop × Fin 3) (MIdBF.eval (topF : Fm Γ) ρ env) (True, 0) :=
  Prod.ext (propext ⟨fun _ => trivial, fun _ h => (h ((False, (0 : Fin 3)) : Prop × Fin 3) : False)⟩) rfl

theorem MIdB_top2 {n : Nat} {Γ : Ctx n} (ρ : MIdBF.U.TEnv n) (env : MIdBF.U.Env Γ ρ) :
    @Prod.snd Prop (Fin 3) (MIdBF.eval (topF : Fm Γ) ρ env) = 0 :=
  congrArg Prod.snd (MIdB_top ρ env)

theorem MIdB_bot2 {n : Nat} {Γ : Ctx n} (ρ : MIdBF.U.TEnv n) (env : MIdBF.U.Env Γ ρ) :
    @Prod.snd Prop (Fin 3) (MIdBF.eval (botF : Fm Γ) ρ env) = 2 :=
  congrArg Prod.snd (MIdBF.eval_all (Γ := Γ) tyT (.var .here) ρ env)

/-- `□φ` holds just in case the value of `φ` has tag `0`. -/
theorem MIdB_holds_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MIdBF.U.TEnv n) (env : MIdBF.U.Env Γ ρ) :
    MIdBF.Holds (boxF φ) ρ env ↔ @Prod.snd Prop (Fin 3) (MIdBF.eval φ ρ env) = 0 :=
  (MIdBF.holds_eqv_t _ _ _ _).trans ((MIdB_eqvT _ _).trans
    ⟨fun h => h.mpr (MIdB_top2 ρ env), fun h => ⟨fun _ => MIdB_top2 ρ env, fun _ => h⟩⟩)

/-! ## The facts -/

theorem MIdB_IdId : MIdBF.Valid IdId := by
  intro ρ env
  refine (MIdBF.holds_tall _ _ _).mpr fun a => ?_
  refine (MIdBF.holds_all _ _ _ _).mpr fun x => (MIdBF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MIdBF.holds_eqv_t _ _ _ _).mpr ((MIdB_eqvT _ _).mpr ?_)
  have e1 : (MIdBF.eval (Tm.eqv tv0 tv0 (.var (.there .here)) (.var .here) : Fm (((Ctx.nil.text).ext tv0).ext tv0))
      (scons a ρ) ((env, x), y) : Prop × Fin 3).2 = 1 :=
    congrArg Prod.snd (MIdBF.eval_eqv (Γ := ((Ctx.nil.text).ext tv0).ext tv0) tv0 tv0 (.var (.there .here)) (.var .here)
      (scons a ρ) ((env, x), y))
  have e2 : (MIdBF.eval (Tm.all tv0.pred (Tm.imp (.app (.var .here) (.var (.there (.there .here))))
      (.app (.var .here) (.var (.there .here)))) : Fm (((Ctx.nil.text).ext tv0).ext tv0))
      (scons a ρ) ((env, x), y) : Prop × Fin 3).2 = 2 :=
    congrArg Prod.snd (MIdBF.eval_all (Γ := ((Ctx.nil.text).ext tv0).ext tv0) tv0.pred
      (Tm.imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))
      (scons a ρ) ((env, x), y))
  exact ⟨fun h => absurd (e1.symm.trans h) MIdB_ne10, fun h => absurd (e2.symm.trans h) MIdB_ne20⟩

theorem MIdB_TopBot : MIdBF.Valid TopBot := by
  intro ρ env
  refine (MIdBF.holds_neg _ _ _).mpr fun h => ?_
  have h1 := (MIdB_eqvT _ _).mp ((MIdBF.holds_eqv_t _ _ _ _).mp h)
  have h2 : (MIdBF.eval (botF : Fm Ctx.nil) ρ env : Prop × Fin 3).2 = 0 :=
    h1.mp (MIdB_top2 ρ env)
  exact MIdB_ne20 ((MIdB_bot2 ρ env).symm.trans h2)

theorem MIdB_not_TAx : ¬ MIdBF.Valid TAx := fun h => by
  have h0 := (MIdBF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) ((False, (0 : Fin 3)) : Prop × Fin 3)
  exact (MIdBF.holds_imp _ _ _ _).mp h0 ((MIdB_holds_box _ _ _).mpr rfl)

theorem MIdB_not_LLEqv : ¬ MIdBF.Valid LLEqv := fun h => by
  have h0 := (MIdBF.holds_all _ _ _ _).mp ((MIdBF.holds_all _ _ _ _).mp
    ((MIdBF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) ((True, (0 : Fin 3)) : Prop × Fin 3))
    ((False, (0 : Fin 3)) : Prop × Fin 3)
  have h1 := (MIdBF.holds_imp _ _ _ _).mp h0 ((MIdBF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩)
  exact (MIdBF.holds_imp _ _ _ _).mp ((MIdBF.holds_all _ _ _ _).mp h1 (fun p : Prop × Fin 3 => p)) trivial

theorem MIdB_not_Truth : ¬ MIdBF.Valid Truth := fun h => by
  have h0 := (MIdBF.holds_all _ _ _ _).mp ((MIdBF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ())
    ((True, (0 : Fin 3)) : Prop × Fin 3)) ((False, (0 : Fin 3)) : Prop × Fin 3)
  have h1 := (MIdBF.holds_imp _ _ _ _).mp h0 ((MIdBF.holds_eqv_t _ _ _ _).mpr ((MIdB_eqvT _ _).mpr Iff.rfl))
  exact (MIdBF.holds_imp _ _ _ _).mp h1 trivial

theorem MIdB_Disjoint : MIdBF.Valid Disjoint := by
  intro ρ env
  refine (MIdBF.holds_tall _ _ _).mpr fun a => (MIdBF.holds_tall _ _ _).mpr fun b => ?_
  refine (MIdBF.holds_imp _ _ _ _).mpr fun hn => ?_
  refine (MIdBF.holds_all _ _ _ _).mpr fun x => (MIdBF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MIdBF.holds_neg _ _ _).mpr fun hxy => ?_
  exact (MIdBF.holds_neg _ _ _).mp hn ((MIdBF.holds_teq _ _ _ _).mpr
    (MIdB_R_eq ((MIdBF.holds_eqv _ _ _ _ _ _).mp hxy)))

theorem MIdB_Slogan : MIdBF.Valid Slogan := by
  intro ρ env
  refine (MIdBF.holds_all _ _ _ _).mpr fun x => (MIdBF.holds_tall _ _ _).mpr fun b => ?_
  refine (MIdBF.holds_all _ _ _ _).mpr fun y => (MIdBF.holds_neg _ _ _).mpr fun hxy => ?_
  have h := MIdB_R_eq ((MIdBF.holds_eqv _ _ _ _ _ _).mp hxy)
  exact nomatch (show (Code.e : Code Empty) = .arr b .t from h)

theorem MIdB_Inj : MIdBF.Valid Inj := by
  intro ρ env
  refine (MIdBF.holds_tall _ _ _).mpr fun a => (MIdBF.holds_tall _ _ _).mpr fun b => ?_
  refine (MIdBF.holds_tall _ _ _).mpr fun c => (MIdBF.holds_tall _ _ _).mpr fun d => ?_
  refine (MIdBF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (MIdBF.holds_teq _ _ _ _).mp h
  injection h' with hab hcd
  exact (MIdBF.holds_conj _ _ _ _).mpr ⟨(MIdBF.holds_teq _ _ _ _).mpr hab, (MIdBF.holds_teq _ _ _ _).mpr hcd⟩

theorem MIdB_Recovery : MIdBF.Valid Recovery := by
  intro ρ env
  refine (MIdBF.holds_tall _ _ _).mpr fun a => (MIdBF.holds_tall _ _ _).mpr fun b => ?_
  refine (MIdBF.holds_tall _ _ _).mpr fun c => (MIdBF.holds_tall _ _ _).mpr fun d => ?_
  refine (MIdBF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (MIdBF.holds_teq _ _ _ _).mp ((MIdBF.holds_conj _ _ _ _).mp h).1
  exact (MIdBF.holds_teq _ _ _ _).mpr (Code.arr.inj h').2

theorem MIdB_not_NITeq : ¬ MIdBF.Valid NITeq := fun h => by
  have h0 := (MIdBF.holds_tall _ _ _).mp ((MIdBF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e
  have hb := (MIdB_holds_box _ _ _).mp ((MIdBF.holds_imp _ _ _ _).mp h0 ((MIdBF.holds_teq _ _ _ _).mpr rfl))
  have e : (MIdBF.eval (Tm.teq tv1 tv0 : Fm Ctx.nil.text.text) (scons .e (scons .e fun i => i.elim0)) () :
      Prop × Fin 3).2 = 1 :=
    congrArg Prod.snd (MIdBF.eval_teq (Γ := Ctx.nil.text.text) tv1 tv0 _ _)
  exact MIdB_ne10 (e.symm.trans hb)

theorem MIdB_NDTeq : MIdBF.Valid NDTeq := by
  intro ρ env
  refine (MIdBF.holds_tall _ _ _).mpr fun a => (MIdBF.holds_tall _ _ _).mpr fun b => ?_
  exact (MIdBF.holds_imp _ _ _ _).mpr fun _ => (MIdB_holds_box _ _ _).mpr rfl

/-! ## Tags of compound formulas -/

theorem MIdB_eqv_tag {n : Nat} {Γ : Ctx n} (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1) (ρ : MIdBF.U.TEnv n)
    (env : MIdBF.U.Env Γ ρ) : @Prod.snd Prop (Fin 3) (MIdBF.eval (Tm.eqv σ τ x y) ρ env) = 1 :=
  congrArg Prod.snd (MIdBF.eval_eqv σ τ x y ρ env)

theorem MIdB_all_tag {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MIdBF.U.TEnv n)
    (env : MIdBF.U.Env Γ ρ) : @Prod.snd Prop (Fin 3) (MIdBF.eval (Tm.all σ φ) ρ env) = 2 :=
  congrArg Prod.snd (MIdBF.eval_all σ φ ρ env)

theorem MIdB_cast_ex_eq {c : Code Empty} {A' : Type} (hA : MIdBF.U.El c = A')
    (h : ((MIdBF.U.El c → MIdBF.U.P) → MIdBF.U.P) = ((A' → MIdBF.U.P) → MIdBF.U.P)) (Q : A' → MIdBF.U.P) :
    cast h (fun R => MIdBF.ex c R) Q = MIdBF.ex c (fun x => Q (cast hA x)) := by
  subst hA; rfl

theorem MIdB_ex_tag {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MIdBF.U.TEnv n)
    (env : MIdBF.U.Env Γ ρ) : @Prod.snd Prop (Fin 3) (MIdBF.eval (Tm.ex σ φ) ρ env) = 2 :=
  congrArg Prod.snd (MIdB_cast_ex_eq (Univ.El_code ρ σ.2) _ _)

/-- Identified functions are identical. -/
theorem MIdB_R_arr {a c d : Code Empty} {f : univMIdB.El (.arr a c)} {g : univMIdB.El (.arr a d)}
    (h : MIdB_R (.arr a c) (.arr a d) f g) : c = d ∧ HEq f g := by
  obtain ⟨e, h⟩ := h
  injection e with _ ec
  subst ec
  exact ⟨rfl, heq_of_eq h⟩

/-! ## Further facts: the modal principles -/

theorem MIdB_not_NIEqv : ¬ MIdBF.Valid NIEqv := fun h => by
  have h0 := (MIdBF.holds_all _ _ _ _).mp ((MIdBF.holds_all _ _ _ _).mp
    ((MIdBF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) (true : Bool)) (true : Bool)
  have hb := (MIdB_holds_box _ _ _).mp ((MIdBF.holds_imp _ _ _ _).mp h0
    ((MIdBF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, trivial⟩))
  exact MIdB_ne10 ((MIdB_eqv_tag _ _ _ _ _ _).symm.trans hb)

theorem MIdB_not_NIX : ¬ MIdBF.Valid NIX := fun h => by
  have h0 := (MIdBF.holds_all _ _ _ _).mp ((MIdBF.holds_all _ _ _ _).mp ((MIdBF.holds_tall _ _ _).mp
    ((MIdBF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e) (true : Bool)) (true : Bool)
  have hb := (MIdB_holds_box _ _ _).mp ((MIdBF.holds_imp _ _ _ _).mp h0
    ((MIdBF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, trivial⟩))
  exact MIdB_ne10 ((MIdB_eqv_tag _ _ _ _ _ _).symm.trans hb)

theorem MIdB_NDX : MIdBF.Valid NDX := by
  intro ρ env
  refine (MIdBF.holds_tall _ _ _).mpr fun _ => (MIdBF.holds_tall _ _ _).mpr fun _ => ?_
  refine (MIdBF.holds_all _ _ _ _).mpr fun _ => (MIdBF.holds_all _ _ _ _).mpr fun _ => ?_
  exact (MIdBF.holds_imp _ _ _ _).mpr fun _ => (MIdB_holds_box _ _ _).mpr rfl

theorem MIdB_not_Collapse : ¬ MIdBF.Valid Collapse := fun h => by
  have h0 := (MIdBF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) ((True, (1 : Fin 3)) : Prop × Fin 3)
  have hb := (MIdB_holds_box _ _ _).mp ((MIdBF.holds_imp _ _ _ _).mp h0 trivial)
  exact MIdB_ne10 hb

theorem MIdB_not_TBF : ¬ ∀ χ, TBFSch χ → MIdBF.Valid χ := fun h => by
  have h0 := h _ ⟨topF, rfl⟩ (fun i => i.elim0) ()
  have h1 := (MIdB_holds_box _ _ _).mp ((MIdBF.holds_imp _ _ _ _).mp h0
    ((MIdBF.holds_tall _ _ _).mpr fun _ => (MIdB_holds_box _ _ _).mpr (MIdB_top2 _ _)))
  exact MIdB_ne20 h1

theorem MIdB_TCBF : ∀ χ, TCBFSch χ → MIdBF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  exact (MIdBF.holds_imp _ _ _ _).mpr fun h => absurd ((MIdB_holds_box _ _ _).mp h) MIdB_ne20

theorem MIdB_not_TNec : ¬ MIdBF.Valid TNec := fun h => by
  have h0 := (MIdBF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e
  have hb := (MIdB_holds_box _ _ _).mp h0
  exact MIdB_ne20 hb

theorem MIdB_not_BF : ¬ MIdBF.Valid BF := fun h => by
  have h0 := (MIdBF.holds_all _ _ _ _).mp ((MIdBF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ : Bool => ((True, (0 : Fin 3)) : Prop × Fin 3))
  have h1 := (MIdB_holds_box _ _ _).mp ((MIdBF.holds_imp _ _ _ _).mp h0
    ((MIdBF.holds_all _ _ _ _).mpr fun _ => (MIdB_holds_box _ _ _).mpr rfl))
  exact MIdB_ne20 ((MIdB_all_tag _ _ _ _).symm.trans h1)

theorem MIdB_CBF : MIdBF.Valid CBF := by
  intro ρ env
  refine (MIdBF.holds_tall _ _ _).mpr fun _ => (MIdBF.holds_all _ _ _ _).mpr fun _ => ?_
  refine (MIdBF.holds_imp _ _ _ _).mpr fun h => ?_
  exact absurd ((MIdB_all_tag _ _ _ _).symm.trans ((MIdB_holds_box _ _ _).mp h)) MIdB_ne20

theorem MIdB_not_Nec : ¬ MIdBF.Valid Nec := fun h => by
  have h0 := (MIdBF.holds_all _ _ _ _).mp ((MIdBF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) (true : Bool)
  exact MIdB_ne20 ((MIdB_ex_tag _ _ _ _).symm.trans ((MIdB_holds_box _ _ _).mp h0))

/-! ## Further facts: Booleanism, PropExt, Classicism -/

theorem MIdB_not_DNeg : ¬ MIdBF.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MIdBF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) ((True, (1 : Fin 3)) : Prop × Fin 3)
  exact MIdB_ne10 (((MIdB_eqvT _ _).mp ((MIdBF.holds_eqv_t _ _ _ _).mp h0)).mp rfl)

theorem MIdB_not_Bool : ¬ ∀ φ, BoolSch φ → MIdBF.Valid φ := fun h => MIdB_not_DNeg (h _ DNeg_bool)

theorem MIdB_not_PropExt : ¬ MIdBF.Valid PropExt := fun h => by
  have h0 := (MIdBF.holds_all _ _ _ _).mp ((MIdBF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ())
    ((True, (0 : Fin 3)) : Prop × Fin 3)) ((True, (1 : Fin 3)) : Prop × Fin 3)
  have h1 := (MIdBF.holds_imp _ _ _ _).mp h0 ((MIdBF.holds_iff _ _ _ _).mpr ⟨fun _ => trivial, fun _ => trivial⟩)
  exact MIdB_ne10 (((MIdB_eqvT _ _).mp ((MIdBF.holds_eqv_t _ _ _ _).mp h1)).mp rfl)

theorem MIdB_not_Class : ¬ ∀ χ, ClassSch χ → MIdBF.Valid χ := fun h =>
  MIdB_not_Bool fun φ hφ => MIdBF.soundness MIdB_model h (d_Bool_of_Class (S := ClassSch) (fun _ hc => hc) φ hφ)

/-! ## Further facts: identity across types, and of types -/

theorem MIdB_not_Hae : ¬ MIdBF.Valid Hae := fun h => by
  have h0 := (MIdBF.holds_all _ _ _ _).mp ((MIdBF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) (true : Bool)
  exact Code.arr_ne_left (Code.e : Code Empty) .t (MIdB_R_eq ((MIdBF.holds_eqv _ _ _ _ _ _).mp h0)).symm

theorem MIdB_not_Twin : ¬ MIdBF.Valid Twin := fun h => by
  have h0 := (MIdBF.holds_all _ _ _ _).mp ((MIdBF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) (true : Bool)
  obtain ⟨_, hb⟩ := (MIdBF.holds_tex _ _ _).mp h0
  have hc := (MIdBF.holds_conj _ _ _ _).mp hb
  obtain ⟨_, hy⟩ := (MIdBF.holds_ex _ _ _ _).mp hc.2
  exact (MIdBF.holds_neg _ _ _).mp hc.1 ((MIdBF.holds_teq _ _ _ _).mpr
    (MIdB_R_eq ((MIdBF.holds_eqv _ _ _ _ _ _).mp hy)))

theorem MIdB_Cantor : MIdBF.Valid Cantor := by
  intro ρ env
  refine (MIdBF.holds_tall _ _ _).mpr fun a => (MIdBF.holds_ex _ _ _ _).mpr
    ⟨fun _ => ((True, (0 : Fin 3)) : Prop × Fin 3), ?_⟩
  refine (MIdBF.holds_all _ _ _ _).mpr fun _ => (MIdBF.holds_neg _ _ _).mpr fun h => ?_
  exact Code.arr_ne_left a .t (MIdB_R_eq ((MIdBF.holds_eqv _ _ _ _ _ _).mp h))

theorem MIdB_ExtT : MIdBF.Valid ExtT := by
  intro ρ env
  refine (MIdBF.holds_tall _ _ _).mpr fun a => (MIdBF.holds_tall _ _ _).mpr fun _ => ?_
  refine (MIdBF.holds_imp _ _ _ _).mpr fun h => (MIdBF.holds_teq _ _ _ _).mpr ?_
  have hs := ((MIdBF.holds_conj _ _ _ _).mp h).1
  have x0 := Classical.choice (Univ.El_nonempty (U := MIdBF.U) a)
  obtain ⟨_, hy⟩ := (MIdBF.holds_ex _ _ _ _).mp ((MIdBF.holds_all _ _ _ _).mp hs x0)
  exact MIdB_R_eq ((MIdBF.holds_eqv _ _ _ _ _ _).mp hy)

/-- `□(α ⊑ β)` is never true, since the value of `α ⊑ β` is a quantification, with tag `2`. -/
theorem MIdB_IntT : MIdBF.Valid IntT := by
  intro ρ env
  refine (MIdBF.holds_tall _ _ _).mpr fun _ => (MIdBF.holds_tall _ _ _).mpr fun _ => ?_
  refine (MIdBF.holds_imp _ _ _ _).mpr fun h => ?_
  exact absurd ((MIdB_all_tag _ _ _ _).symm.trans
    ((MIdB_holds_box _ _ _).mp ((MIdBF.holds_conj _ _ _ _).mp h).1)) MIdB_ne20

/-! ## Further facts: congruence and extensionality -/

/-- A predicate of entities whose values have different tags at the two entities. -/
def MIdB_fc : Bool → Prop × Fin 3 := fun b => (True, bif b then 0 else 1)

theorem MIdB_not_Cong : ¬ MIdBF.Valid Cong := fun h => by
  have h0 := (MIdBF.holds_tall _ _ _).mp ((MIdBF.holds_tall _ _ _).mp ((MIdBF.holds_tall _ _ _).mp
    ((MIdBF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e) .t) .t
  have h1 := (MIdBF.holds_all _ _ _ _).mp ((MIdBF.holds_all _ _ _ _).mp ((MIdBF.holds_all _ _ _ _).mp
    ((MIdBF.holds_all _ _ _ _).mp h0 MIdB_fc) MIdB_fc) (true : Bool)) (false : Bool)
  have h2 := (MIdBF.holds_imp _ _ _ _).mp h1 ((MIdBF.holds_conj _ _ _ _).mpr
    ⟨(MIdBF.holds_eqv _ _ _ _ _ _).mpr (MIdB_R_refl _ _), (MIdBF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, trivial⟩⟩)
  exact MIdB_ne10 (((MIdB_eqvT _ _).mp ((MIdBF.holds_eqv _ _ _ _ _ _).mp h2)).mp rfl)

theorem MIdB_not_WCong : ¬ MIdBF.Valid WCong := fun h => by
  have h0 := (MIdBF.holds_tall _ _ _).mp ((MIdBF.holds_tall _ _ _).mp ((MIdBF.holds_tall _ _ _).mp
    ((MIdBF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e) .t) .t
  have h1 := (MIdBF.holds_all _ _ _ _).mp ((MIdBF.holds_all _ _ _ _).mp ((MIdBF.holds_all _ _ _ _).mp
    ((MIdBF.holds_all _ _ _ _).mp h0 MIdB_fc) MIdB_fc) (true : Bool)) (false : Bool)
  have h2 := (MIdBF.holds_imp _ _ _ _).mp h1 ((MIdBF.holds_conj _ _ _ _).mpr
    ⟨(MIdBF.holds_conj _ _ _ _).mpr ⟨(MIdBF.holds_teq _ _ _ _).mpr rfl, (MIdBF.holds_teq _ _ _ _).mpr rfl⟩,
     (MIdBF.holds_conj _ _ _ _).mpr
      ⟨(MIdBF.holds_eqv _ _ _ _ _ _).mpr (MIdB_R_refl _ _), (MIdBF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, trivial⟩⟩⟩)
  exact MIdB_ne10 (((MIdB_eqvT _ _).mp ((MIdBF.holds_eqv _ _ _ _ _ _).mp h2)).mp rfl)

theorem MIdB_PCong : MIdBF.Valid PCong := by
  intro ρ env
  refine (MIdBF.holds_tall _ _ _).mpr fun a => (MIdBF.holds_tall _ _ _).mpr fun c =>
    (MIdBF.holds_tall _ _ _).mpr fun d => ?_
  refine (MIdBF.holds_all _ _ _ _).mpr fun f => (MIdBF.holds_all _ _ _ _).mpr fun g =>
    (MIdBF.holds_all _ _ _ _).mpr fun x => ?_
  refine (MIdBF.holds_imp _ _ _ _).mpr fun h => ?_
  obtain ⟨ec, hfg⟩ := MIdB_R_arr (a := a) (c := c) (d := d) ((MIdBF.holds_eqv _ _ _ _ _ _).mp h)
  subst ec
  have ef : f = g := eq_of_heq hfg
  subst ef
  exact (MIdBF.holds_eqv _ _ _ _ _ _).mpr (MIdB_R_refl _ _)

theorem MIdB_not_PExt : ¬ MIdBF.Valid PExt := fun h => by
  have h0 := (MIdBF.holds_tall _ _ _).mp ((MIdBF.holds_tall _ _ _).mp ((MIdBF.holds_tall _ _ _).mp
    (h (fun i => i.elim0) ()) .e) .t) .t
  have h1 := (MIdBF.holds_all _ _ _ _).mp ((MIdBF.holds_all _ _ _ _).mp h0
    (fun _ : Bool => ((True, (0 : Fin 3)) : Prop × Fin 3))) (fun _ : Bool => ((False, (0 : Fin 3)) : Prop × Fin 3))
  have h2 := (MIdBF.holds_imp _ _ _ _).mp h1 ((MIdBF.holds_all _ _ _ _).mpr fun _ =>
    (MIdBF.holds_eqv _ _ _ _ _ _).mpr ((MIdB_eqvT _ _).mpr Iff.rfl))
  have h3 := (MIdB_R_arr ((MIdBF.holds_eqv _ _ _ _ _ _).mp h2)).2
  exact cast (congrArg Prod.fst (congrFun (eq_of_heq h3) true)) trivial

theorem MIdB_Choice : MIdBF.Valid Choice := MIdBF.Choice_valid

/-! ## Further facts: Leibniz's law for polymorphic predicates -/

open Tm in
/-- The polymorphic predicate `λγ.λz:γ. ∃_{γ→t} F (F ≡_{γ→t,t→t} λp:t.p ∧ F z)`. Since identified
items have the same type, and identified functions are identical, at `t` it holds of exactly the
true propositions, and at any other type of nothing. -/
def MIdB_PredT : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (ex tv0.pred (conj (eqv tv0.pred tyT.pred (.var .here) (.lam tyT (.var .here)))
    (.app (.var .here) (.var (.there .here))))))

/-- `MIdB_PredT` holds of `z : a` just in case some `F : a → t` is identified with `λp.p` and `F z`. -/
def MIdB_PT (a : Code Empty) (z : univMIdB.El a) : Prop :=
  ∃ F : univMIdB.El a → Prop × Fin 3, MIdB_R (.arr a .t) (.arr .t .t) F (fun p => p) ∧ (F z).1

theorem MIdB_PT_t (z : Prop × Fin 3) : MIdB_PT .t z ↔ z.1 := by
  constructor
  · rintro ⟨F, hF, hz⟩
    obtain ⟨_, hFe⟩ := MIdB_R_arr hF
    have e : F = fun p => p := eq_of_heq hFe
    subst e
    exact hz
  · intro hz
    exact ⟨fun p => p, MIdB_R_refl _ _, hz⟩

theorem MIdB_tr_BridgeT : MIdBF.Holds (Bridge MIdB_PredT) (fun i => i.elim0) () ↔
    ∀ (a b : Code Empty) (x : univMIdB.El a) (y : univMIdB.El b),
      MIdB_R a b x y ∧ a = b → MIdB_PT a x → MIdB_PT b y := Iff.rfl

theorem MIdB_tr_LLPolyT : MIdBF.Holds (LLPoly MIdB_PredT) (fun i => i.elim0) () ↔
    ∀ (a b : Code Empty) (x : univMIdB.El a) (y : univMIdB.El b),
      MIdB_R a b x y → MIdB_PT a x → MIdB_PT b y := Iff.rfl

theorem MIdB_not_Bridge : ¬ MIdBF.Valid (Bridge MIdB_PredT) := fun h => by
  have h0 := MIdB_tr_BridgeT.mp ((MIdBF.valid_iff_tr _).mp h) .t .t ((True, (0 : Fin 3)) : Prop × Fin 3)
    ((False, (0 : Fin 3)) : Prop × Fin 3) ⟨⟨rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩, rfl⟩ ((MIdB_PT_t _).mpr trivial)
  exact (MIdB_PT_t _).mp h0

theorem MIdB_not_LLPoly : ¬ MIdBF.Valid (LLPoly MIdB_PredT) := fun h => by
  have h0 := MIdB_tr_LLPolyT.mp ((MIdBF.valid_iff_tr _).mp h) .t .t ((True, (0 : Fin 3)) : Prop × Fin 3)
    ((False, (0 : Fin 3)) : Prop × Fin 3) ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩ ((MIdB_PT_t _).mpr trivial)
  exact (MIdB_PT_t _).mp h0

end Al
end PIF
