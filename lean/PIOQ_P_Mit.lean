import PIBF

/-!
# The profile of `𝔐_it`

The model `MitF` of `PITagged.lean`: tagged propositions over `E = 1` with no further base types.
The connectives, `≡` and `≈` give the tag `true`; a first-order quantifier over `t` also gives the tag
`true`, while a first-order quantifier over any other type, and the type quantifiers, give `false`.
At `t`, two propositions are identified when they are identical or both have the tag `true`; at
every other type, identity is identity; nothing is identified across types; `≈` is identity of types.

Since `⊤` has the tag `true`, `□φ` (that is, `φ ≡_t ⊤`) holds just in case the value of `φ` has the
tag `true`.

Valid: Cantor, Disjoint, Slogan, PCong, Inj≈, Recovery, Ext≈, NI≡, NI≈, ND≈, NI×, ND×, TCBF.
Refuted: LL≡/≈ and LL≡-Poly (for `Mit_PredT`), Cong, WCong, PExt, Twin, Haecceitism, Collapse,
the Identity Identity, Booleanism, Classicism, TBF, TNec, BF, CBF, Necessitism.
-/
set_option autoImplicit false

namespace PIF
namespace Tg
open Tm

/-! ## Tags and `□` -/

/-- `□φ` holds just in case the value of `φ` has the tag `true`. -/
theorem Mit_box_iff {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MitF.U.TEnv n) (env : MitF.U.Env Γ ρ) :
    MitF.Holds (boxF φ) ρ env ↔ (MitF.eval φ ρ env).2 = true := by
  refine (MitF.holds_eqv_t _ _ _ _).trans ⟨fun h => ?_, fun h => ⟨rfl, Or.inr ⟨h, rfl⟩⟩⟩
  rcases h.2 with e | ⟨s, _⟩
  · exact (congrArg Prod.snd (eq_of_heq e)).trans rfl
  · exact s

/-- The value of `x ≡ y` has the tag `true`. -/
theorem Mit_eqv_snd {n : Nat} {Γ : Ctx n} (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1)
    (ρ : MitF.U.TEnv n) (env : MitF.U.Env Γ ρ) : (MitF.eval (Tm.eqv σ τ x y) ρ env).2 = true :=
  congrArg Prod.snd (Frame.app2_heq (A := MitF.U.CatVal σ.1 ρ) (B := MitF.U.CatVal τ.1 ρ)
    (f := MitF.eval (Tm.castK (Tm.eqv_cat σ τ) (Tm.tapp (Tm.tapp (Tm.const Const.eqv) σ) τ)) ρ env)
    (Univ.El_code ρ σ.2).symm (Univ.El_code ρ τ.2).symm (MitF.eval_eqvConst σ τ ρ env)
    (MitF.eval x ρ env) (MitF.eval y ρ env))

/-- The value of `σ ≈ τ` has the tag `true`. -/
theorem Mit_teq_snd {n : Nat} {Γ : Ctx n} (σ τ : Ty n) (ρ : MitF.U.TEnv n) (env : MitF.U.Env Γ ρ) :
    (MitF.eval (Tm.teq (Γ := Γ) σ τ) ρ env).2 = true := by
  have h1 : HEq (MitF.eval (Tm.tapp (Tm.const (Γ := Γ) Const.teq) σ) ρ env)
      (fun b => (MitF.teq (MitF.U.code σ.1 ρ) b, true)) :=
    MitF.heq_eval_tapp _ σ ρ env
  have h2 : HEq (MitF.eval (Tm.teq (Γ := Γ) σ τ) ρ env)
      (MitF.eval (Tm.tapp (Tm.const (Γ := Γ) Const.teq) σ) ρ env (MitF.U.code τ.1 ρ)) :=
    MitF.heq_eval_tapp _ τ ρ env
  exact congrArg Prod.snd (eq_of_heq (h2.trans (heq_dapp (Q := fun _ => TV) (fun _ => rfl) h1 rfl)))

/-! ## Identity across types -/

/-- No property of a type is identified with an item of that type: they differ in type. -/
theorem Mit_Cantor : MitF.Valid Cantor := by
  intro ρ env
  refine (MitF.holds_tall _ _ _).mpr fun a =>
    (MitF.holds_ex _ _ _ _).mpr ⟨fun _ => ((True : Prop), true), ?_⟩
  refine (MitF.holds_all _ _ _ _).mpr fun y => (MitF.holds_neg _ _ _).mpr fun h => ?_
  exact Code.arr_ne_left a .t ((MitF.holds_eqv _ _ _ _ _ _).mp h).1

theorem Mit_Disjoint : MitF.Valid Disjoint :=
  (MitF.valid_iff_tr _).mpr <| MitF.tr_Disjoint.mpr fun _ _ hab _ _ h => hab h.1

theorem Mit_Slogan : MitF.Valid Slogan :=
  (MitF.valid_iff_tr _).mpr <| MitF.tr_Slogan.mpr fun _ _ _ h => by cases h.1

theorem Mit_not_Twin : ¬ MitF.Valid Twin := fun h => by
  obtain ⟨_, hb, _, hy⟩ := MitF.tr_Twin.mp ((MitF.valid_iff_tr _).mp h) .e ()
  exact hb hy.1

theorem Mit_not_Hae : ¬ MitF.Valid Hae := fun h =>
  Code.arr_ne_left (B := Empty) .e .t (MitF.tr_Hae.mp ((MitF.valid_iff_tr _).mp h) .e ()).1.symm

/-! ## `≈` -/

theorem Mit_Inj : MitF.Valid Inj := (MitF.valid_iff_tr _).mpr <| MitF.tr_Inj.mpr fun _ _ _ _ h => by
  injection h with h1 h2; exact ⟨h1, h2⟩

theorem Mit_Recovery : MitF.Valid Recovery := (MitF.valid_iff_tr _).mpr <|
  (show MitF.Tr Recovery ↔ ∀ a b c d, MitF.teq (.arr a c) (.arr b d) ∧ MitF.teq a b → MitF.teq c d
    from Iff.rfl).mpr fun _ _ _ _ ⟨h, _⟩ => by injection h

/-- Identified items have the same type, so `α ⊑ β` gives `α = β`. -/
theorem Mit_ExtT : MitF.Valid ExtT := (MitF.valid_iff_tr _).mpr <| MitF.tr_ExtT.mpr fun a _ ⟨h1, _⟩ =>
  (h1 (Classical.choice (Univ.El_nonempty (U := univU) a))).elim fun _ h => h.1

/-! ## The congruence principles -/

/-- Identified functions are identical. -/
theorem Mit_PCong : MitF.Valid PCong := (MitF.valid_iff_tr _).mpr <| (show MitF.Tr PCong ↔
    ∀ a c d (f : univU.El a → univU.El c) (g : univU.El a → univU.El d) x,
      MitF.eqv (.arr a c) (.arr a d) f g → MitF.eqv c d (f x) (g x) from Iff.rfl).mpr
  fun a c d f g x h => by
    obtain ⟨h1, h2⟩ := h
    have hcd : c = d := (Code.arr.inj h1).2
    subst hcd
    rcases h2 with h2 | ⟨h2, _⟩
    · have e : f = g := eq_of_heq h2
      subst e
      exact clsEqv_refl Sit _ _
    · exact (h2 : False).elim

/-- A function on propositions that takes `p` to `p` with the tag `false`. -/
def Mit_f : TV → TV := fun p => (p.1, false)

/-- It separates the identified propositions `(True, true)` and `(False, true)`. -/
theorem Mit_f_sep : ¬ MitF.eqv .t .t (Mit_f ((True : Prop), true)) (Mit_f ((False : Prop), true)) := by
  rintro ⟨_, e | ⟨s, _⟩⟩
  · exact cast (congrArg Prod.fst (eq_of_heq e)) trivial
  · exact Bool.noConfusion (s : false = true)

theorem Mit_tr_WCong : MitF.Tr WCong ↔
    ∀ (a b c d : Code univU.Base) (f : univU.El a → univU.El c) (g : univU.El b → univU.El d)
      (x : univU.El a) (y : univU.El b),
      (a = b ∧ c = d) ∧ (MitF.eqv (.arr a c) (.arr b d) f g ∧ MitF.eqv a b x y) →
        MitF.eqv c d (f x) (g y) := Iff.rfl

theorem Mit_not_WCong : ¬ MitF.Valid WCong := fun h =>
  Mit_f_sep (Mit_tr_WCong.mp ((MitF.valid_iff_tr _).mp h) .t .t .t .t Mit_f Mit_f
    ((True : Prop), true) ((False : Prop), true)
    ⟨⟨rfl, rfl⟩, ⟨rfl, Or.inl HEq.rfl⟩, ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩)

theorem Mit_not_Cong : ¬ MitF.Valid Cong := fun h =>
  Mit_f_sep (MitF.tr_Cong.mp ((MitF.valid_iff_tr _).mp h) .t .t .t .t Mit_f Mit_f
    ((True : Prop), true) ((False : Prop), true)
    ⟨⟨rfl, Or.inl HEq.rfl⟩, ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩)

/-- PExt fails: `λx.(True, true)` and `λx.(False, true)` have identified values but differ. -/
theorem Mit_not_PExt : ¬ MitF.Valid PExt := fun h => by
  have h0 := MitF.tr_PExt.mp ((MitF.valid_iff_tr _).mp h) .e .t .t
    (fun _ => ((True : Prop), true)) (fun _ => ((False : Prop), true)) (fun _ => ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)
  rcases h0.2 with e | ⟨s, _⟩
  · exact cast (congrArg Prod.fst (congrFun (eq_of_heq e) ())) trivial
  · exact (s : False).elim

/-! ## Leibniz's law for polymorphic predicates -/

/-- The polymorphic predicate `λγ.λz:γ. ∃_{γ→t} F (F ≡_{γ→t,t→t} λp:t.p ∧ F z)`. At `t` it holds
of just the true propositions. -/
def Mit_PredT : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (Tm.ex tv0.pred (Tm.conj (Tm.eqv tv0.pred tyT.pred (.var .here) (.lam tyT (.var .here)))
    (.app (.var .here) (.var (.there .here))))))

/-- What `Mit_PredT` says of `z : a`. -/
def Mit_PT (a : Code univU.Base) (z : univU.El a) : Prop :=
  ∃ F : univU.El a → TV, MitF.eqv (.arr a .t) (.arr .t .t) F (fun p => p) ∧ (F z).1

theorem Mit_PT_t (z : TV) : Mit_PT .t z ↔ z.1 := by
  constructor
  · rintro ⟨F, ⟨_, hF⟩, hz⟩
    rcases hF with e | ⟨s, _⟩
    · have e' : F = fun p => p := eq_of_heq e
      subst e'
      exact hz
    · exact (s : False).elim
  · intro hz
    exact ⟨fun p => p, ⟨rfl, Or.inl HEq.rfl⟩, hz⟩

theorem Mit_tr_BridgeT : MitF.Tr (Bridge Mit_PredT) ↔
    ∀ (a b : Code univU.Base) (x : univU.El a) (y : univU.El b),
      MitF.eqv a b x y ∧ a = b → Mit_PT a x → Mit_PT b y := Iff.rfl

theorem Mit_tr_LLPolyT : MitF.Tr (LLPoly Mit_PredT) ↔
    ∀ (a b : Code univU.Base) (x : univU.El a) (y : univU.El b),
      MitF.eqv a b x y → Mit_PT a x → Mit_PT b y := Iff.rfl

/-- LL≡/≈ fails: `(True, true)` and `(False, true)` are identified, at the same type. -/
theorem Mit_not_Bridge : ¬ MitF.Valid (Bridge Mit_PredT) := fun h => by
  have h0 := Mit_tr_BridgeT.mp ((MitF.valid_iff_tr _).mp h) .t .t ((True : Prop), true)
    ((False : Prop), true) ⟨⟨rfl, Or.inr ⟨rfl, rfl⟩⟩, rfl⟩ ((Mit_PT_t _).mpr trivial)
  exact (Mit_PT_t _).mp h0

theorem Mit_not_LLPoly : ¬ MitF.Valid (LLPoly Mit_PredT) := fun h => by
  have h0 := Mit_tr_LLPolyT.mp ((MitF.valid_iff_tr _).mp h) .t .t ((True : Prop), true)
    ((False : Prop), true) ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩ ((Mit_PT_t _).mpr trivial)
  exact (Mit_PT_t _).mp h0

/-! ## Modal principles -/

/-- Collapse fails: `(True, false)` is true, but has the tag `false`. -/
theorem Mit_not_Collapse : ¬ MitF.Valid Collapse := fun h => by
  have h0 := (MitF.holds_imp _ _ _ _).mp ((MitF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ())
    ((True : Prop), false)) trivial
  exact Bool.noConfusion ((Mit_box_iff _ _ _).mp h0 : false = true)

theorem Mit_NIEqv : MitF.Valid NIEqv := by
  intro ρ env
  refine (MitF.holds_tall _ _ _).mpr fun _ => (MitF.holds_all _ _ _ _).mpr fun _ =>
    (MitF.holds_all _ _ _ _).mpr fun _ => (MitF.holds_imp _ _ _ _).mpr fun _ => (Mit_box_iff _ _ _).mpr ?_
  exact Mit_eqv_snd _ _ _ _ _ _

theorem Mit_NITeq : MitF.Valid NITeq := by
  intro ρ env
  refine (MitF.holds_tall _ _ _).mpr fun _ => (MitF.holds_tall _ _ _).mpr fun _ =>
    (MitF.holds_imp _ _ _ _).mpr fun _ => (Mit_box_iff _ _ _).mpr ?_
  exact Mit_teq_snd _ _ _ _

theorem Mit_NDTeq : MitF.Valid NDTeq := by
  intro ρ env
  exact (MitF.holds_tall _ _ _).mpr fun _ => (MitF.holds_tall _ _ _).mpr fun _ =>
    (MitF.holds_imp _ _ _ _).mpr fun _ => (Mit_box_iff _ _ _).mpr rfl

theorem Mit_NIX : MitF.Valid NIX := by
  intro ρ env
  refine (MitF.holds_tall _ _ _).mpr fun _ => (MitF.holds_tall _ _ _).mpr fun _ =>
    (MitF.holds_all _ _ _ _).mpr fun _ => (MitF.holds_all _ _ _ _).mpr fun _ =>
      (MitF.holds_imp _ _ _ _).mpr fun _ => (Mit_box_iff _ _ _).mpr ?_
  exact Mit_eqv_snd _ _ _ _ _ _

theorem Mit_NDX : MitF.Valid NDX := by
  intro ρ env
  exact (MitF.holds_tall _ _ _).mpr fun _ => (MitF.holds_tall _ _ _).mpr fun _ =>
    (MitF.holds_all _ _ _ _).mpr fun _ => (MitF.holds_all _ _ _ _).mpr fun _ =>
      (MitF.holds_imp _ _ _ _).mpr fun _ => (Mit_box_iff _ _ _).mpr rfl

/-- `x ≡ y` has the tag `true`, while `∀_{e→t}F(F x → F y)` has the tag `false`. -/
theorem Mit_not_IdId : ¬ MitF.Valid IdId := fun h => by
  have h0 := (MitF.holds_all _ _ _ _).mp ((MitF.holds_all _ _ _ _).mp
    ((MitF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have h2 := MitF.eval_all_snd (Γ := ((Ctx.nil.text).ext tv0).ext tv0) tv0.pred
    (Tm.imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))
    (scons .e fun i => i.elim0) (((), ()), ())
  rcases ((MitF.holds_eqv_t _ _ _ _).mp h0).2 with e | ⟨_, s⟩
  · have h1 := (Mit_eqv_snd _ _ _ _ _ _).symm.trans ((congrArg Prod.snd (eq_of_heq e)).trans h2)
    exact Bool.noConfusion (h1 : true = false)
  · exact Bool.noConfusion ((s.symm.trans h2 : true = MitF.qtag (.arr .e .t)) : true = false)

/-- Booleanism fails: `¬¬(True, false)` has the tag `true`, so is not identified with `(True, false)`. -/
theorem Mit_not_DNeg : ¬ MitF.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MitF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) ((True : Prop), false)
  rcases ((MitF.holds_eqv_t _ _ _ _).mp h0).2 with e | ⟨_, s⟩
  · exact Bool.noConfusion (congrArg Prod.snd (eq_of_heq e) : true = false)
  · exact Bool.noConfusion (s : false = true)

theorem Mit_not_Bool : ¬ ∀ φ, BoolSch φ → MitF.Valid φ := fun h => Mit_not_DNeg (h _ DNeg_bool)

theorem Mit_not_Class : ¬ ∀ χ, ClassSch χ → MitF.Valid χ := fun h =>
  Mit_not_Bool fun φ hφ => MitF.soundness Mit_model h (d_Bool_of_Class (S := ClassSch) (fun _ hc => hc) φ hφ)

/-! ## Barcan formulas and Necessitism -/

/-- TBF fails, for `φ = ⊤`: `𝔸α ⊤` has the tag `false`. -/
theorem Mit_not_TBF : ¬ ∀ χ, TBFSch χ → MitF.Valid χ := fun h => by
  have h0 := h (TBFI (topF : Fm Ctx.nil.text)) ⟨_, rfl⟩ (fun i => i.elim0) ()
  have h1 := (MitF.holds_imp _ _ _ _).mp h0
    ((MitF.holds_tall _ _ _).mpr fun _ => (Mit_box_iff _ _ _).mpr rfl)
  exact Bool.noConfusion ((Mit_box_iff _ _ _).mp h1 : false = true)

/-- TCBF holds vacuously: a type quantification has the tag `false`, so is never necessary. -/
theorem Mit_TCBF : ∀ χ, TCBFSch χ → MitF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MitF.holds_imp _ _ _ _).mpr fun h => ?_
  exact Bool.noConfusion ((Mit_box_iff _ _ _).mp h : false = true)

theorem Mit_not_TNec : ¬ MitF.Valid TNec := fun h =>
  Bool.noConfusion ((Mit_box_iff _ _ _).mp ((MitF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) : false = true)

/-- BF fails at `e`: each `F x` is `(True, true)`, but `∀_e x F x` has the tag `false`. -/
theorem Mit_not_BF : ¬ MitF.Valid BF := fun h => by
  have h0 := (MitF.holds_all _ _ _ _).mp ((MitF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ => ((True : Prop), true))
  have h1 := (MitF.holds_imp _ _ _ _).mp h0
    ((MitF.holds_all _ _ _ _).mpr fun _ => (Mit_box_iff _ _ _).mpr rfl)
  have h2 := ((Mit_box_iff _ _ _).mp h1).symm.trans (MitF.eval_all_snd _ _ _ _)
  exact Bool.noConfusion (h2 : true = false)

/-- CBF fails at `t`: `∀_t x F x` has the tag `true`, but each `F x` is `(True, false)`. -/
theorem Mit_not_CBF : ¬ MitF.Valid CBF := fun h => by
  have h0 := (MitF.holds_all _ _ _ _).mp ((MitF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t)
    (fun _ => ((True : Prop), false))
  have h1 := (MitF.holds_imp _ _ _ _).mp h0
    ((Mit_box_iff _ _ _).mpr ((MitF.eval_all_snd _ _ _ _).trans rfl))
  have h2 := (MitF.holds_all _ _ _ _).mp h1 ((True : Prop), true)
  exact Bool.noConfusion ((Mit_box_iff _ _ _).mp h2 : false = true)

/-- Necessitism fails at `e`: `∃_e y (x ≡ y)` has the tag `false`. -/
theorem Mit_not_Nec : ¬ MitF.Valid Nec := fun h => by
  have h0 := (MitF.holds_all _ _ _ _).mp ((MitF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  have h2 := ((Mit_box_iff _ _ _).mp h0).symm.trans (MitF.eval_ex_snd _ _ _ _)
  exact Bool.noConfusion (h2 : true = false)

end Tg
end PIF
