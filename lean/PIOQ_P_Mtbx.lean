import PIBF

/-!
# The profile of `𝔐_tb,x`

The model `MtbxF` of `PICongQs.lean`: tagged propositions (`PITagged.lean`), every quantified
proposition (first-order or type-quantified) carrying the tag `false`, and `⊤` the tag `true`.
Propositions are identified when they are identical, or both quantified; functions of one type are
identified when their values are identified at every argument; nothing is identified across types,
and `≈` is identity of types.

So `□φ` (that is, `φ ≡_t ⊤`) is true just when `φ` is true and has the tag `true`; in particular
`□ψ` is false for every quantified `ψ`. An unquantified proposition is identified only with itself.
-/
set_option autoImplicit false

namespace PIF
namespace Tg
open Tm

/-! ## `□` -/

/-- `□φ` holds only if `φ` has the tag `true`. -/
theorem Mtbx_box_tag {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MtbxF.U.TEnv n) (env : MtbxF.U.Env Γ ρ)
    (h : MtbxF.Holds (boxF φ) ρ env) : (MtbxF.eval φ ρ env).2 = true := by
  obtain ⟨_, r⟩ := (MtbxF.holds_eqv_t _ _ _ _).mp h
  rcases r with e | ⟨_, s⟩
  · exact congrArg Prod.snd e
  · exact Bool.noConfusion (s : true = false)

/-! ## Identity across types -/

theorem Mtbx_Disjoint : MtbxF.Valid Disjoint := (MtbxF.valid_iff_tr _).mpr <|
  MtbxF.tr_Disjoint.mpr fun _ _ hab _ _ h => by
    obtain ⟨e, _⟩ := h
    exact hab e

theorem Mtbx_Slogan : MtbxF.Valid Slogan := (MtbxF.valid_iff_tr _).mpr <|
  MtbxF.tr_Slogan.mpr fun _ _ _ h => by
    obtain ⟨e, _⟩ := h
    cases e

theorem Mtbx_not_Twin : ¬ MtbxF.Valid Twin := fun h => by
  obtain ⟨_, hb, _, e, _⟩ := MtbxF.tr_Twin.mp ((MtbxF.valid_iff_tr _).mp h) .e ()
  exact hb e

theorem Mtbx_not_Hae : ¬ MtbxF.Valid Hae := fun h => by
  obtain ⟨e, _⟩ := MtbxF.tr_Hae.mp ((MtbxF.valid_iff_tr _).mp h) .e ()
  exact Code.arr_ne_left .e .t e.symm

theorem Mtbx_Cantor : MtbxF.Valid Cantor := (MtbxF.valid_iff_tr _).mpr <|
  (show MtbxF.Tr Cantor ↔ ∀ a, ∃ G : univU.El a → TV, ∀ y : univU.El a, ¬ MtbxF.eqv (.arr a .t) a G y
    from Iff.rfl).mpr fun a => ⟨fun _ => (True, true), fun _ h => by
      obtain ⟨e, _⟩ := h
      exact Code.arr_ne_left a .t e⟩

/-! ## The congruence principles -/

theorem Mtbx_PCong : MtbxF.Valid PCong := (MtbxF.valid_iff_tr _).mpr <| (show MtbxF.Tr PCong ↔
    ∀ a c d (f : univU.El a → univU.El c) (g : univU.El a → univU.El d) x,
      MtbxF.eqv (.arr a c) (.arr a d) f g → MtbxF.eqv c d (f x) (g x) from Iff.rfl).mpr
  fun a c d f g x h => by
    obtain ⟨e, r⟩ := h
    injection e with _ ecd
    subst ecd
    exact ⟨rfl, r x⟩

/-- `λp.¬p` is identified with itself, and the true and the false quantified propositions are
identified; but their negations are distinct unquantified propositions. -/
theorem Mtbx_not_Cong : ¬ MtbxF.Valid Cong := fun h => by
  obtain ⟨_, r⟩ := MtbxF.tr_Cong.mp ((MtbxF.valid_iff_tr _).mp h) .t .t .t .t
    (fun p => ((¬ p.1 : Prop), true)) (fun p => ((¬ p.1 : Prop), true)) (True, false) (False, false)
    ⟨⟨rfl, fun _ => Or.inl rfl⟩, ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
  rcases r with e | ⟨s, _⟩
  · exact (congrArg Prod.fst e).mpr (fun x => x) trivial
  · exact Bool.noConfusion (s : true = false)

theorem Mtbx_tr_WCong : MtbxF.Tr WCong ↔ ∀ a b c d (f : univU.El a → univU.El c) (g : univU.El b → univU.El d) x y,
    (MtbxF.teq a b ∧ MtbxF.teq c d) ∧ (MtbxF.eqv (.arr a c) (.arr b d) f g ∧ MtbxF.eqv a b x y) →
      MtbxF.eqv c d (f x) (g y) := Iff.rfl

theorem Mtbx_not_WCong : ¬ MtbxF.Valid WCong := fun h => by
  obtain ⟨_, r⟩ := Mtbx_tr_WCong.mp ((MtbxF.valid_iff_tr _).mp h) .t .t .t .t
    (fun p => ((¬ p.1 : Prop), true)) (fun p => ((¬ p.1 : Prop), true)) (True, false) (False, false)
    ⟨⟨rfl, rfl⟩, ⟨rfl, fun _ => Or.inl rfl⟩, ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
  rcases r with e | ⟨s, _⟩
  · exact (congrArg Prod.fst e).mpr (fun x => x) trivial
  · exact Bool.noConfusion (s : true = false)

/-! ## The polymorphic Leibniz laws fail

The polymorphic predicate `λγ.λz:γ. ∃_{γ→t} F (F z ∧ F ≡_{γ→t, t→t} λp.(p ∧ p))` is true of the
true quantified proposition and false of the false one, which are identified: at type `t`, the only
`F` identified with `λp.(p ∧ p)` is that function itself, since its values are unquantified. -/

def Mtbx_PredC : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (ex tv0.pred (conj (.app (.var .here) (.var (.there .here)))
    (eqv tv0.pred (Ty.arrow tyT tyT) (.var .here) (.lam tyT (conj (.var .here) (.var .here)))))))

theorem Mtbx_tr_LLPoly : MtbxF.Tr (LLPoly Mtbx_PredC) ↔ ∀ a b (x : univU.El a) (y : univU.El b),
    MtbxF.eqv a b x y →
    (∃ F : univU.El a → TV, (F x).1 ∧
      MtbxF.eqv (.arr a .t) (.arr .t .t) F (fun p => ((p.1 ∧ p.1 : Prop), true))) →
    (∃ F : univU.El b → TV, (F y).1 ∧
      MtbxF.eqv (.arr b .t) (.arr .t .t) F (fun p => ((p.1 ∧ p.1 : Prop), true))) := Iff.rfl

theorem Mtbx_not_LLPoly : ¬ MtbxF.Valid (LLPoly Mtbx_PredC) := fun h => by
  obtain ⟨F, hF, _, r⟩ := Mtbx_tr_LLPoly.mp ((MtbxF.valid_iff_tr _).mp h) .t .t (True, false) (False, false)
    ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩ ⟨fun p => ((p.1 ∧ p.1 : Prop), true), ⟨trivial, trivial⟩, rfl, fun _ => Or.inl rfl⟩
  rcases r (False, false) with e | ⟨_, s⟩
  · exact ((congrArg Prod.fst e).mp hF).1
  · exact Bool.noConfusion (s : true = false)

theorem Mtbx_tr_Bridge : MtbxF.Tr (Bridge Mtbx_PredC) ↔ ∀ a b (x : univU.El a) (y : univU.El b),
    MtbxF.eqv a b x y ∧ MtbxF.teq a b →
    (∃ F : univU.El a → TV, (F x).1 ∧
      MtbxF.eqv (.arr a .t) (.arr .t .t) F (fun p => ((p.1 ∧ p.1 : Prop), true))) →
    (∃ F : univU.El b → TV, (F y).1 ∧
      MtbxF.eqv (.arr b .t) (.arr .t .t) F (fun p => ((p.1 ∧ p.1 : Prop), true))) := Iff.rfl

/-- The same predicate refutes LL≡/≈: the two quantified propositions have the same type. -/
theorem Mtbx_not_Bridge : ¬ MtbxF.Valid (Bridge Mtbx_PredC) := fun h => by
  obtain ⟨F, hF, _, r⟩ := Mtbx_tr_Bridge.mp ((MtbxF.valid_iff_tr _).mp h) .t .t (True, false) (False, false)
    ⟨⟨rfl, Or.inr ⟨rfl, rfl⟩⟩, rfl⟩
    ⟨fun p => ((p.1 ∧ p.1 : Prop), true), ⟨trivial, trivial⟩, rfl, fun _ => Or.inl rfl⟩
  rcases r (False, false) with e | ⟨_, s⟩
  · exact ((congrArg Prod.fst e).mp hF).1
  · exact Bool.noConfusion (s : true = false)

/-! ## `≈` -/

theorem Mtbx_Inj : MtbxF.Valid Inj := (MtbxF.valid_iff_tr _).mpr <| MtbxF.tr_Inj.mpr fun _ _ _ _ h => by
  injection h with h1 h2
  exact ⟨h1, h2⟩

theorem Mtbx_Recovery : MtbxF.Valid Recovery := (MtbxF.valid_iff_tr _).mpr <|
  (show MtbxF.Tr Recovery ↔ ∀ a b c d, MtbxF.teq (.arr a c) (.arr b d) ∧ MtbxF.teq a b → MtbxF.teq c d
    from Iff.rfl).mpr fun _ _ _ _ ⟨h, _⟩ => by injection h

/-- Items are identified only with items of the same type. -/
theorem Mtbx_ExtT : MtbxF.Valid ExtT := (MtbxF.valid_iff_tr _).mpr <| MtbxF.tr_ExtT.mpr fun a _ ⟨h1, _⟩ => by
  obtain ⟨_, e, _⟩ := h1 (Classical.choice (Univ.El_nonempty (U := univU) a))
  exact e

/-- `□(α ⊑ β)` is false, since `α ⊑ β` is quantified. -/
theorem Mtbx_IntT : MtbxF.Valid IntT := by
  intro ρ env a b hc
  have hs := Mtbx_box_tag _ _ _ ((MtbxF.holds_conj _ _ _ _).mp hc).1
  have h0 : (MtbxF.eval (subT (Γ := (Ctx.nil.text).text)) (scons b (scons a ρ)) env).2 = false :=
    MtbxF.eval_all_snd _ _ _ _
  exact (Bool.false_ne_true (h0.symm.trans hs)).elim

/-! ## Necessity of identity and distinctness -/

theorem Mtbx_NIEqv : MtbxF.Valid NIEqv := by
  intro ρ env a
  refine (MtbxF.holds_all _ _ _ _).mpr fun x => (MtbxF.holds_all _ _ _ _).mpr fun y h => ?_
  exact (MtbxF.holds_eqv_t _ _ _ _).mpr
    ⟨rfl, Or.inl (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl)⟩

theorem Mtbx_NITeq : MtbxF.Valid NITeq := by
  intro ρ env a b h
  exact (MtbxF.holds_eqv_t _ _ _ _).mpr
    ⟨rfl, Or.inl (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl)⟩

theorem Mtbx_NDTeq : MtbxF.Valid NDTeq := by
  intro ρ env a b h
  exact (MtbxF.holds_eqv_t _ _ _ _).mpr
    ⟨rfl, Or.inl (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl)⟩

theorem Mtbx_NIX : MtbxF.Valid NIX := by
  intro ρ env a b
  refine (MtbxF.holds_all _ _ _ _).mpr fun x => (MtbxF.holds_all _ _ _ _).mpr fun y h => ?_
  exact (MtbxF.holds_eqv_t _ _ _ _).mpr
    ⟨rfl, Or.inl (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl)⟩

theorem Mtbx_NDX : MtbxF.Valid NDX := by
  intro ρ env a b
  refine (MtbxF.holds_all _ _ _ _).mpr fun x => (MtbxF.holds_all _ _ _ _).mpr fun y h => ?_
  exact (MtbxF.holds_eqv_t _ _ _ _).mpr
    ⟨rfl, Or.inl (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl)⟩

/-! ## Booleanism, the Identity Identity and Classicism -/

/-- `¬¬p` is unquantified, while `p` may be quantified. -/
theorem Mtbx_not_DNeg : ¬ MtbxF.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MtbxF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (True, false)
  obtain ⟨_, r⟩ := (MtbxF.holds_eqv_t _ _ _ _).mp h0
  rcases r with e | ⟨s, _⟩
  · exact Bool.noConfusion (congrArg Prod.snd e : true = false)
  · exact Bool.noConfusion (s : true = false)

theorem Mtbx_not_Bool : ¬ ∀ φ, BoolSch φ → MtbxF.Valid φ := fun h => Mtbx_not_DNeg (h _ DNeg_bool)

/-- `x ≡ y` is unquantified and `∀F(Fx → Fy)` is quantified, so they are never identified. -/
theorem Mtbx_not_IdId : ¬ MtbxF.Valid IdId := fun h => by
  have h0 := (MtbxF.holds_all _ _ _ _).mp ((MtbxF.holds_all _ _ _ _).mp
    ((MtbxF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  obtain ⟨_, r⟩ := (MtbxF.holds_eqv_t _ _ _ _).mp h0
  have h2 := MtbxF.eval_all_snd (Γ := ((Ctx.nil.text).ext tv0).ext tv0) tv0.pred
    (Tm.imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))
    (scons .e fun i => i.elim0) (((), ()), ())
  rcases r with e | ⟨s, _⟩
  · exact Bool.noConfusion ((congrArg Prod.snd e).trans h2 : true = false)
  · exact Bool.noConfusion (s : true = false)

/-- Classicism proves the Identity Identity, which fails. -/
theorem Mtbx_not_Class : ¬ ∀ χ, ClassSch χ → MtbxF.Valid χ := fun h =>
  Mtbx_not_IdId (MtbxF.soundness Mtbx_model h (d_IdId_of_Class (S := ClassSch) (fun _ hχ => hχ)))

/-! ## Barcan formulas and Necessitism -/

/-- `𝔸α ⊤` is type-quantified, so it is not identified with `⊤`. -/
theorem Mtbx_not_TBF : ¬ ∀ χ, TBFSch χ → MtbxF.Valid χ := fun h => by
  have h0 := h _ ⟨topF, rfl⟩ (fun i => i.elim0) ()
  have hb := (MtbxF.holds_imp _ _ _ _).mp h0 (fun _ => (MtbxF.holds_eqv_t _ _ _ _).mpr ⟨rfl, Or.inl rfl⟩)
  exact Bool.noConfusion (Mtbx_box_tag _ _ _ hb : false = true)

theorem Mtbx_TCBF : ∀ χ, TCBFSch χ → MtbxF.Valid χ := by
  rintro χ ⟨φ, rfl⟩ ρ env hb
  exact Bool.noConfusion (Mtbx_box_tag _ _ _ hb : false = true)

theorem Mtbx_not_TNec : ¬ MtbxF.Valid TNec := fun h => by
  have hb := (MtbxF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e
  exact Bool.noConfusion (Mtbx_box_tag _ _ _ hb : false = true)

/-- `λx.⊤` holds necessarily of everything, but `∀x ⊤` is quantified, so not identified with `⊤`. -/
theorem Mtbx_not_BF : ¬ MtbxF.Valid BF := fun h => by
  have h0 := (MtbxF.holds_all _ _ _ _).mp (h (fun i => i.elim0) () .e) (fun _ => (True, true))
  have h1 := h0 ((MtbxF.holds_all _ _ _ _).mpr fun _ => (MtbxF.holds_eqv_t _ _ _ _).mpr
    ⟨rfl, Or.inl (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => trivial⟩) rfl)⟩)
  have hs := Mtbx_box_tag _ _ _ h1
  have h2 := MtbxF.eval_all_snd (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here))
    (scons .e fun i => i.elim0) ((), fun _ => (True, true))
  exact Bool.noConfusion (h2.symm.trans hs : false = true)

/-- `□∀x F x` is false, since `∀x F x` is quantified. -/
theorem Mtbx_CBF : MtbxF.Valid CBF := by
  intro ρ env
  refine (MtbxF.holds_tall _ _ _).mpr fun a => (MtbxF.holds_all _ _ _ _).mpr fun G => ?_
  refine (MtbxF.holds_imp _ _ _ _).mpr fun hb => ?_
  have hs := Mtbx_box_tag _ _ _ hb
  have h0 := MtbxF.eval_all_snd (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here))
    (scons a ρ) (env, G)
  exact (Bool.false_ne_true (h0.symm.trans hs)).elim

/-- `∃y (x ≡ y)` is quantified, so it is not identified with `⊤`. -/
theorem Mtbx_not_Nec : ¬ MtbxF.Valid Nec := fun h => by
  have h0 := (MtbxF.holds_all _ _ _ _).mp (h (fun i => i.elim0) () .e) ()
  have hs := Mtbx_box_tag _ _ _ h0
  have h2 := MtbxF.eval_ex_snd (Γ := (Ctx.nil.text).ext tv0) tv0 (Tm.eqv tv0 tv0 (.var (.there .here)) (.var .here))
    (scons .e fun i => i.elim0) ((), ())
  exact Bool.noConfusion (h2.symm.trans hs : false = true)

end Tg
end PIF
