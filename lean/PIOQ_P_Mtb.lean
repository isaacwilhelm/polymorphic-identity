import PIBF
set_option autoImplicit false

/-!
# Open questions: the profile of `𝔐_tb`

`𝔐_tb` (`lean/PITagged.lean`, `MtbF`): tagged propositions, in which every quantified proposition
(over items or over types) carries the tag `false`, and the other logical constants (in particular
`⊤`, `¬`, `≡` and `≈`) give the tag `true`. `E = 1`, `≈` is identity of types, and an item is
identified with an item just in case they are the same item, or both are propositions with the tag
`false`.

So nothing is identified across types, and `□φ` (that is, `φ ≡_t ⊤`) is true just when `φ` is true
and has the tag `true`; in particular `□ψ` is false for every quantified `ψ`. Within `t`, the
quantified propositions `(True, false)` and `(False, false)` are identified, so the Leibniz laws
and the congruence principles fail.
-/

namespace PIF
namespace Tg
open Tm

/-! ## Basic facts about `□` -/

/-- `□φ` implies that `φ` has the tag `true`. -/
theorem Mtb_box_tag {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MtbF.U.TEnv n) (env : MtbF.U.Env Γ ρ)
    (h : MtbF.Holds (boxF φ) ρ env) : (MtbF.eval φ ρ env).2 = true := by
  rcases ((MtbF.holds_eqv_t _ _ _ _).mp h).2 with e | ⟨_, s⟩
  · exact congrArg Prod.snd (eq_of_heq e)
  · exact Bool.noConfusion (s : true = false)

/-- A true formula with the tag `true` is necessary. -/
theorem Mtb_box_of {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MtbF.U.TEnv n) (env : MtbF.U.Env Γ ρ)
    (ht : (MtbF.eval φ ρ env).2 = true) (h : MtbF.Holds φ ρ env) : MtbF.Holds (boxF φ) ρ env :=
  (MtbF.holds_eqv_t _ _ _ _).mpr
    ⟨rfl, Or.inl (heq_of_eq (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) ht))⟩

/-! ## Identity across types -/

theorem Mtb_Disjoint : MtbF.Valid Disjoint :=
  (MtbF.valid_iff_tr _).mpr <| MtbF.tr_Disjoint.mpr fun _ _ hab _ _ h => hab h.1

theorem Mtb_Slogan : MtbF.Valid Slogan :=
  (MtbF.valid_iff_tr _).mpr <| MtbF.tr_Slogan.mpr fun _ _ _ h => by cases h.1

theorem Mtb_not_Twin : ¬ MtbF.Valid Twin := fun h => by
  obtain ⟨_, hn, _, hy⟩ := MtbF.tr_Twin.mp ((MtbF.valid_iff_tr _).mp h) .e ()
  exact hn hy.1

theorem Mtb_not_Hae : ¬ MtbF.Valid Hae := fun h => by
  have h0 := (MtbF.holds_all _ _ _ _).mp ((MtbF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  have e := ((MtbF.holds_eqv _ _ _ _ _ _).mp h0).1
  exact Code.arr_ne_left (Code.e : Code Empty) .t e.symm

theorem Mtb_tr_Cantor : MtbF.Tr Cantor ↔
    ∀ a, ∃ G : univU.El a → TV, ∀ y : univU.El a, ¬ MtbF.eqv (.arr a .t) a G y := Iff.rfl

/-- A property and an item of its own argument type are never identified: their types differ. -/
theorem Mtb_Cantor : MtbF.Valid Cantor := (MtbF.valid_iff_tr _).mpr <| Mtb_tr_Cantor.mpr
  fun a => ⟨fun _ => (True, true), fun _ h => Code.arr_ne_left a .t h.1⟩

/-! ## The Leibniz laws -/

/-- `λγ.λz:γ. ∃_{γ→t} F (F z ∧ F ≡_{γ→t, t→t} λp.p)`: at `t`, true of exactly the true propositions. -/
def Mtb_PredId : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (ex tv0.pred (conj (.app (.var .here) (.var (.there .here)))
    (eqv tv0.pred (Ty.arrow tyT tyT) (.var .here) (.lam tyT (.var .here))))))

theorem Mtb_tr_LLPoly : MtbF.Tr (LLPoly Mtb_PredId) ↔ ∀ a b (x : univU.El a) (y : univU.El b),
    MtbF.eqv a b x y →
    (∃ F : univU.El a → TV, (F x).1 ∧ MtbF.eqv (.arr a .t) (.arr .t .t) F (fun p => p)) →
    (∃ F : univU.El b → TV, (F y).1 ∧ MtbF.eqv (.arr b .t) (.arr .t .t) F (fun p => p)) := Iff.rfl

/-- `(True, false)` and `(False, false)` are identified, but only the first is true. -/
theorem Mtb_not_LLPoly : ¬ MtbF.Valid (LLPoly Mtb_PredId) := fun h => by
  obtain ⟨F, hF, _, e | ⟨s, _⟩⟩ := Mtb_tr_LLPoly.mp ((MtbF.valid_iff_tr _).mp h) .t .t (True, false)
    (False, false) ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩ ⟨fun p => p, trivial, ⟨rfl, Or.inl HEq.rfl⟩⟩
  · have hF' : F = fun p => p := eq_of_heq e
    subst hF'
    exact hF
  · exact (s : False).elim

theorem Mtb_tr_Bridge : MtbF.Tr (Bridge Mtb_PredId) ↔ ∀ a b (x : univU.El a) (y : univU.El b),
    MtbF.eqv a b x y ∧ MtbF.teq a b →
    (∃ F : univU.El a → TV, (F x).1 ∧ MtbF.eqv (.arr a .t) (.arr .t .t) F (fun p => p)) →
    (∃ F : univU.El b → TV, (F y).1 ∧ MtbF.eqv (.arr b .t) (.arr .t .t) F (fun p => p)) := Iff.rfl

/-- The same predicate refutes LL≡/≈: the two propositions are items of the same type. -/
theorem Mtb_not_Bridge : ¬ MtbF.Valid (Bridge Mtb_PredId) := fun h => by
  obtain ⟨F, hF, _, e | ⟨s, _⟩⟩ := Mtb_tr_Bridge.mp ((MtbF.valid_iff_tr _).mp h) .t .t (True, false)
    (False, false) ⟨⟨rfl, Or.inr ⟨rfl, rfl⟩⟩, rfl⟩ ⟨fun p => p, trivial, ⟨rfl, Or.inl HEq.rfl⟩⟩
  · have hF' : F = fun p => p := eq_of_heq e
    subst hF'
    exact hF
  · exact (s : False).elim

/-! ## The congruence principles -/

theorem Mtb_tr_WCong : MtbF.Tr WCong ↔ ∀ a b c d (f : univU.El a → univU.El c) (g : univU.El b → univU.El d) x y,
    (MtbF.teq a b ∧ MtbF.teq c d) ∧ (MtbF.eqv (.arr a c) (.arr b d) f g ∧ MtbF.eqv a b x y) →
      MtbF.eqv c d (f x) (g y) := Iff.rfl

/-- `λp.(p, true)` sends the identified `(True, false)` and `(False, false)` to distinct
propositions with the tag `true`. -/
theorem Mtb_not_WCong : ¬ MtbF.Valid WCong := fun h => by
  have h1 := Mtb_tr_WCong.mp ((MtbF.valid_iff_tr _).mp h) .t .t .t .t (fun p : TV => (p.1, true))
    (fun p : TV => (p.1, true)) (True, false) (False, false)
    ⟨⟨rfl, rfl⟩, ⟨rfl, Or.inl HEq.rfl⟩, ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
  rcases h1.2 with e | ⟨s, _⟩
  · exact (congrArg Prod.fst (eq_of_heq e)).mp trivial
  · exact Bool.noConfusion (s : true = false)

theorem Mtb_not_Cong : ¬ MtbF.Valid Cong := fun h => by
  have h1 := MtbF.tr_Cong.mp ((MtbF.valid_iff_tr _).mp h) .t .t .t .t (fun p : TV => (p.1, true))
    (fun p : TV => (p.1, true)) (True, false) (False, false)
    ⟨⟨rfl, Or.inl HEq.rfl⟩, ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
  rcases h1.2 with e | ⟨s, _⟩
  · exact (congrArg Prod.fst (eq_of_heq e)).mp trivial
  · exact Bool.noConfusion (s : true = false)

/-- `λx.(True, false)` and `λx.(False, false)` have identified values but are distinct. -/
theorem Mtb_not_PExt : ¬ MtbF.Valid PExt := fun h => by
  have h1 := MtbF.tr_PExt.mp ((MtbF.valid_iff_tr _).mp h) .e .t .t (fun _ => (True, false))
    (fun _ => (False, false)) (fun _ => ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩)
  rcases h1.2 with e | ⟨s, _⟩
  · exact (congrArg Prod.fst (congrFun (eq_of_heq e) ())).mp trivial
  · exact (s : False).elim

/-! ## `≈` -/

theorem Mtb_Inj : MtbF.Valid Inj := (MtbF.valid_iff_tr _).mpr <| MtbF.tr_Inj.mpr fun _ _ _ _ h => by
  injection h with h1 h2; exact ⟨h1, h2⟩

theorem Mtb_Recovery : MtbF.Valid Recovery := (MtbF.valid_iff_tr _).mpr <|
  (show MtbF.Tr Recovery ↔ ∀ a b c d, MtbF.teq (.arr a c) (.arr b d) ∧ MtbF.teq a b → MtbF.teq c d
    from Iff.rfl).mpr fun _ _ _ _ ⟨h, _⟩ => by injection h

theorem Mtb_ExtT : MtbF.Valid ExtT := (MtbF.valid_iff_tr _).mpr <| MtbF.tr_ExtT.mpr fun a _ ⟨h1, _⟩ =>
  (h1 (Classical.choice (Univ.El_nonempty (U := univU) a))).elim fun _ h => h.1

/-- `□(∀x∃y x ≡ y)` is false, since the quantified proposition has the tag `false`. -/
theorem Mtb_IntT : MtbF.Valid IntT := by
  intro ρ env a b hc
  have hs := Mtb_box_tag _ _ _ ((MtbF.holds_conj _ _ _ _).mp hc).1
  have h0 : (MtbF.eval (subT (Γ := (Ctx.nil.text).text)) (scons b (scons a ρ)) env).2 = false :=
    MtbF.eval_all_snd _ _ _ _
  exact (Bool.false_ne_true (h0.symm.trans hs)).elim

/-! ## Necessity of identity and distinctness -/

theorem Mtb_NIEqv : MtbF.Valid NIEqv := by
  intro ρ env a
  refine (MtbF.holds_all _ _ _ _).mpr fun x => (MtbF.holds_all _ _ _ _).mpr fun y h => ?_
  exact Mtb_box_of _ _ _ rfl h

theorem Mtb_NITeq : MtbF.Valid NITeq := by
  intro ρ env a b h
  exact Mtb_box_of _ _ _ rfl h

theorem Mtb_NDTeq : MtbF.Valid NDTeq := by
  intro ρ env a b h
  exact Mtb_box_of _ _ _ rfl h

theorem Mtb_NIX : MtbF.Valid NIX := by
  intro ρ env a b
  refine (MtbF.holds_all _ _ _ _).mpr fun x => (MtbF.holds_all _ _ _ _).mpr fun y h => ?_
  exact Mtb_box_of _ _ _ rfl h

theorem Mtb_NDX : MtbF.Valid NDX := by
  intro ρ env a b
  refine (MtbF.holds_all _ _ _ _).mpr fun x => (MtbF.holds_all _ _ _ _).mpr fun y h => ?_
  exact Mtb_box_of _ _ _ rfl h

/-! ## Booleanism, Classicism and the Identity Identity -/

/-- `¬¬p` has the tag `true`, while `p` may have the tag `false`. -/
theorem Mtb_not_DNeg : ¬ MtbF.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MtbF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (True, false)
  rcases ((MtbF.holds_eqv_t _ _ _ _).mp h0).2 with e | ⟨s, _⟩
  · exact Bool.noConfusion (congrArg Prod.snd (eq_of_heq e) : true = false)
  · exact Bool.noConfusion (s : true = false)

theorem Mtb_not_Bool : ¬ ∀ φ, BoolSch φ → MtbF.Valid φ := fun h => Mtb_not_DNeg (h _ DNeg_bool)

/-- Classicism proves Booleanism, which fails. -/
theorem Mtb_not_Class : ¬ ∀ χ, ClassSch χ → MtbF.Valid χ := fun h =>
  Mtb_not_DNeg (MtbF.soundness Mtb_model h (d_Bool_of_Class (S := ClassSch) (fun _ hχ => hχ) _ DNeg_bool))

theorem Mtb_tr_IdId : MtbF.Tr IdId ↔ ∀ a (x y : univU.El a), MtbF.eqv .t .t (MtbF.eqv a a x y, true)
    ((∀ P : univU.El a → TV, (P x).1 → (P y).1 : Prop), false) := Iff.rfl

/-- `x ≡ y` has the tag `true`, and the quantified `∀F(Fx → Fy)` the tag `false`. -/
theorem Mtb_not_IdId : ¬ MtbF.Valid IdId := fun h => by
  have h0 := Mtb_tr_IdId.mp ((MtbF.valid_iff_tr _).mp h) .e () ()
  rcases h0.2 with e | ⟨s, _⟩
  · exact Bool.noConfusion (congrArg Prod.snd (eq_of_heq e) : true = false)
  · exact Bool.noConfusion (s : true = false)

/-! ## Barcan formulas for the type quantifiers, and Type Necessitism -/

/-- `𝔸α ⊤` is type-quantified, so it has the tag `false` and is not identical to `⊤`. -/
theorem Mtb_not_TBF : ¬ ∀ χ, TBFSch χ → MtbF.Valid χ := fun h => by
  have h0 := h _ ⟨topF, rfl⟩ (fun i => i.elim0) ()
  have hb := (MtbF.holds_imp _ _ _ _).mp h0 (fun _ => (MtbF.holds_eqv_t _ _ _ _).mpr ⟨rfl, Or.inl HEq.rfl⟩)
  exact Bool.noConfusion (Mtb_box_tag _ _ _ hb : false = true)

theorem Mtb_TCBF : ∀ χ, TCBFSch χ → MtbF.Valid χ := by
  rintro χ ⟨φ, rfl⟩ ρ env hb
  exact Bool.noConfusion (Mtb_box_tag _ _ _ hb : false = true)

theorem Mtb_not_TNec : ¬ MtbF.Valid TNec := fun h => by
  have hb := (MtbF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e
  exact Bool.noConfusion (Mtb_box_tag _ _ _ hb : false = true)

/-! ## Barcan formulas for the item quantifiers, and Necessitism -/

theorem Mtb_tr_BF : MtbF.Tr BF ↔
    ∀ a (G : univU.El a → TV), (∀ x, MtbF.eqv .t .t (G x) ((¬ ∀ p : TV, p.1 : Prop), true)) →
      MtbF.eqv .t .t ((∀ x, (G x).1 : Prop), false) ((¬ ∀ p : TV, p.1 : Prop), true) := Iff.rfl

theorem Mtb_tr_CBF : MtbF.Tr CBF ↔
    ∀ a (G : univU.El a → TV), MtbF.eqv .t .t ((∀ x, (G x).1 : Prop), false) ((¬ ∀ p : TV, p.1 : Prop), true) →
      ∀ x, MtbF.eqv .t .t (G x) ((¬ ∀ p : TV, p.1 : Prop), true) := Iff.rfl

theorem Mtb_tr_Nec : MtbF.Tr Nec ↔
    ∀ a (x : univU.El a), MtbF.eqv .t .t ((∃ y, MtbF.eqv a a x y : Prop), false)
      ((¬ ∀ p : TV, p.1 : Prop), true) := Iff.rfl

/-- `∀x ⊤` is quantified, so it has the tag `false`: `□⊤` holds of every entity, but `□∀x ⊤` is false. -/
theorem Mtb_not_BF : ¬ MtbF.Valid BF := fun h => by
  have h1 := Mtb_tr_BF.mp ((MtbF.valid_iff_tr _).mp h) .e (fun _ => ((¬ ∀ p : TV, p.1 : Prop), true))
    (fun _ => ⟨rfl, Or.inl HEq.rfl⟩)
  rcases h1.2 with e | ⟨_, s⟩
  · exact Bool.noConfusion (congrArg Prod.snd (eq_of_heq e) : false = true)
  · exact Bool.noConfusion (s : true = false)

theorem Mtb_CBF : MtbF.Valid CBF := (MtbF.valid_iff_tr _).mpr <| Mtb_tr_CBF.mpr fun _ _ h => by
  rcases h.2 with e | ⟨_, s⟩
  · exact Bool.noConfusion (congrArg Prod.snd (eq_of_heq e) : false = true)
  · exact Bool.noConfusion (s : true = false)

/-- `∃y (x ≡ y)` is quantified, so it has the tag `false` and is not identical to `⊤`. -/
theorem Mtb_not_Nec : ¬ MtbF.Valid Nec := fun h => by
  have h1 := Mtb_tr_Nec.mp ((MtbF.valid_iff_tr _).mp h) .e (show univU.El .e from ())
  rcases h1.2 with e | ⟨_, s⟩
  · exact Bool.noConfusion (congrArg Prod.snd (eq_of_heq e) : false = true)
  · exact Bool.noConfusion (s : true = false)

end Tg
end PIF
