import PIBarcan
import PIAlgModels

/-!
# Models for the Barcan formulas and Type Necessitism
-/
set_option autoImplicit false

namespace PIF

/-! ## Models with worlds: both Barcan formulas hold, since the types are the same at every world -/

namespace Wd
namespace RD
variable (D : RD)

theorem holdsAt_tall {n : Nat} {Γ : Ctx n} (φ : Fm Γ.text) (ρ : D.frame.U.TEnv n) (env : D.frame.U.Env Γ ρ) (w : D.W) :
    D.frame.HoldsAt (Tm.tall φ) ρ env w ↔ ∀ a, D.frame.HoldsAt φ (scons a ρ) env w := Iff.rfl
theorem holdsAt_tex {n : Nat} {Γ : Ctx n} (φ : Fm Γ.text) (ρ : D.frame.U.TEnv n) (env : D.frame.U.Env Γ ρ) (w : D.W) :
    D.frame.HoldsAt (Tm.tex φ) ρ env w ↔ ∃ a, D.frame.HoldsAt φ (scons a ρ) env w := Iff.rfl

theorem TBF_valid : ∀ χ, TBFSch χ → D.frame.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (D.frame.holds_imp _ _ _ _).mpr fun h => ?_
  exact (D.holds_box _ _ _).mpr fun w => (D.holdsAt_tall _ _ _ w).mpr fun a =>
    (D.holds_box _ _ _).mp ((D.frame.holds_tall _ _ _).mp h a) w

theorem TCBF_valid : ∀ χ, TCBFSch χ → D.frame.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (D.frame.holds_imp _ _ _ _).mpr fun h => ?_
  exact (D.frame.holds_tall _ _ _).mpr fun a => (D.holds_box _ _ _).mpr fun w =>
    (D.holdsAt_tall _ _ _ w).mp ((D.holds_box _ _ _).mp h w) a

theorem TNec_valid (hTe : ∀ a w, ∃ b, D.Te a b w) : D.frame.Valid TNec := by
  intro ρ env
  refine (D.frame.holds_tall _ _ _).mpr fun a => (D.holds_box _ _ _).mpr fun w => ?_
  obtain ⟨b, hb⟩ := hTe a w
  exact (D.holdsAt_tex _ _ _ w).mpr ⟨b, (D.frame.holdsAt_teq (Γ := Ctx.nil.text.text) tv1 tv0 _ _ w).mpr hb⟩

theorem not_TNec (a : Code Empty) (w1 : D.W) (h1 : ∀ b, ¬ D.Te a b w1) : ¬ D.frame.Valid TNec := fun h => by
  have hb := (D.holds_box _ _ _).mp ((D.frame.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) a) w1
  obtain ⟨b, hb'⟩ := (D.holdsAt_tex _ _ _ w1).mp hb
  exact h1 b ((D.frame.holdsAt_teq (Γ := Ctx.nil.text.text) tv1 tv0 _ _ w1).mp hb')

end RD

theorem Mw_TBF : ∀ χ, TBFSch χ → DW.frame.Valid χ := DW.TBF_valid
theorem Mw_TCBF : ∀ χ, TCBFSch χ → DW.frame.Valid χ := DW.TCBF_valid
theorem Mw_TNec : DW.frame.Valid TNec := DW.TNec_valid fun a _ => ⟨a, rfl⟩
theorem Mni_TBF : ∀ χ, TBFSch χ → DNI.frame.Valid χ := DNI.TBF_valid
theorem Mni_TCBF : ∀ χ, TCBFSch χ → DNI.frame.Valid χ := DNI.TCBF_valid
theorem Mni_not_TNec : ¬ DNI.frame.Valid TNec := DNI.not_TNec .e false fun _ h => Bool.false_ne_true h.2
theorem Mnd_TNec : DND.frame.Valid TNec := DND.TNec_valid fun a _ => ⟨a, fun _ => rfl⟩
theorem Mie_TNec : DIE.frame.Valid TNec := DIE.TNec_valid fun a _ => ⟨a, rfl⟩
theorem Mnd_TBF : ∀ χ, TBFSch χ → DND.frame.Valid χ := DND.TBF_valid
theorem Mnd_TCBF : ∀ χ, TCBFSch χ → DND.frame.Valid χ := DND.TCBF_valid
theorem Mie_TBF : ∀ χ, TBFSch χ → DIE.frame.Valid χ := DIE.TBF_valid
theorem Mie_TCBF : ∀ χ, TCBFSch χ → DIE.frame.Valid χ := DIE.TCBF_valid

end Wd

/-! ## Tagged models -/

namespace Tg

/-- In `𝔐_z` a type-quantified proposition is never identical to `⊤`, which is unquantified. -/
theorem Mz_not_TBF : ¬ ∀ χ, TBFSch χ → MzF.Valid χ := fun h => by
  have h0 := h _ ⟨topF, rfl⟩ (fun i => i.elim0) ()
  have hb := (MzF.holds_imp _ _ _ _).mp h0 (fun _ => (MzF.holds_eqv_t _ _ _ _).mpr ⟨rfl, HEq.rfl⟩)
  have e := eq_of_heq ((MzF.holds_eqv_t _ _ _ _).mp hb).2
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

theorem Mz_not_TNec : ¬ MzF.Valid TNec := fun h => by
  have hb := (MzF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e
  have e := eq_of_heq ((MzF.holds_eqv_t _ _ _ _).mp hb).2
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

end Tg

/-! ## `𝔐_cb`: TBF and Type Necessitism without TCBF -/

namespace Al

def MbF : Frame where
  U := univI
  eqv := fun a b x y => (a = b ∧ HEq x y, true)
  teq := fun a b => (a = b, false)
  neg := fun p => (¬ p.1, true)
  imp := fun p q => (p.1 → q.1, true)
  cnj := fun p q => (p.1 ∧ q.1, true)
  dsj := fun p q => (p.1 ∨ q.1, true)
  bic := fun p q => (p.1 ↔ q.1, true)
  all := fun _ f => (∀ x, (f x).1, true)
  ex := fun _ f => (∃ x, (f x).1, true)
  tall := fun Q => (∀ a, (Q a).1, true)
  tex := fun Q => (∃ a, (Q a).1, true)
  hneg := fun _ => Iff.rfl
  himp := fun _ _ => Iff.rfl
  hcnj := fun _ _ => Iff.rfl
  hdsj := fun _ _ => Iff.rfl
  hbic := fun _ _ => Iff.rfl
  hall := fun _ _ => Iff.rfl
  hex := fun _ _ => Iff.rfl
  htall := fun _ => Iff.rfl
  htex := fun _ => Iff.rfl

theorem Mb_model : MbF.IsModelPIm :=
  MbF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => ⟨rfl, HEq.rfl⟩) (fun _ _ _ _ h => ⟨h.1.symm, h.2.symm⟩)
    (fun _ _ _ _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)

theorem Mb_top {n : Nat} {Γ : Ctx n} (ρ : MbF.U.TEnv n) (env : MbF.U.Env Γ ρ) :
    MbF.eval (topF : Fm Γ) ρ env = (True, true) :=
  Prod.ext (propext (iff_true_intro (MbF.holds_topF ρ env ⟨(False, true), id⟩))) rfl

theorem Mb_LLEqv : MbF.Valid LLEqv := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => ?_
  refine (MbF.holds_all _ _ _ _).mpr fun x => (MbF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MbF.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (MbF.holds_all _ _ _ _).mpr fun G => (MbF.holds_imp _ _ _ _).mpr fun hGx => ?_
  have h := ((MbF.holds_eqv _ _ _ _ _ _).mp hxy).2
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.trans (cast_heq _ _)))
  subst e
  exact hGx

theorem Mb_TBF : ∀ χ, TBFSch χ → MbF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MbF.holds_imp _ _ _ _).mpr fun h => ?_
  have ha : ∀ a, MbF.eval φ (scons a ρ) env = (True, true) := fun a =>
    (eq_of_heq ((MbF.holds_eqv_t _ _ _ _).mp ((MbF.holds_tall _ _ _).mp h a)).2).trans (Mb_top _ _)
  refine (MbF.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ((?_ : MbF.eval (Tm.tall φ) ρ env = (True, true)).trans (Mb_top _ _).symm)⟩
  exact Prod.ext (propext ⟨fun _ => trivial, fun _ a => cast (congrArg Prod.fst (ha a)).symm trivial⟩) rfl

theorem Mb_TNec : MbF.Valid TNec := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => ?_
  have hv : MbF.eval (Tm.tex (Tm.teq tv1 tv0) : Fm Ctx.nil.text) (scons a ρ) env = (True, true) :=
    Prod.ext (propext ⟨fun _ => trivial, fun _ => by exact ⟨a, rfl⟩⟩) rfl
  exact (MbF.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq (hv.trans (Mb_top (Γ := Ctx.nil.text) _ _).symm)⟩

theorem Mb_not_TCBF : ¬ ∀ χ, TCBFSch χ → MbF.Valid χ := fun h => by
  have h0 := h _ ⟨Tm.teq tv0 tv0, rfl⟩ (fun i => i.elim0) ()
  have hv : MbF.eval (Tm.tall (Tm.teq tv0 tv0) : Fm Ctx.nil) (fun i => i.elim0) () = (True, true) :=
    Prod.ext (propext ⟨fun _ => trivial, fun _ a => by exact (rfl : a = a)⟩) rfl
  have hp : MbF.Holds (boxF (Tm.tall (Tm.teq tv0 tv0) : Fm Ctx.nil)) (fun i => i.elim0) () :=
    (MbF.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq (hv.trans (Mb_top (Γ := Ctx.nil) _ _).symm)⟩
  have hb := (MbF.holds_tall _ _ _).mp ((MbF.holds_imp _ _ _ _).mp h0 hp) .e
  have e := eq_of_heq ((MbF.holds_eqv_t _ _ _ _).mp hb).2
  exact Bool.noConfusion (congrArg Prod.snd (e.trans (Mb_top (Γ := Ctx.nil.text) _ _)) : false = true)

end Al
end PIF
