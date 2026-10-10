import PIKripke

/-!
# Kripke models of PI + Classicism

`𝔐_k,bf`: the Barcan formula for types fails. There are two worlds; the actual world sees both, and
the other sees only itself. A base type `d` with a single item exists only at the other world.
-/
set_option autoImplicit false

namespace PIF
namespace Kr
open Tm

/-- Codes with no base type in them. -/
def noBase : Code Unit → Prop
  | .base _ => False
  | .arr a c => noBase a ∧ noBase c
  | _ => True

def UBF : Univ where
  W := Bool
  w0 := true
  R := fun w v => w = true ∨ v = false
  Rrefl := fun w => by cases w <;> simp
  Rtrans := by
    intro u v w h1 h2
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · rcases h2 with h2 | h2
      · exact absurd (h1.symm.trans h2) Bool.false_ne_true
      · exact Or.inr h2
  E := Bool
  Base := Unit
  B := fun _ => Unit
  neE := ⟨true⟩
  neB := fun _ => ⟨()⟩
  re := fun _ x y => x = y
  rb := fun _ _ _ _ => True
  re_refl := fun _ _ => rfl
  re_symm := fun _ _ _ h => h.symm
  re_trans := fun _ _ _ _ h1 h2 => h1.trans h2
  re_mono := fun _ _ _ _ _ h => h
  rb_refl := fun _ _ _ => trivial
  rb_symm := fun _ _ _ _ _ => trivial
  rb_trans := fun _ _ _ _ _ _ _ => trivial
  rb_mono := fun _ _ _ _ _ _ _ => trivial
  D := fun w a => w = false ∨ noBase a
  D_e := fun _ => Or.inr trivial
  D_t := fun _ => Or.inr trivial
  D_arr := by
    intro w a c ha hc
    rcases ha with ha | ha
    · exact Or.inl ha
    · rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr ⟨ha, hc⟩
  D_mono := by
    intro w v a h ha
    rcases ha with ha | ha
    · subst ha
      rcases h with h | h
      · exact absurd h Bool.false_ne_true
      · exact Or.inl h
    · exact Or.inr ha

/-- Each type with no base type in it has two items which are distinct at every world. -/
theorem two_items : ∀ a : Code Unit, noBase a → ∃ x y : UBF.El a,
    (∀ w, UBF.rel a w x x) ∧ (∀ w, UBF.rel a w y y) ∧ ∀ w, ¬ UBF.rel a w x y
  | .e, _ => ⟨true, false, fun _ => rfl, fun _ => rfl, fun _ h => Bool.noConfusion h⟩
  | .t, _ => ⟨fun _ => True, fun _ => False, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun w h => (h w (UBF.Rrefl w)).mp trivial⟩
  | .base _, h => h.elim
  | .arr a c, ⟨_, hc⟩ => by
    obtain ⟨y1, y2, h1, h2, h12⟩ := two_items c hc
    obtain ⟨x0, hx0⟩ := UBF.adm_nonempty a
    refine ⟨fun _ => y1, fun _ => y2, fun _ v _ _ _ _ => h1 v, fun _ v _ _ _ _ => h2 v, fun w h => ?_⟩
    exact h12 w (h w (UBF.Rrefl w) x0 x0 (hx0 w))

abbrev MbfK : Frame := Frame.simple UBF

/-- The instance of TBF which fails: `φ(α)` says that `α` has two distinct items. -/
def phiBF : Fm Ctx.nil.text := neg (all tv0 (all tv0 (eqv tv0 tv0 (.var (.there .here)) (.var .here))))

theorem phiBF_iff (a : Code Unit) (w : Bool) :
    MbfK.HoldsAt phiBF (scons a (fun i => i.elim0)) () w ↔
      ¬ ∀ x : UBF.El a, UBF.rel a w x x → ∀ y : UBF.El a, UBF.rel a w y y → UBF.rel a w x y := by
  refine (MbfK.holdsAt_neg _ _ _ _).trans (not_congr ?_)
  refine (MbfK.holdsAt_all _ _ _ _ _).trans (forall_congr' fun x => imp_congr Iff.rfl ?_)
  refine (MbfK.holdsAt_all _ _ _ _ _).trans (forall_congr' fun y => imp_congr Iff.rfl ?_)
  exact (MbfK.holdsAt_eqv _ _ _ _ _ _ _).trans (Frame.simple_eqv_same UBF _ _ _ _)

theorem Mbf_not_TBF : ¬ MbfK.Valid (TBFI phiBF) := by
  refine Frame.simple_not_Valid UBF fun h => ?_
  have hA : MbfK.HoldsAt (tall (boxF phiBF)) (fun i => i.elim0) () UBF.w0 := by
    refine (MbfK.holdsAt_tall _ _ _ _).mpr fun a ha => (Frame.simple_box UBF _ _ _ _).mpr fun v _ => ?_
    have hna : noBase a := ha.resolve_left (fun h => Bool.noConfusion (h : true = false))
    obtain ⟨x, y, hx, hy, hxy⟩ := two_items a hna
    exact (phiBF_iff a v).mpr fun h => hxy v (h x (hx v) y (hy v))
  have hB := (Frame.simple_box UBF _ _ _ _).mp ((MbfK.holdsAt_imp _ _ _ _ _).mp h hA) false (Or.inl rfl)
  have hd := (MbfK.holdsAt_tall _ _ _ _).mp hB (.base ()) (Or.inl rfl)
  exact (phiBF_iff (.base ()) false).mp hd fun _ _ _ _ => trivial

theorem Mbf_not_TBFSch : ¬ ∀ χ, TBFSch χ → MbfK.Valid χ := fun h => Mbf_not_TBF (h _ ⟨phiBF, rfl⟩)

theorem Mbf_Class : ∀ χ, ClassSch χ → MbfK.Valid χ := Frame.simple_Class UBF
theorem Mbf_LLEqv : MbfK.Valid LLEqv := fun ρ hρ env henv => Frame.simple_LLEqv UBF _ ρ hρ env henv
theorem Mbf_isModelAt : MbfK.IsModelAt := Frame.simple_isModelAt UBF
theorem Mbf_Disjoint : MbfK.Valid Disjoint := Frame.simple_Disjoint UBF
theorem Mbf_Slogan : MbfK.Valid Slogan := Frame.simple_Slogan UBF
theorem Mbf_Cong : MbfK.Valid Cong := Frame.simple_Cong UBF
theorem Mbf_Inj : MbfK.Valid Inj := Frame.simple_Inj UBF
theorem Mbf_Recovery : MbfK.Valid Recovery := Frame.simple_Recovery UBF
theorem Mbf_ExtT : MbfK.Valid ExtT := Frame.simple_ExtT UBF
theorem Mbf_IntT : MbfK.Valid IntT := Frame.simple_IntT UBF

end Kr
end PIF
