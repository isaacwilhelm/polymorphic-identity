import PIBF

/-!
# The rest of the profile of `𝔐_k,bf`

The model `MbfK := Frame.simple UBF` of `lean/PIKripkeModels.lean`: two worlds; the actual world
`true` sees both, and `false` sees only itself. Propositions are sets of worlds, and two
propositions are identical at a world just in case they agree at every world it sees.

* ND× fails: the proposition true just at the actual world and the empty proposition differ at the
  actual world, but agree at world `false`, so they are identical there.
* Functional Choice fails: the relation relating a proposition `p` to the entity `true` just in case
  `p` holds (and to `false` otherwise) is total; but a function from propositions to entities which
  is an item at the actual world respects identity at world `false`, so it cannot tell apart the
  two propositions above, which differ in truth value at the actual world.
-/
set_option autoImplicit false

namespace PIF
namespace Kr
open Tm

/-- The proposition true just at the actual world. -/
def MbfK_p1 : UBF.El .t := fun w => w = true

/-- The empty proposition. -/
def MbfK_p2 : UBF.El .t := fun _ => False

theorem MbfK_p1_adm (w : Bool) : UBF.rel .t w MbfK_p1 MbfK_p1 := fun _ _ => Iff.rfl

theorem MbfK_p2_adm (w : Bool) : UBF.rel .t w MbfK_p2 MbfK_p2 := fun _ _ => Iff.rfl

/-- The two propositions are identical at world `false`, which sees only itself. -/
theorem MbfK_p12_false : UBF.rel .t false MbfK_p1 MbfK_p2 := by
  intro v hv
  have hv' : v = false := hv.resolve_left Bool.false_ne_true
  subst hv'
  exact ⟨fun h => Bool.false_ne_true h, False.elim⟩

/-- The two propositions are not identical at the actual world. -/
theorem MbfK_p12_true : ¬ UBF.rel .t true MbfK_p1 MbfK_p2 := fun h =>
  (h true (Or.inl rfl)).mp rfl

theorem MbfK_not_NDX : ¬ MbfK.Valid NDX := by
  refine Frame.simple_not_Valid UBF fun h => ?_
  have h1 := (MbfK.holdsAt_tall _ _ _ _).mp ((MbfK.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)) .t
    (Or.inr trivial)
  have h2 := (MbfK.holdsAt_all _ _ _ _ _).mp ((MbfK.holdsAt_all _ _ _ _ _).mp h1 MbfK_p1 (MbfK_p1_adm true))
    MbfK_p2 (MbfK_p2_adm true)
  refine (MbfK.holdsAt_neg _ _ _ _).mp ((Frame.simple_box UBF _ _ _ _).mp ((MbfK.holdsAt_imp _ _ _ _ _).mp h2
    ((MbfK.holdsAt_neg _ _ _ _).mpr fun he => ?_)) false (Or.inr rfl)) ?_
  · exact MbfK_p12_true ((Frame.simple_eqv_same UBF .t MbfK_p1 MbfK_p2 true).mp
      ((MbfK.holdsAt_eqv _ _ _ _ _ _ _).mp he))
  · exact (MbfK.holdsAt_eqv _ _ _ _ _ _ _).mpr
      ((Frame.simple_eqv_same UBF .t MbfK_p1 MbfK_p2 false).mpr MbfK_p12_false)

/-- The relation relating a proposition `p` to `true` just where `p` holds, and to `false` just
where it fails. -/
def MbfK_R : UBF.El (.arr .t (.arr .e .t)) := fun p y w => (p w ↔ y = true)

theorem MbfK_R_adm : UBF.rel (.arr .t (.arr .e .t)) true MbfK_R MbfK_R := by
  intro v _ p p' hp u hu y y' hy s hs
  have ey : y = y' := hy
  subst ey
  have hps : p s ↔ p' s := hp s (UBF.Rtrans _ _ _ hu hs)
  show (p s ↔ y = true) ↔ (p' s ↔ y = true)
  exact ⟨fun h => hps.symm.trans h, fun h => hps.trans h⟩

/-- Every proposition is related to something; but a function which is an item at the actual world
cannot tell apart `p1` and `p2`, which are identical at world `false`. -/
theorem MbfK_not_Choice : ¬ MbfK.Valid Choice := by
  refine Frame.simple_not_Valid UBF fun h => ?_
  have h1 := (MbfK.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)
  have h2 := (MbfK.holdsAt_tall _ _ _ _).mp h1 .e (Or.inr trivial)
  have h3 := (MbfK.holdsAt_all _ _ _ _ _).mp h2 MbfK_R MbfK_R_adm
  have h4 := (MbfK.holdsAt_imp _ _ _ _ _).mp h3 ((MbfK.holdsAt_all _ _ _ _ _).mpr fun p _ => by
    by_cases hp : (p : Bool → Prop) true
    · exact (MbfK.holdsAt_ex _ _ _ _ _).mpr ⟨true, (rfl : true = true),
        show ((p : Bool → Prop) true ↔ true = true) from ⟨fun _ => rfl, fun _ => hp⟩⟩
    · exact (MbfK.holdsAt_ex _ _ _ _ _).mpr ⟨false, (rfl : false = false),
        show ((p : Bool → Prop) true ↔ false = true) from ⟨fun h' => absurd h' hp, fun h' => Bool.noConfusion h'⟩⟩)
  obtain ⟨f, hf, hfx⟩ := (MbfK.holdsAt_ex _ _ _ _ _).mp h4
  have hall := (MbfK.holdsAt_all _ _ _ _ _).mp hfx
  have f1 : MbfK_p1 true ↔ (f : (Bool → Prop) → Bool) MbfK_p1 = true := hall MbfK_p1 (MbfK_p1_adm true)
  have f2 : MbfK_p2 true ↔ (f : (Bool → Prop) → Bool) MbfK_p2 = true := hall MbfK_p2 (MbfK_p2_adm true)
  have e : (f : (Bool → Prop) → Bool) MbfK_p1 = (f : (Bool → Prop) → Bool) MbfK_p2 :=
    hf false (Or.inr rfl) MbfK_p1 MbfK_p2 MbfK_p12_false
  exact f2.mpr (e ▸ f1.mp rfl)

end Kr
end PIF
