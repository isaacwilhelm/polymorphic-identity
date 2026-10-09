import PIAlgI

/-!
# A model with intensional functions

`𝔐_if`: propositions are truth values and identity is identity, but two items of a function type
can take the same value everywhere and still differ (in their tag). So PExt fails, while Disjoint
and LL≡ hold.
-/
set_option autoImplicit false

namespace PIF
namespace AlI

def univF : Univ where
  P := Prop
  V := fun p => p
  p0 := True
  E := Unit
  Base := Empty
  B := Empty.elim
  neE := ⟨()⟩
  neB := fun b => b.elim

def MifF : Frame where
  U := univF
  eqv := fun a b x y => a = b ∧ HEq x y
  teq := fun a b => a = b
  neg := Not
  imp := fun p q => p → q
  cnj := And
  dsj := Or
  bic := Iff
  all := fun _ f => ∀ x, f x
  ex := fun _ f => ∃ x, f x
  tall := fun Q => ∀ a, Q a
  tex := fun Q => ∃ a, Q a
  hneg := fun _ => Iff.rfl
  himp := fun _ _ => Iff.rfl
  hcnj := fun _ _ => Iff.rfl
  hdsj := fun _ _ => Iff.rfl
  hbic := fun _ _ => Iff.rfl
  hall := fun _ _ => Iff.rfl
  hex := fun _ _ => Iff.rfl
  htall := fun _ => Iff.rfl
  htex := fun _ => Iff.rfl

theorem Mif_model : MifF.IsModelPIm :=
  MifF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => ⟨rfl, HEq.rfl⟩) (fun _ _ _ _ h => ⟨h.1.symm, h.2.symm⟩)
    (fun _ _ _ _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)

theorem Mif_LLEqv : MifF.Valid LLEqv := by
  intro ρ env
  refine (MifF.holds_tall _ _ _).mpr fun a => ?_
  refine (MifF.holds_all _ _ _ _).mpr fun x => (MifF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MifF.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (MifF.holds_all _ _ _ _).mpr fun G => (MifF.holds_imp _ _ _ _).mpr fun hGx => ?_
  have h := ((MifF.holds_eqv _ _ _ _ _ _).mp hxy).2
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.trans (cast_heq _ _)))
  subst e
  exact hGx

theorem Mif_Disjoint : MifF.Valid Disjoint := by
  intro ρ env
  refine (MifF.holds_tall _ _ _).mpr fun a => (MifF.holds_tall _ _ _).mpr fun b => ?_
  refine (MifF.holds_imp _ _ _ _).mpr fun hn => ?_
  refine (MifF.holds_all _ _ _ _).mpr fun x => (MifF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MifF.holds_neg _ _ _).mpr fun hxy => ?_
  exact (MifF.holds_neg _ _ _).mp hn ((MifF.holds_teq _ _ _ _).mpr ((MifF.holds_eqv _ _ _ _ _ _).mp hxy).1)

theorem Mif_not_PExt : ¬ MifF.Valid PExt := fun h => by
  have h0 := (MifF.holds_tall _ _ _).mp ((MifF.holds_tall _ _ _).mp ((MifF.holds_tall _ _ _).mp
    (h (fun i => i.elim0) ()) .e) .e) .e
  have h1 := (MifF.holds_all _ _ _ _).mp ((MifF.holds_all _ _ _ _).mp h0 ((fun _ => (), true))) ((fun _ => (), false))
  have h2 := (MifF.holds_imp _ _ _ _).mp h1
    ((MifF.holds_all _ _ _ _).mpr fun x => (MifF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩)
  have e := eq_of_heq ((MifF.holds_eqv _ _ _ _ _ _).mp h2).2
  exact Bool.noConfusion (congrArg Prod.snd e : true = false)

end AlI
end PIF
