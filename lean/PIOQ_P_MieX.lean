import PIBF
set_option autoImplicit false

namespace PIF
namespace Wd

/-!
# More about `𝔐_ie,c,x`

In `𝔐_ie,c,x` identity of types is identity of codes, at every world; so Inj≈, Recovery, and ND≈
hold. Identity of propositions is identity, so TBF holds. Only items of types built from `e`, `d`
and `→` (never `t`) are identified across types; so nothing is identified with a predicate (Slogan
holds), and no proposition has a twin (Twin fails).
-/

theorem MieX_tr_Twin : MieXF.Tr Twin ↔ ∀ a (x : MieXF.U.El a), ∃ b, ¬ MieXF.teq a b MieXF.U.w0 ∧
    ∃ y : MieXF.U.El b, MieXF.eqv a b x y MieXF.U.w0 := Iff.rfl

theorem MieX_tr_Recovery : MieXF.Tr Recovery ↔ ∀ a b c d, MieXF.teq (.arr a c) (.arr b d) MieXF.U.w0 ∧
    MieXF.teq a b MieXF.U.w0 → MieXF.teq c d MieXF.U.w0 := Iff.rfl

/-- No predicate type is free of `t`, so the entity is identified with no predicate. -/
theorem MieX_Slogan : MieXF.Valid Slogan :=
  (MieXF.valid_iff_tr _).mpr <| MieXF.tr_Slogan.mpr fun _ b _ h =>
    h.elim (fun h => nomatch h.1) (fun h => nomatch (show imgU Code.e = imgU (Code.arr b .t) from h.2.2.1))

/-- A proposition is identified only with itself, so it has no twin. -/
theorem MieX_not_Twin : ¬ MieXF.Valid Twin := fun h => by
  obtain ⟨b, hb, _, hy⟩ := MieX_tr_Twin.mp ((MieXF.valid_iff_tr _).mp h) .t (fun _ => True)
  rcases hy with ⟨e, _⟩ | ⟨_, hx⟩
  · exact hb e
  · exact hx.2.2

theorem MieX_Inj : MieXF.Valid Inj := MieXF.Inj_of fun _ _ _ => Iff.rfl

theorem MieX_Recovery : MieXF.Valid Recovery :=
  (MieXF.valid_iff_tr _).mpr <| MieX_tr_Recovery.mpr fun a b c d ⟨h, _⟩ => by
    have h' : Code.arr a c = Code.arr b d := h
    exact (Code.arr.inj h').2

theorem MieX_NDTeq : MieXF.Valid NDTeq :=
  MieXF.NDTeq_of (fun _ => Or.inl ⟨rfl, HEq.rfl⟩) fun _ _ _ => Iff.rfl

theorem MieX_TBF : ∀ χ, TBFSch χ → MieXF.Valid χ :=
  MieXF.TBF_of fun _ _ => ⟨fun h => MieX_eq _ _ _ _ h, fun h => h ▸ Or.inl ⟨rfl, HEq.rfl⟩⟩

end Wd
end PIF
