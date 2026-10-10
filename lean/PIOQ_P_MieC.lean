import PIBF
set_option autoImplicit false

namespace PIF
namespace Wd

/-!
# More about `𝔐_ie,c`

In `𝔐_ie,c` the only identification across types is that of the entity with the item of `d`, at
the actual world. So items of function types are identified only with themselves: Cong and PCong
hold, while PExt fails (the constant functions into `e` and into `d` agree argument by argument).
No proposition has a twin, so Twin fails. Identity of propositions is identity, and every
quantifier ranges over a fixed domain, so BF holds.
-/

theorem MieC_tr_Twin : MieCF.Tr Twin ↔ ∀ a (x : MieCF.U.El a), ∃ b, ¬ MieCF.teq a b MieCF.U.w0 ∧
    ∃ y : MieCF.U.El b, MieCF.eqv a b x y MieCF.U.w0 := Iff.rfl

theorem MieC_tr_PCong : MieCF.Tr PCong ↔ ∀ a c d (f : MieCF.U.El a → MieCF.U.El c)
    (g : MieCF.U.El a → MieCF.U.El d) x,
    MieCF.eqv (.arr a c) (.arr a d) f g MieCF.U.w0 → MieCF.eqv c d (f x) (g x) MieCF.U.w0 := Iff.rfl

/-- Items of function types are identified only with themselves. -/
theorem MieC_arr {a b c d : Code Unit} {f : MieCF.U.El (.arr a c)} {g : MieCF.U.El (.arr b d)} {w : Bool}
    (h : MieCF.eqv (.arr a c) (.arr b d) f g w) : a = b ∧ c = d ∧ HEq f g := by
  rcases h with ⟨e, hfg⟩ | ⟨_, hx⟩
  · injection e with ea ec
    exact ⟨ea, ec, hfg⟩
  · rcases hx with ⟨h, _⟩ | ⟨h, _⟩ <;> exact nomatch h

theorem MieC_cong_core (a b c d : Code Unit) (f : MieCF.U.El a → MieCF.U.El c) (g : MieCF.U.El b → MieCF.U.El d)
    (x : MieCF.U.El a) (y : MieCF.U.El b) (w : Bool)
    (h1 : MieCF.eqv (.arr a c) (.arr b d) f g w) (h2 : MieCF.eqv a b x y w) :
    MieCF.eqv c d (f x) (g y) w := by
  obtain ⟨ea, ec, hfg⟩ := MieC_arr h1
  subst ea; subst ec
  have ef : f = g := eq_of_heq hfg
  subst ef
  have exy : x = y := MieC_eq a x y w h2
  subst exy
  exact Or.inl ⟨rfl, HEq.rfl⟩

/-- Identified functions are the very same function, at one type; so Cong holds. -/
theorem MieC_Cong : MieCF.Valid Cong :=
  (MieCF.valid_iff_tr _).mpr <| MieCF.tr_Cong.mpr fun a b c d f g x y ⟨h1, h2⟩ =>
    MieC_cong_core a b c d f g x y _ h1 h2

theorem MieC_PCong : MieCF.Valid PCong :=
  (MieCF.valid_iff_tr _).mpr <| MieC_tr_PCong.mpr fun a c d f g x h =>
    MieC_cong_core a a c d f g x x _ h (Or.inl ⟨rfl, HEq.rfl⟩)

/-- PExt fails: the constant functions from `e` into `e` and into `d` agree argument by argument at
the actual world, but `e→e` and `e→d` are not identified. -/
theorem MieC_not_PExt : ¬ MieCF.Valid PExt := fun h => by
  have h0 := MieCF.tr_PExt.mp ((MieCF.valid_iff_tr _).mp h) .e .e (.base ())
    (fun _ => (() : MieCF.U.El .e)) (fun _ => (() : MieCF.U.El (.base ())))
    (fun _ => Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)
  obtain ⟨_, ec, _⟩ := MieC_arr h0
  exact nomatch ec

/-- A proposition is identified only with itself, so it has no twin. -/
theorem MieC_not_Twin : ¬ MieCF.Valid Twin := fun h => by
  obtain ⟨b, hb, _, hy⟩ := MieC_tr_Twin.mp ((MieCF.valid_iff_tr _).mp h) .t (fun _ => True)
  rcases hy with ⟨e, _⟩ | ⟨_, hx⟩
  · exact hb e
  · rcases hx with ⟨h, _⟩ | ⟨h, _⟩ <;> exact nomatch h

/-- Identity of propositions is identity and domains are constant, so BF holds. -/
theorem MieC_BF : MieCF.Valid BF :=
  MieCF.BF_of fun _ _ => ⟨fun h => MieC_eq _ _ _ _ h, fun h => h ▸ Or.inl ⟨rfl, HEq.rfl⟩⟩

end Wd
end PIF
