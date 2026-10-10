import PIBF
set_option autoImplicit false

namespace PIF
namespace Wd

/-!
# More about `𝔐_ie,2`

In `𝔐_ie,2` (`Wd.ME2F`) the only identification across types is that of the entity with the item
`true` of `d`, at the actual world; at the other world identity is identity. `≈` is identity of
types, the same at every world.

* Slogan holds and Haecceitism fails: nothing is identified with an item of a function type
  except that item itself.
* Twin fails: a proposition is identified only with itself.
* Cong and PCong hold: identified functions are the very same function, at one type.
* PExt fails: `λx.e₀ : e→e` and `λx.true : e→d` agree argument by argument at the actual world.
* Inj≈, Recovery and ND≈ hold, since `≈` is rigid identity of types.
* ND× holds: whatever is identified at the other world is identified at the actual world.
* TBF and BF hold, since identity of propositions is identity and domains are constant.
-/

theorem ME2_tr_Twin : ME2F.Tr Twin ↔ ∀ a (x : ME2F.U.El a), ∃ b, ¬ ME2F.teq a b ME2F.U.w0 ∧
    ∃ y : ME2F.U.El b, ME2F.eqv a b x y ME2F.U.w0 := Iff.rfl

theorem ME2_tr_PCong : ME2F.Tr PCong ↔ ∀ a c d (f : ME2F.U.El a → ME2F.U.El c)
    (g : ME2F.U.El a → ME2F.U.El d) x,
    ME2F.eqv (.arr a c) (.arr a d) f g ME2F.U.w0 → ME2F.eqv c d (f x) (g x) ME2F.U.w0 := Iff.rfl

theorem ME2_tr_Recovery : ME2F.Tr Recovery ↔ ∀ a b c d, ME2F.teq (.arr a c) (.arr b d) ME2F.U.w0 ∧
    ME2F.teq a b ME2F.U.w0 → ME2F.teq c d ME2F.U.w0 := Iff.rfl

theorem ME2_tr_Hae : ME2F.Tr Hae ↔ ∀ a (x : ME2F.U.El a),
    ME2F.eqv a (.arr a .t) x (fun y => ME2F.eqv a a y x) ME2F.U.w0 := Iff.rfl

/-- The cross-type identification relates only the entity and an item of `d`. -/
theorem ME2_XE_fst {r s : RE2} (h : XE r s) :
    (r.1 = .e ∧ s.1 = .base ()) ∨ (r.1 = .base () ∧ s.1 = .e) := by
  rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr ⟨rfl, h1⟩

/-- Identity of propositions, at the actual world, is identity. -/
theorem ME2_hb : ∀ p q, ME2F.eqv .t .t p q ME2F.U.w0 ↔ p = q :=
  fun _ _ => ⟨fun h => ME2_eq _ _ _ _ h, fun h => h ▸ Or.inl ⟨rfl, HEq.rfl⟩⟩

/-- Items of function types are identified only with themselves. -/
theorem ME2_arr {a b c d : Code Unit} {f : ME2F.U.El (.arr a c)} {g : ME2F.U.El (.arr b d)} {w : Bool}
    (h : ME2F.eqv (.arr a c) (.arr b d) f g w) : a = b ∧ c = d ∧ HEq f g := by
  rcases h with ⟨e, hfg⟩ | ⟨_, hx⟩
  · injection e with ea ec
    exact ⟨ea, ec, hfg⟩
  · rcases ME2_XE_fst hx with ⟨h, _⟩ | ⟨h, _⟩ <;> exact nomatch h

/-! ## Slogan, Haecceitism, Twin -/

/-- The entity is identified with no predicate. -/
theorem ME2_Slogan : ME2F.Valid Slogan :=
  (ME2F.valid_iff_tr _).mpr <| ME2F.tr_Slogan.mpr fun _ b _ h => by
    rcases h with ⟨e, _⟩ | ⟨_, hx⟩
    · exact nomatch e
    · rcases ME2_XE_fst hx with ⟨_, h⟩ | ⟨h, _⟩ <;> exact nomatch h

/-- The entity is not identified with its haecceity, which is a predicate. -/
theorem ME2_not_Hae : ¬ ME2F.Valid Hae := fun hv => by
  have h := ME2_tr_Hae.mp ((ME2F.valid_iff_tr _).mp hv) .e ()
  rcases h with ⟨e, _⟩ | ⟨_, hx⟩
  · exact nomatch e
  · rcases ME2_XE_fst hx with ⟨_, h⟩ | ⟨_, h⟩ <;> exact nomatch h

/-- A proposition is identified only with itself, so it has no twin. -/
theorem ME2_not_Twin : ¬ ME2F.Valid Twin := fun hv => by
  obtain ⟨b, hb, _, hy⟩ := ME2_tr_Twin.mp ((ME2F.valid_iff_tr _).mp hv) .t (fun _ => True)
  rcases hy with ⟨e, _⟩ | ⟨_, hx⟩
  · exact hb e
  · rcases ME2_XE_fst hx with ⟨h, _⟩ | ⟨h, _⟩ <;> exact nomatch h

/-! ## Cong, PCong, PExt -/

theorem ME2_cong_core (a b c d : Code Unit) (f : ME2F.U.El a → ME2F.U.El c) (g : ME2F.U.El b → ME2F.U.El d)
    (x : ME2F.U.El a) (y : ME2F.U.El b) (w : Bool)
    (h1 : ME2F.eqv (.arr a c) (.arr b d) f g w) (h2 : ME2F.eqv a b x y w) :
    ME2F.eqv c d (f x) (g y) w := by
  obtain ⟨ea, ec, hfg⟩ := ME2_arr h1
  subst ea; subst ec
  have ef : f = g := eq_of_heq hfg
  subst ef
  have exy : x = y := ME2_eq a x y w h2
  subst exy
  exact Or.inl ⟨rfl, HEq.rfl⟩

/-- Identified functions are the very same function, at one type; so Cong holds. -/
theorem ME2_Cong : ME2F.Valid Cong :=
  (ME2F.valid_iff_tr _).mpr <| ME2F.tr_Cong.mpr fun a b c d f g x y ⟨h1, h2⟩ =>
    ME2_cong_core a b c d f g x y _ h1 h2

theorem ME2_PCong : ME2F.Valid PCong :=
  (ME2F.valid_iff_tr _).mpr <| ME2_tr_PCong.mpr fun a c d f g x h =>
    ME2_cong_core a a c d f g x x _ h (Or.inl ⟨rfl, HEq.rfl⟩)

/-- PExt fails: the constant function from `e` to the entity and the constant function from `e` to
`true : d` agree argument by argument at the actual world, but `e→e` and `e→d` differ. -/
theorem ME2_not_PExt : ¬ ME2F.Valid PExt := fun hv => by
  have h0 := ME2F.tr_PExt.mp ((ME2F.valid_iff_tr _).mp hv) .e .e (.base ())
    (fun _ => (() : ME2F.U.El .e)) (fun _ => ((true : Bool) : ME2F.U.El (.base ())))
    (fun _ => Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)
  obtain ⟨_, ec, _⟩ := ME2_arr h0
  exact nomatch ec

/-! ## `≈` is rigid identity of types -/

theorem ME2_Inj : ME2F.Valid Inj := ME2F.Inj_of fun _ _ _ => Iff.rfl

theorem ME2_Recovery : ME2F.Valid Recovery :=
  (ME2F.valid_iff_tr _).mpr <| ME2_tr_Recovery.mpr fun a b c d ⟨h, _⟩ => by
    have h' : Code.arr a c = Code.arr b d := h
    exact (Code.arr.inj h').2

theorem ME2_NDTeq : ME2F.Valid NDTeq :=
  ME2F.NDTeq_of (fun _ => Or.inl ⟨rfl, HEq.rfl⟩) fun _ _ _ => Iff.rfl

/-! ## ND× -/

/-- Whatever is identified at some world is identified at the actual world; so ND× holds. -/
theorem ME2_NDX : ME2F.Valid NDX :=
  ME2F.NDX_of (fun _ => Or.inl ⟨rfl, HEq.rfl⟩) fun _ _ _ _ h _ hw =>
    h (hw.elim Or.inl (fun hw' => Or.inr ⟨rfl, hw'.2⟩))

/-! ## The Barcan formulas -/

theorem ME2_TBF : ∀ χ, TBFSch χ → ME2F.Valid χ := ME2F.TBF_of ME2_hb

theorem ME2_BF : ME2F.Valid BF := ME2F.BF_of ME2_hb

end Wd
end PIF
