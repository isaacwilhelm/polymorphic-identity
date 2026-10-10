import PIBF
set_option autoImplicit false

/-!
# Open questions: the profile of `𝔐_E,k`

The standard model `𝔐_E,k` of `PIBridge.lean`: `E = {0,1,2}` with `0 ∼ 1`, and the functions
`k₁ = (0↦0, 1↦0, 2↦2)` and `k₂ = (0↦1, 1↦0, 2↦2)` identified at `e→e`; nothing else is identified
with anything other than itself, and `≈` is identity of types.

* Items are identified only within a type, so Slogan holds; at `t`, `≡` is identity, so Truth,
  ⊤≢⊥, Int≈ and T hold.
* Cong and WCong fail: the function `h = (0↦0, 1↦2, 2↦2)` is identified with itself and `0 ≡ 1`,
  but `h 0 = 0` and `h 1 = 2` are not identified.
* PExt fails: the constant functions `0` and `1` on `e` have identified values but are distinct.
* IdId fails at `0 ≡ 1`, since `0` and `1` differ in their properties; so Classicism fails.
-/

namespace PIF

section MEkP

theorem MEk_hS : ∀ p, ¬ SEk .t p := fun _ h => h

theorem MEk_eqv_t (p q : Prop) : MEk.eqv .t .t p q ↔ p = q := cI_eqv_t MEk_hS p q

/-! ## Identification across types, and propositions -/

theorem MEk_Slogan : MEk.Valid Slogan := cI_Slogan _ _
theorem MEk_Truth : MEk.Valid Truth := cI_Truth MEk_hS
theorem MEk_TopBot : MEk.Valid TopBot := cI_TopBot MEk_hS
theorem MEk_IntT : MEk.Valid IntT := cI_IntT MEk_hS

theorem MEk_TAx : MEk.Valid TAx :=
  (MEk.valid_iff_tr _).mpr <| MEk.tr_TAx.mpr fun _ h => cast ((MEk_eqv_t _ _).mp h).symm
    (fun hall : ∀ q : Prop, q => hall False)

/-! ## Congruence -/

def MEk_h : Fin 3 → Fin 3 := fun v => if v = 0 then 0 else 2

theorem MEk_h0 : MEk_h 0 = 0 := by decide
theorem MEk_h1 : MEk_h 1 = 2 := by decide

theorem MEk_not_h01 : ¬ MEk.eqv .e .e (MEk_h 0) (MEk_h 1) := by
  rw [MEk_h0, MEk_h1]
  rintro ⟨_, e | ⟨_, s⟩⟩
  · exact absurd (eq_of_heq e : (0 : Fin 3) = 2) (by decide)
  · exact absurd (s : (2 : Fin 3) = 0 ∨ (2 : Fin 3) = 1) (show ¬ ((2 : Fin 3) = 0 ∨ (2 : Fin 3) = 1) by decide)

/-- Cong fails: `h ≡ h` and `0 ≡ 1`, but `h 0 = 0` and `h 1 = 2` are not identified. -/
theorem MEk_not_Cong : ¬ MEk.Valid Cong := fun h =>
  MEk_not_h01 (MEk.tr_Cong.mp ((MEk.valid_iff_tr _).mp h) .e .e .e .e MEk_h MEk_h (0 : Fin 3) (1 : Fin 3)
    ⟨⟨rfl, Or.inl HEq.rfl⟩, ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩⟩)

/-- WCong fails, with the same witnesses as Cong. -/
theorem MEk_not_WCong : ¬ MEk.Valid WCong := fun h =>
  MEk_not_h01 (MEk.tr_WCong.mp ((MEk.valid_iff_tr _).mp h) .e .e .e .e MEk_h MEk_h (0 : Fin 3) (1 : Fin 3)
    ⟨⟨rfl, rfl⟩, ⟨⟨rfl, Or.inl HEq.rfl⟩, ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩⟩⟩)

/-- PExt fails: the constant functions `0` and `1` on `e` have identified values, but they are
neither equal nor among `k₁, k₂`. -/
theorem MEk_not_PExt : ¬ MEk.Valid PExt := fun h => by
  have := MEk.tr_PExt.mp ((MEk.valid_iff_tr _).mp h) .e .e .e (fun _ => (0 : Fin 3)) (fun _ => (1 : Fin 3))
    (fun _ => ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩)
  rcases this.2 with h' | ⟨h', _⟩
  · have := congrFun (eq_of_heq h') (0 : Fin 3)
    exact absurd (this : (0 : Fin 3) = 1) (show ¬ (0 : Fin 3) = 1 by decide)
  · rcases (h' : (fun _ => (0 : Fin 3)) = k1 ∨ (fun _ => (0 : Fin 3)) = k2) with e | e
    · exact absurd (congrFun e (2 : Fin 3) : (0 : Fin 3) = k1 2) (show ¬ (0 : Fin 3) = k1 2 by decide)
    · exact absurd (congrFun e (2 : Fin 3) : (0 : Fin 3) = k2 2) (show ¬ (0 : Fin 3) = k2 2 by decide)

/-! ## The Identity Identity and Classicism -/

/-- IdId fails: `0 ≡ 1` is true, but `0` and `1` differ in their properties. -/
theorem MEk_not_IdId : ¬ MEk.Valid IdId := fun h => by
  have := MEk.tr_IdId.mp ((MEk.valid_iff_tr _).mp h) .e (0 : Fin 3) (1 : Fin 3)
  have e := (MEk_eqv_t _ _).mp this
  have h2 : (1 : Fin 3) = 0 := cast e (MEk_eqv_e 0 1 (Or.inr ⟨Or.inl rfl, Or.inr rfl⟩)) (fun z => z = (0 : Fin 3)) rfl
  exact absurd h2 (by decide)

/-- Classicism fails, since it proves IdId. -/
theorem MEk_not_Class : ¬ ∀ χ, ClassSch χ → MEk.Valid χ := fun h =>
  MEk_not_IdId (MEk.soundness MEk_model h (d_IdId_of_Class (S := ClassSch) (fun _ hχ => hχ)))

end MEkP

end PIF
