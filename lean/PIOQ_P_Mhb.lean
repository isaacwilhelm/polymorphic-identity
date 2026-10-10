import PIBF
set_option autoImplicit false

/-!
# Open questions: the profile of `𝔐_hae,R`

The haecceity tower `Mhb` of `PIBridge.lean`, over `E = {0,1,2}`: `1` has the root of `0`, and so does
the property `ind1 = λy.(y = 1)`, which is not a haecceity. Items are identified just in case their
roots agree, and `≈` is identity of types.

At `t` every proposition is its own root, so `≡_t` is identity: Truth, ⊤≢⊥ and T hold. The haecceity of
`0` (the property of being `0` or `1`) is identified with `ind1`, while their values at `0` differ: so
PCong, WCong and Cong fail. The constant functions `0` and `1` on entities agree up to `≡` at every
argument, but are their own roots: so PExt fails. IdId fails at `0 ≡ 1`, and with it Classicism.

Each root is either of the item's own type or of a smaller type, and every type has an item whose root
is of that very type (for `α→t`, the empty property). So no property of `α` is identified with an item of
`α` (Cantor), and types whose items are identified with each other's are the same (Ext≈, and so Int≈).
-/

namespace PIF

section MhbP

/-! ## Roots -/

/-- The root `ovB` assigns is of the item's own type, or of a smaller one. -/
theorem Mhb_ov_cases : ∀ (c : Code univ3.Base) (x : univ3.El c),
    (ovB c x).1 = c ∨ csz (ovB c x).1 < csz c
  | .e, x => by
    show (@ite R3 (x = (1 : Fin 3)) (Classical.propDecidable _) ⟨.e, (0 : Fin 3)⟩ ⟨.e, x⟩).1 = .e ∨ _
    split
    · exact Or.inl rfl
    · exact Or.inl rfl
  | .t, _ => Or.inl rfl
  | .base b, _ => b.elim
  | .arr .e .t, G => by
    rw [ovB_et]
    split
    · exact Or.inr (show 1 < 1 + 1 + 1 by omega)
    · exact Or.inl rfl
  | .arr .e .e, _ => Or.inl rfl
  | .arr .e (.base b), _ => b.elim
  | .arr .e (.arr _ _), _ => Or.inl rfl
  | .arr .t _, _ => Or.inl rfl
  | .arr (.base b) _, _ => b.elim
  | .arr (.arr _ _) _, _ => Or.inl rfl

theorem Mhb_ov_le (c : Code univ3.Base) (x : univ3.El c) : csz (ovB c x).1 ≤ csz c :=
  (Mhb_ov_cases c x).elim (fun h => Nat.le_of_eq (congrArg csz h)) Nat.le_of_lt

/-- A property true of nothing is not identified with anything of a smaller type by `ovB`. -/
theorem Mhb_ov_empty : ∀ (a : Code univ3.Base) (G : univ3.El (.arr a .t)), (∀ z, ¬ G z) →
    (ovB (.arr a .t) G).1 = .arr a .t
  | .e, G, hG => by
    rw [ovB_et]
    split
    · next h => exact absurd ((congrFun h (1 : Fin 3)).mpr rfl) (hG (1 : Fin 3))
    · rfl
  | .t, _, _ => rfl
  | .base b, _, _ => b.elim
  | .arr _ _, _, _ => rfl

/-- The root of an item is of the item's own type, or of a smaller one. -/
theorem Mhb_hr_cases (c : Code univ3.Base) (x : univ3.El c) :
    (hr ovB c x).1 = c ∨ csz (hr ovB c x).1 < csz c := by
  by_cases hc : ∃ a, c = .arr a .t
  · obtain ⟨a, rfl⟩ := hc
    rw [hr_arr_t]
    split
    · next h =>
      have := hr_le Mhb_ov_le a (Classical.choose h)
      exact Or.inr (show csz (hr ovB a (Classical.choose h)).1 < csz a + 1 + 1 by omega)
    · exact Mhb_ov_cases _ _
  · have e : hr ovB c x = ovB c x := by
      cases c with
      | e => rfl
      | t => rfl
      | base b => exact b.elim
      | arr a d =>
        cases d with
        | e => rfl
        | t => exact absurd ⟨a, rfl⟩ hc
        | base b => exact b.elim
        | arr _ _ => rfl
    rw [e]
    exact Mhb_ov_cases c x

/-- The empty property is its own root. -/
theorem Mhb_hr_empty (a : Code univ3.Base) :
    (hr ovB (.arr a .t) (fun _ => False : univ3.El (.arr a .t))).1 = .arr a .t := by
  refine (congrArg Sigma.fst (hr_arr_t ovB a _)).trans ?_
  split
  · next h =>
    have hc := congrFun (Classical.choose_spec h) (Classical.choose h)
    exact absurd (hc.mpr rfl) id
  · exact Mhb_ov_empty a _ (fun _ h => h)

/-- An item of a type `α→β`, with `β` other than `t`, is its own root under `ovB`. -/
theorem Mhb_ov_nt : ∀ (a d : Code univ3.Base), d ≠ .t → ∀ x : univ3.El (.arr a d), (ovB (.arr a d) x).1 = .arr a d
  | .e, .e, _, _ => rfl
  | .e, .t, hd, _ => absurd rfl hd
  | .e, .base b, _, _ => b.elim
  | .e, .arr _ _, _, _ => rfl
  | .t, _, _, _ => rfl
  | .base b, _, _, _ => b.elim
  | .arr _ _, _, _, _ => rfl

/-- Every type has an item whose root is of that type. -/
theorem Mhb_own : ∀ c : Code univ3.Base, ∃ x : univ3.El c, (hr ovB c x).1 = c
  | .e => ⟨(0 : Fin 3), congrArg Sigma.fst hrB_e0⟩
  | .t => ⟨True, rfl⟩
  | .base b => b.elim
  | .arr a .t => ⟨fun _ => False, Mhb_hr_empty a⟩
  | .arr a .e => ⟨fun _ => (0 : Fin 3), Mhb_ov_nt a .e (fun h => nomatch h) _⟩
  | .arr _ (.base b) => b.elim
  | .arr a (.arr c d) => by
    obtain ⟨x0⟩ := Univ.El_nonempty (U := univ3) (.arr a (.arr c d))
    exact ⟨x0, Mhb_ov_nt a (.arr c d) (fun h => nomatch h) x0⟩

theorem Mhb_eqv_t (p q : Prop) : Mhb.eqv .t .t p q ↔ p = q :=
  ⟨fun h => eq_of_heq (Sigma.mk.inj (h : hr ovB .t p = hr ovB .t q)).2,
   fun h => h ▸ MhbD.refl _⟩

/-! ## Identification across types -/

theorem Mhb_Cantor : Mhb.Valid Cantor :=
  (Mhb.valid_iff_tr _).mpr <| Mhb.tr_Cantor.mpr fun (a : Code univ3.Base) => ⟨fun _ => False, fun y h => by
    have h' : hr ovB (.arr a .t) (fun _ => False : univ3.El (.arr a .t)) = hr ovB a y := h
    have h1 : (hr ovB a y).1 = .arr a .t := (congrArg Sigma.fst h').symm.trans (Mhb_hr_empty a)
    rcases Mhb_hr_cases a y with h2 | h2
    · exact Code.arr_ne_left a .t (h1.symm.trans h2)
    · rw [h1] at h2
      exact absurd h2 (show ¬ csz a + csz (Code.t : Code univ3.Base) + 1 < csz a by omega)⟩

theorem Mhb_ExtT : Mhb.Valid ExtT :=
  (Mhb.valid_iff_tr _).mpr <| Mhb.tr_ExtT.mpr fun a b ⟨h1, h2⟩ => by
    show a = b
    refine Classical.byContradiction fun hab => ?_
    obtain ⟨x, hx⟩ := Mhb_own a
    obtain ⟨y, hy⟩ := h1 x
    have hy' : (hr ovB b y).1 = a := (congrArg Sigma.fst (hy : hr ovB a x = hr ovB b y)).symm.trans hx
    obtain ⟨y', hy2⟩ := Mhb_own b
    obtain ⟨x', hx'⟩ := h2 y'
    have hx2 : (hr ovB a x').1 = b := (congrArg Sigma.fst (hx' : hr ovB a x' = hr ovB b y')).trans hy2
    rcases Mhb_hr_cases b y with h3 | h3
    · exact hab (hy'.symm.trans h3)
    · rcases Mhb_hr_cases a x' with h4 | h4
      · exact hab (h4.symm.trans hx2)
      · rw [hy'] at h3
        rw [hx2] at h4
        omega

theorem Mhb_IntT : Mhb.Valid IntT := (Mhb.IntT_iff_ExtT Mhb_eqv_t).mpr Mhb_ExtT

/-! ## Congruence -/

/-- The haecceity of `0` is identified with `ind1`. -/
theorem Mhb_hae_ind1 : Mhb.eqv (.arr .e .t) (.arr .e .t) (haeF ovB .e (0 : Fin 3)) ind1 :=
  (hr_hae ovB .e (0 : Fin 3)).trans (hrB_e0.trans hrB_ind1.symm)

/-- Their values at `0` are not identified: one is true and the other false. -/
theorem Mhb_not_app0 : ¬ Mhb.eqv .t .t (haeF ovB .e (0 : Fin 3) (0 : Fin 3)) (ind1 (0 : Fin 3)) := fun h =>
  f01 (cast ((Mhb_eqv_t _ _).mp h) (rfl : hr ovB .e (0 : Fin 3) = hr ovB .e (0 : Fin 3)))

theorem Mhb_not_PCong : ¬ Mhb.Valid PCong := fun h =>
  Mhb_not_app0 (Mhb.tr_PCong.mp ((Mhb.valid_iff_tr _).mp h) .e .t .t (haeF ovB .e (0 : Fin 3)) ind1
    (0 : Fin 3) Mhb_hae_ind1)

theorem Mhb_not_WCong : ¬ Mhb.Valid WCong := fun h =>
  Mhb_not_app0 (Mhb.tr_WCong.mp ((Mhb.valid_iff_tr _).mp h) .e .e .t .t (haeF ovB .e (0 : Fin 3)) ind1
    (0 : Fin 3) (0 : Fin 3) ⟨⟨rfl, rfl⟩, ⟨Mhb_hae_ind1, rfl⟩⟩)

theorem Mhb_not_Cong : ¬ Mhb.Valid Cong := fun h =>
  Mhb_not_app0 (Mhb.tr_Cong.mp ((Mhb.valid_iff_tr _).mp h) .e .e .t .t (haeF ovB .e (0 : Fin 3)) ind1
    (0 : Fin 3) (0 : Fin 3) ⟨Mhb_hae_ind1, rfl⟩)

/-- PExt fails: the constant functions `0` and `1` on entities have identified values everywhere,
but each is its own root. -/
theorem Mhb_not_PExt : ¬ Mhb.Valid PExt := fun h => by
  have h01 : Mhb.eqv .e .e (0 : Fin 3) (1 : Fin 3) := hrB_e0.trans hrB_e1.symm
  have := Mhb.tr_PExt.mp ((Mhb.valid_iff_tr _).mp h) .e .e .e
    (fun _ => (0 : Fin 3)) (fun _ => (1 : Fin 3)) (fun _ => h01)
  have e : (⟨.arr .e .e, (fun _ => (0 : Fin 3) : univ3.El (.arr .e .e))⟩ : R3) =
      ⟨.arr .e .e, (fun _ => (1 : Fin 3) : univ3.El (.arr .e .e))⟩ := this
  exact f01 (congrFun (eq_of_heq (Sigma.mk.inj e).2) (0 : Fin 3))

/-! ## Propositions -/

theorem Mhb_Truth : Mhb.Valid Truth :=
  (Mhb.valid_iff_tr _).mpr <| Mhb.tr_Truth.mpr fun _ _ h hp => cast ((Mhb_eqv_t _ _).mp h) hp

theorem Mhb_TopBot : Mhb.Valid TopBot :=
  (Mhb.valid_iff_tr _).mpr <| Mhb.tr_TopBot.mpr fun h => by
    have e : (¬ ∀ p : Prop, p) = (∀ p : Prop, p) := (Mhb_eqv_t _ _).mp h
    exact (cast e (fun hall => hall False)) False

/-- IdId fails: `0 ≡ 1` is true, but `0` and `1` differ in their properties. -/
theorem Mhb_not_IdId : ¬ Mhb.Valid IdId := fun h => by
  have := Mhb.tr_IdId.mp ((Mhb.valid_iff_tr _).mp h) .e (0 : Fin 3) (1 : Fin 3)
  have e := (Mhb_eqv_t _ _).mp this
  have h01 : Mhb.eqv .e .e (0 : Fin 3) (1 : Fin 3) := hrB_e0.trans hrB_e1.symm
  have h2 : (1 : Fin 3) = 0 := cast e h01 (fun z => z = (0 : Fin 3)) rfl
  exact f01 h2.symm

/-! ### By soundness -/

theorem Mhb_of_prov {S : Fm Ctx.nil → Prop} (hS : ∀ ψ, S ψ → Mhb.Valid ψ) {φ : Fm Ctx.nil}
    (h : Prov S Ctx.nil φ) : Mhb.Valid φ :=
  Mhb.soundness Mhb_model hS h

/-- Classicism fails, since it proves IdId (in PI⁻). -/
theorem Mhb_not_Class : ¬ ∀ χ, ClassSch χ → Mhb.Valid χ := fun h =>
  Mhb_not_IdId (Mhb_of_prov h (d_IdId_of_Class (S := ClassSch) (fun _ hc => hc)))

theorem Mhb_TAx : Mhb.Valid TAx :=
  Mhb_of_prov (S := (· = Truth)) (fun _ h => h ▸ Mhb_Truth) (d_TAx_of_Truth rfl)

end MhbP

end PIF
