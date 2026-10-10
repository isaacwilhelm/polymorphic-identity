import PIBF
set_option autoImplicit false

/-!
# Open questions: the profile of `𝔐_hae,κ`

The model `Mhk` of `PIHae.lean`: `E = 1`, a base type `D` of propositions, `≈` identifies types with
the same `≈`-normal form (`D` in codomain position becomes `t`), and items are identified just in case
their roots agree. The haecceity of an item has the root of the item; every other item is its own
root, filed under the normal form of its type.

* PCong fails: a property of the entity, read at `e→t` and at `e→D`, is one item with one root, but
  its values lie at `t` and at `D`, which are never identified.
* PExt fails: the constant function from `e` to the entity, and the constant function from `e` to the
  haecceity of the entity, agree everywhere up to `≡`, but each is its own root, at different types.
* Ext≈ holds: every type has an item that is its own root (for `α→t` and `α→D`, the empty property),
  and roots of an item of `α` have size at most that of `α`, with equality only for own roots. So two
  types that cover each other have the same size, and their own roots are filed under the same normal
  form. Int≈ follows, since `≡_t` is identity.
-/

namespace PIF

section MhkP
attribute [local instance] Classical.propDecidable

/-! ## Roots -/

theorem Mhk_haeRoot_cases {A : Type} (f : A → RK) (G : A → Prop) (own : RK) :
    (∃ x, haeRoot f G own = f x) ∨ haeRoot f G own = own := by
  unfold haeRoot
  split
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr rfl

/-- The root of an item is either the root of an item of a smaller type, or its own root. -/
theorem Mhk_hk_cases (c : CHK) (y : univHK.El c) :
    (∃ (b : CHK) (x : univHK.El b), hk c y = hk b x ∧ csz b < csz c) ∨ hk c y = ownR c y := by
  by_cases ha : HaeTy c
  · obtain ⟨b, c', hce, hc⟩ := hae_shape c ha
    subst hce
    have hlt : csz b < csz (Code.arr b c') :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.succ_le_succ (Nat.le_add_right _ _))
    rcases hc with hct | ⟨w, hcw⟩
    · subst hct
      rcases Mhk_haeRoot_cases (hk b) y (ownR (.arr b .t) y) with ⟨x, hx⟩ | hx
      · exact Or.inl ⟨b, x, hx, hlt⟩
      · exact Or.inr hx
    · subst hcw
      rcases Mhk_haeRoot_cases (hk b) y (ownR (.arr b (.base w)) y) with ⟨x, hx⟩ | hx
      · exact Or.inl ⟨b, x, hx, hlt⟩
      · exact Or.inr hx
  · exact Or.inr (hk_own c ha y)

/-- Every type has an item that is its own root. -/
theorem Mhk_own_ex (c : CHK) : ∃ x : univHK.El c, hk c x = ownR c x := by
  by_cases ha : HaeTy c
  · obtain ⟨b, c', hce, hc⟩ := hae_shape c ha
    subst hce
    have key : ∀ own : RK, haeRoot (hk b) (fun _ => False) own = own := fun own => by
      unfold haeRoot
      split
      · next h =>
        obtain ⟨z, hz⟩ := h
        exact (cast (congrFun hz z).symm rfl : False).elim
      · rfl
    rcases hc with hct | ⟨w, hcw⟩
    · subst hct
      exact ⟨fun _ => False, key (ownR (.arr b .t) (fun _ => False))⟩
    · subst hcw
      exact ⟨fun _ => False, key (ownR (.arr b (.base w)) (fun _ => False))⟩
  · obtain ⟨x⟩ := univHK.El_nonempty c
    exact ⟨x, hk_own c ha x⟩

/-- If every item of `α` has the root of an item of `β`, then `α` is no larger than `β`. -/
theorem Mhk_cover_le (a b : CHK) (h : ∀ x : univHK.El a, ∃ y : univHK.El b, hk a x = hk b y) :
    csz a ≤ csz b := by
  obtain ⟨x0, hx0⟩ := Mhk_own_ex a
  obtain ⟨y, hy⟩ := h x0
  have h1 := hk_le b y
  rw [← hy, hx0] at h1
  have h2 : csz (Tn a) ≤ csz b := h1
  rwa [csz_Tn] at h2

/-! ## Ext≈ and Int≈ hold -/

/-- Types that cover each other have the same normal form. -/
theorem Mhk_ext_core (a b : CHK) (h1 : ∀ x : univHK.El a, ∃ y : univHK.El b, hk a x = hk b y)
    (h2 : ∀ y : univHK.El b, ∃ x : univHK.El a, hk a x = hk b y) : Tn a = Tn b := by
  have hab : csz a = csz b := Nat.le_antisymm (Mhk_cover_le a b h1)
    (Mhk_cover_le b a fun y => (h2 y).elim fun x hx => ⟨x, hx.symm⟩)
  obtain ⟨x0, hx0⟩ := Mhk_own_ex a
  obtain ⟨y, hy⟩ := h1 x0
  rcases Mhk_hk_cases b y with ⟨b', x, hx, hlt⟩ | hown
  · exfalso
    have h3 := hk_le b' x
    rw [← hx, ← hy, hx0] at h3
    have h4 : csz (Tn a) ≤ csz b' := h3
    rw [csz_Tn] at h4
    omega
  · rw [hown, hx0] at hy
    exact congrArg Sigma.fst hy

theorem Mhk_ExtT : Mhk.Valid ExtT :=
  (Mhk.valid_iff_tr _).mpr <| Mhk.tr_ExtT.mpr fun a b ⟨h1, h2⟩ => Mhk_ext_core a b h1 h2

theorem Mhk_IntT : Mhk.Valid IntT :=
  (Mhk.IntT_iff_ExtT fun p q => ⟨hk_inj .t p q, fun h => h ▸ rfl⟩).mpr Mhk_ExtT

/-! ## PCong and PExt fail -/

theorem Mhk_not_PCong : ¬ Mhk.Valid PCong := fun h => by
  have := Mhk.tr_PCong.mp ((Mhk.valid_iff_tr _).mp h) .e .t (.base ()) (fun _ => False) (fun _ => False) ()
    (hk_congr (.arr .e .t) (.arr .e (.base ())) _ _ rfl HEq.rfl)
  have h' : ownR .t False = ownR (.base ()) False :=
    (hk_own .t (fun h => h) False).symm.trans (this.trans (hk_own (.base ()) (fun h => h) False))
  cases congrArg Sigma.fst h'

theorem Mhk_not_PExt : ¬ Mhk.Valid PExt := fun h => by
  have := Mhk.tr_PExt.mp ((Mhk.valid_iff_tr _).mp h) .e .e (.arr .e .t) (fun _ => ())
    (fun _ y => hk .e y = hk .e ()) (fun _ => (hk_hae .e ()).symm)
  have h' : ownR (.arr .e .e) (fun _ => ()) = ownR (.arr .e (.arr .e .t)) (fun _ y => hk .e y = hk .e ()) :=
    (hk_own (.arr .e .e) (fun h => h) _).symm.trans (this.trans (hk_own (.arr .e (.arr .e .t)) (fun h => h) _))
  cases congrArg Sigma.fst h'

end MhkP

end PIF
