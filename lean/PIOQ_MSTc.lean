import PIBF
set_option autoImplicit false

/-!
# `𝔐_STc`: Slogan and Twin without Cantor, in PI⁻

A model of PI⁻ in the standard semantics. `E = 1` and there are no further base types; `≈` is
identity of types. Each item has a *root*, and items are identified just in case they have the same
root:
* the root of the entity is `⊤`, so the entity is identified with `⊤`;
* a proposition is its own root;
* every item of `t→t` has the root `⊥`, so all of them are identified with `⊥` and with each other;
* an item of `α→t`, for `α` other than `e` and `t`, which is the haecceity `λy.(y ≡ x)` of some `x`
  has the root of `x`; any other item of `α→t` is its own root;
* every other item (of `e→t`, and of `α→γ` with `γ` other than `t`) is its own root.

So haecceities of entities and of propositions are not stripped, and all others are.

Twin holds: the entity has `⊤` as a twin; a proposition is `⊤` or `⊥`, with twin the entity or any
item of `t→t`; an item of `t→t` has `⊥` as a twin; every other item has its haecceity as a twin.
Slogan holds, since the only items with root `⊤` are the entity and `⊤`. Cantor fails at `t`: every
property of propositions is identified with `⊥`. So LL≡ fails too: `λp.⊤` and `λp.⊥` are identified,
but differ at `⊤`. Within every other type, distinct items have distinct roots; Ext≈ and Int≈ hold.
-/

namespace PIF

section MSTc
attribute [local instance] Classical.propDecidable

/-- The root of an item. -/
noncomputable def MSTc_root : (c : Code unitUniv.Base) → unitUniv.El c → (Σ c : Code unitUniv.Base, unitUniv.El c)
  | .e, _ => ⟨.t, True⟩
  | .arr a .t, G =>
    if a = .t then ⟨.t, False⟩
    else if a = .e then ⟨.arr a .t, G⟩
    else if h : ∃ x, G = (fun y => MSTc_root a y = MSTc_root a x) then MSTc_root a (Classical.choose h)
    else ⟨.arr a .t, G⟩
  | c, x => ⟨c, x⟩

theorem MSTc_root_arr_t (a : Code unitUniv.Base) (G : unitUniv.El (.arr a .t)) :
    MSTc_root (.arr a .t) G =
      if a = .t then ⟨.t, False⟩
      else if a = .e then ⟨.arr a .t, G⟩
      else if h : ∃ x, G = (fun y => MSTc_root a y = MSTc_root a x) then MSTc_root a (Classical.choose h)
      else ⟨.arr a .t, G⟩ := by
  rw [MSTc_root]

theorem MSTc_root_e (x : unitUniv.El .e) : MSTc_root .e x = ⟨.t, True⟩ := rfl
theorem MSTc_root_t (p : Prop) : MSTc_root .t p = ⟨.t, p⟩ := rfl

theorem MSTc_root_tt (G : unitUniv.El (.arr .t .t)) : MSTc_root (.arr .t .t) G = ⟨.t, False⟩ := by
  rw [MSTc_root_arr_t]
  split
  · rfl
  · next h => exact absurd rfl h

theorem MSTc_root_et (G : unitUniv.El (.arr .e .t)) : MSTc_root (.arr .e .t) G = ⟨.arr .e .t, G⟩ := by
  rw [MSTc_root_arr_t]
  split
  · next h => cases h
  · split
    · rfl
    · next h => exact absurd rfl h

/-- The three ways of finding the root of an item of `α→t`. -/
theorem MSTc_root_cases (a : Code unitUniv.Base) (G : unitUniv.El (.arr a .t)) :
    (a = .t ∧ MSTc_root (.arr a .t) G = ⟨.t, False⟩) ∨
    ((a = .e ∨ ¬ ∃ x, G = (fun y => MSTc_root a y = MSTc_root a x)) ∧ MSTc_root (.arr a .t) G = ⟨.arr a .t, G⟩) ∨
    (a ≠ .t ∧ a ≠ .e ∧ ∃ x, G = (fun y => MSTc_root a y = MSTc_root a x) ∧
      MSTc_root (.arr a .t) G = MSTc_root a x) := by
  have e := MSTc_root_arr_t a G
  split at e
  · next h => exact Or.inl ⟨h, e⟩
  · split at e
    · next h => exact Or.inr (Or.inl ⟨Or.inl h, e⟩)
    · split at e
      · next ht he h => exact Or.inr (Or.inr ⟨ht, he, Classical.choose h, Classical.choose_spec h, e⟩)
      · next h => exact Or.inr (Or.inl ⟨Or.inr h, e⟩)

/-- The haecceity of an item of a type other than `e` and `t` has the root of the item. -/
theorem MSTc_root_hae (a : Code unitUniv.Base) (ht : a ≠ .t) (he : a ≠ .e) (x : unitUniv.El a) :
    MSTc_root (.arr a .t) (fun y => MSTc_root a y = MSTc_root a x) = MSTc_root a x := by
  rcases MSTc_root_cases a (fun y => MSTc_root a y = MSTc_root a x) with ⟨h, _⟩ | ⟨h | h, _⟩ | ⟨_, _, x', hG, e⟩
  · exact absurd h ht
  · exact absurd h he
  · exact absurd ⟨x, rfl⟩ h
  · exact e.trans ((congrFun hG x').mpr rfl)

theorem MSTc_TF : (⟨.t, True⟩ : Σ c : Code unitUniv.Base, unitUniv.El c) ≠ ⟨.t, False⟩ := fun h =>
  cast (eq_of_heq (Sigma.mk.inj h).2) trivial

/-- Only the entity and the propositions can have the root `⊤`. -/
theorem MSTc_root_top : ∀ (c : Code unitUniv.Base) (x : unitUniv.El c),
    MSTc_root c x = ⟨.t, True⟩ → c = .e ∨ c = .t
  | .e, _, _ => Or.inl rfl
  | .t, _, _ => Or.inr rfl
  | .base b, _, _ => Empty.elim b
  | .arr a .t, G, h => by
    rcases MSTc_root_cases a G with ⟨_, e⟩ | ⟨_, e⟩ | ⟨ht, he, x, _, e⟩
    · rw [e] at h
      exact absurd h.symm MSTc_TF
    · rw [e] at h
      cases congrArg Sigma.fst h
    · rw [e] at h
      rcases MSTc_root_top a x h with h1 | h1
      · exact absurd h1 he
      · exact absurd h1 ht
  | .arr _ .e, _, h => by cases congrArg Sigma.fst h
  | .arr _ (.base b), _, _ => Empty.elim b
  | .arr _ (.arr _ _), _, h => by cases congrArg Sigma.fst h

/-- The root of an item is of the item's own type, or of type `t`, or of a smaller type. -/
theorem MSTc_root_size : ∀ (c : Code unitUniv.Base) (x : unitUniv.El c),
    (MSTc_root c x).1 = c ∨ (MSTc_root c x).1 = .t ∨ csz (MSTc_root c x).1 < csz c
  | .e, _ => Or.inr (Or.inl rfl)
  | .t, _ => Or.inl rfl
  | .base b, _ => Empty.elim b
  | .arr a .t, G => by
    have hlt : csz a < csz (Code.arr a .t : Code unitUniv.Base) := by
      show csz a < csz a + csz (Code.t : Code unitUniv.Base) + 1
      omega
    rcases MSTc_root_cases a G with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, _, x, _, e⟩
    · rw [e]
      exact Or.inr (Or.inl rfl)
    · rw [e]
      exact Or.inl rfl
    · rw [e]
      refine Or.inr (Or.inr ?_)
      rcases MSTc_root_size a x with h1 | h1 | h1
      · rw [h1]
        exact hlt
      · rw [h1]
        show 1 < csz a + 1 + 1
        omega
      · omega
  | .arr _ .e, _ => Or.inl rfl
  | .arr _ (.base b), _ => Empty.elim b
  | .arr _ (.arr _ _), _ => Or.inl rfl

/-- Items of `e`, `t` and `t→t` have roots of type `t`. -/
theorem MSTc_small_t (c : Code unitUniv.Base) (hc : c = .e ∨ c = .t ∨ c = .arr .t .t) (x : unitUniv.El c) :
    (MSTc_root c x).1 = .t := by
  rcases hc with rfl | rfl | rfl
  · exact congrArg Sigma.fst (MSTc_root_e x)
  · exact congrArg Sigma.fst (MSTc_root_t x)
  · exact congrArg Sigma.fst (MSTc_root_tt x)

/-- Every type other than `e`, `t` and `t→t` has an item whose root is of that type. -/
theorem MSTc_own : ∀ a : Code unitUniv.Base, ¬ (a = .e ∨ a = .t ∨ a = .arr .t .t) →
    ∃ x : unitUniv.El a, (MSTc_root a x).1 = a
  | .e, h => absurd (Or.inl rfl) h
  | .t, h => absurd (Or.inr (Or.inl rfl)) h
  | .base b, _ => Empty.elim b
  | .arr a .t, h => ⟨fun _ => False, by
      rcases MSTc_root_cases a (fun _ => False) with ⟨ha, _⟩ | ⟨_, e⟩ | ⟨_, _, x, hG, _⟩
      · exact absurd (Or.inr (Or.inr (congrArg (fun c => Code.arr c .t) ha))) h
      · rw [e]
      · exact absurd ((congrFun hG x).mpr rfl) id⟩
  | .arr _ .e, _ => ⟨fun _ => (), rfl⟩
  | .arr _ (.base b), _ => Empty.elim b
  | .arr a (.arr c d), _ => ⟨Classical.choice (Univ.El_nonempty (U := unitUniv) (.arr a (.arr c d))), rfl⟩

noncomputable def MSTc_D : IdentData where
  U := unitUniv
  rel := fun p q => MSTc_root p.1 p.2 = MSTc_root q.1 q.2
  refl := fun _ => rfl
  symm := fun h => h.symm
  trans := fun h1 h2 => h1.trans h2

noncomputable abbrev MSTc_F : Frame := MSTc_D.frame

theorem MSTc_model : MSTc_F.IsModelPIm := MSTc_D.model

theorem MSTc_Inj : MSTc_F.Valid Inj := MSTc_D.Inj_valid

theorem MSTc_Recovery : MSTc_F.Valid Recovery :=
  (MSTc_F.valid_iff_tr _).mpr <| MSTc_F.tr_Recovery.mpr fun _ _ _ _ ⟨h, _⟩ => by
    injection h with _ h2

theorem MSTc_eqv_t (p q : Prop) : MSTc_F.eqv .t .t p q ↔ p = q := by
  constructor
  · intro h
    have h' : MSTc_root .t p = MSTc_root .t q := h
    rw [MSTc_root_t, MSTc_root_t] at h'
    exact eq_of_heq (Sigma.mk.inj h').2
  · intro h
    subst h
    exact MSTc_D.refl _

/-- A proposition is `⊤` or `⊥`, and so is identified with the entity or with the items of `t→t`. -/
theorem MSTc_prop_twin (p : Prop) : ∃ b, b ≠ .t ∧ ∃ y : unitUniv.El b, MSTc_root .t p = MSTc_root b y := by
  by_cases hp : p
  · refine ⟨.e, (fun h => by cases h), (), ?_⟩
    exact (MSTc_root_t p).trans ((congrArg (fun q : Prop => (⟨.t, q⟩ : Σ c : Code unitUniv.Base, unitUniv.El c))
      (eq_true hp)).trans (MSTc_root_e ()).symm)
  · refine ⟨.arr .t .t, (fun h => by cases h), fun _ => False, ?_⟩
    exact (MSTc_root_t p).trans ((congrArg (fun q : Prop => (⟨.t, q⟩ : Σ c : Code unitUniv.Base, unitUniv.El c))
      (eq_false hp)).trans (MSTc_root_tt _).symm)

/-- Twin: the entity has `⊤` as a twin; a proposition is `⊤` or `⊥`, with twin the entity or an
item of `t→t`; an item of `t→t` has `⊥` as a twin; every other item has its haecceity as a twin. -/
theorem MSTc_Twin : MSTc_F.Valid Twin :=
  (MSTc_F.valid_iff_tr _).mpr <| MSTc_F.tr_Twin.mpr fun a x => by
    by_cases he : a = .e
    · subst he
      exact ⟨.t, (fun h => by cases h), True, (MSTc_root_e x).trans (MSTc_root_t True).symm⟩
    · by_cases ht : a = .t
      · subst ht
        obtain ⟨b, hb, y, hy⟩ := MSTc_prop_twin x
        exact ⟨b, (fun h => hb h.symm), y, hy⟩
      · by_cases htt : a = .arr .t .t
        · subst htt
          exact ⟨.t, (fun h => by cases h), False, (MSTc_root_tt x).trans (MSTc_root_t False).symm⟩
        · exact ⟨.arr a .t, (fun h => Code.arr_ne_left a .t h.symm), fun y => MSTc_root a y = MSTc_root a x,
            (MSTc_root_hae a ht he x).symm⟩

/-- No entity is identified with a property: only the entity and `⊤` have the root `⊤`. -/
theorem MSTc_Slogan : MSTc_F.Valid Slogan :=
  (MSTc_F.valid_iff_tr _).mpr <| MSTc_F.tr_Slogan.mpr fun x b y h => by
    have h0 : MSTc_root .e x = MSTc_root (.arr b .t) y := h
    have h' : MSTc_root (.arr b .t) y = ⟨.t, True⟩ := h0.symm.trans (MSTc_root_e x)
    rcases MSTc_root_top (.arr b .t) y h' with h1 | h1 <;> cases h1

/-- Cantor fails at `t`: every property of propositions is identified with `⊥`. -/
theorem MSTc_not_Cantor : ¬ MSTc_F.Valid Cantor := fun h => by
  obtain ⟨G, hG⟩ := MSTc_F.tr_Cantor.mp ((MSTc_F.valid_iff_tr _).mp h) .t
  exact hG False ((MSTc_root_tt G).trans (MSTc_root_t False).symm)

/-- LL≡ fails: `λp.⊤` and `λp.⊥` are identified, but only the first is true of `⊤`. -/
theorem MSTc_not_LLEqv : ¬ MSTc_F.Valid LLEqv := fun h =>
  MSTc_F.tr_LLEqv.mp ((MSTc_F.valid_iff_tr _).mp h) (.arr .t .t) (fun _ => True) (fun _ => False)
    ((MSTc_root_tt _).trans (MSTc_root_tt _).symm) (fun G => G True) trivial

/-- The haecceity of the entity is its own root, of type `e→t`, while the entity's root is `⊤`. -/
theorem MSTc_not_Hae : ¬ MSTc_F.Valid Hae := fun h => by
  have h1 : MSTc_root .e () = MSTc_root (.arr .e .t) (fun y => MSTc_F.eqv .e .e y ()) :=
    MSTc_F.tr_Hae.mp ((MSTc_F.valid_iff_tr _).mp h) .e ()
  have h2 := (MSTc_root_e ()).symm.trans (h1.trans (MSTc_root_et _))
  cases congrArg Sigma.fst h2

/-- The entity is identified with `⊤`. -/
theorem MSTc_not_Disjoint : ¬ MSTc_F.Valid Disjoint := fun h =>
  MSTc_F.tr_Disjoint.mp ((MSTc_F.valid_iff_tr _).mp h) .e .t (fun e => by cases e) () True
    ((MSTc_root_e ()).trans (MSTc_root_t True).symm)

/-- LL≡-Poly fails, for `λγ.λz.(γ ≈ e)`: the entity is identified with `⊤`. -/
theorem MSTc_not_LLPoly : ¬ MSTc_F.Valid (LLPoly PredE) := fun h => by
  have := MSTc_F.tr_LLPolyE.mp ((MSTc_F.valid_iff_tr _).mp h) .e .t () True
    ((MSTc_root_e ()).trans (MSTc_root_t True).symm) rfl
  cases this

theorem MSTc_Truth : MSTc_F.Valid Truth :=
  (MSTc_F.valid_iff_tr _).mpr <| MSTc_F.tr_Truth.mpr fun p q h hp => (MSTc_eqv_t p q).mp h ▸ hp

theorem MSTc_TopBot : MSTc_F.Valid TopBot :=
  (MSTc_F.valid_iff_tr _).mpr <| MSTc_F.tr_TopBot.mpr fun h => by
    have e := (MSTc_eqv_t _ _).mp h
    exact (cast e (fun hall : ∀ p : Prop, p => hall False)) False

/-- WCong fails: `λp.⊥` and `λp.⊤` are identified, but their values at `⊤` are not. -/
theorem MSTc_not_WCong : ¬ MSTc_F.Valid WCong := fun h => by
  have := MSTc_F.tr_WCong.mp ((MSTc_F.valid_iff_tr _).mp h) .t .t .t .t (fun _ => False) (fun _ => True)
    True True ⟨⟨rfl, rfl⟩, ⟨(MSTc_root_tt _).trans (MSTc_root_tt _).symm, MSTc_D.refl _⟩⟩
  exact cast ((MSTc_eqv_t _ _).mp this).symm trivial

theorem MSTc_not_Cong : ¬ MSTc_F.Valid Cong := fun h => by
  have := MSTc_F.tr_Cong.mp ((MSTc_F.valid_iff_tr _).mp h) .t .t .t .t (fun _ => False) (fun _ => True)
    True True ⟨(MSTc_root_tt _).trans (MSTc_root_tt _).symm, MSTc_D.refl _⟩
  exact cast ((MSTc_eqv_t _ _).mp this).symm trivial

theorem MSTc_not_PCong : ¬ MSTc_F.Valid PCong := fun h => by
  have := MSTc_F.tr_PCong.mp ((MSTc_F.valid_iff_tr _).mp h) .t .t .t (fun _ => False) (fun _ => True)
    True ((MSTc_root_tt _).trans (MSTc_root_tt _).symm)
  exact cast ((MSTc_eqv_t _ _).mp this).symm trivial

theorem MSTc_root_ee (f : unitUniv.El (.arr .e .e)) : MSTc_root (.arr .e .e) f = ⟨.arr .e .e, f⟩ := rfl

/-- PExt fails: `λx.x` of `e→e` and `λx.⊤` of `e→t` take identified values, but are their own roots,
of different types. -/
theorem MSTc_not_PExt : ¬ MSTc_F.Valid PExt := fun h => by
  have h1 : MSTc_root (.arr .e .e) (fun _ => ()) = MSTc_root (.arr .e .t) (fun _ => True) :=
    MSTc_F.tr_PExt.mp ((MSTc_F.valid_iff_tr _).mp h) .e .e .t (fun _ => ()) (fun _ => True)
      (fun _ => (MSTc_root_e _).trans (MSTc_root_t True).symm)
  have h2 := (MSTc_root_ee _).symm.trans (h1.trans (MSTc_root_et _))
  cases congrArg Sigma.fst h2

/-! ### Ext≈ and Int≈ -/

theorem MSTc_ext (a b : Code unitUniv.Base)
    (h1 : ∀ x : unitUniv.El a, ∃ y : unitUniv.El b, MSTc_root a x = MSTc_root b y)
    (h2 : ∀ y : unitUniv.El b, ∃ x : unitUniv.El a, MSTc_root a x = MSTc_root b y) : a = b := by
  by_cases ha : a = .e ∨ a = .t ∨ a = .arr .t .t
  · by_cases hb : b = .e ∨ b = .t ∨ b = .arr .t .t
    · rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · rfl
      · obtain ⟨x, hx⟩ := h2 False
        exact (MSTc_TF ((MSTc_root_e x).symm.trans (hx.trans (MSTc_root_t False)))).elim
      · obtain ⟨y, hy⟩ := h1 ()
        exact (MSTc_TF ((MSTc_root_e ()).symm.trans (hy.trans (MSTc_root_tt y)))).elim
      · obtain ⟨y, hy⟩ := h1 False
        exact (MSTc_TF ((MSTc_root_e y).symm.trans (hy.symm.trans (MSTc_root_t False)))).elim
      · rfl
      · obtain ⟨y, hy⟩ := h1 True
        exact (MSTc_TF ((MSTc_root_t True).symm.trans (hy.trans (MSTc_root_tt y)))).elim
      · obtain ⟨y, hy⟩ := h1 (fun _ => False)
        exact (MSTc_TF ((MSTc_root_e y).symm.trans (hy.symm.trans (MSTc_root_tt _)))).elim
      · obtain ⟨x, hx⟩ := h2 True
        exact (MSTc_TF ((MSTc_root_t True).symm.trans (hx.symm.trans (MSTc_root_tt x)))).elim
      · rfl
    · obtain ⟨y0, hy0⟩ := MSTc_own b hb
      obtain ⟨x, hx⟩ := h2 y0
      have e := MSTc_small_t a ha x
      rw [hx, hy0] at e
      exact absurd (Or.inr (Or.inl e)) hb
  · obtain ⟨x0, hx0⟩ := MSTc_own a ha
    obtain ⟨y, hy⟩ := h1 x0
    have e1 : (MSTc_root b y).1 = a := (congrArg Sigma.fst hy).symm.trans hx0
    rcases MSTc_root_size b y with s | s | s
    · exact e1.symm.trans s
    · exact absurd (Or.inr (Or.inl (e1.symm.trans s))) ha
    · by_cases hb : b = .e ∨ b = .t ∨ b = .arr .t .t
      · exact absurd (Or.inr (Or.inl (e1.symm.trans (MSTc_small_t b hb y)))) ha
      · obtain ⟨y0, hy0⟩ := MSTc_own b hb
        obtain ⟨x, hx⟩ := h2 y0
        have e2 : (MSTc_root a x).1 = b := (congrArg Sigma.fst hx).trans hy0
        rcases MSTc_root_size a x with r | r | r
        · exact r.symm.trans e2
        · exact absurd (Or.inr (Or.inl (e2.symm.trans r))) hb
        · rw [e1] at s
          rw [e2] at r
          omega

theorem MSTc_ExtT : MSTc_F.Valid ExtT :=
  (MSTc_F.valid_iff_tr _).mpr <| MSTc_F.tr_ExtT.mpr fun a b ⟨h1, h2⟩ => MSTc_ext a b h1 h2

theorem MSTc_IntT : MSTc_F.Valid IntT := (MSTc_F.IntT_iff_ExtT MSTc_eqv_t).mpr MSTc_ExtT

/-! ### LL≡/≈ fails

The polymorphic predicate `λγ.λz. ∃_{γ→t} F (F ≡ ev ∧ F z)`, with `ev = λG:t→t. G ⊤`, is true of
`λp.⊤` but not of `λp.⊥` at `t→t`: identity at `(t→t)→t` is sameness, so `F` must be `ev`. -/

/-- The polymorphic predicate `λγ.λz. ∃_{γ→t} F (F ≡ λG:t→t. G ⊤ ∧ F z)`. -/
def MSTc_PredEv : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (Tm.ex tv0.pred (Tm.conj
    (Tm.eqv tv0.pred (Ty.arrow tyT tyT).pred (.var .here) (.lam (Ty.arrow tyT tyT) (.app (.var .here) topF)))
    (.app (.var .here) (.var (.there .here))))))

/-- What `MSTc_PredEv` says of an item. -/
def MSTc_Evf (F : Frame) (a : Code F.U.Base) (z : F.U.El a) : Prop :=
  ∃ G : F.U.El a → Prop, F.eqv (.arr a .t) (.arr (.arr .t .t) .t) G (fun H : Prop → Prop => H (¬ ∀ p : Prop, p)) ∧ G z

theorem MSTc_tr_BridgeEv (F : Frame) : F.Tr (Bridge MSTc_PredEv) ↔
    ∀ a b (x : F.U.El a) (y : F.U.El b), F.eqv a b x y ∧ F.teq a b → MSTc_Evf F a x → MSTc_Evf F b y := Iff.rfl

/-- `λG. G ⊤` is not a haecceity, and so is its own root. -/
theorem MSTc_ev_root : MSTc_root (.arr (.arr .t .t) .t) (fun H : Prop → Prop => H (¬ ∀ p : Prop, p)) =
    ⟨.arr (.arr .t .t) .t, fun H : Prop → Prop => H (¬ ∀ p : Prop, p)⟩ := by
  rcases MSTc_root_cases (.arr .t .t) (fun H : Prop → Prop => H (¬ ∀ p : Prop, p)) with ⟨ha, _⟩ | ⟨_, e⟩ | ⟨_, _, x, hG, _⟩
  · cases ha
  · exact e
  · exact absurd ((congrFun hG (fun _ => False)).mpr ((MSTc_root_tt _).trans (MSTc_root_tt x).symm)) id

theorem MSTc_Ev_tt (z : unitUniv.El (.arr .t .t)) : MSTc_Evf MSTc_F (.arr .t .t) z ↔ z (¬ ∀ p : Prop, p) := by
  constructor
  · rintro ⟨G, hG, hz⟩
    have h1 : MSTc_root (.arr (.arr .t .t) .t) G =
        ⟨.arr (.arr .t .t) .t, fun H : Prop → Prop => H (¬ ∀ p : Prop, p)⟩ :=
      (hG : MSTc_root (.arr (.arr .t .t) .t) G =
        MSTc_root (.arr (.arr .t .t) .t) (fun H : Prop → Prop => H (¬ ∀ p : Prop, p))).trans MSTc_ev_root
    rcases MSTc_root_cases (.arr .t .t) G with ⟨ha, _⟩ | ⟨_, e⟩ | ⟨_, _, x, _, e⟩
    · cases ha
    · have e2 : G = fun H : Prop → Prop => H (¬ ∀ p : Prop, p) := eq_of_heq (Sigma.mk.inj (e.symm.trans h1)).2
      subst e2
      exact hz
    · have h2 := (MSTc_root_tt x).symm.trans (e.symm.trans h1)
      cases congrArg Sigma.fst h2
  · intro hz
    exact ⟨fun H : Prop → Prop => H (¬ ∀ p : Prop, p), MSTc_D.refl _, hz⟩

theorem MSTc_not_Bridge : ¬ MSTc_F.Valid (Bridge MSTc_PredEv) := fun h => by
  have := (MSTc_tr_BridgeEv MSTc_F).mp ((MSTc_F.valid_iff_tr _).mp h) (.arr .t .t) (.arr .t .t)
    (fun _ => True) (fun _ => False) ⟨(MSTc_root_tt _).trans (MSTc_root_tt _).symm, rfl⟩
    ((MSTc_Ev_tt _).mpr trivial)
  exact (MSTc_Ev_tt _).mp this

/-! ### Principles true in every standard model -/

theorem MSTc_PropExt : MSTc_F.Valid PropExt := MSTc_F.PropExt_valid MSTc_model
theorem MSTc_Collapse : MSTc_F.Valid Collapse := MSTc_F.Collapse_valid MSTc_model
theorem MSTc_Choice : MSTc_F.Valid Choice := MSTc_F.Choice_valid

/-! ### Modal principles, by soundness -/

theorem MSTc_of_prov {S : Fm Ctx.nil → Prop} (hS : ∀ ψ, S ψ → MSTc_F.Valid ψ) {φ : Fm Ctx.nil}
    (h : Prov S Ctx.nil φ) : MSTc_F.Valid φ :=
  MSTc_F.soundness MSTc_model hS h

theorem MSTc_TAx : MSTc_F.Valid TAx :=
  MSTc_of_prov (S := (· = Truth)) (fun _ h => h ▸ MSTc_Truth) (d_TAx_of_Truth rfl)

theorem MSTc_NIEqv : MSTc_F.Valid NIEqv :=
  MSTc_of_prov (S := (· = Collapse)) (fun _ h => h ▸ MSTc_Collapse) (d_NIEqv_of_Collapse rfl)

theorem MSTc_NITeq : MSTc_F.Valid NITeq :=
  MSTc_of_prov (S := (· = Collapse)) (fun _ h => h ▸ MSTc_Collapse) (d_NITeq_of_Collapse rfl)

theorem MSTc_NDTeq : MSTc_F.Valid NDTeq :=
  MSTc_of_prov (S := (· = Collapse)) (fun _ h => h ▸ MSTc_Collapse) (d_NDTeq_of_Collapse rfl)

theorem MSTc_NIX : MSTc_F.Valid NIX :=
  MSTc_of_prov (S := (· = Collapse)) (fun _ h => h ▸ MSTc_Collapse) (d_NIX_of_Collapse rfl)

theorem MSTc_NDX : MSTc_F.Valid NDX :=
  MSTc_of_prov (S := (· = Collapse)) (fun _ h => h ▸ MSTc_Collapse) (d_NDX_of_Collapse rfl)

theorem MSTc_TNec : MSTc_F.Valid TNec :=
  MSTc_of_prov (S := (· = Collapse)) (fun _ h => h ▸ MSTc_Collapse) (d_TNec rfl)

theorem MSTc_Nec : MSTc_F.Valid Nec :=
  MSTc_of_prov (S := (· = Collapse)) (fun _ h => h ▸ MSTc_Collapse) (d_Nec_of_Collapse rfl)

theorem MSTc_Bool : ∀ φ, BoolSch φ → MSTc_F.Valid φ := fun φ hφ =>
  MSTc_of_prov (S := (· = PropExt)) (fun _ h => h ▸ MSTc_PropExt) (d_Bool_of_PropExt (S := (· = PropExt)) rfl φ hφ)

theorem MSTc_TBF : ∀ χ, TBFSch χ → MSTc_F.Valid χ := fun χ hχ =>
  MSTc_of_prov (S := (· = PropExt)) (fun _ h => h ▸ MSTc_PropExt) (d_TBF_of_PropExt (S := (· = PropExt)) rfl χ hχ)

theorem MSTc_TCBF : ∀ χ, TCBFSch χ → MSTc_F.Valid χ := fun χ hχ =>
  MSTc_of_prov (S := (· = PropExt)) (fun _ h => h ▸ MSTc_PropExt) (d_TCBF_of_PropExt (S := (· = PropExt)) rfl χ hχ)

theorem MSTc_BF : MSTc_F.Valid BF :=
  MSTc_of_prov (S := fun ψ => ψ = Collapse ∨ ψ = TAx)
    (fun _ h => h.elim (fun e => e ▸ MSTc_Collapse) (fun e => e ▸ MSTc_TAx))
    (d_BF_of_Collapse (Or.inl rfl) (Or.inr rfl))

theorem MSTc_CBF : MSTc_F.Valid CBF :=
  MSTc_of_prov (S := fun ψ => ψ = Collapse ∨ ψ = TAx)
    (fun _ h => h.elim (fun e => e ▸ MSTc_Collapse) (fun e => e ▸ MSTc_TAx))
    (d_CBF_of_Collapse (Or.inl rfl) (Or.inr rfl))

/-- IdId fails: with Truth it would give LL≡. -/
theorem MSTc_not_IdId : ¬ MSTc_F.Valid IdId := fun h =>
  MSTc_not_LLEqv (MSTc_of_prov (S := fun ψ => ψ = IdId ∨ ψ = Truth)
    (fun _ hψ => hψ.elim (fun e => e ▸ h) (fun e => e ▸ MSTc_Truth)) (d_LLEqv_of_IdId (Or.inl rfl) (Or.inr rfl)))

theorem MSTc_not_Class : ¬ ∀ χ, ClassSch χ → MSTc_F.Valid χ := fun h =>
  MSTc_not_IdId (MSTc_F.soundness MSTc_model h (d_IdId_of_Class (S := ClassSch) (fun _ hc => hc)))

end MSTc

end PIF
