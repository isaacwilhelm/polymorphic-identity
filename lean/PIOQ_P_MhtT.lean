import PIBF

/-!
# The profile of `𝔐_hae,int,1`

The model `MhtTF` of `PIBF.lean`: tagged propositions (`PITagged.lean`), haecceity towers `hrT`
(`PINew.lean`), with first-order quantified propositions carrying the tag `true` (type-quantified
propositions carry the tag `false`). So `□φ` (that is, `φ ≡_t ⊤`) is true just when `φ` is true and
has the tag `true`: every sentence built without type quantifiers or free propositional variables has
the tag `true`, so for such sentences `□φ` is equivalent to `φ`.

Each item's root (`hrT`) is either the item itself, or (for a haecceity) the root of an item of a
smaller type. Every type has an item that is its own root. So types with the same roots are identical,
and Ext≈ and Int≈ hold.
-/
set_option autoImplicit false

namespace PIF
namespace Tg
open Tm

/-! ## Roots -/

/-- An item is its own root, or its root lies at a smaller type. -/
theorem MhtT_hrT_cases (c : Code univU.Base) (x : univU.El c) :
    hrT c x = ⟨c, x⟩ ∨ csz (hrT c x).1 < csz c := by
  by_cases hc : ∃ a, c = .arr a .t
  · obtain ⟨a, rfl⟩ := hc
    have hle : ∀ z, csz (hrT a z).1 < csz (Code.arr a .t) := fun z => by
      have := hrT_le a z
      show csz (hrT a z).1 < csz a + 1 + 1
      omega
    rw [hrT_arr_t]
    split
    · next h => exact Or.inr (hle (Classical.choose h))
    · exact Or.inl rfl
  · exact Or.inl (hrT_own c (fun a h => hc ⟨a, h⟩) x)

/-- Every type has an item that is its own root. -/
theorem MhtT_own (c : Code univU.Base) : ∃ x : univU.El c, hrT c x = ⟨c, x⟩ := by
  by_cases hc : ∃ a, c = .arr a .t
  · obtain ⟨a, rfl⟩ := hc
    have key : ∀ G : univU.El (.arr a .t), (∀ z, (G z).2 = false) → hrT (.arr a .t) G = ⟨.arr a .t, G⟩ := by
      intro G hG
      rw [hrT_arr_t]
      split
      · next h =>
        obtain ⟨x, hx⟩ := h
        have z0 := Classical.choice (Univ.El_nonempty (U := univU) a)
        exact Bool.noConfusion ((hG z0).symm.trans (congrArg Prod.snd (congrFun hx z0)) : false = true)
      · rfl
    exact ⟨_, key (fun _ => (False, false)) (fun _ => rfl)⟩
  · have x0 := Classical.choice (Univ.El_nonempty (U := univU) c)
    exact ⟨x0, hrT_own c (fun a h => hc ⟨a, h⟩) x0⟩

/-- Items of function types identified with each other have the same type and are the same. -/
theorem MhtT_arr_eq (a b c : Code univU.Base) (f : univU.El (.arr a b)) (g : univU.El (.arr a c))
    (h : hrT (.arr a b) f = hrT (.arr a c) g) : b = c ∧ HEq f g := by
  have big : ∀ d, csz a < csz (Code.arr a d) := fun d => by
    show csz a < csz a + csz d + 1
    omega
  by_cases hb : b = .t
  · subst hb
    by_cases hc : c = .t
    · subst hc
      exact ⟨rfl, heq_of_eq (hrT_inj _ f g h)⟩
    · have hg := hrT_own (.arr a c) (fun a' e => hc (Code.arr.inj e).2) g
      rw [hg] at h
      rcases MhtT_hrT_cases (.arr a .t) f with hf | hf
      · rw [hf] at h
        exact ⟨(Code.arr.inj (congrArg Sigma.fst h)).2, (Sigma.mk.inj h).2⟩
      · rw [h] at hf
        rw [hrT_arr_t] at h
        split at h
        · next h' =>
          have := hrT_le a (Classical.choose h')
          rw [h] at this
          exact absurd this (Nat.not_le_of_lt (big c))
        · exact ⟨(Code.arr.inj (congrArg Sigma.fst h)).2, (Sigma.mk.inj h).2⟩
  · have hf := hrT_own (.arr a b) (fun a' e => hb (Code.arr.inj e).2) f
    rw [hf] at h
    rcases MhtT_hrT_cases (.arr a c) g with hg | _
    · rw [hg] at h
      exact ⟨(Code.arr.inj (congrArg Sigma.fst h)).2, (Sigma.mk.inj h).2⟩
    · by_cases hc : c = .t
      · subst hc
        rw [hrT_arr_t] at h
        split at h
        · next h' =>
          have := hrT_le a (Classical.choose h')
          rw [← h] at this
          exact absurd this (Nat.not_le_of_lt (big b))
        · exact ⟨(Code.arr.inj (congrArg Sigma.fst h)).2, (Sigma.mk.inj h).2⟩
      · have hg := hrT_own (.arr a c) (fun a' e => hc (Code.arr.inj e).2) g
        rw [hg] at h
        exact ⟨(Code.arr.inj (congrArg Sigma.fst h)).2, (Sigma.mk.inj h).2⟩

/-! ## The congruence principles -/

theorem MhtT_PCong : MhtTF.Valid PCong := (MhtTF.valid_iff_tr _).mpr <| (show MhtTF.Tr PCong ↔
    ∀ a c d (f : univU.El a → univU.El c) (g : univU.El a → univU.El d) x,
      MhtTF.eqv (.arr a c) (.arr a d) f g → MhtTF.eqv c d (f x) (g x) from Iff.rfl).mpr
  fun a c d f g x h => by
    obtain ⟨hcd, hfg⟩ := MhtT_arr_eq a c d f g h
    subst hcd
    rw [eq_of_heq hfg]

/-- `λx.⊥'` (for `⊥'` the false proposition with the tag `true`) and `λx.(haecceity of ⊥')` have
identified values, but are not identified: they differ in type, and the first is its own root. -/
theorem MhtT_not_PExt : ¬ MhtTF.Valid PExt := fun h => by
  have h1 := (MhtTF.tr_PExt).mp ((MhtTF.valid_iff_tr _).mp h) .e .t (.arr .t .t)
    (fun _ => (False, true)) (fun _ => haeT .t (False, true)) (fun _ => (hrT_hae .t (False, true)).symm)
  have e := congrArg (fun p => csz p.1) h1
  have hle := hrT_le (.arr .e .t) (fun _ => (False, true))
  have hown := hrT_own (.arr .e (.arr .t .t)) (fun a e => by cases e) (fun _ => haeT .t (False, true))
  simp only [hown] at e
  rw [e] at hle
  exact absurd hle (by decide)

/-! ## `≈` -/

theorem MhtT_Inj : MhtTF.Valid Inj := (MhtTF.valid_iff_tr _).mpr <| MhtTF.tr_Inj.mpr fun _ _ _ _ h => by
  injection h with h1 h2; exact ⟨h1, h2⟩

theorem MhtT_Recovery : MhtTF.Valid Recovery := (MhtTF.valid_iff_tr _).mpr <|
  (show MhtTF.Tr Recovery ↔ ∀ a b c d, MhtTF.teq (.arr a c) (.arr b d) ∧ MhtTF.teq a b → MhtTF.teq c d
    from Iff.rfl).mpr fun _ _ _ _ ⟨h, _⟩ => by injection h

/-- Types with the same roots are identical. -/
theorem MhtT_ExtT : MhtTF.Valid ExtT := (MhtTF.valid_iff_tr _).mpr <| MhtTF.tr_ExtT.mpr fun a b ⟨h1, h2⟩ => by
  show a = b
  obtain ⟨x0, hx0⟩ := MhtT_own a
  obtain ⟨y, hy⟩ := h1 x0
  obtain ⟨y0, hy0⟩ := MhtT_own b
  obtain ⟨x, hx⟩ := h2 y0
  have hy' : hrT b y = ⟨a, x0⟩ := (show hrT a x0 = hrT b y from hy).symm.trans hx0
  have hx' : hrT a x = ⟨b, y0⟩ := (show hrT a x = hrT b y0 from hx).trans hy0
  rcases MhtT_hrT_cases b y with e1 | e1
  · exact (congrArg Sigma.fst (hy'.symm.trans e1))
  · rcases MhtT_hrT_cases a x with e2 | e2
    · exact (congrArg Sigma.fst (hx'.symm.trans e2)).symm
    · rw [hy'] at e1
      rw [hx'] at e2
      exact absurd (Nat.lt_trans e1 e2) (Nat.lt_irrefl _)

/-- `□φ` implies `φ`. -/
theorem MhtT_box_holds {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MhtTF.U.TEnv n) (env : MhtTF.U.Env Γ ρ)
    (h : MhtTF.Holds (boxF φ) ρ env) : MhtTF.Holds φ ρ env := by
  have e := eq_of_heq (Sigma.mk.inj ((MhtTF.holds_eqv_t _ _ _ _).mp h)).2
  exact (congrArg Prod.fst e).mpr (fun hall => hall (False, true))

theorem MhtT_IntT : MhtTF.Valid IntT := by
  intro ρ env a b hc
  have hc' := (MhtTF.holds_conj _ _ _ _).mp hc
  exact MhtT_ExtT ρ env a b ⟨MhtT_box_holds _ _ _ hc'.1, MhtT_box_holds _ _ _ hc'.2⟩

/-! ## Necessity of identity and distinctness -/

theorem MhtT_NIEqv : MhtTF.Valid NIEqv := by
  intro ρ env a
  refine (MhtTF.holds_all _ _ _ _).mpr fun x => (MhtTF.holds_all _ _ _ _).mpr fun y h => ?_
  exact (MhtTF.holds_eqv_t _ _ _ _).mpr (congrArg (fun p => (⟨.t, p⟩ : Σ c : Code univU.Base, univU.El c))
    (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl))

theorem MhtT_NITeq : MhtTF.Valid NITeq := by
  intro ρ env a b h
  exact (MhtTF.holds_eqv_t _ _ _ _).mpr (congrArg (fun p => (⟨.t, p⟩ : Σ c : Code univU.Base, univU.El c))
    (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl))

theorem MhtT_NDTeq : MhtTF.Valid NDTeq := by
  intro ρ env a b h
  exact (MhtTF.holds_eqv_t _ _ _ _).mpr (congrArg (fun p => (⟨.t, p⟩ : Σ c : Code univU.Base, univU.El c))
    (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl))

theorem MhtT_NIX : MhtTF.Valid NIX := by
  intro ρ env a b
  refine (MhtTF.holds_all _ _ _ _).mpr fun x => (MhtTF.holds_all _ _ _ _).mpr fun y h => ?_
  exact (MhtTF.holds_eqv_t _ _ _ _).mpr (congrArg (fun p => (⟨.t, p⟩ : Σ c : Code univU.Base, univU.El c))
    (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl))

theorem MhtT_NDX : MhtTF.Valid NDX := by
  intro ρ env a b
  refine (MhtTF.holds_all _ _ _ _).mpr fun x => (MhtTF.holds_all _ _ _ _).mpr fun y h => ?_
  exact (MhtTF.holds_eqv_t _ _ _ _).mpr (congrArg (fun p => (⟨.t, p⟩ : Σ c : Code univU.Base, univU.El c))
    (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl))

/-! ## Booleanism and the Identity Identity -/

/-- `¬¬p` has the tag `true`, while `p` may have the tag `false`. -/
theorem MhtT_not_DNeg : ¬ MhtTF.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MhtTF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (True, false)
  have e := eq_of_heq (Sigma.mk.inj ((MhtTF.holds_eqv_t _ _ _ _).mp h0)).2
  exact Bool.noConfusion (congrArg Prod.snd e : true = false)

theorem MhtT_not_Bool : ¬ ∀ φ, BoolSch φ → MhtTF.Valid φ := fun h => MhtT_not_DNeg (h _ DNeg_bool)

theorem MhtT_IdId : MhtTF.Valid IdId := (MhtTF.valid_iff_tr _).mpr <| (show MhtTF.Tr IdId ↔
    ∀ a (x y : univU.El a), MhtTF.eqv .t .t (MhtTF.eqv a a x y, true)
      ((∀ P : univU.El a → TV, (P x).1 → (P y).1 : Prop), true) from Iff.rfl).mpr
  fun a x y => congrArg (fun p => (⟨.t, p⟩ : Σ c : Code univU.Base, univU.El c))
    (Prod.ext (propext ⟨fun h _ hP => hrT_inj a x y h ▸ hP,
      fun h => h (fun z => ((hrT a x = hrT a z : Prop), true)) rfl⟩) rfl)

/-! ## Barcan formulas and Necessitism -/

/-- `𝔸α ⊤` is type-quantified, so it has the tag `false` and is not identical to `⊤`. -/
theorem MhtT_not_TBF : ¬ ∀ χ, TBFSch χ → MhtTF.Valid χ := fun h => by
  have h0 := h _ ⟨topF, rfl⟩ (fun i => i.elim0) ()
  have hb := (MhtTF.holds_imp _ _ _ _).mp h0 (fun _ => (MhtTF.holds_eqv_t _ _ _ _).mpr rfl)
  have e := eq_of_heq (Sigma.mk.inj ((MhtTF.holds_eqv_t _ _ _ _).mp hb)).2
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

theorem MhtT_TCBF : ∀ χ, TCBFSch χ → MhtTF.Valid χ := by
  rintro χ ⟨φ, rfl⟩ ρ env hb
  have e := eq_of_heq (Sigma.mk.inj ((MhtTF.holds_eqv_t _ _ _ _).mp hb)).2
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

theorem MhtT_not_TNec : ¬ MhtTF.Valid TNec := fun h => by
  have hb := (MhtTF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e
  have e := eq_of_heq (Sigma.mk.inj ((MhtTF.holds_eqv_t _ _ _ _).mp hb)).2
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

theorem MhtT_BF : MhtTF.Valid BF := (MhtTF.valid_iff_tr _).mpr <| (show MhtTF.Tr BF ↔
    ∀ a (G : univU.El a → TV), (∀ x, MhtTF.eqv .t .t (G x) ((¬ ∀ p : TV, p.1 : Prop), true)) →
      MhtTF.eqv .t .t ((∀ x, (G x).1 : Prop), true) ((¬ ∀ p : TV, p.1 : Prop), true) from Iff.rfl).mpr
  fun _ _ h => congrArg (fun p => (⟨.t, p⟩ : Σ c : Code univU.Base, univU.El c))
    (Prod.ext (propext ⟨fun _ hall => hall (False, true),
      fun _ x => (congrArg Prod.fst (eq_of_heq (Sigma.mk.inj (h x)).2)).mpr (fun hall => hall (False, true))⟩) rfl)

theorem MhtT_Nec : MhtTF.Valid Nec := (MhtTF.valid_iff_tr _).mpr <| (show MhtTF.Tr Nec ↔
    ∀ a (x : univU.El a), MhtTF.eqv .t .t ((∃ y, MhtTF.eqv a a x y : Prop), true)
      ((¬ ∀ p : TV, p.1 : Prop), true) from Iff.rfl).mpr
  fun _ x => congrArg (fun p => (⟨.t, p⟩ : Σ c : Code univU.Base, univU.El c))
    (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => ⟨x, rfl⟩⟩) rfl)

end Tg
end PIF
