import PIBF

/-!
# The profile of `𝔐_hae,int`

The model `MhtF` of `PINew.lean`: tagged propositions (`PITagged.lean`), haecceity towers `hrT`,
with every quantified proposition (first-order or type-quantified) carrying the tag `false`. So `□φ`
(that is, `φ ≡_t ⊤`) is true just when `φ` is true and has the tag `true`; in particular `□ψ` is
false for every quantified `ψ`.

`≡` and `≈` are as in `𝔐_hae,int,1` (`PIOQ_P_MhtT.lean`): items are identified when their roots
(`hrT`) agree, and `≈` is identity of types. Each item's root is either the item itself, or (for a
haecceity) the root of an item of a smaller type, and every type has an item that is its own root.
-/
set_option autoImplicit false

namespace PIF
namespace Tg
open Tm

/-! ## Roots -/

/-- An item is its own root, or its root lies at a smaller type. -/
theorem Mht_hrT_cases (c : Code univU.Base) (x : univU.El c) :
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
theorem Mht_own (c : Code univU.Base) : ∃ x : univU.El c, hrT c x = ⟨c, x⟩ := by
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
theorem Mht_arr_eq (a b c : Code univU.Base) (f : univU.El (.arr a b)) (g : univU.El (.arr a c))
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
      rcases Mht_hrT_cases (.arr a .t) f with hf | hf
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
    rcases Mht_hrT_cases (.arr a c) g with hg | _
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

/-- `□φ` holds only if `φ` has the tag `true` (and is true). -/
theorem Mht_box_tag {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MhtF.U.TEnv n) (env : MhtF.U.Env Γ ρ)
    (h : MhtF.Holds (boxF φ) ρ env) : (MhtF.eval φ ρ env).2 = true :=
  congrArg Prod.snd (eq_of_heq (Sigma.mk.inj ((MhtF.holds_eqv_t _ _ _ _).mp h)).2)

/-! ## The congruence principles -/

theorem Mht_PCong : MhtF.Valid PCong := (MhtF.valid_iff_tr _).mpr <| (show MhtF.Tr PCong ↔
    ∀ a c d (f : univU.El a → univU.El c) (g : univU.El a → univU.El d) x,
      MhtF.eqv (.arr a c) (.arr a d) f g → MhtF.eqv c d (f x) (g x) from Iff.rfl).mpr
  fun a c d f g x h => by
    obtain ⟨hcd, hfg⟩ := Mht_arr_eq a c d f g h
    subst hcd
    rw [eq_of_heq hfg]

/-- `λx.⊥'` (for `⊥'` the false proposition with the tag `true`) and `λx.(haecceity of ⊥')` have
identified values, but are not identified: they differ in type, and the first is its own root. -/
theorem Mht_not_PExt : ¬ MhtF.Valid PExt := fun h => by
  have h1 := (MhtF.tr_PExt).mp ((MhtF.valid_iff_tr _).mp h) .e .t (.arr .t .t)
    (fun _ => (False, true)) (fun _ => haeT .t (False, true)) (fun _ => (hrT_hae .t (False, true)).symm)
  have e := congrArg (fun p => csz p.1) h1
  have hle := hrT_le (.arr .e .t) (fun _ => (False, true))
  have hown := hrT_own (.arr .e (.arr .t .t)) (fun a e => by cases e) (fun _ => haeT .t (False, true))
  simp only [hown] at e
  rw [e] at hle
  exact absurd hle (by decide)

/-! ## `≈` -/

theorem Mht_Inj : MhtF.Valid Inj := (MhtF.valid_iff_tr _).mpr <| MhtF.tr_Inj.mpr fun _ _ _ _ h => by
  injection h with h1 h2; exact ⟨h1, h2⟩

theorem Mht_Recovery : MhtF.Valid Recovery := (MhtF.valid_iff_tr _).mpr <|
  (show MhtF.Tr Recovery ↔ ∀ a b c d, MhtF.teq (.arr a c) (.arr b d) ∧ MhtF.teq a b → MhtF.teq c d
    from Iff.rfl).mpr fun _ _ _ _ ⟨h, _⟩ => by injection h

/-- Types with the same roots are identical. -/
theorem Mht_ExtT : MhtF.Valid ExtT := (MhtF.valid_iff_tr _).mpr <| MhtF.tr_ExtT.mpr fun a b ⟨h1, h2⟩ => by
  show a = b
  obtain ⟨x0, hx0⟩ := Mht_own a
  obtain ⟨y, hy⟩ := h1 x0
  obtain ⟨y0, hy0⟩ := Mht_own b
  obtain ⟨x, hx⟩ := h2 y0
  have hy' : hrT b y = ⟨a, x0⟩ := (show hrT a x0 = hrT b y from hy).symm.trans hx0
  have hx' : hrT a x = ⟨b, y0⟩ := (show hrT a x = hrT b y0 from hx).trans hy0
  rcases Mht_hrT_cases b y with e1 | e1
  · exact (congrArg Sigma.fst (hy'.symm.trans e1))
  · rcases Mht_hrT_cases a x with e2 | e2
    · exact (congrArg Sigma.fst (hx'.symm.trans e2)).symm
    · rw [hy'] at e1
      rw [hx'] at e2
      exact absurd (Nat.lt_trans e1 e2) (Nat.lt_irrefl _)

/-- `□(∀x∃y x ≡ y)` is false, since the quantified proposition has the tag `false`. -/
theorem Mht_IntT : MhtF.Valid IntT := by
  intro ρ env a b hc
  have hs := Mht_box_tag _ _ _ ((MhtF.holds_conj _ _ _ _).mp hc).1
  have h0 : (MhtF.eval (subT (Γ := (Ctx.nil.text).text)) (scons b (scons a ρ)) env).2 = false :=
    MhtF.eval_all_snd _ _ _ _
  exact (Bool.false_ne_true (h0.symm.trans hs)).elim

/-! ## Necessity of identity and distinctness for types -/

theorem Mht_NITeq : MhtF.Valid NITeq := by
  intro ρ env a b h
  exact (MhtF.holds_eqv_t _ _ _ _).mpr (congrArg (fun p => (⟨.t, p⟩ : Σ c : Code univU.Base, univU.El c))
    (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl))

theorem Mht_NDTeq : MhtF.Valid NDTeq := by
  intro ρ env a b h
  exact (MhtF.holds_eqv_t _ _ _ _).mpr (congrArg (fun p => (⟨.t, p⟩ : Σ c : Code univU.Base, univU.El c))
    (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl))

/-! ## Booleanism -/

/-- `¬¬p` has the tag `true`, while `p` may have the tag `false`. -/
theorem Mht_not_DNeg : ¬ MhtF.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MhtF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (True, false)
  have e := eq_of_heq (Sigma.mk.inj ((MhtF.holds_eqv_t _ _ _ _).mp h0)).2
  exact Bool.noConfusion (congrArg Prod.snd e : true = false)

theorem Mht_not_Bool : ¬ ∀ φ, BoolSch φ → MhtF.Valid φ := fun h => Mht_not_DNeg (h _ DNeg_bool)

/-! ## Barcan formulas and Necessitism -/

/-- `𝔸α ⊤` is type-quantified, so it has the tag `false` and is not identical to `⊤`. -/
theorem Mht_not_TBF : ¬ ∀ χ, TBFSch χ → MhtF.Valid χ := fun h => by
  have h0 := h _ ⟨topF, rfl⟩ (fun i => i.elim0) ()
  have hb := (MhtF.holds_imp _ _ _ _).mp h0 (fun _ => (MhtF.holds_eqv_t _ _ _ _).mpr rfl)
  have e := eq_of_heq (Sigma.mk.inj ((MhtF.holds_eqv_t _ _ _ _).mp hb)).2
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

theorem Mht_TCBF : ∀ χ, TCBFSch χ → MhtF.Valid χ := by
  rintro χ ⟨φ, rfl⟩ ρ env hb
  have e := eq_of_heq (Sigma.mk.inj ((MhtF.holds_eqv_t _ _ _ _).mp hb)).2
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

theorem Mht_not_TNec : ¬ MhtF.Valid TNec := fun h => by
  have hb := (MhtF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e
  have e := eq_of_heq (Sigma.mk.inj ((MhtF.holds_eqv_t _ _ _ _).mp hb)).2
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

/-- `□∀x F x` is false, since `∀x F x` has the tag `false`. -/
theorem Mht_CBF : MhtF.Valid CBF := by
  intro ρ env
  refine (MhtF.holds_tall _ _ _).mpr fun a => (MhtF.holds_all _ _ _ _).mpr fun G => ?_
  refine (MhtF.holds_imp _ _ _ _).mpr fun hb => ?_
  have hs := Mht_box_tag _ _ _ hb
  have h0 := MhtF.eval_all_snd (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here))
    (scons a ρ) (env, G)
  exact (Bool.false_ne_true (h0.symm.trans hs)).elim

end Tg
end PIF
