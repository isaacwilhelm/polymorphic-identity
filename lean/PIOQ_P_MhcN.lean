import PIBF
set_option autoImplicit false

/-!
# Open questions: the profile of `𝔐_hae,2⁻`

The haecceity tower `Mhc` of `PIHaeQs.lean`, over `E = {true, false}`: the two entities have the same
root, the haecceity of an item has the root of the item, and every other item is its own root. Items
are identified just in case their roots agree, and `≈` is identity of types.

The only haecceity of an entity is the universal property of entities; so, apart from the two
entities, items of the same type are identified only if they are the same. In particular, functions
are identified only with themselves: PCong holds. The constant functions `true` and `false` on
entities have identified values everywhere, but are distinct: PExt fails. Propositions are their own
roots, so PropExt≡ holds, and with it Bool.

Each root is of the item's own type or of a smaller one, and every type has an item whose root is of
that very type (for `α→t`, the empty property): so Ext≈ holds, and with it Int≈.

LL≡/≈ fails for a polymorphic predicate with a free variable `G0 : e→t` naming `λz.(z = true)`: at
`e` the predicate is `G0` itself, which tells `true` and `false` apart although `true ≡ false`.
-/

namespace PIF

section MhcNP
attribute [local instance] Classical.propDecidable

/-! ## Roots -/

/-- An item of a type `α→β`, with `β` other than `t`, is its own root. -/
theorem MhcN_hr_ne_t (a c : Code univB2.Base) (hc : c ≠ .t) (f : univB2.El (.arr a c)) :
    hr ovHC (.arr a c) f = ⟨.arr a c, f⟩ := by
  cases c with
  | e => exact ovHC_ne (.arr a .e) (fun h => nomatch h) f
  | t => exact absurd rfl hc
  | base b => exact b.elim
  | arr c1 c2 => exact ovHC_ne (.arr a (.arr c1 c2)) (fun h => nomatch h) f

/-- An item of a type `α→t` is its own root, or a haecceity. -/
theorem MhcN_hr_t_cases (a : Code univB2.Base) (G : univB2.El (.arr a .t)) :
    hr ovHC (.arr a .t) G = ⟨.arr a .t, G⟩ ∨ ∃ x, G = haeF ovHC a x := by
  rw [hr_arr_t]
  split
  · next h => exact Or.inr ⟨Classical.choose h, Classical.choose_spec h⟩
  · exact Or.inl (ovHC_ne (.arr a .t) (fun h => nomatch h) G)

/-- No item of `α` has a root of type `α→γ`. -/
theorem MhcN_small (a c : Code univB2.Base) (x : univB2.El a) (g : univB2.El (.arr a c))
    (h : hr ovHC a x = ⟨.arr a c, g⟩) : False := by
  have h3 := hr_le ovHC_le a x
  rw [h] at h3
  change csz a + csz c + 1 ≤ csz a at h3
  omega

/-- Functions identified with each other are the same function. -/
theorem MhcN_fun_inj (a c d : Code univB2.Base) (f : univB2.El (.arr a c)) (g : univB2.El (.arr a d))
    (h : hr ovHC (.arr a c) f = hr ovHC (.arr a d) g) :
    (⟨.arr a c, f⟩ : Σ c, univB2.El c) = ⟨.arr a d, g⟩ := by
  by_cases hc : c = .t
  · subst hc
    by_cases hd : d = .t
    · subst hd
      rcases MhcN_hr_t_cases a f with hf | ⟨x1, rfl⟩ <;>
        rcases MhcN_hr_t_cases a g with hg | ⟨x2, rfl⟩
      · rw [hf, hg] at h
        exact h
      · rw [hf, hr_hae] at h
        exact (MhcN_small a .t x2 f h.symm).elim
      · rw [hg, hr_hae] at h
        exact (MhcN_small a .t x1 g h).elim
      · rw [hr_hae, hr_hae] at h
        have e : haeF ovHC a x1 = haeF ovHC a x2 := funext fun y => by
          show (hr ovHC a y = hr ovHC a x1) = (hr ovHC a y = hr ovHC a x2)
          rw [h]
        rw [e]
    · rw [MhcN_hr_ne_t a d hd g] at h
      rcases MhcN_hr_t_cases a f with hf | ⟨x1, rfl⟩
      · rw [hf] at h
        exact h
      · rw [hr_hae] at h
        exact (MhcN_small a d x1 g h).elim
  · rw [MhcN_hr_ne_t a c hc f] at h
    by_cases hd : d = .t
    · subst hd
      rcases MhcN_hr_t_cases a g with hg | ⟨x2, rfl⟩
      · rw [hg] at h
        exact h
      · rw [hr_hae] at h
        exact (MhcN_small a c x2 f h.symm).elim
    · rw [MhcN_hr_ne_t a d hd g] at h
      exact h

/-- The root of an item is of the item's own type, or of a smaller one. -/
theorem MhcN_hr_cases : ∀ (c : Code univB2.Base) (x : univB2.El c),
    (hr ovHC c x).1 = c ∨ csz (hr ovHC c x).1 < csz c
  | .e, x => Or.inl (congrArg Sigma.fst (hrHC_e x))
  | .t, x => Or.inl (congrArg Sigma.fst (hrHC_t x))
  | .base b, _ => b.elim
  | .arr a c, f => by
    by_cases hc : c = .t
    · subst hc
      rcases MhcN_hr_t_cases a f with hf | ⟨x, rfl⟩
      · exact Or.inl (congrArg Sigma.fst hf)
      · rw [hr_hae]
        have := hr_le ovHC_le a x
        refine Or.inr ?_
        change csz (hr ovHC a x).1 < csz a + csz (Code.t : Code univB2.Base) + 1
        omega
    · exact Or.inl (congrArg Sigma.fst (MhcN_hr_ne_t a c hc f))

/-- Every type has an item whose root is of that type. -/
theorem MhcN_own : ∀ c : Code univB2.Base, ∃ x : univB2.El c, (hr ovHC c x).1 = c
  | .e => ⟨true, congrArg Sigma.fst (hrHC_e true)⟩
  | .t => ⟨True, congrArg Sigma.fst (hrHC_t True)⟩
  | .base b => b.elim
  | .arr a c => by
    by_cases hc : c = .t
    · subst hc
      exact ⟨fun _ => False, congrArg Sigma.fst (hrHC_empty a)⟩
    · obtain ⟨x0⟩ := Univ.El_nonempty (U := univB2) (.arr a c)
      exact ⟨x0, congrArg Sigma.fst (MhcN_hr_ne_t a c hc x0)⟩

theorem MhcN_eqv_t (p q : Prop) : Mhc.eqv .t .t p q ↔ p = q :=
  ⟨fun h => by
    have h' : hr ovHC .t p = hr ovHC .t q := h
    rw [hrHC_t, hrHC_t] at h'
    exact eq_of_heq (Sigma.mk.inj h').2,
   fun h => h ▸ MhcD.refl _⟩

/-! ## Congruence and extensionality -/

/-- PCong holds: functions are identified only with themselves. -/
theorem MhcN_PCong : Mhc.Valid PCong :=
  (Mhc.valid_iff_tr _).mpr <| Mhc.tr_PCong.mpr fun a c d f g x h => by
    have e := MhcN_fun_inj a c d f g h
    have e1 : Code.arr a c = Code.arr a d := congrArg Sigma.fst e
    injection e1 with _ hcd
    subst hcd
    have hfg : f = g := eq_of_heq (Sigma.mk.inj e).2
    subst hfg
    exact MhcD.refl _

/-- PExt fails: the constant functions `true` and `false` on entities have identified values
everywhere, but each is its own root. -/
theorem MhcN_not_PExt : ¬ Mhc.Valid PExt := fun h => by
  have := Mhc.tr_PExt.mp ((Mhc.valid_iff_tr _).mp h) .e .e .e
    (fun _ => true) (fun _ => false) (fun _ => (hrHC_e true).trans (hrHC_e false).symm)
  have e : (⟨.arr .e .e, (fun _ => true : univB2.El (.arr .e .e))⟩ : Σ c, univB2.El c) =
      ⟨.arr .e .e, (fun _ => false : univB2.El (.arr .e .e))⟩ :=
    (MhcN_hr_ne_t .e .e (fun h => nomatch h) _).symm.trans
      ((this : hr ovHC (.arr .e .e) (fun _ => true : univB2.El (.arr .e .e)) =
        hr ovHC (.arr .e .e) (fun _ => false : univB2.El (.arr .e .e))).trans
        (MhcN_hr_ne_t .e .e (fun h => nomatch h) _))
  exact Bool.noConfusion (congrFun (eq_of_heq (Sigma.mk.inj e).2) true)

/-! ## Propositions -/

theorem MhcN_PropExt : Mhc.Valid PropExt := Mhc.PropExt_valid Mhc_model

theorem MhcN_Bool : ∀ φ, BoolSch φ → Mhc.Valid φ := fun φ hφ =>
  Mhc.soundness Mhc_model (Ax := (· = PropExt)) (fun _ h => h ▸ MhcN_PropExt)
    (d_Bool_of_PropExt (S := (· = PropExt)) rfl φ hφ)

/-! ## Identification across types -/

theorem MhcN_ExtT : Mhc.Valid ExtT :=
  (Mhc.valid_iff_tr _).mpr <| Mhc.tr_ExtT.mpr fun a b ⟨h1, h2⟩ => by
    show a = b
    refine Classical.byContradiction fun hab => ?_
    obtain ⟨x, hx⟩ := MhcN_own a
    obtain ⟨y, hy⟩ := h1 x
    have hy' : (hr ovHC b y).1 = a := (congrArg Sigma.fst (hy : hr ovHC a x = hr ovHC b y)).symm.trans hx
    obtain ⟨y', hy2⟩ := MhcN_own b
    obtain ⟨x', hx'⟩ := h2 y'
    have hx2 : (hr ovHC a x').1 = b := (congrArg Sigma.fst (hx' : hr ovHC a x' = hr ovHC b y')).trans hy2
    rcases MhcN_hr_cases b y with h3 | h3
    · exact hab (hy'.symm.trans h3)
    · rcases MhcN_hr_cases a x' with h4 | h4
      · exact hab (h4.symm.trans hx2)
      · rw [hy'] at h3
        rw [hx2] at h4
        omega

theorem MhcN_IntT : Mhc.Valid IntT := (Mhc.IntT_iff_ExtT MhcN_eqv_t).mpr MhcN_ExtT

/-! ## LL≡/≈, with a free variable -/

/-- The context `G0 : e→t`. -/
abbrev MhcN_ΓG0 : Ctx 0 := Ctx.nil.ext tyE.pred

open Tm in
/-- `λγ.λx:γ.∀_{γ→t}F (F ≡_{γ→t,e→t} G0 → F x)`: at `γ = e`, this is `G0` itself. -/
def MhcN_PG0 : Tm MhcN_ΓG0 (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (all tv0.pred (imp (eqv tv0.pred tyE.pred (.var .here) (.var (.there (.there (.tthere .here)))))
    (.app (.var .here) (.var (.there .here))))))

theorem MhcN_holds_Bridge (G0 : Bool → Prop) :
    Mhc.Holds (Bridge MhcN_PG0) (fun i => i.elim0) ((), G0) ↔
      ∀ (a b : Code univB2.Base) (x : univB2.El a) (y : univB2.El b), Mhc.eqv a b x y ∧ a = b →
        (∀ F : univB2.El a → Prop, Mhc.eqv (.arr a .t) (.arr .e .t) F G0 → F x) →
        (∀ F : univB2.El b → Prop, Mhc.eqv (.arr b .t) (.arr .e .t) F G0 → F y) := Iff.rfl

/-- **LL≡/≈ with a free variable fails**: with `G0 := λz.(z = true)`, every property identified
with `G0` holds of `true` (it is `G0`, or the universal property of entities), but `G0` does not
hold of `false`, although `true ≡ false`. -/
theorem MhcN_not_Bridge : ¬ Mhc.Valid (Bridge MhcN_PG0) := fun h => by
  have h1 := (MhcN_holds_Bridge (fun z => z = true)).mp (h (fun i => i.elim0) ((), fun z => z = true))
    .e .e true false ⟨(hrHC_e true).trans (hrHC_e false).symm, rfl⟩
    (fun F hF => by
      have hF' : hr ovHC (.arr .e .t) F = hr ovHC (.arr .e .t) (fun z : Bool => z = true) := hF
      rcases MhcN_hr_t_cases .e F with hF1 | ⟨x, rfl⟩
      · rcases MhcN_hr_t_cases .e (fun z : Bool => z = true) with hG | ⟨x, hx⟩
        · have e := hF1.symm.trans (hF'.trans hG)
          have e2 : F = (fun z : Bool => z = true) := eq_of_heq (Sigma.mk.inj e).2
          subst e2
          exact rfl
        · have h2 : (false = true) = (hr ovHC .e false = hr ovHC .e x) := congrFun hx false
          exact (Bool.noConfusion (cast h2.symm ((hrHC_e false).trans (hrHC_e x).symm) : false = true))
      · exact (hrHC_e true).trans (hrHC_e x).symm)
    (fun z => z = true) (MhcD.refl _)
  exact Bool.noConfusion (h1 : false = true)

end MhcNP

end PIF
