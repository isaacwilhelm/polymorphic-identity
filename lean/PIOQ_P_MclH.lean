import PIBF
set_option autoImplicit false

/-!
# Open questions: the profile of `𝔐_cl,hae`

`𝔐_cl,hae` (`MclHF`, defined in `PIHaeQs`) is `𝔐_cl` (propositions `Option Bool`, with `none` the
one truth) except that items are identified just in case they have the same root (haecceity towers
`rootA`), and `≈` is identity of codes.

* Inj≈ and Recovery hold, since `≈` is identity of codes.
* PCong holds: functions with one domain and the same root have the same codomain, so they are of
  one type, and identical.
* Ext≈ and Int≈ hold: every type has an item which is its own root, and roots never lie at larger
  types; and `□φ` holds just in case `φ` does.
* PExt fails: the constant function from `e` to the entity and the constant function to its
  haecceity agree pointwise up to identity, but their roots have different types.
* The Identity Identity fails, as in `𝔐_cl`: `⊤ ≡ some false` is `some true`, while the
  corresponding universal claim is `some false`.
-/

namespace PIF
namespace Al
open Tm

/-! ## Facts about roots -/

/-- The root of an item of `α→β` is the item itself, unless `β` is `t` and the root lies at a code
no larger than `α`. -/
theorem MclH_root_arr (a b : Code Empty) (f : univA.El (.arr a b)) :
    (rootA (.arr a b) f).1 = .arr a b ∨ (b = .t ∧ csz (rootA (.arr a b) f).1 ≤ csz a) := by
  cases b with
  | t =>
    by_cases h : ∃ z, f = hcyA a z
    · obtain ⟨z, rfl⟩ := h
      refine Or.inr ⟨rfl, ?_⟩
      have e : csz (rootA (.arr a .t) (hcyA a z)).1 = csz (rootA a z).1 :=
        congrArg (fun r => csz r.1) (groot_hcy hcyA_inj a z)
      exact Nat.le_trans (Nat.le_of_eq e) (groot_le _ _ a z)
    · exact Or.inl (congrArg Sigma.fst (groot_not univA.El hcyA a f h))
  | e => exact Or.inl rfl
  | base x => exact x.elim
  | arr c d => exact Or.inl rfl

/-- The root of an item has the item's code, or a smaller one. -/
theorem MclH_root (c : Code Empty) (x : univA.El c) : (rootA c x).1 = c ∨ csz (rootA c x).1 < csz c :=
  (groot_lt univA.El hcyA c x).elim (fun h => Or.inl (congrArg Sigma.fst h)) Or.inr

/-- Functions with the same domain and the same root have the same codomain. -/
theorem MclH_cod {a b c : Code Empty} (f : univA.El (.arr a b)) (g : univA.El (.arr a c))
    (h : rootA (.arr a b) f = rootA (.arr a c) g) : b = c := by
  have hs := congrArg Sigma.fst h
  rcases MclH_root_arr a b f with h1 | ⟨h1, h2⟩ <;> rcases MclH_root_arr a c g with h3 | ⟨h3, h4⟩
  · exact (Code.arr.inj (h1.symm.trans (hs.trans h3))).2
  · have h5 : csz (Code.arr a b) ≤ csz a := Nat.le_trans (Nat.le_of_eq (congrArg csz (h1.symm.trans hs))) h4
    have h6 : csz a + csz b + 1 ≤ csz a := h5
    omega
  · have h5 : csz (Code.arr a c) ≤ csz a := Nat.le_trans (Nat.le_of_eq (congrArg csz (h3.symm.trans hs.symm))) h2
    have h6 : csz a + csz c + 1 ≤ csz a := h5
    omega
  · exact h1.trans h3.symm

/-- Every type has an item which is its own root. -/
theorem MclH_own : ∀ c : Code Empty, ∃ x : univA.El c, (rootA c x).1 = c
  | .arr a .t => by
    refine ⟨fun _ => some true, ?_⟩
    have hn : ¬ ∃ z, (fun _ => some true : univA.El (.arr a .t)) = hcyA a z := fun ⟨z, hz⟩ => by
      have e1 : (some true : Option Bool) = mkA (z = z) := congrFun hz z
      rw [mkA_pos rfl] at e1
      exact nomatch e1
    exact congrArg Sigma.fst (groot_not univA.El hcyA a _ hn)
  | .e => ⟨(), rfl⟩
  | .t => ⟨none, rfl⟩
  | .base b => b.elim
  | .arr a .e => ⟨Classical.choice (Univ.El_nonempty (U := univA) (.arr a .e)), rfl⟩
  | .arr _ (.base b) => b.elim
  | .arr a (.arr c d) => ⟨Classical.choice (Univ.El_nonempty (U := univA) (.arr a (.arr c d))), rfl⟩

/-- Types each of whose items has the same root as an item of the other are the same type. -/
theorem MclH_ext_core (a b : Code Empty)
    (hs : ∀ x : univA.El a, ∃ y : univA.El b, rootA a x = rootA b y)
    (hp : ∀ y : univA.El b, ∃ x : univA.El a, rootA a x = rootA b y) : a = b := by
  obtain ⟨x0, hx0⟩ := MclH_own a
  obtain ⟨y0, hy0⟩ := MclH_own b
  obtain ⟨y, hy⟩ := hs x0
  obtain ⟨x, hx⟩ := hp y0
  have c1 : (rootA b y).1 = a := (congrArg Sigma.fst hy).symm.trans hx0
  have c2 : (rootA a x).1 = b := (congrArg Sigma.fst hx).trans hy0
  rcases MclH_root b y with r1 | r1 <;> rcases MclH_root a x with r2 | r2
  · exact c1.symm.trans r1
  · exact c1.symm.trans r1
  · exact (c2.symm.trans r2).symm
  · rw [c1] at r1
    rw [c2] at r2
    exact absurd (Nat.lt_trans r1 r2) (Nat.lt_irrefl _)

/-- In `𝔐_cl,hae`, `□φ` holds just in case `φ` does. -/
theorem MclH_holds_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MclHF.U.TEnv n) (env : MclHF.U.Env Γ ρ) :
    MclHF.Holds (boxF φ) ρ env ↔ MclHF.Holds φ ρ env := by
  refine (MclHF.holds_eqv_t _ _ _ _).trans ⟨fun h => ?_, fun h => (mkA_V _).mpr ?_⟩
  · exact (eq_of_heq (Sigma.mk.inj ((mkA_V _).mp h)).2).trans (MclH_topF ρ env)
  · exact congrArg (fun q => (⟨.t, q⟩ : Σ b : Code univA.Base, univA.El b))
      ((show MclHF.eval φ ρ env = none from h).trans (MclH_topF ρ env).symm)

/-! ## Valid principles -/

theorem MclH_PCong : MclHF.Valid PCong := by
  intro ρ env
  refine (MclHF.holds_tall _ _ _).mpr fun a => (MclHF.holds_tall _ _ _).mpr fun c =>
    (MclHF.holds_tall _ _ _).mpr fun d => ?_
  refine (MclHF.holds_all _ _ _ _).mpr fun f => (MclHF.holds_all _ _ _ _).mpr fun g =>
    (MclHF.holds_all _ _ _ _).mpr fun x => ?_
  refine (MclHF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : rootA (.arr a c) f = rootA (.arr a d) g := (mkA_V _).mp ((MclHF.holds_eqv _ _ _ _ _ _).mp h)
  have hcd : c = d := MclH_cod (a := a) (b := c) (c := d) f g h'
  subst hcd
  have hfg := groot_inj hcyA_inj (.arr a c) f g h'
  subst hfg
  exact (MclHF.holds_eqv _ _ _ _ _ _).mpr ((mkA_V _).mpr rfl)

theorem MclH_Inj : MclHF.Valid Inj := by
  intro ρ env
  refine (MclHF.holds_tall _ _ _).mpr fun a => (MclHF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclHF.holds_tall _ _ _).mpr fun c => (MclHF.holds_tall _ _ _).mpr fun d => ?_
  refine (MclHF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (mkA_V _).mp ((MclHF.holds_teq _ _ _ _).mp h)
  injection h' with hab hcd
  exact (MclHF.holds_conj _ _ _ _).mpr ⟨(MclHF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr hab),
    (MclHF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr hcd)⟩

theorem MclH_Recovery : MclHF.Valid Recovery := by
  intro ρ env
  refine (MclHF.holds_tall _ _ _).mpr fun a => (MclHF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclHF.holds_tall _ _ _).mpr fun c => (MclHF.holds_tall _ _ _).mpr fun d => ?_
  refine (MclHF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d :=
    (mkA_V _).mp ((MclHF.holds_teq _ _ _ _).mp ((MclHF.holds_conj _ _ _ _).mp h).1)
  exact (MclHF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr (Code.arr.inj h').2)

theorem MclH_ExtT : MclHF.Valid ExtT := by
  intro ρ env
  refine (MclHF.holds_tall _ _ _).mpr fun a => (MclHF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclHF.holds_imp _ _ _ _).mpr fun h => (MclHF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr ?_)
  have hc := (MclHF.holds_conj _ _ _ _).mp h
  refine MclH_ext_core a b (fun x => ?_) (fun y => ?_)
  · obtain ⟨y, hy⟩ := (MclHF.holds_ex _ _ _ _).mp ((MclHF.holds_all _ _ _ _).mp hc.1 x)
    exact ⟨y, (mkA_V _).mp ((MclHF.holds_eqv _ _ _ _ _ _).mp hy)⟩
  · obtain ⟨x, hx⟩ := (MclHF.holds_ex _ _ _ _).mp ((MclHF.holds_all _ _ _ _).mp hc.2 y)
    exact ⟨x, (mkA_V _).mp ((MclHF.holds_eqv _ _ _ _ _ _).mp hx)⟩

theorem MclH_IntT : MclHF.Valid IntT := by
  intro ρ env
  refine (MclHF.holds_tall _ _ _).mpr fun a => (MclHF.holds_tall _ _ _).mpr fun b => ?_
  refine (MclHF.holds_imp _ _ _ _).mpr fun h => (MclHF.holds_teq _ _ _ _).mpr ((mkA_V _).mpr ?_)
  have hc := (MclHF.holds_conj _ _ _ _).mp h
  have h1 := (MclH_holds_box _ _ _).mp hc.1
  have h2 := (MclH_holds_box _ _ _).mp hc.2
  refine MclH_ext_core a b (fun x => ?_) (fun y => ?_)
  · obtain ⟨y, hy⟩ := (MclHF.holds_ex _ _ _ _).mp ((MclHF.holds_all _ _ _ _).mp h1 x)
    exact ⟨y, (mkA_V _).mp ((MclHF.holds_eqv _ _ _ _ _ _).mp hy)⟩
  · obtain ⟨x, hx⟩ := (MclHF.holds_ex _ _ _ _).mp ((MclHF.holds_all _ _ _ _).mp h2 y)
    exact ⟨x, (mkA_V _).mp ((MclHF.holds_eqv _ _ _ _ _ _).mp hx)⟩

/-! ## Refuted principles -/

/-- A function `e→e` and a function `e→(e→t)` with pointwise identified values: the constant
function to the entity, and the constant function to its haecceity. -/
theorem MclH_not_PExt : ¬ MclHF.Valid PExt := fun h => by
  have h0 := (MclHF.holds_tall _ _ _).mp ((MclHF.holds_tall _ _ _).mp ((MclHF.holds_tall _ _ _).mp
    (h (fun i => i.elim0) ()) .e) .e) (.arr .e .t)
  have h1 := (MclHF.holds_all _ _ _ _).mp ((MclHF.holds_all _ _ _ _).mp h0
    (fun _ => () : univA.El .e → univA.El .e)) (fun _ => hcyA .e () : univA.El .e → univA.El (.arr .e .t))
  have h2 := (MclHF.holds_imp _ _ _ _).mp h1 ((MclHF.holds_all _ _ _ _).mpr fun _ =>
    (MclHF.holds_eqv _ _ _ _ _ _).mpr ((mkA_V _).mpr (groot_hcy hcyA_inj .e ()).symm))
  have h3 : rootA (.arr .e .e) (fun _ => ()) = rootA (.arr .e (.arr .e .t)) (fun _ => hcyA .e ()) :=
    (mkA_V _).mp ((MclHF.holds_eqv _ _ _ _ _ _).mp h2)
  have h4 : (Code.arr .e .e : Code Empty) = .arr .e (.arr .e .t) := congrArg Sigma.fst h3
  exact nomatch h4

/-- At type `t`, `⊤ ≡ some false` is `some true`, while `∀G (G ⊤ → G (some false))` is
`some false`. -/
theorem MclH_not_IdId : ¬ MclHF.Valid IdId := fun h => by
  have h0 := (MclHF.holds_all _ _ _ _).mp ((MclHF.holds_all _ _ _ _).mp
    ((MclHF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) none) (some false)
  have e := eq_of_heq (Sigma.mk.inj ((mkA_V _).mp ((MclHF.holds_eqv_t _ _ _ _).mp h0))).2
  have hE : MclHF.eqv .t .t none (some false) = some true :=
    mkA_neg (fun h => nomatch (eq_of_heq (Sigma.mk.inj h).2 : (none : Option Bool) = some false))
  have hA : MclHF.all (.arr .t .t) (fun G => MclHF.imp (G none) (G (some false))) = some false :=
    qA_neg (fun h => nomatch ((mkA_V _).mp (h (fun p => p)) rfl : (some false : Option Bool) = none))
  exact Bool.noConfusion (Option.some.inj (hE.symm.trans ((MclHF.eval_eqv _ _ _ _ _ _).symm.trans
    (e.trans ((MclHF.eval_all _ _ _ _).trans hA)))))

end Al
end PIF
