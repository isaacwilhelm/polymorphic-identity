import PIBF
set_option autoImplicit false

/-!
# `𝔐_co`: co-haecceities

A model of PIᶜ in which Twin and Ext≈ hold but Haecceitism fails. `E = 1` and there are no further
base types. The *co-haecceity* of an item `z` of `α` is the property `λy.(y ≠ z)` of `α→t`. The root
of an item is got by stripping off co-haecceities (the generic root construction `groot` of
`PIHaeQs`), and items are identified just in case they have the same root; `≈` is identity of types.

So each item is identified with its co-haecceity, of a different type, and Twin holds. But the
haecceity `λy.(y ≡ x)` of the entity is `λy.⊤`, which is not a co-haecceity, so it is its own root,
and Haecceitism fails.
-/

namespace PIF

section Mco
open Classical

/-- The co-haecceity of `z`: the property of being distinct from `z`. -/
def hcyCo (a : Code unitUniv.Base) (z : unitUniv.El a) : unitUniv.El (.arr a .t) := fun y => y ≠ z

theorem hcyCo_inj (a : Code unitUniv.Base) (z z' : unitUniv.El a) (h : hcyCo a z = hcyCo a z') : z = z' :=
  Classical.byContradiction fun hne => (cast (congrFun h z).symm hne : z ≠ z) rfl

local notation "rootCo" => groot unitUniv.El hcyCo

noncomputable def McoD : IdentData where
  U := unitUniv
  rel := fun p q => rootCo p.1 p.2 = rootCo q.1 q.2
  refl := fun _ => rfl
  symm := fun h => h.symm
  trans := fun h1 h2 => h1.trans h2

noncomputable abbrev Mco : Frame := McoD.frame

theorem rootCo_hcy (a : Code unitUniv.Base) (z : unitUniv.El a) : rootCo (.arr a .t) (hcyCo a z) = rootCo a z :=
  groot_hcy hcyCo_inj a z

/-- The property `λy.⊤` of `α→t` is not a co-haecceity, and so is its own root. -/
theorem rootCo_top (a : Code unitUniv.Base) : rootCo (.arr a .t) (fun _ => True) = ⟨.arr a .t, fun _ => True⟩ :=
  groot_not unitUniv.El hcyCo a _ fun ⟨z, hz⟩ => (cast (congrFun hz z) trivial : z ≠ z) rfl

theorem Mco_model : Mco.IsModelPIm := McoD.model

theorem Mco_LLEqv : Mco.Valid LLEqv := McoD.LLEqv_valid fun c x y h => groot_inj hcyCo_inj c x y h

theorem Mco_Class : ∀ χ, ClassSch χ → Mco.Valid χ := Mco.Class_valid Mco_model Mco_LLEqv

theorem Mco_Inj : Mco.Valid Inj := McoD.Inj_valid

/-- Each item is identified with its co-haecceity, of a different type. -/
theorem Mco_Twin : Mco.Valid Twin :=
  (Mco.valid_iff_tr _).mpr <| Mco.tr_Twin.mpr fun a x =>
    ⟨.arr a .t, fun h => Code.arr_ne_left a .t h.symm, hcyCo a x, (rootCo_hcy a x).symm⟩

/-- The haecceity of the entity is `λy.⊤`, which is its own root, of type `e→t`. -/
theorem Mco_not_Hae : ¬ Mco.Valid Hae := fun h => by
  have h1 : rootCo .e () = rootCo (.arr .e .t) (fun y => Mco.eqv .e .e y ()) :=
    Mco.tr_Hae.mp ((Mco.valid_iff_tr _).mp h) .e ()
  have e : (fun y : unitUniv.El .e => Mco.eqv .e .e y ()) = fun _ => True :=
    funext fun _ => propext ⟨fun _ => trivial, fun _ => rfl⟩
  have h2 : rootCo .e () = rootCo (.arr .e .t) (fun _ => True) := h1.trans (congrArg _ e)
  rw [rootCo_top] at h2
  cases congrArg Sigma.fst h2

/-- The entity is identified with a property: its co-haecceity. -/
theorem Mco_not_Slogan : ¬ Mco.Valid Slogan := fun h =>
  Mco.tr_Slogan.mp ((Mco.valid_iff_tr _).mp h) () .e (hcyCo .e ()) (rootCo_hcy .e ()).symm

theorem Mco_not_Disjoint : ¬ Mco.Valid Disjoint := fun h =>
  Mco.tr_Disjoint.mp ((Mco.valid_iff_tr _).mp h) .e (.arr .e .t) (fun h => Code.arr_ne_left .e .t h.symm)
    () (hcyCo .e ()) (rootCo_hcy .e ()).symm

theorem Mco_eqv_t (p q : Prop) : Mco.eqv .t .t p q ↔ p = q :=
  ⟨groot_inj hcyCo_inj .t p q, fun h => h ▸ rfl⟩

/-- Every type has an item which is its own root. -/
theorem Mco_own_item : ∀ a : Code unitUniv.Base, ∃ x : unitUniv.El a, rootCo a x = ⟨a, x⟩
  | .e => ⟨(), rfl⟩
  | .t => ⟨True, rfl⟩
  | .base b => Empty.elim b
  | .arr _ .e => ⟨fun _ => (), rfl⟩
  | .arr _ (.base b) => Empty.elim b
  | .arr a (.arr c d) => ⟨Classical.choice (Univ.El_nonempty (U := unitUniv) (.arr a (.arr c d))), rfl⟩
  | .arr a .t => ⟨fun _ => True, rootCo_top a⟩

/-- If every item of `a` has the root of an item of `b`, then `a` is no bigger than `b`. -/
theorem Mco_sub_le (a b : Code unitUniv.Base) (h : ∀ x : unitUniv.El a, ∃ y : unitUniv.El b, rootCo a x = rootCo b y) :
    csz a ≤ csz b ∧ (csz a = csz b → a = b) := by
  obtain ⟨x, hx⟩ := Mco_own_item a
  obtain ⟨y, hy⟩ := h x
  rw [hx] at hy
  have l := groot_le unitUniv.El hcyCo b y
  rw [← hy] at l
  refine ⟨l, fun e => ?_⟩
  rcases groot_lt unitUniv.El hcyCo b y with e2 | e2
  · rw [e2] at hy; exact congrArg Sigma.fst hy
  · rw [← hy] at e2; change csz a < csz b at e2; omega

theorem Mco_ExtT : Mco.Valid ExtT :=
  (Mco.valid_iff_tr _).mpr <| Mco.tr_ExtT.mpr fun a b ⟨h1, h2⟩ => by
    have l1 := Mco_sub_le a b h1
    have l2 := Mco_sub_le b a fun y => let ⟨x, hx⟩ := h2 y; ⟨x, hx.symm⟩
    exact l1.2 (Nat.le_antisymm l1.1 l2.1)

theorem Mco_IntT : Mco.Valid IntT := (Mco.IntT_iff_ExtT Mco_eqv_t).mpr Mco_ExtT

theorem Mco_Truth : Mco.Valid Truth :=
  (Mco.valid_iff_tr _).mpr <| Mco.tr_Truth.mpr fun p q h hp => (Mco_eqv_t p q).mp h ▸ hp

theorem Mco_TopBot : Mco.Valid TopBot :=
  (Mco.valid_iff_tr _).mpr <| Mco.tr_TopBot.mpr fun h => by
    have e := (Mco_eqv_t _ _).mp h
    exact (cast e (fun hall : ∀ p : Prop, p => hall False)) False

/-- `λy.⊤` of `α→t` is identified with no item of `α`: its root has a larger type. -/
theorem Mco_Cantor : Mco.Valid Cantor :=
  (Mco.valid_iff_tr _).mpr <| Mco.tr_Cantor.mpr fun (a : Code unitUniv.Base) => ⟨fun _ => True, fun y h => by
    have h' : rootCo (.arr a .t) (fun _ => True) = rootCo a y := h
    rw [rootCo_top] at h'
    have l := groot_le unitUniv.El hcyCo a y
    rw [← h'] at l
    change csz a + 1 + 1 ≤ csz a at l
    omega⟩

theorem Mco_Recovery : Mco.Valid Recovery :=
  (Mco.valid_iff_tr _).mpr <| Mco.tr_Recovery.mpr fun _ _ _ _ ⟨h, _⟩ => by
    injection h with _ h2

theorem Mco_PropExt : Mco.Valid PropExt := Mco.PropExt_valid Mco_model
theorem Mco_Collapse : Mco.Valid Collapse := Mco.Collapse_valid Mco_model
theorem Mco_Choice : Mco.Valid Choice := Mco.Choice_valid

/-- Within a type, identified items are identical; so WCong holds. -/
theorem Mco_WCong : Mco.Valid WCong :=
  (Mco.valid_iff_tr _).mpr <| Mco.tr_WCong.mpr fun a b c d f g x y ⟨⟨hab, hcd⟩, hf, hx⟩ => by
    change a = b at hab
    change c = d at hcd
    subst hab
    subst hcd
    have e1 : f = g := groot_inj hcyCo_inj (.arr a c) f g hf
    have e2 : x = y := groot_inj hcyCo_inj a x y hx
    subst e1
    subst e2
    exact McoD.refl _

/-- Cong fails: `λp.⊥` of `t→t` is identified with its co-haecceity, and `⊤` with its
co-haecceity; but `(λp.⊥) ⊤` is `⊥`, while the co-haecceity of `λp.⊥` is true of the
co-haecceity of `⊤`. -/
theorem Mco_not_Cong : ¬ Mco.Valid Cong := fun h => by
  have h1 := Mco.tr_Cong.mp ((Mco.valid_iff_tr _).mp h) .t (.arr .t .t) .t .t (fun _ => False)
    (hcyCo (.arr .t .t) (fun _ => False)) True (hcyCo .t True)
    ⟨(rootCo_hcy _ _).symm, (rootCo_hcy _ _).symm⟩
  have e := groot_inj hcyCo_inj .t _ _ h1
  have hne : hcyCo .t True ≠ (fun _ => False) := fun heq =>
    cast (congrFun heq False) (fun h : False = True => cast h.symm trivial)
  exact cast e.symm hne

/-- PExt fails: `λx.⊤` of `e→t` and `λx.(co-haecceity of ⊤)` of `e→(t→t)` take identified values,
but are their own roots, of different types. -/
theorem Mco_not_PExt : ¬ Mco.Valid PExt := fun h => by
  have h1 := Mco.tr_PExt.mp ((Mco.valid_iff_tr _).mp h) .e .t (.arr .t .t) (fun _ => True)
    (fun _ => hcyCo .t True) (fun _ => (rootCo_hcy .t True).symm)
  have h2 : rootCo (.arr .e .t) (fun _ => True) = rootCo (.arr .e (.arr .t .t)) (fun _ => hcyCo .t True) := h1
  have h3 : rootCo (.arr .e (.arr .t .t)) (fun _ => hcyCo .t True) = ⟨.arr .e (.arr .t .t), fun _ => hcyCo .t True⟩ :=
    rfl
  rw [rootCo_top, h3] at h2
  cases congrArg Sigma.fst h2

/-! ### PCong

The items with a given root `r`, of type `ρ`, are `r`, its co-haecceity, the co-haecceity of that, and
so on, of types `ρ`, `ρ→t`, `(ρ→t)→t`, …. So identified functions with a common domain have the
same type, and so are identical. -/

/-- `r` followed by `n` arrows into `t`. -/
def coTow (r : Code unitUniv.Base) : Nat → Code unitUniv.Base
  | 0 => r
  | n + 1 => .arr (coTow r n) .t

theorem csz_coTow (r : Code unitUniv.Base) : ∀ n, csz (coTow r n) = csz r + 2 * n
  | 0 => rfl
  | n + 1 => by
    show csz (coTow r n) + 1 + 1 = csz r + 2 * (n + 1)
    rw [csz_coTow r n]
    omega

/-- The type of an item is its root's type followed by some arrows into `t`. -/
theorem rootCo_tow : ∀ (a : Code unitUniv.Base) (x : unitUniv.El a), ∃ n, a = coTow (rootCo a x).1 n
  | .e, _ => ⟨0, rfl⟩
  | .t, _ => ⟨0, rfl⟩
  | .base b, _ => Empty.elim b
  | .arr _ .e, _ => ⟨0, rfl⟩
  | .arr _ (.base b), _ => Empty.elim b
  | .arr _ (.arr _ _), _ => ⟨0, rfl⟩
  | .arr a .t, f => by
    rw [groot_t]
    split
    · next h =>
      obtain ⟨n, hn⟩ := rootCo_tow a (Classical.choose h)
      exact ⟨n + 1, congrArg (fun c => Code.arr c .t) hn⟩
    · exact ⟨0, rfl⟩

theorem coTow_lt (r a c d : Code unitUniv.Base) (n m : Nat) (h1 : Code.arr a c = coTow r n)
    (h2 : Code.arr a d = coTow r m) (hl : n < m) : False := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have ha : a = coTow r k := by injection h2
  have e1 : csz a + csz c + 1 = csz r + 2 * n := by
    have := congrArg csz h1
    rw [csz_coTow] at this
    exact this
  have e2 : csz a = csz r + 2 * k := by rw [ha, csz_coTow]
  omega

theorem coTow_arr (r a c d : Code unitUniv.Base) (n m : Nat) (h1 : Code.arr a c = coTow r n)
    (h2 : Code.arr a d = coTow r m) : c = d := by
  rcases Nat.lt_trichotomy n m with hl | rfl | hl
  · exact (coTow_lt r a c d n m h1 h2 hl).elim
  · have := h1.trans h2.symm
    injection this
  · exact (coTow_lt r a d c m n h2 h1 hl).elim

theorem Mco_PCong : Mco.Valid PCong :=
  (Mco.valid_iff_tr _).mpr <| Mco.tr_PCong.mpr fun a c d f g x h => by
    have h' : rootCo (.arr a c) f = rootCo (.arr a d) g := h
    obtain ⟨n, hn⟩ := rootCo_tow (.arr a c) f
    obtain ⟨m, hm⟩ := rootCo_tow (.arr a d) g
    rw [← h'] at hm
    have hcd : c = d := coTow_arr _ a c d n m hn hm
    subst hcd
    have e : f = g := groot_inj hcyCo_inj (.arr a c) f g h'
    subst e
    exact McoD.refl _

end Mco

end PIF
