import PIExplore

/-!
# Haecceity towers

Models in which every item is identified with its haecceity. Each item `x` of type `α` gets a
*root*: the haecceity `λy.(y ≡ x)` of `x` has the root of `x`, and the remaining items have roots
given by a map `ov`. Two items are identified just in case they have the same root, and `≈` is
identity of types. So Haecceitism holds by construction, and `ov` can be chosen to add other
identifications.
-/
set_option autoImplicit false

namespace PIF

section Tower
attribute [local instance] Classical.propDecidable
variable {U : Univ} (ov : (c : Code U.Base) → U.El c → (Σ c, U.El c))

/-- The root of an item. -/
noncomputable def hr : (c : Code U.Base) → U.El c → (Σ c, U.El c)
  | .arr a .t, G =>
    if h : ∃ x, G = (fun y => hr a y = hr a x) then hr a (Classical.choose h) else ov (.arr a .t) G
  | c, x => ov c x

/-- The haecceity of `x`, as an item of `α→t`. -/
def haeF (a : Code U.Base) (x : U.El a) : U.El (.arr a .t) := fun y => hr ov a y = hr ov a x

theorem hr_arr_t (a : Code U.Base) (G : U.El (.arr a .t)) :
    hr ov (.arr a .t) G =
      if h : ∃ x, G = (fun y => hr ov a y = hr ov a x) then hr ov a (Classical.choose h) else ov (.arr a .t) G := by
  rw [hr]

/-- The haecceity of an item has the same root as the item. -/
theorem hr_hae (a : Code U.Base) (x : U.El a) : hr ov (.arr a .t) (haeF ov a x) = hr ov a x := by
  rw [hr_arr_t]
  split
  · next h =>
    have hc := Classical.choose_spec h
    exact (congrFun hc (Classical.choose h)).mpr rfl
  · next h => exact absurd ⟨x, rfl⟩ h

noncomputable def towerIdent : IdentData where
  U := U
  rel := fun p q => hr ov p.1 p.2 = hr ov q.1 q.2
  refl := fun _ => rfl
  symm := fun h => h.symm
  trans := fun h1 h2 => h1.trans h2

theorem tower_Hae : (towerIdent ov).frame.Valid Hae :=
  ((towerIdent ov).frame.valid_iff_tr _).mpr <| (towerIdent ov).frame.tr_Hae.mpr fun a x => (hr_hae ov a x).symm

theorem tower_Twin : (towerIdent ov).frame.Valid Twin :=
  ((towerIdent ov).frame.valid_iff_tr _).mpr <| (towerIdent ov).frame.tr_Twin.mpr fun a x =>
    ⟨.arr a .t, fun h => Code.arr_ne_left a .t h.symm, haeF ov a x, (hr_hae ov a x).symm⟩

/-- The size of a code. -/
def csz {B : Type} : Code B → Nat
  | .arr a c => csz a + csz c + 1
  | _ => 1

theorem csz_pos {B : Type} : ∀ c : Code B, 1 ≤ csz c
  | .arr _ _ => Nat.succ_le_succ (Nat.zero_le _)
  | .e => Nat.le_refl _
  | .t => Nat.le_refl _
  | .base _ => Nat.le_refl _

variable {ov}

theorem hr_le (hov : ∀ c x, csz (ov c x).1 ≤ csz c) : ∀ c x, csz (hr ov c x).1 ≤ csz c
  | .arr a .t, G => by
    rw [hr_arr_t]
    split
    · exact Nat.le_trans (hr_le hov a _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _))
    · exact hov _ _
  | .e, x => hov _ x
  | .t, x => hov _ x
  | .base _, x => hov _ x
  | .arr _ .e, x => hov _ x
  | .arr _ (.base _), x => hov _ x
  | .arr _ (.arr _ _), x => hov _ x

/-- Within a type, distinct items have distinct roots, if `ov` is injective, does not raise sizes,
and leaves the items of types `α→t` alone. -/
theorem hr_inj (hov : ∀ c x, csz (ov c x).1 ≤ csz c) (hinj : ∀ c x y, ov c x = ov c y → x = y)
    (hid : ∀ a (G : U.El (.arr a .t)), ov (.arr a .t) G = ⟨.arr a .t, G⟩) :
    ∀ c (x y : U.El c), hr ov c x = hr ov c y → x = y
  | .arr a .t, G1, G2, h => by
    rw [hr_arr_t, hr_arr_t] at h
    split at h <;> split at h
    · next h1 h2 =>
      rw [Classical.choose_spec h1, Classical.choose_spec h2]
      funext y
      rw [h]
    · next h1 _ =>
      rw [hid] at h
      have := congrArg (fun p => csz p.1) h
      simp only at this
      have h3 := hr_le hov a (Classical.choose h1)
      rw [this] at h3
      exact absurd h3 (Nat.not_le.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Nat.succ_le_succ (Nat.le_add_right _ _))))
    · next _ h2 =>
      rw [hid] at h
      have := congrArg (fun p => csz p.1) h
      simp only at this
      have h3 := hr_le hov a (Classical.choose h2)
      rw [← this] at h3
      exact absurd h3 (Nat.not_le.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Nat.succ_le_succ (Nat.le_add_right _ _))))
    · rw [hid, hid] at h
      exact eq_of_heq (Sigma.mk.inj h).2
  | .e, x, y, h => hinj _ x y h
  | .t, x, y, h => hinj _ x y h
  | .base _, x, y, h => hinj _ x y h
  | .arr _ .e, x, y, h => hinj _ x y h
  | .arr _ (.base _), x, y, h => hinj _ x y h
  | .arr _ (.arr _ _), x, y, h => hinj _ x y h

theorem tower_LLEqv (hov : ∀ c x, csz (ov c x).1 ≤ csz c) (hinj : ∀ c x y, ov c x = ov c y → x = y)
    (hid : ∀ a (G : U.El (.arr a .t)), ov (.arr a .t) G = ⟨.arr a .t, G⟩) : (towerIdent ov).frame.Valid LLEqv :=
  (towerIdent ov).LLEqv_valid (hr_inj hov hinj hid)

end Tower


/-! ## `𝔐_hae,p`: a model of PI with Haecceitism, in which PCong and Ext≈ fail

`E = 1`. There is a further base type `D` with three items, and a duplicate `d` of `e`. The item of
`d` has the same root as the entity; and the function `g₀ : e→D` with value `2` has the same root as
the entity too. Everything else is as in the haecceity towers. -/

section Mhp
attribute [local instance] Classical.propDecidable

inductive HB : Type where
  | D | de
  deriving DecidableEq

def HBEl : HB → Type
  | .D => Fin 3
  | .de => Unit

def univHP : Univ :=
  { E := Unit, Base := HB, B := HBEl, neE := ⟨()⟩,
    neB := fun b => match b with | .D => ⟨(show Fin 3 from 0)⟩ | .de => ⟨(show Unit from ())⟩ }

def g0D : univHP.El (.arr .e (.base .D)) := fun _ => (show Fin 3 from 2)

abbrev CHP := Code univHP.Base

noncomputable def ovHP (c : CHP) (x : univHP.El c) : Σ c : CHP, univHP.El c :=
  if c = .base HB.de then ⟨.e, ()⟩
  else if h : c = .arr .e (.base HB.D) then (if h ▸ x = g0D then ⟨.e, ()⟩ else ⟨c, x⟩)
  else ⟨c, x⟩

theorem ovHP_le (c : CHP) (x : univHP.El c) : csz (ovHP c x).1 ≤ csz c := by
  unfold ovHP
  split
  · exact csz_pos c
  · split
    · split
      · exact csz_pos c
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem ovHP_inj (c : CHP) (x y : univHP.El c) (h : ovHP c x = ovHP c y) : x = y := by
  unfold ovHP at h
  split at h
  · next hc => subst hc; rfl
  · split at h
    · next h1 hc =>
      subst hc
      split at h <;> split at h
      · next hx hy => exact hx.trans hy.symm
      · cases congrArg Sigma.fst h
      · cases congrArg Sigma.fst h
      · exact eq_of_heq (Sigma.mk.inj h).2
    · exact eq_of_heq (Sigma.mk.inj h).2

theorem ovHP_id (a : CHP) (G : univHP.El (.arr a .t)) : ovHP (.arr a .t) G = ⟨.arr a .t, G⟩ := by
  unfold ovHP
  split
  · next h => cases h
  · split
    · next h => injection h with _ h2; cases h2
    · rfl

noncomputable def MhpD : IdentData := towerIdent (U := univHP) ovHP
noncomputable abbrev Mhp : Frame := MhpD.frame
theorem Mhp_model : Mhp.IsModelPIm := MhpD.model
theorem Mhp_LLEqv : Mhp.Valid LLEqv := tower_LLEqv (U := univHP) ovHP_le ovHP_inj ovHP_id
theorem Mhp_Hae : Mhp.Valid Hae := tower_Hae (U := univHP) ovHP
theorem Mhp_Twin : Mhp.Valid Twin := tower_Twin (U := univHP) ovHP
theorem Mhp_Inj : Mhp.Valid Inj := MhpD.Inj_valid

theorem hrHP_e (x : univHP.El .e) : hr ovHP .e x = ⟨.e, ()⟩ := by
  show ovHP .e x = _
  unfold ovHP
  split
  · next h => cases h
  · split
    · next h => cases h
    · rfl

theorem hrHP_g0 : hr ovHP (.arr .e (.base HB.D)) g0D = ⟨.e, ()⟩ := by
  show ovHP _ g0D = _
  unfold ovHP
  split
  · next h => cases h
  · split
    · split
      · rfl
      · next h => exact absurd rfl h
    · next h => exact absurd rfl h

theorem hrHP_plain (c : CHP) (x : univHP.El c) (h1 : c ≠ .base HB.de) (h2 : c ≠ .arr .e (.base HB.D))
    (h3 : ∀ a, c ≠ .arr a .t) : hr ovHP c x = ⟨c, x⟩ := by
  have : hr ovHP c x = ovHP c x := by
    cases c with
    | arr a c' => cases c' with
      | t => exact absurd rfl (h3 a)
      | _ => rfl
    | _ => rfl
  rw [this]
  unfold ovHP
  split <;> (try split) <;> first | rfl | contradiction

theorem Mhp_not_PCong : ¬ Mhp.Valid PCong := fun h => by
  have := Mhp.tr_PCong.mp ((Mhp.valid_iff_tr _).mp h) .e .t (.base HB.D) (haeF ovHP .e ()) g0D ()
    ((hr_hae ovHP .e ()).trans ((hrHP_e ()).trans hrHP_g0.symm))
  have h' : hr ovHP .t _ = hr ovHP (.base HB.D) _ := this
  rw [hrHP_plain .t _ (fun h => by cases h) (fun h => by cases h) (fun _ h => by cases h),
    hrHP_plain (.base HB.D) _ (fun h => by cases h) (fun h => by cases h) (fun _ h => by cases h)] at h'
  cases congrArg Sigma.fst h'

theorem Mhp_not_ExtT : ¬ Mhp.Valid ExtT := fun h => by
  have hde : ∀ y : univHP.El (.base HB.de), hr ovHP (.base HB.de) y = ⟨.e, ()⟩ := fun y => by
    show ovHP _ y = _
    unfold ovHP
    split
    · rfl
    · next h => exact absurd rfl h
  have := Mhp.tr_ExtT.mp ((Mhp.valid_iff_tr _).mp h) .e (.base HB.de)
    ⟨fun x => ⟨(), (hrHP_e x).trans (hde ()).symm⟩, fun y => ⟨(), (hrHP_e ()).trans (hde y).symm⟩⟩
  cases this

theorem Mhp_eqv_t (p q : Prop) : Mhp.eqv .t .t p q ↔ p = q :=
  ⟨hr_inj (U := univHP) ovHP_le ovHP_inj ovHP_id .t p q, fun h => h ▸ rfl⟩
theorem Mhp_not_IntT : ¬ Mhp.Valid IntT := fun h => Mhp_not_ExtT ((Mhp.IntT_iff_ExtT Mhp_eqv_t).mp h)

end Mhp

/-! ## `𝔐_hae⁻`: a model of PI⁻ only, with Haecceitism, in which PCong and WCong fail

`E = 1`, and every property of the entity has the same root as the entity. -/

section Mhm
attribute [local instance] Classical.propDecidable

noncomputable def ovHM (c : Code unitUniv.Base) (x : unitUniv.El c) : Σ c : Code unitUniv.Base, unitUniv.El c :=
  if c = .arr .e .t then ⟨.e, ()⟩ else ⟨c, x⟩

noncomputable def MhmD : IdentData := towerIdent (U := unitUniv) ovHM
noncomputable abbrev Mhm : Frame := MhmD.frame
theorem Mhm_model : Mhm.IsModelPIm := MhmD.model
theorem Mhm_Hae : Mhm.Valid Hae := tower_Hae (U := unitUniv) ovHM
theorem Mhm_Twin : Mhm.Valid Twin := tower_Twin (U := unitUniv) ovHM
theorem Mhm_Inj : Mhm.Valid Inj := MhmD.Inj_valid

theorem hrHM_et (G : unitUniv.El (.arr .e .t)) : hr ovHM (.arr .e .t) G = ⟨.e, ()⟩ := by
  rw [hr_arr_t]
  split
  · show ovHM .e _ = _
    unfold ovHM
    split
    · next h => cases h
    · rfl
  · unfold ovHM
    split
    · rfl
    · next h => exact absurd rfl h

theorem hrHM_t (p : Prop) : hr ovHM .t p = ⟨.t, p⟩ := by
  show ovHM .t p = _
  unfold ovHM
  split
  · next h => cases h
  · rfl

theorem Mhm_not_LLEqv : ¬ Mhm.Valid LLEqv := fun h =>
  Mhm.tr_LLEqv.mp ((Mhm.valid_iff_tr _).mp h) (.arr .e .t) (fun _ => False) (fun _ => True)
    ((hrHM_et _).trans (hrHM_et _).symm) (fun g => ¬ g ()) id trivial
theorem Mhm_not_PCong : ¬ Mhm.Valid PCong := fun h => by
  have := Mhm.tr_PCong.mp ((Mhm.valid_iff_tr _).mp h) .e .t .t (fun _ => False) (fun _ => True) ()
    ((hrHM_et _).trans (hrHM_et _).symm)
  have h' : hr ovHM .t False = hr ovHM .t True := this
  rw [hrHM_t, hrHM_t] at h'
  exact cast (eq_of_heq (Sigma.mk.inj h').2).symm trivial
theorem Mhm_not_WCong : ¬ Mhm.Valid WCong := fun h => by
  have := Mhm.tr_WCong.mp ((Mhm.valid_iff_tr _).mp h) .e .e .t .t (fun _ => False) (fun _ => True) () ()
    ⟨⟨rfl, rfl⟩, ⟨(hrHM_et _).trans (hrHM_et _).symm, rfl⟩⟩
  have h' : hr ovHM .t False = hr ovHM .t True := this
  rw [hrHM_t, hrHM_t] at h'
  exact cast (eq_of_heq (Sigma.mk.inj h').2).symm trivial

end Mhm

end PIF
