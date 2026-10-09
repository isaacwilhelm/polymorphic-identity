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


/-! ## `𝔐_hae,κ`: a model of PI with Haecceitism, in which Inj≈ and Recovery fail

`E = 1`, with one further base type `D`, whose items are propositions, like those of `t`. As in
`𝔐_κ`, `≈` identifies `α→D` with `α→t` (for every `α`, and so on up through the types), but not `D`
with `t`. Identification is by roots, as in the haecceity towers; an item that is not a haecceity is
its own root, filed under the `≈`-normal form of its type. -/

section Mhk
attribute [local instance] Classical.propDecidable

def univHK : Univ := { E := Unit, Base := Unit, B := fun _ => Prop, neE := ⟨()⟩, neB := fun _ => ⟨True⟩ }
abbrev CHK := Code univHK.Base

/-- The `≈`-normal form of a type: `D` in codomain position becomes `t`. -/
def Tn : CHK → CHK
  | .arr a (.base _) => .arr (Tn a) .t
  | .arr a c => .arr (Tn a) (Tn c)
  | c => c

theorem Tn_arr_t (a : CHK) : Tn (.arr a .t) = .arr (Tn a) .t := rfl
theorem Tn_arr_D (a : CHK) (b : Unit) : Tn (.arr a (.base b)) = .arr (Tn a) .t := rfl

theorem El_Tn : ∀ c : CHK, univHK.El (Tn c) = univHK.El c
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a (.base _) => by show (univHK.El (Tn a) → Prop) = (univHK.El a → Prop); rw [El_Tn a]
  | .arr a .e => by show (univHK.El (Tn a) → univHK.El (Tn .e)) = (univHK.El a → univHK.El .e); rw [El_Tn a]; rfl
  | .arr a .t => by show (univHK.El (Tn a) → univHK.El (Tn .t)) = (univHK.El a → univHK.El .t); rw [El_Tn a]; rfl
  | .arr a (.arr c d) => by
    show (univHK.El (Tn a) → univHK.El (Tn (.arr c d))) = (univHK.El a → univHK.El (.arr c d))
    rw [El_Tn a, El_Tn (.arr c d)]

theorem Tn_eq_t : ∀ c : CHK, Tn c = .t → c = .t
  | .t, _ => rfl
  | .e, h => by cases h
  | .base _, h => by cases h
  | .arr _ (.base _), h => by cases h
  | .arr _ .e, h => by cases h
  | .arr _ .t, h => by cases h
  | .arr _ (.arr _ _), h => by cases h

theorem Tn_eq_base : ∀ (c : CHK) (b : Unit), Tn c = .base b → c = .base b
  | .base _, _, h => h
  | .t, _, h => by cases h
  | .e, _, h => by cases h
  | .arr _ (.base _), _, h => by cases h
  | .arr _ .e, _, h => by cases h
  | .arr _ .t, _, h => by cases h
  | .arr _ (.arr _ _), _, h => by cases h

/-- Types whose items are tested for being haecceities: `α→t` and `α→D`. -/
def HaeTy : CHK → Prop
  | .arr _ .t => True
  | .arr _ (.base _) => True
  | _ => False

theorem Tn_arr (a c : CHK) (hc : ∀ b, c ≠ .base b) : Tn (.arr a c) = .arr (Tn a) (Tn c) := by
  cases c with
  | base b => exact absurd rfl (hc b)
  | _ => rfl

theorem Tn_hT (a a' c c' : CHK) (h1 : Tn a = Tn a') (h2 : Tn c = Tn c') : Tn (.arr a c) = Tn (.arr a' c') := by
  by_cases hc : ∃ b, c = .base b
  · obtain ⟨b, rfl⟩ := hc
    have hc' : c' = .base b := Tn_eq_base c' b h2.symm
    subst hc'
    show Code.arr (Tn a) .t = Code.arr (Tn a') .t
    rw [h1]
  · have hc' : ¬ ∃ b, c' = .base b := fun ⟨b, hb⟩ => hc ⟨b, Tn_eq_base c b (by rw [h2, hb]; rfl)⟩
    rw [Tn_arr a c (fun b h => hc ⟨b, h⟩), Tn_arr a' c' (fun b h => hc' ⟨b, h⟩), h1, h2]

/-- The normal form of a type tells whether it is tested for haecceities, and gives its domain. -/
theorem Tn_hae_iff : ∀ c : CHK, HaeTy c ↔ ∃ x, Tn c = .arr x .t
  | .arr a .t => ⟨fun _ => ⟨Tn a, rfl⟩, fun _ => trivial⟩
  | .arr a (.base _) => ⟨fun _ => ⟨Tn a, rfl⟩, fun _ => trivial⟩
  | .arr a .e => ⟨fun h => h.elim, fun ⟨_, h⟩ => by injection h with _ h2; cases h2⟩
  | .arr a (.arr c d) => ⟨fun h => h.elim, fun ⟨_, h⟩ => by
      injection h with _ h2; exact absurd (Tn_eq_t _ h2) (fun h => by cases h)⟩
  | .e => ⟨fun h => h.elim, fun ⟨_, h⟩ => by cases h⟩
  | .t => ⟨fun h => h.elim, fun ⟨_, h⟩ => by cases h⟩
  | .base _ => ⟨fun h => h.elim, fun ⟨_, h⟩ => by cases h⟩

abbrev RK := Σ c : CHK, univHK.El c

/-- An item filed under the normal form of its type. -/
def ownR (c : CHK) (x : univHK.El c) : RK := ⟨Tn c, cast (El_Tn c).symm x⟩

theorem ownR_congr {c c' : CHK} {x : univHK.El c} {x' : univHK.El c'} (h : Tn c = Tn c') (hx : HEq x x') :
    ownR c x = ownR c' x' := by
  unfold ownR
  have hh : HEq (cast (El_Tn c).symm x) (cast (El_Tn c').symm x') := (cast_heq _ _).trans (hx.trans (cast_heq _ _).symm)
  revert hh
  generalize cast (El_Tn c).symm x = y
  generalize cast (El_Tn c').symm x' = y'
  revert y y'
  rw [h]
  intro y y' hh
  cases hh
  rfl

/-- The root of an item of `α→t` or `α→D`: the root of `x`, if it is the haecceity of `x`; else `own`. -/
noncomputable def haeRoot {A : Type} (f : A → RK) (G : A → Prop) (own : RK) : RK :=
  if h : ∃ x, G = (fun y => f y = f x) then f (Classical.choose h) else own

theorem haeRoot_congr {A A' : Type} (e : A = A') (f : A → RK) (f' : A' → RK) (hf : ∀ y, f y = f' (cast e y))
    (G : A → Prop) (G' : A' → Prop) (hG : HEq G G') {own own' : RK} (ho : own = own') :
    haeRoot f G own = haeRoot f' G' own' := by
  subst e
  have : f = f' := funext hf
  subst this
  cases hG
  rw [ho]

noncomputable def hk : (c : CHK) → univHK.El c → RK
  | .arr a .t, G => haeRoot (hk a) G (ownR (.arr a .t) G)
  | .arr a (.base b), G => haeRoot (hk a) G (ownR (.arr a (.base b)) G)
  | c, x => ownR c x

theorem hk_own (c : CHK) (hc : ¬ HaeTy c) (x : univHK.El c) : hk c x = ownR c x := by
  cases c with
  | arr a c' => cases c' with
    | t => exact absurd trivial hc
    | base b => exact absurd trivial hc
    | _ => rfl
  | _ => rfl

theorem hae_shape : ∀ a : CHK, HaeTy a → ∃ b c, a = .arr b c ∧ (c = .t ∨ ∃ x, c = .base x)
  | .arr b .t, _ => ⟨b, .t, rfl, Or.inl rfl⟩
  | .arr b (.base x), _ => ⟨b, .base x, rfl, Or.inr ⟨x, rfl⟩⟩
  | .arr _ .e, h => h.elim
  | .arr _ (.arr _ _), h => h.elim
  | .e, h => h.elim
  | .t, h => h.elim
  | .base _, h => h.elim

theorem own_case {a a' : CHK} (ha : ¬ HaeTy a) (u : univHK.El a) (u' : univHK.El a') (h : Tn a = Tn a')
    (hu : HEq u u') : hk a u = hk a' u' := by
  have ha' : ¬ HaeTy a' := fun ha' => ha ((Tn_hae_iff a).mpr (h ▸ (Tn_hae_iff a').mp ha'))
  rw [hk_own a ha, hk_own a' ha']
  exact ownR_congr h hu

/-- Items related by the identity between `≈`-identical types have the same root. -/
theorem hk_congr (a : CHK) : ∀ (a' : CHK) (u : univHK.El a) (u' : univHK.El a'), Tn a = Tn a' → HEq u u' →
    hk a u = hk a' u' := by
  induction a with
  | arr b c ihb _ =>
    intro a' u u' h hu
    by_cases hc : c = .t ∨ ∃ x, c = .base x
    · have hTa : ∃ x, Tn (.arr b c) = .arr x .t := (Tn_hae_iff _).mp (by rcases hc with rfl | ⟨x, rfl⟩ <;> trivial)
      have ha' : HaeTy a' := (Tn_hae_iff a').mpr (h ▸ hTa)
      obtain ⟨b', c', ha'eq, hc'⟩ := hae_shape a' ha'
      subst ha'eq
      rcases hc with hct | ⟨x, hcx⟩ <;> rcases hc' with hct' | ⟨x', hcx'⟩ <;>
      · (try subst hct) <;> (try subst hcx) <;> (try subst hct') <;> (try subst hcx')
        have h0 := h
        injection h0 with hb _
        have e : univHK.El b = univHK.El b' := (El_Tn b).symm.trans ((congrArg univHK.El hb).trans (El_Tn b'))
        exact haeRoot_congr e (hk b) (hk b') (fun y => ihb b' y (cast e y) hb (cast_heq _ _).symm) u u' hu
          (ownR_congr h hu)
    · have ha : ¬ HaeTy (.arr b c) := fun ha => by
        obtain ⟨_, _, he, hc2⟩ := hae_shape _ ha
        injection he with _ h2
        subst h2
        exact hc hc2
      exact own_case ha u u' h hu
  | e => intro a' u u' h hu; exact own_case (a := .e) (fun h => h) u u' h hu
  | t => intro a' u u' h hu; exact own_case (a := .t) (fun h => h) u u' h hu
  | base x => intro a' u u' h hu; exact own_case (a := .base x) (fun h => h) u u' h hu

theorem hk_hae (a : CHK) (x : univHK.El a) : hk (.arr a .t) (fun y => hk a y = hk a x) = hk a x := by
  show haeRoot (hk a) (fun y => hk a y = hk a x) _ = _
  unfold haeRoot
  split
  · next h =>
    have hc := Classical.choose_spec h
    exact (congrFun hc (Classical.choose h)).mpr rfl
  · next h => exact absurd ⟨x, rfl⟩ h

theorem csz_Tn : ∀ c : CHK, csz (Tn c) = csz c
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a (.base _) => by show csz (Tn a) + 1 + 1 = csz a + 1 + 1; rw [csz_Tn a]
  | .arr a .e => by show csz (Tn a) + 1 + 1 = csz a + 1 + 1; rw [csz_Tn a]
  | .arr a .t => by show csz (Tn a) + 1 + 1 = csz a + 1 + 1; rw [csz_Tn a]
  | .arr a (.arr c d) => by
    show csz (Tn a) + csz (Tn (.arr c d)) + 1 = csz a + csz (.arr c d) + 1
    rw [csz_Tn a, csz_Tn (.arr c d)]

theorem hk_le : ∀ (c : CHK) (x : univHK.El c), csz (hk c x).1 ≤ csz c := by
  intro c
  induction c with
  | arr b c ihb _ =>
    intro x
    by_cases hc : c = .t ∨ ∃ x, c = .base x
    · rcases hc with hct | ⟨y, hcy⟩ <;> (try subst hct) <;> (try subst hcy) <;>
      · show csz (haeRoot (hk b) x _).1 ≤ _
        unfold haeRoot
        split
        · exact Nat.le_trans (ihb _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _))
        · exact Nat.le_of_eq (csz_Tn _)
    · have ha : ¬ HaeTy (.arr b c) := fun ha => by
        obtain ⟨_, _, he, hc2⟩ := hae_shape _ ha
        injection he with _ h2
        subst h2
        exact hc hc2
      rw [hk_own _ ha]; exact Nat.le_of_eq (csz_Tn _)
  | e => intro x; exact Nat.le_refl _
  | t => intro x; exact Nat.le_refl _
  | base _ => intro x; exact Nat.le_refl _

theorem ownR_inj {c : CHK} {x y : univHK.El c} (h : ownR c x = ownR c y) : x = y := by
  have := (Sigma.mk.inj h).2
  exact eq_of_heq ((cast_heq _ _).symm.trans (this.trans (cast_heq _ _)))

theorem hk_inj (c : CHK) (x y : univHK.El c) (h : hk c x = hk c y) : x = y := by
  by_cases ha : HaeTy c
  · obtain ⟨b, c', hce, hc⟩ := hae_shape c ha
    subst hce
    have big : ∀ z : univHK.El b, csz (hk b z).1 < csz (Tn (.arr b c')) := fun z => by
      rw [csz_Tn]
      exact Nat.lt_of_le_of_lt (hk_le b z) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Nat.succ_le_succ (Nat.le_add_right _ _)))
    rcases hc with hct | ⟨w, hcw⟩ <;> (try subst hct) <;> (try subst hcw) <;>
    · change haeRoot (hk b) x _ = haeRoot (hk b) y _ at h
      unfold haeRoot at h
      split at h <;> split at h
      · next h1 h2 =>
        rw [Classical.choose_spec h1, Classical.choose_spec h2]
        funext z
        rw [h]
      · next h1 _ =>
        have := congrArg (fun p => csz p.1) h
        exact absurd (this ▸ big (Classical.choose h1)) (Nat.lt_irrefl _)
      · next _ h2 =>
        have := congrArg (fun p => csz p.1) h
        exact absurd (this ▸ big (Classical.choose h2)) (Nat.lt_irrefl _)
      · exact ownR_inj h
  · rw [hk_own c ha, hk_own c ha] at h
    exact ownR_inj h

def MhkF : Frame where
  U := univHK
  eqv := fun a b x y => hk a x = hk b y
  teq := fun a b => Tn a = Tn b

theorem hkEl {a a' : CHK} (h : Tn a = Tn a') : univHK.El a = univHK.El a' :=
  (El_Tn a).symm.trans ((congrArg univHK.El h).trans (El_Tn a'))

def MhkI : Invariance MhkF where
  Adm := fun a a' R => Tn a = Tn a' ∧ ∀ x y, R x y ↔ HEq x y
  refl := fun _ => ⟨rfl, fun _ _ => ⟨fun h => h ▸ HEq.rfl, eq_of_heq⟩⟩
  arrow := by
    rintro a a' c c' R S ⟨h1, hR⟩ ⟨h2, hS⟩
    exact ⟨Tn_hT _ _ _ _ h1 h2, fun f f' => fun_heq_iff (hkEl h1) (hkEl h2) hR hS f f'⟩
  total := by
    rintro a a' R ⟨h, hR⟩ u
    exact ⟨cast (hkEl h) u, (hR _ _).mpr (cast_heq _ _).symm⟩
  onto := by
    rintro a a' R ⟨h, hR⟩ u
    exact ⟨cast (hkEl h).symm u, (hR _ _).mpr (cast_heq _ _)⟩
  teq := by
    rintro a a' b b' R S ⟨h1, -⟩ ⟨h2, -⟩
    show Tn a = Tn b ↔ Tn a' = Tn b'
    rw [h1, h2]
  eqv := by
    rintro a a' b b' R S ⟨h1, hR⟩ ⟨h2, hS⟩ u u' v v' hu hv
    show hk a u = hk b v ↔ hk a' u' = hk b' v'
    rw [hk_congr a a' u u' h1 ((hR u u').mp hu), hk_congr b b' v v' h2 ((hS v v').mp hv)]

abbrev Mhk : Frame := MhkF
theorem Mhk_model : Mhk.IsModelPIm :=
  Frame.isModelPIm_of_invariance MhkF MhkI (fun _ _ h => ⟨fun x y => HEq x y, h, fun _ _ => Iff.rfl⟩)
    ((MhkF.valid_iff_tr _).mpr (MhkF.tr_RefEqv.mpr fun _ _ => rfl))
    ((MhkF.valid_iff_tr _).mpr (MhkF.tr_SymEqv.mpr fun _ _ _ _ h => h.symm))
    ((MhkF.valid_iff_tr _).mpr (MhkF.tr_TransEqv.mpr fun _ _ _ _ _ _ ⟨h1, h2⟩ => h1.trans h2))
    ((MhkF.valid_iff_tr _).mpr (MhkF.tr_RefTeq.mpr fun _ => rfl))
theorem Mhk_LLEqv : Mhk.Valid LLEqv :=
  (Mhk.valid_iff_tr _).mpr <| Mhk.tr_LLEqv.mpr fun a x y h _ hP => hk_inj a x y h ▸ hP
theorem Mhk_Hae : Mhk.Valid Hae :=
  (Mhk.valid_iff_tr _).mpr <| Mhk.tr_Hae.mpr fun a x => (hk_hae a x).symm
theorem Mhk_Twin : Mhk.Valid Twin :=
  (Mhk.valid_iff_tr _).mpr <| Mhk.tr_Twin.mpr fun a x =>
    ⟨.arr a .t, fun h => Code.arr_ne_left (Tn a) .t h.symm, fun y => hk a y = hk a x, (hk_hae a x).symm⟩
theorem Mhk_not_Inj : ¬ Mhk.Valid Inj := fun h => by
  have := Mhk.tr_Inj.mp ((Mhk.valid_iff_tr _).mp h) .e .e .t (.base ()) rfl
  cases this.2
theorem Mhk_not_Recovery : ¬ Mhk.Valid Recovery := fun h => by
  have := Mhk.tr_Recovery.mp ((Mhk.valid_iff_tr _).mp h) .e .e .t (.base ()) ⟨rfl, rfl⟩
  cases this

end Mhk

end PIF
