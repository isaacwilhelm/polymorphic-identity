import PIHae
import PIClass
import PIClassModels

/-!
# Haecceitism: further models

Models with Haecceitism which settle the remaining questions about which principles, added to
PI⁻ + Haecceitism, PI + Haecceitism, or PIᶜ + Haecceitism, yield which others. Each is a haecceity
construction: every item has a root, got by stripping off haecceities, and identity is settled by
roots.
-/
set_option autoImplicit false

namespace PIF

/-! ## `𝔐_hae,c⁻`: Cantor and Truth without LL≡, in PI⁻ + Haecceitism

Two entities, which have the same root; every other item is its own root, apart from haecceities. -/

section Mhc
attribute [local instance] Classical.propDecidable

def univB2 : Univ := { E := Bool, Base := Empty, B := fun b => b.elim, neE := ⟨true⟩, neB := fun b => b.elim }

noncomputable def ovHC (c : Code univB2.Base) (x : univB2.El c) : Σ c : Code univB2.Base, univB2.El c :=
  if _h : c = .e then ⟨.e, (false : Bool)⟩ else ⟨c, x⟩

theorem ovHC_le (c : Code univB2.Base) (x : univB2.El c) : csz (ovHC c x).1 ≤ csz c := by
  unfold ovHC
  split
  · next h => subst h; exact Nat.le_refl _
  · exact Nat.le_refl _

theorem ovHC_ne (c : Code univB2.Base) (hc : c ≠ .e) (x : univB2.El c) : ovHC c x = ⟨c, x⟩ := by
  unfold ovHC
  split
  · next h => exact absurd h hc
  · rfl

noncomputable def MhcD : IdentData := towerIdent (U := univB2) ovHC
noncomputable abbrev Mhc : Frame := MhcD.frame
theorem Mhc_model : Mhc.IsModelPIm := MhcD.model
theorem Mhc_Hae : Mhc.Valid Hae := tower_Hae (U := univB2) ovHC
theorem Mhc_Twin : Mhc.Valid Twin := tower_Twin (U := univB2) ovHC
theorem Mhc_Inj : Mhc.Valid Inj := MhcD.Inj_valid

theorem hrHC_t (p : Prop) : hr ovHC .t p = ⟨.t, p⟩ := ovHC_ne .t (fun h => nomatch h) p
theorem hrHC_e (x : Bool) : hr ovHC .e x = ⟨.e, (false : Bool)⟩ := by
  show ovHC .e x = _
  unfold ovHC
  split
  · rfl
  · next h => exact absurd rfl h

theorem Mhc_Truth : Mhc.Valid Truth :=
  (Mhc.valid_iff_tr _).mpr <| Mhc.tr_Truth.mpr fun p q h hp => by
    have h' : hr ovHC .t p = hr ovHC .t q := h
    rw [hrHC_t, hrHC_t] at h'
    exact cast (eq_of_heq (Sigma.mk.inj h').2) hp

/-- The empty property is not a haecceity, so it is its own root. -/
theorem hrHC_empty (a : Code univB2.Base) :
    hr ovHC (.arr a .t) (fun _ => False : univB2.El (.arr a .t)) = ⟨.arr a .t, (fun _ => False : univB2.El (.arr a .t))⟩ := by
  refine (hr_arr_t ovHC a _).trans ?_
  split
  · next h =>
    have hc := congrFun (Classical.choose_spec h) (Classical.choose h)
    exact absurd (hc.mpr rfl) id
  · exact ovHC_ne (.arr a .t) (fun h => nomatch h) _

theorem Mhc_Cantor : Mhc.Valid Cantor :=
  (Mhc.valid_iff_tr _).mpr <| Mhc.tr_Cantor.mpr fun (a : Code univB2.Base) => ⟨fun _ => False, fun y h => by
    have h' : hr ovHC (.arr a .t) (fun _ => False : univB2.El (.arr a .t)) = hr ovHC a y := h
    rw [hrHC_empty] at h'
    have h3 := hr_le ovHC_le a y
    rw [← h'] at h3
    exact absurd h3 (Nat.not_le.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
      (Nat.succ_le_succ (Nat.le_add_right _ _))))⟩

theorem Mhc_not_LLEqv : ¬ Mhc.Valid LLEqv := fun h => by
  have := Mhc.tr_LLEqv.mp ((Mhc.valid_iff_tr _).mp h) .e true false
    ((hrHC_e true).trans (hrHC_e false).symm) (fun z => z = true) rfl
  exact Bool.false_ne_true this

end Mhc

/-! ## `𝔐_hae,r`: Recovery without Inj≈, in PIᶜ + Haecceitism

`E = 1`, with one further base type `D`, also with one item. `≈` is sameness of type once `D` is
replaced by `e` in every argument position: so `D→t ≈ e→t`, while `D` and `e` differ. Each item gets a
root, filed under the type got by replacing `D` by `e` everywhere; the haecceity of `x` has the root
of `x`. Items are identified just in case they have the same root. -/

section Mhr
attribute [local instance] Classical.propDecidable

def univHR : Univ := { E := Unit, Base := Unit, B := fun _ => Unit, neE := ⟨()⟩, neB := fun _ => ⟨()⟩ }
abbrev CHR := Code univHR.Base

/-- Replace `D` by `e` everywhere. -/
def TrR : CHR → CHR
  | .base _ => .e
  | .arr a c => .arr (TrR a) (TrR c)
  | c => c

/-- Replace `D` by `e` in argument positions: the `≈`-normal form. -/
def TnR : CHR → CHR
  | .arr a c => .arr (TrR a) (TnR c)
  | c => c

theorem TrR_idem : ∀ c : CHR, TrR (TrR c) = TrR c
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => by show Code.arr (TrR (TrR a)) (TrR (TrR c)) = _; rw [TrR_idem a, TrR_idem c]; rfl

theorem TrR_TnR : ∀ c : CHR, TrR (TnR c) = TrR c
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => by show Code.arr (TrR (TrR a)) (TrR (TnR c)) = _; rw [TrR_idem a, TrR_TnR c]; rfl

theorem TrR_of_TnR {a a' : CHR} (h : TnR a = TnR a') : TrR a = TrR a' := by
  rw [← TrR_TnR a, h, TrR_TnR]

theorem El_TrR : ∀ c : CHR, univHR.El (TrR c) = univHR.El c
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => by
    show (univHR.El (TrR a) → univHR.El (TrR c)) = (univHR.El a → univHR.El c)
    rw [El_TrR a, El_TrR c]

theorem csz_TrR : ∀ c : CHR, csz (TrR c) = csz c
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => by show csz (TrR a) + csz (TrR c) + 1 = _; rw [csz_TrR a, csz_TrR c]; rfl

theorem csz_TnR : ∀ c : CHR, csz (TnR c) = csz c
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => by show csz (TrR a) + csz (TnR c) + 1 = _; rw [csz_TrR a, csz_TnR c]; rfl

theorem TrR_eq_t : ∀ c : CHR, TrR c = .t → c = .t
  | .t, _ => rfl
  | .e, h => by cases h
  | .base _, h => by cases h
  | .arr _ _, h => by cases h

/-- Types whose items are tested for being haecceities. -/
def HaeR : CHR → Prop
  | .arr _ .t => True
  | _ => False

theorem HaeR_iff : ∀ c : CHR, HaeR c ↔ ∃ x, TrR c = .arr x .t
  | .arr a .t => ⟨fun _ => ⟨TrR a, rfl⟩, fun _ => trivial⟩
  | .arr a .e => ⟨fun h => h.elim, fun ⟨_, h⟩ => by injection h with _ h2; cases h2⟩
  | .arr a (.base _) => ⟨fun h => h.elim, fun ⟨_, h⟩ => by injection h with _ h2; cases h2⟩
  | .arr a (.arr c d) => ⟨fun h => h.elim, fun ⟨_, h⟩ => by injection h with _ h2; cases h2⟩
  | .e => ⟨fun h => h.elim, fun ⟨_, h⟩ => by cases h⟩
  | .t => ⟨fun h => h.elim, fun ⟨_, h⟩ => by cases h⟩
  | .base _ => ⟨fun h => h.elim, fun ⟨_, h⟩ => by cases h⟩

theorem HaeR_shape : ∀ a : CHR, HaeR a → ∃ b, a = .arr b .t
  | .arr b .t, _ => ⟨b, rfl⟩
  | .arr _ .e, h => h.elim
  | .arr _ (.base _), h => h.elim
  | .arr _ (.arr _ _), h => h.elim
  | .e, h => h.elim
  | .t, h => h.elim
  | .base _, h => h.elim

abbrev RR := Σ c : CHR, univHR.El c

def ownRR (c : CHR) (x : univHR.El c) : RR := ⟨TrR c, cast (El_TrR c).symm x⟩

theorem ownRR_congr {c c' : CHR} {x : univHR.El c} {x' : univHR.El c'} (h : TrR c = TrR c') (hx : HEq x x') :
    ownRR c x = ownRR c' x' := by
  unfold ownRR
  have hh : HEq (cast (El_TrR c).symm x) (cast (El_TrR c').symm x') :=
    (cast_heq _ _).trans (hx.trans (cast_heq _ _).symm)
  revert hh
  generalize cast (El_TrR c).symm x = y
  generalize cast (El_TrR c').symm x' = y'
  revert y y'
  rw [h]
  intro y y' hh
  cases hh
  rfl

theorem ownRR_inj {c : CHR} {x y : univHR.El c} (h : ownRR c x = ownRR c y) : x = y := by
  have := (Sigma.mk.inj h).2
  exact eq_of_heq ((cast_heq _ _).symm.trans (this.trans (cast_heq _ _)))

noncomputable def haeRootR {A : Type} (f : A → RR) (G : A → Prop) (own : RR) : RR :=
  if h : ∃ x, G = (fun y => f y = f x) then f (Classical.choose h) else own

theorem haeRootR_congr {A A' : Type} (e : A = A') (f : A → RR) (f' : A' → RR) (hf : ∀ y, f y = f' (cast e y))
    (G : A → Prop) (G' : A' → Prop) (hG : HEq G G') {own own' : RR} (ho : own = own') :
    haeRootR f G own = haeRootR f' G' own' := by
  subst e
  have : f = f' := funext hf
  subst this
  cases hG
  rw [ho]

noncomputable def hkR : (c : CHR) → univHR.El c → RR
  | .arr a .t, G => haeRootR (hkR a) G (ownRR (.arr a .t) G)
  | c, x => ownRR c x

theorem hkR_own (c : CHR) (hc : ¬ HaeR c) (x : univHR.El c) : hkR c x = ownRR c x := by
  cases c with
  | arr a c' => cases c' with
    | t => exact absurd trivial hc
    | _ => rfl
  | _ => rfl

theorem ownR_caseR {a a' : CHR} (ha : ¬ HaeR a) (u : univHR.El a) (u' : univHR.El a') (h : TrR a = TrR a')
    (hu : HEq u u') : hkR a u = hkR a' u' := by
  have ha' : ¬ HaeR a' := fun ha' => ha ((HaeR_iff a).mpr (h ▸ (HaeR_iff a').mp ha'))
  rw [hkR_own a ha, hkR_own a' ha']
  exact ownRR_congr h hu

/-- Items of types which agree once `D` is replaced by `e` have the same root, if they are the same. -/
theorem hkR_congr (a : CHR) : ∀ (a' : CHR) (u : univHR.El a) (u' : univHR.El a'), TrR a = TrR a' → HEq u u' →
    hkR a u = hkR a' u' := by
  induction a with
  | arr b c ihb _ =>
    intro a' u u' h hu
    by_cases hc : c = .t
    · subst hc
      have ha' : HaeR a' := (HaeR_iff a').mpr ⟨TrR b, h.symm⟩
      obtain ⟨b', rfl⟩ := HaeR_shape a' ha'
      have h0 := h
      injection h0 with hb _
      have e : univHR.El b = univHR.El b' := (El_TrR b).symm.trans ((congrArg univHR.El hb).trans (El_TrR b'))
      exact haeRootR_congr e (hkR b) (hkR b') (fun y => ihb b' y (cast e y) hb (cast_heq _ _).symm) u u' hu
        (ownRR_congr h hu)
    · have ha : ¬ HaeR (.arr b c) := fun ha => by
        obtain ⟨_, he⟩ := HaeR_shape _ ha
        injection he with _ h2
        exact hc h2
      exact ownR_caseR ha u u' h hu
  | e => intro a' u u' h hu; exact ownR_caseR (a := .e) (fun h => h) u u' h hu
  | t => intro a' u u' h hu; exact ownR_caseR (a := .t) (fun h => h) u u' h hu
  | base x => intro a' u u' h hu; exact ownR_caseR (a := .base x) (fun h => h) u u' h hu

theorem hkR_hae (a : CHR) (x : univHR.El a) : hkR (.arr a .t) (fun y => hkR a y = hkR a x) = hkR a x := by
  show haeRootR (hkR a) (fun y => hkR a y = hkR a x) _ = _
  unfold haeRootR
  split
  · next h =>
    have hc := Classical.choose_spec h
    exact (congrFun hc (Classical.choose h)).mpr rfl
  · next h => exact absurd ⟨x, rfl⟩ h

theorem hkR_le : ∀ (c : CHR) (x : univHR.El c), csz (hkR c x).1 ≤ csz c := by
  intro c
  induction c with
  | arr b c ihb _ =>
    intro x
    by_cases hc : c = .t
    · subst hc
      show csz (haeRootR (hkR b) x _).1 ≤ _
      unfold haeRootR
      split
      · exact Nat.le_trans (ihb _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _))
      · exact Nat.le_of_eq (csz_TrR _)
    · have ha : ¬ HaeR (.arr b c) := fun ha => by
        obtain ⟨_, he⟩ := HaeR_shape _ ha
        injection he with _ h2
        exact hc h2
      rw [hkR_own _ ha]; exact Nat.le_of_eq (csz_TrR _)
  | e => intro x; exact Nat.le_refl _
  | t => intro x; exact Nat.le_refl _
  | base _ => intro x; exact Nat.le_refl _

theorem hkR_inj (c : CHR) (x y : univHR.El c) (h : hkR c x = hkR c y) : x = y := by
  by_cases ha : HaeR c
  · obtain ⟨b, rfl⟩ := HaeR_shape c ha
    have big : ∀ z : univHR.El b, csz (hkR b z).1 < csz (TrR (.arr b .t)) := fun z => by
      rw [csz_TrR]
      exact Nat.lt_of_le_of_lt (hkR_le b z) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Nat.succ_le_succ (Nat.le_add_right _ _)))
    change haeRootR (hkR b) x _ = haeRootR (hkR b) y _ at h
    unfold haeRootR at h
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
    · exact ownRR_inj h
  · rw [hkR_own c ha, hkR_own c ha] at h
    exact ownRR_inj h

def MhrF : Frame where
  U := univHR
  eqv := fun a b x y => hkR a x = hkR b y
  teq := fun a b => TnR a = TnR b

theorem hrEl {a a' : CHR} (h : TnR a = TnR a') : univHR.El a = univHR.El a' :=
  (El_TrR a).symm.trans ((congrArg univHR.El (TrR_of_TnR h)).trans (El_TrR a'))

def MhrI : Invariance MhrF where
  Adm := fun a a' R => TnR a = TnR a' ∧ ∀ x y, R x y ↔ HEq x y
  refl := fun _ => ⟨rfl, fun _ _ => ⟨fun h => h ▸ HEq.rfl, eq_of_heq⟩⟩
  arrow := by
    rintro a a' c c' R S ⟨h1, hR⟩ ⟨h2, hS⟩
    refine ⟨?_, fun f f' => fun_heq_iff (hrEl h1) (hrEl h2) hR hS f f'⟩
    show Code.arr (TrR a) (TnR c) = Code.arr (TrR a') (TnR c')
    rw [TrR_of_TnR h1, h2]
  total := by
    rintro a a' R ⟨h, hR⟩ u
    exact ⟨cast (hrEl h) u, (hR _ _).mpr (cast_heq _ _).symm⟩
  onto := by
    rintro a a' R ⟨h, hR⟩ u
    exact ⟨cast (hrEl h).symm u, (hR _ _).mpr (cast_heq _ _)⟩
  teq := by
    rintro a a' b b' R S ⟨h1, -⟩ ⟨h2, -⟩
    show TnR a = TnR b ↔ TnR a' = TnR b'
    rw [h1, h2]
  eqv := by
    rintro a a' b b' R S ⟨h1, hR⟩ ⟨h2, hS⟩ u u' v v' hu hv
    show hkR a u = hkR b v ↔ hkR a' u' = hkR b' v'
    rw [hkR_congr a a' u u' (TrR_of_TnR h1) ((hR u u').mp hu),
      hkR_congr b b' v v' (TrR_of_TnR h2) ((hS v v').mp hv)]

abbrev Mhr : Frame := MhrF
theorem Mhr_model : Mhr.IsModelPIm :=
  Frame.isModelPIm_of_invariance MhrF MhrI (fun _ _ h => ⟨fun x y => HEq x y, h, fun _ _ => Iff.rfl⟩)
    ((MhrF.valid_iff_tr _).mpr (MhrF.tr_RefEqv.mpr fun _ _ => rfl))
    ((MhrF.valid_iff_tr _).mpr (MhrF.tr_SymEqv.mpr fun _ _ _ _ h => h.symm))
    ((MhrF.valid_iff_tr _).mpr (MhrF.tr_TransEqv.mpr fun _ _ _ _ _ _ ⟨h1, h2⟩ => h1.trans h2))
    ((MhrF.valid_iff_tr _).mpr (MhrF.tr_RefTeq.mpr fun _ => rfl))
theorem Mhr_LLEqv : Mhr.Valid LLEqv :=
  (Mhr.valid_iff_tr _).mpr <| Mhr.tr_LLEqv.mpr fun a x y h _ hP => hkR_inj a x y h ▸ hP
theorem Mhr_Class : ∀ χ, ClassSch χ → Mhr.Valid χ := Mhr.Class_valid Mhr_model Mhr_LLEqv
theorem Mhr_Hae : Mhr.Valid Hae :=
  (Mhr.valid_iff_tr _).mpr <| Mhr.tr_Hae.mpr fun a x => (hkR_hae a x).symm
theorem Mhr_Twin : Mhr.Valid Twin :=
  (Mhr.valid_iff_tr _).mpr <| Mhr.tr_Twin.mpr fun (a : CHR) x =>
    ⟨.arr a .t, fun h => by
      have := congrArg csz (show TnR a = TnR (.arr a .t) from h)
      rw [csz_TnR, csz_TnR] at this
      exact absurd this (Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
        (Nat.succ_le_succ (Nat.le_add_right _ _)))),
     fun y => hkR a y = hkR a x, (hkR_hae a x).symm⟩
theorem Mhr_Recovery : Mhr.Valid Recovery :=
  (Mhr.valid_iff_tr _).mpr <| Mhr.tr_Recovery.mpr fun _ _ _ _ ⟨h, _⟩ => by
    injection h
theorem Mhr_not_Inj : ¬ Mhr.Valid Inj := fun h => by
  have := Mhr.tr_Inj.mp ((Mhr.valid_iff_tr _).mp h) (.base ()) .e .t .t rfl
  cases this.1

end Mhr

end PIF
