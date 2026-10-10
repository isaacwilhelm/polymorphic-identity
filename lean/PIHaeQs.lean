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

/-! ## `𝔐_hae,ie`: Int≈ without Ext≈, in PIᶜ + Haecceitism

Two worlds, one entity, and a base type `D` with one item. Each item has a root, got by stripping
off haecceities; items are identified at a world just in case they have the same root, or the world
is the actual one and their roots are the entity and the item of `D`. `≈` is identity of types. -/

namespace Wd
open Classical

def univHI : Univ where
  W := Bool
  w0 := true
  E := Unit
  Base := Unit
  B := fun _ => Unit
  neE := ⟨()⟩
  neB := fun _ => ⟨()⟩

abbrev CHI := Code univHI.Base

def hcyI (a : CHI) (z : univHI.El a) : univHI.El (.arr a .t) := fun y _ => y = z

theorem hcyI_inj {a : CHI} {z z' : univHI.El a} (h : hcyI a z = hcyI a z') : z = z' := by
  have := congrFun (congrFun h z) true
  exact cast this rfl

noncomputable def rootI : (a : CHI) → univHI.El a → (Σ b : CHI, univHI.El b)
  | .arr a .t, f => if h : ∃ z, f = hcyI a z then rootI a (Classical.choose h) else ⟨.arr a .t, f⟩
  | a, x => ⟨a, x⟩

theorem rootI_t (a : CHI) (f : univHI.El (.arr a .t)) :
    rootI (.arr a .t) f = if h : ∃ z, f = hcyI a z then rootI a (Classical.choose h) else ⟨.arr a .t, f⟩ := by
  rw [rootI]

/-- An item either is its own root, or has a root of a smaller type. -/
theorem rootI_lt : ∀ (a : CHI) (x : univHI.El a), rootI a x = ⟨a, x⟩ ∨ PIF.csz (rootI a x).1 < PIF.csz a
  | .e, _ => Or.inl rfl
  | .t, _ => Or.inl rfl
  | .base _, _ => Or.inl rfl
  | .arr a .e, _ => Or.inl rfl
  | .arr a (.base _), _ => Or.inl rfl
  | .arr a (.arr c d), _ => Or.inl rfl
  | .arr a .t, f => by
    rw [rootI_t]
    split
    · next h =>
      refine Or.inr ?_
      rcases rootI_lt a (Classical.choose h) with e | e
      · rw [e]; show PIF.csz a < PIF.csz a + 1 + 1; omega
      · show _ < PIF.csz a + 1 + 1; omega
    · exact Or.inl rfl

theorem rootI_le (a : CHI) (x : univHI.El a) : PIF.csz (rootI a x).1 ≤ PIF.csz a := by
  rcases rootI_lt a x with e | e
  · rw [e]; exact Nat.le_refl _
  · exact Nat.le_of_lt e

theorem rootI_hcy (a : CHI) (z : univHI.El a) : rootI (.arr a .t) (hcyI a z) = rootI a z := by
  have h : ∃ z', hcyI a z = hcyI a z' := ⟨z, rfl⟩
  rw [rootI_t]
  split
  · rename_i h'; rw [← hcyI_inj (Classical.choose_spec h')]
  · exact absurd h ‹_›

theorem rootI_not (a : CHI) (f : univHI.El (.arr a .t)) (hf : ¬ ∃ z, f = hcyI a z) :
    rootI (.arr a .t) f = ⟨.arr a .t, f⟩ := by
  rw [rootI_t]
  split
  · exact absurd ‹_› hf
  · rfl

theorem rootI_inj : ∀ (a : CHI) (x y : univHI.El a), rootI a x = rootI a y → x = y
  | .e, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .t, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .base _, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr a .e, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr a (.base _), _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr a (.arr c d), _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr a .t, f, g, h => by
    by_cases hf : ∃ z, f = hcyI a z <;> by_cases hg : ∃ z, g = hcyI a z
    · obtain ⟨z, rfl⟩ := hf; obtain ⟨z', rfl⟩ := hg
      rw [rootI_hcy, rootI_hcy] at h
      rw [rootI_inj a z z' h]
    · obtain ⟨z, rfl⟩ := hf
      rw [rootI_hcy, rootI_not a g hg] at h
      have := rootI_le a z; rw [congrArg Sigma.fst h] at this; simp only [PIF.csz] at this; omega
    · obtain ⟨z', rfl⟩ := hg
      rw [rootI_hcy, rootI_not a f hf] at h
      have := rootI_le a z'; rw [← congrArg Sigma.fst h] at this; simp only [PIF.csz] at this; omega
    · rw [rootI_not a f hf, rootI_not a g hg] at h
      exact eq_of_heq (Sigma.mk.inj h).2

/-- The bottom of a tower of haecceity types. -/
def foot : CHI → CHI
  | .arr a .t => foot a
  | c => c

theorem foot_rootI : ∀ (a : CHI) (x : univHI.El a), foot (rootI a x).1 = foot a
  | .e, _ => rfl
  | .t, _ => rfl
  | .base _, _ => rfl
  | .arr a .e, _ => rfl
  | .arr a (.base _), _ => rfl
  | .arr a (.arr c d), _ => rfl
  | .arr a .t, f => by
    rw [rootI_t]
    split
    · exact foot_rootI a _
    · rfl

/-- Roots which are the entity and the item of `D`. -/
def crossI (r s : Σ b : CHI, univHI.El b) : Prop := (r.1 = .e ∧ s.1 = .base ()) ∨ (r.1 = .base () ∧ s.1 = .e)

theorem crossI_symm {r s : Σ b : CHI, univHI.El b} (h : crossI r s) : crossI s r :=
  h.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)

theorem sig_e : ∀ r : Σ b : CHI, univHI.El b, r.1 = .e → r = ⟨.e, ()⟩
  | ⟨_, _⟩, rfl => rfl
theorem sig_D : ∀ r : Σ b : CHI, univHI.El b, r.1 = .base () → r = ⟨.base (), ()⟩
  | ⟨_, _⟩, rfl => rfl

theorem crossI_trans {r s u : Σ b : CHI, univHI.El b} (h1 : crossI r s) (h2 : crossI s u) : r = u := by
  rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · rw [a2] at b1; cases b1
  · rw [sig_e r a1, sig_e u b2]
  · rw [sig_D r a1, sig_D u b2]
  · rw [a2] at b1; cases b1

noncomputable def MhieF : Frame where
  U := univHI
  eqv := fun a b x y w => rootI a x = rootI b y ∨ (w = true ∧ crossI (rootI a x) (rootI b y))
  teq := fun a b _ => a = b

theorem MhieC_symm : ∀ a b x y w, MhieF.eqv a b x y w → MhieF.eqv b a y x w := fun _ _ _ _ _ h =>
  h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.1, crossI_symm h.2⟩)

theorem MhieC_trans : ∀ a b c x y z w, MhieF.eqv a b x y w → MhieF.eqv b c y z w → MhieF.eqv a c x z w := by
  intro a b c x y z w h1 h2
  rcases h1 with h1 | ⟨hw, h1⟩ <;> rcases h2 with h2 | ⟨_, h2⟩
  · exact Or.inl (h1.trans h2)
  · rw [← h1] at h2; exact Or.inr ⟨by assumption, h2⟩
  · rw [h2] at h1; exact Or.inr ⟨hw, h1⟩
  · exact Or.inl (crossI_trans h1 h2)

theorem MhieC_eq : ∀ a x y w, MhieF.eqv a a x y w → x = y := by
  intro a x y w h
  rcases h with h | ⟨_, h⟩
  · exact rootI_inj a x y h
  · have f1 := foot_rootI a x
    have f2 := foot_rootI a y
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at f1 <;> rw [h2] at f2 <;> rw [← f2] at f1 <;> cases f1

theorem MhieC_isModelAt : MhieF.IsModelAt :=
  MhieF.isModelAt_of (fun _ _ _ => Or.inl rfl) MhieC_symm MhieC_trans (fun _ _ _ => Iff.rfl)

theorem MhieC_model : MhieF.IsModelPIm :=
  MhieF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => Or.inl rfl) (fun a b x y h => MhieC_symm a b x y _ h)
    (fun a b c x y z h1 h2 => MhieC_trans a b c x y z _ h1 h2)

theorem MhieC_LLEqv : MhieF.Valid LLEqv := fun ρ env => MhieF.LLEqv_validAt_of MhieC_eq _ ρ env

theorem MhieC_Class : ∀ χ, ClassSch χ → MhieF.Valid χ :=
  MhieF.Class_valid_of MhieC_isModelAt (MhieF.LLEqv_validAt_of MhieC_eq) fun _ _ => Or.inl rfl

theorem MhieC_Hae : MhieF.Valid Hae := by
  intro ρ env
  show ∀ a (x : univHI.El a), MhieF.eqv a (.arr a .t) x (fun y w => MhieF.eqv a a y x w) univHI.w0
  intro a x
  have e : (fun (y : univHI.El a) (w : Bool) => MhieF.eqv a a y x w) = hcyI a x :=
    funext fun y => funext fun w => propext ⟨fun h => MhieC_eq a y x w h, fun h => h ▸ Or.inl rfl⟩
  refine Or.inl ?_
  exact (rootI_hcy a x).symm.trans (congrArg (rootI (.arr a .t)) e.symm)

theorem MhieC_not_ExtT : ¬ MhieF.Valid ExtT := fun h => by
  have h0 := (MhieF.holds_tall _ _ _).mp ((MhieF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) (.base ())
  have hc : crossI (rootI .e ()) (rootI (.base ()) ()) := Or.inl ⟨rfl, rfl⟩
  have hT := (MhieF.holds_imp _ _ _ _).mp h0 ((MhieF.holds_conj _ _ _ _).mpr
    ⟨(MhieF.holds_all _ _ _ _).mpr fun x => (MhieF.holds_ex _ _ _ _).mpr
        ⟨(), (MhieF.holds_eqv _ _ _ _ _ _).mpr (Or.inr ⟨rfl, hc⟩)⟩,
     (MhieF.holds_all _ _ _ _).mpr fun y => (MhieF.holds_ex _ _ _ _).mpr
        ⟨(), (MhieF.holds_eqv _ _ _ _ _ _).mpr (Or.inr ⟨rfl, hc⟩)⟩⟩)
  exact nomatch (show (Code.e : CHI) = .base () from (MhieF.holds_teq _ _ _ _).mp hT)

/-- Every type has an item which is its own root. -/
theorem own_item : ∀ a : CHI, ∃ x : univHI.El a, rootI a x = ⟨a, x⟩
  | .e => ⟨(), rfl⟩
  | .t => ⟨fun _ => True, rfl⟩
  | .base _ => ⟨(), rfl⟩
  | .arr _ .e => ⟨fun _ => (), rfl⟩
  | .arr _ (.base _) => ⟨fun _ => (), rfl⟩
  | .arr a (.arr c d) => ⟨Classical.choice (Univ.El_nonempty (U := univHI) (.arr a (.arr c d))), rfl⟩
  | .arr a .t => ⟨fun _ _ => False, rootI_not a _ fun ⟨z, hz⟩ => cast (congrFun (congrFun hz z) true).symm rfl⟩

/-- If every item of `a` has the root of an item of `b`, then `a` is no bigger than `b`. -/
theorem sub_le (a b : CHI) (h : ∀ x : univHI.El a, ∃ y : univHI.El b, rootI a x = rootI b y) :
    PIF.csz a ≤ PIF.csz b ∧ (PIF.csz a = PIF.csz b → a = b) := by
  obtain ⟨x, hx⟩ := own_item a
  obtain ⟨y, hy⟩ := h x
  rw [hx] at hy
  have l := rootI_le b y
  rw [← hy] at l
  refine ⟨l, fun e => ?_⟩
  rcases rootI_lt b y with e2 | e2
  · rw [e2] at hy; exact congrArg Sigma.fst hy
  · rw [← hy] at e2; simp only at e2; omega

theorem MhieC_IntT : MhieF.Valid IntT := by
  intro ρ env
  refine (MhieF.holds_tall _ _ _).mpr fun a => (MhieF.holds_tall _ _ _).mpr fun b => ?_
  refine (MhieF.holds_imp _ _ _ _).mpr fun h => (MhieF.holds_teq _ _ _ _).mpr ?_
  have hb : ∀ p q, MhieF.eqv .t .t p q MhieF.U.w0 → p = q := fun p q h => MhieC_eq _ _ _ _ h
  have hs := MhieF.box_all hb _ _ _ ((MhieF.holds_conj _ _ _ _).mp h).1 false
  have ht := MhieF.box_all hb _ _ _ ((MhieF.holds_conj _ _ _ _).mp h).2 false
  have h1 : ∀ x : univHI.El a, ∃ y : univHI.El b, rootI a x = rootI b y := fun x => by
    obtain ⟨y, hy⟩ := (MhieF.holdsAt_ex _ _ _ _ false).mp ((MhieF.holdsAt_all _ _ _ _ false).mp hs x)
    rcases (MhieF.holdsAt_eqv _ _ _ _ _ _ false).mp hy with e | ⟨hw, _⟩
    · exact ⟨y, e⟩
    · exact (Bool.false_ne_true hw).elim
  have h2 : ∀ y : univHI.El b, ∃ x : univHI.El a, rootI b y = rootI a x := fun y => by
    obtain ⟨x, hx⟩ := (MhieF.holdsAt_ex _ _ _ _ false).mp ((MhieF.holdsAt_all _ _ _ _ false).mp ht y)
    rcases (MhieF.holdsAt_eqv _ _ _ _ _ _ false).mp hx with e | ⟨hw, _⟩
    · exact ⟨x, e.symm⟩
    · exact (Bool.false_ne_true hw).elim
  have l1 := sub_le a b h1
  have l2 := sub_le b a h2
  exact l1.2 (Nat.le_antisymm l1.1 l2.1)

end Wd

/-! ## Roots in general

For any family of sets indexed by codes, and any injective way `hcy` of sending an item `z` of `α`
to an item of `α→t` (its haecceity), the root of an item is got by stripping off haecceities. -/

section GRoot
open Classical
variable {B : Type} (El : Code B → Type) (hcy : ∀ a, El a → El (.arr a .t))

noncomputable def groot : (a : Code B) → El a → (Σ b : Code B, El b)
  | .arr a .t, f => if h : ∃ z, f = hcy a z then groot a (Classical.choose h) else ⟨.arr a .t, f⟩
  | a, x => ⟨a, x⟩

theorem groot_t (a : Code B) (f : El (.arr a .t)) :
    groot El hcy (.arr a .t) f = if h : ∃ z, f = hcy a z then groot El hcy a (Classical.choose h) else ⟨.arr a .t, f⟩ := by
  rw [groot]

theorem groot_lt : ∀ (a : Code B) (x : El a), groot El hcy a x = ⟨a, x⟩ ∨ csz (groot El hcy a x).1 < csz a
  | .e, _ => Or.inl rfl
  | .t, _ => Or.inl rfl
  | .base _, _ => Or.inl rfl
  | .arr _ .e, _ => Or.inl rfl
  | .arr _ (.base _), _ => Or.inl rfl
  | .arr _ (.arr _ _), _ => Or.inl rfl
  | .arr a .t, f => by
    rw [groot_t]
    split
    · next h =>
      refine Or.inr ?_
      rcases groot_lt a (Classical.choose h) with e | e
      · rw [e]; show csz a < csz a + 1 + 1; omega
      · show _ < csz a + 1 + 1; omega
    · exact Or.inl rfl

theorem groot_le (a : Code B) (x : El a) : csz (groot El hcy a x).1 ≤ csz a := by
  rcases groot_lt El hcy a x with e | e
  · rw [e]; exact Nat.le_refl _
  · exact Nat.le_of_lt e

theorem groot_not (a : Code B) (f : El (.arr a .t)) (hf : ¬ ∃ z, f = hcy a z) :
    groot El hcy (.arr a .t) f = ⟨.arr a .t, f⟩ := by
  rw [groot_t]
  split
  · exact absurd ‹_› hf
  · rfl

variable {El hcy}
variable (hinj : ∀ a (z z' : El a), hcy a z = hcy a z' → z = z')
include hinj

theorem groot_hcy (a : Code B) (z : El a) : groot El hcy (.arr a .t) (hcy a z) = groot El hcy a z := by
  have h : ∃ z', hcy a z = hcy a z' := ⟨z, rfl⟩
  rw [groot_t]
  split
  · rename_i h'; rw [← hinj a _ _ (Classical.choose_spec h')]
  · exact absurd h ‹_›

theorem groot_inj : ∀ (a : Code B) (x y : El a), groot El hcy a x = groot El hcy a y → x = y
  | .e, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .t, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .base _, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr _ .e, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr _ (.base _), _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr _ (.arr _ _), _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr a .t, f, g, h => by
    by_cases hf : ∃ z, f = hcy a z <;> by_cases hg : ∃ z, g = hcy a z
    · obtain ⟨z, rfl⟩ := hf; obtain ⟨z', rfl⟩ := hg
      rw [groot_hcy hinj, groot_hcy hinj] at h
      rw [groot_inj a z z' h]
    · obtain ⟨z, rfl⟩ := hf
      rw [groot_hcy hinj, groot_not El hcy a g hg] at h
      have := groot_le El hcy a z; rw [congrArg Sigma.fst h] at this; simp only [csz] at this; omega
    · obtain ⟨z', rfl⟩ := hg
      rw [groot_hcy hinj, groot_not El hcy a f hf] at h
      have := groot_le El hcy a z'; rw [← congrArg Sigma.fst h] at this; simp only [csz] at this; omega
    · rw [groot_not El hcy a f hf, groot_not El hcy a g hg] at h
      exact eq_of_heq (Sigma.mk.inj h).2

/-- The haecceity of `x`, given by sameness of root, is `hcy x`. -/
theorem groot_hae (a : Code B) (x : El a) (f : El (.arr a .t)) (hf : f = hcy a x) :
    groot El hcy a x = groot El hcy (.arr a .t) f := by
  rw [hf, groot_hcy hinj]

end GRoot

/-! ## `𝔐_q,hae`: Booleanism, the Identity Identity, NI≡, NI≈ and TCBF without Classicism, in PI + Haecceitism

As `𝔐_q,A`, except that items are identified, rigidly, just in case they have the same root. -/

namespace Al

def hcyQ (a : Code Empty) (z : univQ.El a) : univQ.El (.arr a .t) := fun y _ => y = z

theorem hcyQ_inj (a : Code Empty) (z z' : univQ.El a) (h : hcyQ a z = hcyQ a z') : z = z' :=
  cast (congrFun (congrFun h z) true) rfl

noncomputable abbrev rootQ := groot univQ.El hcyQ

noncomputable def MqHF : Frame where
  U := univQ
  eqv := fun a b x y _ => rootQ a x = rootQ b y
  teq := fun a b _ => a = b
  neg := fun p w => ¬ p w
  imp := fun p q w => p w → q w
  cnj := fun p q w => p w ∧ q w
  dsj := fun p q w => p w ∨ q w
  bic := fun p q w => p w ↔ q w
  all := fun _ f w => ∀ x, f x w
  ex := fun _ f w => ∃ x, f x w
  tall := fun Q w => cond w (∀ a, Q a true) False
  tex := fun Q w => cond w (∃ a, Q a true) True
  hneg := fun _ => Iff.rfl
  himp := fun _ _ => Iff.rfl
  hcnj := fun _ _ => Iff.rfl
  hdsj := fun _ _ => Iff.rfl
  hbic := fun _ _ => Iff.rfl
  hall := fun _ _ => Iff.rfl
  hex := fun _ _ => Iff.rfl
  htall := fun _ => Iff.rfl
  htex := fun _ => Iff.rfl

theorem MqH_eqT (p q : univQ.P) : MqHF.U.V (MqHF.eqv .t .t p q) ↔ p = q :=
  ⟨fun h => eq_of_heq (Sigma.mk.inj h).2, fun h => h ▸ rfl⟩

theorem MqH_eq {a : Code Empty} {x y : univQ.El a} (h : MqHF.U.V (MqHF.eqv a a x y)) : x = y :=
  groot_inj hcyQ_inj a x y h

theorem MqH_model : MqHF.IsModelPIm :=
  MqHF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ _ _ h => h.symm)
    (fun _ _ _ _ _ _ h1 h2 => (h1 : rootQ _ _ = _).trans h2)

theorem MqH_top {n : Nat} {Γ : Ctx n} (ρ : MqHF.U.TEnv n) (env : MqHF.U.Env Γ ρ) :
    MqHF.eval (topF : Fm Γ) ρ env = fun _ => True := by
  funext w
  have e := MqHF.eval_all (Γ := Γ) tyT (.var .here) ρ env
  refine propext ⟨fun _ => trivial, fun _ => ?_⟩
  show ¬ MqHF.eval (botF : Fm Γ) ρ env w
  rw [botF, e]
  exact fun h => h (fun _ => False)

theorem MqH_LLEqv : MqHF.Valid LLEqv := by
  intro ρ env
  refine (MqHF.holds_tall _ _ _).mpr fun a => ?_
  refine (MqHF.holds_all _ _ _ _).mpr fun x => (MqHF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MqHF.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (MqHF.holds_all _ _ _ _).mpr fun G => (MqHF.holds_imp _ _ _ _).mpr fun hGx => ?_
  have h := MqH_eq ((MqHF.holds_eqv _ _ _ _ _ _).mp hxy)
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans ((heq_of_eq h).trans (cast_heq _ _)))
  subst e
  exact hGx

theorem MqH_Hae : MqHF.Valid Hae := by
  intro ρ env
  refine (MqHF.holds_tall _ _ _).mpr fun a => (MqHF.holds_all _ _ _ _).mpr fun x => ?_
  refine (MqHF.holds_eqv _ _ _ _ _ _).mpr (groot_hae hcyQ_inj a x _ ?_)
  funext y w
  exact propext ⟨fun h => groot_inj hcyQ_inj a y x h, fun h => h ▸ rfl⟩

theorem MqH_evalInst {n : Nat} {Γ : Ctx n} {k : Nat} (P : PF k) (as : Fin k → Fm Γ) (ρ : MqHF.U.TEnv n)
    (env : MqHF.U.Env Γ ρ) (w : Bool) :
    MqHF.eval (P.inst as) ρ env w ↔ P.evalP (fun i => MqHF.eval (as i) ρ env w) := by
  induction P with
  | atom i => exact Iff.rfl
  | neg P ih => exact not_congr ih
  | imp P Q ihP ihQ => exact imp_congr ihP ihQ
  | conj P Q ihP ihQ => exact and_congr ihP ihQ
  | disj P Q ihP ihQ => exact or_congr ihP ihQ
  | iff P Q ihP ihQ => exact iff_congr ihP ihQ

theorem MqH_Bool : ∀ φ, BoolSch φ → MqHF.Valid φ := by
  rintro _ ⟨k, P, Q, hT, rfl⟩ ρ env0
  refine MqHF.holds_closeAll k _ ρ (fun env => ?_) env0
  have e : MqHF.eval (P.inst (varsT k)) ρ env = MqHF.eval (Q.inst (varsT k)) ρ env :=
    funext fun w => propext ((MqH_evalInst P _ ρ env w).trans ((hT _).trans (MqH_evalInst Q _ ρ env w).symm))
  exact (MqHF.holds_eqv_t _ _ _ _).mpr ((MqH_eqT _ _).mpr e)

theorem MqH_IdId : MqHF.Valid IdId := by
  intro ρ env
  refine (MqHF.holds_tall _ _ _).mpr fun a => ?_
  refine (MqHF.holds_all _ _ _ _).mpr fun x => (MqHF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MqHF.holds_eqv_t _ _ _ _).mpr ((MqH_eqT _ _).mpr ?_)
  refine (MqHF.eval_eqv _ _ _ _ _ _).trans (Eq.trans ?_ (MqHF.eval_all
    (Γ := ((Ctx.nil.text).ext tv0).ext tv0) tv0.pred
    (Tm.imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))
    (scons a ρ) ((env, x), y)).symm)
  funext w
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans ((heq_of_eq (MqH_eq h)).trans (cast_heq _ _)))
    subst e; intro G hG; exact hG
  · have hy : HEq y x := h (fun z _ => HEq z x) (by exact HEq.rfl)
    have e : y = x := eq_of_heq hy
    subst e
    exact rfl

theorem MqH_NIEqv : MqHF.Valid NIEqv := by
  intro ρ env
  refine (MqHF.holds_tall _ _ _).mpr fun a => ?_
  refine (MqHF.holds_all _ _ _ _).mpr fun x => (MqHF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MqHF.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (MqHF.holds_eqv_t _ _ _ _).mpr ((MqH_eqT _ _).mpr ?_)
  exact ((MqHF.eval_eqv _ _ _ _ _ _).trans (funext fun _ => propext ⟨fun _ => trivial, fun _ => hxy⟩)).trans
    (MqH_top (Γ := ((Ctx.nil.text).ext tv0).ext tv0) _ _).symm

theorem MqH_NITeq : MqHF.Valid NITeq := by
  intro ρ env
  refine (MqHF.holds_tall _ _ _).mpr fun a => (MqHF.holds_tall _ _ _).mpr fun b => ?_
  refine (MqHF.holds_imp _ _ _ _).mpr fun h => ?_
  refine (MqHF.holds_eqv_t _ _ _ _).mpr ((MqH_eqT _ _).mpr ?_)
  exact ((MqHF.eval_teq _ _ _ _).trans (funext fun _ => propext ⟨fun _ => trivial, fun _ => h⟩)).trans
    (MqH_top (Γ := Ctx.nil.text.text) _ _).symm

theorem MqH_TCBF : ∀ χ, TCBFSch χ → MqHF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MqHF.holds_imp _ _ _ _).mpr fun h => ?_
  have e := ((MqH_eqT _ _).mp ((MqHF.holds_eqv_t _ _ _ _).mp h)).trans (MqH_top (Γ := Ctx.nil) _ _)
  exact (cast (congrFun e false).symm trivial : False).elim

open Derive in
/-- `𝔸α(α ≈ α) ≡ ⊤` is an instance of Classicism. -/
theorem TallRef_class : ClassSch (Tm.eqv tyT tyT (Tm.tall (Tm.teq tv0 tv0)) topF : Fm Ctx.nil) := by
  refine Or.inl ⟨0, Ctx.nil, Tm.tall (Tm.teq tv0 tv0), topF, ?_, rfl⟩
  have hr : Ent (fun χ => χ = LLEqv) Δ1 [] (Tm.teq tv0 tv0) := (Ent.closed (Γ := Δ1) Prov.refTeq).tinst tv0
  have ha : Ent (fun χ => χ = LLEqv) Ctx.nil [] (Tm.tall (Tm.teq tv0 tv0)) := Ent.tgen hr
  exact Ent.toProv (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1))))
    (v2 _ topF) (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) ha Ent.top)

theorem MqH_not_Class : ¬ ∀ χ, ClassSch χ → MqHF.Valid χ := fun h => by
  have h0 := h _ TallRef_class (fun i => i.elim0) ()
  have e := ((MqH_eqT _ _).mp ((MqHF.holds_eqv_t _ _ _ _).mp h0)).trans (MqH_top (Γ := Ctx.nil) _ _)
  exact (cast (congrFun e false).symm trivial : False)

end Al

/-! ## `𝔐_cl,hae`: Collapse without PropExt, in PI + Haecceitism

As `𝔐_cl`, except that items are identified just in case they have the same root. -/

namespace Al

noncomputable def hcyA (a : Code Empty) (z : univA.El a) : univA.El (.arr a .t) := fun y => mkA (y = z)

theorem hcyA_inj (a : Code Empty) (z z' : univA.El a) (h : hcyA a z = hcyA a z') : z = z' := by
  have e : mkA (z = z) = mkA (z = z') := congrFun h z
  exact (mkA_V _).mp (e ▸ (mkA_V _).mpr rfl)

noncomputable abbrev rootA := groot univA.El hcyA

noncomputable def MclHF : Frame where
  U := univA
  eqv := fun a b x y => mkA (rootA a x = rootA b y)
  teq := fun a b => mkA (a = b)
  neg := fun p => mkA (¬ p = none)
  imp := fun p q => mkA (p = none → q = none)
  cnj := fun p q => mkA (p = none ∧ q = none)
  dsj := fun p q => mkA (p = none ∨ q = none)
  bic := fun p q => mkA (p = none ↔ q = none)
  all := fun _ f => qA (∀ x, f x = none)
  ex := fun _ f => qA (∃ x, f x = none)
  tall := fun Q => qA (∀ a, Q a = none)
  tex := fun Q => qA (∃ a, Q a = none)
  hneg := fun _ => mkA_V _
  himp := fun _ _ => mkA_V _
  hcnj := fun _ _ => mkA_V _
  hdsj := fun _ _ => mkA_V _
  hbic := fun _ _ => mkA_V _
  hall := fun _ _ => qA_V _
  hex := fun _ _ => qA_V _
  htall := fun _ => qA_V _
  htex := fun _ => qA_V _

theorem MclH_eq {a : Code Empty} {x y : univA.El a} (h : MclHF.U.V (MclHF.eqv a a x y)) : x = y :=
  groot_inj hcyA_inj a x y ((mkA_V _).mp h)

theorem MclH_model : MclHF.IsModelPIm :=
  MclHF.model_of_equiv (fun _ _ => mkA_V _) (fun _ _ => (mkA_V _).mpr rfl)
    (fun _ _ _ _ h => (mkA_V _).mpr ((mkA_V _).mp h).symm)
    (fun _ _ _ _ _ _ h1 h2 => (mkA_V _).mpr (((mkA_V _).mp h1).trans ((mkA_V _).mp h2)))

theorem MclH_topF {n : Nat} {Γ : Ctx n} (ρ : MclHF.U.TEnv n) (env : MclHF.U.Env Γ ρ) :
    MclHF.eval (topF : Fm Γ) ρ env = none :=
  MclHF.holds_topF ρ env ⟨some true, fun h => nomatch (h : (some true : Option Bool) = none)⟩

theorem MclH_LLEqv : MclHF.Valid LLEqv := by
  intro ρ env
  refine (MclHF.holds_tall _ _ _).mpr fun a => ?_
  refine (MclHF.holds_all _ _ _ _).mpr fun x => (MclHF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MclHF.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (MclHF.holds_all _ _ _ _).mpr fun G => (MclHF.holds_imp _ _ _ _).mpr fun hGx => ?_
  have h := MclH_eq ((MclHF.holds_eqv _ _ _ _ _ _).mp hxy)
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans ((heq_of_eq h).trans (cast_heq _ _)))
  subst e
  exact hGx

theorem MclH_Hae : MclHF.Valid Hae := by
  intro ρ env
  refine (MclHF.holds_tall _ _ _).mpr fun a => (MclHF.holds_all _ _ _ _).mpr fun x => ?_
  refine (MclHF.holds_eqv _ _ _ _ _ _).mpr ((mkA_V _).mpr (groot_hae hcyA_inj a x _ ?_))
  funext y
  show mkA (rootA a y = rootA a x) = mkA (y = x)
  exact congrArg mkA (propext ⟨fun h => groot_inj hcyA_inj a y x h, fun h => h ▸ rfl⟩)

theorem MclH_Collapse : MclHF.Valid Collapse := by
  intro ρ env
  refine (MclHF.holds_all _ _ _ _).mpr fun p => (MclHF.holds_imp _ _ _ _).mpr fun hp => ?_
  refine (MclHF.holds_eqv_t _ _ _ _).mpr ((mkA_V _).mpr ?_)
  have hp' : p = none := hp
  have et := MclH_topF (Γ := Ctx.nil.ext tyT) ρ (env, p)
  exact congrArg (fun q => (⟨.t, q⟩ : Σ b : Code univA.Base, univA.El b)) (hp'.trans et.symm)

theorem MclH_not_PropExt : ¬ MclHF.Valid PropExt := fun h => by
  have h0 := (MclHF.holds_all _ _ _ _).mp ((MclHF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (some true))
    (some false)
  have h1 := (MclHF.holds_imp _ _ _ _).mp h0 ((MclHF.holds_iff _ _ _ _).mpr
    (Iff.intro (fun (h : (some true : Option Bool) = none) => nomatch h)
      (fun (h : (some false : Option Bool) = none) => nomatch h)))
  have e := (mkA_V _).mp ((MclHF.holds_eqv_t _ _ _ _).mp h1)
  have e2 : (some true : Option Bool) = some false := eq_of_heq (Sigma.mk.inj e).2
  cases e2

end Al

end PIF
