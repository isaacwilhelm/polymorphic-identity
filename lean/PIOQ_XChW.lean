import PIBF
import PIOQ_KIE

/-!
# A Kripke model of PI⁻ in which Functional Choice and WCong fail, together with Cantor, `⊤ ≢ ⊥`,
# Truth, Inj≈, Recovery, ND≈, ND× and LL≡/≈

`𝔐_k,chw`: three worlds `0, 1, 2`; the actual world `0` sees all three, and `1` and `2` see only
themselves. Entities are booleans, identical at a world just when equal. There is one base type
`D`, a copy of `t` (its items are sets of worlds, identical at a world when they agree at every
world it sees). Every type exists at every world.

* `≈`: at the actual world, sameness of type once `e → D` is replaced by `e → t`; so
  `e → t ≈ e → D`, but not `t ≈ D` (Inj≈ and Recovery fail). At worlds `1` and `2`, sameness of
  type once `D` is replaced by `t`; so `t ≈ D` there (ND≈ fails).
* `≡`: items are identified at a world when their types are `≈` there and they correspond there
  (after `D` is replaced by `t`). Besides that, at the actual world only, all the *junk* is
  identified: the two constant propositions `⊤` and `⊥`, every item of `e → e`, and every item of
  `(e → e) → t`. So `⊤ ≡ ⊥` (`⊤ ≢ ⊥`, Truth and T fail); each property of items of `e → e` is
  identified with an item of `e → e` (Cantor fails); the constant functions to `⊤` and to the
  proposition true just at world `1`, of type `(e → e) → t`, are identified, but their values are
  not (WCong fails).
* `□φ` (that is, `φ ≡ ⊤`) is true at the actual world just when `φ` is true at every world or
  false at every world. ND× fails: `⊤` and the proposition true just at world `1` are distinct at
  the actual world but not at world `1`.
* An item of `t → e` at the actual world must respect agreement of propositions at world `1` and at
  world `2`, so it is constant: Functional Choice fails (as in `𝔐_k,ie`).
* With `P := λγ.λz. ∀_{γ→t} F (F ≡ λp.p → F z)`, `P_t ⊤` holds but `P_t ⊥` does not, though
  `⊤ ≡ ⊥`: LL≡/≈ fails.

The identity axioms of PI⁻ hold at every world, by the fundamental lemma of the Kripke semantics:
the admissible relations are the correspondences between types with one image, and the junk is
closed under them.
-/
set_option autoImplicit false

namespace PIF
namespace Kr
open Tm

/-! ### The universe -/

theorem XCW_Rtrans (u v w : Fin 3) (h1 : u = v ∨ u = 0) (h2 : v = w ∨ v = 0) : u = w ∨ u = 0 := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr h1

/-- Identity at a world of items of `D`: agreement at every world it sees. -/
def XCW_rb (w : Fin 3) (_ : Unit) (p q : Fin 3 → Prop) : Prop := ∀ v, (w = v ∨ w = 0) → (p v ↔ q v)

def XCW_U : Univ where
  W := Fin 3
  w0 := 0
  R := fun w u => w = u ∨ w = 0
  Rrefl := fun _ => Or.inl rfl
  Rtrans := XCW_Rtrans
  E := Bool
  Base := Unit
  B := fun _ => Fin 3 → Prop
  neE := ⟨true⟩
  neB := fun _ => ⟨fun _ => True⟩
  re := fun _ x y => x = y
  rb := XCW_rb
  re_refl := fun _ _ => rfl
  re_symm := fun _ _ _ h => h.symm
  re_trans := fun _ _ _ _ h1 h2 => h1.trans h2
  re_mono := fun _ _ _ _ _ h => h
  rb_refl := fun _ _ _ _ _ => Iff.rfl
  rb_symm := fun _ _ _ _ h v hv => (h v hv).symm
  rb_trans := fun _ _ _ _ _ h1 h2 v hv => (h1 v hv).trans (h2 v hv)
  rb_mono := fun _ _ _ _ _ hwv h u hu => h u (XCW_Rtrans _ _ _ hwv hu)
  D := fun _ _ => True
  D_e := fun _ => trivial
  D_t := fun _ => trivial
  D_arr := fun _ _ _ _ _ => trivial
  D_mono := fun _ _ _ _ _ => trivial

theorem XCW_R_zero {w v : Fin 3} (h : XCW_U.R w v) (hv : v = 0) : w = 0 := by
  rcases h with rfl | h
  · exact hv
  · exact h

theorem XCW_R_ne {w v : Fin 3} (h : XCW_U.R w v) (hw : w ≠ 0) : v = w := by
  rcases h with rfl | h
  · rfl
  · exact absurd h hw

theorem XCW_one_ne_zero : (1 : Fin 3) ≠ 0 := by decide

/-! ### Correspondence of types: putting `t` for `D` -/

/-- The type got by putting `t` for `D`. -/
def XCW_img : Code Unit → Code Unit
  | .base _ => .t
  | .arr a c => .arr (XCW_img a) (XCW_img c)
  | .e => .e
  | .t => .t

/-- The key at the actual world: `e → D` is replaced by `e → t`, from the inside out. -/
def XCW_sp (x y : Code Unit) : Code Unit := if x = .e ∧ y = .base () then .arr .e .t else .arr x y

def XCW_K : Code Unit → Code Unit
  | .arr a c => XCW_sp (XCW_K a) (XCW_K c)
  | .e => .e
  | .t => .t
  | .base b => .base b

theorem XCW_sp_arr (x y : Code Unit) : ∃ p q, XCW_sp x y = .arr p q := by
  unfold XCW_sp
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem XCW_sp_eq {x y p q : Code Unit} (h : XCW_sp x y = .arr p q) (hpq : p ≠ .e ∨ q ≠ .t) :
    x = p ∧ y = q := by
  unfold XCW_sp at h
  split at h
  · injection h with h1 h2
    subst h1; subst h2
    rcases hpq with h | h <;> exact absurd rfl h
  · injection h with h1 h2
    exact ⟨h1, h2⟩

theorem XCW_K_e {a : Code Unit} (h : XCW_K a = .e) : a = .e := by
  cases a with
  | e => rfl
  | t => exact nomatch h
  | base _ => exact nomatch h
  | arr a c =>
    obtain ⟨p, q, hpq⟩ := XCW_sp_arr (XCW_K a) (XCW_K c)
    exact absurd (hpq.symm.trans h) (fun h' => nomatch h')

theorem XCW_K_t {a : Code Unit} (h : XCW_K a = .t) : a = .t := by
  cases a with
  | t => rfl
  | e => exact nomatch h
  | base _ => exact nomatch h
  | arr a c =>
    obtain ⟨p, q, hpq⟩ := XCW_sp_arr (XCW_K a) (XCW_K c)
    exact absurd (hpq.symm.trans h) (fun h' => nomatch h')

theorem XCW_K_ee {b : Code Unit} (h : XCW_K b = .arr .e .e) : b = .arr .e .e := by
  cases b with
  | arr b1 b2 =>
    have h' : XCW_sp (XCW_K b1) (XCW_K b2) = .arr .e .e := h
    obtain ⟨h1, h2⟩ := XCW_sp_eq h' (Or.inr (fun h => nomatch h))
    rw [XCW_K_e h1, XCW_K_e h2]
  | e => exact nomatch h
  | t => exact nomatch h
  | base _ => exact nomatch h

theorem XCW_K_eet {b : Code Unit} (h : XCW_K b = .arr (.arr .e .e) .t) : b = .arr (.arr .e .e) .t := by
  cases b with
  | arr b1 b2 =>
    have h' : XCW_sp (XCW_K b1) (XCW_K b2) = .arr (.arr .e .e) .t := h
    obtain ⟨h1, h2⟩ := XCW_sp_eq h' (Or.inl (fun h => nomatch h))
    rw [XCW_K_ee h1, XCW_K_t h2]
  | e => exact nomatch h
  | t => exact nomatch h
  | base _ => exact nomatch h

theorem XCW_K_ee_val : XCW_K (.arr .e .e) = .arr .e .e := by decide
theorem XCW_K_eet_val : XCW_K (.arr (.arr .e .e) .t) = .arr (.arr .e .e) .t := by decide

theorem XCW_img_e {a : Code Unit} (h : XCW_img a = .e) : a = .e := by
  cases a with
  | e => rfl
  | t => exact nomatch h
  | base _ => exact nomatch h
  | arr _ _ => exact nomatch h

theorem XCW_img_t {a : Code Unit} (h : XCW_img a = .t) : a = .t ∨ a = .base () := by
  cases a with
  | t => exact Or.inl rfl
  | e => exact nomatch h
  | base b => exact Or.inr rfl
  | arr _ _ => exact nomatch h

theorem XCW_img_base {a : Code Unit} {b : Unit} (h : XCW_img a = .base b) : False := by
  cases a with
  | base _ => exact nomatch h
  | e => exact nomatch h
  | t => exact nomatch h
  | arr _ _ => exact nomatch h

theorem XCW_img_arr {a k1 k2 : Code Unit} (h : XCW_img a = .arr k1 k2) :
    ∃ a1 a2, a = .arr a1 a2 ∧ XCW_img a1 = k1 ∧ XCW_img a2 = k2 := by
  cases a with
  | arr a1 a2 => injection h with h1 h2; exact ⟨a1, a2, rfl, h1, h2⟩
  | e => exact nomatch h
  | t => exact nomatch h
  | base _ => exact nomatch h

/-- Correspondence at a world, between items of types with the same image. -/
def XCW_CR : (a b : Code Unit) → Fin 3 → XCW_U.El a → XCW_U.El b → Prop
  | .e, .e => fun _ x y => x = y
  | .t, .t => fun w p q => ∀ v, XCW_U.R w v → (p v ↔ q v)
  | .t, .base _ => fun w p q => ∀ v, XCW_U.R w v → (p v ↔ q v)
  | .base _, .t => fun w p q => ∀ v, XCW_U.R w v → (p v ↔ q v)
  | .base _, .base _ => fun w p q => ∀ v, XCW_U.R w v → (p v ↔ q v)
  | .arr a c, .arr b d => fun w f g => ∀ v, XCW_U.R w v → ∀ x y, XCW_CR a b v x y → XCW_CR c d v (f x) (g y)
  | _, _ => fun _ _ _ => False

/-- Transport, both ways, between types with the same image. -/
noncomputable def XCW_Tr : (a b : Code Unit) → (XCW_U.El a → XCW_U.El b) × (XCW_U.El b → XCW_U.El a)
  | .e, .e => (fun x => x, fun x => x)
  | .t, .t => (fun p => p, fun p => p)
  | .t, .base _ => (fun p => p, fun p => p)
  | .base _, .t => (fun p => p, fun p => p)
  | .base _, .base _ => (fun p => p, fun p => p)
  | .arr a c, .arr b d =>
      (fun f y => (XCW_Tr c d).1 (f ((XCW_Tr a b).2 y)), fun g x => (XCW_Tr c d).2 (g ((XCW_Tr a b).1 x)))
  | a, b => (fun _ => Classical.choose (XCW_U.adm_nonempty b), fun _ => Classical.choose (XCW_U.adm_nonempty a))

noncomputable abbrev XCW_Tf (a b : Code Unit) : XCW_U.El a → XCW_U.El b := (XCW_Tr a b).1
noncomputable abbrev XCW_Tg (a b : Code Unit) : XCW_U.El b → XCW_U.El a := (XCW_Tr a b).2

theorem XCW_CR_diag : ∀ (a : Code Unit) (w : Fin 3) (x y : XCW_U.El a), XCW_U.rel a w x y ↔ XCW_CR a a w x y
  | .e, _, _, _ => Iff.rfl
  | .t, _, _, _ => Iff.rfl
  | .base _, _, _, _ => Iff.rfl
  | .arr a c, _, _, _ => forall_congr' fun v => imp_congr Iff.rfl (forall_congr' fun x => forall_congr' fun y =>
      imp_congr (XCW_CR_diag a v x y) (XCW_CR_diag c v _ _))

set_option maxHeartbeats 4000000 in
/-- Correspondence between types with one image is symmetric, transitive and persistent, and
transport takes each item to one corresponding to it. -/
theorem XCW_shape : ∀ k : Code Unit,
    (∀ a b, XCW_img a = k → XCW_img b = k → ∀ w x y, XCW_CR a b w x y → XCW_CR b a w y x) ∧
    (∀ a b c, XCW_img a = k → XCW_img b = k → XCW_img c = k → ∀ w x y z, XCW_CR a b w x y →
      XCW_CR b c w y z → XCW_CR a c w x z) ∧
    (∀ a b, XCW_img a = k → XCW_img b = k → ∀ w x, XCW_CR a a w x x →
      XCW_CR a b w x (XCW_Tf a b x) ∧ XCW_CR b b w (XCW_Tf a b x) (XCW_Tf a b x)) ∧
    (∀ a b, XCW_img a = k → XCW_img b = k → ∀ w y, XCW_CR b b w y y →
      XCW_CR a b w (XCW_Tg a b y) y ∧ XCW_CR a a w (XCW_Tg a b y) (XCW_Tg a b y)) ∧
    (∀ a b, XCW_img a = k → XCW_img b = k → ∀ w v x y, XCW_U.R w v → XCW_CR a b w x y → XCW_CR a b v x y) := by
  intro k
  induction k with
  | e =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b ha hb w x y h
      have e1 := XCW_img_e ha; have e2 := XCW_img_e hb; subst e1; subst e2
      exact Eq.symm h
    · intro a b c ha hb hc w x y z h1 h2
      have e1 := XCW_img_e ha; have e2 := XCW_img_e hb; have e3 := XCW_img_e hc; subst e1; subst e2; subst e3
      exact Eq.trans h1 h2
    · intro a b ha hb w x _
      have e1 := XCW_img_e ha; have e2 := XCW_img_e hb; subst e1; subst e2
      exact ⟨rfl, rfl⟩
    · intro a b ha hb w x _
      have e1 := XCW_img_e ha; have e2 := XCW_img_e hb; subst e1; subst e2
      exact ⟨rfl, rfl⟩
    · intro a b ha hb w v x y _ h
      have e1 := XCW_img_e ha; have e2 := XCW_img_e hb; subst e1; subst e2
      exact h
  | t =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b ha hb w x y h
      rcases XCW_img_t ha with rfl | rfl <;> rcases XCW_img_t hb with rfl | rfl <;>
        exact fun v hv => (h v hv).symm
    · intro a b c ha hb hc w x y z h1 h2
      rcases XCW_img_t ha with rfl | rfl <;> rcases XCW_img_t hb with rfl | rfl <;>
        rcases XCW_img_t hc with rfl | rfl <;> exact fun v hv => (h1 v hv).trans (h2 v hv)
    · intro a b ha hb w x hx
      rcases XCW_img_t ha with rfl | rfl <;> rcases XCW_img_t hb with rfl | rfl <;> exact ⟨hx, hx⟩
    · intro a b ha hb w x hx
      rcases XCW_img_t ha with rfl | rfl <;> rcases XCW_img_t hb with rfl | rfl <;> exact ⟨hx, hx⟩
    · intro a b ha hb w v x y hv h
      rcases XCW_img_t ha with rfl | rfl <;> rcases XCW_img_t hb with rfl | rfl <;>
        exact fun u hu => h u (XCW_Rtrans _ _ _ hv hu)
  | base b =>
    exact ⟨fun a _ ha => (XCW_img_base ha).elim, fun a _ _ ha => (XCW_img_base ha).elim,
      fun a _ ha => (XCW_img_base ha).elim, fun a _ ha => (XCW_img_base ha).elim,
      fun a _ ha => (XCW_img_base ha).elim⟩
  | arr k1 k2 ih1 ih2 =>
    obtain ⟨S1, R1, P1, Q1, _⟩ := ih1
    obtain ⟨S2, R2, P2, Q2, _⟩ := ih2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b ha hb w f g h
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XCW_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XCW_img_arr hb
      intro v hv x y hxy
      exact S2 a2 b2 ha2 hb2 v _ _ (h v hv y x (S1 b1 a1 hb1 ha1 v x y hxy))
    · intro a b c ha hb hc w f g h hfg hgh
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XCW_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XCW_img_arr hb
      obtain ⟨c1, c2, rfl, hc1, hc2⟩ := XCW_img_arr hc
      intro v hv x z hxz
      have hzz : XCW_CR c1 c1 v z z := R1 c1 a1 c1 hc1 ha1 hc1 v z x z (S1 a1 c1 ha1 hc1 v x z hxz) hxz
      obtain ⟨hyz, _⟩ := Q1 b1 c1 hb1 hc1 v z hzz
      have hxy : XCW_CR a1 b1 v x (XCW_Tg b1 c1 z) :=
        R1 a1 c1 b1 ha1 hc1 hb1 v x z _ hxz (S1 b1 c1 hb1 hc1 v _ z hyz)
      exact R2 a2 b2 c2 ha2 hb2 hc2 v _ _ _ (hfg v hv x _ hxy) (hgh v hv _ z hyz)
    · intro a b ha hb w f hf
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XCW_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XCW_img_arr hb
      refine ⟨?_, ?_⟩
      · intro v hv x y hxy
        have hyy : XCW_CR b1 b1 v y y := R1 b1 a1 b1 hb1 ha1 hb1 v y x y (S1 a1 b1 ha1 hb1 v x y hxy) hxy
        obtain ⟨hTy, hTT⟩ := Q1 a1 b1 ha1 hb1 v y hyy
        have hxT : XCW_CR a1 a1 v x (XCW_Tg a1 b1 y) :=
          R1 a1 b1 a1 ha1 hb1 ha1 v x y _ hxy (S1 a1 b1 ha1 hb1 v _ y hTy)
        have hfx := hf v hv x _ hxT
        obtain ⟨h1, _⟩ := P2 a2 b2 ha2 hb2 v _ (hf v hv _ _ hTT)
        exact R2 a2 a2 b2 ha2 ha2 hb2 v _ _ _ hfx h1
      · intro v hv y y' hyy'
        have hyy : XCW_CR b1 b1 v y y := R1 b1 b1 b1 hb1 hb1 hb1 v y y' y hyy' (S1 b1 b1 hb1 hb1 v y y' hyy')
        have hy'y' : XCW_CR b1 b1 v y' y' :=
          R1 b1 b1 b1 hb1 hb1 hb1 v y' y y' (S1 b1 b1 hb1 hb1 v y y' hyy') hyy'
        obtain ⟨hTy, hTT⟩ := Q1 a1 b1 ha1 hb1 v y hyy
        obtain ⟨hTy', hT'T'⟩ := Q1 a1 b1 ha1 hb1 v y' hy'y'
        have hTyy : XCW_CR a1 a1 v (XCW_Tg a1 b1 y) (XCW_Tg a1 b1 y') :=
          R1 a1 b1 a1 ha1 hb1 ha1 v _ y _ hTy (R1 b1 b1 a1 hb1 hb1 ha1 v y y' _ hyy' (S1 a1 b1 ha1 hb1 v _ y' hTy'))
        obtain ⟨g1, _⟩ := P2 a2 b2 ha2 hb2 v _ (hf v hv _ _ hTT)
        obtain ⟨g2, _⟩ := P2 a2 b2 ha2 hb2 v _ (hf v hv _ _ hT'T')
        exact R2 b2 a2 b2 hb2 ha2 hb2 v _ _ _ (S2 a2 b2 ha2 hb2 v _ _ g1)
          (R2 a2 a2 b2 ha2 ha2 hb2 v _ _ _ (hf v hv _ _ hTyy) g2)
    · intro a b ha hb w g hg
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XCW_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XCW_img_arr hb
      refine ⟨?_, ?_⟩
      · intro v hv x y hxy
        have hxx : XCW_CR a1 a1 v x x := R1 a1 b1 a1 ha1 hb1 ha1 v x y x hxy (S1 a1 b1 ha1 hb1 v x y hxy)
        obtain ⟨hxT, hTT⟩ := P1 a1 b1 ha1 hb1 v x hxx
        have hTy : XCW_CR b1 b1 v (XCW_Tf a1 b1 x) y :=
          R1 b1 a1 b1 hb1 ha1 hb1 v _ x y (S1 a1 b1 ha1 hb1 v x _ hxT) hxy
        have hgy := hg v hv _ y hTy
        obtain ⟨h1, _⟩ := Q2 a2 b2 ha2 hb2 v _ (hg v hv _ _ hTT)
        exact R2 a2 b2 b2 ha2 hb2 hb2 v _ _ _ h1 hgy
      · intro v hv x x' hxx'
        have hxx : XCW_CR a1 a1 v x x := R1 a1 a1 a1 ha1 ha1 ha1 v x x' x hxx' (S1 a1 a1 ha1 ha1 v x x' hxx')
        have hx'x' : XCW_CR a1 a1 v x' x' :=
          R1 a1 a1 a1 ha1 ha1 ha1 v x' x x' (S1 a1 a1 ha1 ha1 v x x' hxx') hxx'
        obtain ⟨hxT, hTT⟩ := P1 a1 b1 ha1 hb1 v x hxx
        obtain ⟨hx'T, hT'T'⟩ := P1 a1 b1 ha1 hb1 v x' hx'x'
        have hTxx : XCW_CR b1 b1 v (XCW_Tf a1 b1 x) (XCW_Tf a1 b1 x') :=
          R1 b1 a1 b1 hb1 ha1 hb1 v _ x _ (S1 a1 b1 ha1 hb1 v x _ hxT) (R1 a1 a1 b1 ha1 ha1 hb1 v x x' _ hxx' hx'T)
        obtain ⟨g1, _⟩ := Q2 a2 b2 ha2 hb2 v _ (hg v hv _ _ hTT)
        obtain ⟨g2, _⟩ := Q2 a2 b2 ha2 hb2 v _ (hg v hv _ _ hT'T')
        exact R2 a2 b2 a2 ha2 hb2 ha2 v _ _ _ g1
          (R2 b2 b2 a2 hb2 hb2 ha2 v _ _ _ (hg v hv _ _ hTxx) (S2 a2 b2 ha2 hb2 v _ _ g2))
    · intro a b ha hb w v f g hv h
      obtain ⟨a1, a2, rfl, _, _⟩ := XCW_img_arr ha
      obtain ⟨b1, b2, rfl, _, _⟩ := XCW_img_arr hb
      exact fun u hu => h u (XCW_Rtrans _ _ _ hv hu)

theorem XCW_CR_symm {a b : Code Unit} (h : XCW_img a = XCW_img b) {w : Fin 3} {x : XCW_U.El a}
    {y : XCW_U.El b} (hxy : XCW_CR a b w x y) : XCW_CR b a w y x :=
  (XCW_shape (XCW_img a)).1 a b rfl h.symm w x y hxy

theorem XCW_CR_trans {a b c : Code Unit} (h1 : XCW_img a = XCW_img b) (h2 : XCW_img b = XCW_img c) {w : Fin 3}
    {x : XCW_U.El a} {y : XCW_U.El b} {z : XCW_U.El c} (hxy : XCW_CR a b w x y) (hyz : XCW_CR b c w y z) :
    XCW_CR a c w x z :=
  (XCW_shape (XCW_img a)).2.1 a b c rfl h1.symm (h1.trans h2).symm w x y z hxy hyz

theorem XCW_CR_mono {a b : Code Unit} (h : XCW_img a = XCW_img b) {w v : Fin 3} {x : XCW_U.El a}
    {y : XCW_U.El b} (hv : XCW_U.R w v) (hxy : XCW_CR a b w x y) : XCW_CR a b v x y :=
  (XCW_shape (XCW_img a)).2.2.2.2 a b rfl h.symm w v x y hv hxy

/-! ### `≈`, and identity apart from the junk -/

/-- `≈` at a world: at the actual world, sameness of key; elsewhere, sameness of image. -/
def XCW_teq (a b : Code Unit) (w : Fin 3) : Prop := (w = 0 → XCW_K a = XCW_K b) ∧ XCW_img a = XCW_img b

/-- Identity apart from the junk: `≈`-types and corresponding items. -/
def XCW_beqv (a b : Code Unit) (x : XCW_U.El a) (y : XCW_U.El b) (w : Fin 3) : Prop :=
  XCW_teq a b w ∧ XCW_CR a b w x y

theorem XCW_beqv_imp {a a' b b' : Code Unit} {u : Fin 3} {x : XCW_U.El a} {x' : XCW_U.El a'} {y : XCW_U.El b}
    {y' : XCW_U.El b'} (ia : XCW_img a = XCW_img a') (ib : XCW_img b = XCW_img b')
    (ca : u = 0 → XCW_K a = XCW_K a') (cb : u = 0 → XCW_K b = XCW_K b')
    (hx : XCW_CR a a' u x x') (hy : XCW_CR b b' u y y') : XCW_beqv a b x y u → XCW_beqv a' b' x' y' u := by
  rintro ⟨⟨h1, h2⟩, h3⟩
  refine ⟨⟨fun hu => (ca hu).symm.trans ((h1 hu).trans (cb hu)), ia.symm.trans (h2.trans ib)⟩, ?_⟩
  exact XCW_CR_trans (ia.symm.trans h2) ib (XCW_CR_trans ia.symm h2 (XCW_CR_symm ia hx) h3) hy

theorem XCW_beqv_iff {a a' b b' : Code Unit} {u : Fin 3} {x : XCW_U.El a} {x' : XCW_U.El a'} {y : XCW_U.El b}
    {y' : XCW_U.El b'} (ia : XCW_img a = XCW_img a') (ib : XCW_img b = XCW_img b')
    (ca : u = 0 → XCW_K a = XCW_K a') (cb : u = 0 → XCW_K b = XCW_K b')
    (hx : XCW_CR a a' u x x') (hy : XCW_CR b b' u y y') : XCW_beqv a b x y u ↔ XCW_beqv a' b' x' y' u :=
  ⟨XCW_beqv_imp ia ib ca cb hx hy, XCW_beqv_imp ia.symm ib.symm (fun hu => (ca hu).symm) (fun hu => (cb hu).symm)
    (XCW_CR_symm ia hx) (XCW_CR_symm ib hy)⟩

theorem XCW_beqv_symm {a b : Code Unit} {x : XCW_U.El a} {y : XCW_U.El b} {w : Fin 3} (h : XCW_beqv a b x y w) :
    XCW_beqv b a y x w :=
  ⟨⟨fun hw => (h.1.1 hw).symm, h.1.2.symm⟩, XCW_CR_symm h.1.2 h.2⟩

theorem XCW_beqv_trans {a b c : Code Unit} {x : XCW_U.El a} {y : XCW_U.El b} {z : XCW_U.El c} {w : Fin 3}
    (h1 : XCW_beqv a b x y w) (h2 : XCW_beqv b c y z w) : XCW_beqv a c x z w :=
  ⟨⟨fun hw => (h1.1.1 hw).trans (h2.1.1 hw), h1.1.2.trans h2.1.2⟩, XCW_CR_trans h1.1.2 h2.1.2 h1.2 h2.2⟩

theorem XCW_beqv_same (a : Code Unit) (x y : XCW_U.El a) (w : Fin 3) : XCW_beqv a a x y w ↔ XCW_U.rel a w x y :=
  ⟨fun h => (XCW_CR_diag a w x y).mpr h.2, fun h => ⟨⟨fun _ => rfl, rfl⟩, (XCW_CR_diag a w x y).mp h⟩⟩

/-! ### The junk -/

/-- A proposition true at every world or false at every world. -/
def XCW_const (p : Fin 3 → Prop) : Prop := (∀ v, p v) ∨ (∀ v, ¬ p v)

/-- The junk of type `t`: the constant propositions. -/
def XCW_Jt : (a : Code Unit) → XCW_U.El a → Prop
  | .t => fun p => XCW_const p
  | _ => fun _ => False

/-- The junk: constant propositions, and all items of `e → e` and of `(e → e) → t`. -/
def XCW_J (a : Code Unit) (x : XCW_U.El a) : Prop :=
  XCW_Jt a x ∨ a = .arr .e .e ∨ a = .arr (.arr .e .e) .t

theorem XCW_J_e (x : XCW_U.El .e) : ¬ XCW_J .e x := by
  rintro (h | h | h)
  · exact h
  · exact nomatch h
  · exact nomatch h

theorem XCW_J_t (p : XCW_U.El .t) : XCW_J .t p ↔ XCW_const p :=
  ⟨fun h => h.elim id (fun h => h.elim (fun h => nomatch h) (fun h => nomatch h)), fun h => Or.inl h⟩

/-- The junk is closed under identity at the actual world. -/
theorem XCW_J_of_beqv {a b : Code Unit} {x : XCW_U.El a} {y : XCW_U.El b} (h : XCW_beqv a b x y 0)
    (hx : XCW_J a x) : XCW_J b y := by
  obtain ⟨⟨hk, _⟩, hc⟩ := h
  have hk' : XCW_K a = XCW_K b := hk rfl
  rcases hx with hj | rfl | rfl
  · cases a with
    | t =>
      have eb : b = .t := XCW_K_t hk'.symm
      subst eb
      have hc' : ∀ v, x v ↔ y v := fun v => hc v (Or.inr rfl)
      refine Or.inl ?_
      rcases (hj : XCW_const x) with h | h
      · exact Or.inl fun v => (hc' v).mp (h v)
      · exact Or.inr fun v hv => h v ((hc' v).mpr hv)
    | e => exact (hj : False).elim
    | base _ => exact (hj : False).elim
    | arr _ _ => exact (hj : False).elim
  · exact Or.inr (Or.inl (XCW_K_ee (hk'.symm.trans XCW_K_ee_val)))
  · exact Or.inr (Or.inr (XCW_K_eet (hk'.symm.trans XCW_K_eet_val)))

theorem XCW_J_iff {a b : Code Unit} {x : XCW_U.El a} {y : XCW_U.El b} (h : XCW_beqv a b x y 0) :
    XCW_J a x ↔ XCW_J b y :=
  ⟨XCW_J_of_beqv h, XCW_J_of_beqv (XCW_beqv_symm h)⟩

/-! ### Identity -/

/-- Identity at a world: `≈`-types and corresponding items, together with the junk, at the actual
world. -/
def XCW_eqv (a b : Code Unit) (x : XCW_U.El a) (y : XCW_U.El b) (w : Fin 3) : Prop :=
  XCW_beqv a b x y w ∨ (w = 0 ∧ XCW_J a x ∧ XCW_J b y)

theorem XCW_eqv_symm {a b : Code Unit} {x : XCW_U.El a} {y : XCW_U.El b} {w : Fin 3} (h : XCW_eqv a b x y w) :
    XCW_eqv b a y x w := by
  rcases h with h | ⟨hw, ja, jb⟩
  · exact Or.inl (XCW_beqv_symm h)
  · exact Or.inr ⟨hw, jb, ja⟩

theorem XCW_eqv_trans {a b c : Code Unit} {x : XCW_U.El a} {y : XCW_U.El b} {z : XCW_U.El c} {w : Fin 3}
    (h1 : XCW_eqv a b x y w) (h2 : XCW_eqv b c y z w) : XCW_eqv a c x z w := by
  rcases h1 with h1 | ⟨hw, ja, jb⟩ <;> rcases h2 with h2 | ⟨hw', jb', jc⟩
  · exact Or.inl (XCW_beqv_trans h1 h2)
  · subst hw'
    exact Or.inr ⟨rfl, XCW_J_of_beqv (XCW_beqv_symm h1) jb', jc⟩
  · subst hw
    exact Or.inr ⟨rfl, ja, XCW_J_of_beqv h2 jb⟩
  · exact Or.inr ⟨hw, ja, jc⟩

theorem XCW_eqv_iff {a a' b b' : Code Unit} {u : Fin 3} {x : XCW_U.El a} {x' : XCW_U.El a'} {y : XCW_U.El b}
    {y' : XCW_U.El b'} (hb : XCW_beqv a b x y u ↔ XCW_beqv a' b' x' y' u)
    (hx : u = 0 → XCW_beqv a a' x x' 0) (hy : u = 0 → XCW_beqv b b' y y' 0) :
    XCW_eqv a b x y u ↔ XCW_eqv a' b' x' y' u := by
  constructor
  · rintro (h | ⟨hu, ja, jb⟩)
    · exact Or.inl (hb.mp h)
    · exact Or.inr ⟨hu, (XCW_J_iff (hx hu)).mp ja, (XCW_J_iff (hy hu)).mp jb⟩
  · rintro (h | ⟨hu, ja, jb⟩)
    · exact Or.inl (hb.mpr h)
    · exact Or.inr ⟨hu, (XCW_J_iff (hx hu)).mpr ja, (XCW_J_iff (hy hu)).mpr jb⟩

theorem XCW_eqv_ne {a b : Code Unit} {x : XCW_U.El a} {y : XCW_U.El b} {w : Fin 3} (hw : w ≠ 0) :
    XCW_eqv a b x y w ↔ XCW_beqv a b x y w :=
  ⟨fun h => h.elim id (fun h => absurd h.1 hw), Or.inl⟩

/-- `𝔐_k,chw`. -/
def XCW_F : Frame where
  U := XCW_U
  eqv := XCW_eqv
  teq := XCW_teq
  eqv_resp := fun u a b x x' y y' hx hy =>
    XCW_eqv_iff (XCW_beqv_iff rfl rfl (fun _ => rfl) (fun _ => rfl) ((XCW_CR_diag a u x x').mp hx)
        ((XCW_CR_diag b u y y').mp hy))
      (fun hu => by subst hu; exact (XCW_beqv_same a x x' 0).mpr hx)
      (fun hu => by subst hu; exact (XCW_beqv_same b y y' 0).mpr hy)

/-- The admissible relations: correspondence between types of one image, at the worlds at which the
two types have the same key. -/
def XCW_Adm (w : Fin 3) (a a' : Code Unit) (S : Fin 3 → XCW_U.El a → XCW_U.El a' → Prop) : Prop :=
  XCW_img a = XCW_img a' ∧ (∀ v : Fin 3, XCW_U.R w v → v = 0 → XCW_K a = XCW_K a') ∧
    ∀ u x y, S u x y ↔ XCW_CR a a' u x y

def XCW_inv : KInv XCW_F where
  Adm := XCW_Adm
  amono := fun ⟨h1, h2, h3⟩ hv => ⟨h1, fun u hu => h2 u (XCW_Rtrans _ _ _ hv hu), h3⟩
  smono := fun ⟨h1, _, h3⟩ u u' x x' _ hu h => (h3 u' x x').mpr (XCW_CR_mono h1 hu ((h3 u x x').mp h))
  refl := fun _ a => ⟨rfl, fun _ _ _ => rfl, fun u x y => XCW_CR_diag a u x y⟩
  arrow := by
    intro w a a' c c' S T hS hT
    obtain ⟨h1, h2, h3⟩ := hS
    obtain ⟨k1, k2, k3⟩ := hT
    refine ⟨by show Code.arr (XCW_img a) (XCW_img c) = Code.arr (XCW_img a') (XCW_img c'); rw [h1, k1],
      fun v hv hv' => by show XCW_sp (XCW_K a) (XCW_K c) = XCW_sp (XCW_K a') (XCW_K c'); rw [h2 v hv hv', k2 v hv hv'],
      fun u f f' => ?_⟩
    exact forall_congr' fun v => imp_congr Iff.rfl (forall_congr' fun x => forall_congr' fun x' =>
      imp_congr (h3 v x x') (k3 v _ _))
  total := by
    intro w a a' S hS u _ x hx
    obtain ⟨h1, _, h3⟩ := hS
    obtain ⟨hxT, hTT⟩ := (XCW_shape (XCW_img a)).2.2.1 a a' rfl h1.symm u x ((XCW_CR_diag a u x x).mp hx)
    exact ⟨XCW_Tf a a' x, (XCW_CR_diag a' u _ _).mpr hTT, (h3 u x _).mpr hxT⟩
  onto := by
    intro w a a' S hS u _ y hy
    obtain ⟨h1, _, h3⟩ := hS
    obtain ⟨hTy, hTT⟩ := (XCW_shape (XCW_img a)).2.2.2.1 a a' rfl h1.symm u y ((XCW_CR_diag a' u y y).mp hy)
    exact ⟨XCW_Tg a a' y, (XCW_CR_diag a u _ _).mpr hTT, (h3 u _ y).mpr hTy⟩
  teq := by
    intro w a a' b b' S T hS hT u hu
    obtain ⟨h1, h2, _⟩ := hS
    obtain ⟨k1, k2, _⟩ := hT
    constructor
    · rintro ⟨e1, e2⟩
      exact ⟨fun hv => (h2 u hu hv).symm.trans ((e1 hv).trans (k2 u hu hv)), h1.symm.trans (e2.trans k1)⟩
    · rintro ⟨e1, e2⟩
      exact ⟨fun hv => (h2 u hu hv).trans ((e1 hv).trans (k2 u hu hv).symm), h1.trans (e2.trans k1.symm)⟩
  eqv := by
    intro w a a' b b' S T hS hT u hu x x' y y' hx hy
    obtain ⟨h1, h2, h3⟩ := hS
    obtain ⟨k1, k2, k3⟩ := hT
    refine XCW_eqv_iff (XCW_beqv_iff h1 k1 (h2 u hu) (k2 u hu) ((h3 u x x').mp hx) ((k3 u y y').mp hy))
      (fun hu0 => ?_) (fun hu0 => ?_)
    · subst hu0
      exact ⟨⟨fun _ => h2 0 hu rfl, h1⟩, (h3 0 x x').mp hx⟩
    · subst hu0
      exact ⟨⟨fun _ => k2 0 hu rfl, k1⟩, (k3 0 y y').mp hy⟩

/-- `𝔐_k,chw` is a model of PI⁻, at every world. -/
theorem XCW_isModelAt : XCW_F.IsModelAt := by
  obtain ⟨h1, h2, h3⟩ := XCW_F.idAx_of (fun a x w hx => Or.inl ((XCW_beqv_same a x x w).mpr hx))
    (fun _ _ _ _ _ h => XCW_eqv_symm h) (fun _ _ _ _ _ _ _ h1 h2 => XCW_eqv_trans h1 h2)
  refine ⟨h1, h2, h3, XCW_F.refTeq_of fun _ _ => ⟨fun _ => rfl, rfl⟩, ?_⟩
  intro n Γ Q w ρ _ env henv
  refine XCW_F.holdsAt_tall _ _ _ w |>.mpr fun a _ => XCW_F.holdsAt_tall _ _ _ w |>.mpr fun b _ => ?_
  refine (XCW_F.holdsAt_imp _ _ _ _ w).mpr fun hab => ?_
  obtain ⟨e1, e2⟩ := (XCW_F.holdsAt_teq (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env w).mp hab
  refine (XCW_F.holdsAt_imp _ _ _ _ w).mpr fun hq => ?_
  exact XCW_inv.llTeq_at Q w ρ env henv a b (XCW_CR a b)
    (show XCW_Adm w a b (XCW_CR a b) from ⟨e2, fun v hv hv' => e1 (XCW_R_zero hv hv'), fun _ _ _ => Iff.rfl⟩) hq


/-! ### Basic facts -/

theorem XCW_Valid_of {φ : Fm Ctx.nil} (h : XCW_F.HoldsAt φ (fun i => i.elim0) () XCW_U.w0) : XCW_F.Valid φ := by
  intro ρ _ env _
  have e1 : ρ = fun i => i.elim0 := funext fun i => i.elim0
  subst e1
  exact h

/-- Identity of propositions, as a formula. -/
theorem XCW_eqv_tt {n : Nat} {Γ : Ctx n} (φ ψ : Fm Γ) (ρ : XCW_F.U.TEnv n) (env : XCW_F.U.Env Γ ρ) (w : Fin 3) :
    XCW_F.HoldsAt (eqv tyT tyT φ ψ) ρ env w ↔ XCW_eqv .t .t (XCW_F.eval φ ρ env) (XCW_F.eval ψ ρ env) w :=
  XCW_F.holdsAt_eqv tyT tyT φ ψ ρ env w

/-- Identity of propositions at the actual world. -/
theorem XCW_eqv_t0 (p q : Fin 3 → Prop) :
    XCW_eqv .t .t p q 0 ↔ (∀ v, p v ↔ q v) ∨ (XCW_const p ∧ XCW_const q) := by
  constructor
  · rintro (⟨_, h⟩ | ⟨_, hp, hq⟩)
    · exact Or.inl fun v => h v (Or.inr rfl)
    · exact Or.inr ⟨(XCW_J_t p).mp hp, (XCW_J_t q).mp hq⟩
  · rintro (h | ⟨hp, hq⟩)
    · exact Or.inl ⟨⟨fun _ => rfl, rfl⟩, fun v _ => h v⟩
    · exact Or.inr ⟨rfl, (XCW_J_t p).mpr hp, (XCW_J_t q).mpr hq⟩

/-- `□φ` at the actual world: `φ` is true at every world or false at every world. -/
theorem XCW_box0 {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : XCW_F.U.TEnv n) (env : XCW_F.U.Env Γ ρ) :
    XCW_F.HoldsAt (boxF φ) ρ env (0 : Fin 3) ↔
      (∀ v : Fin 3, XCW_F.HoldsAt φ ρ env v) ∨ (∀ v : Fin 3, ¬ XCW_F.HoldsAt φ ρ env v) := by
  refine (XCW_eqv_tt φ topF ρ env 0).trans ?_
  have e : XCW_F.eval (topF : Fm Γ) ρ env = fun _ => True := XCW_F.eval_topF ρ env
  have hT : ∀ v : Fin 3, XCW_F.eval (topF : Fm Γ) ρ env v := fun v => cast (congrFun e v).symm trivial
  constructor
  · intro h
    rcases (XCW_eqv_t0 _ _).mp h with h' | ⟨h', _⟩
    · exact Or.inl fun v => (h' v).mpr (hT v)
    · exact h'
  · rintro (h | h)
    · exact (XCW_eqv_t0 _ _).mpr (Or.inl fun v => ⟨fun _ => hT v, fun _ => h v⟩)
    · exact (XCW_eqv_t0 _ _).mpr (Or.inr ⟨Or.inr h, Or.inl hT⟩)

/-- Identity of propositions depends only on their values. -/
theorem XCW_eqv_t_of {p q p' q' : Fin 3 → Prop} {w : Fin 3} (hp : p = p') (hq : q = q')
    (h : XCW_eqv .t .t p' q' w) : XCW_eqv .t .t p q w := by
  subst hp; subst hq; exact h

/-- The proposition true just at world `1`. -/
abbrev XCW_p1 : Fin 3 → Prop := fun w => w = 1

theorem XCW_p1_nc : ¬ XCW_const XCW_p1 := by
  rintro (h | h)
  · exact absurd (h 0) (by decide)
  · exact h 1 rfl

/-- `⊤ ≡ ⊥` at the actual world. -/
theorem XCW_tb0 : XCW_eqv .t .t (fun _ => True) (fun _ => False) 0 :=
  Or.inr ⟨rfl, (XCW_J_t _).mpr (Or.inl fun _ => trivial), (XCW_J_t _).mpr (Or.inr fun _ h => h)⟩

/-- `⊤ ≢ ⊥` at world `1`. -/
theorem XCW_not_tb1 : ¬ XCW_eqv .t .t (fun _ => True) (fun _ => False) 1 := fun h0 => by
  obtain ⟨_, h⟩ := (XCW_eqv_ne XCW_one_ne_zero).mp h0
  exact (h (1 : Fin 3) (Or.inl rfl)).mp trivial

/-- `⊤` and the proposition true just at world `1` are distinct at the actual world. -/
theorem XCW_not_tp1 : ¬ XCW_eqv .t .t (fun _ => True) XCW_p1 0 := fun h0 => by
  rcases (XCW_eqv_t0 _ _).mp h0 with h | ⟨_, h⟩
  · exact absurd ((h 0).mp trivial) (by decide)
  · exact XCW_p1_nc h

/-- ... but identical at world `1`. -/
theorem XCW_tp1_one : XCW_eqv .t .t (fun _ => True) XCW_p1 1 := by
  refine Or.inl ⟨⟨fun h => absurd h XCW_one_ne_zero, rfl⟩, fun v hv => ?_⟩
  have e : v = (1 : Fin 3) := XCW_R_ne hv XCW_one_ne_zero
  subst e
  exact ⟨fun _ => rfl, fun _ => trivial⟩

/-- The type `e → e`, all of whose items are junk. -/
abbrev XCW_ee : Code Unit := .arr .e .e

def XCW_id : XCW_U.El XCW_ee := fun z => z
def XCW_fT : XCW_U.El (.arr XCW_ee .t) := fun _ _ => True
def XCW_fP : XCW_U.El (.arr XCW_ee .t) := fun _ (w : Fin 3) => w = 1

theorem XCW_id_adm (w : Fin 3) : XCW_U.rel XCW_ee w XCW_id XCW_id := fun _ _ _ _ h => h
theorem XCW_fT_adm (w : Fin 3) : XCW_U.rel (.arr XCW_ee .t) w XCW_fT XCW_fT := fun _ _ _ _ _ _ _ => Iff.rfl
theorem XCW_fP_adm (w : Fin 3) : XCW_U.rel (.arr XCW_ee .t) w XCW_fP XCW_fP := fun _ _ _ _ _ _ _ => Iff.rfl

theorem XCW_J_ee (x : XCW_U.El XCW_ee) : XCW_J XCW_ee x := Or.inr (Or.inl rfl)
theorem XCW_J_eet (x : XCW_U.El (.arr XCW_ee .t)) : XCW_J (.arr XCW_ee .t) x := Or.inr (Or.inr rfl)

/-! ### The congruence principles fail -/

/-- The constant functions to `⊤` and to the proposition true just at world `1`, of type
`(e → e) → t`, are identified (both junk), but their values are not. -/
theorem XCW_not_WCong : ¬ XCW_F.Valid WCong := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp
    ((XCW_F.holdsAt_tall _ _ _ _).mp h XCW_ee trivial) XCW_ee trivial) .t trivial) .t trivial
  have h2 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp
    ((XCW_F.holdsAt_all _ _ _ _ _).mp h1 XCW_fT (XCW_fT_adm _)) XCW_fP (XCW_fP_adm _)) XCW_id (XCW_id_adm _))
    XCW_id (XCW_id_adm _)
  have h3 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h2 ((XCW_F.holdsAt_conj _ _ _ _ _).mpr
    ⟨(XCW_F.holdsAt_conj _ _ _ _ _).mpr ⟨(XCW_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => rfl, rfl⟩,
      (XCW_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => rfl, rfl⟩⟩,
     (XCW_F.holdsAt_conj _ _ _ _ _).mpr ⟨(XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr
       (Or.inr ⟨rfl, XCW_J_eet _, XCW_J_eet _⟩),
      (XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (Or.inr ⟨rfl, XCW_J_ee _, XCW_J_ee _⟩)⟩⟩)
  exact XCW_not_tp1 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mp h3)

theorem XCW_not_Cong : ¬ XCW_F.Valid Cong := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp
    ((XCW_F.holdsAt_tall _ _ _ _).mp h XCW_ee trivial) XCW_ee trivial) .t trivial) .t trivial
  have h2 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp
    ((XCW_F.holdsAt_all _ _ _ _ _).mp h1 XCW_fT (XCW_fT_adm _)) XCW_fP (XCW_fP_adm _)) XCW_id (XCW_id_adm _))
    XCW_id (XCW_id_adm _)
  have h3 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h2 ((XCW_F.holdsAt_conj _ _ _ _ _).mpr
    ⟨(XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (Or.inr ⟨rfl, XCW_J_eet _, XCW_J_eet _⟩),
     (XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (Or.inr ⟨rfl, XCW_J_ee _, XCW_J_ee _⟩)⟩)
  exact XCW_not_tp1 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mp h3)

theorem XCW_not_PCong : ¬ XCW_F.Valid PCong := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp
    ((XCW_F.holdsAt_tall _ _ _ _).mp h XCW_ee trivial) .t trivial) .t trivial
  have h2 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp
    ((XCW_F.holdsAt_all _ _ _ _ _).mp h1 XCW_fT (XCW_fT_adm _)) XCW_fP (XCW_fP_adm _)) XCW_id (XCW_id_adm _)
  have h3 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h2
    ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (Or.inr ⟨rfl, XCW_J_eet _, XCW_J_eet _⟩))
  exact XCW_not_tp1 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mp h3)

/-- The constant functions to `⊤` and to `⊥`, of type `e → t`, agree pointwise up to identity (since
`⊤ ≡ ⊥`), but are not identified. -/
theorem XCW_not_PExt : ¬ XCW_F.Valid PExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp
    ((XCW_F.holdsAt_tall _ _ _ _).mp h .e trivial) .t trivial) .t trivial
  have h2 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp h1
    (fun _ _ => True : XCW_U.El (.arr .e .t)) (fun _ _ _ _ _ _ _ => Iff.rfl))
    (fun _ _ => False : XCW_U.El (.arr .e .t)) (fun _ _ _ _ _ _ _ => Iff.rfl)
  have h3 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h2 ((XCW_F.holdsAt_all _ _ _ _ _).mpr fun _ _ =>
    (XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr XCW_tb0)
  rcases (XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mp h3 with ⟨_, hc⟩ | ⟨_, j, _⟩
  · exact (hc (0 : Fin 3) (Or.inl rfl) true true rfl (0 : Fin 3) (Or.inl rfl)).mp trivial
  · rcases j with j | j | j
    · exact j
    · exact nomatch j
    · exact nomatch j

/-! ### Cantor, `⊤ ≢ ⊥`, Truth -/

/-- Every property of items of `e → e` is identified with an item of `e → e`: all are junk. -/
theorem XCW_not_Cantor : ¬ XCW_F.Valid Cantor := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  obtain ⟨G, _, h1⟩ := (XCW_F.holdsAt_ex _ _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp h XCW_ee trivial)
  have h2 := (XCW_F.holdsAt_all _ _ _ _ _).mp h1 XCW_id (XCW_id_adm _)
  exact (XCW_F.holdsAt_neg _ _ _ _).mp h2 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr
    (Or.inr ⟨rfl, XCW_J_eet _, XCW_J_ee _⟩))

theorem XCW_not_TopBot : ¬ XCW_F.Valid TopBot := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  exact (XCW_F.holdsAt_neg _ _ _ _).mp h ((XCW_eqv_tt _ _ _ _ _).mpr
    (XCW_eqv_t_of (XCW_F.eval_topF _ _) (XCW_F.eval_botF _ _) XCW_tb0))

theorem XCW_not_Truth : ¬ XCW_F.Valid Truth := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp h (fun _ => True)
    (fun _ _ => Iff.rfl)) (fun _ => False) (fun _ _ => Iff.rfl)
  have h2 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr XCW_tb0)
  exact (XCW_F.holdsAt_imp _ _ _ _ _).mp h2 trivial

/-- `⊥` is necessary at the actual world, but not true. -/
theorem XCW_not_TAx : ¬ XCW_F.Valid TAx := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_all _ _ _ _ _).mp h (fun _ => False) (fun _ _ => Iff.rfl)
  exact (XCW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCW_box0 _ _ _).mpr (Or.inr fun _ h => h))

theorem XCW_not_LLEqv : ¬ XCW_F.Valid LLEqv := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp
    ((XCW_F.holdsAt_tall _ _ _ _).mp h .t trivial) (fun _ => True) (fun _ _ => Iff.rfl))
    (fun _ => False) (fun _ _ => Iff.rfl)
  have h2 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr XCW_tb0)
  have h3 := (XCW_F.holdsAt_all _ _ _ _ _).mp h2 (fun p => p : XCW_U.El (.arr .t .t)) (fun _ _ _ _ h => h)
  exact (XCW_F.holdsAt_imp _ _ _ _ _).mp h3 trivial


/-! ### Inj≈, Recovery and ND≈ fail -/

theorem XCW_teq_eD : XCW_teq (.arr .e .t) (.arr .e (.base ())) 0 := ⟨fun _ => by decide, by decide⟩
theorem XCW_not_teq_tD : ¬ XCW_teq .t (.base ()) 0 := fun h => absurd (h.1 rfl) (by decide)
theorem XCW_teq_tD_one : XCW_teq .t (.base ()) 1 := ⟨fun h => absurd h XCW_one_ne_zero, rfl⟩

/-- `e → t ≈ e → D` at the actual world, but not `t ≈ D`. -/
theorem XCW_not_Inj : ¬ XCW_F.Valid Inj := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp
    ((XCW_F.holdsAt_tall _ _ _ _).mp h .e trivial) .e trivial) .t trivial) (.base ()) trivial
  have h2 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCW_F.holdsAt_teq _ _ _ _ _).mpr XCW_teq_eD)
  exact XCW_not_teq_tD ((XCW_F.holdsAt_teq _ _ _ _ _).mp ((XCW_F.holdsAt_conj _ _ _ _ _).mp h2).2)

theorem XCW_not_Recovery : ¬ XCW_F.Valid Recovery := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp
    ((XCW_F.holdsAt_tall _ _ _ _).mp h .e trivial) .e trivial) .t trivial) (.base ()) trivial
  have h2 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCW_F.holdsAt_conj _ _ _ _ _).mpr
    ⟨(XCW_F.holdsAt_teq _ _ _ _ _).mpr XCW_teq_eD, (XCW_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => rfl, rfl⟩⟩)
  exact XCW_not_teq_tD ((XCW_F.holdsAt_teq _ _ _ _ _).mp h2)

/-- `t` and `D` are distinct at the actual world, but `≈` at world `1`. -/
theorem XCW_not_NDTeq : ¬ XCW_F.Valid NDTeq := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp h .t trivial) (.base ()) trivial
  have h2 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCW_F.holdsAt_neg _ _ _ _).mpr fun ht =>
    XCW_not_teq_tD ((XCW_F.holdsAt_teq _ _ _ _ _).mp ht))
  rcases (XCW_box0 _ _ _).mp h2 with h3 | h3
  · exact (XCW_F.holdsAt_neg _ _ _ _).mp (h3 1) ((XCW_F.holdsAt_teq _ _ _ _ _).mpr XCW_teq_tD_one)
  · exact h3 0 ((XCW_F.holdsAt_neg _ _ _ _).mpr fun ht => XCW_not_teq_tD ((XCW_F.holdsAt_teq _ _ _ _ _).mp ht))

/-! ### ND× fails -/

/-- `⊤` and the proposition true just at world `1` are distinct at the actual world, but identical at
world `1`. -/
theorem XCW_not_NDX : ¬ XCW_F.Valid NDX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp h .t trivial) .t trivial
  have h2 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp h1 (fun _ => True)
    (fun _ _ => Iff.rfl)) XCW_p1 (fun _ _ => Iff.rfl)
  have h3 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h2 ((XCW_F.holdsAt_neg _ _ _ _).mpr fun he =>
    XCW_not_tp1 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mp he))
  rcases (XCW_box0 _ _ _).mp h3 with h4 | h4
  · exact (XCW_F.holdsAt_neg _ _ _ _).mp (h4 1) ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr XCW_tp1_one)
  · exact h4 0 ((XCW_F.holdsAt_neg _ _ _ _).mpr fun he => XCW_not_tp1 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mp he))

/-! ### Functional Choice fails -/

/-- `t → e`. -/
abbrev XCW_A : Code Unit := .arr .t .e

theorem XCW_f1_adm : XCW_U.rel XCW_A (1 : Fin 3) f1IE f1IE := by
  intro v hv p q hpq
  have hv' : v = (1 : Fin 3) := XCW_R_ne hv XCW_one_ne_zero
  subst hv'
  have e : p (1 : Fin 3) = q (1 : Fin 3) := propext (hpq (1 : Fin 3) (Or.inl rfl))
  show f1IE p = f1IE q
  unfold f1IE
  rw [e]

theorem XCW_relA_eq {v : Fin 3} {x y : XCW_U.El XCW_A} (h : XCW_U.rel XCW_A v x y) : x = y :=
  funext fun p => h v (XCW_U.Rrefl v) p p (fun _ _ => Iff.rfl)

/-- An item of `t → e` at the actual world is constant. -/
theorem XCW_const_of_adm0 {x : XCW_U.El XCW_A} (h : XCW_U.rel XCW_A (0 : Fin 3) x x) (p q : Fin 3 → Prop) :
    x p = x q := by
  have h1 : x p = x (mixIE p q) := h (1 : Fin 3) (Or.inr rfl) p (mixIE p q) (fun u hu => by
    rcases hu with rfl | hu
    · exact ⟨fun hp => Or.inl ⟨rfl, hp⟩, fun h' => h'.elim (fun h'' => h''.2) (fun h'' => absurd rfl h''.1)⟩
    · exact absurd hu (by decide))
  have h2 : x (mixIE p q) = x q := h (2 : Fin 3) (Or.inr rfl) (mixIE p q) q (fun u hu => by
    rcases hu with rfl | hu
    · exact ⟨fun h' => h'.elim (fun h'' => absurd h''.1 (by decide)) (fun h'' => h''.2),
        fun hq => Or.inr ⟨by decide, hq⟩⟩
    · exact absurd hu (by decide))
  exact h1.trans h2

/-- The relation between a proposition and whether it is true. -/
def XCW_Rch : XCW_U.El (.arr .t (.arr .e .t)) := fun (p : Fin 3 → Prop) (y : Bool) (u : Fin 3) => (y = true ↔ p u)

theorem XCW_Rch_adm : XCW_U.rel (.arr .t (.arr .e .t)) (0 : Fin 3) XCW_Rch XCW_Rch := by
  intro v _ p q hpq v' hv' y y' hyy' u hu
  have e : y = y' := hyy'
  subst e
  exact iff_congr Iff.rfl (hpq u (XCW_U.Rtrans _ _ _ hv' hu))

/-- Each proposition is related to an entity, but no item of `t → e` at the actual world chooses
one: such items are constant. -/
theorem XCW_not_Choice : ¬ XCW_F.Valid Choice := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp
    ((XCW_F.holdsAt_tall _ _ _ _).mp h .t trivial) .e trivial) XCW_Rch XCW_Rch_adm
  have h2 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCW_F.holdsAt_all _ _ _ _ _).mpr fun p _ => by
    refine (XCW_F.holdsAt_ex _ _ _ _ _).mpr ?_
    rcases Classical.em (p (0 : Fin 3)) with hp | hp
    · exact ⟨true, rfl, show (true = true ↔ p (0 : Fin 3)) from ⟨fun _ => hp, fun _ => rfl⟩⟩
    · exact ⟨false, rfl, show (false = true ↔ p (0 : Fin 3)) from
        ⟨fun e => Bool.noConfusion e, fun h => absurd h hp⟩⟩)
  obtain ⟨f, hf, h3⟩ := (XCW_F.holdsAt_ex _ _ _ _ _).mp h2
  have hc := XCW_const_of_adm0 hf
  have h4 : f (fun _ => True) = true ↔ True :=
    (XCW_F.holdsAt_all _ _ _ _ _).mp h3 (fun _ => True) (fun _ _ => Iff.rfl)
  have h5 : f (fun _ => False) = true ↔ False :=
    (XCW_F.holdsAt_all _ _ _ _ _).mp h3 (fun _ => False) (fun _ _ => Iff.rfl)
  exact h5.mp ((hc _ _).symm.trans (h4.mpr trivial))

/-! ### LL≡/≈ and LL≡-Poly fail -/

/-- `λγ.λz:γ. ∀_{γ→t} F (F ≡ λp.p → F z)`. -/
def XCW_PI : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (all tv0.pred (imp (eqv tv0.pred (tyT.arrow tyT) (.var .here) (.lam tyT (.var .here)))
    (.app (.var .here) (.var (.there .here))))))

/-- What `XCW_PI` says of a proposition, at the actual world. -/
def XCW_PIsem (z : Fin 3 → Prop) : Prop :=
  ∀ G : XCW_U.El (.arr .t .t), XCW_U.rel (.arr .t .t) (0 : Fin 3) G G →
    XCW_eqv (.arr .t .t) (.arr .t .t) G (fun p => p) 0 → G z (0 : Fin 3)

set_option maxHeartbeats 4000000 in
theorem XCW_PI_iff1 (x y : Fin 3 → Prop) :
    XCW_F.HoldsAt (.app (.tapp ((XCW_PI.twk.twk.wk tv1).wk tv0) tv1) (.var (.there .here)))
      (scons .t (scons .t (fun i => i.elim0))) (((), x), y) (0 : Fin 3) ↔ XCW_PIsem x := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem XCW_PI_iff0 (x y : Fin 3 → Prop) :
    XCW_F.HoldsAt (.app (.tapp ((XCW_PI.twk.twk.wk tv1).wk tv0) tv0) (.var .here))
      (scons .t (scons .t (fun i => i.elim0))) (((), x), y) (0 : Fin 3) ↔ XCW_PIsem y := Iff.rfl

theorem XCW_PIsem_top : XCW_PIsem (fun _ => True) := by
  intro G _ hG
  rcases hG with ⟨_, hc⟩ | ⟨_, j, _⟩
  · exact (hc (0 : Fin 3) (Or.inl rfl) (fun _ => True) (fun _ => True) (fun _ _ => Iff.rfl)
      (0 : Fin 3) (Or.inl rfl)).mpr trivial
  · rcases j with j | j | j
    · exact j.elim
    · exact nomatch j
    · exact nomatch j

theorem XCW_not_PIsem_bot : ¬ XCW_PIsem (fun _ => False) := fun h =>
  h (fun p => p) (fun _ _ _ _ h => h) (Or.inl ⟨⟨fun _ => rfl, rfl⟩, fun _ _ _ _ h => h⟩)

/-- `⊤ ≡ ⊥`, but `P_t ⊤` and not `P_t ⊥`. -/
theorem XCW_not_Bridge : ¬ XCW_F.Valid (Bridge XCW_PI) := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp h .t trivial) .t trivial
  have h2 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp h1 (fun _ => True)
    (fun _ _ => Iff.rfl)) (fun _ => False) (fun _ _ => Iff.rfl)
  have h3 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h2 ((XCW_F.holdsAt_conj _ _ _ _ _).mpr
    ⟨(XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr XCW_tb0, (XCW_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => rfl, rfl⟩⟩)
  have h4 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h3 ((XCW_PI_iff1 _ _).mpr XCW_PIsem_top)
  exact XCW_not_PIsem_bot ((XCW_PI_iff0 _ _).mp h4)

theorem XCW_not_LLPoly : ¬ XCW_F.Valid (LLPoly XCW_PI) := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp h .t trivial) .t trivial
  have h2 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp h1 (fun _ => True)
    (fun _ _ => Iff.rfl)) (fun _ => False) (fun _ _ => Iff.rfl)
  have h3 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h2 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr XCW_tb0)
  have h4 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h3 ((XCW_PI_iff1 _ _).mpr XCW_PIsem_top)
  exact XCW_not_PIsem_bot ((XCW_PI_iff0 _ _).mp h4)

/-! ### Classicism fails -/

open Derive in
/-- `(⊤ ≡ ⊥) ≡ ⊥` is an instance of Classicism, since PI proves `⊤ ≢ ⊥`. -/
theorem XCW_class_inst : ClassSch (Tm.eqv tyT tyT (Tm.eqv tyT tyT topF botF) botF : Fm Ctx.nil) := by
  refine Or.inl ⟨0, Ctx.nil, Tm.eqv tyT tyT topF botF, botF, ?_, rfl⟩
  have ha : Ent (fun χ => χ = LLEqv) Ctx.nil [] TopBot := Ent.ofProv (d_TopBot rfl)
  exact Ent.toProv (Ent.mp2 (Ent.taut (.imp (.neg (.atom 0)) (.imp (.neg (.atom 1)) (.iff (.atom 0) (.atom 1))))
    (v2 (Tm.eqv tyT tyT topF botF) botF) (fun _ a b => ⟨fun h => absurd h a, fun h => absurd h b⟩)) ha Ent.top)

/-- `⊤ ≡ ⊥` is true at the actual world but not at world `1`, so it is not identified with `⊥`. -/
theorem XCW_not_Class : ¬ ∀ χ, ClassSch χ → XCW_F.Valid χ := fun h => by
  have h0 := h _ XCW_class_inst (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_eqv_tt _ _ _ _ _).mp h0
  have e : ∀ w : Fin 3, XCW_F.eval (Tm.eqv tyT tyT topF botF : Fm Ctx.nil) (fun i => i.elim0) () w ↔
      XCW_eqv .t .t (fun _ => True) (fun _ => False) w := fun w =>
    (XCW_eqv_tt (topF : Fm Ctx.nil) botF (fun i => i.elim0) () w).trans
      ⟨fun h => XCW_eqv_t_of (XCW_F.eval_topF _ _).symm (XCW_F.eval_botF _ _).symm h,
       fun h => XCW_eqv_t_of (XCW_F.eval_topF _ _) (XCW_F.eval_botF _ _) h⟩
  have hB : ∀ w : Fin 3, ¬ XCW_F.eval (botF : Fm Ctx.nil) (fun i => i.elim0) () w := fun w hb =>
    (cast (congrFun (XCW_F.eval_botF (Γ := Ctx.nil) (fun i => i.elim0) ()) w) hb : False)
  rcases (XCW_eqv_t0 _ _).mp h1 with h2 | ⟨h2, _⟩
  · exact hB 0 ((h2 0).mp ((e 0).mpr XCW_tb0))
  · rcases h2 with h2 | h2
    · exact XCW_not_tb1 ((e 1).mp (h2 1))
    · exact h2 0 ((e 0).mpr XCW_tb0)


/-! ### Identity across types -/

theorem XCW_J_tT : XCW_J .t (fun _ => True) := (XCW_J_t _).mpr (Or.inl fun _ => trivial)

/-- `⊤` and the identity function on entities are identified (both junk), though `t ≉ e → e`. -/
theorem XCW_not_Disjoint : ¬ XCW_F.Valid Disjoint := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp h .t trivial) XCW_ee trivial
  have h2 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCW_F.holdsAt_neg _ _ _ _).mpr fun ht =>
    nomatch ((XCW_F.holdsAt_teq _ _ _ _ _).mp ht).2)
  have h3 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp h2 (fun _ => True)
    (fun _ _ => Iff.rfl)) XCW_id (XCW_id_adm _)
  exact (XCW_F.holdsAt_neg _ _ _ _).mp h3 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr
    (Or.inr ⟨rfl, XCW_J_tT, XCW_J_ee _⟩))

/-- No entity is identified with anything of another type. -/
theorem XCW_Slogan : XCW_F.Valid Slogan := by
  refine XCW_Valid_of ?_
  refine (XCW_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XCW_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XCW_F.holdsAt_all _ _ _ _ _).mpr fun y _ => (XCW_F.holdsAt_neg _ _ _ _).mpr fun hxy => ?_
  rcases (XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mp hxy with ⟨⟨_, hi⟩, _⟩ | ⟨_, je, _⟩
  · exact nomatch hi
  · exact XCW_J_e x je

/-- The proposition true just at world `1` is identified with nothing of another type. -/
theorem XCW_not_Twin : ¬ XCW_F.Valid Twin := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp h .t trivial) XCW_p1
    (fun _ _ => Iff.rfl)
  obtain ⟨b, _, h2⟩ := (XCW_F.holdsAt_tex _ _ _ _).mp h1
  have h3 := (XCW_F.holdsAt_conj _ _ _ _ _).mp h2
  obtain ⟨y, _, h4⟩ := (XCW_F.holdsAt_ex _ _ _ _ _).mp h3.2
  rcases (XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mp h4 with ⟨ht, _⟩ | ⟨_, jp, _⟩
  · exact (XCW_F.holdsAt_neg _ _ _ _).mp h3.1 ((XCW_F.holdsAt_teq _ _ _ _ _).mpr ht)
  · exact XCW_p1_nc ((XCW_J_t _).mp jp)

theorem XCW_not_Hae : ¬ XCW_F.Valid Hae := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp h .e trivial) true rfl
  rcases (XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mp h1 with ⟨⟨_, i⟩, _⟩ | ⟨_, je, _⟩
  · exact nomatch i
  · exact XCW_J_e true je

/-- `e → e` and `(e → e) → t` are coextensive at the actual world (all their items are junk), but
not `≈`. -/
theorem XCW_not_ExtT : ¬ XCW_F.Valid ExtT := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp h XCW_ee trivial)
    (.arr XCW_ee .t) trivial
  have hc : XCW_F.HoldsAt (Tm.conj (subT : Fm (Ctx.nil.text.text)) supT)
      (scons (.arr XCW_ee .t) (scons XCW_ee (fun i => i.elim0))) () XCW_U.w0 := by
    refine (XCW_F.holdsAt_conj _ _ _ _ _).mpr ⟨?_, ?_⟩
    · refine (XCW_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XCW_F.holdsAt_ex _ _ _ _ _).mpr
        ⟨XCW_fT, XCW_fT_adm _, ?_⟩
      exact (XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (Or.inr ⟨rfl, XCW_J_ee x, XCW_J_eet _⟩)
    · refine (XCW_F.holdsAt_all _ _ _ _ _).mpr fun y _ => (XCW_F.holdsAt_ex _ _ _ _ _).mpr
        ⟨XCW_id, XCW_id_adm _, ?_⟩
      exact (XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (Or.inr ⟨rfl, XCW_J_ee _, XCW_J_eet y⟩)
  have h2 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h1 hc
  have hi := ((XCW_F.holdsAt_teq _ _ _ _ _).mp h2).2
  exact absurd hi (by decide)

/-- Nothing of type `e` is ever identified with anything of type `t`. -/
theorem XCW_not_et (x : XCW_U.El .e) (p : XCW_U.El .t) (w : Fin 3) : ¬ XCW_eqv .e .t x p w := by
  rintro (⟨⟨_, hi⟩, _⟩ | ⟨_, je, _⟩)
  · exact nomatch hi
  · exact XCW_J_e x je

/-- `e ⊑ t` and `t ⊑ e` are false at every world, so necessary at the actual world; but `e ≉ t`. -/
theorem XCW_not_IntT : ¬ XCW_F.Valid IntT := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp h .e trivial) .t trivial
  have hs : XCW_F.HoldsAt (boxF (subT : Fm (Ctx.nil.text.text))) (scons .t (scons .e (fun i => i.elim0))) ()
      (0 : Fin 3) := by
    refine (XCW_box0 _ _ _).mpr (Or.inr fun v hv' => ?_)
    obtain ⟨y, _, hxy⟩ := (XCW_F.holdsAt_ex _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp hv' true rfl)
    exact XCW_not_et _ _ _ ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mp hxy)
  have hp : XCW_F.HoldsAt (boxF (supT : Fm (Ctx.nil.text.text))) (scons .t (scons .e (fun i => i.elim0))) ()
      (0 : Fin 3) := by
    refine (XCW_box0 _ _ _).mpr (Or.inr fun v hv' => ?_)
    obtain ⟨x, _, hxy⟩ := (XCW_F.holdsAt_ex _ _ _ _ _).mp
      ((XCW_F.holdsAt_all _ _ _ _ _).mp hv' (fun _ => True) (fun _ _ => Iff.rfl))
    exact XCW_not_et _ _ _ ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mp hxy)
  have h2 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCW_F.holdsAt_conj _ _ _ _ _).mpr ⟨hs, hp⟩)
  exact nomatch ((XCW_F.holdsAt_teq _ _ _ _ _).mp h2).2

/-! ### Modal principles -/

/-- The proposition true just at the actual world is true, but not necessary. -/
theorem XCW_not_Collapse : ¬ XCW_F.Valid Collapse := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_all _ _ _ _ _).mp h (fun (w : Fin 3) => w = 0) (fun _ _ => Iff.rfl)
  rcases (XCW_box0 _ _ _).mp ((XCW_F.holdsAt_imp _ _ _ _ _).mp h1 rfl) with h2 | h2
  · exact XCW_one_ne_zero (h2 1)
  · exact h2 0 rfl

/-- `⊤ ≡ ⊥` at the actual world, but not at world `1`. -/
theorem XCW_not_NIEqv : ¬ XCW_F.Valid NIEqv := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp
    ((XCW_F.holdsAt_tall _ _ _ _).mp h .t trivial) (fun _ => True) (fun _ _ => Iff.rfl))
    (fun _ => False) (fun _ _ => Iff.rfl)
  have h2 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr XCW_tb0)
  rcases (XCW_box0 _ _ _).mp h2 with h3 | h3
  · exact XCW_not_tb1 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mp (h3 1))
  · exact h3 0 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr XCW_tb0)

theorem XCW_not_NIX : ¬ XCW_F.Valid NIX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp
    ((XCW_F.holdsAt_tall _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp h .t trivial) .t trivial)
    (fun _ => True) (fun _ _ => Iff.rfl)) (fun _ => False) (fun _ _ => Iff.rfl)
  have h2 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr XCW_tb0)
  rcases (XCW_box0 _ _ _).mp h2 with h3 | h3
  · exact XCW_not_tb1 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mp (h3 1))
  · exact h3 0 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr XCW_tb0)

/-- Types `≈` at the actual world have one image, so are `≈` at every world. -/
theorem XCW_NITeq : XCW_F.Valid NITeq := by
  refine XCW_Valid_of ?_
  refine (XCW_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XCW_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XCW_F.holdsAt_imp _ _ _ _ _).mpr fun h => (XCW_box0 _ _ _).mpr (Or.inl fun v => ?_)
  obtain ⟨k, i⟩ := (XCW_F.holdsAt_teq _ _ _ _ _).mp h
  exact (XCW_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => k rfl, i⟩

/-- `⊤` and the proposition false just at world `1` are equivalent but not identical. -/
theorem XCW_not_PropExt : ¬ XCW_F.Valid PropExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp h (fun _ => True)
    (fun _ _ => Iff.rfl)) (fun (w : Fin 3) => w ≠ 1) (fun _ _ => Iff.rfl)
  have h2 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCW_F.holdsAt_iff _ _ _ _ _).mpr
    (show True ↔ (0 : Fin 3) ≠ 1 from ⟨fun _ => by decide, fun _ => trivial⟩))
  rcases (XCW_eqv_t0 _ _).mp ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mp h2) with h3 | ⟨_, h3⟩
  · exact (h3 1).mp trivial rfl
  · rcases h3 with h3 | h3
    · exact h3 1 rfl
    · exact h3 0 (show (0 : Fin 3) ≠ 1 by decide)

/-- `⊤ ≡ ⊥` is true at the actual world; Leibniz identity of `⊤` and `⊥` is not. -/
theorem XCW_not_IdId : ¬ XCW_F.Valid IdId := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp
    ((XCW_F.holdsAt_tall _ _ _ _).mp h .t trivial) (fun _ => True) (fun _ _ => Iff.rfl))
    (fun _ => False) (fun _ _ => Iff.rfl)
  have hA : ∀ w : Fin 3, XCW_F.HoldsAt (Tm.eqv tv0 tv0 (.var (.there .here)) (.var .here) :
      Fm (((Ctx.nil.text).ext tv0).ext tv0)) (scons .t (fun i => i.elim0))
      (((), (fun _ => True : Fin 3 → Prop)), (fun _ => False : Fin 3 → Prop)) w ↔
      XCW_eqv .t .t (fun _ => True) (fun _ => False) w := fun w => XCW_F.holdsAt_eqv _ _ _ _ _ _ w
  have hL : ¬ XCW_F.HoldsAt (Tm.all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here))))
      (.app (.var .here) (.var (.there .here)))) : Fm (((Ctx.nil.text).ext tv0).ext tv0))
      (scons .t (fun i => i.elim0)) (((), (fun _ => True : Fin 3 → Prop)), (fun _ => False : Fin 3 → Prop))
      (0 : Fin 3) := fun hl =>
    (XCW_F.holdsAt_imp _ _ _ _ _).mp ((XCW_F.holdsAt_all _ _ _ _ _).mp hl (fun p => p : XCW_U.El (.arr .t .t))
      (fun _ _ _ _ h => h)) trivial
  rcases (XCW_eqv_t0 _ _).mp ((XCW_eqv_tt _ _ _ _ _).mp h1) with h2 | ⟨h2, _⟩
  · exact hL ((h2 0).mp ((hA 0).mpr XCW_tb0))
  · rcases h2 with h2 | h2
    · exact XCW_not_tb1 ((hA 1).mp (h2 1))
    · exact h2 0 ((hA 0).mpr XCW_tb0)

/-- Booleanism: tautologically equivalent propositions agree at every world. -/
theorem XCW_Bool : ∀ φ, BoolSch φ → XCW_F.Valid φ := by
  rintro _ ⟨k, P, Q, hT, rfl⟩
  unfold BoolInst
  rw [← closeCtx_ctxT]
  refine XCW_F.valid_closeCtx _ _ fun ρ _ env _ => (XCW_eqv_tt _ _ _ _ _).mpr
    (Or.inl ⟨⟨fun _ => rfl, rfl⟩, fun v _ => ?_⟩)
  exact (XCW_F.holdsAt_inst P (varsT k) ρ env v).trans ((hT _).trans (XCW_F.holdsAt_inst Q (varsT k) ρ env v).symm)

/-! ### The Barcan formulas -/

/-- TBF: every type exists at every world, and `□` at the actual world is truth at every world or
falsity at every world. -/
theorem XCW_TBF : ∀ χ, TBFSch χ → XCW_F.Valid χ := by
  rintro _ ⟨φ, rfl⟩
  refine XCW_Valid_of ?_
  refine (XCW_F.holdsAt_imp _ _ _ _ _).mpr fun h => (XCW_box0 _ _ _).mpr ?_
  have h' : ∀ a, (∀ v : Fin 3, XCW_F.HoldsAt φ (scons a (fun i => i.elim0)) () v) ∨
      (∀ v : Fin 3, ¬ XCW_F.HoldsAt φ (scons a (fun i => i.elim0)) () v) := fun a =>
    (XCW_box0 _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp h a trivial)
  rcases Classical.em (∃ a, ∀ v : Fin 3, ¬ XCW_F.HoldsAt φ (scons a (fun i => i.elim0)) () v) with hc | hc
  · obtain ⟨a, ha⟩ := hc
    exact Or.inr fun v hv => ha v ((XCW_F.holdsAt_tall _ _ _ _).mp hv a trivial)
  · refine Or.inl fun v => (XCW_F.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
    rcases h' a with h1 | h1
    · exact h1 v
    · exact absurd ⟨a, h1⟩ hc

/-- `α` has two non-identified items, and `α ≉ e`. -/
def XCW_phiC : Fm Ctx.nil.text :=
  conj (ex tv0 (ex tv0 (neg (eqv tv0 tv0 (.var (.there .here)) (.var .here))))) (neg (teq tv0 tyE))

/-- TCBF fails: `∀α φ` is false at every world (take `α := e`), so necessary; but for `α := e → e`,
`φ` is false at the actual world (all its items are junk) and true at world `1`. -/
theorem XCW_not_TCBF : ¬ ∀ χ, TCBFSch χ → XCW_F.Valid χ := fun hv => by
  have h := hv _ ⟨XCW_phiC, rfl⟩ (fun i => i.elim0) (fun i => i.elim0) () trivial
  have hP : XCW_F.HoldsAt (boxF (tall XCW_phiC)) (fun i => i.elim0) () (0 : Fin 3) := by
    refine (XCW_box0 _ _ _).mpr (Or.inr fun v hv' => ?_)
    have h1 := (XCW_F.holdsAt_conj _ _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp hv' .e trivial)
    exact (XCW_F.holdsAt_neg _ _ _ _).mp h1.2 ((XCW_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => rfl, rfl⟩)
  have h1 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h hP
  rcases (XCW_box0 _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp h1 XCW_ee trivial) with h2 | h2
  · have h3 := (XCW_F.holdsAt_conj _ _ _ _ _).mp (h2 0)
    obtain ⟨x, _, h4⟩ := (XCW_F.holdsAt_ex _ _ _ _ _).mp h3.1
    obtain ⟨y, _, h5⟩ := (XCW_F.holdsAt_ex _ _ _ _ _).mp h4
    exact (XCW_F.holdsAt_neg _ _ _ _).mp h5 ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr
      (Or.inr ⟨rfl, XCW_J_ee _, XCW_J_ee _⟩))
  · refine h2 1 ((XCW_F.holdsAt_conj _ _ _ _ _).mpr ⟨?_, ?_⟩)
    · refine (XCW_F.holdsAt_ex _ _ _ _ _).mpr ⟨XCW_id, XCW_id_adm _, (XCW_F.holdsAt_ex _ _ _ _ _).mpr
        ⟨(fun _ => true : XCW_U.El XCW_ee), fun _ _ _ _ _ => rfl, (XCW_F.holdsAt_neg _ _ _ _).mpr fun he => ?_⟩⟩
      have he' := (XCW_eqv_ne XCW_one_ne_zero).mp ((XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mp he)
      have h6 : false = true := he'.2 (1 : Fin 3) (Or.inl rfl) false false rfl
      exact Bool.noConfusion h6
    · exact (XCW_F.holdsAt_neg _ _ _ _).mpr fun ht => nomatch ((XCW_F.holdsAt_teq _ _ _ _ _).mp ht).2

theorem XCW_TNec : XCW_F.Valid TNec := by
  refine XCW_Valid_of ((XCW_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XCW_box0 _ _ _).mpr (Or.inl fun v => ?_))
  exact (XCW_F.holdsAt_tex _ _ _ _).mpr ⟨a, trivial, (XCW_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => rfl, rfl⟩⟩

theorem XCW_Nec : XCW_F.Valid Nec := by
  refine XCW_Valid_of ((XCW_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XCW_F.holdsAt_all _ _ _ _ _).mpr
    fun x hx => (XCW_box0 _ _ _).mpr (Or.inl fun v => ?_))
  have hxv : XCW_U.rel a v x x := XCW_U.rel_mono a (0 : Fin 3) v x x (Or.inr rfl) hx
  exact (XCW_F.holdsAt_ex _ _ _ _ _).mpr ⟨x, hxv, (XCW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr
    (Or.inl ((XCW_beqv_same a x x v).mpr hxv))⟩

/-- The property of being constant, of items of `t → e`. -/
def XCW_Fc : XCW_U.El (.arr XCW_A .t) := fun (x : (Fin 3 → Prop) → Bool) (_ : Fin 3) => ∀ p q, x p = x q

theorem XCW_Fc_adm : XCW_U.rel (.arr XCW_A .t) (0 : Fin 3) XCW_Fc XCW_Fc := by
  intro v _ x y hxy
  have e : x = y := XCW_relA_eq hxy
  subst e
  exact fun _ _ => Iff.rfl

/-- Every item of `t → e` at the actual world is constant, at every world; but at world `1`, `f₁` is
an item of `t → e` which is not constant. -/
theorem XCW_not_BF : ¬ XCW_F.Valid BF := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp h XCW_A trivial) XCW_Fc XCW_Fc_adm
  have h2 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCW_F.holdsAt_all _ _ _ _ _).mpr fun _ hx =>
    (XCW_box0 _ _ _).mpr (Or.inl fun _ => XCW_const_of_adm0 hx))
  rcases (XCW_box0 _ _ _).mp h2 with h3 | h3
  · have h4 := (XCW_F.holdsAt_all _ _ _ _ _).mp (h3 1) f1IE XCW_f1_adm
    have h5 : ∀ p q : Fin 3 → Prop, f1IE p = f1IE q := h4
    have h6 := h5 (fun _ => True) (fun _ => False)
    rw [f1IE_pos _ trivial, f1IE_neg _ (fun h => h)] at h6
    exact Bool.noConfusion h6
  · exact h3 0 ((XCW_F.holdsAt_all _ _ _ _ _).mpr fun _ hx => XCW_const_of_adm0 hx)

/-- Every proposition is false at every world (take `⊥`), but the proposition true just at the actual
world is not necessary. -/
theorem XCW_not_CBF : ¬ XCW_F.Valid CBF := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCW_F.holdsAt_all _ _ _ _ _).mp ((XCW_F.holdsAt_tall _ _ _ _).mp h .t trivial)
    (fun p => p : XCW_U.El (.arr .t .t)) (fun _ _ _ _ h => h)
  have h2 := (XCW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCW_box0 _ _ _).mpr (Or.inr fun _ hv' =>
    ((XCW_F.holdsAt_all _ _ _ _ _).mp hv' (fun _ => False) (fun _ _ => Iff.rfl) : False)))
  have h3 := (XCW_F.holdsAt_all _ _ _ _ _).mp h2 (fun (w : Fin 3) => w = 0) (fun _ _ => Iff.rfl)
  rcases (XCW_box0 _ _ _).mp h3 with h4 | h4
  · exact XCW_one_ne_zero (h4 1)
  · exact h4 0 rfl

end Kr
end PIF
