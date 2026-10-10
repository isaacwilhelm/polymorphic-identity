import PIBF
import PIOQ_KIE

/-!
# A Kripke model of PIᶜ refuting ND≈, TBF, BF, NI×, Int≈, Ext≈, PCong and ND× at once

`𝔐_k,x`: three worlds `0, 1, 2`; the actual world `0` sees all three, and `1` and `2` see only
themselves. Entities are booleans. There are three base types: `d`, a copy of `e`; `d₂`, another
copy of the booleans; and `c`, with a single item, which exists only at world `2`. Identity of
entities, and of items of each base type, is equality at every world.

Identity across types has two sources.

* Each item of a type built from `d` is identified, at every world, with the corresponding item
  of the type got by putting `e` for `d` (identity between such types is the logical relation
  built from equality of booleans). So `e` and `d` are necessarily coextensive.
* At the actual world only, an item of `t → e` (or of `t → d`) and an item of `t → d₂` are
  identified when they are the same function and that function is an item of `t → e` there.

`≈` is identity of types, except at world `1`, where each type is `≈` to the type got from it by
putting `e` for `d`.

Within a type, identity is identity at the world, so the frame validates Classicism (and LL≡) at
every world; LL≈ holds at world `1` by the Kripke invariance lemma, with the logical relations
between types with the same image as admissible relations.

* ND≈ fails: `¬(e ≈ d)`, but `e ≈ d` at world `1`.
* Int≈ and Ext≈ fail: `e` and `d` are necessarily coextensive, but `¬(e ≈ d)`.
* NI× and PCong fail: the constant function of `t → e` is identified with that of `t → d₂` at the
  actual world, but not at world `1`; and their values, of types `e` and `d₂`, are not identified.
* TBF fails: every type at the actual world necessarily has two distinct items, but at world `2`
  the type `c` has only one.
* BF, ND× and Functional Choice fail, as in `𝔐_k,ie`.
-/
set_option autoImplicit false

namespace PIF
namespace Kr
open Tm

/-! ### The universe -/

/-- The base types: `d`, a copy of `e`; `d₂`, another copy of the booleans; `c`, with one item. -/
inductive XMK_B where
  | d
  | d2
  | c

/-- The items of the base types. -/
def XMK_BT : XMK_B → Type
  | .d => Bool
  | .d2 => Bool
  | .c => Unit

/-- Codes not mentioning `c`. -/
def XMK_noC : Code XMK_B → Prop
  | .base .c => False
  | .arr a b => XMK_noC a ∧ XMK_noC b
  | _ => True

def XMK_U : Univ where
  W := Fin 3
  w0 := 0
  R := fun w u => w = u ∨ w = 0
  Rrefl := fun _ => Or.inl rfl
  Rtrans := by
    intro u v w h1 h2
    rcases h1 with rfl | h1
    · exact h2
    · exact Or.inr h1
  E := Bool
  Base := XMK_B
  B := XMK_BT
  neE := ⟨true⟩
  neB := fun b => match b with
    | .d => ⟨true⟩
    | .d2 => ⟨true⟩
    | .c => ⟨()⟩
  re := fun _ x y => x = y
  rb := fun _ _ x y => x = y
  re_refl := fun _ _ => rfl
  re_symm := fun _ _ _ h => h.symm
  re_trans := fun _ _ _ _ h1 h2 => h1.trans h2
  re_mono := fun _ _ _ _ _ h => h
  rb_refl := fun _ _ _ => rfl
  rb_symm := fun _ _ _ _ h => h.symm
  rb_trans := fun _ _ _ _ _ h1 h2 => h1.trans h2
  rb_mono := fun _ _ _ _ _ _ h => h
  D := fun w a => w = 2 ∨ XMK_noC a
  D_e := fun _ => Or.inr trivial
  D_t := fun _ => Or.inr trivial
  D_arr := by
    intro w a c ha hc
    rcases ha with ha | ha
    · exact Or.inl ha
    · rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr ⟨ha, hc⟩
  D_mono := by
    intro w v a h ha
    rcases ha with ha | ha
    · subst ha
      rcases h with h | h
      · exact Or.inl h.symm
      · exact absurd h (by decide)
    · exact Or.inr ha

/-- The type got by putting `e` for `d`. -/
def XMK_img : Code XMK_B → Code XMK_B
  | .e => .e
  | .t => .t
  | .base .d => .e
  | .base .d2 => .base .d2
  | .base .c => .base .c
  | .arr a c => .arr (XMK_img a) (XMK_img c)

/-! ### Identity between types with the same image -/

def XMK_EB : (u : XMK_B) → Bool → XMK_BT u → Prop
  | .d => fun x y => x = y
  | .d2 => fun _ _ => False
  | .c => fun _ _ => False

def XMK_BE : (u : XMK_B) → XMK_BT u → Bool → Prop
  | .d => fun x y => x = y
  | .d2 => fun _ _ => False
  | .c => fun _ _ => False

def XMK_BB : (u v : XMK_B) → XMK_BT u → XMK_BT v → Prop
  | .d, .d => fun x y => x = y
  | .d2, .d2 => fun x y => x = y
  | .c, .c => fun x y => x = y
  | _, _ => fun _ _ => False

/-- Identity at a world between items of types with the same image. -/
def XMK_CR : (a b : Code XMK_B) → Fin 3 → XMK_U.El a → XMK_U.El b → Prop
  | .e, .e => fun _ x y => x = y
  | .e, .base u => fun _ x y => XMK_EB u x y
  | .base u, .e => fun _ x y => XMK_BE u x y
  | .base u, .base v => fun _ x y => XMK_BB u v x y
  | .t, .t => fun w p q => ∀ v, XMK_U.R w v → (p v ↔ q v)
  | .arr a c, .arr b d => fun w f g => ∀ v, XMK_U.R w v → ∀ x y, XMK_CR a b v x y → XMK_CR c d v (f x) (g y)
  | _, _ => fun _ _ _ => False

/-- Transport, both ways, between types with the same image. -/
noncomputable def XMK_Tr : (a b : Code XMK_B) → (XMK_U.El a → XMK_U.El b) × (XMK_U.El b → XMK_U.El a)
  | .e, .e => (fun x => x, fun x => x)
  | .e, .base .d => (fun x => x, fun x => x)
  | .base .d, .e => (fun x => x, fun x => x)
  | .base .d, .base .d => (fun x => x, fun x => x)
  | .base .d2, .base .d2 => (fun x => x, fun x => x)
  | .base .c, .base .c => (fun x => x, fun x => x)
  | .t, .t => (fun p => p, fun p => p)
  | .arr a c, .arr b d => (fun f y => (XMK_Tr c d).1 (f ((XMK_Tr a b).2 y)),
      fun g x => (XMK_Tr c d).2 (g ((XMK_Tr a b).1 x)))
  | a, b => (fun _ => Classical.choose (XMK_U.adm_nonempty b), fun _ => Classical.choose (XMK_U.adm_nonempty a))

noncomputable abbrev XMK_Tf (a b : Code XMK_B) : XMK_U.El a → XMK_U.El b := (XMK_Tr a b).1
noncomputable abbrev XMK_Tg (a b : Code XMK_B) : XMK_U.El b → XMK_U.El a := (XMK_Tr a b).2

theorem XMK_CR_diag : ∀ (a : Code XMK_B) (w : Fin 3) (x y : XMK_U.El a), XMK_U.rel a w x y ↔ XMK_CR a a w x y
  | .e, _, _, _ => Iff.rfl
  | .t, _, _, _ => Iff.rfl
  | .base .d, _, _, _ => Iff.rfl
  | .base .d2, _, _, _ => Iff.rfl
  | .base .c, _, _, _ => Iff.rfl
  | .arr a c, _, _, _ => forall_congr' fun v => imp_congr Iff.rfl (forall_congr' fun x => forall_congr' fun y =>
      imp_congr (XMK_CR_diag a v x y) (XMK_CR_diag c v _ _))

theorem XMK_CR_mono (a b : Code XMK_B) (w v : Fin 3) (x : XMK_U.El a) (y : XMK_U.El b) (hv : XMK_U.R w v)
    (h : XMK_CR a b w x y) : XMK_CR a b v x y := by
  cases a <;> cases b <;> first | exact h | exact fun u hu => h u (XMK_U.Rtrans _ _ _ hv hu)

theorem XMK_img_e {a : Code XMK_B} (h : XMK_img a = .e) : a = .e ∨ a = .base .d := by
  cases a with
  | e => exact Or.inl rfl
  | t => exact nomatch h
  | base u =>
    cases u with
    | d => exact Or.inr rfl
    | d2 => exact nomatch h
    | c => exact nomatch h
  | arr _ _ => exact nomatch h

theorem XMK_img_t {a : Code XMK_B} (h : XMK_img a = .t) : a = .t := by
  cases a with
  | t => rfl
  | e => exact nomatch h
  | base u =>
    cases u with
    | d => exact nomatch h
    | d2 => exact nomatch h
    | c => exact nomatch h
  | arr _ _ => exact nomatch h

theorem XMK_img_d {a : Code XMK_B} (h : XMK_img a = .base .d) : False := by
  cases a with
  | t => exact nomatch h
  | e => exact nomatch h
  | base u =>
    cases u with
    | d => exact nomatch h
    | d2 => exact nomatch h
    | c => exact nomatch h
  | arr _ _ => exact nomatch h

theorem XMK_img_d2 {a : Code XMK_B} (h : XMK_img a = .base .d2) : a = .base .d2 := by
  cases a with
  | t => exact nomatch h
  | e => exact nomatch h
  | base u =>
    cases u with
    | d => exact nomatch h
    | d2 => rfl
    | c => exact nomatch h
  | arr _ _ => exact nomatch h

theorem XMK_img_c {a : Code XMK_B} (h : XMK_img a = .base .c) : a = .base .c := by
  cases a with
  | t => exact nomatch h
  | e => exact nomatch h
  | base u =>
    cases u with
    | d => exact nomatch h
    | d2 => exact nomatch h
    | c => rfl
  | arr _ _ => exact nomatch h

theorem XMK_img_arr {a k1 k2 : Code XMK_B} (h : XMK_img a = .arr k1 k2) :
    ∃ a1 a2, a = .arr a1 a2 ∧ XMK_img a1 = k1 ∧ XMK_img a2 = k2 := by
  cases a with
  | arr a1 a2 => injection h with h1 h2; exact ⟨a1, a2, rfl, h1, h2⟩
  | e => exact nomatch h
  | t => exact nomatch h
  | base u =>
    cases u with
    | d => exact nomatch h
    | d2 => exact nomatch h
    | c => exact nomatch h

/-- The four facts at a base type whose items are booleans or units, identity being equality. -/
theorem XMK_shape_base (a0 : Code XMK_B) (ha0 : ∀ a, XMK_img a = XMK_img a0 → a = a0)
    (hsymm : ∀ w x y, XMK_CR a0 a0 w x y → XMK_CR a0 a0 w y x)
    (htrans : ∀ w x y z, XMK_CR a0 a0 w x y → XMK_CR a0 a0 w y z → XMK_CR a0 a0 w x z)
    (hT : ∀ w x, XMK_CR a0 a0 w x x → XMK_CR a0 a0 w x (XMK_Tf a0 a0 x) ∧
      XMK_CR a0 a0 w (XMK_Tf a0 a0 x) (XMK_Tf a0 a0 x))
    (hT' : ∀ w y, XMK_CR a0 a0 w y y → XMK_CR a0 a0 w (XMK_Tg a0 a0 y) y ∧
      XMK_CR a0 a0 w (XMK_Tg a0 a0 y) (XMK_Tg a0 a0 y)) :
    (∀ a b, XMK_img a = XMK_img a0 → XMK_img b = XMK_img a0 → ∀ w x y, XMK_CR a b w x y → XMK_CR b a w y x) ∧
    (∀ a b c, XMK_img a = XMK_img a0 → XMK_img b = XMK_img a0 → XMK_img c = XMK_img a0 →
      ∀ w x y z, XMK_CR a b w x y → XMK_CR b c w y z → XMK_CR a c w x z) ∧
    (∀ a b, XMK_img a = XMK_img a0 → XMK_img b = XMK_img a0 → ∀ w x, XMK_CR a a w x x →
      XMK_CR a b w x (XMK_Tf a b x) ∧ XMK_CR b b w (XMK_Tf a b x) (XMK_Tf a b x)) ∧
    (∀ a b, XMK_img a = XMK_img a0 → XMK_img b = XMK_img a0 → ∀ w y, XMK_CR b b w y y →
      XMK_CR a b w (XMK_Tg a b y) y ∧ XMK_CR a a w (XMK_Tg a b y) (XMK_Tg a b y)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b ha hb
    obtain rfl := ha0 a ha
    obtain rfl := ha0 b hb
    exact hsymm
  · intro a b c ha hb hc
    obtain rfl := ha0 a ha
    obtain rfl := ha0 b hb
    obtain rfl := ha0 c hc
    exact htrans
  · intro a b ha hb
    obtain rfl := ha0 a ha
    obtain rfl := ha0 b hb
    exact hT
  · intro a b ha hb
    obtain rfl := ha0 a ha
    obtain rfl := ha0 b hb
    exact hT'

set_option maxHeartbeats 4000000 in
/-- Identity between types of one shape is symmetric and transitive, and transport takes each item
to one identified with it. -/
theorem XMK_shape : ∀ k : Code XMK_B,
    (∀ a b, XMK_img a = k → XMK_img b = k → ∀ w x y, XMK_CR a b w x y → XMK_CR b a w y x) ∧
    (∀ a b c, XMK_img a = k → XMK_img b = k → XMK_img c = k → ∀ w x y z, XMK_CR a b w x y →
      XMK_CR b c w y z → XMK_CR a c w x z) ∧
    (∀ a b, XMK_img a = k → XMK_img b = k → ∀ w x, XMK_CR a a w x x →
      XMK_CR a b w x (XMK_Tf a b x) ∧ XMK_CR b b w (XMK_Tf a b x) (XMK_Tf a b x)) ∧
    (∀ a b, XMK_img a = k → XMK_img b = k → ∀ w y, XMK_CR b b w y y →
      XMK_CR a b w (XMK_Tg a b y) y ∧ XMK_CR a a w (XMK_Tg a b y) (XMK_Tg a b y)) := by
  intro k
  induction k with
  | e =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b ha hb w x y h
      rcases XMK_img_e ha with rfl | rfl <;> rcases XMK_img_e hb with rfl | rfl <;> exact Eq.symm h
    · intro a b c ha hb hc w x y z h1 h2
      rcases XMK_img_e ha with rfl | rfl <;> rcases XMK_img_e hb with rfl | rfl <;>
        rcases XMK_img_e hc with rfl | rfl <;> exact Eq.trans h1 h2
    · intro a b ha hb w x _
      rcases XMK_img_e ha with rfl | rfl <;> rcases XMK_img_e hb with rfl | rfl <;> exact ⟨rfl, rfl⟩
    · intro a b ha hb w x _
      rcases XMK_img_e ha with rfl | rfl <;> rcases XMK_img_e hb with rfl | rfl <;> exact ⟨rfl, rfl⟩
  | t =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b ha hb w x y h
      have e1 := XMK_img_t ha; have e2 := XMK_img_t hb; subst e1; subst e2
      exact fun v hv => (h v hv).symm
    · intro a b c ha hb hc w x y z h1 h2
      have e1 := XMK_img_t ha; have e2 := XMK_img_t hb; have e3 := XMK_img_t hc; subst e1; subst e2; subst e3
      exact fun v hv => (h1 v hv).trans (h2 v hv)
    · intro a b ha hb w x hx
      have e1 := XMK_img_t ha; have e2 := XMK_img_t hb; subst e1; subst e2
      exact ⟨hx, hx⟩
    · intro a b ha hb w x hx
      have e1 := XMK_img_t ha; have e2 := XMK_img_t hb; subst e1; subst e2
      exact ⟨hx, hx⟩
  | base u =>
    cases u with
    | d => exact ⟨fun a _ ha => (XMK_img_d ha).elim, fun a _ _ ha => (XMK_img_d ha).elim,
        fun a _ ha => (XMK_img_d ha).elim, fun a _ ha => (XMK_img_d ha).elim⟩
    | d2 =>
      exact XMK_shape_base (.base .d2) (fun _ h => XMK_img_d2 h) (fun _ _ _ h => Eq.symm h)
        (fun _ _ _ _ h1 h2 => Eq.trans h1 h2) (fun _ _ _ => ⟨rfl, rfl⟩) (fun _ _ _ => ⟨rfl, rfl⟩)
    | c =>
      exact XMK_shape_base (.base .c) (fun _ h => XMK_img_c h) (fun _ _ _ h => Eq.symm h)
        (fun _ _ _ _ h1 h2 => Eq.trans h1 h2) (fun _ _ _ => ⟨rfl, rfl⟩) (fun _ _ _ => ⟨rfl, rfl⟩)
  | arr k1 k2 ih1 ih2 =>
    obtain ⟨S1, R1, P1, Q1⟩ := ih1
    obtain ⟨S2, R2, P2, Q2⟩ := ih2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b ha hb w f g h
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XMK_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XMK_img_arr hb
      intro v hv x y hxy
      exact S2 a2 b2 ha2 hb2 v _ _ (h v hv y x (S1 b1 a1 hb1 ha1 v x y hxy))
    · intro a b c ha hb hc w f g h hfg hgh
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XMK_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XMK_img_arr hb
      obtain ⟨c1, c2, rfl, hc1, hc2⟩ := XMK_img_arr hc
      intro v hv x z hxz
      have hzz : XMK_CR c1 c1 v z z := R1 c1 a1 c1 hc1 ha1 hc1 v z x z (S1 a1 c1 ha1 hc1 v x z hxz) hxz
      obtain ⟨hyz, _⟩ := Q1 b1 c1 hb1 hc1 v z hzz
      have hxy : XMK_CR a1 b1 v x (XMK_Tg b1 c1 z) :=
        R1 a1 c1 b1 ha1 hc1 hb1 v x z _ hxz (S1 b1 c1 hb1 hc1 v _ z hyz)
      exact R2 a2 b2 c2 ha2 hb2 hc2 v _ _ _ (hfg v hv x _ hxy) (hgh v hv _ z hyz)
    · intro a b ha hb w f hf
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XMK_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XMK_img_arr hb
      refine ⟨?_, ?_⟩
      · intro v hv x y hxy
        have hyy : XMK_CR b1 b1 v y y := R1 b1 a1 b1 hb1 ha1 hb1 v y x y (S1 a1 b1 ha1 hb1 v x y hxy) hxy
        obtain ⟨hTy, hTT⟩ := Q1 a1 b1 ha1 hb1 v y hyy
        have hxT : XMK_CR a1 a1 v x (XMK_Tg a1 b1 y) :=
          R1 a1 b1 a1 ha1 hb1 ha1 v x y _ hxy (S1 a1 b1 ha1 hb1 v _ y hTy)
        have hfx := hf v hv x _ hxT
        obtain ⟨h1, _⟩ := P2 a2 b2 ha2 hb2 v _ (hf v hv _ _ hTT)
        exact R2 a2 a2 b2 ha2 ha2 hb2 v _ _ _ hfx h1
      · intro v hv y y' hyy'
        have hyy : XMK_CR b1 b1 v y y := R1 b1 b1 b1 hb1 hb1 hb1 v y y' y hyy' (S1 b1 b1 hb1 hb1 v y y' hyy')
        have hy'y' : XMK_CR b1 b1 v y' y' :=
          R1 b1 b1 b1 hb1 hb1 hb1 v y' y y' (S1 b1 b1 hb1 hb1 v y y' hyy') hyy'
        obtain ⟨hTy, hTT⟩ := Q1 a1 b1 ha1 hb1 v y hyy
        obtain ⟨hTy', hT'T'⟩ := Q1 a1 b1 ha1 hb1 v y' hy'y'
        have hTyy : XMK_CR a1 a1 v (XMK_Tg a1 b1 y) (XMK_Tg a1 b1 y') :=
          R1 a1 b1 a1 ha1 hb1 ha1 v _ y _ hTy (R1 b1 b1 a1 hb1 hb1 ha1 v y y' _ hyy' (S1 a1 b1 ha1 hb1 v _ y' hTy'))
        obtain ⟨g1, _⟩ := P2 a2 b2 ha2 hb2 v _ (hf v hv _ _ hTT)
        obtain ⟨g2, _⟩ := P2 a2 b2 ha2 hb2 v _ (hf v hv _ _ hT'T')
        exact R2 b2 a2 b2 hb2 ha2 hb2 v _ _ _ (S2 a2 b2 ha2 hb2 v _ _ g1)
          (R2 a2 a2 b2 ha2 ha2 hb2 v _ _ _ (hf v hv _ _ hTyy) g2)
    · intro a b ha hb w g hg
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XMK_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XMK_img_arr hb
      refine ⟨?_, ?_⟩
      · intro v hv x y hxy
        have hxx : XMK_CR a1 a1 v x x := R1 a1 b1 a1 ha1 hb1 ha1 v x y x hxy (S1 a1 b1 ha1 hb1 v x y hxy)
        obtain ⟨hxT, hTT⟩ := P1 a1 b1 ha1 hb1 v x hxx
        have hTy : XMK_CR b1 b1 v (XMK_Tf a1 b1 x) y :=
          R1 b1 a1 b1 hb1 ha1 hb1 v _ x y (S1 a1 b1 ha1 hb1 v x _ hxT) hxy
        have hgy := hg v hv _ y hTy
        obtain ⟨h1, _⟩ := Q2 a2 b2 ha2 hb2 v _ (hg v hv _ _ hTT)
        exact R2 a2 b2 b2 ha2 hb2 hb2 v _ _ _ h1 hgy
      · intro v hv x x' hxx'
        have hxx : XMK_CR a1 a1 v x x := R1 a1 a1 a1 ha1 ha1 ha1 v x x' x hxx' (S1 a1 a1 ha1 ha1 v x x' hxx')
        have hx'x' : XMK_CR a1 a1 v x' x' :=
          R1 a1 a1 a1 ha1 ha1 ha1 v x' x x' (S1 a1 a1 ha1 ha1 v x x' hxx') hxx'
        obtain ⟨hxT, hTT⟩ := P1 a1 b1 ha1 hb1 v x hxx
        obtain ⟨hx'T, hT'T'⟩ := P1 a1 b1 ha1 hb1 v x' hx'x'
        have hTxx : XMK_CR b1 b1 v (XMK_Tf a1 b1 x) (XMK_Tf a1 b1 x') :=
          R1 b1 a1 b1 hb1 ha1 hb1 v _ x _ (S1 a1 b1 ha1 hb1 v x _ hxT) (R1 a1 a1 b1 ha1 ha1 hb1 v x x' _ hxx' hx'T)
        obtain ⟨g1, _⟩ := Q2 a2 b2 ha2 hb2 v _ (hg v hv _ _ hTT)
        obtain ⟨g2, _⟩ := Q2 a2 b2 ha2 hb2 v _ (hg v hv _ _ hT'T')
        exact R2 a2 b2 a2 ha2 hb2 ha2 v _ _ _ g1
          (R2 b2 b2 a2 hb2 hb2 ha2 v _ _ _ (hg v hv _ _ hTxx) (S2 a2 b2 ha2 hb2 v _ _ g2))

theorem XMK_CR_symm {a b : Code XMK_B} (h : XMK_img a = XMK_img b) {w : Fin 3} {x : XMK_U.El a}
    {y : XMK_U.El b} (hxy : XMK_CR a b w x y) : XMK_CR b a w y x :=
  (XMK_shape (XMK_img a)).1 a b rfl h.symm w x y hxy

theorem XMK_CR_trans {a b c : Code XMK_B} (h1 : XMK_img a = XMK_img b) (h2 : XMK_img b = XMK_img c)
    {w : Fin 3} {x : XMK_U.El a} {y : XMK_U.El b} {z : XMK_U.El c} (hxy : XMK_CR a b w x y)
    (hyz : XMK_CR b c w y z) : XMK_CR a c w x z :=
  (XMK_shape (XMK_img a)).2.1 a b c rfl h1.symm (h1.trans h2).symm w x y z hxy hyz

/-! ### Identity across `t → e`, `t → d` and `t → d₂`, at the actual world -/

/-- `A := t → e`. -/
abbrev XMK_A : Code XMK_B := .arr .t .e
/-- `A_d := t → d`. -/
abbrev XMK_Ad : Code XMK_B := .arr .t (.base .d)
/-- `B := t → d₂`. -/
abbrev XMK_Bd : Code XMK_B := .arr .t (.base .d2)

/-- The set that `A`, `A_d` and `B` all name. -/
abbrev XMK_G : Type := (Fin 3 → Prop) → Bool

/-- The graph of an item of `A`, `A_d` or `B`. -/
def XMK_toG : (a : Code XMK_B) → XMK_U.El a → Option XMK_G
  | .arr .t .e, f => some f
  | .arr .t (.base .d), f => some f
  | .arr .t (.base .d2), f => some f
  | _, _ => none

theorem XMK_toG_some : ∀ (a : Code XMK_B) (x : XMK_U.El a) (g : XMK_G), XMK_toG a x = some g →
    XMK_img a = XMK_A ∨ XMK_img a = XMK_Bd
  | .arr .t .e, _, _, _ => Or.inl rfl
  | .arr .t (.base .d), _, _, _ => Or.inl rfl
  | .arr .t (.base .d2), _, _, _ => Or.inr rfl
  | .arr .t (.base .c), _, _, h => nomatch h
  | .e, _, _, h => nomatch h
  | .t, _, _, h => nomatch h
  | .base _, _, _, h => nomatch h
  | .arr .e _, _, _, h => nomatch h
  | .arr (.base _) _, _, _, h => nomatch h
  | .arr (.arr _ _) _, _, _, h => nomatch h
  | .arr .t .t, _, _, h => nomatch h
  | .arr .t (.arr _ _), _, _, h => nomatch h

theorem XMK_toG_none (a : Code XMK_B) (x : XMK_U.El a) (h1 : XMK_img a ≠ XMK_A) (h2 : XMK_img a ≠ XMK_Bd) :
    XMK_toG a x = none := by
  cases hg : XMK_toG a x with
  | none => rfl
  | some g => exact ((XMK_toG_some a x g hg).elim h1 h2).elim

theorem XMK_img_A {a : Code XMK_B} (h : XMK_img a = XMK_A) : a = XMK_A ∨ a = XMK_Ad := by
  obtain ⟨a1, a2, rfl, h1, h2⟩ := XMK_img_arr h
  obtain rfl := XMK_img_t h1
  rcases XMK_img_e h2 with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem XMK_img_Bd {a : Code XMK_B} (h : XMK_img a = XMK_Bd) : a = XMK_Bd := by
  obtain ⟨a1, a2, rfl, h1, h2⟩ := XMK_img_arr h
  obtain rfl := XMK_img_t h1
  obtain rfl := XMK_img_d2 h2
  rfl

/-- Items of types with the same image which are identified have the same graph. -/
theorem XMK_toG_CR (a b : Code XMK_B) (w : Fin 3) (x : XMK_U.El a) (y : XMK_U.El b)
    (hi : XMK_img a = XMK_img b) (h : XMK_CR a b w x y) : XMK_toG a x = XMK_toG b y := by
  by_cases hA : XMK_img a = XMK_A
  · rcases XMK_img_A hA with rfl | rfl <;> rcases XMK_img_A (hi.symm.trans hA) with rfl | rfl <;>
      exact congrArg some (funext fun p => h w (XMK_U.Rrefl w) p p (fun _ _ => Iff.rfl))
  · by_cases hB : XMK_img a = XMK_Bd
    · obtain rfl := XMK_img_Bd hB
      obtain rfl := XMK_img_Bd (hi.symm.trans hB)
      exact congrArg some (funext fun p => h w (XMK_U.Rrefl w) p p (fun _ _ => Iff.rfl))
    · rw [XMK_toG_none a x hA hB, XMK_toG_none b y (hi ▸ hA) (hi ▸ hB)]

/-- Two items with one graph, which is an item of `A` at the actual world, of types with the same
image, are identified at every world. -/
theorem XMK_toG_rel (a c : Code XMK_B) (x : XMK_U.El a) (z : XMK_U.El c) (g : XMK_G) (w : Fin 3)
    (hx : XMK_toG a x = some g) (hz : XMK_toG c z = some g) (hi : XMK_img a = XMK_img c)
    (hg : XMK_U.rel XMK_A (0 : Fin 3) g g) : XMK_CR a c w x z := by
  rcases XMK_toG_some a x g hx with hA | hB
  · rcases XMK_img_A hA with rfl | rfl <;> rcases XMK_img_A (hi.symm.trans hA) with rfl | rfl <;>
    · have e1 : x = g := Option.some.inj hx
      have e2 : z = g := Option.some.inj hz
      subst e1; subst e2
      exact fun v _ p q hpq => hg v (Or.inr rfl) p q hpq
  · obtain rfl := XMK_img_Bd hB
    obtain rfl := XMK_img_Bd (hi.symm.trans hB)
    have e1 : x = g := Option.some.inj hx
    have e2 : z = g := Option.some.inj hz
    subst e1; subst e2
    exact fun v _ p q hpq => hg v (Or.inr rfl) p q hpq

/-! ### The frame -/

/-- Identity at a world in `𝔐_k,x`. -/
def XMK_eqv (a b : Code XMK_B) (x : XMK_U.El a) (y : XMK_U.El b) (w : Fin 3) : Prop :=
  (XMK_img a = XMK_img b ∧ XMK_CR a b w x y) ∨
  (w = 0 ∧ XMK_img a ≠ XMK_img b ∧
    ∃ g : XMK_G, XMK_toG a x = some g ∧ XMK_toG b y = some g ∧ XMK_U.rel XMK_A (0 : Fin 3) g g)

theorem XMK_eqv_resp (u : Fin 3) (a b : Code XMK_B) (x x' : XMK_U.El a) (y y' : XMK_U.El b)
    (hx : XMK_U.rel a u x x') (hy : XMK_U.rel b u y y') : XMK_eqv a b x y u ↔ XMK_eqv a b x' y' u := by
  have hx' := (XMK_CR_diag a u x x').mp hx
  have hy' := (XMK_CR_diag b u y y').mp hy
  constructor
  · rintro (⟨hi, h⟩ | ⟨hu, hi, g, h1, h2, h3⟩)
    · exact Or.inl ⟨hi, XMK_CR_trans hi rfl (XMK_CR_trans rfl hi (XMK_CR_symm rfl hx') h) hy'⟩
    · exact Or.inr ⟨hu, hi, g, (XMK_toG_CR a a u x x' rfl hx').symm.trans h1,
        (XMK_toG_CR b b u y y' rfl hy').symm.trans h2, h3⟩
  · rintro (⟨hi, h⟩ | ⟨hu, hi, g, h1, h2, h3⟩)
    · exact Or.inl ⟨hi, XMK_CR_trans hi rfl (XMK_CR_trans rfl hi hx' h) (XMK_CR_symm rfl hy')⟩
    · exact Or.inr ⟨hu, hi, g, (XMK_toG_CR a a u x x' rfl hx').trans h1,
        (XMK_toG_CR b b u y y' rfl hy').trans h2, h3⟩

theorem XMK_eqv_same (a : Code XMK_B) (x y : XMK_U.El a) (w : Fin 3) : XMK_eqv a a x y w ↔ XMK_U.rel a w x y :=
  ⟨fun h => h.elim (fun h => (XMK_CR_diag a w x y).mpr h.2) (fun h => absurd rfl h.2.1),
    fun h => Or.inl ⟨rfl, (XMK_CR_diag a w x y).mp h⟩⟩

theorem XMK_eqv_symm {a b : Code XMK_B} {x : XMK_U.El a} {y : XMK_U.El b} {w : Fin 3}
    (h : XMK_eqv a b x y w) : XMK_eqv b a y x w := by
  rcases h with ⟨hi, h⟩ | ⟨hu, hi, g, h1, h2, h3⟩
  · exact Or.inl ⟨hi.symm, XMK_CR_symm hi h⟩
  · exact Or.inr ⟨hu, fun e => hi e.symm, g, h2, h1, h3⟩

theorem XMK_eqv_trans {a b c : Code XMK_B} {x : XMK_U.El a} {y : XMK_U.El b} {z : XMK_U.El c} {w : Fin 3}
    (h1 : XMK_eqv a b x y w) (h2 : XMK_eqv b c y z w) : XMK_eqv a c x z w := by
  rcases h1 with ⟨i1, r1⟩ | ⟨u1, n1, g, gx, gy, hg⟩
  · rcases h2 with ⟨i2, r2⟩ | ⟨u2, n2, g', gy', gz, hg'⟩
    · exact Or.inl ⟨i1.trans i2, XMK_CR_trans i1 i2 r1 r2⟩
    · exact Or.inr ⟨u2, fun e => n2 (i1.symm.trans e), g', (XMK_toG_CR a b w x y i1 r1).trans gy', gz, hg'⟩
  · rcases h2 with ⟨i2, r2⟩ | ⟨_, n2, g', gy', gz, _⟩
    · exact Or.inr ⟨u1, fun e => n1 (e.trans i2.symm), g, gx, (XMK_toG_CR b c w y z i2 r2).symm.trans gy, hg⟩
    · have e : g = g' := Option.some.inj (gy.symm.trans gy')
      subst e
      by_cases hac : XMK_img a = XMK_img c
      · exact Or.inl ⟨hac, XMK_toG_rel a c x z g w gx gz hac hg⟩
      · exact Or.inr ⟨u1, hac, g, gx, gz, hg⟩

/-- At world `1`, identity is invariant under putting `e` for `d`. -/
theorem XMK_eqv_one {a a' b b' : Code XMK_B} {x : XMK_U.El a} {x' : XMK_U.El a'} {y : XMK_U.El b}
    {y' : XMK_U.El b'} (ia : XMK_img a = XMK_img a') (ib : XMK_img b = XMK_img b')
    (hx : XMK_CR a a' (1 : Fin 3) x x') (hy : XMK_CR b b' (1 : Fin 3) y y') :
    XMK_eqv a b x y (1 : Fin 3) ↔ XMK_eqv a' b' x' y' (1 : Fin 3) := by
  constructor
  · rintro (⟨h2, h3⟩ | ⟨hu, _⟩)
    · exact Or.inl ⟨ia.symm.trans (h2.trans ib),
        XMK_CR_trans (ia.symm.trans h2) ib (XMK_CR_trans ia.symm h2 (XMK_CR_symm ia hx) h3) hy⟩
    · exact absurd hu (by decide)
  · rintro (⟨h2, h3⟩ | ⟨hu, _⟩)
    · exact Or.inl ⟨ia.trans (h2.trans ib.symm),
        XMK_CR_trans ia (h2.trans ib.symm) hx (XMK_CR_trans h2 ib.symm h3 (XMK_CR_symm ib hy))⟩
    · exact absurd hu (by decide)

/-- `𝔐_k,x`. -/
def XMK_F : Frame where
  U := XMK_U
  eqv := XMK_eqv
  teq := fun a b w => (w ≠ (1 : Fin 3) → a = b) ∧ XMK_img a = XMK_img b
  eqv_resp := XMK_eqv_resp

theorem XMK_heq : ∀ a x y w, XMK_F.eqv a a x y w ↔ XMK_F.U.rel a w x y := XMK_eqv_same

theorem XMK_R_ne {w u : Fin 3} (h : XMK_U.R w u) (hu : u ≠ 1) : w ≠ 1 := by
  rcases h with rfl | rfl
  · exact hu
  · decide

/-- The admissible relations of `𝔐_k,x`: identity between types with the same image, at world `1`,
and identity within a type elsewhere. -/
def XMK_Inv : KInv XMK_F where
  Adm := fun w a a' S => XMK_img a = XMK_img a' ∧ (w ≠ (1 : Fin 3) → a = a') ∧
    ∀ u x y, S u x y ↔ XMK_CR a a' u x y
  amono := fun ⟨h1, h2, h3⟩ hv => ⟨h1, fun hv1 => h2 (XMK_R_ne hv hv1), h3⟩
  smono := fun ⟨_, _, h3⟩ u u' x x' _ hu h => (h3 u' x x').mpr (XMK_CR_mono _ _ u u' x x' hu ((h3 u x x').mp h))
  refl := fun _ a => ⟨rfl, fun _ => rfl, fun u x y => XMK_CR_diag a u x y⟩
  arrow := by
    intro w a a' c c' S T hS hT
    obtain ⟨h1, h2, h3⟩ := hS
    obtain ⟨k1, k2, k3⟩ := hT
    refine ⟨by show Code.arr (XMK_img a) (XMK_img c) = Code.arr (XMK_img a') (XMK_img c'); rw [h1, k1],
      fun hw => by rw [h2 hw, k2 hw], fun u f f' => ?_⟩
    exact forall_congr' fun v => imp_congr Iff.rfl (forall_congr' fun x => forall_congr' fun x' =>
      imp_congr (h3 v x x') (k3 v _ _))
  total := by
    intro w a a' S hS u _ x hx
    obtain ⟨h1, _, h3⟩ := hS
    obtain ⟨hxT, hTT⟩ := (XMK_shape (XMK_img a)).2.2.1 a a' rfl h1.symm u x ((XMK_CR_diag a u x x).mp hx)
    exact ⟨XMK_Tf a a' x, (XMK_CR_diag a' u _ _).mpr hTT, (h3 u x _).mpr hxT⟩
  onto := by
    intro w a a' S hS u _ y hy
    obtain ⟨h1, _, h3⟩ := hS
    obtain ⟨hTy, hTT⟩ := (XMK_shape (XMK_img a)).2.2.2 a a' rfl h1.symm u y ((XMK_CR_diag a' u y y).mp hy)
    exact ⟨XMK_Tg a a' y, (XMK_CR_diag a u _ _).mpr hTT, (h3 u _ y).mpr hTy⟩
  teq := by
    intro w a a' b b' S T hS hT u hu
    obtain ⟨h1, h2, _⟩ := hS
    obtain ⟨k1, k2, _⟩ := hT
    constructor
    · rintro ⟨e1, e2⟩
      exact ⟨fun hv => (h2 (XMK_R_ne hu hv)).symm.trans ((e1 hv).trans (k2 (XMK_R_ne hu hv))),
        h1.symm.trans (e2.trans k1)⟩
    · rintro ⟨e1, e2⟩
      exact ⟨fun hv => (h2 (XMK_R_ne hu hv)).trans ((e1 hv).trans (k2 (XMK_R_ne hu hv)).symm),
        h1.trans (e2.trans k1.symm)⟩
  eqv := by
    intro w a a' b b' S T hS hT u hu x x' y y' hx hy
    obtain ⟨h1, h2, h3⟩ := hS
    obtain ⟨k1, k2, k3⟩ := hT
    by_cases hu1 : (u : Fin 3) = (1 : Fin 3)
    · subst hu1
      exact XMK_eqv_one h1 k1 ((h3 _ x x').mp hx) ((k3 _ y y').mp hy)
    · have hw := XMK_R_ne hu hu1
      obtain rfl := h2 hw
      obtain rfl := k2 hw
      exact XMK_eqv_resp u a b x x' y y' ((XMK_CR_diag a u x x').mpr ((h3 u x x').mp hx))
        ((XMK_CR_diag b u y y').mpr ((k3 u y y').mp hy))

/-- `𝔐_k,x` is a model of PI⁻ at every world: LL≈ holds at world `1` by the invariance lemma. -/
theorem XMK_isModelAt : XMK_F.IsModelAt := by
  obtain ⟨h1, h2, h3⟩ := XMK_F.idAx_of (fun a x w hx => (XMK_heq a x x w).mpr hx)
    (fun _ _ _ _ _ h => XMK_eqv_symm h) (fun _ _ _ _ _ _ _ h1 h2 => XMK_eqv_trans h1 h2)
  refine ⟨h1, h2, h3, XMK_F.refTeq_of fun _ _ => ⟨fun _ => rfl, rfl⟩, ?_⟩
  intro n Γ Q w ρ _ env henv
  refine XMK_F.holdsAt_tall _ _ _ w |>.mpr fun a _ => XMK_F.holdsAt_tall _ _ _ w |>.mpr fun b _ => ?_
  refine (XMK_F.holdsAt_imp _ _ _ _ w).mpr fun hab => ?_
  obtain ⟨e1, e2⟩ := (XMK_F.holdsAt_teq (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env w).mp hab
  refine (XMK_F.holdsAt_imp _ _ _ _ w).mpr fun hq => ?_
  exact XMK_Inv.llTeq_at Q w ρ env henv a b (XMK_CR a b) ⟨e2, e1, fun _ _ _ => Iff.rfl⟩ hq

theorem XMK_LLEqv : XMK_F.Valid LLEqv := fun ρ hρ env henv => XMK_F.LLEqv_of XMK_heq _ ρ hρ env henv

theorem XMK_Class : ∀ χ, ClassSch χ → XMK_F.Valid χ :=
  XMK_F.Class_valid XMK_isModelAt (XMK_F.LLEqv_of XMK_heq) XMK_heq

theorem XMK_of_prov {φ : Fm Ctx.nil} (h : Prov SIE Ctx.nil φ) : XMK_F.Valid φ :=
  KIE.valid_of_PIc XMK_F XMK_isModelAt (XMK_F.LLEqv_of XMK_heq) XMK_heq h

/-! ### Every theorem of PIᶜ is valid -/

open Derive in
theorem XMK_Bool : ∀ φ, BoolSch φ → XMK_F.Valid φ := fun φ h => XMK_of_prov (d_Bool_of_Class SIE_C φ h)
theorem XMK_IdId : XMK_F.Valid IdId := XMK_of_prov (d_IdId_of_Class SIE_C)
theorem XMK_NIEqv : XMK_F.Valid NIEqv := XMK_of_prov (d_NIEqv_of_Class SIE_C SIE_LL)
theorem XMK_NITeq : XMK_F.Valid NITeq := XMK_of_prov (d_NITeq_of_Class SIE_C)
theorem XMK_TNec : XMK_F.Valid TNec := XMK_of_prov (d_TNec_of_Class SIE_C)
theorem XMK_TCBF : ∀ χ, TCBFSch χ → XMK_F.Valid χ := fun χ h => XMK_of_prov (d_TCBF_of_Class SIE_C SIE_LL χ h)
theorem XMK_Nec : XMK_F.Valid Nec := XMK_of_prov (d_Nec_of_Class SIE_C)
theorem XMK_CBF : XMK_F.Valid CBF := XMK_of_prov (d_CBF_of_Class SIE_C SIE_LL)
theorem XMK_Truth : XMK_F.Valid Truth := XMK_of_prov (Derive.d_Truth SIE_LL)
theorem XMK_TopBot : XMK_F.Valid TopBot := XMK_of_prov (Derive.d_TopBot SIE_LL)
theorem XMK_Cantor : XMK_F.Valid Cantor := XMK_of_prov (Derive.d_Cantor SIE_LL)
theorem XMK_WCong : XMK_F.Valid WCong := XMK_of_prov (Derive.d_WCong SIE_LL)

theorem XMK_Valid_of {φ : Fm Ctx.nil} (h : XMK_F.HoldsAt φ (fun i => i.elim0) () (0 : Fin 3)) : XMK_F.Valid φ := by
  intro ρ _ env _
  have e1 : ρ = fun i => i.elim0 := funext fun i => i.elim0
  subst e1
  exact h

/-! ### LL≡/≈ holds for every polymorphic predicate, with parameters; LL≡-Poly fails -/

/-- The predicate of a polymorphic Leibniz law, at its two types. -/
theorem XMK_evalP {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XMK_F.U.TEnv n)
    (env : XMK_F.U.Env Γ ρ) (a b : Code XMK_B) (x : XMK_U.El a) (y : XMK_U.El b) :
    HEq (XMK_F.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y)) (XMK_F.eval P ρ env) := by
  have e1 : XMK_F.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y) =
      XMK_F.eval (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) :=
    XMK_F.eval_wk tv0 (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) y
  have e2 : XMK_F.eval (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) =
      XMK_F.eval P.twk.twk (scons b (scons a ρ)) env := XMK_F.eval_wk tv1 P.twk.twk (scons b (scons a ρ)) env x
  exact (heq_of_eq (e1.trans e2)).trans ((XMK_F.eval_twk P.twk b (scons a ρ) env).trans (XMK_F.eval_twk P a ρ env))

theorem XMK_evalP1 {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XMK_F.U.TEnv n)
    (env : XMK_F.U.Env Γ ρ) (a b : Code XMK_B) (x : XMK_U.El a) (y : XMK_U.El b) (w : Fin 3) :
    XMK_F.HoldsAt (.app (.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (.var (.there .here))) (scons b (scons a ρ))
      ((env, x), y) w ↔ XMK_F.eval P ρ env a x w := by
  have h1 : HEq (XMK_F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (scons b (scons a ρ)) ((env, x), y))
      (XMK_F.eval P ρ env a) :=
    (XMK_F.heq_eval_tapp ((P.twk.twk.wk tv1).wk tv0) tv1 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => XMK_U.El c → Fin 3 → Prop) (Q := fun c => XMK_U.El c → Fin 3 → Prop)
        (fun _ => rfl) (XMK_evalP P ρ env a b x y) rfl)
  have e := congrFun (congrFun (eq_of_heq h1) x) w
  exact Iff.of_eq e

theorem XMK_evalP0 {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XMK_F.U.TEnv n)
    (env : XMK_F.U.Env Γ ρ) (a b : Code XMK_B) (x : XMK_U.El a) (y : XMK_U.El b) (w : Fin 3) :
    XMK_F.HoldsAt (.app (.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (.var .here)) (scons b (scons a ρ))
      ((env, x), y) w ↔ XMK_F.eval P ρ env b y w := by
  have h1 : HEq (XMK_F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (scons b (scons a ρ)) ((env, x), y))
      (XMK_F.eval P ρ env b) :=
    (XMK_F.heq_eval_tapp ((P.twk.twk.wk tv1).wk tv0) tv0 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => XMK_U.El c → Fin 3 → Prop) (Q := fun c => XMK_U.El c → Fin 3 → Prop)
        (fun _ => rfl) (XMK_evalP P ρ env a b x y) rfl)
  have e := congrFun (congrFun (eq_of_heq h1) y) w
  exact Iff.of_eq e

/-- At the actual world, a polymorphic predicate does not tell apart items identical there. -/
theorem XMK_poly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XMK_F.U.TEnv n)
    (env : XMK_F.U.Env Γ ρ) (henv : XMK_F.EnvAdm Γ ρ (0 : Fin 3) env) (a : Code XMK_B) (x y : XMK_U.El a)
    (hxy : XMK_U.rel a (0 : Fin 3) x y) :
    XMK_F.eval P ρ env a x (0 : Fin 3) → XMK_F.eval P ρ env a y (0 : Fin 3) :=
  (XMK_F.adm_eval P ρ (0 : Fin 3) env henv (0 : Fin 3) (XMK_U.Rrefl _) a a (XMK_U.rel a)
    (XMK_F.hom.refl (0 : Fin 3) a) (0 : Fin 3) (XMK_U.Rrefl _) x y hxy (0 : Fin 3) (XMK_U.Rrefl _)).mp

/-- LL≡/≈ holds, for every polymorphic predicate, with parameters: at the actual world `≈` is
identity of types. -/
theorem XMK_Bridge {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : XMK_F.Valid (Bridge P) := by
  intro ρ _ env henv
  refine (XMK_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XMK_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XMK_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XMK_F.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (XMK_F.holdsAt_imp _ _ _ _ _).mpr fun h => (XMK_F.holdsAt_imp _ _ _ _ _).mpr fun hPx => ?_
  obtain ⟨h1, h2⟩ := (XMK_F.holdsAt_conj _ _ _ _ _).mp h
  have eab : a = b := ((XMK_F.holdsAt_teq _ _ _ _ _).mp h2).1 (by decide : (0 : Fin 3) ≠ 1)
  subst eab
  have hxy : XMK_U.rel a (0 : Fin 3) x y := (XMK_heq _ _ _ _).mp ((XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h1)
  exact (XMK_evalP0 P ρ env a a x y _).mpr
    (XMK_poly P ρ env henv a x y hxy ((XMK_evalP1 P ρ env a a x y _).mp hPx))

/-- What `λγ.λz.(γ ≈ e)` says of an item. -/
theorem XMK_PredE (ρ : XMK_F.U.TEnv 0) (a : Code XMK_B) (x : XMK_U.El a) (w : Fin 3) :
    XMK_F.eval PredE ρ () a x w ↔ XMK_F.teq a .e w :=
  XMK_F.holdsAt_teq (Γ := (Ctx.nil.text).ext tv0) tv0 tyE (scons a ρ) ((), x) w

/-- LL≡-Poly fails, for `λγ.λz.(γ ≈ e)`: each entity is identified with its copy in `d`. -/
theorem XMK_not_LLPoly : ¬ XMK_F.Valid (LLPoly PredE) := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_tall _ _ _ _).mp ((XMK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base .d) (Or.inr trivial)
  have h2 := (XMK_F.holdsAt_all _ _ _ _ _).mp ((XMK_F.holdsAt_all _ _ _ _ _).mp h1 true rfl) true rfl
  have h3 := (XMK_F.holdsAt_imp _ _ _ _ _).mp h2 ((XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (Or.inl ⟨rfl, rfl⟩))
  have h4 := (XMK_F.holdsAt_imp _ _ _ _ _).mp h3 ((XMK_evalP1 PredE _ () .e (.base .d) true true _).mpr
    ((XMK_PredE _ .e true _).mpr ⟨fun _ => rfl, rfl⟩))
  have h5 := (XMK_PredE _ (.base .d) true _).mp ((XMK_evalP0 PredE _ () .e (.base .d) true true _).mp h4)
  exact nomatch h5.1 (by decide : (0 : Fin 3) ≠ 1)

/-! ### The targets: ND≈, Ext≈, Int≈, NI×, PCong, TBF, BF, ND× -/

/-- `¬(e ≈ d)`, but `e ≈ d` at world `1`. -/
theorem XMK_not_NDTeq : ¬ XMK_F.Valid NDTeq := fun h => by
  have h0 := h (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_tall _ _ _ _).mp ((XMK_F.holdsAt_tall _ _ _ _).mp h0 .e (Or.inr trivial))
    (.base .d) (Or.inr trivial)
  have h2 := (XMK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XMK_F.holdsAt_neg _ _ _ _).mpr fun ht =>
    nomatch ((XMK_F.holdsAt_teq _ _ _ _ _).mp ht).1 (by decide : (0 : Fin 3) ≠ 1))
  have h3 := (XMK_F.box_of XMK_heq _ _ _ _).mp h2 (1 : Fin 3) (Or.inr rfl)
  exact (XMK_F.holdsAt_neg _ _ _ _).mp h3 ((XMK_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun h => absurd rfl h, rfl⟩)

/-- At every world, each item of `e` is identified with its copy in `d`, and conversely. -/
theorem XMK_ed_sub (w : Fin 3) : XMK_F.HoldsAt (Tm.conj (subT : Fm (Ctx.nil.text.text)) supT)
    (scons (.base .d) (scons .e (fun i => i.elim0))) () w := by
  refine (XMK_F.holdsAt_conj _ _ _ _ _).mpr ⟨?_, ?_⟩
  · refine (XMK_F.holdsAt_all _ _ _ _ _).mpr fun x hx => (XMK_F.holdsAt_ex _ _ _ _ _).mpr ⟨x, hx, ?_⟩
    exact (XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (Or.inl ⟨rfl, rfl⟩)
  · refine (XMK_F.holdsAt_all _ _ _ _ _).mpr fun y hy => (XMK_F.holdsAt_ex _ _ _ _ _).mpr ⟨y, hy, ?_⟩
    exact (XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (Or.inl ⟨rfl, rfl⟩)

theorem XMK_not_ExtT : ¬ XMK_F.Valid ExtT := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_tall _ _ _ _).mp ((XMK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base .d) (Or.inr trivial)
  have h2 := (XMK_F.holdsAt_imp _ _ _ _ _).mp h1 (XMK_ed_sub (0 : Fin 3))
  exact nomatch ((XMK_F.holdsAt_teq _ _ _ _ _).mp h2).1 (by decide : (0 : Fin 3) ≠ 1)

theorem XMK_not_IntT : ¬ XMK_F.Valid IntT := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_tall _ _ _ _).mp ((XMK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base .d) (Or.inr trivial)
  have h2 := (XMK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XMK_F.holdsAt_conj _ _ _ _ _).mpr
    ⟨(XMK_F.box_of XMK_heq _ _ _ _).mpr fun v _ => ((XMK_F.holdsAt_conj _ _ _ _ _).mp (XMK_ed_sub v)).1,
     (XMK_F.box_of XMK_heq _ _ _ _).mpr fun v _ => ((XMK_F.holdsAt_conj _ _ _ _ _).mp (XMK_ed_sub v)).2⟩)
  exact nomatch ((XMK_F.holdsAt_teq _ _ _ _ _).mp h2).1 (by decide : (0 : Fin 3) ≠ 1)

/-- The constant function. -/
def XMK_k : XMK_G := fun _ => true

theorem XMK_k_adm (w : Fin 3) : XMK_U.rel XMK_A w XMK_k XMK_k := fun _ _ _ _ _ => rfl
theorem XMK_k_admB (w : Fin 3) : XMK_U.rel XMK_Bd w XMK_k XMK_k := fun _ _ _ _ _ => rfl

theorem XMK_A_ne_Bd : XMK_img XMK_A ≠ XMK_img XMK_Bd := fun h => by
  injection h with _ h2
  exact nomatch h2

/-- At the actual world, each item of `A` is identified with the same function, of type `B`. -/
theorem XMK_AB (x : XMK_G) (hx : XMK_U.rel XMK_A (0 : Fin 3) x x) : XMK_eqv XMK_A XMK_Bd x x (0 : Fin 3) :=
  Or.inr ⟨rfl, XMK_A_ne_Bd, x, rfl, rfl, hx⟩

/-- The constant functions of `A` and of `B` are identified, but not at world `1`. -/
theorem XMK_not_NIX : ¬ XMK_F.Valid NIX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_tall _ _ _ _).mp ((XMK_F.holdsAt_tall _ _ _ _).mp h XMK_A (Or.inr ⟨trivial, trivial⟩))
    XMK_Bd (Or.inr ⟨trivial, trivial⟩)
  have h2 := (XMK_F.holdsAt_all _ _ _ _ _).mp ((XMK_F.holdsAt_all _ _ _ _ _).mp h1 XMK_k (XMK_k_adm _))
    XMK_k (XMK_k_admB _)
  have h3 := (XMK_F.holdsAt_imp _ _ _ _ _).mp h2
    ((XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XMK_AB XMK_k (XMK_k_adm _)))
  have h4 := (XMK_F.box_of XMK_heq _ _ _ _).mp h3 (1 : Fin 3) (Or.inr rfl)
  rcases (XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h4 with ⟨hi, _⟩ | ⟨hu, _⟩
  · exact XMK_A_ne_Bd hi
  · exact absurd hu (by decide)

/-- The constant functions of `A` and `B` are identified, but their values, of types `e` and `d₂`,
are not. -/
theorem XMK_not_PCong : ¬ XMK_F.Valid PCong := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_tall _ _ _ _).mp ((XMK_F.holdsAt_tall _ _ _ _).mp
    ((XMK_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)) .e (Or.inr trivial)) (.base .d2) (Or.inr trivial)
  have h2 := (XMK_F.holdsAt_all _ _ _ _ _).mp ((XMK_F.holdsAt_all _ _ _ _ _).mp
    ((XMK_F.holdsAt_all _ _ _ _ _).mp h1 XMK_k (XMK_k_adm _)) XMK_k (XMK_k_admB _)) (fun _ => True) (fun _ _ => Iff.rfl)
  have h3 := (XMK_F.holdsAt_imp _ _ _ _ _).mp h2
    ((XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XMK_AB XMK_k (XMK_k_adm _)))
  rcases (XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h3 with ⟨hi, _⟩ | ⟨_, _, g, hg, _, _⟩
  · exact nomatch hi
  · exact nomatch hg

theorem XMK_phiBF_iff (a : Code XMK_B) (w : Fin 3) :
    XMK_F.HoldsAt phiBF (scons a (fun i => i.elim0)) () w ↔
      ¬ ∀ x : XMK_U.El a, XMK_U.rel a w x x → ∀ y : XMK_U.El a, XMK_U.rel a w y y → XMK_U.rel a w x y := by
  refine (XMK_F.holdsAt_neg _ _ _ _).trans (not_congr ?_)
  refine (XMK_F.holdsAt_all _ _ _ _ _).trans (forall_congr' fun x => imp_congr Iff.rfl ?_)
  refine (XMK_F.holdsAt_all _ _ _ _ _).trans (forall_congr' fun y => imp_congr Iff.rfl ?_)
  exact (XMK_F.holdsAt_eqv _ _ _ _ _ _ _).trans (XMK_heq _ _ _ _)

/-- Each type not mentioning `c` has two items which are distinct at every world. -/
theorem XMK_two_items : ∀ a : Code XMK_B, XMK_noC a → ∃ x y : XMK_U.El a,
    (∀ w, XMK_U.rel a w x x) ∧ (∀ w, XMK_U.rel a w y y) ∧ ∀ w, ¬ XMK_U.rel a w x y
  | .e, _ => ⟨true, false, fun _ => rfl, fun _ => rfl, fun _ h => Bool.noConfusion h⟩
  | .t, _ => ⟨fun _ => True, fun _ => False, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun w h => (h w (XMK_U.Rrefl w)).mp trivial⟩
  | .base .d, _ => ⟨true, false, fun _ => rfl, fun _ => rfl, fun _ h => Bool.noConfusion h⟩
  | .base .d2, _ => ⟨true, false, fun _ => rfl, fun _ => rfl, fun _ h => Bool.noConfusion h⟩
  | .base .c, h => h.elim
  | .arr a c, ⟨_, hc⟩ => by
    obtain ⟨y1, y2, h1, h2, h12⟩ := XMK_two_items c hc
    obtain ⟨x0, hx0⟩ := XMK_U.adm_nonempty a
    refine ⟨fun _ => y1, fun _ => y2, fun _ v _ _ _ _ => h1 v, fun _ v _ _ _ _ => h2 v, fun w h => ?_⟩
    exact h12 w (h w (XMK_U.Rrefl w) x0 x0 (hx0 w))

/-- Every type at the actual world necessarily has two distinct items; but at world `2` the type
`c` has only one. -/
theorem XMK_not_TBF : ¬ XMK_F.Valid (TBFI phiBF) := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have hA : XMK_F.HoldsAt (tall (boxF phiBF)) (fun i => i.elim0) () (0 : Fin 3) := by
    refine (XMK_F.holdsAt_tall _ _ _ _).mpr fun a ha => (XMK_F.box_of XMK_heq _ _ _ _).mpr fun v _ => ?_
    have hna : XMK_noC a := Or.resolve_left ha (fun h => absurd h (by decide))
    obtain ⟨x, y, hx, hy, hxy⟩ := XMK_two_items a hna
    exact (XMK_phiBF_iff a v).mpr fun h => hxy v (h x (hx v) y (hy v))
  have hB := (XMK_F.box_of XMK_heq _ _ _ _).mp ((XMK_F.holdsAt_imp _ _ _ _ _).mp h hA) (2 : Fin 3) (Or.inr rfl)
  have hd := (XMK_F.holdsAt_tall _ _ _ _).mp hB (.base .c) (Or.inl rfl)
  exact (XMK_phiBF_iff (.base .c) (2 : Fin 3)).mp hd fun _ _ _ _ => rfl

theorem XMK_not_TBFSch : ¬ ∀ χ, TBFSch χ → XMK_F.Valid χ := fun h => XMK_not_TBF (h _ ⟨phiBF, rfl⟩)

open Classical in
/-- The function sending `p` to whether `p` is true at world `1`. -/
noncomputable def XMK_f1 (p : Fin 3 → Prop) : Bool := if p (1 : Fin 3) then true else false

theorem XMK_f1_pos (p : Fin 3 → Prop) (hp : p (1 : Fin 3)) : XMK_f1 p = true := by
  unfold XMK_f1
  split
  · rfl
  · rename_i h; exact absurd hp h

theorem XMK_f1_neg (p : Fin 3 → Prop) (hp : ¬ p (1 : Fin 3)) : XMK_f1 p = false := by
  unfold XMK_f1
  split
  · rename_i h; exact absurd h hp
  · rfl

/-- At world `1`, `f₁` is an item of `A`. -/
theorem XMK_f1_adm : XMK_U.rel XMK_A (1 : Fin 3) XMK_f1 XMK_f1 := by
  intro v hv p q hpq
  have hv' : v = (1 : Fin 3) := by
    rcases hv with h | h
    · exact h.symm
    · exact absurd h (by decide)
  subst hv'
  have e : p (1 : Fin 3) = q (1 : Fin 3) := propext (hpq (1 : Fin 3) (Or.inl rfl))
  show XMK_f1 p = XMK_f1 q
  unfold XMK_f1
  rw [e]

/-- Identity at a world, at `A`, implies equality. -/
theorem XMK_relA_eq {v : Fin 3} {x y : XMK_G} (h : XMK_U.rel XMK_A v x y) : x = y :=
  funext fun p => h v (XMK_U.Rrefl v) p p (fun _ _ => Iff.rfl)

/-- The proposition true at `1` where `p` is, and elsewhere where `q` is. -/
def XMK_mix (p q : Fin 3 → Prop) : Fin 3 → Prop := fun w => (w = 1 ∧ p w) ∨ (w ≠ 1 ∧ q w)

/-- An item of `A` at the actual world is constant. -/
theorem XMK_const_of_adm0 {x : XMK_G} (h : XMK_U.rel XMK_A (0 : Fin 3) x x) (p q : Fin 3 → Prop) : x p = x q := by
  have h1 : x p = x (XMK_mix p q) := h (1 : Fin 3) (Or.inr rfl) p (XMK_mix p q) (fun u hu => by
    rcases hu with rfl | hu
    · exact ⟨fun hp => Or.inl ⟨rfl, hp⟩, fun h' => h'.elim (fun h'' => h''.2) (fun h'' => absurd rfl h''.1)⟩
    · exact absurd hu (by decide))
  have h2 : x (XMK_mix p q) = x q := h (2 : Fin 3) (Or.inr rfl) (XMK_mix p q) q (fun u hu => by
    rcases hu with rfl | hu
    · exact ⟨fun h' => h'.elim (fun h'' => absurd h''.1 (by decide)) (fun h'' => h''.2),
        fun hq => Or.inr ⟨by decide, hq⟩⟩
    · exact absurd hu (by decide))
  exact h1.trans h2

/-- The property of being constant, of items of `A`. -/
def XMK_FC : XMK_U.El (.arr XMK_A .t) := fun (x : XMK_G) (_ : Fin 3) => ∀ p q, x p = x q

theorem XMK_FC_adm : XMK_U.rel (.arr XMK_A .t) (0 : Fin 3) XMK_FC XMK_FC := by
  intro v _ x y hxy
  have e : x = y := XMK_relA_eq hxy
  subst e
  exact fun _ _ => Iff.rfl

/-- Every item of `A` at the actual world is necessarily constant, but at world `1`, `f₁` is an
item of `A` which is not constant. -/
theorem XMK_not_BF : ¬ XMK_F.Valid BF := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_all _ _ _ _ _).mp ((XMK_F.holdsAt_tall _ _ _ _).mp h XMK_A (Or.inr ⟨trivial, trivial⟩))
    XMK_FC XMK_FC_adm
  have h2 := (XMK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XMK_F.holdsAt_all _ _ _ _ _).mpr fun _ hx =>
    (XMK_F.box_of XMK_heq _ _ _ _).mpr fun _ _ => XMK_const_of_adm0 hx)
  have h3 := (XMK_F.box_of XMK_heq _ _ _ _).mp h2 (1 : Fin 3) (Or.inr rfl)
  have h4 := (XMK_F.holdsAt_all _ _ _ _ _).mp h3 XMK_f1 XMK_f1_adm
  have h5 : ∀ p q : Fin 3 → Prop, XMK_f1 p = XMK_f1 q := h4
  have h6 := h5 (fun _ => True) (fun _ => False)
  rw [XMK_f1_pos _ trivial, XMK_f1_neg _ (fun h => h)] at h6
  exact Bool.noConfusion h6

/-- `⊤` and the proposition false just at the actual world are distinct, but identical at world `1`. -/
theorem XMK_not_NDX : ¬ XMK_F.Valid NDX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_tall _ _ _ _).mp ((XMK_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)) .t (Or.inr trivial)
  have h2 := (XMK_F.holdsAt_all _ _ _ _ _).mp ((XMK_F.holdsAt_all _ _ _ _ _).mp h1 (fun _ => True)
    (fun _ _ => Iff.rfl)) (fun (w : Fin 3) => w = 1) (fun _ _ => Iff.rfl)
  refine (XMK_F.holdsAt_neg _ _ _ _).mp ((XMK_F.box_of XMK_heq _ _ _ _).mp ((XMK_F.holdsAt_imp _ _ _ _ _).mp h2
    ((XMK_F.holdsAt_neg _ _ _ _).mpr fun he => ?_)) (1 : Fin 3) (Or.inr rfl)) ?_
  · have he' := (XMK_heq .t _ _ _).mp ((XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mp he)
    have h3 : True ↔ (0 : Fin 3) = 1 := he' (0 : Fin 3) (Or.inl rfl)
    exact absurd (h3.mp trivial) (by decide)
  · refine (XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ((XMK_heq .t _ _ _).mpr fun u hu => ?_)
    rcases hu with rfl | hu
    · exact ⟨fun _ => rfl, fun _ => trivial⟩
    · exact absurd hu (by decide)

/-! ### The other principles -/

/-- The relation between a proposition and whether it is true. -/
def XMK_RC : XMK_U.El (.arr .t (.arr .e .t)) := fun (p : Fin 3 → Prop) (y : Bool) (u : Fin 3) => (y = true ↔ p u)

theorem XMK_RC_adm : XMK_U.rel (.arr .t (.arr .e .t)) (0 : Fin 3) XMK_RC XMK_RC := by
  intro v _ p q hpq v' hv' y y' hyy' u hu
  have e : y = y' := hyy'
  subst e
  exact iff_congr Iff.rfl (hpq u (XMK_U.Rtrans _ _ _ hv' hu))

/-- Each proposition is related to an entity, but no item of `t → e` at the actual world chooses
one: such an item is constant. -/
theorem XMK_not_Choice : ¬ XMK_F.Valid Choice := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_all _ _ _ _ _).mp ((XMK_F.holdsAt_tall _ _ _ _).mp
    ((XMK_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)) .e (Or.inr trivial)) XMK_RC XMK_RC_adm
  have h2 := (XMK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XMK_F.holdsAt_all _ _ _ _ _).mpr fun p _ => by
    refine (XMK_F.holdsAt_ex _ _ _ _ _).mpr ?_
    rcases Classical.em (p (0 : Fin 3)) with hp | hp
    · exact ⟨true, rfl, show (true = true ↔ p (0 : Fin 3)) from ⟨fun _ => hp, fun _ => rfl⟩⟩
    · exact ⟨false, rfl, show (false = true ↔ p (0 : Fin 3)) from
        ⟨fun e => Bool.noConfusion e, fun h => absurd h hp⟩⟩)
  obtain ⟨f, hf, h3⟩ := (XMK_F.holdsAt_ex _ _ _ _ _).mp h2
  have hc := XMK_const_of_adm0 hf
  have h4 : f (fun _ => True) = true ↔ True :=
    (XMK_F.holdsAt_all _ _ _ _ _).mp h3 (fun _ => True) (fun _ _ => Iff.rfl)
  have h5 : f (fun _ => False) = true ↔ False :=
    (XMK_F.holdsAt_all _ _ _ _ _).mp h3 (fun _ => False) (fun _ _ => Iff.rfl)
  exact h5.mp ((hc _ _).symm.trans (h4.mpr trivial))

theorem XMK_TAx : XMK_F.Valid TAx := by
  refine XMK_Valid_of ?_
  refine (XMK_F.holdsAt_all _ _ _ _ _).mpr fun p _ => (XMK_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  exact (XMK_F.box_of XMK_heq _ _ _ _).mp h (0 : Fin 3) (XMK_U.Rrefl _)

/-- The proposition true just at the actual world is not necessary. -/
theorem XMK_not_Collapse : ¬ XMK_F.Valid Collapse := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_all _ _ _ _ _).mp h (fun (w : Fin 3) => w = 0) (fun _ _ => Iff.rfl)
  have h2 := (XMK_F.box_of XMK_heq _ _ _ _).mp ((XMK_F.holdsAt_imp _ _ _ _ _).mp h1 rfl) (1 : Fin 3) (Or.inr rfl)
  have h3 : (1 : Fin 3) = 0 := h2
  exact absurd h3 (by decide)

/-- `⊤` and the proposition false just at world `1` are equivalent but not identical. -/
theorem XMK_not_PropExt : ¬ XMK_F.Valid PropExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_all _ _ _ _ _).mp ((XMK_F.holdsAt_all _ _ _ _ _).mp h (fun _ => True)
    (fun _ _ => Iff.rfl)) (fun (w : Fin 3) => w ≠ 1) (fun _ _ => Iff.rfl)
  have h2 := (XMK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XMK_F.holdsAt_iff _ _ _ _ _).mpr
    (show True ↔ (0 : Fin 3) ≠ 1 from ⟨fun _ => by decide, fun _ => trivial⟩))
  have h3 := (XMK_heq .t _ _ _).mp ((XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h2)
  have h4 : True ↔ (1 : Fin 3) ≠ 1 := h3 (1 : Fin 3) (Or.inr rfl)
  exact h4.mp trivial rfl

/-- `e` and `d` are distinct, but each entity is identified with its copy. -/
theorem XMK_not_Disjoint : ¬ XMK_F.Valid Disjoint := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_tall _ _ _ _).mp ((XMK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base .d) (Or.inr trivial)
  have h2 := (XMK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XMK_F.holdsAt_neg _ _ _ _).mpr fun ht =>
    nomatch ((XMK_F.holdsAt_teq _ _ _ _ _).mp ht).1 (by decide : (0 : Fin 3) ≠ 1))
  have h3 := (XMK_F.holdsAt_all _ _ _ _ _).mp ((XMK_F.holdsAt_all _ _ _ _ _).mp h2 true rfl) true rfl
  exact (XMK_F.holdsAt_neg _ _ _ _).mp h3 ((XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (Or.inl ⟨rfl, rfl⟩))

/-- No entity is identified with an item of a type of predicates. -/
theorem XMK_Slogan : XMK_F.Valid Slogan := by
  refine XMK_Valid_of ?_
  refine (XMK_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XMK_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XMK_F.holdsAt_all _ _ _ _ _).mpr fun y _ => (XMK_F.holdsAt_neg _ _ _ _).mpr fun hxy => ?_
  rcases (XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mp hxy with ⟨hi, _⟩ | ⟨_, _, g, hg, _, _⟩
  · exact nomatch hi
  · exact nomatch hg

/-- `⊤` is identified with nothing of another type. -/
theorem XMK_not_Twin : ¬ XMK_F.Valid Twin := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_all _ _ _ _ _).mp ((XMK_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial))
    (fun _ => True) (fun _ _ => Iff.rfl)
  obtain ⟨b, _, h2⟩ := (XMK_F.holdsAt_tex _ _ _ _).mp h1
  have h3 := (XMK_F.holdsAt_conj _ _ _ _ _).mp h2
  obtain ⟨y, _, h4⟩ := (XMK_F.holdsAt_ex _ _ _ _ _).mp h3.2
  rcases (XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h4 with ⟨hi, _⟩ | ⟨_, _, g, hg, _, _⟩
  · exact (XMK_F.holdsAt_neg _ _ _ _).mp h3.1
      ((XMK_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => (XMK_img_t hi.symm).symm, hi⟩)
  · exact nomatch hg

theorem XMK_not_Hae : ¬ XMK_F.Valid Hae := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_all _ _ _ _ _).mp ((XMK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) true rfl
  rcases (XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h1 with ⟨hi, _⟩ | ⟨_, _, g, hg, _, _⟩
  · exact nomatch hi
  · exact nomatch hg

/-- The constant functions of `A` and `B` are identified, and `⊤` with itself, but the values, of
types `e` and `d₂`, are not. -/
theorem XMK_not_Cong : ¬ XMK_F.Valid Cong := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_tall _ _ _ _).mp ((XMK_F.holdsAt_tall _ _ _ _).mp ((XMK_F.holdsAt_tall _ _ _ _).mp
    ((XMK_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)) .t (Or.inr trivial)) .e (Or.inr trivial))
    (.base .d2) (Or.inr trivial)
  have h2 := (XMK_F.holdsAt_all _ _ _ _ _).mp ((XMK_F.holdsAt_all _ _ _ _ _).mp ((XMK_F.holdsAt_all _ _ _ _ _).mp
    ((XMK_F.holdsAt_all _ _ _ _ _).mp h1 XMK_k (XMK_k_adm _)) XMK_k (XMK_k_admB _)) (fun _ => True)
    (fun _ _ => Iff.rfl)) (fun _ => True) (fun _ _ => Iff.rfl)
  have h3 := (XMK_F.holdsAt_imp _ _ _ _ _).mp h2 ((XMK_F.holdsAt_conj _ _ _ _ _).mpr
    ⟨(XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XMK_AB XMK_k (XMK_k_adm _)),
     (XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ((XMK_heq .t _ _ _).mpr fun _ _ => Iff.rfl)⟩)
  rcases (XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h3 with ⟨hi, _⟩ | ⟨_, _, g, hg, _, _⟩
  · exact nomatch hi
  · exact nomatch hg

/-- The constantly-constant functions from `e` to `A` and to `B` agree pointwise up to identity,
but are not identified. -/
theorem XMK_not_PExt : ¬ XMK_F.Valid PExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XMK_F.holdsAt_tall _ _ _ _).mp ((XMK_F.holdsAt_tall _ _ _ _).mp
    ((XMK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) XMK_A (Or.inr ⟨trivial, trivial⟩))
    XMK_Bd (Or.inr ⟨trivial, trivial⟩)
  have hk : ∀ w : Fin 3, XMK_U.rel (.arr .e XMK_A) w (fun _ => XMK_k) (fun _ => XMK_k) :=
    fun _ v _ _ _ _ => XMK_k_adm v
  have hkB : ∀ w : Fin 3, XMK_U.rel (.arr .e XMK_Bd) w (fun _ => XMK_k) (fun _ => XMK_k) :=
    fun _ v _ _ _ _ => XMK_k_admB v
  have h2 := (XMK_F.holdsAt_all _ _ _ _ _).mp ((XMK_F.holdsAt_all _ _ _ _ _).mp h1 (fun _ => XMK_k) (hk _))
    (fun _ => XMK_k) (hkB _)
  have h3 := (XMK_F.holdsAt_imp _ _ _ _ _).mp h2 ((XMK_F.holdsAt_all _ _ _ _ _).mpr fun _ _ =>
    (XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XMK_AB XMK_k (XMK_k_adm _)))
  rcases (XMK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h3 with ⟨hi, _⟩ | ⟨_, _, g, hg, _, _⟩
  · exact nomatch hi
  · exact nomatch hg

theorem XMK_Inj : XMK_F.Valid Inj := by
  refine XMK_Valid_of ?_
  refine (XMK_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XMK_F.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (XMK_F.holdsAt_tall _ _ _ _).mpr fun c _ => (XMK_F.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (XMK_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code XMK_B) = .arr b d :=
    ((XMK_F.holdsAt_teq _ _ _ _ _).mp h).1 (by decide : (0 : Fin 3) ≠ 1)
  exact (XMK_F.holdsAt_conj _ _ _ _ _).mpr
    ⟨(XMK_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => (Code.arr.inj e).1, congrArg XMK_img (Code.arr.inj e).1⟩,
     (XMK_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => (Code.arr.inj e).2, congrArg XMK_img (Code.arr.inj e).2⟩⟩

theorem XMK_Recovery : XMK_F.Valid Recovery := by
  refine XMK_Valid_of ?_
  refine (XMK_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XMK_F.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (XMK_F.holdsAt_tall _ _ _ _).mpr fun c _ => (XMK_F.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (XMK_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code XMK_B) = .arr b d :=
    ((XMK_F.holdsAt_teq _ _ _ _ _).mp ((XMK_F.holdsAt_conj _ _ _ _ _).mp h).1).1 (by decide : (0 : Fin 3) ≠ 1)
  exact (XMK_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => (Code.arr.inj e).2, congrArg XMK_img (Code.arr.inj e).2⟩

end Kr
end PIF
