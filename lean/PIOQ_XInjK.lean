import PIBF
import PIOQ_KIE

/-!
# A Kripke model of PIᶜ in which Inj≈ and Recovery fail, together with ND≈, TBF, BF, Functional
# Choice, ND× and NI×

`𝔐_k,inj`: three worlds `0, 1, 2`; the actual world `0` sees all three, and `1` and `2` see only
themselves. Entities are booleans. There are three base types: `D`, a copy of `t` (its items are
sets of worlds, identical at a world when they agree at every world it sees); `X`, a copy of `e`;
and `N`, with one item, which exists only at worlds `1` and `2`.

* At the actual world, `≈` is sameness of type once `e → D` is replaced by `e → t` (as in `𝔐_κ`):
  so `e → t ≈ e → D`, but not `t ≈ D`, and Inj≈ and Recovery fail. At worlds `1` and `2`, `≈` is
  sameness of type once `D` is replaced by `t`: so `t ≈ D` there, and ND≈ fails.
* Items are identified at a world when their types are `≈` there and they correspond (after `D` is
  replaced by `t`) at that world. Besides that, at the actual world only, each entity is identified
  with the item of `X` with the same boolean value: so NI× fails.
* `N` exists only at worlds `1` and `2`, and has a single item: so TBF fails.
* As in `𝔐_k,ie`, an item of `t → e` at the actual world must respect agreement of propositions at
  world `1` and at world `2`, so it is constant: so BF and Functional Choice fail. ND× fails since
  `⊤` and the proposition true just at world `1` differ at the actual world but not at world `1`.

Within a type, identity at a world is the Kripke identity, so the frame validates LL≡ and
Classicism at every world, and so every theorem of PIᶜ.
-/
set_option autoImplicit false

namespace PIF
namespace Kr
open Tm

/-! ### The universe -/

/-- The base types: `D` (a copy of `t`), `X` (a copy of `e`), and `N` (one item; only at worlds
`1` and `2`). -/
inductive XIK_B : Type where
  | D : XIK_B
  | X : XIK_B
  | N : XIK_B
  deriving DecidableEq

/-- The items of the base types. -/
def XIK_Bt : XIK_B → Type
  | .D => Fin 3 → Prop
  | .X => Bool
  | .N => Unit

theorem XIK_Rtrans (u v w : Fin 3) (h1 : u = v ∨ u = 0) (h2 : v = w ∨ v = 0) : u = w ∨ u = 0 := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr h1

/-- Identity at a world of items of the base types. -/
def XIK_rb (w : Fin 3) : (b : XIK_B) → XIK_Bt b → XIK_Bt b → Prop
  | .D => fun p q => ∀ v, (w = v ∨ w = 0) → (p v ↔ q v)
  | .X => fun x y => x = y
  | .N => fun _ _ => True

/-- Types without `N`: the types that exist at the actual world. -/
def XIK_noN : Code XIK_B → Prop
  | .base .N => False
  | .arr a c => XIK_noN a ∧ XIK_noN c
  | _ => True

def XIK_U : Univ where
  W := Fin 3
  w0 := 0
  R := fun w u => w = u ∨ w = 0
  Rrefl := fun _ => Or.inl rfl
  Rtrans := XIK_Rtrans
  E := Bool
  Base := XIK_B
  B := XIK_Bt
  neE := ⟨true⟩
  neB := fun b => match b with
    | .D => ⟨fun _ => True⟩
    | .X => ⟨true⟩
    | .N => ⟨()⟩
  re := fun _ x y => x = y
  rb := XIK_rb
  re_refl := fun _ _ => rfl
  re_symm := fun _ _ _ h => h.symm
  re_trans := fun _ _ _ _ h1 h2 => h1.trans h2
  re_mono := fun _ _ _ _ _ h => h
  rb_refl := fun w b x => match b with
    | .D => fun _ _ => Iff.rfl
    | .X => (rfl : (x : Bool) = x)
    | .N => trivial
  rb_symm := fun w b x y h => match b with
    | .D => fun v hv => (h v hv).symm
    | .X => (Eq.symm h : (y : Bool) = x)
    | .N => trivial
  rb_trans := fun w b x y z h1 h2 => match b with
    | .D => fun v hv => (h1 v hv).trans (h2 v hv)
    | .X => (Eq.trans h1 h2 : (x : Bool) = z)
    | .N => trivial
  rb_mono := fun w v b x y hwv h => match b with
    | .D => fun u hu => h u (XIK_Rtrans _ _ _ hwv hu)
    | .X => h
    | .N => trivial
  D := fun w a => w ≠ 0 ∨ XIK_noN a
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
    · rcases h with rfl | h
      · exact Or.inl ha
      · exact absurd h ha
    · exact Or.inr ha

theorem XIK_R_zero {w v : Fin 3} (h : XIK_U.R w v) (hv : v = 0) : w = 0 := by
  rcases h with rfl | h
  · exact hv
  · exact h

theorem XIK_R_ne {w v : Fin 3} (h : XIK_U.R w v) (hw : w ≠ 0) : v = w := by
  rcases h with rfl | h
  · rfl
  · exact absurd h hw

/-! ### Correspondence of types: putting `t` for `D` -/

/-- The type got by putting `t` for `D`. -/
def XIK_img : Code XIK_B → Code XIK_B
  | .base .D => .t
  | .base .X => .base .X
  | .base .N => .base .N
  | .arr a c => .arr (XIK_img a) (XIK_img c)
  | .e => .e
  | .t => .t

/-- The key at the actual world: `e → D` is replaced by `e → t`, from the inside out. -/
def XIK_sp (x y : Code XIK_B) : Code XIK_B := if x = .e ∧ y = .base .D then .arr .e .t else .arr x y

def XIK_K : Code XIK_B → Code XIK_B
  | .arr a c => XIK_sp (XIK_K a) (XIK_K c)
  | .e => .e
  | .t => .t
  | .base b => .base b

theorem XIK_sp_arr (x y : Code XIK_B) : ∃ p q, XIK_sp x y = .arr p q := by
  unfold XIK_sp
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem XIK_img_sp (x y : Code XIK_B) : XIK_img (XIK_sp x y) = .arr (XIK_img x) (XIK_img y) := by
  unfold XIK_sp
  split
  · next h => obtain ⟨rfl, rfl⟩ := h; rfl
  · rfl

theorem XIK_img_K : ∀ a, XIK_img (XIK_K a) = XIK_img a
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => by
    show XIK_img (XIK_sp (XIK_K a) (XIK_K c)) = .arr (XIK_img a) (XIK_img c)
    rw [XIK_img_sp, XIK_img_K a, XIK_img_K c]

theorem XIK_K_e {a : Code XIK_B} (h : XIK_K a = .e) : a = .e := by
  cases a with
  | e => rfl
  | t => exact nomatch h
  | base _ => exact nomatch h
  | arr a c =>
    obtain ⟨p, q, hpq⟩ := XIK_sp_arr (XIK_K a) (XIK_K c)
    exact absurd (hpq.symm.trans h) (fun h' => nomatch h')

theorem XIK_K_t {a : Code XIK_B} (h : XIK_K a = .t) : a = .t := by
  cases a with
  | t => rfl
  | e => exact nomatch h
  | base _ => exact nomatch h
  | arr a c =>
    obtain ⟨p, q, hpq⟩ := XIK_sp_arr (XIK_K a) (XIK_K c)
    exact absurd (hpq.symm.trans h) (fun h' => nomatch h')

theorem XIK_K_base {a : Code XIK_B} {b : XIK_B} (h : XIK_K a = .base b) : a = .base b := by
  cases a with
  | base _ => exact h
  | e => exact nomatch h
  | t => exact nomatch h
  | arr a c =>
    obtain ⟨p, q, hpq⟩ := XIK_sp_arr (XIK_K a) (XIK_K c)
    exact absurd (hpq.symm.trans h) (fun h' => nomatch h')

theorem XIK_img_e {a : Code XIK_B} (h : XIK_img a = .e) : a = .e := by
  cases a with
  | e => rfl
  | t => exact nomatch h
  | base b => cases b <;> exact nomatch h
  | arr _ _ => exact nomatch h

theorem XIK_img_t {a : Code XIK_B} (h : XIK_img a = .t) : a = .t ∨ a = .base .D := by
  cases a with
  | t => exact Or.inl rfl
  | e => exact nomatch h
  | base b =>
    cases b with
    | D => exact Or.inr rfl
    | X => exact nomatch h
    | N => exact nomatch h
  | arr _ _ => exact nomatch h

theorem XIK_img_X {a : Code XIK_B} (h : XIK_img a = .base .X) : a = .base .X := by
  cases a with
  | base b =>
    cases b with
    | X => rfl
    | D => exact nomatch h
    | N => exact nomatch h
  | e => exact nomatch h
  | t => exact nomatch h
  | arr _ _ => exact nomatch h

theorem XIK_img_N {a : Code XIK_B} (h : XIK_img a = .base .N) : a = .base .N := by
  cases a with
  | base b =>
    cases b with
    | N => rfl
    | D => exact nomatch h
    | X => exact nomatch h
  | e => exact nomatch h
  | t => exact nomatch h
  | arr _ _ => exact nomatch h

theorem XIK_img_D {a : Code XIK_B} (h : XIK_img a = .base .D) : False := by
  cases a with
  | base b => cases b <;> exact nomatch h
  | e => exact nomatch h
  | t => exact nomatch h
  | arr _ _ => exact nomatch h

theorem XIK_img_arr {a k1 k2 : Code XIK_B} (h : XIK_img a = .arr k1 k2) :
    ∃ a1 a2, a = .arr a1 a2 ∧ XIK_img a1 = k1 ∧ XIK_img a2 = k2 := by
  cases a with
  | arr a1 a2 => injection h with h1 h2; exact ⟨a1, a2, rfl, h1, h2⟩
  | e => exact nomatch h
  | t => exact nomatch h
  | base b => cases b <;> exact nomatch h

/-- Correspondence at a world, between items of types with the same image. -/
def XIK_CR : (a b : Code XIK_B) → Fin 3 → XIK_U.El a → XIK_U.El b → Prop
  | .e, .e => fun _ x y => x = y
  | .t, .t => fun w p q => ∀ v, XIK_U.R w v → (p v ↔ q v)
  | .t, .base .D => fun w p q => ∀ v, XIK_U.R w v → (p v ↔ q v)
  | .base .D, .t => fun w p q => ∀ v, XIK_U.R w v → (p v ↔ q v)
  | .base .D, .base .D => fun w p q => ∀ v, XIK_U.R w v → (p v ↔ q v)
  | .base .X, .base .X => fun _ x y => x = y
  | .base .N, .base .N => fun _ _ _ => True
  | .arr a c, .arr b d => fun w f g => ∀ v, XIK_U.R w v → ∀ x y, XIK_CR a b v x y → XIK_CR c d v (f x) (g y)
  | _, _ => fun _ _ _ => False

/-- Transport, both ways, between types with the same image. -/
noncomputable def XIK_Tr : (a b : Code XIK_B) → (XIK_U.El a → XIK_U.El b) × (XIK_U.El b → XIK_U.El a)
  | .e, .e => (fun x => x, fun x => x)
  | .t, .t => (fun p => p, fun p => p)
  | .t, .base .D => (fun p => p, fun p => p)
  | .base .D, .t => (fun p => p, fun p => p)
  | .base .D, .base .D => (fun p => p, fun p => p)
  | .base .X, .base .X => (fun x => x, fun x => x)
  | .base .N, .base .N => (fun x => x, fun x => x)
  | .arr a c, .arr b d =>
      (fun f y => (XIK_Tr c d).1 (f ((XIK_Tr a b).2 y)), fun g x => (XIK_Tr c d).2 (g ((XIK_Tr a b).1 x)))
  | a, b => (fun _ => Classical.choose (XIK_U.adm_nonempty b), fun _ => Classical.choose (XIK_U.adm_nonempty a))

noncomputable abbrev XIK_Tf (a b : Code XIK_B) : XIK_U.El a → XIK_U.El b := (XIK_Tr a b).1
noncomputable abbrev XIK_Tg (a b : Code XIK_B) : XIK_U.El b → XIK_U.El a := (XIK_Tr a b).2

theorem XIK_CR_diag : ∀ (a : Code XIK_B) (w : Fin 3) (x y : XIK_U.El a), XIK_U.rel a w x y ↔ XIK_CR a a w x y
  | .e, _, _, _ => Iff.rfl
  | .t, _, _, _ => Iff.rfl
  | .base .D, _, _, _ => Iff.rfl
  | .base .X, _, _, _ => Iff.rfl
  | .base .N, _, _, _ => Iff.rfl
  | .arr a c, _, _, _ => forall_congr' fun v => imp_congr Iff.rfl (forall_congr' fun x => forall_congr' fun y =>
      imp_congr (XIK_CR_diag a v x y) (XIK_CR_diag c v _ _))

set_option maxHeartbeats 4000000 in
/-- Correspondence between types with one image is symmetric, transitive and persistent, and
transport takes each item to one corresponding to it. -/
theorem XIK_shape : ∀ k : Code XIK_B,
    (∀ a b, XIK_img a = k → XIK_img b = k → ∀ w x y, XIK_CR a b w x y → XIK_CR b a w y x) ∧
    (∀ a b c, XIK_img a = k → XIK_img b = k → XIK_img c = k → ∀ w x y z, XIK_CR a b w x y →
      XIK_CR b c w y z → XIK_CR a c w x z) ∧
    (∀ a b, XIK_img a = k → XIK_img b = k → ∀ w x, XIK_CR a a w x x →
      XIK_CR a b w x (XIK_Tf a b x) ∧ XIK_CR b b w (XIK_Tf a b x) (XIK_Tf a b x)) ∧
    (∀ a b, XIK_img a = k → XIK_img b = k → ∀ w y, XIK_CR b b w y y →
      XIK_CR a b w (XIK_Tg a b y) y ∧ XIK_CR a a w (XIK_Tg a b y) (XIK_Tg a b y)) ∧
    (∀ a b, XIK_img a = k → XIK_img b = k → ∀ w v x y, XIK_U.R w v → XIK_CR a b w x y → XIK_CR a b v x y) := by
  intro k
  induction k with
  | e =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b ha hb w x y h
      have e1 := XIK_img_e ha; have e2 := XIK_img_e hb; subst e1; subst e2
      exact Eq.symm h
    · intro a b c ha hb hc w x y z h1 h2
      have e1 := XIK_img_e ha; have e2 := XIK_img_e hb; have e3 := XIK_img_e hc; subst e1; subst e2; subst e3
      exact Eq.trans h1 h2
    · intro a b ha hb w x _
      have e1 := XIK_img_e ha; have e2 := XIK_img_e hb; subst e1; subst e2
      exact ⟨rfl, rfl⟩
    · intro a b ha hb w x _
      have e1 := XIK_img_e ha; have e2 := XIK_img_e hb; subst e1; subst e2
      exact ⟨rfl, rfl⟩
    · intro a b ha hb w v x y _ h
      have e1 := XIK_img_e ha; have e2 := XIK_img_e hb; subst e1; subst e2
      exact h
  | t =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b ha hb w x y h
      rcases XIK_img_t ha with rfl | rfl <;> rcases XIK_img_t hb with rfl | rfl <;>
        exact fun v hv => (h v hv).symm
    · intro a b c ha hb hc w x y z h1 h2
      rcases XIK_img_t ha with rfl | rfl <;> rcases XIK_img_t hb with rfl | rfl <;>
        rcases XIK_img_t hc with rfl | rfl <;> exact fun v hv => (h1 v hv).trans (h2 v hv)
    · intro a b ha hb w x hx
      rcases XIK_img_t ha with rfl | rfl <;> rcases XIK_img_t hb with rfl | rfl <;> exact ⟨hx, hx⟩
    · intro a b ha hb w x hx
      rcases XIK_img_t ha with rfl | rfl <;> rcases XIK_img_t hb with rfl | rfl <;> exact ⟨hx, hx⟩
    · intro a b ha hb w v x y hv h
      rcases XIK_img_t ha with rfl | rfl <;> rcases XIK_img_t hb with rfl | rfl <;>
        exact fun u hu => h u (XIK_Rtrans _ _ _ hv hu)
  | base b =>
    cases b with
    | D => exact ⟨fun a _ ha => (XIK_img_D ha).elim, fun a _ _ ha => (XIK_img_D ha).elim,
        fun a _ ha => (XIK_img_D ha).elim, fun a _ ha => (XIK_img_D ha).elim, fun a _ ha => (XIK_img_D ha).elim⟩
    | X =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a b ha hb w x y h
        have e1 := XIK_img_X ha; have e2 := XIK_img_X hb; subst e1; subst e2
        exact Eq.symm h
      · intro a b c ha hb hc w x y z h1 h2
        have e1 := XIK_img_X ha; have e2 := XIK_img_X hb; have e3 := XIK_img_X hc; subst e1; subst e2; subst e3
        exact Eq.trans h1 h2
      · intro a b ha hb w x _
        have e1 := XIK_img_X ha; have e2 := XIK_img_X hb; subst e1; subst e2
        exact ⟨rfl, rfl⟩
      · intro a b ha hb w x _
        have e1 := XIK_img_X ha; have e2 := XIK_img_X hb; subst e1; subst e2
        exact ⟨rfl, rfl⟩
      · intro a b ha hb w v x y _ h
        have e1 := XIK_img_X ha; have e2 := XIK_img_X hb; subst e1; subst e2
        exact h
    | N =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a b ha hb w x y _
        have e1 := XIK_img_N ha; have e2 := XIK_img_N hb; subst e1; subst e2
        exact trivial
      · intro a b c ha hb hc w x y z _ _
        have e1 := XIK_img_N ha; have e2 := XIK_img_N hb; have e3 := XIK_img_N hc; subst e1; subst e2; subst e3
        exact trivial
      · intro a b ha hb w x _
        have e1 := XIK_img_N ha; have e2 := XIK_img_N hb; subst e1; subst e2
        exact ⟨trivial, trivial⟩
      · intro a b ha hb w x _
        have e1 := XIK_img_N ha; have e2 := XIK_img_N hb; subst e1; subst e2
        exact ⟨trivial, trivial⟩
      · intro a b ha hb w v x y _ _
        have e1 := XIK_img_N ha; have e2 := XIK_img_N hb; subst e1; subst e2
        exact trivial
  | arr k1 k2 ih1 ih2 =>
    obtain ⟨S1, R1, P1, Q1, _⟩ := ih1
    obtain ⟨S2, R2, P2, Q2, _⟩ := ih2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a b ha hb w f g h
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XIK_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XIK_img_arr hb
      intro v hv x y hxy
      exact S2 a2 b2 ha2 hb2 v _ _ (h v hv y x (S1 b1 a1 hb1 ha1 v x y hxy))
    · intro a b c ha hb hc w f g h hfg hgh
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XIK_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XIK_img_arr hb
      obtain ⟨c1, c2, rfl, hc1, hc2⟩ := XIK_img_arr hc
      intro v hv x z hxz
      have hzz : XIK_CR c1 c1 v z z := R1 c1 a1 c1 hc1 ha1 hc1 v z x z (S1 a1 c1 ha1 hc1 v x z hxz) hxz
      obtain ⟨hyz, _⟩ := Q1 b1 c1 hb1 hc1 v z hzz
      have hxy : XIK_CR a1 b1 v x (XIK_Tg b1 c1 z) :=
        R1 a1 c1 b1 ha1 hc1 hb1 v x z _ hxz (S1 b1 c1 hb1 hc1 v _ z hyz)
      exact R2 a2 b2 c2 ha2 hb2 hc2 v _ _ _ (hfg v hv x _ hxy) (hgh v hv _ z hyz)
    · intro a b ha hb w f hf
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XIK_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XIK_img_arr hb
      refine ⟨?_, ?_⟩
      · intro v hv x y hxy
        have hyy : XIK_CR b1 b1 v y y := R1 b1 a1 b1 hb1 ha1 hb1 v y x y (S1 a1 b1 ha1 hb1 v x y hxy) hxy
        obtain ⟨hTy, hTT⟩ := Q1 a1 b1 ha1 hb1 v y hyy
        have hxT : XIK_CR a1 a1 v x (XIK_Tg a1 b1 y) :=
          R1 a1 b1 a1 ha1 hb1 ha1 v x y _ hxy (S1 a1 b1 ha1 hb1 v _ y hTy)
        have hfx := hf v hv x _ hxT
        obtain ⟨h1, _⟩ := P2 a2 b2 ha2 hb2 v _ (hf v hv _ _ hTT)
        exact R2 a2 a2 b2 ha2 ha2 hb2 v _ _ _ hfx h1
      · intro v hv y y' hyy'
        have hyy : XIK_CR b1 b1 v y y := R1 b1 b1 b1 hb1 hb1 hb1 v y y' y hyy' (S1 b1 b1 hb1 hb1 v y y' hyy')
        have hy'y' : XIK_CR b1 b1 v y' y' :=
          R1 b1 b1 b1 hb1 hb1 hb1 v y' y y' (S1 b1 b1 hb1 hb1 v y y' hyy') hyy'
        obtain ⟨hTy, hTT⟩ := Q1 a1 b1 ha1 hb1 v y hyy
        obtain ⟨hTy', hT'T'⟩ := Q1 a1 b1 ha1 hb1 v y' hy'y'
        have hTyy : XIK_CR a1 a1 v (XIK_Tg a1 b1 y) (XIK_Tg a1 b1 y') :=
          R1 a1 b1 a1 ha1 hb1 ha1 v _ y _ hTy (R1 b1 b1 a1 hb1 hb1 ha1 v y y' _ hyy' (S1 a1 b1 ha1 hb1 v _ y' hTy'))
        obtain ⟨g1, _⟩ := P2 a2 b2 ha2 hb2 v _ (hf v hv _ _ hTT)
        obtain ⟨g2, _⟩ := P2 a2 b2 ha2 hb2 v _ (hf v hv _ _ hT'T')
        exact R2 b2 a2 b2 hb2 ha2 hb2 v _ _ _ (S2 a2 b2 ha2 hb2 v _ _ g1)
          (R2 a2 a2 b2 ha2 ha2 hb2 v _ _ _ (hf v hv _ _ hTyy) g2)
    · intro a b ha hb w g hg
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XIK_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XIK_img_arr hb
      refine ⟨?_, ?_⟩
      · intro v hv x y hxy
        have hxx : XIK_CR a1 a1 v x x := R1 a1 b1 a1 ha1 hb1 ha1 v x y x hxy (S1 a1 b1 ha1 hb1 v x y hxy)
        obtain ⟨hxT, hTT⟩ := P1 a1 b1 ha1 hb1 v x hxx
        have hTy : XIK_CR b1 b1 v (XIK_Tf a1 b1 x) y :=
          R1 b1 a1 b1 hb1 ha1 hb1 v _ x y (S1 a1 b1 ha1 hb1 v x _ hxT) hxy
        have hgy := hg v hv _ y hTy
        obtain ⟨h1, _⟩ := Q2 a2 b2 ha2 hb2 v _ (hg v hv _ _ hTT)
        exact R2 a2 b2 b2 ha2 hb2 hb2 v _ _ _ h1 hgy
      · intro v hv x x' hxx'
        have hxx : XIK_CR a1 a1 v x x := R1 a1 a1 a1 ha1 ha1 ha1 v x x' x hxx' (S1 a1 a1 ha1 ha1 v x x' hxx')
        have hx'x' : XIK_CR a1 a1 v x' x' :=
          R1 a1 a1 a1 ha1 ha1 ha1 v x' x x' (S1 a1 a1 ha1 ha1 v x x' hxx') hxx'
        obtain ⟨hxT, hTT⟩ := P1 a1 b1 ha1 hb1 v x hxx
        obtain ⟨hx'T, hT'T'⟩ := P1 a1 b1 ha1 hb1 v x' hx'x'
        have hTxx : XIK_CR b1 b1 v (XIK_Tf a1 b1 x) (XIK_Tf a1 b1 x') :=
          R1 b1 a1 b1 hb1 ha1 hb1 v _ x _ (S1 a1 b1 ha1 hb1 v x _ hxT) (R1 a1 a1 b1 ha1 ha1 hb1 v x x' _ hxx' hx'T)
        obtain ⟨g1, _⟩ := Q2 a2 b2 ha2 hb2 v _ (hg v hv _ _ hTT)
        obtain ⟨g2, _⟩ := Q2 a2 b2 ha2 hb2 v _ (hg v hv _ _ hT'T')
        exact R2 a2 b2 a2 ha2 hb2 ha2 v _ _ _ g1
          (R2 b2 b2 a2 hb2 hb2 ha2 v _ _ _ (hg v hv _ _ hTxx) (S2 a2 b2 ha2 hb2 v _ _ g2))
    · intro a b ha hb w v f g hv h
      obtain ⟨a1, a2, rfl, _, _⟩ := XIK_img_arr ha
      obtain ⟨b1, b2, rfl, _, _⟩ := XIK_img_arr hb
      exact fun u hu => h u (XIK_Rtrans _ _ _ hv hu)

theorem XIK_CR_symm {a b : Code XIK_B} (h : XIK_img a = XIK_img b) {w : Fin 3} {x : XIK_U.El a}
    {y : XIK_U.El b} (hxy : XIK_CR a b w x y) : XIK_CR b a w y x :=
  (XIK_shape (XIK_img a)).1 a b rfl h.symm w x y hxy

theorem XIK_CR_trans {a b c : Code XIK_B} (h1 : XIK_img a = XIK_img b) (h2 : XIK_img b = XIK_img c) {w : Fin 3}
    {x : XIK_U.El a} {y : XIK_U.El b} {z : XIK_U.El c} (hxy : XIK_CR a b w x y) (hyz : XIK_CR b c w y z) :
    XIK_CR a c w x z :=
  (XIK_shape (XIK_img a)).2.1 a b c rfl h1.symm (h1.trans h2).symm w x y z hxy hyz

theorem XIK_CR_mono {a b : Code XIK_B} (h : XIK_img a = XIK_img b) {w v : Fin 3} {x : XIK_U.El a}
    {y : XIK_U.El b} (hv : XIK_U.R w v) (hxy : XIK_CR a b w x y) : XIK_CR a b v x y :=
  (XIK_shape (XIK_img a)).2.2.2.2 a b rfl h.symm w v x y hv hxy

/-! ### Identity -/

/-- The boolean value of an entity or of an item of `X`. -/
def XIK_toB : (a : Code XIK_B) → XIK_U.El a → Option Bool
  | .e, x => some x
  | .base .X, x => some x
  | _, _ => none

theorem XIK_toB_some {a : Code XIK_B} {x : XIK_U.El a} {c : Bool} (h : XIK_toB a x = some c) :
    a = .e ∨ a = .base .X := by
  cases a with
  | e => exact Or.inl rfl
  | t => exact nomatch h
  | base b =>
    cases b with
    | X => exact Or.inr rfl
    | D => exact nomatch h
    | N => exact nomatch h
  | arr _ _ => exact nomatch h

theorem XIK_toB_resp {a : Code XIK_B} {w : Fin 3} {x x' : XIK_U.El a} {c : Bool} (h : XIK_toB a x = some c)
    (hx : XIK_CR a a w x x') : XIK_toB a x' = some c := by
  rcases XIK_toB_some h with rfl | rfl
  · have e : x = x' := hx
    subst e; exact h
  · have e : (x : Bool) = x' := hx
    subst e; exact h

theorem XIK_toB_CR {a : Code XIK_B} {w : Fin 3} {x x' : XIK_U.El a} {c : Bool} (h : XIK_toB a x = some c)
    (h' : XIK_toB a x' = some c) : XIK_CR a a w x x' := by
  rcases XIK_toB_some h with rfl | rfl
  · exact (Option.some.inj h).trans (Option.some.inj h').symm
  · exact ((Option.some.inj h).trans (Option.some.inj h').symm : (x : Bool) = x')

theorem XIK_toB_K {a : Code XIK_B} {x : XIK_U.El a} {c : Bool} (h : XIK_toB a x = some c) : XIK_K a = a := by
  rcases XIK_toB_some h with rfl | rfl <;> rfl

theorem XIK_toB_img {a : Code XIK_B} {x : XIK_U.El a} {c : Bool} (h : XIK_toB a x = some c) : XIK_img a = a := by
  rcases XIK_toB_some h with rfl | rfl <;> rfl

/-- If `a` is `e` or `X`, so is every type with its key. -/
theorem XIK_toB_K_eq {a a' : Code XIK_B} {x : XIK_U.El a} {c : Bool} (h : XIK_toB a x = some c)
    (hk : XIK_K a = XIK_K a') : a' = a := by
  rcases XIK_toB_some h with rfl | rfl
  · exact XIK_K_e hk.symm
  · exact XIK_K_base hk.symm

/-- `≈` at a world: at the actual world, sameness of key; elsewhere, sameness of image. -/
def XIK_teq (a b : Code XIK_B) (w : Fin 3) : Prop := (w = 0 → XIK_K a = XIK_K b) ∧ XIK_img a = XIK_img b

/-- An entity and an item of `X` with the same value. -/
def XIK_cross (a b : Code XIK_B) (x : XIK_U.El a) (y : XIK_U.El b) : Prop :=
  a ≠ b ∧ ∃ c, XIK_toB a x = some c ∧ XIK_toB b y = some c

/-- Identity at a world. -/
def XIK_eqv (a b : Code XIK_B) (x : XIK_U.El a) (y : XIK_U.El b) (w : Fin 3) : Prop :=
  (XIK_teq a b w ∧ XIK_CR a b w x y) ∨ (w = 0 ∧ XIK_cross a b x y)

theorem XIK_eqv_imp {a a' b b' : Code XIK_B} {u : Fin 3} {x : XIK_U.El a} {x' : XIK_U.El a'} {y : XIK_U.El b}
    {y' : XIK_U.El b'} (ia : XIK_img a = XIK_img a') (ib : XIK_img b = XIK_img b')
    (ca : u = 0 → XIK_K a = XIK_K a') (cb : u = 0 → XIK_K b = XIK_K b')
    (hx : XIK_CR a a' u x x') (hy : XIK_CR b b' u y y') : XIK_eqv a b x y u → XIK_eqv a' b' x' y' u := by
  rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨hu, hne, c, hxc, hyc⟩)
  · refine Or.inl ⟨⟨fun hu => (ca hu).symm.trans ((h1 hu).trans (cb hu)), ia.symm.trans (h2.trans ib)⟩, ?_⟩
    exact XIK_CR_trans (ia.symm.trans h2) ib (XIK_CR_trans ia.symm h2 (XIK_CR_symm ia hx) h3) hy
  · have ea : a' = a := XIK_toB_K_eq hxc (ca hu)
    have eb : b' = b := XIK_toB_K_eq hyc (cb hu)
    subst ea; subst eb
    exact Or.inr ⟨hu, hne, c, XIK_toB_resp hxc hx, XIK_toB_resp hyc hy⟩

theorem XIK_eqv_iff {a a' b b' : Code XIK_B} {u : Fin 3} {x : XIK_U.El a} {x' : XIK_U.El a'} {y : XIK_U.El b}
    {y' : XIK_U.El b'} (ia : XIK_img a = XIK_img a') (ib : XIK_img b = XIK_img b')
    (ca : u = 0 → XIK_K a = XIK_K a') (cb : u = 0 → XIK_K b = XIK_K b')
    (hx : XIK_CR a a' u x x') (hy : XIK_CR b b' u y y') : XIK_eqv a b x y u ↔ XIK_eqv a' b' x' y' u :=
  ⟨XIK_eqv_imp ia ib ca cb hx hy, XIK_eqv_imp ia.symm ib.symm (fun hu => (ca hu).symm) (fun hu => (cb hu).symm)
    (XIK_CR_symm ia hx) (XIK_CR_symm ib hy)⟩

theorem XIK_eqv_symm {a b : Code XIK_B} {x : XIK_U.El a} {y : XIK_U.El b} {w : Fin 3} (h : XIK_eqv a b x y w) :
    XIK_eqv b a y x w := by
  rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨hu, hne, c, hxc, hyc⟩
  · exact Or.inl ⟨⟨fun hw => (h1 hw).symm, h2.symm⟩, XIK_CR_symm h2 h3⟩
  · exact Or.inr ⟨hu, fun e => hne e.symm, c, hyc, hxc⟩

theorem XIK_eqv_trans {a b c : Code XIK_B} {x : XIK_U.El a} {y : XIK_U.El b} {z : XIK_U.El c} {w : Fin 3}
    (h1 : XIK_eqv a b x y w) (h2 : XIK_eqv b c y z w) : XIK_eqv a c x z w := by
  rcases h1 with ⟨⟨k1, i1⟩, r1⟩ | ⟨hu, hne1, c1, hx1, hy1⟩
  · rcases h2 with ⟨⟨k2, i2⟩, r2⟩ | ⟨hu, hne2, c2, hy2, hz2⟩
    · exact Or.inl ⟨⟨fun hw => (k1 hw).trans (k2 hw), i1.trans i2⟩, XIK_CR_trans i1 i2 r1 r2⟩
    · have eab : a = b := XIK_toB_K_eq hy2 (k1 hu).symm
      subst eab
      exact Or.inr ⟨hu, hne2, c2, XIK_toB_resp hy2 (XIK_CR_symm rfl r1), hz2⟩
  · rcases h2 with ⟨⟨k2, i2⟩, r2⟩ | ⟨_, _, c2, hy2, hz2⟩
    · have ecb : c = b := XIK_toB_K_eq hy1 (k2 hu)
      subst ecb
      exact Or.inr ⟨hu, hne1, c1, hx1, XIK_toB_resp hy1 r2⟩
    · have e12 : c1 = c2 := Option.some.inj (hy1.symm.trans hy2)
      subst e12
      by_cases hac : a = c
      · subst hac
        exact Or.inl ⟨⟨fun _ => rfl, rfl⟩, XIK_toB_CR hx1 hz2⟩
      · exact Or.inr ⟨hu, hac, c1, hx1, hz2⟩

theorem XIK_eqv_same (a : Code XIK_B) (x y : XIK_U.El a) (w : Fin 3) : XIK_eqv a a x y w ↔ XIK_U.rel a w x y := by
  constructor
  · rintro (⟨_, h⟩ | ⟨_, hne, _⟩)
    · exact (XIK_CR_diag a w x y).mpr h
    · exact absurd rfl hne
  · intro h; exact Or.inl ⟨⟨fun _ => rfl, rfl⟩, (XIK_CR_diag a w x y).mp h⟩

/-- `𝔐_k,inj`. -/
def XIK_F : Frame where
  U := XIK_U
  eqv := XIK_eqv
  teq := XIK_teq
  eqv_resp := fun u a b x x' y y' hx hy => XIK_eqv_iff rfl rfl (fun _ => rfl) (fun _ => rfl)
    ((XIK_CR_diag a u x x').mp hx) ((XIK_CR_diag b u y y').mp hy)

theorem XIK_heq : ∀ a x y w, XIK_F.eqv a a x y w ↔ XIK_F.U.rel a w x y := XIK_eqv_same

/-- The admissible relations: correspondence between types of one image, at the worlds at which the
two types have the same key. -/
def XIK_Adm (w : Fin 3) (a a' : Code XIK_B) (S : Fin 3 → XIK_U.El a → XIK_U.El a' → Prop) : Prop :=
  XIK_img a = XIK_img a' ∧ (∀ v : Fin 3, XIK_U.R w v → v = 0 → XIK_K a = XIK_K a') ∧ ∀ u x y, S u x y ↔ XIK_CR a a' u x y

def XIK_inv : KInv XIK_F where
  Adm := XIK_Adm
  amono := fun ⟨h1, h2, h3⟩ hv => ⟨h1, fun u hu => h2 u (XIK_Rtrans _ _ _ hv hu), h3⟩
  smono := fun ⟨h1, _, h3⟩ u u' x x' _ hu h => (h3 u' x x').mpr (XIK_CR_mono h1 hu ((h3 u x x').mp h))
  refl := fun _ a => ⟨rfl, fun _ _ _ => rfl, fun u x y => XIK_CR_diag a u x y⟩
  arrow := by
    intro w a a' c c' S T hS hT
    obtain ⟨h1, h2, h3⟩ := hS
    obtain ⟨k1, k2, k3⟩ := hT
    refine ⟨by show Code.arr (XIK_img a) (XIK_img c) = Code.arr (XIK_img a') (XIK_img c'); rw [h1, k1],
      fun v hv hv' => by show XIK_sp (XIK_K a) (XIK_K c) = XIK_sp (XIK_K a') (XIK_K c'); rw [h2 v hv hv', k2 v hv hv'],
      fun u f f' => ?_⟩
    exact forall_congr' fun v => imp_congr Iff.rfl (forall_congr' fun x => forall_congr' fun x' =>
      imp_congr (h3 v x x') (k3 v _ _))
  total := by
    intro w a a' S hS u _ x hx
    obtain ⟨h1, _, h3⟩ := hS
    obtain ⟨hxT, hTT⟩ := (XIK_shape (XIK_img a)).2.2.1 a a' rfl h1.symm u x ((XIK_CR_diag a u x x).mp hx)
    exact ⟨XIK_Tf a a' x, (XIK_CR_diag a' u _ _).mpr hTT, (h3 u x _).mpr hxT⟩
  onto := by
    intro w a a' S hS u _ y hy
    obtain ⟨h1, _, h3⟩ := hS
    obtain ⟨hTy, hTT⟩ := (XIK_shape (XIK_img a)).2.2.2.1 a a' rfl h1.symm u y ((XIK_CR_diag a' u y y).mp hy)
    exact ⟨XIK_Tg a a' y, (XIK_CR_diag a u _ _).mpr hTT, (h3 u _ y).mpr hTy⟩
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
    exact XIK_eqv_iff h1 k1 (h2 u hu) (k2 u hu) ((h3 u x x').mp hx) ((k3 u y y').mp hy)

theorem XIK_isModelAt : XIK_F.IsModelAt := by
  obtain ⟨h1, h2, h3⟩ := XIK_F.idAx_of (fun a x w hx => (XIK_heq a x x w).mpr hx)
    (fun _ _ _ _ _ h => XIK_eqv_symm h) (fun _ _ _ _ _ _ _ h1 h2 => XIK_eqv_trans h1 h2)
  refine ⟨h1, h2, h3, XIK_F.refTeq_of fun _ _ => ⟨fun _ => rfl, rfl⟩, ?_⟩
  intro n Γ Q w ρ _ env henv
  refine XIK_F.holdsAt_tall _ _ _ w |>.mpr fun a _ => XIK_F.holdsAt_tall _ _ _ w |>.mpr fun b _ => ?_
  refine (XIK_F.holdsAt_imp _ _ _ _ w).mpr fun hab => ?_
  obtain ⟨e1, e2⟩ := (XIK_F.holdsAt_teq (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env w).mp hab
  refine (XIK_F.holdsAt_imp _ _ _ _ w).mpr fun hq => ?_
  exact XIK_inv.llTeq_at Q w ρ env henv a b (XIK_CR a b)
    (show XIK_Adm w a b (XIK_CR a b) from ⟨e2, fun v hv hv' => e1 (XIK_R_zero hv hv'), fun _ _ _ => Iff.rfl⟩) hq

theorem XIK_LLEqv : XIK_F.Valid LLEqv := fun ρ hρ env henv => XIK_F.LLEqv_of XIK_heq _ ρ hρ env henv
theorem XIK_Class : ∀ χ, ClassSch χ → XIK_F.Valid χ :=
  XIK_F.Class_valid XIK_isModelAt (XIK_F.LLEqv_of XIK_heq) XIK_heq

theorem XIK_Valid_of {φ : Fm Ctx.nil} (h : XIK_F.HoldsAt φ (fun i => i.elim0) () XIK_U.w0) : XIK_F.Valid φ := by
  intro ρ _ env _
  have e1 : ρ = fun i => i.elim0 := funext fun i => i.elim0
  subst e1
  exact h

/-! ### Every theorem of PIᶜ is valid -/

theorem XIK_of_prov {φ : Fm Ctx.nil} (h : Prov SIE Ctx.nil φ) : XIK_F.Valid φ :=
  KIE.valid_of_PIc XIK_F XIK_isModelAt (XIK_F.LLEqv_of XIK_heq) XIK_heq h

open Derive in
theorem XIK_Bool : ∀ φ, BoolSch φ → XIK_F.Valid φ := fun φ h => XIK_of_prov (d_Bool_of_Class SIE_C φ h)
theorem XIK_IdId : XIK_F.Valid IdId := XIK_of_prov (d_IdId_of_Class SIE_C)
theorem XIK_NIEqv : XIK_F.Valid NIEqv := XIK_of_prov (d_NIEqv_of_Class SIE_C SIE_LL)
theorem XIK_NITeq : XIK_F.Valid NITeq := XIK_of_prov (d_NITeq_of_Class SIE_C)
theorem XIK_TNec : XIK_F.Valid TNec := XIK_of_prov (d_TNec_of_Class SIE_C)
theorem XIK_TCBF : ∀ χ, TCBFSch χ → XIK_F.Valid χ := fun χ h => XIK_of_prov (d_TCBF_of_Class SIE_C SIE_LL χ h)
theorem XIK_Nec : XIK_F.Valid Nec := XIK_of_prov (d_Nec_of_Class SIE_C)
theorem XIK_CBF : XIK_F.Valid CBF := XIK_of_prov (d_CBF_of_Class SIE_C SIE_LL)
theorem XIK_Truth : XIK_F.Valid Truth := XIK_of_prov (Derive.d_Truth SIE_LL)
theorem XIK_TopBot : XIK_F.Valid TopBot := XIK_of_prov (Derive.d_TopBot SIE_LL)
theorem XIK_Cantor : XIK_F.Valid Cantor := XIK_of_prov (Derive.d_Cantor SIE_LL)
theorem XIK_WCong : XIK_F.Valid WCong := XIK_of_prov (Derive.d_WCong SIE_LL)

/-! ### Small facts -/

theorem XIK_one_ne_zero : (1 : Fin 3) ≠ 0 := by decide
theorem XIK_img_e_ne_X : XIK_img (.e : Code XIK_B) ≠ XIK_img (.base .X) := by decide
theorem XIK_img_e_ne_arr (a c : Code XIK_B) : XIK_img (.e : Code XIK_B) ≠ XIK_img (.arr a c) := fun h => nomatch h
theorem XIK_toB_t (x : XIK_U.El .t) (c : Bool) : XIK_toB .t x ≠ some c := fun h => nomatch h
theorem XIK_toB_D (x : XIK_U.El (.base .D)) (c : Bool) : XIK_toB (.base .D) x ≠ some c := fun h => nomatch h
theorem XIK_toB_arr (a c : Code XIK_B) (x : XIK_U.El (.arr a c)) (d : Bool) : XIK_toB (.arr a c) x ≠ some d :=
  fun h => nomatch h
theorem XIK_teq_eD : XIK_teq (.arr .e .t) (.arr .e (.base .D)) 0 := ⟨fun _ => by decide, by decide⟩
theorem XIK_not_teq_tD : ¬ XIK_teq .t (.base .D) 0 := fun h => absurd (h.1 rfl) (by decide)
theorem XIK_teq_tD_one : XIK_teq .t (.base .D) 1 := ⟨fun h => absurd h XIK_one_ne_zero, rfl⟩

/-- At the actual world, each entity is identified with the item of `X` with its value. -/
theorem XIK_cross_eX (c : Bool) : XIK_eqv .e (.base .X) c c 0 :=
  Or.inr ⟨rfl, And.intro (fun h => nomatch h) ⟨c, rfl, rfl⟩⟩

/-- At world `1`, no entity is identified with an item of `X`. -/
theorem XIK_not_eX_one (c c' : Bool) : ¬ XIK_eqv .e (.base .X) c c' 1 := by
  rintro (⟨⟨_, hi⟩, _⟩ | ⟨h1, _⟩)
  · exact XIK_img_e_ne_X hi
  · exact XIK_one_ne_zero h1

/-! ### Inj≈, Recovery and ND≈ fail -/

/-- `e → t ≈ e → D` at the actual world, but not `t ≈ D`. -/
theorem XIK_not_Inj : ¬ XIK_F.Valid Inj := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_tall _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp
    ((XIK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) .e (Or.inr trivial)) .t (Or.inr trivial))
    (.base .D) (Or.inr trivial)
  have h2 := (XIK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIK_F.holdsAt_teq _ _ _ _ _).mpr XIK_teq_eD)
  exact XIK_not_teq_tD ((XIK_F.holdsAt_teq _ _ _ _ _).mp ((XIK_F.holdsAt_conj _ _ _ _ _).mp h2).2)

theorem XIK_not_Recovery : ¬ XIK_F.Valid Recovery := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_tall _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp
    ((XIK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) .e (Or.inr trivial)) .t (Or.inr trivial))
    (.base .D) (Or.inr trivial)
  have h2 := (XIK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIK_F.holdsAt_conj _ _ _ _ _).mpr
    ⟨(XIK_F.holdsAt_teq _ _ _ _ _).mpr XIK_teq_eD, (XIK_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => rfl, rfl⟩⟩)
  exact XIK_not_teq_tD ((XIK_F.holdsAt_teq _ _ _ _ _).mp h2)

/-- `t` and `D` are distinct at the actual world, but `≈` at world `1`. -/
theorem XIK_not_NDTeq : ¬ XIK_F.Valid NDTeq := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_tall _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial))
    (.base .D) (Or.inr trivial)
  have h2 := (XIK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIK_F.holdsAt_neg _ _ _ _).mpr fun ht =>
    XIK_not_teq_tD ((XIK_F.holdsAt_teq _ _ _ _ _).mp ht))
  have h3 := (XIK_F.box_of XIK_heq _ _ _ _).mp h2 (1 : Fin 3) (Or.inr rfl)
  exact (XIK_F.holdsAt_neg _ _ _ _).mp h3 ((XIK_F.holdsAt_teq _ _ _ _ _).mpr XIK_teq_tD_one)

/-! ### Identity across types -/

/-- The entity `true` is identified with the item `true` of `X` at the actual world, but not at
world `1`. -/
theorem XIK_not_NIX : ¬ XIK_F.Valid NIX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_tall _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base .X) (Or.inr trivial)
  have h2 := (XIK_F.holdsAt_all _ _ _ _ _).mp ((XIK_F.holdsAt_all _ _ _ _ _).mp h1 true rfl) true rfl
  have h3 := (XIK_F.holdsAt_imp _ _ _ _ _).mp h2 ((XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XIK_cross_eX true))
  have h4 := (XIK_F.box_of XIK_heq _ _ _ _).mp h3 (1 : Fin 3) (Or.inr rfl)
  exact XIK_not_eX_one true true ((XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h4)

theorem XIK_not_Disjoint : ¬ XIK_F.Valid Disjoint := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_tall _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base .X) (Or.inr trivial)
  have h2 := (XIK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIK_F.holdsAt_neg _ _ _ _).mpr fun ht =>
    XIK_img_e_ne_X ((XIK_F.holdsAt_teq _ _ _ _ _).mp ht).2)
  have h3 := (XIK_F.holdsAt_all _ _ _ _ _).mp ((XIK_F.holdsAt_all _ _ _ _ _).mp h2 true rfl) true rfl
  exact (XIK_F.holdsAt_neg _ _ _ _).mp h3 ((XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XIK_cross_eX true))

/-- No entity is identified with a property. -/
theorem XIK_Slogan : XIK_F.Valid Slogan := by
  refine XIK_Valid_of ?_
  refine (XIK_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XIK_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XIK_F.holdsAt_all _ _ _ _ _).mpr fun y _ => (XIK_F.holdsAt_neg _ _ _ _).mpr fun hxy => ?_
  rcases (XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mp hxy with ⟨⟨_, hi⟩, _⟩ | ⟨_, _, c, _, hc⟩
  · exact XIK_img_e_ne_arr _ _ hi
  · exact XIK_toB_arr _ _ _ _ hc

/-- `e` and `X` are coextensive at the actual world, but not `≈`. -/
theorem XIK_not_ExtT : ¬ XIK_F.Valid ExtT := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_tall _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base .X) (Or.inr trivial)
  have hc : XIK_F.HoldsAt (Tm.conj (subT : Fm (Ctx.nil.text.text)) supT)
      (scons (.base .X) (scons .e (fun i => i.elim0))) () XIK_U.w0 := by
    refine (XIK_F.holdsAt_conj _ _ _ _ _).mpr ⟨?_, ?_⟩
    · refine (XIK_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XIK_F.holdsAt_ex _ _ _ _ _).mpr ⟨x, rfl, ?_⟩
      exact (XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XIK_cross_eX x)
    · refine (XIK_F.holdsAt_all _ _ _ _ _).mpr fun y _ => (XIK_F.holdsAt_ex _ _ _ _ _).mpr ⟨y, rfl, ?_⟩
      exact (XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XIK_cross_eX y)
  have h2 := (XIK_F.holdsAt_imp _ _ _ _ _).mp h1 hc
  exact XIK_img_e_ne_X ((XIK_F.holdsAt_teq _ _ _ _ _).mp h2).2

/-- If, at the actual world and at world `1`, each item of `α` is identified with an item of `β`,
then `α ≈ β`: identity across types other than by key holds only at the actual world. -/
theorem XIK_IntT : XIK_F.Valid IntT := by
  refine XIK_Valid_of ?_
  refine (XIK_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XIK_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XIK_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hs := (XIK_F.box_of XIK_heq _ _ _ _).mp ((XIK_F.holdsAt_conj _ _ _ _ _).mp h).1
  obtain ⟨x0, hx0⟩ := XIK_U.adm_nonempty a
  have h0 := (XIK_F.holdsAt_all _ _ _ _ _).mp (hs XIK_U.w0 (XIK_U.Rrefl _)) x0 (hx0 _)
  obtain ⟨y, _, hxy⟩ := (XIK_F.holdsAt_ex _ _ _ _ _).mp h0
  rcases (XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mp hxy with ⟨ht, _⟩ | ⟨_, hne, c, hxc, hyc⟩
  · exact (XIK_F.holdsAt_teq _ _ _ _ _).mpr ht
  · exfalso
    have h1 := (XIK_F.holdsAt_all _ _ _ _ _).mp (hs (1 : Fin 3) (Or.inr rfl)) x0 (hx0 _)
    obtain ⟨y', _, hxy'⟩ := (XIK_F.holdsAt_ex _ _ _ _ _).mp h1
    rcases (XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mp hxy' with ⟨⟨_, hi⟩, _⟩ | ⟨h10, _⟩
    · exact hne ((XIK_toB_img hxc).symm.trans (hi.trans (XIK_toB_img hyc)))
    · exact XIK_one_ne_zero h10

theorem XIK_not_Twin : ¬ XIK_F.Valid Twin := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_all _ _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial))
    (fun _ => True) (fun _ _ => Iff.rfl)
  obtain ⟨b, _, h2⟩ := (XIK_F.holdsAt_tex _ _ _ _).mp h1
  have h3 := (XIK_F.holdsAt_conj _ _ _ _ _).mp h2
  obtain ⟨y, _, h4⟩ := (XIK_F.holdsAt_ex _ _ _ _ _).mp h3.2
  rcases (XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h4 with ⟨ht, _⟩ | ⟨_, _, c, hc, _⟩
  · exact (XIK_F.holdsAt_neg _ _ _ _).mp h3.1 ((XIK_F.holdsAt_teq _ _ _ _ _).mpr ht)
  · exact XIK_toB_t _ _ hc

theorem XIK_not_Hae : ¬ XIK_F.Valid Hae := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_all _ _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) true rfl
  rcases (XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h1 with ⟨⟨_, i⟩, _⟩ | ⟨_, _, c, _, hc⟩
  · exact XIK_img_e_ne_arr _ _ i
  · exact XIK_toB_arr _ _ _ _ hc

/-! ### The congruence principles -/

/-- The constant functions to `⊤`, of types `e → t` and `e → D`. -/
def XIK_kt : XIK_U.El (.arr .e .t) := fun _ _ => True
def XIK_kD : XIK_U.El (.arr .e (.base .D)) := fun _ _ => True

theorem XIK_kt_adm (w : Fin 3) : XIK_U.rel (.arr .e .t) w XIK_kt XIK_kt := fun _ _ _ _ _ _ _ => Iff.rfl
theorem XIK_kD_adm (w : Fin 3) : XIK_U.rel (.arr .e (.base .D)) w XIK_kD XIK_kD := fun _ _ _ _ _ _ _ => Iff.rfl

/-- The two constant functions are identified at the actual world. -/
theorem XIK_ktD : XIK_eqv (.arr .e .t) (.arr .e (.base .D)) XIK_kt XIK_kD 0 :=
  Or.inl ⟨XIK_teq_eD, fun _ _ _ _ _ _ _ => Iff.rfl⟩

/-- Nothing of type `t` is identified with anything of type `D` at the actual world. -/
theorem XIK_not_tD (p : XIK_U.El .t) (q : XIK_U.El (.base .D)) : ¬ XIK_eqv .t (.base .D) p q 0 := by
  rintro (⟨ht, _⟩ | ⟨_, _, c, hc, _⟩)
  · exact XIK_not_teq_tD ht
  · exact XIK_toB_t _ _ hc

theorem XIK_not_Cong : ¬ XIK_F.Valid Cong := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_tall _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp
    ((XIK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) .e (Or.inr trivial)) .t (Or.inr trivial))
    (.base .D) (Or.inr trivial)
  have h2 := (XIK_F.holdsAt_all _ _ _ _ _).mp ((XIK_F.holdsAt_all _ _ _ _ _).mp ((XIK_F.holdsAt_all _ _ _ _ _).mp
    ((XIK_F.holdsAt_all _ _ _ _ _).mp h1 XIK_kt (XIK_kt_adm _)) XIK_kD (XIK_kD_adm _)) true rfl) true rfl
  have h3 := (XIK_F.holdsAt_imp _ _ _ _ _).mp h2 ((XIK_F.holdsAt_conj _ _ _ _ _).mpr
    ⟨(XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr XIK_ktD,
     (XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ((XIK_heq .e _ _ _).mpr rfl)⟩)
  exact XIK_not_tD _ _ ((XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h3)

theorem XIK_not_PCong : ¬ XIK_F.Valid PCong := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_tall _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp
    ((XIK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) .t (Or.inr trivial)) (.base .D) (Or.inr trivial)
  have h2 := (XIK_F.holdsAt_all _ _ _ _ _).mp ((XIK_F.holdsAt_all _ _ _ _ _).mp
    ((XIK_F.holdsAt_all _ _ _ _ _).mp h1 XIK_kt (XIK_kt_adm _)) XIK_kD (XIK_kD_adm _)) true rfl
  have h3 := (XIK_F.holdsAt_imp _ _ _ _ _).mp h2 ((XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr XIK_ktD)
  exact XIK_not_tD _ _ ((XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h3)

/-- The constant functions to `true`, of types `e → e` and `e → X`. -/
def XIK_ke : XIK_U.El (.arr .e .e) := fun _ => true
def XIK_kX : XIK_U.El (.arr .e (.base .X)) := fun _ => true

theorem XIK_ke_adm (w : Fin 3) : XIK_U.rel (.arr .e .e) w XIK_ke XIK_ke := fun _ _ _ _ _ => rfl
theorem XIK_kX_adm (w : Fin 3) : XIK_U.rel (.arr .e (.base .X)) w XIK_kX XIK_kX :=
  fun _ _ _ _ _ => (rfl : (true : Bool) = true)

theorem XIK_img_ee_ne_eX : XIK_img (.arr .e .e : Code XIK_B) ≠ XIK_img (.arr .e (.base .X)) := by decide

/-- The two constant functions agree pointwise up to identity, but are not identified. -/
theorem XIK_not_PExt : ¬ XIK_F.Valid PExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_tall _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp
    ((XIK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) .e (Or.inr trivial)) (.base .X) (Or.inr trivial)
  have h2 := (XIK_F.holdsAt_all _ _ _ _ _).mp ((XIK_F.holdsAt_all _ _ _ _ _).mp h1 XIK_ke (XIK_ke_adm _))
    XIK_kX (XIK_kX_adm _)
  have h3 := (XIK_F.holdsAt_imp _ _ _ _ _).mp h2 ((XIK_F.holdsAt_all _ _ _ _ _).mpr fun _ _ =>
    (XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XIK_cross_eX true))
  rcases (XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h3 with ⟨⟨_, i⟩, _⟩ | ⟨_, _, c, hc, _⟩
  · exact XIK_img_ee_ne_eX i
  · exact XIK_toB_arr _ _ _ _ hc

/-! ### LL≡-Poly fails; LL≡/≈ holds, with parameters -/

set_option maxHeartbeats 4000000 in
theorem XIK_PredE_iff1 (x y : Bool) :
    XIK_F.HoldsAt (.app (.tapp ((PredE.twk.twk.wk tv1).wk tv0) tv1) (.var (.there .here)))
      (scons (.base .X) (scons .e (fun i => i.elim0))) (((), x), y) XIK_U.w0 ↔ XIK_teq .e .e 0 := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem XIK_PredE_iff0 (x y : Bool) :
    XIK_F.HoldsAt (.app (.tapp ((PredE.twk.twk.wk tv1).wk tv0) tv0) (.var .here))
      (scons (.base .X) (scons .e (fun i => i.elim0))) (((), x), y) XIK_U.w0 ↔ XIK_teq (.base .X) .e 0 := Iff.rfl

/-- With `P := λγ.λz.(γ ≈ e)`: the entity `true` is identified with the item `true` of `X`, but
only the first has `P`. -/
theorem XIK_not_LLPoly : ¬ XIK_F.Valid (LLPoly PredE) := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_tall _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base .X) (Or.inr trivial)
  have h2 := (XIK_F.holdsAt_all _ _ _ _ _).mp ((XIK_F.holdsAt_all _ _ _ _ _).mp h1 true rfl) true rfl
  have h3 := (XIK_F.holdsAt_imp _ _ _ _ _).mp h2 ((XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XIK_cross_eX true))
  have h4 := (XIK_F.holdsAt_imp _ _ _ _ _).mp h3 ((XIK_PredE_iff1 true true).mpr ⟨fun _ => rfl, rfl⟩)
  exact XIK_img_e_ne_X ((XIK_PredE_iff0 true true).mp h4).2.symm

theorem XIK_evalP {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XIK_F.U.TEnv n)
    (env : XIK_F.U.Env Γ ρ) (a b : Code XIK_B) (x : XIK_U.El a) (y : XIK_U.El b) :
    HEq (XIK_F.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y)) (XIK_F.eval P ρ env) := by
  have e1 : XIK_F.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y) =
      XIK_F.eval (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) :=
    XIK_F.eval_wk tv0 (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) y
  have e2 : XIK_F.eval (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) =
      XIK_F.eval P.twk.twk (scons b (scons a ρ)) env := XIK_F.eval_wk tv1 P.twk.twk (scons b (scons a ρ)) env x
  exact (heq_of_eq (e1.trans e2)).trans ((XIK_F.eval_twk P.twk b (scons a ρ) env).trans (XIK_F.eval_twk P a ρ env))

theorem XIK_evalP1 {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XIK_F.U.TEnv n)
    (env : XIK_F.U.Env Γ ρ) (a b : Code XIK_B) (x : XIK_U.El a) (y : XIK_U.El b) (w : Fin 3) :
    XIK_F.HoldsAt (.app (.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (.var (.there .here))) (scons b (scons a ρ))
      ((env, x), y) w ↔ XIK_F.eval P ρ env a x w := by
  have h1 : HEq (XIK_F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (scons b (scons a ρ)) ((env, x), y))
      (XIK_F.eval P ρ env a) :=
    (XIK_F.heq_eval_tapp ((P.twk.twk.wk tv1).wk tv0) tv1 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => XIK_U.El c → Fin 3 → Prop) (Q := fun c => XIK_U.El c → Fin 3 → Prop)
        (fun _ => rfl) (XIK_evalP P ρ env a b x y) rfl)
  have e := congrFun (congrFun (eq_of_heq h1) x) w
  exact Iff.of_eq e

theorem XIK_evalP0 {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XIK_F.U.TEnv n)
    (env : XIK_F.U.Env Γ ρ) (a b : Code XIK_B) (x : XIK_U.El a) (y : XIK_U.El b) (w : Fin 3) :
    XIK_F.HoldsAt (.app (.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (.var .here)) (scons b (scons a ρ))
      ((env, x), y) w ↔ XIK_F.eval P ρ env b y w := by
  have h1 : HEq (XIK_F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (scons b (scons a ρ)) ((env, x), y))
      (XIK_F.eval P ρ env b) :=
    (XIK_F.heq_eval_tapp ((P.twk.twk.wk tv1).wk tv0) tv0 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => XIK_U.El c → Fin 3 → Prop) (Q := fun c => XIK_U.El c → Fin 3 → Prop)
        (fun _ => rfl) (XIK_evalP P ρ env a b x y) rfl)
  have e := congrFun (congrFun (eq_of_heq h1) y) w
  exact Iff.of_eq e

/-- At the actual world, a polymorphic predicate does not tell apart corresponding items of two
types with the same key. -/
theorem XIK_poly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XIK_F.U.TEnv n)
    (env : XIK_F.U.Env Γ ρ) (henv : XIK_F.EnvAdm Γ ρ XIK_U.w0 env) (a b : Code XIK_B) (x : XIK_U.El a)
    (y : XIK_U.El b) (hab : XIK_Adm XIK_U.w0 a b (XIK_CR a b)) (hxy : XIK_CR a b XIK_U.w0 x y) :
    XIK_F.eval P ρ env a x XIK_U.w0 → XIK_F.eval P ρ env b y XIK_U.w0 := by
  have hrel := XIK_inv.fundamental P ρ ρ (XIK_F.homRs ρ) XIK_U.w0 (fun i => XIK_inv.refl XIK_U.w0 (ρ i)) env env
    (KInv.EnvRel_indep XIK_F.hom XIK_inv Γ ρ ρ _ XIK_U.w0 env env henv) XIK_U.w0 (XIK_U.Rrefl _) a b
    (XIK_CR a b) hab XIK_U.w0 (XIK_U.Rrefl _) x y hxy XIK_U.w0 (XIK_U.Rrefl _)
  exact hrel.mp

/-- LL≡/≈ holds, for every polymorphic predicate, with parameters. -/
theorem XIK_Bridge {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : XIK_F.Valid (Bridge P) := by
  intro ρ _ env henv
  refine (XIK_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XIK_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XIK_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XIK_F.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (XIK_F.holdsAt_imp _ _ _ _ _).mpr fun h => (XIK_F.holdsAt_imp _ _ _ _ _).mpr fun hPx => ?_
  obtain ⟨h1, h2⟩ := (XIK_F.holdsAt_conj _ _ _ _ _).mp h
  obtain ⟨k, i⟩ := (XIK_F.holdsAt_teq _ _ _ _ _).mp h2
  have hk : XIK_K a = XIK_K b := k rfl
  have hxy : XIK_CR a b XIK_U.w0 x y := by
    rcases (XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h1 with ⟨_, r⟩ | ⟨_, hne, c, hxc, _⟩
    · exact r
    · exact absurd (XIK_toB_K_eq hxc hk) (fun e => hne e.symm)
  have hab : XIK_Adm XIK_U.w0 a b (XIK_CR a b) := ⟨i, fun _ _ _ => hk, fun _ _ _ => Iff.rfl⟩
  exact (XIK_evalP0 P ρ env a b x y XIK_U.w0).mpr
    (XIK_poly P ρ env henv a b x y hab hxy ((XIK_evalP1 P ρ env a b x y XIK_U.w0).mp hPx))

/-! ### Modal principles -/

theorem XIK_TAx : XIK_F.Valid TAx := by
  refine XIK_Valid_of ?_
  refine (XIK_F.holdsAt_all _ _ _ _ _).mpr fun p _ => (XIK_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  exact (XIK_F.box_of XIK_heq _ _ _ _).mp h XIK_U.w0 (XIK_U.Rrefl _)

/-- The proposition true just at the actual world is not necessary. -/
theorem XIK_not_Collapse : ¬ XIK_F.Valid Collapse := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_all _ _ _ _ _).mp h (fun (w : Fin 3) => w = 0) (fun _ _ => Iff.rfl)
  have h2 := (XIK_F.box_of XIK_heq _ _ _ _).mp ((XIK_F.holdsAt_imp _ _ _ _ _).mp h1 rfl) (1 : Fin 3) (Or.inr rfl)
  have h3 : (1 : Fin 3) = 0 := h2
  exact XIK_one_ne_zero h3

/-- `⊤` and the proposition true just at world `1` are distinct, but identical at world `1`. -/
theorem XIK_not_NDX : ¬ XIK_F.Valid NDX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_tall _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)) .t
    (Or.inr trivial)
  have h2 := (XIK_F.holdsAt_all _ _ _ _ _).mp ((XIK_F.holdsAt_all _ _ _ _ _).mp h1 (fun _ => True)
    (fun _ _ => Iff.rfl)) (fun (w : Fin 3) => w = 1) (fun _ _ => Iff.rfl)
  refine (XIK_F.holdsAt_neg _ _ _ _).mp ((XIK_F.box_of XIK_heq _ _ _ _).mp ((XIK_F.holdsAt_imp _ _ _ _ _).mp h2
    ((XIK_F.holdsAt_neg _ _ _ _).mpr fun he => ?_)) (1 : Fin 3) (Or.inr rfl)) ?_
  · have he' := (XIK_heq .t _ _ _).mp ((XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mp he)
    have h3 : True ↔ (0 : Fin 3) = 1 := he' (0 : Fin 3) (Or.inl rfl)
    exact absurd (h3.mp trivial) (by decide)
  · refine (XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ((XIK_heq .t _ _ _).mpr fun u hu => ?_)
    have hu' : u = (1 : Fin 3) := XIK_R_ne hu XIK_one_ne_zero
    subst hu'
    exact ⟨fun _ => rfl, fun _ => trivial⟩

/-- `⊤` and the proposition false just at world `1` are equivalent but not identical. -/
theorem XIK_not_PropExt : ¬ XIK_F.Valid PropExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_all _ _ _ _ _).mp ((XIK_F.holdsAt_all _ _ _ _ _).mp h (fun _ => True)
    (fun _ _ => Iff.rfl)) (fun (w : Fin 3) => w ≠ 1) (fun _ _ => Iff.rfl)
  have h2 := (XIK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIK_F.holdsAt_iff _ _ _ _ _).mpr
    (show True ↔ (0 : Fin 3) ≠ 1 from ⟨fun _ => by decide, fun _ => trivial⟩))
  have h3 := (XIK_heq .t _ _ _).mp ((XIK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h2)
  have h4 : True ↔ (1 : Fin 3) ≠ 1 := h3 (1 : Fin 3) (Or.inr rfl)
  exact h4.mp trivial rfl

/-! ### TBF fails: `N` exists only at worlds `1` and `2` -/

/-- Each type existing at the actual world has two items which are distinct at every world. -/
theorem XIK_two_items : ∀ a : Code XIK_B, XIK_noN a → ∃ x y : XIK_U.El a,
    (∀ w, XIK_U.rel a w x x) ∧ (∀ w, XIK_U.rel a w y y) ∧ ∀ w, ¬ XIK_U.rel a w x y
  | .e, _ => ⟨true, false, fun _ => rfl, fun _ => rfl, fun _ h => Bool.noConfusion h⟩
  | .t, _ => ⟨fun _ => True, fun _ => False, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun w h => (h w (XIK_U.Rrefl w)).mp trivial⟩
  | .base .D, _ => ⟨(fun _ => True : Fin 3 → Prop), (fun _ => False : Fin 3 → Prop), fun _ _ _ => Iff.rfl,
      fun _ _ _ => Iff.rfl, fun w h => (h w (Or.inl rfl)).mp trivial⟩
  | .base .X, _ => ⟨(true : Bool), (false : Bool), fun _ => (rfl : (true : Bool) = true),
      fun _ => (rfl : (false : Bool) = false), fun _ h => Bool.noConfusion (h : (true : Bool) = false)⟩
  | .base .N, h => False.elim h
  | .arr a c, ⟨_, hc⟩ => by
    obtain ⟨y1, y2, h1, h2, h12⟩ := XIK_two_items c hc
    obtain ⟨x0, hx0⟩ := XIK_U.adm_nonempty a
    refine ⟨fun _ => y1, fun _ => y2, fun _ v _ _ _ _ => h1 v, fun _ v _ _ _ _ => h2 v, fun w h => ?_⟩
    exact h12 w (h w (XIK_U.Rrefl w) x0 x0 (hx0 w))

theorem XIK_phiBF_iff (a : Code XIK_B) (w : Fin 3) :
    XIK_F.HoldsAt phiBF (scons a (fun i => i.elim0)) () w ↔
      ¬ ∀ x : XIK_U.El a, XIK_U.rel a w x x → ∀ y : XIK_U.El a, XIK_U.rel a w y y → XIK_U.rel a w x y := by
  refine (XIK_F.holdsAt_neg _ _ _ _).trans (not_congr ?_)
  refine (XIK_F.holdsAt_all _ _ _ _ _).trans (forall_congr' fun x => imp_congr Iff.rfl ?_)
  refine (XIK_F.holdsAt_all _ _ _ _ _).trans (forall_congr' fun y => imp_congr Iff.rfl ?_)
  exact (XIK_F.holdsAt_eqv _ _ _ _ _ _ _).trans (XIK_heq _ _ _ _)

/-- At the actual world, every type necessarily has two distinct items; but at world `1`, `N`
does not. -/
theorem XIK_not_TBF : ¬ XIK_F.Valid (TBFI phiBF) := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have hA : XIK_F.HoldsAt (tall (boxF phiBF)) (fun i => i.elim0) () XIK_U.w0 := by
    refine (XIK_F.holdsAt_tall _ _ _ _).mpr fun a ha => (XIK_F.box_of XIK_heq _ _ _ _).mpr fun v _ => ?_
    have hna : XIK_noN a := Or.resolve_left ha (fun h => h rfl)
    obtain ⟨x, y, hx, hy, hxy⟩ := XIK_two_items a hna
    exact (XIK_phiBF_iff a v).mpr fun h => hxy v (h x (hx v) y (hy v))
  have hB := (XIK_F.box_of XIK_heq _ _ _ _).mp ((XIK_F.holdsAt_imp _ _ _ _ _).mp h hA) (1 : Fin 3) (Or.inr rfl)
  have hd := (XIK_F.holdsAt_tall _ _ _ _).mp hB (.base .N) (Or.inl XIK_one_ne_zero)
  exact (XIK_phiBF_iff (.base .N) 1).mp hd fun _ _ _ _ => trivial

theorem XIK_not_TBFSch : ¬ ∀ χ, TBFSch χ → XIK_F.Valid χ := fun h => XIK_not_TBF (h _ ⟨phiBF, rfl⟩)

/-! ### The Barcan formula and Functional Choice fail -/

/-- `t → e`. -/
abbrev XIK_A : Code XIK_B := .arr .t .e

/-- At world `1`, `f₁` (sending `p` to whether `p` is true at `1`) is an item of `t → e`. -/
theorem XIK_f1_adm : XIK_U.rel XIK_A (1 : Fin 3) f1IE f1IE := by
  intro v hv p q hpq
  have hv' : v = (1 : Fin 3) := XIK_R_ne hv XIK_one_ne_zero
  subst hv'
  have e : p (1 : Fin 3) = q (1 : Fin 3) := propext (hpq (1 : Fin 3) (Or.inl rfl))
  show f1IE p = f1IE q
  unfold f1IE
  rw [e]

theorem XIK_relA_eq {v : Fin 3} {x y : XIK_U.El XIK_A} (h : XIK_U.rel XIK_A v x y) : x = y :=
  funext fun p => h v (XIK_U.Rrefl v) p p (fun _ _ => Iff.rfl)

/-- An item of `t → e` at the actual world is constant. -/
theorem XIK_const_of_adm0 {x : XIK_U.El XIK_A} (h : XIK_U.rel XIK_A (0 : Fin 3) x x) (p q : Fin 3 → Prop) :
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

/-- The property of being constant, of items of `t → e`. -/
def XIK_Fc : XIK_U.El (.arr XIK_A .t) := fun (x : (Fin 3 → Prop) → Bool) (_ : Fin 3) => ∀ p q, x p = x q

theorem XIK_Fc_adm : XIK_U.rel (.arr XIK_A .t) (0 : Fin 3) XIK_Fc XIK_Fc := by
  intro v _ x y hxy
  have e : x = y := XIK_relA_eq hxy
  subst e
  exact fun _ _ => Iff.rfl

/-- Every item of `t → e` at the actual world is necessarily constant, but at world `1`, `f₁` is an
item of `t → e` which is not constant. -/
theorem XIK_not_BF : ¬ XIK_F.Valid BF := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_all _ _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp h XIK_A (Or.inr ⟨trivial, trivial⟩))
    XIK_Fc XIK_Fc_adm
  have h2 := (XIK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIK_F.holdsAt_all _ _ _ _ _).mpr fun _ hx =>
    (XIK_F.box_of XIK_heq _ _ _ _).mpr fun _ _ => XIK_const_of_adm0 hx)
  have h3 := (XIK_F.box_of XIK_heq _ _ _ _).mp h2 (1 : Fin 3) (Or.inr rfl)
  have h4 := (XIK_F.holdsAt_all _ _ _ _ _).mp h3 f1IE XIK_f1_adm
  have h5 : ∀ p q : Fin 3 → Prop, f1IE p = f1IE q := h4
  have h6 := h5 (fun _ => True) (fun _ => False)
  rw [f1IE_pos _ trivial, f1IE_neg _ (fun h => h)] at h6
  exact Bool.noConfusion h6

/-- The relation between a proposition and whether it is true. -/
def XIK_Rch : XIK_U.El (.arr .t (.arr .e .t)) := fun (p : Fin 3 → Prop) (y : Bool) (u : Fin 3) => (y = true ↔ p u)

theorem XIK_Rch_adm : XIK_U.rel (.arr .t (.arr .e .t)) (0 : Fin 3) XIK_Rch XIK_Rch := by
  intro v _ p q hpq v' hv' y y' hyy' u hu
  have e : y = y' := hyy'
  subst e
  exact iff_congr Iff.rfl (hpq u (XIK_U.Rtrans _ _ _ hv' hu))

/-- Each proposition is related to an entity, but no item of `t → e` at the actual world chooses
one: such items are constant. -/
theorem XIK_not_Choice : ¬ XIK_F.Valid Choice := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIK_F.holdsAt_all _ _ _ _ _).mp ((XIK_F.holdsAt_tall _ _ _ _).mp
    ((XIK_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)) .e (Or.inr trivial)) XIK_Rch XIK_Rch_adm
  have h2 := (XIK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIK_F.holdsAt_all _ _ _ _ _).mpr fun p _ => by
    refine (XIK_F.holdsAt_ex _ _ _ _ _).mpr ?_
    rcases Classical.em (p (0 : Fin 3)) with hp | hp
    · exact ⟨true, rfl, show (true = true ↔ p (0 : Fin 3)) from ⟨fun _ => hp, fun _ => rfl⟩⟩
    · exact ⟨false, rfl, show (false = true ↔ p (0 : Fin 3)) from
        ⟨fun e => Bool.noConfusion e, fun h => absurd h hp⟩⟩)
  obtain ⟨f, hf, h3⟩ := (XIK_F.holdsAt_ex _ _ _ _ _).mp h2
  have hc := XIK_const_of_adm0 hf
  have h4 : f (fun _ => True) = true ↔ True :=
    (XIK_F.holdsAt_all _ _ _ _ _).mp h3 (fun _ => True) (fun _ _ => Iff.rfl)
  have h5 : f (fun _ => False) = true ↔ False :=
    (XIK_F.holdsAt_all _ _ _ _ _).mp h3 (fun _ => False) (fun _ _ => Iff.rfl)
  exact h5.mp ((hc _ _).symm.trans (h4.mpr trivial))

end Kr
end PIF
