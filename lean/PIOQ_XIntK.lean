import PIBF
import PIOQ_KIE
set_option autoImplicit false

/-!
# A Kripke model of PIᶜ without Int≈, Ext≈, ND≈, ND×, NI×, TBF, BF, Choice or Recovery

`𝔐_k,xi`: three worlds `0, 1, 2`; the actual world `0` sees all three, and `1` and `2` see only
themselves. Entities are booleans. There are two base types: `d`, whose items are booleans too (a
copy of `e`), and `u`, with a single item, which exists only at world `2`. Identity of entities and
of items of the base types is equality at every world; propositions and functions are identical at
a world when they agree, on identical arguments, at every world it sees.

`≈` and identity across types are given world by world.

* At world `1`, `≈` holds between types which agree once `d` is replaced by `e`, and items of such
  types are identified when they correspond (as in `𝔐_k,nd`). So `d ≈ e` at world `1`.
* At worlds `0` and `2`, `≈` holds between types which agree once each `t → d` is replaced by
  `t → e`, and items of such types are identified when they correspond. So `(t → d) ≈ (t → e)`
  there, but `d ≉ e`: Recovery and Inj≈ fail.
* Besides, an entity and an item of `d` are identified at world `0` when they are the same boolean,
  and at world `2` when they are different booleans.

So `e` and `d` necessarily have the same items, but are distinct: Int≈ and Ext≈ fail. `¬(e ≈ d)`
is true but not necessary (ND≈ fails); the entity `true` and the item `true` of `d` are identified,
but not at world `2` (NI× fails). Items of `t → e` at the actual world respect agreement at worlds
`1` and `2`, so they are constant: BF and Functional Choice fail (as in `𝔐_k,ie`). The type `u`
has one item, while every type at the actual world necessarily has two distinct items: TBF fails.

Identity within a type is identity at the world, so the frame validates Classicism, and so every
theorem of PIᶜ. It also validates T, Slogan, Cong, PCong→ and LL≡/≈ (with parameters), and it
refutes Disjoint, Twin, Haecceitism, LL≡-Poly, PCong←, Collapse and PropExt≡.
-/

namespace PIF
namespace Kr
open Tm

/-! ## The universe -/

/-- The items of the base types: `d` (`false`) has two, `u` (`true`) one. -/
def XIE_B : Bool → Type
  | false => Bool
  | true => Unit

/-- Types in which `u` does not occur. -/
def XIE_noU : Code Bool → Prop
  | .e => True
  | .t => True
  | .base b => b = false
  | .arr a c => XIE_noU a ∧ XIE_noU c

def XIE_U : Univ where
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
  Base := Bool
  B := XIE_B
  neE := ⟨true⟩
  neB := fun b => match b with
    | false => ⟨true⟩
    | true => ⟨()⟩
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
  D := fun w a => w = 2 ∨ XIE_noU a
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

/-- World `1` sees only itself. -/
theorem XIE_R_ne1 {w v : Fin 3} (h : XIE_U.R w v) (hv : v ≠ 1) : w ≠ 1 := by
  rintro rfl
  rcases h with h | h
  · exact hv h.symm
  · exact absurd h (by decide)

/-! ## Two ways of identifying types -/

/-- The type got by putting `e` for `d`. -/
def XIE_img : Code Bool → Code Bool
  | .e => .e
  | .t => .t
  | .base false => .e
  | .base true => .base true
  | .arr a c => .arr (XIE_img a) (XIE_img c)

/-- An arrow type, with `t → e` put for `t → d`. -/
def XIE_arrN (A C : Code Bool) : Code Bool := if A = .t ∧ C = .base false then .arr .t .e else .arr A C

/-- The type got by putting `t → e` for each `t → d`. -/
def XIE_N : Code Bool → Code Bool
  | .e => .e
  | .t => .t
  | .base b => .base b
  | .arr a c => XIE_arrN (XIE_N a) (XIE_N c)

theorem XIE_img_arrN (A C : Code Bool) : XIE_img (XIE_arrN A C) = .arr (XIE_img A) (XIE_img C) := by
  unfold XIE_arrN
  split
  · rename_i h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · rfl

theorem XIE_img_N : ∀ a : Code Bool, XIE_img (XIE_N a) = XIE_img a
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => by
    show XIE_img (XIE_arrN (XIE_N a) (XIE_N c)) = _
    rw [XIE_img_arrN, XIE_img_N a, XIE_img_N c]
    rfl

theorem XIE_img_of_N {a b : Code Bool} (h : XIE_N a = XIE_N b) : XIE_img a = XIE_img b := by
  rw [← XIE_img_N a, h, XIE_img_N]

theorem XIE_arrN_arr (A C : Code Bool) : ∃ X Y, XIE_arrN A C = .arr X Y := by
  unfold XIE_arrN
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem XIE_N_e {a : Code Bool} (h : XIE_N a = .e) : a = .e := by
  cases a with
  | e => rfl
  | t => exact nomatch h
  | base _ => exact nomatch h
  | arr a c =>
    obtain ⟨X, Y, hXY⟩ := XIE_arrN_arr (XIE_N a) (XIE_N c)
    have h' : XIE_arrN (XIE_N a) (XIE_N c) = .e := h
    rw [hXY] at h'
    exact nomatch h'

theorem XIE_N_d {a : Code Bool} (h : XIE_N a = .base false) : a = .base false := by
  cases a with
  | e => exact nomatch h
  | t => exact nomatch h
  | base b => exact h
  | arr a c =>
    obtain ⟨X, Y, hXY⟩ := XIE_arrN_arr (XIE_N a) (XIE_N c)
    have h' : XIE_arrN (XIE_N a) (XIE_N c) = .base false := h
    rw [hXY] at h'
    exact nomatch h'

theorem XIE_N_t {a : Code Bool} (h : XIE_N a = .t) : a = .t := by
  cases a with
  | e => exact nomatch h
  | t => rfl
  | base _ => exact nomatch h
  | arr a c =>
    obtain ⟨X, Y, hXY⟩ := XIE_arrN_arr (XIE_N a) (XIE_N c)
    have h' : XIE_arrN (XIE_N a) (XIE_N c) = .t := h
    rw [hXY] at h'
    exact nomatch h'

theorem XIE_img_e {a : Code Bool} (h : XIE_img a = .e) : a = .e ∨ a = .base false := by
  cases a with
  | e => exact Or.inl rfl
  | t => exact nomatch h
  | base b => cases b with
    | false => exact Or.inr rfl
    | true => exact nomatch h
  | arr _ _ => exact nomatch h

theorem XIE_img_t {a : Code Bool} (h : XIE_img a = .t) : a = .t := by
  cases a with
  | e => exact nomatch h
  | t => rfl
  | base b => cases b with
    | false => exact nomatch h
    | true => exact nomatch h
  | arr _ _ => exact nomatch h

theorem XIE_img_base {a : Code Bool} {b : Bool} (h : XIE_img a = .base b) : a = .base true ∧ b = true := by
  cases a with
  | e => exact nomatch h
  | t => exact nomatch h
  | base c => cases c with
    | false => exact nomatch h
    | true => injection h with h; exact ⟨rfl, h.symm⟩
  | arr _ _ => exact nomatch h

theorem XIE_img_arr {a k1 k2 : Code Bool} (h : XIE_img a = .arr k1 k2) :
    ∃ a1 a2, a = .arr a1 a2 ∧ XIE_img a1 = k1 ∧ XIE_img a2 = k2 := by
  cases a with
  | arr a1 a2 => injection h with h1 h2; exact ⟨a1, a2, rfl, h1, h2⟩
  | e => exact nomatch h
  | t => exact nomatch h
  | base b => cases b with
    | false => exact nomatch h
    | true => exact nomatch h

/-! ## Identity between items of types with the same image -/

/-- Identity at a world between items of types with the same image. -/
def XIE_CR : (a b : Code Bool) → Fin 3 → XIE_U.El a → XIE_U.El b → Prop
  | .e, .e => fun _ x y => x = y
  | .e, .base false => fun _ x y => x = y
  | .base false, .e => fun _ x y => x = y
  | .base false, .base false => fun _ x y => x = y
  | .base true, .base true => fun _ x y => x = y
  | .t, .t => fun w p q => ∀ v, XIE_U.R w v → (p v ↔ q v)
  | .arr a c, .arr b d => fun w f g => ∀ v, XIE_U.R w v → ∀ x y, XIE_CR a b v x y → XIE_CR c d v (f x) (g y)
  | _, _ => fun _ _ _ => False

theorem XIE_CR_diag : ∀ (a : Code Bool) (w : Fin 3) (x y : XIE_U.El a), XIE_U.rel a w x y ↔ XIE_CR a a w x y
  | .e, _, _, _ => Iff.rfl
  | .t, _, _, _ => Iff.rfl
  | .base false, _, _, _ => Iff.rfl
  | .base true, _, _, _ => Iff.rfl
  | .arr a c, _, _, _ => forall_congr' fun v => imp_congr Iff.rfl (forall_congr' fun x => forall_congr' fun y =>
      imp_congr (XIE_CR_diag a v x y) (XIE_CR_diag c v _ _))

theorem XIE_CR_mono (a b : Code Bool) (w v : Fin 3) (x : XIE_U.El a) (y : XIE_U.El b) (hv : XIE_U.R w v)
    (h : XIE_CR a b w x y) : XIE_CR a b v x y := by
  rcases a with _ | _ | (_ | _) | ⟨a1, a2⟩ <;> rcases b with _ | _ | (_ | _) | ⟨b1, b2⟩ <;>
    first | exact h | exact fun u hu => h u (XIE_U.Rtrans _ _ _ hv hu)

/-- Transport, both ways, between types with the same image. -/
noncomputable def XIE_Tr : (a b : Code Bool) → (XIE_U.El a → XIE_U.El b) × (XIE_U.El b → XIE_U.El a)
  | .e, .e => (fun x => x, fun x => x)
  | .e, .base false => (fun x => x, fun x => x)
  | .base false, .e => (fun x => x, fun x => x)
  | .base false, .base false => (fun x => x, fun x => x)
  | .base true, .base true => (fun x => x, fun x => x)
  | .t, .t => (fun p => p, fun p => p)
  | .arr a c, .arr b d => (fun f y => (XIE_Tr c d).1 (f ((XIE_Tr a b).2 y)),
      fun g x => (XIE_Tr c d).2 (g ((XIE_Tr a b).1 x)))
  | a, b => (fun _ => Classical.choose (XIE_U.adm_nonempty b), fun _ => Classical.choose (XIE_U.adm_nonempty a))

noncomputable abbrev XIE_Tf (a b : Code Bool) : XIE_U.El a → XIE_U.El b := (XIE_Tr a b).1
noncomputable abbrev XIE_Tg (a b : Code Bool) : XIE_U.El b → XIE_U.El a := (XIE_Tr a b).2

set_option maxHeartbeats 2000000 in
/-- Identity between types of one shape is symmetric and transitive, and transport takes each item
to one identified with it. -/
theorem XIE_shape : ∀ k : Code Bool,
    (∀ a b, XIE_img a = k → XIE_img b = k → ∀ w x y, XIE_CR a b w x y → XIE_CR b a w y x) ∧
    (∀ a b c, XIE_img a = k → XIE_img b = k → XIE_img c = k → ∀ w x y z,
      XIE_CR a b w x y → XIE_CR b c w y z → XIE_CR a c w x z) ∧
    (∀ a b, XIE_img a = k → XIE_img b = k → ∀ w x, XIE_CR a a w x x →
      XIE_CR a b w x (XIE_Tf a b x) ∧ XIE_CR b b w (XIE_Tf a b x) (XIE_Tf a b x)) ∧
    (∀ a b, XIE_img a = k → XIE_img b = k → ∀ w y, XIE_CR b b w y y →
      XIE_CR a b w (XIE_Tg a b y) y ∧ XIE_CR a a w (XIE_Tg a b y) (XIE_Tg a b y)) := by
  intro k
  induction k with
  | e =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b ha hb w x y h
      rcases XIE_img_e ha with rfl | rfl <;> rcases XIE_img_e hb with rfl | rfl <;> exact Eq.symm h
    · intro a b c ha hb hc w x y z h1 h2
      rcases XIE_img_e ha with rfl | rfl <;> rcases XIE_img_e hb with rfl | rfl <;>
        rcases XIE_img_e hc with rfl | rfl <;> exact Eq.trans h1 h2
    · intro a b ha hb w x _
      rcases XIE_img_e ha with rfl | rfl <;> rcases XIE_img_e hb with rfl | rfl <;> exact ⟨rfl, rfl⟩
    · intro a b ha hb w x _
      rcases XIE_img_e ha with rfl | rfl <;> rcases XIE_img_e hb with rfl | rfl <;> exact ⟨rfl, rfl⟩
  | t =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b ha hb w x y h
      have e1 := XIE_img_t ha; have e2 := XIE_img_t hb; subst e1; subst e2
      exact fun v hv => (h v hv).symm
    · intro a b c ha hb hc w x y z h1 h2
      have e1 := XIE_img_t ha; have e2 := XIE_img_t hb; have e3 := XIE_img_t hc; subst e1; subst e2; subst e3
      exact fun v hv => (h1 v hv).trans (h2 v hv)
    · intro a b ha hb w x hx
      have e1 := XIE_img_t ha; have e2 := XIE_img_t hb; subst e1; subst e2
      exact ⟨hx, hx⟩
    · intro a b ha hb w x hx
      have e1 := XIE_img_t ha; have e2 := XIE_img_t hb; subst e1; subst e2
      exact ⟨hx, hx⟩
  | base k0 =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b ha hb w x y h
      obtain ⟨rfl, _⟩ := XIE_img_base ha; obtain ⟨rfl, _⟩ := XIE_img_base hb
      exact Eq.symm h
    · intro a b c ha hb hc w x y z h1 h2
      obtain ⟨rfl, _⟩ := XIE_img_base ha; obtain ⟨rfl, _⟩ := XIE_img_base hb
      obtain ⟨rfl, _⟩ := XIE_img_base hc
      exact Eq.trans h1 h2
    · intro a b ha hb w x _
      obtain ⟨rfl, _⟩ := XIE_img_base ha; obtain ⟨rfl, _⟩ := XIE_img_base hb
      exact ⟨rfl, rfl⟩
    · intro a b ha hb w x _
      obtain ⟨rfl, _⟩ := XIE_img_base ha; obtain ⟨rfl, _⟩ := XIE_img_base hb
      exact ⟨rfl, rfl⟩
  | arr k1 k2 ih1 ih2 =>
    obtain ⟨S1, R1, P1, Q1⟩ := ih1
    obtain ⟨S2, R2, P2, Q2⟩ := ih2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b ha hb w f g h
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XIE_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XIE_img_arr hb
      intro v hv x y hxy
      exact S2 a2 b2 ha2 hb2 v _ _ (h v hv y x (S1 b1 a1 hb1 ha1 v x y hxy))
    · intro a b c ha hb hc w f g h hfg hgh
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XIE_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XIE_img_arr hb
      obtain ⟨c1, c2, rfl, hc1, hc2⟩ := XIE_img_arr hc
      intro v hv x z hxz
      have hzz : XIE_CR c1 c1 v z z := R1 c1 a1 c1 hc1 ha1 hc1 v z x z (S1 a1 c1 ha1 hc1 v x z hxz) hxz
      obtain ⟨hyz, _⟩ := Q1 b1 c1 hb1 hc1 v z hzz
      have hxy : XIE_CR a1 b1 v x (XIE_Tg b1 c1 z) := R1 a1 c1 b1 ha1 hc1 hb1 v x z _ hxz (S1 b1 c1 hb1 hc1 v _ z hyz)
      exact R2 a2 b2 c2 ha2 hb2 hc2 v _ _ _ (hfg v hv x _ hxy) (hgh v hv _ z hyz)
    · intro a b ha hb w f hf
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XIE_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XIE_img_arr hb
      refine ⟨?_, ?_⟩
      · intro v hv x y hxy
        have hyy : XIE_CR b1 b1 v y y := R1 b1 a1 b1 hb1 ha1 hb1 v y x y (S1 a1 b1 ha1 hb1 v x y hxy) hxy
        obtain ⟨hTy, hTT⟩ := Q1 a1 b1 ha1 hb1 v y hyy
        have hxT : XIE_CR a1 a1 v x (XIE_Tg a1 b1 y) := R1 a1 b1 a1 ha1 hb1 ha1 v x y _ hxy (S1 a1 b1 ha1 hb1 v _ y hTy)
        have hfx := hf v hv x _ hxT
        obtain ⟨h1, _⟩ := P2 a2 b2 ha2 hb2 v _ (hf v hv _ _ hTT)
        exact R2 a2 a2 b2 ha2 ha2 hb2 v _ _ _ hfx h1
      · intro v hv y y' hyy'
        have hyy : XIE_CR b1 b1 v y y := R1 b1 b1 b1 hb1 hb1 hb1 v y y' y hyy' (S1 b1 b1 hb1 hb1 v y y' hyy')
        have hy'y' : XIE_CR b1 b1 v y' y' := R1 b1 b1 b1 hb1 hb1 hb1 v y' y y' (S1 b1 b1 hb1 hb1 v y y' hyy') hyy'
        obtain ⟨hTy, hTT⟩ := Q1 a1 b1 ha1 hb1 v y hyy
        obtain ⟨hTy', hT'T'⟩ := Q1 a1 b1 ha1 hb1 v y' hy'y'
        have hTyy : XIE_CR a1 a1 v (XIE_Tg a1 b1 y) (XIE_Tg a1 b1 y') :=
          R1 a1 b1 a1 ha1 hb1 ha1 v _ y _ hTy (R1 b1 b1 a1 hb1 hb1 ha1 v y y' _ hyy' (S1 a1 b1 ha1 hb1 v _ y' hTy'))
        obtain ⟨g1, _⟩ := P2 a2 b2 ha2 hb2 v _ (hf v hv _ _ hTT)
        obtain ⟨g2, _⟩ := P2 a2 b2 ha2 hb2 v _ (hf v hv _ _ hT'T')
        exact R2 b2 a2 b2 hb2 ha2 hb2 v _ _ _ (S2 a2 b2 ha2 hb2 v _ _ g1)
          (R2 a2 a2 b2 ha2 ha2 hb2 v _ _ _ (hf v hv _ _ hTyy) g2)
    · intro a b ha hb w g hg
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := XIE_img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := XIE_img_arr hb
      refine ⟨?_, ?_⟩
      · intro v hv x y hxy
        have hxx : XIE_CR a1 a1 v x x := R1 a1 b1 a1 ha1 hb1 ha1 v x y x hxy (S1 a1 b1 ha1 hb1 v x y hxy)
        obtain ⟨hxT, hTT⟩ := P1 a1 b1 ha1 hb1 v x hxx
        have hTy : XIE_CR b1 b1 v (XIE_Tf a1 b1 x) y := R1 b1 a1 b1 hb1 ha1 hb1 v _ x y (S1 a1 b1 ha1 hb1 v x _ hxT) hxy
        have hgy := hg v hv _ y hTy
        obtain ⟨h1, _⟩ := Q2 a2 b2 ha2 hb2 v _ (hg v hv _ _ hTT)
        exact R2 a2 b2 b2 ha2 hb2 hb2 v _ _ _ h1 hgy
      · intro v hv x x' hxx'
        have hxx : XIE_CR a1 a1 v x x := R1 a1 a1 a1 ha1 ha1 ha1 v x x' x hxx' (S1 a1 a1 ha1 ha1 v x x' hxx')
        have hx'x' : XIE_CR a1 a1 v x' x' := R1 a1 a1 a1 ha1 ha1 ha1 v x' x x' (S1 a1 a1 ha1 ha1 v x x' hxx') hxx'
        obtain ⟨hxT, hTT⟩ := P1 a1 b1 ha1 hb1 v x hxx
        obtain ⟨hx'T, hT'T'⟩ := P1 a1 b1 ha1 hb1 v x' hx'x'
        have hTxx : XIE_CR b1 b1 v (XIE_Tf a1 b1 x) (XIE_Tf a1 b1 x') :=
          R1 b1 a1 b1 hb1 ha1 hb1 v _ x _ (S1 a1 b1 ha1 hb1 v x _ hxT) (R1 a1 a1 b1 ha1 ha1 hb1 v x x' _ hxx' hx'T)
        obtain ⟨g1, _⟩ := Q2 a2 b2 ha2 hb2 v _ (hg v hv _ _ hTT)
        obtain ⟨g2, _⟩ := Q2 a2 b2 ha2 hb2 v _ (hg v hv _ _ hT'T')
        exact R2 a2 b2 a2 ha2 hb2 ha2 v _ _ _ g1
          (R2 b2 b2 a2 hb2 hb2 ha2 v _ _ _ (hg v hv _ _ hTxx) (S2 a2 b2 ha2 hb2 v _ _ g2))


theorem XIE_CR_symm {a b : Code Bool} (h : XIE_img a = XIE_img b) {w : Fin 3} {x : XIE_U.El a} {y : XIE_U.El b}
    (hxy : XIE_CR a b w x y) : XIE_CR b a w y x := (XIE_shape (XIE_img a)).1 a b rfl h.symm w x y hxy

theorem XIE_CR_trans {a b c : Code Bool} (h1 : XIE_img a = XIE_img b) (h2 : XIE_img b = XIE_img c) {w : Fin 3}
    {x : XIE_U.El a} {y : XIE_U.El b} {z : XIE_U.El c} (hxy : XIE_CR a b w x y) (hyz : XIE_CR b c w y z) :
    XIE_CR a c w x z :=
  (XIE_shape (XIE_img a)).2.1 a b c rfl h1.symm (h1.trans h2).symm w x y z hxy hyz

/-! ## The frame -/

/-- The extra identifications of entities with items of `d`: at world `0`, of the same boolean; at
world `2`, of different booleans. -/
def XIE_tw : (a b : Code Bool) → Fin 3 → XIE_U.El a → XIE_U.El b → Prop
  | .e, .base false => fun w x y => (w = 0 ∧ x = y) ∨ (w = 2 ∧ x ≠ y)
  | .base false, .e => fun w x y => (w = 0 ∧ x = y) ∨ (w = 2 ∧ x ≠ y)
  | _, _ => fun _ _ _ => False

/-- Identity at a world. -/
def XIE_eqv (a b : Code Bool) (x : XIE_U.El a) (y : XIE_U.El b) (w : Fin 3) : Prop :=
  ((w ≠ 1 → XIE_N a = XIE_N b) ∧ XIE_img a = XIE_img b ∧ XIE_CR a b w x y) ∨ XIE_tw a b w x y

theorem XIE_tw_cases {a b : Code Bool} {w : Fin 3} {x : XIE_U.El a} {y : XIE_U.El b} (h : XIE_tw a b w x y) :
    ((a = .e ∧ b = .base false) ∨ (a = .base false ∧ b = .e)) ∧ w ≠ 1 := by
  rcases a with _ | _ | (_ | _) | ⟨a1, a2⟩ <;> rcases b with _ | _ | (_ | _) | ⟨b1, b2⟩ <;>
    first
    | exact h.elim
    | (refine ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩; rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide)
    | (refine ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩; rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide)

theorem XIE_tw_symm {a b : Code Bool} {w : Fin 3} {x : XIE_U.El a} {y : XIE_U.El b} (h : XIE_tw a b w x y) :
    XIE_tw b a w y x := by
  rcases a with _ | _ | (_ | _) | ⟨a1, a2⟩ <;> rcases b with _ | _ | (_ | _) | ⟨b1, b2⟩ <;>
    first
    | exact h.elim
    | (rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
       · exact Or.inl ⟨h1, h2.symm⟩
       · exact Or.inr ⟨h1, fun e => h2 e.symm⟩)

theorem XIE_tw_diag {a : Code Bool} {w : Fin 3} {x y : XIE_U.El a} : ¬ XIE_tw a a w x y := fun h => by
  obtain ⟨h1 | h1, _⟩ := XIE_tw_cases h
  · exact nomatch h1.1.symm.trans h1.2
  · exact nomatch h1.1.symm.trans h1.2

theorem XIE_bool_ne_ne {x y z : Bool} (h1 : x ≠ y) (h2 : y ≠ z) : x = z := by
  cases x <;> cases y <;> cases z <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2

theorem XIE_eqv_symm {a b : Code Bool} {w : Fin 3} {x : XIE_U.El a} {y : XIE_U.El b} (h : XIE_eqv a b x y w) :
    XIE_eqv b a y x w := by
  rcases h with ⟨h1, h2, h3⟩ | h
  · exact Or.inl ⟨fun hw => (h1 hw).symm, h2.symm, XIE_CR_symm h2 h3⟩
  · exact Or.inr (XIE_tw_symm h)

theorem XIE_eqv_trans {a b c : Code Bool} {w : Fin 3} {x : XIE_U.El a} {y : XIE_U.El b} {z : XIE_U.El c}
    (h1 : XIE_eqv a b x y w) (h2 : XIE_eqv b c y z w) : XIE_eqv a c x z w := by
  rcases h1 with ⟨n1, i1, c1⟩ | t1 <;> rcases h2 with ⟨n2, i2, c2⟩ | t2
  · exact Or.inl ⟨fun hw => (n1 hw).trans (n2 hw), i1.trans i2, XIE_CR_trans i1 i2 c1 c2⟩
  · obtain ⟨hbc, hw⟩ := XIE_tw_cases t2
    rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have ea := XIE_N_e (n1 hw); subst ea
      have exy : x = y := c1
      subst exy; exact Or.inr t2
    · have ea := XIE_N_d (n1 hw); subst ea
      have exy : x = y := c1
      subst exy; exact Or.inr t2
  · obtain ⟨hab, hw⟩ := XIE_tw_cases t1
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have ec := XIE_N_d (n2 hw).symm; subst ec
      have eyz : y = z := c2
      subst eyz; exact Or.inr t1
    · have ec := XIE_N_e (n2 hw).symm; subst ec
      have eyz : y = z := c2
      subst eyz; exact Or.inr t1
  · obtain ⟨hab, _⟩ := XIE_tw_cases t1
    obtain ⟨hbc, _⟩ := XIE_tw_cases t2
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hbc with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact nomatch h3
    · subst h4
      refine Or.inl ⟨fun _ => rfl, rfl, ?_⟩
      show x = z
      rcases t1 with ⟨rfl, e1⟩ | ⟨rfl, e1⟩ <;> rcases t2 with ⟨hw, e2⟩ | ⟨hw, e2⟩
      · exact e1.trans e2
      · exact nomatch hw
      · exact nomatch hw
      · exact XIE_bool_ne_ne e1 e2
    · subst h4
      refine Or.inl ⟨fun _ => rfl, rfl, ?_⟩
      show x = z
      rcases t1 with ⟨rfl, e1⟩ | ⟨rfl, e1⟩ <;> rcases t2 with ⟨hw, e2⟩ | ⟨hw, e2⟩
      · exact e1.trans e2
      · exact nomatch hw
      · exact nomatch hw
      · exact XIE_bool_ne_ne e1 e2
    · exact nomatch h3

/-- Identity respects correspondence between types with one image, which agree once `t → d` is
replaced by `t → e` at the worlds other than `1`. -/
theorem XIE_eqv_imp {a a' b b' : Code Bool} {u : Fin 3} {x : XIE_U.El a} {x' : XIE_U.El a'} {y : XIE_U.El b}
    {y' : XIE_U.El b'} (ia : XIE_img a = XIE_img a') (ib : XIE_img b = XIE_img b')
    (ca : u ≠ 1 → XIE_N a = XIE_N a') (cb : u ≠ 1 → XIE_N b = XIE_N b')
    (hx : XIE_CR a a' u x x') (hy : XIE_CR b b' u y y') : XIE_eqv a b x y u → XIE_eqv a' b' x' y' u := by
  rintro (⟨h1, h2, h3⟩ | h)
  · refine Or.inl ⟨fun hu => (ca hu).symm.trans ((h1 hu).trans (cb hu)), ia.symm.trans (h2.trans ib), ?_⟩
    exact XIE_CR_trans (ia.symm.trans h2) ib (XIE_CR_trans ia.symm h2 (XIE_CR_symm ia hx) h3) hy
  · obtain ⟨hab, hu⟩ := XIE_tw_cases h
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have e1 := XIE_N_e (ca hu).symm; have e2 := XIE_N_d (cb hu).symm
      subst e1; subst e2
      have ex : x = x' := hx
      have ey : y = y' := hy
      subst ex; subst ey; exact Or.inr h
    · have e1 := XIE_N_d (ca hu).symm; have e2 := XIE_N_e (cb hu).symm
      subst e1; subst e2
      have ex : x = x' := hx
      have ey : y = y' := hy
      subst ex; subst ey; exact Or.inr h

theorem XIE_eqv_iff {a a' b b' : Code Bool} {u : Fin 3} {x : XIE_U.El a} {x' : XIE_U.El a'} {y : XIE_U.El b}
    {y' : XIE_U.El b'} (ia : XIE_img a = XIE_img a') (ib : XIE_img b = XIE_img b')
    (ca : u ≠ 1 → XIE_N a = XIE_N a') (cb : u ≠ 1 → XIE_N b = XIE_N b')
    (hx : XIE_CR a a' u x x') (hy : XIE_CR b b' u y y') : XIE_eqv a b x y u ↔ XIE_eqv a' b' x' y' u :=
  ⟨XIE_eqv_imp ia ib ca cb hx hy, XIE_eqv_imp ia.symm ib.symm (fun hu => (ca hu).symm) (fun hu => (cb hu).symm)
    (XIE_CR_symm ia hx) (XIE_CR_symm ib hy)⟩

/-- `𝔐_k,xi`. -/
def XIE_F : Frame where
  U := XIE_U
  eqv := XIE_eqv
  teq := fun a b w => (w ≠ (1 : Fin 3) → XIE_N a = XIE_N b) ∧ XIE_img a = XIE_img b
  eqv_resp := fun u a b x x' y y' hx hy => XIE_eqv_iff rfl rfl (fun _ => rfl) (fun _ => rfl)
    ((XIE_CR_diag a u x x').mp hx) ((XIE_CR_diag b u y y').mp hy)

theorem XIE_heq' (a : Code Bool) (x y : XIE_U.El a) (w : Fin 3) : XIE_eqv a a x y w ↔ XIE_U.rel a w x y :=
  ⟨fun h => h.elim (fun h' => (XIE_CR_diag a w x y).mpr h'.2.2) (fun h' => (XIE_tw_diag h').elim),
   fun h => Or.inl ⟨fun _ => rfl, rfl, (XIE_CR_diag a w x y).mp h⟩⟩

theorem XIE_heq : ∀ a x y w, XIE_F.eqv a a x y w ↔ XIE_F.U.rel a w x y := XIE_heq'

/-- The admissible relations: correspondence between types of one image, from a world on which
they agree once `t → d` is replaced by `t → e` at every world other than `1`. -/
def XIE_Inv : KInv XIE_F where
  Adm := fun w a a' S => XIE_img a = XIE_img a' ∧ (∀ v, XIE_U.R w v → v ≠ (1 : Fin 3) → XIE_N a = XIE_N a') ∧
    ∀ u x y, S u x y ↔ XIE_CR a a' u x y
  amono := fun ⟨h1, h2, h3⟩ hv => ⟨h1, fun u hu => h2 u (XIE_U.Rtrans _ _ _ hv hu), h3⟩
  smono := fun ⟨_, _, h3⟩ u u' x x' _ hu h => (h3 u' x x').mpr (XIE_CR_mono _ _ u u' x x' hu ((h3 u x x').mp h))
  refl := fun _ a => ⟨rfl, fun _ _ _ => rfl, fun u x y => XIE_CR_diag a u x y⟩
  arrow := by
    intro w a a' c c' S T hS hT
    obtain ⟨h1, h2, h3⟩ := hS
    obtain ⟨k1, k2, k3⟩ := hT
    refine ⟨by show Code.arr (XIE_img a) (XIE_img c) = Code.arr (XIE_img a') (XIE_img c'); rw [h1, k1],
      fun v hv hv' => by
        show XIE_arrN (XIE_N a) (XIE_N c) = XIE_arrN (XIE_N a') (XIE_N c')
        rw [h2 v hv hv', k2 v hv hv'], fun u f f' => ?_⟩
    exact forall_congr' fun v => imp_congr Iff.rfl (forall_congr' fun x => forall_congr' fun x' =>
      imp_congr (h3 v x x') (k3 v _ _))
  total := by
    intro w a a' S hS u _ x hx
    obtain ⟨h1, _, h3⟩ := hS
    obtain ⟨hxT, hTT⟩ := (XIE_shape (XIE_img a)).2.2.1 a a' rfl h1.symm u x ((XIE_CR_diag a u x x).mp hx)
    exact ⟨XIE_Tf a a' x, (XIE_CR_diag a' u _ _).mpr hTT, (h3 u x _).mpr hxT⟩
  onto := by
    intro w a a' S hS u _ y hy
    obtain ⟨h1, _, h3⟩ := hS
    obtain ⟨hTy, hTT⟩ := (XIE_shape (XIE_img a)).2.2.2 a a' rfl h1.symm u y ((XIE_CR_diag a' u y y).mp hy)
    exact ⟨XIE_Tg a a' y, (XIE_CR_diag a u _ _).mpr hTT, (h3 u _ y).mpr hTy⟩
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
    exact XIE_eqv_iff h1 k1 (h2 u hu) (k2 u hu) ((h3 u x x').mp hx) ((k3 u y y').mp hy)

theorem XIE_isModelAt : XIE_F.IsModelAt := by
  obtain ⟨h1, h2, h3⟩ := XIE_F.idAx_of (fun a x w hx => (XIE_heq a x x w).mpr hx)
    (fun _ _ _ _ _ h => XIE_eqv_symm h) (fun _ _ _ _ _ _ _ h1 h2 => XIE_eqv_trans h1 h2)
  refine ⟨h1, h2, h3, XIE_F.refTeq_of fun _ _ => ⟨fun _ => rfl, rfl⟩, ?_⟩
  intro n Γ Q w ρ _ env henv
  refine XIE_F.holdsAt_tall _ _ _ w |>.mpr fun a _ => XIE_F.holdsAt_tall _ _ _ w |>.mpr fun b _ => ?_
  refine (XIE_F.holdsAt_imp _ _ _ _ w).mpr fun hab => ?_
  obtain ⟨e1, e2⟩ := (XIE_F.holdsAt_teq (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env w).mp hab
  refine (XIE_F.holdsAt_imp _ _ _ _ w).mpr fun hq => ?_
  exact XIE_Inv.llTeq_at Q w ρ env henv a b (XIE_CR a b)
    ⟨e2, fun v hv hv' => e1 (XIE_R_ne1 hv hv'), fun _ _ _ => Iff.rfl⟩ hq

theorem XIE_LLEqv : XIE_F.Valid LLEqv := fun ρ hρ env henv => XIE_F.LLEqv_of XIE_heq _ ρ hρ env henv
theorem XIE_Class : ∀ χ, ClassSch χ → XIE_F.Valid χ :=
  XIE_F.Class_valid XIE_isModelAt (XIE_F.LLEqv_of XIE_heq) XIE_heq

theorem XIE_Valid_of {φ : Fm Ctx.nil} (h : XIE_F.HoldsAt φ (fun i => i.elim0) () XIE_U.w0) : XIE_F.Valid φ := by
  intro ρ _ env _
  have e1 : ρ = fun i => i.elim0 := funext fun i => i.elim0
  subst e1
  exact h

/-! ## Every theorem of PIᶜ is valid -/

theorem XIE_of_prov {φ : Fm Ctx.nil} (h : Prov SIE Ctx.nil φ) : XIE_F.Valid φ :=
  KIE.valid_of_PIc XIE_F XIE_isModelAt (XIE_F.LLEqv_of XIE_heq) XIE_heq h

open Derive in
theorem XIE_Bool : ∀ φ, BoolSch φ → XIE_F.Valid φ := fun φ h => XIE_of_prov (d_Bool_of_Class SIE_C φ h)
theorem XIE_IdId : XIE_F.Valid IdId := XIE_of_prov (d_IdId_of_Class SIE_C)
theorem XIE_NIEqv : XIE_F.Valid NIEqv := XIE_of_prov (d_NIEqv_of_Class SIE_C SIE_LL)
theorem XIE_NITeq : XIE_F.Valid NITeq := XIE_of_prov (d_NITeq_of_Class SIE_C)
theorem XIE_TNec : XIE_F.Valid TNec := XIE_of_prov (d_TNec_of_Class SIE_C)
theorem XIE_TCBF : ∀ χ, TCBFSch χ → XIE_F.Valid χ := fun χ h => XIE_of_prov (d_TCBF_of_Class SIE_C SIE_LL χ h)
theorem XIE_Nec : XIE_F.Valid Nec := XIE_of_prov (d_Nec_of_Class SIE_C)
theorem XIE_CBF : XIE_F.Valid CBF := XIE_of_prov (d_CBF_of_Class SIE_C SIE_LL)
theorem XIE_Truth : XIE_F.Valid Truth := XIE_of_prov (Derive.d_Truth SIE_LL)
theorem XIE_TopBot : XIE_F.Valid TopBot := XIE_of_prov (Derive.d_TopBot SIE_LL)
theorem XIE_Cantor : XIE_F.Valid Cantor := XIE_of_prov (Derive.d_Cantor SIE_LL)
theorem XIE_WCong : XIE_F.Valid WCong := XIE_of_prov (Derive.d_WCong SIE_LL)

theorem XIE_TAx : XIE_F.Valid TAx := by
  refine XIE_Valid_of ?_
  refine (XIE_F.holdsAt_all _ _ _ _ _).mpr fun p _ => (XIE_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  exact (XIE_F.box_of XIE_heq _ _ _ _).mp h XIE_U.w0 (XIE_U.Rrefl _)

/-! ## Entities and the items of `d` -/

theorem XIE_bool_ne (b : Bool) : b ≠ !b := by cases b <;> decide

theorem XIE_fin3 (w : Fin 3) : w = 0 ∨ w = 1 ∨ w = 2 := by
  revert w; decide

/-- At each world, each entity is identified with an item of `d`. -/
theorem XIE_ed (w : Fin 3) (x : XIE_U.El .e) : ∃ y : XIE_U.El (.base false), XIE_eqv .e (.base false) x y w := by
  rcases XIE_fin3 w with rfl | rfl | rfl
  · exact ⟨x, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨x, Or.inl ⟨fun h => absurd rfl h, rfl, rfl⟩⟩
  · refine ⟨!x, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
    show (x : Bool) ≠ !x
    exact XIE_bool_ne x

/-- At each world, each item of `d` is identified with an entity. -/
theorem XIE_de (w : Fin 3) (y : XIE_U.El (.base false)) : ∃ x : XIE_U.El .e, XIE_eqv .e (.base false) x y w := by
  rcases XIE_fin3 w with rfl | rfl | rfl
  · exact ⟨y, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨y, Or.inl ⟨fun h => absurd rfl h, rfl, rfl⟩⟩
  · refine ⟨!y, Or.inr (Or.inr ⟨rfl, ?_⟩)⟩
    show (!y) ≠ y
    cases y <;> decide

theorem XIE_N_ed : XIE_N .e ≠ XIE_N (.base false) := by decide

/-- `e` and `d` are not identical at the actual world. -/
theorem XIE_not_teq_ed : ¬ XIE_F.teq .e (.base false) XIE_U.w0 := fun h =>
  XIE_N_ed (h.1 (show (0 : Fin 3) ≠ 1 by decide))

theorem XIE_sub_ed {n : Nat} {Γ : Ctx n} (ρ : XIE_U.TEnv n) (env : XIE_U.Env Γ ρ) (w : Fin 3) :
    XIE_F.HoldsAt (subT : Fm (Γ.text.text)) (scons (.base false) (scons .e ρ)) env w ∧
    XIE_F.HoldsAt (supT : Fm (Γ.text.text)) (scons (.base false) (scons .e ρ)) env w := by
  refine ⟨?_, ?_⟩
  · refine (XIE_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XIE_F.holdsAt_ex _ _ _ _ _).mpr ?_
    obtain ⟨y, hy⟩ := XIE_ed w x
    exact ⟨y, rfl, (XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mpr hy⟩
  · refine (XIE_F.holdsAt_all _ _ _ _ _).mpr fun y _ => (XIE_F.holdsAt_ex _ _ _ _ _).mpr ?_
    obtain ⟨x, hx⟩ := XIE_de w y
    exact ⟨x, rfl, (XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mpr hx⟩

/-- `e` and `d` necessarily have the same items, but are distinct. -/
theorem XIE_not_IntT : ¬ XIE_F.Valid IntT := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_tall _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base false) (Or.inr rfl)
  have hc : XIE_F.HoldsAt (Tm.conj (boxF (subT : Fm (Ctx.nil.text.text))) (boxF supT))
      (scons (.base false) (scons .e (fun i => i.elim0))) () XIE_U.w0 :=
    (XIE_F.holdsAt_conj _ _ _ _ _).mpr ⟨(XIE_F.box_of XIE_heq _ _ _ _).mpr fun v _ => (XIE_sub_ed _ _ v).1,
      (XIE_F.box_of XIE_heq _ _ _ _).mpr fun v _ => (XIE_sub_ed _ _ v).2⟩
  exact XIE_not_teq_ed ((XIE_F.holdsAt_teq _ _ _ _ _).mp ((XIE_F.holdsAt_imp _ _ _ _ _).mp h1 hc))

/-- `e` and `d` have the same items, but are distinct. -/
theorem XIE_not_ExtT : ¬ XIE_F.Valid ExtT := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_tall _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base false) (Or.inr rfl)
  have hc : XIE_F.HoldsAt (Tm.conj (subT : Fm (Ctx.nil.text.text)) supT)
      (scons (.base false) (scons .e (fun i => i.elim0))) () XIE_U.w0 :=
    (XIE_F.holdsAt_conj _ _ _ _ _).mpr (XIE_sub_ed _ _ XIE_U.w0)
  exact XIE_not_teq_ed ((XIE_F.holdsAt_teq _ _ _ _ _).mp ((XIE_F.holdsAt_imp _ _ _ _ _).mp h1 hc))

/-- `e` and `d` are distinct, but identical at world `1`. -/
theorem XIE_not_NDTeq : ¬ XIE_F.Valid NDTeq := fun h => by
  have h0 := h (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_tall _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp h0 .e (Or.inr trivial))
    (.base false) (Or.inr rfl)
  have h2 := (XIE_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIE_F.holdsAt_neg _ _ _ _).mpr fun ht =>
    XIE_not_teq_ed ((XIE_F.holdsAt_teq _ _ _ _ _).mp ht))
  have h3 := (XIE_F.box_of XIE_heq _ _ _ _).mp h2 (1 : Fin 3) (Or.inr rfl)
  exact (XIE_F.holdsAt_neg _ _ _ _).mp h3 ((XIE_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun h => absurd rfl h, rfl⟩)

/-- The entity `true` and the item `true` of `d` are identified, but not at world `2`. -/
theorem XIE_not_NIX : ¬ XIE_F.Valid NIX := fun h => by
  have h0 := h (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_tall _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp h0 .e (Or.inr trivial))
    (.base false) (Or.inr rfl)
  have h2 := (XIE_F.holdsAt_all _ _ _ _ _).mp ((XIE_F.holdsAt_all _ _ _ _ _).mp h1 true rfl) true rfl
  have h3 := (XIE_F.holdsAt_imp _ _ _ _ _).mp h2
    ((XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have h4 := (XIE_F.box_of XIE_heq _ _ _ _).mp h3 (2 : Fin 3) (Or.inr rfl)
  rcases (XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mp h4 with ⟨hn, _, _⟩ | ht
  · exact XIE_N_ed (hn (by decide))
  · rcases ht with ⟨h5, _⟩ | ⟨_, h5⟩
    · exact absurd h5 (by decide)
    · exact h5 rfl

/-- `e` and `d` are distinct, but their items are identified. -/
theorem XIE_not_Disjoint : ¬ XIE_F.Valid Disjoint := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_tall _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base false) (Or.inr rfl)
  have h2 := (XIE_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIE_F.holdsAt_neg _ _ _ _).mpr fun ht =>
    XIE_not_teq_ed ((XIE_F.holdsAt_teq _ _ _ _ _).mp ht))
  have h3 := (XIE_F.holdsAt_all _ _ _ _ _).mp ((XIE_F.holdsAt_all _ _ _ _ _).mp h2 true rfl) true rfl
  exact (XIE_F.holdsAt_neg _ _ _ _).mp h3 ((XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)))

/-! ## Modal principles -/

/-- The proposition true just at the actual world is not necessary. -/
theorem XIE_not_Collapse : ¬ XIE_F.Valid Collapse := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_all _ _ _ _ _).mp h (fun (w : Fin 3) => w = 0) (fun _ _ => Iff.rfl)
  have h2 := (XIE_F.box_of XIE_heq _ _ _ _).mp ((XIE_F.holdsAt_imp _ _ _ _ _).mp h1 rfl) (1 : Fin 3) (Or.inr rfl)
  have h3 : (1 : Fin 3) = 0 := h2
  exact absurd h3 (by decide)

/-- `⊤` and the proposition false just at the actual world are distinct, but identical at world `1`. -/
theorem XIE_not_NDX : ¬ XIE_F.Valid NDX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_tall _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)) .t (Or.inr trivial)
  have h2 := (XIE_F.holdsAt_all _ _ _ _ _).mp ((XIE_F.holdsAt_all _ _ _ _ _).mp h1 (fun _ => True)
    (fun _ _ => Iff.rfl)) (fun (w : Fin 3) => w = 1) (fun _ _ => Iff.rfl)
  refine (XIE_F.holdsAt_neg _ _ _ _).mp ((XIE_F.box_of XIE_heq _ _ _ _).mp ((XIE_F.holdsAt_imp _ _ _ _ _).mp h2
    ((XIE_F.holdsAt_neg _ _ _ _).mpr fun he => ?_)) (1 : Fin 3) (Or.inr rfl)) ?_
  · have he' := (XIE_heq .t _ _ _).mp ((XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mp he)
    have h3 : True ↔ (0 : Fin 3) = 1 := he' (0 : Fin 3) (Or.inl rfl)
    exact absurd (h3.mp trivial) (by decide)
  · refine (XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ((XIE_heq .t _ _ _).mpr fun u hu => ?_)
    rcases hu with rfl | hu
    · exact ⟨fun _ => rfl, fun _ => trivial⟩
    · exact absurd hu (by decide)

/-- `⊤` and the proposition false just at world `1` are equivalent but not identical. -/
theorem XIE_not_PropExt : ¬ XIE_F.Valid PropExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_all _ _ _ _ _).mp ((XIE_F.holdsAt_all _ _ _ _ _).mp h (fun _ => True)
    (fun _ _ => Iff.rfl)) (fun (w : Fin 3) => w ≠ 1) (fun _ _ => Iff.rfl)
  have h2 := (XIE_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIE_F.holdsAt_iff _ _ _ _ _).mpr
    (show True ↔ (0 : Fin 3) ≠ 1 from ⟨fun _ => by decide, fun _ => trivial⟩))
  have h3 := (XIE_heq .t _ _ _).mp ((XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mp h2)
  have h4 : True ↔ (1 : Fin 3) ≠ 1 := h3 (1 : Fin 3) (Or.inr rfl)
  exact h4.mp trivial rfl

/-! ### The Barcan formula and Functional Choice fail -/

/-- `A := t → e`. -/
abbrev XIE_A : Code Bool := .arr .t .e
/-- The set `A` names. -/
abbrev XIE_G : Type := (Fin 3 → Prop) → Bool

open Classical in
/-- The function sending `p` to whether `p` is true at world `1`. -/
noncomputable def XIE_f1 (p : Fin 3 → Prop) : Bool := if p (1 : Fin 3) then true else false

theorem XIE_f1_pos (p : Fin 3 → Prop) (hp : p (1 : Fin 3)) : XIE_f1 p = true := by
  unfold XIE_f1
  split
  · rfl
  · rename_i h; exact absurd hp h

theorem XIE_f1_neg (p : Fin 3 → Prop) (hp : ¬ p (1 : Fin 3)) : XIE_f1 p = false := by
  unfold XIE_f1
  split
  · rename_i h; exact absurd h hp
  · rfl

/-- At world `1`, `f₁` is an item of `A`. -/
theorem XIE_f1_adm : XIE_U.rel XIE_A (1 : Fin 3) XIE_f1 XIE_f1 := by
  intro v hv p q hpq
  have hv' : v = (1 : Fin 3) := by
    rcases hv with h | h
    · exact h.symm
    · exact absurd h (by decide)
  subst hv'
  have e : p (1 : Fin 3) = q (1 : Fin 3) := propext (hpq (1 : Fin 3) (Or.inl rfl))
  show XIE_f1 p = XIE_f1 q
  unfold XIE_f1
  rw [e]

/-- Identity at a world, at `A`, implies equality. -/
theorem XIE_relA_eq {v : Fin 3} {x y : XIE_G} (h : XIE_U.rel XIE_A v x y) : x = y :=
  funext fun p => h v (XIE_U.Rrefl v) p p (fun _ _ => Iff.rfl)

/-- The proposition true at `1` where `p` is, and elsewhere where `q` is. -/
def XIE_mix (p q : Fin 3 → Prop) : Fin 3 → Prop := fun w => (w = 1 ∧ p w) ∨ (w ≠ 1 ∧ q w)

/-- An item of `A` at the actual world is constant. -/
theorem XIE_const_of_adm0 {x : XIE_G} (h : XIE_U.rel XIE_A XIE_U.w0 x x) (p q : Fin 3 → Prop) : x p = x q := by
  have h1 : x p = x (XIE_mix p q) := h (1 : Fin 3) (Or.inr rfl) p (XIE_mix p q) (fun u hu => by
    rcases hu with rfl | hu
    · exact ⟨fun hp => Or.inl ⟨rfl, hp⟩, fun h' => h'.elim (fun h'' => h''.2) (fun h'' => absurd rfl h''.1)⟩
    · exact absurd hu (by decide))
  have h2 : x (XIE_mix p q) = x q := h (2 : Fin 3) (Or.inr rfl) (XIE_mix p q) q (fun u hu => by
    rcases hu with rfl | hu
    · exact ⟨fun h' => h'.elim (fun h'' => absurd h''.1 (by decide)) (fun h'' => h''.2),
        fun hq => Or.inr ⟨by decide, hq⟩⟩
    · exact absurd hu (by decide))
  exact h1.trans h2

/-- The property of being constant, of items of `A`. -/
def XIE_Fc : XIE_U.El (.arr XIE_A .t) := fun (x : XIE_G) (_ : Fin 3) => ∀ p q, x p = x q

theorem XIE_Fc_adm : XIE_U.rel (.arr XIE_A .t) XIE_U.w0 XIE_Fc XIE_Fc := by
  intro v _ x y hxy
  have e : x = y := XIE_relA_eq hxy
  subst e
  exact fun _ _ => Iff.rfl

/-- Every item of `A` at the actual world is necessarily constant, but at world `1`, `f₁` is an
item of `A` which is not constant. -/
theorem XIE_not_BF : ¬ XIE_F.Valid BF := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_all _ _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp h XIE_A (Or.inr ⟨trivial, trivial⟩))
    XIE_Fc XIE_Fc_adm
  have h2 := (XIE_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIE_F.holdsAt_all _ _ _ _ _).mpr fun _ hx =>
    (XIE_F.box_of XIE_heq _ _ _ _).mpr fun _ _ => XIE_const_of_adm0 hx)
  have h3 := (XIE_F.box_of XIE_heq _ _ _ _).mp h2 (1 : Fin 3) (Or.inr rfl)
  have h4 := (XIE_F.holdsAt_all _ _ _ _ _).mp h3 XIE_f1 XIE_f1_adm
  have h5 : ∀ p q : Fin 3 → Prop, XIE_f1 p = XIE_f1 q := h4
  have h6 := h5 (fun _ => True) (fun _ => False)
  rw [XIE_f1_pos _ trivial, XIE_f1_neg _ (fun h => h)] at h6
  exact Bool.noConfusion h6

/-- The relation between a proposition and whether it is true. -/
def XIE_Rc : XIE_U.El (.arr .t (.arr .e .t)) := fun (p : Fin 3 → Prop) (y : Bool) (u : Fin 3) => (y = true ↔ p u)

theorem XIE_Rc_adm : XIE_U.rel (.arr .t (.arr .e .t)) XIE_U.w0 XIE_Rc XIE_Rc := by
  intro v _ p q hpq v' hv' y y' hyy' u hu
  have e : y = y' := hyy'
  subst e
  exact iff_congr Iff.rfl (hpq u (XIE_U.Rtrans _ _ _ hv' hu))

/-- Each proposition is related by `R` to an entity, but no item of `t → e` at the actual world
chooses one: such an item is constant. -/
theorem XIE_not_Choice : ¬ XIE_F.Valid Choice := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_all _ _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp
    ((XIE_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)) .e (Or.inr trivial)) XIE_Rc XIE_Rc_adm
  have h2 := (XIE_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIE_F.holdsAt_all _ _ _ _ _).mpr fun p _ => by
    refine (XIE_F.holdsAt_ex _ _ _ _ _).mpr ?_
    rcases Classical.em (p (0 : Fin 3)) with hp | hp
    · exact ⟨true, rfl, show (true = true ↔ p (0 : Fin 3)) from ⟨fun _ => hp, fun _ => rfl⟩⟩
    · exact ⟨false, rfl, show (false = true ↔ p (0 : Fin 3)) from ⟨fun e => Bool.noConfusion e, fun h => absurd h hp⟩⟩)
  obtain ⟨f, hf, h3⟩ := (XIE_F.holdsAt_ex _ _ _ _ _).mp h2
  have hc := XIE_const_of_adm0 hf
  have h4 : f (fun _ => True) = true ↔ True :=
    (XIE_F.holdsAt_all _ _ _ _ _).mp h3 (fun _ => True) (fun _ _ => Iff.rfl)
  have h5 : f (fun _ => False) = true ↔ False :=
    (XIE_F.holdsAt_all _ _ _ _ _).mp h3 (fun _ => False) (fun _ _ => Iff.rfl)
  exact h5.mp ((hc _ _).symm.trans (h4.mpr trivial))

/-! ### The Barcan formula for types fails -/

/-- Each type with no `u` in it has two items which are distinct at every world. -/
theorem XIE_two_items : ∀ a : Code Bool, XIE_noU a → ∃ x y : XIE_U.El a,
    (∀ w, XIE_U.rel a w x x) ∧ (∀ w, XIE_U.rel a w y y) ∧ ∀ w, ¬ XIE_U.rel a w x y
  | .e, _ => ⟨true, false, fun _ => rfl, fun _ => rfl, fun _ h => Bool.noConfusion h⟩
  | .t, _ => ⟨fun _ => True, fun _ => False, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun w h => (h w (XIE_U.Rrefl w)).mp trivial⟩
  | .base false, _ => ⟨(true : Bool), (false : Bool), fun _ => rfl, fun _ => rfl,
      fun _ h => Bool.noConfusion (h : (true : Bool) = false)⟩
  | .base true, h => nomatch (h : true = false)
  | .arr a c, ⟨_, hc⟩ => by
    obtain ⟨y1, y2, h1, h2, h12⟩ := XIE_two_items c hc
    obtain ⟨x0, hx0⟩ := XIE_U.adm_nonempty a
    refine ⟨fun _ => y1, fun _ => y2, fun _ v _ _ _ _ => h1 v, fun _ v _ _ _ _ => h2 v, fun w h => ?_⟩
    exact h12 w (h w (XIE_U.Rrefl w) x0 x0 (hx0 w))

/-- The instance of TBF which fails: `φ(α)` says that `α` has two distinct items. -/
def XIE_phi : Fm Ctx.nil.text := neg (all tv0 (all tv0 (eqv tv0 tv0 (.var (.there .here)) (.var .here))))

theorem XIE_phi_iff (a : Code Bool) (w : Fin 3) :
    XIE_F.HoldsAt XIE_phi (scons a (fun i => i.elim0)) () w ↔
      ¬ ∀ x : XIE_U.El a, XIE_U.rel a w x x → ∀ y : XIE_U.El a, XIE_U.rel a w y y → XIE_U.rel a w x y := by
  refine (XIE_F.holdsAt_neg _ _ _ _).trans (not_congr ?_)
  refine (XIE_F.holdsAt_all _ _ _ _ _).trans (forall_congr' fun x => imp_congr Iff.rfl ?_)
  refine (XIE_F.holdsAt_all _ _ _ _ _).trans (forall_congr' fun y => imp_congr Iff.rfl ?_)
  exact (XIE_F.holdsAt_eqv _ _ _ _ _ _ _).trans (XIE_heq _ _ _ _)

/-- Every type at the actual world necessarily has two distinct items; but at world `2` there is a
type, `u`, with only one. -/
theorem XIE_not_TBF : ¬ XIE_F.Valid (TBFI XIE_phi) := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have hA : XIE_F.HoldsAt (tall (boxF XIE_phi)) (fun i => i.elim0) () XIE_U.w0 := by
    refine (XIE_F.holdsAt_tall _ _ _ _).mpr fun a ha => (XIE_F.box_of XIE_heq _ _ _ _).mpr fun v _ => ?_
    have hna : XIE_noU a := ha.resolve_left (show ¬ ((0 : Fin 3) = 2) by decide)
    obtain ⟨x, y, hx, hy, hxy⟩ := XIE_two_items a hna
    exact (XIE_phi_iff a v).mpr fun h => hxy v (h x (hx v) y (hy v))
  have hB := (XIE_F.box_of XIE_heq _ _ _ _).mp ((XIE_F.holdsAt_imp _ _ _ _ _).mp h hA) (2 : Fin 3) (Or.inr rfl)
  have hd := (XIE_F.holdsAt_tall _ _ _ _).mp hB (.base true) (Or.inl rfl)
  exact (XIE_phi_iff (.base true) (2 : Fin 3)).mp hd fun _ _ _ _ => rfl

theorem XIE_not_TBFSch : ¬ ∀ χ, TBFSch χ → XIE_F.Valid χ := fun h => XIE_not_TBF (h _ ⟨XIE_phi, rfl⟩)

/-! ## Principles about `≈` -/

theorem XIE_N_td : XIE_N (.arr .t (.base false)) = XIE_N (.arr .t .e) := by decide

/-- At the actual world, `t → d` and `t → e` are identical. -/
theorem XIE_teq_td : XIE_F.teq (.arr .t (.base false)) (.arr .t .e) XIE_U.w0 := ⟨fun _ => XIE_N_td, rfl⟩

/-- `(t → d) ≈ (t → e)` and `t ≈ t`, but not `d ≈ e`. -/
theorem XIE_not_Recovery : ¬ XIE_F.Valid Recovery := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_tall _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp
    ((XIE_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)) .t (Or.inr trivial)) (.base false) (Or.inr rfl))
    .e (Or.inr trivial)
  have h2 := (XIE_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIE_F.holdsAt_conj _ _ _ _ _).mpr
    ⟨(XIE_F.holdsAt_teq _ _ _ _ _).mpr XIE_teq_td, (XIE_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => rfl, rfl⟩⟩)
  exact XIE_N_ed (((XIE_F.holdsAt_teq _ _ _ _ _).mp h2).1 (show (0 : Fin 3) ≠ 1 by decide)).symm

/-- `(t → d) ≈ (t → e)`, but not `d ≈ e`. -/
theorem XIE_not_Inj : ¬ XIE_F.Valid Inj := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_tall _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp
    ((XIE_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)) .t (Or.inr trivial)) (.base false) (Or.inr rfl))
    .e (Or.inr trivial)
  have h2 := (XIE_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIE_F.holdsAt_teq _ _ _ _ _).mpr XIE_teq_td)
  have h3 := ((XIE_F.holdsAt_conj _ _ _ _ _).mp h2).2
  exact XIE_N_ed (((XIE_F.holdsAt_teq _ _ _ _ _).mp h3).1 (show (0 : Fin 3) ≠ 1 by decide)).symm

/-! ## Principles about identity across types -/

theorem XIE_tw_N {a b : Code Bool} {w : Fin 3} {x : XIE_U.El a} {y : XIE_U.El b} (h : XIE_tw a b w x y) :
    XIE_N a ≠ XIE_N b := by
  obtain ⟨hab, _⟩ := XIE_tw_cases h
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact XIE_N_ed
  · exact fun e => XIE_N_ed e.symm

/-- At the actual world, an item is identified with an item of a type which agrees with its own once
`t → d` is replaced by `t → e`, or else it is an entity or an item of `d`. -/
theorem XIE_eqv0 {a b : Code Bool} {x : XIE_U.El a} {y : XIE_U.El b} (h : XIE_eqv a b x y 0) :
    XIE_N a = XIE_N b ∨ ((a = .e ∧ b = .base false) ∨ (a = .base false ∧ b = .e)) := by
  rcases h with ⟨h1, _, _⟩ | h
  · exact Or.inl (h1 (by decide))
  · exact Or.inr (XIE_tw_cases h).1

/-- No entity is identified with a property. -/
theorem XIE_Slogan : XIE_F.Valid Slogan := by
  refine XIE_Valid_of ?_
  refine (XIE_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XIE_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XIE_F.holdsAt_all _ _ _ _ _).mpr fun y _ => (XIE_F.holdsAt_neg _ _ _ _).mpr fun hxy => ?_
  rcases XIE_eqv0 ((XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mp hxy) with h | h
  · exact nomatch XIE_N_e h.symm
  · rcases h with ⟨_, h⟩ | ⟨h, _⟩
    · exact nomatch h
    · exact nomatch h

/-- `⊤` is identified with nothing of another type. -/
theorem XIE_not_Twin : ¬ XIE_F.Valid Twin := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_all _ _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial))
    (fun _ => True) (fun _ _ => Iff.rfl)
  obtain ⟨b, _, h2⟩ := (XIE_F.holdsAt_tex _ _ _ _).mp h1
  have h3 := (XIE_F.holdsAt_conj _ _ _ _ _).mp h2
  obtain ⟨y, _, h4⟩ := (XIE_F.holdsAt_ex _ _ _ _ _).mp h3.2
  rcases XIE_eqv0 ((XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mp h4) with h5 | h5
  · have e := XIE_N_t h5.symm
    subst e
    exact (XIE_F.holdsAt_neg _ _ _ _).mp h3.1 ((XIE_F.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => rfl, rfl⟩)
  · rcases h5 with ⟨h6, _⟩ | ⟨h6, _⟩
    · exact nomatch h6
    · exact nomatch h6

/-- No entity is identified with its haecceity. -/
theorem XIE_not_Hae : ¬ XIE_F.Valid Hae := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_all _ _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) true rfl
  rcases XIE_eqv0 ((XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mp h1) with h2 | h2
  · exact nomatch XIE_N_e h2.symm
  · rcases h2 with ⟨_, h3⟩ | ⟨h3, _⟩
    · exact nomatch h3
    · exact nomatch h3

theorem XIE_N_ee_ed : XIE_N (.arr .e .e) ≠ XIE_N (.arr .e (.base false)) := by decide

/-- The identity functions `e → e` and `e → d` agree pointwise up to identity, but are not
identified. -/
theorem XIE_not_PExt : ¬ XIE_F.Valid PExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_tall _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp
    ((XIE_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) .e (Or.inr trivial)) (.base false) (Or.inr rfl)
  have hf : XIE_U.rel (.arr .e .e) XIE_U.w0 (fun x => x) (fun x => x) := fun _ _ _ _ h => h
  have hg : XIE_U.rel (.arr .e (.base false)) XIE_U.w0 (fun (x : Bool) => x) (fun (x : Bool) => x) :=
    fun _ _ _ _ h => h
  have h2 := (XIE_F.holdsAt_all _ _ _ _ _).mp ((XIE_F.holdsAt_all _ _ _ _ _).mp h1 _ hf) _ hg
  have h3 := (XIE_F.holdsAt_imp _ _ _ _ _).mp h2 ((XIE_F.holdsAt_all _ _ _ _ _).mpr fun _ _ =>
    (XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  rcases XIE_eqv0 ((XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mp h3) with h4 | h4
  · exact XIE_N_ee_ed h4
  · rcases h4 with ⟨h5, _⟩ | ⟨h5, _⟩
    · exact nomatch h5
    · exact nomatch h5

/-! ### Congruence holds at the actual world -/

theorem XIE_arrN_inj {A B C D : Code Bool} (h : XIE_arrN A C = XIE_arrN B D) :
    A = B ∧ (C = D ∨ (C = .base false ∧ D = .e) ∨ (C = .e ∧ D = .base false)) := by
  unfold XIE_arrN at h
  split at h <;> split at h
  · rename_i h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨rfl, Or.inl rfl⟩
  · rename_i h1 _
    obtain ⟨rfl, rfl⟩ := h1
    injection h with e1 e2
    subst e1; subst e2
    exact ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · rename_i _ h2
    obtain ⟨rfl, rfl⟩ := h2
    injection h with e1 e2
    subst e1; subst e2
    exact ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  · injection h with e1 e2
    exact ⟨e1, Or.inl e2⟩

/-- At the actual world, identified functions take identified values at identified arguments. -/
theorem XIE_cong0 {a b c d : Code Bool} {f : XIE_U.El (.arr a c)} {g : XIE_U.El (.arr b d)} {x : XIE_U.El a}
    {y : XIE_U.El b} (h1 : XIE_eqv (.arr a c) (.arr b d) f g 0) (h2 : XIE_eqv a b x y 0) :
    XIE_eqv c d (f x) (g y) 0 := by
  rcases h1 with ⟨n1, i1, c1⟩ | t1
  · have n1' : XIE_arrN (XIE_N a) (XIE_N c) = XIE_arrN (XIE_N b) (XIE_N d) := n1 (by decide)
    obtain ⟨hab, hcd⟩ := XIE_arrN_inj n1'
    have cxy : XIE_CR a b 0 x y := by
      rcases h2 with ⟨_, _, h⟩ | t2
      · exact h
      · exact absurd hab (XIE_tw_N t2)
    have hv := c1 (0 : Fin 3) (XIE_U.Rrefl _) x y cxy
    injection i1 with _ ic
    rcases hcd with hcd | ⟨hc, hd⟩ | ⟨hc, hd⟩
    · exact Or.inl ⟨fun _ => hcd, ic, hv⟩
    · have ec := XIE_N_d hc; have ed := XIE_N_e hd
      subst ec; subst ed
      exact Or.inr (Or.inl ⟨rfl, hv⟩)
    · have ec := XIE_N_e hc; have ed := XIE_N_d hd
      subst ec; subst ed
      exact Or.inr (Or.inl ⟨rfl, hv⟩)
  · obtain ⟨hab, _⟩ := XIE_tw_cases t1
    rcases hab with ⟨h3, _⟩ | ⟨h3, _⟩
    · exact nomatch h3
    · exact nomatch h3

theorem XIE_Cong : XIE_F.Valid Cong := by
  refine XIE_Valid_of ?_
  refine (XIE_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XIE_F.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (XIE_F.holdsAt_tall _ _ _ _).mpr fun c _ => (XIE_F.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (XIE_F.holdsAt_all _ _ _ _ _).mpr fun f _ => (XIE_F.holdsAt_all _ _ _ _ _).mpr fun g _ =>
    (XIE_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XIE_F.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (XIE_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hc := (XIE_F.holdsAt_conj _ _ _ _ _).mp h
  have h1 := (XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mp hc.1
  have h2 := (XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mp hc.2
  exact (XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XIE_cong0 (a := a) (b := b) (c := c) (d := d) h1 h2)

theorem XIE_PCong : XIE_F.Valid PCong := by
  refine XIE_Valid_of ?_
  refine (XIE_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XIE_F.holdsAt_tall _ _ _ _).mpr fun c _ =>
    (XIE_F.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (XIE_F.holdsAt_all _ _ _ _ _).mpr fun f _ => (XIE_F.holdsAt_all _ _ _ _ _).mpr fun g _ =>
    (XIE_F.holdsAt_all _ _ _ _ _).mpr fun x hx => ?_
  refine (XIE_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have h1 := (XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mp h
  exact (XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XIE_cong0 (a := a) (b := a) (c := c) (d := d) h1 ((XIE_heq' a x x 0).mpr hx))

/-! ### LL≡-Poly fails; LL≡/≈ holds -/

set_option maxHeartbeats 4000000 in
theorem XIE_PredE_iff1 (a b : Code Bool) (x : XIE_U.El a) (y : XIE_U.El b) :
    XIE_F.HoldsAt (.app (.tapp ((PredE.twk.twk.wk tv1).wk tv0) tv1) (.var (.there .here)))
      (scons b (scons a (fun i => i.elim0))) (((), x), y) XIE_U.w0 ↔ XIE_F.teq a .e XIE_U.w0 := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem XIE_PredE_iff0 (a b : Code Bool) (x : XIE_U.El a) (y : XIE_U.El b) :
    XIE_F.HoldsAt (.app (.tapp ((PredE.twk.twk.wk tv1).wk tv0) tv0) (.var .here))
      (scons b (scons a (fun i => i.elim0))) (((), x), y) XIE_U.w0 ↔ XIE_F.teq b .e XIE_U.w0 := Iff.rfl

/-- With `P := λγ.λz.(γ ≈ e)`, the entity `true` and the item `true` of `d` are identified, but only
the first has `P`. -/
theorem XIE_not_LLPoly : ¬ XIE_F.Valid (LLPoly PredE) := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIE_F.holdsAt_tall _ _ _ _).mp ((XIE_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base false) (Or.inr rfl)
  have h2 := (XIE_F.holdsAt_all _ _ _ _ _).mp ((XIE_F.holdsAt_all _ _ _ _ _).mp h1 true rfl) true rfl
  have h3 := (XIE_F.holdsAt_imp _ _ _ _ _).mp h2
    ((XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  have h4 := (XIE_F.holdsAt_imp _ _ _ _ _).mp h3 ((XIE_PredE_iff1 _ _ _ _).mpr ⟨fun _ => rfl, rfl⟩)
  exact XIE_N_ed (((XIE_PredE_iff0 _ _ _ _).mp h4).1 (show (0 : Fin 3) ≠ 1 by decide)).symm

/-- The predicate of a polymorphic Leibniz law, at its two types. -/
theorem XIE_evalP {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XIE_U.TEnv n)
    (env : XIE_U.Env Γ ρ) (a b : Code Bool) (x : XIE_U.El a) (y : XIE_U.El b) :
    HEq (XIE_F.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y)) (XIE_F.eval P ρ env) := by
  have e1 : XIE_F.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y) =
      XIE_F.eval (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) :=
    XIE_F.eval_wk tv0 (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) y
  have e2 : XIE_F.eval (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) =
      XIE_F.eval P.twk.twk (scons b (scons a ρ)) env := XIE_F.eval_wk tv1 P.twk.twk (scons b (scons a ρ)) env x
  exact (heq_of_eq (e1.trans e2)).trans ((XIE_F.eval_twk P.twk b (scons a ρ) env).trans (XIE_F.eval_twk P a ρ env))

theorem XIE_evalP1 {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XIE_U.TEnv n)
    (env : XIE_U.Env Γ ρ) (a b : Code Bool) (x : XIE_U.El a) (y : XIE_U.El b) :
    XIE_F.HoldsAt (.app (.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (.var (.there .here))) (scons b (scons a ρ))
      ((env, x), y) XIE_U.w0 ↔ XIE_F.eval P ρ env a x XIE_U.w0 := by
  have h1 : HEq (XIE_F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (scons b (scons a ρ)) ((env, x), y))
      (XIE_F.eval P ρ env a) :=
    (XIE_F.heq_eval_tapp ((P.twk.twk.wk tv1).wk tv0) tv1 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => XIE_U.El c → Fin 3 → Prop) (Q := fun c => XIE_U.El c → Fin 3 → Prop)
        (fun _ => rfl) (XIE_evalP P ρ env a b x y) rfl)
  have e := congrFun (congrFun (eq_of_heq h1) x) XIE_U.w0
  exact Iff.of_eq e

theorem XIE_evalP0 {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XIE_U.TEnv n)
    (env : XIE_U.Env Γ ρ) (a b : Code Bool) (x : XIE_U.El a) (y : XIE_U.El b) :
    XIE_F.HoldsAt (.app (.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (.var .here)) (scons b (scons a ρ))
      ((env, x), y) XIE_U.w0 ↔ XIE_F.eval P ρ env b y XIE_U.w0 := by
  have h1 : HEq (XIE_F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (scons b (scons a ρ)) ((env, x), y))
      (XIE_F.eval P ρ env b) :=
    (XIE_F.heq_eval_tapp ((P.twk.twk.wk tv1).wk tv0) tv0 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => XIE_U.El c → Fin 3 → Prop) (Q := fun c => XIE_U.El c → Fin 3 → Prop)
        (fun _ => rfl) (XIE_evalP P ρ env a b x y) rfl)
  have e := congrFun (congrFun (eq_of_heq h1) y) XIE_U.w0
  exact Iff.of_eq e

/-- LL≡/≈ holds, for every polymorphic predicate, with parameters: items identified at the actual
world, of types identical there, correspond, and correspondence is admissible. -/
theorem XIE_Bridge {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : XIE_F.Valid (Bridge P) := by
  intro ρ _ env henv
  refine (XIE_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XIE_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XIE_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XIE_F.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (XIE_F.holdsAt_imp _ _ _ _ _).mpr fun h => (XIE_F.holdsAt_imp _ _ _ _ _).mpr fun hPx => ?_
  obtain ⟨h1, h2⟩ := (XIE_F.holdsAt_conj _ _ _ _ _).mp h
  obtain ⟨hN, hI⟩ := (XIE_F.holdsAt_teq _ _ _ _ _).mp h2
  have hN' : XIE_N a = XIE_N b := hN (show (0 : Fin 3) ≠ 1 by decide)
  have hxy : XIE_CR a b XIE_U.w0 x y := by
    rcases (XIE_F.holdsAt_eqv _ _ _ _ _ _ _).mp h1 with ⟨_, _, h⟩ | t
    · exact h
    · exact absurd hN' (XIE_tw_N t)
  have hrel := XIE_Inv.fundamental P ρ ρ (XIE_F.homRs ρ) XIE_U.w0 (fun i => XIE_Inv.refl XIE_U.w0 (ρ i)) env env
    (KInv.EnvRel_indep XIE_F.hom XIE_Inv Γ ρ ρ _ XIE_U.w0 env env henv) XIE_U.w0 (XIE_U.Rrefl _) a b
    (XIE_CR a b) ⟨hI, fun _ _ _ => hN', fun _ _ _ => Iff.rfl⟩ XIE_U.w0 (XIE_U.Rrefl _) x y hxy
    XIE_U.w0 (XIE_U.Rrefl _)
  exact (XIE_evalP0 P ρ env a b x y).mpr (hrel.mp ((XIE_evalP1 P ρ env a b x y).mp hPx))

end Kr
end PIF
