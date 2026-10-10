import PIKripkeModels

/-!
# A Kripke model of PI + Classicism without Necessity of Distinctness for types

`𝔐_k,nd`: two worlds; the actual world sees both, and the other sees only itself. There is a base
type `d` with two items, a copy of `e`. At the actual world, `≈` is identity of types and items are
identified only within a type. At the other world, `d` is identified with `e` (and every type
built from `d` with the corresponding type built from `e`), and each item with its copy. So
`¬(e ≈ d)` is true, but not necessarily true.
-/
set_option autoImplicit false

namespace PIF
namespace Kr

def UND : Univ where
  W := Bool
  w0 := true
  R := fun w v => w = true ∨ v = false
  Rrefl := fun w => by cases w <;> simp
  Rtrans := by
    intro u v w h1 h2
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · rcases h2 with h2 | h2
      · exact absurd (h1.symm.trans h2) Bool.false_ne_true
      · exact Or.inr h2
  E := Bool
  Base := Unit
  B := fun _ => Bool
  neE := ⟨true⟩
  neB := fun _ => ⟨true⟩
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
  D := fun _ _ => True
  D_e := fun _ => trivial
  D_t := fun _ => trivial
  D_arr := fun _ _ _ _ _ => trivial
  D_mono := fun _ _ _ _ _ => trivial

/-- The type got by putting `e` for `d`. -/
def img : Code Unit → Code Unit
  | .base _ => .e
  | .arr a c => .arr (img a) (img c)
  | .e => .e
  | .t => .t

/-- Identity at a world between items of types with the same image. -/
def CR : (a b : Code Unit) → Bool → UND.El a → UND.El b → Prop
  | .e, .e => fun _ x y => x = y
  | .e, .base _ => fun _ x y => x = y
  | .base _, .e => fun _ x y => x = y
  | .base _, .base _ => fun _ x y => x = y
  | .t, .t => fun w p q => ∀ v, UND.R w v → (p v ↔ q v)
  | .arr a c, .arr b d => fun w f g => ∀ v, UND.R w v → ∀ x y, CR a b v x y → CR c d v (f x) (g y)
  | _, _ => fun _ _ _ => False

/-- Transport, both ways, between types with the same image. -/
noncomputable def Tr : (a b : Code Unit) → (UND.El a → UND.El b) × (UND.El b → UND.El a)
  | .e, .e => (fun x => x, fun x => x)
  | .e, .base _ => (fun x => x, fun x => x)
  | .base _, .e => (fun x => x, fun x => x)
  | .base _, .base _ => (fun x => x, fun x => x)
  | .t, .t => (fun p => p, fun p => p)
  | .arr a c, .arr b d => (fun f y => (Tr c d).1 (f ((Tr a b).2 y)), fun g x => (Tr c d).2 (g ((Tr a b).1 x)))
  | a, b => (fun _ => Classical.choose (UND.adm_nonempty b), fun _ => Classical.choose (UND.adm_nonempty a))

noncomputable abbrev Tf (a b : Code Unit) : UND.El a → UND.El b := (Tr a b).1
noncomputable abbrev Tg (a b : Code Unit) : UND.El b → UND.El a := (Tr a b).2

theorem CR_diag : ∀ (a : Code Unit) (w : Bool) (x y : UND.El a), UND.rel a w x y ↔ CR a a w x y
  | .e, _, _, _ => Iff.rfl
  | .t, _, _, _ => Iff.rfl
  | .base _, _, _, _ => Iff.rfl
  | .arr a c, _, _, _ => forall_congr' fun v => imp_congr Iff.rfl (forall_congr' fun x => forall_congr' fun y =>
      imp_congr (CR_diag a v x y) (CR_diag c v _ _))

theorem CR_mono : ∀ (a b : Code Unit) (w v : Bool) (x : UND.El a) (y : UND.El b), UND.R w v → CR a b w x y → CR a b v x y
  | .e, .e, _, _, _, _, _, h => h
  | .e, .base _, _, _, _, _, _, h => h
  | .base _, .e, _, _, _, _, _, h => h
  | .base _, .base _, _, _, _, _, _, h => h
  | .t, .t, _, _, _, _, hv, h => fun u hu => h u (UND.Rtrans _ _ _ hv hu)
  | .arr _ _, .arr _ _, _, _, _, _, hv, h => fun u hu => h u (UND.Rtrans _ _ _ hv hu)
  | .e, .t, _, _, _, _, _, h => h.elim
  | .e, .arr _ _, _, _, _, _, _, h => h.elim
  | .t, .e, _, _, _, _, _, h => h.elim
  | .t, .base _, _, _, _, _, _, h => h.elim
  | .t, .arr _ _, _, _, _, _, _, h => h.elim
  | .base _, .t, _, _, _, _, _, h => h.elim
  | .base _, .arr _ _, _, _, _, _, _, h => h.elim
  | .arr _ _, .e, _, _, _, _, _, h => h.elim
  | .arr _ _, .t, _, _, _, _, _, h => h.elim
  | .arr _ _, .base _, _, _, _, _, _, h => h.elim

theorem img_e {a : Code Unit} (h : img a = .e) : a = .e ∨ ∃ u, a = .base u := by
  cases a with
  | e => exact Or.inl rfl
  | base u => exact Or.inr ⟨u, rfl⟩
  | t => exact nomatch h
  | arr _ _ => exact nomatch h

theorem img_t {a : Code Unit} (h : img a = .t) : a = .t := by
  cases a with
  | t => rfl
  | e => exact nomatch h
  | base _ => exact nomatch h
  | arr _ _ => exact nomatch h

theorem img_arr {a k1 k2 : Code Unit} (h : img a = .arr k1 k2) : ∃ a1 a2, a = .arr a1 a2 ∧ img a1 = k1 ∧ img a2 = k2 := by
  cases a with
  | arr a1 a2 => injection h with h1 h2; exact ⟨a1, a2, rfl, h1, h2⟩
  | e => exact nomatch h
  | t => exact nomatch h
  | base _ => exact nomatch h

theorem img_ne_base {a : Code Unit} {u : Unit} (h : img a = .base u) : False := by
  cases a with
  | arr _ _ => exact nomatch h
  | e => exact nomatch h
  | t => exact nomatch h
  | base _ => exact nomatch h

set_option maxHeartbeats 2000000 in
/-- Identity between types of one shape is symmetric and transitive, and transport takes each item
to one identified with it. -/
theorem shape : ∀ k : Code Unit,
    (∀ a b, img a = k → img b = k → ∀ w x y, CR a b w x y → CR b a w y x) ∧
    (∀ a b c, img a = k → img b = k → img c = k → ∀ w x y z, CR a b w x y → CR b c w y z → CR a c w x z) ∧
    (∀ a b, img a = k → img b = k → ∀ w x, CR a a w x x → CR a b w x (Tf a b x) ∧ CR b b w (Tf a b x) (Tf a b x)) ∧
    (∀ a b, img a = k → img b = k → ∀ w y, CR b b w y y → CR a b w (Tg a b y) y ∧ CR a a w (Tg a b y) (Tg a b y)) := by
  intro k
  induction k with
  | e =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b ha hb w x y h
      rcases img_e ha with rfl | ⟨u, rfl⟩ <;> rcases img_e hb with rfl | ⟨u', rfl⟩ <;> exact Eq.symm h
    · intro a b c ha hb hc w x y z h1 h2
      rcases img_e ha with rfl | ⟨u, rfl⟩ <;> rcases img_e hb with rfl | ⟨u', rfl⟩ <;>
        rcases img_e hc with rfl | ⟨u'', rfl⟩ <;> exact Eq.trans h1 h2
    · intro a b ha hb w x _
      rcases img_e ha with rfl | ⟨u, rfl⟩ <;> rcases img_e hb with rfl | ⟨u', rfl⟩ <;> exact ⟨rfl, rfl⟩
    · intro a b ha hb w x _
      rcases img_e ha with rfl | ⟨u, rfl⟩ <;> rcases img_e hb with rfl | ⟨u', rfl⟩ <;> exact ⟨rfl, rfl⟩
  | t =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b ha hb w x y h
      have e1 := img_t ha; have e2 := img_t hb; subst e1; subst e2
      exact fun v hv => (h v hv).symm
    · intro a b c ha hb hc w x y z h1 h2
      have e1 := img_t ha; have e2 := img_t hb; have e3 := img_t hc; subst e1; subst e2; subst e3
      exact fun v hv => (h1 v hv).trans (h2 v hv)
    · intro a b ha hb w x hx
      have e1 := img_t ha; have e2 := img_t hb; subst e1; subst e2
      exact ⟨hx, hx⟩
    · intro a b ha hb w x hx
      have e1 := img_t ha; have e2 := img_t hb; subst e1; subst e2
      exact ⟨hx, hx⟩
  | base u => exact ⟨fun a _ ha => (img_ne_base ha).elim, fun a _ _ ha => (img_ne_base ha).elim,
      fun a _ ha => (img_ne_base ha).elim, fun a _ ha => (img_ne_base ha).elim⟩
  | arr k1 k2 ih1 ih2 =>
    obtain ⟨S1, R1, P1, Q1⟩ := ih1
    obtain ⟨S2, R2, P2, Q2⟩ := ih2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b ha hb w f g h
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := img_arr hb
      intro v hv x y hxy
      exact S2 a2 b2 ha2 hb2 v _ _ (h v hv y x (S1 b1 a1 hb1 ha1 v x y hxy))
    · intro a b c ha hb hc w f g h hfg hgh
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := img_arr hb
      obtain ⟨c1, c2, rfl, hc1, hc2⟩ := img_arr hc
      intro v hv x z hxz
      have hzz : CR c1 c1 v z z := R1 c1 a1 c1 hc1 ha1 hc1 v z x z (S1 a1 c1 ha1 hc1 v x z hxz) hxz
      obtain ⟨hyz, _⟩ := Q1 b1 c1 hb1 hc1 v z hzz
      have hxy : CR a1 b1 v x (Tg b1 c1 z) := R1 a1 c1 b1 ha1 hc1 hb1 v x z _ hxz (S1 b1 c1 hb1 hc1 v _ z hyz)
      exact R2 a2 b2 c2 ha2 hb2 hc2 v _ _ _ (hfg v hv x _ hxy) (hgh v hv _ z hyz)
    · intro a b ha hb w f hf
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := img_arr hb
      refine ⟨?_, ?_⟩
      · intro v hv x y hxy
        have hyy : CR b1 b1 v y y := R1 b1 a1 b1 hb1 ha1 hb1 v y x y (S1 a1 b1 ha1 hb1 v x y hxy) hxy
        obtain ⟨hTy, hTT⟩ := Q1 a1 b1 ha1 hb1 v y hyy
        have hxT : CR a1 a1 v x (Tg a1 b1 y) := R1 a1 b1 a1 ha1 hb1 ha1 v x y _ hxy (S1 a1 b1 ha1 hb1 v _ y hTy)
        have hfx := hf v hv x _ hxT
        obtain ⟨h1, _⟩ := P2 a2 b2 ha2 hb2 v _ (hf v hv _ _ hTT)
        exact R2 a2 a2 b2 ha2 ha2 hb2 v _ _ _ hfx h1
      · intro v hv y y' hyy'
        have hyy : CR b1 b1 v y y := R1 b1 b1 b1 hb1 hb1 hb1 v y y' y hyy' (S1 b1 b1 hb1 hb1 v y y' hyy')
        have hy'y' : CR b1 b1 v y' y' := R1 b1 b1 b1 hb1 hb1 hb1 v y' y y' (S1 b1 b1 hb1 hb1 v y y' hyy') hyy'
        obtain ⟨hTy, hTT⟩ := Q1 a1 b1 ha1 hb1 v y hyy
        obtain ⟨hTy', hT'T'⟩ := Q1 a1 b1 ha1 hb1 v y' hy'y'
        have hTyy : CR a1 a1 v (Tg a1 b1 y) (Tg a1 b1 y') :=
          R1 a1 b1 a1 ha1 hb1 ha1 v _ y _ hTy (R1 b1 b1 a1 hb1 hb1 ha1 v y y' _ hyy' (S1 a1 b1 ha1 hb1 v _ y' hTy'))
        obtain ⟨g1, _⟩ := P2 a2 b2 ha2 hb2 v _ (hf v hv _ _ hTT)
        obtain ⟨g2, _⟩ := P2 a2 b2 ha2 hb2 v _ (hf v hv _ _ hT'T')
        exact R2 b2 a2 b2 hb2 ha2 hb2 v _ _ _ (S2 a2 b2 ha2 hb2 v _ _ g1)
          (R2 a2 a2 b2 ha2 ha2 hb2 v _ _ _ (hf v hv _ _ hTyy) g2)
    · intro a b ha hb w g hg
      obtain ⟨a1, a2, rfl, ha1, ha2⟩ := img_arr ha
      obtain ⟨b1, b2, rfl, hb1, hb2⟩ := img_arr hb
      refine ⟨?_, ?_⟩
      · intro v hv x y hxy
        have hxx : CR a1 a1 v x x := R1 a1 b1 a1 ha1 hb1 ha1 v x y x hxy (S1 a1 b1 ha1 hb1 v x y hxy)
        obtain ⟨hxT, hTT⟩ := P1 a1 b1 ha1 hb1 v x hxx
        have hTy : CR b1 b1 v (Tf a1 b1 x) y := R1 b1 a1 b1 hb1 ha1 hb1 v _ x y (S1 a1 b1 ha1 hb1 v x _ hxT) hxy
        have hgy := hg v hv _ y hTy
        obtain ⟨h1, _⟩ := Q2 a2 b2 ha2 hb2 v _ (hg v hv _ _ hTT)
        exact R2 a2 b2 b2 ha2 hb2 hb2 v _ _ _ h1 hgy
      · intro v hv x x' hxx'
        have hxx : CR a1 a1 v x x := R1 a1 a1 a1 ha1 ha1 ha1 v x x' x hxx' (S1 a1 a1 ha1 ha1 v x x' hxx')
        have hx'x' : CR a1 a1 v x' x' := R1 a1 a1 a1 ha1 ha1 ha1 v x' x x' (S1 a1 a1 ha1 ha1 v x x' hxx') hxx'
        obtain ⟨hxT, hTT⟩ := P1 a1 b1 ha1 hb1 v x hxx
        obtain ⟨hx'T, hT'T'⟩ := P1 a1 b1 ha1 hb1 v x' hx'x'
        have hTxx : CR b1 b1 v (Tf a1 b1 x) (Tf a1 b1 x') :=
          R1 b1 a1 b1 hb1 ha1 hb1 v _ x _ (S1 a1 b1 ha1 hb1 v x _ hxT) (R1 a1 a1 b1 ha1 ha1 hb1 v x x' _ hxx' hx'T)
        obtain ⟨g1, _⟩ := Q2 a2 b2 ha2 hb2 v _ (hg v hv _ _ hTT)
        obtain ⟨g2, _⟩ := Q2 a2 b2 ha2 hb2 v _ (hg v hv _ _ hT'T')
        exact R2 a2 b2 a2 ha2 hb2 ha2 v _ _ _ g1
          (R2 b2 b2 a2 hb2 hb2 ha2 v _ _ _ (hg v hv _ _ hTxx) (S2 a2 b2 ha2 hb2 v _ _ g2))

end Kr
end PIF
