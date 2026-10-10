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

theorem CR_symm {a b : Code Unit} (h : img a = img b) {w : Bool} {x : UND.El a} {y : UND.El b}
    (hxy : CR a b w x y) : CR b a w y x := (shape (img a)).1 a b rfl h.symm w x y hxy

theorem CR_trans {a b c : Code Unit} (h1 : img a = img b) (h2 : img b = img c) {w : Bool} {x : UND.El a}
    {y : UND.El b} {z : UND.El c} (hxy : CR a b w x y) (hyz : CR b c w y z) : CR a c w x z :=
  (shape (img a)).2.1 a b c rfl h1.symm (h1.trans h2).symm w x y z hxy hyz

/-- Identity at a world in `𝔐_k,nd`. -/
def eqvND (a b : Code Unit) (x : UND.El a) (y : UND.El b) (w : Bool) : Prop :=
  (w = true → a = b) ∧ img a = img b ∧ CR a b w x y

theorem eqvND_iff {a a' b b' : Code Unit} {u : Bool} {x : UND.El a} {x' : UND.El a'} {y : UND.El b} {y' : UND.El b'}
    (ia : img a = img a') (ib : img b = img b') (ca : u = true → a = a') (cb : u = true → b = b')
    (hx : CR a a' u x x') (hy : CR b b' u y y') : eqvND a b x y u ↔ eqvND a' b' x' y' u := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun hu => (ca hu).symm.trans ((h1 hu).trans (cb hu)), ia.symm.trans (h2.trans ib), ?_⟩
    exact CR_trans (ia.symm.trans h2) ib (CR_trans ia.symm h2 (CR_symm ia hx) h3) hy
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun hu => (ca hu).trans ((h1 hu).trans (cb hu).symm), ia.trans (h2.trans ib.symm), ?_⟩
    exact CR_trans ia (h2.trans ib.symm) hx (CR_trans h2 ib.symm h3 (CR_symm ib hy))

def MndK : Frame where
  U := UND
  eqv := eqvND
  teq := fun a b w => (w = true → a = b) ∧ img a = img b
  eqv_resp := fun u a b x x' y y' hx hy => eqvND_iff rfl rfl (fun _ => rfl) (fun _ => rfl)
    ((CR_diag a u x x').mp hx) ((CR_diag b u y y').mp hy)

theorem MndK_heq : ∀ a x y w, MndK.eqv a a x y w ↔ MndK.U.rel a w x y := fun a x y w =>
  ⟨fun h => (CR_diag a w x y).mpr h.2.2, fun h => ⟨fun _ => rfl, rfl, (CR_diag a w x y).mp h⟩⟩

theorem R_true {w v : Bool} (h : UND.R w v) (hv : v = true) : w = true := by
  rcases h with h | h
  · exact h
  · subst hv; exact Bool.noConfusion h

/-- The admissible relations of `𝔐_k,nd`: identity between types of one shape, at the worlds at which
the two types are not told apart. -/
def ndInv : KInv MndK where
  Adm := fun w a a' S => img a = img a' ∧ (∀ v, UND.R w v → v = true → a = a') ∧ ∀ u x y, S u x y ↔ CR a a' u x y
  amono := fun ⟨h1, h2, h3⟩ hv => ⟨h1, fun u hu => h2 u (UND.Rtrans _ _ _ hv hu), h3⟩
  smono := fun ⟨_, _, h3⟩ u u' x x' _ hu h => (h3 u' x x').mpr (CR_mono _ _ u u' x x' hu ((h3 u x x').mp h))
  refl := fun _ a => ⟨rfl, fun _ _ _ => rfl, fun u x y => CR_diag a u x y⟩
  arrow := by
    intro w a a' c c' S T hS hT
    obtain ⟨h1, h2, h3⟩ := hS
    obtain ⟨k1, k2, k3⟩ := hT
    refine ⟨by show Code.arr (img a) (img c) = Code.arr (img a') (img c'); rw [h1, k1],
      fun v hv hv' => by rw [h2 v hv hv', k2 v hv hv'], fun u f f' => ?_⟩
    exact forall_congr' fun v => imp_congr Iff.rfl (forall_congr' fun x => forall_congr' fun x' =>
      imp_congr (h3 v x x') (k3 v _ _))
  total := by
    intro w a a' S hS u _ x hx
    obtain ⟨h1, _, h3⟩ := hS
    obtain ⟨hxT, hTT⟩ := (shape (img a)).2.2.1 a a' rfl h1.symm u x ((CR_diag a u x x).mp hx)
    exact ⟨Tf a a' x, (CR_diag a' u _ _).mpr hTT, (h3 u x _).mpr hxT⟩
  onto := by
    intro w a a' S hS u _ y hy
    obtain ⟨h1, _, h3⟩ := hS
    obtain ⟨hTy, hTT⟩ := (shape (img a)).2.2.2 a a' rfl h1.symm u y ((CR_diag a' u y y).mp hy)
    exact ⟨Tg a a' y, (CR_diag a u _ _).mpr hTT, (h3 u _ y).mpr hTy⟩
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
    exact eqvND_iff h1 k1 (h2 u hu) (k2 u hu) ((h3 u x x').mp hx) ((k3 u y y').mp hy)

theorem MndK_isModelAt : MndK.IsModelAt where
  refEqv := by
    intro w ρ _ env _
    refine MndK.holdsAt_tall _ _ _ w |>.mpr fun a _ => (MndK.holdsAt_all _ _ _ _ w).mpr fun x hx => ?_
    exact (MndK.holdsAt_eqv _ _ _ _ _ _ w).mpr ((MndK_heq _ _ _ w).mpr hx)
  symEqv := by
    intro w ρ _ env _
    refine MndK.holdsAt_tall _ _ _ w |>.mpr fun a _ => MndK.holdsAt_tall _ _ _ w |>.mpr fun b _ => ?_
    refine (MndK.holdsAt_all _ _ _ _ w).mpr fun x _ => (MndK.holdsAt_all _ _ _ _ w).mpr fun y _ => ?_
    refine (MndK.holdsAt_imp _ _ _ _ w).mpr fun h => ?_
    obtain ⟨h1, h2, h3⟩ := (MndK.holdsAt_eqv _ _ _ _ _ _ w).mp h
    exact (MndK.holdsAt_eqv _ _ _ _ _ _ w).mpr ⟨fun hw => (h1 hw).symm, h2.symm, CR_symm h2 h3⟩
  transEqv := by
    intro w ρ _ env _
    refine MndK.holdsAt_tall _ _ _ w |>.mpr fun a _ => MndK.holdsAt_tall _ _ _ w |>.mpr fun b _ =>
      MndK.holdsAt_tall _ _ _ w |>.mpr fun c _ => ?_
    refine (MndK.holdsAt_all _ _ _ _ w).mpr fun x _ => (MndK.holdsAt_all _ _ _ _ w).mpr fun y _ =>
      (MndK.holdsAt_all _ _ _ _ w).mpr fun z _ => ?_
    refine (MndK.holdsAt_imp _ _ _ _ w).mpr fun h => ?_
    have hc := (MndK.holdsAt_conj _ _ _ _ w).mp h
    obtain ⟨h1, h2, h3⟩ := (MndK.holdsAt_eqv (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv2 tv1
      (.var (.there (.there .here))) (.var (.there .here)) (scons c (scons b (scons a ρ))) (((env, x), y), z) w).mp hc.1
    obtain ⟨k1, k2, k3⟩ := (MndK.holdsAt_eqv (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv1 tv0
      (.var (.there .here)) (.var .here) (scons c (scons b (scons a ρ))) (((env, x), y), z) w).mp hc.2
    exact (MndK.holdsAt_eqv _ _ _ _ _ _ w).mpr ⟨fun hw => (h1 hw).trans (k1 hw), h2.trans k2, CR_trans h2 k2 h3 k3⟩
  refTeq := by
    intro w ρ _ env _
    exact MndK.holdsAt_tall _ _ _ w |>.mpr fun a _ => (MndK.holdsAt_teq _ _ _ _ w).mpr ⟨fun _ => rfl, rfl⟩
  llTeq := by
    intro n Γ Q w ρ _ env henv
    refine MndK.holdsAt_tall _ _ _ w |>.mpr fun a _ => MndK.holdsAt_tall _ _ _ w |>.mpr fun b _ => ?_
    refine (MndK.holdsAt_imp _ _ _ _ w).mpr fun hab => ?_
    obtain ⟨e1, e2⟩ := (MndK.holdsAt_teq (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env w).mp hab
    refine (MndK.holdsAt_imp _ _ _ _ w).mpr fun hq => ?_
    exact ndInv.llTeq_at Q w ρ env henv a b (CR a b) ⟨e2, fun v hv hv' => e1 (R_true hv hv'), fun _ _ _ => Iff.rfl⟩ hq

theorem Mnd_LLEqv : MndK.Valid LLEqv := fun ρ hρ env henv => MndK.LLEqv_of MndK_heq _ ρ hρ env henv
theorem Mnd_Class : ∀ χ, ClassSch χ → MndK.Valid χ :=
  MndK.Class_valid MndK_isModelAt (MndK.LLEqv_of MndK_heq) MndK_heq

theorem Mnd_not_NDTeq : ¬ MndK.Valid NDTeq := fun h => by
  have h0 := h (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MndK.holdsAt_tall _ _ _ _).mp ((MndK.holdsAt_tall _ _ _ _).mp h0 .e trivial) (.base ()) trivial
  have h2 := (MndK.holdsAt_imp _ _ _ _ _).mp h1 ((MndK.holdsAt_neg _ _ _ _).mpr fun ht =>
    nomatch ((MndK.holdsAt_teq _ _ _ _ _).mp ht).1 rfl)
  have h3 := (MndK.box_of MndK_heq _ _ _ _).mp h2 false (Or.inl rfl)
  exact (MndK.holdsAt_neg _ _ _ _).mp h3 ((MndK.holdsAt_teq _ _ _ _ _).mpr ⟨(fun h => nomatch h), rfl⟩)

theorem Mnd_Valid_of {φ : Fm Ctx.nil} (h : MndK.HoldsAt φ (fun i => i.elim0) () true) : MndK.Valid φ := by
  intro ρ _ env _
  have e1 : ρ = fun i => i.elim0 := funext fun i => i.elim0
  subst e1
  exact h

theorem Mnd_Disjoint : MndK.Valid Disjoint := by
  refine Mnd_Valid_of ?_
  refine (MndK.holdsAt_tall _ _ _ _).mpr fun a _ => (MndK.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MndK.holdsAt_imp _ _ _ _ _).mpr fun hn => ?_
  refine (MndK.holdsAt_all _ _ _ _ _).mpr fun x _ => (MndK.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (MndK.holdsAt_neg _ _ _ _).mpr fun hxy => ?_
  obtain ⟨h1, h2, _⟩ := (MndK.holdsAt_eqv _ _ _ _ _ _ _).mp hxy
  exact (MndK.holdsAt_neg _ _ _ _).mp hn ((MndK.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => h1 rfl, h2⟩)

theorem Mnd_Slogan : MndK.Valid Slogan := by
  refine Mnd_Valid_of ?_
  refine (MndK.holdsAt_all _ _ _ _ _).mpr fun x _ => (MndK.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MndK.holdsAt_all _ _ _ _ _).mpr fun y _ => (MndK.holdsAt_neg _ _ _ _).mpr fun hxy => ?_
  obtain ⟨h1, _, _⟩ := (MndK.holdsAt_eqv _ _ _ _ _ _ _).mp hxy
  exact nomatch h1 rfl

theorem Mnd_cong {a b c d : Code Unit} {f : UND.El (.arr a c)} {g : UND.El (.arr b d)} {x : UND.El a} {y : UND.El b}
    (h1 : eqvND (.arr a c) (.arr b d) f g true) (h2 : eqvND a b x y true) : eqvND c d (f x) (g y) true := by
  obtain ⟨e1, _, r1⟩ := h1
  obtain ⟨e2, _, r2⟩ := h2
  have e := e1 rfl
  injection e with ea ec
  subst ea; subst ec
  exact ⟨fun _ => rfl, rfl, r1 true (UND.Rrefl true) x y r2⟩

theorem Mnd_Cong : MndK.Valid Cong := by
  refine Mnd_Valid_of ?_
  refine (MndK.holdsAt_tall _ _ _ _).mpr fun a _ => (MndK.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (MndK.holdsAt_tall _ _ _ _).mpr fun c _ => (MndK.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MndK.holdsAt_all _ _ _ _ _).mpr fun f _ => (MndK.holdsAt_all _ _ _ _ _).mpr fun g _ =>
    (MndK.holdsAt_all _ _ _ _ _).mpr fun x _ => (MndK.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (MndK.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hc := (MndK.holdsAt_conj _ _ _ _ _).mp h
  have h1 := (MndK.holdsAt_eqv _ _ _ _ _ _ _).mp hc.1
  have h2 := (MndK.holdsAt_eqv _ _ _ _ _ _ _).mp hc.2
  have h3 := Mnd_cong h1 h2
  exact (MndK.holdsAt_eqv _ _ _ _ _ _ _).mpr h3

theorem Mnd_Inj : MndK.Valid Inj := by
  refine Mnd_Valid_of ?_
  refine (MndK.holdsAt_tall _ _ _ _).mpr fun a _ => (MndK.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (MndK.holdsAt_tall _ _ _ _).mpr fun c _ => (MndK.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MndK.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code Unit) = .arr b d := ((MndK.holdsAt_teq _ _ _ _ _).mp h).1 rfl
  exact (MndK.holdsAt_conj _ _ _ _ _).mpr ⟨(MndK.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => (Code.arr.inj e).1,
    congrArg img (Code.arr.inj e).1⟩, (MndK.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => (Code.arr.inj e).2,
    congrArg img (Code.arr.inj e).2⟩⟩

theorem Mnd_Recovery : MndK.Valid Recovery := by
  refine Mnd_Valid_of ?_
  refine (MndK.holdsAt_tall _ _ _ _).mpr fun a _ => (MndK.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (MndK.holdsAt_tall _ _ _ _).mpr fun c _ => (MndK.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MndK.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code Unit) = .arr b d :=
    ((MndK.holdsAt_teq _ _ _ _ _).mp ((MndK.holdsAt_conj _ _ _ _ _).mp h).1).1 rfl
  exact (MndK.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => (Code.arr.inj e).2, congrArg img (Code.arr.inj e).2⟩

theorem Mnd_sub_eq {n : Nat} {Γ : Ctx n} (ρ : UND.TEnv n) (env : UND.Env Γ ρ) (a b : Code Unit)
    (h : MndK.HoldsAt (subT : Fm (Γ.text.text)) (scons b (scons a ρ)) env true) : a = b := by
  obtain ⟨x, hx⟩ := UND.adm_nonempty a
  obtain ⟨y, _, hy⟩ := (MndK.holdsAt_ex _ _ _ _ _).mp ((MndK.holdsAt_all _ _ _ _ _).mp h x (hx true))
  exact ((MndK.holdsAt_eqv _ _ _ _ _ _ _).mp hy).1 rfl

theorem Mnd_ExtT : MndK.Valid ExtT := by
  refine Mnd_Valid_of ?_
  refine (MndK.holdsAt_tall _ _ _ _).mpr fun a _ => (MndK.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MndK.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e := Mnd_sub_eq _ _ a b ((MndK.holdsAt_conj _ _ _ _ _).mp h).1
  exact (MndK.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => e, congrArg img e⟩

theorem Mnd_IntT : MndK.Valid IntT := by
  refine Mnd_Valid_of ?_
  refine (MndK.holdsAt_tall _ _ _ _).mpr fun a _ => (MndK.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MndK.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have h1 := (MndK.box_of MndK_heq _ _ _ _).mp ((MndK.holdsAt_conj _ _ _ _ _).mp h).1 true (UND.Rrefl true)
  have e := Mnd_sub_eq _ _ a b h1
  exact (MndK.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => e, congrArg img e⟩

/-- With constant domains of types, the Barcan formula for types holds. -/
theorem Mnd_TBF : ∀ χ, TBFSch χ → MndK.Valid χ := by
  rintro _ ⟨φ, rfl⟩
  refine Mnd_Valid_of ?_
  refine (MndK.holdsAt_imp _ _ _ _ _).mpr fun h => (MndK.box_of MndK_heq _ _ _ _).mpr fun v hv => ?_
  refine (MndK.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  exact (MndK.box_of MndK_heq _ _ _ _).mp ((MndK.holdsAt_tall _ _ _ _).mp h a trivial) v hv

/-- Where `≈` is identity of types at every world, Necessity of Distinctness holds. -/
theorem Mbf_NDTeq : MbfK.Valid NDTeq := by
  refine Frame.simple_Valid_of UBF ?_
  refine (MbfK.holdsAt_tall _ _ _ _).mpr fun a _ => (MbfK.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MbfK.holdsAt_imp _ _ _ _ _).mpr fun hn => (Frame.simple_box UBF _ _ _ _).mpr fun v _ => ?_
  refine (MbfK.holdsAt_neg _ _ _ _).mpr fun ht => (MbfK.holdsAt_neg _ _ _ _).mp hn ?_
  have e : a = b := (MbfK.holdsAt_teq _ _ _ _ v).mp ht
  exact (MbfK.holdsAt_teq _ _ _ _ _).mpr e

end Kr
end PIF
