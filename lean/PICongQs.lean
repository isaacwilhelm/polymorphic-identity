import PINoSelf

/-!
# Cong, PCong and PExt with the other principles

Models settling the questions left open, in the Strength diagram, by assuming Cong, PCong or PExt
over PI⁻, PI or PIᶜ.
-/
set_option autoImplicit false

namespace PIF

/-! ## `𝔐_k,cong` also satisfies Disjoint and PExt -/

namespace Kr
open Tm

theorem KC_Disjoint : KC.Valid Disjoint := by
  intro ρ _ env _
  refine (KC.holdsAt_tall _ _ _ _).mpr fun a _ => (KC.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (KC.holdsAt_imp _ _ _ _ _).mpr fun hn => ?_
  refine (KC.holdsAt_all _ _ _ _ _).mpr fun x _ => (KC.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (KC.holdsAt_neg _ _ _ _).mpr fun hxy => ?_
  exact (KC.holdsAt_neg _ _ _ _).mp hn ((KC.holdsAt_teq _ _ _ _ _).mpr ((KC.holdsAt_eqv _ _ _ _ _ _ _).mp hxy))

theorem KC_PExt : KC.Valid PExt := by
  intro ρ _ env _
  refine (KC.holdsAt_tall _ _ _ _).mpr fun a _ => (KC.holdsAt_tall _ _ _ _).mpr fun c _ =>
    (KC.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (KC.holdsAt_all _ _ _ _ _).mpr fun f _ => (KC.holdsAt_all _ _ _ _ _).mpr fun g _ => ?_
  refine (KC.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  obtain ⟨x0, hx0⟩ := UC.adm_nonempty a
  have e : c = d := (KC.holdsAt_eqv _ _ _ _ _ _ _).mp ((KC.holdsAt_all _ _ _ _ _).mp h x0 (hx0 _))
  exact (KC.holdsAt_eqv _ _ _ _ _ _ _).mpr (congrArg (Code.arr a) e)

end Kr

/-! ## `𝔐_tb` satisfies PCong -/

namespace Tg

theorem Mtb_PCong : MtbF.Valid PCong := by
  refine (MtbF.valid_iff_tr _).mpr ?_
  show ∀ a c d (f : MtbF.U.El a → MtbF.U.El c) (g : MtbF.U.El a → MtbF.U.El d) x,
    MtbF.eqv (.arr a c) (.arr a d) f g → MtbF.eqv c d (f x) (g x)
  intro a c d f g x h
  obtain ⟨e, h2⟩ := h
  injection e with _ ecd
  subst ecd
  rcases h2 with h2 | ⟨s, _⟩
  · rw [eq_of_heq h2]; exact clsEqv_refl Stb _ _
  · exact s.elim

end Tg

/-! ## `𝔐_1,tow`: towers over `e ≡ ⊥`

`E = 1`. The entity is identified with `⊥`; more generally, the bottom item of each type is
identified with the bottom items of the types with the same arguments, where the bottom item of
`A → e` is its only item and the bottom item of `A → t` is the constantly false property. Each item
has a *key*: the type `A → e` whose bottom it is, if it is a bottom. Items are identified just in case
they are identical, or have the same key. -/

section Tow
open Classical

noncomputable def bkeyT (p : Prop) : Option (Code Empty) := if ¬ p then some .e else none

/-- The key of a bottom item. -/
noncomputable def bkey : (c : Code Empty) → unitUniv.El c → Option (Code Empty)
  | .e, _ => some .e
  | .t, p => bkeyT p
  | .base b, _ => b.elim
  | .arr a c, f => if h : ∃ K, ∀ z, bkey c (f z) = some K then some (.arr a (Classical.choose h)) else none

/-- `A → e`, for `A → e` or `A → t`. -/
def finE : Code Empty → Code Empty
  | .arr a c => .arr a (finE c)
  | _ => .e

theorem bkey_arr_some {a c : Code Empty} {f : unitUniv.El (.arr a c)} {K : Code Empty}
    (h : ∀ z, bkey c (f z) = some K) : bkey (.arr a c) f = some (.arr a K) := by
  have h' : ∃ K, ∀ z, bkey c (f z) = some K := ⟨K, h⟩
  show (if h : ∃ K, ∀ z, bkey c (f z) = some K then some (Code.arr a (Classical.choose h)) else none) = _
  split
  · rename_i h''
    obtain ⟨x0⟩ := Univ.El_nonempty (U := unitUniv) a
    have := (Classical.choose_spec h'' x0).symm.trans (h x0)
    injection this with e
    rw [e]
  · exact absurd h' ‹_›

theorem bkey_arr {a c : Code Empty} {f : unitUniv.El (.arr a c)} {K : Code Empty}
    (h : bkey (.arr a c) f = some K) : ∃ K1, K = .arr a K1 ∧ ∀ z, bkey c (f z) = some K1 := by
  by_cases h' : ∃ K, ∀ z, bkey c (f z) = some K
  · obtain ⟨K1, hK1⟩ := h'
    rw [bkey_arr_some hK1] at h
    injection h with e
    exact ⟨K1, e.symm, hK1⟩
  · have : bkey (.arr a c) f = none := by
      show (if h : ∃ K, ∀ z, bkey c (f z) = some K then some (Code.arr a (Classical.choose h)) else none) = _
      split
      · exact absurd ‹_› h'
      · rfl
    rw [this] at h; cases h

theorem bkey_t {p : Prop} {K : Code Empty} (h : bkey .t p = some K) : ¬ p ∧ K = .e := by
  change bkeyT p = some K at h
  unfold bkeyT at h
  split at h
  · rename_i hp; injection h with e'; exact ⟨hp, e'.symm⟩
  · cases h

/-- The key of a bottom item of `c` is `finE c`. -/
theorem bkey_code : ∀ (c : Code Empty) (x : unitUniv.El c) (K : Code Empty), bkey c x = some K → K = finE c
  | .e, _, K, h => by injection h with e; exact e.symm
  | .t, _, _, h => (bkey_t h).2
  | .base b, _, _, _ => b.elim
  | .arr a c, f, K, h => by
    obtain ⟨K1, rfl, hK1⟩ := bkey_arr h
    obtain ⟨x0⟩ := Univ.El_nonempty (U := unitUniv) a
    show Code.arr a K1 = Code.arr a (finE c)
    rw [bkey_code c (f x0) K1 (hK1 x0)]

/-- Each type has at most one bottom. -/
theorem bkey_unique : ∀ (c : Code Empty) (x y : unitUniv.El c) (K : Code Empty),
    bkey c x = some K → bkey c y = some K → x = y
  | .e, (), (), _, _, _ => rfl
  | .t, _, _, _, hx, hy => propext ⟨fun h => ((bkey_t hx).1 h).elim, fun h => ((bkey_t hy).1 h).elim⟩
  | .base b, _, _, _, _, _ => b.elim
  | .arr a c, f, g, K, hf, hg => by
    obtain ⟨K1, rfl, h1⟩ := bkey_arr hf
    obtain ⟨K2, e, h2⟩ := bkey_arr hg
    injection e with _ e2
    subst e2
    exact funext fun z => bkey_unique c (f z) (g z) K1 (h1 z) (h2 z)

/-- A type `A → t` has an item with no key. -/
theorem bkey_none : ∀ c : Code Empty, finE c ≠ c → ∃ x : unitUniv.El c, bkey c x = none
  | .e, h => (h rfl).elim
  | .t, _ => ⟨True, by
      change bkeyT True = none
      unfold bkeyT
      split
      · rename_i h; exact (h trivial).elim
      · rfl⟩
  | .base b, _ => b.elim
  | .arr a c, h => by
    have hc : finE c ≠ c := fun e => h (by show Code.arr a (finE c) = Code.arr a c; rw [e])
    obtain ⟨z, hz⟩ := bkey_none c hc
    refine ⟨fun _ => z, ?_⟩
    cases hk : bkey (Code.arr a c) (fun _ => z) with
    | none => rfl
    | some K =>
      obtain ⟨K1, _, h1⟩ := bkey_arr hk
      obtain ⟨x0⟩ := Univ.El_nonempty (U := unitUniv) a
      have := h1 x0
      rw [hz] at this
      cases this

def towRel (p q : Σ c, unitUniv.El c) : Prop := p = q ∨ ∃ K, bkey p.1 p.2 = some K ∧ bkey q.1 q.2 = some K

def towD : IdentData where
  U := unitUniv
  rel := towRel
  refl := fun _ => Or.inl rfl
  symm := by
    rintro p q (h | ⟨K, h1, h2⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨K, h2, h1⟩
  trans := by
    rintro p q r (h | ⟨K, h1, h2⟩) (h' | ⟨K', h1', h2'⟩)
    · exact Or.inl (h.trans h')
    · subst h; exact Or.inr ⟨K', h1', h2'⟩
    · subst h'; exact Or.inr ⟨K, h1, h2⟩
    · rw [h2] at h1'; injection h1' with e; subst e; exact Or.inr ⟨K, h1, h2'⟩

theorem tow_within (c : Code Empty) (x y : unitUniv.El c) (h : towRel ⟨c, x⟩ ⟨c, y⟩) : x = y := by
  rcases h with h | ⟨K, h1, h2⟩
  · exact eq_of_heq (Sigma.mk.inj h).2
  · exact bkey_unique c x y K h1 h2

abbrev Mtow : Frame := towD.frame
theorem Mtow_model : Mtow.IsModelPIm := towD.model
theorem Mtow_LLEqv : Mtow.Valid LLEqv := towD.LLEqv_valid tow_within
theorem Mtow_Class : ∀ χ, ClassSch χ → Mtow.Valid χ := Mtow.Class_valid Mtow_model Mtow_LLEqv

theorem Mtow_not_Disjoint : ¬ Mtow.Valid Disjoint := fun h =>
  Mtow.tr_Disjoint.mp ((Mtow.valid_iff_tr _).mp h) .e .t (fun (e : (Code.e : Code Empty) = .t) => nomatch e) () False
    (Or.inr ⟨.e, rfl, by
      change bkeyT False = some Code.e
      unfold bkeyT
      split
      · rfl
      · rename_i h; exact (h not_false).elim⟩)

theorem Mtow_Cong : Mtow.Valid Cong := by
  refine (Mtow.valid_iff_tr _).mpr (Mtow.tr_Cong.mpr ?_)
  intro a b c d f g x y ⟨h1, h2⟩
  rcases h1 with h1 | ⟨K, k1, k2⟩
  · obtain ⟨e1, e2⟩ := Sigma.mk.inj h1
    injection e1 with ea ec
    subst ea; subst ec
    have ef : f = g := eq_of_heq e2
    subst ef
    have exy : x = y := tow_within a x y h2
    subst exy
    exact Or.inl rfl
  · obtain ⟨K1, rfl, hf⟩ := bkey_arr k1
    obtain ⟨K2, e, hg⟩ := bkey_arr k2
    injection e with ea eK
    subst ea; subst eK
    have exy : x = y := tow_within a x y h2
    subst exy
    exact Or.inr ⟨K1, hf x, hg x⟩

theorem Mtow_PExt : Mtow.Valid PExt := by
  refine (Mtow.valid_iff_tr _).mpr (Mtow.tr_PExt.mpr ?_)
  intro a c d f g h
  obtain ⟨x0⟩ := Univ.El_nonempty (U := unitUniv) a
  by_cases ecd : c = d
  · subst ecd
    exact Or.inl (by rw [funext fun z => tow_within c (f z) (g z) (h z)])
  · have key : ∀ z, bkey c (f z) = some (finE c) ∧ bkey d (g z) = some (finE c) := by
      intro z
      rcases h z with h' | ⟨K, k1, k2⟩
      · exact (ecd (congrArg Sigma.fst h')).elim
      · have e := bkey_code c (f z) K k1; subst e; exact ⟨k1, k2⟩
    exact Or.inr ⟨.arr a (finE c), bkey_arr_some fun z => (key z).1, bkey_arr_some fun z => (key z).2⟩

theorem finE_idem : ∀ c : Code Empty, finE (finE c) = finE c
  | .arr a c => by show Code.arr a (finE (finE c)) = Code.arr a (finE c); rw [finE_idem c]
  | .e => rfl
  | .t => rfl
  | .base b => b.elim

theorem Mtow_ExtT : Mtow.Valid ExtT := by
  refine (Mtow.valid_iff_tr _).mpr (Mtow.tr_ExtT.mpr ?_)
  intro a b ⟨h1, h2⟩
  show a = b
  refine Classical.byContradiction fun hab => ?_
  -- every item of `a`, and of `b`, has a key; so both are `A → e`, with the same `A`
  have ka : ∀ x : unitUniv.El a, ∃ K, bkey a x = some K := fun x => by
    obtain ⟨y, hy⟩ := h1 x
    rcases hy with hy | ⟨K, k1, _⟩
    · exact (hab (congrArg Sigma.fst hy)).elim
    · exact ⟨K, k1⟩
  have kb : ∀ y : unitUniv.El b, ∃ K, bkey b y = some K := fun y => by
    obtain ⟨x, hx⟩ := h2 y
    rcases hx with hx | ⟨K, _, k2⟩
    · exact (hab (congrArg Sigma.fst hx)).elim
    · exact ⟨K, k2⟩
  have fa : finE a = a := Classical.byContradiction fun hne => by
    obtain ⟨x, hx⟩ := bkey_none a hne
    obtain ⟨K, hK⟩ := ka x
    rw [hx] at hK; cases hK
  have fb : finE b = b := Classical.byContradiction fun hne => by
    obtain ⟨y, hy⟩ := bkey_none b hne
    obtain ⟨K, hK⟩ := kb y
    rw [hy] at hK; cases hK
  obtain ⟨x0⟩ := Univ.El_nonempty (U := unitUniv) a
  obtain ⟨y, hy⟩ := h1 x0
  rcases hy with hy | ⟨K, k1, k2⟩
  · exact hab (congrArg Sigma.fst hy)
  · exact hab (fa.symm.trans ((bkey_code a x0 K k1).symm.trans ((bkey_code b y K k2).trans fb)))

end Tow

/-! ## `𝔐_k,w1`: identity is identity at the other world (PI⁻)

Two worlds; the actual world sees both, the other only itself. Items of one type are identified,
at either world, just in case they are identical at the other world. So Cong and PExt hold; `⊤ ≢ ⊥`;
but the proposition true only at the other world is identified with `⊤` without being true, so T
fails. -/

namespace Kr
open Tm

def UW1 : Univ where
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
  Base := Empty
  B := Empty.elim
  neE := ⟨true⟩
  neB := fun b => b.elim
  re := fun _ x y => x = y
  rb := fun _ b => b.elim
  re_refl := fun _ _ => rfl
  re_symm := fun _ _ _ h => h.symm
  re_trans := fun _ _ _ _ h1 h2 => h1.trans h2
  re_mono := fun _ _ _ _ _ h => h
  rb_refl := fun _ b => b.elim
  rb_symm := fun _ b => b.elim
  rb_trans := fun _ b => b.elim
  rb_mono := fun _ _ b => b.elim
  D := fun _ _ => True
  D_e := fun _ => trivial
  D_t := fun _ => trivial
  D_arr := fun _ _ _ _ _ => trivial
  D_mono := fun _ _ _ _ _ => trivial

theorem UW1_toF : ∀ w, UW1.R w false := fun _ => Or.inr rfl

def KW1 : Frame where
  U := UW1
  eqv := fun a b x y _ => ∃ h : a = b, UW1.rel b false (cast (congrArg UW1.El h) x) y
  teq := fun a b _ => a = b
  eqv_resp := by
    intro u a b x x' y y' hx hy
    have hx' := UW1.rel_mono a u false x x' (UW1_toF u) hx
    have hy' := UW1.rel_mono b u false y y' (UW1_toF u) hy
    constructor
    · rintro ⟨h, r⟩; subst h
      exact ⟨rfl, UW1.rel_trans _ _ _ _ _ (UW1.rel_trans _ _ _ _ _ (UW1.rel_symm _ _ _ _ hx') r) hy'⟩
    · rintro ⟨h, r⟩; subst h
      exact ⟨rfl, UW1.rel_trans _ _ _ _ _ (UW1.rel_trans _ _ _ _ _ hx' r) (UW1.rel_symm _ _ _ _ hy')⟩

theorem KW1_same (a : Code Empty) (x y : UW1.El a) (w : Bool) : KW1.eqv a a x y w ↔ UW1.rel a false x y :=
  ⟨fun ⟨_, r⟩ => by rwa [cast_eq] at r, fun r => ⟨rfl, r⟩⟩

theorem KW1_isModelAt : KW1.IsModelAt := by
  obtain ⟨h1, h2, h3⟩ := KW1.idAx_of
    (fun a x w hx => (KW1_same a x x w).mpr (UW1.rel_mono a w false x x (UW1_toF w) hx))
    (fun a b x y w h => by obtain ⟨e, r⟩ := h; subst e; exact ⟨rfl, UW1.rel_symm _ _ _ _ r⟩)
    (fun a b c x y z w h1 h2 => by
      obtain ⟨e1, r1⟩ := h1; obtain ⟨e2, r2⟩ := h2; subst e1; subst e2
      exact ⟨rfl, UW1.rel_trans _ _ _ _ _ r1 r2⟩)
  exact ⟨h1, h2, h3, KW1.refTeq_of fun _ _ => rfl, fun Q => KW1.llTeq_of_eq (fun _ _ _ h => h) Q⟩

theorem KW1_cong {a b c d : Code Empty} {f : UW1.El (.arr a c)} {g : UW1.El (.arr b d)} {x : UW1.El a}
    {y : UW1.El b} {w : Bool} (h1 : KW1.eqv (.arr a c) (.arr b d) f g w) (h2 : KW1.eqv a b x y w) :
    KW1.eqv c d (f x) (g y) w := by
  obtain ⟨e1, r1⟩ := h1; obtain ⟨e2, r2⟩ := h2
  injection e1 with ea ec
  subst ea; subst ec
  have r1' : UW1.rel (.arr a c) false f g := (KW1_same _ f g w).mp ⟨e1, r1⟩
  have r2' : UW1.rel a false x y := (KW1_same _ x y w).mp ⟨e2, r2⟩
  exact ⟨rfl, r1' false (UW1.Rrefl false) x y r2'⟩

theorem KW1_Cong : KW1.Valid Cong := by
  intro ρ _ env _
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => (KW1.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (KW1.holdsAt_tall _ _ _ _).mpr fun c _ => (KW1.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (KW1.holdsAt_all _ _ _ _ _).mpr fun f _ => (KW1.holdsAt_all _ _ _ _ _).mpr fun g _ =>
    (KW1.holdsAt_all _ _ _ _ _).mpr fun x _ => (KW1.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hc := (KW1.holdsAt_conj _ _ _ _ _).mp h
  have h1 := (KW1.holdsAt_eqv _ _ _ _ _ _ _).mp hc.1
  have h2 := (KW1.holdsAt_eqv _ _ _ _ _ _ _).mp hc.2
  have h3 := KW1_cong h1 h2
  exact (KW1.holdsAt_eqv _ _ _ _ _ _ _).mpr h3

theorem KW1_PExt : KW1.Valid PExt := by
  intro ρ _ env _
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => (KW1.holdsAt_tall _ _ _ _).mpr fun c _ =>
    (KW1.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (KW1.holdsAt_all _ _ _ _ _).mpr fun f hf => (KW1.holdsAt_all _ _ _ _ _).mpr fun g hg => ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hpt : ∀ x : UW1.El a, UW1.rel a true x x → KW1.eqv c d (f x) (g x) true := fun x hx =>
    (KW1.holdsAt_eqv _ _ _ _ _ _ _).mp ((KW1.holdsAt_all _ _ _ _ _).mp h x hx)
  obtain ⟨x0, hx0⟩ := UW1.adm_nonempty a
  obtain ⟨ecd, _⟩ := hpt x0 (hx0 _)
  subst ecd
  have hf' : UW1.rel (.arr a c) true f f := hf
  have hg' : UW1.rel (.arr a c) true g g := hg
  refine (KW1.holdsAt_eqv _ _ _ _ _ _ _).mpr ((KW1_same _ _ _ _).mpr ?_)
  intro v hv x x' hxx'
  have hvf : v = false := hv.resolve_left Bool.false_ne_true
  subst hvf
  obtain ⟨z, hz, hzx⟩ := UW1.dense true false (fun _ _ => Or.inr rfl) (fun _ _ => Or.inr rfl) a x' (UW1.rel_refl_right a false _ _ hxx')
  have hxz := UW1.rel_trans a false _ _ _ hxx' (UW1.rel_symm a false _ _ hzx)
  have e1 := hf' false (Or.inl rfl) x z hxz
  have e2 := (KW1_same c _ _ true).mp (hpt z hz)
  have e3 := hg' false (Or.inl rfl) z x' hzx
  exact UW1.rel_trans c false _ _ _ e1 (UW1.rel_trans c false _ _ _ e2 e3)

theorem KW1_TopBot : KW1.Valid TopBot := by
  intro ρ _ env _
  refine (KW1.holdsAt_neg _ _ _ _).mpr fun h => ?_
  have h' := (KW1_same .t _ _ _).mp ((KW1.holdsAt_eqv _ _ _ _ _ _ _).mp h)
  have this : KW1.eval (topF : Fm Ctx.nil) ρ env false → KW1.eval (botF : Fm Ctx.nil) ρ env false :=
    (h' false (UW1.Rrefl false)).mp
  rw [KW1.eval_topF, KW1.eval_botF] at this
  exact this trivial

theorem KW1_not_TAx : ¬ KW1.Valid TAx := fun h => by
  have h0 := h (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (KW1.holdsAt_all _ _ _ _ _).mp h0 (fun w => w = false) (fun _ _ => Iff.rfl)
  have hb : KW1.HoldsAt (Γ := Ctx.nil.ext tyT) (boxF (Tm.var .here)) (fun i => i.elim0) ((), fun (w : Bool) => w = false) true := by
    refine (KW1.holdsAt_eqv _ _ _ _ _ _ _).mpr ((KW1_same .t _ _ _).mpr ?_)
    intro v hv
    have hvf : v = false := hv.resolve_left Bool.false_ne_true
    subst hvf
    have et := congrFun (KW1.eval_topF (Γ := Ctx.nil.ext tyT) (fun i => i.elim0) ((), fun (w : Bool) => w = false)) false
    show (false = false) ↔ KW1.eval (topF : Fm (Ctx.nil.ext tyT)) (fun i => i.elim0) ((), fun (w : Bool) => w = false) false
    rw [et]
    exact ⟨fun _ => trivial, fun _ => rfl⟩
  exact Bool.noConfusion ((KW1.holdsAt_imp _ _ _ _ _).mp h1 hb : true = false)

end Kr

/-! ## `𝔐_cl` satisfies Cong, PCong and PExt -/

namespace Al

theorem Mcl_Cong : MclF.Valid Cong := by
  intro ρ env
  refine (MclF.holds_tall _ _ _).mpr fun a => (MclF.holds_tall _ _ _).mpr fun b =>
    (MclF.holds_tall _ _ _).mpr fun c => (MclF.holds_tall _ _ _).mpr fun d => ?_
  refine (MclF.holds_all _ _ _ _).mpr fun f => (MclF.holds_all _ _ _ _).mpr fun g =>
    (MclF.holds_all _ _ _ _).mpr fun x => (MclF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MclF.holds_imp _ _ _ _).mpr fun h => ?_
  have hc := (MclF.holds_conj _ _ _ _).mp h
  obtain ⟨e1, hfg⟩ := (mkA_V _).mp ((MclF.holds_eqv _ _ _ _ _ _).mp hc.1)
  obtain ⟨_, hxy⟩ := (mkA_V _).mp ((MclF.holds_eqv _ _ _ _ _ _).mp hc.2)
  have e1' : (Code.arr a c : Code Empty) = Code.arr b d := e1
  injection e1' with ea ec
  subst ea; subst ec
  have ef : f = g := eq_of_heq ((cast_heq _ _).symm.trans (hfg.trans (cast_heq _ _)))
  have ex : x = y := eq_of_heq ((cast_heq _ _).symm.trans (hxy.trans (cast_heq _ _)))
  subst ef; subst ex
  exact (MclF.holds_eqv _ _ _ _ _ _).mpr ((mkA_V _).mpr ⟨rfl, HEq.rfl⟩)

theorem Mcl_PCong : MclF.Valid PCong := by
  intro ρ env
  refine (MclF.holds_tall _ _ _).mpr fun a => (MclF.holds_tall _ _ _).mpr fun c =>
    (MclF.holds_tall _ _ _).mpr fun d => ?_
  refine (MclF.holds_all _ _ _ _).mpr fun f => (MclF.holds_all _ _ _ _).mpr fun g =>
    (MclF.holds_all _ _ _ _).mpr fun x => ?_
  refine (MclF.holds_imp _ _ _ _).mpr fun h => ?_
  obtain ⟨e1, hfg⟩ := (mkA_V _).mp ((MclF.holds_eqv _ _ _ _ _ _).mp h)
  have e1' : (Code.arr a c : Code Empty) = Code.arr a d := e1
  injection e1' with _ ec
  subst ec
  have ef : f = g := eq_of_heq ((cast_heq _ _).symm.trans (hfg.trans (cast_heq _ _)))
  subst ef
  exact (MclF.holds_eqv _ _ _ _ _ _).mpr ((mkA_V _).mpr ⟨rfl, HEq.rfl⟩)

theorem Mcl_PExt : MclF.Valid PExt := by
  intro ρ env
  refine (MclF.holds_tall _ _ _).mpr fun a => (MclF.holds_tall _ _ _).mpr fun c =>
    (MclF.holds_tall _ _ _).mpr fun d => ?_
  refine (MclF.holds_all _ _ _ _).mpr fun f => (MclF.holds_all _ _ _ _).mpr fun g => ?_
  refine (MclF.holds_imp _ _ _ _).mpr fun h => ?_
  have hp : ∀ x, _ := fun x => (mkA_V _).mp ((MclF.holds_eqv _ _ _ _ _ _).mp ((MclF.holds_all _ _ _ _).mp h x))
  have x0 := Classical.choice (Univ.El_nonempty (U := MclF.U) a)
  have ecd : c = d := (hp x0).1
  subst ecd
  have ef : f = g := funext fun x => eq_of_heq ((cast_heq _ _).symm.trans ((hp x).2.trans (cast_heq _ _)))
  subst ef
  exact (MclF.holds_eqv _ _ _ _ _ _).mpr ((mkA_V _).mpr ⟨rfl, HEq.rfl⟩)

end Al

/-! ## `𝔐_tb,x`: `𝔐_tb` with identity of functions pointwise (PI⁻)

As `𝔐_tb`, quantified propositions are identified with each other; in addition, functions of one
type are identified when their values are identified at every argument. So PExt holds; T holds, as
before, and Truth fails. -/

namespace Tg

def Etb : (c : Code univU.Base) → univU.El c → univU.El c → Prop
  | .t => fun p q => p = q ∨ (Stb .t p ∧ Stb .t q)
  | .arr _ c => fun f g => ∀ x, Etb c (f x) (g x)
  | _ => fun x y => x = y

theorem Etb_refl : ∀ (c : Code univU.Base) (x : univU.El c), Etb c x x
  | .t, _ => Or.inl rfl
  | .arr _ c, _ => fun _ => Etb_refl c _
  | .e, _ => rfl
  | .base b, _ => b.elim

theorem Etb_symm : ∀ (c : Code univU.Base) (x y : univU.El c), Etb c x y → Etb c y x
  | .t, _, _, h => h.elim (fun e => Or.inl e.symm) (fun ⟨p, q⟩ => Or.inr ⟨q, p⟩)
  | .arr _ c, _, _, h => fun x => Etb_symm c _ _ (h x)
  | .e, _, _, h => h.symm
  | .base b, _, _, _ => b.elim

theorem Etb_trans : ∀ (c : Code univU.Base) (x y z : univU.El c), Etb c x y → Etb c y z → Etb c x z
  | .t, _, _, _, h1, h2 => by
    rcases h1 with e1 | ⟨s1, s2⟩ <;> rcases h2 with e2 | ⟨s3, s4⟩
    · exact Or.inl (e1.trans e2)
    · exact Or.inr ⟨e1 ▸ s3, s4⟩
    · exact Or.inr ⟨s1, e2 ▸ s2⟩
    · exact Or.inr ⟨s1, s4⟩
  | .arr _ c, _, _, _, h1, h2 => fun x => Etb_trans c _ _ _ (h1 x) (h2 x)
  | .e, _, _, _, h1, h2 => h1.trans h2
  | .base b, _, _, _, _, _ => b.elim

def eqvX (a b : Code univU.Base) (x : univU.El a) (y : univU.El b) : Prop :=
  ∃ h : a = b, Etb b (cast (congrArg univU.El h) x) y

abbrev MtbxF : Frame where
  U := univU
  eqv := eqvX
  teq := fun a b => a = b
  qtag := fun _ => false

theorem Mtbx_model : MtbxF.IsModelPIm :=
  MtbxF.model_of_equiv (fun _ _ => Iff.rfl) (fun a x => ⟨rfl, Etb_refl a x⟩)
    (fun a b x y h => by obtain ⟨e, r⟩ := h; subst e; exact ⟨rfl, Etb_symm _ _ _ r⟩)
    (fun a b c x y z h1 h2 => by
      obtain ⟨e1, r1⟩ := h1; obtain ⟨e2, r2⟩ := h2; subst e1; subst e2
      exact ⟨rfl, Etb_trans _ _ _ _ r1 r2⟩)

theorem Mtbx_PExt : MtbxF.Valid PExt := by
  refine (MtbxF.valid_iff_tr _).mpr (MtbxF.tr_PExt.mpr ?_)
  intro a c d f g h
  have x0 := Classical.choice (Univ.El_nonempty (U := univU) a)
  obtain ⟨ecd, _⟩ := h x0
  subst ecd
  refine ⟨rfl, fun x => ?_⟩
  obtain ⟨e, r⟩ := h x
  exact r

theorem Mtbx_TAx : MtbxF.Valid TAx := by
  intro ρ env
  refine (MtbxF.holds_all _ _ _ _).mpr fun p => (MtbxF.holds_imp _ _ _ _).mpr fun hb => ?_
  obtain ⟨_, r⟩ := (MtbxF.holds_eqv_t _ _ _ _).mp hb
  rcases r with e | ⟨_, s⟩
  · show p.1
    rw [show p = MtbxF.eval (topF : Fm (Ctx.nil.ext tyT)) ρ (env, p) from e]
    exact (MtbxF.holds_neg _ _ _).mpr fun hb' => (MtbxF.holds_all _ _ _ _).mp hb' (False, true)
  · exact Bool.noConfusion (s : true = false)

theorem Mtbx_not_Truth : ¬ MtbxF.Valid Truth := fun h => by
  have h1 := (MtbxF.holds_all _ _ _ _).mp ((MtbxF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (True, false)) (False, false)
  exact h1 ((MtbxF.holds_eqv_t _ _ _ _).mpr ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩) trivial

end Tg

/-! ## `𝔐_ie,c,x`: `𝔐_ie,c` with towers (PIᶜ)

As `𝔐_ie,c`, the entity is identified with the item of `d` at the actual world; in addition, the only
item of each type `A → e` is identified there with the only item of each type `A' → d` with the same
image (`d` put for `e`). So Cong and PExt hold, as well as Int≈, while Ext≈ fails. -/

namespace Wd

def finU : Code Unit → Prop
  | .e => True
  | .base _ => True
  | .arr _ c => finU c
  | .t => False

def imgU : Code Unit → Code Unit
  | .base _ => .e
  | .arr a c => .arr (imgU a) (imgU c)
  | .e => .e
  | .t => .t

theorem finU_img : ∀ c : Code Unit, finU (imgU c) ↔ finU c
  | .e => Iff.rfl
  | .t => Iff.rfl
  | .base _ => Iff.rfl
  | .arr _ c => finU_img c

theorem finU_unique : ∀ (c : Code Unit), finU c → ∀ x y : univIE.El c, x = y
  | .e, _, (), () => rfl
  | .base _, _, (), () => rfl
  | .arr _ c, h, f, g => funext fun z => finU_unique c h (f z) (g z)
  | .t, h, _, _ => h.elim

def crossX (a b : Code Unit) : Prop := a ≠ b ∧ imgU a = imgU b ∧ finU a

theorem crossX_symm {a b : Code Unit} (h : crossX a b) : crossX b a :=
  ⟨fun e => h.1 e.symm, h.2.1.symm, (finU_img b).mp (h.2.1 ▸ (finU_img a).mpr h.2.2)⟩

def MieXF : Frame where
  U := univIE
  eqv := fun a b x y w => (a = b ∧ HEq x y) ∨ (w = true ∧ crossX a b)
  teq := fun a b _ => a = b

theorem MieX_trans : ∀ a b c x y z w, MieXF.eqv a b x y w → MieXF.eqv b c y z w → MieXF.eqv a c x z w := by
  intro a b c x y z w h1 h2
  rcases h1 with ⟨rfl, h1⟩ | ⟨hw, hx⟩
  · rcases h2 with ⟨rfl, h2⟩ | ⟨hw, hx⟩
    · exact Or.inl ⟨rfl, h1.trans h2⟩
    · exact Or.inr ⟨hw, hx⟩
  · rcases h2 with ⟨rfl, _⟩ | ⟨_, hy⟩
    · exact Or.inr ⟨hw, hx⟩
    · by_cases hac : a = c
      · subst hac; exact Or.inl ⟨rfl, heq_of_eq (finU_unique a hx.2.2 x z)⟩
      · exact Or.inr ⟨hw, hac, hx.2.1.trans hy.2.1, hx.2.2⟩

theorem MieX_symm : ∀ a b x y w, MieXF.eqv a b x y w → MieXF.eqv b a y x w := fun _ _ _ _ _ h =>
  h.elim (fun h => Or.inl ⟨h.1.symm, h.2.symm⟩) (fun h => Or.inr ⟨h.1, crossX_symm h.2⟩)

theorem MieX_eq : ∀ a x y w, MieXF.eqv a a x y w → x = y := fun _ _ _ _ h =>
  h.elim (fun h => eq_of_heq h.2) (fun h => (h.2.1 rfl).elim)

theorem MieX_isModelAt : MieXF.IsModelAt :=
  MieXF.isModelAt_of (fun _ _ _ => Or.inl ⟨rfl, HEq.rfl⟩) MieX_symm MieX_trans (fun _ _ _ => Iff.rfl)

theorem MieX_model : MieXF.IsModelPIm :=
  MieXF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => Or.inl ⟨rfl, HEq.rfl⟩)
    (fun a b x y h => MieX_symm a b x y _ h) (fun a b c x y z h1 h2 => MieX_trans a b c x y z _ h1 h2)

theorem MieX_LLEqv : MieXF.Valid LLEqv := fun ρ env => MieXF.LLEqv_validAt_of MieX_eq _ ρ env

theorem MieX_Class : ∀ χ, ClassSch χ → MieXF.Valid χ :=
  MieXF.Class_valid_of MieX_isModelAt (MieXF.LLEqv_validAt_of MieX_eq) fun _ _ => Or.inl ⟨rfl, HEq.rfl⟩

theorem MieX_Cong : MieXF.Valid Cong :=
  (MieXF.valid_iff_tr _).mpr <| MieXF.tr_Cong.mpr fun a b c d f g x y ⟨h1, h2⟩ => by
    rcases h1 with ⟨e, hfg⟩ | ⟨hw, hx⟩
    · injection e with ea ec
      subst ea; subst ec
      have ef : f = g := eq_of_heq hfg
      subst ef
      have exy : x = y := MieX_eq a x y _ h2
      subst exy
      exact Or.inl ⟨rfl, HEq.rfl⟩
    · have hc : finU c := hx.2.2
      have hi : imgU c = imgU d := by injection hx.2.1 with _ e2
      by_cases hcd : c = d
      · subst hcd; exact Or.inl ⟨rfl, heq_of_eq (finU_unique c hc _ _)⟩
      · exact Or.inr ⟨hw, hcd, hi, hc⟩

theorem MieX_PExt : MieXF.Valid PExt :=
  (MieXF.valid_iff_tr _).mpr <| MieXF.tr_PExt.mpr fun a c d f g h => by
    have x0 := Classical.choice (Univ.El_nonempty (U := univIE) a)
    rcases h x0 with ⟨ecd, _⟩ | ⟨hw, hx⟩
    · subst ecd
      exact Or.inl ⟨rfl, heq_of_eq (funext fun x => MieX_eq c _ _ _ (h x))⟩
    · refine Or.inr ⟨hw, fun e => hx.1 (by injection e), ?_, hx.2.2⟩
      show Code.arr (imgU a) (imgU c) = Code.arr (imgU a) (imgU d)
      rw [hx.2.1]

theorem MieX_not_ExtT : ¬ MieXF.Valid ExtT := fun h => by
  have h0 := (MieXF.holds_tall _ _ _).mp ((MieXF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) (.base ())
  have hc : crossX .e (.base ()) := ⟨(fun e => nomatch e), rfl, trivial⟩
  have hT := (MieXF.holds_imp _ _ _ _).mp h0 ((MieXF.holds_conj _ _ _ _).mpr
    ⟨(MieXF.holds_all _ _ _ _).mpr fun x => (MieXF.holds_ex _ _ _ _).mpr
        ⟨(), (MieXF.holds_eqv _ _ _ _ _ _).mpr (Or.inr ⟨rfl, hc⟩)⟩,
     (MieXF.holds_all _ _ _ _).mpr fun y => (MieXF.holds_ex _ _ _ _).mpr
        ⟨(), (MieXF.holds_eqv _ _ _ _ _ _).mpr (Or.inr ⟨rfl, hc⟩)⟩⟩)
  exact nomatch (show (Code.e : Code Unit) = .base () from (MieXF.holds_teq _ _ _ _).mp hT)

theorem MieX_IntT : MieXF.Valid IntT := by
  intro ρ env
  refine (MieXF.holds_tall _ _ _).mpr fun a => (MieXF.holds_tall _ _ _).mpr fun b => ?_
  refine (MieXF.holds_imp _ _ _ _).mpr fun h => (MieXF.holds_teq _ _ _ _).mpr ?_
  have hb : ∀ p q, MieXF.eqv .t .t p q MieXF.U.w0 → p = q := fun p q h => MieX_eq _ _ _ _ h
  have hs := MieXF.box_all hb _ _ _ ((MieXF.holds_conj _ _ _ _).mp h).1 false
  have x0 := Classical.choice (Univ.El_nonempty (U := MieXF.U) a)
  obtain ⟨y, hy⟩ := (MieXF.holdsAt_ex _ _ _ _ false).mp ((MieXF.holdsAt_all _ _ _ _ false).mp hs x0)
  rcases (MieXF.holdsAt_eqv _ _ _ _ _ _ false).mp hy with ⟨e, _⟩ | ⟨hw, _⟩
  · exact e
  · exact (Bool.false_ne_true hw).elim

end Wd

end PIF
