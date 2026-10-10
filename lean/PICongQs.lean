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

end PIF
