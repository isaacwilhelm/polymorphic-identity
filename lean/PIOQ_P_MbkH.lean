import PIBF
import PIOQ_KBF

/-!
# The rest of the profile of `𝔐_k,bf2,h`

The model `MbkH` of `lean/PIOQ_KBF.lean`: the Kripke model `𝔐_k,bk` (three worlds; the actual world
`0` sees all three, and `1` and `2` see only themselves; four entities, with `0` and `1` identical at
world `2`), with haecceities added at the actual world. At the actual world, items are identified
just in case they have the same root, got by stripping off haecceities; at the other worlds, items
are identified just in case they are of one type and identical there. `≈` is identity of types at
every world, and every type exists at every world.

* Inj≈, Recovery, ND≈ and TBF hold, since `≈` is identity of types and the types are the same at
  every world.
* PCong holds: functions with one domain and different codomains never have the same root, so
  identified functions with one domain are of one type, and identical.
* Ext≈ and Int≈ hold: every type has an item which is its own root, and roots never lie at larger
  types; so types each of whose items is identified with an item of the other are the same.
* NI× fails: `0` is identified with its haecceity at the actual world, but not at world `1`.
* Functional Choice fails: the relation which, at the actual world, relates `0` just to `2` and `1`
  just to `3` (and holds everywhere at the other worlds) is total, but a function choosing for it
  would send `0` and `1`, which are identical at world `2`, to `2` and `3`, which are not; so it is
  not an item at the actual world.
-/
set_option autoImplicit false

namespace PIF
namespace Kr
open Tm

theorem MbkH_Valid_of {φ : Fm Ctx.nil} (h : MbkH.HoldsAt φ (fun i => i.elim0) () UBk.w0) : MbkH.Valid φ := by
  intro ρ _ env _
  have e1 : ρ = fun i => i.elim0 := funext fun i => i.elim0
  subst e1
  exact h

/-! ## Roots -/

/-- A root is the item itself, or (for an item of `β → t`) lies at a type no larger than `β`. -/
theorem MbkH_Root_cases (U : Univ) (a : Code U.Base) (x : U.El a) :
    U.Root a x = ⟨a, x⟩ ∨ ∃ b, a = .arr b .t ∧ Csz (U.Root a x).1 ≤ Csz b := by
  by_cases ha : ∃ b, a = .arr b .t
  · obtain ⟨b, rfl⟩ := ha
    by_cases h : ∃ z, U.rel b U.w0 z z ∧ U.rel (.arr b .t) U.w0 x (U.hcy b z)
    · refine Or.inr ⟨b, rfl, ?_⟩
      rw [U.Root_arr_pos b x h]
      exact U.Root_sz b _
    · exact Or.inl (U.Root_arr_neg b x h)
  · exact Or.inl (U.Root_other x fun b h => ha ⟨b, h⟩)

/-- Every type has an item, at the actual world, which is its own root. -/
theorem MbkH_selfroot (U : Univ) (a : Code U.Base) : ∃ x : U.El a, U.rel a U.w0 x x ∧ U.Root a x = ⟨a, x⟩ := by
  by_cases ha : ∃ b, a = .arr b .t
  · obtain ⟨b, rfl⟩ := ha
    refine ⟨fun _ _ => False, fun _ _ _ _ _ _ _ => Iff.rfl, U.Root_arr_neg b _ ?_⟩
    rintro ⟨z, hz, hr⟩
    exact (hr U.w0 (U.Rrefl _) z z hz U.w0 (U.Rrefl _)).mpr hz
  · obtain ⟨x, hx⟩ := U.adm_nonempty a
    exact ⟨x, hx _, U.Root_other x fun b h => ha ⟨b, h⟩⟩

/-- Functions with one domain whose roots agree have one codomain. -/
theorem MbkH_HR_arr (U : Univ) (a c d : Code U.Base) (f : U.El (.arr a c)) (g : U.El (.arr a d))
    (h : U.HR (.arr a c) (.arr a d) f g) : c = d := by
  obtain ⟨_, _, e, _⟩ := h
  rcases MbkH_Root_cases U _ f with h1 | ⟨b1, hb1, hs1⟩ <;>
    rcases MbkH_Root_cases U _ g with h2 | ⟨b2, hb2, hs2⟩
  · rw [h1, h2] at e
    exact (Code.arr.inj e).2
  · rw [h1] at e
    dsimp only at e
    rw [← e] at hs2
    have hab : a = b2 := (Code.arr.inj hb2).1
    subst hab
    simp only [Csz] at hs2
    omega
  · rw [h2] at e
    dsimp only at e
    rw [e] at hs1
    have hab : a = b1 := (Code.arr.inj hb1).1
    subst hab
    simp only [Csz] at hs1
    omega
  · exact (Code.arr.inj hb1).2.trans (Code.arr.inj hb2).2.symm

/-- Types each of whose items is identified, at the actual world, with an item of the other are
the same. -/
theorem MbkH_ext_eq (U : Univ) (a b : Code U.Base)
    (hsub : ∀ x : U.El a, U.rel a U.w0 x x → ∃ y : U.El b, U.HR a b x y)
    (hsup : ∀ y : U.El b, U.rel b U.w0 y y → ∃ x : U.El a, U.HR a b x y) : a = b := by
  obtain ⟨x0, hx0, ex0⟩ := MbkH_selfroot U a
  obtain ⟨y0, hy0, ey0⟩ := MbkH_selfroot U b
  obtain ⟨y, _, _, e1, _⟩ := hsub x0 hx0
  obtain ⟨x, _, _, e2, _⟩ := hsup y0 hy0
  rw [ex0] at e1
  dsimp only at e1
  rw [ey0] at e2
  dsimp only at e2
  have s2 := U.Root_sz a x
  rw [e2] at s2
  rcases MbkH_Root_cases U b y with h | ⟨c, hc, hs⟩
  · rw [h] at e1
    exact e1
  · rw [← e1] at hs
    subst hc
    simp only [Csz] at s2 hs
    omega

/-! ## Principles about `≈`, which is identity of types -/

theorem MbkH_Inj : MbkH.Valid Inj := by
  refine MbkH_Valid_of ?_
  refine (MbkH.holdsAt_tall _ _ _ _).mpr fun a _ => (MbkH.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (MbkH.holdsAt_tall _ _ _ _).mpr fun c _ => (MbkH.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MbkH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code Empty) = .arr b d := (MbkH.holdsAt_teq _ _ _ _ _).mp h
  exact (MbkH.holdsAt_conj _ _ _ _ _).mpr ⟨(MbkH.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).1,
    (MbkH.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).2⟩

theorem MbkH_Recovery : MbkH.Valid Recovery := by
  refine MbkH_Valid_of ?_
  refine (MbkH.holdsAt_tall _ _ _ _).mpr fun a _ => (MbkH.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (MbkH.holdsAt_tall _ _ _ _).mpr fun c _ => (MbkH.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MbkH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code Empty) = .arr b d :=
    (MbkH.holdsAt_teq _ _ _ _ _).mp ((MbkH.holdsAt_conj _ _ _ _ _).mp h).1
  exact (MbkH.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).2

theorem MbkH_NDTeq : MbkH.Valid NDTeq := by
  refine MbkH_Valid_of ?_
  refine (MbkH.holdsAt_tall _ _ _ _).mpr fun a _ => (MbkH.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MbkH.holdsAt_imp _ _ _ _ _).mpr fun hn => (MbkH.box_of MbkH_heq _ _ _ _).mpr fun v _ => ?_
  refine (MbkH.holdsAt_neg _ _ _ _).mpr fun ht => (MbkH.holdsAt_neg _ _ _ _).mp hn ?_
  have e : a = b := (MbkH.holdsAt_teq _ _ _ _ v).mp ht
  exact (MbkH.holdsAt_teq _ _ _ _ _).mpr e

/-- The same types exist at every world, so the Barcan formula for types holds. -/
theorem MbkH_TBF : ∀ χ, TBFSch χ → MbkH.Valid χ := by
  rintro _ ⟨φ, rfl⟩
  refine MbkH_Valid_of ?_
  refine (MbkH.holdsAt_imp _ _ _ _ _).mpr fun h => (MbkH.box_of MbkH_heq _ _ _ _).mpr fun v hv => ?_
  refine (MbkH.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  exact (MbkH.box_of MbkH_heq _ _ _ _).mp ((MbkH.holdsAt_tall _ _ _ _).mp h a trivial) v hv

/-! ## Ext≈ and Int≈ -/

theorem MbkH_sub {n : Nat} {Γ : Ctx n} (ρ : UBk.TEnv n) (env : UBk.Env Γ ρ) (a b : Code Empty)
    (h : MbkH.HoldsAt (subT : Fm (Γ.text.text)) (scons b (scons a ρ)) env UBk.w0) :
    ∀ x : UBk.El a, UBk.rel a UBk.w0 x x → ∃ y : UBk.El b, UBk.HR a b x y := by
  intro x hx
  obtain ⟨y, _, hxy⟩ := (MbkH.holdsAt_ex _ _ _ _ _).mp ((MbkH.holdsAt_all _ _ _ _ _).mp h x hx)
  exact ⟨y, ((MbkH.holdsAt_eqv _ _ _ _ _ _ _).mp hxy).1 rfl⟩

theorem MbkH_sup {n : Nat} {Γ : Ctx n} (ρ : UBk.TEnv n) (env : UBk.Env Γ ρ) (a b : Code Empty)
    (h : MbkH.HoldsAt (supT : Fm (Γ.text.text)) (scons b (scons a ρ)) env UBk.w0) :
    ∀ y : UBk.El b, UBk.rel b UBk.w0 y y → ∃ x : UBk.El a, UBk.HR a b x y := by
  intro y hy
  obtain ⟨x, _, hxy⟩ := (MbkH.holdsAt_ex _ _ _ _ _).mp ((MbkH.holdsAt_all _ _ _ _ _).mp h y hy)
  exact ⟨x, ((MbkH.holdsAt_eqv _ _ _ _ _ _ _).mp hxy).1 rfl⟩

theorem MbkH_ExtT : MbkH.Valid ExtT := by
  refine MbkH_Valid_of ?_
  refine (MbkH.holdsAt_tall _ _ _ _).mpr fun a _ => (MbkH.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MbkH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hc := (MbkH.holdsAt_conj _ _ _ _ _).mp h
  exact (MbkH.holdsAt_teq _ _ _ _ _).mpr (MbkH_ext_eq UBk a b (MbkH_sub _ _ a b hc.1) (MbkH_sup _ _ a b hc.2))

theorem MbkH_IntT : MbkH.Valid IntT := by
  refine MbkH_Valid_of ?_
  refine (MbkH.holdsAt_tall _ _ _ _).mpr fun a _ => (MbkH.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MbkH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hc := (MbkH.holdsAt_conj _ _ _ _ _).mp h
  have h1 := (MbkH.box_of MbkH_heq _ _ _ _).mp hc.1 UBk.w0 (UBk.Rrefl _)
  have h2 := (MbkH.box_of MbkH_heq _ _ _ _).mp hc.2 UBk.w0 (UBk.Rrefl _)
  exact (MbkH.holdsAt_teq _ _ _ _ _).mpr (MbkH_ext_eq UBk a b (MbkH_sub _ _ a b h1) (MbkH_sup _ _ a b h2))

/-! ## PCong holds -/

theorem MbkH_PCong : MbkH.Valid PCong := by
  refine MbkH_Valid_of ?_
  refine (MbkH.holdsAt_tall _ _ _ _).mpr fun a _ => (MbkH.holdsAt_tall _ _ _ _).mpr fun c _ =>
    (MbkH.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MbkH.holdsAt_all _ _ _ _ _).mpr fun f _ => (MbkH.holdsAt_all _ _ _ _ _).mpr fun g _ =>
    (MbkH.holdsAt_all _ _ _ _ _).mpr fun x hx => ?_
  refine (MbkH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have h1 : UBk.HR (.arr a c) (.arr a d) f g := ((MbkH.holdsAt_eqv _ _ _ _ _ _ _).mp h).1 rfl
  have ecd : c = d := MbkH_HR_arr UBk a c d f g h1
  subst ecd
  have h2 : UBk.rel (.arr a c) UBk.w0 f g := (UBk.HR_same UBk_all (.arr a c) f g).mp h1
  exact (MbkH.holdsAt_eqv _ _ _ _ _ _ _).mpr ((MbkH_heq _ _ _ _).mpr (h2 UBk.w0 (UBk.Rrefl _) x x hx))

/-! ## NI× fails -/

theorem MbkH_rel0 : UBk.rel .e UBk.w0 (0 : Fin 4) (0 : Fin 4) := Or.inl rfl

theorem MbkH_hcy0 (w : Fin 3) : UBk.rel (.arr .e .t) w (UBk.hcy .e (0 : Fin 4)) (UBk.hcy .e (0 : Fin 4)) :=
  UBk.rel_mono _ UBk.w0 w _ _ (UBk_all w) (UBk.hcy_resp .e (show Fin 4 from 0) (show Fin 4 from 0) MbkH_rel0 UBk_all)

/-- At the actual world, `0` is identified with its haecceity. -/
theorem MbkH_HR0 : UBk.HR .e (.arr .e .t) (0 : Fin 4) (UBk.hcy .e (0 : Fin 4)) :=
  ⟨MbkH_rel0, MbkH_hcy0 UBk.w0, UBk.RR_symm (UBk.Root_hcy UBk_all .e (show Fin 4 from 0) MbkH_rel0)⟩

/-- `0` is identified with its haecceity at the actual world, but not at world `1`. -/
theorem MbkH_not_NIX : ¬ MbkH.Valid NIX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MbkH.holdsAt_tall _ _ _ _).mp ((MbkH.holdsAt_tall _ _ _ _).mp h .e trivial) (.arr .e .t) trivial
  have h2 := (MbkH.holdsAt_all _ _ _ _ _).mp ((MbkH.holdsAt_all _ _ _ _ _).mp h1 (show Fin 4 from 0) MbkH_rel0)
    (UBk.hcy .e (0 : Fin 4)) (MbkH_hcy0 UBk.w0)
  have h3 := (MbkH.holdsAt_imp _ _ _ _ _).mp h2
    ((MbkH.holdsAt_eqv _ _ _ _ _ _ _).mpr ⟨fun _ => MbkH_HR0, fun hw => absurd rfl hw⟩)
  have h4 := (MbkH.box_of MbkH_heq _ _ _ _).mp h3 (1 : Fin 3) (Or.inr rfl)
  have hne : (1 : Fin 3) ≠ UBk.w0 := (by decide : (1 : Fin 3) ≠ 0)
  obtain ⟨e, _⟩ := ((MbkH.holdsAt_eqv _ _ _ _ _ _ _).mp h4).2 hne
  have e' : (Code.e : Code Empty) = .arr .e .t := e
  exact nomatch e'

/-! ## Functional Choice fails -/

/-- The chosen value: `2` for `0` and `2`, `3` for `1` and `3`. -/
def MbkH_g (x : Fin 4) : Fin 4 := if x.val % 2 = 0 then 2 else 3

/-- The relation holding everywhere at the other worlds, and at the actual world relating `x` just
to `g x`. -/
def MbkH_R : UBk.El (.arr .e (.arr .e .t)) := fun x y w => w ≠ (0 : Fin 3) ∨ y = MbkH_g x

theorem MbkH_R_adm : UBk.rel (.arr .e (.arr .e .t)) UBk.w0 MbkH_R MbkH_R := by
  intro v hv x x' hx u hu y y' hy s hs
  by_cases hs0 : s = (0 : Fin 3)
  · subst hs0
    have hu' : u = (0 : Fin 3) := hs.elim id id
    subst hu'
    have hv' : v = (0 : Fin 3) := hu.elim id id
    subst hv'
    have ex : x = x' := hx.elim id (fun h => absurd h.1 (by decide))
    have ey : y = y' := hy.elim id (fun h => absurd h.1 (by decide))
    subst ex; subst ey
    exact Iff.rfl
  · exact ⟨fun _ => Or.inl hs0, fun _ => Or.inl hs0⟩

/-- Every entity is related to something, but a choice function would send `0` and `1`, which are
identical at world `2`, to `2` and `3`, which are not; so no item at the actual world chooses. -/
theorem MbkH_not_Choice : ¬ MbkH.Valid Choice := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MbkH.holdsAt_tall _ _ _ _).mp h .e trivial
  have h2 := (MbkH.holdsAt_tall _ _ _ _).mp h1 .e trivial
  have h3 := (MbkH.holdsAt_all _ _ _ _ _).mp h2 MbkH_R MbkH_R_adm
  have h4 := (MbkH.holdsAt_imp _ _ _ _ _).mp h3 ((MbkH.holdsAt_all _ _ _ _ _).mpr fun x _ =>
    (MbkH.holdsAt_ex _ _ _ _ _).mpr ⟨MbkH_g x, Or.inl rfl, Or.inr rfl⟩)
  obtain ⟨f, hf, hfx⟩ := (MbkH.holdsAt_ex _ _ _ _ _).mp h4
  have hall := (MbkH.holdsAt_all _ _ _ _ _).mp hfx
  have f0 : (f : Fin 4 → Fin 4) (0 : Fin 4) = MbkH_g (0 : Fin 4) :=
    (show (0 : Fin 3) ≠ (0 : Fin 3) ∨ (f : Fin 4 → Fin 4) (0 : Fin 4) = MbkH_g (0 : Fin 4) from
      hall (0 : Fin 4) (Or.inl rfl)).resolve_left (fun h => h rfl)
  have f1 : (f : Fin 4 → Fin 4) (1 : Fin 4) = MbkH_g (1 : Fin 4) :=
    (show (0 : Fin 3) ≠ (0 : Fin 3) ∨ (f : Fin 4 → Fin 4) (1 : Fin 4) = MbkH_g (1 : Fin 4) from
      hall (1 : Fin 4) (Or.inl rfl)).resolve_left (fun h => h rfl)
  have hr : UBk.re (2 : Fin 3) ((f : Fin 4 → Fin 4) (0 : Fin 4)) ((f : Fin 4 → Fin 4) (1 : Fin 4)) :=
    hf (2 : Fin 3) (Or.inr rfl) (0 : Fin 4) (1 : Fin 4) (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)
  rw [f0, f1] at hr
  rcases hr with e | ⟨_, ⟨e, _⟩ | ⟨e, _⟩⟩
  · exact absurd e (by decide)
  · exact absurd e (by decide)
  · exact absurd e (by decide)

end Kr
end PIF
