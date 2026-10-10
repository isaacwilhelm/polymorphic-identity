import PIBF

/-!
# The rest of the profile of `𝔐_k,ch,h`

The model `MchH` of `lean/PIModalX.lean`: the Kripke model `𝔐_k,ch` (two worlds; the actual world
`true` sees both, the other world `false` sees only itself; four entities, with `0` and `1`
identical at `false`), with haecceities added at the actual world. At the actual world, items are
identified just in case they have the same root, got by stripping off haecceities; at the other
world, items are identified just in case they are of one type and identical there. `≈` is identity
of types at both worlds, and every type exists at both worlds.

* Inj≈, Recovery, ND≈ and TBF hold, since `≈` is identity of types and the types are the same at
  both worlds.
* PCong holds: functions with one domain and different codomains never have the same root, so
  identified functions with one domain are of one type, and identical.
* Ext≈ and Int≈ hold: every type has an item which is its own root, and roots never lie at larger
  types; so types each of whose items is identified with an item of the other are the same.
* BF holds: each item at the other world is identical there to an item at the actual world.
* PExt fails: the constant functions to `0` and to the haecceity of `0` agree pointwise up to
  identity, but are not identified, since their roots are of different types.
* NI× fails: `0` is identified with its haecceity at the actual world, but not at the other world.
-/
set_option autoImplicit false

namespace PIF
namespace Kr
open Tm

theorem MchH_Valid_of {φ : Fm Ctx.nil} (h : MchH.HoldsAt φ (fun i => i.elim0) () UCh.w0) : MchH.Valid φ := by
  intro ρ _ env _
  have e1 : ρ = fun i => i.elim0 := funext fun i => i.elim0
  subst e1
  exact h

/-! ## Roots -/

/-- A root is the item itself, or (for an item of `β → t`) lies at a type no larger than `β`. -/
theorem MchH_Root_cases (U : Univ) (a : Code U.Base) (x : U.El a) :
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
theorem MchH_selfroot (U : Univ) (a : Code U.Base) : ∃ x : U.El a, U.rel a U.w0 x x ∧ U.Root a x = ⟨a, x⟩ := by
  by_cases ha : ∃ b, a = .arr b .t
  · obtain ⟨b, rfl⟩ := ha
    refine ⟨fun _ _ => False, fun _ _ _ _ _ _ _ => Iff.rfl, U.Root_arr_neg b _ ?_⟩
    rintro ⟨z, hz, hr⟩
    exact (hr U.w0 (U.Rrefl _) z z hz U.w0 (U.Rrefl _)).mpr hz
  · obtain ⟨x, hx⟩ := U.adm_nonempty a
    exact ⟨x, hx _, U.Root_other x fun b h => ha ⟨b, h⟩⟩

/-- Functions with one domain whose roots agree have one codomain. -/
theorem MchH_HR_arr (U : Univ) (a c d : Code U.Base) (f : U.El (.arr a c)) (g : U.El (.arr a d))
    (h : U.HR (.arr a c) (.arr a d) f g) : c = d := by
  obtain ⟨_, _, e, _⟩ := h
  rcases MchH_Root_cases U _ f with h1 | ⟨b1, hb1, hs1⟩ <;>
    rcases MchH_Root_cases U _ g with h2 | ⟨b2, hb2, hs2⟩
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
theorem MchH_ext_eq (U : Univ) (a b : Code U.Base)
    (hsub : ∀ x : U.El a, U.rel a U.w0 x x → ∃ y : U.El b, U.HR a b x y)
    (hsup : ∀ y : U.El b, U.rel b U.w0 y y → ∃ x : U.El a, U.HR a b x y) : a = b := by
  obtain ⟨x0, hx0, ex0⟩ := MchH_selfroot U a
  obtain ⟨y0, hy0, ey0⟩ := MchH_selfroot U b
  obtain ⟨y, _, _, e1, _⟩ := hsub x0 hx0
  obtain ⟨x, _, _, e2, _⟩ := hsup y0 hy0
  rw [ex0] at e1
  dsimp only at e1
  rw [ey0] at e2
  dsimp only at e2
  have s2 := U.Root_sz a x
  rw [e2] at s2
  rcases MchH_Root_cases U b y with h | ⟨c, hc, hs⟩
  · rw [h] at e1
    exact e1
  · rw [← e1] at hs
    subst hc
    simp only [Csz] at s2 hs
    omega

/-! ## Principles about `≈`, which is identity of types -/

theorem MchH_Inj : MchH.Valid Inj := by
  refine MchH_Valid_of ?_
  refine (MchH.holdsAt_tall _ _ _ _).mpr fun a _ => (MchH.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (MchH.holdsAt_tall _ _ _ _).mpr fun c _ => (MchH.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MchH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code Empty) = .arr b d := (MchH.holdsAt_teq _ _ _ _ _).mp h
  exact (MchH.holdsAt_conj _ _ _ _ _).mpr ⟨(MchH.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).1,
    (MchH.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).2⟩

theorem MchH_Recovery : MchH.Valid Recovery := by
  refine MchH_Valid_of ?_
  refine (MchH.holdsAt_tall _ _ _ _).mpr fun a _ => (MchH.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (MchH.holdsAt_tall _ _ _ _).mpr fun c _ => (MchH.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MchH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code Empty) = .arr b d :=
    (MchH.holdsAt_teq _ _ _ _ _).mp ((MchH.holdsAt_conj _ _ _ _ _).mp h).1
  exact (MchH.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).2

theorem MchH_NDTeq : MchH.Valid NDTeq := by
  refine MchH_Valid_of ?_
  refine (MchH.holdsAt_tall _ _ _ _).mpr fun a _ => (MchH.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MchH.holdsAt_imp _ _ _ _ _).mpr fun hn => (MchH.box_of MchH_heq _ _ _ _).mpr fun v _ => ?_
  refine (MchH.holdsAt_neg _ _ _ _).mpr fun ht => (MchH.holdsAt_neg _ _ _ _).mp hn ?_
  have e : a = b := (MchH.holdsAt_teq _ _ _ _ v).mp ht
  exact (MchH.holdsAt_teq _ _ _ _ _).mpr e

/-- The same types exist at both worlds, so the Barcan formula for types holds. -/
theorem MchH_TBF : ∀ χ, TBFSch χ → MchH.Valid χ := by
  rintro _ ⟨φ, rfl⟩
  refine MchH_Valid_of ?_
  refine (MchH.holdsAt_imp _ _ _ _ _).mpr fun h => (MchH.box_of MchH_heq _ _ _ _).mpr fun v hv => ?_
  refine (MchH.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  exact (MchH.box_of MchH_heq _ _ _ _).mp ((MchH.holdsAt_tall _ _ _ _).mp h a trivial) v hv

/-! ## Ext≈ and Int≈ -/

theorem MchH_sub {n : Nat} {Γ : Ctx n} (ρ : UCh.TEnv n) (env : UCh.Env Γ ρ) (a b : Code Empty)
    (h : MchH.HoldsAt (subT : Fm (Γ.text.text)) (scons b (scons a ρ)) env true) :
    ∀ x : UCh.El a, UCh.rel a true x x → ∃ y : UCh.El b, UCh.HR a b x y := by
  intro x hx
  obtain ⟨y, _, hxy⟩ := (MchH.holdsAt_ex _ _ _ _ _).mp ((MchH.holdsAt_all _ _ _ _ _).mp h x hx)
  exact ⟨y, ((MchH.holdsAt_eqv _ _ _ _ _ _ _).mp hxy).1 rfl⟩

theorem MchH_sup {n : Nat} {Γ : Ctx n} (ρ : UCh.TEnv n) (env : UCh.Env Γ ρ) (a b : Code Empty)
    (h : MchH.HoldsAt (supT : Fm (Γ.text.text)) (scons b (scons a ρ)) env true) :
    ∀ y : UCh.El b, UCh.rel b true y y → ∃ x : UCh.El a, UCh.HR a b x y := by
  intro y hy
  obtain ⟨x, _, hxy⟩ := (MchH.holdsAt_ex _ _ _ _ _).mp ((MchH.holdsAt_all _ _ _ _ _).mp h y hy)
  exact ⟨x, ((MchH.holdsAt_eqv _ _ _ _ _ _ _).mp hxy).1 rfl⟩

theorem MchH_ExtT : MchH.Valid ExtT := by
  refine MchH_Valid_of ?_
  refine (MchH.holdsAt_tall _ _ _ _).mpr fun a _ => (MchH.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MchH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hc := (MchH.holdsAt_conj _ _ _ _ _).mp h
  exact (MchH.holdsAt_teq _ _ _ _ _).mpr (MchH_ext_eq UCh a b (MchH_sub _ _ a b hc.1) (MchH_sup _ _ a b hc.2))

theorem MchH_IntT : MchH.Valid IntT := by
  refine MchH_Valid_of ?_
  refine (MchH.holdsAt_tall _ _ _ _).mpr fun a _ => (MchH.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MchH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hc := (MchH.holdsAt_conj _ _ _ _ _).mp h
  have h1 := (MchH.box_of MchH_heq _ _ _ _).mp hc.1 true (Or.inl rfl)
  have h2 := (MchH.box_of MchH_heq _ _ _ _).mp hc.2 true (Or.inl rfl)
  exact (MchH.holdsAt_teq _ _ _ _ _).mpr (MchH_ext_eq UCh a b (MchH_sub _ _ a b h1) (MchH_sup _ _ a b h2))

/-! ## PCong holds, PExt fails -/

theorem MchH_PCong : MchH.Valid PCong := by
  refine MchH_Valid_of ?_
  refine (MchH.holdsAt_tall _ _ _ _).mpr fun a _ => (MchH.holdsAt_tall _ _ _ _).mpr fun c _ =>
    (MchH.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MchH.holdsAt_all _ _ _ _ _).mpr fun f _ => (MchH.holdsAt_all _ _ _ _ _).mpr fun g _ =>
    (MchH.holdsAt_all _ _ _ _ _).mpr fun x hx => ?_
  refine (MchH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have h1 : UCh.HR (.arr a c) (.arr a d) f g := ((MchH.holdsAt_eqv _ _ _ _ _ _ _).mp h).1 rfl
  have ecd : c = d := MchH_HR_arr UCh a c d f g h1
  subst ecd
  have h2 : UCh.rel (.arr a c) true f g := (UCh.HR_same UCh_all (.arr a c) f g).mp h1
  exact (MchH.holdsAt_eqv _ _ _ _ _ _ _).mpr ((MchH_heq _ _ _ _).mpr (h2 true (Or.inl rfl) x x hx))

theorem MchH_rel0 : UCh.rel .e true (0 : Fin 4) (0 : Fin 4) := Or.inl rfl

theorem MchH_hcy0 (w : Bool) : UCh.rel (.arr .e .t) w (UCh.hcy .e (0 : Fin 4)) (UCh.hcy .e (0 : Fin 4)) :=
  UCh.rel_mono _ true w _ _ (UCh_all w) (UCh.hcy_resp .e (show Fin 4 from 0) (show Fin 4 from 0) MchH_rel0 UCh_all)

/-- At the actual world, `0` is identified with its haecceity. -/
theorem MchH_HR0 : UCh.HR .e (.arr .e .t) (0 : Fin 4) (UCh.hcy .e (0 : Fin 4)) :=
  ⟨MchH_rel0, MchH_hcy0 true, UCh.RR_symm (UCh.Root_hcy UCh_all .e (show Fin 4 from 0) MchH_rel0)⟩

/-- The constant functions to `0` and to the haecceity of `0` agree pointwise up to identity, but
their roots are of different types. -/
theorem MchH_not_PExt : ¬ MchH.Valid PExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MchH.holdsAt_tall _ _ _ _).mp ((MchH.holdsAt_tall _ _ _ _).mp
    ((MchH.holdsAt_tall _ _ _ _).mp h .e trivial) .e trivial) (.arr .e .t) trivial
  have hf : UCh.rel (.arr .e .e) true (fun _ => (0 : Fin 4)) (fun _ => (0 : Fin 4)) :=
    fun _ _ _ _ _ => Or.inl rfl
  have hg : UCh.rel (.arr .e (.arr .e .t)) true (fun _ => UCh.hcy .e (0 : Fin 4))
      (fun _ => UCh.hcy .e (0 : Fin 4)) := fun v _ _ _ _ => MchH_hcy0 v
  have h2 := (MchH.holdsAt_all _ _ _ _ _).mp ((MchH.holdsAt_all _ _ _ _ _).mp h1 _ hf) _ hg
  have h3 := (MchH.holdsAt_imp _ _ _ _ _).mp h2 ((MchH.holdsAt_all _ _ _ _ _).mpr fun _ _ =>
    (MchH.holdsAt_eqv _ _ _ _ _ _ _).mpr ⟨fun _ => MchH_HR0, fun hw => absurd rfl hw⟩)
  have h4 : UCh.HR (.arr .e .e) (.arr .e (.arr .e .t)) (fun _ => (0 : Fin 4)) (fun _ => UCh.hcy .e (0 : Fin 4)) :=
    ((MchH.holdsAt_eqv _ _ _ _ _ _ _).mp h3).1 rfl
  obtain ⟨_, _, e, _⟩ := h4
  have e' : (Code.arr .e .e : Code Empty) = .arr .e (.arr .e .t) := e
  exact nomatch (Code.arr.inj e').2

/-! ## NI× fails -/

/-- `0` is identified with its haecceity at the actual world, but not at the other world. -/
theorem MchH_not_NIX : ¬ MchH.Valid NIX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MchH.holdsAt_tall _ _ _ _).mp ((MchH.holdsAt_tall _ _ _ _).mp h .e trivial) (.arr .e .t) trivial
  have h2 := (MchH.holdsAt_all _ _ _ _ _).mp ((MchH.holdsAt_all _ _ _ _ _).mp h1 (show Fin 4 from 0) MchH_rel0)
    (UCh.hcy .e (0 : Fin 4)) (MchH_hcy0 true)
  have h3 := (MchH.holdsAt_imp _ _ _ _ _).mp h2
    ((MchH.holdsAt_eqv _ _ _ _ _ _ _).mpr ⟨fun _ => MchH_HR0, fun hw => absurd rfl hw⟩)
  have h4 := (MchH.box_of MchH_heq _ _ _ _).mp h3 false (Or.inr rfl)
  obtain ⟨e, _⟩ := ((MchH.holdsAt_eqv _ _ _ _ _ _ _).mp h4).2 (fun h => Bool.noConfusion h)
  have e' : (Code.e : Code Empty) = .arr .e .t := e
  exact nomatch e'

/-! ## The Barcan formula holds -/

/-- Each item at the other world is identical there to an item at the actual world, and each
property at the actual world respects identity at the other world. -/
theorem MchH_BF : MchH.Valid BF := by
  refine MchH_Valid_of ?_
  refine (MchH.holdsAt_tall _ _ _ _).mpr fun a _ => (MchH.holdsAt_all _ _ _ _ _).mpr fun F hF => ?_
  refine (MchH.holdsAt_imp _ _ _ _ _).mpr fun h => (MchH.box_of MchH_heq _ _ _ _).mpr fun v _ => ?_
  have hall := (MchH.holdsAt_all _ _ _ _ _).mp h
  cases v with
  | true =>
    refine (MchH.holdsAt_all _ _ _ _ _).mpr fun x hx => ?_
    exact (MchH.box_of MchH_heq _ _ _ _).mp (hall x hx) true (Or.inl rfl)
  | false =>
    refine (MchH.holdsAt_all _ _ _ _ _).mpr fun x hx => ?_
    obtain ⟨z, hz, hzx⟩ := UCh.dense true false (fun _ _ => Or.inr rfl) (fun _ _ => Or.inr rfl) a x hx
    have h1 := (MchH.box_of MchH_heq _ _ _ _).mp (hall z hz) false (Or.inr rfl)
    have hF' : UCh.rel (.arr a .t) true F F := hF
    exact (hF' false (Or.inr rfl) z x hzx false (Or.inr rfl)).mp h1

end Kr
end PIF
