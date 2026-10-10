import PIBF
set_option autoImplicit false

/-!
# More about `𝔐_k,nd,h`

`𝔐_k,nd,h` is `𝔐_k,nd` with haecceities added at the actual world `true`. Two worlds: `true` sees
both, `false` sees only itself. At the actual world items are identified just in case they have the
same root (got by stripping off haecceities); at the other world identity is as in `𝔐_k,nd`.

* PCong holds: at the actual world, functions with one domain are identified only if their
  codomains are the same type.
* PExt fails: `λx.x : e → e` and `λx.λy.(y ≡ x) : e → (e → t)` agree pointwise, but are not identified.
* Inj≈ and Recovery hold, since `≈` is as in `𝔐_k,nd`.
* Ext≈ and Int≈ hold: each type has an item which is its own root, so mutual covering forces
  sizes, and then types, to agree.
* NI× fails (`x ≡ λy.(y ≡ x)` at the actual world, but not at the other world), and so does ND×
  (an entity and its copy in `d` are identified at the other world only).
* The Barcan formula holds (each item at the other world is identical there to one at the actual
  world), but Functional Choice fails.
-/

namespace PIF
namespace Kr
open Tm

theorem MndH_Valid_of {φ : Fm Ctx.nil} (h : MndH.HoldsAt φ (fun i => i.elim0) () true) : MndH.Valid φ := by
  intro ρ _ env _
  have e1 : ρ = fun i => i.elim0 := funext fun i => i.elim0
  subst e1
  exact h

/-! ## Inj≈ and Recovery: `≈` is as in `𝔐_k,nd` -/

theorem MndH_Inj : MndH.Valid Inj := by
  refine MndH_Valid_of ?_
  refine (MndH.holdsAt_tall _ _ _ _).mpr fun a _ => (MndH.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (MndH.holdsAt_tall _ _ _ _).mpr fun c _ => (MndH.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MndH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code Unit) = .arr b d := ((MndH.holdsAt_teq _ _ _ _ _).mp h).1 rfl
  exact (MndH.holdsAt_conj _ _ _ _ _).mpr ⟨(MndH.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => (Code.arr.inj e).1,
    congrArg img (Code.arr.inj e).1⟩, (MndH.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => (Code.arr.inj e).2,
    congrArg img (Code.arr.inj e).2⟩⟩

theorem MndH_Recovery : MndH.Valid Recovery := by
  refine MndH_Valid_of ?_
  refine (MndH.holdsAt_tall _ _ _ _).mpr fun a _ => (MndH.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (MndH.holdsAt_tall _ _ _ _).mpr fun c _ => (MndH.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MndH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code Unit) = .arr b d :=
    ((MndH.holdsAt_teq _ _ _ _ _).mp ((MndH.holdsAt_conj _ _ _ _ _).mp h).1).1 rfl
  exact (MndH.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => (Code.arr.inj e).2, congrArg img (Code.arr.inj e).2⟩

/-! ## Roots -/

/-- The root of a function is the function itself, or (for a haecceity) no bigger than its domain. -/
theorem MndH_root_arr (a c : Code UND.Base) (f : UND.El (.arr a c)) :
    (UND.Root (.arr a c) f).1 = .arr a c ∨ (c = .t ∧ Csz (UND.Root (.arr a c) f).1 ≤ Csz a) := by
  cases c with
  | t =>
    by_cases h : ∃ z, UND.rel a UND.w0 z z ∧ UND.rel (.arr a .t) UND.w0 f (UND.hcy a z)
    · rw [UND.Root_arr_pos a f h]; exact Or.inr ⟨rfl, UND.Root_sz a _⟩
    · rw [UND.Root_arr_neg a f h]; exact Or.inl rfl
  | e => exact Or.inl rfl
  | base _ => exact Or.inl rfl
  | arr _ _ => exact Or.inl rfl

/-- Each root is of the item's own type, or of a smaller type. -/
theorem MndH_root_cases (a : Code UND.Base) (x : UND.El a) :
    (UND.Root a x).1 = a ∨ Csz (UND.Root a x).1 < Csz a := by
  cases a with
  | arr a c =>
    rcases MndH_root_arr a c x with h | ⟨_, h⟩
    · exact Or.inl h
    · have s : Csz (Code.arr a c) = Csz a + Csz c + 1 := rfl
      exact Or.inr (by omega)
  | e => exact Or.inl rfl
  | t => exact Or.inl rfl
  | base _ => exact Or.inl rfl

/-- At the actual world, functions with one domain are identified only if their codomains agree. -/
theorem MndH_HR_arr {a c d : Code UND.Base} {f : UND.El (.arr a c)} {g : UND.El (.arr a d)}
    (h : UND.HR (.arr a c) (.arr a d) f g) : c = d := by
  obtain ⟨_, _, e, _⟩ := h
  have e' := congrArg Csz e
  have s1 : Csz (Code.arr a c) = Csz a + Csz c + 1 := rfl
  have s2 : Csz (Code.arr a d) = Csz a + Csz d + 1 := rfl
  rcases MndH_root_arr a c f with h1 | ⟨h1, h2⟩ <;> rcases MndH_root_arr a d g with k1 | ⟨k1, k2⟩
  · rw [h1, k1] at e; exact (Code.arr.inj e).2
  · rw [h1] at e'; omega
  · rw [k1] at e'; omega
  · exact h1.trans k1.symm

theorem MndH_pcong {a c d : Code UND.Base} {f : UND.El (.arr a c)} {g : UND.El (.arr a d)} {x : UND.El a}
    (hx : UND.rel a true x x) (h : UND.HR (.arr a c) (.arr a d) f g) : UND.HR c d (f x) (g x) := by
  have e := MndH_HR_arr h
  subst e
  exact (UND.HR_same UND_all _ _ _).mpr ((UND.HR_same UND_all _ f g).mp h true (UND.Rrefl true) x x hx)

/-! ## PCong holds -/

theorem MndH_PCong : MndH.Valid PCong := by
  refine MndH_Valid_of ?_
  refine (MndH.holdsAt_tall _ _ _ _).mpr fun a _ => (MndH.holdsAt_tall _ _ _ _).mpr fun c _ =>
    (MndH.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MndH.holdsAt_all _ _ _ _ _).mpr fun f _ => (MndH.holdsAt_all _ _ _ _ _).mpr fun g _ =>
    (MndH.holdsAt_all _ _ _ _ _).mpr fun x hx => ?_
  refine (MndH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have h1 : UND.HR (.arr a c) (.arr a d) f g := ((MndH.holdsAt_eqv _ _ _ _ _ _ _).mp h).1 rfl
  have h2 : UND.HR c d (f x) (g x) := MndH_pcong hx h1
  exact (MndH.holdsAt_eqv _ _ _ _ _ _ _).mpr ⟨fun _ => h2, fun hw => absurd rfl hw⟩

/-! ## Ext≈ and Int≈ hold -/

/-- Two items of each type, items at every world, which are not identical at the actual world. -/
theorem MndH_two : ∀ a : Code UND.Base, ∃ x y : UND.El a,
    (∀ w, UND.rel a w x x) ∧ (∀ w, UND.rel a w y y) ∧ ¬ UND.rel a true x y
  | .e => ⟨true, false, fun _ => rfl, fun _ => rfl, fun h => (by decide : ¬ (true = false)) h⟩
  | .base _ => ⟨true, false, fun _ => rfl, fun _ => rfl, fun h => (by decide : ¬ (true = false)) h⟩
  | .t => ⟨fun _ => True, fun _ => False, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun h => (h true (UND.Rrefl true)).mp trivial⟩
  | .arr a c => by
    obtain ⟨x, y, hx, hy, hxy⟩ := MndH_two c
    obtain ⟨z, hz⟩ := UND.adm_nonempty a
    exact ⟨fun _ => x, fun _ => y, fun _ v _ _ _ _ => hx v, fun _ v _ _ _ _ => hy v,
      fun h => hxy (h true (UND.Rrefl true) z z (hz true))⟩

/-- Each type has an item, at the actual world, which is its own root. -/
theorem MndH_root_self (a : Code UND.Base) : ∃ x : UND.El a, UND.rel a true x x ∧ (UND.Root a x).1 = a := by
  cases a with
  | arr a c =>
    cases c with
    | t =>
      refine ⟨fun _ _ => True, fun _ _ _ _ _ _ _ => Iff.rfl, ?_⟩
      have hn : ¬ ∃ z, UND.rel a UND.w0 z z ∧
          UND.rel (.arr a .t) UND.w0 (fun _ _ => True) (UND.hcy a z) := by
        rintro ⟨z, _, hz⟩
        obtain ⟨x, y, hx, hy, hxy⟩ := MndH_two a
        have h1 : UND.rel a true x z :=
          (hz true (UND.Rrefl true) x x (hx true) true (UND.Rrefl true)).mp trivial
        have h2 : UND.rel a true y z :=
          (hz true (UND.Rrefl true) y y (hy true) true (UND.Rrefl true)).mp trivial
        exact hxy (UND.rel_trans a true _ _ _ h1 (UND.rel_symm a true _ _ h2))
      exact congrArg Sigma.fst (UND.Root_arr_neg a _ hn)
    | e => obtain ⟨x, hx⟩ := UND.adm_nonempty (.arr a .e); exact ⟨x, hx true, rfl⟩
    | base u => obtain ⟨x, hx⟩ := UND.adm_nonempty (.arr a (.base u)); exact ⟨x, hx true, rfl⟩
    | arr c d => obtain ⟨x, hx⟩ := UND.adm_nonempty (.arr a (.arr c d)); exact ⟨x, hx true, rfl⟩
  | e => obtain ⟨x, hx⟩ := UND.adm_nonempty .e; exact ⟨x, hx true, rfl⟩
  | t => obtain ⟨x, hx⟩ := UND.adm_nonempty .t; exact ⟨x, hx true, rfl⟩
  | base u => obtain ⟨x, hx⟩ := UND.adm_nonempty (.base u); exact ⟨x, hx true, rfl⟩

theorem MndH_sub_cases {n : Nat} {Γ : Ctx n} (ρ : UND.TEnv n) (env : UND.Env Γ ρ) (a b : Code UND.Base)
    (h : MndH.HoldsAt (subT : Fm (Γ.text.text)) (scons b (scons a ρ)) env true) : a = b ∨ Csz a < Csz b := by
  obtain ⟨x, hx, hxr⟩ := MndH_root_self a
  obtain ⟨y, _, hy⟩ := (MndH.holdsAt_ex _ _ _ _ _).mp ((MndH.holdsAt_all _ _ _ _ _).mp h x hx)
  have hr : UND.HR a b x y := ((MndH.holdsAt_eqv _ _ _ _ _ _ _).mp hy).1 rfl
  obtain ⟨_, _, e, _⟩ := hr
  rw [hxr] at e
  rcases MndH_root_cases b y with h1 | h1
  · exact Or.inl (e.trans h1)
  · exact Or.inr (by rw [e]; exact h1)

theorem MndH_sup_cases {n : Nat} {Γ : Ctx n} (ρ : UND.TEnv n) (env : UND.Env Γ ρ) (a b : Code UND.Base)
    (h : MndH.HoldsAt (supT : Fm (Γ.text.text)) (scons b (scons a ρ)) env true) : b = a ∨ Csz b < Csz a := by
  obtain ⟨y, hy, hyr⟩ := MndH_root_self b
  obtain ⟨x, _, hx⟩ := (MndH.holdsAt_ex _ _ _ _ _).mp ((MndH.holdsAt_all _ _ _ _ _).mp h y hy)
  have hr : UND.HR a b x y := ((MndH.holdsAt_eqv _ _ _ _ _ _ _).mp hx).1 rfl
  obtain ⟨e, _⟩ := UND.RR_symm hr.2.2
  rw [hyr] at e
  rcases MndH_root_cases a x with h1 | h1
  · exact Or.inl (e.trans h1)
  · exact Or.inr (by rw [e]; exact h1)

theorem MndH_eq_of {a b : Code UND.Base} (h1 : a = b ∨ Csz a < Csz b) (h2 : b = a ∨ Csz b < Csz a) : a = b := by
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact h2.symm
    · omega

theorem MndH_ExtT : MndH.Valid ExtT := by
  refine MndH_Valid_of ?_
  refine (MndH.holdsAt_tall _ _ _ _).mpr fun a _ => (MndH.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MndH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hc := (MndH.holdsAt_conj _ _ _ _ _).mp h
  have e := MndH_eq_of (MndH_sub_cases _ _ a b hc.1) (MndH_sup_cases _ _ a b hc.2)
  exact (MndH.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => e, congrArg img e⟩

theorem MndH_IntT : MndH.Valid IntT := by
  refine MndH_Valid_of ?_
  refine (MndH.holdsAt_tall _ _ _ _).mpr fun a _ => (MndH.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MndH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hc := (MndH.holdsAt_conj _ _ _ _ _).mp h
  have h1 := (MndH.box_of MndH_heq _ _ _ _).mp hc.1 true (UND.Rrefl true)
  have h2 := (MndH.box_of MndH_heq _ _ _ _).mp hc.2 true (UND.Rrefl true)
  have e := MndH_eq_of (MndH_sub_cases _ _ a b h1) (MndH_sup_cases _ _ a b h2)
  exact (MndH.holdsAt_teq _ _ _ _ _).mpr ⟨fun _ => e, congrArg img e⟩

/-! ## NI×, ND× and PExt fail -/

theorem MndH_hcy_adm (x : Bool) : UND.rel (.arr .e .t) true (UND.hcy .e x) (UND.hcy .e x) :=
  UND.hcy_resp .e x x rfl UND_all

theorem MndH_HR_hcy (x : Bool) : UND.HR .e (.arr .e .t) x (UND.hcy .e x) :=
  ⟨rfl, MndH_hcy_adm x, UND.RR_symm (UND.Root_hcy UND_all .e x rfl)⟩

theorem MndH_hcyF_adm : UND.rel (.arr .e (.arr .e .t)) true (UND.hcy .e) (UND.hcy .e) := by
  intro v hv x x' hxx'
  have e : x = x' := hxx'
  subst e
  exact UND.rel_mono (.arr .e .t) true v _ _ hv (MndH_hcy_adm x)

/-- An entity is identified with its haecceity at the actual world, but not at the other world. -/
theorem MndH_not_NIX : ¬ MndH.Valid NIX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MndH.holdsAt_tall _ _ _ _).mp ((MndH.holdsAt_tall _ _ _ _).mp h .e trivial) (.arr .e .t) trivial
  have h2 := (MndH.holdsAt_all _ _ _ _ _).mp ((MndH.holdsAt_all _ _ _ _ _).mp h1 (show Bool from true) rfl)
    (UND.hcy .e true) (MndH_hcy_adm true)
  have h3 := (MndH.holdsAt_imp _ _ _ _ _).mp h2 ((MndH.holdsAt_eqv _ _ _ _ _ _ _).mpr
    ⟨fun _ => MndH_HR_hcy true, fun hw => absurd rfl hw⟩)
  have h4 := (MndH.box_of MndH_heq _ _ _ _).mp h3 false (Or.inl rfl)
  have h5 := ((MndH.holdsAt_eqv _ _ _ _ _ _ _).mp h4).2 Bool.false_ne_true
  have e : (Code.e : Code Unit) = .arr .e .t := h5.2.1
  exact absurd e (by decide)

/-- An entity and its copy in `d` are distinct at the actual world, but identified at the other. -/
theorem MndH_not_NDX : ¬ MndH.Valid NDX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MndH.holdsAt_tall _ _ _ _).mp ((MndH.holdsAt_tall _ _ _ _).mp h .e trivial) (.base ()) trivial
  have h2 := (MndH.holdsAt_all _ _ _ _ _).mp ((MndH.holdsAt_all _ _ _ _ _).mp h1 (show Bool from true) rfl)
    (show Bool from true) rfl
  have h3 := (MndH.holdsAt_imp _ _ _ _ _).mp h2 ((MndH.holdsAt_neg _ _ _ _).mpr fun he => by
    obtain ⟨_, _, e, _⟩ := ((MndH.holdsAt_eqv _ _ _ _ _ _ _).mp he).1 rfl
    have e' : (Code.e : Code Unit) = .base () := e
    exact absurd e' (by decide))
  have h4 := (MndH.box_of MndH_heq _ _ _ _).mp h3 false (Or.inl rfl)
  exact (MndH.holdsAt_neg _ _ _ _).mp h4 ((MndH.holdsAt_eqv _ _ _ _ _ _ _).mpr
    ⟨fun hw => absurd hw Bool.false_ne_true, fun _ => ⟨fun hw => absurd hw Bool.false_ne_true, rfl, rfl⟩⟩)

/-- `λx.x : e → e` and `λx.λy.(y ≡ x) : e → (e → t)` agree pointwise, but are not identified. -/
theorem MndH_not_PExt : ¬ MndH.Valid PExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MndH.holdsAt_tall _ _ _ _).mp ((MndH.holdsAt_tall _ _ _ _).mp
    ((MndH.holdsAt_tall _ _ _ _).mp h .e trivial) .e trivial) (.arr .e .t) trivial
  have h2 := (MndH.holdsAt_all _ _ _ _ _).mp ((MndH.holdsAt_all _ _ _ _ _).mp h1
    (fun x : Bool => x) (fun _ _ _ _ hxy => hxy)) (UND.hcy .e) MndH_hcyF_adm
  have h3 := (MndH.holdsAt_imp _ _ _ _ _).mp h2 ((MndH.holdsAt_all _ _ _ _ _).mpr fun x _ =>
    (MndH.holdsAt_eqv _ _ _ _ _ _ _).mpr ⟨fun _ => MndH_HR_hcy x, fun hw => absurd rfl hw⟩)
  obtain ⟨_, _, e, _⟩ := ((MndH.holdsAt_eqv _ _ _ _ _ _ _).mp h3).1 rfl
  have e' : (Code.arr .e .e : Code Unit) = .arr .e (.arr .e .t) := e
  exact absurd e' (by decide)

/-! ## The Barcan formula holds -/

theorem MndH_BF : MndH.Valid BF := by
  refine MndH_Valid_of ?_
  refine (MndH.holdsAt_tall _ _ _ _).mpr fun a _ => (MndH.holdsAt_all _ _ _ _ _).mpr fun F hF => ?_
  refine (MndH.holdsAt_imp _ _ _ _ _).mpr fun h => (MndH.box_of MndH_heq _ _ _ _).mpr fun v _ => ?_
  refine (MndH.holdsAt_all _ _ _ _ _).mpr fun x hx => ?_
  have hF' : UND.rel (.arr a .t) true F F := hF
  cases v with
  | true =>
    exact (MndH.box_of MndH_heq _ _ _ _).mp ((MndH.holdsAt_all _ _ _ _ _).mp h x hx) true (UND.Rrefl true)
  | false =>
    obtain ⟨z, hz, hzx⟩ := UND.dense true false (fun _ _ => Or.inr rfl) (fun _ _ => Or.inr rfl) a x hx
    have h1 := (MndH.box_of MndH_heq _ _ _ _).mp ((MndH.holdsAt_all _ _ _ _ _).mp h z hz) false (Or.inl rfl)
    exact (hF' false (Or.inl rfl) z x hzx false (UND.Rrefl false)).mp h1

/-! ## Functional Choice fails -/

/-- `R p q` is true at the actual world just in case `q` is true at the other world iff `p` is
true at the actual world; at the other world it is true. -/
def MndH_RC : UND.El (.arr .t (.arr .t .t)) :=
  fun (p q : Bool → Prop) (w : Bool) => w = true → (q false ↔ p true)

theorem MndH_RC_adm : UND.rel (.arr .t (.arr .t .t)) true MndH_RC MndH_RC := by
  intro v hv p p' hp v' hv' q q' hq u hu
  show (u = true → (q false ↔ p true)) ↔ (u = true → (q' false ↔ p' true))
  rcases Bool.eq_false_or_eq_true u with hu1 | hu1
  · subst hu1
    have e1 : v' = true := R_true hu rfl
    subst e1
    have e2 : v = true := R_true hv' rfl
    subst e2
    have hpt := hp true (UND.Rrefl true)
    have hqf := hq false (Or.inl rfl)
    exact ⟨fun h _ => hqf.symm.trans ((h rfl).trans hpt), fun h _ => hqf.trans ((h rfl).trans hpt.symm)⟩
  · subst hu1
    exact ⟨fun _ hw => absurd hw Bool.false_ne_true, fun _ hw => absurd hw Bool.false_ne_true⟩

/-- Each proposition `p` is `R`-related to the proposition which is constantly `p`'s actual truth
value. But a choice function `f` would have to make `f p` true at the other world just in case `p`
is actually true, and so could not respect identity at the other world. -/
theorem MndH_not_Choice : ¬ MndH.Valid Choice := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MndH.holdsAt_all _ _ _ _ _).mp ((MndH.holdsAt_tall _ _ _ _).mp
    ((MndH.holdsAt_tall _ _ _ _).mp h .t trivial) .t trivial) MndH_RC MndH_RC_adm
  have h2 := (MndH.holdsAt_imp _ _ _ _ _).mp h1 ((MndH.holdsAt_all _ _ _ _ _).mpr fun p _ =>
    (MndH.holdsAt_ex _ _ _ _ _).mpr ⟨fun _ => p true, fun _ _ => Iff.rfl,
      show (true = true → (p true ↔ p true)) from fun _ => Iff.rfl⟩)
  obtain ⟨f, hf, h3⟩ := (MndH.holdsAt_ex _ _ _ _ _).mp h2
  have hf' : UND.rel (.arr .t .t) true f f := hf
  have h4 : true = true → (f (fun w => w = true) false ↔ true = true) :=
    (MndH.holdsAt_all _ _ _ _ _).mp h3 (fun w => w = true) (fun _ _ => Iff.rfl)
  have h5 : true = true → (f (fun _ => False) false ↔ False) :=
    (MndH.holdsAt_all _ _ _ _ _).mp h3 (fun _ => False) (fun _ _ => Iff.rfl)
  have hpp : UND.rel .t false (fun w => w = true) (fun _ => False) := by
    intro u hu
    rcases hu with hu | hu
    · exact absurd hu Bool.false_ne_true
    · subst hu
      exact ⟨fun hw => absurd hw Bool.false_ne_true, False.elim⟩
  have h6 := hf' false (Or.inl rfl) _ _ hpp false (UND.Rrefl false)
  exact (h5 rfl).mp (h6.mp ((h4 rfl).mpr rfl))

end Kr
end PIF
