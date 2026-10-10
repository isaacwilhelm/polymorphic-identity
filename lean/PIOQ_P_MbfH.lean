import PIBF
set_option autoImplicit false

/-!
# More about `𝔐_k,bf,h`

`𝔐_k,bf,h` is `𝔐_k,bf` (two worlds: the actual world `true` sees both, `false` sees only itself;
`E = 2`, rigid; a base type `d` exists only at `false`) with haecceities added at the actual world:
there, items are identified just in case they have the same root (got by stripping off
haecceities); at the other world, items are identified just in case they are of one type and
identical there. `≈` is identity of types.

* PCong holds: identified functions at the actual world have the same codomain, since a root
  of a function type `α → β` is that function itself unless `β = t`.
* PExt fails: `λx.0` and `λx.(λy.y ≡ 0)` have identified values everywhere, but different roots.
* Inj≈ and Recovery hold, since `≈` is identity of types.
* Ext≈ and Int≈ hold: every type has an item which is its own root.
* NI× fails: `0 ≡ λy.(y ≡ 0)` at the actual world, but not at the other one.
* ND× fails: the proposition true only at the actual world is identical at the other world to `⊥`.
* BF holds: every item self-identical at the other world is identical there to one self-identical
  at the actual world.
* Functional Choice fails: the relation `R p y` iff (`y = 1` iff `p`) is total, but a function
  choosing its values would separate propositions identical at the other world.
-/

namespace PIF
namespace Kr
open Tm

/-! ## Basic facts -/

theorem MbfH_Valid_of {φ : Fm Ctx.nil} (h : MbfH.HoldsAt φ (fun i => i.elim0) () true) : MbfH.Valid φ := by
  intro ρ _ env _
  have e1 : ρ = fun i => i.elim0 := funext fun i => i.elim0
  subst e1
  exact h

theorem MbfH_D_et : UBF.D true (.arr .e .t) := Or.inr ⟨trivial, trivial⟩

theorem MbfH_hcy_adm : UBF.rel (.arr .e .t) true (UBF.hcy .e true) (UBF.hcy .e true) :=
  UBF.hcy_resp .e true true rfl UBF_all

/-- At the actual world, the entity `true` is identified with its haecceity. -/
theorem MbfH_hae_key : MbfH.eqv .e (.arr .e .t) true (UBF.hcy .e true) true :=
  ⟨fun _ => ⟨rfl, MbfH_hcy_adm, UBF.RR_symm (UBF.Root_hcy UBF_all .e true rfl)⟩, fun h => absurd rfl h⟩

/-! ## Roots -/

/-- A root is either the item itself, or of a smaller type, got from a type `α → t`. -/
theorem MbfH_root_cases : ∀ (a : Code UBF.Base) (x : UBF.El a),
    (UBF.Root a x).1 = a ∨ ((∃ a', a = .arr a' .t) ∧ Csz (UBF.Root a x).1 < Csz a)
  | .arr a .t, f => by
    by_cases h : ∃ z, UBF.rel a UBF.w0 z z ∧ UBF.rel (.arr a .t) UBF.w0 f (UBF.hcy a z)
    · refine Or.inr ⟨⟨a, rfl⟩, ?_⟩
      rw [UBF.Root_arr_pos a f h]
      have h1 := UBF.Root_sz a (Classical.choose h)
      have h2 : Csz (Code.arr a Code.t : Code UBF.Base) = Csz a + 1 := rfl
      omega
    · refine Or.inl ?_
      rw [UBF.Root_arr_neg a f h]
  | .arr _ .e, _ => Or.inl rfl
  | .arr _ (.base _), _ => Or.inl rfl
  | .arr _ (.arr _ _), _ => Or.inl rfl
  | .e, _ => Or.inl rfl
  | .t, _ => Or.inl rfl
  | .base _, _ => Or.inl rfl

/-- Every type has an item, self-identical at the actual world, which is its own root. -/
theorem MbfH_plain : ∀ a : Code UBF.Base, ∃ x : UBF.El a, UBF.rel a true x x ∧ (UBF.Root a x).1 = a
  | .arr a .t => by
    have h : ¬ ∃ z, UBF.rel a UBF.w0 z z ∧
        UBF.rel (.arr a .t) UBF.w0 (fun _ _ => False) (UBF.hcy a z) := by
      rintro ⟨z, hz, hf⟩
      exact (hf true (Or.inl rfl) z z hz true (Or.inl rfl)).mpr hz
    refine ⟨fun _ _ => False, fun _ _ _ _ _ _ _ => Iff.rfl, ?_⟩
    rw [UBF.Root_arr_neg a _ h]
  | .arr a .e => let ⟨x, hx⟩ := UBF.adm_nonempty (.arr a .e); ⟨x, hx true, rfl⟩
  | .arr a (.base b) => let ⟨x, hx⟩ := UBF.adm_nonempty (.arr a (.base b)); ⟨x, hx true, rfl⟩
  | .arr a (.arr c d) => let ⟨x, hx⟩ := UBF.adm_nonempty (.arr a (.arr c d)); ⟨x, hx true, rfl⟩
  | .e => let ⟨x, hx⟩ := UBF.adm_nonempty .e; ⟨x, hx true, rfl⟩
  | .t => let ⟨x, hx⟩ := UBF.adm_nonempty .t; ⟨x, hx true, rfl⟩
  | .base b => let ⟨x, hx⟩ := UBF.adm_nonempty (.base b); ⟨x, hx true, rfl⟩

/-- Functions identified at the actual world have the same codomain. -/
theorem MbfH_HR_arr {a b c : Code UBF.Base} {f : UBF.El (.arr a b)} {g : UBF.El (.arr a c)}
    (h : UBF.HR (.arr a b) (.arr a c) f g) : b = c := by
  have e : (UBF.Root (.arr a b) f).1 = (UBF.Root (.arr a c) g).1 := h.2.2.1
  have s1 : Csz (Code.arr a b) = Csz a + Csz b + 1 := rfl
  have s2 : Csz (Code.arr a c) = Csz a + Csz c + 1 := rfl
  rcases MbfH_root_cases (.arr a b) f with hb | ⟨⟨b', hb'⟩, hb⟩ <;>
    rcases MbfH_root_cases (.arr a c) g with hc | ⟨⟨c', hc'⟩, hc⟩
  · exact (Code.arr.inj (hb.symm.trans (e.trans hc))).2
  · have e2 : c = .t := (Code.arr.inj hc').2
    have s3 : Csz c = 0 := by subst e2; rfl
    have c1 := congrArg Csz (hb.symm.trans e)
    omega
  · have e2 : b = .t := (Code.arr.inj hb').2
    have s3 : Csz b = 0 := by subst e2; rfl
    have c1 := congrArg Csz (e.trans hc)
    omega
  · exact (Code.arr.inj hb').2.trans (Code.arr.inj hc').2.symm

/-! ## PCong holds, PExt fails -/

theorem MbfH_PCong_at (a b c : Code UBF.Base) (f : UBF.El (.arr a b)) (g : UBF.El (.arr a c)) (x : UBF.El a)
    (hx : UBF.rel a true x x) (h : MbfH.eqv (.arr a b) (.arr a c) f g true) :
    MbfH.eqv b c (f x) (g x) true := by
  have e := MbfH_HR_arr (h.1 rfl)
  subst e
  exact (MbfH_heq b _ _ true).mpr ((MbfH_heq (.arr a b) f g true).mp h true (Or.inl rfl) x x hx)

theorem MbfH_PCong : MbfH.Valid PCong := by
  refine MbfH_Valid_of ?_
  refine (MbfH.holdsAt_tall _ _ _ _).mpr fun a _ => (MbfH.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (MbfH.holdsAt_tall _ _ _ _).mpr fun c _ => ?_
  refine (MbfH.holdsAt_all _ _ _ _ _).mpr fun f _ => (MbfH.holdsAt_all _ _ _ _ _).mpr fun g _ =>
    (MbfH.holdsAt_all _ _ _ _ _).mpr fun x hx => ?_
  refine (MbfH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  exact (MbfH.holdsAt_eqv _ _ _ _ _ _ _).mpr
    (MbfH_PCong_at a b c f g x hx ((MbfH.holdsAt_eqv _ _ _ _ _ _ _).mp h))

theorem MbfH_not_PExt : ¬ MbfH.Valid PExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MbfH.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)
  have h2 := (MbfH.holdsAt_tall _ _ _ _).mp h1 .e (Or.inr trivial)
  have h3 := (MbfH.holdsAt_tall _ _ _ _).mp h2 (.arr .e .t) MbfH_D_et
  have h4 := (MbfH.holdsAt_all _ _ _ _ _).mp h3 (fun _ => true : UBF.El (.arr .e .e)) (fun _ _ _ _ _ => rfl)
  have h5 := (MbfH.holdsAt_all _ _ _ _ _).mp h4 (fun _ => UBF.hcy .e true : UBF.El (.arr .e (.arr .e .t)))
    (fun v hv _ _ _ => UBF.rel_mono (.arr .e .t) true v _ _ hv MbfH_hcy_adm)
  have h6 := (MbfH.holdsAt_imp _ _ _ _ _).mp h5 ((MbfH.holdsAt_all _ _ _ _ _).mpr fun _ _ =>
    (MbfH.holdsAt_eqv _ _ _ _ _ _ _).mpr MbfH_hae_key)
  have h7 := ((MbfH.holdsAt_eqv _ _ _ _ _ _ _).mp h6).1 rfl
  have e : (Code.arr .e .e : Code UBF.Base) = .arr .e (.arr .e .t) := h7.2.2.1
  exact nomatch (Code.arr.inj e).2

/-! ## Inj≈, Recovery, Ext≈ and Int≈ hold -/

theorem MbfH_Inj : MbfH.Valid Inj := by
  refine MbfH_Valid_of ?_
  refine (MbfH.holdsAt_tall _ _ _ _).mpr fun a _ => (MbfH.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (MbfH.holdsAt_tall _ _ _ _).mpr fun c _ => (MbfH.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MbfH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code UBF.Base) = .arr b d := (MbfH.holdsAt_teq _ _ _ _ _).mp h
  exact (MbfH.holdsAt_conj _ _ _ _ _).mpr ⟨(MbfH.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).1,
    (MbfH.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).2⟩

theorem MbfH_Recovery : MbfH.Valid Recovery := by
  refine MbfH_Valid_of ?_
  refine (MbfH.holdsAt_tall _ _ _ _).mpr fun a _ => (MbfH.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (MbfH.holdsAt_tall _ _ _ _).mpr fun c _ => (MbfH.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MbfH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code UBF.Base) = .arr b d :=
    (MbfH.holdsAt_teq _ _ _ _ _).mp ((MbfH.holdsAt_conj _ _ _ _ _).mp h).1
  exact (MbfH.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).2

/-- At the actual world, if each item of `α` is identified with one of `β` and vice versa, then
`α` and `β` are the same type. -/
theorem MbfH_sub_eq {n : Nat} {Γ : Ctx n} (ρ : MbfH.U.TEnv n) (env : MbfH.U.Env Γ ρ) (a b : Code UBF.Base)
    (h1 : MbfH.HoldsAt (subT : Fm (Γ.text.text)) (scons b (scons a ρ)) env true)
    (h2 : MbfH.HoldsAt (supT : Fm (Γ.text.text)) (scons b (scons a ρ)) env true) : a = b := by
  obtain ⟨x, hx, hxr⟩ := MbfH_plain a
  obtain ⟨y', hy', hyr⟩ := MbfH_plain b
  obtain ⟨y, _, hxy⟩ := (MbfH.holdsAt_ex _ _ _ _ _).mp ((MbfH.holdsAt_all _ _ _ _ _).mp h1 x hx)
  obtain ⟨x', _, hxy'⟩ := (MbfH.holdsAt_ex _ _ _ _ _).mp ((MbfH.holdsAt_all _ _ _ _ _).mp h2 y' hy')
  have e1 : MbfH.eqv a b x y true := (MbfH.holdsAt_eqv _ _ _ _ _ _ _).mp hxy
  have e2 : MbfH.eqv a b x' y' true := (MbfH.holdsAt_eqv _ _ _ _ _ _ _).mp hxy'
  have r1 : (UBF.Root a x).1 = (UBF.Root b y).1 := (e1.1 rfl).2.2.1
  have r2 : (UBF.Root a x').1 = (UBF.Root b y').1 := (e2.1 rfl).2.2.1
  rcases MbfH_root_cases b y with hb | ⟨_, hb⟩
  · exact hxr.symm.trans (r1.trans hb)
  · rcases MbfH_root_cases a x' with ha | ⟨_, ha⟩
    · exact ha.symm.trans (r2.trans hyr)
    · have c1 := congrArg Csz (hxr.symm.trans r1)
      have c2 := congrArg Csz (r2.trans hyr)
      omega

theorem MbfH_ExtT : MbfH.Valid ExtT := by
  refine MbfH_Valid_of ?_
  refine (MbfH.holdsAt_tall _ _ _ _).mpr fun a _ => (MbfH.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MbfH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hc := (MbfH.holdsAt_conj _ _ _ _ _).mp h
  exact (MbfH.holdsAt_teq _ _ _ _ _).mpr (MbfH_sub_eq _ _ a b hc.1 hc.2)

theorem MbfH_IntT : MbfH.Valid IntT := by
  refine MbfH_Valid_of ?_
  refine (MbfH.holdsAt_tall _ _ _ _).mpr fun a _ => (MbfH.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MbfH.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hc := (MbfH.holdsAt_conj _ _ _ _ _).mp h
  have h1 := (MbfH.box_of MbfH_heq _ _ _ _).mp hc.1 true (Or.inl rfl)
  have h2 := (MbfH.box_of MbfH_heq _ _ _ _).mp hc.2 true (Or.inl rfl)
  exact (MbfH.holdsAt_teq _ _ _ _ _).mpr (MbfH_sub_eq _ _ a b h1 h2)

/-! ## NI× and ND× fail -/

theorem MbfH_not_NIX : ¬ MbfH.Valid NIX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MbfH.holdsAt_tall _ _ _ _).mp ((MbfH.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.arr .e .t) MbfH_D_et
  have h2 := (MbfH.holdsAt_all _ _ _ _ _).mp ((MbfH.holdsAt_all _ _ _ _ _).mp h1 true rfl)
    (UBF.hcy .e true) MbfH_hcy_adm
  have h3 := (MbfH.box_of MbfH_heq _ _ _ _).mp ((MbfH.holdsAt_imp _ _ _ _ _).mp h2
    ((MbfH.holdsAt_eqv _ _ _ _ _ _ _).mpr MbfH_hae_key)) false (Or.inl rfl)
  obtain ⟨e, _⟩ := ((MbfH.holdsAt_eqv _ _ _ _ _ _ _).mp h3).2 Bool.false_ne_true
  have e' : (Code.e : Code UBF.Base) = .arr .e .t := e
  exact nomatch e'

/-- The proposition true only at the actual world. -/
def MbfH_pT : UBF.El .t := fun w => w = true
/-- The impossible proposition. -/
def MbfH_pF : UBF.El .t := fun _ => False

theorem MbfH_pT_pF : UBF.rel .t false MbfH_pT MbfH_pF := by
  intro v hv
  rcases hv with h | h
  · exact absurd h Bool.false_ne_true
  · subst h
    exact ⟨fun h => Bool.false_ne_true h, False.elim⟩

theorem MbfH_pT_ne_pF : ¬ UBF.rel .t true MbfH_pT MbfH_pF := fun h =>
  (h true (Or.inl rfl)).mp rfl

theorem MbfH_not_NDX : ¬ MbfH.Valid NDX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MbfH.holdsAt_tall _ _ _ _).mp ((MbfH.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)) .t (Or.inr trivial)
  have h2 := (MbfH.holdsAt_all _ _ _ _ _).mp ((MbfH.holdsAt_all _ _ _ _ _).mp h1 MbfH_pT (fun _ _ => Iff.rfl))
    MbfH_pF (fun _ _ => Iff.rfl)
  refine (MbfH.holdsAt_neg _ _ _ _).mp ((MbfH.box_of MbfH_heq _ _ _ _).mp ((MbfH.holdsAt_imp _ _ _ _ _).mp h2
    ((MbfH.holdsAt_neg _ _ _ _).mpr fun he => ?_)) false (Or.inr rfl)) ?_
  · exact MbfH_pT_ne_pF ((MbfH_heq .t MbfH_pT MbfH_pF true).mp ((MbfH.holdsAt_eqv _ _ _ _ _ _ _).mp he))
  · exact (MbfH.holdsAt_eqv _ _ _ _ _ _ _).mpr ((MbfH_heq .t MbfH_pT MbfH_pF false).mpr MbfH_pT_pF)

/-! ## BF holds -/

theorem MbfH_BF : MbfH.Valid BF := by
  refine MbfH_Valid_of ?_
  refine (MbfH.holdsAt_tall _ _ _ _).mpr fun a _ => (MbfH.holdsAt_all _ _ _ _ _).mpr fun F hF => ?_
  refine (MbfH.holdsAt_imp _ _ _ _ _).mpr fun h => (MbfH.box_of MbfH_heq _ _ _ _).mpr fun v _ => ?_
  refine (MbfH.holdsAt_all _ _ _ _ _).mpr fun x hx => ?_
  have hF' : UBF.rel (.arr a .t) true F F := hF
  have key : ∀ z : UBF.El a, UBF.rel a true z z → ∀ u, UBF.R true u → F z u := fun z hz u hu =>
    (MbfH.box_of MbfH_heq _ _ _ _).mp ((MbfH.holdsAt_all _ _ _ _ _).mp h z hz) u hu
  cases v with
  | true => exact key x hx true (Or.inl rfl)
  | false =>
    have hx' : UBF.rel a false x x := hx
    obtain ⟨z, hz, hzx⟩ := UBF.dense true false (fun _ _ => Or.inr rfl) (fun _ _ => Or.inr rfl) a x hx'
    exact (hF' false (Or.inr rfl) z x hzx false (Or.inr rfl)).mp (key z hz false (Or.inr rfl))

/-! ## Functional Choice fails -/

/-- `R p y` iff (`y` is `1` iff `p`). -/
def MbfH_RC : UBF.El (.arr .t (.arr .e .t)) := fun p y w => (y = true ↔ p w)

theorem MbfH_RC_adm : UBF.rel (.arr .t (.arr .e .t)) true MbfH_RC MbfH_RC := by
  intro v _ p q hpq u hu y y' hy s hs
  have hy' : y = y' := hy
  subst hy'
  have hps : p s ↔ q s := hpq s (UBF.Rtrans _ _ _ hu hs)
  show (y = true ↔ p s) ↔ (y = true ↔ q s)
  exact iff_congr Iff.rfl hps

theorem MbfH_RC_total (p : UBF.El .t) : ∃ y : Bool, (y = true ↔ p true) := by
  by_cases hp : p true
  · exact ⟨true, fun _ => hp, fun _ => rfl⟩
  · exact ⟨false, fun h => absurd h Bool.false_ne_true, fun h => absurd h hp⟩

theorem MbfH_not_Choice : ¬ MbfH.Valid Choice := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MbfH.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)
  have h2 := (MbfH.holdsAt_tall _ _ _ _).mp h1 .e (Or.inr trivial)
  have h3 := (MbfH.holdsAt_all _ _ _ _ _).mp h2 MbfH_RC MbfH_RC_adm
  have h4 := (MbfH.holdsAt_imp _ _ _ _ _).mp h3 ((MbfH.holdsAt_all _ _ _ _ _).mpr fun p _ =>
    let ⟨y, hy⟩ := MbfH_RC_total p
    (MbfH.holdsAt_ex _ _ _ _ _).mpr ⟨y, rfl, hy⟩)
  obtain ⟨f, hf, hfx⟩ := (MbfH.holdsAt_ex _ _ _ _ _).mp h4
  have hall := (MbfH.holdsAt_all _ _ _ _ _).mp hfx
  have f1 : (f : UBF.El (.arr .t .e)) MbfH_pT = true :=
    (hall MbfH_pT (fun _ _ => Iff.rfl) : ((f : UBF.El (.arr .t .e)) MbfH_pT = true ↔ MbfH_pT true)).mpr rfl
  have f2 : ¬ (f : UBF.El (.arr .t .e)) MbfH_pF = true := fun e =>
    (hall MbfH_pF (fun _ _ => Iff.rfl) : ((f : UBF.El (.arr .t .e)) MbfH_pF = true ↔ MbfH_pF true)).mp e
  have hr : (f : UBF.El (.arr .t .e)) MbfH_pT = (f : UBF.El (.arr .t .e)) MbfH_pF :=
    hf false (Or.inr rfl) MbfH_pT MbfH_pF MbfH_pT_pF
  exact f2 (hr ▸ f1)

end Kr
end PIF
