import PIBF

/-!
# The profile of `𝔐_k,cong`

In `𝔐_k,cong` (`Kr.KC`, lean/PIKripkeCong.lean) any two items of one type are identified, at every
world, and `≈` is identity of types. So every identity statement between items of one type is true
at every world: `□φ` (that is, `φ ≡_t ⊤`) is always true, and so is every instance of Booleanism and
Classicism. Hence Collapse, NI≡, NI≈, ND≈, NI×, ND×, IdId, PropExt≡, TBF, TCBF, TNec and Nec hold,
while T fails (`⊥` is necessary) and so does `⊤ ≢ ⊥`. Since `≈` is identity of types, Inj≈ and
Recovery hold, Int≈ fails (`□` is trivial, but `e` and `t` are distinct), and Slogan holds (nothing
is identified across types).

Functional Choice fails: at the actual world any relation between entities is admissible, so we may
take the graph of a function `h` which does not respect identity at the second world (`h 0 = 0`,
`h 1 = 2`); no admissible function of type `e → e` agrees with `h`.
-/
set_option autoImplicit false

namespace PIF
namespace Kr
open Tm

/-! ### Basic facts -/

theorem MKC_Valid_of {φ : Fm Ctx.nil} (h : KC.HoldsAt φ (fun i => i.elim0) () KC.U.w0) : KC.Valid φ := by
  intro ρ _ env _
  have e1 : ρ = fun i => i.elim0 := funext fun i => i.elim0
  subst e1
  exact h

/-- Any two items of one type are identified. -/
theorem MKC_eqv_same {n : Nat} {Γ : Ctx n} (σ : Ty n) (x y : Tm Γ σ.1) (ρ : KC.U.TEnv n)
    (env : KC.U.Env Γ ρ) (w : KC.U.W) : KC.HoldsAt (eqv σ σ x y) ρ env w :=
  (KC.holdsAt_eqv _ _ _ _ _ _ _).mpr rfl

/-- `□φ` is always true. -/
theorem MKC_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : KC.U.TEnv n) (env : KC.U.Env Γ ρ) (w : KC.U.W) :
    KC.HoldsAt (boxF φ) ρ env w :=
  MKC_eqv_same tyT φ topF ρ env w

/-! ### Booleanism and Classicism -/

theorem MKC_Class : ∀ χ, ClassSch χ → KC.Valid χ := by
  rintro _ (⟨n, Γ, φ, ψ, _, rfl⟩ | ⟨n, Γ, σ, φ, ψ, _, rfl⟩)
  · exact KC.valid_closeCtx Γ _ fun ρ _ env _ => MKC_eqv_same tyT φ ψ ρ env _
  · exact KC.valid_closeCtx Γ _ fun ρ _ env _ => MKC_eqv_same σ.pred (lam σ φ) (lam σ ψ) ρ env _

theorem MKC_Bool : ∀ φ, BoolSch φ → KC.Valid φ := by
  rintro _ ⟨k, P, Q, _, rfl⟩
  unfold BoolInst
  rw [← closeCtx_ctxT]
  exact KC.valid_closeCtx _ _ fun ρ _ env _ => MKC_eqv_same tyT _ _ ρ env _

theorem MKC_IdId : KC.Valid IdId := by
  refine MKC_Valid_of ?_
  refine (KC.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  refine (KC.holdsAt_all _ _ _ _ _).mpr fun x _ => (KC.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  exact MKC_eqv_same tyT _ _ _ _ _

theorem MKC_PropExt : KC.Valid PropExt := by
  refine MKC_Valid_of ?_
  refine (KC.holdsAt_all _ _ _ _ _).mpr fun p _ => (KC.holdsAt_all _ _ _ _ _).mpr fun q _ => ?_
  exact (KC.holdsAt_imp _ _ _ _ _).mpr fun _ => MKC_eqv_same tyT _ _ _ _ _

/-- `⊤` and `⊥` are both propositions, so they are identified. -/
theorem MKC_not_TopBot : ¬ KC.Valid TopBot := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  exact (KC.holdsAt_neg _ _ _ _).mp h (MKC_eqv_same tyT topF botF _ _ _)

/-! ### Modal principles: `□` is trivial -/

/-- `⊥` is necessary but not true. -/
theorem MKC_not_TAx : ¬ KC.Valid TAx := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (KC.holdsAt_all _ _ _ _ _).mp h (fun _ => False) (fun _ _ => Iff.rfl)
  exact (KC.holdsAt_imp _ _ _ _ _).mp h1 (MKC_box _ _ _ _)

theorem MKC_Collapse : KC.Valid Collapse := by
  refine MKC_Valid_of ?_
  refine (KC.holdsAt_all _ _ _ _ _).mpr fun p _ => ?_
  exact (KC.holdsAt_imp _ _ _ _ _).mpr fun _ => MKC_box _ _ _ _

theorem MKC_NIEqv : KC.Valid NIEqv := by
  refine MKC_Valid_of ?_
  refine (KC.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  refine (KC.holdsAt_all _ _ _ _ _).mpr fun x _ => (KC.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  exact (KC.holdsAt_imp _ _ _ _ _).mpr fun _ => MKC_box _ _ _ _

theorem MKC_NITeq : KC.Valid NITeq := by
  refine MKC_Valid_of ?_
  refine (KC.holdsAt_tall _ _ _ _).mpr fun a _ => (KC.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  exact (KC.holdsAt_imp _ _ _ _ _).mpr fun _ => MKC_box _ _ _ _

theorem MKC_NDTeq : KC.Valid NDTeq := by
  refine MKC_Valid_of ?_
  refine (KC.holdsAt_tall _ _ _ _).mpr fun a _ => (KC.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  exact (KC.holdsAt_imp _ _ _ _ _).mpr fun _ => MKC_box _ _ _ _

theorem MKC_NIX : KC.Valid NIX := by
  refine MKC_Valid_of ?_
  refine (KC.holdsAt_tall _ _ _ _).mpr fun a _ => (KC.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (KC.holdsAt_all _ _ _ _ _).mpr fun x _ => (KC.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  exact (KC.holdsAt_imp _ _ _ _ _).mpr fun _ => MKC_box _ _ _ _

theorem MKC_NDX : KC.Valid NDX := by
  refine MKC_Valid_of ?_
  refine (KC.holdsAt_tall _ _ _ _).mpr fun a _ => (KC.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (KC.holdsAt_all _ _ _ _ _).mpr fun x _ => (KC.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  exact (KC.holdsAt_imp _ _ _ _ _).mpr fun _ => MKC_box _ _ _ _

theorem MKC_TBF : ∀ χ, TBFSch χ → KC.Valid χ := by
  rintro _ ⟨φ, rfl⟩
  refine MKC_Valid_of ?_
  exact (KC.holdsAt_imp _ _ _ _ _).mpr fun _ => MKC_box _ _ _ _

theorem MKC_TCBF : ∀ χ, TCBFSch χ → KC.Valid χ := by
  rintro _ ⟨φ, rfl⟩
  refine MKC_Valid_of ?_
  refine (KC.holdsAt_imp _ _ _ _ _).mpr fun _ => ?_
  exact (KC.holdsAt_tall _ _ _ _).mpr fun a _ => MKC_box _ _ _ _

theorem MKC_TNec : KC.Valid TNec := by
  refine MKC_Valid_of ?_
  exact (KC.holdsAt_tall _ _ _ _).mpr fun a _ => MKC_box _ _ _ _

theorem MKC_Nec : KC.Valid Nec := by
  refine MKC_Valid_of ?_
  refine (KC.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  exact (KC.holdsAt_all _ _ _ _ _).mpr fun x _ => MKC_box _ _ _ _

/-! ### Principles about `≈`, which is identity of types -/

theorem MKC_Inj : KC.Valid Inj := by
  refine MKC_Valid_of ?_
  refine (KC.holdsAt_tall _ _ _ _).mpr fun a _ => (KC.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (KC.holdsAt_tall _ _ _ _).mpr fun c _ => (KC.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (KC.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code Empty) = .arr b d := (KC.holdsAt_teq _ _ _ _ _).mp h
  exact (KC.holdsAt_conj _ _ _ _ _).mpr ⟨(KC.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).1,
    (KC.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).2⟩

theorem MKC_Recovery : KC.Valid Recovery := by
  refine MKC_Valid_of ?_
  refine (KC.holdsAt_tall _ _ _ _).mpr fun a _ => (KC.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (KC.holdsAt_tall _ _ _ _).mpr fun c _ => (KC.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (KC.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code Empty) = .arr b d :=
    (KC.holdsAt_teq _ _ _ _ _).mp ((KC.holdsAt_conj _ _ _ _ _).mp h).1
  exact (KC.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).2

/-- `□` is trivial, but `e` and `t` are distinct types. -/
theorem MKC_not_IntT : ¬ KC.Valid IntT := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (KC.holdsAt_tall _ _ _ _).mp ((KC.holdsAt_tall _ _ _ _).mp h .e trivial) .t trivial
  have h2 := (KC.holdsAt_imp _ _ _ _ _).mp h1
    ((KC.holdsAt_conj _ _ _ _ _).mpr ⟨MKC_box _ _ _ _, MKC_box _ _ _ _⟩)
  have e : (Code.e : Code Empty) = .t := (KC.holdsAt_teq _ _ _ _ _).mp h2
  exact nomatch e

/-- Nothing is identified across types. -/
theorem MKC_Slogan : KC.Valid Slogan := by
  refine MKC_Valid_of ?_
  refine (KC.holdsAt_all _ _ _ _ _).mpr fun x _ => (KC.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (KC.holdsAt_all _ _ _ _ _).mpr fun y _ => (KC.holdsAt_neg _ _ _ _).mpr fun hxy => ?_
  have e : (Code.e : Code Empty) = .arr b .t := (KC.holdsAt_eqv _ _ _ _ _ _ _).mp hxy
  exact nomatch e

/-! ### Functional Choice fails -/

/-- A function on entities which does not respect identity at the second world. -/
def MKC_h (i : Fin 3) : Fin 3 := if i.val = 0 then 0 else 2

/-- The graph of `MKC_h`, at the actual world; true everywhere else. -/
def MKC_R : UC.El (.arr .e (.arr .e .t)) := fun x y (w : W3) => w = .a → y = MKC_h x

theorem MKC_R_adm : UC.rel (.arr .e (.arr .e .t)) .a MKC_R MKC_R := by
  intro v hv x x' hxx' u hu y y' hyy' u' hu'
  show (u' = .a → y = MKC_h x) ↔ (u' = .a → y' = MKC_h x')
  by_cases hua : u' = .a
  · subst hua
    have hu0 : u = .a := hu'.elim id id
    subst hu0
    have hv0 : v = .a := hu.elim id id
    subst hv0
    have ex : x = x' := hxx'
    have ey : y = y' := hyy'
    subst ex; subst ey; exact Iff.rfl
  · exact ⟨fun _ h => absurd h hua, fun _ h => absurd h hua⟩

/-- No admissible function on entities agrees with `MKC_h` at `0` and `1`. -/
theorem MKC_no_choice (g : Fin 3 → Fin 3) (hg : UC.rel (.arr .e .e) .a g g)
    (h0 : W3.a = .a → g 0 = MKC_h 0) (h1 : W3.a = .a → g 1 = MKC_h 1) : False := by
  have hr := (adm_ee hg).1
  have e0 : g 0 = 0 := (h0 rfl).trans (by decide)
  have e1 : g 1 = 2 := (h1 rfl).trans (by decide)
  rw [e0, e1] at hr
  revert hr
  unfold R1
  decide

/-- Each entity is related by `MKC_R` to an entity, but no admissible function on entities picks
one out: it would agree with `MKC_h`, which sends `0` and `1`, identical at the second world, to
`0` and `2`, distinct there. -/
theorem MKC_not_Choice : ¬ KC.Valid Choice := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (KC.holdsAt_all _ _ _ _ _).mp ((KC.holdsAt_tall _ _ _ _).mp
    ((KC.holdsAt_tall _ _ _ _).mp h .e trivial) .e trivial) MKC_R MKC_R_adm
  have h2 := (KC.holdsAt_imp _ _ _ _ _).mp h1 ((KC.holdsAt_all _ _ _ _ _).mpr fun x _ =>
    (KC.holdsAt_ex _ _ _ _ _).mpr ⟨MKC_h x, rfl, show (W3.a = .a → MKC_h x = MKC_h x) from fun _ => rfl⟩)
  obtain ⟨f, hf, h3⟩ := (KC.holdsAt_ex _ _ _ _ _).mp h2
  exact MKC_no_choice f hf ((KC.holdsAt_all _ _ _ _ _).mp h3 (0 : Fin 3) rfl)
    ((KC.holdsAt_all _ _ _ _ _).mp h3 (1 : Fin 3) rfl)

end Kr
end PIF
