import PIBF

/-!
# The profile of `𝔐_k,w1`

In `𝔐_k,w1` (`Kr.KW1`, lean/PICongQs.lean) there are two worlds: the actual world `T` sees both,
and the other world `F` sees only itself. Entities are booleans, and identity of entities is
equality. Items of one type are identified, at either world, just in case they are identical at
`F`; nothing is identified across types; and `≈` is identity of types. So identity statements do
not depend on the world, and `□φ` (that is, `φ ≡_t ⊤`) is true, at either world, just in case `φ`
is true at `F`.

Hence NI≡, NI≈, ND≈, NI×, ND×, TBF, TCBF, TNec and Nec hold, while Collapse fails (the proposition
true only at the actual world is not necessary). Disjoint, Slogan, Cantor, Inj≈, Recovery, Ext≈
and Int≈ hold, and Twin and Haecceitism fail. CBF holds, and so does BF, since every item at `F`
is identical there to an item at the actual world. Since LL≡ holds at `F`, and soundness holds
world by world, Classicism holds, and with it Bool and IdId. Functional Choice fails: no item of
`t → e` at the actual world picks out the truth value of each proposition there.

LL≡/≈ and LL≡-Poly hold, for every polymorphic predicate (with parameters): by the fundamental
lemma for a family of admissible relations which, at the actual world, may swap two classes of
items that are identical at `F`.
-/
set_option autoImplicit false

namespace PIF
namespace Kr
open Tm

/-! ### Basic facts -/

theorem MKW1_Valid_of {φ : Fm Ctx.nil} (h : KW1.HoldsAt φ (fun i => i.elim0) () true) : KW1.Valid φ := by
  intro ρ _ env _
  have e1 : ρ = fun i => i.elim0 := funext fun i => i.elim0
  subst e1
  exact h

theorem MKW1_R_false {v : Bool} (h : UW1.R false v) : v = false := h.resolve_left Bool.false_ne_true

theorem MKW1_R_true {u : Bool} (h : UW1.R u true) : u = true := h.elim id (fun e => Bool.noConfusion e)

/-- `□φ` is true, at either world, just in case `φ` is true at `F`. -/
theorem MKW1_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : KW1.U.TEnv n) (env : KW1.U.Env Γ ρ) (w : Bool) :
    KW1.HoldsAt (boxF φ) ρ env w ↔ KW1.HoldsAt φ ρ env false := by
  refine (KW1.holdsAt_eqv tyT tyT φ topF ρ env w).trans ((KW1_same _ _ _ w).trans ?_)
  show (∀ v, UW1.R false v → (KW1.eval φ ρ env v ↔ KW1.eval topF ρ env v)) ↔ KW1.eval φ ρ env false
  have e := KW1.eval_topF ρ env
  rw [e]
  constructor
  · intro h; exact (h false (UW1.Rrefl false)).mpr trivial
  · intro h v hv
    have hv' := MKW1_R_false hv
    subst hv'
    exact ⟨fun _ => trivial, fun _ => h⟩

/-! ### Principles about identity across types and `≈` -/

theorem MKW1_Disjoint : KW1.Valid Disjoint := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => (KW1.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun hn => ?_
  refine (KW1.holdsAt_all _ _ _ _ _).mpr fun x _ => (KW1.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (KW1.holdsAt_neg _ _ _ _).mpr fun hxy => ?_
  obtain ⟨e, _⟩ := (KW1.holdsAt_eqv _ _ _ _ _ _ _).mp hxy
  exact (KW1.holdsAt_neg _ _ _ _).mp hn ((KW1.holdsAt_teq _ _ _ _ _).mpr e)

/-- Nothing is identified across types. -/
theorem MKW1_Slogan : KW1.Valid Slogan := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_all _ _ _ _ _).mpr fun x _ => (KW1.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (KW1.holdsAt_all _ _ _ _ _).mpr fun y _ => (KW1.holdsAt_neg _ _ _ _).mpr fun hxy => ?_
  obtain ⟨e, _⟩ := (KW1.holdsAt_eqv _ _ _ _ _ _ _).mp hxy
  have e' : (Code.e : Code Empty) = .arr b .t := e
  exact nomatch e'

theorem MKW1_not_Twin : ¬ KW1.Valid Twin := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (KW1.holdsAt_all _ _ _ _ _).mp ((KW1.holdsAt_tall _ _ _ _).mp h .e trivial)
    (show UW1.El .e from true) rfl
  obtain ⟨b, _, h2⟩ := (KW1.holdsAt_tex _ _ _ _).mp h1
  obtain ⟨hn, h3⟩ := (KW1.holdsAt_conj _ _ _ _ _).mp h2
  obtain ⟨y, _, h4⟩ := (KW1.holdsAt_ex _ _ _ _ _).mp h3
  obtain ⟨e, _⟩ := (KW1.holdsAt_eqv _ _ _ _ _ _ _).mp h4
  exact (KW1.holdsAt_neg _ _ _ _).mp hn ((KW1.holdsAt_teq _ _ _ _ _).mpr e)

theorem MKW1_not_Hae : ¬ KW1.Valid Hae := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (KW1.holdsAt_all _ _ _ _ _).mp ((KW1.holdsAt_tall _ _ _ _).mp h .e trivial)
    (show UW1.El .e from true) rfl
  obtain ⟨e, _⟩ := (KW1.holdsAt_eqv _ _ _ _ _ _ _).mp h1
  have e' : (Code.e : Code Empty) = .arr .e .t := e
  exact nomatch e'

theorem MKW1_Cantor : KW1.Valid Cantor := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  obtain ⟨G, hG⟩ := UW1.adm_nonempty (.arr a .t)
  refine (KW1.holdsAt_ex _ _ _ _ _).mpr ⟨G, hG true, ?_⟩
  refine (KW1.holdsAt_all _ _ _ _ _).mpr fun y _ => (KW1.holdsAt_neg _ _ _ _).mpr fun hGy => ?_
  obtain ⟨e, _⟩ := (KW1.holdsAt_eqv _ _ _ _ _ _ _).mp hGy
  exact Code.arr_ne_left a .t e

theorem MKW1_Inj : KW1.Valid Inj := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => (KW1.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (KW1.holdsAt_tall _ _ _ _).mpr fun c _ => (KW1.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code Empty) = .arr b d := (KW1.holdsAt_teq _ _ _ _ _).mp h
  exact (KW1.holdsAt_conj _ _ _ _ _).mpr ⟨(KW1.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).1,
    (KW1.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).2⟩

theorem MKW1_Recovery : KW1.Valid Recovery := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => (KW1.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (KW1.holdsAt_tall _ _ _ _).mpr fun c _ => (KW1.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code Empty) = .arr b d :=
    (KW1.holdsAt_teq _ _ _ _ _).mp ((KW1.holdsAt_conj _ _ _ _ _).mp h).1
  exact (KW1.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).2

theorem MKW1_sub_eq {n : Nat} {Γ : Ctx n} (ρ : KW1.U.TEnv n) (env : KW1.U.Env Γ ρ) (w : Bool) (a b : Code Empty)
    (h : KW1.HoldsAt (subT : Fm (Γ.text.text)) (scons b (scons a ρ)) env w) : a = b := by
  obtain ⟨x, hx⟩ := UW1.adm_nonempty a
  obtain ⟨y, _, hy⟩ := (KW1.holdsAt_ex _ _ _ _ _).mp ((KW1.holdsAt_all _ _ _ _ _).mp h x (hx w))
  exact ((KW1.holdsAt_eqv _ _ _ _ _ _ _).mp hy).1

theorem MKW1_ExtT : KW1.Valid ExtT := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => (KW1.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  exact (KW1.holdsAt_teq _ _ _ _ _).mpr (MKW1_sub_eq _ _ _ a b ((KW1.holdsAt_conj _ _ _ _ _).mp h).1)

theorem MKW1_IntT : KW1.Valid IntT := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => (KW1.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have h1 := (MKW1_box _ _ _ _).mp ((KW1.holdsAt_conj _ _ _ _ _).mp h).1
  exact (KW1.holdsAt_teq _ _ _ _ _).mpr (MKW1_sub_eq _ _ _ a b h1)

/-! ### Modal principles -/

/-- The proposition true only at the actual world is true but not necessary. -/
theorem MKW1_not_Collapse : ¬ KW1.Valid Collapse := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (KW1.holdsAt_all _ _ _ _ _).mp h (fun w => w = true) (fun _ _ => Iff.rfl)
  have h2 := (KW1.holdsAt_imp _ _ _ _ _).mp h1 rfl
  have h3 := (MKW1_box _ _ _ _).mp h2
  exact Bool.noConfusion (h3 : false = true)

theorem MKW1_NIEqv : KW1.Valid NIEqv := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  refine (KW1.holdsAt_all _ _ _ _ _).mpr fun x _ => (KW1.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun h => (MKW1_box _ _ _ _).mpr ?_
  exact (KW1.holdsAt_eqv _ _ _ _ _ _ _).mpr ((KW1.holdsAt_eqv _ _ _ _ _ _ _).mp h)

theorem MKW1_NIX : KW1.Valid NIX := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => (KW1.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (KW1.holdsAt_all _ _ _ _ _).mpr fun x _ => (KW1.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun h => (MKW1_box _ _ _ _).mpr ?_
  exact (KW1.holdsAt_eqv _ _ _ _ _ _ _).mpr ((KW1.holdsAt_eqv _ _ _ _ _ _ _).mp h)

theorem MKW1_NDX : KW1.Valid NDX := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => (KW1.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (KW1.holdsAt_all _ _ _ _ _).mpr fun x _ => (KW1.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun hn => (MKW1_box _ _ _ _).mpr ?_
  refine (KW1.holdsAt_neg _ _ _ _).mpr fun h => (KW1.holdsAt_neg _ _ _ _).mp hn ?_
  exact (KW1.holdsAt_eqv _ _ _ _ _ _ _).mpr ((KW1.holdsAt_eqv _ _ _ _ _ _ _).mp h)

theorem MKW1_NITeq : KW1.Valid NITeq := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => (KW1.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun h => (MKW1_box _ _ _ _).mpr ?_
  exact (KW1.holdsAt_teq _ _ _ _ false).mpr ((KW1.holdsAt_teq _ _ _ _ true).mp h)

theorem MKW1_NDTeq : KW1.Valid NDTeq := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => (KW1.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun hn => (MKW1_box _ _ _ _).mpr ?_
  refine (KW1.holdsAt_neg _ _ _ _).mpr fun h => (KW1.holdsAt_neg _ _ _ _).mp hn ?_
  exact (KW1.holdsAt_teq _ _ _ _ true).mpr ((KW1.holdsAt_teq _ _ _ _ false).mp h)

theorem MKW1_TNec : KW1.Valid TNec := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => (MKW1_box _ _ _ _).mpr ?_
  exact (KW1.holdsAt_tex _ _ _ _).mpr ⟨a, trivial, (KW1.holdsAt_teq _ _ _ _ _).mpr rfl⟩

theorem MKW1_Nec : KW1.Valid Nec := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  refine (KW1.holdsAt_all _ _ _ _ _).mpr fun x hx => (MKW1_box _ _ _ _).mpr ?_
  have hx' : UW1.rel a false x x := UW1.rel_mono a true false x x (UW1_toF true) hx
  exact (KW1.holdsAt_ex _ _ _ _ _).mpr ⟨x, hx', (KW1.holdsAt_eqv _ _ _ _ _ _ _).mpr ((KW1_same a x x _).mpr hx')⟩

/-- With constant domains of types, the Barcan formula for types holds. -/
theorem MKW1_TBF : ∀ χ, TBFSch χ → KW1.Valid χ := by
  rintro _ ⟨φ, rfl⟩
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun h => (MKW1_box _ _ _ _).mpr ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  exact (MKW1_box _ _ _ _).mp ((KW1.holdsAt_tall _ _ _ _).mp h a trivial)

theorem MKW1_TCBF : ∀ χ, TCBFSch χ → KW1.Valid χ := by
  rintro _ ⟨φ, rfl⟩
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun h => (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  exact (MKW1_box _ _ _ _).mpr ((KW1.holdsAt_tall _ _ _ _).mp ((MKW1_box _ _ _ _).mp h) a trivial)

theorem MKW1_CBF : KW1.Valid CBF := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  refine (KW1.holdsAt_all _ _ _ _ _).mpr fun G _ => (KW1.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  refine (KW1.holdsAt_all _ _ _ _ _).mpr fun x hx => (MKW1_box _ _ _ _).mpr ?_
  exact (KW1.holdsAt_all _ _ _ _ _).mp ((MKW1_box _ _ _ _).mp h) x
    (UW1.rel_mono a true false x x (UW1_toF true) hx)

/-- Every item at `F` is identical there to an item at the actual world. -/
theorem MKW1_BF : KW1.Valid BF := by
  refine MKW1_Valid_of ?_
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  refine (KW1.holdsAt_all _ _ _ _ _).mpr fun G hG => (KW1.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  refine (MKW1_box _ _ _ _).mpr ((KW1.holdsAt_all _ _ _ _ _).mpr fun x hx => ?_)
  obtain ⟨z, hz, hzx⟩ := UW1.dense true false (fun _ _ => Or.inr rfl) (fun _ _ => Or.inr rfl) a x hx
  have h1 := (MKW1_box _ _ _ _).mp ((KW1.holdsAt_all _ _ _ _ _).mp h z hz)
  have hG' : UW1.rel (.arr a .t) true G G := hG
  exact (hG' false (UW1_toF true) z x hzx false (UW1.Rrefl false)).mp h1

/-! ### Functional Choice fails -/

/-- At the actual world, `R p y` says that `y` is the truth value of `p` there. -/
def MKW1_Rel : UW1.El (.arr .t (.arr .e .t)) := fun p y w => w = true → (y = true ↔ p true)

theorem MKW1_Rel_adm : UW1.rel (.arr .t (.arr .e .t)) true MKW1_Rel MKW1_Rel := by
  intro v _ p p' hpp u hu y y' hyy u' hu'
  show (u' = true → (y = true ↔ p true)) ↔ (u' = true → (y' = true ↔ p' true))
  have ey : y = y' := hyy
  subst ey
  by_cases h : u' = true
  · subst h
    have hu1 := MKW1_R_true hu'
    subst hu1
    have hv1 := MKW1_R_true hu
    subst hv1
    have hp : p true ↔ p' true := hpp true (Or.inl rfl)
    exact ⟨fun h1 h2 => (h1 h2).trans hp, fun h1 h2 => (h1 h2).trans hp.symm⟩
  · exact ⟨fun _ h' => absurd h' h, fun _ h' => absurd h' h⟩

/-- Each proposition has a truth value at the actual world, but no item of `t → e` there picks it
out: such an item gives the same value to `⊤` and to the proposition true only at `F`. -/
theorem MKW1_not_Choice : ¬ KW1.Valid Choice := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (KW1.holdsAt_all _ _ _ _ _).mp ((KW1.holdsAt_tall _ _ _ _).mp
    ((KW1.holdsAt_tall _ _ _ _).mp h .t trivial) .e trivial) MKW1_Rel MKW1_Rel_adm
  have h2 := (KW1.holdsAt_imp _ _ _ _ _).mp h1 ((KW1.holdsAt_all _ _ _ _ _).mpr fun p _ =>
    (KW1.holdsAt_ex _ _ _ _ _).mpr (by
      by_cases hp : p true
      · exact ⟨(true : Bool), rfl, fun _ => ⟨fun _ => hp, fun _ => rfl⟩⟩
      · exact ⟨(false : Bool), rfl, fun _ => ⟨fun e => Bool.noConfusion e, fun h' => absurd h' hp⟩⟩))
  obtain ⟨f, hf, h3⟩ := (KW1.holdsAt_ex _ _ _ _ _).mp h2
  have e1 := (KW1.holdsAt_all _ _ _ _ _).mp h3 (fun _ => True) (fun _ _ => Iff.rfl)
  have e2 := (KW1.holdsAt_all _ _ _ _ _).mp h3 (fun w => w = false) (fun _ _ => Iff.rfl)
  have hf' : UW1.rel (.arr .t .e) true f f := hf
  have hfe : f (fun _ => True) = f (fun w => w = false) :=
    hf' false (UW1_toF true) (fun _ => True) (fun w => w = false) (fun v hv => by
      have hv' := MKW1_R_false hv
      subst hv'
      exact ⟨fun _ => rfl, fun _ => trivial⟩)
  have a1 : f (fun _ => True) = true := ((e1 : MKW1_Rel (fun _ => True) (f fun _ => True) true) rfl).mpr trivial
  have a2 : f (fun w => w = false) = true := hfe ▸ a1
  exact Bool.noConfusion (((e2 : MKW1_Rel (fun w => w = false) (f fun w => w = false) true) rfl).mp a2)


/-! ### Soundness at a single world

At `F`, identity within a type is identity at `F`, so LL≡ holds there. Soundness holds world by
world; so every theorem of PI is true at `F`. -/

/-- Truth at the world `w`, under every valuation admissible there. -/
def MKW1_ValidW (F : Frame) (w : F.U.W) {n : Nat} {Γ : Ctx n} (φ : Fm Γ) : Prop :=
  ∀ ρ, (∀ i, F.U.D w (ρ i)) → ∀ env, F.EnvAdm Γ ρ w env → F.HoldsAt φ ρ env w

/-- **Soundness at a single world.** -/
theorem MKW1_soundW (F : Frame) (w : F.U.W) {Ax : Fm Ctx.nil → Prop} (hM : F.IsModelAt)
    (hAx : ∀ φ, Ax φ → MKW1_ValidW F w φ) {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : Prov Ax Γ φ) :
    MKW1_ValidW F w φ := by
  induction h with
  | taut P as hP => intro ρ _ env _; exact (F.holdsAt_inst P as ρ env w).mpr (hP _)
  | instAll σ φ κ =>
    intro ρ _ env henv h
    show F.HoldsAt (φ.subst0 κ) ρ env w
    unfold Frame.HoldsAt; rw [Frame.eval_subst0]
    exact (F.holdsAt_all σ φ ρ env w).mp h _ ((F.relV_iff σ ρ w _ _).mp (F.adm_eval κ ρ w env henv))
  | distAll σ φ ψ =>
    intro ρ _ env _ h hφ
    refine (F.holdsAt_all σ ψ ρ env w).mpr fun v hv => ?_
    have h' := (F.holdsAt_all σ _ ρ env w).mp h v hv
    have hw : F.HoldsAt (φ.wk σ) ρ (env, v) w := by unfold Frame.HoldsAt; rw [Frame.eval_wk]; exact hφ
    exact h' hw
  | dualEx σ φ =>
    intro ρ _ env _
    refine (F.holdsAt_ex σ φ ρ env w).trans ?_
    refine Iff.trans ?_ (not_congr (F.holdsAt_all σ φ.neg ρ env w)).symm
    constructor
    · rintro ⟨v, hv, h⟩ h'; exact h' v hv h
    · intro h; exact Classical.byContradiction fun hn => h fun v hv h' => hn ⟨v, hv, h'⟩
  | instTAll φ σ =>
    intro ρ hρ env _ h
    exact cast ((congrArg (fun f : F.U.W → Prop => f w)) (eq_of_heq (F.eval_tinst φ σ ρ env))).symm
      (h (F.U.code σ.1 ρ) (F.D_code σ.1 w ρ hρ σ.2))
  | distTAll φ ψ =>
    intro ρ _ env _ h hφ a ha
    exact h a ha (cast ((congrArg (fun f : F.U.W → Prop => f w)) (eq_of_heq (F.eval_twk φ a ρ env))).symm hφ)
  | dualTEx φ =>
    intro ρ _ env _
    show (∃ a, F.U.D w a ∧ F.HoldsAt φ (scons a ρ) env w) ↔ ¬ ∀ a, F.U.D w a → ¬ F.HoldsAt φ (scons a ρ) env w
    constructor
    · rintro ⟨a, ha, h⟩ h'; exact h' a ha h
    · intro h; exact Classical.byContradiction fun hn => h fun a ha h' => hn ⟨a, ha, h'⟩
  | beta h => intro ρ _ env _; exact Iff.of_eq ((congrArg (fun f : F.U.W → Prop => f w)) (F.eval_betaEq h ρ env))
  | refEqv => exact hM.refEqv w
  | symEqv => exact hM.symEqv w
  | transEqv => exact hM.transEqv w
  | refTeq => exact hM.refTeq w
  | llTeq Q => exact hM.llTeq Q w
  | ax h => exact hAx _ h
  | mp _ _ ih1 ih2 => intro ρ hρ env henv; exact ih2 ρ hρ env henv (ih1 ρ hρ env henv)
  | genAll σ _ ih =>
    intro ρ hρ env henv
    exact (F.holdsAt_all σ _ ρ env w).mpr fun v hv => ih ρ hρ (env, v) ⟨henv, F.adm_of_rel σ ρ w v hv⟩
  | genTAll _ ih => intro ρ hρ env henv a ha; exact ih (scons a ρ) (fin_cases ha hρ) env henv
  | ren ρr _ ih =>
    intro ρ' hρ' env' henv'
    exact cast (F.holdsAt_of_heq (F.eval_ren _ ρr ρ' env' _ (F.pullEnv _ ρr ρ' env') (fun _ => rfl)
      (fun x => F.lookup_pull x ρr ρ' env')) w).symm
      (ih _ (fun i => hρ' _) _ (F.EnvAdm_pull _ ρr ρ' w env' henv'))
  | strengthen σ _ ih =>
    intro ρ hρ env henv
    obtain ⟨x, hx⟩ := F.U.adm_nonempty (F.U.code σ.1 ρ)
    have hv : F.U.rel (F.U.code σ.1 ρ) w (cast (Univ.El_code ρ σ.2).symm (cast (Univ.El_code ρ σ.2) x))
        (cast (Univ.El_code ρ σ.2).symm (cast (Univ.El_code ρ σ.2) x)) := by
      rw [cast_cast, cast_eq]; exact hx w
    have := ih ρ hρ (env, cast (Univ.El_code ρ σ.2) x) ⟨henv, F.adm_of_rel σ ρ w _ hv⟩
    unfold Frame.HoldsAt at this
    rwa [Frame.eval_wk] at this
  | tstrengthen _ ih =>
    intro ρ hρ env henv
    exact cast (F.holdsAt_of_heq (F.eval_twk _ .e ρ env) w) (ih (scons .e ρ) (fin_cases (F.U.D_e w) hρ) env henv)

/-- LL≡ holds at `F`. -/
theorem MKW1_LLEqv_F : MKW1_ValidW KW1 false LLEqv := by
  intro ρ _ env _
  refine (KW1.holdsAt_tall _ _ _ false).mpr fun a _ => ?_
  refine (KW1.holdsAt_all _ _ _ _ false).mpr fun x _ => (KW1.holdsAt_all _ _ _ _ false).mpr fun y _ => ?_
  refine (KW1.holdsAt_imp _ _ _ _ false).mpr fun hxy => ?_
  refine (KW1.holdsAt_all _ _ _ _ false).mpr fun G hG => (KW1.holdsAt_imp _ _ _ _ false).mpr fun hGx => ?_
  have hxy' : UW1.rel a false x y := (KW1_same _ _ _ false).mp ((KW1.holdsAt_eqv _ _ _ _ _ _ false).mp hxy)
  have hG' : UW1.rel (.arr a .t) false G G := hG
  exact (hG' false (UW1.Rrefl false) x y hxy' false (UW1.Rrefl false)).mp hGx

/-- Every theorem of PI is true at `F`. -/
theorem MKW1_PIP_F {n : Nat} {Γ : Ctx n} {θ : Fm Γ} (h : PIP Γ θ) : MKW1_ValidW KW1 false θ :=
  MKW1_soundW KW1 false KW1_isModelAt (fun χ (e : χ = LLEqv) => e ▸ MKW1_LLEqv_F) h

theorem MKW1_validAt_closeCtx : ∀ {n : Nat} (Γ : Ctx n) (χ : Fm Γ),
    (∀ w ρ, (∀ i, KW1.U.D w (ρ i)) → ∀ env, KW1.EnvAdm Γ ρ w env → KW1.HoldsAt χ ρ env w) →
    KW1.ValidAt (closeCtx Γ χ)
  | _, .nil, _, h => h
  | _, .ext Γ σ, χ, h => MKW1_validAt_closeCtx Γ (Tm.all σ χ) fun w ρ hρ env henv =>
      (KW1.holdsAt_all σ χ ρ env w).mpr fun v hv => h w ρ hρ (env, v) ⟨henv, KW1.adm_of_rel σ ρ w v hv⟩
  | _, .text Γ, χ, h => MKW1_validAt_closeCtx Γ (Tm.tall χ) fun w ρ hρ env henv =>
      (KW1.holdsAt_tall χ ρ env w).mpr fun a ha => h w (scons a ρ) (fin_cases ha hρ) env henv

/-- **Classicism**, at every world: identity of propositions, and of properties, is agreement at
`F`, and every theorem of PI is true at `F`. -/
theorem MKW1_Class_validAt : ∀ χ, ClassSch χ → KW1.ValidAt χ := by
  rintro _ (⟨n, Γ, φ, ψ, hp, rfl⟩ | ⟨n, Γ, σ, φ, ψ, hp, rfl⟩)
  · refine MKW1_validAt_closeCtx Γ _ fun w ρ _ env henv => ?_
    refine ((KW1.holdsAt_eqv tyT tyT φ ψ ρ env w).trans (KW1_same _ _ _ w)).mpr ?_
    intro v hv
    have hv' := MKW1_R_false hv
    subst hv'
    exact (KW1.holdsAt_iff _ _ _ _ _).mp
      (MKW1_PIP_F hp ρ (fun _ => trivial) env (KW1.EnvAdm_mono ρ w false (UW1_toF w) env henv))
  · refine MKW1_validAt_closeCtx Γ _ fun w ρ _ env henv => ?_
    refine ((KW1.holdsAt_eqv σ.pred σ.pred _ _ ρ env w).trans (KW1_same _ _ _ w)).mpr ?_
    refine (KW1.relV_iff σ.pred ρ _ _ _).mp ?_
    have henvF := KW1.EnvAdm_mono ρ w false (UW1_toF w) env henv
    intro v hv u u' huu x hx
    have hA := KW1.adm_eval (Tm.lam σ φ) ρ false env henvF v hv u u' huu x hx
    have hu' : KW1.hom.Rel σ.1 ρ ρ (KW1.homRs ρ) x u' u' := by
      have h1 := (KW1.relV_iff σ ρ v u u').mp huu
      have h2 := UW1.rel_mono _ v x _ _ hx (UW1.rel_refl_right _ v _ _ h1)
      exact (KW1.relV_iff σ ρ x u' u').mpr h2
    have hx' : x = false := MKW1_R_false (UW1.Rtrans _ _ _ hv hx)
    subst hx'
    exact hA.trans ((KW1.holdsAt_iff _ _ _ _ _).mp (MKW1_PIP_F hp ρ (fun _ => trivial) (env, u') ⟨henvF, hu'⟩))

theorem MKW1_Class : ∀ χ, ClassSch χ → KW1.Valid χ := fun χ h ρ hρ env henv =>
  MKW1_Class_validAt χ h _ ρ hρ env henv

/-- Every theorem of PI⁻ together with Classicism is valid. -/
theorem MKW1_of_prov {φ : Fm Ctx.nil} (h : Prov ClassSch Ctx.nil φ) : KW1.Valid φ := fun ρ hρ env henv =>
  KW1.soundnessAt KW1_isModelAt MKW1_Class_validAt h _ ρ hρ env henv

theorem MKW1_Bool : ∀ φ, BoolSch φ → KW1.Valid φ := fun φ h => MKW1_of_prov (d_Bool_of_Class (fun _ h => h) φ h)

theorem MKW1_IdId : KW1.Valid IdId := MKW1_of_prov (d_IdId_of_Class (fun _ h => h))


/-! ### The polymorphic Leibniz laws hold

At the actual world a polymorphic predicate cannot tell apart two items identical at `F`. The
proof is by the fundamental lemma, for a family of admissible relations between items of one type:
at `F` the relation is identity at `F`, and at the actual world it is a bijection between the
classes of identity there, which preserves identity at `F`. Such families are closed under the
function-type construction; and for any two items `x`, `y` identical at `F` there is one relating
`x` to `y` at the actual world (it swaps the class of `x` with the class of `y`). -/

theorem MKW1_tr {a : Code Empty} {w : Bool} {x y z : UW1.El a} (h1 : UW1.rel a w x y) (h2 : UW1.rel a w y z) :
    UW1.rel a w x z := UW1.rel_trans a w x y z h1 h2

theorem MKW1_sy {a : Code Empty} {w : Bool} {x y : UW1.El a} (h : UW1.rel a w x y) : UW1.rel a w y x :=
  UW1.rel_symm a w x y h

theorem MKW1_mono {a : Code Empty} {x y : UW1.El a} (h : UW1.rel a true x y) : UW1.rel a false x y :=
  UW1.rel_mono a true false x y (UW1_toF true) h

theorem MKW1_resp {a : Code Empty} {w : Bool} {x y : UW1.El a} (z : UW1.El a) (h : UW1.rel a w x y) :
    UW1.rel a w x z ↔ UW1.rel a w y z :=
  ⟨fun h1 => MKW1_tr (MKW1_sy h) h1, fun h1 => MKW1_tr h h1⟩

/-- The relations of the family, at a type. -/
structure MKW1_Good (a : Code Empty) (S : Bool → UW1.El a → UW1.El a → Prop) : Prop where
  hF : ∀ x y, S false x y ↔ UW1.rel a false x y
  hTF : ∀ x y, S true x y → UW1.rel a false x y
  hTl : ∀ x y, S true x y → UW1.rel a true x x
  hTr : ∀ x y, S true x y → UW1.rel a true y y
  tot : ∀ x, UW1.rel a true x x → ∃ y, UW1.rel a true y y ∧ S true x y
  onto : ∀ y, UW1.rel a true y y → ∃ x, UW1.rel a true x x ∧ S true x y
  fn : ∀ x x' y y', S true x x' → S true y y' → (UW1.rel a true x y ↔ UW1.rel a true x' y')
  sat : ∀ x x' y y', S true x x' → UW1.rel a true x y → UW1.rel a true x' y' → S true y y'

def MKW1_flip {a : Code Empty} (S : Bool → UW1.El a → UW1.El a → Prop) : Bool → UW1.El a → UW1.El a → Prop :=
  fun u x y => S u y x

theorem MKW1_Good.flip {a : Code Empty} {S : Bool → UW1.El a → UW1.El a → Prop} (h : MKW1_Good a S) :
    MKW1_Good a (MKW1_flip S) where
  hF := fun x y => (h.hF y x).trans ⟨MKW1_sy, MKW1_sy⟩
  hTF := fun x y hxy => MKW1_sy (h.hTF y x hxy)
  hTl := fun x y hxy => h.hTr y x hxy
  hTr := fun x y hxy => h.hTl y x hxy
  tot := fun x hx => h.onto x hx
  onto := fun y hy => h.tot y hy
  fn := fun x x' y y' h1 h2 => (h.fn x' x y' y h1 h2).symm
  sat := fun x x' y y' h1 hxy hx'y' => h.sat x' x y' y h1 hx'y' hxy

theorem MKW1_Good.rel (a : Code Empty) : MKW1_Good a (UW1.rel a) where
  hF := fun _ _ => Iff.rfl
  hTF := fun _ _ h => MKW1_mono h
  hTl := fun x y h => UW1.rel_refl_left a true x y h
  hTr := fun x y h => UW1.rel_refl_right a true x y h
  tot := fun x hx => ⟨x, hx, hx⟩
  onto := fun x hx => ⟨x, hx, hx⟩
  fn := fun _ _ _ _ h1 h2 =>
    ⟨fun h => MKW1_tr (MKW1_tr (MKW1_sy h1) h) h2, fun h => MKW1_tr (MKW1_tr h1 h) (MKW1_sy h2)⟩
  sat := fun _ _ _ _ h1 h2 h3 => MKW1_tr (MKW1_tr (MKW1_sy h2) h1) h3

/-- The relation at a function type. -/
def MKW1_arr {a c : Code Empty} (S : Bool → UW1.El a → UW1.El a → Prop) (T : Bool → UW1.El c → UW1.El c → Prop) :
    Bool → UW1.El (.arr a c) → UW1.El (.arr a c) → Prop :=
  fun v f f' => ∀ u, UW1.R v u → ∀ x x', S u x x' → T u (f x) (f' x')

theorem MKW1_arr_flip {a c : Code Empty} (S : Bool → UW1.El a → UW1.El a → Prop)
    (T : Bool → UW1.El c → UW1.El c → Prop) (v : Bool) (f f' : UW1.El (.arr a c)) :
    MKW1_arr (MKW1_flip S) (MKW1_flip T) v f' f ↔ MKW1_arr S T v f f' :=
  ⟨fun h u hu x x' hs => h u hu x' x hs, fun h u hu x x' hs => h u hu x' x hs⟩

section ArrowLemmas
variable {a c : Code Empty} {S : Bool → UW1.El a → UW1.El a → Prop} {T : Bool → UW1.El c → UW1.El c → Prop}

theorem MKW1_arr_F (hS : MKW1_Good a S) (hT : MKW1_Good c T) (f f' : UW1.El (.arr a c)) :
    MKW1_arr S T false f f' ↔ UW1.rel (.arr a c) false f f' := by
  constructor
  · intro h v hv x y hxy
    have hv' := MKW1_R_false hv
    subst hv'
    exact (hT.hF _ _).mp (h false hv x y ((hS.hF x y).mpr hxy))
  · intro h u hu x x' hs
    have hu' := MKW1_R_false hu
    subst hu'
    exact (hT.hF _ _).mpr (h false hu x x' ((hS.hF x x').mp hs))

theorem MKW1_arr_TF (hS : MKW1_Good a S) (hT : MKW1_Good c T) {f f' : UW1.El (.arr a c)}
    (h : MKW1_arr S T true f f') : UW1.rel (.arr a c) false f f' :=
  (MKW1_arr_F hS hT f f').mp fun u _ => h u (Or.inl rfl)

theorem MKW1_arr_Tl (hS : MKW1_Good a S) (hT : MKW1_Good c T) {f f' : UW1.El (.arr a c)}
    (h : MKW1_arr S T true f f') : UW1.rel (.arr a c) true f f := by
  intro v _ x y hxy
  cases v with
  | false => exact UW1.rel_refl_left _ false f f' (MKW1_arr_TF hS hT h) false (UW1.Rrefl false) x y hxy
  | true =>
    obtain ⟨x', hx', hs⟩ := hS.tot x (UW1.rel_refl_left a true x y hxy)
    have hs2 := hS.sat x x' y x' hs hxy hx'
    have t1 := h true (UW1.Rrefl true) x x' hs
    have t2 := h true (UW1.Rrefl true) y x' hs2
    exact (hT.fn _ _ _ _ t1 t2).mpr (hT.hTr _ _ t1)

theorem MKW1_arr_Tr (hS : MKW1_Good a S) (hT : MKW1_Good c T) {f f' : UW1.El (.arr a c)}
    (h : MKW1_arr S T true f f') : UW1.rel (.arr a c) true f' f' :=
  MKW1_arr_Tl hS.flip hT.flip ((MKW1_arr_flip S T true f f').mpr h)

theorem MKW1_arr_tot (hS : MKW1_Good a S) (hT : MKW1_Good c T) (f : UW1.El (.arr a c))
    (hf : UW1.rel (.arr a c) true f f) : ∃ f', UW1.rel (.arr a c) true f' f' ∧ MKW1_arr S T true f f' := by
  have hfT : ∀ x y, UW1.rel a true x y → UW1.rel c true (f x) (f y) := fun x y h => hf true (UW1.Rrefl true) x y h
  have hfF : ∀ x y, UW1.rel a false x y → UW1.rel c false (f x) (f y) := fun x y h => hf false (UW1_toF true) x y h
  have hpick : ∀ x' : UW1.El a, ∃ x : UW1.El a, UW1.rel a true x' x' → (UW1.rel a true x x ∧ S true x x') := by
    intro x'
    by_cases hx' : UW1.rel a true x' x'
    · obtain ⟨x, hx, hs⟩ := hS.onto x' hx'
      exact ⟨x, fun _ => ⟨hx, hs⟩⟩
    · exact ⟨x', fun h => absurd h hx'⟩
  obtain ⟨pick, spick⟩ : ∃ pick : UW1.El a → UW1.El a, ∀ x', UW1.rel a true x' x' →
      (UW1.rel a true (pick x') (pick x') ∧ S true (pick x') x') :=
    ⟨fun x' => Classical.choose (hpick x'), fun x' => Classical.choose_spec (hpick x')⟩
  have hval : ∀ x' : UW1.El a, ∃ y : UW1.El c,
      (UW1.rel a true x' x' → UW1.rel c true y y ∧ T true (f (pick x')) y) ∧ (¬ UW1.rel a true x' x' → y = f x') := by
    intro x'
    by_cases hx' : UW1.rel a true x' x'
    · obtain ⟨y, hy, hty⟩ := hT.tot (f (pick x')) (hfT _ _ (spick x' hx').1)
      exact ⟨y, fun _ => ⟨hy, hty⟩, fun hn => absurd hx' hn⟩
    · exact ⟨f x', fun h => absurd h hx', fun _ => rfl⟩
  obtain ⟨f', sf'⟩ : ∃ f' : UW1.El a → UW1.El c, ∀ x',
      (UW1.rel a true x' x' → UW1.rel c true (f' x') (f' x') ∧ T true (f (pick x')) (f' x')) ∧
      (¬ UW1.rel a true x' x' → f' x' = f x') :=
    ⟨fun x' => Classical.choose (hval x'), fun x' => Classical.choose_spec (hval x')⟩
  have hB : ∀ x x', UW1.rel a false x x' → UW1.rel c false (f x) (f' x') := by
    intro x x' hxx'
    by_cases hx' : UW1.rel a true x' x'
    · have hsp := (spick x' hx').2
      have h1 : UW1.rel a false (pick x') x' := hS.hTF _ _ hsp
      have h2 : UW1.rel c false (f (pick x')) (f' x') := hT.hTF _ _ ((sf' x').1 hx').2
      exact MKW1_tr (hfF x (pick x') (MKW1_tr hxx' (MKW1_sy h1))) h2
    · rw [(sf' x').2 hx']
      exact hfF x x' hxx'
  refine ⟨f', ?_, ?_⟩
  · intro v _ x' y' hxy
    cases v with
    | false =>
      exact MKW1_tr (MKW1_sy (hB x' x' (UW1.rel_refl_left a false x' y' hxy))) (hB x' y' hxy)
    | true =>
      have hx' := UW1.rel_refl_left a true x' y' hxy
      have hy' := UW1.rel_refl_right a true x' y' hxy
      have hpq : UW1.rel a true (pick x') (pick y') := (hS.fn _ _ _ _ (spick x' hx').2 (spick y' hy').2).mpr hxy
      exact (hT.fn _ _ _ _ ((sf' x').1 hx').2 ((sf' y').1 hy').2).mp (hfT _ _ hpq)
  · intro u _ x x' hs
    cases u with
    | false => exact (hT.hF _ _).mpr (hB x x' ((hS.hF x x').mp hs))
    | true =>
      have hx' := hS.hTr x x' hs
      have hsp := (spick x' hx').2
      have hxp : UW1.rel a true x (pick x') := (hS.fn x x' (pick x') x' hs hsp).mpr hx'
      exact hT.sat _ _ _ _ ((sf' x').1 hx').2 (hfT _ _ (MKW1_sy hxp)) ((sf' x').1 hx').1

theorem MKW1_arr_onto (hS : MKW1_Good a S) (hT : MKW1_Good c T) (f' : UW1.El (.arr a c))
    (hf' : UW1.rel (.arr a c) true f' f') : ∃ f, UW1.rel (.arr a c) true f f ∧ MKW1_arr S T true f f' := by
  obtain ⟨f, hf, h⟩ := MKW1_arr_tot hS.flip hT.flip f' hf'
  exact ⟨f, hf, (MKW1_arr_flip S T true f f').mp h⟩

theorem MKW1_arr_fn1 (hS : MKW1_Good a S) (hT : MKW1_Good c T) {f f' g g' : UW1.El (.arr a c)}
    (hf : MKW1_arr S T true f f') (hg : MKW1_arr S T true g g') (hfg : UW1.rel (.arr a c) true f g) :
    UW1.rel (.arr a c) true f' g' := by
  intro v _ x' y' hxy
  cases v with
  | false =>
    have e : UW1.rel (.arr a c) false f' g' :=
      MKW1_tr (MKW1_tr (MKW1_sy (MKW1_arr_TF hS hT hf)) (MKW1_mono hfg)) (MKW1_arr_TF hS hT hg)
    exact e false (UW1.Rrefl false) x' y' hxy
  | true =>
    obtain ⟨x, hx, hs⟩ := hS.onto x' (UW1.rel_refl_left a true x' y' hxy)
    have hs2 := hS.sat x x' x y' hs hx hxy
    have t1 := hf true (UW1.Rrefl true) x x' hs
    have t2 := hg true (UW1.Rrefl true) x y' hs2
    exact (hT.fn _ _ _ _ t1 t2).mp (hfg true (UW1.Rrefl true) x x hx)

theorem MKW1_arr_sat (hS : MKW1_Good a S) (hT : MKW1_Good c T) {f f' g g' : UW1.El (.arr a c)}
    (hf : MKW1_arr S T true f f') (hfg : UW1.rel (.arr a c) true f g) (hfg' : UW1.rel (.arr a c) true f' g') :
    MKW1_arr S T true g g' := by
  intro u _ x x' hs
  cases u with
  | false =>
    have e : UW1.rel (.arr a c) false g g' :=
      MKW1_tr (MKW1_tr (MKW1_sy (MKW1_mono hfg)) (MKW1_arr_TF hS hT hf)) (MKW1_mono hfg')
    exact (hT.hF _ _).mpr (e false (UW1.Rrefl false) x x' ((hS.hF x x').mp hs))
  | true =>
    have t := hf true (UW1.Rrefl true) x x' hs
    exact hT.sat _ _ _ _ t (hfg true (UW1.Rrefl true) x x (hS.hTl x x' hs))
      (hfg' true (UW1.Rrefl true) x' x' (hS.hTr x x' hs))

theorem MKW1_Good.arr (hS : MKW1_Good a S) (hT : MKW1_Good c T) : MKW1_Good (.arr a c) (MKW1_arr S T) where
  hF := MKW1_arr_F hS hT
  hTF := fun _ _ h => MKW1_arr_TF hS hT h
  hTl := fun _ _ h => MKW1_arr_Tl hS hT h
  hTr := fun _ _ h => MKW1_arr_Tr hS hT h
  tot := MKW1_arr_tot hS hT
  onto := MKW1_arr_onto hS hT
  fn := fun _ _ _ _ hf hg => ⟨MKW1_arr_fn1 hS hT hf hg,
    MKW1_arr_fn1 hS.flip hT.flip ((MKW1_arr_flip S T true _ _).mpr hf) ((MKW1_arr_flip S T true _ _).mpr hg)⟩
  sat := fun _ _ _ _ hf hfg hfg' => MKW1_arr_sat hS hT hf hfg hfg'

end ArrowLemmas

/-- The admissible relations: the relations of the family, between items of one type. -/
def MKW1_Inv : KInv KW1 where
  Adm := fun _ a a' S => ∃ h : a' = a, ∃ S0 : Bool → UW1.El a → UW1.El a → Prop, HEq S S0 ∧ MKW1_Good a S0
  amono := fun h _ => h
  smono := by
    intro w a a' S hA u u' x x' _ hu h
    obtain ⟨rfl, S0, hS, hG⟩ := hA
    have e := eq_of_heq hS; subst e
    cases u' with
    | true =>
      have hu1 := MKW1_R_true hu
      subst hu1
      exact h
    | false =>
      cases u with
      | false => exact h
      | true => exact (hG.hF x x').mpr (hG.hTF x x' h)
  refl := fun _ a => ⟨rfl, UW1.rel a, HEq.rfl, MKW1_Good.rel a⟩
  arrow := by
    intro w a a' c c' S T hA hB
    obtain ⟨rfl, S0, hS, hGS⟩ := hA
    obtain ⟨rfl, T0, hT, hGT⟩ := hB
    have e1 := eq_of_heq hS; have e2 := eq_of_heq hT; subst e1; subst e2
    exact ⟨rfl, _, HEq.rfl, hGS.arr hGT⟩
  total := by
    intro w a a' S hA u _ x hx
    obtain ⟨rfl, S0, hS, hG⟩ := hA
    have e := eq_of_heq hS; subst e
    cases u with
    | true => exact hG.tot x hx
    | false => exact ⟨x, hx, (hG.hF x x).mpr hx⟩
  onto := by
    intro w a a' S hA u _ x hx
    obtain ⟨rfl, S0, hS, hG⟩ := hA
    have e := eq_of_heq hS; subst e
    cases u with
    | true => exact hG.onto x hx
    | false => exact ⟨x, hx, (hG.hF x x).mpr hx⟩
  teq := by
    intro w a a' b b' S T hA hB u _
    obtain ⟨rfl, _⟩ := hA
    obtain ⟨rfl, _⟩ := hB
    exact Iff.rfl
  eqv := by
    intro w a a' b b' S T hA hB u _ x x' y y' hx hy
    obtain ⟨rfl, S0, hS, hGS⟩ := hA
    obtain ⟨rfl, T0, hT, hGT⟩ := hB
    have e1 := eq_of_heq hS; have e2 := eq_of_heq hT; subst e1; subst e2
    have hx' : UW1.rel _ false x x' := by
      cases u with
      | true => exact hGS.hTF x x' hx
      | false => exact (hGS.hF x x').mp hx
    have hy' : UW1.rel _ false y y' := by
      cases u with
      | true => exact hGT.hTF y y' hy
      | false => exact (hGT.hF y y').mp hy
    exact KW1.eqv_resp false _ _ x x' y y' hx' hy'

/-- The relation swapping the class of `x₀` with the class of `y₀`, at the actual world. -/
def MKW1_sw (a : Code Empty) (x0 y0 : UW1.El a) : Bool → UW1.El a → UW1.El a → Prop
  | false, x, x' => UW1.rel a false x x'
  | true, x, x' => UW1.rel a true x x ∧ UW1.rel a true x' x' ∧
      (UW1.rel a true x x0 ↔ UW1.rel a true x' y0) ∧ (UW1.rel a true x y0 ↔ UW1.rel a true x' x0) ∧
      (UW1.rel a true x x' ∨ UW1.rel a true x x0 ∨ UW1.rel a true x y0)

theorem MKW1_sw_good (a : Code Empty) (x0 y0 : UW1.El a) (hx0 : UW1.rel a true x0 x0)
    (hy0 : UW1.rel a true y0 y0) (hxy : UW1.rel a false x0 y0) : MKW1_Good a (MKW1_sw a x0 y0) where
  hF := fun _ _ => Iff.rfl
  hTF := by
    intro x x' h
    obtain ⟨_, _, i1, i2, h3⟩ := h
    rcases h3 with h3 | h3 | h3
    · exact MKW1_mono h3
    · exact MKW1_tr (MKW1_mono h3) (MKW1_tr hxy (MKW1_sy (MKW1_mono (i1.mp h3))))
    · exact MKW1_tr (MKW1_mono h3) (MKW1_tr (MKW1_sy hxy) (MKW1_sy (MKW1_mono (i2.mp h3))))
  hTl := fun _ _ h => h.1
  hTr := fun _ _ h => h.2.1
  tot := by
    intro x hx
    by_cases h1 : UW1.rel a true x x0
    · exact ⟨y0, hy0, hx, hy0, ⟨fun _ => hy0, fun _ => h1⟩,
        ⟨fun h => MKW1_tr (MKW1_sy h) h1, fun h => MKW1_tr h1 (MKW1_sy h)⟩, Or.inr (Or.inl h1)⟩
    · by_cases h2 : UW1.rel a true x y0
      · exact ⟨x0, hx0, hx, hx0, ⟨fun h => absurd h h1, fun h => MKW1_tr h2 (MKW1_sy h)⟩,
          ⟨fun _ => hx0, fun _ => h2⟩, Or.inr (Or.inr h2)⟩
      · exact ⟨x, hx, hx, hx, ⟨fun h => absurd h h1, fun h => absurd h h2⟩,
          ⟨fun h => absurd h h2, fun h => absurd h h1⟩, Or.inl hx⟩
  onto := by
    intro x' hx'
    by_cases h1 : UW1.rel a true x' y0
    · exact ⟨x0, hx0, hx0, hx', ⟨fun _ => h1, fun _ => hx0⟩,
        ⟨fun h => MKW1_tr h1 (MKW1_sy h), fun h => MKW1_tr (MKW1_sy h) h1⟩, Or.inr (Or.inl hx0)⟩
    · by_cases h2 : UW1.rel a true x' x0
      · exact ⟨y0, hy0, hy0, hx', ⟨fun h => MKW1_tr h2 (MKW1_sy h), fun h => absurd h h1⟩,
          ⟨fun _ => h2, fun _ => hy0⟩, Or.inr (Or.inr hy0)⟩
      · exact ⟨x', hx', hx', hx', ⟨fun h => absurd h h2, fun h => absurd h h1⟩,
          ⟨fun h => absurd h h1, fun h => absurd h h2⟩, Or.inl hx'⟩
  fn := by
    intro x x' y y' hs hs'
    obtain ⟨_, _, i1, i2, h3⟩ := hs
    obtain ⟨_, _, j1, j2, k3⟩ := hs'
    constructor
    · intro hxy'
      by_cases h1 : UW1.rel a true x x0
      · exact MKW1_tr (i1.mp h1) (MKW1_sy (j1.mp ((MKW1_resp x0 hxy').mp h1)))
      · by_cases h2 : UW1.rel a true x y0
        · exact MKW1_tr (i2.mp h2) (MKW1_sy (j2.mp ((MKW1_resp y0 hxy').mp h2)))
        · have g1 : ¬ UW1.rel a true y x0 := fun h => h1 ((MKW1_resp x0 hxy').mpr h)
          have g2 : ¬ UW1.rel a true y y0 := fun h => h2 ((MKW1_resp y0 hxy').mpr h)
          have hxx : UW1.rel a true x x' := h3.elim id fun h => h.elim (fun h => absurd h h1) (fun h => absurd h h2)
          have hyy : UW1.rel a true y y' := k3.elim id fun h => h.elim (fun h => absurd h g1) (fun h => absurd h g2)
          exact MKW1_tr (MKW1_tr (MKW1_sy hxx) hxy') hyy
    · intro hxy'
      by_cases h1 : UW1.rel a true x' y0
      · exact MKW1_tr (i1.mpr h1) (MKW1_sy (j1.mpr ((MKW1_resp y0 hxy').mp h1)))
      · by_cases h2 : UW1.rel a true x' x0
        · exact MKW1_tr (i2.mpr h2) (MKW1_sy (j2.mpr ((MKW1_resp x0 hxy').mp h2)))
        · have g1 : ¬ UW1.rel a true y' y0 := fun h => h1 ((MKW1_resp y0 hxy').mpr h)
          have g2 : ¬ UW1.rel a true y' x0 := fun h => h2 ((MKW1_resp x0 hxy').mpr h)
          have hxx : UW1.rel a true x x' := h3.elim id fun h => h.elim (fun h => absurd (i1.mp h) h1)
            (fun h => absurd (i2.mp h) h2)
          have hyy : UW1.rel a true y y' := k3.elim id fun h => h.elim (fun h => absurd (j1.mp h) g1)
            (fun h => absurd (j2.mp h) g2)
          exact MKW1_tr (MKW1_tr hxx hxy') (MKW1_sy hyy)
  sat := by
    intro x x' y y' hs hxy' hx'y'
    obtain ⟨_, _, i1, i2, h3⟩ := hs
    refine ⟨UW1.rel_refl_right a true x y hxy', UW1.rel_refl_right a true x' y' hx'y',
      ((MKW1_resp x0 hxy').symm.trans (i1.trans (MKW1_resp y0 hx'y'))),
      ((MKW1_resp y0 hxy').symm.trans (i2.trans (MKW1_resp x0 hx'y'))), ?_⟩
    rcases h3 with h3 | h3 | h3
    · exact Or.inl (MKW1_tr (MKW1_tr (MKW1_sy hxy') h3) hx'y')
    · exact Or.inr (Or.inl ((MKW1_resp x0 hxy').mp h3))
    · exact Or.inr (Or.inr ((MKW1_resp y0 hxy').mp h3))

/-- At the actual world, a polymorphic predicate does not tell apart two items identical at `F`. -/
theorem MKW1_poly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : KW1.U.TEnv n)
    (env : KW1.U.Env Γ ρ) (henv : KW1.EnvAdm Γ ρ true env) (a : Code Empty) (x y : UW1.El a)
    (hx : UW1.rel a true x x) (hy : UW1.rel a true y y) (hxy : UW1.rel a false x y) :
    KW1.eval P ρ env a x true → KW1.eval P ρ env a y true := by
  have hG := MKW1_sw_good a x y hx hy hxy
  have hS : MKW1_sw a x y true x y :=
    ⟨hx, hy, ⟨fun _ => hy, fun _ => hx⟩, ⟨MKW1_sy, MKW1_sy⟩, Or.inr (Or.inl hx)⟩
  have hrel := MKW1_Inv.fundamental P ρ ρ (KW1.homRs ρ) true (fun i => MKW1_Inv.refl true (ρ i)) env env
    (KInv.EnvRel_indep KW1.hom MKW1_Inv Γ ρ ρ _ true env env henv) true (UW1.Rrefl true) a a
    (MKW1_sw a x y) ⟨rfl, _, HEq.rfl, hG⟩ true (UW1.Rrefl true) x y hS true (UW1.Rrefl true)
  exact hrel.mp

/-- The predicate of a polymorphic Leibniz law, at its two types. -/
theorem MKW1_evalP {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : KW1.U.TEnv n)
    (env : KW1.U.Env Γ ρ) (a b : Code Empty) (x : UW1.El a) (y : UW1.El b) :
    HEq (KW1.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y)) (KW1.eval P ρ env) := by
  have e1 : KW1.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y) =
      KW1.eval (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) :=
    KW1.eval_wk tv0 (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) y
  have e2 : KW1.eval (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) =
      KW1.eval P.twk.twk (scons b (scons a ρ)) env := KW1.eval_wk tv1 P.twk.twk (scons b (scons a ρ)) env x
  exact (heq_of_eq (e1.trans e2)).trans ((KW1.eval_twk P.twk b (scons a ρ) env).trans (KW1.eval_twk P a ρ env))

theorem MKW1_evalP1 {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : KW1.U.TEnv n)
    (env : KW1.U.Env Γ ρ) (a b : Code Empty) (x : UW1.El a) (y : UW1.El b) :
    KW1.HoldsAt (.app (.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (.var (.there .here))) (scons b (scons a ρ))
      ((env, x), y) true ↔ KW1.eval P ρ env a x true := by
  have h1 : HEq (KW1.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (scons b (scons a ρ)) ((env, x), y))
      (KW1.eval P ρ env a) :=
    (KW1.heq_eval_tapp ((P.twk.twk.wk tv1).wk tv0) tv1 (scons b (scons a ρ)) ((env, x), y)).trans (heq_dapp (P := fun c => UW1.El c → Bool → Prop)
      (Q := fun c => UW1.El c → Bool → Prop) (fun _ => rfl) (MKW1_evalP P ρ env a b x y) rfl)
  have e := congrFun (congrFun (eq_of_heq h1) x) true
  exact Iff.of_eq e

theorem MKW1_evalP0 {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : KW1.U.TEnv n)
    (env : KW1.U.Env Γ ρ) (a b : Code Empty) (x : UW1.El a) (y : UW1.El b) :
    KW1.HoldsAt (.app (.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (.var .here)) (scons b (scons a ρ))
      ((env, x), y) true ↔ KW1.eval P ρ env b y true := by
  have h1 : HEq (KW1.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (scons b (scons a ρ)) ((env, x), y))
      (KW1.eval P ρ env b) :=
    (KW1.heq_eval_tapp ((P.twk.twk.wk tv1).wk tv0) tv0 (scons b (scons a ρ)) ((env, x), y)).trans (heq_dapp (P := fun c => UW1.El c → Bool → Prop)
      (Q := fun c => UW1.El c → Bool → Prop) (fun _ => rfl) (MKW1_evalP P ρ env a b x y) rfl)
  have e := congrFun (congrFun (eq_of_heq h1) y) true
  exact Iff.of_eq e

/-- LL≡/≈ holds, for every polymorphic predicate, with parameters. -/
theorem MKW1_Bridge {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : KW1.Valid (Bridge P) := by
  intro ρ _ env henv
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => (KW1.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (KW1.holdsAt_all _ _ _ _ _).mpr fun x hx => (KW1.holdsAt_all _ _ _ _ _).mpr fun y hy => ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun h => (KW1.holdsAt_imp _ _ _ _ _).mpr fun hPx => ?_
  obtain ⟨h1, h2⟩ := (KW1.holdsAt_conj _ _ _ _ _).mp h
  have eab : a = b := (KW1.holdsAt_teq _ _ _ _ _).mp h2
  subst eab
  have hxy : UW1.rel a false x y := (KW1_same _ _ _ _).mp ((KW1.holdsAt_eqv _ _ _ _ _ _ _).mp h1)
  exact (MKW1_evalP0 P ρ env a a x y).mpr
    (MKW1_poly P ρ env henv a x y hx hy hxy ((MKW1_evalP1 P ρ env a a x y).mp hPx))

/-- LL≡-Poly holds, for every polymorphic predicate, with parameters. -/
theorem MKW1_LLPoly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : KW1.Valid (LLPoly P) := by
  intro ρ _ env henv
  refine (KW1.holdsAt_tall _ _ _ _).mpr fun a _ => (KW1.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (KW1.holdsAt_all _ _ _ _ _).mpr fun x hx => (KW1.holdsAt_all _ _ _ _ _).mpr fun y hy => ?_
  refine (KW1.holdsAt_imp _ _ _ _ _).mpr fun h => (KW1.holdsAt_imp _ _ _ _ _).mpr fun hPx => ?_
  have eab : a = b := ((KW1.holdsAt_eqv _ _ _ _ _ _ _).mp h).1
  subst eab
  have hxy : UW1.rel a false x y := (KW1_same _ _ _ _).mp ((KW1.holdsAt_eqv _ _ _ _ _ _ _).mp h)
  exact (MKW1_evalP0 P ρ env a a x y).mpr
    (MKW1_poly P ρ env henv a x y hx hy hxy ((MKW1_evalP1 P ρ env a a x y).mp hPx))

end Kr
end PIF
