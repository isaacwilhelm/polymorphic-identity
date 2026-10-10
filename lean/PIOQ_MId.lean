import PIBF

/-!
# Open questions: `𝔐_Id,T`, the Identity Identity and T without LL≡ or Truth

An algebraic model of PI⁻. A proposition is a truth value with a tag: `0` for the values of the
connectives, `1` for the values of `≡` and `≈`, `2` for the values of the quantifiers. There are two
entities. Identity is a = b plus an equivalence relation at each type: at `e` it identifies
everything; at `t`, it identifies equal propositions and also all the propositions with tag `1` or
`2`; at every other type it is equality.

So `⊤ = ¬⊥` (with tag `0`) is identified only with itself, which gives T; `x ≡ y` (tag `1`) and
`∀F(Fx → Fy)` (tag `2`) are always identified, which gives the Identity Identity; but the two
entities are identified although a property separates them, so LL≡ fails, and a true and a false
proposition (with tags `1` and `2`) are identified, so Truth fails.
-/
set_option autoImplicit false

namespace PIF
namespace Al

/-- Propositions are truth values with a tag. -/
def univIdT : Univ where
  P := Prop × Fin 3
  V := fun p => p.1
  p0 := (True, 0)
  E := Bool
  Base := Empty
  B := Empty.elim
  neE := ⟨true⟩
  neB := fun b => b.elim

/-- The items of type `t` with a nonzero tag; there are no such items at other types. -/
def nzIdT : (a : Code Empty) → univIdT.El a → Prop
  | .t => fun p => (p : Prop × Fin 3).2 ≠ 0
  | .e => fun _ => False
  | .base _ => fun _ => False
  | .arr _ _ => fun _ => False

/-- Identity: the same type, and either equal items, or entities, or propositions with nonzero tags. -/
def RIdT (a b : Code Empty) (x : univIdT.El a) (y : univIdT.El b) : Prop :=
  a = b ∧ (HEq x y ∨ a = .e ∨ (nzIdT a x ∧ nzIdT b y))

def MIdTF : Frame where
  U := univIdT
  eqv := fun a b x y => (RIdT a b x y, 1)
  teq := fun a b => (a = b, 1)
  neg := fun p => (¬ p.1, 0)
  imp := fun p q => (p.1 → q.1, 0)
  cnj := fun p q => (p.1 ∧ q.1, 0)
  dsj := fun p q => (p.1 ∨ q.1, 0)
  bic := fun p q => (p.1 ↔ q.1, 0)
  all := fun _ f => (∀ x, (f x).1, 2)
  ex := fun _ f => (∃ x, (f x).1, 2)
  tall := fun Q => (∀ a, (Q a).1, 2)
  tex := fun Q => (∃ a, (Q a).1, 2)
  hneg := fun _ => Iff.rfl
  himp := fun _ _ => Iff.rfl
  hcnj := fun _ _ => Iff.rfl
  hdsj := fun _ _ => Iff.rfl
  hbic := fun _ _ => Iff.rfl
  hall := fun _ _ => Iff.rfl
  hex := fun _ _ => Iff.rfl
  htall := fun _ => Iff.rfl
  htex := fun _ => Iff.rfl

theorem RIdT_symm (a b : Code Empty) (x : univIdT.El a) (y : univIdT.El b) (h : RIdT a b x y) :
    RIdT b a y x := by
  obtain ⟨e, h⟩ := h
  subst e
  refine ⟨rfl, ?_⟩
  rcases h with h | h | ⟨h1, h2⟩
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h2, h1⟩)

theorem RIdT_trans (a b c : Code Empty) (x : univIdT.El a) (y : univIdT.El b) (z : univIdT.El c)
    (h1 : RIdT a b x y) (h2 : RIdT b c y z) : RIdT a c x z := by
  obtain ⟨e1, h1⟩ := h1
  obtain ⟨e2, h2⟩ := h2
  subst e1; subst e2
  refine ⟨rfl, ?_⟩
  rcases h1 with h1 | h1 | ⟨h1, h1'⟩
  · cases h1; exact h2
  · exact Or.inr (Or.inl h1)
  · rcases h2 with h2 | h2 | ⟨_, h2'⟩
    · cases h2; exact Or.inr (Or.inr ⟨h1, h1'⟩)
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨h1, h2'⟩)

theorem MIdT_model : MIdTF.IsModelPIm :=
  MIdTF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => ⟨rfl, Or.inl HEq.rfl⟩) RIdT_symm RIdT_trans

/-! ### The values of `⊥`, `⊤`, and the tags of compound formulas -/

theorem MIdT_bot {n : Nat} {Γ : Ctx n} (ρ : MIdTF.U.TEnv n) (env : MIdTF.U.Env Γ ρ) :
    MIdTF.eval (botF : Fm Γ) ρ env = (False, 2) :=
  (MIdTF.eval_all (Γ := Γ) tyT (.var .here) ρ env).trans
    (Prod.ext (propext ⟨fun h => h (False, 0), False.elim⟩) rfl)

theorem MIdT_top {n : Nat} {Γ : Ctx n} (ρ : MIdTF.U.TEnv n) (env : MIdTF.U.Env Γ ρ) :
    MIdTF.eval (topF : Fm Γ) ρ env = (True, 0) :=
  Prod.ext (propext (iff_true_intro (MIdTF.holds_topF ρ env ⟨(False, 0), id⟩))) rfl

theorem MIdT_tag_eqv {n : Nat} {Γ : Ctx n} (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1)
    (ρ : MIdTF.U.TEnv n) (env : MIdTF.U.Env Γ ρ) : (MIdTF.eval (Tm.eqv σ τ x y) ρ env).2 = 1 :=
  congrArg Prod.snd (MIdTF.eval_eqv σ τ x y ρ env)

theorem MIdT_tag_teq {n : Nat} {Γ : Ctx n} (σ τ : Ty n) (ρ : MIdTF.U.TEnv n) (env : MIdTF.U.Env Γ ρ) :
    (MIdTF.eval (Tm.teq (Γ := Γ) σ τ) ρ env).2 = 1 :=
  congrArg Prod.snd (MIdTF.eval_teq σ τ ρ env)

theorem MIdT_nz_eqv {n : Nat} {Γ : Ctx n} (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1)
    (ρ : MIdTF.U.TEnv n) (env : MIdTF.U.Env Γ ρ) : nzIdT .t (MIdTF.eval (Tm.eqv σ τ x y) ρ env) :=
  fun e => absurd ((MIdT_tag_eqv σ τ x y ρ env).symm.trans e) (by decide)

theorem MIdT_nz_teq {n : Nat} {Γ : Ctx n} (σ τ : Ty n) (ρ : MIdTF.U.TEnv n) (env : MIdTF.U.Env Γ ρ) :
    nzIdT .t (MIdTF.eval (Tm.teq (Γ := Γ) σ τ) ρ env) :=
  fun e => absurd ((MIdT_tag_teq σ τ ρ env).symm.trans e) (by decide)

theorem MIdT_tag_all {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MIdTF.U.TEnv n)
    (env : MIdTF.U.Env Γ ρ) : (MIdTF.eval (Tm.all σ φ) ρ env).2 = 2 :=
  congrArg Prod.snd (MIdTF.eval_all σ φ ρ env)

theorem MIdT_nz_all {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MIdTF.U.TEnv n)
    (env : MIdTF.U.Env Γ ρ) : nzIdT .t (MIdTF.eval (Tm.all σ φ) ρ env) :=
  fun e => absurd ((MIdT_tag_all σ φ ρ env).symm.trans e) (by decide)

/-- `□φ` holds just in case the value of `φ` is `⊤`. -/
theorem MIdT_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MIdTF.U.TEnv n) (env : MIdTF.U.Env Γ ρ) :
    MIdTF.Holds (boxF φ) ρ env ↔ MIdTF.eval φ ρ env = (True, 0) := by
  refine (MIdTF.holds_eqv_t _ _ _ _).trans ⟨fun h => ?_, fun h => ⟨rfl, Or.inl (heq_of_eq (h.trans (MIdT_top ρ env).symm))⟩⟩
  rcases h.2 with h | h | ⟨_, h⟩
  · exact (eq_of_heq h).trans (MIdT_top ρ env)
  · exact nomatch h
  · exact absurd (congrArg Prod.snd (MIdT_top ρ env)) h

theorem MIdT_holds_of_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MIdTF.U.TEnv n) (env : MIdTF.U.Env Γ ρ)
    (h : MIdTF.Holds (boxF φ) ρ env) : MIdTF.Holds φ ρ env := by
  show MIdTF.U.V (MIdTF.eval φ ρ env)
  rw [(MIdT_box φ ρ env).mp h]
  exact trivial

/-- A formula whose value has a nonzero tag is never necessary. -/
theorem MIdT_not_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MIdTF.U.TEnv n) (env : MIdTF.U.Env Γ ρ)
    (h : (MIdTF.eval φ ρ env).2 ≠ 0) : ¬ MIdTF.Holds (boxF φ) ρ env := fun hb =>
  h (congrArg Prod.snd ((MIdT_box φ ρ env).mp hb))

theorem MIdT_tag_of_box {n : Nat} {Γ : Ctx n} {φ : Fm Γ} {ρ : MIdTF.U.TEnv n} {env : MIdTF.U.Env Γ ρ}
    (h : MIdTF.Holds (boxF φ) ρ env) : (MIdTF.eval φ ρ env).2 = 0 :=
  congrArg Prod.snd ((MIdT_box φ ρ env).mp h)

/-! ### The principles -/

theorem MIdT_IdId : MIdTF.Valid IdId := by
  intro ρ env
  refine (MIdTF.holds_tall _ _ _).mpr fun a => ?_
  refine (MIdTF.holds_all _ _ _ _).mpr fun x => (MIdTF.holds_all _ _ _ _).mpr fun y => ?_
  exact (MIdTF.holds_eqv_t _ _ _ _).mpr ⟨rfl, Or.inr (Or.inr ⟨MIdT_nz_eqv _ _ _ _ _ _, MIdT_nz_all _ _ _ _⟩)⟩

theorem MIdT_TAx : MIdTF.Valid TAx := by
  intro ρ env
  refine (MIdTF.holds_all _ _ _ _).mpr fun p => (MIdTF.holds_imp _ _ _ _).mpr fun h => ?_
  exact MIdT_holds_of_box _ _ _ h

theorem MIdT_TopBot : MIdTF.Valid TopBot := by
  intro ρ env
  refine (MIdTF.holds_neg _ _ _).mpr fun h => ?_
  rcases ((MIdTF.holds_eqv_t _ _ _ _).mp h).2 with h | h | ⟨h, _⟩
  · have e : ((True, 0) : Prop × Fin 3) = (False, 2) :=
      (MIdT_top ρ env).symm.trans ((eq_of_heq h).trans (MIdT_bot ρ env))
    exact absurd (congrArg Prod.snd e) (by decide)
  · exact nomatch h
  · exact h (congrArg Prod.snd (MIdT_top ρ env))

theorem MIdT_not_LLEqv : ¬ MIdTF.Valid LLEqv := fun h => by
  have h0 := (MIdTF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e
  have h1 := (MIdTF.holds_all _ _ _ _).mp ((MIdTF.holds_all _ _ _ _).mp h0 true) false
  have h2 := (MIdTF.holds_imp _ _ _ _).mp h1
    ((MIdTF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, Or.inr (Or.inl rfl)⟩)
  have h3 := (MIdTF.holds_imp _ _ _ _).mp ((MIdTF.holds_all _ _ _ _).mp h2
    (fun z : Bool => ((z = true : Prop), (0 : Fin 3)))) rfl
  exact Bool.false_ne_true h3

theorem MIdT_not_Truth : ¬ MIdTF.Valid Truth := fun h => by
  have h0 := (MIdTF.holds_all _ _ _ _).mp ((MIdTF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ())
    ((True, 1) : Prop × Fin 3)) ((False, 2) : Prop × Fin 3)
  have h1 := (MIdTF.holds_imp _ _ _ _).mp h0 ((MIdTF.holds_eqv_t _ _ _ _).mpr
    ⟨rfl, Or.inr (Or.inr ⟨(by decide : (1 : Fin 3) ≠ 0), (by decide : (2 : Fin 3) ≠ 0)⟩)⟩)
  exact (MIdTF.holds_imp _ _ _ _).mp h1 trivial

theorem MIdT_Disjoint : MIdTF.Valid Disjoint := by
  intro ρ env
  refine (MIdTF.holds_tall _ _ _).mpr fun a => (MIdTF.holds_tall _ _ _).mpr fun b => ?_
  refine (MIdTF.holds_imp _ _ _ _).mpr fun hn => ?_
  refine (MIdTF.holds_all _ _ _ _).mpr fun x => (MIdTF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MIdTF.holds_neg _ _ _).mpr fun hxy => ?_
  exact (MIdTF.holds_neg _ _ _).mp hn ((MIdTF.holds_teq _ _ _ _).mpr ((MIdTF.holds_eqv _ _ _ _ _ _).mp hxy).1)

theorem MIdT_Slogan : MIdTF.Valid Slogan := by
  intro ρ env
  refine (MIdTF.holds_all _ _ _ _).mpr fun x => (MIdTF.holds_tall _ _ _).mpr fun b => ?_
  refine (MIdTF.holds_all _ _ _ _).mpr fun y => (MIdTF.holds_neg _ _ _).mpr fun hxy => ?_
  have h := ((MIdTF.holds_eqv _ _ _ _ _ _).mp hxy).1
  exact nomatch (show (Code.e : Code Empty) = .arr b .t from h)

theorem MIdT_Inj : MIdTF.Valid Inj := by
  intro ρ env
  refine (MIdTF.holds_tall _ _ _).mpr fun a => (MIdTF.holds_tall _ _ _).mpr fun b => ?_
  refine (MIdTF.holds_tall _ _ _).mpr fun c => (MIdTF.holds_tall _ _ _).mpr fun d => ?_
  refine (MIdTF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (MIdTF.holds_teq _ _ _ _).mp h
  exact (MIdTF.holds_conj _ _ _ _).mpr ⟨(MIdTF.holds_teq _ _ _ _).mpr (Code.arr.inj h').1,
    (MIdTF.holds_teq _ _ _ _).mpr (Code.arr.inj h').2⟩

theorem MIdT_Recovery : MIdTF.Valid Recovery := by
  intro ρ env
  refine (MIdTF.holds_tall _ _ _).mpr fun a => (MIdTF.holds_tall _ _ _).mpr fun b => ?_
  refine (MIdTF.holds_tall _ _ _).mpr fun c => (MIdTF.holds_tall _ _ _).mpr fun d => ?_
  refine (MIdTF.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (MIdTF.holds_teq _ _ _ _).mp ((MIdTF.holds_conj _ _ _ _).mp h).1
  exact (MIdTF.holds_teq _ _ _ _).mpr (Code.arr.inj h').2

/-- NI≈ fails: `α ≈ α` is true, but its value has tag `1`, so it is not `⊤`. -/
theorem MIdT_not_NITeq : ¬ MIdTF.Valid NITeq := fun h => by
  have h0 := (MIdTF.holds_tall _ _ _).mp ((MIdTF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e
  have h1 := (MIdTF.holds_imp _ _ _ _).mp h0 ((MIdTF.holds_teq _ _ _ _).mpr rfl)
  exact MIdT_not_box _ _ _ (MIdT_nz_teq (Γ := Ctx.nil.text.text) tv1 tv0 _ _) h1

theorem MIdT_NDTeq : MIdTF.Valid NDTeq := by
  intro ρ env
  refine (MIdTF.holds_tall _ _ _).mpr fun a => (MIdTF.holds_tall _ _ _).mpr fun b => ?_
  refine (MIdTF.holds_imp _ _ _ _).mpr fun h => (MIdT_box _ _ _).mpr ?_
  exact Prod.ext (propext (iff_true_intro h)) rfl

/-! ### Further principles -/

theorem MIdT_cast_ex {c : Code Empty} {A' : Type} (hA : univIdT.El c = A')
    (h : ((univIdT.El c → Prop × Fin 3) → Prop × Fin 3) = ((A' → Prop × Fin 3) → Prop × Fin 3))
    (Q : A' → Prop × Fin 3) : (cast h (fun R => MIdTF.ex c R) Q).2 = 2 := by
  subst hA; rfl

theorem MIdT_tag_ex {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MIdTF.U.TEnv n)
    (env : MIdTF.U.Env Γ ρ) : (MIdTF.eval (Tm.ex σ φ) ρ env).2 = 2 :=
  MIdT_cast_ex (Univ.El_code ρ σ.2) _ _

/-- A property of entities that holds of `true` but not of `false`. -/
def MIdT_G : Bool → Prop × Fin 3 := fun z => ((z = true : Prop), 0)

theorem MIdT_G_sep : ¬ RIdT .t .t (MIdT_G true) (MIdT_G false) := fun ⟨_, h⟩ => by
  rcases h with h | h | ⟨h, _⟩
  · have e : ((true = true : Prop), (0 : Fin 3)) = ((false = true : Prop), (0 : Fin 3)) := eq_of_heq h
    exact Bool.false_ne_true (cast (congrArg Prod.fst e) rfl)
  · exact nomatch h
  · exact h rfl

theorem MIdT_ExtT : MIdTF.Valid ExtT := by
  intro ρ env
  refine (MIdTF.holds_tall _ _ _).mpr fun a => (MIdTF.holds_tall _ _ _).mpr fun b => ?_
  refine (MIdTF.holds_imp _ _ _ _).mpr fun h => (MIdTF.holds_teq _ _ _ _).mpr ?_
  have hs := ((MIdTF.holds_conj _ _ _ _).mp h).1
  have x0 := Classical.choice (Univ.El_nonempty (U := MIdTF.U) a)
  obtain ⟨_, hy⟩ := (MIdTF.holds_ex _ _ _ _).mp ((MIdTF.holds_all _ _ _ _).mp hs x0)
  exact ((MIdTF.holds_eqv _ _ _ _ _ _).mp hy).1

theorem MIdT_IntT : MIdTF.Valid IntT := by
  intro ρ env
  refine (MIdTF.holds_tall _ _ _).mpr fun a => (MIdTF.holds_tall _ _ _).mpr fun b => ?_
  refine (MIdTF.holds_imp _ _ _ _).mpr fun h => (MIdTF.holds_teq _ _ _ _).mpr ?_
  have hs := MIdT_holds_of_box _ _ _ ((MIdTF.holds_conj _ _ _ _).mp h).1
  have x0 := Classical.choice (Univ.El_nonempty (U := MIdTF.U) a)
  obtain ⟨_, hy⟩ := (MIdTF.holds_ex _ _ _ _).mp ((MIdTF.holds_all _ _ _ _).mp hs x0)
  exact ((MIdTF.holds_eqv _ _ _ _ _ _).mp hy).1

theorem MIdT_Cantor : MIdTF.Valid Cantor := by
  intro ρ env
  refine (MIdTF.holds_tall _ _ _).mpr fun a =>
    (MIdTF.holds_ex _ _ _ _).mpr ⟨fun _ => ((True : Prop), (0 : Fin 3)), ?_⟩
  refine (MIdTF.holds_all _ _ _ _).mpr fun y => (MIdTF.holds_neg _ _ _).mpr fun h => ?_
  exact Code.arr_ne_left a .t ((MIdTF.holds_eqv _ _ _ _ _ _).mp h).1

theorem MIdT_tr_PCong : MIdTF.Holds PCong (fun i => i.elim0) () ↔
    ∀ (a c d : Code Empty) (f : univIdT.El a → univIdT.El c) (g : univIdT.El a → univIdT.El d)
      (x : univIdT.El a), RIdT (.arr a c) (.arr a d) f g → RIdT c d (f x) (g x) := Iff.rfl

theorem MIdT_PCong : MIdTF.Valid PCong :=
  (MIdTF.valid_iff_tr _).mpr (MIdT_tr_PCong.mpr fun a c d f g _ ⟨h1, h2⟩ => by
    have hcd : c = d := (Code.arr.inj h1).2
    subst hcd
    rcases h2 with h2 | h2 | ⟨h2, _⟩
    · cases h2; exact ⟨rfl, Or.inl HEq.rfl⟩
    · exact nomatch h2
    · exact (h2 : False).elim)

theorem MIdT_tr_Cong : MIdTF.Holds Cong (fun i => i.elim0) () ↔
    ∀ (a b c d : Code Empty) (f : univIdT.El a → univIdT.El c) (g : univIdT.El b → univIdT.El d)
      (x : univIdT.El a) (y : univIdT.El b),
      RIdT (.arr a c) (.arr b d) f g ∧ RIdT a b x y → RIdT c d (f x) (g y) := Iff.rfl

/-- Cong fails: the two entities are identified, but `MIdT_G` gives them distinct values. -/
theorem MIdT_not_Cong : ¬ MIdTF.Valid Cong := fun h =>
  MIdT_G_sep (MIdT_tr_Cong.mp ((MIdTF.valid_iff_tr _).mp h) .e .e .t .t MIdT_G MIdT_G true false
    ⟨⟨rfl, Or.inl HEq.rfl⟩, ⟨rfl, Or.inr (Or.inl rfl)⟩⟩)

theorem MIdT_tr_WCong : MIdTF.Holds WCong (fun i => i.elim0) () ↔
    ∀ (a b c d : Code Empty) (f : univIdT.El a → univIdT.El c) (g : univIdT.El b → univIdT.El d)
      (x : univIdT.El a) (y : univIdT.El b),
      (a = b ∧ c = d) ∧ (RIdT (.arr a c) (.arr b d) f g ∧ RIdT a b x y) → RIdT c d (f x) (g y) := Iff.rfl

theorem MIdT_not_WCong : ¬ MIdTF.Valid WCong := fun h =>
  MIdT_G_sep (MIdT_tr_WCong.mp ((MIdTF.valid_iff_tr _).mp h) .e .e .t .t MIdT_G MIdT_G true false
    ⟨⟨rfl, rfl⟩, ⟨rfl, Or.inl HEq.rfl⟩, ⟨rfl, Or.inr (Or.inl rfl)⟩⟩)

theorem MIdT_tr_PExt : MIdTF.Holds PExt (fun i => i.elim0) () ↔
    ∀ (a c d : Code Empty) (f : univIdT.El a → univIdT.El c) (g : univIdT.El a → univIdT.El d),
      (∀ x, RIdT c d (f x) (g x)) → RIdT (.arr a c) (.arr a d) f g := Iff.rfl

/-- PExt fails: the constant functions to the two entities have identified values but differ. -/
theorem MIdT_not_PExt : ¬ MIdTF.Valid PExt := fun h => by
  have h0 := MIdT_tr_PExt.mp ((MIdTF.valid_iff_tr _).mp h) .e .e .e (fun _ => true) (fun _ => false)
    (fun _ => ⟨rfl, Or.inr (Or.inl rfl)⟩)
  rcases h0.2 with h1 | h1 | ⟨h1, _⟩
  · exact Bool.noConfusion (congrFun (eq_of_heq h1 : (fun _ => true : Bool → Bool) = fun _ => false) true)
  · exact nomatch h1
  · exact (h1 : False).elim

theorem MIdT_not_Hae : ¬ MIdTF.Valid Hae := fun h => by
  have h0 := (MIdTF.holds_all _ _ _ _).mp ((MIdTF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) true
  exact Code.arr_ne_left .e .t ((MIdTF.holds_eqv _ _ _ _ _ _).mp h0).1.symm

theorem MIdT_not_Twin : ¬ MIdTF.Valid Twin := fun h => by
  have h0 := (MIdTF.holds_all _ _ _ _).mp ((MIdTF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) true
  obtain ⟨_, hb⟩ := (MIdTF.holds_tex _ _ _).mp h0
  have hb' := (MIdTF.holds_conj _ _ _ _).mp hb
  obtain ⟨_, hy⟩ := (MIdTF.holds_ex _ _ _ _).mp hb'.2
  exact (MIdTF.holds_neg _ _ _).mp hb'.1 ((MIdTF.holds_teq _ _ _ _).mpr ((MIdTF.holds_eqv _ _ _ _ _ _).mp hy).1)

/-- PropExt fails: `(True, 0)` and `(True, 1)` are both true, but not identified. -/
theorem MIdT_not_PropExt : ¬ MIdTF.Valid PropExt := fun h => by
  have h0 := (MIdTF.holds_all _ _ _ _).mp ((MIdTF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ())
    ((True, 0) : Prop × Fin 3)) ((True, 1) : Prop × Fin 3)
  have h1 := (MIdTF.holds_imp _ _ _ _).mp h0 ((MIdTF.holds_iff _ _ _ _).mpr ⟨fun _ => trivial, fun _ => trivial⟩)
  rcases ((MIdTF.holds_eqv_t _ _ _ _).mp h1).2 with h2 | h2 | ⟨h2, _⟩
  · exact absurd (congrArg Prod.snd (eq_of_heq h2) : (0 : Fin 3) = 1) (by decide)
  · exact nomatch h2
  · exact h2 rfl

/-- Collapse fails: `(True, 1)` is true, but is not `⊤`. -/
theorem MIdT_not_Collapse : ¬ MIdTF.Valid Collapse := fun h => by
  have h0 := (MIdTF.holds_imp _ _ _ _).mp ((MIdTF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ())
    ((True, 1) : Prop × Fin 3)) trivial
  have e := MIdT_tag_of_box h0
  exact (by decide : (1 : Fin 3) ≠ 0) e

theorem MIdT_not_NIEqv : ¬ MIdTF.Valid NIEqv := fun h => by
  have h0 := (MIdTF.holds_all _ _ _ _).mp ((MIdTF.holds_all _ _ _ _).mp
    ((MIdTF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) true) true
  have h1 := (MIdTF.holds_imp _ _ _ _).mp h0 ((MIdTF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, Or.inl HEq.rfl⟩)
  exact MIdT_not_box _ _ _ (MIdT_nz_eqv _ _ _ _ _ _) h1

theorem MIdT_not_NIX : ¬ MIdTF.Valid NIX := fun h => by
  have h0 := (MIdTF.holds_all _ _ _ _).mp ((MIdTF.holds_all _ _ _ _).mp
    ((MIdTF.holds_tall _ _ _).mp ((MIdTF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e) true) true
  have h1 := (MIdTF.holds_imp _ _ _ _).mp h0 ((MIdTF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, Or.inl HEq.rfl⟩)
  exact MIdT_not_box _ _ _ (MIdT_nz_eqv _ _ _ _ _ _) h1

theorem MIdT_NDX : MIdTF.Valid NDX := by
  intro ρ env
  refine (MIdTF.holds_tall _ _ _).mpr fun a => (MIdTF.holds_tall _ _ _).mpr fun b => ?_
  refine (MIdTF.holds_all _ _ _ _).mpr fun x => (MIdTF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MIdTF.holds_imp _ _ _ _).mpr fun h => (MIdT_box _ _ _).mpr ?_
  exact Prod.ext (propext (iff_true_intro h)) rfl

/-- Booleanism fails: `¬¬(True, 1)` is `(True, 0)`, which is not identified with `(True, 1)`. -/
theorem MIdT_not_DNeg : ¬ MIdTF.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MIdTF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) ((True, 1) : Prop × Fin 3)
  rcases ((MIdTF.holds_eqv_t _ _ _ _).mp h0).2 with h1 | h1 | ⟨h1, _⟩
  · exact absurd (congrArg Prod.snd (eq_of_heq h1) : (0 : Fin 3) = 1) (by decide)
  · exact nomatch h1
  · exact h1 rfl

theorem MIdT_not_Bool : ¬ ∀ φ, BoolSch φ → MIdTF.Valid φ := fun h => MIdT_not_DNeg (h _ DNeg_bool)

theorem MIdT_not_Class : ¬ ∀ χ, ClassSch χ → MIdTF.Valid χ := fun h =>
  MIdT_not_Bool fun φ hφ => MIdTF.soundness MIdT_model h (d_Bool_of_Class (S := ClassSch) (fun _ hc => hc) φ hφ)

/-- TCBF holds vacuously: the value of a type quantification is never `⊤`. -/
theorem MIdT_TCBF : ∀ χ, TCBFSch χ → MIdTF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MIdTF.holds_imp _ _ _ _).mpr fun h => ?_
  have e := MIdT_tag_of_box h
  exact ((by decide : (2 : Fin 3) ≠ 0) e).elim

/-- TBF fails, for `φ = ⊤`. -/
theorem MIdT_not_TBF : ¬ ∀ χ, TBFSch χ → MIdTF.Valid χ := fun h => by
  have h0 := h (TBFI (topF : Fm Ctx.nil.text)) ⟨_, rfl⟩ (fun i => i.elim0) ()
  have h1 := (MIdTF.holds_imp _ _ _ _).mp h0
    ((MIdTF.holds_tall _ _ _).mpr fun _ => (MIdT_box _ _ _).mpr (MIdT_top _ _))
  have e := MIdT_tag_of_box h1
  exact (by decide : (2 : Fin 3) ≠ 0) e

theorem MIdT_not_TNec : ¬ MIdTF.Valid TNec := fun h => by
  have e := MIdT_tag_of_box ((MIdTF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
  exact (by decide : (2 : Fin 3) ≠ 0) e

/-- BF fails, for the property of entities with value `⊤`. -/
theorem MIdT_not_BF : ¬ MIdTF.Valid BF := fun h => by
  have h0 := (MIdTF.holds_all _ _ _ _).mp ((MIdTF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ => ((True : Prop), (0 : Fin 3)))
  have h1 := (MIdTF.holds_imp _ _ _ _).mp h0 ((MIdTF.holds_all _ _ _ _).mpr fun _ => (MIdT_box _ _ _).mpr rfl)
  exact MIdT_not_box _ _ _ (MIdT_nz_all _ _ _ _) h1

/-- CBF holds vacuously: the value of a quantification is never `⊤`. -/
theorem MIdT_CBF : MIdTF.Valid CBF := by
  intro ρ env
  refine (MIdTF.holds_tall _ _ _).mpr fun _ => (MIdTF.holds_all _ _ _ _).mpr fun _ => ?_
  exact (MIdTF.holds_imp _ _ _ _).mpr fun h => absurd h (MIdT_not_box _ _ _ (MIdT_nz_all _ _ _ _))

theorem MIdT_not_Nec : ¬ MIdTF.Valid Nec := fun h => by
  have h0 := (MIdTF.holds_all _ _ _ _).mp ((MIdTF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) true
  exact MIdT_not_box _ _ _ (fun e => absurd ((MIdT_tag_ex _ _ _ _).symm.trans e) (by decide)) h0

theorem MIdT_Choice : MIdTF.Valid Choice := MIdTF.Choice_valid

/-- The polymorphic predicate `λγ:∗.λz:γ.∃_{γ→t}F (F ≡_{γ→t,t→t} λp:t.p ∧ F z)`: at `t`, it holds of
just the true propositions. -/
def PredIdT : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (Tm.ex tv0.pred (Tm.conj (Tm.eqv tv0.pred tyT.pred (.var .here) (.lam tyT (.var .here)))
    (.app (.var .here) (.var (.there .here))))))

theorem MIdT_tr_LLPolyId : MIdTF.Holds (LLPoly PredIdT) (fun i => i.elim0) () ↔
    ∀ (a b : Code Empty) (x : univIdT.El a) (y : univIdT.El b), RIdT a b x y →
      (∃ F : univIdT.El a → Prop × Fin 3, RIdT (.arr a .t) (.arr .t .t) F (fun p => p) ∧ (F x).1) →
      (∃ G : univIdT.El b → Prop × Fin 3, RIdT (.arr b .t) (.arr .t .t) G (fun p => p) ∧ (G y).1) := Iff.rfl

/-- LL≡-Poly fails, for `PredIdT`: `(True, 1)` and `(False, 2)` are identified. -/
theorem MIdT_not_LLPoly : ¬ MIdTF.Valid (LLPoly PredIdT) := fun h => by
  have h0 := MIdT_tr_LLPolyId.mp ((MIdTF.valid_iff_tr _).mp h) .t .t ((True, 1) : Prop × Fin 3)
    ((False, 2) : Prop × Fin 3)
    ⟨rfl, Or.inr (Or.inr ⟨(by decide : (1 : Fin 3) ≠ 0), (by decide : (2 : Fin 3) ≠ 0)⟩)⟩
    ⟨fun p => p, ⟨rfl, Or.inl HEq.rfl⟩, trivial⟩
  obtain ⟨G, ⟨_, hG⟩, hy⟩ := h0
  rcases hG with hG | hG | ⟨hG, _⟩
  · have e : G = fun p => p := eq_of_heq hG
    subst e
    exact hy
  · exact nomatch hG
  · exact (hG : False).elim

end Al
end PIF
