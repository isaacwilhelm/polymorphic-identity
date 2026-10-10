import PIBF
set_option autoImplicit false

/-!
# Open questions: the profile of `𝔐_T,hae`

`𝔐_T,hae` (`MTH`, `lean/PIHaeQs.lean`) is an algebraic model with three propositions `0`, `1`, `2`:
`0` and `1` are true, `2` is false. The connectives, the quantifiers, `≡` and `≈` take only the
values `0` and `2`. `≈` is identity of types. Items are identified just in case they have the same
root (got by stripping off haecceities), except that the propositions `1` and `2` are identified.

Since `□φ` is `φ ≡ ⊤`, and only `0` is identified with `⊤ = 0`, `□φ` holds just in case the value of
`φ` is `0`. Every formula headed by a constant has value `0` or `2`, so for such formulas `□φ` is
equivalent to `φ`; only atomic propositions (such as `1`) can be true without being necessary.

Valid: Inj≈, Recovery, Cantor, PCong, Ext≈, Int≈, NI≡, NI≈, ND≈, NI×, ND×, TBF, TCBF (by a logical
relation: every closed formula has value `0` or `2`), TNec, BF, Nec.
Refuted: LL≡/≈ (for `MTH_PredT`), Cong, WCong, PExt, Booleanism, the Identity Identity, CBF,
Classicism.
-/

namespace PIF
namespace Al
open Tm

/-! ## Basic facts -/

theorem MTH_mk3_ne1 (c : Prop) : mk3 c ≠ (1 : Fin 3) := by
  unfold mk3
  split
  · decide
  · decide

theorem MTH_fin0 : ∀ p : Fin 3, p ≠ 1 → VT p → p = 0 := by
  unfold VT; decide

theorem MTH_simT_eq : ∀ p q : Fin 3, simT p q → p ≠ 1 → q ≠ 1 → p = q := by
  unfold simT; decide

theorem MTH_V_teq (a b : Code Empty) : MTH.U.V (MTH.teq a b) ↔ a = b := mk3_V VT VT0 VT2 _

theorem MTH_V_eqv (a b : Code Empty) (x : (univ3 VT).El a) (y : (univ3 VT).El b) :
    MTH.U.V (MTH.eqv a b x y) ↔ Er3 VT simT (root3 VT simT a x) (root3 VT simT b y) := mk3_V VT VT0 VT2 _

/-- `□φ` holds just in case the value of `φ` is `0`. -/
theorem MTH_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MTH.U.TEnv n) (env : MTH.U.Env Γ ρ) :
    MTH.Holds (boxF φ) ρ env ↔ @Eq (Fin 3) (MTH.eval φ ρ env) 0 := by
  refine (MTH.holds_eqv_t _ _ _ _).trans ((F3_eqT VT VT0 VT2 simT _ _ simT_refl).trans ?_)
  rw [F3_top VT VT0 VT2 simT (Γ := Γ) ρ env]
  exact ⟨fun h => h.elim id (fun h' => absurd rfl h'.2), Or.inl⟩

theorem MTH_holds_of_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MTH.U.TEnv n) (env : MTH.U.Env Γ ρ)
    (h : MTH.Holds (boxF φ) ρ env) : MTH.Holds φ ρ env :=
  (congrArg VT ((MTH_box φ ρ env).mp h)).mpr VT0

/-- A true formula whose value is not `1` is necessary. -/
theorem MTH_box_of {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MTH.U.TEnv n) (env : MTH.U.Env Γ ρ)
    (h1 : @Ne (Fin 3) (MTH.eval φ ρ env) 1) (h : MTH.Holds φ ρ env) : MTH.Holds (boxF φ) ρ env :=
  (MTH_box φ ρ env).mpr (MTH_fin0 _ h1 h)

theorem MTH_cast_ex_eq {c : Code Empty} {A' : Type} (hA : MTH.U.El c = A')
    (h : ((MTH.U.El c → MTH.U.P) → MTH.U.P) = ((A' → MTH.U.P) → MTH.U.P)) (Q : A' → MTH.U.P) :
    cast h (fun R => MTH.ex c R) Q = MTH.ex c (fun x => Q (cast hA x)) := by
  subst hA; rfl

theorem MTH_eval_ex {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MTH.U.TEnv n)
    (env : MTH.U.Env Γ ρ) :
    MTH.eval (Tm.ex σ φ) ρ env = MTH.ex (MTH.U.code σ.1 ρ) (fun x => MTH.eval φ ρ (env, cast (Univ.El_code ρ σ.2) x)) :=
  MTH_cast_ex_eq (Univ.El_code ρ σ.2) _ _

theorem MTH_eqv_ne1 {n : Nat} {Γ : Ctx n} (σ τ : Ty n) (x : Tm Γ σ.1) (y : Tm Γ τ.1) (ρ : MTH.U.TEnv n)
    (env : MTH.U.Env Γ ρ) : @Ne (Fin 3) (MTH.eval (Tm.eqv σ τ x y) ρ env) 1 := fun h =>
  MTH_mk3_ne1 _ ((MTH.eval_eqv σ τ x y ρ env).symm.trans h)

theorem MTH_teq_ne1 {n : Nat} {Γ : Ctx n} (σ τ : Ty n) (ρ : MTH.U.TEnv n) (env : MTH.U.Env Γ ρ) :
    @Ne (Fin 3) (MTH.eval (Tm.teq σ τ : Fm Γ) ρ env) 1 := fun h =>
  MTH_mk3_ne1 _ ((MTH.eval_teq σ τ ρ env).symm.trans h)

theorem MTH_neg_ne1 {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MTH.U.TEnv n) (env : MTH.U.Env Γ ρ) :
    @Ne (Fin 3) (MTH.eval (Tm.neg φ) ρ env) 1 := MTH_mk3_ne1 _

theorem MTH_all_ne1 {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MTH.U.TEnv n)
    (env : MTH.U.Env Γ ρ) : @Ne (Fin 3) (MTH.eval (Tm.all σ φ) ρ env) 1 := fun h =>
  MTH_mk3_ne1 _ ((MTH.eval_all σ φ ρ env).symm.trans h)

theorem MTH_ex_ne1 {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MTH.U.TEnv n)
    (env : MTH.U.Env Γ ρ) : @Ne (Fin 3) (MTH.eval (Tm.ex σ φ) ρ env) 1 := fun h =>
  MTH_mk3_ne1 _ ((MTH_eval_ex σ φ ρ env).symm.trans h)

theorem MTH_tall_ne1 {n : Nat} {Γ : Ctx n} (φ : Fm (.text Γ)) (ρ : MTH.U.TEnv n) (env : MTH.U.Env Γ ρ) :
    @Ne (Fin 3) (MTH.eval (Tm.tall φ) ρ env) 1 := MTH_mk3_ne1 _

theorem MTH_tex_ne1 {n : Nat} {Γ : Ctx n} (φ : Fm (.text Γ)) (ρ : MTH.U.TEnv n) (env : MTH.U.Env Γ ρ) :
    @Ne (Fin 3) (MTH.eval (Tm.tex φ) ρ env) 1 := MTH_mk3_ne1 _

/-- Identified propositions neither of which is `1` are equally true. -/
theorem MTH_holds_eqv_t_good {n : Nat} {Γ : Ctx n} (φ ψ : Fm Γ) (ρ : MTH.U.TEnv n) (env : MTH.U.Env Γ ρ)
    (h : MTH.Holds (Tm.eqv tyT tyT φ ψ) ρ env) (h1 : @Ne (Fin 3) (MTH.eval φ ρ env) 1)
    (h2 : @Ne (Fin 3) (MTH.eval ψ ρ env) 1) : MTH.Holds φ ρ env ↔ MTH.Holds ψ ρ env :=
  Iff.of_eq (congrArg VT (MTH_simT_eq _ _
    ((F3_eqT VT VT0 VT2 simT _ _ simT_refl).mp ((MTH.holds_eqv_t _ _ _ _).mp h)) h1 h2))

/-! ## Roots -/

open Classical in
theorem MTH_root_t (a : Code (univ3 VT).Base) (f : (univ3 VT).El (.arr a .t)) :
    root3 VT simT (.arr a .t) f =
      if h : ∃ z, f = mkH3 VT a (fun y => Er3 VT simT (root3 VT simT a y) (root3 VT simT a z))
      then root3 VT simT a (Classical.choose h) else ⟨.arr a .t, f⟩ :=
  eroot_t _ _ _ a f

/-- A predicate is its own root, or it is the haecceity of an item whose root it has. -/
theorem MTH_root_own_or_hae (a : Code (univ3 VT).Base) (f : (univ3 VT).El (.arr a .t)) :
    root3 VT simT (.arr a .t) f = ⟨.arr a .t, f⟩ ∨
      ∃ z, f = mkH3 VT a (fun y => Er3 VT simT (root3 VT simT a y) (root3 VT simT a z)) ∧
        root3 VT simT (.arr a .t) f = root3 VT simT a z := by
  rw [MTH_root_t]
  split
  · next h => exact Or.inr ⟨Classical.choose h, Classical.choose_spec h, rfl⟩
  · exact Or.inl rfl

/-- A predicate that never takes the value `0` is not a haecceity, so it is its own root. -/
theorem MTH_root_own_no0 (a : Code (univ3 VT).Base) (f : (univ3 VT).El (.arr a .t)) (hf : ∀ y, f y ≠ (0 : Fin 3)) :
    root3 VT simT (.arr a .t) f = ⟨.arr a .t, f⟩ := by
  rcases MTH_root_own_or_hae a f with h | ⟨z, hz, _⟩
  · exact h
  · exact absurd ((congrFun hz z).trans (mk3_eq0 (Or.inl rfl))) (hf z)

/-- A predicate that takes the value `1` is not a haecceity, so it is its own root. -/
theorem MTH_root_own_1 (a : Code (univ3 VT).Base) (f : (univ3 VT).El (.arr a .t)) (y : (univ3 VT).El a)
    (hy : f y = (1 : Fin 3)) : root3 VT simT (.arr a .t) f = ⟨.arr a .t, f⟩ := by
  rcases MTH_root_own_or_hae a f with h | ⟨z, hz, _⟩
  · exact h
  · exact absurd ((congrFun hz y).symm.trans hy) (MTH_mk3_ne1 _)

theorem MTH_root_lt : ∀ (a : Code (univ3 VT).Base) (x : (univ3 VT).El a),
    root3 VT simT a x = ⟨a, x⟩ ∨ csz (root3 VT simT a x).1 < csz a
  | .e, _ => Or.inl rfl
  | .t, _ => Or.inl rfl
  | .base b, _ => nomatch b
  | .arr _ .e, _ => Or.inl rfl
  | .arr _ (.base b), _ => nomatch b
  | .arr _ (.arr _ _), _ => Or.inl rfl
  | .arr a .t, f => by
    rcases MTH_root_own_or_hae a f with h | ⟨z, _, h⟩
    · exact Or.inl h
    · refine Or.inr ?_
      rw [h]
      rcases MTH_root_lt a z with e | e
      · rw [e]; show csz a < csz a + 1 + 1; omega
      · show _ < csz a + 1 + 1; omega

theorem MTH_root_le (a : Code (univ3 VT).Base) (x : (univ3 VT).El a) : csz (root3 VT simT a x).1 ≤ csz a := by
  rcases MTH_root_lt a x with e | e
  · rw [e]; exact Nat.le_refl _
  · exact Nat.le_of_lt e

/-- A function is its own root, or it is a predicate whose root has a code no larger than its domain. -/
theorem MTH_root_arr (a b : Code (univ3 VT).Base) (f : (univ3 VT).El (.arr a b)) :
    root3 VT simT (.arr a b) f = ⟨.arr a b, f⟩ ∨ (b = .t ∧ csz (root3 VT simT (.arr a b) f).1 ≤ csz a) := by
  cases b with
  | t =>
    rcases MTH_root_own_or_hae a f with h | ⟨z, _, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, by rw [h]; exact MTH_root_le a z⟩
  | e => exact Or.inl rfl
  | base x => exact nomatch x
  | arr _ _ => exact Or.inl rfl

theorem MTH_arr_ne_t (a b : Code (univ3 VT).Base) : Code.arr a b ≠ .t := fun h => by cases h

theorem MTH_Er3_fst {r s : Σ b : Code (univ3 VT).Base, (univ3 VT).El b} (h : Er3 VT simT r s) : r.1 = s.1 := by
  rcases h with rfl | ⟨p, q, rfl, rfl, _⟩ <;> rfl

theorem MTH_Er3_eq {r s : Σ b : Code (univ3 VT).Base, (univ3 VT).El b} (h : Er3 VT simT r s) (hr : r.1 ≠ .t) : r = s := by
  rcases h with h | ⟨p, q, e1, _, _⟩
  · exact h
  · exact absurd (congrArg Sigma.fst e1) hr

/-- Each type has an item that is its own root. -/
theorem MTH_own : ∀ c : Code (univ3 VT).Base, ∃ x : (univ3 VT).El c, root3 VT simT c x = ⟨c, x⟩
  | .arr a .t => ⟨fun _ => (1 : Fin 3), MTH_root_own_no0 a _ (fun _ => (by decide : (1 : Fin 3) ≠ 0))⟩
  | .e => ⟨(), rfl⟩
  | .t => ⟨(0 : Fin 3), rfl⟩
  | .base b => nomatch b
  | .arr _ .e => ⟨fun _ => (), rfl⟩
  | .arr _ (.base b) => nomatch b
  | .arr _ (.arr _ _) => ⟨Classical.choice (Univ.El_nonempty (U := univ3 VT) _), rfl⟩

/-- `λp.p` is identified only with itself. -/
theorem MTH_eq_id (F : (univ3 VT).El (.arr .t .t))
    (h : Er3 VT simT (root3 VT simT (.arr .t .t) F) (root3 VT simT (.arr .t .t) (fun p => p))) :
    F = fun p => p := by
  rw [MTH_root_own_1 .t (fun p => p) (1 : Fin 3) rfl] at h
  have hF := MTH_Er3_fst h
  rcases MTH_root_own_or_hae .t F with e | ⟨z, _, e⟩
  · rw [e] at h
    exact eq_of_heq (Sigma.mk.inj (MTH_Er3_eq h (MTH_arr_ne_t _ _))).2
  · rw [e] at hF
    exact absurd hF.symm (MTH_arr_ne_t _ _)

/-! ## Identity of types -/

theorem MTH_Inj : MTH.Valid Inj := by
  intro ρ env
  refine (MTH.holds_tall _ _ _).mpr fun a => (MTH.holds_tall _ _ _).mpr fun b => ?_
  refine (MTH.holds_tall _ _ _).mpr fun c => (MTH.holds_tall _ _ _).mpr fun d => ?_
  refine (MTH.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (MTH_V_teq _ _).mp ((MTH.holds_teq _ _ _ _).mp h)
  injection h' with hab hcd
  exact (MTH.holds_conj _ _ _ _).mpr ⟨(MTH.holds_teq _ _ _ _).mpr ((MTH_V_teq _ _).mpr hab),
    (MTH.holds_teq _ _ _ _).mpr ((MTH_V_teq _ _).mpr hcd)⟩

theorem MTH_Recovery : MTH.Valid Recovery := by
  intro ρ env
  refine (MTH.holds_tall _ _ _).mpr fun a => (MTH.holds_tall _ _ _).mpr fun b => ?_
  refine (MTH.holds_tall _ _ _).mpr fun c => (MTH.holds_tall _ _ _).mpr fun d => ?_
  refine (MTH.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d :=
    (MTH_V_teq _ _).mp ((MTH.holds_teq _ _ _ _).mp ((MTH.holds_conj _ _ _ _).mp h).1)
  exact (MTH.holds_teq _ _ _ _).mpr ((MTH_V_teq _ _).mpr (Code.arr.inj h').2)

/-- Mutually embeddable types are the same: compare the roots of items that are their own roots. -/
theorem MTH_ext_core (a b : Code (univ3 VT).Base)
    (h1 : ∀ x : (univ3 VT).El a, ∃ y : (univ3 VT).El b, Er3 VT simT (root3 VT simT a x) (root3 VT simT b y))
    (h2 : ∀ y : (univ3 VT).El b, ∃ x : (univ3 VT).El a, Er3 VT simT (root3 VT simT a x) (root3 VT simT b y)) :
    a = b := by
  obtain ⟨xa, hxa⟩ := MTH_own a
  obtain ⟨xb, hxb⟩ := MTH_own b
  obtain ⟨y, hy⟩ := h1 xa
  obtain ⟨x, hx⟩ := h2 xb
  have e1 := MTH_Er3_fst hy
  have e2 := MTH_Er3_fst hx
  rw [hxa] at e1
  rw [hxb] at e2
  rcases MTH_root_lt b y with h3 | h3
  · rw [h3] at e1; exact e1
  rcases MTH_root_lt a x with h4 | h4
  · rw [h4] at e2; exact e2
  rw [← e1] at h3
  rw [e2] at h4
  have c1 : csz a < csz b := h3
  have c2 : csz b < csz a := h4
  omega

theorem MTH_ExtT : MTH.Valid ExtT := by
  intro ρ env
  refine (MTH.holds_tall _ _ _).mpr fun a => (MTH.holds_tall _ _ _).mpr fun b => ?_
  refine (MTH.holds_imp _ _ _ _).mpr fun h => (MTH.holds_teq _ _ _ _).mpr ((MTH_V_teq _ _).mpr ?_)
  have hs := (MTH.holds_conj _ _ _ _).mp h
  refine MTH_ext_core a b (fun x => ?_) (fun y => ?_)
  · obtain ⟨y, hy⟩ := (MTH.holds_ex _ _ _ _).mp ((MTH.holds_all _ _ _ _).mp hs.1 x)
    exact ⟨y, (MTH_V_eqv _ _ _ _).mp ((MTH.holds_eqv _ _ _ _ _ _).mp hy)⟩
  · obtain ⟨x, hx⟩ := (MTH.holds_ex _ _ _ _).mp ((MTH.holds_all _ _ _ _).mp hs.2 y)
    exact ⟨x, (MTH_V_eqv _ _ _ _).mp ((MTH.holds_eqv _ _ _ _ _ _).mp hx)⟩

/-- `□(α ⊑ β)` implies `α ⊑ β`, so Int≈ follows as Ext≈ does. -/
theorem MTH_IntT : MTH.Valid IntT := by
  intro ρ env
  refine (MTH.holds_tall _ _ _).mpr fun a => (MTH.holds_tall _ _ _).mpr fun b => ?_
  refine (MTH.holds_imp _ _ _ _).mpr fun h => (MTH.holds_teq _ _ _ _).mpr ((MTH_V_teq _ _).mpr ?_)
  have hs := (MTH.holds_conj _ _ _ _).mp h
  have hs1 := MTH_holds_of_box _ _ _ hs.1
  have hs2 := MTH_holds_of_box _ _ _ hs.2
  refine MTH_ext_core a b (fun x => ?_) (fun y => ?_)
  · obtain ⟨y, hy⟩ := (MTH.holds_ex _ _ _ _).mp ((MTH.holds_all _ _ _ _).mp hs1 x)
    exact ⟨y, (MTH_V_eqv _ _ _ _).mp ((MTH.holds_eqv _ _ _ _ _ _).mp hy)⟩
  · obtain ⟨x, hx⟩ := (MTH.holds_ex _ _ _ _).mp ((MTH.holds_all _ _ _ _).mp hs2 y)
    exact ⟨x, (MTH_V_eqv _ _ _ _).mp ((MTH.holds_eqv _ _ _ _ _ _).mp hx)⟩

/-! ## Cantor -/

/-- The constant predicate `1` is its own root, so it is identified with nothing of a smaller type. -/
theorem MTH_Cantor : MTH.Valid Cantor := by
  intro ρ env
  refine (MTH.holds_tall _ _ _).mpr fun a => (MTH.holds_ex _ _ _ _).mpr
    ⟨fun _ => (1 : Fin 3), (MTH.holds_all _ _ _ _).mpr fun y => (MTH.holds_neg _ _ _).mpr fun h => ?_⟩
  have h1 : Er3 VT simT (root3 VT simT (.arr a .t) (fun _ => (1 : Fin 3))) (root3 VT simT a y) :=
    (MTH_V_eqv _ _ _ _).mp ((MTH.holds_eqv _ _ _ _ _ _).mp h)
  have h2 := MTH_Er3_fst h1
  rw [MTH_root_own_no0 a (fun _ => (1 : Fin 3)) (fun _ => (by decide : (1 : Fin 3) ≠ 0))] at h2
  have h3 := MTH_root_le a y
  rw [← h2] at h3
  have h4 : csz a + csz Code.t + 1 ≤ csz a := h3
  omega

/-! ## Congruence and extensionality -/

/-- Identified functions agree, up to identity, at each argument. -/
theorem MTH_PCong_core (a b c : Code (univ3 VT).Base) (f : (univ3 VT).El (.arr a b)) (g : (univ3 VT).El (.arr a c))
    (h : Er3 VT simT (root3 VT simT (.arr a b) f) (root3 VT simT (.arr a c) g)) (x : (univ3 VT).El a) :
    Er3 VT simT (root3 VT simT b (f x)) (root3 VT simT c (g x)) := by
  have big : ∀ d : Code (univ3 VT).Base, csz a < csz (Code.arr a d) := fun d => by
    show csz a < csz a + csz d + 1
    omega
  rcases MTH_root_arr a b f with hf | ⟨hb, hf⟩ <;> rcases MTH_root_arr a c g with hg | ⟨hc, hg⟩
  · rw [hf, hg] at h
    have e := MTH_Er3_eq h (MTH_arr_ne_t _ _)
    have e1 := (Sigma.mk.inj e).1
    injection e1 with _ e3
    subst e3
    have e4 : f = g := eq_of_heq (Sigma.mk.inj e).2
    subst e4
    exact Or.inl rfl
  · have e := MTH_Er3_fst h
    rw [hf] at e
    rw [← e] at hg
    exact absurd hg (Nat.not_le_of_lt (big b))
  · have e := MTH_Er3_fst h
    rw [hg] at e
    rw [e] at hf
    exact absurd hf (Nat.not_le_of_lt (big c))
  · subst hb
    subst hc
    rcases MTH_root_own_or_hae a f with hf' | ⟨z, hz, hf'⟩
    · rw [hf'] at hf
      exact absurd hf (Nat.not_le_of_lt (big .t))
    rcases MTH_root_own_or_hae a g with hg' | ⟨z', hz', hg'⟩
    · rw [hg'] at hg
      exact absurd hg (Nat.not_le_of_lt (big .t))
    rw [hf', hg'] at h
    subst hz
    subst hz'
    have e : mkH3 VT a (fun y => Er3 VT simT (root3 VT simT a y) (root3 VT simT a z)) x =
        mkH3 VT a (fun y => Er3 VT simT (root3 VT simT a y) (root3 VT simT a z')) x :=
      congrArg mk3 (propext ⟨fun h1 => Er3_trans VT simT simT_trans _ _ _ h1 h,
        fun h1 => Er3_trans VT simT simT_trans _ _ _ h1 (Er3_symm VT simT simT_symm _ _ h)⟩)
    rw [e]
    exact Or.inl rfl

theorem MTH_PCong : MTH.Valid PCong := by
  intro ρ env
  refine (MTH.holds_tall _ _ _).mpr fun a => (MTH.holds_tall _ _ _).mpr fun b =>
    (MTH.holds_tall _ _ _).mpr fun c => ?_
  refine (MTH.holds_all _ _ _ _).mpr fun f => (MTH.holds_all _ _ _ _).mpr fun g =>
    (MTH.holds_all _ _ _ _).mpr fun x => ?_
  refine (MTH.holds_imp _ _ _ _).mpr fun h => (MTH.holds_eqv _ _ _ _ _ _).mpr ((MTH_V_eqv _ _ _ _).mpr ?_)
  exact MTH_PCong_core a b c f g ((MTH_V_eqv _ _ _ _).mp ((MTH.holds_eqv _ _ _ _ _ _).mp h)) x

/-- With `f = g = ¬` on propositions: `1 ≡ 2`, but `¬1 = 2` and `¬2 = 0` are not identified. -/
theorem MTH_not_WCong : ¬ MTH.Valid WCong := fun h => by
  have h0 := (MTH.holds_tall _ _ _).mp ((MTH.holds_tall _ _ _).mp ((MTH.holds_tall _ _ _).mp
    ((MTH.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) .t) .t) .t
  have h1 := (MTH.holds_all _ _ _ _).mp ((MTH.holds_all _ _ _ _).mp ((MTH.holds_all _ _ _ _).mp
    ((MTH.holds_all _ _ _ _).mp h0 (fun p : Fin 3 => mk3 (¬ VT p))) (fun p : Fin 3 => mk3 (¬ VT p)))
    (1 : Fin 3)) (2 : Fin 3)
  have h2 := (MTH.holds_imp _ _ _ _).mp h1 ((MTH.holds_conj _ _ _ _).mpr
    ⟨(MTH.holds_conj _ _ _ _).mpr ⟨(MTH.holds_teq _ _ _ _).mpr ((MTH_V_teq _ _).mpr rfl),
      (MTH.holds_teq _ _ _ _).mpr ((MTH_V_teq _ _).mpr rfl)⟩,
     (MTH.holds_conj _ _ _ _).mpr ⟨(MTH.holds_eqv _ _ _ _ _ _).mpr ((MTH_V_eqv _ _ _ _).mpr (Or.inl rfl)),
      (MTH.holds_eqv _ _ _ _ _ _).mpr ((F3_eqT VT VT0 VT2 simT 1 2 simT_refl).mpr
        (Or.inr ⟨by decide, by decide⟩))⟩⟩)
  have h3 : simT (mk3 (¬ VT (1 : Fin 3))) (mk3 (¬ VT (2 : Fin 3))) :=
    (F3_eqT VT VT0 VT2 simT _ _ simT_refl).mp ((MTH.holds_eqv _ _ _ _ _ _).mp h2)
  rw [mk3_eq2 (fun hn => hn (by unfold VT; decide)), mk3_eq0 VT2] at h3
  exact absurd h3 (by unfold simT; decide)

/-- With `f = g = ¬` on propositions: `1 ≡ 2`, but `¬1 = 2` and `¬2 = 0` are not identified. -/
theorem MTH_not_Cong : ¬ MTH.Valid Cong := fun h => by
  have h0 := (MTH.holds_tall _ _ _).mp ((MTH.holds_tall _ _ _).mp ((MTH.holds_tall _ _ _).mp
    ((MTH.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) .t) .t) .t
  have h1 := (MTH.holds_all _ _ _ _).mp ((MTH.holds_all _ _ _ _).mp ((MTH.holds_all _ _ _ _).mp
    ((MTH.holds_all _ _ _ _).mp h0 (fun p : Fin 3 => mk3 (¬ VT p))) (fun p : Fin 3 => mk3 (¬ VT p)))
    (1 : Fin 3)) (2 : Fin 3)
  have h2 := (MTH.holds_imp _ _ _ _).mp h1 ((MTH.holds_conj _ _ _ _).mpr
     ⟨(MTH.holds_eqv _ _ _ _ _ _).mpr ((MTH_V_eqv _ _ _ _).mpr (Or.inl rfl)),
      (MTH.holds_eqv _ _ _ _ _ _).mpr ((F3_eqT VT VT0 VT2 simT 1 2 simT_refl).mpr
        (Or.inr ⟨by decide, by decide⟩))⟩)
  have h3 : simT (mk3 (¬ VT (1 : Fin 3))) (mk3 (¬ VT (2 : Fin 3))) :=
    (F3_eqT VT VT0 VT2 simT _ _ simT_refl).mp ((MTH.holds_eqv _ _ _ _ _ _).mp h2)
  rw [mk3_eq2 (fun hn => hn (by unfold VT; decide)), mk3_eq0 VT2] at h3
  exact absurd h3 (by unfold simT; decide)

/-- `λx.1` and `λx.2` agree up to identity at each entity, but neither is a haecceity, so each is
its own root, and they differ. -/
theorem MTH_not_PExt : ¬ MTH.Valid PExt := fun h => by
  have h0 := (MTH.holds_tall _ _ _).mp ((MTH.holds_tall _ _ _).mp ((MTH.holds_tall _ _ _).mp
    (h (fun i => i.elim0) ()) .e) .t) .t
  have h1 := (MTH.holds_all _ _ _ _).mp ((MTH.holds_all _ _ _ _).mp h0 (fun _ : Unit => (1 : Fin 3)))
    (fun _ : Unit => (2 : Fin 3))
  have h2 := (MTH.holds_imp _ _ _ _).mp h1 ((MTH.holds_all _ _ _ _).mpr fun _ =>
    (MTH.holds_eqv _ _ _ _ _ _).mpr ((F3_eqT VT VT0 VT2 simT 1 2 simT_refl).mpr (Or.inr ⟨by decide, by decide⟩)))
  have h3 : Er3 VT simT (root3 VT simT (.arr .e .t) (fun _ => (1 : Fin 3)))
      (root3 VT simT (.arr .e .t) (fun _ => (2 : Fin 3))) :=
    (MTH_V_eqv _ _ _ _).mp ((MTH.holds_eqv _ _ _ _ _ _).mp h2)
  rw [MTH_root_own_no0 .e (fun _ => (1 : Fin 3)) (fun _ => (by decide : (1 : Fin 3) ≠ 0)),
    MTH_root_own_no0 .e (fun _ => (2 : Fin 3)) (fun _ => (by decide : (2 : Fin 3) ≠ 0))] at h3
  have e := MTH_Er3_eq h3 (MTH_arr_ne_t _ _)
  have e2 : (1 : Fin 3) = 2 := congrFun (eq_of_heq (Sigma.mk.inj e).2) ()
  exact absurd e2 (by decide)

/-! ## Necessity of identity and distinctness -/

theorem MTH_NIEqv : MTH.Valid NIEqv := by
  intro ρ env
  refine (MTH.holds_tall _ _ _).mpr fun a => (MTH.holds_all _ _ _ _).mpr fun x =>
    (MTH.holds_all _ _ _ _).mpr fun y => ?_
  exact (MTH.holds_imp _ _ _ _).mpr fun h => MTH_box_of _ _ _ (MTH_eqv_ne1 _ _ _ _ _ _) h

theorem MTH_NIX : MTH.Valid NIX := by
  intro ρ env
  refine (MTH.holds_tall _ _ _).mpr fun a => (MTH.holds_tall _ _ _).mpr fun b => ?_
  refine (MTH.holds_all _ _ _ _).mpr fun x => (MTH.holds_all _ _ _ _).mpr fun y => ?_
  exact (MTH.holds_imp _ _ _ _).mpr fun h => MTH_box_of _ _ _ (MTH_eqv_ne1 _ _ _ _ _ _) h

theorem MTH_NDX : MTH.Valid NDX := by
  intro ρ env
  refine (MTH.holds_tall _ _ _).mpr fun a => (MTH.holds_tall _ _ _).mpr fun b => ?_
  refine (MTH.holds_all _ _ _ _).mpr fun x => (MTH.holds_all _ _ _ _).mpr fun y => ?_
  exact (MTH.holds_imp _ _ _ _).mpr fun h => MTH_box_of _ _ _ (MTH_neg_ne1 _ _ _) h

theorem MTH_NITeq : MTH.Valid NITeq := by
  intro ρ env
  refine (MTH.holds_tall _ _ _).mpr fun a => (MTH.holds_tall _ _ _).mpr fun b => ?_
  exact (MTH.holds_imp _ _ _ _).mpr fun h => MTH_box_of _ _ _ (MTH_teq_ne1 _ _ _ _) h

theorem MTH_NDTeq : MTH.Valid NDTeq := by
  intro ρ env
  refine (MTH.holds_tall _ _ _).mpr fun a => (MTH.holds_tall _ _ _).mpr fun b => ?_
  exact (MTH.holds_imp _ _ _ _).mpr fun h => MTH_box_of _ _ _ (MTH_neg_ne1 _ _ _) h

/-! ## Booleanism, the Identity Identity, Classicism -/

/-- `¬¬1 = 0` is not identified with `1`. -/
theorem MTH_not_DNeg : ¬ MTH.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MTH.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (1 : Fin 3)
  have h1 : simT (mk3 (¬ VT (mk3 (¬ VT (1 : Fin 3))))) 1 :=
    (F3_eqT VT VT0 VT2 simT _ _ simT_refl).mp ((MTH.holds_eqv_t _ _ _ _).mp h0)
  rw [mk3_eq2 (c := ¬ VT (1 : Fin 3)) (fun hn => hn (by unfold VT; decide)),
    mk3_eq0 (c := ¬ VT (2 : Fin 3)) VT2] at h1
  exact absurd h1 (by unfold simT; decide)

theorem MTH_not_Bool : ¬ ∀ φ, BoolSch φ → MTH.Valid φ := fun h => MTH_not_DNeg (h _ DNeg_bool)

theorem MTH_not_Class : ¬ ∀ χ, ClassSch χ → MTH.Valid χ := fun h =>
  MTH_not_Bool fun φ hφ => MTH.soundness MTH_model h (d_Bool_of_Class (S := ClassSch) (fun _ hc => hc) φ hφ)

/-- `1 ≡ 2` is true, but `∀F(F 1 → F 2)` is false (take `F = λp.p`); both have value `0` or `2`,
so they are not identified. -/
theorem MTH_not_IdId : ¬ MTH.Valid IdId := fun h => by
  have h0 := (MTH.holds_all _ _ _ _).mp ((MTH.holds_all _ _ _ _).mp
    ((MTH.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) (1 : Fin 3)) (2 : Fin 3)
  have hr := (MTH_holds_eqv_t_good _ _ _ _ h0 (MTH_eqv_ne1 _ _ _ _ _ _) (MTH_all_ne1 _ _ _ _)).mp
    ((MTH.holds_eqv _ _ _ _ _ _).mpr ((F3_eqT VT VT0 VT2 simT 1 2 simT_refl).mpr (Or.inr ⟨by decide, by decide⟩)))
  have h1 := (MTH.holds_imp _ _ _ _).mp ((MTH.holds_all _ _ _ _).mp hr (fun p : Fin 3 => p))
    (show VT (1 : Fin 3) by unfold VT; decide)
  exact VT2 h1

/-! ## Barcan formulas and Type Necessitism -/

theorem MTH_TBF : ∀ χ, TBFSch χ → MTH.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MTH.holds_imp _ _ _ _).mpr fun h => MTH_box_of _ _ _ (MTH_tall_ne1 _ _ _) ?_
  exact (MTH.holds_tall _ _ _).mpr fun a => MTH_holds_of_box _ _ _ ((MTH.holds_tall _ _ _).mp h a)

theorem MTH_TNec : MTH.Valid TNec := by
  intro ρ env
  refine (MTH.holds_tall _ _ _).mpr fun a => MTH_box_of _ _ _ (MTH_tex_ne1 _ _ _) ?_
  exact (MTH.holds_tex _ _ _).mpr ⟨a, (MTH.holds_teq _ _ _ _).mpr ((MTH_V_teq _ _).mpr rfl)⟩

theorem MTH_BF : MTH.Valid BF := by
  intro ρ env
  refine (MTH.holds_tall _ _ _).mpr fun a => (MTH.holds_all _ _ _ _).mpr fun F => ?_
  refine (MTH.holds_imp _ _ _ _).mpr fun h => MTH_box_of _ _ _ (MTH_all_ne1 _ _ _ _) ?_
  exact (MTH.holds_all _ _ _ _).mpr fun x => MTH_holds_of_box _ _ _ ((MTH.holds_all _ _ _ _).mp h x)

/-- With `F` taking each entity to `1`: `∀x F x` is `0`, so necessary; but `F x = 1` is not. -/
theorem MTH_not_CBF : ¬ MTH.Valid CBF := fun h => by
  have h0 := (MTH.holds_all _ _ _ _).mp ((MTH.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ : Unit => (1 : Fin 3))
  have hb : MTH.Holds (boxF (all tv0 (Tm.app (.var (.there .here)) (.var .here))) : Fm ((Ctx.nil.text).ext tv0.pred))
      (scons .e fun i => i.elim0) ((), fun _ : Unit => (1 : Fin 3)) :=
    MTH_box_of _ _ _ (MTH_all_ne1 _ _ _ _) ((MTH.holds_all _ _ _ _).mpr fun _ =>
      (show VT (1 : Fin 3) by unfold VT; decide))
  have h1 := (MTH.holds_all _ _ _ _).mp ((MTH.holds_imp _ _ _ _).mp h0 hb) ()
  have e : (1 : Fin 3) = 0 := (MTH_box _ _ _).mp h1
  exact absurd e (by decide)

theorem MTH_Nec : MTH.Valid Nec := by
  intro ρ env
  refine (MTH.holds_tall _ _ _).mpr fun a => (MTH.holds_all _ _ _ _).mpr fun x =>
    MTH_box_of _ _ _ (MTH_ex_ne1 _ _ _ _) ?_
  exact (MTH.holds_ex _ _ _ _).mpr ⟨x, (MTH.holds_eqv _ _ _ _ _ _).mpr ((MTH_V_eqv _ _ _ _).mpr (Or.inl rfl))⟩

/-! ## Leibniz's law for polymorphic predicates -/

/-- The polymorphic predicate `λγ.λz:γ. ∃_{γ→t} F (F ≡_{γ→t,t→t} λp:t.p ∧ F z)`. Since `λp.p` is
identified only with itself, at `t` it holds of exactly the true propositions. -/
def MTH_PredT : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (ex tv0.pred (conj (eqv tv0.pred tyT.pred (.var .here) (.lam tyT (.var .here)))
    (.app (.var .here) (.var (.there .here))))))

/-- The value of `MTH_PredT` at `z : a`. -/
noncomputable def MTH_PT (a : Code (univ3 VT).Base) (z : (univ3 VT).El a) : Fin 3 :=
  MTH.ex (.arr a .t) fun F => MTH.cnj (MTH.eqv (.arr a .t) (.arr .t .t) F (fun p => p)) (F z)

theorem MTH_tr_Bridge : MTH.Holds (Bridge MTH_PredT) (fun i => i.elim0) () ↔
    MTH.U.V (MTH.tall fun a => MTH.tall fun b => MTH.all a fun x => MTH.all b fun y =>
      MTH.imp (MTH.cnj (MTH.eqv a b x y) (MTH.teq a b)) (MTH.imp (MTH_PT a x) (MTH_PT b y))) := Iff.rfl

theorem MTH_PT_t (z : Fin 3) : MTH.U.V (MTH_PT .t z) ↔ VT z := by
  refine (MTH.hex _ _).trans ⟨fun ⟨F, hF⟩ => ?_, fun hz => ⟨fun p => p, (MTH.hcnj _ _).mpr
    ⟨(MTH_V_eqv _ _ _ _).mpr (Or.inl rfl), hz⟩⟩⟩
  have hF' := (MTH.hcnj _ _).mp hF
  have e := MTH_eq_id F ((MTH_V_eqv _ _ _ _).mp hF'.1)
  subst e
  exact hF'.2

/-- `1 ≡ 2` and `t ≈ t`; `MTH_PredT` holds of `1`, which is true, but not of `2`, which is false. -/
theorem MTH_not_Bridge : ¬ MTH.Valid (Bridge MTH_PredT) := fun h => by
  have h0 := MTH_tr_Bridge.mp ((MTH.valid_iff_tr _).mp h)
  have h1 := (MTH.hall _ _).mp ((MTH.hall _ _).mp ((MTH.htall _).mp ((MTH.htall _).mp h0 .t) .t)
    (1 : Fin 3)) (2 : Fin 3)
  have h2 := (MTH.himp _ _).mp h1 ((MTH.hcnj _ _).mpr ⟨(F3_eqT VT VT0 VT2 simT 1 2 simT_refl).mpr
    (Or.inr ⟨by decide, by decide⟩), (MTH_V_teq _ _).mpr rfl⟩)
  have h3 := (MTH.himp _ _).mp h2 ((MTH_PT_t 1).mpr (by unfold VT; decide))
  exact VT2 ((MTH_PT_t 2).mp h3)

/-! ## TCBF, by a logical relation

Every value of a constant is *good*: it has the form `mk3 c`, so it is `0` or `2`. A logical relation
shows that the value of every closed formula is good. So if `𝔸α φ` is true, each instance of `φ` is
true and good, hence `0`, hence necessary. -/

section MTH_Good
variable (Gt : MTH.U.P → Prop)

/-- Goodness at each code. -/
def MTH_GC : (c : Code MTH.U.Base) → MTH.U.El c → Prop
  | .e, _ => True
  | .t, p => Gt p
  | .base _, _ => True
  | .arr a c, f => ∀ x, MTH_GC a x → MTH_GC c (f x)

/-- Goodness at each category. -/
def MTH_GK : {n : Nat} → (K : Cat n) → (ρ : MTH.U.TEnv n) → MTH.U.CatVal K ρ → Prop
  | _, .e, _, _ => True
  | _, .t, _, p => Gt p
  | _, .var i, ρ, x => MTH_GC Gt (ρ i) x
  | _, .arr K L, ρ, f => ∀ u, MTH_GK K ρ u → MTH_GK L ρ (f u)
  | _, .pi K, ρ, G => ∀ a, MTH_GK K (scons a ρ) (G a)

theorem MTH_GC_heq {c c' : Code MTH.U.Base} (hc : c = c') (x : MTH.U.El c) (y : MTH.U.El c')
    (h : HEq x y) : MTH_GC Gt c x ↔ MTH_GC Gt c' y := by
  subst hc; cases h; exact Iff.rfl

theorem MTH_GK_GC {n : Nat} (K : Cat n) : ∀ (_ : K.Simple) (ρ : MTH.U.TEnv n) (u : MTH.U.CatVal K ρ)
    (x : MTH.U.El (MTH.U.code K ρ)), HEq u x → (MTH_GK Gt K ρ u ↔ MTH_GC Gt (MTH.U.code K ρ) x) := by
  induction K with
  | e => intro _ ρ u x hx; cases hx; exact Iff.rfl
  | t => intro _ ρ u x hx; cases hx; exact Iff.rfl
  | var i => intro _ ρ u x hx; cases hx; exact Iff.rfl
  | arr a b iha ihb =>
    intro hK ρ u x hx
    refine Invariance.forall_heq (Univ.El_code ρ hK.1).symm fun v y hvy => ?_
    refine imp_congr (iha hK.1 ρ v y hvy) (ihb hK.2 ρ _ _ ?_)
    exact heq_app (Univ.El_code ρ hK.1).symm (Univ.El_code ρ hK.2).symm hx hvy
  | pi _ _ => intro hK; exact hK.elim

theorem MTH_GK_ren {n : Nat} (K : Cat n) : ∀ {m : Nat} (r : Fin n → Fin m) (ρ : MTH.U.TEnv m)
    (ρ₂ : MTH.U.TEnv n), (∀ i, ρ (r i) = ρ₂ i) → ∀ (v : MTH.U.CatVal (K.ren r) ρ) (w : MTH.U.CatVal K ρ₂),
    HEq v w → (MTH_GK Gt (K.ren r) ρ v ↔ MTH_GK Gt K ρ₂ w) := by
  induction K with
  | e => intro m r ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | t => intro m r ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | var i => intro m r ρ ρ₂ hρ v w hv; exact MTH_GC_heq Gt (hρ i) v w hv
  | arr a b iha ihb =>
    intro m r ρ ρ₂ hρ v w hv
    refine Invariance.forall_heq (Univ.CatVal_ren a r ρ ρ₂ hρ) fun u y huy => ?_
    refine imp_congr (iha r ρ ρ₂ hρ u y huy) (ihb r ρ ρ₂ hρ _ _ ?_)
    exact heq_app (Univ.CatVal_ren a r ρ ρ₂ hρ) (Univ.CatVal_ren b r ρ ρ₂ hρ) hv huy
  | pi K ih =>
    intro m r ρ ρ₂ hρ v w hv
    refine forall_congr' fun a => ?_
    exact ih (liftR r) (scons a ρ) (scons a ρ₂) (fin_cases rfl (fun i => hρ i)) _ _
      (heq_dapp (fun a => Univ.CatVal_ren K (liftR r) (scons a ρ) (scons a ρ₂)
        (fin_cases rfl (fun i => hρ i))) hv rfl)

theorem MTH_GK_sub {n : Nat} (K : Cat n) : ∀ {m : Nat} (s : Fin n → Ty m) (ρ : MTH.U.TEnv m)
    (ρ₂ : MTH.U.TEnv n), (∀ i, MTH.U.code (s i).1 ρ = ρ₂ i) →
    ∀ (v : MTH.U.CatVal (K.sub s) ρ) (w : MTH.U.CatVal K ρ₂),
    HEq v w → (MTH_GK Gt (K.sub s) ρ v ↔ MTH_GK Gt K ρ₂ w) := by
  induction K with
  | e => intro m s ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | t => intro m s ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | var i =>
    intro m s ρ ρ₂ hρ v w hv
    exact (MTH_GK_GC Gt (s i).1 (s i).2 ρ v (cast (Univ.El_code ρ (s i).2).symm v) (cast_heq _ v).symm).trans
      (MTH_GC_heq Gt (hρ i) _ w ((cast_heq _ v).trans hv))
  | arr a b iha ihb =>
    intro m s ρ ρ₂ hρ v w hv
    refine Invariance.forall_heq (Univ.CatVal_sub a s ρ ρ₂ hρ) fun u y huy => ?_
    refine imp_congr (iha s ρ ρ₂ hρ u y huy) (ihb s ρ ρ₂ hρ _ _ ?_)
    exact heq_app (Univ.CatVal_sub a s ρ ρ₂ hρ) (Univ.CatVal_sub b s ρ ρ₂ hρ) hv huy
  | pi K ih =>
    intro m s ρ ρ₂ hρ v w hv
    have hl : ∀ a, ∀ i, MTH.U.code (liftT s i).1 (scons a ρ) = scons a ρ₂ i := fun a =>
      fin_cases rfl (fun i => by
        show MTH.U.code ((s i).1.ren fs) (scons a ρ) = ρ₂ i
        rw [Univ.code_ren]; exact hρ i)
    refine forall_congr' fun a => ?_
    exact ih (liftT s) (scons a ρ) (scons a ρ₂) (hl a) _ _
      (heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ) (scons a ρ₂) (hl a)) hv rfl)

/-- Good values for the term variables of a context. -/
def MTH_EG : {n : Nat} → (Γ : Ctx n) → (ρ : MTH.U.TEnv n) → MTH.U.Env Γ ρ → Prop
  | _, .nil, _, _ => True
  | _, .ext Γ σ, ρ, env => MTH_EG Γ ρ env.1 ∧ MTH_GK Gt σ.1 ρ env.2
  | _, .text Γ, ρ, env => MTH_EG Γ (fun i => ρ (fs i)) env

theorem MTH_lookup_good {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) :
    ∀ (ρ : MTH.U.TEnv n) (env : MTH.U.Env Γ ρ), MTH_EG Gt Γ ρ env → MTH_GK Gt K ρ (MTH.U.lookup x ρ env) := by
  induction x with
  | here => intro ρ env h; exact h.2
  | there y ih => intro ρ env h; exact ih ρ env.1 h.1
  | tthere y ih =>
    intro ρ env h
    exact (MTH_GK_ren Gt _ fs ρ (fun i => ρ (fs i)) (fun _ => rfl) _ _ (MTH.lookup_tthere y ρ env)).mpr
      (ih _ env h)

/-- **The fundamental lemma**: if every constant is good, every term is good under good values
for its variables. -/
theorem MTH_fund (hc : ∀ {n : Nat} {K : Cat n} (c : Const n K) (ρ : MTH.U.TEnv n),
      MTH_GK Gt K ρ (MTH.constVal c ρ))
    {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) : ∀ (ρ : MTH.U.TEnv n) (env : MTH.U.Env Γ ρ),
    MTH_EG Gt Γ ρ env → MTH_GK Gt K ρ (MTH.eval M ρ env) := by
  induction M with
  | var x => intro ρ env h; exact MTH_lookup_good Gt x ρ env h
  | const c => intro ρ _ _; exact hc c ρ
  | app f a ihf iha => intro ρ env h; exact ihf ρ env h _ (iha ρ env h)
  | lam σ b ih => intro ρ env h u hu; exact ih ρ (env, u) ⟨h, hu⟩
  | tlam b ih => intro ρ env h a; exact ih (scons a ρ) env h
  | tapp f σ ih =>
    intro ρ env h
    exact (MTH_GK_sub Gt _ (inst σ) ρ (scons (MTH.U.code σ.1 ρ) ρ) (fin_cases rfl (fun _ => rfl)) _ _
      (MTH.heq_eval_tapp f σ ρ env)).mpr (ih ρ env h (MTH.U.code σ.1 ρ))

end MTH_Good

/-- A proposition is good if it is `0` or `2`. -/
def MTH_Gt (p : MTH.U.P) : Prop := ∃ c : Prop, p = mk3 c

theorem MTH_const_good {n : Nat} {K : Cat n} (c : Const n K) (ρ : MTH.U.TEnv n) :
    MTH_GK MTH_Gt K ρ (MTH.constVal c ρ) := by
  cases c with
  | neg => intro _ _; exact ⟨_, rfl⟩
  | imp => intro _ _ _ _; exact ⟨_, rfl⟩
  | and => intro _ _ _ _; exact ⟨_, rfl⟩
  | or => intro _ _ _ _; exact ⟨_, rfl⟩
  | iff => intro _ _ _ _; exact ⟨_, rfl⟩
  | all => intro _ _ _; exact ⟨_, rfl⟩
  | ex => intro _ _ _; exact ⟨_, rfl⟩
  | tall => intro _ _; exact ⟨_, rfl⟩
  | tex => intro _ _; exact ⟨_, rfl⟩
  | eqv => intro _ _ _ _ _ _; exact ⟨_, rfl⟩
  | teq => intro _ _; exact ⟨_, rfl⟩

/-- The value of every closed formula (with one free type variable) is good. -/
theorem MTH_closed_good (φ : Fm Ctx.nil.text) (a : Code MTH.U.Base) (ρ : MTH.U.TEnv 0)
    (env : MTH.U.Env Ctx.nil ρ) : MTH_Gt (MTH.eval φ (scons a ρ) env) :=
  MTH_fund MTH_Gt MTH_const_good φ (scons a ρ) env trivial

theorem MTH_TCBF : ∀ χ, TCBFSch χ → MTH.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MTH.holds_imp _ _ _ _).mpr fun h => (MTH.holds_tall _ _ _).mpr fun a => ?_
  have h1 := (MTH.holds_tall _ _ _).mp (MTH_holds_of_box _ _ _ h) a
  obtain ⟨c, hc⟩ := MTH_closed_good φ a ρ env
  exact MTH_box_of _ _ _ (fun e => MTH_mk3_ne1 c (hc.symm.trans e)) h1

end Al
end PIF
