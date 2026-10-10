import PIBF
import PIOQ_F3c
set_option autoImplicit false

/-!
# More about `𝔐_⊤⊥,c`

In `𝔐_⊤⊥,c` (`MCc`, `PIOQ_F3c.lean`) there are three propositions `0`, `1`, `2`; only `0` is true;
the connectives, the quantifiers, `≡` and `≈` take only the values `0` and `2`. Items are identified
just in case they have the same root (got by stripping off haecceities), except that the
propositions `0` and `2` are identified. `≈` is identity of codes.

Since `0` and `2` are identified, `□φ` (that is, `φ ≡ ⊤`) holds just in case the value of `φ` is
not `1`. Every value of a constant is `0` or `2`, and a logical relation shows that the value of
every closed formula is not `1`.

At a type `α → t`, identity is identity: two haecceities are identified just in case they are the
haecceities of identified items, and then they are the same function. So functions are identified
only with themselves (PCong holds), while a function into `t` whose value is `1` is a haecceity of
nothing, and so is identified with nothing of a lower type (Cantor, Ext≈).

Valid: Cantor, PCong, Inj≈, Recovery, Ext≈, the Identity Identity, TBF, TCBF, Choice.
Refuted: LL≡/≈ (for `MCc_PredT`), Cong, WCong, PExt, Int≈, Booleanism, Classicism.
-/

namespace PIF
open Tm

namespace Al

open Classical

/-! ## Values of `≡` and `≈` -/

theorem MCc_V_eqv (a b : Code (univ3 VB).Base) (x : (univ3 VB).El a) (y : (univ3 VB).El b) :
    MCc.U.V (MCc.eqv a b x y) ↔ Er3 VB simC (root3 VB simC a x) (root3 VB simC b y) :=
  mk3_V VB VB0 VB2 _

theorem MCc_V_teq (a b : Code (univ3 VB).Base) : MCc.U.V (MCc.teq a b) ↔ a = b := mk3_V VB VB0 VB2 _

theorem MCc_Er3_fst {r s : Σ b : Code (univ3 VB).Base, (univ3 VB).El b} (h : Er3 VB simC r s) : r.1 = s.1 := by
  rcases h with rfl | ⟨p, q, rfl, rfl, _⟩
  · rfl
  · rfl

/-! ## Roots -/

theorem MCc_root_arr_t (a : Code (univ3 VB).Base) (f : (univ3 VB).El (.arr a .t)) :
    root3 VB simC (.arr a .t) f =
      if h : ∃ z, f = mkH3 VB a (fun y => Er3 VB simC (root3 VB simC a y) (root3 VB simC a z))
      then root3 VB simC a (Classical.choose h) else ⟨.arr a .t, f⟩ :=
  eroot_t (univ3 VB).El (Er3 VB simC) (mkH3 VB) a f

theorem MCc_root_le : ∀ (c : Code (univ3 VB).Base) (x : (univ3 VB).El c), csz (root3 VB simC c x).1 ≤ csz c
  | .arr a .t, f => by
    rw [MCc_root_arr_t]
    split
    · exact Nat.le_trans (MCc_root_le a _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _))
    · exact Nat.le_refl _
  | .e, _ => Nat.le_refl _
  | .t, _ => Nat.le_refl _
  | .base b, _ => Empty.elim b
  | .arr _ .e, _ => Nat.le_refl _
  | .arr _ (.base b), _ => Empty.elim b
  | .arr _ (.arr _ _), _ => Nat.le_refl _

/-- The root of a function is the function itself, unless it is a haecceity, whose root is the
root of an item of its argument type. -/
theorem MCc_root_arr (a d : Code (univ3 VB).Base) (f : (univ3 VB).El (.arr a d)) :
    root3 VB simC (.arr a d) f = ⟨.arr a d, f⟩ ∨ (d = .t ∧ csz (root3 VB simC (.arr a d) f).1 ≤ csz a) := by
  cases d with
  | t =>
    rw [MCc_root_arr_t]
    split
    · exact Or.inr ⟨rfl, MCc_root_le a _⟩
    · exact Or.inl rfl
  | e => exact Or.inl rfl
  | base b => exact Empty.elim b
  | arr _ _ => exact Or.inl rfl

/-- Every item is its own root, or has a root of smaller code. -/
theorem MCc_root_cases : ∀ (c : Code (univ3 VB).Base) (x : (univ3 VB).El c),
    root3 VB simC c x = ⟨c, x⟩ ∨ csz (root3 VB simC c x).1 < csz c
  | .e, _ => Or.inl rfl
  | .t, _ => Or.inl rfl
  | .base b, _ => Empty.elim b
  | .arr a d, f => (MCc_root_arr a d f).imp id fun h => by
      have : csz a < csz (Code.arr a d) := by show csz a < csz a + csz d + 1; omega
      exact Nat.lt_of_le_of_lt h.2 this

/-- The function with constant value `1`. -/
def MCc_one (a : Code (univ3 VB).Base) : (univ3 VB).El (.arr a .t) := fun _ => (1 : Fin 3)

/-- The function with constant value `1` is a haecceity of nothing. -/
theorem MCc_root_one (a : Code (univ3 VB).Base) :
    root3 VB simC (.arr a .t) (MCc_one a) = ⟨.arr a .t, MCc_one a⟩ := by
  refine (MCc_root_arr_t a _).trans ?_
  split
  · next h =>
    exfalso
    obtain ⟨z, hz⟩ := h
    exact mk3_ne1 _ (congrFun hz z).symm
  · rfl

/-- The root of an item of type `a` never has the code `a → d`. -/
theorem MCc_root_ne_arr (a d : Code (univ3 VB).Base) (y : (univ3 VB).El a) :
    (root3 VB simC a y).1 ≠ Code.arr a d := fun e => by
  have l := MCc_root_le a y
  rw [e] at l
  exact absurd l (Nat.not_le.mpr (by show csz a < csz a + csz d + 1; omega))

/-- Every type has an item which is its own root. -/
theorem MCc_fix : ∀ c : Code (univ3 VB).Base, ∃ x : (univ3 VB).El c, root3 VB simC c x = ⟨c, x⟩
  | .e => ⟨(), rfl⟩
  | .t => ⟨(1 : Fin 3), rfl⟩
  | .base b => Empty.elim b
  | .arr a .t => ⟨MCc_one a, MCc_root_one a⟩
  | .arr a .e => ⟨fun _ => (), rfl⟩
  | .arr _ (.base b) => Empty.elim b
  | .arr a (.arr c d) => by
    obtain ⟨y⟩ := Univ.El_nonempty (U := univ3 VB) (.arr c d)
    exact ⟨fun _ => y, rfl⟩

/-- Identified functions into `t` are the same function. -/
theorem MCc_arr_t_same (a : Code (univ3 VB).Base) (f g : (univ3 VB).El (.arr a .t))
    (h : Er3 VB simC (root3 VB simC (.arr a .t) f) (root3 VB simC (.arr a .t) g)) : f = g := by
  revert h
  rw [MCc_root_arr_t a f, MCc_root_arr_t a g]
  split
  · next hf =>
    split
    · next hg =>
      intro h
      refine (Classical.choose_spec hf).trans (Eq.trans ?_ (Classical.choose_spec hg).symm)
      funext y
      show mk3 _ = mk3 _
      exact congrArg mk3 (propext ⟨fun h1 => Er3_trans VB simC simC_trans _ _ _ h1 h,
        fun h2 => Er3_trans VB simC simC_trans _ _ _ h2 (Er3_symm VB simC simC_symm _ _ h)⟩)
    · intro h
      exfalso
      have e := MCc_Er3_fst h
      have l := MCc_root_le a (Classical.choose hf)
      rw [e] at l
      exact absurd l (Nat.not_le.mpr (by show csz a < csz a + csz Code.t + 1; omega))
  · split
    · next hg =>
      intro h
      exfalso
      have e := MCc_Er3_fst h
      have l := MCc_root_le a (Classical.choose hg)
      rw [← e] at l
      exact absurd l (Nat.not_le.mpr (by show csz a < csz a + csz Code.t + 1; omega))
    · intro h
      rcases h with h | ⟨p, q, e1, _, _⟩
      · exact eq_of_heq (Sigma.mk.inj h).2
      · exact absurd (congrArg Sigma.fst e1) (fun e => nomatch e)

/-- Two identified functions with the same argument type are the same function. -/
theorem MCc_arr_same {a b c : Code (univ3 VB).Base} {f : (univ3 VB).El (.arr a b)} {g : (univ3 VB).El (.arr a c)}
    (h : Er3 VB simC (root3 VB simC (.arr a b) f) (root3 VB simC (.arr a c) g)) : b = c ∧ HEq f g := by
  rcases MCc_root_arr a b f with hf | ⟨hb, hf⟩ <;> rcases MCc_root_arr a c g with hg | ⟨hc, hg⟩
  · rw [hf, hg] at h
    rcases h with h | ⟨p, q, e1, _, _⟩
    · obtain ⟨h1, h2⟩ := Sigma.mk.inj h
      exact ⟨(Code.arr.inj h1).2, h2⟩
    · exact absurd (congrArg Sigma.fst e1) (fun e => nomatch e)
  · have e := MCc_Er3_fst h
    rw [hf] at e
    rw [← e] at hg
    exact absurd hg (Nat.not_le.mpr (by show csz a < csz a + csz b + 1; omega))
  · have e := MCc_Er3_fst h
    rw [hg] at e
    rw [e] at hf
    exact absurd hf (Nat.not_le.mpr (by show csz a < csz a + csz c + 1; omega))
  · subst hb; subst hc
    exact ⟨rfl, heq_of_eq (MCc_arr_t_same a f g h)⟩

/-- `□` of a universal quantification holds: its value is `0` or `2`. -/
theorem MCc_box_all {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (Γ.ext σ)) (ρ : MCc.U.TEnv n)
    (env : MCc.U.Env Γ ρ) : MCc.Holds (boxF (Tm.all σ φ)) ρ env := by
  refine (MCc.holds_eqv_t _ _ _ _).mpr ((F3_eqT VB VB0 VB2 simC _ _ simC_refl).mpr ?_)
  rw [F3_top VB VB0 VB2 simC (Γ := Γ) ρ env, MCc.eval_all]
  exact simC_mk3 _

/-! ## Identity of types -/

theorem MCc_Inj : MCc.Valid Inj := by
  intro ρ env
  refine (MCc.holds_tall _ _ _).mpr fun a => (MCc.holds_tall _ _ _).mpr fun b => ?_
  refine (MCc.holds_tall _ _ _).mpr fun c => (MCc.holds_tall _ _ _).mpr fun d => ?_
  refine (MCc.holds_imp _ _ _ _).mpr fun h => (MCc.holds_conj _ _ _ _).mpr ⟨?_, ?_⟩
  · have h' : Code.arr a c = Code.arr b d := (MCc_V_teq _ _).mp ((MCc.holds_teq _ _ _ _).mp h)
    exact (MCc.holds_teq _ _ _ _).mpr ((MCc_V_teq _ _).mpr (Code.arr.inj h').1)
  · have h' : Code.arr a c = Code.arr b d := (MCc_V_teq _ _).mp ((MCc.holds_teq _ _ _ _).mp h)
    exact (MCc.holds_teq _ _ _ _).mpr ((MCc_V_teq _ _).mpr (Code.arr.inj h').2)

theorem MCc_Recovery : MCc.Valid Recovery := by
  intro ρ env
  refine (MCc.holds_tall _ _ _).mpr fun a => (MCc.holds_tall _ _ _).mpr fun b => ?_
  refine (MCc.holds_tall _ _ _).mpr fun c => (MCc.holds_tall _ _ _).mpr fun d => ?_
  refine (MCc.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d :=
    (MCc_V_teq _ _).mp ((MCc.holds_teq _ _ _ _).mp ((MCc.holds_conj _ _ _ _).mp h).1)
  exact (MCc.holds_teq _ _ _ _).mpr ((MCc_V_teq _ _).mpr (Code.arr.inj h').2)

/-- Ext≈ holds: an item which is its own root is identified only with items whose root has its
type, and roots have no larger code. -/
theorem MCc_ExtT : MCc.Valid ExtT := by
  intro ρ env
  refine (MCc.holds_tall _ _ _).mpr fun a => (MCc.holds_tall _ _ _).mpr fun b => ?_
  refine (MCc.holds_imp _ _ _ _).mpr fun h => (MCc.holds_teq _ _ _ _).mpr ((MCc_V_teq _ _).mpr ?_)
  obtain ⟨hs, hp⟩ := (MCc.holds_conj _ _ _ _).mp h
  obtain ⟨x0, hx0⟩ := MCc_fix a
  obtain ⟨y0, hy0⟩ := MCc_fix b
  obtain ⟨y, hy⟩ := (MCc.holds_ex _ _ _ _).mp ((MCc.holds_all _ _ _ _).mp hs x0)
  obtain ⟨x, hx⟩ := (MCc.holds_ex _ _ _ _).mp ((MCc.holds_all _ _ _ _).mp hp y0)
  have e1 : (root3 VB simC a x0).1 = (root3 VB simC b y).1 :=
    MCc_Er3_fst ((MCc_V_eqv _ _ _ _).mp ((MCc.holds_eqv _ _ _ _ _ _).mp hy))
  have e2 : (root3 VB simC a x).1 = (root3 VB simC b y0).1 :=
    MCc_Er3_fst ((MCc_V_eqv _ _ _ _).mp ((MCc.holds_eqv _ _ _ _ _ _).mp hx))
  rw [hx0] at e1
  rw [hy0] at e2
  have l2 : csz b ≤ csz a := Nat.le_trans (Nat.le_of_eq (congrArg csz e2).symm) (MCc_root_le a x)
  rcases MCc_root_cases b y with hb | hb
  · rw [hb] at e1
    exact e1
  · rw [← e1] at hb
    exact absurd hb (Nat.not_lt.mpr l2)

/-- Int≈ fails: `□(α ⊑ β)` always holds, since the value of a quantification is `0` or `2`. -/
theorem MCc_not_IntT : ¬ MCc.Valid IntT := fun h => by
  have h0 := (MCc.holds_tall _ _ _).mp ((MCc.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) .e
  have h1 := (MCc.holds_imp _ _ _ _).mp h0
    ((MCc.holds_conj _ _ _ _).mpr ⟨MCc_box_all _ _ _ _, MCc_box_all _ _ _ _⟩)
  have e : (Code.t : Code (univ3 VB).Base) = .e := (MCc_V_teq _ _).mp ((MCc.holds_teq _ _ _ _).mp h1)
  exact nomatch e

/-! ## Cantor -/

/-- The function with constant value `1` is identified with no item of its argument type. -/
theorem MCc_Cantor : MCc.Valid Cantor := by
  intro ρ env
  refine (MCc.holds_tall _ _ _).mpr fun a => (MCc.holds_ex _ _ _ _).mpr
    ⟨MCc_one a, ?_⟩
  refine (MCc.holds_all _ _ _ _).mpr fun y => (MCc.holds_neg _ _ _).mpr fun h => ?_
  have h1 : Er3 VB simC (root3 VB simC (.arr a .t) (MCc_one a)) (root3 VB simC a y) :=
    (MCc_V_eqv _ _ _ _).mp ((MCc.holds_eqv _ _ _ _ _ _).mp h)
  exact MCc_root_ne_arr a .t y ((congrArg Sigma.fst (MCc_root_one a)).symm.trans (MCc_Er3_fst h1)).symm

/-! ## Congruence -/

/-- A function sending `0` to `0` and `2` to `1`. -/
def MCc_G (p : Fin 3) : Fin 3 := if p = 2 then 1 else 0

/-- Cong fails: `0` and `2` are identified, but `MCc_G 0 = 0` and `MCc_G 2 = 1` are not. -/
theorem MCc_not_Cong : ¬ MCc.Valid Cong := fun h => by
  have h0 := (MCc.holds_tall _ _ _).mp ((MCc.holds_tall _ _ _).mp ((MCc.holds_tall _ _ _).mp
    ((MCc.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) .t) .t) .t
  have h1 := (MCc.holds_all _ _ _ _).mp ((MCc.holds_all _ _ _ _).mp h0 MCc_G) MCc_G
  have h2 := (MCc.holds_all _ _ _ _).mp ((MCc.holds_all _ _ _ _).mp h1 (0 : Fin 3)) (2 : Fin 3)
  have h3 := (MCc.holds_imp _ _ _ _).mp h2 ((MCc.holds_conj _ _ _ _).mpr
    ⟨(MCc.holds_eqv _ _ _ _ _ _).mpr ((MCc_V_eqv _ _ _ _).mpr (Or.inl rfl)),
     (MCc.holds_eqv _ _ _ _ _ _).mpr ((MCc_V_eqv _ _ _ _).mpr
       (Or.inr ⟨0, 2, rfl, rfl, Or.inr ⟨by decide, by decide⟩⟩))⟩)
  have hq : simC (MCc_G 0) (MCc_G 2) :=
    (F3_eqT VB VB0 VB2 simC _ _ simC_refl).mp ((MCc.holds_eqv _ _ _ _ _ _).mp h3)
  rcases hq with e | ⟨_, e⟩
  · exact absurd e (by decide)
  · exact e (by decide)

/-- WCong fails, for the same reason: all four types are `t`. -/
theorem MCc_not_WCong : ¬ MCc.Valid WCong := fun h => by
  have h0 := (MCc.holds_tall _ _ _).mp ((MCc.holds_tall _ _ _).mp ((MCc.holds_tall _ _ _).mp
    ((MCc.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) .t) .t) .t
  have h1 := (MCc.holds_all _ _ _ _).mp ((MCc.holds_all _ _ _ _).mp h0 MCc_G) MCc_G
  have h2 := (MCc.holds_all _ _ _ _).mp ((MCc.holds_all _ _ _ _).mp h1 (0 : Fin 3)) (2 : Fin 3)
  have h3 := (MCc.holds_imp _ _ _ _).mp h2 ((MCc.holds_conj _ _ _ _).mpr
    ⟨(MCc.holds_conj _ _ _ _).mpr ⟨(MCc.holds_teq _ _ _ _).mpr ((MCc_V_teq _ _).mpr rfl),
      (MCc.holds_teq _ _ _ _).mpr ((MCc_V_teq _ _).mpr rfl)⟩,
     (MCc.holds_conj _ _ _ _).mpr ⟨(MCc.holds_eqv _ _ _ _ _ _).mpr ((MCc_V_eqv _ _ _ _).mpr (Or.inl rfl)),
      (MCc.holds_eqv _ _ _ _ _ _).mpr ((MCc_V_eqv _ _ _ _).mpr
        (Or.inr ⟨0, 2, rfl, rfl, Or.inr ⟨by decide, by decide⟩⟩))⟩⟩)
  have hq : simC (MCc_G 0) (MCc_G 2) :=
    (F3_eqT VB VB0 VB2 simC _ _ simC_refl).mp ((MCc.holds_eqv _ _ _ _ _ _).mp h3)
  rcases hq with e | ⟨_, e⟩
  · exact absurd e (by decide)
  · exact e (by decide)

/-- PCong holds: identified functions with the same argument type are the same function. -/
theorem MCc_PCong : MCc.Valid PCong := by
  intro ρ env
  refine (MCc.holds_tall _ _ _).mpr fun a => (MCc.holds_tall _ _ _).mpr fun b => ?_
  refine (MCc.holds_tall _ _ _).mpr fun c => ?_
  refine (MCc.holds_all _ _ _ _).mpr fun f => (MCc.holds_all _ _ _ _).mpr fun g => ?_
  refine (MCc.holds_all _ _ _ _).mpr fun x => (MCc.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Er3 VB simC (root3 VB simC (.arr a b) f) (root3 VB simC (.arr a c) g) :=
    (MCc_V_eqv _ _ _ _).mp ((MCc.holds_eqv _ _ _ _ _ _).mp h)
  obtain ⟨hbc, hfg⟩ := MCc_arr_same h'
  subst hbc
  have e : f = g := eq_of_heq hfg
  subst e
  exact (MCc.holds_eqv _ _ _ _ _ _).mpr ((MCc_V_eqv _ _ _ _).mpr (Or.inl rfl))

/-- PExt fails: the constant functions with values `0` and `2` agree up to identity everywhere,
but are different functions. -/
theorem MCc_not_PExt : ¬ MCc.Valid PExt := fun h => by
  have h0 := (MCc.holds_tall _ _ _).mp ((MCc.holds_tall _ _ _).mp
    ((MCc.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .t) .t
  have h1 := (MCc.holds_all _ _ _ _).mp ((MCc.holds_all _ _ _ _).mp h0 (fun _ => (0 : Fin 3)))
    (fun _ => (2 : Fin 3))
  have h2 := (MCc.holds_imp _ _ _ _).mp h1 ((MCc.holds_all _ _ _ _).mpr fun _ =>
    (MCc.holds_eqv _ _ _ _ _ _).mpr ((MCc_V_eqv _ _ _ _).mpr
      (Or.inr ⟨0, 2, rfl, rfl, Or.inr ⟨by decide, by decide⟩⟩)))
  have h3 : Er3 VB simC (root3 VB simC (.arr .e .t) (fun _ => (0 : Fin 3)))
      (root3 VB simC (.arr .e .t) (fun _ => (2 : Fin 3))) :=
    (MCc_V_eqv _ _ _ _).mp ((MCc.holds_eqv _ _ _ _ _ _).mp h2)
  have e : (0 : Fin 3) = 2 := congrFun (MCc_arr_t_same .e _ _ h3) ()
  exact absurd e (by decide)

/-! ## Leibniz's law across identified types -/

/-- The polymorphic predicate `λγ.λz:γ. ∃_{γ→t} F (F ≡_{γ→t,t→t} λp:t.p ∧ F z)`. -/
def MCc_PredT : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (ex tv0.pred (conj (eqv tv0.pred tyT.pred (.var .here) (.lam tyT (.var .here)))
    (.app (.var .here) (.var (.there .here))))))

/-- The body of `MCc_PredT`. -/
def MCc_PredT_body : Fm ((Ctx.nil.text).ext tv0) :=
  ex tv0.pred (conj (eqv tv0.pred tyT.pred (.var .here) (.lam tyT (.var .here)))
    (.app (.var .here) (.var (.there .here))))

/-- At `t`, `MCc_PredT` holds of exactly the true proposition: only `λp.p` is identified with `λp.p`. -/
theorem MCc_PredT_t (z : Fin 3) :
    MCc.Holds MCc_PredT_body (scons .t (fun i => i.elim0)) ((), z) ↔ VB z := by
  refine (MCc.holds_ex _ _ _ _).trans ⟨fun ⟨F, hF⟩ => ?_, fun hz => ⟨fun p => p, ?_⟩⟩
  · obtain ⟨h1, h2⟩ := (MCc.holds_conj _ _ _ _).mp hF
    have e : Er3 VB simC (root3 VB simC (.arr .t .t) F) (root3 VB simC (.arr .t .t) (fun p => p)) :=
      (MCc_V_eqv _ _ _ _).mp ((MCc.holds_eqv _ _ _ _ _ _).mp h1)
    have hF' : F = fun p => p := MCc_arr_t_same .t F _ e
    subst hF'
    exact h2
  · exact (MCc.holds_conj _ _ _ _).mpr ⟨(MCc.holds_eqv _ _ _ _ _ _).mpr ((MCc_V_eqv _ _ _ _).mpr (Or.inl rfl)), hz⟩

/-- LL≡/≈ fails for `MCc_PredT`: `0` and `2` are identified items of type `t`, but `MCc_PredT`
holds of `0` and not of `2`. -/
theorem MCc_not_Bridge : ¬ MCc.Valid (Bridge MCc_PredT) := fun h => by
  have h0 := (MCc.holds_tall _ _ _).mp ((MCc.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) .t
  have h1 := (MCc.holds_all _ _ _ _).mp ((MCc.holds_all _ _ _ _).mp h0 (0 : Fin 3)) (2 : Fin 3)
  have hx : MCc.Holds MCc_PredT_body (scons .t (fun i => i.elim0)) ((), (0 : Fin 3)) :=
    (MCc_PredT_t 0).mpr rfl
  have h2 := (MCc.holds_imp _ _ _ _).mp ((MCc.holds_imp _ _ _ _).mp h1 ((MCc.holds_conj _ _ _ _).mpr
    ⟨(MCc.holds_eqv _ _ _ _ _ _).mpr ((MCc_V_eqv _ _ _ _).mpr
       (Or.inr ⟨0, 2, rfl, rfl, Or.inr ⟨by decide, by decide⟩⟩)),
     (MCc.holds_teq _ _ _ _).mpr ((MCc_V_teq _ _).mpr rfl)⟩)) hx
  have h3 : MCc.Holds MCc_PredT_body (scons .t (fun i => i.elim0)) ((), (2 : Fin 3)) := h2
  exact VB2 ((MCc_PredT_t 2).mp h3)

/-! ## Booleanism, Classicism, and the Identity Identity -/

/-- Booleanism fails: `¬¬1` is `2`, which is not identified with `1`. -/
theorem MCc_not_Bool : ¬ ∀ φ, BoolSch φ → MCc.Valid φ := fun h => by
  have h0 := h _ DNeg_bool (fun i => i.elim0) ()
  rw [DNeg_eq] at h0
  have h1 := (MCc.holds_all _ _ _ _).mp h0 (1 : Fin 3)
  have hq := (F3_eqT VB VB0 VB2 simC _ _ simC_refl).mp ((MCc.holds_eqv_t _ _ _ _).mp h1)
  rcases hq with e | ⟨_, e⟩
  · exact mk3_ne1 _ e
  · exact e rfl

theorem MCc_not_Class : ¬ ∀ χ, ClassSch χ → MCc.Valid χ := fun h =>
  MCc_not_Bool fun φ hφ => MCc.soundness MCc_model h (d_Bool_of_Class (S := ClassSch) (fun _ hc => hc) φ hφ)

/-- The Identity Identity holds: both sides are `0` or `2`, which are identified. -/
theorem MCc_IdId : MCc.Valid IdId := by
  intro ρ env
  refine (MCc.holds_tall _ _ _).mpr fun a => (MCc.holds_all _ _ _ _).mpr fun x =>
    (MCc.holds_all _ _ _ _).mpr fun y => ?_
  refine (MCc.holds_eqv_t _ _ _ _).mpr ((F3_eqT VB VB0 VB2 simC _ _ simC_refl).mpr ?_)
  exact Or.inr ⟨fun e => mk3_ne1 _ ((MCc.eval_eqv _ _ _ _ _ _).symm.trans e),
    fun e => mk3_ne1 _ ((MCc.eval_all _ _ _ _).symm.trans e)⟩

theorem MCc_Choice : MCc.Valid Choice := MCc.Choice_valid

/-! ## TBF, and TCBF by a logical relation

A proposition is *good* if it is not `1`. Every value of a constant is good, so (by a logical
relation) the value of every closed formula is good, and so identified with `⊤`. -/

/-- Goodness of propositions. -/
def MCc_Gt (p : Fin 3) : Prop := p ≠ 1

/-- Goodness at each code. -/
def MCc_GC : (c : Code MCc.U.Base) → MCc.U.El c → Prop
  | .e, _ => True
  | .t, p => MCc_Gt p
  | .base _, _ => True
  | .arr a c, f => ∀ x, MCc_GC a x → MCc_GC c (f x)

/-- Goodness at each category. -/
def MCc_GK : {n : Nat} → (K : Cat n) → (ρ : MCc.U.TEnv n) → MCc.U.CatVal K ρ → Prop
  | _, .e, _, _ => True
  | _, .t, _, p => MCc_Gt p
  | _, .var i, ρ, x => MCc_GC (ρ i) x
  | _, .arr K L, ρ, f => ∀ u, MCc_GK K ρ u → MCc_GK L ρ (f u)
  | _, .pi K, ρ, G => ∀ a, MCc_GK K (scons a ρ) (G a)

theorem MCc_GC_heq {c c' : Code MCc.U.Base} (hc : c = c') (x : MCc.U.El c) (y : MCc.U.El c')
    (h : HEq x y) : MCc_GC c x ↔ MCc_GC c' y := by
  subst hc; cases h; exact Iff.rfl

theorem MCc_GK_GC {n : Nat} (K : Cat n) : ∀ (_ : K.Simple) (ρ : MCc.U.TEnv n) (u : MCc.U.CatVal K ρ)
    (x : MCc.U.El (MCc.U.code K ρ)), HEq u x → (MCc_GK K ρ u ↔ MCc_GC (MCc.U.code K ρ) x) := by
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

theorem MCc_GK_ren {n : Nat} (K : Cat n) : ∀ {m : Nat} (r : Fin n → Fin m) (ρ : MCc.U.TEnv m)
    (ρ₂ : MCc.U.TEnv n), (∀ i, ρ (r i) = ρ₂ i) → ∀ (v : MCc.U.CatVal (K.ren r) ρ) (w : MCc.U.CatVal K ρ₂),
    HEq v w → (MCc_GK (K.ren r) ρ v ↔ MCc_GK K ρ₂ w) := by
  induction K with
  | e => intro m r ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | t => intro m r ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | var i => intro m r ρ ρ₂ hρ v w hv; exact MCc_GC_heq (hρ i) v w hv
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

theorem MCc_GK_sub {n : Nat} (K : Cat n) : ∀ {m : Nat} (s : Fin n → Ty m) (ρ : MCc.U.TEnv m)
    (ρ₂ : MCc.U.TEnv n), (∀ i, MCc.U.code (s i).1 ρ = ρ₂ i) →
    ∀ (v : MCc.U.CatVal (K.sub s) ρ) (w : MCc.U.CatVal K ρ₂),
    HEq v w → (MCc_GK (K.sub s) ρ v ↔ MCc_GK K ρ₂ w) := by
  induction K with
  | e => intro m s ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | t => intro m s ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | var i =>
    intro m s ρ ρ₂ hρ v w hv
    exact (MCc_GK_GC (s i).1 (s i).2 ρ v (cast (Univ.El_code ρ (s i).2).symm v) (cast_heq _ v).symm).trans
      (MCc_GC_heq (hρ i) _ w ((cast_heq _ v).trans hv))
  | arr a b iha ihb =>
    intro m s ρ ρ₂ hρ v w hv
    refine Invariance.forall_heq (Univ.CatVal_sub a s ρ ρ₂ hρ) fun u y huy => ?_
    refine imp_congr (iha s ρ ρ₂ hρ u y huy) (ihb s ρ ρ₂ hρ _ _ ?_)
    exact heq_app (Univ.CatVal_sub a s ρ ρ₂ hρ) (Univ.CatVal_sub b s ρ ρ₂ hρ) hv huy
  | pi K ih =>
    intro m s ρ ρ₂ hρ v w hv
    have hl : ∀ a, ∀ i, MCc.U.code (liftT s i).1 (scons a ρ) = scons a ρ₂ i := fun a =>
      fin_cases rfl (fun i => by
        show MCc.U.code ((s i).1.ren fs) (scons a ρ) = ρ₂ i
        rw [Univ.code_ren]; exact hρ i)
    refine forall_congr' fun a => ?_
    exact ih (liftT s) (scons a ρ) (scons a ρ₂) (hl a) _ _
      (heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ) (scons a ρ₂) (hl a)) hv rfl)

/-- Good values for the term variables of a context. -/
def MCc_EG : {n : Nat} → (Γ : Ctx n) → (ρ : MCc.U.TEnv n) → MCc.U.Env Γ ρ → Prop
  | _, .nil, _, _ => True
  | _, .ext Γ σ, ρ, env => MCc_EG Γ ρ env.1 ∧ MCc_GK σ.1 ρ env.2
  | _, .text Γ, ρ, env => MCc_EG Γ (fun i => ρ (fs i)) env

theorem MCc_lookup_good {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) :
    ∀ (ρ : MCc.U.TEnv n) (env : MCc.U.Env Γ ρ), MCc_EG Γ ρ env → MCc_GK K ρ (MCc.U.lookup x ρ env) := by
  induction x with
  | here => intro ρ env h; exact h.2
  | there y ih => intro ρ env h; exact ih ρ env.1 h.1
  | tthere y ih =>
    intro ρ env h
    exact (MCc_GK_ren _ fs ρ (fun i => ρ (fs i)) (fun _ => rfl) _ _ (MCc.lookup_tthere y ρ env)).mpr
      (ih _ env h)

/-- Every value of a constant is good. -/
theorem MCc_const_good {n : Nat} {K : Cat n} (c : Const n K) (ρ : MCc.U.TEnv n) :
    MCc_GK K ρ (MCc.constVal c ρ) := by
  cases c with
  | neg => intro _ _; exact mk3_ne1 _
  | imp => intro _ _ _ _; exact mk3_ne1 _
  | and => intro _ _ _ _; exact mk3_ne1 _
  | or => intro _ _ _ _; exact mk3_ne1 _
  | iff => intro _ _ _ _; exact mk3_ne1 _
  | all => intro _ _ _; exact mk3_ne1 _
  | ex => intro _ _ _; exact mk3_ne1 _
  | tall => intro _ _; exact mk3_ne1 _
  | tex => intro _ _; exact mk3_ne1 _
  | eqv => intro _ _ _ _ _ _; exact mk3_ne1 _
  | teq => intro _ _; exact mk3_ne1 _

/-- **The fundamental lemma**: every term is good under good values for its variables. -/
theorem MCc_fund {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) : ∀ (ρ : MCc.U.TEnv n) (env : MCc.U.Env Γ ρ),
    MCc_EG Γ ρ env → MCc_GK K ρ (MCc.eval M ρ env) := by
  induction M with
  | var x => intro ρ env h; exact MCc_lookup_good x ρ env h
  | const c => intro ρ _ _; exact MCc_const_good c ρ
  | app f a ihf iha => intro ρ env h; exact ihf ρ env h _ (iha ρ env h)
  | lam σ b ih => intro ρ env h u hu; exact ih ρ (env, u) ⟨h, hu⟩
  | tlam b ih => intro ρ env h a; exact ih (scons a ρ) env h
  | tapp f σ ih =>
    intro ρ env h
    exact (MCc_GK_sub _ (inst σ) ρ (scons (MCc.U.code σ.1 ρ) ρ) (fin_cases rfl (fun _ => rfl)) _ _
      (MCc.heq_eval_tapp f σ ρ env)).mpr (ih ρ env h (MCc.U.code σ.1 ρ))

/-- The value of every closed formula (with one free type variable) is not `1`. -/
theorem MCc_closed_good (φ : Fm Ctx.nil.text) (a : Code MCc.U.Base) (ρ : MCc.U.TEnv 0)
    (env : MCc.U.Env Ctx.nil ρ) : MCc_Gt (MCc.eval φ (scons a ρ) env) :=
  MCc_fund φ (scons a ρ) env trivial

/-- TBF holds: `□𝔸α φ` always holds, since the value of `𝔸α φ` is `0` or `2`. -/
theorem MCc_TBF : ∀ χ, TBFSch χ → MCc.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MCc.holds_imp _ _ _ _).mpr fun _ => ?_
  refine (MCc.holds_eqv_t _ _ _ _).mpr ((F3_eqT VB VB0 VB2 simC _ _ simC_refl).mpr ?_)
  rw [F3_top VB VB0 VB2 simC (Γ := Ctx.nil) ρ env]
  exact simC_mk3 _

/-- TCBF holds: each instance of a closed formula has a value other than `1`, so is necessary. -/
theorem MCc_TCBF : ∀ χ, TCBFSch χ → MCc.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MCc.holds_imp _ _ _ _).mpr fun _ => (MCc.holds_tall _ _ _).mpr fun a => ?_
  refine (MCc.holds_eqv_t _ _ _ _).mpr ((F3_eqT VB VB0 VB2 simC _ _ simC_refl).mpr ?_)
  rw [F3_top VB VB0 VB2 simC (Γ := Ctx.nil.text) (scons a ρ) env]
  exact Or.inr ⟨MCc_closed_good φ a ρ env, by decide⟩

end Al

end PIF
