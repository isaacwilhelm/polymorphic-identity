import PIBF
set_option autoImplicit false

/-!
# The profile of `𝔐_⊤⊥,hae`

`𝔐_⊤⊥,hae` (`MBH`, defined in `PIHaeQs.lean`) is the algebraic model `F3 VB VB0 VB2 simB`: three
propositions `0`, `1`, `2`, with only `0` true; the connectives, the quantifiers, `≡` and `≈` take
only the values `0` and `2`; items are identified just in case their roots (got by stripping off
haecceities) are the same, except that the propositions `0` and `1` are identified; `≈` is
identity of codes. `E = 1`.

Valid: Cantor (the constant function to `1` is not a haecceity), PCong, Inj≈, Recovery, Ext≈,
Int≈, TBF (by a logical relation: no closed formula has the value `1`), TCBF.

Refuted: LL≡/≈ (for `MBH_PredId`), Cong and WCong (`0 ≡ 1`, but a function can send them to `0`
and `2`), PExt, the Identity Identity, Booleanism (`¬¬1` is `2`), Classicism.
-/

namespace PIF
namespace Al
open Tm

/-! ## Basic facts -/

/-- Rooted items of `𝔐_⊤⊥,hae`. -/
abbrev MBH_R := Σ b : Code (univ3 VB).Base, (univ3 VB).El b

theorem MBH_mk3_ne1 (c : Prop) : mk3 c ≠ (1 : Fin 3) := by
  unfold mk3
  split
  · decide
  · decide

theorem MBH_fin3 : ∀ p : Fin 3, p = 0 ∨ p = 1 ∨ p = 2 := by decide

theorem MBH_V (c : Prop) : VB (mk3 c) ↔ c := mk3_V VB VB0 VB2 c

/-- A proposition related by `simB` to a true one, and not `1`, is true. -/
theorem MBH_sim_true {p q : Fin 3} (h : simB p q) (hp : VB p) (hq : q ≠ 1) : VB q := by
  have hp' : p = 0 := hp
  subst hp'
  rcases h with h | ⟨_, h2⟩
  · exact h.symm
  · rcases MBH_fin3 q with e | e | e
    · exact e
    · exact absurd e hq
    · exact absurd e h2

theorem MBH_csz_arr (a c : Code (univ3 VB).Base) : csz a < csz (Code.arr a c) := by
  show csz a < csz a + csz c + 1
  omega

theorem MBH_Er_fst {r s : MBH_R} (h : Er3 VB simB r s) : r.1 = s.1 := by
  rcases h with h | ⟨p, q, e1, e2, _⟩
  · rw [h]
  · rw [e1, e2]

theorem MBH_Er_eq {r s : MBH_R} (h : Er3 VB simB r s) (hr : r.1 ≠ .t) : r = s := by
  rcases h with h | ⟨p, q, e1, _, _⟩
  · exact h
  · exact absurd (congrArg Sigma.fst e1) hr

/-! ## Roots -/

/-- The root of an item has the item's code, or a smaller one. -/
theorem MBH_root_lt : ∀ (c : Code (univ3 VB).Base) (x : (univ3 VB).El c),
    (root3 VB simB c x).1 = c ∨ csz (root3 VB simB c x).1 < csz c
  | .e, _ => Or.inl rfl
  | .t, _ => Or.inl rfl
  | .base b, _ => (b : Empty).elim
  | .arr a .t, f => by
    have e := eroot_t (univ3 VB).El (Er3 VB simB) (mkH3 VB) a f
    rw [show root3 VB simB (.arr a .t) f = _ from e]
    split
    · next h =>
      refine Or.inr ?_
      have hl : csz a < csz (Code.arr a .t : Code (univ3 VB).Base) := MBH_csz_arr a .t
      rcases MBH_root_lt a (Classical.choose h) with h1 | h1
      · rw [h1]; exact hl
      · exact Nat.lt_trans h1 hl
    · exact Or.inl rfl
  | .arr _ .e, _ => Or.inl rfl
  | .arr _ (.base b), _ => (b : Empty).elim
  | .arr _ (.arr _ _), _ => Or.inl rfl

theorem MBH_root_le (c : Code (univ3 VB).Base) (x : (univ3 VB).El c) : csz (root3 VB simB c x).1 ≤ csz c := by
  rcases MBH_root_lt c x with h | h
  · rw [h]; exact Nat.le_refl _
  · exact Nat.le_of_lt h

/-- An item of `α→t` is its own root, or a haecceity whose root lies at a code no larger than `α`. -/
theorem MBH_root_t_cases (a : Code (univ3 VB).Base) (f : (univ3 VB).El (.arr a .t)) :
    root3 VB simB (.arr a .t) f = ⟨.arr a .t, f⟩ ∨
    (csz (root3 VB simB (.arr a .t) f).1 ≤ csz a ∧
      f = mkH3 VB a (fun y => Er3 VB simB (root3 VB simB a y) (root3 VB simB (.arr a .t) f))) := by
  by_cases h : ∃ z, f = mkH3 VB a (fun y => Er3 VB simB (root3 VB simB a y) (root3 VB simB a z))
  · have e1 : root3 VB simB (.arr a .t) f = root3 VB simB a (Classical.choose h) := by
      refine (eroot_t (univ3 VB).El (Er3 VB simB) (mkH3 VB) a f).trans ?_
      split
      · rfl
      · next h' => exact absurd h h'
    refine Or.inr ?_
    rw [e1]
    exact ⟨MBH_root_le a _, Classical.choose_spec h⟩
  · refine Or.inl ((eroot_t (univ3 VB).El (Er3 VB simB) (mkH3 VB) a f).trans ?_)
    split
    · next h' => exact absurd h' h
    · rfl

theorem MBH_root_arr (a b : Code (univ3 VB).Base) (f : (univ3 VB).El (.arr a b)) :
    root3 VB simB (.arr a b) f = ⟨.arr a b, f⟩ ∨ (b = .t ∧ csz (root3 VB simB (.arr a b) f).1 ≤ csz a) := by
  cases b with
  | t =>
    rcases MBH_root_t_cases a f with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩
  | e => exact Or.inl rfl
  | base x => exact (x : Empty).elim
  | arr c d => exact Or.inl rfl

/-- The constant function to `1` is not a haecceity, since haecceities take only the values `0`
and `2`. -/
theorem MBH_one_not_hae (a : Code (univ3 VB).Base) (P : (univ3 VB).El a → Prop) :
    (fun _ => (1 : Fin 3) : (univ3 VB).El (.arr a .t)) ≠ mkH3 VB a P := fun h => by
  obtain ⟨x⟩ := Univ.El_nonempty (U := univ3 VB) a
  exact MBH_mk3_ne1 (P x) ((congrFun h x).symm : mk3 (P x) = 1)

theorem MBH_root_one (a : Code (univ3 VB).Base) :
    root3 VB simB (.arr a .t) (fun _ => (1 : Fin 3)) = ⟨.arr a .t, fun _ => (1 : Fin 3)⟩ := by
  refine (eroot_t (univ3 VB).El (Er3 VB simB) (mkH3 VB) a _).trans ?_
  split
  · next h => exact absurd (Classical.choose_spec h) (MBH_one_not_hae a _)
  · rfl

/-- Every type has an item which is its own root. -/
theorem MBH_own : ∀ c : Code (univ3 VB).Base, ∃ x : (univ3 VB).El c, (root3 VB simB c x).1 = c
  | .arr a .t => ⟨fun _ => (1 : Fin 3), congrArg Sigma.fst (MBH_root_one a)⟩
  | .e => ⟨(), rfl⟩
  | .t => ⟨(0 : Fin 3), rfl⟩
  | .base b => (b : Empty).elim
  | .arr a .e => ⟨Classical.choice (Univ.El_nonempty (U := univ3 VB) (.arr a .e)), rfl⟩
  | .arr _ (.base b) => (b : Empty).elim
  | .arr a (.arr c d) => ⟨Classical.choice (Univ.El_nonempty (U := univ3 VB) (.arr a (.arr c d))), rfl⟩

/-- A root at code `α→γ` cannot lie at a code no larger than `α`. -/
theorem MBH_not_small {a c : Code (univ3 VB).Base} {r : MBH_R} (h1 : r.1 = .arr a c) (h2 : csz r.1 ≤ csz a) :
    False := by
  rw [h1] at h2
  exact absurd (Nat.lt_of_lt_of_le (MBH_csz_arr a c) h2) (Nat.lt_irrefl _)

/-- Functions with one domain whose roots are related have the same codomain, and are the same. -/
theorem MBH_cod {a c d : Code (univ3 VB).Base} (f : (univ3 VB).El (.arr a c)) (g : (univ3 VB).El (.arr a d))
    (h : Er3 VB simB (root3 VB simB (.arr a c) f) (root3 VB simB (.arr a d) g)) : c = d ∧ HEq f g := by
  have hs := MBH_Er_fst h
  rcases MBH_root_arr a c f with h1 | ⟨hc, h2⟩ <;> rcases MBH_root_arr a d g with h3 | ⟨hd, h4⟩
  · rw [h1, h3] at h
    have e := MBH_Er_eq h (fun e => by cases e)
    exact ⟨(Code.arr.inj (congrArg Sigma.fst e)).2, (Sigma.mk.inj e).2⟩
  · exact (MBH_not_small (hs.symm.trans (congrArg Sigma.fst h1)) h4).elim
  · exact (MBH_not_small (hs.trans (congrArg Sigma.fst h3)) h2).elim
  · subst hc
    subst hd
    refine ⟨rfl, heq_of_eq ?_⟩
    rcases MBH_root_t_cases a f with e1 | ⟨_, e1⟩
    · exact (MBH_not_small (congrArg Sigma.fst e1) h2).elim
    rcases MBH_root_t_cases a g with e2 | ⟨_, e2⟩
    · exact (MBH_not_small (congrArg Sigma.fst e2) h4).elim
    refine e1.trans (Eq.trans ?_ e2.symm)
    exact congrArg (mkH3 VB a) (funext fun y => propext
      ⟨fun hy => Er3_trans VB simB simB_trans _ _ _ hy h,
       fun hy => Er3_trans VB simB simB_trans _ _ _ hy (Er3_symm VB simB simB_symm _ _ h)⟩)

/-- Types each of whose items is identified with an item of the other are the same type. -/
theorem MBH_ext_core (a b : Code (univ3 VB).Base)
    (hs : ∀ x : (univ3 VB).El a, ∃ y : (univ3 VB).El b, Er3 VB simB (root3 VB simB a x) (root3 VB simB b y))
    (hp : ∀ y : (univ3 VB).El b, ∃ x : (univ3 VB).El a, Er3 VB simB (root3 VB simB a x) (root3 VB simB b y)) :
    a = b := by
  obtain ⟨x0, hx0⟩ := MBH_own a
  obtain ⟨y0, hy0⟩ := MBH_own b
  obtain ⟨y, hy⟩ := hs x0
  obtain ⟨x, hx⟩ := hp y0
  have c1 : (root3 VB simB b y).1 = a := (MBH_Er_fst hy).symm.trans hx0
  have c2 : (root3 VB simB a x).1 = b := (MBH_Er_fst hx).trans hy0
  rcases MBH_root_lt b y with r1 | r1 <;> rcases MBH_root_lt a x with r2 | r2
  · exact c1.symm.trans r1
  · exact c1.symm.trans r1
  · exact (c2.symm.trans r2).symm
  · rw [c1] at r1
    rw [c2] at r2
    exact absurd (Nat.lt_trans r1 r2) (Nat.lt_irrefl _)

/-- `□φ` holds just in case the value of `φ` is `0` or `1`. -/
theorem MBH_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MBH.U.TEnv n) (env : MBH.U.Env Γ ρ) :
    MBH.Holds (boxF φ) ρ env ↔ simB (MBH.eval φ ρ env) 0 := by
  refine (MBH.holds_eqv_t _ _ _ _).trans ((F3_eqT VB VB0 VB2 simB _ _ simB_refl).trans ?_)
  rw [F3_top VB VB0 VB2 simB ρ env]

theorem MBH_eval_all_ne1 {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : MBH.U.TEnv n)
    (env : MBH.U.Env Γ ρ) : @Ne (Fin 3) (MBH.eval (Tm.all σ φ) ρ env) 1 := by
  rw [MBH.eval_all]
  exact MBH_mk3_ne1 _

theorem MBH_sim01 : simB 0 1 := Or.inr ⟨by decide, by decide⟩

theorem MBH_not_sim02 : ¬ simB 0 2 := by
  intro h
  rcases h with e | ⟨_, h2⟩
  · exact absurd e (by decide)
  · exact h2 rfl

/-! ## Valid principles -/

/-- Cantor: the constant function to `1` is not a haecceity, so it is its own root, which lies at
a larger code than the root of any item of `α`. -/
theorem MBH_Cantor : MBH.Valid Cantor := by
  intro ρ env
  refine (MBH.holds_tall _ _ _).mpr fun a => (MBH.holds_ex _ _ _ _).mpr ⟨fun _ => (1 : Fin 3), ?_⟩
  refine (MBH.holds_all _ _ _ _).mpr fun y => (MBH.holds_neg _ _ _).mpr fun h => ?_
  have h1 : Er3 VB simB (root3 VB simB (.arr a .t) (fun _ => (1 : Fin 3))) (root3 VB simB a y) :=
    (MBH_V _).mp ((MBH.holds_eqv _ _ _ _ _ _).mp h)
  have h2 : (root3 VB simB a y).1 = .arr a .t :=
    (MBH_Er_fst h1).symm.trans (congrArg Sigma.fst (MBH_root_one a))
  exact MBH_not_small h2 (MBH_root_le a y)

/-- PCong: functions with one domain which are identified are the same function. -/
theorem MBH_PCong : MBH.Valid PCong := by
  intro ρ env
  refine (MBH.holds_tall _ _ _).mpr fun a => (MBH.holds_tall _ _ _).mpr fun c =>
    (MBH.holds_tall _ _ _).mpr fun d => ?_
  refine (MBH.holds_all _ _ _ _).mpr fun f => (MBH.holds_all _ _ _ _).mpr fun g =>
    (MBH.holds_all _ _ _ _).mpr fun x => ?_
  refine (MBH.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Er3 VB simB (root3 VB simB (.arr a c) f) (root3 VB simB (.arr a d) g) :=
    (MBH_V _).mp ((MBH.holds_eqv _ _ _ _ _ _).mp h)
  obtain ⟨hcd, hfg⟩ := MBH_cod (a := a) (c := c) (d := d) f g h'
  subst hcd
  cases hfg
  exact (MBH.holds_eqv _ _ _ _ _ _).mpr ((MBH_V _).mpr (Er3_refl VB simB _))

theorem MBH_Inj : MBH.Valid Inj := by
  intro ρ env
  refine (MBH.holds_tall _ _ _).mpr fun a => (MBH.holds_tall _ _ _).mpr fun b => ?_
  refine (MBH.holds_tall _ _ _).mpr fun c => (MBH.holds_tall _ _ _).mpr fun d => ?_
  refine (MBH.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (MBH_V _).mp ((MBH.holds_teq _ _ _ _).mp h)
  injection h' with hab hcd
  exact (MBH.holds_conj _ _ _ _).mpr ⟨(MBH.holds_teq _ _ _ _).mpr ((MBH_V _).mpr hab),
    (MBH.holds_teq _ _ _ _).mpr ((MBH_V _).mpr hcd)⟩

theorem MBH_Recovery : MBH.Valid Recovery := by
  intro ρ env
  refine (MBH.holds_tall _ _ _).mpr fun a => (MBH.holds_tall _ _ _).mpr fun b => ?_
  refine (MBH.holds_tall _ _ _).mpr fun c => (MBH.holds_tall _ _ _).mpr fun d => ?_
  refine (MBH.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d :=
    (MBH_V _).mp ((MBH.holds_teq _ _ _ _).mp ((MBH.holds_conj _ _ _ _).mp h).1)
  exact (MBH.holds_teq _ _ _ _).mpr ((MBH_V _).mpr (Code.arr.inj h').2)

theorem MBH_ExtT : MBH.Valid ExtT := by
  intro ρ env
  refine (MBH.holds_tall _ _ _).mpr fun a => (MBH.holds_tall _ _ _).mpr fun b => ?_
  refine (MBH.holds_imp _ _ _ _).mpr fun h => (MBH.holds_teq _ _ _ _).mpr ((MBH_V _).mpr ?_)
  have hc := (MBH.holds_conj _ _ _ _).mp h
  refine MBH_ext_core a b (fun x => ?_) (fun y => ?_)
  · obtain ⟨y, hy⟩ := (MBH.holds_ex _ _ _ _).mp ((MBH.holds_all _ _ _ _).mp hc.1 x)
    exact ⟨y, (MBH_V _).mp ((MBH.holds_eqv _ _ _ _ _ _).mp hy)⟩
  · obtain ⟨x, hx⟩ := (MBH.holds_ex _ _ _ _).mp ((MBH.holds_all _ _ _ _).mp hc.2 y)
    exact ⟨x, (MBH_V _).mp ((MBH.holds_eqv _ _ _ _ _ _).mp hx)⟩

/-- Int≈: a necessary universal claim is true, since its value is not `1`. -/
theorem MBH_IntT : MBH.Valid IntT := by
  intro ρ env
  refine (MBH.holds_tall _ _ _).mpr fun a => (MBH.holds_tall _ _ _).mpr fun b => ?_
  refine (MBH.holds_imp _ _ _ _).mpr fun h => (MBH.holds_teq _ _ _ _).mpr ((MBH_V _).mpr ?_)
  have hc := (MBH.holds_conj _ _ _ _).mp h
  have h1 : MBH.Holds (subT : Fm (Ctx.nil.text.text)) (scons b (scons a ρ)) env :=
    MBH_sim_true (simB_symm _ _ ((MBH_box _ _ _).mp hc.1)) VB0 (MBH_eval_all_ne1 _ _ _ _)
  have h2 : MBH.Holds (supT : Fm (Ctx.nil.text.text)) (scons b (scons a ρ)) env :=
    MBH_sim_true (simB_symm _ _ ((MBH_box _ _ _).mp hc.2)) VB0 (MBH_eval_all_ne1 _ _ _ _)
  refine MBH_ext_core a b (fun x => ?_) (fun y => ?_)
  · obtain ⟨y, hy⟩ := (MBH.holds_ex _ _ _ _).mp ((MBH.holds_all _ _ _ _).mp h1 x)
    exact ⟨y, (MBH_V _).mp ((MBH.holds_eqv _ _ _ _ _ _).mp hy)⟩
  · obtain ⟨x, hx⟩ := (MBH.holds_ex _ _ _ _).mp ((MBH.holds_all _ _ _ _).mp h2 y)
    exact ⟨x, (MBH_V _).mp ((MBH.holds_eqv _ _ _ _ _ _).mp hx)⟩

/-! ## TBF and TCBF, by a logical relation

Every constant is *good*: its values at `t` are never `1`. A logical relation shows that the value of
every closed formula is good. So a closed formula identified with `⊤` (that is, with value `0` or
`1`) has the value `0`, and is true. -/

section Good
variable (Gt : MBH.U.P → Prop)

/-- Goodness at each code. -/
def MBH_GC : (c : Code MBH.U.Base) → MBH.U.El c → Prop
  | .e, _ => True
  | .t, p => Gt p
  | .base _, _ => True
  | .arr a c, f => ∀ x, MBH_GC a x → MBH_GC c (f x)

/-- Goodness at each category. -/
def MBH_GK : {n : Nat} → (K : Cat n) → (ρ : MBH.U.TEnv n) → MBH.U.CatVal K ρ → Prop
  | _, .e, _, _ => True
  | _, .t, _, p => Gt p
  | _, .var i, ρ, x => MBH_GC Gt (ρ i) x
  | _, .arr K L, ρ, f => ∀ u, MBH_GK K ρ u → MBH_GK L ρ (f u)
  | _, .pi K, ρ, G => ∀ a, MBH_GK K (scons a ρ) (G a)

theorem MBH_GC_heq {c c' : Code MBH.U.Base} (hc : c = c') (x : MBH.U.El c) (y : MBH.U.El c')
    (h : HEq x y) : MBH_GC Gt c x ↔ MBH_GC Gt c' y := by
  subst hc; cases h; exact Iff.rfl

theorem MBH_GK_GC {n : Nat} (K : Cat n) : ∀ (_ : K.Simple) (ρ : MBH.U.TEnv n) (u : MBH.U.CatVal K ρ)
    (x : MBH.U.El (MBH.U.code K ρ)), HEq u x → (MBH_GK Gt K ρ u ↔ MBH_GC Gt (MBH.U.code K ρ) x) := by
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

theorem MBH_GK_ren {n : Nat} (K : Cat n) : ∀ {m : Nat} (r : Fin n → Fin m) (ρ : MBH.U.TEnv m)
    (ρ₂ : MBH.U.TEnv n), (∀ i, ρ (r i) = ρ₂ i) → ∀ (v : MBH.U.CatVal (K.ren r) ρ) (w : MBH.U.CatVal K ρ₂),
    HEq v w → (MBH_GK Gt (K.ren r) ρ v ↔ MBH_GK Gt K ρ₂ w) := by
  induction K with
  | e => intro m r ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | t => intro m r ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | var i => intro m r ρ ρ₂ hρ v w hv; exact MBH_GC_heq Gt (hρ i) v w hv
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

theorem MBH_GK_sub {n : Nat} (K : Cat n) : ∀ {m : Nat} (s : Fin n → Ty m) (ρ : MBH.U.TEnv m)
    (ρ₂ : MBH.U.TEnv n), (∀ i, MBH.U.code (s i).1 ρ = ρ₂ i) →
    ∀ (v : MBH.U.CatVal (K.sub s) ρ) (w : MBH.U.CatVal K ρ₂),
    HEq v w → (MBH_GK Gt (K.sub s) ρ v ↔ MBH_GK Gt K ρ₂ w) := by
  induction K with
  | e => intro m s ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | t => intro m s ρ ρ₂ _ v w hv; cases hv; exact Iff.rfl
  | var i =>
    intro m s ρ ρ₂ hρ v w hv
    exact (MBH_GK_GC Gt (s i).1 (s i).2 ρ v (cast (Univ.El_code ρ (s i).2).symm v) (cast_heq _ v).symm).trans
      (MBH_GC_heq Gt (hρ i) _ w ((cast_heq _ v).trans hv))
  | arr a b iha ihb =>
    intro m s ρ ρ₂ hρ v w hv
    refine Invariance.forall_heq (Univ.CatVal_sub a s ρ ρ₂ hρ) fun u y huy => ?_
    refine imp_congr (iha s ρ ρ₂ hρ u y huy) (ihb s ρ ρ₂ hρ _ _ ?_)
    exact heq_app (Univ.CatVal_sub a s ρ ρ₂ hρ) (Univ.CatVal_sub b s ρ ρ₂ hρ) hv huy
  | pi K ih =>
    intro m s ρ ρ₂ hρ v w hv
    have hl : ∀ a, ∀ i, MBH.U.code (liftT s i).1 (scons a ρ) = scons a ρ₂ i := fun a =>
      fin_cases rfl (fun i => by
        show MBH.U.code ((s i).1.ren fs) (scons a ρ) = ρ₂ i
        rw [Univ.code_ren]; exact hρ i)
    refine forall_congr' fun a => ?_
    exact ih (liftT s) (scons a ρ) (scons a ρ₂) (hl a) _ _
      (heq_dapp (fun a => Univ.CatVal_sub K (liftT s) (scons a ρ) (scons a ρ₂) (hl a)) hv rfl)

/-- Good values for the term variables of a context. -/
def MBH_EG : {n : Nat} → (Γ : Ctx n) → (ρ : MBH.U.TEnv n) → MBH.U.Env Γ ρ → Prop
  | _, .nil, _, _ => True
  | _, .ext Γ σ, ρ, env => MBH_EG Γ ρ env.1 ∧ MBH_GK Gt σ.1 ρ env.2
  | _, .text Γ, ρ, env => MBH_EG Γ (fun i => ρ (fs i)) env

theorem MBH_lookup_good {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) :
    ∀ (ρ : MBH.U.TEnv n) (env : MBH.U.Env Γ ρ), MBH_EG Gt Γ ρ env → MBH_GK Gt K ρ (MBH.U.lookup x ρ env) := by
  induction x with
  | here => intro ρ env h; exact h.2
  | there y ih => intro ρ env h; exact ih ρ env.1 h.1
  | tthere y ih =>
    intro ρ env h
    exact (MBH_GK_ren Gt _ fs ρ (fun i => ρ (fs i)) (fun _ => rfl) _ _ (MBH.lookup_tthere y ρ env)).mpr
      (ih _ env h)

/-- **The fundamental lemma**: if every constant is good, every term is good under good values
for its variables. -/
theorem MBH_fund (hc : ∀ {n : Nat} {K : Cat n} (c : Const n K) (ρ : MBH.U.TEnv n),
      MBH_GK Gt K ρ (MBH.constVal c ρ))
    {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) : ∀ (ρ : MBH.U.TEnv n) (env : MBH.U.Env Γ ρ),
    MBH_EG Gt Γ ρ env → MBH_GK Gt K ρ (MBH.eval M ρ env) := by
  induction M with
  | var x => intro ρ env h; exact MBH_lookup_good Gt x ρ env h
  | const c => intro ρ _ _; exact hc c ρ
  | app f a ihf iha => intro ρ env h; exact ihf ρ env h _ (iha ρ env h)
  | lam σ b ih => intro ρ env h u hu; exact ih ρ (env, u) ⟨h, hu⟩
  | tlam b ih => intro ρ env h a; exact ih (scons a ρ) env h
  | tapp f σ ih =>
    intro ρ env h
    exact (MBH_GK_sub Gt _ (inst σ) ρ (scons (MBH.U.code σ.1 ρ) ρ) (fin_cases rfl (fun _ => rfl)) _ _
      (MBH.heq_eval_tapp f σ ρ env)).mpr (ih ρ env h (MBH.U.code σ.1 ρ))

end Good

/-- A proposition is good if it is not `1`. -/
def MBH_Gt (p : MBH.U.P) : Prop := @Ne (Fin 3) p 1

theorem MBH_const_good {n : Nat} {K : Cat n} (c : Const n K) (ρ : MBH.U.TEnv n) :
    MBH_GK MBH_Gt K ρ (MBH.constVal c ρ) := by
  cases c with
  | neg => intro _ _; exact MBH_mk3_ne1 _
  | imp => intro _ _ _ _; exact MBH_mk3_ne1 _
  | and => intro _ _ _ _; exact MBH_mk3_ne1 _
  | or => intro _ _ _ _; exact MBH_mk3_ne1 _
  | iff => intro _ _ _ _; exact MBH_mk3_ne1 _
  | all => intro _ _ _; exact MBH_mk3_ne1 _
  | ex => intro _ _ _; exact MBH_mk3_ne1 _
  | tall => intro _ _; exact MBH_mk3_ne1 _
  | tex => intro _ _; exact MBH_mk3_ne1 _
  | eqv => intro _ _ _ _ _ _; exact MBH_mk3_ne1 _
  | teq => intro _ _; exact MBH_mk3_ne1 _

/-- No closed formula (with one free type variable) has the value `1`. -/
theorem MBH_closed_good (φ : Fm Ctx.nil.text) (a : Code MBH.U.Base) (ρ : MBH.U.TEnv 0)
    (env : MBH.U.Env Ctx.nil ρ) : MBH_Gt (MBH.eval φ (scons a ρ) env) :=
  MBH_fund MBH_Gt MBH_const_good φ (scons a ρ) env trivial

/-- No closed formula has the value `1`. -/
theorem MBH_closed_good0 (φ : Fm Ctx.nil) (ρ : MBH.U.TEnv 0) (env : MBH.U.Env Ctx.nil ρ) :
    MBH_Gt (MBH.eval φ ρ env) :=
  MBH_fund MBH_Gt MBH_const_good φ ρ env trivial

theorem MBH_TBF : ∀ χ, TBFSch χ → MBH.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MBH.holds_imp _ _ _ _).mpr fun h => (MBH_box _ _ _).mpr (Or.inl ?_)
  have h1 : MBH.Holds (Tm.tall φ) ρ env := (MBH.holds_tall _ _ _).mpr fun a =>
    MBH_sim_true (simB_symm _ _ ((MBH_box _ _ _).mp ((MBH.holds_tall _ _ _).mp h a))) VB0
      (MBH_closed_good φ a ρ env)
  exact h1

theorem MBH_TCBF : ∀ χ, TCBFSch χ → MBH.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MBH.holds_imp _ _ _ _).mpr fun h => (MBH.holds_tall _ _ _).mpr fun a =>
    (MBH_box _ _ _).mpr (Or.inl ?_)
  have h1 : MBH.Holds (Tm.tall φ) ρ env :=
    MBH_sim_true (simB_symm _ _ ((MBH_box _ _ _).mp h)) VB0 (MBH_closed_good0 (Tm.tall φ) ρ env)
  exact (MBH.holds_tall _ _ _).mp h1 a

/-! ## Refuted principles -/

/-- The function sending `0` to `0`, and `1` and `2` to `2`. -/
noncomputable def MBH_phi : (univ3 VB).El (.arr .t .t) := fun p => mk3 (p = (0 : Fin 3))

theorem MBH_phi_0 : @Eq (Fin 3) (MBH_phi (0 : Fin 3)) 0 := mk3_eq0 rfl
theorem MBH_phi_1 : @Eq (Fin 3) (MBH_phi (1 : Fin 3)) 2 := mk3_eq2 (by decide : ¬ (1 : Fin 3) = 0)

/-- WCong fails: `0 ≡ 1`, but `MBH_phi` sends them to `0` and `2`, which are not identified. -/
theorem MBH_not_WCong : ¬ MBH.Valid WCong := fun h => by
  have h0 := (MBH.holds_tall _ _ _).mp ((MBH.holds_tall _ _ _).mp ((MBH.holds_tall _ _ _).mp
    ((MBH.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) .t) .t) .t
  have h1 := (MBH.holds_all _ _ _ _).mp ((MBH.holds_all _ _ _ _).mp ((MBH.holds_all _ _ _ _).mp
    ((MBH.holds_all _ _ _ _).mp h0 MBH_phi) MBH_phi) (0 : Fin 3)) (1 : Fin 3)
  have h2 := (MBH.holds_imp _ _ _ _).mp h1 ((MBH.holds_conj _ _ _ _).mpr
    ⟨(MBH.holds_conj _ _ _ _).mpr ⟨(MBH.holds_teq _ _ _ _).mpr ((MBH_V _).mpr rfl),
      (MBH.holds_teq _ _ _ _).mpr ((MBH_V _).mpr rfl)⟩,
     (MBH.holds_conj _ _ _ _).mpr ⟨(MBH.holds_eqv _ _ _ _ _ _).mpr ((MBH_V _).mpr (Er3_refl VB simB _)),
       (MBH.holds_eqv _ _ _ _ _ _).mpr ((F3_eqT VB VB0 VB2 simB _ _ simB_refl).mpr MBH_sim01)⟩⟩)
  have h3 : simB (MBH_phi (0 : Fin 3)) (MBH_phi (1 : Fin 3)) :=
    (F3_eqT VB VB0 VB2 simB _ _ simB_refl).mp ((MBH.holds_eqv _ _ _ _ _ _).mp h2)
  rw [MBH_phi_0, MBH_phi_1] at h3
  exact MBH_not_sim02 h3

/-- Cong fails, for the same reason. -/
theorem MBH_not_Cong : ¬ MBH.Valid Cong := fun h => by
  have h0 := (MBH.holds_tall _ _ _).mp ((MBH.holds_tall _ _ _).mp ((MBH.holds_tall _ _ _).mp
    ((MBH.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) .t) .t) .t
  have h1 := (MBH.holds_all _ _ _ _).mp ((MBH.holds_all _ _ _ _).mp ((MBH.holds_all _ _ _ _).mp
    ((MBH.holds_all _ _ _ _).mp h0 MBH_phi) MBH_phi) (0 : Fin 3)) (1 : Fin 3)
  have h2 := (MBH.holds_imp _ _ _ _).mp h1 ((MBH.holds_conj _ _ _ _).mpr
    ⟨(MBH.holds_eqv _ _ _ _ _ _).mpr ((MBH_V _).mpr (Er3_refl VB simB _)),
     (MBH.holds_eqv _ _ _ _ _ _).mpr ((F3_eqT VB VB0 VB2 simB _ _ simB_refl).mpr MBH_sim01)⟩)
  have h3 : simB (MBH_phi (0 : Fin 3)) (MBH_phi (1 : Fin 3)) :=
    (F3_eqT VB VB0 VB2 simB _ _ simB_refl).mp ((MBH.holds_eqv _ _ _ _ _ _).mp h2)
  rw [MBH_phi_0, MBH_phi_1] at h3
  exact MBH_not_sim02 h3

/-- The haecceity of the entity. -/
noncomputable def MBH_hae : (univ3 VB).El (.arr .e .t) :=
  mkH3 VB .e (fun y => Er3 VB simB (root3 VB simB .e y) (root3 VB simB .e ()))

theorem MBH_hae_root : Er3 VB simB (root3 VB simB .e ()) (root3 VB simB (.arr .e .t) MBH_hae) :=
  eroot_hae (univ3 VB).El (Er3 VB simB) (mkH3 VB) (Er3_refl VB simB) (Er3_symm VB simB simB_symm)
    (fun _ P Q h y hy => (mk3_V VB VB0 VB2 _).mp
      ((congrArg VB (congrFun h y : mk3 (P y) = mk3 (Q y))).mpr ((mk3_V VB VB0 VB2 _).mpr hy))) .e ()

/-- PExt fails: the constant function from `e` to the entity and the constant function to its
haecceity agree pointwise up to identity, but they are their own roots, at different codes. -/
theorem MBH_not_PExt : ¬ MBH.Valid PExt := fun h => by
  have h0 := (MBH.holds_tall _ _ _).mp ((MBH.holds_tall _ _ _).mp ((MBH.holds_tall _ _ _).mp
    (h (fun i => i.elim0) ()) .e) .e) (.arr .e .t)
  have h1 := (MBH.holds_all _ _ _ _).mp ((MBH.holds_all _ _ _ _).mp h0
    (fun _ => () : (univ3 VB).El .e → (univ3 VB).El .e))
    (fun _ => MBH_hae : (univ3 VB).El .e → (univ3 VB).El (.arr .e .t))
  have h2 := (MBH.holds_imp _ _ _ _).mp h1 ((MBH.holds_all _ _ _ _).mpr fun _ =>
    (MBH.holds_eqv _ _ _ _ _ _).mpr ((MBH_V _).mpr MBH_hae_root))
  have h3 : Er3 VB simB (root3 VB simB (.arr .e .e) (fun _ => () : (univ3 VB).El .e → (univ3 VB).El .e))
      (root3 VB simB (.arr .e (.arr .e .t)) (fun _ => MBH_hae : (univ3 VB).El .e → (univ3 VB).El (.arr .e .t))) :=
    (MBH_V _).mp ((MBH.holds_eqv _ _ _ _ _ _).mp h2)
  have h4 := MBH_Er_fst h3
  exact nomatch (h4 : (Code.arr .e .e : Code (univ3 VB).Base) = .arr .e (.arr .e .t))

/-- The Identity Identity fails: `0 ≡ 1` is `0`, while `∀G (G 0 → G 1)` is `2`. -/
theorem MBH_not_IdId : ¬ MBH.Valid IdId := fun h => by
  have h0 := (MBH.holds_all _ _ _ _).mp ((MBH.holds_all _ _ _ _).mp
    ((MBH.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) (0 : Fin 3)) (1 : Fin 3)
  have h1 := (F3_eqT VB VB0 VB2 simB _ _ simB_refl).mp ((MBH.holds_eqv_t _ _ _ _).mp h0)
  have hX : MBH.Holds (Tm.eqv tv0 tv0 (.var (.there .here)) (.var .here) : Fm (((Ctx.nil.text).ext tv0).ext tv0))
      (scons .t (fun i => i.elim0)) (((), (0 : Fin 3)), (1 : Fin 3)) :=
    (MBH.holds_eqv _ _ _ _ _ _).mpr ((F3_eqT VB VB0 VB2 simB _ _ simB_refl).mpr MBH_sim01)
  have hY := MBH_sim_true h1 hX (MBH_eval_all_ne1 _ _ _ _)
  have h5 := (MBH.holds_imp _ _ _ _).mp ((MBH.holds_all _ _ _ _).mp hY (fun p => p)) rfl
  exact (by decide : ¬ (1 : Fin 3) = 0) h5

/-- Booleanism fails: `¬¬1` is `2`, which is not identified with `1`. -/
theorem MBH_not_DNeg : ¬ MBH.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MBH.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (1 : Fin 3)
  have h1 : simB (MBH.neg (MBH.neg (1 : Fin 3))) 1 :=
    (F3_eqT VB VB0 VB2 simB _ _ simB_refl).mp ((MBH.holds_eqv_t _ _ _ _).mp h0)
  have e1 : @Eq (Fin 3) (MBH.neg (1 : Fin 3)) 0 := mk3_eq0 (show ¬ VB 1 by unfold VB; decide)
  have e2 : @Eq (Fin 3) (MBH.neg (0 : Fin 3)) 2 := mk3_eq2 (fun h => h VB0)
  rw [e1, e2] at h1
  rcases h1 with e | ⟨h2, _⟩
  · exact absurd e (by decide)
  · exact h2 rfl

theorem MBH_not_Bool : ¬ ∀ φ, BoolSch φ → MBH.Valid φ := fun h => MBH_not_DNeg (h _ DNeg_bool)

theorem MBH_not_Class : ¬ ∀ χ, ClassSch χ → MBH.Valid χ := fun h =>
  MBH_not_Bool fun φ hφ => MBH.soundness MBH_model h (d_Bool_of_Class (S := ClassSch) (fun _ hc => hc) φ hφ)

/-! ## LL≡/≈ fails

The polymorphic predicate `λγ.λz:γ. ∃_{γ→t} F (F ≡_{γ→t,t→t} λp:t.p ∧ F z)`. At `t`, the only `F`
identified with `λp.p` is `λp.p` itself (which is not a haecceity, since it takes the value `1`),
so the predicate holds of just the true proposition `0`. But `0 ≡ 1`, at the same type. -/

def MBH_PredId : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (Tm.ex tv0.pred (Tm.conj (Tm.eqv tv0.pred tyT.pred (.var .here) (.lam tyT (.var .here)))
    (.app (.var .here) (.var (.there .here))))))

theorem MBH_not_Bridge : ¬ MBH.Valid (Bridge MBH_PredId) := fun h => by
  have h0 := (MBH.holds_tall _ _ _).mp ((MBH.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) .t
  have h1 := (MBH.holds_all _ _ _ _).mp ((MBH.holds_all _ _ _ _).mp h0 (0 : Fin 3)) (1 : Fin 3)
  have h2 := (MBH.holds_imp _ _ _ _).mp h1 ((MBH.holds_conj _ _ _ _).mpr
    ⟨(MBH.holds_eqv _ _ _ _ _ _).mpr ((F3_eqT VB VB0 VB2 simB _ _ simB_refl).mpr MBH_sim01),
     (MBH.holds_teq _ _ _ _).mpr ((MBH_V _).mpr rfl)⟩)
  have hP0 : VB (MBH.ex (.arr .t .t) (fun F => MBH.cnj (MBH.eqv (.arr .t .t) (.arr .t .t) F (fun p => p))
      (F (0 : Fin 3)))) :=
    (MBH.hex _ _).mpr ⟨fun p => p, (MBH.hcnj _ _).mpr ⟨(MBH_V _).mpr (Er3_refl VB simB _), rfl⟩⟩
  have h3 := (MBH.holds_imp _ _ _ _).mp h2 hP0
  have hP1 : VB (MBH.ex (.arr .t .t) (fun F => MBH.cnj (MBH.eqv (.arr .t .t) (.arr .t .t) F (fun p => p))
      (F (1 : Fin 3)))) := h3
  obtain ⟨F, hF⟩ := (MBH.hex _ _).mp hP1
  have hF' := (MBH.hcnj _ _).mp hF
  have e := (MBH_cod (a := .t) (c := .t) (d := .t) F (fun p => p) ((MBH_V _).mp hF'.1)).2
  have e' : F = fun p => p := eq_of_heq e
  subst e'
  exact (by decide : ¬ (1 : Fin 3) = 0) hF'.2

end Al
end PIF
