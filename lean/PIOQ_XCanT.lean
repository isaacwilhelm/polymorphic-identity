import PIBF
import PIOQ_MSTc
set_option autoImplicit false

/-!
# `𝔐_C,tw`: Cantor fails, together with Collapse, PropExt≡, Booleanism and the modal principles

An algebraic model of PI⁻. There is one entity and no further base types. Propositions are pairs of
a set of two worlds (the actual world `true` and another world `false`) and a tag; a proposition is
true when the actual world is in its set.

Each item has a *root*: every item of `t→t` has the root `⊥₀` (true at no world, tag `true`);
every other item is its own root. Identity of items holds at the actual world just in case
the roots agree, holds at the other world always, and has tag `false`. Identity of types holds at
the actual world just in case the types are the same, and at the other world just in case they
differ, with tag `true`. The connectives act world by world with tag `true`; the existential
quantifiers (over items and over types) act world by world with tag `false`; the universal
quantifiers act world by world, with tag `false` when every instance is `⊤₀` (true at both worlds,
tag `true`) and tag `true` otherwise.

So `□φ` holds just in case the value of `φ` is `⊤₀`.

Cantor fails at `t`: every property of propositions is identified with `⊥₀`. The two worlds refute
Collapse, PropExt≡, NI≈ and ND≈; the tags refute Booleanism, NI≡, NI×, Nec and Type Necessitism;
identity at the other world refutes ND×; and the tags of the universal quantifiers refute both
Barcan formulas and both type Barcan formulas.

The full profile. Valid: Truth, ⊤≢⊥, T, Slogan, Inj≈, Recovery, Ext≈, Int≈, Choice.
Refuted: Cantor, LL≡, Classicism, LL≡/≈ and LL≡-Poly (for `MSTc_PredEv`), WCong, Cong, PCong→,
PCong←, Haecceitism, Disjoint, Twin, the Identity Identity, Collapse, PropExt≡, Booleanism, NI≡,
NI≈, ND≈, NI×, ND×, Nec, TNec, BF, CBF, TBF, TCBF.
-/

namespace PIF
namespace Al
open Tm

section XCT
attribute [local instance] Classical.propDecidable

/-- `⊥₀`: true at no world, tag `true`. -/
def XCT_bot : univH.P := ((fun _ => False), true)
/-- `⊤₀`: true at both worlds, tag `true`. -/
def XCT_top : univH.P := ((fun _ => True), true)

theorem XCT_top_ne_bot : XCT_top ≠ XCT_bot := fun e =>
  cast (congrArg (fun p : univH.P => p.1 true) e) trivial

/-- The tag of a universal quantification: `false` just in case the condition holds. -/
noncomputable def XCT_tg (c : Prop) : Bool := if c then false else true

theorem XCT_tg_pos {c : Prop} (h : c) : XCT_tg c = false := by
  unfold XCT_tg
  split
  · rfl
  · contradiction

theorem XCT_tg_neg {c : Prop} (h : ¬ c) : XCT_tg c = true := by
  unfold XCT_tg
  split
  · contradiction
  · rfl

/-- Roots: every item of `t→t` has the root `⊥₀`; every other item is its own root. -/
def XCT_root : (c : Code univH.Base) → univH.El c → RW
  | .arr .t .t, _ => ⟨.t, XCT_bot⟩
  | c, x => ⟨c, x⟩

theorem XCT_root_tt (G : univH.El (.arr .t .t)) : XCT_root (.arr .t .t) G = ⟨.t, XCT_bot⟩ := rfl

theorem XCT_root_ne : ∀ (c : Code Empty) (x : univH.El c), c ≠ .arr .t .t → XCT_root c x = ⟨c, x⟩
  | .e, _, _ => rfl
  | .t, _, _ => rfl
  | .base b, _, _ => Empty.elim b
  | .arr .e _, _, _ => rfl
  | .arr .t .e, _, _ => rfl
  | .arr .t .t, _, h => absurd rfl h
  | .arr .t (.base b), _, _ => Empty.elim b
  | .arr .t (.arr _ _), _, _ => rfl
  | .arr (.base b) _, _, _ => Empty.elim b
  | .arr (.arr _ _) _, _, _ => rfl

/-- The root of an item is of the item's own type, or of type `t`. -/
theorem XCT_root_fst (c : Code Empty) (x : univH.El c) : (XCT_root c x).1 = c ∨ (XCT_root c x).1 = .t := by
  by_cases h : c = .arr .t .t
  · subst h
    exact Or.inr rfl
  · rw [XCT_root_ne c x h]
    exact Or.inl rfl

theorem XCT_eq_of_root_t {p q : univH.P} (h : XCT_root .t p = XCT_root .t q) : p = q :=
  eq_of_heq (Sigma.mk.inj h).2

noncomputable def XCT_F : Frame where
  U := univH
  eqv := fun a b x y => ((fun w => cond w (XCT_root a x = XCT_root b y) True), false)
  teq := fun a b => ((fun w => cond w (a = b) (a ≠ b)), true)
  neg := fun p => ((fun w => ¬ p.1 w), true)
  imp := fun p q => ((fun w => p.1 w → q.1 w), true)
  cnj := fun p q => ((fun w => p.1 w ∧ q.1 w), true)
  dsj := fun p q => ((fun w => p.1 w ∨ q.1 w), true)
  bic := fun p q => ((fun w => p.1 w ↔ q.1 w), true)
  all := fun _ f => ((fun w => ∀ x, (f x).1 w), XCT_tg (∀ x, f x = XCT_top))
  ex := fun _ f => ((fun w => ∃ x, (f x).1 w), false)
  tall := fun Q => ((fun w => ∀ a, (Q a).1 w), XCT_tg (∀ a, Q a = XCT_top))
  tex := fun Q => ((fun w => ∃ a, (Q a).1 w), false)
  hneg := fun _ => Iff.rfl
  himp := fun _ _ => Iff.rfl
  hcnj := fun _ _ => Iff.rfl
  hdsj := fun _ _ => Iff.rfl
  hbic := fun _ _ => Iff.rfl
  hall := fun _ _ => Iff.rfl
  hex := fun _ _ => Iff.rfl
  htall := fun _ => Iff.rfl
  htex := fun _ => Iff.rfl

end XCT

theorem XCT_model : XCT_F.IsModelPIm :=
  XCT_F.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ _ _ h => h.symm)
    (fun _ _ _ _ _ _ h1 h2 => h1.trans h2)

/-! ## Basic facts -/

theorem XCT_topF {n : Nat} {Γ : Ctx n} (ρ : XCT_F.U.TEnv n) (env : XCT_F.U.Env Γ ρ) :
    XCT_F.eval (topF : Fm Γ) ρ env = XCT_top :=
  Prod.ext (funext fun _ => propext ⟨fun _ => trivial, fun _ h => (h XCT_bot : False)⟩) rfl

theorem XCT_holds_eqv_t {n : Nat} {Γ : Ctx n} (x y : Fm Γ) (ρ : XCT_F.U.TEnv n) (env : XCT_F.U.Env Γ ρ) :
    XCT_F.Holds (eqv tyT tyT x y) ρ env ↔ XCT_F.eval x ρ env = XCT_F.eval y ρ env :=
  (XCT_F.holds_eqv_t x y ρ env).trans ⟨fun h => XCT_eq_of_root_t h, fun h => congrArg (XCT_root .t) h⟩

/-- `□φ` holds just in case `φ` has the value `⊤₀`. -/
theorem XCT_holds_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : XCT_F.U.TEnv n) (env : XCT_F.U.Env Γ ρ) :
    XCT_F.Holds (boxF φ) ρ env ↔ XCT_F.eval φ ρ env = XCT_top :=
  (XCT_holds_eqv_t φ topF ρ env).trans
    ⟨fun h => h.trans (XCT_topF ρ env), fun h => h.trans (XCT_topF ρ env).symm⟩

theorem XCT_of_prov {S : Fm Ctx.nil → Prop} (hS : ∀ ψ, S ψ → XCT_F.Valid ψ) {φ : Fm Ctx.nil}
    (h : Prov S Ctx.nil φ) : XCT_F.Valid φ :=
  XCT_F.soundness XCT_model hS h

/-! ## Cantor -/

/-- Cantor fails at `t`: every property of propositions is identified with `⊥₀`. -/
theorem XCT_not_Cantor : ¬ XCT_F.Valid Cantor := fun h => by
  obtain ⟨G, hG⟩ := (XCT_F.holds_ex _ _ _ _).mp ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t)
  exact (XCT_F.holds_neg _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp hG XCT_bot) rfl

/-! ## The two worlds: Collapse, PropExt≡, NI≈, ND≈ -/

theorem XCT_not_Collapse : ¬ XCT_F.Valid Collapse := fun h => by
  have h0 := (XCT_F.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (((fun w => w = true), true) : univH.P)
  have hb := (XCT_holds_box _ _ _).mp ((XCT_F.holds_imp _ _ _ _).mp h0 rfl)
  exact Bool.noConfusion (cast (congrFun (congrArg Prod.fst hb) false).symm trivial : false = true)

theorem XCT_not_PropExt : ¬ XCT_F.Valid PropExt := fun h => by
  have h0 := (XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) XCT_top)
    (((fun w => w = true), true) : univH.P)
  have h1 := (XCT_F.holds_imp _ _ _ _).mp h0 ((XCT_F.holds_iff _ _ _ _).mpr ⟨fun _ => rfl, fun _ => trivial⟩)
  have e : XCT_top = (((fun w => w = true), true) : univH.P) := (XCT_holds_eqv_t _ _ _ _).mp h1
  exact Bool.noConfusion (cast (congrFun (congrArg Prod.fst e) false) trivial : false = true)

theorem XCT_not_NITeq : ¬ XCT_F.Valid NITeq := fun h => by
  have h0 := (XCT_F.holds_tall _ _ _).mp ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e
  have hb := (XCT_holds_box _ _ _).mp ((XCT_F.holds_imp _ _ _ _).mp h0 ((XCT_F.holds_teq _ _ _ _).mpr rfl))
  exact (cast (congrFun (congrArg Prod.fst hb) false).symm trivial : (Code.e : Code Empty) ≠ .e) rfl

theorem XCT_not_NDTeq : ¬ XCT_F.Valid NDTeq := fun h => by
  have h0 := (XCT_F.holds_tall _ _ _).mp ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .t
  have hn : XCT_F.Holds (Tm.neg (Tm.teq tv1 tv0) : Fm Ctx.nil.text.text) (scons .t (scons .e fun i => i.elim0)) () :=
    (XCT_F.holds_neg _ _ _).mpr fun ht => nomatch ((XCT_F.holds_teq _ _ _ _).mp ht : (Code.e : Code Empty) = .t)
  have hb := (XCT_holds_box _ _ _).mp ((XCT_F.holds_imp _ _ _ _).mp h0 hn)
  exact (cast (congrFun (congrArg Prod.fst hb) false).symm trivial : ¬ ((Code.e : Code Empty) ≠ .t))
    (fun e => nomatch e)

/-! ## The tags: Booleanism, NI≡, NI×, Nec, Type Necessitism -/

theorem XCT_not_DNeg : ¬ XCT_F.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (XCT_F.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (((fun _ => True), false) : univH.P)
  have e := (XCT_holds_eqv_t _ _ _ _).mp h0
  exact Bool.noConfusion (congrArg Prod.snd e : true = false)

theorem XCT_not_Bool : ¬ ∀ φ, BoolSch φ → XCT_F.Valid φ := fun h => XCT_not_DNeg (h _ DNeg_bool)

theorem XCT_not_NIEqv : ¬ XCT_F.Valid NIEqv := fun h => by
  have h0 := (XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp
    ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have hb := (XCT_holds_box _ _ _).mp ((XCT_F.holds_imp _ _ _ _).mp h0 rfl)
  exact Bool.noConfusion (congrArg Prod.snd hb : false = true)

theorem XCT_not_NIX : ¬ XCT_F.Valid NIX := fun h => by
  have h0 := (XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_tall _ _ _).mp
    ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .e) ()) ()
  have hb := (XCT_holds_box _ _ _).mp ((XCT_F.holds_imp _ _ _ _).mp h0 rfl)
  exact Bool.noConfusion (congrArg Prod.snd hb : false = true)

theorem XCT_not_Nec : ¬ XCT_F.Valid Nec := fun h => by
  have h0 := (XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  have hb := (XCT_holds_box _ _ _).mp h0
  exact Bool.noConfusion (congrArg Prod.snd hb : false = true)

theorem XCT_not_TNec : ¬ XCT_F.Valid TNec := fun h => by
  have hb := (XCT_holds_box _ _ _).mp ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
  exact Bool.noConfusion (congrArg Prod.snd hb : false = true)

/-! ## Identity at the other world: ND× -/

theorem XCT_not_NDX : ¬ XCT_F.Valid NDX := fun h => by
  have h0 := (XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_tall _ _ _).mp
    ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) .t) XCT_top) XCT_bot
  have hb := (XCT_holds_box _ _ _).mp ((XCT_F.holds_imp _ _ _ _).mp h0 ((XCT_F.holds_neg _ _ _).mpr fun he =>
    XCT_top_ne_bot (XCT_eq_of_root_t (p := XCT_top) (q := XCT_bot) he)))
  exact (cast (congrFun (congrArg Prod.fst hb) false).symm trivial : ¬ True) trivial

/-! ## Barcan formulas -/

theorem XCT_not_BF : ¬ XCT_F.Valid BF := fun h => by
  have h0 := (XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ => XCT_top)
  have hb := (XCT_holds_box _ _ _).mp ((XCT_F.holds_imp _ _ _ _).mp h0
    ((XCT_F.holds_all _ _ _ _).mpr fun _ => (XCT_holds_box _ _ _).mpr rfl))
  have e : XCT_tg (∀ _x : Unit, XCT_top = XCT_top) = true := congrArg Prod.snd hb
  exact Bool.noConfusion ((XCT_tg_pos (fun _ => rfl)).symm.trans e)

theorem XCT_not_CBF : ¬ XCT_F.Valid CBF := fun h => by
  have h0 := (XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ => (((fun _ => True), false) : univH.P))
  have hne : ¬ ∀ _x : Unit, (((fun _ => True), false) : univH.P) = XCT_top := fun hall =>
    Bool.noConfusion (congrArg Prod.snd (hall ()) : false = true)
  have hb : XCT_F.Holds (boxF (all tv0 (Tm.app (.var (.there .here)) (.var .here))) : Fm ((Ctx.nil.text).ext tv0.pred))
      (scons .e fun i => i.elim0) ((), fun _ => (((fun _ => True), false) : univH.P)) :=
    (XCT_holds_box _ _ _).mpr (Prod.ext (funext fun _ => propext ⟨fun _ => trivial, fun _ _ => trivial⟩)
      (XCT_tg_neg hne))
  have h1 := (XCT_F.holds_imp _ _ _ _).mp h0 hb
  have e := (XCT_holds_box _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp h1 ())
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

theorem XCT_not_TBF : ¬ ∀ χ, TBFSch χ → XCT_F.Valid χ := fun h => by
  have h0 := h _ ⟨topF, rfl⟩ (fun i => i.elim0) ()
  have hb := (XCT_holds_box _ _ _).mp ((XCT_F.holds_imp _ _ _ _).mp h0 ((XCT_F.holds_tall _ _ _).mpr fun _ =>
    (XCT_holds_box _ _ _).mpr (XCT_topF _ _)))
  have e : XCT_tg (∀ a, XCT_F.eval (topF : Fm Ctx.nil.text) (scons a (fun i => i.elim0)) () = XCT_top) = true :=
    congrArg Prod.snd hb
  exact Bool.noConfusion ((XCT_tg_pos (fun a => XCT_topF (Γ := Ctx.nil.text) (scons a (fun i => i.elim0)) ())).symm.trans e)

theorem XCT_exists_ne (a : Code Empty) : ∃ b : Code Empty, a ≠ b := by
  cases a
  · exact ⟨.t, fun h => nomatch h⟩
  · exact ⟨.e, fun h => nomatch h⟩
  · exact ⟨.e, fun h => nomatch h⟩
  · exact ⟨.e, fun h => nomatch h⟩

theorem XCT_not_TCBF : ¬ ∀ χ, TCBFSch χ → XCT_F.Valid χ := fun h => by
  have h0 := h _ ⟨Tm.tex (Tm.teq tv1 tv0), rfl⟩ (fun i => i.elim0) ()
  have hne : ¬ ∀ a, XCT_F.eval (Tm.tex (Tm.teq tv1 tv0) : Fm Ctx.nil.text) (scons a (fun i => i.elim0)) () = XCT_top :=
    fun hall => Bool.noConfusion (congrArg Prod.snd (hall .e) : false = true)
  have hv : XCT_F.eval (Tm.tall (Tm.tex (Tm.teq tv1 tv0)) : Fm Ctx.nil) (fun i => i.elim0) () = XCT_top := by
    refine Prod.ext (funext fun w => propext ⟨fun _ => trivial, fun _ a => ?_⟩) (XCT_tg_neg hne)
    cases w
    · obtain ⟨b, hb⟩ := XCT_exists_ne a
      exact (⟨b, hb⟩ : ∃ b : Code Empty, cond false (a = b) (a ≠ b))
    · exact (⟨a, rfl⟩ : ∃ b : Code Empty, cond true (a = b) (a ≠ b))
  have hb := (XCT_F.holds_tall _ _ _).mp ((XCT_F.holds_imp _ _ _ _).mp h0 ((XCT_holds_box _ _ _).mpr hv)) .e
  exact Bool.noConfusion (congrArg Prod.snd ((XCT_holds_box _ _ _).mp hb) : false = true)

/-! ## Truth, `⊤ ≢ ⊥`, T -/

theorem XCT_Truth : XCT_F.Valid Truth := by
  intro ρ env
  refine (XCT_F.holds_all _ _ _ _).mpr fun p => (XCT_F.holds_all _ _ _ _).mpr fun q => ?_
  refine (XCT_F.holds_imp _ _ _ _).mpr fun he => (XCT_F.holds_imp _ _ _ _).mpr fun hp => ?_
  have e : p = q := (XCT_holds_eqv_t _ _ _ _).mp he
  subst e
  exact hp

theorem XCT_TopBot : XCT_F.Valid TopBot := by
  intro ρ env
  refine (XCT_F.holds_neg _ _ _).mpr fun h => ?_
  have e := (XCT_topF ρ env).symm.trans ((XCT_holds_eqv_t _ _ _ _).mp h)
  exact (cast (congrArg (fun p : univH.P => p.1 true) e) trivial : ∀ p : univH.P, p.1 true) XCT_bot

theorem XCT_TAx : XCT_F.Valid TAx :=
  XCT_of_prov (S := (· = Truth)) (fun _ h => h ▸ XCT_Truth) (d_TAx_of_Truth rfl)

/-! ## Identity of types -/

theorem XCT_Inj : XCT_F.Valid Inj := by
  intro ρ env
  refine (XCT_F.holds_tall _ _ _).mpr fun a => (XCT_F.holds_tall _ _ _).mpr fun b => ?_
  refine (XCT_F.holds_tall _ _ _).mpr fun c => (XCT_F.holds_tall _ _ _).mpr fun d => ?_
  refine (XCT_F.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (XCT_F.holds_teq _ _ _ _).mp h
  injection h' with hab hcd
  exact (XCT_F.holds_conj _ _ _ _).mpr ⟨(XCT_F.holds_teq _ _ _ _).mpr hab, (XCT_F.holds_teq _ _ _ _).mpr hcd⟩

theorem XCT_Recovery : XCT_F.Valid Recovery := by
  intro ρ env
  refine (XCT_F.holds_tall _ _ _).mpr fun a => (XCT_F.holds_tall _ _ _).mpr fun b => ?_
  refine (XCT_F.holds_tall _ _ _).mpr fun c => (XCT_F.holds_tall _ _ _).mpr fun d => ?_
  refine (XCT_F.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (XCT_F.holds_teq _ _ _ _).mp ((XCT_F.holds_conj _ _ _ _).mp h).1
  exact (XCT_F.holds_teq _ _ _ _).mpr (Code.arr.inj h').2

/-- Every type other than `t→t` has an item whose root is not `⊥₀`. -/
theorem XCT_wit (b : Code Empty) (hb : b ≠ .arr .t .t) : ∃ y : univH.El b, XCT_root b y ≠ ⟨.t, XCT_bot⟩ := by
  by_cases ht : b = .t
  · subst ht
    exact ⟨XCT_top, fun h => XCT_top_ne_bot (XCT_eq_of_root_t h)⟩
  · obtain ⟨y⟩ := Univ.El_nonempty (U := univH) b
    refine ⟨y, fun h => ht ?_⟩
    have e := congrArg Sigma.fst h
    rw [XCT_root_ne b y hb] at e
    exact e

theorem XCT_ext (a b : Code Empty)
    (h1 : ∀ x : univH.El a, ∃ y : univH.El b, XCT_root a x = XCT_root b y)
    (h2 : ∀ y : univH.El b, ∃ x : univH.El a, XCT_root a x = XCT_root b y) : a = b := by
  by_cases ha : a = .arr .t .t
  · by_cases hb : b = .arr .t .t
    · exact ha.trans hb.symm
    · obtain ⟨y, hy⟩ := XCT_wit b hb
      obtain ⟨x, hx⟩ := h2 y
      subst ha
      exact absurd ((XCT_root_tt x).symm.trans hx).symm hy
  · by_cases hb : b = .arr .t .t
    · obtain ⟨x, hx⟩ := XCT_wit a ha
      obtain ⟨y, hy⟩ := h1 x
      subst hb
      exact absurd (hy.trans (XCT_root_tt y)) hx
    · obtain ⟨x⟩ := Univ.El_nonempty (U := univH) a
      obtain ⟨y, hy⟩ := h1 x
      rw [XCT_root_ne a x ha, XCT_root_ne b y hb] at hy
      exact congrArg Sigma.fst hy

theorem XCT_ExtT : XCT_F.Valid ExtT := by
  intro ρ env
  refine (XCT_F.holds_tall _ _ _).mpr fun a => (XCT_F.holds_tall _ _ _).mpr fun b => ?_
  refine (XCT_F.holds_imp _ _ _ _).mpr fun h => (XCT_F.holds_teq _ _ _ _).mpr ?_
  have hs := (XCT_F.holds_conj _ _ _ _).mp h
  have h1 : ∀ x : univH.El a, ∃ y : univH.El b, XCT_root a x = XCT_root b y := fun x =>
    (XCT_F.holds_ex _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp hs.1 x)
  have h2 : ∀ y : univH.El b, ∃ x : univH.El a, XCT_root a x = XCT_root b y := fun y =>
    (XCT_F.holds_ex _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp hs.2 y)
  exact XCT_ext a b h1 h2

theorem XCT_IntT : XCT_F.Valid IntT :=
  XCT_of_prov (S := fun ψ => ψ = TAx ∨ ψ = ExtT)
    (fun _ h => h.elim (fun e => e ▸ XCT_TAx) (fun e => e ▸ XCT_ExtT)) (d_IntT_of_TAx (Or.inl rfl) (Or.inr rfl))

theorem XCT_Choice : XCT_F.Valid Choice := XCT_F.Choice_valid

/-! ## Leibniz's law, the Identity Identity, Classicism -/

/-- LL≡ fails: `λp.⊤₀` and `λp.⊥₀` are identified, but only the first is true of `⊤₀`. -/
theorem XCT_not_LLEqv : ¬ XCT_F.Valid LLEqv := fun h => by
  have h0 := (XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp
    ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) (.arr .t .t))
      (fun _ => XCT_top : univH.P → univH.P)) (fun _ => XCT_bot : univH.P → univH.P)
  have h1 := (XCT_F.holds_imp _ _ _ _).mp h0 rfl
  exact (XCT_F.holds_imp _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp h1
    (fun G : univH.P → univH.P => G XCT_top)) trivial

theorem XCT_not_IdId : ¬ XCT_F.Valid IdId := fun h =>
  XCT_not_LLEqv (XCT_of_prov (S := fun ψ => ψ = IdId ∨ ψ = Truth)
    (fun _ hψ => hψ.elim (fun e => e ▸ h) (fun e => e ▸ XCT_Truth)) (d_LLEqv_of_IdId (Or.inl rfl) (Or.inr rfl)))

theorem XCT_not_Class : ¬ ∀ χ, ClassSch χ → XCT_F.Valid χ := fun h =>
  XCT_not_Bool fun φ hφ => XCT_F.soundness XCT_model h (d_Bool_of_Class (S := ClassSch) (fun _ hc => hc) φ hφ)

/-! ## Haecceitism, Disjoint, Slogan, Twin -/

theorem XCT_not_Hae : ¬ XCT_F.Valid Hae := fun h => by
  have h0 := (XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  have h1 := congrArg Sigma.fst ((XCT_F.holds_eqv _ _ _ _ _ _).mp h0)
  exact nomatch (h1 : (Code.e : Code Empty) = .arr .e .t)

theorem XCT_not_Disjoint : ¬ XCT_F.Valid Disjoint := fun h => by
  have h0 := (XCT_F.holds_tall _ _ _).mp ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) (.arr .t .t)) .t
  have h1 := (XCT_F.holds_imp _ _ _ _).mp h0 ((XCT_F.holds_neg _ _ _).mpr fun ht =>
    nomatch ((XCT_F.holds_teq _ _ _ _).mp ht : (Code.arr .t .t : Code Empty) = .t))
  exact (XCT_F.holds_neg _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp h1
    (fun _ => XCT_bot : univH.P → univH.P)) XCT_bot) rfl

/-- No entity is identified with a property: the root of a property is of its own type or of `t`. -/
theorem XCT_Slogan : XCT_F.Valid Slogan := by
  intro ρ env
  refine (XCT_F.holds_all _ _ _ _).mpr fun x => (XCT_F.holds_tall _ _ _).mpr fun b => ?_
  refine (XCT_F.holds_all _ _ _ _).mpr fun y => (XCT_F.holds_neg _ _ _).mpr fun h => ?_
  have h' : XCT_root .e x = XCT_root (.arr b .t) y := h
  rcases XCT_root_fst (.arr b .t) y with e | e
  · exact nomatch ((congrArg Sigma.fst h').trans e : (Code.e : Code Empty) = .arr b .t)
  · exact nomatch ((congrArg Sigma.fst h').trans e : (Code.e : Code Empty) = .t)

/-- The entity has no twin. -/
theorem XCT_not_Twin : ¬ XCT_F.Valid Twin := fun h => by
  obtain ⟨b, hb⟩ := (XCT_F.holds_tex _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp
    ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ())
  have hc := (XCT_F.holds_conj _ _ _ _).mp hb
  have hne : ¬ (Code.e : Code Empty) = b := fun e => (XCT_F.holds_neg _ _ _).mp hc.1 ((XCT_F.holds_teq _ _ _ _).mpr e)
  obtain ⟨y, hy⟩ := (XCT_F.holds_ex _ _ _ _).mp hc.2
  have hy' : XCT_root .e () = XCT_root b y := hy
  rcases XCT_root_fst b y with e | e
  · exact hne ((congrArg Sigma.fst hy').trans e)
  · exact nomatch ((congrArg Sigma.fst hy').trans e : (Code.e : Code Empty) = .t)

/-! ## Congruence and extensionality -/

theorem XCT_not_WCong : ¬ XCT_F.Valid WCong := fun h => by
  have h0 := (XCT_F.holds_tall _ _ _).mp ((XCT_F.holds_tall _ _ _).mp ((XCT_F.holds_tall _ _ _).mp
    ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) .t) .t) .t
  have h1 := (XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp
    ((XCT_F.holds_all _ _ _ _).mp h0 (fun _ => XCT_bot : univH.P → univH.P))
      (fun _ => XCT_top : univH.P → univH.P)) XCT_top) XCT_top
  have h2 := (XCT_F.holds_imp _ _ _ _).mp h1 ((XCT_F.holds_conj _ _ _ _).mpr
    ⟨(XCT_F.holds_conj _ _ _ _).mpr ⟨rfl, rfl⟩, (XCT_F.holds_conj _ _ _ _).mpr ⟨rfl, rfl⟩⟩)
  exact XCT_top_ne_bot (XCT_eq_of_root_t (p := XCT_bot) (q := XCT_top) h2).symm

theorem XCT_not_Cong : ¬ XCT_F.Valid Cong := fun h => by
  have h0 := (XCT_F.holds_tall _ _ _).mp ((XCT_F.holds_tall _ _ _).mp ((XCT_F.holds_tall _ _ _).mp
    ((XCT_F.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) .t) .t) .t
  have h1 := (XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp
    ((XCT_F.holds_all _ _ _ _).mp h0 (fun _ => XCT_bot : univH.P → univH.P))
      (fun _ => XCT_top : univH.P → univH.P)) XCT_top) XCT_top
  have h2 := (XCT_F.holds_imp _ _ _ _).mp h1 ((XCT_F.holds_conj _ _ _ _).mpr ⟨rfl, rfl⟩)
  exact XCT_top_ne_bot (XCT_eq_of_root_t (p := XCT_bot) (q := XCT_top) h2).symm

theorem XCT_not_PCong : ¬ XCT_F.Valid PCong := fun h => by
  have h0 := (XCT_F.holds_tall _ _ _).mp ((XCT_F.holds_tall _ _ _).mp ((XCT_F.holds_tall _ _ _).mp
    (h (fun i => i.elim0) ()) .t) .t) .t
  have h1 := (XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp h0
    (fun _ => XCT_bot : univH.P → univH.P)) (fun _ => XCT_top : univH.P → univH.P)) XCT_top
  have h2 := (XCT_F.holds_imp _ _ _ _).mp h1 rfl
  exact XCT_top_ne_bot (XCT_eq_of_root_t (p := XCT_bot) (q := XCT_top) h2).symm

/-- PCong← fails: `λx.λp.⊤₀` and `λx.λp.⊥₀` of `e→(t→t)` take identified values, but are distinct
items that are their own roots. -/
theorem XCT_not_PExt : ¬ XCT_F.Valid PExt := fun h => by
  have h0 := (XCT_F.holds_tall _ _ _).mp ((XCT_F.holds_tall _ _ _).mp ((XCT_F.holds_tall _ _ _).mp
    (h (fun i => i.elim0) ()) .e) (.arr .t .t)) (.arr .t .t)
  have h1 := (XCT_F.holds_all _ _ _ _).mp ((XCT_F.holds_all _ _ _ _).mp h0
    (fun _ _ => XCT_top : Unit → univH.P → univH.P)) (fun _ _ => XCT_bot : Unit → univH.P → univH.P)
  have h2 := (XCT_F.holds_imp _ _ _ _).mp h1 ((XCT_F.holds_all _ _ _ _).mpr fun _ => rfl)
  have h3 : (⟨.arr .e (.arr .t .t), fun (_ : Unit) (_ : univH.P) => XCT_top⟩ : RW) =
      ⟨.arr .e (.arr .t .t), fun (_ : Unit) (_ : univH.P) => XCT_bot⟩ := h2
  exact XCT_top_ne_bot (congrFun (congrFun (eq_of_heq (Sigma.mk.inj h3).2) ()) XCT_top)

/-! ## LL≡/≈ and LL≡-Poly fail

The polymorphic predicate `λγ.λz. ∃_{γ→t} F (F ≡ ev ∧ F z)`, with `ev = λG:t→t. G ⊤`, holds of
`λp.⊤₀` but not of `λp.⊥₀` at `t→t`: identity at `(t→t)→t` is sameness, so `F` must be `ev`. -/

/-- The value of `⊤`. -/
def XCT_topv : univH.P := ((fun w => ¬ ∀ p : univH.P, p.1 w), true)

/-- What `MSTc_PredEv` says of an item. -/
def XCT_Evf (a : Code Empty) (z : univH.El a) : Prop :=
  ∃ G : univH.El a → univH.P, XCT_root (.arr a .t) G =
    XCT_root (.arr (.arr .t .t) .t) (fun H : univH.P → univH.P => H XCT_topv) ∧ (G z).1 true

theorem XCT_tr_BridgeEv : XCT_F.Holds (Bridge MSTc_PredEv) (fun i => i.elim0) () ↔
    ∀ (a b : Code Empty) (x : univH.El a) (y : univH.El b),
      (XCT_root a x = XCT_root b y ∧ a = b) → XCT_Evf a x → XCT_Evf b y := Iff.rfl

theorem XCT_tr_LLPolyEv : XCT_F.Holds (LLPoly MSTc_PredEv) (fun i => i.elim0) () ↔
    ∀ (a b : Code Empty) (x : univH.El a) (y : univH.El b),
      XCT_root a x = XCT_root b y → XCT_Evf a x → XCT_Evf b y := Iff.rfl

theorem XCT_Ev_tt (z : univH.El (.arr .t .t)) : XCT_Evf (.arr .t .t) z ↔ (z XCT_topv).1 true := by
  constructor
  · rintro ⟨G, hG, hz⟩
    have hG' : (⟨.arr (.arr .t .t) .t, G⟩ : RW) =
        ⟨.arr (.arr .t .t) .t, fun H : univH.P → univH.P => H XCT_topv⟩ := hG
    have e : G = fun H : univH.P → univH.P => H XCT_topv := eq_of_heq (Sigma.mk.inj hG').2
    subst e
    exact hz
  · intro hz
    exact ⟨fun H : univH.P → univH.P => H XCT_topv, rfl, hz⟩

theorem XCT_not_Bridge : ¬ XCT_F.Valid (Bridge MSTc_PredEv) := fun h => by
  have := XCT_tr_BridgeEv.mp ((XCT_F.valid_iff_tr _).mp h) (.arr .t .t) (.arr .t .t)
    (fun _ => XCT_top : univH.P → univH.P) (fun _ => XCT_bot : univH.P → univH.P) ⟨rfl, rfl⟩
    ((XCT_Ev_tt _).mpr trivial)
  exact (XCT_Ev_tt _).mp this

theorem XCT_not_LLPoly : ¬ XCT_F.Valid (LLPoly MSTc_PredEv) := fun h => by
  have := XCT_tr_LLPolyEv.mp ((XCT_F.valid_iff_tr _).mp h) (.arr .t .t) (.arr .t .t)
    (fun _ => XCT_top : univH.P → univH.P) (fun _ => XCT_bot : univH.P → univH.P) rfl
    ((XCT_Ev_tt _).mpr trivial)
  exact (XCT_Ev_tt _).mp this

end Al
end PIF
