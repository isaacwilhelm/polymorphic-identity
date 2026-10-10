import PIBF
set_option autoImplicit false

/-!
# Open questions: the profile of `𝔐_cq,C`

`𝔐_cq,C` (`McqC` in `lean/PIBarcanModels.lean`): propositions are sets of two worlds, the actual
one `true`; the propositions true at the actual world, together with the proposition `p₀` true
only at the other world, are identified with each other, and nothing else is identified with
anything but itself. Identity of items and of types is the same at both worlds; the connectives and
the item quantifiers act world by world; at the other world `𝔸` is true and `𝔼` false.

So the class of `⊤` is exactly the propositions true at *some* world, and `□φ` (that is, `φ ≡ ⊤`)
holds just when `φ` is true at one of the two worlds.
-/

namespace PIF
namespace Al
open Tm

/-! ## Basic facts -/

/-- The class of `⊤` consists of the propositions true at some world. -/
theorem McqC_S (p : Bool → Prop) : Scq .t p ↔ (p true ∨ p false) := by
  show (p true ∨ p = p0Q) ↔ _
  constructor
  · rintro (h | e)
    · exact Or.inl h
    · subst e; exact Or.inr rfl
  · rintro (h | h)
    · exact Or.inl h
    · by_cases h1 : p true
      · exact Or.inl h1
      · refine Or.inr (funext fun w => ?_)
        cases w
        · exact propext ⟨fun _ => rfl, fun _ => h⟩
        · exact propext ⟨fun h' => absurd h' h1, fun e => Bool.noConfusion e⟩

/-- `□φ` holds just when `φ` is true at one of the two worlds. -/
theorem McqC_holds_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : McqC.U.TEnv n) (env : McqC.U.Env Γ ρ) :
    McqC.Holds (boxF φ) ρ env ↔ (McqC.eval φ ρ env true ∨ McqC.eval φ ρ env false) := by
  have e := Mcq_top (fun _ => True) (fun _ => False) ρ env
  refine (McqC.holds_eqv_t _ _ _ _).trans ⟨fun h => ?_, fun h => ⟨rfl, Or.inr ⟨(McqC_S _).mpr h, ?_⟩⟩⟩
  · rcases h.2 with h | ⟨s, _⟩
    · exact Or.inl (cast (congrFun ((eq_of_heq h).trans e) true).symm trivial)
    · exact (McqC_S _).mp s
  · exact (McqC_S _).mpr (Or.inl (cast (congrFun e true).symm trivial))

theorem McqC_cast_all_at {c : Code McqC.U.Base} {A' : Type} (hA : McqC.U.El c = A')
    (h : ((McqC.U.El c → McqC.U.P) → McqC.U.P) = ((A' → McqC.U.P) → McqC.U.P)) (Q : A' → McqC.U.P) (w : Bool) :
    cast h (fun R => McqC.all c R) Q w ↔ ∀ x, Q x w := by
  subst hA; rw [cast_eq]; exact Iff.rfl

theorem McqC_cast_ex_at {c : Code McqC.U.Base} {A' : Type} (hA : McqC.U.El c = A')
    (h : ((McqC.U.El c → McqC.U.P) → McqC.U.P) = ((A' → McqC.U.P) → McqC.U.P)) (Q : A' → McqC.U.P) (w : Bool) :
    cast h (fun R => McqC.ex c R) Q w ↔ ∃ x, Q x w := by
  subst hA; rw [cast_eq]; exact Iff.rfl

/-- A universal quantification is true at a world just when every instance is. -/
theorem McqC_evalAt_all {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : McqC.U.TEnv n)
    (env : McqC.U.Env Γ ρ) (w : Bool) :
    McqC.eval (Tm.all σ φ) ρ env w ↔ ∀ v : McqC.U.CatVal σ.1 ρ, McqC.eval φ ρ (env, v) w :=
  McqC_cast_all_at (Univ.El_code ρ σ.2) _ _ w

/-- An existential quantification is true at a world just when some instance is. -/
theorem McqC_evalAt_ex {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : McqC.U.TEnv n)
    (env : McqC.U.Env Γ ρ) (w : Bool) :
    McqC.eval (Tm.ex σ φ) ρ env w ↔ ∃ v : McqC.U.CatVal σ.1 ρ, McqC.eval φ ρ (env, v) w :=
  McqC_cast_ex_at (Univ.El_code ρ σ.2) _ _ w

/-- `⊥` is false at both worlds. -/
theorem McqC_bot_false {n : Nat} {Γ : Ctx n} (ρ : McqC.U.TEnv n) (env : McqC.U.Env Γ ρ) (w : Bool) :
    ¬ McqC.eval (botF : Fm Γ) ρ env w := fun h =>
  (McqC_evalAt_all (Γ := Γ) tyT (.var .here) ρ env w).mp h (fun _ => False)

/-- Nothing false at both worlds is identified with anything else. -/
theorem McqC_eqv_t_of_false {p q : Bool → Prop} (hq1 : ¬ q true) (hq2 : ¬ q false)
    (h : McqC.eqv .t .t p q true) : p = q := by
  rcases h.2 with e | ⟨_, s⟩
  · exact eq_of_heq e
  · exact ((McqC_S q).mp s).elim (fun h => absurd h hq1) (fun h => absurd h hq2)

/-! ## Booleanism -/

theorem McqC_evalInst {n : Nat} {Γ : Ctx n} {k : Nat} (P : PF k) (as : Fin k → Fm Γ) (ρ : McqC.U.TEnv n)
    (env : McqC.U.Env Γ ρ) (w : Bool) :
    McqC.eval (P.inst as) ρ env w ↔ P.evalP (fun i => McqC.eval (as i) ρ env w) := by
  induction P with
  | atom i => exact Iff.rfl
  | neg P ih => exact not_congr ih
  | imp P Q ihP ihQ => exact imp_congr ihP ihQ
  | conj P Q ihP ihQ => exact and_congr ihP ihQ
  | disj P Q ihP ihQ => exact or_congr ihP ihQ
  | iff P Q ihP ihQ => exact iff_congr ihP ihQ

theorem McqC_Bool : ∀ φ, BoolSch φ → McqC.Valid φ := by
  rintro _ ⟨k, P, Q, hT, rfl⟩ ρ env0
  refine McqC.holds_closeAll k _ ρ (fun env => ?_) env0
  have e : McqC.eval (P.inst (varsT k)) ρ env = McqC.eval (Q.inst (varsT k)) ρ env :=
    funext fun w => propext ((McqC_evalInst P _ ρ env w).trans ((hT _).trans (McqC_evalInst Q _ ρ env w).symm))
  exact (McqC.holds_eqv_t _ _ _ _).mpr ⟨rfl, Or.inl (heq_of_eq e)⟩

/-! ## The Identity Identity fails

At `x := ⊤`, `y := p₀`: `x ≡ y` is true at both worlds, but `∀F (F x → F y)` is false at both. -/

theorem McqC_tr_IdId : McqC.Holds IdId (fun i => i.elim0) () ↔ ∀ a (x y : univQ.El a),
    McqC.eqv .t .t (McqC.eqv a a x y) (fun w => ∀ G : univQ.El a → Bool → Prop, G x w → G y w) true := Iff.rfl

theorem McqC_not_IdId : ¬ McqC.Valid IdId := fun h => by
  have h0 := McqC_tr_IdId.mp ((McqC.valid_iff_tr _).mp h) .t (fun _ => True) p0Q
  have e := McqC_eqv_t_of_false (fun hq => (hq (fun p => p) trivial : p0Q true) |> Bool.noConfusion)
    (fun hq => (hq (fun p _ => p true) trivial : p0Q true) |> Bool.noConfusion) h0
  exact (cast (congrFun e true) ⟨rfl, Or.inr ⟨Or.inl trivial, Or.inr rfl⟩⟩ :
    ∀ G : univQ.El .t → Bool → Prop, G (fun _ => True) true → G p0Q true) (fun p => p) trivial |> Bool.noConfusion

/-! ## Identity across types, and identity of types -/

theorem McqC_Disjoint : McqC.Valid Disjoint := by
  intro ρ env
  refine (McqC.holds_tall _ _ _).mpr fun a => (McqC.holds_tall _ _ _).mpr fun b => ?_
  refine (McqC.holds_imp _ _ _ _).mpr fun hn => ?_
  refine (McqC.holds_all _ _ _ _).mpr fun x => (McqC.holds_all _ _ _ _).mpr fun y => ?_
  refine (McqC.holds_neg _ _ _).mpr fun hxy => ?_
  exact (McqC.holds_neg _ _ _).mp hn ((McqC.holds_teq _ _ _ _).mpr ((McqC.holds_eqv _ _ _ _ _ _).mp hxy).1)

theorem McqC_Slogan : McqC.Valid Slogan := by
  intro ρ env
  refine (McqC.holds_all _ _ _ _).mpr fun x => (McqC.holds_tall _ _ _).mpr fun b => ?_
  refine (McqC.holds_all _ _ _ _).mpr fun y => (McqC.holds_neg _ _ _).mpr fun hxy => ?_
  have h := ((McqC.holds_eqv _ _ _ _ _ _).mp hxy).1
  exact nomatch (show (Code.e : Code Empty) = .arr b .t from h)

theorem McqC_not_Twin : ¬ McqC.Valid Twin := fun h => by
  have h0 := (McqC.holds_all _ _ _ _).mp ((McqC.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  obtain ⟨b, hb⟩ := (McqC.holds_tex _ _ _).mp h0
  have hc := (McqC.holds_conj _ _ _ _).mp hb
  obtain ⟨_, hy⟩ := (McqC.holds_ex _ _ _ _).mp hc.2
  have e := ((McqC.holds_eqv _ _ _ _ _ _).mp hy).1
  exact (McqC.holds_neg _ _ _).mp hc.1 ((McqC.holds_teq _ _ _ _).mpr e)

theorem McqC_not_Hae : ¬ McqC.Valid Hae := fun h => by
  have h0 := (McqC.holds_all _ _ _ _).mp ((McqC.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  have e := ((McqC.holds_eqv _ _ _ _ _ _).mp h0).1
  exact Code.arr_ne_left (Code.e : Code Empty) .t e.symm

theorem McqC_Cantor : McqC.Valid Cantor := by
  intro ρ env
  refine (McqC.holds_tall _ _ _).mpr fun a => (McqC.holds_ex _ _ _ _).mpr ⟨fun _ _ => True, ?_⟩
  refine (McqC.holds_all _ _ _ _).mpr fun y => (McqC.holds_neg _ _ _).mpr fun h => ?_
  exact Code.arr_ne_left a .t ((McqC.holds_eqv _ _ _ _ _ _).mp h).1

theorem McqC_TopBot : McqC.Valid TopBot := by
  intro ρ env
  refine (McqC.holds_neg _ _ _).mpr fun h => ?_
  have e := McqC_eqv_t_of_false (McqC_bot_false ρ env true) (McqC_bot_false ρ env false)
    ((McqC.holds_eqv_t _ _ _ _).mp h)
  exact McqC_bot_false ρ env true (cast (congrFun ((Mcq_top _ _ ρ env).symm.trans e) true) trivial)

theorem McqC_Inj : McqC.Valid Inj := by
  intro ρ env
  refine (McqC.holds_tall _ _ _).mpr fun a => (McqC.holds_tall _ _ _).mpr fun b => ?_
  refine (McqC.holds_tall _ _ _).mpr fun c => (McqC.holds_tall _ _ _).mpr fun d => ?_
  refine (McqC.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (McqC.holds_teq _ _ _ _).mp h
  injection h' with hab hcd
  exact (McqC.holds_conj _ _ _ _).mpr ⟨(McqC.holds_teq _ _ _ _).mpr hab, (McqC.holds_teq _ _ _ _).mpr hcd⟩

theorem McqC_Recovery : McqC.Valid Recovery := by
  intro ρ env
  refine (McqC.holds_tall _ _ _).mpr fun a => (McqC.holds_tall _ _ _).mpr fun b => ?_
  refine (McqC.holds_tall _ _ _).mpr fun c => (McqC.holds_tall _ _ _).mpr fun d => ?_
  refine (McqC.holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := (McqC.holds_teq _ _ _ _).mp ((McqC.holds_conj _ _ _ _).mp h).1
  exact (McqC.holds_teq _ _ _ _).mpr (Code.arr.inj h').2

theorem McqC_ExtT : McqC.Valid ExtT := by
  intro ρ env
  refine (McqC.holds_tall _ _ _).mpr fun a => (McqC.holds_tall _ _ _).mpr fun b => ?_
  refine (McqC.holds_imp _ _ _ _).mpr fun h => (McqC.holds_teq _ _ _ _).mpr ?_
  have hs := ((McqC.holds_conj _ _ _ _).mp h).1
  have x0 := Classical.choice (Univ.El_nonempty (U := McqC.U) a)
  obtain ⟨_, hy⟩ := (McqC.holds_ex _ _ _ _).mp ((McqC.holds_all _ _ _ _).mp hs x0)
  exact ((McqC.holds_eqv _ _ _ _ _ _).mp hy).1

/-- `□(α ⊑ β)` requires `α ⊑ β` at one of the worlds, and identity across types is the same at both. -/
theorem McqC_IntT : McqC.Valid IntT := by
  intro ρ env
  refine (McqC.holds_tall _ _ _).mpr fun a => (McqC.holds_tall _ _ _).mpr fun b => ?_
  refine (McqC.holds_imp _ _ _ _).mpr fun h => (McqC.holds_teq _ _ _ _).mpr ?_
  have hs := (McqC_holds_box _ _ _).mp ((McqC.holds_conj _ _ _ _).mp h).1
  have x0 := Classical.choice (Univ.El_nonempty (U := McqC.U) a)
  have key : ∀ w, McqC.eval (subT : Fm (Ctx.nil.text.text)) (scons b (scons a ρ)) env w → a = b := fun w hw => by
    obtain ⟨y, hy⟩ := (McqC_evalAt_ex (n := 2) _ _ _ _ w).mp ((McqC_evalAt_all (n := 2) _ _ _ _ w).mp hw x0)
    exact (cast (congrFun (McqC.eval_eqv _ _ _ _ _ _) w) hy).1
  rcases hs with hw | hw
  · exact key true hw
  · exact key false hw

/-! ## Congruence and extensionality

Functions are identified only with themselves. Negation sends `⊤` and `p₀` to `⊥` and to the
proposition true only at the actual world, which are not identified; so Cong and WCong fail. -/

theorem McqC_tr_Cong : McqC.Holds Cong (fun i => i.elim0) () ↔
    ∀ (a b c d : Code Empty) (f : univQ.El a → univQ.El c) (g : univQ.El b → univQ.El d) x y,
      (McqC.eqv (.arr a c) (.arr b d) f g true ∧ McqC.eqv a b x y true) → McqC.eqv c d (f x) (g y) true := Iff.rfl

theorem McqC_tr_WCong : McqC.Holds WCong (fun i => i.elim0) () ↔
    ∀ (a b c d : Code Empty) (f : univQ.El a → univQ.El c) (g : univQ.El b → univQ.El d) x y,
      (McqC.teq a b true ∧ McqC.teq c d true) ∧ (McqC.eqv (.arr a c) (.arr b d) f g true ∧ McqC.eqv a b x y true) →
      McqC.eqv c d (f x) (g y) true := Iff.rfl

theorem McqC_tr_PCong : McqC.Holds PCong (fun i => i.elim0) () ↔
    ∀ (a c d : Code Empty) (f : univQ.El a → univQ.El c) (g : univQ.El a → univQ.El d) x,
      McqC.eqv (.arr a c) (.arr a d) f g true → McqC.eqv c d (f x) (g x) true := Iff.rfl

theorem McqC_tr_PExt : McqC.Holds PExt (fun i => i.elim0) () ↔
    ∀ (a c d : Code Empty) (f : univQ.El a → univQ.El c) (g : univQ.El a → univQ.El d),
      (∀ x, McqC.eqv c d (f x) (g x) true) → McqC.eqv (.arr a c) (.arr a d) f g true := Iff.rfl

theorem McqC_top_p0 : McqC.eqv .t .t (fun _ => True) p0Q true := ⟨rfl, Or.inr ⟨Or.inl trivial, Or.inr rfl⟩⟩

theorem McqC_neg_ne : ¬ McqC.eqv .t .t (fun _ => ¬ True) (fun w => ¬ p0Q w) true := fun h => by
  rcases h.2 with e | ⟨s, _⟩
  · exact (cast (congrFun (eq_of_heq e) true).symm (fun e' : true = false => Bool.noConfusion e')) trivial
  · rcases (McqC_S _).mp s with s | s
    · exact s trivial
    · exact s trivial

theorem McqC_not_Cong : ¬ McqC.Valid Cong := fun h =>
  McqC_neg_ne (McqC_tr_Cong.mp ((McqC.valid_iff_tr _).mp h) .t .t .t .t
    (fun (p : Bool → Prop) (w : Bool) => ¬ p w) (fun (p : Bool → Prop) (w : Bool) => ¬ p w)
    (fun _ => True) p0Q ⟨⟨rfl, Or.inl HEq.rfl⟩, McqC_top_p0⟩)

theorem McqC_not_WCong : ¬ McqC.Valid WCong := fun h =>
  McqC_neg_ne (McqC_tr_WCong.mp ((McqC.valid_iff_tr _).mp h) .t .t .t .t
    (fun (p : Bool → Prop) (w : Bool) => ¬ p w) (fun (p : Bool → Prop) (w : Bool) => ¬ p w)
    (fun _ => True) p0Q ⟨⟨rfl, rfl⟩, ⟨rfl, Or.inl HEq.rfl⟩, McqC_top_p0⟩)

theorem McqC_PCong : McqC.Valid PCong :=
  (McqC.valid_iff_tr _).mpr <| McqC_tr_PCong.mpr fun a c d f g x ⟨e, h⟩ => by
    have ecd := (Code.arr.inj e).2
    subst ecd
    rcases h with h | ⟨s, _⟩
    · have hf : f = g := eq_of_heq h
      subst hf
      exact ⟨rfl, Or.inl HEq.rfl⟩
    · exact (s : False).elim

theorem McqC_not_PExt : ¬ McqC.Valid PExt := fun h => by
  have h0 := McqC_tr_PExt.mp ((McqC.valid_iff_tr _).mp h) .e .t .t (fun (_ : Unit) (_ : Bool) => True)
    (fun (_ : Unit) => p0Q) (fun _ => McqC_top_p0)
  rcases h0.2 with e | ⟨s, _⟩
  · have e' := congrFun (congrFun (eq_of_heq e) ()) true
    exact Bool.noConfusion (cast e' trivial : true = false)
  · exact (s : False).elim

/-! ## The polymorphic Leibniz laws fail

The polymorphic predicate `λγ.λz:γ. ∃_{γ→t} F (F z ∧ F ≡_{γ→t, t→t} λp.p)` is true of `⊤` and
false of `p₀` at the actual world (at type `t`, the only `F` identified with `λp.p` is `λp.p`
itself); and `⊤ ≡ p₀`, at the same type. -/

def McqC_PredId : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (ex tv0.pred (conj (.app (.var .here) (.var (.there .here)))
    (eqv tv0.pred (Ty.arrow tyT tyT) (.var .here) (.lam tyT (.var .here))))))

theorem McqC_tr_LLPoly : McqC.Holds (LLPoly McqC_PredId) (fun i => i.elim0) () ↔
    ∀ a b (x : univQ.El a) (y : univQ.El b), McqC.eqv a b x y true →
    (∃ F : univQ.El a → Bool → Prop, F x true ∧ McqC.eqv (.arr a .t) (.arr .t .t) F (fun p => p) true) →
    (∃ F : univQ.El b → Bool → Prop, F y true ∧ McqC.eqv (.arr b .t) (.arr .t .t) F (fun p => p) true) := Iff.rfl

theorem McqC_not_LLPoly : ¬ McqC.Valid (LLPoly McqC_PredId) := fun h => by
  obtain ⟨F, hF, _, e | ⟨s, _⟩⟩ := McqC_tr_LLPoly.mp ((McqC.valid_iff_tr _).mp h) .t .t (fun _ => True)
    p0Q McqC_top_p0 ⟨fun p => p, trivial, ⟨rfl, Or.inl HEq.rfl⟩⟩
  · have hF' : F = fun p => p := eq_of_heq e
    subst hF'
    exact Bool.noConfusion (hF : true = false)
  · exact (s : False).elim

theorem McqC_tr_Bridge : McqC.Holds (Bridge McqC_PredId) (fun i => i.elim0) () ↔
    ∀ a b (x : univQ.El a) (y : univQ.El b), McqC.eqv a b x y true ∧ McqC.teq a b true →
    (∃ F : univQ.El a → Bool → Prop, F x true ∧ McqC.eqv (.arr a .t) (.arr .t .t) F (fun p => p) true) →
    (∃ F : univQ.El b → Bool → Prop, F y true ∧ McqC.eqv (.arr b .t) (.arr .t .t) F (fun p => p) true) := Iff.rfl

theorem McqC_not_Bridge : ¬ McqC.Valid (Bridge McqC_PredId) := fun h => by
  obtain ⟨F, hF, _, e | ⟨s, _⟩⟩ := McqC_tr_Bridge.mp ((McqC.valid_iff_tr _).mp h) .t .t (fun _ => True)
    p0Q ⟨McqC_top_p0, rfl⟩ ⟨fun p => p, trivial, ⟨rfl, Or.inl HEq.rfl⟩⟩
  · have hF' : F = fun p => p := eq_of_heq e
    subst hF'
    exact Bool.noConfusion (hF : true = false)
  · exact (s : False).elim

/-! ## The Barcan formulas

`□𝔸α φ` always holds, since `𝔸α φ` is true at the other world. -/

theorem McqC_TBF : ∀ χ, TBFSch χ → McqC.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  exact (McqC.holds_imp _ _ _ _).mpr fun _ => (McqC_holds_box _ _ _).mpr (Or.inr trivial)

theorem McqC_CBF : McqC.Valid CBF := by
  intro ρ env
  refine (McqC.holds_tall _ _ _).mpr fun a => (McqC.holds_all _ _ _ _).mpr fun F => ?_
  refine (McqC.holds_imp _ _ _ _).mpr fun h => (McqC.holds_all _ _ _ _).mpr fun x => ?_
  refine (McqC_holds_box _ _ _).mpr ?_
  rcases (McqC_holds_box _ _ _).mp h with hw | hw
  · exact Or.inl ((McqC_evalAt_all (n := 1) _ _ _ _ true).mp hw x)
  · exact Or.inr ((McqC_evalAt_all (n := 1) _ _ _ _ false).mp hw x)

/-- BF fails: with `F x` true at the actual world just when `x` is, and at the other world just when
`x` is not true at the actual world, each `F x` is true at some world, but `∀x F x` at neither. -/
theorem McqC_not_BF : ¬ McqC.Valid BF := fun h => by
  have h0 := (McqC.holds_all _ _ _ _).mp ((McqC.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t)
    (fun (x : Bool → Prop) (w : Bool) => cond w (x true) (¬ x true))
  have h1 := (McqC.holds_imp _ _ _ _).mp h0 ((McqC.holds_all _ _ _ _).mpr fun x =>
    (McqC_holds_box _ _ _).mpr (Classical.em (x true)))
  rcases (McqC_holds_box _ _ _).mp h1 with hw | hw
  · exact ((McqC_evalAt_all (n := 1) _ _ _ _ true).mp hw (fun _ => False) : False)
  · exact ((McqC_evalAt_all (n := 1) _ _ _ _ false).mp hw (fun _ => True) : ¬ True) trivial

/-! ## Classicism fails

PI proves `((p ≡ q) ∧ p ∧ ¬q) ↔ ⊥` (by Truth); but at `p := ⊤`, `q := p₀` the left side is the
proposition true only at the actual world, which is not identified with `⊥`. -/

section
open Derive

def McqC_v4 {n : Nat} {Γ : Ctx n} (a b c d : Fm Γ) : Fin 4 → Fm Γ :=
  fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d

abbrev McqC_ClsF : Fm Γpq := conj (eqv tyT tyT pV qV) (conj pV qV.neg)

set_option maxHeartbeats 8000000 in
theorem McqC_cls_PIP : PIP Γpq (iff McqC_ClsF botF) := by
  have hT : Ent (fun χ => χ = LLEqv) Γpq [] ((eqv tyT tyT pV qV).imp (pV.imp qV)) :=
    ((Ent.closed (Γ := Γpq) (Hs := []) (d_Truth (S := fun χ => χ = LLEqv) rfl)).inst pV).inst qV
  have ht : Ent (fun χ => χ = LLEqv) Γpq []
      (((eqv tyT tyT pV qV).imp (pV.imp qV)).imp ((botF : Fm Γpq).neg.imp (iff McqC_ClsF botF))) :=
    Ent.taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2)))
        (.imp (.neg (.atom 3)) (.iff (.conj (.atom 0) (.conj (.atom 1) (.neg (.atom 2)))) (.atom 3))))
      (McqC_v4 (eqv tyT tyT pV qV) pV qV botF)
      (fun _ h nb => ⟨fun ⟨a, p, nq⟩ => (nq (h a p)).elim, fun b => (nb b).elim⟩)
  exact Ent.toProv (Ent.mp2 ht hT Ent.top)

theorem McqC_cls : ClassSch (closeCtx Γpq (eqv tyT tyT McqC_ClsF botF)) :=
  Or.inl ⟨0, Γpq, McqC_ClsF, botF, McqC_cls_PIP, rfl⟩

end

theorem McqC_not_Class : ¬ ∀ χ, ClassSch χ → McqC.Valid χ := fun h => by
  have h0 := (McqC.holds_all _ _ _ _).mp ((McqC.holds_all _ _ _ _).mp (h _ McqC_cls (fun i => i.elim0) ())
    (fun _ => True)) p0Q
  have hL : McqC.Holds McqC_ClsF (fun i => i.elim0) (((), fun _ => True), p0Q) :=
    (McqC.holds_conj _ _ _ _).mpr ⟨(McqC.holds_eqv_t _ _ _ _).mpr McqC_top_p0,
      (McqC.holds_conj _ _ _ _).mpr ⟨trivial, (McqC.holds_neg _ _ _).mpr fun e => Bool.noConfusion e⟩⟩
  have e := McqC_eqv_t_of_false (McqC_bot_false (Γ := Γpq) _ _ true) (McqC_bot_false (Γ := Γpq) _ _ false)
    ((McqC.holds_eqv_t _ _ _ _).mp h0)
  exact McqC_bot_false (Γ := Γpq) _ _ true (cast (congrFun e true) hL)

end Al
end PIF
