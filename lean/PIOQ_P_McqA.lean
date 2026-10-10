import PIBF

/-!
# Open questions: the profile of `𝔐_cq,A`

`𝔐_cq,A` (`lean/PIBarcanModels.lean`, `McqA`): propositions are sets of two worlds (the actual
world is `true`); the propositions true at the actual world, together with the proposition `p₀`
true only at the other world `false`, are identified with each other, and nothing else is
identified with anything but itself. Identity of items and of types is the same at both worlds;
the connectives and item quantifiers act world by world; at the other world type-universal claims
are false and type-existential ones true.

So the class of `⊤` is the set of non-empty propositions, and `□φ` (that is, `φ ≡ ⊤`) holds just
when `φ` is true at some world.
-/
set_option autoImplicit false

namespace PIF
namespace Al
open Tm

/-! ## Basic facts -/

/-- A proposition is in the class of `⊤` just when it is true at some world. -/
theorem McqA_Scq_t (p : Bool → Prop) : Scq .t p ↔ (p true ∨ p false) := by
  constructor
  · rintro (h | e)
    · exact Or.inl h
    · subst e; exact Or.inr rfl
  · intro h
    by_cases h1 : p true
    · exact Or.inl h1
    · refine Or.inr (funext fun w => ?_)
      cases w
      · exact propext ⟨fun _ => rfl, fun _ => h.resolve_left h1⟩
      · exact propext ⟨fun h' => absurd h' h1, fun e => Bool.noConfusion e⟩

/-- Identity of propositions in `𝔐_cq,A`, at any world. -/
theorem McqA_eqv_t (p q : Bool → Prop) (w : Bool) :
    McqA.eqv .t .t p q w ↔ (p = q ∨ ((p true ∨ p false) ∧ (q true ∨ q false))) := by
  constructor
  · rintro ⟨_, e | ⟨s1, s2⟩⟩
    · exact Or.inl (eq_of_heq e)
    · exact Or.inr ⟨(McqA_Scq_t p).mp s1, (McqA_Scq_t q).mp s2⟩
  · rintro (e | ⟨h1, h2⟩)
    · exact ⟨rfl, Or.inl (heq_of_eq e)⟩
    · exact ⟨rfl, Or.inr ⟨(McqA_Scq_t p).mpr h1, (McqA_Scq_t q).mpr h2⟩⟩

/-- `p ≡ ⊤` just when `p` is true at some world. -/
theorem McqA_box_t (p : Bool → Prop) (w : Bool) :
    McqA.eqv .t .t p (fun v => ¬ ∀ q : Bool → Prop, q v) w ↔ (p true ∨ p false) := by
  constructor
  · intro h
    rcases (McqA_eqv_t _ _ _).mp h with e | ⟨h1, _⟩
    · exact Or.inl (cast (congrFun e true).symm (fun h' => h' (fun _ => False)))
    · exact h1
  · intro h
    exact (McqA_eqv_t _ _ _).mpr (Or.inr ⟨h, Or.inl (fun h' => h' (fun _ => False))⟩)

/-- `□φ` holds just when `φ` is true at some world. -/
theorem McqA_holds_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : McqA.U.TEnv n) (env : McqA.U.Env Γ ρ) :
    McqA.Holds (boxF φ) ρ env ↔ (McqA.eval φ ρ env true ∨ McqA.eval φ ρ env false) := by
  refine (McqA.holds_eqv_t _ _ _ _).trans ?_
  have e := Mcq_top (fun _ => False) (fun _ => True) ρ env
  refine (McqA_eqv_t _ _ true).trans ⟨fun h => ?_, fun h => Or.inr ⟨h, ?_⟩⟩
  · rcases h with e' | ⟨h, _⟩
    · exact Or.inl (cast (congrFun (e'.trans e) true).symm trivial)
    · exact h
  · exact Or.inl (cast (congrFun e true).symm trivial)

/-- The truth of a closed formula at the actual world. -/
theorem McqA_valid_iff (φ : Fm Ctx.nil) : McqA.Valid φ ↔ McqA.Holds φ (fun i => i.elim0) () := McqA.valid_iff_tr φ

/-! ## Identity across types, and identity of types -/

theorem McqA_tr_Disjoint : McqA.Holds Disjoint (fun i => i.elim0) () ↔
    ∀ a b : Code Empty, ¬ McqA.teq a b true → ∀ (x : McqA.U.El a) (y : McqA.U.El b), ¬ McqA.eqv a b x y true :=
  Iff.rfl

theorem McqA_Disjoint : McqA.Valid Disjoint :=
  (McqA_valid_iff _).mpr <| McqA_tr_Disjoint.mpr fun _ _ hn _ _ h => hn h.1

theorem McqA_tr_Slogan : McqA.Holds Slogan (fun i => i.elim0) () ↔
    ∀ (x : Unit) (b : Code Empty) (y : McqA.U.El b → Bool → Prop), ¬ McqA.eqv .e (.arr b .t) x y true := Iff.rfl

theorem McqA_Slogan : McqA.Valid Slogan :=
  (McqA_valid_iff _).mpr <| McqA_tr_Slogan.mpr fun _ _ _ h => nomatch h.1

theorem McqA_tr_Cantor : McqA.Holds Cantor (fun i => i.elim0) () ↔ ∀ a : Code Empty, ∃ G : McqA.U.El a → Bool → Prop,
    ∀ y : McqA.U.El a, ¬ McqA.eqv (.arr a .t) a G y true := Iff.rfl

theorem McqA_Cantor : McqA.Valid Cantor :=
  (McqA_valid_iff _).mpr <| McqA_tr_Cantor.mpr fun a =>
    ⟨fun _ _ => True, fun _ h => Code.arr_ne_left a .t h.1⟩

theorem McqA_tr_Twin : McqA.Holds Twin (fun i => i.elim0) () ↔ ∀ a (x : McqA.U.El a), ∃ b, ¬ McqA.teq a b true ∧
    ∃ y : McqA.U.El b, McqA.eqv a b x y true := Iff.rfl

theorem McqA_not_Twin : ¬ McqA.Valid Twin := fun h => by
  obtain ⟨_, hn, _, hy⟩ := McqA_tr_Twin.mp ((McqA_valid_iff _).mp h) .e ()
  exact hn hy.1

theorem McqA_tr_Inj : McqA.Holds Inj (fun i => i.elim0) () ↔ ∀ a b c d : Code Empty,
    McqA.teq (.arr a c) (.arr b d) true → McqA.teq a b true ∧ McqA.teq c d true := Iff.rfl

theorem McqA_Inj : McqA.Valid Inj :=
  (McqA_valid_iff _).mpr <| McqA_tr_Inj.mpr fun a b c d h => by
    have h' : Code.arr a c = Code.arr b d := h
    exact Code.arr.inj h'

theorem McqA_tr_Recovery : McqA.Holds Recovery (fun i => i.elim0) () ↔ ∀ a b c d : Code Empty,
    McqA.teq (.arr a c) (.arr b d) true ∧ McqA.teq a b true → McqA.teq c d true := Iff.rfl

theorem McqA_Recovery : McqA.Valid Recovery :=
  (McqA_valid_iff _).mpr <| McqA_tr_Recovery.mpr fun a b c d ⟨h, _⟩ => by
    have h' : Code.arr a c = Code.arr b d := h
    exact (Code.arr.inj h').2

theorem McqA_tr_Hae : McqA.Holds Hae (fun i => i.elim0) () ↔
    ∀ a (x : McqA.U.El a), McqA.eqv a (.arr a .t) x (fun y => McqA.eqv a a y x) true := Iff.rfl

theorem McqA_not_Hae : ¬ McqA.Valid Hae := fun h =>
  Code.arr_ne_left (Code.e : Code Empty) .t (McqA_tr_Hae.mp ((McqA_valid_iff _).mp h) .e ()).1.symm

theorem McqA_tr_ExtT : McqA.Holds ExtT (fun i => i.elim0) () ↔ ∀ a b : Code Empty,
    (∀ x : McqA.U.El a, ∃ y : McqA.U.El b, McqA.eqv a b x y true) ∧
    (∀ y : McqA.U.El b, ∃ x : McqA.U.El a, McqA.eqv a b x y true) → McqA.teq a b true := Iff.rfl

theorem McqA_ExtT : McqA.Valid ExtT :=
  (McqA_valid_iff _).mpr <| McqA_tr_ExtT.mpr fun a _ ⟨h, _⟩ => by
    have x0 := Classical.choice (Univ.El_nonempty (U := McqA.U) a)
    obtain ⟨_, hy⟩ := h x0
    exact hy.1

theorem McqA_tr_IntT : McqA.Holds IntT (fun i => i.elim0) () ↔ ∀ a b : Code Empty,
    McqA.eqv .t .t (fun w => ∀ x : McqA.U.El a, ∃ y : McqA.U.El b, McqA.eqv a b x y w)
      (fun v => ¬ ∀ q : Bool → Prop, q v) true ∧
    McqA.eqv .t .t (fun w => ∀ y : McqA.U.El b, ∃ x : McqA.U.El a, McqA.eqv a b x y w)
      (fun v => ¬ ∀ q : Bool → Prop, q v) true → McqA.teq a b true := Iff.rfl

theorem McqA_IntT : McqA.Valid IntT :=
  (McqA_valid_iff _).mpr <| McqA_tr_IntT.mpr fun a _ ⟨h, _⟩ => by
    have x0 := Classical.choice (Univ.El_nonempty (U := McqA.U) a)
    rcases (McqA_box_t _ _).mp h with h1 | h1
    · obtain ⟨_, hy⟩ := h1 x0
      exact hy.1
    · obtain ⟨_, hy⟩ := h1 x0
      exact hy.1

theorem McqA_tr_TopBot : McqA.Holds TopBot (fun i => i.elim0) () ↔
    ¬ McqA.eqv .t .t (fun v => ¬ ∀ q : Bool → Prop, q v) (fun v => ∀ q : Bool → Prop, q v) true := Iff.rfl

theorem McqA_TopBot : McqA.Valid TopBot :=
  (McqA_valid_iff _).mpr <| McqA_tr_TopBot.mpr fun h => by
    rcases (McqA_eqv_t _ _ _).mp h with e | ⟨_, hb | hb⟩
    · exact (fun h' => h' (fun _ => False)) (cast (congrFun e true) (fun h' => h' (fun _ => False)))
    · exact hb (fun _ => False)
    · exact hb (fun _ => False)

/-! ## Congruence and extensionality

`⊤` and `p₀` are identified, but negation sends them to `⊥` and to the proposition true only at
the actual world, which are not identified; and functions are identified only with themselves. -/

theorem McqA_tr_Cong : McqA.Holds Cong (fun i => i.elim0) () ↔ ∀ (a b c d : Code Empty)
    (f : McqA.U.El a → McqA.U.El c) (g : McqA.U.El b → McqA.U.El d) x y,
    McqA.eqv (.arr a c) (.arr b d) f g true ∧ McqA.eqv a b x y true → McqA.eqv c d (f x) (g y) true := Iff.rfl

theorem McqA_tr_WCong : McqA.Holds WCong (fun i => i.elim0) () ↔ ∀ (a b c d : Code Empty)
    (f : McqA.U.El a → McqA.U.El c) (g : McqA.U.El b → McqA.U.El d) x y,
    (McqA.teq a b true ∧ McqA.teq c d true) ∧ (McqA.eqv (.arr a c) (.arr b d) f g true ∧ McqA.eqv a b x y true) →
    McqA.eqv c d (f x) (g y) true := Iff.rfl

theorem McqA_tr_PCong : McqA.Holds PCong (fun i => i.elim0) () ↔ ∀ (a c d : Code Empty)
    (f : McqA.U.El a → McqA.U.El c) (g : McqA.U.El a → McqA.U.El d) x,
    McqA.eqv (.arr a c) (.arr a d) f g true → McqA.eqv c d (f x) (g x) true := Iff.rfl

theorem McqA_tr_PExt : McqA.Holds PExt (fun i => i.elim0) () ↔ ∀ (a c d : Code Empty)
    (f : McqA.U.El a → McqA.U.El c) (g : McqA.U.El a → McqA.U.El d),
    (∀ x, McqA.eqv c d (f x) (g x) true) → McqA.eqv (.arr a c) (.arr a d) f g true := Iff.rfl

/-- `⊤` and `p₀` are identified. -/
theorem McqA_top_p0 (w : Bool) : McqA.eqv .t .t (fun _ => True) p0Q w := ⟨rfl, Or.inr ⟨Or.inl trivial, Or.inr rfl⟩⟩

/-- Negation sends `⊤` and `p₀` to propositions that are not identified. -/
theorem McqA_neg_ne : ¬ McqA.eqv .t .t (fun _ => ¬ True) (fun w => ¬ p0Q w) true := fun h => by
  rcases (McqA_eqv_t _ _ _).mp h with e | ⟨h1, _⟩
  · exact (cast (congrFun e true).symm (fun e' : true = false => Bool.noConfusion e')) trivial
  · rcases h1 with h1 | h1
    · exact h1 trivial
    · exact h1 trivial

theorem McqA_not_Cong : ¬ McqA.Valid Cong := fun h =>
  McqA_neg_ne (McqA_tr_Cong.mp ((McqA_valid_iff _).mp h) .t .t .t .t
    (fun (p : Bool → Prop) (w : Bool) => ¬ p w) (fun (p : Bool → Prop) (w : Bool) => ¬ p w)
    (fun _ => True) p0Q ⟨⟨rfl, Or.inl HEq.rfl⟩, McqA_top_p0 true⟩)

theorem McqA_not_WCong : ¬ McqA.Valid WCong := fun h =>
  McqA_neg_ne (McqA_tr_WCong.mp ((McqA_valid_iff _).mp h) .t .t .t .t
    (fun (p : Bool → Prop) (w : Bool) => ¬ p w) (fun (p : Bool → Prop) (w : Bool) => ¬ p w)
    (fun _ => True) p0Q ⟨⟨rfl, rfl⟩, ⟨rfl, Or.inl HEq.rfl⟩, McqA_top_p0 true⟩)

theorem McqA_PCong : McqA.Valid PCong :=
  (McqA_valid_iff _).mpr <| McqA_tr_PCong.mpr fun a c d f g x ⟨e, h⟩ => by
    have e' : Code.arr a c = Code.arr a d := e
    have ecd := (Code.arr.inj e').2
    subst ecd
    rcases h with h | ⟨s, _⟩
    · have hf : f = g := eq_of_heq h
      subst hf
      exact ⟨rfl, Or.inl HEq.rfl⟩
    · exact (s : False).elim

theorem McqA_not_PExt : ¬ McqA.Valid PExt := fun h => by
  have h0 := McqA_tr_PExt.mp ((McqA_valid_iff _).mp h) .e .t .t (fun (_ : Unit) (_ : Bool) => True)
    (fun (_ : Unit) => p0Q) (fun _ => McqA_top_p0 true)
  rcases h0.2 with e | ⟨s, _⟩
  · have e' := congrFun (congrFun (eq_of_heq e) ()) true
    exact Bool.noConfusion (cast e' trivial : true = false)
  · exact (s : False).elim

/-! ## Booleanism, the Identity Identity, Classicism -/

theorem McqA_evalInst {n : Nat} {Γ : Ctx n} {k : Nat} (P : PF k) (as : Fin k → Fm Γ) (ρ : McqA.U.TEnv n)
    (env : McqA.U.Env Γ ρ) (w : Bool) :
    McqA.eval (P.inst as) ρ env w ↔ P.evalP (fun i => McqA.eval (as i) ρ env w) := by
  induction P with
  | atom i => exact Iff.rfl
  | neg P ih => exact not_congr ih
  | imp P Q ihP ihQ => exact imp_congr ihP ihQ
  | conj P Q ihP ihQ => exact and_congr ihP ihQ
  | disj P Q ihP ihQ => exact or_congr ihP ihQ
  | iff P Q ihP ihQ => exact iff_congr ihP ihQ

theorem McqA_Bool : ∀ φ, BoolSch φ → McqA.Valid φ := by
  rintro _ ⟨k, P, Q, hT, rfl⟩ ρ env0
  refine McqA.holds_closeAll k _ ρ (fun env => ?_) env0
  have e : McqA.eval (P.inst (varsT k)) ρ env = McqA.eval (Q.inst (varsT k)) ρ env :=
    funext fun w => propext ((McqA_evalInst P _ ρ env w).trans ((hT _).trans (McqA_evalInst Q _ ρ env w).symm))
  exact (McqA.holds_eqv_t _ _ _ _).mpr ⟨rfl, Or.inl (heq_of_eq e)⟩

theorem McqA_tr_IdId : McqA.Holds IdId (fun i => i.elim0) () ↔ ∀ a (x y : McqA.U.El a), McqA.eqv .t .t (McqA.eqv a a x y)
    (fun w => ∀ G : McqA.U.El a → Bool → Prop, G x w → G y w) true := Iff.rfl

theorem McqA_not_IdId : ¬ McqA.Valid IdId := fun h => by
  have h0 := McqA_tr_IdId.mp ((McqA_valid_iff _).mp h) .t (fun _ => True) p0Q
  have hR : ∀ w, ¬ ∀ G : (Bool → Prop) → Bool → Prop, G (fun _ => True) w → G p0Q w := fun w hG => by
    have e : p0Q = fun _ => True := hG (fun p _ => p = fun _ => True) rfl
    exact Bool.noConfusion (cast (congrFun e true).symm trivial : true = false)
  rcases (McqA_eqv_t _ _ _).mp h0 with e | ⟨_, h1 | h1⟩
  · exact hR true (cast (congrFun e true) (McqA_top_p0 true))
  · exact hR true h1
  · exact hR false h1

theorem McqA_not_Class : ¬ ∀ χ, ClassSch χ → McqA.Valid χ := fun h =>
  McqA_not_IdId (McqA.soundness (Mcq_model _ _) h (d_IdId_of_Class (S := ClassSch) fun _ hc => hc))

/-! ## The Barcan formulas

`□` is "true at some world", so the converse Barcan formulas hold and the Barcan formula fails. -/

theorem McqA_TCBF : ∀ χ, TCBFSch χ → McqA.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (McqA.holds_imp _ _ _ _).mpr fun h => ?_
  refine (McqA.holds_tall _ _ _).mpr fun a => (McqA_holds_box _ _ _).mpr (Or.inl ?_)
  rcases (McqA_holds_box _ _ _).mp h with h1 | h1
  · exact (McqA.holds_tall φ ρ env).mp h1 a
  · exact (h1 : False).elim

theorem McqA_tr_BF : McqA.Holds BF (fun i => i.elim0) () ↔ ∀ a (G : McqA.U.El a → Bool → Prop),
    (∀ x, McqA.eqv .t .t (G x) (fun v => ¬ ∀ q : Bool → Prop, q v) true) →
    McqA.eqv .t .t (fun w => ∀ x, G x w) (fun v => ¬ ∀ q : Bool → Prop, q v) true := Iff.rfl

theorem McqA_tr_CBF : McqA.Holds CBF (fun i => i.elim0) () ↔ ∀ a (G : McqA.U.El a → Bool → Prop),
    McqA.eqv .t .t (fun w => ∀ x, G x w) (fun v => ¬ ∀ q : Bool → Prop, q v) true →
    ∀ x, McqA.eqv .t .t (G x) (fun v => ¬ ∀ q : Bool → Prop, q v) true := Iff.rfl

theorem McqA_CBF : McqA.Valid CBF :=
  (McqA_valid_iff _).mpr <| McqA_tr_CBF.mpr fun _ G h x => by
    refine (McqA_box_t _ _).mpr ?_
    rcases (McqA_box_t _ _).mp h with h1 | h1
    · exact Or.inl (h1 x)
    · exact Or.inr (h1 x)

/-- The predicate of propositions true at the other world when false at the actual one, and
conversely: each of its values is true at some world, but nothing has it at both worlds. -/
theorem McqA_not_BF : ¬ McqA.Valid BF := fun h => by
  have h0 := McqA_tr_BF.mp ((McqA_valid_iff _).mp h) .t (fun (x : Bool → Prop) (w : Bool) => cond w (¬ x true) (x true))
    (fun x => (McqA_box_t _ _).mpr (Classical.em (x true)).symm)
  rcases (McqA_box_t _ _).mp h0 with h1 | h1
  · exact (h1 (fun _ => True) : ¬ True) trivial
  · exact (h1 (fun _ => False) : False)

/-! ## The polymorphic Leibniz law fails

The polymorphic predicate `λγ.λz:γ. ∃_{γ→t} F (F z ∧ F ≡_{γ→t, t→t} λp.p)` is true of `⊤` and
false of `p₀` (at type `t`, the only `F` identified with `λp.p` is `λp.p` itself). -/

def McqA_PredId : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (ex tv0.pred (conj (.app (.var .here) (.var (.there .here)))
    (eqv tv0.pred (Ty.arrow tyT tyT) (.var .here) (.lam tyT (.var .here))))))

theorem McqA_tr_LLPoly : McqA.Holds (LLPoly McqA_PredId) (fun i => i.elim0) () ↔
    ∀ a b (x : McqA.U.El a) (y : McqA.U.El b), McqA.eqv a b x y true →
    (∃ F : McqA.U.El a → Bool → Prop, F x true ∧ McqA.eqv (.arr a .t) (.arr .t .t) F (fun p => p) true) →
    (∃ F : McqA.U.El b → Bool → Prop, F y true ∧ McqA.eqv (.arr b .t) (.arr .t .t) F (fun p => p) true) := Iff.rfl

theorem McqA_not_LLPoly : ¬ McqA.Valid (LLPoly McqA_PredId) := fun h => by
  obtain ⟨F, hF, _, e | ⟨s, _⟩⟩ := McqA_tr_LLPoly.mp ((McqA_valid_iff _).mp h) .t .t (fun _ => True)
    p0Q (McqA_top_p0 true) ⟨fun p => p, trivial, ⟨rfl, Or.inl HEq.rfl⟩⟩
  · have hF' : F = fun p => p := eq_of_heq e
    subst hF'
    exact Bool.noConfusion (hF : true = false)
  · exact (s : False).elim

theorem McqA_tr_Bridge : McqA.Holds (Bridge McqA_PredId) (fun i => i.elim0) () ↔
    ∀ a b (x : McqA.U.El a) (y : McqA.U.El b), McqA.eqv a b x y true ∧ McqA.teq a b true →
    (∃ F : McqA.U.El a → Bool → Prop, F x true ∧ McqA.eqv (.arr a .t) (.arr .t .t) F (fun p => p) true) →
    (∃ F : McqA.U.El b → Bool → Prop, F y true ∧ McqA.eqv (.arr b .t) (.arr .t .t) F (fun p => p) true) := Iff.rfl

/-- The same predicate refutes LL≡/≈: `⊤` and `p₀` are items of the same type. -/
theorem McqA_not_Bridge : ¬ McqA.Valid (Bridge McqA_PredId) := fun h => by
  obtain ⟨F, hF, _, e | ⟨s, _⟩⟩ := McqA_tr_Bridge.mp ((McqA_valid_iff _).mp h) .t .t (fun _ => True)
    p0Q ⟨McqA_top_p0 true, rfl⟩ ⟨fun p => p, trivial, ⟨rfl, Or.inl HEq.rfl⟩⟩
  · have hF' : F = fun p => p := eq_of_heq e
    subst hF'
    exact Bool.noConfusion (hF : true = false)
  · exact (s : False).elim

end Al
end PIF
