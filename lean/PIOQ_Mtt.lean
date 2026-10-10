import PIBF
set_option autoImplicit false

namespace PIF
namespace Wd

/-!
# More about `𝔐_tt`

In `𝔐_tt` (two worlds, the actual one `true`), `⊤` is identified with the proposition `Y` true
only at the non-actual world `false`, and nothing else is identified with anything but itself.
The class of `⊤` is `{⊤, Y}`: exactly the propositions true at the non-actual world. So `□φ`
(that is, `φ ≡ ⊤`) is true just when `φ` is true at the non-actual world. Identity of items and
of types is the same at both worlds, so the modal principles about identity, and the Barcan
formulas, all hold; the connectives act world by world, so Booleanism holds.
-/

/-- A proposition is in the class of `⊤` just when it is true at the non-actual world. -/
theorem Mtt_St_t (p : Bool → Prop) : St .t p ↔ p false := by
  constructor
  · rintro (e | e)
    · subst e; trivial
    · subst e; rfl
  · intro h
    by_cases h1 : p true
    · refine Or.inl (funext fun w => ?_)
      cases w
      · exact propext ⟨fun _ => trivial, fun _ => h⟩
      · exact propext ⟨fun _ => trivial, fun _ => h1⟩
    · refine Or.inr (funext fun w => ?_)
      cases w
      · exact propext ⟨fun _ => rfl, fun _ => h⟩
      · exact propext ⟨fun h' => absurd h' h1, fun e => Bool.noConfusion e⟩

/-- Identity of propositions in `𝔐_tt`, at any world. -/
theorem Mtt_eqv_t (p q : Bool → Prop) (w : Bool) :
    MttF.eqv .t .t p q w ↔ (p = q ∨ (p false ∧ q false)) := by
  constructor
  · rintro ⟨_, e | ⟨s1, s2⟩⟩
    · exact Or.inl (eq_of_heq e)
    · exact Or.inr ⟨(Mtt_St_t p).mp s1, (Mtt_St_t q).mp s2⟩
  · rintro (e | ⟨h1, h2⟩)
    · exact ⟨rfl, Or.inl (heq_of_eq e)⟩
    · exact ⟨rfl, Or.inr ⟨(Mtt_St_t p).mpr h1, (Mtt_St_t q).mpr h2⟩⟩

/-- Identified propositions agree at the non-actual world. -/
theorem Mtt_eqv_t_false {p q : Bool → Prop} {w : Bool} (h : MttF.eqv .t .t p q w) : p false ↔ q false := by
  rcases (Mtt_eqv_t p q w).mp h with e | ⟨h1, h2⟩
  · subst e; exact Iff.rfl
  · exact ⟨fun _ => h2, fun _ => h1⟩

/-- `□φ` is true in `𝔐_tt` just when `φ` is true at the non-actual world. -/
theorem Mtt_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MttF.U.TEnv n) (env : MttF.U.Env Γ ρ) :
    MttF.Holds (boxF φ) ρ env ↔ MttF.HoldsAt φ ρ env false := by
  refine (MttF.holdsAt_eqv_t φ topF ρ env _).trans ?_
  rw [MttF.eval_topF]
  refine (Mtt_eqv_t _ _ _).trans ⟨fun h => ?_, fun h => Or.inr ⟨h, trivial⟩⟩
  rcases h with e | ⟨h, _⟩
  · exact cast (congrFun e false).symm trivial
  · exact h

theorem Mtt_holdsAt_tex {n : Nat} {Γ : Ctx n} (φ : Fm Γ.text) (ρ : MttF.U.TEnv n) (env : MttF.U.Env Γ ρ) (w : Bool) :
    MttF.HoldsAt (Tm.tex φ) ρ env w ↔ ∃ a, MttF.HoldsAt φ (scons a ρ) env w := Iff.rfl

/-! ## Booleanism -/

theorem Mtt_Bool : ∀ φ, BoolSch φ → MttF.Valid φ := MttF.bool_valid fun _ => ⟨rfl, Or.inl HEq.rfl⟩

/-! ## Identity across types, and identity of types -/

theorem Mtt_Disjoint : MttF.Valid Disjoint :=
  (MttF.valid_iff_tr _).mpr <| MttF.tr_Disjoint.mpr fun _ _ hn _ _ h => hn h.1

theorem Mtt_Slogan : MttF.Valid Slogan :=
  (MttF.valid_iff_tr _).mpr <| MttF.tr_Slogan.mpr fun _ _ _ h => nomatch h.1

theorem Mtt_tr_Cantor : MttF.Tr Cantor ↔ ∀ a, ∃ G : MttF.U.El a → Bool → Prop,
    ∀ y : MttF.U.El a, ¬ MttF.eqv (.arr a .t) a G y MttF.U.w0 := Iff.rfl

theorem Mtt_Cantor : MttF.Valid Cantor :=
  (MttF.valid_iff_tr _).mpr <| Mtt_tr_Cantor.mpr fun a =>
    ⟨fun _ _ => True, fun _ h => Code.arr_ne_left a .t h.1⟩

theorem Mtt_Inj : MttF.Valid Inj := MttF.Inj_of fun _ _ _ => Iff.rfl

theorem Mtt_tr_Recovery : MttF.Tr Recovery ↔ ∀ a b c d, MttF.teq (.arr a c) (.arr b d) MttF.U.w0 ∧
    MttF.teq a b MttF.U.w0 → MttF.teq c d MttF.U.w0 := Iff.rfl

theorem Mtt_Recovery : MttF.Valid Recovery :=
  (MttF.valid_iff_tr _).mpr <| Mtt_tr_Recovery.mpr fun a b c d ⟨h, _⟩ => by
    have h' : Code.arr a c = Code.arr b d := h
    exact (Code.arr.inj h').2

theorem Mtt_ExtT : MttF.Valid ExtT :=
  (MttF.valid_iff_tr _).mpr <| MttF.tr_ExtT.mpr fun a _ ⟨h, _⟩ => by
    have x0 := Classical.choice (Univ.El_nonempty (U := MttF.U) a)
    obtain ⟨_, hy⟩ := h x0
    exact hy.1

theorem Mtt_IntT : MttF.Valid IntT := by
  intro ρ env
  refine (MttF.holds_tall _ _ _).mpr fun a => (MttF.holds_tall _ _ _).mpr fun b => ?_
  refine (MttF.holds_imp _ _ _ _).mpr fun h => (MttF.holds_teq _ _ _ _).mpr ?_
  have hs := (Mtt_box _ _ _).mp ((MttF.holds_conj _ _ _ _).mp h).1
  have x0 := Classical.choice (Univ.El_nonempty (U := MttF.U) a)
  obtain ⟨y, hy⟩ := (MttF.holdsAt_ex _ _ _ _ false).mp ((MttF.holdsAt_all _ _ _ _ false).mp hs x0)
  exact ((MttF.holdsAt_eqv _ _ _ _ _ _ false).mp hy).1

/-! ## Necessity of identity and distinctness -/

theorem Mtt_NIEqv : MttF.Valid NIEqv := by
  intro ρ env
  refine (MttF.holds_tall _ _ _).mpr fun a => ?_
  refine (MttF.holds_all _ _ _ _).mpr fun x => (MttF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MttF.holds_imp _ _ _ _).mpr fun hxy => (Mtt_box _ _ _).mpr ?_
  exact (MttF.holdsAt_eqv _ _ _ _ _ _ false).mpr ((MttF.holds_eqv _ _ _ _ _ _).mp hxy)

theorem Mtt_NITeq : MttF.Valid NITeq := by
  intro ρ env
  refine (MttF.holds_tall _ _ _).mpr fun a => (MttF.holds_tall _ _ _).mpr fun b => ?_
  refine (MttF.holds_imp _ _ _ _).mpr fun h => (Mtt_box _ _ _).mpr ?_
  exact (MttF.holdsAt_teq _ _ _ _ false).mpr ((MttF.holds_teq _ _ _ _).mp h)

theorem Mtt_NDTeq : MttF.Valid NDTeq := by
  intro ρ env
  refine (MttF.holds_tall _ _ _).mpr fun a => (MttF.holds_tall _ _ _).mpr fun b => ?_
  refine (MttF.holds_imp _ _ _ _).mpr fun hn => (Mtt_box _ _ _).mpr ?_
  refine (MttF.holdsAt_neg _ _ _ false).mpr fun ht => ?_
  exact (MttF.holds_neg _ _ _).mp hn ((MttF.holds_teq _ _ _ _).mpr ((MttF.holdsAt_teq _ _ _ _ false).mp ht))

/-! ## The Barcan formulas, and Necessitism -/

theorem Mtt_TBF : ∀ χ, TBFSch χ → MttF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MttF.holds_imp _ _ _ _).mpr fun h => ?_
  exact (Mtt_box _ _ _).mpr ((MttF.holdsAt_tall _ _ _ false).mpr fun a =>
    (Mtt_box _ _ _).mp ((MttF.holds_tall _ _ _).mp h a))

theorem Mtt_TCBF : ∀ χ, TCBFSch χ → MttF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MttF.holds_imp _ _ _ _).mpr fun h => ?_
  exact (MttF.holds_tall _ _ _).mpr fun a => (Mtt_box _ _ _).mpr
    ((MttF.holdsAt_tall _ _ _ false).mp ((Mtt_box _ _ _).mp h) a)

theorem Mtt_TNec : MttF.Valid TNec := by
  intro ρ env
  refine (MttF.holds_tall _ _ _).mpr fun a => (Mtt_box _ _ _).mpr ?_
  exact (Mtt_holdsAt_tex _ _ _ false).mpr ⟨a, (MttF.holdsAt_teq (Γ := Ctx.nil.text.text) tv1 tv0 _ _ false).mpr rfl⟩

theorem Mtt_BF : MttF.Valid BF := by
  intro ρ env
  refine (MttF.holds_tall _ _ _).mpr fun a => (MttF.holds_all _ _ _ _).mpr fun G => ?_
  refine (MttF.holds_imp _ _ _ _).mpr fun h => (Mtt_box _ _ _).mpr ?_
  exact (MttF.holdsAt_all _ _ _ _ false).mpr fun x => (Mtt_box _ _ _).mp ((MttF.holds_all _ _ _ _).mp h x)

theorem Mtt_CBF : MttF.Valid CBF := by
  intro ρ env
  refine (MttF.holds_tall _ _ _).mpr fun a => (MttF.holds_all _ _ _ _).mpr fun G => ?_
  refine (MttF.holds_imp _ _ _ _).mpr fun h => (MttF.holds_all _ _ _ _).mpr fun x => (Mtt_box _ _ _).mpr ?_
  exact (MttF.holdsAt_all _ _ _ _ false).mp ((Mtt_box _ _ _).mp h) x

theorem Mtt_Nec : MttF.Valid Nec := by
  intro ρ env
  refine (MttF.holds_tall _ _ _).mpr fun a => (MttF.holds_all _ _ _ _).mpr fun x => (Mtt_box _ _ _).mpr ?_
  exact (MttF.holdsAt_ex _ _ _ _ false).mpr ⟨x, (MttF.holdsAt_eqv _ _ _ _ _ _ false).mpr ⟨rfl, Or.inl HEq.rfl⟩⟩

/-! ## Further facts: what fails in `𝔐_tt`

`⊤` and `Y` are identified, but `⊤` is true and `Y` is false (at the actual world); and
functions are identified only with themselves. -/

theorem Mtt_tr_Truth : MttF.Tr Truth ↔ ∀ p q : Bool → Prop, MttF.eqv .t .t p q true → p true → q true := Iff.rfl

theorem Mtt_not_Truth : ¬ MttF.Valid Truth := fun h =>
  Bool.noConfusion (Mtt_tr_Truth.mp ((MttF.valid_iff_tr _).mp h) (fun _ => True) (fun w => w = false)
    ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩ trivial : true = false)

theorem Mtt_tr_LLEqv : MttF.Tr LLEqv ↔ ∀ a (x y : MttF.U.El a), MttF.eqv a a x y true →
    ∀ P : MttF.U.El a → Bool → Prop, P x true → P y true := Iff.rfl

theorem Mtt_not_LLEqv : ¬ MttF.Valid LLEqv := fun h =>
  Bool.noConfusion (Mtt_tr_LLEqv.mp ((MttF.valid_iff_tr _).mp h) .t (fun _ => True) (fun w => w = false)
    ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩ (fun p => p) trivial : true = false)

theorem Mtt_not_Collapse : ¬ MttF.Valid Collapse := fun h => by
  have h0 := (MttF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (fun w => w = true)
  have hb := (MttF.holds_imp _ _ _ _).mp h0 (show true = true from rfl)
  exact Bool.noConfusion ((Mtt_box _ _ _).mp hb : false = true)

theorem Mtt_tr_PropExt : MttF.Tr PropExt ↔ ∀ p q : Bool → Prop, (p true ↔ q true) → MttF.eqv .t .t p q true :=
  Iff.rfl

theorem Mtt_not_PropExt : ¬ MttF.Valid PropExt := fun h => by
  have h0 := Mtt_tr_PropExt.mp ((MttF.valid_iff_tr _).mp h) (fun _ => True) (fun w => w = true)
    ⟨fun _ => rfl, fun _ => trivial⟩
  have e := (Mtt_eqv_t_false h0).mp trivial
  exact Bool.noConfusion (e : false = true)

theorem Mtt_tr_WCong : MttF.Tr WCong ↔ ∀ a b c d (f : MttF.U.El a → MttF.U.El c) (g : MttF.U.El b → MttF.U.El d) x y,
    (MttF.teq a b true ∧ MttF.teq c d true) ∧ (MttF.eqv (.arr a c) (.arr b d) f g true ∧ MttF.eqv a b x y true) →
    MttF.eqv c d (f x) (g y) true := Iff.rfl

theorem Mtt_tr_PCong : MttF.Tr PCong ↔ ∀ a c d (f : MttF.U.El a → MttF.U.El c) (g : MttF.U.El a → MttF.U.El d) x,
    MttF.eqv (.arr a c) (.arr a d) f g true → MttF.eqv c d (f x) (g x) true := Iff.rfl

/-- Negation sends `⊤` and `Y` to propositions that are not identified. -/
theorem Mtt_neg_ne : ¬ MttF.eqv .t .t (fun _ => ¬ True) (fun w => ¬ (w = false)) true := fun h => by
  rcases (Mtt_eqv_t _ _ _).mp h with e | ⟨h1, _⟩
  · exact (cast (congrFun e true).symm (fun e' : true = false => Bool.noConfusion e')) trivial
  · exact h1 trivial

theorem Mtt_not_Cong : ¬ MttF.Valid Cong := fun h =>
  Mtt_neg_ne (MttF.tr_Cong.mp ((MttF.valid_iff_tr _).mp h) .t .t .t .t
    (fun (p : Bool → Prop) (w : Bool) => ¬ p w) (fun (p : Bool → Prop) (w : Bool) => ¬ p w)
    (fun _ => True) (fun w => w = false) ⟨⟨rfl, Or.inl HEq.rfl⟩, ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩⟩)

theorem Mtt_not_WCong : ¬ MttF.Valid WCong := fun h =>
  Mtt_neg_ne (Mtt_tr_WCong.mp ((MttF.valid_iff_tr _).mp h) .t .t .t .t
    (fun (p : Bool → Prop) (w : Bool) => ¬ p w) (fun (p : Bool → Prop) (w : Bool) => ¬ p w)
    (fun _ => True) (fun w => w = false) ⟨⟨rfl, rfl⟩, ⟨rfl, Or.inl HEq.rfl⟩, ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩⟩)

theorem Mtt_PCong : MttF.Valid PCong :=
  (MttF.valid_iff_tr _).mpr <| Mtt_tr_PCong.mpr fun a c d f g x ⟨e, h⟩ => by
    have e' : Code.arr a c = Code.arr a d := e
    have ecd := (Code.arr.inj e').2
    subst ecd
    rcases h with h | ⟨s, _⟩
    · have hf : f = g := eq_of_heq h
      subst hf
      exact ⟨rfl, Or.inl HEq.rfl⟩
    · exact (s : False).elim

theorem Mtt_not_PExt : ¬ MttF.Valid PExt := fun h => by
  have h0 := MttF.tr_PExt.mp ((MttF.valid_iff_tr _).mp h) .e .t .t (fun (_ : Unit) (_ : Bool) => True)
    (fun (_ : Unit) (w : Bool) => w = false) (fun _ => ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩)
  rcases h0.2 with e | ⟨s, _⟩
  · have e' := congrFun (congrFun (eq_of_heq e) ()) true
    exact Bool.noConfusion (cast e' trivial : true = false)
  · exact (s : False).elim

theorem Mtt_tr_Hae : MttF.Tr Hae ↔ ∀ a (x : MttF.U.El a), MttF.eqv a (.arr a .t) x (fun y => MttF.eqv a a y x) true :=
  Iff.rfl

theorem Mtt_not_Hae : ¬ MttF.Valid Hae := fun h =>
  Code.arr_ne_left (Code.e : Code Empty) .t (Mtt_tr_Hae.mp ((MttF.valid_iff_tr _).mp h) .e ()).1.symm

theorem Mtt_tr_Twin : MttF.Tr Twin ↔ ∀ a (x : MttF.U.El a), ∃ b, ¬ MttF.teq a b true ∧
    ∃ y : MttF.U.El b, MttF.eqv a b x y true := Iff.rfl

theorem Mtt_not_Twin : ¬ MttF.Valid Twin := fun h => by
  obtain ⟨_, hn, _, hy⟩ := Mtt_tr_Twin.mp ((MttF.valid_iff_tr _).mp h) .e ()
  exact hn hy.1

theorem Mtt_tr_IdId : MttF.Tr IdId ↔ ∀ a (x y : MttF.U.El a), MttF.eqv .t .t (MttF.eqv a a x y)
    (fun w => ∀ G : MttF.U.El a → Bool → Prop, G x w → G y w) true := Iff.rfl

theorem Mtt_not_IdId : ¬ MttF.Valid IdId := fun h => by
  have h0 := Mtt_tr_IdId.mp ((MttF.valid_iff_tr _).mp h) .t (fun _ => True) (fun w => w = false)
  have hQ := (Mtt_eqv_t_false h0).mp ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩
  have hY := hQ (fun p _ => p = fun _ => True) rfl
  exact Bool.noConfusion (cast (congrFun hY true).symm trivial : true = false)

/-! ## The polymorphic Leibniz law fails

The polymorphic predicate `λγ.λz:γ. ∃_{γ→t} F (F z ∧ F ≡_{γ→t, t→t} λp.p)` is true of `⊤` and
false of `Y` (at type `t`, the only `F` identified with `λp.p` is `λp.p` itself). -/

open Tm in
def MttPredId : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (ex tv0.pred (conj (.app (.var .here) (.var (.there .here)))
    (eqv tv0.pred (Ty.arrow tyT tyT) (.var .here) (.lam tyT (.var .here))))))

theorem Mtt_tr_LLPoly : MttF.Tr (LLPoly MttPredId) ↔ ∀ a b (x : MttF.U.El a) (y : MttF.U.El b), MttF.eqv a b x y true →
    (∃ F : MttF.U.El a → Bool → Prop, F x true ∧ MttF.eqv (.arr a .t) (.arr .t .t) F (fun p => p) true) →
    (∃ F : MttF.U.El b → Bool → Prop, F y true ∧ MttF.eqv (.arr b .t) (.arr .t .t) F (fun p => p) true) := Iff.rfl

theorem Mtt_not_LLPoly : ¬ MttF.Valid (LLPoly MttPredId) := fun h => by
  obtain ⟨F, hF, _, e | ⟨s, _⟩⟩ := Mtt_tr_LLPoly.mp ((MttF.valid_iff_tr _).mp h) .t .t (fun _ => True)
    (fun w => w = false) ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩ ⟨fun p => p, trivial, ⟨rfl, Or.inl HEq.rfl⟩⟩
  · have hF' : F = fun p => p := eq_of_heq e
    subst hF'
    exact Bool.noConfusion (hF : true = false)
  · exact (s : False).elim

theorem Mtt_tr_Bridge : MttF.Tr (Bridge MttPredId) ↔ ∀ a b (x : MttF.U.El a) (y : MttF.U.El b),
    MttF.eqv a b x y true ∧ MttF.teq a b true →
    (∃ F : MttF.U.El a → Bool → Prop, F x true ∧ MttF.eqv (.arr a .t) (.arr .t .t) F (fun p => p) true) →
    (∃ F : MttF.U.El b → Bool → Prop, F y true ∧ MttF.eqv (.arr b .t) (.arr .t .t) F (fun p => p) true) := Iff.rfl

/-- The same predicate refutes LL≡/≈: `⊤` and `Y` are items of the same type. -/
theorem Mtt_not_Bridge : ¬ MttF.Valid (Bridge MttPredId) := fun h => by
  obtain ⟨F, hF, _, e | ⟨s, _⟩⟩ := Mtt_tr_Bridge.mp ((MttF.valid_iff_tr _).mp h) .t .t (fun _ => True)
    (fun w => w = false) ⟨⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩, rfl⟩ ⟨fun p => p, trivial, ⟨rfl, Or.inl HEq.rfl⟩⟩
  · have hF' : F = fun p => p := eq_of_heq e
    subst hF'
    exact Bool.noConfusion (hF : true = false)
  · exact (s : False).elim

/-! ## Classicism fails

PI proves `((p ≡ q) ∧ p ∧ ¬q) ↔ ⊥` (by Truth); but at `p := ⊤`, `q := Y` the left side is the
proposition true only at the actual world, which is not identified with `⊥`. -/

section
open Derive Tm

def Mtt_v4 {n : Nat} {Γ : Ctx n} (a b c d : Fm Γ) : Fin 4 → Fm Γ :=
  fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d

abbrev MttClsF : Fm Γpq := conj (eqv tyT tyT pV qV) (conj pV qV.neg)

set_option maxHeartbeats 8000000 in
theorem Mtt_cls_PIP : PIP Γpq (iff MttClsF botF) := by
  have hT : Ent (fun χ => χ = LLEqv) Γpq [] ((eqv tyT tyT pV qV).imp (pV.imp qV)) :=
    ((Ent.closed (Γ := Γpq) (Hs := []) (d_Truth (S := fun χ => χ = LLEqv) rfl)).inst pV).inst qV
  have ht : Ent (fun χ => χ = LLEqv) Γpq []
      (((eqv tyT tyT pV qV).imp (pV.imp qV)).imp ((botF : Fm Γpq).neg.imp (iff MttClsF botF))) :=
    Ent.taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2)))
        (.imp (.neg (.atom 3)) (.iff (.conj (.atom 0) (.conj (.atom 1) (.neg (.atom 2)))) (.atom 3))))
      (Mtt_v4 (eqv tyT tyT pV qV) pV qV botF)
      (fun _ h nb => ⟨fun ⟨a, p, nq⟩ => (nq (h a p)).elim, fun b => (nb b).elim⟩)
  exact Ent.toProv (Ent.mp2 ht hT Ent.top)

theorem Mtt_cls : ClassSch (closeCtx Γpq (eqv tyT tyT MttClsF botF)) :=
  Or.inl ⟨0, Γpq, MttClsF, botF, Mtt_cls_PIP, rfl⟩

end

theorem Mtt_not_Class : ¬ ∀ χ, ClassSch χ → MttF.Valid χ := fun h => by
  have h0 := (MttF.holds_all _ _ _ _).mp ((MttF.holds_all _ _ _ _).mp (h _ Mtt_cls (fun i => i.elim0) ())
    (fun _ => True)) (fun w => w = false)
  have h1 := (MttF.holdsAt_eqv_t _ _ _ _ _).mp h0
  have eb := MttF.eval_botF (Γ := Γpq) (fun i => i.elim0) (((), fun _ => True), fun w => w = false)
  rcases (Mtt_eqv_t _ _ _).mp h1 with e | ⟨_, hb⟩
  · refine cast (congrFun (e.trans eb) true) ?_
    exact (MttF.holds_conj _ _ _ _).mpr ⟨(MttF.holdsAt_eqv_t _ _ _ _ _).mpr ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩,
      (MttF.holds_conj _ _ _ _).mpr ⟨trivial, (MttF.holds_neg _ _ _).mpr fun e => Bool.noConfusion (e : true = false)⟩⟩
  · exact cast (congrFun eb false) hb

end Wd
end PIF
