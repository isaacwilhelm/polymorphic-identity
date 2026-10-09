import PIBarcan
import PIAlgModels

/-!
# Models for the Barcan formulas and Type Necessitism
-/
set_option autoImplicit false

namespace PIF

/-! ## Models with worlds: both Barcan formulas hold, since the types are the same at every world -/

namespace Wd
namespace RD
variable (D : RD)

theorem holdsAt_tall {n : Nat} {Γ : Ctx n} (φ : Fm Γ.text) (ρ : D.frame.U.TEnv n) (env : D.frame.U.Env Γ ρ) (w : D.W) :
    D.frame.HoldsAt (Tm.tall φ) ρ env w ↔ ∀ a, D.frame.HoldsAt φ (scons a ρ) env w := Iff.rfl
theorem holdsAt_tex {n : Nat} {Γ : Ctx n} (φ : Fm Γ.text) (ρ : D.frame.U.TEnv n) (env : D.frame.U.Env Γ ρ) (w : D.W) :
    D.frame.HoldsAt (Tm.tex φ) ρ env w ↔ ∃ a, D.frame.HoldsAt φ (scons a ρ) env w := Iff.rfl

theorem TBF_valid : ∀ χ, TBFSch χ → D.frame.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (D.frame.holds_imp _ _ _ _).mpr fun h => ?_
  exact (D.holds_box _ _ _).mpr fun w => (D.holdsAt_tall _ _ _ w).mpr fun a =>
    (D.holds_box _ _ _).mp ((D.frame.holds_tall _ _ _).mp h a) w

theorem TCBF_valid : ∀ χ, TCBFSch χ → D.frame.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (D.frame.holds_imp _ _ _ _).mpr fun h => ?_
  exact (D.frame.holds_tall _ _ _).mpr fun a => (D.holds_box _ _ _).mpr fun w =>
    (D.holdsAt_tall _ _ _ w).mp ((D.holds_box _ _ _).mp h w) a

theorem TNec_valid (hTe : ∀ a w, ∃ b, D.Te a b w) : D.frame.Valid TNec := by
  intro ρ env
  refine (D.frame.holds_tall _ _ _).mpr fun a => (D.holds_box _ _ _).mpr fun w => ?_
  obtain ⟨b, hb⟩ := hTe a w
  exact (D.holdsAt_tex _ _ _ w).mpr ⟨b, (D.frame.holdsAt_teq (Γ := Ctx.nil.text.text) tv1 tv0 _ _ w).mpr hb⟩

theorem not_TNec (a : Code Empty) (w1 : D.W) (h1 : ∀ b, ¬ D.Te a b w1) : ¬ D.frame.Valid TNec := fun h => by
  have hb := (D.holds_box _ _ _).mp ((D.frame.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) a) w1
  obtain ⟨b, hb'⟩ := (D.holdsAt_tex _ _ _ w1).mp hb
  exact h1 b ((D.frame.holdsAt_teq (Γ := Ctx.nil.text.text) tv1 tv0 _ _ w1).mp hb')

end RD

theorem Mw_TBF : ∀ χ, TBFSch χ → DW.frame.Valid χ := DW.TBF_valid
theorem Mw_TCBF : ∀ χ, TCBFSch χ → DW.frame.Valid χ := DW.TCBF_valid
theorem Mw_TNec : DW.frame.Valid TNec := DW.TNec_valid fun a _ => ⟨a, rfl⟩
theorem Mni_TBF : ∀ χ, TBFSch χ → DNI.frame.Valid χ := DNI.TBF_valid
theorem Mni_TCBF : ∀ χ, TCBFSch χ → DNI.frame.Valid χ := DNI.TCBF_valid
theorem Mni_not_TNec : ¬ DNI.frame.Valid TNec := DNI.not_TNec .e false fun _ h => Bool.false_ne_true h.2
theorem Mnd_TNec : DND.frame.Valid TNec := DND.TNec_valid fun a _ => ⟨a, fun _ => rfl⟩
theorem Mie_TNec : DIE.frame.Valid TNec := DIE.TNec_valid fun a _ => ⟨a, rfl⟩
theorem Mnd_TBF : ∀ χ, TBFSch χ → DND.frame.Valid χ := DND.TBF_valid
theorem Mnd_TCBF : ∀ χ, TCBFSch χ → DND.frame.Valid χ := DND.TCBF_valid
theorem Mie_TBF : ∀ χ, TBFSch χ → DIE.frame.Valid χ := DIE.TBF_valid
theorem Mie_TCBF : ∀ χ, TCBFSch χ → DIE.frame.Valid χ := DIE.TCBF_valid

end Wd

/-! ## Tagged models -/

namespace Tg

/-- In `𝔐_z` a type-quantified proposition is never identical to `⊤`, which is unquantified. -/
theorem Mz_not_TBF : ¬ ∀ χ, TBFSch χ → MzF.Valid χ := fun h => by
  have h0 := h _ ⟨topF, rfl⟩ (fun i => i.elim0) ()
  have hb := (MzF.holds_imp _ _ _ _).mp h0 (fun _ => (MzF.holds_eqv_t _ _ _ _).mpr ⟨rfl, HEq.rfl⟩)
  have e := eq_of_heq ((MzF.holds_eqv_t _ _ _ _).mp hb).2
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

theorem Mz_not_TNec : ¬ MzF.Valid TNec := fun h => by
  have hb := (MzF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e
  have e := eq_of_heq ((MzF.holds_eqv_t _ _ _ _).mp hb).2
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

end Tg

/-! ## `𝔐_cb`: TBF and Type Necessitism without TCBF -/

namespace Al

def MbF : Frame where
  U := univI
  eqv := fun a b x y => (a = b ∧ HEq x y, true)
  teq := fun a b => (a = b, false)
  neg := fun p => (¬ p.1, true)
  imp := fun p q => (p.1 → q.1, true)
  cnj := fun p q => (p.1 ∧ q.1, true)
  dsj := fun p q => (p.1 ∨ q.1, true)
  bic := fun p q => (p.1 ↔ q.1, true)
  all := fun _ f => (∀ x, (f x).1, true)
  ex := fun _ f => (∃ x, (f x).1, true)
  tall := fun Q => (∀ a, (Q a).1, true)
  tex := fun Q => (∃ a, (Q a).1, true)
  hneg := fun _ => Iff.rfl
  himp := fun _ _ => Iff.rfl
  hcnj := fun _ _ => Iff.rfl
  hdsj := fun _ _ => Iff.rfl
  hbic := fun _ _ => Iff.rfl
  hall := fun _ _ => Iff.rfl
  hex := fun _ _ => Iff.rfl
  htall := fun _ => Iff.rfl
  htex := fun _ => Iff.rfl

theorem Mb_model : MbF.IsModelPIm :=
  MbF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => ⟨rfl, HEq.rfl⟩) (fun _ _ _ _ h => ⟨h.1.symm, h.2.symm⟩)
    (fun _ _ _ _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)

theorem Mb_top {n : Nat} {Γ : Ctx n} (ρ : MbF.U.TEnv n) (env : MbF.U.Env Γ ρ) :
    MbF.eval (topF : Fm Γ) ρ env = (True, true) :=
  Prod.ext (propext (iff_true_intro (MbF.holds_topF ρ env ⟨(False, true), id⟩))) rfl

theorem Mb_LLEqv : MbF.Valid LLEqv := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => ?_
  refine (MbF.holds_all _ _ _ _).mpr fun x => (MbF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MbF.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (MbF.holds_all _ _ _ _).mpr fun G => (MbF.holds_imp _ _ _ _).mpr fun hGx => ?_
  have h := ((MbF.holds_eqv _ _ _ _ _ _).mp hxy).2
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.trans (cast_heq _ _)))
  subst e
  exact hGx

theorem Mb_TBF : ∀ χ, TBFSch χ → MbF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MbF.holds_imp _ _ _ _).mpr fun h => ?_
  have ha : ∀ a, MbF.eval φ (scons a ρ) env = (True, true) := fun a =>
    (eq_of_heq ((MbF.holds_eqv_t _ _ _ _).mp ((MbF.holds_tall _ _ _).mp h a)).2).trans (Mb_top _ _)
  refine (MbF.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ((?_ : MbF.eval (Tm.tall φ) ρ env = (True, true)).trans (Mb_top _ _).symm)⟩
  exact Prod.ext (propext ⟨fun _ => trivial, fun _ a => cast (congrArg Prod.fst (ha a)).symm trivial⟩) rfl

theorem Mb_TNec : MbF.Valid TNec := by
  intro ρ env
  refine (MbF.holds_tall _ _ _).mpr fun a => ?_
  have hv : MbF.eval (Tm.tex (Tm.teq tv1 tv0) : Fm Ctx.nil.text) (scons a ρ) env = (True, true) :=
    Prod.ext (propext ⟨fun _ => trivial, fun _ => by exact ⟨a, rfl⟩⟩) rfl
  exact (MbF.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq (hv.trans (Mb_top (Γ := Ctx.nil.text) _ _).symm)⟩

theorem Mb_not_TCBF : ¬ ∀ χ, TCBFSch χ → MbF.Valid χ := fun h => by
  have h0 := h _ ⟨Tm.teq tv0 tv0, rfl⟩ (fun i => i.elim0) ()
  have hv : MbF.eval (Tm.tall (Tm.teq tv0 tv0) : Fm Ctx.nil) (fun i => i.elim0) () = (True, true) :=
    Prod.ext (propext ⟨fun _ => trivial, fun _ a => by exact (rfl : a = a)⟩) rfl
  have hp : MbF.Holds (boxF (Tm.tall (Tm.teq tv0 tv0) : Fm Ctx.nil)) (fun i => i.elim0) () :=
    (MbF.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq (hv.trans (Mb_top (Γ := Ctx.nil) _ _).symm)⟩
  have hb := (MbF.holds_tall _ _ _).mp ((MbF.holds_imp _ _ _ _).mp h0 hp) .e
  have e := eq_of_heq ((MbF.holds_eqv_t _ _ _ _).mp hb).2
  exact Bool.noConfusion (congrArg Prod.snd (e.trans (Mb_top (Γ := Ctx.nil.text) _ _)) : false = true)

end Al

/-! ## Models in which the type quantifiers act differently at a second world -/

namespace Al

namespace Frame
variable (F : Frame)

theorem holds_closeAll : ∀ (k : Nat) (φ : Fm (ctxT k)) (ρ : F.U.TEnv 0),
    (∀ env : F.U.Env (ctxT k) ρ, F.Holds φ ρ env) → ∀ env0 : F.U.Env Ctx.nil ρ, F.Holds (closeAll k φ) ρ env0
  | 0, _, _, h, env0 => h env0
  | k + 1, φ, ρ, h, env0 =>
    holds_closeAll k (Tm.all tyT φ) ρ (fun env => (F.holds_all tyT φ ρ env).mpr fun v => h (env, v)) env0

end Frame

def univQ : Univ where
  P := Bool → Prop
  V := fun p => p true
  p0 := fun _ => True
  E := Unit
  Base := Empty
  B := Empty.elim
  neE := ⟨()⟩
  neB := fun b => b.elim

/-- Two worlds; identity of items and of types is rigid; the connectives and the term quantifiers act
world by world; at the actual world the type quantifiers are as usual, and at the other world their
values are `TA` and `TE`. -/
def MqF (TA TE : (Code Empty → (Bool → Prop)) → Prop) : Frame where
  U := univQ
  eqv := fun a b x y _ => a = b ∧ HEq x y
  teq := fun a b _ => a = b
  neg := fun p w => ¬ p w
  imp := fun p q w => p w → q w
  cnj := fun p q w => p w ∧ q w
  dsj := fun p q w => p w ∨ q w
  bic := fun p q w => p w ↔ q w
  all := fun _ f w => ∀ x, f x w
  ex := fun _ f w => ∃ x, f x w
  tall := fun Q w => cond w (∀ a, Q a true) (TA Q)
  tex := fun Q w => cond w (∃ a, Q a true) (TE Q)
  hneg := fun _ => Iff.rfl
  himp := fun _ _ => Iff.rfl
  hcnj := fun _ _ => Iff.rfl
  hdsj := fun _ _ => Iff.rfl
  hbic := fun _ _ => Iff.rfl
  hall := fun _ _ => Iff.rfl
  hex := fun _ _ => Iff.rfl
  htall := fun _ => Iff.rfl
  htex := fun _ => Iff.rfl

section Mq
variable (TA TE : (Code Empty → (Bool → Prop)) → Prop)

theorem Mq_model : (MqF TA TE).IsModelPIm :=
  (MqF TA TE).model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => ⟨rfl, HEq.rfl⟩) (fun _ _ _ _ h => ⟨h.1.symm, h.2.symm⟩)
    (fun _ _ _ _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)

theorem Mq_top {n : Nat} {Γ : Ctx n} (ρ : (MqF TA TE).U.TEnv n) (env : (MqF TA TE).U.Env Γ ρ) :
    (MqF TA TE).eval (topF : Fm Γ) ρ env = fun _ => True := by
  funext w
  have e := (MqF TA TE).eval_all (Γ := Γ) tyT (.var .here) ρ env
  refine propext ⟨fun _ => trivial, fun _ => ?_⟩
  show ¬ (MqF TA TE).eval (botF : Fm Γ) ρ env w
  rw [botF, e]
  exact fun h => h (fun _ => False)

theorem Mq_LLEqv : (MqF TA TE).Valid LLEqv := by
  intro ρ env
  refine ((MqF TA TE).holds_tall _ _ _).mpr fun a => ?_
  refine ((MqF TA TE).holds_all _ _ _ _).mpr fun x => ((MqF TA TE).holds_all _ _ _ _).mpr fun y => ?_
  refine ((MqF TA TE).holds_imp _ _ _ _).mpr fun hxy => ?_
  refine ((MqF TA TE).holds_all _ _ _ _).mpr fun G => ((MqF TA TE).holds_imp _ _ _ _).mpr fun hGx => ?_
  have h := (((MqF TA TE).holds_eqv _ _ _ _ _ _).mp hxy).2
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.trans (cast_heq _ _)))
  subst e
  exact hGx

theorem Mq_evalInst {n : Nat} {Γ : Ctx n} {k : Nat} (P : PF k) (as : Fin k → Fm Γ) (ρ : (MqF TA TE).U.TEnv n)
    (env : (MqF TA TE).U.Env Γ ρ) (w : Bool) :
    (MqF TA TE).eval (P.inst as) ρ env w ↔ P.evalP (fun i => (MqF TA TE).eval (as i) ρ env w) := by
  induction P with
  | atom i => exact Iff.rfl
  | neg P ih => exact not_congr ih
  | imp P Q ihP ihQ => exact imp_congr ihP ihQ
  | conj P Q ihP ihQ => exact and_congr ihP ihQ
  | disj P Q ihP ihQ => exact or_congr ihP ihQ
  | iff P Q ihP ihQ => exact iff_congr ihP ihQ

theorem Mq_Bool : ∀ φ, BoolSch φ → (MqF TA TE).Valid φ := by
  rintro _ ⟨k, P, Q, hT, rfl⟩ ρ env0
  refine (MqF TA TE).holds_closeAll k _ ρ (fun env => ?_) env0
  have e : (MqF TA TE).eval (P.inst (varsT k)) ρ env = (MqF TA TE).eval (Q.inst (varsT k)) ρ env :=
    funext fun w => propext ((Mq_evalInst TA TE P _ ρ env w).trans ((hT _).trans (Mq_evalInst TA TE Q _ ρ env w).symm))
  exact ((MqF TA TE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq e⟩

theorem Mq_IdId : (MqF TA TE).Valid IdId := by
  intro ρ env
  refine ((MqF TA TE).holds_tall _ _ _).mpr fun a => ?_
  refine ((MqF TA TE).holds_all _ _ _ _).mpr fun x => ((MqF TA TE).holds_all _ _ _ _).mpr fun y => ?_
  refine ((MqF TA TE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine ((MqF TA TE).eval_eqv _ _ _ _ _ _).trans (Eq.trans ?_ ((MqF TA TE).eval_all
    (Γ := ((Ctx.nil.text).ext tv0).ext tv0) tv0.pred
    (Tm.imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))
    (scons a ρ) ((env, x), y)).symm)
  funext w
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.2.trans (cast_heq _ _)))
    subst e; intro G hG; exact hG
  · have hy : HEq y x := h (fun z _ => HEq z x) (by exact HEq.rfl)
    exact ⟨rfl, (cast_heq _ _).trans (hy.symm.trans (cast_heq _ _).symm)⟩

theorem Mq_NIEqv : (MqF TA TE).Valid NIEqv := by
  intro ρ env
  refine ((MqF TA TE).holds_tall _ _ _).mpr fun a => ?_
  refine ((MqF TA TE).holds_all _ _ _ _).mpr fun x => ((MqF TA TE).holds_all _ _ _ _).mpr fun y => ?_
  refine ((MqF TA TE).holds_imp _ _ _ _).mpr fun hxy => ?_
  refine ((MqF TA TE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  exact (((MqF TA TE).eval_eqv _ _ _ _ _ _).trans (funext fun _ => propext ⟨fun _ => trivial, fun _ => hxy⟩)).trans
    (Mq_top TA TE (Γ := ((Ctx.nil.text).ext tv0).ext tv0) _ _).symm

theorem Mq_NITeq : (MqF TA TE).Valid NITeq := by
  intro ρ env
  refine ((MqF TA TE).holds_tall _ _ _).mpr fun a => ((MqF TA TE).holds_tall _ _ _).mpr fun b => ?_
  refine ((MqF TA TE).holds_imp _ _ _ _).mpr fun h => ?_
  refine ((MqF TA TE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  exact (((MqF TA TE).eval_teq _ _ _ _).trans (funext fun _ => propext ⟨fun _ => trivial, fun _ => h⟩)).trans
    (Mq_top TA TE (Γ := Ctx.nil.text.text) _ _).symm

theorem Mq_NDTeq : (MqF TA TE).Valid NDTeq := by
  intro ρ env
  refine ((MqF TA TE).holds_tall _ _ _).mpr fun a => ((MqF TA TE).holds_tall _ _ _).mpr fun b => ?_
  refine ((MqF TA TE).holds_imp _ _ _ _).mpr fun h => ?_
  refine ((MqF TA TE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine Eq.trans ?_ (Mq_top TA TE (Γ := Ctx.nil.text.text) _ _).symm
  funext w
  exact propext ⟨fun _ => trivial, fun _ => h⟩

theorem Mq_Disjoint : (MqF TA TE).Valid Disjoint := by
  intro ρ env
  refine ((MqF TA TE).holds_tall _ _ _).mpr fun a => ((MqF TA TE).holds_tall _ _ _).mpr fun b => ?_
  refine ((MqF TA TE).holds_imp _ _ _ _).mpr fun hn => ?_
  refine ((MqF TA TE).holds_all _ _ _ _).mpr fun x => ((MqF TA TE).holds_all _ _ _ _).mpr fun y => ?_
  refine ((MqF TA TE).holds_neg _ _ _).mpr fun hxy => ?_
  exact ((MqF TA TE).holds_neg _ _ _).mp hn (((MqF TA TE).holds_teq _ _ _ _).mpr (((MqF TA TE).holds_eqv _ _ _ _ _ _).mp hxy).1)

theorem Mq_Inj : (MqF TA TE).Valid Inj := by
  intro ρ env
  refine ((MqF TA TE).holds_tall _ _ _).mpr fun a => ((MqF TA TE).holds_tall _ _ _).mpr fun b => ?_
  refine ((MqF TA TE).holds_tall _ _ _).mpr fun c => ((MqF TA TE).holds_tall _ _ _).mpr fun d => ?_
  refine ((MqF TA TE).holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := ((MqF TA TE).holds_teq _ _ _ _).mp h
  injection h' with hab hcd
  exact ((MqF TA TE).holds_conj _ _ _ _).mpr ⟨((MqF TA TE).holds_teq _ _ _ _).mpr hab, ((MqF TA TE).holds_teq _ _ _ _).mpr hcd⟩

theorem Mq_tr_Slogan : (MqF TA TE).Holds Slogan (fun i => i.elim0) () ↔
    ∀ (x : Unit) (b : Code Empty) (y : univQ.El b → (Bool → Prop)), ¬ ((Code.e : Code Empty) = .arr b .t ∧ HEq x y) := Iff.rfl

theorem Mq_Slogan : (MqF TA TE).Valid Slogan :=
  ((MqF TA TE).valid_iff_tr _).mpr ((Mq_tr_Slogan TA TE).mpr fun _ _ _ h => nomatch h.1)

theorem Mq_tr_PExt : (MqF TA TE).Holds PExt (fun i => i.elim0) () ↔
    ∀ (a c d : Code Empty) (f : univQ.El a → univQ.El c) (g : univQ.El a → univQ.El d),
      (∀ x, c = d ∧ HEq (f x) (g x)) → (Code.arr a c = Code.arr a d ∧ HEq f g) := Iff.rfl

theorem Mq_PExt : (MqF TA TE).Valid PExt :=
  ((MqF TA TE).valid_iff_tr _).mpr ((Mq_tr_PExt TA TE).mpr fun a c d f g h => by
    have x0 := Classical.choice (Univ.El_nonempty (U := univQ) a)
    have hcd : c = d := (h x0).1
    subst hcd
    exact ⟨rfl, heq_of_eq (funext fun x => eq_of_heq (h x).2)⟩)

theorem Mq_tr_Cong : (MqF TA TE).Holds Cong (fun i => i.elim0) () ↔
    ∀ (a b c d : Code Empty) (f : univQ.El a → univQ.El c) (g : univQ.El b → univQ.El d) x y,
      (Code.arr a c = Code.arr b d ∧ HEq f g) ∧ (a = b ∧ HEq x y) → (c = d ∧ HEq (f x) (g y)) := Iff.rfl

theorem Mq_Cong : (MqF TA TE).Valid Cong :=
  ((MqF TA TE).valid_iff_tr _).mpr ((Mq_tr_Cong TA TE).mpr fun a b c d f g x y ⟨⟨h1, h2⟩, ⟨_, h4⟩⟩ => by
    injection h1 with hab hcd
    subst hab; subst hcd
    cases h2; cases h4
    exact ⟨rfl, HEq.rfl⟩)

end Mq

/-- `𝔐_q,A`: at the other world, type-universal claims are false and type-existential ones true. -/
abbrev MqA : Frame := MqF (fun _ => False) (fun _ => True)
/-- `𝔐_q,C`: at the other world, type-universal claims are true and type-existential ones false. -/
abbrev MqC : Frame := MqF (fun _ => True) (fun _ => False)

theorem MqA_not_TBF : ¬ ∀ χ, TBFSch χ → MqA.Valid χ := fun h => by
  have h0 := h _ ⟨topF, rfl⟩ (fun i => i.elim0) ()
  have hb := (MqA.holds_imp _ _ _ _).mp h0 ((MqA.holds_tall _ _ _).mpr fun a =>
    (MqA.holds_eqv_t _ _ _ _).mpr ⟨rfl, HEq.rfl⟩)
  have e := (eq_of_heq ((MqA.holds_eqv_t _ _ _ _).mp hb).2).trans (Mq_top _ _ (Γ := Ctx.nil) _ _)
  exact (cast (congrFun e false).symm trivial : False)

theorem MqA_TCBF : ∀ χ, TCBFSch χ → MqA.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MqA.holds_imp _ _ _ _).mpr fun h => ?_
  have e := (eq_of_heq ((MqA.holds_eqv_t _ _ _ _).mp h).2).trans (Mq_top _ _ (Γ := Ctx.nil) _ _)
  exact (cast (congrFun e false).symm trivial : False).elim

theorem MqA_TNec : MqA.Valid TNec := by
  intro ρ env
  refine (MqA.holds_tall _ _ _).mpr fun a => (MqA.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine Eq.trans ?_ (Mq_top _ _ (Γ := Ctx.nil.text) _ _).symm
  funext w
  cases w
  · exact propext ⟨fun _ => trivial, fun _ => trivial⟩
  · exact propext ⟨fun _ => trivial, fun _ => ⟨a, rfl⟩⟩

theorem MqC_TBF : ∀ χ, TBFSch χ → MqC.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MqC.holds_imp _ _ _ _).mpr fun h => ?_
  refine (MqC.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine Eq.trans ?_ (Mq_top _ _ (Γ := Ctx.nil) _ _).symm
  funext w
  cases w
  · exact propext ⟨fun _ => trivial, fun _ => trivial⟩
  · refine propext ⟨fun _ => trivial, fun _ a => ?_⟩
    have e := (eq_of_heq ((MqC.holds_eqv_t _ _ _ _).mp ((MqC.holds_tall _ _ _).mp h a)).2).trans
      (Mq_top _ _ (Γ := Ctx.nil.text) _ _)
    exact cast (congrFun e true).symm trivial

theorem MqC_not_TCBF : ¬ ∀ χ, TCBFSch χ → MqC.Valid χ := fun h => by
  have h0 := h _ ⟨Tm.tex (Tm.teq tv1 tv0), rfl⟩ (fun i => i.elim0) ()
  have hp : MqC.Holds (boxF (Tm.tall (Tm.tex (Tm.teq tv1 tv0))) : Fm Ctx.nil) (fun i => i.elim0) () := by
    refine (MqC.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
    refine Eq.trans ?_ (Mq_top _ _ (Γ := Ctx.nil) _ _).symm
    funext w
    cases w
    · exact propext ⟨fun _ => trivial, fun _ => trivial⟩
    · exact propext ⟨fun _ => trivial, fun _ a => ⟨a, rfl⟩⟩
  have hb := (MqC.holds_tall _ _ _).mp ((MqC.holds_imp _ _ _ _).mp h0 hp) .e
  have e := (eq_of_heq ((MqC.holds_eqv_t _ _ _ _).mp hb).2).trans (Mq_top _ _ (Γ := Ctx.nil.text) _ _)
  exact (cast (congrFun e false).symm trivial : False)

theorem MqC_not_TNec : ¬ MqC.Valid TNec := fun h => by
  have hb := (MqC.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e
  have e := (eq_of_heq ((MqC.holds_eqv_t _ _ _ _).mp hb).2).trans (Mq_top _ _ (Γ := Ctx.nil.text) _ _)
  exact (cast (congrFun e false).symm trivial : False)

end Al

namespace Al

/-- The haecceity tower of `𝔐_hw`, with the type quantifiers acting differently at the other world. -/
noncomputable def MhwG (TA TE : (Code Empty → univH.P) → Prop) : Frame where
  U := univH
  eqv := fun a b x y => ((fun w => hrW a x = hrW b y ∧ w = true), false)
  teq := fun a b => ((fun w => if w = true then a = b else a ≠ b), true)
  neg := fun p => ((fun w => ¬ p.1 w), true)
  imp := fun p q => ((fun w => p.1 w → q.1 w), true)
  cnj := fun p q => ((fun w => p.1 w ∧ q.1 w), true)
  dsj := fun p q => ((fun w => p.1 w ∨ q.1 w), true)
  bic := fun p q => ((fun w => p.1 w ↔ q.1 w), true)
  all := fun _ f => ((fun w => ∀ x, (f x).1 w), true)
  ex := fun _ f => ((fun w => ∃ x, (f x).1 w), true)
  tall := fun Q => ((fun w => cond w (∀ a, (Q a).1 true) (TA Q)), true)
  tex := fun Q => ((fun w => cond w (∃ a, (Q a).1 true) (TE Q)), true)
  hneg := fun _ => Iff.rfl
  himp := fun _ _ => Iff.rfl
  hcnj := fun _ _ => Iff.rfl
  hdsj := fun _ _ => Iff.rfl
  hbic := fun _ _ => Iff.rfl
  hall := fun _ _ => Iff.rfl
  hex := fun _ _ => Iff.rfl
  htall := fun _ => Iff.rfl
  htex := fun _ => Iff.rfl

section MhwG
variable (TA TE : (Code Empty → univH.P) → Prop)

theorem MhwG_model : (MhwG TA TE).IsModelPIm :=
  (MhwG TA TE).model_of_equiv (fun a b => show (if true = true then a = b else a ≠ b) ↔ a = b by simp)
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => ⟨h.1.symm, rfl⟩) (fun _ _ _ _ _ _ h1 h2 => ⟨h1.1.trans h2.1, rfl⟩)

theorem MhwG_Hae : (MhwG TA TE).Valid Hae := by
  intro ρ env
  refine ((MhwG TA TE).holds_tall _ _ _).mpr fun a => ((MhwG TA TE).holds_all _ _ _ _).mpr fun x => ?_
  exact ((MhwG TA TE).holds_eqv _ _ _ _ _ _).mpr ⟨(hrW_hae a x).symm, rfl⟩

theorem MhwG_LLEqv : (MhwG TA TE).Valid LLEqv := by
  intro ρ env
  refine ((MhwG TA TE).holds_tall _ _ _).mpr fun a => ?_
  refine ((MhwG TA TE).holds_all _ _ _ _).mpr fun x => ((MhwG TA TE).holds_all _ _ _ _).mpr fun y => ?_
  refine ((MhwG TA TE).holds_imp _ _ _ _).mpr fun hxy => ?_
  refine ((MhwG TA TE).holds_all _ _ _ _).mpr fun G => ((MhwG TA TE).holds_imp _ _ _ _).mpr fun hGx => ?_
  have e := hrW_inj a _ _ (((MhwG TA TE).holds_eqv _ _ _ _ _ _).mp hxy).1
  have e' : x = y := e
  subst e'
  exact hGx

theorem MhwG_top {n : Nat} {Γ : Ctx n} (ρ : (MhwG TA TE).U.TEnv n) (env : (MhwG TA TE).U.Env Γ ρ) :
    (MhwG TA TE).eval (topF : Fm Γ) ρ env = ((fun _ => True), true) :=
  Prod.ext (funext fun _ => propext ⟨fun _ => trivial, fun _ h => (h ((fun _ => False), true) : False)⟩) rfl

end MhwG

/-- `𝔐_hw,A`: as `𝔐_q,A`. -/
noncomputable abbrev MhwA : Frame := MhwG (fun _ => False) (fun _ => True)
/-- `𝔐_hw,C`: as `𝔐_q,C`. -/
noncomputable abbrev MhwC : Frame := MhwG (fun _ => True) (fun _ => False)

theorem MhwA_not_TBF : ¬ ∀ χ, TBFSch χ → MhwA.Valid χ := fun h => by
  have h0 := h _ ⟨topF, rfl⟩ (fun i => i.elim0) ()
  have hb := (MhwA.holds_imp _ _ _ _).mp h0 ((MhwA.holds_tall _ _ _).mpr fun a =>
    (MhwA.holds_eqv_t _ _ _ _).mpr ⟨rfl, rfl⟩)
  have e := (hrW_inj .t _ _ ((MhwA.holds_eqv_t _ _ _ _).mp hb).1).trans (MhwG_top _ _ (Γ := Ctx.nil) _ _)
  exact (cast (congrFun (congrArg Prod.fst e) false).symm trivial : False)

theorem MhwC_not_TCBF : ¬ ∀ χ, TCBFSch χ → MhwC.Valid χ := fun h => by
  have h0 := h _ ⟨Tm.tex (Tm.teq tv1 tv0), rfl⟩ (fun i => i.elim0) ()
  have hv : MhwC.eval (Tm.tall (Tm.tex (Tm.teq tv1 tv0)) : Fm Ctx.nil) (fun i => i.elim0) () = ((fun _ => True), true) :=
    Prod.ext (funext fun w => by
      cases w
      · exact propext ⟨fun _ => trivial, fun _ => trivial⟩
      · exact propext ⟨fun _ => trivial, fun _ a => ⟨a, show (if true = true then a = a else a ≠ a) by simp⟩⟩) rfl
  have hp : MhwC.Holds (boxF (Tm.tall (Tm.tex (Tm.teq tv1 tv0))) : Fm Ctx.nil) (fun i => i.elim0) () :=
    (MhwC.holds_eqv_t _ _ _ _).mpr ⟨congrArg (hrW .t) (hv.trans (MhwG_top _ _ (Γ := Ctx.nil) _ _).symm), rfl⟩
  have hb := (MhwC.holds_tall _ _ _).mp ((MhwC.holds_imp _ _ _ _).mp h0 hp) .e
  have e := (hrW_inj .t _ _ ((MhwC.holds_eqv_t _ _ _ _).mp hb).1).trans (MhwG_top _ _ (Γ := Ctx.nil.text) _ _)
  exact (cast (congrFun (congrArg Prod.fst e) false).symm trivial : False)

theorem MhwC_not_TNec : ¬ MhwC.Valid TNec := fun h => by
  have hb := (MhwC.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e
  have e := (hrW_inj .t _ _ ((MhwC.holds_eqv_t _ _ _ _).mp hb).1).trans (MhwG_top _ _ (Γ := Ctx.nil.text) _ _)
  exact (cast (congrFun (congrArg Prod.fst e) false).symm trivial : False)


theorem Mhw_TNec : MhwF.Valid TNec := by
  intro ρ env
  refine (MhwF.holds_tall _ _ _).mpr fun a => ?_
  have hv : MhwF.eval (Tm.tex (Tm.teq tv1 tv0) : Fm Ctx.nil.text) (scons a ρ) env = ((fun _ => True), true) := by
    refine Prod.ext (funext fun w => propext ⟨fun _ => trivial, fun _ => ?_⟩) rfl
    cases w
    · have hne : ∃ b : Code Empty, a ≠ b := by
        cases a
        · exact ⟨.t, fun h => nomatch h⟩
        · exact ⟨.e, fun h => nomatch h⟩
        · exact ⟨.e, fun h => nomatch h⟩
        · exact ⟨.e, fun h => nomatch h⟩
      obtain ⟨b, hb⟩ := hne
      exact ⟨b, show (if false = true then a = b else a ≠ b) by simp; exact hb⟩
    · exact ⟨a, show (if true = true then a = a else a ≠ a) by simp⟩
  exact (MhwF.holds_eqv_t _ _ _ _).mpr ⟨congrArg (hrW .t) (hv.trans (Mhw_topF (Γ := Ctx.nil.text) _ _).symm), rfl⟩

/-! ### `𝔐_cq,A` and `𝔐_cq,C`: Collapse without T, and without TBF or TCBF (PI⁻)

Two worlds; the propositions true at the actual world, together with the proposition `p₀` true only
at the other world, are identified with each other; nothing else is identified with anything but
itself. The type quantifiers act at the other world as in `𝔐_q,A` and `𝔐_q,C`. -/

def p0Q : Bool → Prop := fun w => w = false

def Scq : (c : Code Empty) → univQ.El c → Prop
  | .t, x => x true ∨ x = p0Q
  | _, _ => False

def McqF (TA TE : (Code Empty → (Bool → Prop)) → Prop) : Frame where
  U := univQ
  eqv := fun a b x y _ => a = b ∧ (HEq x y ∨ (Scq a x ∧ Scq b y))
  teq := fun a b _ => a = b
  neg := fun p w => ¬ p w
  imp := fun p q w => p w → q w
  cnj := fun p q w => p w ∧ q w
  dsj := fun p q w => p w ∨ q w
  bic := fun p q w => p w ↔ q w
  all := fun _ f w => ∀ x, f x w
  ex := fun _ f w => ∃ x, f x w
  tall := fun Q w => cond w (∀ a, Q a true) (TA Q)
  tex := fun Q w => cond w (∃ a, Q a true) (TE Q)
  hneg := fun _ => Iff.rfl
  himp := fun _ _ => Iff.rfl
  hcnj := fun _ _ => Iff.rfl
  hdsj := fun _ _ => Iff.rfl
  hbic := fun _ _ => Iff.rfl
  hall := fun _ _ => Iff.rfl
  hex := fun _ _ => Iff.rfl
  htall := fun _ => Iff.rfl
  htex := fun _ => Iff.rfl

section Mcq
variable (TA TE : (Code Empty → (Bool → Prop)) → Prop)

theorem Mcq_model : (McqF TA TE).IsModelPIm :=
  (McqF TA TE).model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => ⟨rfl, Or.inl HEq.rfl⟩)
    (fun _ _ _ _ h => ⟨h.1.symm, h.2.elim (fun e => Or.inl e.symm) (fun ⟨p, q⟩ => Or.inr ⟨q, p⟩)⟩)
    (fun a b c x y z h1 h2 => by
      obtain ⟨hab, e1⟩ := h1
      obtain ⟨hbc, e2⟩ := h2
      subst hab; subst hbc
      refine ⟨rfl, ?_⟩
      rcases e1 with e1 | ⟨s1, s2⟩ <;> rcases e2 with e2 | ⟨s3, s4⟩
      · exact Or.inl (e1.trans e2)
      · exact Or.inr ⟨eq_of_heq e1 ▸ s3, s4⟩
      · exact Or.inr ⟨s1, eq_of_heq e2 ▸ s2⟩
      · exact Or.inr ⟨s1, s4⟩)

theorem Mcq_top {n : Nat} {Γ : Ctx n} (ρ : (McqF TA TE).U.TEnv n) (env : (McqF TA TE).U.Env Γ ρ) :
    (McqF TA TE).eval (topF : Fm Γ) ρ env = fun _ => True := by
  funext w
  have e := (McqF TA TE).eval_all (Γ := Γ) tyT (.var .here) ρ env
  refine propext ⟨fun _ => trivial, fun _ => ?_⟩
  show ¬ (McqF TA TE).eval (botF : Fm Γ) ρ env w
  rw [botF, e]
  exact fun h => h (fun _ => False)

theorem Mcq_Collapse : (McqF TA TE).Valid Collapse := by
  intro ρ env
  refine ((McqF TA TE).holds_all _ _ _ _).mpr fun p => ((McqF TA TE).holds_imp _ _ _ _).mpr fun hp => ?_
  refine ((McqF TA TE).holds_eqv_t _ _ _ _).mpr ⟨rfl, Or.inr ⟨Or.inl hp, Or.inl ?_⟩⟩
  exact cast (congrFun (Mcq_top TA TE (Γ := Ctx.nil.ext tyT) ρ (env, p)) true).symm trivial

end Mcq

abbrev McqA : Frame := McqF (fun _ => False) (fun _ => True)
abbrev McqC : Frame := McqF (fun _ => True) (fun _ => False)

theorem McqA_not_TBF : ¬ ∀ χ, TBFSch χ → McqA.Valid χ := fun h => by
  have h0 := h _ ⟨Tm.tex botF, rfl⟩ (fun i => i.elim0) ()
  have hv : ∀ a, McqA.eval (Tm.tex (botF : Fm Ctx.nil.text.text) : Fm Ctx.nil.text) (scons a fun i => i.elim0) () = p0Q := by
    intro a; funext w
    cases w
    · exact propext ⟨fun _ => rfl, fun _ => trivial⟩
    · refine propext ⟨fun ⟨b, hb⟩ => ?_, fun h => nomatch h⟩
      exact ((cast (congrFun (McqA.eval_all (Γ := Ctx.nil.text.text) tyT (.var .here) (scons b (scons a fun i => i.elim0)) ()) true) hb : ∀ x : Bool → Prop, x true) (fun _ => False)).elim
  have hp : McqA.Holds (Tm.tall (boxF (Tm.tex botF)) : Fm Ctx.nil) (fun i => i.elim0) () :=
    (McqA.holds_tall _ _ _).mpr fun a => (McqA.holds_eqv_t _ _ _ _).mpr ⟨rfl, Or.inr ⟨Or.inr (hv a),
      Or.inl (cast (congrFun (Mcq_top _ _ (Γ := Ctx.nil.text) _ _) true).symm trivial)⟩⟩
  have hb := (McqA.holds_imp _ _ _ _).mp h0 hp
  rcases ((McqA.holds_eqv_t _ _ _ _).mp hb).2 with e | ⟨s, _⟩
  · have e' := (eq_of_heq e).trans (Mcq_top _ _ (Γ := Ctx.nil) _ _)
    exact (cast (congrFun e' false).symm trivial : False)
  · rcases s with s | s
    · obtain ⟨b, hb⟩ := (s .e : ∃ b, McqA.eval (botF : Fm Ctx.nil.text.text) (scons b (scons .e fun i => i.elim0)) () true)
      exact (cast (congrFun (McqA.eval_all (Γ := Ctx.nil.text.text) tyT (.var .here) (scons b (scons .e fun i => i.elim0)) ()) true) hb : ∀ x : Bool → Prop, x true) (fun _ => False)
    · exact (cast (congrFun s false).symm rfl : False)

theorem McqC_not_TCBF : ¬ ∀ χ, TCBFSch χ → McqC.Valid χ := fun h => by
  have h0 := h _ ⟨botF, rfl⟩ (fun i => i.elim0) ()
  have hv : McqC.eval (Tm.tall (botF : Fm Ctx.nil.text) : Fm Ctx.nil) (fun i => i.elim0) () = p0Q := by
    funext w
    cases w
    · exact propext ⟨fun _ => rfl, fun _ => trivial⟩
    · refine propext ⟨fun h => ?_, fun h => nomatch h⟩
      exact ((cast (congrFun (McqC.eval_all (Γ := Ctx.nil.text) tyT (.var .here) (scons .e fun i => i.elim0) ()) true) (h .e) : ∀ x : Bool → Prop, x true) (fun _ => False)).elim
  have hp : McqC.Holds (boxF (Tm.tall (botF : Fm Ctx.nil.text)) : Fm Ctx.nil) (fun i => i.elim0) () :=
    (McqC.holds_eqv_t _ _ _ _).mpr ⟨rfl, Or.inr ⟨Or.inr hv, Or.inl (cast (congrFun (Mcq_top _ _ (Γ := Ctx.nil) _ _) true).symm trivial)⟩⟩
  have hb := (McqC.holds_tall _ _ _).mp ((McqC.holds_imp _ _ _ _).mp h0 hp) .e
  rcases ((McqC.holds_eqv_t _ _ _ _).mp hb).2 with e | ⟨s, _⟩
  · have e' := (eq_of_heq e).trans (Mcq_top _ _ (Γ := Ctx.nil.text) _ _)
    exact (cast (congrFun e' true).symm trivial : (McqC.eval (botF : Fm Ctx.nil.text) _ () true))
      |> fun hb' => (cast (congrFun (McqC.eval_all (Γ := Ctx.nil.text) tyT (.var .here) (scons .e fun i => i.elim0) ()) true) hb' :
        ∀ x : Bool → Prop, x true) (fun _ => False)
  · rcases s with s | s
    · exact (cast (congrFun (McqC.eval_all (Γ := Ctx.nil.text) tyT (.var .here) (scons .e fun i => i.elim0) ()) true) s :
        ∀ x : Bool → Prop, x true) (fun _ => False)
    · have := congrFun s false
      exact (cast this.symm rfl : McqC.eval (botF : Fm Ctx.nil.text) _ () false) |> fun hb' =>
        (cast (congrFun (McqC.eval_all (Γ := Ctx.nil.text) tyT (.var .here) (scons .e fun i => i.elim0) ()) false) hb' :
          ∀ x : Bool → Prop, x false) (fun _ => False)

end Al

/-! ## The Barcan formulas and Type Necessitism in `𝔐_tot` -/

theorem Mtot_TBF : ∀ χ, TBFSch χ → Mtot.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env _
  exact (Mtot.holds_eqv tyT tyT _ _ _ _).mpr ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩

theorem Mtot_TCBF : ∀ χ, TCBFSch χ → Mtot.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env _ a
  exact (Mtot.holds_eqv tyT tyT _ _ _ _).mpr ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩

theorem Mtot_TNec : Mtot.Valid TNec := by
  intro ρ env a
  exact (Mtot.holds_eqv tyT tyT _ _ _ _).mpr ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩

end PIF
