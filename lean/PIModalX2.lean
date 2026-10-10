import PIModalX

/-!
# NI×, ND×, and Functional Choice, with Disjoint, the congruence principles, and Haecceitism

Further models, settling which principles follow from which, once one or more of NI×, ND× and
Functional Choice are added, together with one of Disjoint, Cong, PCong→, PCong← and Haecceitism,
to PI or to PIᶜ.
-/
set_option autoImplicit false

namespace PIF
open Tm

/-! ## Tagged models: NI× and ND× hold, the Identity Identity fails -/

namespace Tg

theorem Mz_NIX : MzF.Valid NIX := by
  intro ρ env a b
  refine (MzF.holds_all _ _ _ _).mpr fun x => (MzF.holds_all _ _ _ _).mpr fun y h => ?_
  exact (MzF.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl)⟩

theorem Mz_NDX : MzF.Valid NDX := by
  intro ρ env a b
  refine (MzF.holds_all _ _ _ _).mpr fun x => (MzF.holds_all _ _ _ _).mpr fun y h => ?_
  exact (MzF.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl)⟩

/-- In `𝔐_int0`, `x ≡ y` is not quantified and `∀F(Fx → Fy)` is, so they are never identical. -/
theorem Mz_not_IdId : ¬ MzF.Valid IdId := fun h => by
  have h0 := (MzF.holds_all _ _ _ _).mp ((MzF.holds_all _ _ _ _).mp
    ((MzF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have e := eq_of_heq ((MzF.holds_eqv_t _ _ _ _).mp h0).2
  have h1 := congrArg Prod.snd e
  have h2 := MzF.eval_all_snd (Γ := ((Ctx.nil.text).ext tv0).ext tv0) tv0.pred
    (Tm.imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))
    (scons .e fun i => i.elim0) (((), ()), ())
  exact Bool.noConfusion (h1.trans h2 : true = false)

theorem Mht_NIX : MhtF.Valid NIX := by
  intro ρ env a b
  refine (MhtF.holds_all _ _ _ _).mpr fun x => (MhtF.holds_all _ _ _ _).mpr fun y h => ?_
  exact (MhtF.holds_eqv_t _ _ _ _).mpr (congrArg (fun p => (⟨.t, p⟩ : Σ c : Code univU.Base, univU.El c))
    (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl))

theorem Mht_NDX : MhtF.Valid NDX := by
  intro ρ env a b
  refine (MhtF.holds_all _ _ _ _).mpr fun x => (MhtF.holds_all _ _ _ _).mpr fun y h => ?_
  exact (MhtF.holds_eqv_t _ _ _ _).mpr (congrArg (fun p => (⟨.t, p⟩ : Σ c : Code univU.Base, univU.El c))
    (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl))

theorem Mht_not_IdId : ¬ MhtF.Valid IdId := fun h => by
  have h0 := (MhtF.holds_all _ _ _ _).mp ((MhtF.holds_all _ _ _ _).mp
    ((MhtF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have e := eq_of_heq (Sigma.mk.inj ((MhtF.holds_eqv_t _ _ _ _).mp h0)).2
  have h1 := congrArg Prod.snd e
  have h2 := MhtF.eval_all_snd (Γ := ((Ctx.nil.text).ext tv0).ext tv0) tv0.pred
    (Tm.imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))
    (scons .e fun i => i.elim0) (((), ()), ())
  exact Bool.noConfusion (h1.trans h2 : true = false)

end Tg

/-! ## Worlds -/

namespace Wd
namespace Frame
variable (F : Frame)

theorem tr_Disjoint : F.Tr Disjoint ↔ ∀ a b, ¬ F.teq a b F.U.w0 →
    ∀ (x : F.U.El a) (y : F.U.El b), ¬ F.eqv a b x y F.U.w0 := Iff.rfl
theorem tr_NITeq : F.Tr NITeq ↔ ∀ a b, F.teq a b F.U.w0 →
    F.eqv .t .t (F.teq a b) (F.eval (topF : Fm Ctx.nil) (fun i => i.elim0) ()) F.U.w0 := Iff.rfl
theorem tr_NIEqv : F.Tr NIEqv ↔ ∀ a (x y : F.U.El a), F.eqv a a x y F.U.w0 →
    F.eqv .t .t (F.eqv a a x y) (F.eval (topF : Fm Ctx.nil) (fun i => i.elim0) ()) F.U.w0 := Iff.rfl

end Frame

/-! ### More about `𝔐_ie,d` -/

theorem MieD_Disjoint : MieDF.Valid Disjoint :=
  (MieDF.valid_iff_tr _).mpr <| MieDF.tr_Disjoint.mpr fun _ _ hn _ _ h =>
    h.elim (fun h => hn h.1) (fun h => Bool.noConfusion h.1)

theorem MieD_Cong : MieDF.Valid Cong :=
  (MieDF.valid_iff_tr _).mpr <| MieDF.tr_Cong.mpr fun a b c d f g x y ⟨h1, h2⟩ => by
    rcases h1 with ⟨e1, hf⟩ | ⟨hw, _⟩
    · rcases h2 with ⟨_, hx⟩ | ⟨hw, _⟩
      · injection e1 with ea ec
        subst ea; subst ec
        have ef : f = g := eq_of_heq hf
        have ex : x = y := eq_of_heq hx
        subst ef; subst ex
        exact Or.inl ⟨rfl, HEq.rfl⟩
      · exact absurd hw (fun h => Bool.noConfusion h)
    · exact absurd hw (fun h => Bool.noConfusion h)

theorem MieD_PExt : MieDF.Valid PExt :=
  (MieDF.valid_iff_tr _).mpr <| MieDF.tr_PExt.mpr fun a c d f g h => by
    have x0 := Classical.choice (Univ.El_nonempty (U := univIE) a)
    have hp : ∀ x, c = d ∧ HEq (f x) (g x) := fun x =>
      (h x).elim id (fun h => absurd h.1 (fun h => Bool.noConfusion h))
    have ecd : c = d := (hp x0).1
    subst ecd
    have ef : f = g := funext fun x => eq_of_heq (hp x).2
    subst ef
    exact Or.inl ⟨rfl, HEq.rfl⟩

theorem MieD_NDTeq : MieDF.Valid NDTeq := MieDF.NDTeq_of (fun _ => Or.inl ⟨rfl, HEq.rfl⟩) fun _ _ _ => Iff.rfl
theorem MieD_TBF : ∀ χ, TBFSch χ → MieDF.Valid χ :=
  MieDF.TBF_of fun _ _ => ⟨fun h => MieD_eq _ _ _ _ h, fun h => h ▸ Or.inl ⟨rfl, HEq.rfl⟩⟩

/-! ### `𝔐_hae,ie,d`: as `𝔐_hae,ie`, with the entity and the item of `d` identified at the other world only -/

noncomputable def MhieDF : Frame where
  U := univHI
  eqv := fun a b x y w => rootI a x = rootI b y ∨ (w = false ∧ crossI (rootI a x) (rootI b y))
  teq := fun a b _ => a = b

theorem MhieD_symm : ∀ a b x y w, MhieDF.eqv a b x y w → MhieDF.eqv b a y x w := fun _ _ _ _ _ h =>
  h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.1, crossI_symm h.2⟩)

theorem MhieD_trans : ∀ a b c x y z w, MhieDF.eqv a b x y w → MhieDF.eqv b c y z w → MhieDF.eqv a c x z w := by
  intro a b c x y z w h1 h2
  rcases h1 with h1 | ⟨hw, h1⟩ <;> rcases h2 with h2 | ⟨_, h2⟩
  · exact Or.inl (h1.trans h2)
  · rw [← h1] at h2; exact Or.inr ⟨by assumption, h2⟩
  · rw [h2] at h1; exact Or.inr ⟨hw, h1⟩
  · exact Or.inl (crossI_trans h1 h2)

theorem MhieD_eq : ∀ a x y w, MhieDF.eqv a a x y w → x = y := by
  intro a x y w h
  rcases h with h | ⟨_, h⟩
  · exact rootI_inj a x y h
  · have f1 := foot_rootI a x
    have f2 := foot_rootI a y
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at f1 <;> rw [h2] at f2 <;> rw [← f2] at f1 <;> cases f1

theorem MhieD_isModelAt : MhieDF.IsModelAt :=
  MhieDF.isModelAt_of (fun _ _ _ => Or.inl rfl) MhieD_symm MhieD_trans (fun _ _ _ => Iff.rfl)

theorem MhieD_model : MhieDF.IsModelPIm :=
  MhieDF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => Or.inl rfl) (fun a b x y h => MhieD_symm a b x y _ h)
    (fun a b c x y z h1 h2 => MhieD_trans a b c x y z _ h1 h2)

theorem MhieD_LLEqv : MhieDF.Valid LLEqv := fun ρ env => MhieDF.LLEqv_validAt_of MhieD_eq _ ρ env

theorem MhieD_Class : ∀ χ, ClassSch χ → MhieDF.Valid χ :=
  MhieDF.Class_valid_of MhieD_isModelAt (MhieDF.LLEqv_validAt_of MhieD_eq) fun _ _ => Or.inl rfl

theorem MhieD_Hae : MhieDF.Valid Hae := by
  intro ρ env
  show ∀ a (x : univHI.El a), MhieDF.eqv a (.arr a .t) x (fun y w => MhieDF.eqv a a y x w) univHI.w0
  intro a x
  have e : (fun (y : univHI.El a) (w : Bool) => MhieDF.eqv a a y x w) = hcyI a x :=
    funext fun y => funext fun w => propext ⟨fun h => MhieD_eq a y x w h, fun h => h ▸ Or.inl rfl⟩
  refine Or.inl ?_
  exact (rootI_hcy a x).symm.trans (congrArg (rootI (.arr a .t)) e.symm)


theorem MhieD_NIX : MhieDF.Valid NIX :=
  MhieDF.NIX_of (fun _ => Or.inl rfl) fun _ _ _ _ h _ =>
    h.elim Or.inl (fun h => absurd h.1 (fun e => Bool.noConfusion e))
theorem MhieD_not_NDX : ¬ MhieDF.Valid NDX :=
  MhieDF.not_NDX_of (fun _ _ h => MhieD_eq _ _ _ _ h) (a := .e) (b := .base ()) () ()
    (fun h => h.elim (fun h => nomatch congrArg Sigma.fst h) (fun h => Bool.noConfusion h.1)) false
    (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)

/-! ### Haecceity towers with `≈` varying across worlds -/

/-- Identity is sameness of root, at every world; `≈` is given by `Te`. -/
noncomputable def MhTF (Te : Code Empty → Code Empty → Bool → Prop) : Frame where
  U := univHC
  eqv := fun a b x y _ => root a x = root b y
  teq := Te

section MhT
variable (Te : Code Empty → Code Empty → Bool → Prop) (hT : ∀ a b, Te a b true ↔ a = b)
include hT

theorem MhT_model : (MhTF Te).IsModelPIm :=
  (MhTF Te).model_of_equiv hT (fun _ _ => rfl) (fun _ _ _ _ h => h.symm) (fun _ _ _ _ _ _ h1 h2 => h1.trans h2)

omit hT in
theorem MhT_LLEqv : (MhTF Te).Valid LLEqv := fun ρ env =>
  (MhTF Te).LLEqv_validAt_of (fun a x y _ h => root_inj a x y h) _ ρ env

omit hT in
theorem MhT_Hae : (MhTF Te).Valid Hae := by
  intro ρ env
  show ∀ a (x : univHC.El a), root a x = root (.arr a .t) (fun y _ => root a y = root a x)
  intro a x
  have e : (fun (y : univHC.El a) (_ : Bool) => root a y = root a x) = hcy a x :=
    funext fun y => funext fun _ => propext ⟨root_inj a y x, fun h => h ▸ rfl⟩
  have := root_hcy a x
  rw [← e] at this
  exact this.symm

omit hT in
theorem MhT_NIX : (MhTF Te).Valid NIX := (MhTF Te).NIX_of (fun _ => rfl) fun _ _ _ _ h _ => h
omit hT in
theorem MhT_NDX : (MhTF Te).Valid NDX := (MhTF Te).NDX_of (fun _ => rfl) fun _ _ _ _ h _ => h

end MhT

def TeNI (a b : Code Empty) (w : Bool) : Prop := a = b ∧ w = true
def TeND (a b : Code Empty) (w : Bool) : Prop := w = true → a = b

noncomputable abbrev MhNI : Frame := MhTF TeNI
noncomputable abbrev MhND : Frame := MhTF TeND

theorem MhNI_model : MhNI.IsModelPIm := MhT_model TeNI fun _ _ => ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
theorem MhND_model : MhND.IsModelPIm := MhT_model TeND fun _ _ => ⟨fun h => h rfl, fun h _ => h⟩

theorem MhNI_not_NITeq : ¬ MhNI.Valid NITeq := fun hv => by
  have h0 := MhNI.tr_NITeq.mp ((MhNI.valid_iff_tr _).mp hv) .e .e ⟨rfl, rfl⟩
  have e : TeNI .e .e = MhNI.eval (topF : Fm Ctx.nil) (fun i => i.elim0) () := root_inj _ _ _ h0
  have e2 := e.trans (MhNI.eval_topF (Γ := Ctx.nil) _ _)
  exact Bool.false_ne_true (cast (congrFun e2 false).symm trivial).2

theorem MhND_not_NDTeq : ¬ MhND.Valid NDTeq := fun hv => by
  have h0 := MhND.tr_NDTeq.mp ((MhND.valid_iff_tr _).mp hv) .e .t (fun h => nomatch h rfl)
  have e : (fun w => ¬ TeND .e .t w) = MhND.eval (topF : Fm Ctx.nil) (fun i => i.elim0) () := root_inj _ _ _ h0
  have e2 := e.trans (MhND.eval_topF (Γ := Ctx.nil) _ _)
  exact cast (congrFun e2 false).symm trivial (fun h => Bool.noConfusion h)

/-! ### `𝔐_hae,ie⁻`: identity holds only at the actual world -/

def hcyE (a : Code Empty) (z : univHC.El a) : univHC.El (.arr a .t) := fun y w => y = z ∧ w = true

theorem hcyE_inj (a : Code Empty) (z z' : univHC.El a) (h : hcyE a z = hcyE a z') : z = z' :=
  (cast (congrFun (congrFun h z) true) ⟨rfl, rfl⟩).1

noncomputable abbrev rootE := groot univHC.El hcyE

noncomputable def MhEF : Frame where
  U := univHC
  eqv := fun a b x y w => rootE a x = rootE b y ∧ w = true
  teq := fun a b _ => a = b

theorem MhE_model : MhEF.IsModelPIm :=
  MhEF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => ⟨h.1.symm, h.2⟩)
    (fun _ _ _ _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h1.2⟩)

theorem MhE_LLEqv : MhEF.Valid LLEqv := fun ρ env =>
  MhEF.LLEqv_validAt_of (fun a x y _ h => groot_inj hcyE_inj a x y h.1) _ ρ env

theorem MhE_Hae : MhEF.Valid Hae := by
  intro ρ env
  show ∀ a (x : univHC.El a), rootE a x = rootE (.arr a .t) (fun y w => rootE a y = rootE a x ∧ w = true) ∧ true = true
  intro a x
  refine ⟨groot_hae hcyE_inj a x _ ?_, rfl⟩
  funext y w
  exact propext ⟨fun h => ⟨groot_inj hcyE_inj a y x h.1, h.2⟩, fun h => ⟨h.1 ▸ rfl, h.2⟩⟩

theorem MhE_NDX : MhEF.Valid NDX :=
  MhEF.NDX_of (fun _ => ⟨rfl, rfl⟩) fun _ _ _ _ h _ hw => h ⟨hw.1, rfl⟩

theorem MhE_not_NIEqv : ¬ MhEF.Valid NIEqv := fun hv => by
  have h0 := MhEF.tr_NIEqv.mp ((MhEF.valid_iff_tr _).mp hv) .e () () ⟨rfl, rfl⟩
  have e := (groot_inj hcyE_inj _ _ _ h0.1).trans (MhEF.eval_topF (Γ := Ctx.nil) _ _)
  exact Bool.false_ne_true (cast (congrFun e false).symm trivial).2

end Wd

/-! ## `𝔐_q,hae`, and its variant `𝔐_q,hae,C` -/

namespace Al

theorem MqH_NIX : MqHF.Valid NIX := by
  intro ρ env
  refine (MqHF.holds_tall _ _ _).mpr fun a => (MqHF.holds_tall _ _ _).mpr fun b => ?_
  refine (MqHF.holds_all _ _ _ _).mpr fun x => (MqHF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MqHF.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (MqHF.holds_eqv_t _ _ _ _).mpr ((MqH_eqT _ _).mpr ?_)
  exact ((MqHF.eval_eqv _ _ _ _ _ _).trans (funext fun _ => propext ⟨fun _ => trivial, fun _ => hxy⟩)).trans
    (MqH_top (Γ := ((Ctx.nil.text.text).ext tv1).ext tv0) _ _).symm

theorem MqH_NDX : MqHF.Valid NDX := by
  intro ρ env
  refine (MqHF.holds_tall _ _ _).mpr fun a => (MqHF.holds_tall _ _ _).mpr fun b => ?_
  refine (MqHF.holds_all _ _ _ _).mpr fun x => (MqHF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MqHF.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (MqHF.holds_eqv_t _ _ _ _).mpr ((MqH_eqT _ _).mpr ?_)
  refine Eq.trans ?_ (MqH_top (Γ := ((Ctx.nil.text.text).ext tv1).ext tv0) _ _).symm
  funext w
  refine propext ⟨fun _ => trivial, fun _ hw => (MqHF.holds_neg _ _ _).mp hxy ?_⟩
  have e := MqHF.eval_eqv (Γ := ((Ctx.nil.text.text).ext tv1).ext tv0) tv1 tv0 (.var (.there .here)) (.var .here)
    (scons b (scons a ρ)) ((env, x), y)
  have hw' := congrFun e w ▸ hw
  exact cast (congrFun e true).symm hw'

theorem MqH_not_TBF : ¬ ∀ χ, TBFSch χ → MqHF.Valid χ := fun h => by
  have h0 := h _ ⟨topF, rfl⟩ (fun i => i.elim0) ()
  have hb := (MqHF.holds_imp _ _ _ _).mp h0 ((MqHF.holds_tall _ _ _).mpr fun a =>
    (MqHF.holds_eqv_t _ _ _ _).mpr ((MqH_eqT _ _).mpr rfl))
  have e := ((MqH_eqT _ _).mp ((MqHF.holds_eqv_t _ _ _ _).mp hb)).trans (MqH_top (Γ := Ctx.nil) _ _)
  exact (cast (congrFun e false).symm trivial : False)

/-- As `𝔐_q,hae`, except that at the other world type-universal claims are true and
type-existential ones false. -/
noncomputable def MqHCF : Frame where
  U := univQ
  eqv := fun a b x y _ => rootQ a x = rootQ b y
  teq := fun a b _ => a = b
  neg := fun p w => ¬ p w
  imp := fun p q w => p w → q w
  cnj := fun p q w => p w ∧ q w
  dsj := fun p q w => p w ∨ q w
  bic := fun p q w => p w ↔ q w
  all := fun _ f w => ∀ x, f x w
  ex := fun _ f w => ∃ x, f x w
  tall := fun Q w => cond w (∀ a, Q a true) True
  tex := fun Q w => cond w (∃ a, Q a true) False
  hneg := fun _ => Iff.rfl
  himp := fun _ _ => Iff.rfl
  hcnj := fun _ _ => Iff.rfl
  hdsj := fun _ _ => Iff.rfl
  hbic := fun _ _ => Iff.rfl
  hall := fun _ _ => Iff.rfl
  hex := fun _ _ => Iff.rfl
  htall := fun _ => Iff.rfl
  htex := fun _ => Iff.rfl

theorem MqHC_eqT (p q : univQ.P) : MqHCF.U.V (MqHCF.eqv .t .t p q) ↔ p = q :=
  ⟨fun h => eq_of_heq (Sigma.mk.inj h).2, fun h => h ▸ rfl⟩

theorem MqHC_model : MqHCF.IsModelPIm :=
  MqHCF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ _ _ h => h.symm)
    (fun _ _ _ _ _ _ h1 h2 => (h1 : rootQ _ _ = _).trans h2)

theorem MqHC_top {n : Nat} {Γ : Ctx n} (ρ : MqHCF.U.TEnv n) (env : MqHCF.U.Env Γ ρ) :
    MqHCF.eval (topF : Fm Γ) ρ env = fun _ => True := by
  funext w
  have e := MqHCF.eval_all (Γ := Γ) tyT (.var .here) ρ env
  refine propext ⟨fun _ => trivial, fun _ => ?_⟩
  show ¬ MqHCF.eval (botF : Fm Γ) ρ env w
  rw [botF, e]
  exact fun h => h (fun _ => False)

theorem MqHC_LLEqv : MqHCF.Valid LLEqv := by
  intro ρ env
  refine (MqHCF.holds_tall _ _ _).mpr fun a => ?_
  refine (MqHCF.holds_all _ _ _ _).mpr fun x => (MqHCF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MqHCF.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (MqHCF.holds_all _ _ _ _).mpr fun G => (MqHCF.holds_imp _ _ _ _).mpr fun hGx => ?_
  have h : _ := groot_inj hcyQ_inj _ _ _ ((MqHCF.holds_eqv _ _ _ _ _ _).mp hxy)
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans ((heq_of_eq h).trans (cast_heq _ _)))
  subst e
  exact hGx

theorem MqHC_Hae : MqHCF.Valid Hae := by
  intro ρ env
  refine (MqHCF.holds_tall _ _ _).mpr fun a => (MqHCF.holds_all _ _ _ _).mpr fun x => ?_
  refine (MqHCF.holds_eqv _ _ _ _ _ _).mpr (groot_hae hcyQ_inj a x _ ?_)
  funext y w
  exact propext ⟨fun h => groot_inj hcyQ_inj a y x h, fun h => h ▸ rfl⟩

theorem MqHC_NIX : MqHCF.Valid NIX := by
  intro ρ env
  refine (MqHCF.holds_tall _ _ _).mpr fun a => (MqHCF.holds_tall _ _ _).mpr fun b => ?_
  refine (MqHCF.holds_all _ _ _ _).mpr fun x => (MqHCF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MqHCF.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (MqHCF.holds_eqv_t _ _ _ _).mpr ((MqHC_eqT _ _).mpr ?_)
  exact ((MqHCF.eval_eqv _ _ _ _ _ _).trans (funext fun _ => propext ⟨fun _ => trivial, fun _ => hxy⟩)).trans
    (MqHC_top (Γ := ((Ctx.nil.text.text).ext tv1).ext tv0) _ _).symm

theorem MqHC_NDX : MqHCF.Valid NDX := by
  intro ρ env
  refine (MqHCF.holds_tall _ _ _).mpr fun a => (MqHCF.holds_tall _ _ _).mpr fun b => ?_
  refine (MqHCF.holds_all _ _ _ _).mpr fun x => (MqHCF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MqHCF.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (MqHCF.holds_eqv_t _ _ _ _).mpr ((MqHC_eqT _ _).mpr ?_)
  refine Eq.trans ?_ (MqHC_top (Γ := ((Ctx.nil.text.text).ext tv1).ext tv0) _ _).symm
  funext w
  refine propext ⟨fun _ => trivial, fun _ hw => (MqHCF.holds_neg _ _ _).mp hxy ?_⟩
  have e := MqHCF.eval_eqv (Γ := ((Ctx.nil.text.text).ext tv1).ext tv0) tv1 tv0 (.var (.there .here)) (.var .here)
    (scons b (scons a ρ)) ((env, x), y)
  have hw' := congrFun e w ▸ hw
  exact cast (congrFun e true).symm hw'

theorem MqHC_not_TCBF : ¬ ∀ χ, TCBFSch χ → MqHCF.Valid χ := fun h => by
  have h0 := h _ ⟨Tm.tex (Tm.teq tv1 tv0), rfl⟩ (fun i => i.elim0) ()
  have hp : MqHCF.Holds (boxF (Tm.tall (Tm.tex (Tm.teq tv1 tv0))) : Fm Ctx.nil) (fun i => i.elim0) () := by
    refine (MqHCF.holds_eqv_t _ _ _ _).mpr ((MqHC_eqT _ _).mpr ?_)
    refine Eq.trans ?_ (MqHC_top (Γ := Ctx.nil) _ _).symm
    funext w
    cases w
    · exact propext ⟨fun _ => trivial, fun _ => trivial⟩
    · exact propext ⟨fun _ => trivial, fun _ a => ⟨a, rfl⟩⟩
  have hb := (MqHCF.holds_tall _ _ _).mp ((MqHCF.holds_imp _ _ _ _).mp h0 hp) .e
  have e := ((MqHC_eqT _ _).mp ((MqHCF.holds_eqv_t _ _ _ _).mp hb)).trans (MqHC_top (Γ := Ctx.nil.text) _ _)
  exact (cast (congrFun e false).symm trivial : False)

theorem MqHC_not_TNec : ¬ MqHCF.Valid TNec := fun h => by
  have hb := (MqHCF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e
  have e := ((MqHC_eqT _ _).mp ((MqHCF.holds_eqv_t _ _ _ _).mp hb)).trans (MqHC_top (Γ := Ctx.nil.text) _ _)
  exact (cast (congrFun e false).symm trivial : False)

end Al

namespace AlI

/-- In `𝔐_if` propositions are truth values, so Collapse holds. -/
theorem Mif_Collapse : MifF.Valid Collapse := by
  intro ρ env
  refine (MifF.holds_all _ _ _ _).mpr fun p => (MifF.holds_imp _ _ _ _).mpr fun hp => ?_
  have ht : MifF.Holds (topF : Fm (Ctx.nil.ext tyT)) ρ (env, p) :=
    (MifF.holds_neg _ _ _).mpr fun hb => (MifF.holds_all _ _ _ _).mp hb False
  exact (MifF.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq (propext ⟨fun _ => ht, fun _ => hp⟩)⟩

end AlI

end PIF
