import PIClass
import PIAlgIModels

/-!
# Models of PI + Classicism

Models which settle questions about PIᶜ (PI plus Classicism): the intensional-function model
`𝔐_if`, and models with two worlds in which identity across types holds at one world only.
-/
set_option autoImplicit false

namespace PIF

/-! ## `𝔐_if` is a model of Classicism -/

namespace AlI
namespace Frame
variable (F : Frame)

theorem valid_closeCtx : ∀ {n : Nat} (Γ : Ctx n) (χ : Fm Γ), (∀ ρ env, F.Holds χ ρ env) → F.Valid (closeCtx Γ χ)
  | _, .nil, _, h => h
  | _, .ext Γ σ, χ, h => valid_closeCtx Γ (Tm.all σ χ) fun ρ env => (F.holds_all σ χ ρ env).mpr fun v => h ρ (env, v)
  | _, .text Γ, χ, h => valid_closeCtx Γ (Tm.tall χ) fun ρ env => (F.holds_tall χ ρ env).mpr fun a => h (scons a ρ) env

end Frame

set_option maxHeartbeats 4000000 in
theorem Mif_Class : ∀ χ, ClassSch χ → MifF.Valid χ := by
  have ref : ∀ a x, MifF.eqv a a x x := fun _ _ => ⟨rfl, HEq.rfl⟩
  rintro _ (⟨n, Γ, φ, ψ, hp, rfl⟩ | ⟨n, Γ, σ, φ, ψ, hp, rfl⟩)
  · have hv := MifF.soundness Mif_model (fun χ (h : χ = LLEqv) => h ▸ Mif_LLEqv) hp
    refine MifF.valid_closeCtx Γ _ fun ρ env => ?_
    have e : MifF.eval φ ρ env = MifF.eval ψ ρ env := propext (hv ρ env)
    refine (MifF.holds_eqv tyT tyT φ ψ ρ env).mpr ?_
    show MifF.eqv .t .t (MifF.eval φ ρ env) (MifF.eval ψ ρ env)
    rw [e]; exact ref _ _
  · have hv := MifF.soundness Mif_model (fun χ (h : χ = LLEqv) => h ▸ Mif_LLEqv) hp
    refine MifF.valid_closeCtx Γ _ fun ρ env => ?_
    have e : MifF.eval (Tm.lam σ φ : Tm Γ σ.pred.1) ρ env = MifF.eval (Tm.lam σ ψ : Tm Γ σ.pred.1) ρ env :=
      Prod.ext (funext fun v => propext (hv ρ (env, v))) rfl
    refine (MifF.holds_eqv σ.pred σ.pred _ _ ρ env).mpr ?_
    have key : ∀ x y : MifF.U.CatVal σ.pred.1 ρ, x = y →
        MifF.eqv (MifF.U.code σ.pred.1 ρ) (MifF.U.code σ.pred.1 ρ) (cast (Univ.El_code ρ σ.pred.2).symm x)
          (cast (Univ.El_code ρ σ.pred.2).symm y) := by
      intro x y h; cases h; exact ⟨rfl, HEq.rfl⟩
    exact key _ _ e

end AlI

/-! ## Two-world models of Classicism -/

namespace Wd
namespace Frame
variable (F : Frame)

theorem isModelAt_of (hr : ∀ a x w, F.eqv a a x x w) (hs : ∀ a b x y w, F.eqv a b x y w → F.eqv b a y x w)
    (ht : ∀ a b c x y z w, F.eqv a b x y w → F.eqv b c y z w → F.eqv a c x z w)
    (hT : ∀ a b w, F.teq a b w ↔ a = b) : F.IsModelAt where
  refEqv := by
    intro w ρ env
    refine (F.holdsAt_tall _ _ _ w).mpr fun a => (F.holdsAt_all _ _ _ _ w).mpr fun x => ?_
    exact (F.holdsAt_eqv _ _ _ _ _ _ w).mpr (hr _ _ _)
  symEqv := by
    intro w ρ env
    refine (F.holdsAt_tall _ _ _ w).mpr fun a => (F.holdsAt_tall _ _ _ w).mpr fun b => ?_
    refine (F.holdsAt_all _ _ _ _ w).mpr fun x => (F.holdsAt_all _ _ _ _ w).mpr fun y => ?_
    refine (F.holdsAt_imp _ _ _ _ w).mpr fun h => ?_
    exact (F.holdsAt_eqv _ _ _ _ _ _ w).mpr (hs _ _ _ _ _ ((F.holdsAt_eqv _ _ _ _ _ _ w).mp h))
  transEqv := by
    intro w ρ env
    refine (F.holdsAt_tall _ _ _ w).mpr fun a => (F.holdsAt_tall _ _ _ w).mpr fun b =>
      (F.holdsAt_tall _ _ _ w).mpr fun c => ?_
    refine (F.holdsAt_all _ _ _ _ w).mpr fun x => (F.holdsAt_all _ _ _ _ w).mpr fun y =>
      (F.holdsAt_all _ _ _ _ w).mpr fun z => ?_
    refine (F.holdsAt_imp _ _ _ _ w).mpr fun h => ?_
    have h1 := (F.holdsAt_eqv (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv2 tv1
      (.var (.there (.there .here))) (.var (.there .here)) (scons c (scons b (scons a ρ))) (((env, x), y), z) w).mp h.1
    have h2 := (F.holdsAt_eqv (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv1 tv0
      (.var (.there .here)) (.var .here) (scons c (scons b (scons a ρ))) (((env, x), y), z) w).mp h.2
    exact (F.holdsAt_eqv _ _ _ _ _ _ w).mpr (ht _ _ _ _ _ _ _ h1 h2)
  refTeq := by
    intro w ρ env
    exact (F.holdsAt_tall _ _ _ w).mpr fun a => (F.holdsAt_teq _ _ _ _ w).mpr ((hT a a w).mpr rfl)
  llTeq := by
    intro n Γ Q w ρ env
    refine (F.holdsAt_tall _ _ _ w).mpr fun a => (F.holdsAt_tall _ _ _ w).mpr fun b => ?_
    refine (F.holdsAt_imp _ _ _ _ w).mpr fun hab => ?_
    have hab' : a = b := (hT a b w).mp ((F.holdsAt_teq (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env w).mp hab)
    subst hab'
    refine (F.holdsAt_imp _ _ _ _ w).mpr fun hq => ?_
    have e1 : HEq (F.eval (Tm.tapp Q.twk.twk tv1) (scons a (scons a ρ)) env)
        (F.eval Q.twk.twk (scons a (scons a ρ)) env a) :=
      F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv1 (scons a (scons a ρ)) env
    have e2 : HEq (F.eval (Tm.tapp Q.twk.twk tv0) (scons a (scons a ρ)) env)
        (F.eval Q.twk.twk (scons a (scons a ρ)) env a) :=
      F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv0 (scons a (scons a ρ)) env
    exact cast (F.holdsAt_of_heq (e1.trans e2.symm) w) hq

theorem LLEqv_validAt_of (hl : ∀ a x y w, F.eqv a a x y w → x = y) : F.ValidAt LLEqv := by
  intro w ρ env
  refine (F.holdsAt_tall _ _ _ w).mpr fun a => ?_
  refine (F.holdsAt_all _ _ _ _ w).mpr fun x => (F.holdsAt_all _ _ _ _ w).mpr fun y => ?_
  refine (F.holdsAt_imp _ _ _ _ w).mpr fun hxy => ?_
  refine (F.holdsAt_all _ _ _ _ w).mpr fun G => (F.holdsAt_imp _ _ _ _ w).mpr fun hGx => ?_
  have e := hl _ _ _ _ ((F.holdsAt_eqv _ _ _ _ _ _ w).mp hxy)
  have e' : x = y := eq_of_heq ((cast_heq _ _).symm.trans ((heq_of_eq e).trans (cast_heq _ _)))
  subst e'
  exact hGx

/-- Where identity of propositions is identity, `□φ` is truth at every world. -/
theorem box_all (hb : ∀ p q, F.eqv .t .t p q F.U.w0 → p = q) {n : Nat} {Γ : Ctx n} (φ : Fm Γ)
    (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (h : F.Holds (boxF φ) ρ env) (w : F.U.W) : F.HoldsAt φ ρ env w := by
  have e := hb _ _ ((F.holdsAt_eqv_t φ topF ρ env F.U.w0).mp h)
  show F.U.ap (F.eval φ ρ env) w
  rw [e, F.eval_topF]; exact trivial

/-- A frame in which the identity axioms and LL≡ hold at every world is a model of Classicism. -/
theorem Class_valid_of (hM : F.IsModelAt) (hLL : F.ValidAt LLEqv) (ref : ∀ a x, F.eqv a a x x F.U.w0) :
    ∀ χ, ClassSch χ → F.Valid χ := by
  have sound : ∀ {n : Nat} {Γ : Ctx n} {θ : Fm Γ}, PIP Γ θ → F.ValidAt θ := fun h =>
    F.soundnessAt hM (fun χ (e : χ = LLEqv) => e ▸ hLL) h
  rintro _ (⟨n, Γ, φ, ψ, hp, rfl⟩ | ⟨n, Γ, σ, φ, ψ, hp, rfl⟩)
  · refine F.valid_closeCtx Γ _ fun ρ env => ?_
    have e : F.eval φ ρ env = F.eval ψ ρ env := funext fun w => propext (sound hp w ρ env)
    refine (F.holdsAt_eqv_t φ ψ ρ env _).mpr ?_
    rw [e]; exact ref _ _
  · refine F.valid_closeCtx Γ _ fun ρ env => ?_
    have e : F.eval (Tm.lam σ φ : Tm Γ σ.pred.1) ρ env = F.eval (Tm.lam σ ψ : Tm Γ σ.pred.1) ρ env :=
      funext fun v => funext fun w => propext (sound hp w ρ (env, v))
    refine (F.holds_eqv σ.pred σ.pred _ _ ρ env).mpr ?_
    have key : ∀ x y : F.U.CatVal σ.pred.1 ρ, x = y →
        F.eqv (F.U.code σ.pred.1 ρ) (F.U.code σ.pred.1 ρ) (cast (Univ.El_code ρ σ.pred.2).symm x)
          (cast (Univ.El_code ρ σ.pred.2).symm y) F.U.w0 := by
      intro x y h; subst h; exact ref _ _
    exact key _ _ e

end Frame

/-! ### `𝔐_ie,c`: Int≈ without Ext≈, in PIᶜ

Two worlds. The entity is identified with the one item of a base type `d` at the actual world only;
otherwise identity is identity, and `≈` is identity of types. So `e` and `d` are coextensive but not
necessarily coextensive: Ext≈ fails, while Int≈ holds. -/

def univIE : Univ where
  W := Bool
  w0 := true
  E := Unit
  Base := Unit
  B := fun _ => Unit
  neE := ⟨()⟩
  neB := fun _ => ⟨()⟩

def crossIE (a b : Code Unit) : Prop := (a = .e ∧ b = .base ()) ∨ (a = .base () ∧ b = .e)

def MieCF : Frame where
  U := univIE
  eqv := fun a b x y w => (a = b ∧ HEq x y) ∨ (w = true ∧ crossIE a b)
  teq := fun a b _ => a = b

theorem crossIE_symm {a b : Code Unit} (h : crossIE a b) : crossIE b a := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inl ⟨h2, h1⟩
theorem crossIE_ne {a b : Code Unit} (h : crossIE a b) : a ≠ b := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> intro h <;> cases h

theorem MieC_trans : ∀ a b c x y z w, MieCF.eqv a b x y w → MieCF.eqv b c y z w → MieCF.eqv a c x z w := by
  intro a b c x y z w h1 h2
  rcases h1 with ⟨rfl, h1⟩ | ⟨hw, hx⟩
  · rcases h2 with ⟨rfl, h2⟩ | ⟨hw, hx⟩
    · exact Or.inl ⟨rfl, h1.trans h2⟩
    · exact Or.inr ⟨hw, hx⟩
  · rcases h2 with ⟨rfl, _⟩ | ⟨_, hy⟩
    · exact Or.inr ⟨hw, hx⟩
    · refine Or.inl ?_
      rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hy with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;> cases h
      · exact ⟨rfl, by cases x; cases z; rfl⟩
      · exact ⟨rfl, by cases x; cases z; rfl⟩

theorem MieC_isModelAt : MieCF.IsModelAt :=
  MieCF.isModelAt_of (fun _ _ _ => Or.inl ⟨rfl, HEq.rfl⟩)
    (fun _ _ _ _ _ h => h.elim (fun h => Or.inl ⟨h.1.symm, h.2.symm⟩) (fun h => Or.inr ⟨h.1, crossIE_symm h.2⟩))
    MieC_trans (fun _ _ _ => Iff.rfl)

theorem MieC_eq : ∀ a x y w, MieCF.eqv a a x y w → x = y := fun _ _ _ _ h =>
  h.elim (fun h => eq_of_heq h.2) (fun h => (crossIE_ne h.2 rfl).elim)

theorem MieC_model : MieCF.IsModelPIm :=
  MieCF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => Or.inl ⟨rfl, HEq.rfl⟩)
    (fun _ _ _ _ h => h.elim (fun h => Or.inl ⟨h.1.symm, h.2.symm⟩) (fun h => Or.inr ⟨h.1, crossIE_symm h.2⟩))
    (fun a b c x y z h1 h2 => MieC_trans a b c x y z _ h1 h2)

theorem MieC_LLEqv : MieCF.Valid LLEqv := fun ρ env => MieCF.LLEqv_validAt_of MieC_eq _ ρ env

theorem MieC_Class : ∀ χ, ClassSch χ → MieCF.Valid χ :=
  MieCF.Class_valid_of MieC_isModelAt (MieCF.LLEqv_validAt_of MieC_eq) fun _ _ => Or.inl ⟨rfl, HEq.rfl⟩

theorem MieC_not_ExtT : ¬ MieCF.Valid ExtT := fun h => by
  have h0 := (MieCF.holds_tall _ _ _).mp ((MieCF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) (.base ())
  have hT := (MieCF.holds_imp _ _ _ _).mp h0 ((MieCF.holds_conj _ _ _ _).mpr
    ⟨(MieCF.holds_all _ _ _ _).mpr fun x => (MieCF.holds_ex _ _ _ _).mpr
        ⟨(), (MieCF.holds_eqv _ _ _ _ _ _).mpr (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)⟩,
     (MieCF.holds_all _ _ _ _).mpr fun y => (MieCF.holds_ex _ _ _ _).mpr
        ⟨(), (MieCF.holds_eqv _ _ _ _ _ _).mpr (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)⟩⟩)
  exact nomatch (show (Code.e : Code Unit) = .base () from (MieCF.holds_teq _ _ _ _).mp hT)

theorem MieC_IntT : MieCF.Valid IntT := by
  intro ρ env
  refine (MieCF.holds_tall _ _ _).mpr fun a => (MieCF.holds_tall _ _ _).mpr fun b => ?_
  refine (MieCF.holds_imp _ _ _ _).mpr fun h => (MieCF.holds_teq _ _ _ _).mpr ?_
  have hb : ∀ p q, MieCF.eqv .t .t p q MieCF.U.w0 → p = q := fun p q h => MieC_eq _ _ _ _ h
  have hs := MieCF.box_all hb _ _ _ ((MieCF.holds_conj _ _ _ _).mp h).1 false
  have x0 := Classical.choice (Univ.El_nonempty (U := MieCF.U) a)
  obtain ⟨y, hy⟩ := (MieCF.holdsAt_ex _ _ _ _ false).mp ((MieCF.holdsAt_all _ _ _ _ false).mp hs x0)
  rcases (MieCF.holdsAt_eqv _ _ _ _ _ _ false).mp hy with ⟨e, _⟩ | ⟨hw, _⟩
  · exact e
  · exact (Bool.false_ne_true hw).elim

end Wd

end PIF
