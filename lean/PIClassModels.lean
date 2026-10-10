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

/-! ### `𝔐_tw,c`: Twin without Collapse, in PIᶜ

Two worlds. Entities are propositions (sets of worlds), and each type is paired with a twin, got by
swapping its leftmost `e` and `t`; the twins have the very same items, and each item is identified
with itself in the twin type. Identity within a type is identity, and `≈` is identity of types. So
Twin holds, while Collapse fails, since a truth need not hold at the other world. -/

def univTW : Univ where
  W := Bool
  w0 := true
  E := Bool → Prop
  Base := Empty
  B := Empty.elim
  neE := ⟨fun _ => True⟩
  neB := fun b => b.elim

def sw : Code Empty → Code Empty
  | .e => .t
  | .t => .e
  | .base b => b.elim
  | .arr a c => .arr (sw a) c

theorem sw_sw : ∀ a, sw (sw a) = a
  | .e => rfl
  | .t => rfl
  | .base b => b.elim
  | .arr a c => by simp only [sw, sw_sw a]

theorem sw_ne : ∀ a, sw a ≠ a
  | .e => fun h => nomatch h
  | .t => fun h => nomatch h
  | .base b => b.elim
  | .arr a c => fun h => by injection h with h1; exact sw_ne a h1

theorem El_sw : ∀ a, univTW.El (sw a) = univTW.El a
  | .e => rfl
  | .t => rfl
  | .base b => b.elim
  | .arr a c => by show (univTW.El (sw a) → univTW.El c) = (univTW.El a → univTW.El c); rw [El_sw a]

def MtwCF : Frame where
  U := univTW
  eqv := fun a b x y _ => (b = a ∨ b = sw a) ∧ HEq x y
  teq := fun a b _ => a = b

theorem MtwC_sym : ∀ a b x y w, MtwCF.eqv a b x y w → MtwCF.eqv b a y x w := by
  rintro a b x y w ⟨h | h, hx⟩
  · exact ⟨Or.inl h.symm, hx.symm⟩
  · exact ⟨Or.inr (by rw [h]; exact (sw_sw _).symm), hx.symm⟩

theorem MtwC_trans : ∀ a b c x y z w, MtwCF.eqv a b x y w → MtwCF.eqv b c y z w → MtwCF.eqv a c x z w := by
  rintro a b c x y z w ⟨h1, hx⟩ ⟨h2, hy⟩
  refine ⟨?_, hx.trans hy⟩
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (h2.trans h1)
  · exact Or.inr (h2.trans (congrArg sw h1))
  · exact Or.inr (h2.trans h1)
  · exact Or.inl ((h2.trans (congrArg sw h1)).trans (sw_sw a))

theorem MtwC_isModelAt : MtwCF.IsModelAt :=
  MtwCF.isModelAt_of (fun _ _ _ => ⟨Or.inl rfl, HEq.rfl⟩) MtwC_sym MtwC_trans (fun _ _ _ => Iff.rfl)

theorem MtwC_eq : ∀ a x y w, MtwCF.eqv a a x y w → x = y := fun _ _ _ _ h => eq_of_heq h.2

theorem MtwC_model : MtwCF.IsModelPIm :=
  MtwCF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => ⟨Or.inl rfl, HEq.rfl⟩)
    (fun a b x y h => MtwC_sym a b x y _ h) (fun a b c x y z h1 h2 => MtwC_trans a b c x y z _ h1 h2)

theorem MtwC_LLEqv : MtwCF.Valid LLEqv := fun ρ env => MtwCF.LLEqv_validAt_of MtwC_eq _ ρ env

theorem MtwC_Class : ∀ χ, ClassSch χ → MtwCF.Valid χ :=
  MtwCF.Class_valid_of MtwC_isModelAt (MtwCF.LLEqv_validAt_of MtwC_eq) fun _ _ => ⟨Or.inl rfl, HEq.rfl⟩

theorem MtwC_Twin : MtwCF.Valid Twin := by
  intro ρ env
  show ∀ a (x : univTW.El a), ∃ b, ¬ (a = b) ∧ ∃ y : univTW.El b, (b = a ∨ b = sw a) ∧ HEq x y
  intro a x
  exact ⟨sw a, fun h => sw_ne a h.symm, cast (El_sw a).symm x, ⟨Or.inr rfl, (cast_heq _ _).symm⟩⟩

theorem MtwC_not_Collapse : ¬ MtwCF.Valid Collapse := fun h => by
  have h0 := (MtwCF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (fun w => w = true)
  have hb := (MtwCF.holds_imp _ _ _ _).mp h0 (show true = true from rfl)
  have := MtwCF.box_all (fun p q h => MtwC_eq _ _ _ _ h) _ _ _ hb false
  exact Bool.false_ne_true this

/-! ### `𝔐_hae,c`: Haecceitism without Collapse, in PIᶜ

Two worlds, one entity. Each item `x : α` is identified with its haecceity `λy.(y = x)` in `α→t`,
which is identified with its own haecceity in turn, and so on: two items are identified just in
case they have the same root, got by stripping off haecceities. Within a type, identity is
identity. Haecceitism holds, while Collapse fails. -/

open Classical

def univHC : Univ where
  W := Bool
  w0 := true
  E := Unit
  Base := Empty
  B := Empty.elim
  neE := ⟨()⟩
  neB := fun b => b.elim

/-- The haecceity of `z`. -/
def hcy (a : Code Empty) (z : univHC.El a) : univHC.El (.arr a .t) := fun y _ => y = z

theorem hcy_inj {a : Code Empty} {z z' : univHC.El a} (h : hcy a z = hcy a z') : z = z' := by
  have := congrFun (congrFun h z) true
  exact cast this rfl

def csz : Code Empty → Nat
  | .arr a c => csz a + csz c + 1
  | _ => 0

open Classical in
/-- The root of an item: strip off haecceities. -/
noncomputable def root : (a : Code Empty) → univHC.El a → (Σ b : Code Empty, univHC.El b)
  | .arr a .t, f => if h : ∃ z, f = hcy a z then root a (Classical.choose h) else ⟨.arr a .t, f⟩
  | a, x => ⟨a, x⟩

theorem root_sz : ∀ (a : Code Empty) (x : univHC.El a), csz (root a x).1 ≤ csz a
  | .e, _ => Nat.le_refl _
  | .t, _ => Nat.le_refl _
  | .base b, _ => b.elim
  | .arr a .t, f => by
    unfold root
    split
    · rename_i h; have := root_sz a (Classical.choose h); simp only [csz]; omega
    · exact Nat.le_refl _
  | .arr a .e, _ => Nat.le_refl _
  | .arr a (.base b), _ => b.elim
  | .arr a (.arr c d), _ => Nat.le_refl _

theorem root_hcy (a : Code Empty) (z : univHC.El a) : root (.arr a .t) (hcy a z) = root a z := by
  have h : ∃ z', hcy a z = hcy a z' := ⟨z, rfl⟩
  show (if h : ∃ z', hcy a z = hcy a z' then root a (Classical.choose h) else ⟨.arr a .t, hcy a z⟩) = _
  split
  · rename_i h'; rw [← hcy_inj (Classical.choose_spec h')]
  · exact absurd h ‹_›

theorem root_inj : ∀ (a : Code Empty) (x y : univHC.El a), root a x = root a y → x = y
  | .e, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .t, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .base b, _, _, _ => b.elim
  | .arr a .e, _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr a (.base b), _, _, _ => b.elim
  | .arr a (.arr c d), _, _, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr a .t, f, g, h => by
    by_cases hf : ∃ z, f = hcy a z <;> by_cases hg : ∃ z, g = hcy a z
    · obtain ⟨z, rfl⟩ := hf; obtain ⟨z', rfl⟩ := hg
      rw [root_hcy, root_hcy] at h
      rw [root_inj a z z' h]
    · obtain ⟨z, rfl⟩ := hf
      rw [root_hcy] at h
      have e : root (.arr a .t) g = ⟨.arr a .t, g⟩ := by
        show (if h : ∃ z, g = hcy a z then root a (Classical.choose h) else ⟨.arr a .t, g⟩) = _
        split
        · exact absurd ‹_› hg
        · rfl
      rw [e] at h
      have := root_sz a z; rw [congrArg Sigma.fst h] at this; simp only [csz] at this; omega
    · obtain ⟨z', rfl⟩ := hg
      rw [root_hcy] at h
      have e : root (.arr a .t) f = ⟨.arr a .t, f⟩ := by
        show (if h : ∃ z, f = hcy a z then root a (Classical.choose h) else ⟨.arr a .t, f⟩) = _
        split
        · exact absurd ‹_› hf
        · rfl
      rw [e] at h
      have := root_sz a z'; rw [← congrArg Sigma.fst h] at this; simp only [csz] at this; omega
    · have e1 : root (.arr a .t) f = ⟨.arr a .t, f⟩ := by
        show (if h : ∃ z, f = hcy a z then root a (Classical.choose h) else ⟨.arr a .t, f⟩) = _
        split
        · exact absurd ‹_› hf
        · rfl
      have e2 : root (.arr a .t) g = ⟨.arr a .t, g⟩ := by
        show (if h : ∃ z, g = hcy a z then root a (Classical.choose h) else ⟨.arr a .t, g⟩) = _
        split
        · exact absurd ‹_› hg
        · rfl
      rw [e1, e2] at h
      exact eq_of_heq (Sigma.mk.inj h).2

noncomputable def MhaeCF : Frame where
  U := univHC
  eqv := fun a b x y _ => root a x = root b y
  teq := fun a b _ => a = b

theorem MhaeC_isModelAt : MhaeCF.IsModelAt :=
  MhaeCF.isModelAt_of (fun _ _ _ => rfl) (fun _ _ _ _ _ h => h.symm) (fun _ _ _ _ _ _ _ h1 h2 => h1.trans h2)
    (fun _ _ _ => Iff.rfl)

theorem MhaeC_eq : ∀ a x y w, MhaeCF.eqv a a x y w → x = y := fun a x y _ h => root_inj a x y h

theorem MhaeC_model : MhaeCF.IsModelPIm :=
  MhaeCF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ _ _ h => h.symm)
    (fun _ _ _ _ _ _ h1 h2 => h1.trans h2)

theorem MhaeC_LLEqv : MhaeCF.Valid LLEqv := fun ρ env => MhaeCF.LLEqv_validAt_of MhaeC_eq _ ρ env

theorem MhaeC_Class : ∀ χ, ClassSch χ → MhaeCF.Valid χ :=
  MhaeCF.Class_valid_of MhaeC_isModelAt (MhaeCF.LLEqv_validAt_of MhaeC_eq) fun _ _ => rfl

theorem MhaeC_Hae : MhaeCF.Valid Hae := by
  intro ρ env
  show ∀ a (x : univHC.El a), root a x = root (.arr a .t) (fun y _ => root a y = root a x)
  intro a x
  have e : (fun (y : univHC.El a) (_ : Bool) => root a y = root a x) = hcy a x :=
    funext fun y => funext fun _ => propext ⟨root_inj a y x, fun h => h ▸ rfl⟩
  have := root_hcy a x
  rw [← e] at this
  exact this.symm

theorem MhaeC_not_Collapse : ¬ MhaeCF.Valid Collapse := fun h => by
  have h0 := (MhaeCF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (fun w => w = true)
  have hb := (MhaeCF.holds_imp _ _ _ _).mp h0 (show true = true from rfl)
  have := MhaeCF.box_all (fun p q h => MhaeC_eq _ _ _ _ h) _ _ _ hb false
  exact Bool.false_ne_true this

end Wd

end PIF
