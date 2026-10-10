import PIHaeQs
import PICongQs

/-!
# Necessity of identity across types, and Functional Choice

Three further principles: the necessity of identity and of distinctness for items of any two
types (NI×, ND×), and Functional Choice (every total relation contains a function). In the
standard semantics, and in the semantics with worlds, with tags, and of algebras, every function
between the relevant sets is an item, and Functional Choice holds.
-/
set_option autoImplicit false

namespace PIF
open Tm

/-- (NI×) `𝔸α 𝔸β ∀_α x ∀_β y (x ≡ y → □(x ≡ y))` -/
def NIX : Fm Ctx.nil :=
  tall (tall (all tv1 (all tv0 (imp (eqv tv1 tv0 (.var (.there .here)) (.var .here))
    (boxF (eqv tv1 tv0 (.var (.there .here)) (.var .here)))))))

/-- (ND×) `𝔸α 𝔸β ∀_α x ∀_β y (¬ x ≡ y → □¬(x ≡ y))` -/
def NDX : Fm Ctx.nil :=
  tall (tall (all tv1 (all tv0 (imp (neg (eqv tv1 tv0 (.var (.there .here)) (.var .here)))
    (boxF (neg (eqv tv1 tv0 (.var (.there .here)) (.var .here))))))))

/-- (Choice) `𝔸α 𝔸β ∀_{α→β→t} R (∀_α x ∃_β y R x y → ∃_{α→β} f ∀_α x R x (f x))` -/
def Choice : Fm Ctx.nil :=
  tall (tall (all (tv1.arrow tv0.pred) (imp
    (all tv1 (ex tv0 (.app (.app (.var (.there (.there .here))) (.var (.there .here))) (.var .here))))
    (ex (tv1.arrow tv0) (all tv1 (.app (.app (.var (.there (.there .here))) (.var .here))
      (.app (.var (.there .here)) (.var .here))))))))

/-! ## Derivations -/

section Derivations
open Derive
variable {S : Fm Ctx.nil → Prop}

abbrev ExyX : Fm C11 := Tm.eqv tv1 tv0 (.var (.there .here)) (.var .here)

set_option maxHeartbeats 4000000 in
/-- Collapse proves NI×. -/
theorem d_NIX_of_Collapse (hC : S Collapse) : Prov S Ctx.nil NIX := by
  have h : Ent S C11 ([] ++ [ExyX]) (boxF ExyX) :=
    Ent.mp ((Ent.axm (Γ := C11) (Hs := [ExyX]) hC).inst ExyX) (Ent.hyp _ 0 (by decide))
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.gen tv1 (Hs := []) (Ent.gen tv0 (Hs := []) (Ent.intro h)))))

set_option maxHeartbeats 4000000 in
/-- Collapse proves ND×. -/
theorem d_NDX_of_Collapse (hC : S Collapse) : Prov S Ctx.nil NDX := by
  have h : Ent S C11 ([] ++ [neg ExyX]) (boxF (neg ExyX)) :=
    Ent.mp ((Ent.axm (Γ := C11) (Hs := [neg ExyX]) hC).inst (neg ExyX)) (Ent.hyp _ 0 (by decide))
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.gen tv1 (Hs := []) (Ent.gen tv0 (Hs := []) (Ent.intro h)))))

set_option maxHeartbeats 4000000 in
/-- NI× proves NI≡: take `β` to be `α`. -/
theorem d_NIEqv_of_NIX (hN : S NIX) : Prov S Ctx.nil NIEqv := by
  have h : Ent S Γxy [] (Exy.imp (boxF Exy)) :=
    ((((Ent.axm (Γ := Γxy) (Hs := []) hN).tinst tv0).tinst tv0).inst (.var (.there .here))).inst (.var .here)
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen tv0 (Hs := []) (Ent.gen tv0 (Hs := []) h)))

end Derivations

/-! ## The standard semantics -/

namespace Frame
variable (F : Frame)

theorem tr_Choice : F.Tr Choice ↔ ∀ a b (R : F.U.El a → F.U.El b → Prop),
    (∀ x, ∃ y, R x y) → ∃ f : F.U.El a → F.U.El b, ∀ x, R x (f x) := Iff.rfl

/-- Functional Choice holds in every standard frame. -/
theorem Choice_valid : F.Valid Choice :=
  (F.valid_iff_tr _).mpr <| F.tr_Choice.mpr fun _ _ _ h => ⟨fun x => Classical.choose (h x), fun x => Classical.choose_spec (h x)⟩

end Frame

/-! ## Worlds -/

namespace Wd
namespace Frame
variable (F : Frame)

theorem tr_Choice : F.Tr Choice ↔ ∀ a b (R : F.U.El a → F.U.El b → F.U.W → Prop),
    (∀ x, ∃ y, R x y F.U.w0) → ∃ f : F.U.El a → F.U.El b, ∀ x, R x (f x) F.U.w0 := Iff.rfl

theorem Choice_valid : F.Valid Choice :=
  (F.valid_iff_tr _).mpr <| F.tr_Choice.mpr fun _ _ _ h => ⟨fun x => Classical.choose (h x), fun x => Classical.choose_spec (h x)⟩

theorem tr_NIX : F.Tr NIX ↔ ∀ a b (x : F.U.El a) (y : F.U.El b), F.eqv a b x y F.U.w0 →
    F.eqv .t .t (F.eqv a b x y) (F.eval (topF : Fm Ctx.nil) (fun i => i.elim0) ()) F.U.w0 := Iff.rfl

end Frame
end Wd

namespace Al
namespace Frame
variable (F : Frame)

/-- Functional Choice holds in every frame of this semantics. -/
theorem Choice_valid : F.Valid Choice := by
  intro ρ env
  refine (F.holds_tall _ _ _).mpr fun a => (F.holds_tall _ _ _).mpr fun b => ?_
  refine (F.holds_all _ _ _ _).mpr fun R => (F.holds_imp _ _ _ _).mpr fun h => ?_
  have h' := fun x => (F.holds_ex _ _ _ _).mp ((F.holds_all _ _ _ _).mp h x)
  exact (F.holds_ex _ _ _ _).mpr ⟨fun x => Classical.choose (h' x),
    (F.holds_all _ _ _ _).mpr fun x => Classical.choose_spec (h' x)⟩

end Frame
end Al

namespace Tg
namespace Frame
variable (F : Frame)

/-- Functional Choice holds in every frame of this semantics. -/
theorem Choice_valid : F.Valid Choice := by
  intro ρ env
  refine (F.holds_tall _ _ _).mpr fun a => (F.holds_tall _ _ _).mpr fun b => ?_
  refine (F.holds_all _ _ _ _).mpr fun R => (F.holds_imp _ _ _ _).mpr fun h => ?_
  have h' := fun x => (F.holds_ex _ _ _ _).mp ((F.holds_all _ _ _ _).mp h x)
  exact (F.holds_ex _ _ _ _).mpr ⟨fun x => Classical.choose (h' x),
    (F.holds_all _ _ _ _).mpr fun x => Classical.choose_spec (h' x)⟩

end Frame
end Tg

namespace AlI
namespace Frame
variable (F : Frame)

/-- Functional Choice holds in every frame with intensional functions. -/
theorem Choice_valid : F.Valid Choice := by
  intro ρ env
  refine (F.holds_tall _ _ _).mpr fun a => (F.holds_tall _ _ _).mpr fun b => ?_
  refine (F.holds_all _ _ _ _).mpr fun R => (F.holds_imp _ _ _ _).mpr fun h => ?_
  have h' := fun x => (F.holds_ex _ _ _ _).mp ((F.holds_all _ _ _ _).mp h x)
  exact (F.holds_ex _ _ _ _).mpr ⟨(fun x => Classical.choose (h' x), true),
    (F.holds_all _ _ _ _).mpr fun x => Classical.choose_spec (h' x)⟩

end Frame
end AlI

/-! ## Kripke models -/

namespace Kr
namespace Frame
variable (U : Univ)

theorem simple_eqv_mono {a b : Code U.Base} {x : U.El a} {y : U.El b} {w v : U.W} (hv : U.R w v)
    (h : (Frame.simple U).eqv a b x y w) : (Frame.simple U).eqv a b x y v :=
  let ⟨e, hr⟩ := h; ⟨e, U.rel_mono _ w v _ _ hv hr⟩

/-- In a simple Kripke frame, identity persists along `R`, so NI× holds. -/
theorem simple_NIX : (S U).Valid NIX := by
  refine simple_Valid_of U ?_
  refine ((S U).holdsAt_tall _ _ _ _).mpr fun a _ => ((S U).holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine ((S U).holdsAt_all _ _ _ _ _).mpr fun x _ => ((S U).holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine ((S U).holdsAt_imp _ _ _ _ _).mpr fun h => (simple_box U _ _ _ _).mpr fun v hv => ?_
  exact ((S U).holdsAt_eqv _ _ _ _ _ _ _).mpr (simple_eqv_mono U hv (((S U).holdsAt_eqv _ _ _ _ _ _ _).mp h))

end Frame

/-! ### `𝔐_k,ch`: Functional Choice fails

Two worlds; the actual world sees both, and the other sees only itself. There are four entities
`0, 1, 2, 3`, distinct at the actual world; at the other world, `0` and `1` are identical. The
relation `R x y`, which at the actual world says that `y` is `2` if `x` is even and `3` if `x` is
odd, and holds everywhere at the other world, relates each entity to some entity. But a function
choosing these values would send `0` and `1` to `2` and `3`, which are distinct at the other world,
where `0` and `1` are identical; so it is not an item. -/

def UCh : Univ where
  W := Bool
  w0 := true
  R := fun w v => w = true ∨ v = false
  Rrefl := fun w => by cases w <;> simp
  Rtrans := by
    intro u v w h1 h2
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · rcases h2 with h2 | h2
      · exact absurd (h1.symm.trans h2) Bool.false_ne_true
      · exact Or.inr h2
  E := Fin 4
  Base := Empty
  B := Empty.elim
  neE := ⟨0⟩
  neB := fun b => b.elim
  re := fun w x y => x = y ∨ (w = false ∧ x.val < 2 ∧ y.val < 2)
  rb := fun _ b => b.elim
  re_refl := fun _ _ => Or.inl rfl
  re_symm := fun _ _ _ h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.1, h.2.2, h.2.1⟩)
  re_trans := by
    intro w x y z h1 h2
    rcases h1 with rfl | ⟨hw, hx, _⟩
    · exact h2
    · rcases h2 with rfl | ⟨_, _, hz⟩
      · exact Or.inr ⟨hw, hx, by assumption⟩
      · exact Or.inr ⟨hw, hx, hz⟩
  re_mono := by
    intro w v x y h hxy
    rcases hxy with e | ⟨hw, hx, hy⟩
    · exact Or.inl e
    · subst hw
      rcases h with h | h
      · exact absurd h Bool.false_ne_true
      · exact Or.inr ⟨h, hx, hy⟩
  rb_refl := fun _ b => b.elim
  rb_symm := fun _ b => b.elim
  rb_trans := fun _ b => b.elim
  rb_mono := fun _ _ b => b.elim
  D := fun _ _ => True
  D_e := fun _ => trivial
  D_t := fun _ => trivial
  D_arr := fun _ _ _ _ _ => trivial
  D_mono := fun _ _ _ _ _ => trivial

abbrev MchK : Frame := Frame.simple UCh

/-- The chosen value. -/
def gCh (x : Fin 4) : Fin 4 := if x.val % 2 = 0 then 2 else 3

def RCh : UCh.El (.arr .e (.arr .e .t)) := fun x y w => w = false ∨ y = gCh x

theorem RCh_adm : UCh.rel (.arr .e (.arr .e .t)) true RCh RCh := by
  intro v hv x x' hx u hu y y' hy s hs
  cases s
  · exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩
  · have hu' : u = true := hs.elim id (fun h => absurd h (by decide))
    subst hu'
    have hv' : v = true := hu.elim id (fun h => absurd h (by decide))
    subst hv'
    have ex : x = x' := hx.elim id (fun h => absurd h.1 (by decide))
    have ey : y = y' := hy.elim id (fun h => absurd h.1 (by decide))
    subst ex; subst ey
    exact Iff.rfl

theorem Mch_not_Choice : ¬ MchK.Valid Choice := by
  refine Frame.simple_not_Valid UCh fun h => ?_
  have h1 := (MchK.holdsAt_tall _ _ _ _).mp h .e trivial
  have h2 := (MchK.holdsAt_tall _ _ _ _).mp h1 .e trivial
  have h3 := (MchK.holdsAt_all _ _ _ _ _).mp h2 RCh RCh_adm
  have h4 := (MchK.holdsAt_imp _ _ _ _ _).mp h3 ((MchK.holdsAt_all _ _ _ _ _).mpr fun x _ =>
    (MchK.holdsAt_ex _ _ _ _ _).mpr ⟨gCh x, Or.inl rfl, Or.inr rfl⟩)
  obtain ⟨f, hf, hfx⟩ := (MchK.holdsAt_ex _ _ _ _ _).mp h4
  have hall := (MchK.holdsAt_all _ _ _ _ _).mp hfx
  have f0 : (f : Fin 4 → Fin 4) (0 : Fin 4) = gCh (0 : Fin 4) :=
    (show true = false ∨ (f : Fin 4 → Fin 4) (0 : Fin 4) = gCh (0 : Fin 4) from
      hall (0 : Fin 4) (Or.inl rfl)).resolve_left (fun h => Bool.noConfusion h)
  have f1 : (f : Fin 4 → Fin 4) (1 : Fin 4) = gCh (1 : Fin 4) :=
    (show true = false ∨ (f : Fin 4 → Fin 4) (1 : Fin 4) = gCh (1 : Fin 4) from
      hall (1 : Fin 4) (Or.inl rfl)).resolve_left (fun h => Bool.noConfusion h)
  have hr : UCh.re false ((f : Fin 4 → Fin 4) (0 : Fin 4)) ((f : Fin 4 → Fin 4) (1 : Fin 4)) :=
    hf false (Or.inr rfl) (0 : Fin 4) (1 : Fin 4) (Or.inr ⟨rfl, by decide, by decide⟩)
  rw [f0, f1] at hr
  rcases hr with e | ⟨_, _, h3⟩
  · exact absurd e (by decide)
  · exact absurd h3 (by decide)

theorem Mch_not_NDX : ¬ MchK.Valid NDX := by
  refine Frame.simple_not_Valid UCh fun h => ?_
  have h1 := (MchK.holdsAt_tall _ _ _ _).mp ((MchK.holdsAt_tall _ _ _ _).mp h .e trivial) .e trivial
  have h2 := (MchK.holdsAt_all _ _ _ _ _).mp ((MchK.holdsAt_all _ _ _ _ _).mp h1 (show Fin 4 from 0) (Or.inl rfl))
    (show Fin 4 from 1) (Or.inl rfl)
  refine (MchK.holdsAt_neg _ _ _ _).mp ((Frame.simple_box UCh _ _ _ _).mp ((MchK.holdsAt_imp _ _ _ _ _).mp h2
    ((MchK.holdsAt_neg _ _ _ _).mpr fun he => ?_)) false (Or.inr rfl)) ?_
  · have he' := (MchK.holdsAt_eqv _ _ _ _ _ _ _).mp he
    have := (Frame.simple_eqv_same UCh .e (show Fin 4 from 0) (show Fin 4 from 1) true).mp he'
    rcases this with e | ⟨hw, _⟩
    · exact absurd e (by decide)
    · exact absurd hw (by decide)
  · exact (MchK.holdsAt_eqv _ _ _ _ _ _ _).mpr
      ((Frame.simple_eqv_same UCh .e (show Fin 4 from 0) (show Fin 4 from 1) false).mpr
        (Or.inr ⟨rfl, by decide, by decide⟩))

theorem Mch_NIX : MchK.Valid NIX := Frame.simple_NIX UCh
theorem Mch_Class : ∀ χ, ClassSch χ → MchK.Valid χ := Frame.simple_Class UCh
theorem Mch_LLEqv : MchK.Valid LLEqv := fun ρ hρ env henv => Frame.simple_LLEqv UCh _ ρ hρ env henv
theorem Mch_isModelAt : MchK.IsModelAt := Frame.simple_isModelAt UCh
theorem Mch_Disjoint : MchK.Valid Disjoint := Frame.simple_Disjoint UCh
theorem Mch_Cong : MchK.Valid Cong := Frame.simple_Cong UCh
theorem Mch_Inj : MchK.Valid Inj := Frame.simple_Inj UCh
theorem Mch_ExtT : MchK.Valid ExtT := Frame.simple_ExtT UCh

end Kr

end PIF
