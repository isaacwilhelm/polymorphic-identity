import PIBF

/-!
# Three-proposition algebraic models: the Barcan formulas

* `𝔐_⊤⊥,hae` (`MBH`): BF fails. Each `F x` is `1`, identified with `⊤ = 0`, so `∀x □(F x)` holds;
  but `∀x F x` is `2`, which is not identified with `⊤`.
* `𝔐_⊤⊥,c` (`MCc`): as `𝔐_⊤⊥,hae`, but `⊤` and `⊥` are identified and `1` is identified with
  nothing else; only `0` is true. Collapse holds and `⊤ ≢ ⊥` fails; T fails, since `2` is
  identified with `⊤` but false. Every proposition of the form `mk3 c` (in particular, every
  quantified proposition) is identified with `⊤`, so BF holds; CBF fails, since `∀x F x` is `2`,
  identified with `⊤`, while `F x = 1` is not identified with `⊤`.
-/
set_option autoImplicit false

namespace PIF
open Tm

namespace Al

/-- The value `mk3 c` is never the middle proposition `1`. -/
theorem mk3_ne1 (c : Prop) : mk3 c ≠ (1 : Fin 3) := by
  unfold mk3
  split
  · decide
  · decide

/-- A proposition of the form `mk3 c` that `simB` relates to `0` is `0`. -/
theorem mk3_simB_F3c {c : Prop} (h : simB (mk3 c) 0) : VB (mk3 c) := by
  by_cases hc : c
  · exact mk3_eq0 hc
  · rw [mk3_eq2 hc] at h
    rcases h with h | ⟨h, _⟩
    · exact absurd h (by decide)
    · exact absurd rfl h

/-! ## `𝔐_⊤⊥,hae`: BF fails -/

/-- In `𝔐_⊤⊥,hae`, with `F` taking each entity to `1`: each `F x` is identified with `⊤`, but
`∀x F x` is `2`, which is not. -/
theorem MBH_not_BF : ¬ MBH.Valid BF := fun h => by
  let G : (univ3 VB).El (.arr .e .t) := fun _ => (1 : Fin 3)
  have h0 := (MBH.holds_all _ _ _ _).mp ((MBH.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) G
  have hb : MBH.Holds (all tv0 (boxF (Tm.app (.var (.there .here)) (.var .here))) : Fm ((Ctx.nil.text).ext tv0.pred))
      (scons .e fun i => i.elim0) ((), G) := by
    refine (MBH.holds_all _ _ _ _).mpr fun x => ?_
    refine (MBH.holds_eqv_t _ _ _ _).mpr ((F3_eqT VB VB0 VB2 simB _ _ simB_refl).mpr ?_)
    rw [F3_top VB VB0 VB2 simB (Γ := ((Ctx.nil.text).ext tv0.pred).ext tv0) (scons .e fun i => i.elim0) (((), G), x)]
    exact Or.inr ⟨(by decide : (1 : Fin 3) ≠ 2), (by decide : (0 : Fin 3) ≠ 2)⟩
  have h1 := (MBH.holds_imp _ _ _ _).mp h0 hb
  have hq := (F3_eqT VB VB0 VB2 simB _ _ simB_refl).mp ((MBH.holds_eqv_t _ _ _ _).mp h1)
  rw [F3_top VB VB0 VB2 simB (Γ := (Ctx.nil.text).ext tv0.pred) (scons .e fun i => i.elim0) ((), G)] at hq
  have e := MBH.eval_all (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here))
    (scons .e fun i => i.elim0) ((), G)
  rw [e] at hq
  have hall : MBH.Holds (all tv0 (Tm.app (.var (.there .here)) (.var .here)) : Fm ((Ctx.nil.text).ext tv0.pred))
      (scons .e fun i => i.elim0) ((), G) := cast (congrArg MBH.U.V e).symm (mk3_simB_F3c hq)
  have hx := (MBH.holds_all _ _ _ _).mp hall ()
  have hx' : (1 : Fin 3) = 0 := hx
  exact absurd hx' (by decide)

/-! ## `𝔐_⊤⊥,c`: `⊤` and `⊥` identified, `1` alone -/

/-- `0` and `2` are identified; `1` is identified with nothing else. -/
def simC (p q : Fin 3) : Prop := p = q ∨ (p ≠ 1 ∧ q ≠ 1)
theorem simC_refl : ∀ p, simC p p := fun _ => Or.inl rfl
theorem simC_symm : ∀ p q, simC p q → simC q p := fun _ _ h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.2, h.1⟩)
theorem simC_trans : ∀ p q r, simC p q → simC q r → simC p r := by
  intro p q r h1 h2
  rcases h1 with rfl | ⟨a1, a2⟩
  · exact h2
  · rcases h2 with rfl | ⟨_, b2⟩
    · exact Or.inr ⟨a1, a2⟩
    · exact Or.inr ⟨a1, b2⟩

/-- Every proposition of the form `mk3 c` is identified with `0`. -/
theorem simC_mk3 (c : Prop) : simC (mk3 c) 0 := Or.inr ⟨mk3_ne1 c, by decide⟩

noncomputable abbrev MCc : Frame := F3 VB VB0 VB2 simC
theorem MCc_model : MCc.IsModelPIm := F3_model VB VB0 VB2 simC simC_symm simC_trans
theorem MCc_Hae : MCc.Valid Hae := F3_Hae VB VB0 VB2 simC simC_symm

/-- The only true proposition is `0 = ⊤`. -/
theorem MCc_Collapse : MCc.Valid Collapse := by
  intro ρ env
  refine (MCc.holds_all _ _ _ _).mpr fun p => (MCc.holds_imp _ _ _ _).mpr fun hp => ?_
  refine (MCc.holds_eqv_t _ _ _ _).mpr ((F3_eqT VB VB0 VB2 simC _ _ simC_refl).mpr ?_)
  rw [F3_top VB VB0 VB2 simC (Γ := Ctx.nil.ext tyT) ρ (env, p)]
  exact Or.inl hp

/-- `⊤` is `0` and `⊥` is `2`, which are identified. -/
theorem MCc_not_TopBot : ¬ MCc.Valid TopBot := fun h => by
  have h0 := (MCc.holds_neg _ _ _).mp (h (fun i => i.elim0) ())
  refine h0 ((MCc.holds_eqv_t _ _ _ _).mpr ((F3_eqT VB VB0 VB2 simC _ _ simC_refl).mpr ?_))
  rw [F3_top VB VB0 VB2 simC (Γ := Ctx.nil) (fun i => i.elim0) (),
    F3_bot VB VB0 VB2 simC (Γ := Ctx.nil) (fun i => i.elim0) ()]
  exact Or.inr ⟨(by decide : (0 : Fin 3) ≠ 1), (by decide : (2 : Fin 3) ≠ 1)⟩

/-- `2` is identified with `⊤`, but false. -/
theorem MCc_not_TAx : ¬ MCc.Valid TAx := fun h => by
  have h0 := (MCc.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (2 : Fin 3)
  have h1 := (MCc.holds_imp _ _ _ _).mp h0 ((MCc.holds_eqv_t _ _ _ _).mpr
    ((F3_eqT VB VB0 VB2 simC _ _ simC_refl).mpr (by
      rw [F3_top VB VB0 VB2 simC (Γ := Ctx.nil.ext tyT) _ ((), (2 : Fin 3))]
      exact Or.inr ⟨(by decide : (2 : Fin 3) ≠ 1), (by decide : (0 : Fin 3) ≠ 1)⟩)))
  have h2 : VB 2 := h1
  exact VB2 h2

/-- Every quantified proposition is `0` or `2`, so it is identified with `⊤`. -/
theorem MCc_BF : MCc.Valid BF := by
  intro ρ env
  refine (MCc.holds_tall _ _ _).mpr fun a => (MCc.holds_all _ _ _ _).mpr fun G => ?_
  refine (MCc.holds_imp _ _ _ _).mpr fun _ => ?_
  refine (MCc.holds_eqv_t _ _ _ _).mpr ((F3_eqT VB VB0 VB2 simC _ _ simC_refl).mpr ?_)
  rw [F3_top VB VB0 VB2 simC (Γ := (Ctx.nil.text).ext tv0.pred) (scons a ρ) (env, G),
    MCc.eval_all (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here)) (scons a ρ) (env, G)]
  exact simC_mk3 _

/-- With `F` taking each entity to `1`: `∀x F x` is `2`, identified with `⊤`; but `F x = 1` is not
identified with `⊤`. -/
theorem MCc_not_CBF : ¬ MCc.Valid CBF := fun h => by
  let G : (univ3 VB).El (.arr .e .t) := fun _ => (1 : Fin 3)
  have h0 := (MCc.holds_all _ _ _ _).mp ((MCc.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) G
  have hb : MCc.Holds (boxF (all tv0 (Tm.app (.var (.there .here)) (.var .here))) : Fm ((Ctx.nil.text).ext tv0.pred))
      (scons .e fun i => i.elim0) ((), G) := by
    refine (MCc.holds_eqv_t _ _ _ _).mpr ((F3_eqT VB VB0 VB2 simC _ _ simC_refl).mpr ?_)
    rw [F3_top VB VB0 VB2 simC (Γ := (Ctx.nil.text).ext tv0.pred) (scons .e fun i => i.elim0) ((), G),
      MCc.eval_all (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here))
        (scons .e fun i => i.elim0) ((), G)]
    exact simC_mk3 _
  have h1 := (MCc.holds_all _ _ _ _).mp ((MCc.holds_imp _ _ _ _).mp h0 hb) ()
  have hq := (F3_eqT VB VB0 VB2 simC _ _ simC_refl).mp ((MCc.holds_eqv_t _ _ _ _).mp h1)
  rw [F3_top VB VB0 VB2 simC (Γ := ((Ctx.nil.text).ext tv0.pred).ext tv0) (scons .e fun i => i.elim0) (((), G), ())] at hq
  have hq' : simC 1 0 := hq
  rcases hq' with e | ⟨e, _⟩
  · exact absurd e (by decide)
  · exact e rfl

end Al

end PIF
