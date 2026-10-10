import PIModalX2

/-!
# The Barcan formulas for items, Necessitism, and three-way interactions

The Barcan formula and its converse for the item quantifiers, stated for a predicate variable
(each instance of the schema follows by instantiating the predicate with a λ-term), and
Necessitism for items. Classicism proves the converse Barcan formula and Necessitism; Classicism
and PCong← prove the Barcan formula. And Classicism, Disjoint, Inj≈ and ND× together prove ND≈.
-/
set_option autoImplicit false

namespace PIF
open Tm

/-- (BF) `𝔸α ∀_{α→t} F (∀_α x □(F x) → □∀_α x F x)` -/
def BF : Fm Ctx.nil :=
  tall (all tv0.pred (imp (all tv0 (boxF (.app (.var (.there .here)) (.var .here))))
    (boxF (all tv0 (.app (.var (.there .here)) (.var .here))))))

/-- (CBF) `𝔸α ∀_{α→t} F (□∀_α x F x → ∀_α x □(F x))` -/
def CBF : Fm Ctx.nil :=
  tall (all tv0.pred (imp (boxF (all tv0 (.app (.var (.there .here)) (.var .here))))
    (all tv0 (boxF (.app (.var (.there .here)) (.var .here))))))

/-- (Nec) `𝔸α ∀_α x □∃_α y (x ≡ y)` -/
def Nec : Fm Ctx.nil :=
  tall (all tv0 (boxF (ex tv0 (eqv tv0 tv0 (.var (.there .here)) (.var .here)))))

section Derivations
open Derive
variable {S : Fm Ctx.nil → Prop}

abbrev ΓF : Ctx 1 := Δ1.ext tv0.pred
abbrev ΓFx : Ctx 1 := ΓF.ext tv0
abbrev FxF : Fm ΓFx := Tm.app (.var (.there .here)) (.var .here)
abbrev AllF : Fm ΓF := all tv0 (Tm.app (.var (.there .here)) (.var .here))
abbrev AllF' : Fm ΓFx := all tv0 (Tm.app (.var (.there (.there .here))) (.var .here))

set_option maxHeartbeats 4000000 in
/-- Classicism proves Necessitism: `∃y(x ≡ y)` is a theorem of PI, so it is identical to `⊤`. -/
theorem d_Nec_of_Class (hC : ∀ χ, ClassSch χ → S χ) : Prov S Ctx.nil Nec := by
  refine Prov.ax (hC _ (Or.inl ⟨1, Δ1.ext tv0, ex tv0 (eqv tv0 tv0 (.var (.there .here)) (.var .here)), topF, ?_, rfl⟩))
  have hr : Ent (fun χ => χ = LLEqv) (Δ1.ext tv0) [] (eqv tv0 tv0 (.var .here) (.var .here)) :=
    ((Ent.closed (Γ := Δ1.ext tv0) Prov.refEqv).tinst tv0).inst (.var .here)
  have he : Ent (fun χ => χ = LLEqv) (Δ1.ext tv0) [] (ex tv0 (eqv tv0 tv0 (.var (.there .here)) (.var .here))) :=
    Ent.exI (.var .here) hr
  exact Ent.toProv (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1))))
    (v2 _ topF) (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) he Ent.top)

set_option maxHeartbeats 8000000 in
/-- Classicism and LL≡ prove CBF: `□∀x F x` gives `F x ≡ F x ∨ ∀x F x ≡ F x ∨ ⊤ ≡ ⊤`. -/
theorem d_CBF_of_Class (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) : Prov S Ctx.nil CBF := by
  have hc1 : S (tall (all tv0.pred (all tv0 (eqv tyT tyT (disj FxF AllF') FxF)))) := by
    refine hC _ (Or.inl ⟨1, ΓFx, disj FxF AllF', FxF, ?_, rfl⟩)
    have hH : Ent (fun χ => χ = LLEqv) ΓFx [AllF'] AllF' := Ent.hyp _ 0 (by decide)
    have h1 : Ent (fun χ => χ = LLEqv) ΓFx [AllF'] FxF := hH.inst (.var .here)
    have hAF : Ent (fun χ => χ = LLEqv) ΓFx [] (AllF'.imp FxF) := Ent.intro (Hs := []) h1
    exact Ent.toProv (Ent.mp (Ent.taut (.imp (.imp (.atom 1) (.atom 0)) (.iff (.disj (.atom 0) (.atom 1)) (.atom 0)))
      (v2 FxF AllF') (fun _ f => ⟨fun h => h.elim id f, Or.inl⟩)) hAF)
  have hc2 : S (tall (all tv0.pred (all tv0 (eqv tyT tyT (disj FxF topF) topF)))) := by
    refine hC _ (Or.inl ⟨1, ΓFx, disj FxF topF, topF, ?_, rfl⟩)
    exact Ent.toProv (Ent.mp (Ent.taut (.imp (.atom 1) (.iff (.disj (.atom 0) (.atom 1)) (.atom 1)))
      (v2 FxF topF) (fun _ t => ⟨fun _ => t, Or.inr⟩)) (Ent.top (Ax := fun χ => χ = LLEqv) (Hs := [])))
  let H : Fm ΓFx := boxF AllF'
  have hq : Ent S ΓFx [H] (eqv tyT tyT AllF' topF) := Ent.hyp _ 0 (by decide)
  have e1 : Ent S ΓFx [H] (eqv tyT tyT (disj FxF AllF') FxF) :=
    (((Ent.axm (Γ := ΓFx) (Hs := [H]) hc1).tinst tv0).inst (.var (.there .here))).inst (.var .here)
  have e2 : Ent S ΓFx [H] (eqv tyT tyT (disj FxF topF) topF) :=
    (((Ent.axm (Γ := ΓFx) (Hs := [H]) hc2).tinst tv0).inst (.var (.there .here))).inst (.var .here)
  have e3 : Ent S ΓFx [H] (eqv tyT tyT (disj FxF AllF') (disj FxF topF)) := Ent.mp (Ent.ofProv (or_cong hLL FxF AllF' topF)) hq
  have e4 : Ent S ΓFx [H] (eqv tyT tyT FxF (disj FxF AllF')) := Ent.mp (Ent.ofProv (sym_t (disj FxF AllF') FxF)) e1
  have e5 : Ent S ΓFx [H] (eqv tyT tyT FxF (disj FxF topF)) :=
    Ent.mp (Ent.ofProv (trans_t FxF (disj FxF AllF') (disj FxF topF))) (Ent.andI e4 e3)
  have e6 : Ent S ΓFx [H] (boxF FxF) :=
    Ent.mp (Ent.ofProv (trans_t FxF (disj FxF topF) topF)) (Ent.andI e5 e2)
  have e7 : Ent S ΓF [boxF AllF] (all tv0 (boxF FxF)) := Ent.gen tv0 e6
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen tv0.pred (Hs := []) (Ent.intro (Hs := []) e7)))

abbrev HBF : Fm ΓF := all tv0 (boxF (Tm.app (.var (.there .here)) (.var .here)))
abbrev lamTop : Tm ΓF (tv0.pred).1 := Tm.lam tv0 topF

set_option maxHeartbeats 8000000 in
/-- Classicism, LL≡ and PCong← prove BF. If `F x ≡ ⊤` for every `x`, PCong← makes `F`
identical to `λx.⊤`; and `□∀x(λx.⊤)x` holds by Classicism, so LL≡ carries it over to `□∀x F x`. -/
theorem d_BF_of_PExt (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) (hPE : S PExt) : Prov S Ctx.nil BF := by
  -- Classicism: `∀x ⊤ ≡ ⊤`
  have hct : S (tall (eqv tyT tyT (all tv0 topF) topF)) := by
    refine hC _ (Or.inl ⟨1, Δ1, all tv0 topF, topF, ?_, rfl⟩)
    have ha : Ent (fun χ => χ = LLEqv) Δ1 [] (all tv0 topF) := Ent.gen tv0 (Hs := []) Ent.top
    exact Ent.toProv (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1))))
      (v2 _ topF) (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) ha Ent.top)
  have hT : Ent S ΓF [HBF] (boxF (all tv0 topF)) := (Ent.axm (Γ := ΓF) (Hs := [HBF]) hct).tinst tv0
  -- PCong←, for `F` and `λx.⊤`
  have pe0 := (((((Ent.axm (Γ := ΓF) (Hs := [HBF]) hPE).tinst tv0).tinst tyT).tinst tyT).inst (.var .here)).inst lamTop
  have pe : Ent S ΓF [HBF] (HBF.imp (eqv tv0.pred tv0.pred (.var .here) lamTop)) :=
    Ent.beta pe0 (BetaEq.imp (BetaEq.appR _ (BetaEq.lamC tv0 (BetaEq.eqvC (.refl _) (.step (.beta _ _))))) (.refl _))
  have hFg : Ent S ΓF [HBF] (eqv tv0.pred tv0.pred (.var .here) lamTop) := Ent.mp pe (Ent.hyp _ 0 (by decide))
  have hgF : Ent S ΓF [HBF] (eqv tv0.pred tv0.pred lamTop (.var .here)) :=
    Ent.mp (((((Ent.closed (Γ := ΓF) (Hs := [HBF]) (Ax := S) Prov.symEqv).tinst tv0.pred).tinst tv0.pred).inst
      (.var .here)).inst lamTop) hFg
  -- LL≡, with `P := λG. □∀x G x`
  have ll := Ent.mp ((((Ent.axm (Γ := ΓF) (Hs := [HBF]) hLL).tinst tv0.pred).inst lamTop).inst (.var .here)) hgF
  have ll1 := ll.inst (Tm.lam tv0.pred (boxF (all tv0 (Tm.app (.var (.there .here)) (.var .here)))))
  have ll2 : Ent S ΓF [HBF] ((boxF (all tv0 topF)).imp (boxF AllF)) :=
    Ent.beta ll1 (BetaEq.imp
      (BetaEq.trans (.step (.beta _ _)) (BetaEq.eqvC (BetaEq.appR _ (BetaEq.lamC tv0 (.step (.beta _ _)))) (.refl _)))
      (.step (.beta _ _)))
  have h := Ent.mp ll2 hT
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen tv0.pred (Hs := []) (Ent.intro (Hs := []) h)))

abbrev idA : Tm Δ2 (tv1.arrow tv1).1 := Tm.lam tv1 (.var .here)
abbrev idB : Tm Δ2 (tv0.arrow tv0).1 := Tm.lam tv0 (.var .here)
abbrev Aab : Fm Δ2 := Tm.teq tv1 tv0
abbrev Eid : Fm Δ2 := Tm.eqv (tv1.arrow tv1) (tv0.arrow tv0) idA idB

set_option maxHeartbeats 4000000 in
/-- PI proves that if `α ≈ β`, the identity functions on `α` and `β` are identical. -/
theorem d_id_of_teq {S' : Fm Ctx.nil → Prop} : Ent S' Δ2 [] (Aab.imp Eid) := by
  have hQ : Ent S' Δ2 [] (LLTeq (Tm.tlam (Tm.eqv (tv2.arrow tv2) (tv0.arrow tv0)
      (Tm.lam tv2 (.var .here)) (Tm.lam tv0 (.var .here)))) : Fm Δ2) := Ent.ofProv (Prov.llTeq _)
  have h1 : Ent S' Δ2 [] (Aab.imp ((Tm.eqv (tv1.arrow tv1) (tv1.arrow tv1) idA idA).imp Eid)) :=
    Ent.beta ((hQ.tinst tv1).tinst tv0) (BetaEq.imp (.refl _) (BetaEq.imp (BetaEq.tbeta _ _) (BetaEq.tbeta _ _)))
  have hr : Ent S' Δ2 [] (Tm.eqv (tv1.arrow tv1) (tv1.arrow tv1) idA idA) :=
    ((Ent.closed (Γ := Δ2) Prov.refEqv).tinst (tv1.arrow tv1)).inst idA
  exact Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2))) (.imp (.atom 1) (.imp (.atom 0) (.atom 2))))
    (v3 Aab (Tm.eqv (tv1.arrow tv1) (tv1.arrow tv1) idA idA) Eid) (fun _ f b a => f a b)) h1 hr

set_option maxHeartbeats 8000000 in
/-- Classicism, LL≡, Disjoint, Inj≈ and ND× prove ND≈. If `¬ α ≈ β`, then `¬(α→α ≈ β→β)` by Inj≈,
so the identity functions on `α` and `β` are distinct by Disjoint, and necessarily so by ND×. But PI
proves that if `α ≈ β` then they are identical; so, by Classicism, `¬ α ≈ β` is necessary too. -/
theorem d_NDTeq_of_DisjInjNDX (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) (hD : S Disjoint) (hI : S Inj)
    (hN : S NDX) : Prov S Ctx.nil NDTeq := by
  -- Classicism: `¬A ∨ ¬E ≡ ¬A` and `¬A ∨ ⊤ ≡ ⊤`
  have hc1 : S (tall (tall (eqv tyT tyT (disj (neg Aab) (neg Eid)) (neg Aab)))) := by
    refine hC _ (Or.inl ⟨2, Δ2, disj (neg Aab) (neg Eid), neg Aab, ?_, rfl⟩)
    exact Ent.toProv (Ent.mp (Ent.taut (.imp (.imp (.atom 0) (.atom 1))
      (.iff (.disj (.neg (.atom 0)) (.neg (.atom 1))) (.neg (.atom 0))))
      (v2 Aab Eid) (fun _ f => ⟨fun h => h.elim id (fun ne a => ne (f a)), Or.inl⟩)) d_id_of_teq)
  have hc2 : S (tall (tall (eqv tyT tyT (disj (neg Aab) topF) topF))) := by
    refine hC _ (Or.inl ⟨2, Δ2, disj (neg Aab) topF, topF, ?_, rfl⟩)
    exact Ent.toProv (Ent.mp (Ent.taut (.imp (.atom 1) (.iff (.disj (.atom 0) (.atom 1)) (.atom 1)))
      (v2 (neg Aab) topF) (fun _ t => ⟨fun _ => t, Or.inr⟩)) (Ent.top (Ax := fun χ => χ = LLEqv) (Hs := [])))
  let Hs : List (Fm Δ2) := [neg Aab]
  have hnA : Ent S Δ2 Hs (neg Aab) := Ent.hyp _ 0 (by decide)
  -- Inj≈: `α→α ≈ β→β → α ≈ β`
  have hinj : Ent S Δ2 Hs ((Tm.teq (tv1.arrow tv1) (tv0.arrow tv0)).imp (Aab.conj Aab)) :=
    ((((Ent.axm (Γ := Δ2) (Hs := Hs) hI).tinst tv1).tinst tv0).tinst tv1).tinst tv0
  have hnT : Ent S Δ2 Hs (neg (Tm.teq (tv1.arrow tv1) (tv0.arrow tv0))) :=
    Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.conj (.atom 1) (.atom 1))) (.imp (.neg (.atom 1)) (.neg (.atom 0))))
      (v2 (Tm.teq (tv1.arrow tv1) (tv0.arrow tv0)) Aab) (fun _ f n t => n (f t).1)) hinj hnA
  -- Disjoint: the identity functions are distinct
  have hdis := Ent.mp (((Ent.axm (Γ := Δ2) (Hs := Hs) hD).tinst (tv1.arrow tv1)).tinst (tv0.arrow tv0)) hnT
  have hnE : Ent S Δ2 Hs (neg Eid) := (hdis.inst idA).inst idB
  -- ND×: necessarily so
  have hbE : Ent S Δ2 Hs (boxF (neg Eid)) :=
    Ent.mp ((((Ent.axm (Γ := Δ2) (Hs := Hs) hN).tinst (tv1.arrow tv1)).tinst (tv0.arrow tv0)).inst idA |>.inst idB) hnE
  -- Classicism, LL≡: `¬A ≡ ¬A ∨ ¬E ≡ ¬A ∨ ⊤ ≡ ⊤`
  have e1 : Ent S Δ2 Hs (eqv tyT tyT (disj (neg Aab) (neg Eid)) (neg Aab)) :=
    ((Ent.axm (Γ := Δ2) (Hs := Hs) hc1).tinst tv1).tinst tv0
  have e2 : Ent S Δ2 Hs (eqv tyT tyT (disj (neg Aab) topF) topF) :=
    ((Ent.axm (Γ := Δ2) (Hs := Hs) hc2).tinst tv1).tinst tv0
  have e3 := Ent.mp (Ent.ofProv (or_cong hLL (neg Aab) (neg Eid) topF)) hbE
  have e4 := Ent.mp (Ent.ofProv (sym_t (disj (neg Aab) (neg Eid)) (neg Aab))) e1
  have e5 := Ent.mp (Ent.ofProv (trans_t (neg Aab) (disj (neg Aab) (neg Eid)) (disj (neg Aab) topF))) (Ent.andI e4 e3)
  have e6 : Ent S Δ2 ([] ++ [neg Aab]) (boxF (neg Aab)) :=
    Ent.mp (Ent.ofProv (trans_t (neg Aab) (disj (neg Aab) topF) topF)) (Ent.andI e5 e2)
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.intro (Hs := []) e6)))

set_option maxHeartbeats 4000000 in
/-- Collapse proves Necessitism. -/
theorem d_Nec_of_Collapse (hC : S Collapse) : Prov S Ctx.nil Nec := by
  have hr : Ent S (Δ1.ext tv0) [] (eqv tv0 tv0 (.var .here) (.var .here)) :=
    ((Ent.closed (Γ := Δ1.ext tv0) Prov.refEqv).tinst tv0).inst (.var .here)
  have he : Ent S (Δ1.ext tv0) [] (ex tv0 (eqv tv0 tv0 (.var (.there .here)) (.var .here))) := Ent.exI (.var .here) hr
  have hb := Ent.mp ((Ent.axm (Γ := Δ1.ext tv0) (Hs := []) hC).inst
    (ex tv0 (eqv tv0 tv0 (.var (.there .here)) (.var .here)))) he
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen tv0 (Hs := []) hb))

set_option maxHeartbeats 4000000 in
/-- Collapse and T prove BF: `∀x □F x` gives `∀x F x` by T, and so `□∀x F x` by Collapse. -/
theorem d_BF_of_Collapse (hC : S Collapse) (hT : S TAx) : Prov S Ctx.nil BF := by
  have h1 : Ent S ΓFx [boxF FxF] FxF :=
    Ent.mp ((Ent.axm (Γ := ΓFx) (Hs := [boxF FxF]) hT).inst FxF) (Ent.hyp _ 0 (by decide))
  have h2 : Ent S ΓFx [HBF.wk tv0] (boxF FxF) := (Ent.hyp _ 0 (by decide) : Ent S ΓFx [HBF.wk tv0] _).inst (.var .here)
  have h3 : Ent S ΓFx [HBF.wk tv0] FxF := Ent.mp (Ent.ofProv (Ent.toProv (Ent.intro (Hs := []) h1))) h2
  have h4 : Ent S ΓF [HBF] AllF := Ent.gen tv0 h3
  have h5 : Ent S ΓF [HBF] (boxF AllF) := Ent.mp ((Ent.axm (Γ := ΓF) (Hs := [HBF]) hC).inst AllF) h4
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen tv0.pred (Hs := []) (Ent.intro (Hs := []) h5)))

set_option maxHeartbeats 4000000 in
/-- Collapse and T prove CBF: `□∀x F x` gives `∀x F x` by T, so `F x`, and so `□F x` by Collapse. -/
theorem d_CBF_of_Collapse (hC : S Collapse) (hT : S TAx) : Prov S Ctx.nil CBF := by
  have h1 : Ent S ΓFx [boxF AllF'] AllF' :=
    Ent.mp ((Ent.axm (Γ := ΓFx) (Hs := [boxF AllF']) hT).inst AllF') (Ent.hyp _ 0 (by decide))
  have h2 : Ent S ΓFx [boxF AllF'] FxF := h1.inst (.var .here)
  have h3 : Ent S ΓFx [boxF AllF'] (boxF FxF) := Ent.mp ((Ent.axm (Γ := ΓFx) (Hs := [boxF AllF']) hC).inst FxF) h2
  have h4 : Ent S ΓF [boxF AllF] (all tv0 (boxF FxF)) := Ent.gen tv0 h3
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen tv0.pred (Hs := []) (Ent.intro (Hs := []) h4)))

end Derivations

/-! ## Tagged models: quantified propositions carry the tag `false`, so BF and Necessitism fail -/

namespace Tg
namespace Frame
variable (F : Frame)

theorem cast_exists_snd {A A' : Type} (hA : A = A') (h : ((A → TV) → TV) = ((A' → TV) → TV)) (b : Bool)
    (P : A' → TV) : (cast h (fun Q : A → TV => ((∃ x, (Q x).1 : Prop), b)) P).2 = b := by
  subst hA; rw [cast_eq]

theorem eval_ex_snd {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    (F.eval (Tm.ex σ φ) ρ env).2 = F.qtag (F.U.code σ.1 ρ) :=
  cast_exists_snd (Univ.El_code ρ σ.2) _ _ _

end Frame

theorem Mz_not_BF : ¬ MzF.Valid BF := fun h => by
  have h0 := (MzF.holds_all _ _ _ _).mp (h (fun i => i.elim0) () .e) (fun _ => (True, true))
  have h1 := h0 ((MzF.holds_all _ _ _ _).mpr fun x => (MzF.holds_eqv_t _ _ _ _).mpr
    ⟨rfl, heq_of_eq (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => trivial⟩) rfl)⟩)
  have e := eq_of_heq ((MzF.holds_eqv_t _ _ _ _).mp h1).2
  have h2 := MzF.eval_all_snd (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here))
    (scons .e fun i => i.elim0) ((), fun _ => (True, true))
  exact Bool.noConfusion (h2.symm.trans (congrArg Prod.snd e) : false = true)

theorem Mz_CBF : MzF.Valid CBF := by
  intro ρ env a
  refine (MzF.holds_all _ _ _ _).mpr fun F hb => ?_
  have e := eq_of_heq ((MzF.holds_eqv_t _ _ _ _).mp hb).2
  have h2 := MzF.eval_all_snd (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here))
    (scons a ρ) (env, F)
  exact absurd (h2.symm.trans (congrArg Prod.snd e) : false = true) (fun h => Bool.noConfusion h)

theorem Mz_not_Nec : ¬ MzF.Valid Nec := fun h => by
  have h0 := (MzF.holds_all _ _ _ _).mp (h (fun i => i.elim0) () .e) ()
  have e := eq_of_heq ((MzF.holds_eqv_t _ _ _ _).mp h0).2
  have h2 := MzF.eval_ex_snd (Γ := (Ctx.nil.text).ext tv0) tv0 (Tm.eqv tv0 tv0 (.var (.there .here)) (.var .here))
    (scons .e fun i => i.elim0) ((), ())
  exact Bool.noConfusion (h2.symm.trans (congrArg Prod.snd e) : false = true)

end Tg

/-! ## Worlds -/

namespace Wd
namespace Frame
variable (F : Frame)

theorem tr_BF : F.Tr BF ↔ ∀ a (G : F.U.El a → F.U.W → Prop),
    (∀ x, F.eqv .t .t (G x) (F.eval (topF : Fm (((Ctx.nil.text).ext tv0.pred).ext tv0)) (scons a fun i => i.elim0) (((), G), x)) F.U.w0) →
    F.eqv .t .t (fun w => ∀ x, G x w) (F.eval (topF : Fm ((Ctx.nil.text).ext tv0.pred)) (scons a fun i => i.elim0) ((), G)) F.U.w0 :=
  Iff.rfl

theorem tr_CBF : F.Tr CBF ↔ ∀ a (G : F.U.El a → F.U.W → Prop),
    F.eqv .t .t (fun w => ∀ x, G x w) (F.eval (topF : Fm ((Ctx.nil.text).ext tv0.pred)) (scons a fun i => i.elim0) ((), G)) F.U.w0 →
    ∀ x, F.eqv .t .t (G x) (F.eval (topF : Fm (((Ctx.nil.text).ext tv0.pred).ext tv0)) (scons a fun i => i.elim0) (((), G), x)) F.U.w0 :=
  Iff.rfl

theorem tr_Nec : F.Tr Nec ↔ ∀ a (x : F.U.El a),
    F.eqv .t .t (fun w => ∃ y, F.eqv a a x y w) (F.eval (topF : Fm ((Ctx.nil.text).ext tv0)) (scons a fun i => i.elim0) ((), x)) F.U.w0 :=
  Iff.rfl

variable (hb : ∀ p q, F.eqv .t .t p q F.U.w0 ↔ p = q)
include hb

theorem BF_of : F.Valid BF :=
  (F.valid_iff_tr _).mpr <| F.tr_BF.mpr fun a G h => (hb _ _).mpr <| by
    refine Eq.trans ?_ (F.eval_topF _ _).symm
    funext w
    exact propext ⟨fun _ => trivial, fun _ x => by
      have e := ((hb _ _).mp (h x)).trans (F.eval_topF _ _)
      exact cast (congrFun e w).symm trivial⟩

theorem CBF_of : F.Valid CBF :=
  (F.valid_iff_tr _).mpr <| F.tr_CBF.mpr fun a G h x => (hb _ _).mpr <| by
    have e := ((hb _ _).mp h).trans (F.eval_topF _ _)
    refine Eq.trans ?_ (F.eval_topF _ _).symm
    funext w
    exact propext ⟨fun _ => trivial, fun _ => cast (congrFun e w).symm trivial x⟩

theorem Nec_of (hr : ∀ a x w, F.eqv a a x x w) : F.Valid Nec :=
  (F.valid_iff_tr _).mpr <| F.tr_Nec.mpr fun a x => (hb _ _).mpr <| by
    refine Eq.trans ?_ (F.eval_topF _ _).symm
    funext w
    exact propext ⟨fun _ => trivial, fun _ => ⟨x, hr a x w⟩⟩

theorem not_Nec_of {a : Code F.U.Base} (x : F.U.El a) (w : F.U.W) (h : ∀ y, ¬ F.eqv a a x y w) : ¬ F.Valid Nec :=
  fun hv => by
    have e := ((hb _ _).mp (F.tr_Nec.mp ((F.valid_iff_tr _).mp hv) a x)).trans (F.eval_topF _ _)
    obtain ⟨y, hy⟩ := cast (congrFun e w).symm trivial
    exact h y hy

end Frame

theorem RD.hb (D : RD) : ∀ p q, D.frame.eqv .t .t p q D.w0 ↔ p = q :=
  fun _ _ => ⟨fun h => eq_of_heq h.2.1, fun h => h ▸ ⟨rfl, HEq.rfl, D.hE⟩⟩

theorem Mw_BF : DW.frame.Valid BF := DW.frame.BF_of DW.hb
theorem Mw_CBF : DW.frame.Valid CBF := DW.frame.CBF_of DW.hb
theorem Mw_Nec : DW.frame.Valid Nec := DW.frame.Nec_of DW.hb fun _ _ _ => ⟨rfl, HEq.rfl, trivial⟩
theorem Mie_BF : DIE.frame.Valid BF := DIE.frame.BF_of DIE.hb
theorem Mie_CBF : DIE.frame.Valid CBF := DIE.frame.CBF_of DIE.hb
theorem Mie_not_Nec : ¬ DIE.frame.Valid Nec :=
  DIE.frame.not_Nec_of DIE.hb (a := .e) () false fun _ h => Bool.noConfusion h.2.2

theorem MhE_hb : ∀ p q, MhEF.eqv .t .t p q MhEF.U.w0 ↔ p = q :=
  fun _ _ => ⟨fun h => groot_inj hcyE_inj _ _ _ h.1, fun h => h ▸ ⟨rfl, rfl⟩⟩
theorem MhE_BF : MhEF.Valid BF := MhEF.BF_of MhE_hb
theorem MhE_CBF : MhEF.Valid CBF := MhEF.CBF_of MhE_hb
theorem MhE_not_Nec : ¬ MhEF.Valid Nec :=
  MhEF.not_Nec_of MhE_hb (a := .e) () false fun _ h => Bool.noConfusion h.2

end Wd

/-! ## `𝔐_q,∀`: the item quantifiers over `e` act differently at the other world -/

namespace Al

def isE : Code Empty → Bool
  | .e => true
  | _ => false

/-- Two worlds; identity is rigid; the connectives, the type quantifiers, and the item quantifiers
over types other than `e`, act world by world. At the other world, `∀_e` and `∃_e` take the values
`IA` and `IE`. -/
noncomputable def MqIF (IA IE : Prop) : Frame where
  U := univQ
  eqv := fun a b x y _ => a = b ∧ HEq x y
  teq := fun a b _ => a = b
  neg := fun p w => ¬ p w
  imp := fun p q w => p w → q w
  cnj := fun p q w => p w ∧ q w
  dsj := fun p q w => p w ∨ q w
  bic := fun p q w => p w ↔ q w
  all := fun a f w => cond w (∀ x, f x true) (cond (isE a) IA (∀ x, f x w))
  ex := fun a f w => cond w (∃ x, f x true) (cond (isE a) IE (∃ x, f x w))
  tall := fun Q w => ∀ a, Q a w
  tex := fun Q w => ∃ a, Q a w
  hneg := fun _ => Iff.rfl
  himp := fun _ _ => Iff.rfl
  hcnj := fun _ _ => Iff.rfl
  hdsj := fun _ _ => Iff.rfl
  hbic := fun _ _ => Iff.rfl
  hall := fun _ _ => Iff.rfl
  hex := fun _ _ => Iff.rfl
  htall := fun _ => Iff.rfl
  htex := fun _ => Iff.rfl

section MqI
variable (IA IE : Prop)

theorem MqI_model : (MqIF IA IE).IsModelPIm :=
  (MqIF IA IE).model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => ⟨rfl, HEq.rfl⟩) (fun _ _ _ _ h => ⟨h.1.symm, h.2.symm⟩)
    (fun _ _ _ _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)

theorem MqI_top {n : Nat} {Γ : Ctx n} (ρ : (MqIF IA IE).U.TEnv n) (env : (MqIF IA IE).U.Env Γ ρ) :
    (MqIF IA IE).eval (topF : Fm Γ) ρ env = fun _ => True := by
  funext w
  have e := (MqIF IA IE).eval_all (Γ := Γ) tyT (.var .here) ρ env
  refine propext ⟨fun _ => trivial, fun _ => ?_⟩
  show ¬ (MqIF IA IE).eval (botF : Fm Γ) ρ env w
  rw [botF, e]
  cases w
  · exact fun h => h (fun _ => False)
  · exact fun h => h (fun _ => False)

theorem MqI_LLEqv : (MqIF IA IE).Valid LLEqv := by
  intro ρ env
  refine ((MqIF IA IE).holds_tall _ _ _).mpr fun a => ?_
  refine ((MqIF IA IE).holds_all _ _ _ _).mpr fun x => ((MqIF IA IE).holds_all _ _ _ _).mpr fun y => ?_
  refine ((MqIF IA IE).holds_imp _ _ _ _).mpr fun hxy => ?_
  refine ((MqIF IA IE).holds_all _ _ _ _).mpr fun G => ((MqIF IA IE).holds_imp _ _ _ _).mpr fun hGx => ?_
  have h := (((MqIF IA IE).holds_eqv _ _ _ _ _ _).mp hxy).2
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.trans (cast_heq _ _)))
  subst e
  exact hGx

theorem MqI_NIX : (MqIF IA IE).Valid NIX := by
  intro ρ env
  refine ((MqIF IA IE).holds_tall _ _ _).mpr fun a => ((MqIF IA IE).holds_tall _ _ _).mpr fun b => ?_
  refine ((MqIF IA IE).holds_all _ _ _ _).mpr fun x => ((MqIF IA IE).holds_all _ _ _ _).mpr fun y => ?_
  refine ((MqIF IA IE).holds_imp _ _ _ _).mpr fun hxy => ?_
  refine ((MqIF IA IE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  exact (((MqIF IA IE).eval_eqv _ _ _ _ _ _).trans (funext fun _ => propext ⟨fun _ => trivial, fun _ => hxy⟩)).trans
    (MqI_top IA IE (Γ := ((Ctx.nil.text.text).ext tv1).ext tv0) _ _).symm

theorem MqI_NDX : (MqIF IA IE).Valid NDX := by
  intro ρ env
  refine ((MqIF IA IE).holds_tall _ _ _).mpr fun a => ((MqIF IA IE).holds_tall _ _ _).mpr fun b => ?_
  refine ((MqIF IA IE).holds_all _ _ _ _).mpr fun x => ((MqIF IA IE).holds_all _ _ _ _).mpr fun y => ?_
  refine ((MqIF IA IE).holds_imp _ _ _ _).mpr fun hxy => ?_
  refine ((MqIF IA IE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine Eq.trans ?_ (MqI_top IA IE (Γ := ((Ctx.nil.text.text).ext tv1).ext tv0) _ _).symm
  funext w
  refine propext ⟨fun _ => trivial, fun _ hw => ((MqIF IA IE).holds_neg _ _ _).mp hxy ?_⟩
  have e := (MqIF IA IE).eval_eqv (Γ := ((Ctx.nil.text.text).ext tv1).ext tv0) tv1 tv0 (.var (.there .here)) (.var .here)
    (scons b (scons a ρ)) ((env, x), y)
  have hw' := congrFun e w ▸ hw
  exact cast (congrFun e true).symm hw'

theorem MqI_evalInst {n : Nat} {Γ : Ctx n} {k : Nat} (P : PF k) (as : Fin k → Fm Γ) (ρ : (MqIF IA IE).U.TEnv n)
    (env : (MqIF IA IE).U.Env Γ ρ) (w : Bool) :
    (MqIF IA IE).eval (P.inst as) ρ env w ↔ P.evalP (fun i => (MqIF IA IE).eval (as i) ρ env w) := by
  induction P with
  | atom i => exact Iff.rfl
  | neg P ih => exact not_congr ih
  | imp P Q ihP ihQ => exact imp_congr ihP ihQ
  | conj P Q ihP ihQ => exact and_congr ihP ihQ
  | disj P Q ihP ihQ => exact or_congr ihP ihQ
  | iff P Q ihP ihQ => exact iff_congr ihP ihQ

theorem MqI_Bool : ∀ φ, BoolSch φ → (MqIF IA IE).Valid φ := by
  rintro _ ⟨k, P, Q, hT, rfl⟩ ρ env0
  refine (MqIF IA IE).holds_closeAll k _ ρ (fun env => ?_) env0
  have e : (MqIF IA IE).eval (P.inst (varsT k)) ρ env = (MqIF IA IE).eval (Q.inst (varsT k)) ρ env :=
    funext fun w => propext ((MqI_evalInst IA IE P _ ρ env w).trans ((hT _).trans (MqI_evalInst IA IE Q _ ρ env w).symm))
  exact ((MqIF IA IE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq e⟩

theorem MqI_NIEqv : (MqIF IA IE).Valid NIEqv := by
  intro ρ env
  refine ((MqIF IA IE).holds_tall _ _ _).mpr fun a => ?_
  refine ((MqIF IA IE).holds_all _ _ _ _).mpr fun x => ((MqIF IA IE).holds_all _ _ _ _).mpr fun y => ?_
  refine ((MqIF IA IE).holds_imp _ _ _ _).mpr fun hxy => ?_
  refine ((MqIF IA IE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  exact (((MqIF IA IE).eval_eqv _ _ _ _ _ _).trans (funext fun _ => propext ⟨fun _ => trivial, fun _ => hxy⟩)).trans
    (MqI_top IA IE (Γ := ((Ctx.nil.text).ext tv0).ext tv0) _ _).symm

theorem MqI_NITeq : (MqIF IA IE).Valid NITeq := by
  intro ρ env
  refine ((MqIF IA IE).holds_tall _ _ _).mpr fun a => ((MqIF IA IE).holds_tall _ _ _).mpr fun b => ?_
  refine ((MqIF IA IE).holds_imp _ _ _ _).mpr fun h => ?_
  refine ((MqIF IA IE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  exact (((MqIF IA IE).eval_teq _ _ _ _).trans (funext fun _ => propext ⟨fun _ => trivial, fun _ => h⟩)).trans
    (MqI_top IA IE (Γ := Ctx.nil.text.text) _ _).symm

theorem MqI_NDTeq : (MqIF IA IE).Valid NDTeq := by
  intro ρ env
  refine ((MqIF IA IE).holds_tall _ _ _).mpr fun a => ((MqIF IA IE).holds_tall _ _ _).mpr fun b => ?_
  refine ((MqIF IA IE).holds_imp _ _ _ _).mpr fun h => ?_
  refine ((MqIF IA IE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine Eq.trans ?_ (MqI_top IA IE (Γ := Ctx.nil.text.text) _ _).symm
  funext w
  exact propext ⟨fun _ => trivial, fun _ => h⟩

theorem MqI_Disjoint : (MqIF IA IE).Valid Disjoint := by
  intro ρ env
  refine ((MqIF IA IE).holds_tall _ _ _).mpr fun a => ((MqIF IA IE).holds_tall _ _ _).mpr fun b => ?_
  refine ((MqIF IA IE).holds_imp _ _ _ _).mpr fun hn => ?_
  refine ((MqIF IA IE).holds_all _ _ _ _).mpr fun x => ((MqIF IA IE).holds_all _ _ _ _).mpr fun y => ?_
  refine ((MqIF IA IE).holds_neg _ _ _).mpr fun hxy => ?_
  exact ((MqIF IA IE).holds_neg _ _ _).mp hn (((MqIF IA IE).holds_teq _ _ _ _).mpr (((MqIF IA IE).holds_eqv _ _ _ _ _ _).mp hxy).1)

theorem MqI_Inj : (MqIF IA IE).Valid Inj := by
  intro ρ env
  refine ((MqIF IA IE).holds_tall _ _ _).mpr fun a => ((MqIF IA IE).holds_tall _ _ _).mpr fun b => ?_
  refine ((MqIF IA IE).holds_tall _ _ _).mpr fun c => ((MqIF IA IE).holds_tall _ _ _).mpr fun d => ?_
  refine ((MqIF IA IE).holds_imp _ _ _ _).mpr fun h => ?_
  have h' : Code.arr a c = Code.arr b d := ((MqIF IA IE).holds_teq _ _ _ _).mp h
  injection h' with hab hcd
  exact ((MqIF IA IE).holds_conj _ _ _ _).mpr ⟨((MqIF IA IE).holds_teq _ _ _ _).mpr hab, ((MqIF IA IE).holds_teq _ _ _ _).mpr hcd⟩

theorem MqI_tr_Slogan : (MqIF IA IE).Holds Slogan (fun i => i.elim0) () ↔
    ∀ (x : Unit) (b : Code Empty) (y : univQ.El b → (Bool → Prop)), ¬ ((Code.e : Code Empty) = .arr b .t ∧ HEq x y) := Iff.rfl

theorem MqI_Slogan : (MqIF IA IE).Valid Slogan :=
  ((MqIF IA IE).valid_iff_tr _).mpr ((MqI_tr_Slogan IA IE).mpr fun _ _ _ h => nomatch h.1)

theorem MqI_tr_PExt : (MqIF IA IE).Holds PExt (fun i => i.elim0) () ↔
    ∀ (a c d : Code Empty) (f : univQ.El a → univQ.El c) (g : univQ.El a → univQ.El d),
      (∀ x, c = d ∧ HEq (f x) (g x)) → (Code.arr a c = Code.arr a d ∧ HEq f g) := Iff.rfl

theorem MqI_PExt : (MqIF IA IE).Valid PExt :=
  ((MqIF IA IE).valid_iff_tr _).mpr ((MqI_tr_PExt IA IE).mpr fun a c d f g h => by
    have x0 := Classical.choice (Univ.El_nonempty (U := univQ) a)
    have hcd : c = d := (h x0).1
    subst hcd
    exact ⟨rfl, heq_of_eq (funext fun x => eq_of_heq (h x).2)⟩)

theorem MqI_tr_Cong : (MqIF IA IE).Holds Cong (fun i => i.elim0) () ↔
    ∀ (a b c d : Code Empty) (f : univQ.El a → univQ.El c) (g : univQ.El b → univQ.El d) x y,
      (Code.arr a c = Code.arr b d ∧ HEq f g) ∧ (a = b ∧ HEq x y) → (c = d ∧ HEq (f x) (g y)) := Iff.rfl

theorem MqI_Cong : (MqIF IA IE).Valid Cong :=
  ((MqIF IA IE).valid_iff_tr _).mpr ((MqI_tr_Cong IA IE).mpr fun a b c d f g x y ⟨⟨h1, h2⟩, ⟨_, h4⟩⟩ => by
    injection h1 with hab hcd
    subst hab; subst hcd
    cases h2; cases h4
    exact ⟨rfl, HEq.rfl⟩)


theorem MqI_TBF : ∀ χ, TBFSch χ → (MqIF IA IE).Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine ((MqIF IA IE).holds_imp _ _ _ _).mpr fun h => ?_
  have e : ∀ a, (MqIF IA IE).eval φ (scons a ρ) env = fun _ => True := fun a =>
    (eq_of_heq (((MqIF IA IE).holds_eqv_t _ _ _ _).mp (((MqIF IA IE).holds_tall _ _ _).mp h a)).2).trans
      (MqI_top IA IE (Γ := Ctx.nil.text) _ _)
  refine ((MqIF IA IE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine Eq.trans ?_ (MqI_top IA IE (Γ := Ctx.nil) _ _).symm
  funext w
  exact propext ⟨fun _ => trivial, fun _ a => cast (congrFun (e a) w).symm trivial⟩

theorem MqI_TCBF : ∀ χ, TCBFSch χ → (MqIF IA IE).Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine ((MqIF IA IE).holds_imp _ _ _ _).mpr fun h => ((MqIF IA IE).holds_tall _ _ _).mpr fun a => ?_
  have e := (eq_of_heq (((MqIF IA IE).holds_eqv_t _ _ _ _).mp h).2).trans (MqI_top IA IE (Γ := Ctx.nil) _ _)
  refine ((MqIF IA IE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine Eq.trans ?_ (MqI_top IA IE (Γ := Ctx.nil.text) _ _).symm
  funext w
  exact propext ⟨fun _ => trivial, fun _ => (cast (congrFun e w).symm trivial : ∀ a, _) a⟩

theorem MqI_TNec : (MqIF IA IE).Valid TNec := by
  intro ρ env
  refine ((MqIF IA IE).holds_tall _ _ _).mpr fun a => ((MqIF IA IE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine Eq.trans ?_ (MqI_top IA IE (Γ := Ctx.nil.text) _ _).symm
  funext w
  exact propext ⟨fun _ => trivial, fun _ => ⟨a, rfl⟩⟩

theorem MqI_cast_ex_eq {c : Code Empty} {A' : Type} (hA : (MqIF IA IE).U.El c = A')
    (h : (((MqIF IA IE).U.El c → (MqIF IA IE).U.P) → (MqIF IA IE).U.P) = ((A' → (MqIF IA IE).U.P) → (MqIF IA IE).U.P))
    (Q : A' → (MqIF IA IE).U.P) :
    cast h (fun R => (MqIF IA IE).ex c R) Q = (MqIF IA IE).ex c (fun x => Q (cast hA x)) := by
  subst hA; rfl

theorem MqI_eval_ex {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : (MqIF IA IE).U.TEnv n)
    (env : (MqIF IA IE).U.Env Γ ρ) :
    (MqIF IA IE).eval (Tm.ex σ φ) ρ env =
      (MqIF IA IE).ex ((MqIF IA IE).U.code σ.1 ρ) (fun x => (MqIF IA IE).eval φ ρ (env, cast (Univ.El_code ρ σ.2) x)) :=
  MqI_cast_ex_eq IA IE (Univ.El_code ρ σ.2) _ _

theorem MqI_Nec (hIE : IE) : (MqIF IA IE).Valid Nec := by
  intro ρ env
  refine ((MqIF IA IE).holds_tall _ _ _).mpr fun a => ((MqIF IA IE).holds_all _ _ _ _).mpr fun x => ?_
  refine ((MqIF IA IE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine (MqI_eval_ex IA IE _ _ _ _).trans ?_
  refine Eq.trans ?_ (MqI_top IA IE (Γ := (Ctx.nil.text).ext tv0) _ _).symm
  funext w
  cases w
  · show cond (isE a) IE _ = True
    cases isE a
    · exact propext ⟨fun _ => trivial, fun _ => ⟨x, rfl, HEq.rfl⟩⟩
    · exact propext ⟨fun _ => trivial, fun _ => hIE⟩
  · exact propext ⟨fun _ => trivial, fun _ => ⟨x, rfl, HEq.rfl⟩⟩

theorem MqI_BF (hIA : IA) : (MqIF IA IE).Valid BF := by
  intro ρ env
  refine ((MqIF IA IE).holds_tall _ _ _).mpr fun a => ((MqIF IA IE).holds_all _ _ _ _).mpr fun F => ?_
  refine ((MqIF IA IE).holds_imp _ _ _ _).mpr fun h => ?_
  have e : ∀ x, (MqIF IA IE).eval (Tm.app (.var (.there .here)) (.var .here) : Fm (((Ctx.nil.text).ext tv0.pred).ext tv0))
      (scons a ρ) ((env, F), x) = fun _ => True := fun x =>
    (eq_of_heq (((MqIF IA IE).holds_eqv_t _ _ _ _).mp (((MqIF IA IE).holds_all _ _ _ _).mp h x)).2).trans
      (MqI_top IA IE (Γ := ((Ctx.nil.text).ext tv0.pred).ext tv0) _ _)
  refine ((MqIF IA IE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine ((MqIF IA IE).eval_all _ _ _ _).trans ?_
  refine Eq.trans ?_ (MqI_top IA IE (Γ := (Ctx.nil.text).ext tv0.pred) _ _).symm
  funext w
  cases w
  · show cond (isE a) IA _ = True
    cases isE a
    · exact propext ⟨fun _ => trivial, fun _ x => cast (congrFun (e x) false).symm trivial⟩
    · exact propext ⟨fun _ => trivial, fun _ => hIA⟩
  · exact propext ⟨fun _ => trivial, fun _ x => cast (congrFun (e x) true).symm trivial⟩

theorem MqI_CBF (hIA : ¬ IA) : (MqIF IA IE).Valid CBF := by
  intro ρ env
  refine ((MqIF IA IE).holds_tall _ _ _).mpr fun a => ((MqIF IA IE).holds_all _ _ _ _).mpr fun F => ?_
  refine ((MqIF IA IE).holds_imp _ _ _ _).mpr fun h => ((MqIF IA IE).holds_all _ _ _ _).mpr fun x => ?_
  have e := (eq_of_heq (((MqIF IA IE).holds_eqv_t _ _ _ _).mp h).2).trans
    (MqI_top IA IE (Γ := (Ctx.nil.text).ext tv0.pred) _ _)
  replace e := ((MqIF IA IE).eval_all _ _ _ _).symm.trans e
  refine ((MqIF IA IE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine Eq.trans ?_ (MqI_top IA IE (Γ := ((Ctx.nil.text).ext tv0.pred).ext tv0) _ _).symm
  funext w
  have hw := cast (congrFun e w).symm trivial
  refine propext ⟨fun _ => trivial, fun _ => ?_⟩
  cases w
  · revert hw
    show cond (isE a) IA _ → _
    cases isE a
    · exact fun hw => hw x
    · exact fun hw => absurd hw hIA
  · exact hw x

end MqI

/-- `𝔐_q,∀,A`: at the other world, `∀_e` is false and `∃_e` true. -/
noncomputable abbrev MqIA : Frame := MqIF False True
/-- `𝔐_q,∀,C`: at the other world, `∀_e` is true and `∃_e` false. -/
noncomputable abbrev MqIC : Frame := MqIF True False
/-- `𝔐_q,∀,N`: at the other world, `∀_e` and `∃_e` are both true. -/
noncomputable abbrev MqIN : Frame := MqIF True True

/-- In `𝔐_q,∀,A`, each entity is necessarily such that `⊤`, but `∀x ⊤` is not necessary. -/
theorem MqI_not_BF (IE : Prop) : ¬ (MqIF False IE).Valid BF := fun h => by
  have h0 := ((MqIF False IE).holds_all _ _ _ _).mp (((MqIF False IE).holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e)
    (fun _ _ => True : univQ.El (.arr .e .t))
  have h1 := ((MqIF False IE).holds_imp _ _ _ _).mp h0 (((MqIF False IE).holds_all _ _ _ _).mpr fun x =>
    ((MqIF False IE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq (MqI_top False IE (Γ := ((Ctx.nil.text).ext tv0.pred).ext tv0) _ _).symm⟩)
  have e := (eq_of_heq (((MqIF False IE).holds_eqv_t _ _ _ _).mp h1).2).trans
    (MqI_top False IE (Γ := (Ctx.nil.text).ext tv0.pred) _ _)
  have e2 := (MqIF False IE).eval_all (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here))
    (scons .e fun i => i.elim0) ((), (fun _ _ => True : univQ.El (.arr .e .t)))
  rw [e2] at e
  exact (cast (congrFun e false).symm trivial : False)

/-- In `𝔐_q,∀,C`, `∀x F x` is necessary, for `F` true of each entity at the actual world only;
but no `F x` is necessary. -/
theorem MqI_not_CBF (IE : Prop) : ¬ (MqIF True IE).Valid CBF := fun h => by
  let G : univQ.El (.arr .e .t) := fun _ w => w = true
  have h0 := ((MqIF True IE).holds_all _ _ _ _).mp (((MqIF True IE).holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) G
  have e2 := (MqIF True IE).eval_all (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here))
    (scons .e fun i => i.elim0) ((), G)
  have hb : (MqIF True IE).Holds (boxF (all tv0 (Tm.app (.var (.there .here)) (.var .here))) : Fm ((Ctx.nil.text).ext tv0.pred)) (scons .e fun i => i.elim0) ((), G) := by
    refine ((MqIF True IE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
    rw [e2]
    refine Eq.trans ?_ (MqI_top True IE (Γ := (Ctx.nil.text).ext tv0.pred) _ _).symm
    funext w
    cases w
    · exact propext ⟨fun _ => trivial, fun _ => trivial⟩
    · exact propext ⟨fun _ => trivial, fun _ _ => rfl⟩
  have h1 := ((MqIF True IE).holds_all _ _ _ _).mp (((MqIF True IE).holds_imp _ _ _ _).mp h0 hb) ()
  have e := (eq_of_heq (((MqIF True IE).holds_eqv_t _ _ _ _).mp h1).2).trans
    (MqI_top True IE (Γ := ((Ctx.nil.text).ext tv0.pred).ext tv0) _ _)
  exact Bool.noConfusion (cast (congrFun e false).symm trivial : false = true)

end Al

/-! ## `𝔐_q`: the item quantifiers act world by world, so BF, CBF and Necessitism hold -/

namespace Al
section MqBF
variable (TA TE : (Code Empty → (Bool → Prop)) → Prop)

theorem Mq_cast_ex_eq {c : Code Empty} {A' : Type} (hA : (MqF TA TE).U.El c = A')
    (h : (((MqF TA TE).U.El c → (MqF TA TE).U.P) → (MqF TA TE).U.P) = ((A' → (MqF TA TE).U.P) → (MqF TA TE).U.P))
    (Q : A' → (MqF TA TE).U.P) :
    cast h (fun R => (MqF TA TE).ex c R) Q = (MqF TA TE).ex c (fun x => Q (cast hA x)) := by
  subst hA; rfl

theorem Mq_eval_ex {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : (MqF TA TE).U.TEnv n)
    (env : (MqF TA TE).U.Env Γ ρ) :
    (MqF TA TE).eval (Tm.ex σ φ) ρ env =
      (MqF TA TE).ex ((MqF TA TE).U.code σ.1 ρ) (fun x => (MqF TA TE).eval φ ρ (env, cast (Univ.El_code ρ σ.2) x)) :=
  Mq_cast_ex_eq TA TE (Univ.El_code ρ σ.2) _ _

theorem Mq_Nec : (MqF TA TE).Valid Nec := by
  intro ρ env
  refine ((MqF TA TE).holds_tall _ _ _).mpr fun a => ((MqF TA TE).holds_all _ _ _ _).mpr fun x => ?_
  refine ((MqF TA TE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine (Mq_eval_ex TA TE _ _ _ _).trans ?_
  refine Eq.trans ?_ (Mq_top TA TE (Γ := (Ctx.nil.text).ext tv0) _ _).symm
  funext w
  exact propext ⟨fun _ => trivial, fun _ => ⟨x, rfl, HEq.rfl⟩⟩

theorem Mq_BF : (MqF TA TE).Valid BF := by
  intro ρ env
  refine ((MqF TA TE).holds_tall _ _ _).mpr fun a => ((MqF TA TE).holds_all _ _ _ _).mpr fun F => ?_
  refine ((MqF TA TE).holds_imp _ _ _ _).mpr fun h => ?_
  have e : ∀ x, (MqF TA TE).eval (Tm.app (.var (.there .here)) (.var .here) : Fm (((Ctx.nil.text).ext tv0.pred).ext tv0))
      (scons a ρ) ((env, F), x) = fun _ => True := fun x =>
    (eq_of_heq (((MqF TA TE).holds_eqv_t _ _ _ _).mp (((MqF TA TE).holds_all _ _ _ _).mp h x)).2).trans
      (Mq_top TA TE (Γ := ((Ctx.nil.text).ext tv0.pred).ext tv0) _ _)
  refine ((MqF TA TE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine ((MqF TA TE).eval_all (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here)) (scons a ρ) (env, F)).trans ?_
  refine Eq.trans ?_ (Mq_top TA TE (Γ := (Ctx.nil.text).ext tv0.pred) _ _).symm
  funext w
  exact propext ⟨fun _ => trivial, fun _ x => cast (congrFun (e x) w).symm trivial⟩

theorem Mq_CBF : (MqF TA TE).Valid CBF := by
  intro ρ env
  refine ((MqF TA TE).holds_tall _ _ _).mpr fun a => ((MqF TA TE).holds_all _ _ _ _).mpr fun F => ?_
  refine ((MqF TA TE).holds_imp _ _ _ _).mpr fun h => ((MqF TA TE).holds_all _ _ _ _).mpr fun x => ?_
  have e := (eq_of_heq (((MqF TA TE).holds_eqv_t _ _ _ _).mp h).2).trans
    (Mq_top TA TE (Γ := (Ctx.nil.text).ext tv0.pred) _ _)
  replace e := ((MqF TA TE).eval_all (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here)) (scons a ρ) (env, F)).symm.trans e
  refine ((MqF TA TE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine Eq.trans ?_ (Mq_top TA TE (Γ := ((Ctx.nil.text).ext tv0.pred).ext tv0) _ _).symm
  funext w
  exact propext ⟨fun _ => trivial, fun _ => (cast (congrFun e w).symm trivial : ∀ x, _) x⟩

end MqBF
end Al

/-! ## Tagged haecceity models -/

namespace Tg

theorem Mht_not_BF : ¬ MhtF.Valid BF := fun h => by
  have h0 := (MhtF.holds_all _ _ _ _).mp (h (fun i => i.elim0) () .e) (fun _ => (True, true))
  have h1 := h0 ((MhtF.holds_all _ _ _ _).mpr fun x => (MhtF.holds_eqv_t _ _ _ _).mpr
    (congrArg (fun p => (⟨.t, p⟩ : Σ c : Code univU.Base, univU.El c))
      (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => trivial⟩) rfl)))
  have e := eq_of_heq (Sigma.mk.inj ((MhtF.holds_eqv_t _ _ _ _).mp h1)).2
  have h2 := MhtF.eval_all_snd (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here))
    (scons .e fun i => i.elim0) ((), fun _ => (True, true))
  exact Bool.noConfusion (h2.symm.trans (congrArg Prod.snd e) : false = true)

theorem Mht_not_Nec : ¬ MhtF.Valid Nec := fun h => by
  have h0 := (MhtF.holds_all _ _ _ _).mp (h (fun i => i.elim0) () .e) ()
  have e := eq_of_heq (Sigma.mk.inj ((MhtF.holds_eqv_t _ _ _ _).mp h0)).2
  have h2 := MhtF.eval_ex_snd (Γ := (Ctx.nil.text).ext tv0) tv0 (Tm.eqv tv0 tv0 (.var (.there .here)) (.var .here))
    (scons .e fun i => i.elim0) ((), ())
  exact Bool.noConfusion (h2.symm.trans (congrArg Prod.snd e) : false = true)

/-- `𝔐_hae,int,1`: as `𝔐_hae,int`, but quantified propositions carry the tag `true`. -/
noncomputable abbrev MhtTF : Frame where
  U := univU
  eqv := fun a b x y => hrT a x = hrT b y
  teq := fun a b => a = b
  qtag := fun _ => true

theorem MhtT_model : MhtTF.IsModelPIm :=
  MhtTF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ _ _ h => h.symm) (fun _ _ _ _ _ _ h1 h2 => h1.trans h2)
theorem MhtT_Hae : MhtTF.Valid Hae := (MhtTF.valid_iff_tr _).mpr <| MhtTF.tr_Hae.mpr fun a x => (hrT_hae a x).symm
theorem MhtT_LLEqv : MhtTF.Valid LLEqv := (MhtTF.valid_iff_tr _).mpr <| MhtTF.tr_LLEqv.mpr fun a x y h _ hP =>
  hrT_inj a x y h ▸ hP

/-- `∀x F x` is identical to `⊤`, for `F` taking each entity to a truth with the tag `false`; but no
`F x` is identical to `⊤`. -/
theorem MhtT_not_CBF : ¬ MhtTF.Valid CBF := fun h => by
  have h0 := (MhtTF.holds_all _ _ _ _).mp (h (fun i => i.elim0) () .e) (fun _ => (True, false))
  have h1 := h0 ((MhtTF.holds_eqv_t _ _ _ _).mpr (congrArg (fun p => (⟨.t, p⟩ : Σ c : Code univU.Base, univU.El c))
      (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ _ => trivial⟩)
        (MhtTF.eval_all_snd (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here))
          (scons .e fun i => i.elim0) ((), fun _ => (True, false))))))
  have h2 := (MhtTF.holds_all _ _ _ _).mp h1 ()
  have e := eq_of_heq (Sigma.mk.inj ((MhtTF.holds_eqv_t _ _ _ _).mp h2)).2
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

end Tg

/-! ## `𝔐_nec`: Necessitism without NI≡ -/

namespace Wd

def univNB : Univ where
  W := Bool
  w0 := true
  E := Bool
  Base := Empty
  B := Empty.elim
  neE := ⟨true⟩
  neB := fun b => b.elim

/-- A map on each type with no fixed point. -/
def ffp : (a : Code Empty) → univNB.El a → univNB.El a
  | .e, x => !x
  | .t, p => fun w => ¬ p w
  | .base b, _ => b.elim
  | .arr _ c, f => fun z => ffp c (f z)

theorem ffp_ne : ∀ (a : Code Empty) (x : univNB.El a), ffp a x ≠ x
  | .e, x => fun h => by cases x <;> exact Bool.noConfusion h
  | .t, p => fun h => by
    have e := congrFun h true
    by_cases hp : p true
    · exact (cast e.symm hp) hp
    · exact hp (cast e (show ¬ p true from hp))
  | .base b, _ => b.elim
  | .arr a c, f => fun h => by
    have z0 := Classical.choice (Univ.El_nonempty (U := univNB) a)
    exact ffp_ne c (f z0) (congrFun h z0)

def MNecF : Frame where
  U := univNB
  eqv := fun a b x y w => a = b ∧ cond w (HEq x y) (¬ HEq x y)
  teq := fun a b _ => a = b

theorem MNec_model : MNecF.IsModelPIm :=
  MNecF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => ⟨rfl, HEq.rfl⟩) (fun _ _ _ _ h => ⟨h.1.symm, h.2.symm⟩)
    (fun _ _ _ _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)

theorem MNec_LLEqv : MNecF.Valid LLEqv := by
  intro ρ env
  refine (MNecF.holdsAt_tall _ _ _ _).mpr fun a => ?_
  refine (MNecF.holdsAt_all _ _ _ _ _).mpr fun x => (MNecF.holdsAt_all _ _ _ _ _).mpr fun y => ?_
  refine (MNecF.holdsAt_imp _ _ _ _ _).mpr fun hxy => ?_
  refine (MNecF.holdsAt_all _ _ _ _ _).mpr fun G => (MNecF.holdsAt_imp _ _ _ _ _).mpr fun hGx => ?_
  have e := eq_of_heq ((MNecF.holdsAt_eqv _ _ _ _ _ _ _).mp hxy).2
  have e' : x = y := eq_of_heq ((cast_heq _ _).symm.trans ((heq_of_eq e).trans (cast_heq _ _)))
  subst e'
  exact hGx

theorem MNec_hb : ∀ p q, MNecF.eqv .t .t p q MNecF.U.w0 ↔ p = q :=
  fun _ _ => ⟨fun h => eq_of_heq h.2, fun h => h ▸ ⟨rfl, HEq.rfl⟩⟩

theorem MNec_Nec : MNecF.Valid Nec :=
  (MNecF.valid_iff_tr _).mpr <| MNecF.tr_Nec.mpr fun a x => (MNec_hb _ _).mpr <| by
    refine Eq.trans ?_ (MNecF.eval_topF _ _).symm
    funext w
    refine propext ⟨fun _ => trivial, fun _ => ?_⟩
    cases w
    · exact ⟨ffp a x, rfl, fun h => ffp_ne a x (eq_of_heq h).symm⟩
    · exact ⟨x, rfl, HEq.rfl⟩

theorem MNec_not_NIEqv : ¬ MNecF.Valid NIEqv := fun hv => by
  have h0 := MNecF.tr_NIEqv.mp ((MNecF.valid_iff_tr _).mp hv) .e true true ⟨rfl, HEq.rfl⟩
  have e := ((MNec_hb _ _).mp h0).trans (MNecF.eval_topF (Γ := Ctx.nil) _ _)
  exact (cast (congrFun e false).symm trivial).2 HEq.rfl

theorem MNec_BF : MNecF.Valid BF := MNecF.BF_of MNec_hb
theorem MNec_CBF : MNecF.Valid CBF := MNecF.CBF_of MNec_hb

theorem Mni_BF : DNI.frame.Valid BF := DNI.frame.BF_of DNI.hb
theorem Mni_CBF : DNI.frame.Valid CBF := DNI.frame.CBF_of DNI.hb
theorem Mni_Nec : DNI.frame.Valid Nec := DNI.frame.Nec_of DNI.hb fun _ _ _ => ⟨rfl, HEq.rfl, trivial⟩
theorem Mnd_BF : DND.frame.Valid BF := DND.frame.BF_of DND.hb
theorem Mnd_CBF : DND.frame.Valid CBF := DND.frame.CBF_of DND.hb
theorem Mnd_Nec : DND.frame.Valid Nec := DND.frame.Nec_of DND.hb fun _ _ _ => ⟨rfl, HEq.rfl, trivial⟩

end Wd

end PIF
