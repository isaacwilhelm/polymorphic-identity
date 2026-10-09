import PINF
import PISyntax

/-!
# Modal and Booleanist principles

Principles suggested by Bacon and Dorr, "Classicism", stated with PI's own `□φ`, that is
`φ ≡_t ⊤`: the T axiom, Collapse (every truth is necessary), the necessity of identity and of
distinctness, Booleanism (tautologically equivalent propositions are identical), and the Identity
Identity (that `x` is `y` is the proposition that `y` has every property `x` has).
-/
set_option autoImplicit false

namespace PIF
open Tm

/-- (T) `∀_t p (□p → p)` -/
def TAx : Fm Ctx.nil := all tyT (imp (boxF (.var .here)) (.var .here))

/-- (Collapse) `∀_t p (p → □p)` -/
def Collapse : Fm Ctx.nil := all tyT (imp (.var .here) (boxF (.var .here)))

/-- (NI≡) `𝔸α ∀_α x ∀_α y (x ≡_α y → □(x ≡_α y))` -/
def NIEqv : Fm Ctx.nil :=
  tall (all tv0 (all tv0 (imp (eqv tv0 tv0 (.var (.there .here)) (.var .here))
    (boxF (eqv tv0 tv0 (.var (.there .here)) (.var .here))))))

/-- (NI≈) `𝔸α 𝔸β (α ≈ β → □(α ≈ β))` -/
def NITeq : Fm Ctx.nil := tall (tall (imp (teq tv1 tv0) (boxF (teq tv1 tv0))))

/-- (ND≈) `𝔸α 𝔸β (¬ α ≈ β → □¬ α ≈ β)` -/
def NDTeq : Fm Ctx.nil := tall (tall (imp (neg (teq tv1 tv0)) (boxF (neg (teq tv1 tv0)))))

/-- (IdId) `𝔸α ∀_α x ∀_α y ((x ≡_α y) ≡_t ∀_{α→t} F (F x → F y))` -/
def IdId : Fm Ctx.nil :=
  tall (all tv0 (all tv0 (eqv tyT tyT (eqv tv0 tv0 (.var (.there .here)) (.var .here))
    (all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here))))
                       (.app (.var .here) (.var (.there .here))))))))

/-! ### Booleanism, as a schema -/

/-- The context of `k` propositional variables. -/
def ctxT : Nat → Ctx 0
  | 0 => Ctx.nil
  | k + 1 => (ctxT k).ext tyT

/-- The propositional variables of `ctxT k`. -/
def varsT : (k : Nat) → Fin k → Fm (ctxT k)
  | 0 => fun i => i.elim0
  | k + 1 => fun i => if h : i.val = 0 then .var .here else ((varsT k ⟨i.val - 1, by omega⟩).wk tyT : Fm _)

/-- Universal closure over the propositional variables. -/
def closeAll : (k : Nat) → Fm (ctxT k) → Fm Ctx.nil
  | 0 => fun φ => φ
  | k + 1 => fun φ => closeAll k (all tyT φ)

/-- The instance of Booleanism for the formulas `P` and `Q` of propositional logic. -/
def BoolInst {k : Nat} (P Q : PF k) : Fm Ctx.nil :=
  closeAll k (eqv tyT tyT (P.inst (varsT k)) (Q.inst (varsT k)))

/-- (Bool) Every tautologically equivalent pair of propositional forms gives an identity. -/
def BoolSch : Fm Ctx.nil → Prop := fun φ => ∃ k, ∃ P Q : PF k, (PF.iff P Q).Taut ∧ φ = BoolInst P Q

/-- The instance `∀_t p (¬¬p ≡_t p)`. -/
def DNeg : Fm Ctx.nil := BoolInst (k := 1) (.neg (.neg (.atom 0))) (.atom 0)

theorem DNeg_bool : BoolSch DNeg :=
  ⟨1, .neg (.neg (.atom 0)), .atom 0,
    fun v => show (¬¬ v 0 ↔ v 0) from ⟨fun h => Classical.byContradiction h, fun h n => n h⟩, rfl⟩


theorem DNeg_eq : DNeg = all tyT (eqv tyT tyT (neg (neg (.var .here))) (.var .here)) := rfl

/-! ## Derivations -/

section Derivations
open Derive
variable {S : Fm Ctx.nil → Prop}

abbrev Γp : Ctx 0 := Ctx.nil.ext tyT
abbrev pp : Fm Γp := .var .here

set_option maxHeartbeats 4000000 in
/-- Truth proves T: from `p ≡ ⊤`, Sym≡ gives `⊤ ≡ p`, and Truth gives `⊤ → p`. -/
theorem d_TAx_of_Truth (hT : S Truth) : Prov S Ctx.nil TAx := by
  have hb : Ent S Γp [boxF pp] (eqv tyT tyT pp topF) := Ent.hyp _ 0 (by decide)
  have hsym : Ent S Γp [boxF pp] ((eqv tyT tyT pp topF).imp (eqv tyT tyT topF pp)) :=
    ((((Ent.closed (Γ := Γp) (Hs := [boxF pp]) (Ax := S) Prov.symEqv).tinst tyT).tinst tyT).inst pp).inst topF
  have htr : Ent S Γp [boxF pp] ((eqv tyT tyT topF pp).imp (topF.imp pp)) :=
    ((Ent.axm (Γ := Γp) (Hs := [boxF pp]) hT).inst topF).inst pp
  have h : Ent S Γp ([] ++ [boxF pp]) pp := Ent.mp (Ent.mp htr (Ent.mp hsym hb)) Ent.top
  exact Ent.toProv (Ent.gen tyT (Hs := []) (Ent.intro h))

set_option maxHeartbeats 4000000 in
/-- PropExt≡ proves Collapse: a truth is materially equivalent to `⊤`. -/
theorem d_Collapse_of_PropExt (hP : S PropExt) : Prov S Ctx.nil Collapse := by
  have hp : Ent S Γp [pp] pp := Ent.hyp _ 0 (by decide)
  have hpe : Ent S Γp [pp] ((iff pp topF).imp (eqv tyT tyT pp topF)) :=
    ((Ent.axm (Γ := Γp) (Hs := [pp]) hP).inst pp).inst topF
  have h : Ent S Γp ([] ++ [pp]) (boxF pp) :=
    Ent.mp hpe (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1)))) (v2 pp topF)
      (fun _ x y => ⟨fun _ => y, fun _ => x⟩)) hp Ent.top)
  exact Ent.toProv (Ent.gen tyT (Hs := []) (Ent.intro h))

abbrev Exy : Fm Γxy := eqv tv0 tv0 (.var (.there .here)) (.var .here)

set_option maxHeartbeats 4000000 in
/-- Collapse proves NI≡. -/
theorem d_NIEqv_of_Collapse (hC : S Collapse) : Prov S Ctx.nil NIEqv := by
  have h : Ent S Γxy ([] ++ [Exy]) (boxF Exy) :=
    Ent.mp ((Ent.axm (Γ := Γxy) (Hs := [Exy]) hC).inst Exy) (Ent.hyp _ 0 (by decide))
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen tv0 (Hs := []) (Ent.gen tv0 (Hs := []) (Ent.intro h))))

set_option maxHeartbeats 4000000 in
/-- Collapse proves NI≈. -/
theorem d_NITeq_of_Collapse (hC : S Collapse) : Prov S Ctx.nil NITeq := by
  have h : Ent S Δ2 ([] ++ [teq tv1 tv0]) (boxF (teq tv1 tv0)) :=
    Ent.mp ((Ent.axm (Γ := Δ2) (Hs := [teq tv1 tv0]) hC).inst (teq tv1 tv0)) (Ent.hyp _ 0 (by decide))
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.intro h)))

set_option maxHeartbeats 4000000 in
/-- Collapse proves ND≈. -/
theorem d_NDTeq_of_Collapse (hC : S Collapse) : Prov S Ctx.nil NDTeq := by
  have h : Ent S Δ2 ([] ++ [neg (teq tv1 tv0)]) (boxF (neg (teq tv1 tv0))) :=
    Ent.mp ((Ent.axm (Γ := Δ2) (Hs := [neg (teq tv1 tv0)]) hC).inst (neg (teq tv1 tv0))) (Ent.hyp _ 0 (by decide))
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.intro h)))

set_option maxHeartbeats 4000000 in
/-- Collapse and Int≈ prove Ext≈. -/
theorem d_ExtT_of_Collapse (hC : S Collapse) (hI : S IntT) : Prov S Ctx.nil ExtT := by
  have hH : Ent S Δ2 [HypE] HypE := Ent.hyp _ 0 (by decide)
  have hb1 : Ent S Δ2 [HypE] (boxF (subT : Fm Δ2)) :=
    Ent.mp ((Ent.axm (Γ := Δ2) (Hs := [HypE]) hC).inst (subT : Fm Δ2)) (Ent.andE1 hH)
  have hb2 : Ent S Δ2 [HypE] (boxF (supT : Fm Δ2)) :=
    Ent.mp ((Ent.axm (Γ := Δ2) (Hs := [HypE]) hC).inst (supT : Fm Δ2)) (Ent.andE2 hH)
  have hi : Ent S Δ2 [HypE] ((conj (boxF (subT : Fm Δ2)) (boxF (supT : Fm Δ2))).imp (teq tv1 tv0)) :=
    ((Ent.axm (Γ := Δ2) (Hs := [HypE]) hI).tinst tv1).tinst tv0
  have h2 : Ent S Δ2 ([] ++ [HypE]) (teq tv1 tv0) := Ent.mp hi (Ent.andI hb1 hb2)
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.intro (Hs := []) h2)))

abbrev HypI : Fm Δ2 := conj (boxF (subT : Fm Δ2)) (boxF (supT : Fm Δ2))

set_option maxHeartbeats 4000000 in
/-- T and Ext≈ prove Int≈. -/
theorem d_IntT_of_TAx (hT : S TAx) (hE : S ExtT) : Prov S Ctx.nil IntT := by
  have hH : Ent S Δ2 [HypI] HypI := Ent.hyp _ 0 (by decide)
  have h1 : Ent S Δ2 [HypI] (subT : Fm Δ2) :=
    Ent.mp ((Ent.axm (Γ := Δ2) (Hs := [HypI]) hT).inst (subT : Fm Δ2)) (Ent.andE1 hH)
  have h2 : Ent S Δ2 [HypI] (supT : Fm Δ2) :=
    Ent.mp ((Ent.axm (Γ := Δ2) (Hs := [HypI]) hT).inst (supT : Fm Δ2)) (Ent.andE2 hH)
  have he : Ent S Δ2 [HypI] ((conj (subT : Fm Δ2) (supT : Fm Δ2)).imp (teq tv1 tv0)) :=
    ((Ent.axm (Γ := Δ2) (Hs := [HypI]) hE).tinst tv1).tinst tv0
  have h3 : Ent S Δ2 ([] ++ [HypI]) (teq tv1 tv0) := Ent.mp he (Ent.andI h1 h2)
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.intro (Hs := []) h3)))

abbrev Axy : Fm Γxy := all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here))))
  (.app (.var .here) (.var (.there .here))))

set_option maxHeartbeats 4000000 in
/-- The Identity Identity and Truth prove LL≡. -/
theorem d_LLEqv_of_IdId (hI : S IdId) (hT : S Truth) : Prov S Ctx.nil LLEqv := by
  have hid : Ent S Γxy [Exy] (eqv tyT tyT Exy Axy) :=
    (((Ent.axm (Γ := Γxy) (Hs := [Exy]) hI).tinst tv0).inst (.var (.there .here))).inst (.var .here)
  have htr : Ent S Γxy [Exy] ((eqv tyT tyT Exy Axy).imp (Exy.imp Axy)) :=
    ((Ent.axm (Γ := Γxy) (Hs := [Exy]) hT).inst Exy).inst Axy
  have h : Ent S Γxy ([] ++ [Exy]) Axy := Ent.mp (Ent.mp htr hid) (Ent.hyp _ 0 (by decide))
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen tv0 (Hs := []) (Ent.gen tv0 (Hs := []) (Ent.intro h))))

set_option maxHeartbeats 4000000 in
/-- PropExt≡ and LL≡ prove the Identity Identity. -/
theorem d_IdId_of_PropExt (hP : S PropExt) (hLL : S LLEqv) : Prov S Ctx.nil IdId := by
  have hl : Ent S Γxy [] (Exy.imp Axy) :=
    (((Ent.axm (Γ := Γxy) (Hs := []) hLL).tinst tv0).inst (.var (.there .here))).inst (.var .here)
  have hH : Ent S Γxy [Axy] Axy := Ent.hyp _ 0 (by decide)
  have h1 := Ent.inst hH (.lam tv0 (eqv tv0 tv0 (.var (.there (.there .here))) (.var .here)))
  have h2 : Ent S Γxy [Axy]
      ((eqv tv0 tv0 (.var (.there .here)) (.var (.there .here))).imp Exy) :=
    Ent.beta h1 (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  have hr : Ent S Γxy [Axy] (eqv tv0 tv0 (.var (.there .here)) (.var (.there .here))) :=
    ((Ent.closed (Γ := Γxy) Prov.refEqv).tinst tv0).inst (.var (.there .here))
  have h3 : Ent S Γxy ([] ++ [Axy]) Exy := Ent.mp h2 hr
  have hiff : Ent S Γxy [] (iff Exy Axy) :=
    Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.atom 1)) (.imp (.imp (.atom 1) (.atom 0)) (.iff (.atom 0) (.atom 1))))
      (v2 Exy Axy) (fun _ f g => ⟨f, g⟩)) hl (Ent.intro h3)
  have hpe : Ent S Γxy [] ((iff Exy Axy).imp (eqv tyT tyT Exy Axy)) :=
    ((Ent.axm (Γ := Γxy) (Hs := []) hP).inst Exy).inst Axy
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen tv0 (Hs := []) (Ent.gen tv0 (Hs := []) (Ent.mp hpe hiff))))

theorem prov_closeAll : ∀ (k : Nat) (φ : Fm (ctxT k)), Prov S (ctxT k) φ → Prov S Ctx.nil (closeAll k φ)
  | 0, _, h => h
  | k + 1, _, h => prov_closeAll k _ (Prov.genAll tyT h)

/-- The substitution of two propositions for `p` and `q`. -/
def subPQ {k : Nat} (a b : Fm (ctxT k)) : TSub tvar Γpq (ctxT k) := fun {_} x =>
  match x with
  | .here => b
  | .there .here => a

set_option maxHeartbeats 4000000 in
/-- PropExt≡ proves every instance of Booleanism. -/
theorem d_Bool_of_PropExt (hP : S PropExt) : ∀ φ, BoolSch φ → Prov S Ctx.nil φ := by
  rintro _ ⟨k, P, Q, hT, rfl⟩
  have hbase : Prov S Γpq ((iff pV qV).imp (eqv tyT tyT pV qV)) :=
    Ent.toProv (((Ent.axm (Γ := Γpq) (Hs := []) hP).inst pV).inst qV)
  have h2 : Prov S (ctxT k) ((iff (P.inst (varsT k)) (Q.inst (varsT k))).imp
      (eqv tyT tyT (P.inst (varsT k)) (Q.inst (varsT k)))) :=
    Prov.subst _ _ hbase (subPQ (P.inst (varsT k)) (Q.inst (varsT k)))
  exact prov_closeAll k _ (Prov.mp (Prov.taut (PF.iff P Q) (varsT k) hT) h2)


abbrev HsA : List (Fm Γpq) := [iff pV qV, pV]
abbrev HsB : List (Fm Γpq) := [iff pV qV, neg pV]

set_option maxHeartbeats 16000000 in
/-- If `p ↔ q` and `p`, Collapse gives `p ≡ ⊤` and `q ≡ ⊤`, so `p ≡ q`. -/
theorem collapse_caseA (hC : S Collapse) : Ent S Γpq HsA (eqv tyT tyT pV qV) := by
  have hi : Ent S Γpq HsA (iff pV qV) := Ent.hyp _ 0 (by decide)
  have hp : Ent S Γpq HsA pV := Ent.hyp _ 1 (by decide)
  have hq : Ent S Γpq HsA qV :=
    Ent.mp2 (Ent.taut (.imp (.iff (.atom 0) (.atom 1)) (.imp (.atom 0) (.atom 1))) (v2 pV qV) (fun _ e a => e.mp a)) hi hp
  have hcp : Ent S Γpq HsA (eqv tyT tyT pV topF) := Ent.mp ((Ent.axm (Γ := Γpq) (Hs := HsA) hC).inst pV) hp
  have hcq : Ent S Γpq HsA (eqv tyT tyT qV topF) := Ent.mp ((Ent.axm (Γ := Γpq) (Hs := HsA) hC).inst qV) hq
  have hsym : Ent S Γpq HsA ((eqv tyT tyT qV topF).imp (eqv tyT tyT topF qV)) :=
    ((((Ent.closed (Γ := Γpq) (Hs := HsA) (Ax := S) Prov.symEqv).tinst tyT).tinst tyT).inst qV).inst topF
  have htr : Ent S Γpq HsA ((conj (eqv tyT tyT pV topF) (eqv tyT tyT topF qV)).imp (eqv tyT tyT pV qV)) :=
    ((((((Ent.closed (Γ := Γpq) (Hs := HsA) (Ax := S) Prov.transEqv).tinst tyT).tinst tyT).tinst tyT).inst pV).inst
      topF).inst qV
  exact Ent.mp htr (Ent.andI hcp (Ent.mp hsym hcq))

set_option maxHeartbeats 16000000 in
/-- If `p ↔ q` and `¬p`, Collapse gives `¬p ≡ ¬q`; then LL≡, with `F := λr.(p ≡ ¬r)`, and `¬¬p ≡ p`,
`¬¬q ≡ q`, give `p ≡ q`. -/
theorem collapse_caseB (hC : S Collapse) (hD : S DNeg) (hLL : S LLEqv) : Ent S Γpq HsB (eqv tyT tyT pV qV) := by
  have hD' : S (all tyT (eqv tyT tyT (neg (neg (.var .here))) (.var .here))) := DNeg_eq ▸ hD
  have hi : Ent S Γpq HsB (iff pV qV) := Ent.hyp _ 0 (by decide)
  have hnp : Ent S Γpq HsB (neg pV) := Ent.hyp _ 1 (by decide)
  have hnq : Ent S Γpq HsB (neg qV) :=
    Ent.mp2 (Ent.taut (.imp (.iff (.atom 0) (.atom 1)) (.imp (.neg (.atom 0)) (.neg (.atom 1)))) (v2 pV qV)
      (fun _ e na b => na (e.mpr b))) hi hnp
  have hcp : Ent S Γpq HsB (eqv tyT tyT (neg pV) topF) := Ent.mp ((Ent.axm (Γ := Γpq) (Hs := HsB) hC).inst (neg pV)) hnp
  have hcq : Ent S Γpq HsB (eqv tyT tyT (neg qV) topF) := Ent.mp ((Ent.axm (Γ := Γpq) (Hs := HsB) hC).inst (neg qV)) hnq
  have hsym : Ent S Γpq HsB ((eqv tyT tyT (neg qV) topF).imp (eqv tyT tyT topF (neg qV))) :=
    ((((Ent.closed (Γ := Γpq) (Hs := HsB) (Ax := S) Prov.symEqv).tinst tyT).tinst tyT).inst (neg qV)).inst topF
  have htr : Ent S Γpq HsB ((conj (eqv tyT tyT (neg pV) topF) (eqv tyT tyT topF (neg qV))).imp
      (eqv tyT tyT (neg pV) (neg qV))) :=
    ((((((Ent.closed (Γ := Γpq) (Hs := HsB) (Ax := S) Prov.transEqv).tinst tyT).tinst tyT).tinst tyT).inst (neg pV)).inst
      topF).inst (neg qV)
  have hnn : Ent S Γpq HsB (eqv tyT tyT (neg pV) (neg qV)) := Ent.mp htr (Ent.andI hcp (Ent.mp hsym hcq))
  have hl := ((((Ent.axm (Γ := Γpq) (Hs := HsB) hLL).tinst tyT).inst (neg pV)).inst (neg qV))
  have hall := Ent.mp hl hnn
  have h1 := Ent.inst hall (.lam tyT (eqv tyT tyT (.var (.there (.there .here))) (neg (.var .here))))
  have h2 : Ent S Γpq HsB ((eqv tyT tyT pV (neg (neg pV))).imp (eqv tyT tyT pV (neg (neg qV)))) :=
    Ent.beta h1 (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  have hdp : Ent S Γpq HsB (eqv tyT tyT (neg (neg pV)) pV) := (Ent.axm (Γ := Γpq) (Hs := HsB) hD').inst pV
  have hdq : Ent S Γpq HsB (eqv tyT tyT (neg (neg qV)) qV) := (Ent.axm (Γ := Γpq) (Hs := HsB) hD').inst qV
  have hsym2 : Ent S Γpq HsB ((eqv tyT tyT (neg (neg pV)) pV).imp (eqv tyT tyT pV (neg (neg pV)))) :=
    ((((Ent.closed (Γ := Γpq) (Hs := HsB) (Ax := S) Prov.symEqv).tinst tyT).tinst tyT).inst (neg (neg pV))).inst pV
  have h3 : Ent S Γpq HsB (eqv tyT tyT pV (neg (neg qV))) := Ent.mp h2 (Ent.mp hsym2 hdp)
  have htr2 : Ent S Γpq HsB ((conj (eqv tyT tyT pV (neg (neg qV))) (eqv tyT tyT (neg (neg qV)) qV)).imp
      (eqv tyT tyT pV qV)) :=
    ((((((Ent.closed (Γ := Γpq) (Hs := HsB) (Ax := S) Prov.transEqv).tinst tyT).tinst tyT).tinst tyT).inst pV).inst
      (neg (neg qV))).inst qV
  exact Ent.mp htr2 (Ent.andI h3 hdq)

set_option maxHeartbeats 4000000 in
/-- Collapse, `¬¬p ≡ p` (an instance of Booleanism), and LL≡ prove PropExt≡. -/
theorem d_PropExt_of_Collapse (hC : S Collapse) (hD : S DNeg) (hLL : S LLEqv) : Prov S Ctx.nil PropExt := by
  have hA : Ent S Γpq [iff pV qV] (pV.imp (eqv tyT tyT pV qV)) := Ent.intro (collapse_caseA hC)
  have hB : Ent S Γpq [iff pV qV] ((neg pV).imp (eqv tyT tyT pV qV)) := Ent.intro (collapse_caseB hC hD hLL)
  have h : Ent S Γpq ([] ++ [iff pV qV]) (eqv tyT tyT pV qV) :=
    Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.atom 1)) (.imp (.imp (.neg (.atom 0)) (.atom 1)) (.atom 1)))
      (v2 pV (eqv tyT tyT pV qV)) (fun _ f g => Classical.byCases f g)) hA hB
  exact Ent.toProv (Ent.gen tyT (Hs := []) (Ent.gen tyT (Hs := []) (Ent.intro h)))


set_option maxHeartbeats 4000000 in
/-- T proves `⊤ ≢ ⊥`: if `⊤ ≡ ⊥`, then `⊥ ≡ ⊤`, that is `□⊥`, so T gives `⊥`. -/
theorem d_TopBot_of_TAx (hT : S TAx) : Prov S Ctx.nil TopBot := by
  have hE : Ent S Ctx.nil [eqv tyT tyT topF botF] (eqv tyT tyT topF botF) := Ent.hyp _ 0 (by decide)
  have hsym : Ent S Ctx.nil [eqv tyT tyT topF botF] ((eqv tyT tyT topF botF).imp (eqv tyT tyT botF topF)) :=
    ((((Ent.closed (Γ := Ctx.nil) (Hs := [eqv tyT tyT topF botF]) (Ax := S) Prov.symEqv).tinst tyT).tinst tyT).inst
      topF).inst botF
  have hb : Ent S Ctx.nil [eqv tyT tyT topF botF] (boxF (botF : Fm Ctx.nil)) := Ent.mp hsym hE
  have h1 : Ent S Ctx.nil ([] ++ [eqv tyT tyT topF botF]) botF :=
    Ent.mp ((Ent.axm (Γ := Ctx.nil) (Hs := [eqv tyT tyT topF botF]) hT).inst botF) hb
  have h2 : Ent S Ctx.nil ([] ++ [eqv tyT tyT topF botF]) (botF : Fm Ctx.nil).neg := Ent.top
  exact Ent.toProv (Ent.notI h1 h2)
end Derivations

end PIF
