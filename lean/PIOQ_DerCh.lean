import PIBF
set_option autoImplicit false

/-!
# Functional Choice and the necessity of distinctness

In PI + Classicism, `□φ` (that is `φ ≡ ⊤`) obeys K, and Functional Choice gives the B axiom at the
actual world: Choice, for the relation `λx.λy.((x ∧ y ≡ ⊤) ∨ (¬x ∧ y ≡ ⊥))`, gives a function `f`
with `f p ≡ ⊤` for every truth `p` and `f ⊥ ≡ ⊥`; these identities are necessary, so `p ≡ ⊥` is
necessarily false. With NI≈ (necessarily), this gives ND≈.
-/

namespace PIF
open Tm Derive

section DerCh
variable {S : Fm Ctx.nil → Prop}

/-! ### K for `□` -/

set_option maxHeartbeats 4000000 in
/-- Classicism: `∀q ((⊤ → q) ≡ q)`. -/
theorem dch_class_topimp (hC : ∀ χ, ClassSch χ → S χ) : S (all tyT (eqv tyT tyT (imp topF pp) pp)) := by
  refine hC _ (Or.inl ⟨0, Γp, imp topF pp, pp, ?_, rfl⟩)
  exact Ent.toProv (Ent.mp (Ent.taut (.imp (.atom 1) (.iff (.imp (.atom 1) (.atom 0)) (.atom 0))) (v2 pp topF)
    (fun _ t => ⟨fun f => f t, fun a _ => a⟩)) (Ent.top (Ax := fun χ => χ = LLEqv) (Hs := [])))

set_option maxHeartbeats 8000000 in
/-- K for `□`, for two propositional variables: from `(p → q) ≡ ⊤` and `p ≡ ⊤`, LL≡ gives
`(⊤ → q) ≡ ⊤`, and Classicism gives `(⊤ → q) ≡ q`. -/
theorem dch_K_pq (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) :
    Prov S Γpq ((boxF (imp pV qV)).imp ((boxF pV).imp (boxF qV))) := by
  let Hs : List (Fm Γpq) := [boxF (imp pV qV), boxF pV]
  have h1 : Ent S Γpq Hs (boxF (imp pV qV)) := Ent.hyp _ 0 (by decide)
  have h2 : Ent S Γpq Hs (boxF pV) := Ent.hyp _ 1 (by decide)
  have hl := Ent.mp ((((Ent.axm (Γ := Γpq) (Hs := Hs) hLL).tinst tyT).inst pV).inst topF) h2
  have hl1 := hl.inst (Tm.lam tyT (boxF (imp (.var .here) (.var (.there .here)))))
  have hl2 : Ent S Γpq Hs ((boxF (imp pV qV)).imp (boxF (imp topF qV))) :=
    Ent.beta hl1 (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  have h3 : Ent S Γpq Hs (boxF (imp topF qV)) := Ent.mp hl2 h1
  have hc : Ent S Γpq Hs (eqv tyT tyT (imp topF qV) qV) :=
    (Ent.axm (Γ := Γpq) (Hs := Hs) (dch_class_topimp hC)).inst qV
  have h4 : Ent S Γpq Hs (eqv tyT tyT qV (imp topF qV)) := Ent.mp (Ent.ofProv (sym_t _ _)) hc
  have h5 : Ent S Γpq ([boxF (imp pV qV)] ++ [boxF pV]) (boxF qV) :=
    Ent.mp (Ent.ofProv (trans_t _ _ _)) (Ent.andI h4 h3)
  exact Ent.toProv (Ent.intro (Hs := []) (Ent.intro h5))

set_option maxHeartbeats 4000000 in
/-- K for `□`, for any two formulas. -/
theorem dch_K_gen (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) {n : Nat} {Γ : Ctx n} (a b : Fm Γ) :
    Prov S Γ ((boxF (imp a b)).imp ((boxF a).imp (boxF b))) :=
  Prov.subst _ _ (dch_K_pq hC hLL) (subPQG a b)

/-- K for `□`, under hypotheses. -/
theorem dch_K (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)}
    {a b : Fm Γ} (h1 : Ent S Γ Hs (boxF (imp a b))) (h2 : Ent S Γ Hs (boxF a)) : Ent S Γ Hs (boxF b) :=
  Ent.mp (Ent.mp (Ent.ofProv (dch_K_gen hC hLL a b)) h1) h2


/-! ### B at the actual world, from Functional Choice -/

/-- `(x ∧ y ≡ ⊤) ∨ (¬x ∧ y ≡ ⊥)` -/
abbrev dch_Rb {n : Nat} {Γ : Ctx n} (x y : Fm Γ) : Fm Γ :=
  disj (conj x (eqv tyT tyT y topF)) (conj (neg x) (eqv tyT tyT y botF))

/-- The relation `λx.λy.((x ∧ y ≡ ⊤) ∨ (¬x ∧ y ≡ ⊥))`. -/
abbrev dch_R {n : Nat} {Γ : Ctx n} : Tm Γ (.arr .t (.arr .t .t)) :=
  lam tyT (lam tyT (dch_Rb (.var (.there .here)) (.var .here)))

/-- The context `p : t, f : t → t`. -/
abbrev dch_Γpf : Ctx 0 := Γp.ext (tyT.arrow tyT)
abbrev dch_p : Fm dch_Γpf := .var (.there .here)
abbrev dch_f : Tm dch_Γpf (tyT.arrow tyT).1 := .var .here
abbrev dch_fp : Fm dch_Γpf := .app dch_f dch_p
abbrev dch_fb : Fm dch_Γpf := .app dch_f botF

/-- The PI theorem `f p ≡ ⊤ → (f ⊥ ≡ ⊥ → ¬(p ≡ ⊥))`. -/
abbrev dch_T1 : Fm dch_Γpf :=
  imp (eqv tyT tyT dch_fp topF) (imp (eqv tyT tyT dch_fb botF) (neg (eqv tyT tyT dch_p botF)))

set_option maxHeartbeats 8000000 in
/-- PI proves `f p ≡ ⊤ → (f ⊥ ≡ ⊥ → ¬(p ≡ ⊥))`: from `p ≡ ⊥`, LL≡ gives `f p ≡ f ⊥`, so `⊤ ≡ ⊥`. -/
theorem dch_T1_prov : PIP dch_Γpf dch_T1 := by
  let Hs : List (Fm dch_Γpf) := [eqv tyT tyT dch_fp topF, eqv tyT tyT dch_fb botF, eqv tyT tyT dch_p botF]
  have ha : Ent (fun χ => χ = LLEqv) dch_Γpf Hs (eqv tyT tyT dch_fp topF) := Ent.hyp _ 0 (by decide)
  have hb : Ent (fun χ => χ = LLEqv) dch_Γpf Hs (eqv tyT tyT dch_fb botF) := Ent.hyp _ 1 (by decide)
  have hc : Ent (fun χ => χ = LLEqv) dch_Γpf Hs (eqv tyT tyT dch_p botF) := Ent.hyp _ 2 (by decide)
  have hl := Ent.mp ((((Ent.axm (Γ := dch_Γpf) (Hs := Hs) (Ax := fun χ => χ = LLEqv) rfl).tinst tyT).inst dch_p).inst botF) hc
  have hl1 := hl.inst (Tm.lam tyT (eqv tyT tyT (.app (.var (.there .here)) (.var (.there (.there .here))))
    (.app (.var (.there .here)) (.var .here))))
  have hl2 : Ent (fun χ => χ = LLEqv) dch_Γpf Hs ((eqv tyT tyT dch_fp dch_fp).imp (eqv tyT tyT dch_fp dch_fb)) :=
    Ent.beta hl1 (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  have hr : Ent (fun χ => χ = LLEqv) dch_Γpf Hs (eqv tyT tyT dch_fp dch_fp) :=
    ((Ent.closed (Γ := dch_Γpf) Prov.refEqv).tinst tyT).inst dch_fp
  have hfb : Ent (fun χ => χ = LLEqv) dch_Γpf Hs (eqv tyT tyT dch_fp dch_fb) := Ent.mp hl2 hr
  have h1 : Ent (fun χ => χ = LLEqv) dch_Γpf Hs (eqv tyT tyT topF dch_fp) := Ent.mp (Ent.ofProv (sym_t _ _)) ha
  have h2 : Ent (fun χ => χ = LLEqv) dch_Γpf Hs (eqv tyT tyT topF dch_fb) :=
    Ent.mp (Ent.ofProv (trans_t _ _ _)) (Ent.andI h1 hfb)
  have h3 : Ent (fun χ => χ = LLEqv) dch_Γpf ([eqv tyT tyT dch_fp topF, eqv tyT tyT dch_fb botF] ++
      [eqv tyT tyT dch_p botF]) (eqv tyT tyT topF botF) :=
    Ent.mp (Ent.ofProv (trans_t _ _ _)) (Ent.andI h2 hb)
  have htb : Ent (fun χ => χ = LLEqv) dch_Γpf ([eqv tyT tyT dch_fp topF, eqv tyT tyT dch_fb botF] ++
      [eqv tyT tyT dch_p botF]) (eqv tyT tyT topF botF).neg :=
    Ent.closed (Γ := dch_Γpf) (d_TopBot (S := fun χ => χ = LLEqv) rfl)
  have h4 : Ent (fun χ => χ = LLEqv) dch_Γpf ([eqv tyT tyT dch_fp topF] ++ [eqv tyT tyT dch_fb botF])
      (neg (eqv tyT tyT dch_p botF)) := Ent.notI h3 htb
  exact Ent.toProv (Ent.intro (Hs := []) (Ent.intro h4))

/-- `∀x R x (f x)`, in the context `p, f`. -/
abbrev dch_ChF : Fm dch_Γpf :=
  all tyT (Tm.app (Tm.app dch_R (.var .here)) (Tm.app (.var (.there .here)) (.var .here)))

set_option maxHeartbeats 16000000 in
/-- PI proves `∀x ∃y R x y`: take `y := ⊤` if `x`, and `y := ⊥` if not. -/
theorem dch_total {Ax : Fm Ctx.nil → Prop} {Hs : List (Fm Γp)} :
    Ent Ax Γp Hs (all tyT (ex tyT (Tm.app (Tm.app dch_R (.var (.there .here))) (.var .here)))) := by
  refine Ent.gen tyT ?_
  let Γx : Ctx 0 := Γp.ext tyT
  let x : Fm Γx := .var .here
  let H : List (Fm Γx) := Hs.map (fun h => h.wk tyT)
  have hT : Ent Ax Γx (H ++ [x]) (dch_Rb x topF) := by
    have hr : Ent Ax Γx (H ++ [x]) (eqv tyT tyT topF topF) := ((Ent.closed (Γ := Γx) Prov.refEqv).tinst tyT).inst topF
    exact Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.disj (.conj (.atom 0) (.atom 1)) (.conj (.neg (.atom 0)) (.atom 2)))))
      (v3 x (eqv tyT tyT topF topF) (eqv tyT tyT topF botF)) (fun _ a b => Or.inl ⟨a, b⟩)) Ent.last hr
  have hF : Ent Ax Γx (H ++ [neg x]) (dch_Rb x botF) := by
    have hr : Ent Ax Γx (H ++ [neg x]) (eqv tyT tyT botF botF) := ((Ent.closed (Γ := Γx) Prov.refEqv).tinst tyT).inst botF
    exact Ent.mp2 (Ent.taut (.imp (.neg (.atom 0)) (.imp (.atom 2) (.disj (.conj (.atom 0) (.atom 1)) (.conj (.neg (.atom 0)) (.atom 2)))))
      (v3 x (eqv tyT tyT botF topF) (eqv tyT tyT botF botF)) (fun _ a b => Or.inr ⟨a, b⟩)) Ent.last hr
  have hT' : Ent Ax Γx (H ++ [x]) (ex tyT (Tm.app (Tm.app dch_R (.var (.there .here))) (.var .here))) :=
    Ent.exI topF (Ent.beta hT (BetaEq.symm (BetaEq.trans (BetaEq.appL _ (.step (.beta _ _))) (.step (.beta _ _)))))
  have hF' : Ent Ax Γx (H ++ [neg x]) (ex tyT (Tm.app (Tm.app dch_R (.var (.there .here))) (.var .here))) :=
    Ent.exI botF (Ent.beta hF (BetaEq.symm (BetaEq.trans (BetaEq.appL _ (.step (.beta _ _))) (.step (.beta _ _)))))
  exact Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.atom 1)) (.imp (.imp (.neg (.atom 0)) (.atom 1)) (.atom 1)))
    (v2 x (ex tyT (Tm.app (Tm.app dch_R (.var (.there .here))) (.var .here)))) (fun _ f g => Classical.byCases f g))
    (Ent.intro hT') (Ent.intro hF')

set_option maxHeartbeats 16000000 in
/-- Functional Choice gives B at the actual world, in the form `p → □¬(p ≡ ⊥)`. Choice gives `f`
with `f p ≡ ⊤` (as `p`) and `f ⊥ ≡ ⊥`; NI≡ makes both necessary, and PI proves
`f p ≡ ⊤ → (f ⊥ ≡ ⊥ → ¬(p ≡ ⊥))`, which Classicism makes necessary; K gives `□¬(p ≡ ⊥)`. -/
theorem dch_B0 (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) (hCh : S Choice) :
    Prov S Γp (pp.imp (boxF (neg (eqv tyT tyT pp botF)))) := by
  have hNI := d_NIEqv_of_Class hC hLL
  have hch := Ent.mp ((((Ent.axm (Γ := Γp) (Hs := [pp]) hCh).tinst tyT).tinst tyT).inst dch_R) dch_total
  have hcl : S (closeCtx dch_Γpf (eqv tyT tyT dch_T1 topF)) := by
    refine hC _ (Or.inl ⟨0, dch_Γpf, dch_T1, topF, ?_, rfl⟩)
    exact Ent.toProv (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1))))
      (v2 dch_T1 topF) (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) (Ent.ofProv dch_T1_prov) Ent.top)
  let Hs2 : List (Fm dch_Γpf) := [pp].map (fun h => h.wk (tyT.arrow tyT)) ++ [dch_ChF]
  have hp : Ent S dch_Γpf Hs2 dch_p := Ent.hyp _ 0 (by decide)
  have hH : Ent S dch_Γpf Hs2 dch_ChF := Ent.hyp _ 1 (by decide)
  have hRp : Ent S dch_Γpf Hs2 (dch_Rb dch_p dch_fp) :=
    Ent.beta (hH.inst dch_p) (BetaEq.trans (BetaEq.appL _ (.step (.beta _ _))) (.step (.beta _ _)))
  have hRb : Ent S dch_Γpf Hs2 (dch_Rb botF dch_fb) :=
    Ent.beta (hH.inst botF) (BetaEq.trans (BetaEq.appL _ (.step (.beta _ _))) (.step (.beta _ _)))
  have hfp : Ent S dch_Γpf Hs2 (eqv tyT tyT dch_fp topF) :=
    Ent.mp2 (Ent.taut (.imp (.disj (.conj (.atom 0) (.atom 1)) (.conj (.neg (.atom 0)) (.atom 2))) (.imp (.atom 0) (.atom 1)))
      (v3 dch_p (eqv tyT tyT dch_fp topF) (eqv tyT tyT dch_fp botF))
      (fun _ h a => h.elim (fun c => c.2) (fun c => (c.1 a).elim))) hRp hp
  have hfb : Ent S dch_Γpf Hs2 (eqv tyT tyT dch_fb botF) :=
    Ent.mp2 (Ent.taut (.imp (.disj (.conj (.atom 0) (.atom 1)) (.conj (.neg (.atom 0)) (.atom 2))) (.imp (.neg (.atom 0)) (.atom 2)))
      (v3 botF (eqv tyT tyT dch_fb topF) (eqv tyT tyT dch_fb botF))
      (fun _ h a => h.elim (fun c => (a c.1).elim) (fun c => c.2))) hRb Ent.top
  have hbp : Ent S dch_Γpf Hs2 (boxF (eqv tyT tyT dch_fp topF)) :=
    Ent.mp ((((Ent.closed (Γ := dch_Γpf) (Hs := Hs2) hNI).tinst tyT).inst dch_fp).inst topF) hfp
  have hbb : Ent S dch_Γpf Hs2 (boxF (eqv tyT tyT dch_fb botF)) :=
    Ent.mp ((((Ent.closed (Γ := dch_Γpf) (Hs := Hs2) hNI).tinst tyT).inst dch_fb).inst botF) hfb
  have hT1 : Ent S dch_Γpf Hs2 (boxF dch_T1) := ((Ent.axm (Γ := dch_Γpf) (Hs := Hs2) hcl).inst dch_p).inst dch_f
  have hZ : Ent S dch_Γpf Hs2 (boxF (neg (eqv tyT tyT dch_p botF))) := dch_K hC hLL (dch_K hC hLL hT1 hbp) hbb
  exact Ent.toProv (Ent.intro (Hs := []) (Ent.exE hch hZ))

/-- One proposition, substituted for `p`. -/
def dch_sub1 {n : Nat} {Γ : Ctx n} (a : Fm Γ) : TSub (fun i => i.elim0) Γp Γ := fun {_} x =>
  match x with
  | .here => a

set_option maxHeartbeats 4000000 in
/-- B at the actual world, for any formula `a`: `a → □¬(a ≡ ⊥)`. -/
theorem dch_B0_gen (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) (hCh : S Choice) {n : Nat} {Γ : Ctx n}
    (a : Fm Γ) : Prov S Γ (a.imp (boxF (neg (eqv tyT tyT a botF)))) :=
  Prov.subst _ _ (dch_B0 hC hLL hCh) (dch_sub1 a)

/-! ### ND≈ -/

/-- `□(α ≈ α)` -/
abbrev dch_Y : Fm Δ2 := boxF (teq tv1 tv1)
/-- `¬(α ≈ β)` -/
abbrev dch_nA : Fm Δ2 := neg Aab

/-- The PI theorem `□(α ≈ α) → (α ≈ β → □(α ≈ β))` (from LL≈). -/
abbrev dch_T3 : Fm Δ2 := imp dch_Y (imp Aab (boxF Aab))

set_option maxHeartbeats 4000000 in
theorem dch_T3_prov : PIP Δ2 dch_T3 := by
  have hQ : Ent (fun χ => χ = LLEqv) Δ2 [] (LLTeq (Tm.tlam (boxF (Tm.teq tv2 tv0)))) := Ent.ofProv (Prov.llTeq _)
  have h1 : Ent (fun χ => χ = LLEqv) Δ2 [] (Aab.imp (dch_Y.imp (boxF Aab))) :=
    Ent.beta ((hQ.tinst tv1).tinst tv0) (BetaEq.imp (.refl _) (BetaEq.imp (BetaEq.tbeta _ _) (BetaEq.tbeta _ _)))
  exact Ent.toProv (Ent.mp (Ent.taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2))) (.imp (.atom 1) (.imp (.atom 0) (.atom 2))))
    (v3 Aab dch_Y (boxF Aab)) (fun _ f b a => f a b)) h1)

/-- The PI theorem `¬(¬A ≡ ⊥) → ((A → □A) → ((¬⊤ ≡ ⊥) → ¬A))`, for `A := α ≈ β`. -/
abbrev dch_T2 : Fm Δ2 :=
  imp (neg (eqv tyT tyT dch_nA botF)) (imp (imp Aab (boxF Aab)) (imp (eqv tyT tyT (neg topF) botF) dch_nA))

set_option maxHeartbeats 8000000 in
/-- If `A ≡ ⊤`, LL≡ gives `¬A ≡ ¬⊤`, so `¬A ≡ ⊥` given `¬⊤ ≡ ⊥`. -/
theorem dch_T2_prov : PIP Δ2 dch_T2 := by
  let Hs : List (Fm Δ2) := [neg (eqv tyT tyT dch_nA botF), imp Aab (boxF Aab), eqv tyT tyT (neg topF) botF, Aab]
  have h0 : Ent (fun χ => χ = LLEqv) Δ2 Hs (neg (eqv tyT tyT dch_nA botF)) := Ent.hyp _ 0 (by decide)
  have h1 : Ent (fun χ => χ = LLEqv) Δ2 Hs (imp Aab (boxF Aab)) := Ent.hyp _ 1 (by decide)
  have h2 : Ent (fun χ => χ = LLEqv) Δ2 Hs (eqv tyT tyT (neg topF) botF) := Ent.hyp _ 2 (by decide)
  have h3 : Ent (fun χ => χ = LLEqv) Δ2 Hs Aab := Ent.hyp _ 3 (by decide)
  have hb : Ent (fun χ => χ = LLEqv) Δ2 Hs (boxF Aab) := Ent.mp h1 h3
  have hl := Ent.mp ((((Ent.axm (Γ := Δ2) (Hs := Hs) (Ax := fun χ => χ = LLEqv) rfl).tinst tyT).inst Aab).inst topF) hb
  have hl1 := hl.inst (Tm.lam tyT (eqv tyT tyT (neg (teq tv1 tv0)) (neg (.var .here))))
  have hl2 : Ent (fun χ => χ = LLEqv) Δ2 Hs ((eqv tyT tyT dch_nA dch_nA).imp (eqv tyT tyT dch_nA (neg topF))) :=
    Ent.beta hl1 (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  have hr : Ent (fun χ => χ = LLEqv) Δ2 Hs (eqv tyT tyT dch_nA dch_nA) :=
    ((Ent.closed (Γ := Δ2) Prov.refEqv).tinst tyT).inst dch_nA
  have h4 : Ent (fun χ => χ = LLEqv) Δ2 Hs (eqv tyT tyT dch_nA (neg topF)) := Ent.mp hl2 hr
  have h5 : Ent (fun χ => χ = LLEqv) Δ2 ([neg (eqv tyT tyT dch_nA botF), imp Aab (boxF Aab),
      eqv tyT tyT (neg topF) botF] ++ [Aab]) (eqv tyT tyT dch_nA botF) :=
    Ent.mp (Ent.ofProv (trans_t _ _ _)) (Ent.andI h4 h2)
  have h6 : Ent (fun χ => χ = LLEqv) Δ2 ([neg (eqv tyT tyT dch_nA botF), imp Aab (boxF Aab),
      eqv tyT tyT (neg topF) botF] ++ [Aab]) (neg (eqv tyT tyT dch_nA botF)) := h0
  have h7 : Ent (fun χ => χ = LLEqv) Δ2 ([neg (eqv tyT tyT dch_nA botF)] ++ [imp Aab (boxF Aab)] ++
      [eqv tyT tyT (neg topF) botF]) dch_nA := Ent.notI h5 h6
  exact Ent.toProv (Ent.intro (Hs := []) (Ent.intro (Hs := [neg (eqv tyT tyT dch_nA botF)]) (Ent.intro h7)))

set_option maxHeartbeats 4000000 in
/-- A PI theorem in the context `α β` is necessary, by Classicism. -/
theorem dch_class2 (hC : ∀ χ, ClassSch χ → S χ) (φ : Fm Δ2) (h : PIP Δ2 φ) :
    S (closeCtx Δ2 (eqv tyT tyT φ topF)) := by
  refine hC _ (Or.inl ⟨2, Δ2, φ, topF, ?_, rfl⟩)
  exact Ent.toProv (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1))))
    (v2 φ topF) (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) (Ent.ofProv h) Ent.top)

set_option maxHeartbeats 16000000 in
/-- Classicism, LL≡ and Functional Choice prove ND≈. If `¬ α ≈ β`, B at the actual world gives
`□¬(¬(α ≈ β) ≡ ⊥)`. Necessarily, NI≈ holds (from LL≈ and the necessary `□(α ≈ α)`) and `¬⊤ ≡ ⊥`;
and PI proves that these together with `¬(¬(α ≈ β) ≡ ⊥)` give `¬ α ≈ β`. So, by K, `□¬(α ≈ β)`. -/
theorem d_NDTeq_of_ClassChoice {S : Fm Ctx.nil → Prop} (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv)
    (hCh : S Choice) : Prov S Ctx.nil NDTeq := by
  have hNI := d_NIEqv_of_Class hC hLL
  let Hs : List (Fm Δ2) := [dch_nA]
  have hnA : Ent S Δ2 Hs dch_nA := Ent.hyp _ 0 (by decide)
  -- B at the actual world
  have hB : Ent S Δ2 Hs (boxF (neg (eqv tyT tyT dch_nA botF))) := Ent.mp (Ent.ofProv (dch_B0_gen hC hLL hCh dch_nA)) hnA
  -- `□(¬⊤ ≡ ⊥)`
  have hc0 : S (eqv tyT tyT (neg topF) botF) := by
    refine hC _ (Or.inl ⟨0, Ctx.nil, neg topF, botF, ?_, rfl⟩)
    exact Prov.taut (.iff (.neg (.neg (.atom 0))) (.atom 0)) (v2 botF botF)
      (fun _ => ⟨fun h => Classical.byContradiction h, fun h n => n h⟩)
  have hnb : Ent S Δ2 Hs (boxF (eqv tyT tyT (neg topF) botF)) :=
    Ent.mp ((((Ent.closed (Γ := Δ2) (Hs := Hs) hNI).tinst tyT).inst (neg topF)).inst botF) (Ent.axm (Γ := Δ2) hc0)
  -- `□(A → □A)`
  have hR : S (tall (boxF (teq tv0 tv0))) := by
    refine hC _ (Or.inl ⟨1, Δ1, teq tv0 tv0, topF, ?_, rfl⟩)
    have hr : Ent (fun χ => χ = LLEqv) Δ1 [] (teq tv0 tv0) := (Ent.closed (Γ := Δ1) Prov.refTeq).tinst tv0
    exact Ent.toProv (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1))))
      (v2 _ topF) (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) hr Ent.top)
  have hY : Ent S Δ2 Hs dch_Y := (Ent.axm (Γ := Δ2) (Hs := Hs) hR).tinst tv1
  have hbY : Ent S Δ2 Hs (boxF dch_Y) :=
    Ent.mp ((((Ent.closed (Γ := Δ2) (Hs := Hs) hNI).tinst tyT).inst (teq tv1 tv1)).inst topF) hY
  have hbT3 : Ent S Δ2 Hs (boxF dch_T3) :=
    ((Ent.axm (Γ := Δ2) (Hs := Hs) (dch_class2 hC dch_T3 dch_T3_prov)).tinst tv1).tinst tv0
  have hbAA : Ent S Δ2 Hs (boxF (imp Aab (boxF Aab))) := dch_K hC hLL hbT3 hbY
  -- the PI theorem, necessarily
  have hbT2 : Ent S Δ2 Hs (boxF dch_T2) :=
    ((Ent.axm (Γ := Δ2) (Hs := Hs) (dch_class2 hC dch_T2 dch_T2_prov)).tinst tv1).tinst tv0
  have hfin : Ent S Δ2 ([] ++ [dch_nA]) (boxF dch_nA) := dch_K hC hLL (dch_K hC hLL (dch_K hC hLL hbT2 hB) hbAA) hnb
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.intro (Hs := []) hfin)))

end DerCh
end PIF
