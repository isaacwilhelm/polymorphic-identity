import PIBF
set_option autoImplicit false

/-!
# ND≈ from ND×, in PI with Classicism

With Classicism and LL≡, `□` (that is, `≡ ⊤`) obeys K, T and 4, and every theorem of PI is
necessary. ND× at the type `t`, applied to a proposition and `⊤`, is the 5 axiom
`¬□p → □¬□p`. So if `¬ α ≈ β`, then `¬□(α ≈ β)` by T, and `□¬□(α ≈ β)` by 5; and NI≈ holds
necessarily (it follows from an instance of LL≈ and `□(α ≈ α)`, which is necessary by 4), so
`□¬(α ≈ β)` by K.

BF and TBF are not derived here. The textbook derivation of BF from B generalizes inside `□`:
it needs `□∀x(◇□F x → F x)`. But ND× is only assumed to hold actually; the case split that
necessitates its instances gives `∀x□(◇□F x → F x)`, and moving `∀x` inside `□` is BF again.
Classicism only makes theorems of PI necessary, and gives no such step.
-/

namespace PIF
open Tm Derive

section DerNDX
variable {S : Fm Ctx.nil → Prop}

/-! ### Tools -/

/-- Replacing axioms by derivations of them. -/
theorem dnx_cut {Ax Ax' : Fm Ctx.nil → Prop} (hA : ∀ χ, Ax χ → Prov Ax' Ctx.nil χ) {n : Nat} {Γ : Ctx n}
    {φ : Fm Γ} (h : Prov Ax Γ φ) : Prov Ax' Γ φ := by
  induction h with
  | taut P as hP => exact Prov.taut P as hP
  | instAll σ φ κ => exact Prov.instAll σ φ κ
  | distAll σ φ ψ => exact Prov.distAll σ φ ψ
  | dualEx σ φ => exact Prov.dualEx σ φ
  | instTAll φ σ => exact Prov.instTAll φ σ
  | distTAll φ ψ => exact Prov.distTAll φ ψ
  | dualTEx φ => exact Prov.dualTEx φ
  | beta h => exact Prov.beta h
  | refEqv => exact Prov.refEqv
  | symEqv => exact Prov.symEqv
  | transEqv => exact Prov.transEqv
  | refTeq => exact Prov.refTeq
  | llTeq Q => exact Prov.llTeq Q
  | ax h => exact hA _ h
  | mp _ _ ih1 ih2 => exact Prov.mp ih1 ih2
  | genAll σ _ ih => exact Prov.genAll σ ih
  | genTAll _ ih => exact Prov.genTAll ih
  | ren ρr _ ih => exact Prov.ren ρr ih
  | strengthen σ _ ih => exact Prov.strengthen σ ih
  | tstrengthen _ ih => exact Prov.tstrengthen ih

/-- A universal closure, once derived, gives the formula in its own context. -/
theorem dnx_open {Ax : Fm Ctx.nil → Prop} : ∀ {n : Nat} (Γ : Ctx n) (χ : Fm Γ),
    Prov Ax Ctx.nil (closeCtx Γ χ) → Prov Ax Γ χ
  | _, .nil, _, h => h
  | _, .ext Γ σ, χ, h => by
    have h1 : Prov Ax Γ (Tm.all σ χ) := dnx_open Γ (Tm.all σ χ) h
    have h2 : Prov Ax (Γ.ext σ) (Tm.all (σ.ren (fun i => i)) (χ.ren (Compl.wkL (Γ := Γ) σ))) :=
      Prov.ren (wkRen σ) h1
    have h3 := Prov.mp h2 (Prov.instAll (σ.ren (fun i => i)) (χ.ren (Compl.wkL (Γ := Γ) σ))
      (Tm.castK (Cat.ren_id σ.1).symm (Tm.var .here)))
    exact (congrArg (Prov Ax (Γ.ext σ)) (eq_of_heq (Compl.contract_heq σ χ))).mp h3
  | _, .text Γ, χ, h => by
    have h1 : Prov Ax Γ (Tm.tall χ) := dnx_open Γ (Tm.tall χ) h
    have h2 : Prov Ax Γ.text (Tm.tall (χ.ren (Compl.twkL Γ))) := Prov.ren (twkRen Γ) h1
    have h3 := Prov.mp h2 (Prov.instTAll (χ.ren (Compl.twkL Γ)) (tvar fz))
    exact (congrArg (Prov Ax Γ.text) (tcontract_eq χ)).mp h3

/-- Classicism, in any context. -/
theorem dnx_cls (hC : ∀ χ, ClassSch χ → S χ) {n : Nat} {Γ : Ctx n} {φ ψ : Fm Γ} (h : PIP Γ (iff φ ψ)) :
    Prov S Γ (eqv tyT tyT φ ψ) :=
  dnx_open Γ _ (Prov.ax (hC _ (Or.inl ⟨n, Γ, φ, ψ, h, rfl⟩)))

/-- Every theorem of PI is necessary. -/
theorem dnx_nec (hC : ∀ χ, ClassSch χ → S χ) {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : PIP Γ φ) :
    Prov S Γ (boxF φ) :=
  dnx_cls hC (Ent.toProv (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1))))
    (v2 φ topF) (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) (Ent.ofProv (Hs := []) h) Ent.top))

/-- The substitution of a proposition for the variable of `Γp`. -/
def dnx_sub1 {n : Nat} {Γ : Ctx n} (a : Fm Γ) : TSub (fun i => i.elim0) Γp Γ := fun {_} x =>
  match x with
  | .here => a

set_option maxHeartbeats 4000000 in
/-- (T) `□a → a`, from LL≡. -/
theorem dnx_T (hLL : S LLEqv) {n : Nat} {Γ : Ctx n} (a : Fm Γ) : Prov S Γ ((boxF a).imp a) := by
  have hT : Prov S Ctx.nil TAx :=
    dnx_cut (Ax := fun χ => χ = Truth) (fun χ (e : χ = Truth) => e ▸ d_Truth hLL) (d_TAx_of_Truth rfl)
  have h : Prov S Γp ((boxF pp).imp pp) := Ent.toProv ((Ent.closed (Γ := Γp) (Hs := []) hT).inst pp)
  exact Prov.subst _ _ h (dnx_sub1 a)

set_option maxHeartbeats 4000000 in
/-- (4) `□a → □□a`, from NI≡ at `t`. -/
theorem dnx_four (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) {n : Nat} {Γ : Ctx n} (a : Fm Γ) :
    Prov S Γ ((boxF a).imp (boxF (boxF a))) := by
  have h : Prov S Γp ((boxF pp).imp (boxF (boxF pp))) :=
    Ent.toProv ((((Ent.closed (Γ := Γp) (Hs := []) (d_NIEqv_of_Class hC hLL)).tinst tyT).inst pp).inst topF)
  exact Prov.subst _ _ h (dnx_sub1 a)

set_option maxHeartbeats 4000000 in
/-- (5) `¬□a → □¬□a`, from ND× at `t`, for `a` and `⊤`. -/
theorem dnx_five (hN : S NDX) {n : Nat} {Γ : Ctx n} (a : Fm Γ) :
    Prov S Γ ((boxF a).neg.imp (boxF (boxF a).neg)) := by
  have h : Prov S Γp ((boxF pp).neg.imp (boxF (boxF pp).neg)) :=
    Ent.toProv (((((Ent.axm (Γ := Γp) (Hs := []) hN).tinst tyT).tinst tyT).inst pp).inst topF)
  exact Prov.subst _ _ h (dnx_sub1 a)

set_option maxHeartbeats 8000000 in
/-- (K) `□(a → b) → □a → □b`. Classicism gives `q ≡ q ∨ (p ∧ (p → q))`; LL≡ replaces `p` and
`p → q` by `⊤`; and Classicism gives `q ∨ (⊤ ∧ ⊤) ≡ ⊤`. -/
theorem dnx_K (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) {n : Nat} {Γ : Ctx n} (a b : Fm Γ) :
    Prov S Γ ((boxF (a.imp b)).imp ((boxF a).imp (boxF b))) := by
  let Hs : List (Fm Γpq) := [boxF (pV.imp qV), boxF pV]
  have h1 : Ent S Γpq Hs (boxF (pV.imp qV)) := Ent.hyp _ 0 (by decide)
  have h2 : Ent S Γpq Hs (boxF pV) := Ent.hyp _ 1 (by decide)
  have c1 : Ent S Γpq Hs (eqv tyT tyT qV (disj qV (conj pV (pV.imp qV)))) :=
    Ent.ofProv (dnx_cls hC (Ent.toProv (Ent.taut (Hs := [])
      (.iff (.atom 1) (.disj (.atom 1) (.conj (.atom 0) (.imp (.atom 0) (.atom 1))))) (v2 pV qV)
      (fun _ => ⟨Or.inl, fun h => h.elim id (fun h' => h'.2 h'.1)⟩))))
  -- LL≡: `p ≡ ⊤`, with `λz. q ≡ q ∨ (z ∧ (p → q))`
  have l1 := Ent.mp ((((Ent.axm (Γ := Γpq) (Hs := Hs) hLL).tinst tyT).inst pV).inst topF) h2
  have l1' := l1.inst (Tm.lam tyT (eqv tyT tyT (.var (.there .here))
    (disj (.var (.there .here)) (conj (.var .here) ((Tm.var (.there (.there .here))).imp (.var (.there .here)))))))
  have e1 : Ent S Γpq Hs ((eqv tyT tyT qV (disj qV (conj pV (pV.imp qV)))).imp
      (eqv tyT tyT qV (disj qV (conj topF (pV.imp qV))))) :=
    Ent.beta l1' (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  -- LL≡: `(p → q) ≡ ⊤`, with `λz. q ≡ q ∨ (⊤ ∧ z)`
  have l2 := Ent.mp ((((Ent.axm (Γ := Γpq) (Hs := Hs) hLL).tinst tyT).inst (pV.imp qV)).inst topF) h1
  have l2' := l2.inst (Tm.lam tyT (eqv tyT tyT (.var (.there .here))
    (disj (.var (.there .here)) (conj topF (.var .here)))))
  have e2 : Ent S Γpq Hs ((eqv tyT tyT qV (disj qV (conj topF (pV.imp qV)))).imp
      (eqv tyT tyT qV (disj qV (conj topF topF)))) :=
    Ent.beta l2' (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  have c2 : Ent S Γpq Hs (eqv tyT tyT (disj qV (conj topF topF)) topF) :=
    Ent.ofProv (dnx_cls hC (Ent.toProv (Ent.mp (Ent.taut (Hs := [])
      (.imp (.atom 1) (.iff (.disj (.atom 0) (.conj (.atom 1) (.atom 1))) (.atom 1))) (v2 qV topF)
      (fun _ t => ⟨fun _ => t, fun _ => Or.inr ⟨t, t⟩⟩)) Ent.top)))
  have e3 := Ent.mp e2 (Ent.mp e1 c1)
  have hK : Ent S Γpq Hs (boxF qV) := Ent.mp (Ent.ofProv (trans_t qV _ topF)) (Ent.andI e3 c2)
  exact Prov.subst _ _ hK (subPQG a b)

/-- K, as a rule. -/
theorem dnx_Kmp (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)}
    {a b : Fm Γ} (h1 : Ent S Γ Hs (boxF (a.imp b))) (h2 : Ent S Γ Hs (boxF a)) : Ent S Γ Hs (boxF b) :=
  Ent.mp2 (Ent.ofProv (dnx_K hC hLL a b)) h1 h2

/-- `□` is closed under implications PI proves. -/
theorem dnx_boxImp (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)}
    {a b : Fm Γ} (h : PIP Γ (a.imp b)) (ha : Ent S Γ Hs (boxF a)) : Ent S Γ Hs (boxF b) :=
  dnx_Kmp hC hLL (Ent.ofProv (dnx_nec hC h)) ha

/-- The same, with two premises. -/
theorem dnx_boxImp2 (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)}
    {a b c : Fm Γ} (h : PIP Γ (a.imp (b.imp c))) (ha : Ent S Γ Hs (boxF a)) (hb : Ent S Γ Hs (boxF b)) :
    Ent S Γ Hs (boxF c) :=
  dnx_Kmp hC hLL (dnx_Kmp hC hLL (Ent.ofProv (dnx_nec hC h)) ha) hb

/-! ### ND≈ -/

set_option maxHeartbeats 4000000 in
/-- NI≈ holds necessarily: PI proves `□(α ≈ α) → (α ≈ β → □(α ≈ β))` (LL≈ with `Λγ.□(α ≈ γ)`),
and `□□(α ≈ α)` by Classicism and 4. -/
theorem dnx_boxNIT (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) {Hs : List (Fm Δ2)} :
    Ent S Δ2 Hs (boxF (Aab.imp (boxF Aab))) := by
  have hpi : PIP Δ2 ((boxF (teq tv1 tv1)).imp (Aab.imp (boxF Aab))) := by
    have hQ : Ent (fun χ => χ = LLEqv) Δ2 [] (LLTeq (Tm.tlam (boxF (Tm.teq tv2 tv0)))) := Ent.ofProv (Prov.llTeq _)
    have h1 : Ent (fun χ => χ = LLEqv) Δ2 [] ((Tm.teq tv1 tv0).imp ((boxF (Tm.teq tv1 tv1)).imp (boxF (Tm.teq tv1 tv0)))) :=
      Ent.beta ((hQ.tinst tv1).tinst tv0) (BetaEq.imp (.refl _) (BetaEq.imp (BetaEq.tbeta _ _) (BetaEq.tbeta _ _)))
    exact Ent.toProv (Ent.mp (Ent.taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2)))
      (.imp (.atom 1) (.imp (.atom 0) (.atom 2)))) (v3 Aab (boxF (teq tv1 tv1)) (boxF Aab))
      (fun _ f b a => f a b)) h1)
  have hB : Ent S Δ2 Hs (boxF (teq tv1 tv1)) :=
    Ent.ofProv (dnx_nec hC ((Ent.closed (Ax := fun χ => χ = LLEqv) (Γ := Δ2) (Hs := []) Prov.refTeq).tinst tv1))
  have hBB : Ent S Δ2 Hs (boxF (boxF (teq tv1 tv1))) := Ent.mp (Ent.ofProv (dnx_four hC hLL _)) hB
  exact dnx_boxImp hC hLL hpi hBB

set_option maxHeartbeats 4000000 in
/-- Classicism, LL≡ and ND× prove ND≈. If `¬ α ≈ β`, then `¬□(α ≈ β)` by T, so `□¬□(α ≈ β)` by
ND× (for `α ≈ β` and `⊤`); and since `□(α ≈ β → □(α ≈ β))`, K gives `□¬(α ≈ β)`. -/
theorem d_NDTeq_of_ClassNDX (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) (hN : S NDX) :
    Prov S Ctx.nil NDTeq := by
  let Hs : List (Fm Δ2) := [neg Aab]
  have hnA : Ent S Δ2 Hs (neg Aab) := Ent.hyp _ 0 (by decide)
  have hT : Ent S Δ2 Hs ((boxF Aab).imp Aab) := Ent.ofProv (dnx_T hLL Aab)
  have hnb : Ent S Δ2 Hs (boxF Aab).neg :=
    Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.atom 1)) (.imp (.neg (.atom 1)) (.neg (.atom 0))))
      (v2 (boxF Aab) Aab) (fun _ f n b => n (f b))) hT hnA
  have h5 : Ent S Δ2 Hs (boxF (boxF Aab).neg) := Ent.mp (Ent.ofProv (dnx_five hN Aab)) hnb
  have hpi : PIP Δ2 ((Aab.imp (boxF Aab)).imp ((boxF Aab).neg.imp (neg Aab))) :=
    Ent.toProv (Ent.taut (Hs := []) (.imp (.imp (.atom 0) (.atom 1)) (.imp (.neg (.atom 1)) (.neg (.atom 0))))
      (v2 Aab (boxF Aab)) (fun _ f n a => n (f a)))
  have hfin : Ent S Δ2 ([] ++ [neg Aab]) (boxF (neg Aab)) := dnx_boxImp2 hC hLL hpi (dnx_boxNIT hC hLL) h5
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.intro (Hs := []) hfin)))

end DerNDX
end PIF
