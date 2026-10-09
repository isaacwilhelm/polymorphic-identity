import PICanonical
import PIModal

/-!
# Barcan formulas for the type quantifiers, and Type Necessitism
-/
set_option autoImplicit false

namespace PIF
open Tm Derive

/-- (TBF), the instance for `φ`: `𝔸α □φ → □𝔸α φ`. -/
def TBFI (φ : Fm Ctx.nil.text) : Fm Ctx.nil := imp (tall (boxF φ)) (boxF (tall φ))
def TBFSch : Fm Ctx.nil → Prop := fun χ => ∃ φ, χ = TBFI φ

/-- (TCBF), the instance for `φ`: `□𝔸α φ → 𝔸α □φ`. -/
def TCBFI (φ : Fm Ctx.nil.text) : Fm Ctx.nil := imp (boxF (tall φ)) (tall (boxF φ))
def TCBFSch : Fm Ctx.nil → Prop := fun χ => ∃ φ, χ = TCBFI φ

/-- (TNec) `𝔸α □𝔼β (α ≈ β)`: every type is necessarily some type. -/
def TNec : Fm Ctx.nil := tall (boxF (tex (teq tv1 tv0)))

section Derivs
variable {S : Fm Ctx.nil → Prop}

theorem tcontract_eq {n : Nat} {Γ : Ctx n} (ψ : Fm Γ.text) : (ψ.ren (Compl.twkL Γ)).tinst (tvar fz) = ψ :=
  eq_of_heq (Compl.tcontract_heq ψ)

set_option maxHeartbeats 4000000 in
/-- Collapse and T prove every instance of TBF. -/
theorem d_TBF (hC : S Collapse) (hT : S TAx) : ∀ χ, TBFSch χ → Prov S Ctx.nil χ := by
  rintro _ ⟨φ, rfl⟩
  have hH : Ent S Ctx.nil.text ([tall (boxF φ)].map (fun h => (h.twk : Fm Ctx.nil.text)))
      (tall ((boxF φ).ren (Compl.twkL Ctx.nil))) := Ent.hyp _ 0 (by exact Nat.one_pos)
  have h1 := (congrArg (Ent S _ _) (tcontract_eq (boxF φ))).mp (Ent.tinst hH (tvar fz))
  have h2 : Ent S Ctx.nil.text ([tall (boxF φ)].map (fun h => (h.twk : Fm Ctx.nil.text))) φ :=
    Ent.mp ((Ent.axm (Γ := Ctx.nil.text) hT).inst φ) h1
  have h3 : Ent S Ctx.nil ([] ++ [tall (boxF φ)]) (tall φ) := Ent.tgen h2
  have h4 : Ent S Ctx.nil ([] ++ [tall (boxF φ)]) (boxF (tall φ)) :=
    Ent.mp ((Ent.axm (Γ := Ctx.nil) hC).inst (tall φ)) h3
  exact Ent.toProv (Ent.intro h4)

set_option maxHeartbeats 4000000 in
/-- Collapse and T prove every instance of TCBF. -/
theorem d_TCBF (hC : S Collapse) (hT : S TAx) : ∀ χ, TCBFSch χ → Prov S Ctx.nil χ := by
  rintro _ ⟨φ, rfl⟩
  have hH : Ent S Ctx.nil.text ([boxF (tall φ)].map (fun h => (h.twk : Fm Ctx.nil.text)))
      (boxF (tall (φ.ren (Compl.twkL Ctx.nil)))) := Ent.hyp _ 0 (by exact Nat.one_pos)
  have h0 : Ent S Ctx.nil.text ([boxF (tall φ)].map (fun h => (h.twk : Fm Ctx.nil.text)))
      (tall (φ.ren (Compl.twkL Ctx.nil))) :=
    Ent.mp ((Ent.axm (Γ := Ctx.nil.text) hT).inst (tall (φ.ren (Compl.twkL Ctx.nil)))) hH
  have h1 := (congrArg (Ent S _ _) (tcontract_eq φ)).mp (Ent.tinst h0 (tvar fz))
  have h2 : Ent S Ctx.nil.text ([boxF (tall φ)].map (fun h => (h.twk : Fm Ctx.nil.text))) (boxF φ) :=
    Ent.mp ((Ent.axm (Γ := Ctx.nil.text) hC).inst φ) h1
  have h3 : Ent S Ctx.nil ([] ++ [boxF (tall φ)]) (tall (boxF φ)) := Ent.tgen h2
  exact Ent.toProv (Ent.intro h3)

set_option maxHeartbeats 4000000 in
/-- Collapse proves Type Necessitism. -/
theorem d_TNec (hC : S Collapse) : Prov S Ctx.nil TNec := by
  have hr : Ent S Δ1 [] (teq tv0 tv0) := (Ent.closed (Γ := Δ1) Prov.refTeq).tinst tv0
  have he : Ent S Δ1 [] (tex (teq tv1 tv0)) := Ent.texI (φ := teq tv1 tv0) tv0 hr
  have hb : Ent S Δ1 [] (boxF (tex (teq tv1 tv0))) := Ent.mp ((Ent.axm (Γ := Δ1) hC).inst _) he
  exact Ent.toProv (Ent.tgen (Hs := []) hb)


theorem chain_twk {n : Nat} {Γ : Ctx n} (Hs : List (Fm Γ)) (φ : Fm Γ) :
    Derive.chain (Hs.map (fun h => (h.twk : Fm Γ.text))) (φ.twk : Fm Γ.text) = ((Derive.chain Hs φ).twk : Fm Γ.text) := by
  induction Hs with
  | nil => rfl
  | cons h hs ih => show (h.twk : Fm Γ.text).imp (Derive.chain _ _) = _; rw [ih]; rfl

theorem Ent.ren_twk {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)} {φ : Fm Γ} (h : Ent S Γ Hs φ) :
    Ent S Γ.text (Hs.map (fun h => (h.twk : Fm Γ.text))) (φ.twk : Fm Γ.text) := by
  unfold Ent; rw [chain_twk]; exact Prov.ren _ h


abbrev Γpqr : Ctx 0 := Γpq.ext tyT

/-- Two propositions, substituted for `p` and `q`. -/
def subPQG {n : Nat} {Γ : Ctx n} (a b : Fm Γ) : TSub (fun i => i.elim0) Γpq Γ := fun {_} x =>
  match x with
  | .here => b
  | .there .here => a

/-- Three propositions, substituted for `p`, `q` and `r`. -/
def subPQR {n : Nat} {Γ : Ctx n} (a b c : Fm Γ) : TSub (fun i => i.elim0) Γpqr Γ := fun {_} x =>
  match x with
  | .here => c
  | .there .here => b
  | .there (.there .here) => a

set_option maxHeartbeats 4000000 in
theorem pe_inst (hP : S PropExt) {n : Nat} {Γ : Ctx n} (a b : Fm Γ) :
    Prov S Γ ((iff a b).imp (eqv tyT tyT a b)) :=
  Prov.subst _ _ (Ent.toProv (((Ent.axm (Γ := Γpq) (Hs := []) hP).inst pV).inst qV)) (subPQG a b)

set_option maxHeartbeats 4000000 in
theorem sym_t {n : Nat} {Γ : Ctx n} (a b : Fm Γ) : Prov S Γ ((eqv tyT tyT a b).imp (eqv tyT tyT b a)) :=
  Prov.subst _ _ (Ent.toProv ((((Ent.closed (Γ := Γpq) (Hs := []) (Ax := S) Prov.symEqv).tinst tyT).tinst tyT).inst
    pV |>.inst qV)) (subPQG a b)

set_option maxHeartbeats 4000000 in
theorem trans_t {n : Nat} {Γ : Ctx n} (a b c : Fm Γ) :
    Prov S Γ ((conj (eqv tyT tyT a b) (eqv tyT tyT b c)).imp (eqv tyT tyT a c)) :=
  Prov.subst _ _ (Ent.toProv ((((((Ent.closed (Γ := Γpqr) (Hs := []) (Ax := S) Prov.transEqv).tinst tyT).tinst tyT).tinst
    tyT).inst (.var (.there (.there .here)))).inst (.var (.there .here)) |>.inst (.var .here))) (subPQR a b c)

set_option maxHeartbeats 8000000 in
/-- From PropExt≡, a false proposition identical to `⊤` makes `⊤ ≡ ⊥`. -/
theorem propext_collapse_TB {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)} (hP : S PropExt) {ψ : Fm Γ}
    (hb : Ent S Γ Hs (boxF ψ)) (hn : Ent S Γ Hs ψ.neg) : Ent S Γ Hs (eqv tyT tyT topF botF) := by
  have hpe : Ent S Γ Hs ((iff ψ botF).imp (eqv tyT tyT ψ botF)) := Ent.ofProv (pe_inst hP ψ botF)
  have hbot : Ent S Γ Hs (botF : Fm Γ).neg := Ent.top
  have hiff : Ent S Γ Hs (iff ψ botF) :=
    Ent.mp2 (Ent.taut (.imp (.neg (.atom 0)) (.imp (.neg (.atom 1)) (.iff (.atom 0) (.atom 1)))) (v2 ψ botF)
      (fun _ a b => ⟨fun x => (a x).elim, fun y => (b y).elim⟩)) hn hbot
  have hpb : Ent S Γ Hs (eqv tyT tyT ψ botF) := Ent.mp hpe hiff
  have hsym : Ent S Γ Hs ((eqv tyT tyT ψ topF).imp (eqv tyT tyT topF ψ)) := Ent.ofProv (sym_t ψ topF)
  have htr : Ent S Γ Hs ((conj (eqv tyT tyT topF ψ) (eqv tyT tyT ψ botF)).imp (eqv tyT tyT topF botF)) :=
    Ent.ofProv (trans_t topF ψ botF)
  exact Ent.mp htr (Ent.andI (Ent.mp hsym hb) hpb)

set_option maxHeartbeats 8000000 in
/-- From PropExt≡ and `⊤ ≡ ⊥`, every proposition is necessary. -/
theorem propext_all_box {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)} (hP : S PropExt) (ψ : Fm Γ)
    (htb : Ent S Γ Hs (eqv tyT tyT topF botF)) : Ent S Γ Hs (boxF ψ) := by
  have hpt : Ent S Γ Hs ((iff ψ topF).imp (eqv tyT tyT ψ topF)) := Ent.ofProv (pe_inst hP ψ topF)
  have hpb : Ent S Γ Hs ((iff ψ botF).imp (eqv tyT tyT ψ botF)) := Ent.ofProv (pe_inst hP ψ botF)
  have hsym : Ent S Γ Hs ((eqv tyT tyT topF botF).imp (eqv tyT tyT botF topF)) := Ent.ofProv (sym_t topF botF)
  have htr : Ent S Γ Hs ((conj (eqv tyT tyT ψ botF) (eqv tyT tyT botF topF)).imp (eqv tyT tyT ψ topF)) :=
    Ent.ofProv (trans_t ψ botF topF)
  have hcase : Ent S Γ Hs (ψ.imp (boxF ψ)) :=
    Ent.intro (Ent.mp (Ent.weaken hpt) (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1))))
      (v2 ψ topF) (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) Ent.last Ent.top))
  have hcase2 : Ent S Γ Hs (ψ.neg.imp (boxF ψ)) := by
    refine Ent.intro (Ent.mp (Ent.weaken htr) (Ent.andI ?_ (Ent.mp (Ent.weaken hsym) (Ent.weaken htb))))
    refine Ent.mp (Ent.weaken hpb) (Ent.mp2 (Ent.taut (.imp (.neg (.atom 0)) (.imp (.neg (.atom 1)) (.iff (.atom 0) (.atom 1))))
      (v2 ψ botF) (fun _ a b => ⟨fun x => (a x).elim, fun y => (b y).elim⟩)) Ent.last Ent.top)
  exact Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.atom 1)) (.imp (.imp (.neg (.atom 0)) (.atom 1)) (.atom 1)))
    (v2 ψ (boxF ψ)) (fun _ f g => Classical.byCases f g)) hcase hcase2

set_option maxHeartbeats 8000000 in
/-- PropExt≡ proves every instance of TBF, without T. -/
theorem d_TBF_of_PropExt (hP : S PropExt) : ∀ χ, TBFSch χ → Prov S Ctx.nil χ := by
  rintro _ ⟨φ, rfl⟩
  -- under the hypothesis `𝔸α □φ`, either `𝔸α φ` (then PropExt≡) or some `¬φ` (then `⊤ ≡ ⊥`)
  have hA : Ent S Ctx.nil [tall (boxF φ)] ((tall φ).imp (boxF (tall φ))) :=
    Ent.intro (Ent.mp (Ent.ofProv (pe_inst hP (tall φ) topF))
      (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1)))) (v2 (tall φ) topF)
        (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) Ent.last Ent.top))
  have hB : Ent S Ctx.nil [tall (boxF φ)] ((tall φ).neg.imp (boxF (tall φ))) := by
    refine Ent.intro (propext_all_box hP _ ?_)
    have hex : Ent S Ctx.nil ([tall (boxF φ)] ++ [(tall φ).neg]) (tex φ.neg) :=
      Ent.mp (Ent.ofProv (Compl.prov_notTAll φ)) Ent.last
    refine Ent.texE hex ?_
    have hH : Ent S Ctx.nil.text (([tall (boxF φ)] ++ [(tall φ).neg]).map (fun h => (h.twk : Fm Ctx.nil.text)) ++ [φ.neg])
        (tall ((boxF φ).ren (Compl.twkL Ctx.nil))) := Ent.hyp _ 0 (by exact Nat.zero_lt_succ _)
    have hb := (congrArg (Ent S _ _) (tcontract_eq (boxF φ))).mp (Ent.tinst hH (tvar fz))
    exact propext_collapse_TB hP hb Ent.last
  exact Ent.toProv (Ent.intro (Hs := []) (Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.atom 1))
    (.imp (.imp (.neg (.atom 0)) (.atom 1)) (.atom 1))) (v2 (tall φ) (boxF (tall φ)))
    (fun _ f g => Classical.byCases f g)) hA hB))

set_option maxHeartbeats 8000000 in
/-- PropExt≡ proves every instance of TCBF, without T. -/
theorem d_TCBF_of_PropExt (hP : S PropExt) : ∀ χ, TCBFSch χ → Prov S Ctx.nil χ := by
  rintro _ ⟨φ, rfl⟩
  have hB : Ent S Ctx.nil [boxF (tall φ)] ((tall φ).neg.imp (tall (boxF φ))) := by
    refine Ent.intro ?_
    have htb := propext_collapse_TB hP (Ent.weaken (Ent.hyp [boxF (tall φ)] 0 Nat.one_pos)) Ent.last
    refine Ent.tgen ?_
    have htb' : Ent S Ctx.nil.text (([boxF (tall φ)] ++ [(tall φ).neg]).map (fun h => (h.twk : Fm Ctx.nil.text)))
        (eqv tyT tyT topF botF) := by
      exact Ent.ren_twk htb
    exact propext_all_box hP φ htb'
  have hA : Ent S Ctx.nil [boxF (tall φ)] ((tall φ).imp (tall (boxF φ))) := by
    refine Ent.intro (Ent.tgen ?_)
    have hH : Ent S Ctx.nil.text (([boxF (tall φ)] ++ [tall φ]).map (fun h => (h.twk : Fm Ctx.nil.text)))
        (tall (φ.ren (Compl.twkL Ctx.nil))) := Ent.hyp _ 1 (by exact Nat.one_lt_two)
    have h1 := (congrArg (Ent S _ _) (tcontract_eq φ)).mp (Ent.tinst hH (tvar fz))
    exact Ent.mp (Ent.ofProv (pe_inst hP φ topF))
      (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1)))) (v2 φ topF)
        (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) h1 Ent.top)
  exact Ent.toProv (Ent.intro (Hs := []) (Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.atom 1))
    (.imp (.imp (.neg (.atom 0)) (.atom 1)) (.atom 1))) (v2 (tall φ) (tall (boxF φ)))
    (fun _ f g => Classical.byCases f g)) hA hB))

end Derivs
end PIF
