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

end Derivs
end PIF
