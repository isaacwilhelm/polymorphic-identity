import PIBF

/-!
# LL≡-Poly from Disjoint and LL≡/≈

Disjoint and LL≡/≈ (Bridge) prove LL≡-Poly, instance by instance, in PI⁻: if `x ≡ y` with `x : α`,
`y : β`, then `α ≈ β` by Disjoint (classically), so the instance of LL≡/≈ for `P` gives
`P_α x → P_β y`.
-/
set_option autoImplicit false

namespace PIF

section Bridge
open Tm Derive
variable (P : Tm Ctx.nil PK)

variable {S : Fm Ctx.nil → Prop}

theorem BridgeB_congr_LLP {a a' : Tm Γb PK} (ha : a = a') : BridgeB a = BridgeB a' := by rw [ha]

set_option maxHeartbeats 4000000 in
/-- Disjoint and LL≡/≈ prove LL≡-Poly, instance by instance, in PI⁻: from `x ≡ y`, Disjoint gives
`α ≈ β` (classically), and then the instance of LL≡/≈ for `P` gives `P_α x → P_β y`. -/
theorem d_LLPoly_of_DisjBridge (hD : S Disjoint) (h : S (Bridge P)) : Prov S Ctx.nil (LLPoly P) := by
  have h' : S (BridgeT (Pc P Γb)) := bridge_eq P ▸ h
  have hb := ((((Ent.axm (Γ := Γb) (Hs := []) h').tinst tv1).tinst tv0).inst (.var (.there .here))).inst (.var .here)
  have hB : Ent S Γb [] (BridgeB (Pc P Γb)) := Ent.congr hb (BridgeB_congr_LLP (eq_of_heq (by pc_heq)))
  have h1 : Ent S Γb [] ((neg (teq tv1 tv0)).imp (all tv1 (all tv0 (neg (eqv tv1 tv0 (.var (.there .here)) (.var .here)))))) :=
    ((Ent.axm (Γ := Γb) (Hs := []) hD).tinst tv1).tinst tv0
  have h2 : Ent S Γb [] ((neg (teq tv1 tv0)).imp (neg (eqv tv1 tv0 (.var (.there .here)) (.var .here)))) :=
    Ent.impInst (Ent.impInst h1 (.var (.there .here))) (.var .here)
  have h3 : Ent S Γb [] (QBg tv1 tv0 (Pc P Γb)) :=
    Ent.mp2 (Ent.taut (.imp (.imp (.neg (.atom 0)) (.neg (.atom 1)))
        (.imp (.imp (.conj (.atom 1) (.atom 0)) (.imp (.atom 2) (.atom 3))) (.imp (.atom 1) (.imp (.atom 2) (.atom 3)))))
      (v4 (teq tv1 tv0) (eqv tv1 tv0 (.var (.there .here)) (.var .here))
        (.app (.tapp (Pc P Γb) tv1) (.var (.there .here))) (.app (.tapp (Pc P Γb) tv0) (.var .here)))
      (fun _ f g e => g ⟨e, Classical.byContradiction fun nt => f nt e⟩)) h2 hB
  rw [llPoly_eq]
  exact Ent.toProv (Ent.tgen (Ent.tgen (Ent.gen tv1 (Ent.gen tv0 h3))))

end Bridge

end PIF
