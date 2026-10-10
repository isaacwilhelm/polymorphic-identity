import PIBF

/-!
# The Barcan formulas from PropExt≡

PropExt≡ alone proves both BF and CBF for the item quantifiers (in PI⁻, without T or Classicism).
The argument splits on whether `⊤ ≡ ⊥`. If so, PropExt≡ makes every proposition necessary. If
not, PropExt≡ makes every necessary proposition true (a necessary falsehood would give `⊤ ≡ ⊥`),
and every truth necessary.
-/
set_option autoImplicit false

namespace PIF
open Tm

section OQDerBF
open Derive
variable {S : Fm Ctx.nil → Prop}

/-- `⊤ ≡ ⊥`, in any context. -/
abbrev TopEqBotD {n : Nat} {Γ : Ctx n} : Fm Γ := eqv tyT tyT topF botF

set_option maxHeartbeats 8000000 in
/-- PropExt≡ makes every truth necessary: from `ψ`, `ψ ↔ ⊤`, so `ψ ≡ ⊤`. -/
theorem dbf_box_of_true {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)} (hP : S PropExt) {ψ : Fm Γ}
    (h : Ent S Γ Hs ψ) : Ent S Γ Hs (boxF ψ) :=
  Ent.mp (Ent.ofProv (pe_inst hP ψ topF))
    (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1)))) (v2 ψ topF)
      (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) h Ent.top)

set_option maxHeartbeats 8000000 in
/-- PropExt≡ and `¬(⊤ ≡ ⊥)` make every necessary proposition true: if `□ψ` and `¬ψ`, then `⊤ ≡ ⊥`. -/
theorem dbf_true_of_box {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)} (hP : S PropExt) {ψ : Fm Γ}
    (hb : Ent S Γ Hs (boxF ψ)) (hn : Ent S Γ Hs (TopEqBotD : Fm Γ).neg) : Ent S Γ Hs ψ := by
  have hc : Ent S Γ Hs (ψ.neg.imp TopEqBotD) := Ent.intro (propext_collapse_TB hP (Ent.weaken hb) Ent.last)
  exact Ent.mp2 (Ent.taut (.imp (.imp (.neg (.atom 0)) (.atom 1)) (.imp (.neg (.atom 1)) (.atom 0)))
    (v2 ψ TopEqBotD) (fun _ f nb => Classical.byContradiction fun nc => nb (f nc))) hc hn

set_option maxHeartbeats 8000000 in
/-- Splitting on `⊤ ≡ ⊥`: if `⊤ ≡ ⊥` then `□χ` by PropExt≡, so it suffices to derive `□χ` from
`¬(⊤ ≡ ⊥)`. -/
theorem dbf_box_split {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)} (hP : S PropExt) (χ : Fm Γ)
    (hneg : Ent S Γ (Hs ++ [(TopEqBotD : Fm Γ).neg]) (boxF χ)) : Ent S Γ Hs (boxF χ) := by
  have hpos : Ent S Γ Hs ((TopEqBotD : Fm Γ).imp (boxF χ)) := Ent.intro (propext_all_box hP χ Ent.last)
  exact Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.atom 1)) (.imp (.imp (.neg (.atom 0)) (.atom 1)) (.atom 1)))
    (v2 TopEqBotD (boxF χ)) (fun _ f g => Classical.byCases f g)) hpos (Ent.intro hneg)

set_option maxHeartbeats 8000000 in
/-- PropExt≡ proves BF. Given `∀x □F x`: if `⊤ ≡ ⊥`, every proposition is necessary. If not, each
`F x` is true (being necessary), so `∀x F x` is true, and so necessary by PropExt≡. -/
theorem d_BF_of_PropExt (hP : S PropExt) : Prov S Ctx.nil BF := by
  let Hs : List (Fm ΓF) := [HBF, (TopEqBotD : Fm ΓF).neg]
  have hb : Ent S ΓFx (Hs.map (fun h => h.wk tv0)) (boxF FxF) :=
    (Ent.hyp (Hs.map (fun h => h.wk tv0)) 0 (by decide) : Ent S ΓFx _ (HBF.wk tv0)).inst (.var .here)
  have hn : Ent S ΓFx (Hs.map (fun h => h.wk tv0)) (TopEqBotD : Fm ΓFx).neg :=
    Ent.hyp (Hs.map (fun h => h.wk tv0)) 1 (by decide)
  have hx : Ent S ΓFx (Hs.map (fun h => h.wk tv0)) FxF := dbf_true_of_box hP hb hn
  have hall : Ent S ΓF ([HBF] ++ [(TopEqBotD : Fm ΓF).neg]) AllF := Ent.gen tv0 hx
  have h : Ent S ΓF ([] ++ [HBF]) (boxF AllF) := dbf_box_split hP AllF (dbf_box_of_true hP hall)
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen tv0.pred (Hs := []) (Ent.intro (Hs := []) h)))

set_option maxHeartbeats 8000000 in
/-- PropExt≡ proves CBF. Given `□∀x F x` and any `x`: if `⊤ ≡ ⊥`, every proposition is necessary.
If not, `∀x F x` is true (being necessary), so `F x` is true, and so necessary by PropExt≡. -/
theorem d_CBF_of_PropExt (hP : S PropExt) : Prov S Ctx.nil CBF := by
  have hb : Ent S ΓFx ([boxF AllF'] ++ [(TopEqBotD : Fm ΓFx).neg]) (boxF AllF') := Ent.hyp _ 0 (by decide)
  have hall : Ent S ΓFx ([boxF AllF'] ++ [(TopEqBotD : Fm ΓFx).neg]) AllF' := dbf_true_of_box hP hb Ent.last
  have hx : Ent S ΓFx ([boxF AllF'] ++ [(TopEqBotD : Fm ΓFx).neg]) FxF := hall.inst (.var .here)
  have h1 : Ent S ΓFx [boxF AllF'] (boxF FxF) := dbf_box_split hP FxF (dbf_box_of_true hP hx)
  have h2 : Ent S ΓF ([] ++ [boxF AllF]) (all tv0 (boxF FxF)) := Ent.gen tv0 h1
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen tv0.pred (Hs := []) (Ent.intro (Hs := []) h2)))

end OQDerBF
end PIF
