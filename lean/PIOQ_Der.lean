import PIBF

/-!
# Three derivations

* Disjoint, PCong and LL≡ prove Cong.
* Collapse and T prove Truth.
* WCong and Truth prove LL≡.
-/
set_option autoImplicit false

namespace PIF
open Tm

section OQDerivations
open Derive
variable {S : Fm Ctx.nil → Prop}

/-! ### Truth from Collapse and T -/

abbrev ΓpqD : Ctx 0 := (Ctx.nil.ext tyT).ext tyT
abbrev pD : Fm ΓpqD := .var (.there .here)
abbrev qD : Fm ΓpqD := .var .here
abbrev EpqD : Fm ΓpqD := eqv tyT tyT pD qD

set_option maxHeartbeats 4000000 in
/-- Collapse and T prove Truth: if `p ≡ q` and `p`, then `p ≡ ⊤` by Collapse, so `q ≡ ⊤`, and `q`
by T. -/
theorem d_Truth_of_CollapseT (hC : S Collapse) (hT : S TAx) : Prov S Ctx.nil Truth := by
  let Hs : List (Fm ΓpqD) := [EpqD, pD]
  have he : Ent S ΓpqD Hs EpqD := Ent.hyp _ 0 (by decide)
  have hp : Ent S ΓpqD Hs pD := Ent.hyp _ 1 (by decide)
  have hpb : Ent S ΓpqD Hs (boxF pD) := Ent.mp ((Ent.axm (Γ := ΓpqD) (Hs := Hs) hC).inst pD) hp
  have hqp : Ent S ΓpqD Hs (eqv tyT tyT qD pD) := Ent.mp (Ent.ofProv (sym_t pD qD)) he
  have hqb : Ent S ΓpqD Hs (boxF qD) :=
    Ent.mp (Ent.ofProv (trans_t qD pD topF)) (Ent.andI hqp hpb)
  have hq : Ent S ΓpqD ([EpqD] ++ [pD]) qD := Ent.mp ((Ent.axm (Γ := ΓpqD) (Hs := Hs) hT).inst qD) hqb
  exact Ent.toProv (Ent.gen tyT (Hs := []) (Ent.gen tyT (Hs := []) (Ent.intro (Hs := []) (Ent.intro (Hs := [EpqD]) hq))))

/-! ### LL≡ from WCong and Truth -/

set_option maxHeartbeats 4000000 in
/-- WCong and Truth prove LL≡: with `α = β`, `γ = δ = t` and `f = g = G`, WCong gives `G x ≡ G y`
from `x ≡ y` (as `α ≈ α`, `t ≈ t` and `G ≡ G`); Truth then gives `G x → G y`. -/
theorem d_LLEqv_of_WCongTruth (hW : S WCong) (hT : S Truth) : Prov S Ctx.nil LLEqv := by
  have hc0 : Ent S C22 [E22', Fx22] _ :=
    ((((Ent.axm (Γ := C22) (Hs := [E22', Fx22]) hW).tinst tv0).tinst tv0).tinst tyT).tinst tyT
  have hc : Ent S C22 [E22', Fx22] ((((Tm.teq tv0 tv0).conj (Tm.teq tyT tyT)).conj
      ((Tm.eqv tv0.pred tv0.pred (.var .here) (.var .here)).conj E22')).imp
      (Tm.eqv tyT tyT Fx22 Fy22)) :=
    Ent.inst (Ent.inst (Ent.inst (Ent.inst hc0 (.var .here)) (.var .here)) (.var (.there (.there .here)))) (.var (.there .here))
  have hr : Ent S C22 [E22', Fx22] (Tm.eqv tv0.pred tv0.pred (.var .here) (.var .here)) :=
    ((Ent.closed (Γ := C22) (Hs := [E22', Fx22]) (Ax := S) Prov.refEqv).tinst tv0.pred).inst (.var .here)
  have hra : Ent S C22 [E22', Fx22] (Tm.teq tv0 tv0) :=
    (Ent.closed (Γ := C22) (Hs := [E22', Fx22]) (Ax := S) Prov.refTeq).tinst tv0
  have hrt : Ent S C22 [E22', Fx22] (Tm.teq tyT tyT) :=
    (Ent.closed (Γ := C22) (Hs := [E22', Fx22]) (Ax := S) Prov.refTeq).tinst tyT
  have he : Ent S C22 [E22', Fx22] E22' := Ent.hyp _ 0 (by decide)
  have hfx : Ent S C22 [E22', Fx22] Fx22 := Ent.hyp _ 1 (by decide)
  have ht : Ent S C22 [E22', Fx22] ((Tm.eqv tyT tyT Fx22 Fy22).imp (Fx22.imp Fy22)) :=
    Ent.inst (Ent.inst (Ent.axm (Γ := C22) (Hs := [E22', Fx22]) hT) Fx22) Fy22
  have h2 : Ent S C22 ([E22'] ++ [Fx22]) Fy22 :=
    Ent.mp2 ht (Ent.mp hc (Ent.andI (Ent.andI hra hrt) (Ent.andI hr he))) hfx
  have h3 : Ent S ((Δ1.ext tv0).ext tv0) ([] ++ [E22]) (Tm.all tv0.pred (Fx22.imp Fy22)) :=
    Ent.gen (Hs := [] ++ [E22]) tv0.pred (Ent.intro (Hs := [E22']) h2)
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen (Hs := []) tv0 (Ent.gen (Hs := []) tv0 (Ent.intro (Hs := []) h3))))

/-! ### Cong from Disjoint, PCong and LL≡ -/

/-- The body of Cong (after its four type quantifiers), with `τ` for the domain of `g`:
`∀_{α→γ} f ∀_{τ→δ} g ∀_α x ∀_τ y ((f ≡ g ∧ x ≡ y) → f x ≡ g y)`, where `α γ δ` are `tv3 tv1 tv0`. -/
abbrev BodyCD (τ : Ty 4) : Fm Δ4 :=
  all (tv3.arrow tv1) (all (τ.arrow tv0) (all tv3 (all τ
    (imp (conj (eqv (tv3.arrow tv1) (τ.arrow tv0) (.var (.there (.there (.there .here)))) (.var (.there (.there .here))))
               (eqv tv3 τ (.var (.there .here)) (.var .here)))
         (eqv tv1 tv0 (.app (.var (.there (.there (.there .here)))) (.var (.there .here)))
                      (.app (.var (.there (.there .here))) (.var .here)))))))

/-- The polymorphic predicate `Λζ. ∀_{α→γ} f ∀_{ζ→δ} g ∀_α x ∀_ζ y ((f ≡ g ∧ x ≡ y) → f x ≡ g y)`. -/
abbrev QCD : Tm Δ4 (.pi .t) :=
  Tm.tlam (all (tv4'.arrow tv2) (all (tv0.arrow tv1) (all tv4' (all tv0
    (imp (conj (eqv (tv4'.arrow tv2) (tv0.arrow tv1) (.var (.there (.there (.there .here)))) (.var (.there (.there .here))))
               (eqv tv4' tv0 (.var (.there .here)) (.var .here)))
         (eqv tv2 tv1 (.app (.var (.there (.there (.there .here)))) (.var (.there .here)))
                      (.app (.var (.there (.there .here))) (.var .here))))))))

/-- The context `α β γ δ, f : α→γ, g : α→δ, x : α, y : α`. -/
abbrev CAD : Ctx 4 := (((Δ4.ext (tv3.arrow tv1)).ext (tv3.arrow tv0)).ext tv3).ext tv3
abbrev fAD : Tm CAD (tv3.arrow tv1).1 := .var (.there (.there (.there .here)))
abbrev gAD : Tm CAD (tv3.arrow tv0).1 := .var (.there (.there .here))
abbrev xAD : Tm CAD tv3.1 := .var (.there .here)
abbrev yAD : Tm CAD tv3.1 := .var .here
abbrev HAD : Fm CAD := conj (eqv (tv3.arrow tv1) (tv3.arrow tv0) fAD gAD) (eqv tv3 tv3 xAD yAD)

/-- The context `α β γ δ, f : α→γ, g : β→δ, x : α, y : β`. -/
abbrev CBD : Ctx 4 := (((Δ4.ext (tv3.arrow tv1)).ext (tv2.arrow tv0)).ext tv3).ext tv2
abbrev HBD : Fm CBD := conj (eqv (tv3.arrow tv1) (tv2.arrow tv0) (.var (.there (.there (.there .here)))) (.var (.there (.there .here))))
  (eqv tv3 tv2 (.var (.there .here)) (.var .here))
abbrev GBD : Fm CBD := eqv tv1 tv0 (.app (.var (.there (.there (.there .here)))) (.var (.there .here)))
  (.app (.var (.there (.there .here))) (.var .here))

set_option maxHeartbeats 8000000 in
/-- The instance `ζ = α` of the predicate: PCong gives `f x ≡ g x`, and LL≡ (with `λz. f x ≡ g z`)
carries it over to `f x ≡ g y`. -/
theorem d_QCD_alpha (hLL : S LLEqv) (hP : S PCong) : Ent S Δ4 [] (BodyCD tv3) := by
  have hH : Ent S CAD [HAD] HAD := Ent.hyp _ 0 (by decide)
  have hfg := Ent.andE1 hH
  have hxy := Ent.andE2 hH
  -- PCong: `f ≡ g → f x ≡ g x`
  have hpc : Ent S CAD [HAD] ((eqv (tv3.arrow tv1) (tv3.arrow tv0) fAD gAD).imp
      (eqv tv1 tv0 (.app fAD xAD) (.app gAD xAD))) :=
    ((((((Ent.axm (Γ := CAD) (Hs := [HAD]) hP).tinst tv3).tinst tv1).tinst tv0).inst fAD).inst gAD).inst xAD
  have hfx : Ent S CAD [HAD] (eqv tv1 tv0 (.app fAD xAD) (.app gAD xAD)) := Ent.mp hpc hfg
  -- LL≡ with `λz. f x ≡ g z`
  have hll := Ent.mp ((((Ent.axm (Γ := CAD) (Hs := [HAD]) hLL).tinst tv3).inst xAD).inst yAD) hxy
  have hll1 := hll.inst (Tm.lam tv3 (eqv tv1 tv0 (.app (.var (.there (.there (.there (.there .here))))) (.var (.there (.there .here))))
    (.app (.var (.there (.there (.there .here)))) (.var .here))))
  have hll2 : Ent S CAD [HAD] ((eqv tv1 tv0 (.app fAD xAD) (.app gAD xAD)).imp (eqv tv1 tv0 (.app fAD xAD) (.app gAD yAD))) :=
    Ent.beta hll1 (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  have hg : Ent S CAD ([] ++ [HAD]) (eqv tv1 tv0 (.app fAD xAD) (.app gAD yAD)) := Ent.mp hll2 hfx
  exact Ent.gen (Hs := []) _ (Ent.gen (Hs := []) _ (Ent.gen (Hs := []) _ (Ent.gen (Hs := []) _ (Ent.intro (Hs := []) hg))))

set_option maxHeartbeats 8000000 in
/-- Disjoint, PCong and LL≡ prove Cong. If `α ≈ β`, LL≈ (with the predicate `QCD`) carries the
instance `ζ = α`, which follows from PCong and LL≡, over to `ζ = β`. If not, Disjoint says that no
`x : α` is identical to any `y : β`, so the antecedent of Cong fails. -/
theorem d_Cong_of_DisjPCong (hLL : S LLEqv) (hD : S Disjoint) (hP : S PCong) : Prov S Ctx.nil Cong := by
  have hQ : Ent S Δ4 [] (LLTeq QCD) := Ent.ofProv (Prov.llTeq _)
  have h1 : Ent S Δ4 [] ((Tm.teq tv3 tv2).imp ((BodyCD tv3).imp (BodyCD tv2))) :=
    Ent.beta ((hQ.tinst tv3).tinst tv2) (BetaEq.imp (.refl _) (BetaEq.imp (BetaEq.tbeta _ _) (BetaEq.tbeta _ _)))
  have hpos : Ent S Δ4 [] ((Tm.teq tv3 tv2).imp (BodyCD tv2)) :=
    Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2))) (.imp (.atom 1) (.imp (.atom 0) (.atom 2))))
      (v3 (Tm.teq tv3 tv2) (BodyCD tv3) (BodyCD tv2)) (fun _ f b a => f a b)) h1 (d_QCD_alpha hLL hP)
  -- the case `¬ α ≈ β`
  have hnt : Ent S CBD [neg (Tm.teq tv3 tv2), HBD] (neg (Tm.teq tv3 tv2)) := Ent.hyp _ 0 (by decide)
  have hHB : Ent S CBD [neg (Tm.teq tv3 tv2), HBD] HBD := Ent.hyp _ 1 (by decide)
  have hdis : Ent S CBD [neg (Tm.teq tv3 tv2), HBD] (neg (eqv tv3 tv2 (.var (.there .here)) (.var .here))) :=
    ((Ent.mp (((Ent.axm (Γ := CBD) (Hs := [neg (Tm.teq tv3 tv2), HBD]) hD).tinst tv3).tinst tv2) hnt).inst
      (.var (.there .here))).inst (.var .here)
  have hG : Ent S CBD ([neg (Tm.teq tv3 tv2)] ++ [HBD]) GBD := Ent.absurd (Ent.andE2 hHB) hdis
  have hn4 : Ent S Δ4 ([] ++ [neg (Tm.teq tv3 tv2)]) (BodyCD tv2) :=
    Ent.gen (Hs := [] ++ [neg (Tm.teq tv3 tv2)]) _ (Ent.gen (Hs := [neg (Tm.teq tv3 tv2)]) _
      (Ent.gen (Hs := [neg (Tm.teq tv3 tv2)]) _ (Ent.gen (Hs := [neg (Tm.teq tv3 tv2)]) _
        (Ent.intro (Hs := [neg (Tm.teq tv3 tv2)]) hG))))
  have hneg : Ent S Δ4 [] ((neg (Tm.teq tv3 tv2)).imp (BodyCD tv2)) := Ent.intro (Hs := []) hn4
  have hfin : Ent S Δ4 [] (BodyCD tv2) :=
    Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.atom 1)) (.imp (.imp (.neg (.atom 0)) (.atom 1)) (.atom 1)))
      (v2 (Tm.teq tv3 tv2) (BodyCD tv2)) (fun _ f g => Classical.byCases f g)) hpos hneg
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) hfin))))

end OQDerivations
end PIF
