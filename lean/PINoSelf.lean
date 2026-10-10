import PIKripkeCong

/-!
# No type is identical to the type of its properties (PI⁻)

A diagonal argument shows that no function from `α→t` to `α` is injective, in the sense of Leibniz
identity. With LL≈, applied to the polymorphic property "`γ` injects into `α`", it follows that
`α ≈ α→t` is false: the identity function injects `α` into `α`. This needs no LL≡.
-/
set_option autoImplicit false

namespace PIF
open Tm Derive

section NoSelf
variable {S : Fm Ctx.nil → Prop}

/-- Leibniz identity. -/
def lb {n : Nat} {Γ : Ctx n} (σ : Ty n) (p q : Tm Γ σ.1) : Fm Γ :=
  all σ.pred (imp (app (var .here) (p.wk σ.pred)) (app (var .here) (q.wk σ.pred)))

theorem lb_refl {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)} (σ : Ty n) (p : Tm Γ σ.1) : Ent S Γ Hs (lb σ p p) :=
  Ent.gen _ (Ent.taut (k := 1) (.imp (.atom 0) (.atom 0)) (fun _ => app (var .here) (p.wk σ.pred)) (fun _ h => h))

abbrev P1 : Ty 1 := tv0.pred
abbrev IT : Ty 1 := P1.arrow tv0
abbrev Γi : Ctx 1 := Δ1.ext IT

/-- `i` is injective: `∀G ∀H (i G = i H → G = H)`. -/
def InjF : Fm Γi :=
  all P1 (all P1 (imp (lb tv0 (app (var (.there (.there .here))) (var (.there .here)))
                              (app (var (.there (.there .here))) (var .here)))
                      (lb P1 (var (.there .here)) (var .here))))

/-- The diagonal predicate `λy. ∃G (i G = y ∧ ¬ G y)`. -/
def Dg : Tm Γi P1.1 :=
  lam tv0 (ex P1 (conj (lb tv0 (app (var (.there (.there .here))) (var .here)) (var (.there .here)))
                       (neg (app (var .here) (var (.there .here))))))

def d0 : Tm Γi tv0.1 := app (var .here) Dg

abbrev Gv : Tm (Γi.ext P1) P1.1 := var .here
abbrev iv : Tm (Γi.ext P1) IT.1 := var (.there .here)

set_option maxHeartbeats 8000000 in
/-- The diagonal argument, first half: given injectivity, `D(d₀)` is false. -/
theorem diag_neg : Ent S Γi [InjF] (neg (app Dg d0)) := by
  refine Ent.notI (B := app Dg d0) Ent.last ?_
  have hex : Ent S Γi ([InjF] ++ [app Dg d0])
      (ex P1 (conj (lb tv0 (app iv Gv) (d0.wk P1)) (neg (app Gv (d0.wk P1))))) :=
    Ent.beta Ent.last (.step (.beta _ _))
  refine Ent.exE hex ?_
  have hb : Ent S (Γi.ext P1) (([InjF] ++ [app Dg d0]).map (fun h => h.wk P1) ++
      [conj (lb tv0 (app iv Gv) (d0.wk P1)) (neg (app Gv (d0.wk P1)))])
      (conj (lb tv0 (app iv Gv) (d0.wk P1)) (neg (app Gv (d0.wk P1)))) := Ent.last
  have hl := Ent.andE1 hb
  have hn := Ent.andE2 hb
  have hI : Ent S (Γi.ext P1) (([InjF] ++ [app Dg d0]).map (fun h => h.wk P1) ++
      [conj (lb tv0 (app iv Gv) (d0.wk P1)) (neg (app Gv (d0.wk P1)))]) (InjF.wk P1) :=
    Ent.hyp _ 0 (by decide)
  have hI2 : Ent S (Γi.ext P1) (([InjF] ++ [app Dg d0]).map (fun h => h.wk P1) ++
      [conj (lb tv0 (app iv Gv) (d0.wk P1)) (neg (app Gv (d0.wk P1)))])
      (imp (lb tv0 (app iv Gv) (app iv (Dg.wk P1))) (lb P1 Gv (Dg.wk P1))) :=
    Ent.inst (Ent.inst hI Gv) (Dg.wk P1)
  have hL := Ent.mp hI2 hl
  have hF := Ent.inst hL (lam P1 (neg (app (var .here) ((d0.wk P1).wk P1))))
  have hF' : Ent S (Γi.ext P1) (([InjF] ++ [app Dg d0]).map (fun h => h.wk P1) ++
      [conj (lb tv0 (app iv Gv) (d0.wk P1)) (neg (app Gv (d0.wk P1)))])
      (imp (neg (app Gv (d0.wk P1))) (neg (app (Dg.wk P1) (d0.wk P1)))) :=
    Ent.beta hF (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  exact Ent.mp hF' hn

set_option maxHeartbeats 8000000 in
/-- The diagonal argument, second half: `D(d₀)` is true, with `G := D`. -/
theorem diag_pos : Ent S Γi [InjF] (app Dg d0) := by
  have h1 : Ent S Γi [InjF] (conj (lb tv0 d0 d0) (neg (app Dg d0))) := Ent.andI (lb_refl tv0 d0) diag_neg
  have h2 : Ent S Γi [InjF] (ex P1 (conj (lb tv0 (app iv Gv) (d0.wk P1)) (neg (app Gv (d0.wk P1))))) :=
    Ent.exI Dg h1
  exact Ent.beta h2 (BetaEq.symm (.step (.beta _ _)))

/-- No function from `α→t` to `α` is injective. -/
theorem not_InjF : Prov S Γi (neg InjF) :=
  Ent.toProv (Ent.notI (Hs := []) (B := app Dg d0) diag_pos diag_neg)

/-- `γ` injects into `δ`: `∃i:γ→δ ∀x ∀y (i x = i y → x = y)`, with `γ := tv0`, `δ := tv1`. -/
def InjQ : Fm (Δ2.ext (tv0.arrow tv1)) :=
  all tv0 (all tv0 (imp (lb tv1 (app (var (.there (.there .here))) (var (.there .here)))
                               (app (var (.there (.there .here))) (var .here)))
                         (lb tv0 (var (.there .here)) (var .here))))

def Qinj : Tm Δ1 (.pi .t) := tlam (ex (tv0.arrow tv1) InjQ)

abbrev II : Ty 1 := tv0.arrow tv0

def InjA : Fm (Δ1.ext II) :=
  all tv0 (all tv0 (imp (lb tv0 (app (var (.there (.there .here))) (var (.there .here)))
                               (app (var (.there (.there .here))) (var .here)))
                         (lb tv0 (var (.there .here)) (var .here))))

abbrev Γxy1 : Ctx 1 := (Δ1.ext tv0).ext tv0
abbrev idt : Tm Γxy1 II.1 := lam tv0 (var .here)

set_option maxHeartbeats 8000000 in
/-- The identity function is injective. -/
theorem inj_id {Hs : List (Fm Δ1)} : Ent S Δ1 Hs (ex II InjA) := by
  refine Ent.exI (lam tv0 (var .here)) ?_
  refine Ent.gen tv0 (Ent.gen tv0 (Ent.intro (Ent.gen tv0.pred ?_)))
  rw [List.map_append]
  have hH : Ent S (Γxy1.ext tv0.pred) ((((Hs.map (fun h => h.wk tv0)).map (fun h => h.wk tv0)).map
      (fun h => h.wk tv0.pred)) ++ [(lb tv0 (app idt (var (.there .here))) (app idt (var .here))).wk tv0.pred])
      ((lb tv0 (app idt (var (.there .here))) (app idt (var .here))).wk tv0.pred) := Ent.last
  have h1 := Ent.inst hH (var .here)
  exact Ent.beta h1 (BetaEq.imp (BetaEq.appR _ (.step (.beta _ _))) (BetaEq.appR _ (.step (.beta _ _))))

/-- (NoSelf) `𝔸α ¬(α ≈ α→t)`. -/
def NoSelf : Fm Ctx.nil := tall (neg (teq tv0 tv0.pred))

set_option maxHeartbeats 8000000 in
/-- **PI⁻ proves that no type is identical to the type of its properties.** -/
theorem d_NoSelf : Prov S Ctx.nil NoSelf := by
  have hQ : Ent S Δ1 [teq tv0 P1] (LLTeq Qinj) := Ent.ofProv (Prov.llTeq _)
  have h1 : Ent S Δ1 [teq tv0 P1] (imp (teq tv0 P1) (imp (ex II InjA) (ex IT InjF))) :=
    Ent.beta ((hQ.tinst tv0).tinst P1) (BetaEq.imp (.refl _) (BetaEq.imp (BetaEq.tbeta _ _) (BetaEq.tbeta _ _)))
  have h2 : Ent S Δ1 [teq tv0 P1] (ex IT InjF) := Ent.mp (Ent.mp h1 (Ent.hyp _ 0 (by decide))) inj_id
  have h3 : Ent S Δ1 [teq tv0 P1] (neg (teq tv0 P1)) := by
    refine Ent.exE h2 ?_
    exact Ent.absurd Ent.last (Ent.ofProv not_InjF)
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.notI (Hs := []) (B := teq tv0 P1) Ent.last h3))

end NoSelf
end PIF
