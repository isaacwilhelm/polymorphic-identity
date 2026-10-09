import PIBridge
import PITagged

/-!
# Four further principles

Propositional extensionality for `≡` (PropExt≡), identity of indiscernibles (PII), extensionality
for identified functions (the converse of PCong, PExt), and uniqueness of counterparts (Uniq).
-/
set_option autoImplicit false

namespace PIF
open Tm

/-- (PropExt≡) `∀_t p ∀_t q ((p ↔ q) → p ≡_t q)` -/
def PropExt : Fm Ctx.nil :=
  all tyT (all tyT (imp (iff (.var (.there .here)) (.var .here)) (eqv tyT tyT (.var (.there .here)) (.var .here))))

/-- (PII) `𝔸α ∀_α x ∀_α y (∀_{α→t} F (F x → F y) → x ≡_α y)` -/
def PII : Fm Ctx.nil :=
  tall (all tv0 (all tv0 (imp (all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here))))
                                                  (.app (.var .here) (.var (.there .here)))))
    (eqv tv0 tv0 (.var (.there .here)) (.var .here)))))

/-- (Uniq) `𝔸α 𝔸β ∀_α x ∀_β y ∀_β y' ((x ≡ y ∧ x ≡ y') → ∀_{β→t} F (F y → F y'))` -/
def Uniq : Fm Ctx.nil :=
  tall (tall (all tv1 (all tv0 (all tv0 (imp
    (conj (eqv tv1 tv0 (.var (.there (.there .here))) (.var (.there .here)))
          (eqv tv1 tv0 (.var (.there (.there .here))) (.var .here)))
    (all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here))))
                       (.app (.var .here) (.var (.there .here))))))))))

/-- (PExt) `𝔸α 𝔸γ 𝔸δ ∀_{α→γ} f ∀_{α→δ} g (∀_α x (f x ≡ g x) → f ≡ g)`: the converse of PCong. -/
def PExt : Fm Ctx.nil :=
  tall (tall (tall (all (tv2.arrow tv1) (all (tv2.arrow tv0) (imp
    (all tv2 (eqv tv1 tv0 (.app (.var (.there (.there .here))) (.var .here)) (.app (.var (.there .here)) (.var .here))))
    (eqv (tv2.arrow tv1) (tv2.arrow tv0) (.var (.there .here)) (.var .here)))))))

namespace Frame
variable (F : Frame)

theorem tr_PropExt : F.Tr PropExt ↔ ∀ p q : Prop, (p ↔ q) → F.eqv .t .t p q := Iff.rfl
theorem tr_PExt : F.Tr PExt ↔ ∀ a c d (f : F.U.El a → F.U.El c) (g : F.U.El a → F.U.El d),
    (∀ x, F.eqv c d (f x) (g x)) → F.eqv (.arr a c) (.arr a d) f g := Iff.rfl

/-- PropExt≡ is true in every model whose propositions are truth values. -/
theorem PropExt_valid (hM : F.IsModelPIm) : F.Valid PropExt :=
  (F.valid_iff_tr _).mpr <| F.tr_PropExt.mpr fun p _ h =>
    propext h ▸ F.tr_RefEqv.mp ((F.valid_iff_tr _).mp hM.refEqv) .t p

end Frame

section Derivations
open Derive
variable {S : Fm Ctx.nil → Prop}

abbrev Γxy : Ctx 1 := (Δ1.ext tv0).ext tv0

set_option maxHeartbeats 4000000 in
/-- PII is a theorem of PI⁻: take `F := λz.(x ≡ z)`; `F x` by Ref≡, so `F y`. -/
theorem d_PII : Prov S Ctx.nil PII := by
  have hH : Ent S Γxy [all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))]
      (all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))) :=
    Ent.hyp _ 0 (by decide)
  have h1 := Ent.inst hH (.lam tv0 (eqv tv0 tv0 (.var (.there (.there .here))) (.var .here)))
  have h2 : Ent S Γxy [all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))]
      ((eqv tv0 tv0 (.var (.there .here)) (.var (.there .here))).imp (eqv tv0 tv0 (.var (.there .here)) (.var .here))) :=
    Ent.beta h1 (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  have hr : Ent S Γxy [all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))]
      (eqv tv0 tv0 (.var (.there .here)) (.var (.there .here))) :=
    ((Ent.closed (Γ := Γxy) Prov.refEqv).tinst tv0).inst (.var (.there .here))
  have h3 : Ent S Γxy ([] ++ [all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))])
      (eqv tv0 tv0 (.var (.there .here)) (.var .here)) := Ent.mp h2 hr
  exact Ent.toProv (Ent.tgen (Ent.gen tv0 (Ent.gen tv0 (Ent.intro h3))))

set_option maxHeartbeats 4000000 in
/-- Uniq proves LL≡: its instance with `β := α` and `y := x`, with Ref≡. -/
theorem d_LLEqv_of_Uniq (hU : S Uniq) : Prov S Ctx.nil LLEqv := by
  have h0 := (((((Ent.axm (Γ := Γxy) (Hs := []) hU).tinst tv0).tinst tv0).inst (.var (.there .here))).inst
    (.var (.there .here))).inst (.var .here)
  have hr : Ent S Γxy [] (eqv tv0 tv0 (.var (.there .here)) (.var (.there .here))) :=
    ((Ent.closed (Γ := Γxy) Prov.refEqv).tinst tv0).inst (.var (.there .here))
  have h1 : Ent S Γxy [] ((eqv tv0 tv0 (.var (.there .here)) (.var .here)).imp
      (all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here)))))) :=
    Ent.mp2 (Ent.taut (.imp (.imp (.conj (.atom 0) (.atom 1)) (.atom 2)) (.imp (.atom 0) (.imp (.atom 1) (.atom 2))))
      (v3 (eqv tv0 tv0 (.var (.there .here)) (.var (.there .here))) (eqv tv0 tv0 (.var (.there .here)) (.var .here))
        (all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))))
      (fun _ f a b => f ⟨a, b⟩)) h0 hr
  exact Ent.toProv (Ent.tgen (Ent.gen tv0 (Ent.gen tv0 h1)))

abbrev Γu : Ctx 2 := ((Δ2.ext tv1).ext tv0).ext tv0
abbrev HypU : Fm Γu := conj (eqv tv1 tv0 (.var (.there (.there .here))) (.var (.there .here)))
  (eqv tv1 tv0 (.var (.there (.there .here))) (.var .here))

set_option maxHeartbeats 4000000 in
/-- LL≡ proves Uniq: from `x ≡ y` and `x ≡ y'`, Sym≡ and Trans≡ give `y ≡ y'`, and then LL≡. -/
theorem d_Uniq_of_LLEqv (hLL : S LLEqv) : Prov S Ctx.nil Uniq := by
  have hH : Ent S Γu [HypU] HypU := Ent.hyp _ 0 (by decide)
  have hs : Ent S Γu [HypU] ((eqv tv1 tv0 (.var (.there (.there .here))) (.var (.there .here))).imp
      (eqv tv0 tv1 (.var (.there .here)) (.var (.there (.there .here))))) :=
    ((((Ent.closed (Γ := Γu) (Hs := [HypU]) (Ax := S) Prov.symEqv).tinst tv1).tinst tv0).inst (.var (.there (.there .here)))).inst
      (.var (.there .here))
  have hyx := Ent.mp hs (Ent.andE1 hH)
  have ht : Ent S Γu [HypU] ((conj (eqv tv0 tv1 (.var (.there .here)) (.var (.there (.there .here))))
      (eqv tv1 tv0 (.var (.there (.there .here))) (.var .here))).imp (eqv tv0 tv0 (.var (.there .here)) (.var .here))) :=
    ((((((Ent.closed (Γ := Γu) (Hs := [HypU]) (Ax := S) Prov.transEqv).tinst tv0).tinst tv1).tinst tv0).inst
      (.var (.there .here))).inst (.var (.there (.there .here)))).inst (.var .here)
  have hyy := Ent.mp ht (Ent.andI hyx (Ent.andE2 hH))
  have hl : Ent S Γu [HypU] ((eqv tv0 tv0 (.var (.there .here)) (.var .here)).imp
      (all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here)))))) :=
    (((Ent.axm (Γ := Γu) (Hs := [HypU]) hLL).tinst tv0).inst (.var (.there .here))).inst (.var .here)
  have h3 : Ent S Γu ([] ++ [HypU])
      (all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here))))) :=
    Ent.mp hl hyy
  exact Ent.toProv (Ent.tgen (Ent.tgen (Ent.gen tv1 (Ent.gen tv0 (Ent.gen tv0 (Ent.intro h3))))))

abbrev Γpq : Ctx 0 := (Ctx.nil.ext tyT).ext tyT
abbrev pV : Fm Γpq := .var (.there .here)
abbrev qV : Fm Γpq := .var .here
abbrev HsT : List (Fm Γpq) := [eqv tyT tyT pV qV, pV, qV.neg]

set_option maxHeartbeats 16000000 in
/-- PropExt≡ and `⊤ ≢ ⊥` prove Truth: if `p ≡ q`, `p` and `¬q`, then `p ≡ ⊤` and `q ≡ ⊥`, so `⊤ ≡ ⊥`. -/
theorem d_Truth_of_PropExt (hP : S PropExt) (hT : S TopBot) : Prov S Ctx.nil Truth := by
  have hE : Ent S Γpq HsT (eqv tyT tyT pV qV) := Ent.hyp _ 0 (by decide)
  have hp : Ent S Γpq HsT pV := Ent.hyp _ 1 (by decide)
  have hnq : Ent S Γpq HsT qV.neg := Ent.hyp _ 2 (by decide)
  have htop : Ent S Γpq HsT (topF : Fm Γpq) := Ent.top
  have hpe1 : Ent S Γpq HsT ((iff pV topF).imp (eqv tyT tyT pV topF)) :=
    ((Ent.axm (Γ := Γpq) (Hs := HsT) hP).inst pV).inst topF
  have hpe2 : Ent S Γpq HsT ((iff qV botF).imp (eqv tyT tyT qV botF)) :=
    ((Ent.axm (Γ := Γpq) (Hs := HsT) hP).inst qV).inst botF
  have hpt : Ent S Γpq HsT (eqv tyT tyT pV topF) :=
    Ent.mp hpe1 (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1)))) (v2 pV topF)
      (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) hp htop)
  have hqb : Ent S Γpq HsT (eqv tyT tyT qV botF) :=
    Ent.mp hpe2 (Ent.mp2 (Ent.taut (.imp (.neg (.atom 0)) (.imp (.neg (.atom 1)) (.iff (.atom 0) (.atom 1))))
      (v2 qV botF) (fun _ a b => ⟨fun x => (a x).elim, fun y => (b y).elim⟩)) hnq htop)
  have hsym : Ent S Γpq HsT ((eqv tyT tyT pV topF).imp (eqv tyT tyT topF pV)) :=
    ((((Ent.closed (Γ := Γpq) (Hs := HsT) (Ax := S) Prov.symEqv).tinst tyT).tinst tyT).inst pV).inst topF
  have htr1 : Ent S Γpq HsT ((conj (eqv tyT tyT topF pV) (eqv tyT tyT pV qV)).imp (eqv tyT tyT topF qV)) :=
    (((((Ent.closed (Γ := Γpq) (Hs := HsT) (Ax := S) Prov.transEqv).tinst tyT).tinst tyT).tinst tyT).inst topF).inst pV
      |>.inst qV
  have htr2 : Ent S Γpq HsT ((conj (eqv tyT tyT topF qV) (eqv tyT tyT qV botF)).imp (eqv tyT tyT topF botF)) :=
    (((((Ent.closed (Γ := Γpq) (Hs := HsT) (Ax := S) Prov.transEqv).tinst tyT).tinst tyT).tinst tyT).inst topF).inst qV
      |>.inst botF
  have htq : Ent S Γpq HsT (eqv tyT tyT topF qV) := Ent.mp htr1 (Ent.andI (Ent.mp hsym hpt) hE)
  have htb : Ent S Γpq HsT (eqv tyT tyT topF botF) := Ent.mp htr2 (Ent.andI htq hqb)
  have hn : Ent S Γpq HsT (eqv tyT tyT topF botF).neg := Ent.axm (Γ := Γpq) (Hs := HsT) hT
  have hq : Ent S Γpq ([eqv tyT tyT pV qV, pV]) qV := Ent.byContra (Hs := [eqv tyT tyT pV qV, pV]) htb hn
  have h2 : Ent S Γpq ([] ++ [eqv tyT tyT pV qV]) (pV.imp qV) := Ent.intro (Hs := [eqv tyT tyT pV qV]) hq
  exact Ent.toProv (Ent.gen tyT (Ent.gen tyT (Ent.intro h2)))

set_option maxHeartbeats 16000000 in
/-- PropExt≡ and Int≈ prove Ext≈: if `α ⊑ β`, then `(α ⊑ β) ↔ ⊤`, so `□(α ⊑ β)`. -/
theorem d_ExtT_of_PropExt (hP : S PropExt) (hI : S IntT) : Prov S Ctx.nil ExtT := by
  have hH : Ent S Δ2 [HypE] HypE := Ent.hyp _ 0 (by decide)
  have htop : Ent S Δ2 [HypE] (topF : Fm Δ2) := Ent.top
  have hpe1 : Ent S Δ2 [HypE] ((iff (subT : Fm Δ2) topF).imp (boxF (subT : Fm Δ2))) :=
    ((Ent.axm (Γ := Δ2) (Hs := [HypE]) hP).inst (subT : Fm Δ2)).inst topF
  have hpe2 : Ent S Δ2 [HypE] ((iff (supT : Fm Δ2) topF).imp (boxF (supT : Fm Δ2))) :=
    ((Ent.axm (Γ := Δ2) (Hs := [HypE]) hP).inst (supT : Fm Δ2)).inst topF
  have hb1 : Ent S Δ2 [HypE] (boxF (subT : Fm Δ2)) :=
    Ent.mp hpe1 (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1)))) (v2 (subT : Fm Δ2) topF)
      (fun _ x y => ⟨fun _ => y, fun _ => x⟩)) (Ent.andE1 hH) htop)
  have hb2 : Ent S Δ2 [HypE] (boxF (supT : Fm Δ2)) :=
    Ent.mp hpe2 (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1)))) (v2 (supT : Fm Δ2) topF)
      (fun _ x y => ⟨fun _ => y, fun _ => x⟩)) (Ent.andE2 hH) htop)
  have hi : Ent S Δ2 [HypE] ((conj (boxF (subT : Fm Δ2)) (boxF (supT : Fm Δ2))).imp (teq tv1 tv0)) :=
    ((Ent.axm (Γ := Δ2) (Hs := [HypE]) hI).tinst tv1).tinst tv0
  have h2 : Ent S Δ2 ([] ++ [HypE]) (teq tv1 tv0) := Ent.mp hi (Ent.andI hb1 hb2)
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.intro (Hs := []) h2)))

end Derivations


/-! ## Truth values -/

namespace KeyData
variable (D : KeyData)

/-- In a model built from keys, PExt holds as long as keys are preserved by `→`. -/
theorem PExt_valid (hKa : ∀ a c d, D.K c = D.K d → D.K (.arr a c) = D.K (.arr a d)) : D.frame.Valid PExt :=
  (D.frame.valid_iff_tr _).mpr <| D.frame.tr_PExt.mpr fun a c d f g h =>
    have x0 := Classical.choice (Univ.El_nonempty (U := D.U) a)
    ⟨hKa a c d (h x0).1, heq_funext rfl (D.hK c d (h x0).1) (fun u u' hu => by cases hu; exact (h u).2)⟩

end KeyData

theorem M0_PExt : M0.Valid PExt := M0D.PExt_valid fun a _ _ h => congrArg (Code.arr a) h
theorem M0e_PExt : M0e.Valid PExt := M0eD.PExt_valid fun a _ _ h => congrArg (Code.arr (norm0e a)) h
theorem Mk_PExt : Mk.Valid PExt := MkD.PExt_valid fun a _ _ h => congrArg (specialK (normK a)) h
theorem Mcard_PExt : Mcard.Valid PExt := McardD.PExt_valid fun a _ _ h => congrArg (specialC (normC a)) h
theorem Mr_PExt : Mr.Valid PExt := MrD.PExt_valid fun a _ _ h => congrArg (Code.arr (normR a)) h
theorem Mtw_PExt : Mtw.Valid PExt := MtwD.PExt_valid fun a _ _ h => congrArg (Code.arr (normTw a)) h
theorem Mrec_PExt : Mrec.Valid PExt := MrecD.PExt_valid fun a _ _ h => congrArg (Code.arr (normKt a)) h
theorem Mt2_PExt : Mt2.Valid PExt := Mt2D.PExt_valid fun a _ _ h => congrArg (spT (normK2 a)) h

/-- In `𝔐(HF⁺, ∼ₚ)`, the constant functions with values `f₀` and `g₀` take identified values
everywhere, but are not identified. -/
theorem Mp_not_PExt : ¬ Mp.Valid PExt := fun h => by
  have := Mp.tr_PExt.mp ((Mp.valid_iff_tr _).mp h) .e (.arr .e .t) (.arr .e (.base ())) (fun _ => f0p) (fun _ => g0p)
    (fun _ => Or.inr (Or.inl ⟨rfl, rfl⟩))
  rcases this with h | ⟨h1, _⟩ | ⟨h1, _⟩
  · cases congrArg Sigma.fst h
  · cases congrArg Sigma.fst h1
  · cases congrArg Sigma.fst h1

/-- In `𝔐_D`, the constant functions `0` and `1` on `e` take identified values, but are not identified. -/
theorem MD_not_PExt : ¬ MD.Valid PExt := fun h => by
  have := MD.tr_PExt.mp ((MD.valid_iff_tr _).mp h) .e .e .e (fun _ => (0 : Fin 3)) (fun _ => (1 : Fin 3))
    (fun _ => ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩)
  rcases this.2 with h' | ⟨h', _⟩
  · have := congrFun (eq_of_heq h') (0 : Fin 3)
    exact absurd (this : (0 : Fin 3) = 1) (show ¬ (0 : Fin 3) = 1 by decide)
  · exact h'

namespace Tg

theorem Mi_not_PropExt : ¬ MiF.Valid PropExt := fun h => by
  have h1 := (MiF.holds_all _ _ _ _).mp ((MiF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (True, false)) (True, true)
  have := ((MiF.holds_eqv_t _ _ _ _).mp (h1 ⟨fun _ => trivial, fun _ => trivial⟩)).2
  exact Bool.noConfusion (congrArg Prod.snd (eq_of_heq this))

theorem Mtb_not_PropExt : ¬ MtbF.Valid PropExt := fun h => by
  have h1 := (MtbF.holds_all _ _ _ _).mp ((MtbF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (True, false)) (True, true)
  rcases ((MtbF.holds_eqv_t _ _ _ _).mp (h1 ⟨fun _ => trivial, fun _ => trivial⟩)).2 with e | ⟨_, s⟩
  · exact Bool.noConfusion (congrArg Prod.snd (eq_of_heq e))
  · exact Bool.noConfusion (s : true = false)

theorem Mit_not_PropExt : ¬ MitF.Valid PropExt := fun h => by
  have h1 := (MitF.holds_all _ _ _ _).mp ((MitF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (True, false)) (True, true)
  rcases ((MitF.holds_eqv_t _ _ _ _).mp (h1 ⟨fun _ => trivial, fun _ => trivial⟩)).2 with e | ⟨s, _⟩
  · exact Bool.noConfusion (congrArg Prod.snd (eq_of_heq e))
  · exact Bool.noConfusion (s : false = true)

end Tg


/-! ## Further models for PropExt≡ and PExt -/

theorem heq_app_of {A A' C C' : Type} (hA : A = A') (hC : C = C') {f : A → C} {g : A' → C'} {x : A} {y : A'}
    (hf : HEq f g) (hx : HEq x y) : HEq (f x) (g y) := by
  subst hA; subst hC; cases hf; cases hx; rfl

theorem Mall_PExt : Mall.Valid PExt := (Mall.valid_iff_tr _).mpr <| Mall.tr_PExt.mpr fun _ _ _ _ _ _ => trivial
theorem Mtot_PExt : Mtot.Valid PExt := (Mtot.valid_iff_tr _).mpr <| Mtot.tr_PExt.mpr fun a _ _ _ _ h =>
  ⟨congrArg (Code.arr a) (h (Classical.choice (Univ.El_nonempty (U := unitUniv) a))).1, Or.inr ⟨trivial, trivial⟩⟩
theorem Mfn_PExt : Mfn.Valid PExt := (Mfn.valid_iff_tr _).mpr <| Mfn.tr_PExt.mpr fun a _ _ _ _ h =>
  ⟨congrArg (Code.arr a) (h (Classical.choice (Univ.El_nonempty (U := unitUniv) a))).1, Or.inr ⟨trivial, trivial⟩⟩

/-- In `𝔐_hae,p`, the haecceity of the entity (a function from `e` to `t`) and the function sending
the entity to the haecceity of that haecceity's value take identified values, but are not identified. -/
theorem Mhp_not_PExt : ¬ Mhp.Valid PExt := fun h => by
  have := Mhp.tr_PExt.mp ((Mhp.valid_iff_tr _).mp h) .e .t (.arr .t .t) (haeF ovHP .e ())
    (fun x => haeF ovHP .t (haeF ovHP .e () x)) (fun x => (hr_hae ovHP .t _).symm)
  have h' : hr ovHP (.arr .e .t) (haeF ovHP .e ()) =
      hr ovHP (.arr .e (.arr .t .t)) (fun x => haeF ovHP .t (haeF ovHP .e () x)) := this
  have hr' := hrHP_plain (.arr .e (.arr .t .t)) (fun x => haeF ovHP .t (haeF ovHP .e () x)) (fun h => by cases h)
    (fun h => by injection h with _ h2; cases h2) (fun _ h => by injection h with _ h2; cases h2)
  cases congrArg Sigma.fst ((hrHP_e ()).symm.trans ((hr_hae ovHP .e ()).symm.trans (h'.trans hr')))

/-! ### `𝔐_bt`: Cong without PExt, in PI

`E = 1`, with a further base type `d` of two items; the entity is identified with the first of them,
and nothing else is identified with anything but itself. The constant functions on `e` with values
the entity and that item take identified values, but are not identified. -/

def univBT : Univ := { E := Unit, Base := Unit, B := fun _ => Bool, neE := ⟨()⟩, neB := fun _ => ⟨true⟩ }

def btC (p : Σ c : Code Unit, univBT.El c) : Prop := p.1 = .e ∨ (p.1 = .base () ∧ HEq p.2 true)

def MbtD : IdentData where
  U := univBT
  rel := fun p q => p = q ∨ (btC p ∧ btC q)
  refl := fun _ => Or.inl rfl
  symm := fun h => h.elim (fun e => Or.inl e.symm) (fun ⟨a, b⟩ => Or.inr ⟨b, a⟩)
  trans := by
    rintro p q r (rfl | ⟨_, hq⟩) (rfl | ⟨hq', hr⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hq', hr⟩
    · exact Or.inr ⟨by assumption, hq⟩
    · exact Or.inr ⟨by assumption, hr⟩

abbrev Mbt : Frame := MbtD.frame
theorem Mbt_model : Mbt.IsModelPIm := MbtD.model
theorem Mbt_Inj : Mbt.Valid Inj := MbtD.Inj_valid

theorem Mbt_within (c : Code Unit) (x y : univBT.El c) (h : MbtD.rel ⟨c, x⟩ ⟨c, y⟩) : x = y := by
  rcases h with h | ⟨hx, hy⟩
  · exact eq_of_heq (Sigma.mk.inj h).2
  · rcases hx with hx | ⟨hx, hx'⟩
    · cases c with
      | e => rfl
      | _ => cases hx
    · rcases hy with hy | ⟨_, hy'⟩
      · cases c with
        | e => rfl
        | _ => cases hy
      · exact eq_of_heq (hx'.trans hy'.symm)

theorem Mbt_LLEqv : Mbt.Valid LLEqv := MbtD.LLEqv_valid Mbt_within
theorem Mbt_Cong : Mbt.Valid Cong := (Mbt.valid_iff_tr _).mpr <| Mbt.tr_Cong.mpr fun a b c d f g x y ⟨hfg, hxy⟩ => by
  rcases hfg with hfg | ⟨h1 | ⟨h1, _⟩, _⟩
  · have hab : Code.arr a c = Code.arr b d := congrArg Sigma.fst hfg
    injection hab with ha hc
    subst ha; subst hc
    have e1 : f = g := eq_of_heq (Sigma.mk.inj hfg).2
    subst e1
    have e2 : x = y := Mbt_within a x y hxy
    subst e2
    exact MbtD.refl _
  · cases h1
  · cases h1
theorem Mbt_not_PExt : ¬ Mbt.Valid PExt := fun h => by
  have := Mbt.tr_PExt.mp ((Mbt.valid_iff_tr _).mp h) .e .e (.base ()) (fun _ => ()) (fun _ => true)
    (fun _ => Or.inr ⟨Or.inl rfl, Or.inr ⟨rfl, HEq.rfl⟩⟩)
  rcases this with h | ⟨h1 | ⟨h1, _⟩, _⟩
  · cases congrArg Sigma.fst h
  · cases h1
  · cases h1
theorem Mbt_Slogan : Mbt.Valid Slogan := (Mbt.valid_iff_tr _).mpr <| Mbt.tr_Slogan.mpr fun _ _ _ h => by
  rcases h with h | ⟨_, h | ⟨h, _⟩⟩
  · cases congrArg Sigma.fst h
  · cases h
  · cases h

theorem Mbt_loner (c : Code Unit) (hc : c ≠ .e) : ∃ z : univBT.El c, ¬ btC ⟨c, z⟩ := by
  cases c with
  | e => exact absurd rfl hc
  | base u => exact ⟨(show Bool from false), fun h => h.elim (fun h => by cases h) (fun ⟨_, h⟩ => by
      cases (eq_of_heq h : (false : Bool) = true))⟩
  | t => exact ⟨True, fun h => h.elim (fun h => by cases h) (fun ⟨h, _⟩ => by cases h)⟩
  | arr a c' => exact ⟨Classical.choice (Univ.El_nonempty (U := univBT) _), fun h =>
      h.elim (fun h => by cases h) (fun ⟨h, _⟩ => by cases h)⟩

theorem Mbt_ExtT : Mbt.Valid ExtT := (Mbt.valid_iff_tr _).mpr <| Mbt.tr_ExtT.mpr fun a b ⟨h1, h2⟩ => by
  show a = b
  refine Classical.byContradiction fun hab => ?_
  by_cases ha : a = .e
  · have hb : b ≠ .e := fun hb => hab (ha.trans hb.symm)
    obtain ⟨y, hy⟩ := Mbt_loner b hb
    obtain ⟨x, hx⟩ := h2 y
    rcases hx with hx | ⟨_, hy'⟩
    · exact hab (congrArg Sigma.fst hx)
    · exact hy hy'
  · obtain ⟨x, hx⟩ := Mbt_loner a ha
    obtain ⟨y, hy⟩ := h1 x
    rcases hy with hy | ⟨hx', _⟩
    · exact hab (congrArg Sigma.fst hy)
    · exact hx hx'
theorem Mbt_IntT : Mbt.Valid IntT :=
  (Mbt.IntT_iff_ExtT (fun p q => ⟨Mbt_within .t p q, fun h => h ▸ Or.inl rfl⟩)).mpr Mbt_ExtT

namespace Tg

namespace Frame
variable (F : Frame)

def Tr (φ : Fm Ctx.nil) : Prop := F.Holds φ (fun i => i.elim0) ()

theorem valid_iff_tr (φ : Fm Ctx.nil) : F.Valid φ ↔ F.Tr φ := by
  constructor
  · intro h; exact h _ _
  · intro h ρ env
    have : ρ = (fun i => i.elim0) := funext fun i => i.elim0
    subst this; exact h

theorem tr_Cong : F.Tr Cong ↔ ∀ a b c d (f : F.U.El a → F.U.El c) (g : F.U.El b → F.U.El d) x y,
    F.eqv (.arr a c) (.arr b d) f g ∧ F.eqv a b x y → F.eqv c d (f x) (g y) := Iff.rfl
theorem tr_PExt : F.Tr PExt ↔ ∀ a c d (f : F.U.El a → F.U.El c) (g : F.U.El a → F.U.El d),
    (∀ x, F.eqv c d (f x) (g x)) → F.eqv (.arr a c) (.arr a d) f g := Iff.rfl
theorem tr_Slogan : F.Tr Slogan ↔ ∀ x : F.U.E, ∀ b (y : F.U.El b → TV), ¬ F.eqv .e (.arr b .t) x y := Iff.rfl
theorem tr_Twin : F.Tr Twin ↔ ∀ a (x : F.U.El a), ∃ b, ¬ F.teq a b ∧ ∃ y : F.U.El b, F.eqv a b x y := Iff.rfl
theorem tr_Inj : F.Tr Inj ↔ ∀ a b c d, F.teq (.arr a c) (.arr b d) → F.teq a b ∧ F.teq c d := Iff.rfl
theorem tr_Disjoint : F.Tr Disjoint ↔ ∀ a b, ¬ F.teq a b → ∀ (x : F.U.El a) (y : F.U.El b), ¬ F.eqv a b x y := Iff.rfl
theorem tr_ExtT : F.Tr ExtT ↔ ∀ a b, ((∀ x : F.U.El a, ∃ y : F.U.El b, F.eqv a b x y) ∧
    (∀ y : F.U.El b, ∃ x : F.U.El a, F.eqv a b x y)) → F.teq a b := Iff.rfl

end Frame

/-! ### More values for `𝔐_int` -/

theorem El_kI : ∀ c, univI.El (kI c) = univI.El c
  | .e => rfl
  | .t => rfl
  | .base true => rfl
  | .base false => rfl
  | .arr a c => by show (univI.El (kI a) → univI.El (kI c)) = _; rw [El_kI a, El_kI c]; rfl

def twI : Code Bool → Code Bool
  | .e => .base true
  | .t => .base false
  | .base true => .e
  | .base false => .t
  | .arr a c => .arr (twI a) c

theorem kI_twI : ∀ c, kI (twI c) = kI c
  | .e => rfl
  | .t => rfl
  | .base true => rfl
  | .base false => rfl
  | .arr a c => by show Code.arr (kI (twI a)) (kI c) = _; rw [kI_twI a]; rfl

theorem twI_ne : ∀ c, twI c ≠ c
  | .e => fun h => by cases h
  | .t => fun h => by cases h
  | .base true => fun h => by cases h
  | .base false => fun h => by cases h
  | .arr a _ => fun h => by injection h with h1 _; exact twI_ne a h1

theorem elI {a b : Code Bool} (h : kI a = kI b) : univI.El a = univI.El b :=
  (El_kI a).symm.trans ((congrArg univI.El h).trans (El_kI b))

theorem Mi_Twin : MiF.Valid Twin := (MiF.valid_iff_tr _).mpr <| MiF.tr_Twin.mpr fun a x =>
  ⟨twI a, fun h => twI_ne a h.symm, cast (elI (kI_twI a).symm) x, (kI_twI a).symm, (cast_heq _ _).symm⟩
theorem Mi_Slogan : MiF.Valid Slogan := (MiF.valid_iff_tr _).mpr <| MiF.tr_Slogan.mpr fun _ _ _ h => by cases h.1
theorem Mi_Inj : MiF.Valid Inj := (MiF.valid_iff_tr _).mpr <| MiF.tr_Inj.mpr fun _ _ _ _ h => by
  injection h with h1 h2; exact ⟨h1, h2⟩
theorem Mi_Cong : MiF.Valid Cong := (MiF.valid_iff_tr _).mpr <| MiF.tr_Cong.mpr fun a b c d f g x y ⟨⟨hk, hfg⟩, ⟨hk2, hxy⟩⟩ => by
  injection hk with _ hcd
  exact ⟨hcd, heq_app_of (elI hk2) (elI hcd) hfg hxy⟩
theorem Mi_PExt : MiF.Valid PExt := (MiF.valid_iff_tr _).mpr <| MiF.tr_PExt.mpr fun a c d f g h =>
  have x0 := Classical.choice (Univ.El_nonempty (U := univI) a)
  ⟨congrArg (Code.arr (kI a)) (h x0).1, heq_funext rfl (elI (h x0).1) (fun u u' hu => by cases hu; exact (h u).2)⟩

/-! ### `𝔐_int0`: nothing identified across types, propositions finer than truth values -/

abbrev MzF : Frame where
  U := univU
  eqv := fun a b x y => a = b ∧ HEq x y
  teq := fun a b => a = b
  qtag := fun _ => false

theorem Mz_model : MzF.IsModelPIm :=
  MzF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => ⟨rfl, HEq.rfl⟩) (fun _ _ _ _ h => ⟨h.1.symm, h.2.symm⟩)
    (fun _ _ _ _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)

theorem Mz_LLEqv : MzF.Valid LLEqv := by
  intro ρ env a
  refine (MzF.holds_all _ _ _ _).mpr fun x => (MzF.holds_all _ _ _ _).mpr fun y hxy => ?_
  refine (MzF.holds_all _ _ _ _).mpr fun G hGx => ?_
  have h := ((MzF.holds_eqv _ _ _ _ _ _).mp hxy).2
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.trans (cast_heq _ _)))
  subst e
  exact hGx

theorem Mz_Disjoint : MzF.Valid Disjoint := (MzF.valid_iff_tr _).mpr <| MzF.tr_Disjoint.mpr fun _ _ hab _ _ h => hab h.1
theorem Mz_ExtT : MzF.Valid ExtT := (MzF.valid_iff_tr _).mpr <| MzF.tr_ExtT.mpr fun a _ ⟨h1, _⟩ =>
  (h1 (Classical.choice (Univ.El_nonempty (U := univU) a))).elim fun _ h => h.1
theorem Mz_IntT : MzF.Valid IntT := by
  intro ρ env a b hc
  have h1 := (MzF.holds_eqv _ _ _ _ _ _).mp ((MzF.holds_conj _ _ _ _).mp hc).1
  have h2 := (cast_heq _ _).symm.trans (h1.2.trans (cast_heq _ _))
  have e := congrArg Prod.snd (eq_of_heq h2)
  have hs : (MzF.eval (subT (Γ := (Ctx.nil.text).text)) (scons b (scons a ρ)) env).2 = false :=
    MzF.eval_all_snd _ _ _ _
  exact (Bool.false_ne_true (hs.symm.trans (e.trans rfl))).elim
theorem Mz_not_PropExt : ¬ MzF.Valid PropExt := fun h => by
  have h1 := (MzF.holds_all _ _ _ _).mp ((MzF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (True, false)) (True, true)
  have := ((MzF.holds_eqv_t _ _ _ _).mp (h1 ⟨fun _ => trivial, fun _ => trivial⟩)).2
  exact Bool.noConfusion (congrArg Prod.snd (eq_of_heq this))
theorem Mz_Slogan : MzF.Valid Slogan := (MzF.valid_iff_tr _).mpr <| MzF.tr_Slogan.mpr fun _ _ _ h => by cases h.1
theorem Mz_Cong : MzF.Valid Cong := (MzF.valid_iff_tr _).mpr <| MzF.tr_Cong.mpr fun _ _ _ _ _ _ _ _ ⟨⟨hk, hfg⟩, ⟨hk2, hxy⟩⟩ => by
  injection hk with _ hcd
  subst hk2; subst hcd
  exact ⟨rfl, heq_app_of rfl rfl hfg hxy⟩
theorem Mz_PExt : MzF.Valid PExt := (MzF.valid_iff_tr _).mpr <| MzF.tr_PExt.mpr fun a c d f g h =>
  have x0 := Classical.choice (Univ.El_nonempty (U := univU) a)
  ⟨congrArg (Code.arr a) (h x0).1, heq_funext rfl (congrArg univU.El (h x0).1) (fun u u' hu => by cases hu; exact (h u).2)⟩

end Tg


/-! ### `𝔐_hae,int`: haecceity towers with propositions finer than truth values -/

namespace Tg

section TowerT
attribute [local instance] Classical.propDecidable

abbrev RU := Σ c : Code univU.Base, univU.El c

/-- Roots, as in `PIHae.lean`; the haecceity of `x` is `λy.(y ≡ x)`, a tagged proposition. -/
noncomputable def hrT : (c : Code univU.Base) → univU.El c → RU
  | .arr a .t, G =>
    if h : ∃ x, G = (fun y => ((hrT a y = hrT a x : Prop), true)) then hrT a (Classical.choose h) else ⟨.arr a .t, G⟩
  | c, x => ⟨c, x⟩

def haeT (a : Code univU.Base) (x : univU.El a) : univU.El (.arr a .t) := fun y => ((hrT a y = hrT a x : Prop), true)

theorem hrT_arr_t (a : Code univU.Base) (G : univU.El (.arr a .t)) :
    hrT (.arr a .t) G = if h : ∃ x, G = (fun y => ((hrT a y = hrT a x : Prop), true))
      then hrT a (Classical.choose h) else ⟨.arr a .t, G⟩ := by
  rw [hrT]

theorem hrT_hae (a : Code univU.Base) (x : univU.El a) : hrT (.arr a .t) (haeT a x) = hrT a x := by
  rw [hrT_arr_t]
  split
  · next h =>
    have hc := Classical.choose_spec h
    exact (congrArg Prod.fst (congrFun hc (Classical.choose h))).mpr rfl
  · next h => exact absurd ⟨x, rfl⟩ h

theorem hrT_own (c : Code univU.Base) (hc : ∀ a, c ≠ .arr a .t) (x : univU.El c) : hrT c x = ⟨c, x⟩ := by
  cases c with
  | arr a c' => cases c' with
    | t => exact absurd rfl (hc a)
    | _ => rfl
  | _ => rfl

theorem hrT_le : ∀ (c : Code univU.Base) (x : univU.El c), csz (hrT c x).1 ≤ csz c
  | .arr a .t, G => by
    rw [hrT_arr_t]
    split
    · exact Nat.le_trans (hrT_le a _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _))
    · exact Nat.le_refl _
  | .e, _ => Nat.le_refl _
  | .t, _ => Nat.le_refl _
  | .base b, _ => b.elim
  | .arr _ .e, _ => Nat.le_refl _
  | .arr _ (.base b), _ => b.elim
  | .arr _ (.arr _ _), _ => Nat.le_refl _

theorem hrT_inj : ∀ (c : Code univU.Base) (x y : univU.El c), hrT c x = hrT c y → x = y
  | .arr a .t, G1, G2, h => by
    rw [hrT_arr_t, hrT_arr_t] at h
    have big : ∀ z, csz (hrT a z).1 < csz (Code.arr a .t) := fun z =>
      Nat.lt_of_le_of_lt (hrT_le a z) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.succ_le_succ (Nat.le_add_right _ _)))
    split at h <;> split at h
    · next h1 h2 =>
      rw [Classical.choose_spec h1, Classical.choose_spec h2]
      funext y
      rw [h]
    · next h1 _ =>
      have := congrArg (fun p => csz p.1) h
      exact absurd (this ▸ big (Classical.choose h1)) (Nat.lt_irrefl _)
    · next _ h2 =>
      have := congrArg (fun p => csz p.1) h
      exact absurd (this.symm ▸ big (Classical.choose h2)) (Nat.lt_irrefl _)
    · exact eq_of_heq (Sigma.mk.inj h).2
  | .e, x, y, h => eq_of_heq (Sigma.mk.inj h).2
  | .t, x, y, h => eq_of_heq (Sigma.mk.inj h).2
  | .base b, _, _, _ => b.elim
  | .arr _ .e, x, y, h => eq_of_heq (Sigma.mk.inj h).2
  | .arr _ (.base b), _, _, _ => b.elim
  | .arr _ (.arr _ _), x, y, h => eq_of_heq (Sigma.mk.inj h).2

noncomputable abbrev MhtF : Frame where
  U := univU
  eqv := fun a b x y => hrT a x = hrT b y
  teq := fun a b => a = b
  qtag := fun _ => false

end TowerT

namespace Frame
variable (F : Frame)
theorem tr_Hae : F.Tr Hae ↔ ∀ a (x : F.U.El a), F.eqv a (.arr a .t) x (fun y => (F.eqv a a y x, true)) := Iff.rfl
theorem tr_LLEqv : F.Tr LLEqv ↔ ∀ a (x y : F.U.El a), F.eqv a a x y → ∀ P : F.U.El a → TV, (P x).1 → (P y).1 := Iff.rfl
end Frame

theorem Mht_model : MhtF.IsModelPIm :=
  MhtF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => rfl) (fun _ _ _ _ h => h.symm) (fun _ _ _ _ _ _ h1 h2 => h1.trans h2)
theorem Mht_Hae : MhtF.Valid Hae := (MhtF.valid_iff_tr _).mpr <| MhtF.tr_Hae.mpr fun a x => (hrT_hae a x).symm
theorem Mht_LLEqv : MhtF.Valid LLEqv := (MhtF.valid_iff_tr _).mpr <| MhtF.tr_LLEqv.mpr fun a x y h _ hP =>
  hrT_inj a x y h ▸ hP
theorem Mht_not_PropExt : ¬ MhtF.Valid PropExt := fun h => by
  have h1 := (MhtF.holds_all _ _ _ _).mp ((MhtF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (True, false)) (True, true)
  have := (MhtF.holds_eqv_t _ _ _ _).mp (h1 ⟨fun _ => trivial, fun _ => trivial⟩)
  have e := hrT_inj .t _ _ this
  exact Bool.noConfusion (congrArg Prod.snd e)

end Tg

end PIF
