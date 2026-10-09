import PIBarcanModels

/-!
# Classicism

The Classicist thesis that logical equivalence suffices for identity, in the form: whenever PI proves
`φ ↔ ψ`, the universal closure of `φ ≡_t ψ` holds, and so does that of `λx.φ ≡ λx.ψ`. With PI, this
is the base logic "PI + Classicism".
-/
set_option autoImplicit false

namespace PIF
open Tm Derive

/-- Universal closure over all the variables of a context. -/
def closeCtx : {n : Nat} → (Γ : Ctx n) → Fm Γ → Fm Ctx.nil
  | _, .nil, φ => φ
  | _, .ext Γ σ, φ => closeCtx Γ (all σ φ)
  | _, .text Γ, φ => closeCtx Γ (tall φ)

/-- Provability in PI, with no further axioms. -/
abbrev PIP {n : Nat} (Γ : Ctx n) (φ : Fm Γ) : Prop := Prov (fun χ => χ = LLEqv) Γ φ

/-- (Class) The Classicist schema. -/
def ClassSch : Fm Ctx.nil → Prop := fun χ =>
  (∃ n, ∃ Γ : Ctx n, ∃ φ ψ : Fm Γ, PIP Γ (iff φ ψ) ∧ χ = closeCtx Γ (eqv tyT tyT φ ψ)) ∨
  (∃ n, ∃ Γ : Ctx n, ∃ σ : Ty n, ∃ φ ψ : Fm (Γ.ext σ), PIP (Γ.ext σ) (iff φ ψ) ∧
    χ = closeCtx Γ (eqv σ.pred σ.pred (lam σ φ) (lam σ ψ)))

theorem closeCtx_ctxT : ∀ (k : Nat) (φ : Fm (ctxT k)), closeCtx (ctxT k) φ = closeAll k φ
  | 0, _ => rfl
  | k + 1, φ => closeCtx_ctxT k (all tyT φ)

/-! ## Derivations -/

section Derivs
variable {S : Fm Ctx.nil → Prop}

/-- Classicism proves every instance of Booleanism. -/
theorem d_Bool_of_Class (hC : ∀ χ, ClassSch χ → S χ) : ∀ χ, BoolSch χ → Prov S Ctx.nil χ := by
  rintro _ ⟨k, P, Q, hT, rfl⟩
  refine Prov.ax (hC _ (Or.inl ⟨0, ctxT k, P.inst (varsT k), Q.inst (varsT k), Prov.taut (PF.iff P Q) (varsT k) hT, ?_⟩))
  exact (closeCtx_ctxT k _).symm

set_option maxHeartbeats 4000000 in
theorem iff_IdId (hLL : S LLEqv) : Prov S Γxy (iff Exy Axy) := by
  have hl : Ent S Γxy [] (Exy.imp Axy) :=
    (((Ent.axm (Γ := Γxy) (Hs := []) hLL).tinst tv0).inst (.var (.there .here))).inst (.var .here)
  have hH : Ent S Γxy [Axy] Axy := Ent.hyp _ 0 (by decide)
  have h1 := Ent.inst hH (.lam tv0 (eqv tv0 tv0 (.var (.there (.there .here))) (.var .here)))
  have h2 : Ent S Γxy [Axy] ((eqv tv0 tv0 (.var (.there .here)) (.var (.there .here))).imp Exy) :=
    Ent.beta h1 (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  have hr : Ent S Γxy [Axy] (eqv tv0 tv0 (.var (.there .here)) (.var (.there .here))) :=
    ((Ent.closed (Γ := Γxy) Prov.refEqv).tinst tv0).inst (.var (.there .here))
  have h3 : Ent S Γxy ([] ++ [Axy]) Exy := Ent.mp h2 hr
  exact Ent.toProv (Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.atom 1)) (.imp (.imp (.atom 1) (.atom 0)) (.iff (.atom 0) (.atom 1))))
      (v2 Exy Axy) (fun _ f g => ⟨f, g⟩)) hl (Ent.intro h3))

/-- Classicism proves the Identity Identity (given LL≡). -/
theorem d_IdId_of_Class (hC : ∀ χ, ClassSch χ → S χ) : Prov S Ctx.nil IdId :=
  Prov.ax (hC _ (Or.inl ⟨1, Γxy, Exy, Axy, iff_IdId rfl, rfl⟩))

abbrev Γx1 : Ctx 1 := Δ1.ext tv0
/-- `𝔸α ∀_α x □(x ≡ x)` -/
def RefBox : Fm Ctx.nil := tall (all tv0 (boxF (eqv tv0 tv0 (.var .here) (.var .here))))

set_option maxHeartbeats 4000000 in
theorem RefBox_class : ClassSch RefBox := by
  refine Or.inl ⟨1, Γx1, eqv tv0 tv0 (.var .here) (.var .here), topF, ?_, rfl⟩
  have hr : Ent (fun χ => χ = LLEqv) Γx1 [] (eqv tv0 tv0 (.var .here) (.var .here)) :=
    ((Ent.closed (Γ := Γx1) Prov.refEqv).tinst tv0).inst (.var .here)
  exact Ent.toProv (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1))))
    (v2 _ topF) (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) hr Ent.top)

set_option maxHeartbeats 4000000 in
/-- Classicism and LL≡ prove NI≡, by Quine's argument: LL≡ with `F := λz.□(x ≡ z)`. -/
theorem d_NIEqv_of_Class (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) : Prov S Ctx.nil NIEqv := by
  have hR : S RefBox := hC _ RefBox_class
  have hl : Ent S Γxy [Exy] (Exy.imp Axy) :=
    (((Ent.axm (Γ := Γxy) (Hs := [Exy]) hLL).tinst tv0).inst (.var (.there .here))).inst (.var .here)
  have hA := Ent.mp hl (Ent.hyp _ 0 (by decide))
  have h1 := Ent.inst hA (.lam tv0 (boxF (eqv tv0 tv0 (.var (.there (.there .here))) (.var .here))))
  have h2 : Ent S Γxy [Exy] ((boxF (eqv tv0 tv0 (.var (.there .here)) (.var (.there .here)))).imp (boxF Exy)) :=
    Ent.beta h1 (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  have hb : Ent S Γxy [Exy] (boxF (eqv tv0 tv0 (.var (.there .here)) (.var (.there .here)))) :=
    ((Ent.axm (Γ := Γxy) (Hs := [Exy]) hR).tinst tv0).inst (.var (.there .here))
  have h3 : Ent S Γxy ([] ++ [Exy]) (boxF Exy) := Ent.mp h2 hb
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen tv0 (Hs := []) (Ent.gen tv0 (Hs := []) (Ent.intro h3))))

set_option maxHeartbeats 4000000 in
/-- Classicism proves Type Necessitism. -/
theorem d_TNec_of_Class (hC : ∀ χ, ClassSch χ → S χ) : Prov S Ctx.nil TNec := by
  refine Prov.ax (hC _ (Or.inl ⟨1, Δ1, tex (teq tv1 tv0), topF, ?_, rfl⟩))
  have hr : Ent (fun χ => χ = LLEqv) Δ1 [] (teq tv0 tv0) := (Ent.closed (Γ := Δ1) Prov.refTeq).tinst tv0
  have he : Ent (fun χ => χ = LLEqv) Δ1 [] (tex (teq tv1 tv0)) := Ent.texI (φ := teq tv1 tv0) tv0 hr
  exact Ent.toProv (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1))))
    (v2 _ topF) (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) he Ent.top)

set_option maxHeartbeats 4000000 in
/-- Classicism proves NI≈, by the argument for NI≡ with LL≈ in place of LL≡: LL≈ with
`Q := Λβ.□(α ≈ β)`. -/
theorem d_NITeq_of_Class (hC : ∀ χ, ClassSch χ → S χ) : Prov S Ctx.nil NITeq := by
  have hR : S (tall (boxF (teq tv0 tv0))) := by
    refine hC _ (Or.inl ⟨1, Δ1, teq tv0 tv0, topF, ?_, rfl⟩)
    have hr : Ent (fun χ => χ = LLEqv) Δ1 [] (teq tv0 tv0) := (Ent.closed (Γ := Δ1) Prov.refTeq).tinst tv0
    exact Ent.toProv (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1))))
      (v2 _ topF) (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) hr Ent.top)
  have hQ : Ent S Δ2 [] (LLTeq (Tm.tlam (boxF (Tm.teq tv2 tv0)))) := Ent.ofProv (Prov.llTeq _)
  have h1 : Ent S Δ2 [] ((Tm.teq tv1 tv0).imp ((boxF (Tm.teq tv1 tv1)).imp (boxF (Tm.teq tv1 tv0)))) :=
    Ent.beta ((hQ.tinst tv1).tinst tv0) (BetaEq.imp (.refl _) (BetaEq.imp (BetaEq.tbeta _ _) (BetaEq.tbeta _ _)))
  have hb : Ent S Δ2 [] (boxF (Tm.teq tv1 tv1)) := (Ent.axm (Γ := Δ2) hR).tinst tv1
  have h2 : Ent S Δ2 [] ((Tm.teq tv1 tv0).imp (boxF (Tm.teq tv1 tv0))) :=
    Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2))) (.imp (.atom 1) (.imp (.atom 0) (.atom 2))))
      (v3 (Tm.teq tv1 tv0) (boxF (Tm.teq tv1 tv1)) (boxF (Tm.teq tv1 tv0))) (fun _ f b a => f a b)) h1 hb
  exact Ent.toProv (Ent.tgen (Ent.tgen h2))

set_option maxHeartbeats 4000000 in
/-- LL≡ at `t` makes disjunction respect identity in its second place. -/
theorem or_cong (hLL : S LLEqv) {n : Nat} {Γ : Ctx n} (a b c : Fm Γ) :
    Prov S Γ ((eqv tyT tyT b c).imp (eqv tyT tyT (disj a b) (disj a c))) := by
  have hl : Ent S Γpqr [eqv tyT tyT (.var (.there .here)) (.var .here)]
      ((eqv tyT tyT (.var (.there .here)) (.var .here)).imp
        (all tyT.pred (imp (.app (.var .here) (.var (.there (.there .here))))
                       (.app (.var .here) (.var (.there .here)))))) :=
    (((Ent.axm (Γ := Γpqr) hLL).tinst tyT).inst (.var (.there .here))).inst (.var .here)
  have hA := Ent.mp hl (Ent.hyp _ 0 (by decide))
  have h1 := Ent.inst hA (.lam tyT (eqv tyT tyT (disj (.var (.there (.there (.there .here)))) (.var (.there (.there .here))))
    (disj (.var (.there (.there (.there .here)))) (.var .here))))
  have h2 : Ent S Γpqr [eqv tyT tyT (.var (.there .here)) (.var .here)]
      ((eqv tyT tyT (disj (.var (.there (.there .here))) (.var (.there .here))) (disj (.var (.there (.there .here))) (.var (.there .here)))).imp
       (eqv tyT tyT (disj (.var (.there (.there .here))) (.var (.there .here))) (disj (.var (.there (.there .here))) (.var .here)))) :=
    Ent.beta h1 (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  have hr : Ent S Γpqr [eqv tyT tyT (.var (.there .here)) (.var .here)]
      (eqv tyT tyT (disj (.var (.there (.there .here))) (.var (.there .here))) (disj (.var (.there (.there .here))) (.var (.there .here)))) :=
    ((Ent.closed (Γ := Γpqr) Prov.refEqv).tinst tyT).inst _
  have h : Prov S Γpqr ((eqv tyT tyT (.var (.there .here)) (.var .here)).imp
      (eqv tyT tyT (disj (.var (.there (.there .here))) (.var (.there .here))) (disj (.var (.there (.there .here))) (.var .here)))) :=
    Ent.toProv (Ent.intro (Hs := []) (Ent.mp h2 hr))
  exact Prov.subst _ _ h (subPQR a b c)

set_option maxHeartbeats 8000000 in
/-- Classicism and LL≡ prove every instance of TCBF: `□𝔸α φ` gives `φ ≡ φ ∨ 𝔸α φ ≡ φ ∨ ⊤ ≡ ⊤`. -/
theorem d_TCBF_of_Class (hC : ∀ χ, ClassSch χ → S χ) (hLL : S LLEqv) : ∀ χ, TCBFSch χ → Prov S Ctx.nil χ := by
  rintro _ ⟨φ, rfl⟩
  let A : Fm Ctx.nil.text := tall (φ.ren (Compl.twkL Ctx.nil))
  let Hs : List (Fm Ctx.nil.text) := [boxF (tall φ)].map (fun h => (h.twk : Fm Ctx.nil.text))
  have hq : Ent S Ctx.nil.text Hs (eqv tyT tyT A topF) := Ent.hyp _ 0 (by exact Nat.one_pos)
  -- Classicism: `φ ∨ 𝔸α φ ≡ φ` and `φ ∨ ⊤ ≡ ⊤`
  have hc1 : S (tall (eqv tyT tyT (disj φ A) φ)) := by
    refine hC _ (Or.inl ⟨1, Δ1, disj φ A, φ, ?_, rfl⟩)
    have hH : Ent (fun χ => χ = LLEqv) Ctx.nil.text [A] A := Ent.hyp _ 0 (by exact Nat.one_pos)
    have h1 := (congrArg (Ent _ _ _) (tcontract_eq φ)).mp (Ent.tinst hH (tvar fz))
    have hAφ : Ent (fun χ => χ = LLEqv) Ctx.nil.text [] (A.imp φ) := Ent.intro (Hs := []) h1
    exact Ent.toProv (Ent.mp (Ent.taut (.imp (.imp (.atom 1) (.atom 0)) (.iff (.disj (.atom 0) (.atom 1)) (.atom 0)))
      (v2 φ A) (fun _ f => ⟨fun h => h.elim id f, Or.inl⟩)) hAφ)
  have hc2 : S (tall (eqv tyT tyT (disj φ topF) topF)) := by
    refine hC _ (Or.inl ⟨1, Δ1, disj φ topF, topF, ?_, rfl⟩)
    exact Ent.toProv (Ent.mp (Ent.taut (.imp (.atom 1) (.iff (.disj (.atom 0) (.atom 1)) (.atom 1)))
      (v2 φ topF) (fun _ t => ⟨fun _ => t, Or.inr⟩)) (Ent.top (Ax := fun χ => χ = LLEqv) (Hs := [])))
  have e10 : Ent S Ctx.nil [] (tall (eqv tyT tyT (disj φ A) φ)) := Prov.ax hc1
  have e11 : Prov S Ctx.nil.text (eqv tyT tyT (disj φ A) φ) :=
    (congrArg (Ent S Ctx.nil.text []) (tcontract_eq (eqv tyT tyT (disj φ A) φ))).mp (Ent.tinst (Ent.ren_twk e10) (tvar fz))
  have e1 : Ent S Ctx.nil.text Hs (eqv tyT tyT (disj φ A) φ) := Ent.ofProv e11
  have e20 : Ent S Ctx.nil [] (tall (eqv tyT tyT (disj φ topF) topF)) := Prov.ax hc2
  have e21 : Prov S Ctx.nil.text (eqv tyT tyT (disj φ topF) topF) :=
    (congrArg (Ent S Ctx.nil.text []) (tcontract_eq (eqv tyT tyT (disj φ topF) topF))).mp (Ent.tinst (Ent.ren_twk e20) (tvar fz))
  have e2 : Ent S Ctx.nil.text Hs (eqv tyT tyT (disj φ topF) topF) := Ent.ofProv e21
  have e3 : Ent S Ctx.nil.text Hs (eqv tyT tyT (disj φ A) (disj φ topF)) := Ent.mp (Ent.ofProv (or_cong hLL φ A topF)) hq
  have e4 : Ent S Ctx.nil.text Hs (eqv tyT tyT φ (disj φ A)) := Ent.mp (Ent.ofProv (sym_t (disj φ A) φ)) e1
  have e5 : Ent S Ctx.nil.text Hs (eqv tyT tyT φ (disj φ topF)) :=
    Ent.mp (Ent.ofProv (trans_t φ (disj φ A) (disj φ topF))) (Ent.andI e4 e3)
  have e6 : Ent S Ctx.nil.text Hs (boxF φ) :=
    Ent.mp (Ent.ofProv (trans_t φ (disj φ topF) topF)) (Ent.andI e5 e2)
  have h3 : Ent S Ctx.nil ([] ++ [boxF (tall φ)]) (tall (boxF φ)) := Ent.tgen e6
  exact Ent.toProv (Ent.intro h3)

end Derivs

/-! ## Every model of PI in the semantics of the notes is a model of Classicism -/

namespace Frame
variable (F : Frame)

theorem valid_closeCtx : ∀ {n : Nat} (Γ : Ctx n) (χ : Fm Γ), (∀ ρ env, F.Holds χ ρ env) → F.Valid (closeCtx Γ χ)
  | _, .nil, _, h => h
  | _, .ext Γ σ, χ, h => valid_closeCtx Γ (all σ χ) fun ρ env => (F.holds_all σ χ ρ env).mpr fun v => h ρ (env, v)
  | _, .text Γ, χ, h => valid_closeCtx Γ (tall χ) fun ρ env a => h (scons a ρ) env

theorem Class_valid (hM : F.IsModelPIm) (hLL : F.Valid LLEqv) : ∀ χ, ClassSch χ → F.Valid χ := by
  have ref : ∀ a x, F.eqv a a x x := F.tr_RefEqv.mp ((F.valid_iff_tr _).mp hM.refEqv)
  rintro _ (⟨n, Γ, φ, ψ, hp, rfl⟩ | ⟨n, Γ, σ, φ, ψ, hp, rfl⟩)
  · have hv := F.soundness hM (fun χ (h : χ = LLEqv) => h ▸ hLL) hp
    refine F.valid_closeCtx Γ _ fun ρ env => ?_
    have e : F.eval φ ρ env = F.eval ψ ρ env := propext (hv ρ env)
    refine (F.holds_eqv tyT tyT φ ψ ρ env).mpr ?_
    show F.eqv .t .t (F.eval φ ρ env) (F.eval ψ ρ env)
    rw [e]; exact ref _ _
  · have hv := F.soundness hM (fun χ (h : χ = LLEqv) => h ▸ hLL) hp
    refine F.valid_closeCtx Γ _ fun ρ env => ?_
    have e : F.eval (lam σ φ : Tm Γ σ.pred.1) ρ env = F.eval (lam σ ψ : Tm Γ σ.pred.1) ρ env :=
      funext fun v => propext (hv ρ (env, v))
    refine (F.holds_eqv σ.pred σ.pred _ _ ρ env).mpr ?_
    have key : ∀ x y : F.U.CatVal σ.pred.1 ρ, x = y →
        F.eqv (F.U.code σ.pred.1 ρ) (F.U.code σ.pred.1 ρ) (cast (Univ.El_code ρ σ.pred.2).symm x)
          (cast (Univ.El_code ρ σ.pred.2).symm y) := by
      intro x y h; subst h; exact ref _ _
    exact key _ _ e

end Frame

theorem M0_Class : ∀ χ, ClassSch χ → M0.Valid χ := M0.Class_valid M0_model M0_LLEqv
theorem M0e_Class : ∀ χ, ClassSch χ → M0e.Valid χ := M0e.Class_valid M0e_model M0e_LLEqv
theorem M1_Class : ∀ χ, ClassSch χ → M1.Valid χ := M1.Class_valid M1_model M1_LLEqv
theorem Mh_Class : ∀ χ, ClassSch χ → Mh.Valid χ := Mh.Class_valid Mh_model Mh_LLEqv
theorem Mp_Class : ∀ χ, ClassSch χ → Mp.Valid χ := Mp.Class_valid Mp_model Mp_LLEqv
theorem Mhp_Class : ∀ χ, ClassSch χ → Mhp.Valid χ := Mhp.Class_valid Mhp_model Mhp_LLEqv
theorem Mhk_Class : ∀ χ, ClassSch χ → Mhk.Valid χ := Mhk.Class_valid Mhk_model Mhk_LLEqv
theorem Mbt_Class : ∀ χ, ClassSch χ → Mbt.Valid χ := Mbt.Class_valid Mbt_model Mbt_LLEqv
theorem Mhx_Class : ∀ χ, ClassSch χ → Mhx.Valid χ := Mhx.Class_valid Mhx_model Mhx_LLEqv
theorem Mk_Class : ∀ χ, ClassSch χ → Mk.Valid χ := Mk.Class_valid Mk_model Mk_LLEqv
theorem Mr_Class : ∀ χ, ClassSch χ → Mr.Valid χ := Mr.Class_valid Mr_model Mr_LLEqv
theorem Mcard_Class : ∀ χ, ClassSch χ → Mcard.Valid χ := Mcard.Class_valid Mcard_model Mcard_LLEqv
theorem Mtw_Class : ∀ χ, ClassSch χ → Mtw.Valid χ := Mtw.Class_valid Mtw_model Mtw_LLEqv
theorem Mt2_Class : ∀ χ, ClassSch χ → Mt2.Valid χ := Mt2.Class_valid Mt2_model Mt2_LLEqv
theorem Mrec_Class : ∀ χ, ClassSch χ → Mrec.Valid χ := Mrec.Class_valid Mrec_model Mrec_LLEqv

/-! ## `𝔐_w` is a model of Classicism -/

namespace Wd

namespace Frame
variable (F : Frame)

theorem holdsAt_tall {n : Nat} {Γ : Ctx n} (φ : Fm Γ.text) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (w : F.U.W) :
    F.HoldsAt (Tm.tall φ) ρ env w ↔ ∀ a, F.HoldsAt φ (scons a ρ) env w := Iff.rfl

theorem valid_closeCtx : ∀ {n : Nat} (Γ : Ctx n) (χ : Fm Γ), (∀ ρ env, F.Holds χ ρ env) → F.Valid (closeCtx Γ χ)
  | _, .nil, _, h => h
  | _, .ext Γ σ, χ, h => valid_closeCtx Γ (all σ χ) fun ρ env => (F.holds_all σ χ ρ env).mpr fun v => h ρ (env, v)
  | _, .text Γ, χ, h => valid_closeCtx Γ (tall χ) fun ρ env => (F.holds_tall χ ρ env).mpr fun a => h (scons a ρ) env

end Frame

namespace RD
variable (D : RD)

theorem isModelAt (hE : ∀ w, D.Ee w) (hT : ∀ a b w, D.Te a b w ↔ a = b) : D.frame.IsModelAt where
  refEqv := by
    intro w ρ env
    refine (D.frame.holdsAt_tall _ _ _ w).mpr fun a => (D.frame.holdsAt_all _ _ _ _ w).mpr fun x => ?_
    exact (D.frame.holdsAt_eqv _ _ _ _ _ _ w).mpr ⟨rfl, HEq.rfl, hE w⟩
  symEqv := by
    intro w ρ env
    refine (D.frame.holdsAt_tall _ _ _ w).mpr fun a => (D.frame.holdsAt_tall _ _ _ w).mpr fun b => ?_
    refine (D.frame.holdsAt_all _ _ _ _ w).mpr fun x => (D.frame.holdsAt_all _ _ _ _ w).mpr fun y => ?_
    refine (D.frame.holdsAt_imp _ _ _ _ w).mpr fun h => ?_
    have h' := (D.frame.holdsAt_eqv _ _ _ _ _ _ w).mp h
    exact (D.frame.holdsAt_eqv _ _ _ _ _ _ w).mpr ⟨h'.1.symm, h'.2.1.symm, h'.2.2⟩
  transEqv := by
    intro w ρ env
    refine (D.frame.holdsAt_tall _ _ _ w).mpr fun a => (D.frame.holdsAt_tall _ _ _ w).mpr fun b =>
      (D.frame.holdsAt_tall _ _ _ w).mpr fun c => ?_
    refine (D.frame.holdsAt_all _ _ _ _ w).mpr fun x => (D.frame.holdsAt_all _ _ _ _ w).mpr fun y =>
      (D.frame.holdsAt_all _ _ _ _ w).mpr fun z => ?_
    refine (D.frame.holdsAt_imp _ _ _ _ w).mpr fun h => ?_
    have h1 := (D.frame.holdsAt_eqv (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv2 tv1
      (.var (.there (.there .here))) (.var (.there .here)) (scons c (scons b (scons a ρ))) (((env, x), y), z) w).mp h.1
    have h2 := (D.frame.holdsAt_eqv (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv1 tv0
      (.var (.there .here)) (.var .here) (scons c (scons b (scons a ρ))) (((env, x), y), z) w).mp h.2
    exact (D.frame.holdsAt_eqv _ _ _ _ _ _ w).mpr ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2⟩
  refTeq := by
    intro w ρ env
    exact (D.frame.holdsAt_tall _ _ _ w).mpr fun a => (D.frame.holdsAt_teq _ _ _ _ w).mpr ((hT a a w).mpr rfl)
  llTeq := by
    intro n Γ Q w ρ env
    refine (D.frame.holdsAt_tall _ _ _ w).mpr fun a => (D.frame.holdsAt_tall _ _ _ w).mpr fun b => ?_
    refine (D.frame.holdsAt_imp _ _ _ _ w).mpr fun hab => ?_
    have hab' : a = b := (hT a b w).mp ((D.frame.holdsAt_teq (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env w).mp hab)
    subst hab'
    refine (D.frame.holdsAt_imp _ _ _ _ w).mpr fun hq => ?_
    have e1 : HEq (D.frame.eval (Tm.tapp Q.twk.twk tv1) (scons a (scons a ρ)) env)
        (D.frame.eval Q.twk.twk (scons a (scons a ρ)) env a) :=
      D.frame.heq_eval_tapp (K := Cat.t) Q.twk.twk tv1 (scons a (scons a ρ)) env
    have e2 : HEq (D.frame.eval (Tm.tapp Q.twk.twk tv0) (scons a (scons a ρ)) env)
        (D.frame.eval Q.twk.twk (scons a (scons a ρ)) env a) :=
      D.frame.heq_eval_tapp (K := Cat.t) Q.twk.twk tv0 (scons a (scons a ρ)) env
    exact cast (D.frame.holdsAt_of_heq (e1.trans e2.symm) w) hq

theorem LLEqv_validAt : D.frame.ValidAt LLEqv := by
  intro w ρ env
  refine (D.frame.holdsAt_tall _ _ _ w).mpr fun a => ?_
  refine (D.frame.holdsAt_all _ _ _ _ w).mpr fun x => (D.frame.holdsAt_all _ _ _ _ w).mpr fun y => ?_
  refine (D.frame.holdsAt_imp _ _ _ _ w).mpr fun hxy => ?_
  refine (D.frame.holdsAt_all _ _ _ _ w).mpr fun G => (D.frame.holdsAt_imp _ _ _ _ w).mpr fun hGx => ?_
  have h := ((D.frame.holdsAt_eqv _ _ _ _ _ _ w).mp hxy).2.1
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.trans (cast_heq _ _)))
  subst e
  exact hGx

theorem Class_valid (hE : ∀ w, D.Ee w) (hT : ∀ a b w, D.Te a b w ↔ a = b) : ∀ χ, ClassSch χ → D.frame.Valid χ := by
  have sound : ∀ {n : Nat} {Γ : Ctx n} {θ : Fm Γ}, PIP Γ θ → D.frame.ValidAt θ := fun h =>
    D.frame.soundnessAt (D.isModelAt hE hT) (fun χ (e : χ = LLEqv) => e ▸ D.LLEqv_validAt) h
  rintro _ (⟨n, Γ, φ, ψ, hp, rfl⟩ | ⟨n, Γ, σ, φ, ψ, hp, rfl⟩)
  · refine D.frame.valid_closeCtx Γ _ fun ρ env => ?_
    have e : D.frame.eval φ ρ env = D.frame.eval ψ ρ env := funext fun w => propext (sound hp w ρ env)
    exact (D.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq e, D.hE⟩
  · refine D.frame.valid_closeCtx Γ _ fun ρ env => ?_
    have e : D.frame.eval (lam σ φ) ρ env = D.frame.eval (lam σ ψ) ρ env :=
      funext fun v => funext fun w => propext (sound hp w ρ (env, v))
    exact (D.frame.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, (cast_heq _ _).trans ((heq_of_eq e).trans (cast_heq _ _).symm), D.hE⟩

end RD

theorem Mw_Class : ∀ χ, ClassSch χ → DW.frame.Valid χ := DW.Class_valid (fun _ => trivial) (fun _ _ _ => Iff.rfl)

end Wd
end PIF
