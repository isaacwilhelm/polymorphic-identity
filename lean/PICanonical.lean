import PICompleteness

/-!
# Completeness, part 2: witnesses and the canonical general model

Building on the Henkin chain of `PICompleteness`: the witness lemmas, then the canonical general
model, whose types are the codes of types at some stage, whose items are classes of codes of terms
modulo β-conversion, and whose truth valuation is truth in the limit.
-/
set_option autoImplicit false

namespace PIF
namespace Compl
open Derive

/-! ## Syntactic lemmas -/

theorem ex_inj {n : Nat} {Γ : Ctx n} {σ σ' : Ty n} {φ : Fm (Γ.ext σ)} {φ' : Fm (Γ.ext σ')}
    (h : Tm.ex σ φ = Tm.ex σ' φ') : σ = σ' ∧ HEq φ φ' := by
  obtain ⟨e1, _, e3⟩ := Tm.app.inj h
  have e : σ = σ' := Subtype.ext (Cat.arr.inj e1).1
  subst e
  exact ⟨rfl, heq_of_eq (Tm.lam.inj (eq_of_heq e3))⟩

theorem tex_inj {n : Nat} {Γ : Ctx n} {φ φ' : Fm Γ.text} (h : Tm.tex φ = Tm.tex φ') : φ = φ' := by
  obtain ⟨_, _, e3⟩ := Tm.app.inj h
  exact Tm.tlam.inj (eq_of_heq e3)

/-- Weakening beneath the last type variable. -/
abbrev twkL {n : Nat} (Γ : Ctx n) : ∀ {K : Cat (n+1)}, Var Γ.text K → Var Γ.text.text (K.ren (liftR fs)) :=
  @TRen.tlift _ _ fs Γ Γ.text (twkRen Γ)

/-- Weakening beneath the last term variable. -/
abbrev wkL {n : Nat} {Γ : Ctx n} (τ : Ty n) : ∀ {K : Cat n}, Var (Γ.ext τ) K → Var ((Γ.ext τ).ext (τ.ren (fun i => i))) (K.ren (fun i => i)) :=
  TRen.lift (wkRen (Γ := Γ) τ) τ

/-- Renaming a fresh copy of the last variable, then substituting the last variable for it. -/
theorem contract_heq {n : Nat} {Γ : Ctx n} (τ : Ty n) {L : Cat n} (ψ : Tm (.ext Γ τ) L) :
    HEq ((ψ.ren (wkL (Γ := Γ) τ)).subst0 (Tm.castK (Cat.ren_id τ.1).symm (Tm.var .here))) ψ := by
  let σi : TSub tvar (.ext Γ τ) (.ext Γ τ) := fun {L'} x => Tm.castK (Cat.sub_var L').symm (Tm.var x)
  have h1 : HEq ((ψ.ren (wkL (Γ := Γ) τ)).sub (sub0 (Tm.castK (Cat.ren_id τ.1).symm (Tm.var .here))))
      (ψ.sub σi) := by
    refine Tm.sub_ren_heq ψ _ rfl _ σi (fun _ => rfl) ?_
    intro L' x
    cases x with
    | here => exact (castK_heq _ _).trans ((castK_heq _ _).trans (castK_heq _ _).symm)
    | there y => exact (castK_heq _ _).trans ((var_castK_heq _ _).trans (castK_heq _ _).symm)
  exact (castK_heq _ _).trans (h1.trans (Tm.sub_id_heq ψ rfl σi (fun _ => rfl) (fun _ => (castK_heq _ _).symm)).symm)

/-- The same, for a type variable. -/
theorem tcontract_heq {n : Nat} {Γ : Ctx n} {L : Cat (n+1)} (ψ : Tm Γ.text L) :
    HEq ((ψ.ren (twkL Γ)).tinst (tvar fz)) ψ := by
  let σi : TSub tvar Γ.text Γ.text := fun {L'} x => Tm.castK (Cat.sub_var L').symm (Tm.var x)
  have h1 : HEq ((ψ.ren (twkL Γ)).tinst (tvar fz)) (ψ.sub σi) := by
    refine Tm.sub_ren_heq ψ _ rfl _ σi (fin_cases rfl (fun _ => rfl)) ?_
    intro L' x
    cases x with
    | tthere y => exact (tsub_varCast_heq _ _ _).trans ((castK_heq _ _).trans (castK_heq _ _).symm)
  exact h1.trans (Tm.sub_id_heq ψ rfl σi (fun _ => rfl) (fun _ => (castK_heq _ _).symm)).symm

theorem subst0_cons_heq {n m : Nat} {s : Fin n → Ty m} {Γ : Ctx n} {Δ : Ctx m} (σs : TSub s Γ Δ) {σ : Ty n}
    {L : Cat n} (b : Tm (.ext Γ σ) L) (N : Tm Δ (σ.1.sub s)) :
    HEq ((b.sub (σs.lift σ)).subst0 N) (b.sub (σs.cons N)) := by
  refine (castK_heq _ _).trans (Tm.sub_sub_heq b (σs.lift σ) rfl (sub0 N) (σs.cons N) (fun i => Cat.sub_var _) ?_)
  intro L' x
  cases x with
  | here => exact castK_heq _ _
  | there y => exact wk_subst0_heq (τ := σ.sub s) (σs y) N

/-- Extending a substitution by a type for the last type variable. -/
def _root_.PIF.TSub.tcons {n m : Nat} {s : Fin n → Ty m} {Γ : Ctx n} {Δ : Ctx m} (σs : TSub s Γ Δ) (τ : Ty m) :
    TSub (scons τ s) Γ.text Δ := fun {_} x =>
  match x with
  | .tthere (K := L') y => Tm.castK (Cat.sub_ren_congr (r := fs) (s := scons τ s) (s' := s) L' (fun _ => rfl)).symm (σs y)

theorem tinst_tcons_heq {n m : Nat} {s : Fin n → Ty m} {Γ : Ctx n} {Δ : Ctx m} (σs : TSub s Γ Δ)
    {K : Cat (n+1)} (b : Tm Γ.text K) (τ : Ty m) :
    HEq ((b.sub (TSub.tlift σs)).tinst τ) (b.sub (TSub.tcons σs τ)) := by
  refine Tm.sub_sub_heq b (TSub.tlift σs) rfl (tsub0 Δ τ) (TSub.tcons σs τ) (fin_cases rfl (fun i => Cat.ren_fs_inst _ _)) ?_
  intro L' x
  cases x with
  | tthere y => exact (sub_castK_heq _ _ _).trans ((twk_tinst_heq τ (σs y)).trans (castK_heq _ _).symm)

section Derivs
variable {Ax : Fm Ctx.nil → Prop} {n : Nat} {Γ : Ctx n}

theorem prov_notAll (τ : Ty n) (ψ : Fm (Γ.ext τ)) : Prov Ax Γ ((Tm.all τ ψ).neg.imp (Tm.ex τ ψ.neg)) := by
  have c1 : ((ψ.neg).ren (wkL (Γ := Γ) τ)).subst0 (Tm.castK (Cat.ren_id τ.1).symm (Tm.var .here)) = ψ.neg :=
    eq_of_heq (contract_heq τ ψ.neg)
  refine Ent.toProv (Ent.intro (Ent.byContra (B := Tm.all τ ψ) (Ent.gen τ ?_) (Ent.weaken Ent.last)))
  refine Ent.byContra (B := (Tm.ex τ ψ.neg).wk τ) ?_ ?_
  · refine Ent.exI (σ := τ.ren (fun i => i)) (φ := (ψ.neg).ren (wkL (Γ := Γ) τ))
      (Tm.castK (Cat.ren_id τ.1).symm (Tm.var .here)) ?_
    exact (congrArg (Ent Ax _ _) c1).mpr Ent.last
  · exact Ent.weaken (Ent.hyp _ 1 (by simp))

theorem prov_notTAll (ψ : Fm Γ.text) : Prov Ax Γ ((Tm.tall ψ).neg.imp (Tm.tex ψ.neg)) := by
  have c1 : ((ψ.neg).ren (twkL Γ)).tinst (tvar fz) = ψ.neg := eq_of_heq (tcontract_heq ψ.neg)
  refine Ent.toProv (Ent.intro (Ent.byContra (B := Tm.tall ψ) (Ent.tgen ?_) (Ent.weaken Ent.last)))
  refine Ent.byContra (B := (Tm.tex ψ.neg).twk) ?_ ?_
  · refine Ent.texI (φ := (ψ.neg).ren (twkL Γ)) (tvar fz) ?_
    exact (congrArg (Ent Ax _ _) c1).mpr Ent.last
  · exact Ent.weaken (Ent.hyp _ 1 (by exact Nat.one_lt_two))

end Derivs


/-! ## Witnesses -/

theorem step_of_task0 (S : St) {K c : Nat} (h : task K = some (0, c)) : step S K = stepEx S c := by
  unfold step; rw [h]; rfl

theorem step_of_task1 (S : St) {K c : Nat} (h : task K = some (1, c)) : step S K = stepTex S c := by
  unfold step; rw [h]; rfl

section Wit
variable {Ax : Fm Ctx.nil → Prop} {n0 : Nat} {Γ0 : Ctx n0} (φ0 : Fm Γ0)

theorem witness_ex_at (K c : Nat) (hK : task K = some (0, c))
    (hex : ∃ p : (σ : Ty (chain n0 Γ0 K).n) × Fm ((chain n0 Γ0 K).Γ.ext σ), codeF (Tm.ex p.1 p.2) = c) :
    ∃ τ' : Ty (chain n0 Γ0 (K + 1)).n, ∃ ψ' : Fm ((chain n0 Γ0 (K + 1)).Γ.ext τ'),
      ∃ w : Tm (chain n0 Γ0 (K + 1)).Γ τ'.1,
      codeF (Tm.ex τ' ψ') = c ∧ E (Ax := Ax) φ0 (K + 1) ((Tm.ex τ' ψ').imp (ψ'.subst0 w)) := by
  have hstep : step (chain n0 Γ0 K) K =
      ⟨⟨_, (chain n0 Γ0 K).Γ.ext (Classical.choose hex).1⟩, liftWk _ (Classical.choose hex).1,
        Tm.imp ((Tm.ex (Classical.choose hex).1 (Classical.choose hex).2).wk (Classical.choose hex).1)
          (Classical.choose hex).2⟩ :=
    (step_of_task0 _ hK).trans (dite_eq_left hex)
  have hp := Classical.choose_spec hex
  generalize Classical.choose hex = p at hstep hp
  obtain ⟨p1, p2⟩ := p
  unfold E
  show ∃ τ' : Ty (step (chain n0 Γ0 K) K).S'.n, ∃ ψ' : Fm ((step (chain n0 Γ0 K) K).S'.Γ.ext τ'),
    ∃ w : Tm (step (chain n0 Γ0 K) K).S'.Γ τ'.1, codeF (Tm.ex τ' ψ') = c ∧
      Ent Ax (step (chain n0 Γ0 K) K).S'.Γ
        (decideStep Ax ((theory Ax φ0 K).map (liftF (step (chain n0 Γ0 K) K).L) ++ [(step (chain n0 Γ0 K) K).W]) (task K))
        ((Tm.ex τ' ψ').imp (ψ'.subst0 w))
  rw [hstep]
  refine ⟨p1.ren (fun i => i), p2.ren (wkL p1), Tm.castK (Cat.ren_id p1.1).symm (Tm.var .here), ?_, ?_⟩
  · exact (codeF_wk p1 (Tm.ex p1 p2)).trans hp
  · obtain ⟨extra, e⟩ := decideStep_ext (Ax := Ax)
      (((theory Ax φ0 K).map (liftF (liftWk (chain n0 Γ0 K) p1))) ++ [Tm.imp ((Tm.ex p1 p2).wk p1) p2]) (task K)
    rw [e]
    have c1 := eq_of_heq (contract_heq p1 p2)
    exact (congrArg (fun χ => Ent Ax _ _ (Tm.imp ((Tm.ex p1 p2).wk p1) χ)) c1).mpr (ent_append Ent.last extra)

/-- Every existential formula gets a witness at a later stage. -/
theorem witness_ex {J : Nat} (τ : Ty (chain n0 Γ0 J).n) (ψ : Fm ((chain n0 Γ0 J).Γ.ext τ)) :
    ∃ J', J ≤ J' ∧ ∃ τ' : Ty (chain n0 Γ0 J').n, ∃ ψ' : Fm ((chain n0 Γ0 J').Γ.ext τ'),
      ∃ w : Tm (chain n0 Γ0 J').Γ τ'.1,
      codeF (Tm.ex τ' ψ') = codeF (Tm.ex τ ψ) ∧ E (Ax := Ax) φ0 J' ((Tm.ex τ' ψ').imp (ψ'.subst0 w)) := by
  have hK : J ≤ pairN 0 (pairN J (codeF (Tm.ex τ ψ))) := Nat.le_trans (le_pairN_left _ _) (le_pairN_right _ _)
  exact ⟨_, Nat.le_succ_of_le hK, witness_ex_at φ0 _ _ (task_pairN 0 J _)
    ⟨⟨τ.ren (liftL n0 Γ0 _ _ hK).r, ψ.ren (TRen.lift (liftL n0 Γ0 _ _ hK).ρ τ)⟩, codeF_up hK (Tm.ex τ ψ)⟩⟩

theorem witness_tex_at (K c : Nat) (hK : task K = some (1, c))
    (hex : ∃ φ : Fm (chain n0 Γ0 K).Γ.text, codeF (Tm.tex φ) = c) :
    ∃ ψ' : Fm (chain n0 Γ0 (K + 1)).Γ.text, ∃ τw : Ty (chain n0 Γ0 (K + 1)).n,
      codeF (Tm.tex ψ') = c ∧ E (Ax := Ax) φ0 (K + 1) ((Tm.tex ψ').imp (ψ'.tinst τw)) := by
  have hstep : step (chain n0 Γ0 K) K =
      ⟨⟨_, (chain n0 Γ0 K).Γ.text⟩, liftTwk _, Tm.imp ((Tm.tex (Classical.choose hex)).twk) (Classical.choose hex)⟩ :=
    (step_of_task1 _ hK).trans (dite_eq_left hex)
  have hp := Classical.choose_spec hex
  generalize Classical.choose hex = p at hstep hp
  unfold E
  show ∃ ψ' : Fm (step (chain n0 Γ0 K) K).S'.Γ.text, ∃ τw : Ty (step (chain n0 Γ0 K) K).S'.n,
      codeF (Tm.tex ψ') = c ∧
      Ent Ax (step (chain n0 Γ0 K) K).S'.Γ
        (decideStep Ax ((theory Ax φ0 K).map (liftF (step (chain n0 Γ0 K) K).L) ++ [(step (chain n0 Γ0 K) K).W]) (task K))
        ((Tm.tex ψ').imp (ψ'.tinst τw))
  rw [hstep]
  refine ⟨p.ren (twkL _), tvar fz, ?_, ?_⟩
  · exact (codeF_twk (Tm.tex p)).trans hp
  · obtain ⟨extra, e⟩ := decideStep_ext (Ax := Ax)
      (((theory Ax φ0 K).map (liftF (liftTwk (chain n0 Γ0 K)))) ++ [Tm.imp ((Tm.tex p).twk) p]) (task K)
    rw [e]
    have c1 := eq_of_heq (tcontract_heq p)
    exact (congrArg (fun χ => Ent Ax _ _ (Tm.imp ((Tm.tex p).twk) χ)) c1).mpr (ent_append Ent.last extra)

/-- Every type-existential formula gets a witness at a later stage. -/
theorem witness_tex {J : Nat} (ψ : Fm (chain n0 Γ0 J).Γ.text) :
    ∃ J', J ≤ J' ∧ ∃ ψ' : Fm (chain n0 Γ0 J').Γ.text, ∃ τw : Ty (chain n0 Γ0 J').n,
      codeF (Tm.tex ψ') = codeF (Tm.tex ψ) ∧ E (Ax := Ax) φ0 J' ((Tm.tex ψ').imp (ψ'.tinst τw)) := by
  have hK : J ≤ pairN 1 (pairN J (codeF (Tm.tex ψ))) := Nat.le_trans (le_pairN_left _ _) (le_pairN_right _ _)
  exact ⟨_, Nat.le_succ_of_le hK, witness_tex_at φ0 _ _ (task_pairN 1 J _)
    ⟨ψ.ren (TRen.tlift (liftL n0 Γ0 _ _ hK).ρ), codeF_up hK (Tm.tex ψ)⟩⟩

end Wit

end Compl
end PIF
