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


/-! ## The canonical structure -/

section Canon
variable {n0 : Nat} (Γ0 : Ctx n0)

/-- `c` is the code of a type at stage `J`. -/
def TyAt (J : Nat) (c : List Nat) : Prop := ∃ σ : Ty (chain n0 Γ0 J).n, codeCat 0 σ.1 = c

/-- `m` is the code of a term at stage `J` whose type has code `c`. -/
def TmAt (J : Nat) (c m : List Nat) : Prop :=
  ∃ σ : Ty (chain n0 Γ0 J).n, ∃ M : Tm (chain n0 Γ0 J).Γ σ.1, codeCat 0 σ.1 = c ∧ codeTm 0 0 M = m

/-- `m` and `m'` are the codes of β-equivalent terms at stage `J`. -/
def RelAt (J : Nat) (m m' : List Nat) : Prop :=
  ∃ σ : Ty (chain n0 Γ0 J).n, ∃ M M' : Tm (chain n0 Γ0 J).Γ σ.1,
    codeTm 0 0 M = m ∧ codeTm 0 0 M' = m' ∧ BetaEq M M'

variable {Γ0}

theorem tyAt_mono {J J' : Nat} (h : J ≤ J') {c : List Nat} : TyAt Γ0 J c → TyAt Γ0 J' c
  | ⟨σ, hc⟩ => ⟨σ.ren (liftL n0 Γ0 J J' h).r, ((liftL n0 Γ0 J J' h).codeC σ.1).trans hc⟩

theorem tmAt_mono {J J' : Nat} (h : J ≤ J') {c m : List Nat} : TmAt Γ0 J c m → TmAt Γ0 J' c m
  | ⟨σ, M, hc, hm⟩ => ⟨σ.ren (liftL n0 Γ0 J J' h).r, M.ren (liftL n0 Γ0 J J' h).ρ,
      ((liftL n0 Γ0 J J' h).codeC σ.1).trans hc, ((liftL n0 Γ0 J J' h).codeT M).trans hm⟩

theorem relAt_mono {J J' : Nat} (h : J ≤ J') {m m' : List Nat} : RelAt Γ0 J m m' → RelAt Γ0 J' m m'
  | ⟨σ, M, M', h1, h2, hb⟩ => ⟨σ.ren (liftL n0 Γ0 J J' h).r, M.ren (liftL n0 Γ0 J J' h).ρ,
      M'.ren (liftL n0 Γ0 J J' h).ρ, ((liftL n0 Γ0 J J' h).codeT M).trans h1,
      ((liftL n0 Γ0 J J' h).codeT M').trans h2, BetaEq.ren hb _⟩

theorem cat_unique {n : Nat} {K K' : Cat n} (h : codeCat 0 K = codeCat 0 K') : K = K' :=
  (codeCat_inj K K' 0 [] [] (by rw [List.append_nil, List.append_nil]; exact h)).1

theorem tm_unique {n : Nat} {Γ : Ctx n} {K K' : Cat n} {M : Tm Γ K} {M' : Tm Γ K'}
    (h : codeTm 0 0 M = codeTm 0 0 M') : K = K' ∧ HEq M M' := by
  have := codeTm_inj M M' 0 0 [] [] (by rw [List.append_nil, List.append_nil]; exact h)
  exact ⟨this.1, this.2.1⟩

variable (Γ0)

/-- Codes of terms of the type with code `c`. -/
def Rep (c : List Nat) : Type := {m : List Nat // ∃ J, TmAt Γ0 J c m}

/-- β-equivalence at some stage. -/
def Rel (m m' : List Nat) : Prop := ∃ J, RelAt Γ0 J m m'

variable {Γ0}

theorem rel_refl {c : List Nat} (a : Rep Γ0 c) : Rel Γ0 a.1 a.1 := by
  obtain ⟨J, σ, M, _, hm⟩ := a.2
  exact ⟨J, σ, M, M, hm, hm, .refl M⟩

theorem rel_symm {m m' : List Nat} : Rel Γ0 m m' → Rel Γ0 m' m
  | ⟨J, σ, M, M', h1, h2, hb⟩ => ⟨J, σ, M', M, h2, h1, hb.symm⟩

theorem rel_trans {m m' m'' : List Nat} : Rel Γ0 m m' → Rel Γ0 m' m'' → Rel Γ0 m m'' := by
  rintro ⟨J1, r1⟩ ⟨J2, r2⟩
  obtain ⟨σ1, M1, M1', a1, b1, e1⟩ := relAt_mono (Nat.le_max_left J1 J2) r1
  obtain ⟨σ2, M2, M2', a2, b2, e2⟩ := relAt_mono (Nat.le_max_right J1 J2) r2
  obtain ⟨hK, hM⟩ := tm_unique (b1.trans a2.symm)
  have hσ : σ1 = σ2 := Subtype.ext hK
  subst hσ
  cases hM
  exact ⟨_, σ1, M1, M2', a1, b2, e1.trans e2⟩

variable (Γ0)

def repSetoid (c : List Nat) : Setoid (Rep Γ0 c) :=
  ⟨fun a b => Rel Γ0 a.1 b.1, ⟨rel_refl, rel_symm, rel_trans⟩⟩

/-- The types: codes of types at some stage. -/
def CT : Type := {c : List Nat // ∃ J, TyAt Γ0 J c}

def ctE : CT Γ0 := ⟨[0], 0, ⟨Cat.e, trivial⟩, rfl⟩
def ctT : CT Γ0 := ⟨[1], 0, ⟨Cat.t, trivial⟩, rfl⟩

theorem arr_ok (A B : CT Γ0) : ∃ J, TyAt Γ0 J (4 :: (A.1 ++ B.1)) := by
  obtain ⟨J1, h1⟩ := A.2
  obtain ⟨J2, h2⟩ := B.2
  obtain ⟨σ, hσ⟩ := tyAt_mono (Nat.le_max_left J1 J2) h1
  obtain ⟨τ, hτ⟩ := tyAt_mono (Nat.le_max_right J1 J2) h2
  exact ⟨_, ⟨.arr σ.1 τ.1, σ.2, τ.2⟩, by show 4 :: (codeCat 0 σ.1 ++ codeCat 0 τ.1) = _; rw [hσ, hτ]⟩

def ctArr (A B : CT Γ0) : CT Γ0 := ⟨4 :: (A.1 ++ B.1), arr_ok Γ0 A B⟩

/-- The items of a type: codes of terms of that type, modulo β-conversion. -/
def CD (A : CT Γ0) : Type := Quotient (repSetoid Γ0 A.1)

/-- The item named by a term. -/
noncomputable def mkD {J : Nat} (σ : Ty (chain n0 Γ0 J).n) (M : Tm (chain n0 Γ0 J).Γ σ.1) (A : CT Γ0)
    (h : codeCat 0 σ.1 = A.1) : CD Γ0 A :=
  Quotient.mk _ ⟨codeTm 0 0 M, J, σ, M, h, rfl⟩

variable {Γ0}

theorem mkD_eq {J J' : Nat} {σ : Ty (chain n0 Γ0 J).n} {M : Tm (chain n0 Γ0 J).Γ σ.1}
    {σ' : Ty (chain n0 Γ0 J').n} {M' : Tm (chain n0 Γ0 J').Γ σ'.1} {A : CT Γ0} {h : codeCat 0 σ.1 = A.1}
    {h' : codeCat 0 σ'.1 = A.1} (e : codeTm 0 0 M = codeTm 0 0 M') : mkD Γ0 σ M A h = mkD Γ0 σ' M' A h' := by
  unfold mkD; congr 1; exact Subtype.ext e

theorem mkD_heq {J J' : Nat} {σ : Ty (chain n0 Γ0 J).n} {M : Tm (chain n0 Γ0 J).Γ σ.1}
    {σ' : Ty (chain n0 Γ0 J').n} {M' : Tm (chain n0 Γ0 J').Γ σ'.1} {A A' : CT Γ0} {h : codeCat 0 σ.1 = A.1}
    {h' : codeCat 0 σ'.1 = A'.1} (eA : A = A') (e : codeTm 0 0 M = codeTm 0 0 M') :
    HEq (mkD Γ0 σ M A h) (mkD Γ0 σ' M' A' h') := by
  subst eA; exact heq_of_eq (mkD_eq e)

theorem mkD_surj {A : CT Γ0} (x : CD Γ0 A) : ∃ J, ∃ σ : Ty (chain n0 Γ0 J).n, ∃ M : Tm (chain n0 Γ0 J).Γ σ.1,
    ∃ h : codeCat 0 σ.1 = A.1, x = mkD Γ0 σ M A h := by
  induction x using Quotient.ind with
  | _ a =>
    obtain ⟨m, J, σ, M, h, hm⟩ := a
    exact ⟨J, σ, M, h, by unfold mkD; congr 1; exact Subtype.ext hm.symm⟩

theorem mkD_exact {J J' : Nat} {σ : Ty (chain n0 Γ0 J).n} {M : Tm (chain n0 Γ0 J).Γ σ.1}
    {σ' : Ty (chain n0 Γ0 J').n} {M' : Tm (chain n0 Γ0 J').Γ σ'.1} {A : CT Γ0} {h : codeCat 0 σ.1 = A.1}
    {h' : codeCat 0 σ'.1 = A.1} (e : mkD Γ0 σ M A h = mkD Γ0 σ' M' A h') : Rel Γ0 (codeTm 0 0 M) (codeTm 0 0 M') :=
  Quotient.exact e

theorem mkD_sound {J : Nat} {σ : Ty (chain n0 Γ0 J).n} {M M' : Tm (chain n0 Γ0 J).Γ σ.1} {A : CT Γ0}
    {h h' : codeCat 0 σ.1 = A.1} (hb : BetaEq M M') : mkD Γ0 σ M A h = mkD Γ0 σ M' A h' :=
  Quotient.sound ⟨J, σ, M, M', rfl, rfl, hb⟩

/-! ### Application -/

theorem app_at {J : Nat} {A B : CT Γ0} {f a : List Nat} (hf : TmAt Γ0 J (4 :: (A.1 ++ B.1)) f)
    (ha : TmAt Γ0 J A.1 a) (hB : TyAt Γ0 J B.1) : TmAt Γ0 J B.1 (3 :: (f ++ a)) := by
  obtain ⟨σf, F, hcf, hF⟩ := hf
  obtain ⟨σa, X, hca, hX⟩ := ha
  obtain ⟨τ, hτ⟩ := hB
  have e : σf.1 = Cat.arr σa.1 τ.1 :=
    cat_unique (by rw [hcf]; show _ = 4 :: (codeCat 0 σa.1 ++ codeCat 0 τ.1); rw [hca, hτ])
  exact ⟨τ, Tm.app (Tm.castK e F) X, hτ, by
    show 3 :: (codeTm 0 0 (Tm.castK e F) ++ codeTm 0 0 X) = _; rw [codeTm_castK, hF, hX]⟩

variable (Γ0)

def appRep {A B : CT Γ0} (f : Rep Γ0 (ctArr Γ0 A B).1) (a : Rep Γ0 A.1) : Rep Γ0 B.1 :=
  ⟨3 :: (f.1 ++ a.1), by
    obtain ⟨J1, h1⟩ := f.2
    obtain ⟨J2, h2⟩ := a.2
    obtain ⟨J3, h3⟩ := B.2
    exact ⟨J1 + J2 + J3, app_at (tmAt_mono (by omega) h1) (tmAt_mono (by omega) h2) (tyAt_mono (by omega) h3)⟩⟩

variable {Γ0}

theorem app_rel {A B : CT Γ0} (f f' : Rep Γ0 (ctArr Γ0 A B).1) (a a' : Rep Γ0 A.1) (hf : Rel Γ0 f.1 f'.1)
    (ha : Rel Γ0 a.1 a'.1) : Rel Γ0 (appRep Γ0 f a).1 (appRep Γ0 f' a').1 := by
  obtain ⟨J1, h1⟩ := f.2
  obtain ⟨J2, h2⟩ := a.2
  obtain ⟨J3, h3⟩ := B.2
  obtain ⟨J4, h4⟩ := hf
  obtain ⟨J5, h5⟩ := ha
  obtain ⟨σf, F0, hcf, hF0⟩ := tmAt_mono (J' := J1 + J2 + J3 + J4 + J5) (by omega) h1
  obtain ⟨σa, X0, hca, hX0⟩ := tmAt_mono (J' := J1 + J2 + J3 + J4 + J5) (by omega) h2
  obtain ⟨τ, hτ⟩ := tyAt_mono (J' := J1 + J2 + J3 + J4 + J5) (by omega) h3
  obtain ⟨σ1, F, F', c1, c1', bF⟩ := relAt_mono (J' := J1 + J2 + J3 + J4 + J5) (by omega) h4
  obtain ⟨σ2, X, X', d1, d1', bX⟩ := relAt_mono (J' := J1 + J2 + J3 + J4 + J5) (by omega) h5
  have e1 : σ1.1 = σf.1 := (tm_unique (c1.trans hF0.symm)).1
  have e2 : σ2.1 = σa.1 := (tm_unique (d1.trans hX0.symm)).1
  have e : σ1.1 = Cat.arr σ2.1 τ.1 :=
    cat_unique (by rw [e1, hcf, e2]; show 4 :: (A.1 ++ B.1) = 4 :: (codeCat 0 σa.1 ++ codeCat 0 τ.1); rw [hca, hτ])
  refine ⟨_, τ, Tm.app (Tm.castK e F) X, Tm.app (Tm.castK e F') X', ?_, ?_,
    BetaEq.app2' (BetaEq.castKC e bF) bX⟩
  · show 3 :: (codeTm 0 0 (Tm.castK e F) ++ codeTm 0 0 X) = _; rw [codeTm_castK, c1, d1]; rfl
  · show 3 :: (codeTm 0 0 (Tm.castK e F') ++ codeTm 0 0 X') = _; rw [codeTm_castK, c1', d1']; rfl

end Canon


/-! ## The canonical model -/

section Model
variable {Ax : Fm Ctx.nil → Prop} {n0 : Nat} {Γ0 : Ctx n0} (φ0 : Fm Γ0)

theorem trL_beta {J : Nat} {φ φ' : Fm (chain n0 Γ0 J).Γ} (hb : BetaEq φ φ') (h : TrL Ax φ0 (codeTm 0 0 φ)) :
    TrL Ax φ0 (codeTm 0 0 φ') := by
  obtain ⟨J', hJ, e⟩ := (trL_iff φ).1 h
  exact (trL_iff φ').2 ⟨J', hJ, Ent.beta e (BetaEq.ren hb _)⟩

theorem trL_rel {m m' : List Nat} (hm : ∃ J, TmAt Γ0 J [1] m) (h : Rel Γ0 m m') (ht : TrL Ax φ0 m) :
    TrL Ax φ0 m' := by
  obtain ⟨J1, h1⟩ := hm
  obtain ⟨J2, r⟩ := h
  obtain ⟨σa, Ma, hca, hma⟩ := tmAt_mono (Nat.le_max_left J1 J2) h1
  obtain ⟨σ, M, M', e1, e2, hb⟩ := relAt_mono (Nat.le_max_right J1 J2) r
  have e : σ.1 = Cat.t := by rw [(tm_unique (e1.trans hma.symm)).1]; exact cat_unique hca
  have := trL_beta φ0 (BetaEq.castKC e hb) (by rw [codeTm_castK, e1]; exact ht)
  rwa [codeTm_castK, e2] at this

variable (Ax)

/-- The truth valuation: truth in the limit. -/
noncomputable def VV : CD Γ0 (ctT Γ0) → Prop :=
  Quotient.lift (fun a => TrL Ax φ0 a.1)
    (fun a b hab => propext ⟨trL_rel φ0 a.2 hab, trL_rel φ0 b.2 (rel_symm hab)⟩)

include Ax φ0 in
theorem ne_ok (A : CT Γ0) : Nonempty (CD Γ0 A) := by
  obtain ⟨J, σ, hc⟩ := A.2
  obtain ⟨J', hJ, τ', ψ', w, hcode, _⟩ := witness_ex (Ax := Ax) φ0 σ topF
  have h1 : Tm.ex τ' ψ' = Tm.ex (σ.ren (liftL n0 Γ0 J J' hJ).r) (Tm.ren (TRen.lift (liftL n0 Γ0 J J' hJ).ρ σ) topF) :=
    codeF_inj _ _ (hcode.trans (codeF_up hJ (Tm.ex σ topF)).symm)
  have h2 := (ex_inj h1).1
  exact ⟨mkD Γ0 τ' w A (by rw [h2]; exact ((liftL n0 Γ0 J J' hJ).codeC σ.1).trans hc)⟩

/-- The canonical structure. -/
noncomputable def CS : Gen.Struct where
  T := CT Γ0
  eT := ctE Γ0
  tT := ctT Γ0
  arr := ctArr Γ0
  D := CD Γ0
  ne := ne_ok Ax φ0
  app := fun f a => Quotient.lift₂ (fun f a => Quotient.mk _ (appRep Γ0 f a))
    (fun _ _ _ _ hf ha => Quotient.sound (app_rel _ _ _ _ hf ha)) f a
  V := VV Ax φ0

variable {Ax}

theorem tc_code {J : Nat} {n : Nat} {s : Fin n → Ty (chain n0 Γ0 J).n} {ρ : Fin n → CT Γ0}
    (hs : ∀ i, codeCat 0 (s i).1 = (ρ i).1) : ∀ (L : Cat n), L.Simple → codeCat 0 (L.sub s) = ((CS Ax φ0).tc L ρ).1
  | .e, _ => rfl
  | .t, _ => rfl
  | .var i, _ => hs i
  | .arr a b, h => by
    have h1 := tc_code hs a h.1
    have h2 := tc_code hs b h.2
    show 4 :: (codeCat 0 (a.sub s) ++ codeCat 0 (b.sub s)) = 4 :: (((CS Ax φ0).tc a ρ).1 ++ ((CS Ax φ0).tc b ρ).1)
    rw [h1, h2]
  | .pi _, h => h.elim

/-- A stage and a substitution into it which match a valuation. -/
structure CData {n : Nat} (Γ : Ctx n) (ρ : Fin n → CT Γ0) (env : (CS Ax φ0).Env Γ ρ) where
  J : Nat
  s : Fin n → Ty (chain n0 Γ0 J).n
  σs : TSub s Γ (chain n0 Γ0 J).Γ
  hs : ∀ i, codeCat 0 (s i).1 = (ρ i).1
  hx : ∀ {L : Cat n} (x : Var Γ L), mkD Γ0 ⟨L.sub s, Cat.Simple_sub s (Gen.var_simple x)⟩ (σs x) ((CS Ax φ0).tc L ρ)
      (tc_code φ0 hs L (Gen.var_simple x)) = (CS Ax φ0).lookup x ρ env

variable {φ0}

/-- Moving matching data to a later stage. -/
noncomputable def CData.lift {n : Nat} {Γ : Ctx n} {ρ : Fin n → CT Γ0} {env : (CS Ax φ0).Env Γ ρ}
    (d : CData φ0 Γ ρ env) (J' : Nat) (h : d.J ≤ J') : CData φ0 Γ ρ env where
  J := J'
  s := fun i => (d.s i).ren (liftL n0 Γ0 d.J J' h).r
  σs := fun {L} x => Tm.castK (Cat.ren_sub L d.s _) ((d.σs x).ren (liftL n0 Γ0 d.J J' h).ρ)
  hs := fun i => ((liftL n0 Γ0 d.J J' h).codeC _).trans (d.hs i)
  hx := fun x => (mkD_eq (by rw [codeTm_castK]; exact (liftL n0 Γ0 d.J J' h).codeT _)).trans (d.hx x)

theorem code_sub_lift {n : Nat} {Γ : Ctx n} {ρ : Fin n → CT Γ0} {env : (CS Ax φ0).Env Γ ρ}
    (d : CData φ0 Γ ρ env) (J' : Nat) (h : d.J ≤ J') {K : Cat n} (M : Tm Γ K) :
    codeTm 0 0 (M.sub (d.lift J' h).σs) = codeTm 0 0 (M.sub d.σs) := by
  have hh : HEq ((M.sub d.σs).ren (liftL n0 Γ0 d.J J' h).ρ) (M.sub (d.lift J' h).σs) :=
    Tm.ren_sub_heq M d.σs rfl (liftL n0 Γ0 d.J J' h).ρ (d.lift J' h).σs (fun _ => rfl)
      (fun _ => (castK_heq _ _).symm)
  exact (codeTm_heq (Cat.ren_sub K d.s _) hh 0 0).symm.trans ((liftL n0 Γ0 d.J J' h).codeT _)

theorem var_bound : ∀ {n : Nat} (Γ : Ctx n) (f : ∀ {L : Cat n}, Var Γ L → Nat), ∃ B, ∀ {L : Cat n} (x : Var Γ L), f x ≤ B
  | _, .nil, _ => ⟨0, fun x => nomatch x⟩
  | _, .ext Γ _, f => by
    obtain ⟨B, hB⟩ := var_bound Γ (fun y => f (.there y))
    refine ⟨max B (f .here), fun x => ?_⟩
    cases x with
    | here => exact Nat.le_max_right _ _
    | there y => exact Nat.le_trans (hB y) (Nat.le_max_left _ _)
  | _, .text Γ, f => by
    obtain ⟨B, hB⟩ := var_bound Γ (fun y => f (.tthere y))
    refine ⟨B, fun x => ?_⟩
    cases x with
    | tthere y => exact hB y

theorem fin_bound : ∀ {n : Nat} (f : Fin n → Nat), ∃ B, ∀ i, f i ≤ B
  | 0, _ => ⟨0, fun i => i.elim0⟩
  | _ + 1, f => by
    obtain ⟨B, hB⟩ := fin_bound (fun i => f (fs i))
    exact ⟨max B (f fz), fin_cases (Nat.le_max_right _ _) (fun i => Nat.le_trans (hB i) (Nat.le_max_left _ _))⟩

theorem beta_of_heq {n : Nat} {Γ : Ctx n} {K K' : Cat n} (e : K = K') {N N' : Tm Γ K} {P P' : Tm Γ K'}
    (q1 : HEq N P) (q2 : HEq N' P') (hb : BetaEq N N') : BetaEq P P' := by
  subst e; cases q1; cases q2; exact hb

theorem relAt_sub {J n : Nat} {Γ : Ctx n} {K : Cat n} (hK : K.Simple) (M : Tm Γ K)
    (s1 s2 : Fin n → Ty (chain n0 Γ0 J).n) (σa : TSub s1 Γ (chain n0 Γ0 J).Γ) (σb : TSub s2 Γ (chain n0 Γ0 J).Γ)
    (hs : ∀ i, s1 i = s2 i) (hx : ∀ {L : Cat n} (x : Var Γ L), RelAt Γ0 J (codeTm 0 0 (σa x)) (codeTm 0 0 (σb x))) :
    RelAt Γ0 J (codeTm 0 0 (M.sub σa)) (codeTm 0 0 (M.sub σb)) := by
  have e : s1 = s2 := funext hs
  subst e
  refine ⟨⟨K.sub s1, Cat.Simple_sub s1 hK⟩, M.sub σa, M.sub σb, rfl, rfl, Tm.sub_betaEq M σa σb (fun x => ?_)⟩
  obtain ⟨σ, N, N', h1, h2, hb⟩ := hx x
  obtain ⟨e1, q1⟩ := tm_unique h1
  obtain ⟨_, q2⟩ := tm_unique h2
  exact beta_of_heq e1 q1 q2 hb

theorem cdata_agree {n : Nat} {Γ : Ctx n} {ρ : Fin n → CT Γ0} {env : (CS Ax φ0).Env Γ ρ}
    (d1 d2 : CData φ0 Γ ρ env) {K : Cat n} (hK : K.Simple) (M : Tm Γ K) :
    Rel Γ0 (codeTm 0 0 (M.sub d1.σs)) (codeTm 0 0 (M.sub d2.σs)) := by
  have hr : ∀ {L : Cat n} (x : Var Γ L), Rel Γ0 (codeTm 0 0 (d1.σs x)) (codeTm 0 0 (d2.σs x)) :=
    fun x => mkD_exact ((d1.hx x).trans (d2.hx x).symm)
  obtain ⟨B, hB⟩ := var_bound Γ (fun x => Classical.choose (hr x))
  have h1 : d1.J ≤ d1.J + d2.J + B := by omega
  have h2 : d2.J ≤ d1.J + d2.J + B := by omega
  refine ⟨d1.J + d2.J + B, ?_⟩
  rw [← code_sub_lift d1 _ h1 M, ← code_sub_lift d2 _ h2 M]
  refine relAt_sub hK M _ _ _ _ (fun i => Subtype.ext (cat_unique ?_)) (fun x => ?_)
  · exact ((d1.lift _ h1).hs i).trans ((d2.lift _ h2).hs i).symm
  · have e1 : codeTm 0 0 ((d1.lift _ h1).σs x) = codeTm 0 0 (d1.σs x) := code_sub_lift d1 _ h1 (Tm.var x)
    have e2 : codeTm 0 0 ((d2.lift _ h2).σs x) = codeTm 0 0 (d2.σs x) := code_sub_lift d2 _ h2 (Tm.var x)
    have := relAt_mono (J' := d1.J + d2.J + B) (by have := hB x; omega) (Classical.choose_spec (hr x))
    rw [← e1, ← e2] at this
    exact this

theorem rep_at {J J' n : Nat} {L : Cat n} (hL : L.Simple) {s : Fin n → Ty (chain n0 Γ0 J).n} {ρ : Fin n → CT Γ0}
    (hs : ∀ i, codeCat 0 (s i).1 = (ρ i).1) (hJ : J' ≤ J) (σ : Ty (chain n0 Γ0 J').n) (M : Tm (chain n0 Γ0 J').Γ σ.1)
    (h : codeCat 0 σ.1 = ((CS Ax φ0).tc L ρ).1) :
    ∃ N : Tm (chain n0 Γ0 J).Γ (L.sub s),
      mkD Γ0 ⟨L.sub s, Cat.Simple_sub s hL⟩ N _ (tc_code φ0 hs L hL) = mkD Γ0 σ M _ h := by
  have e : σ.1.ren (liftL n0 Γ0 J' J hJ).r = L.sub s :=
    cat_unique (((liftL n0 Γ0 J' J hJ).codeC σ.1).trans (h.trans (tc_code φ0 hs L hL).symm))
  exact ⟨Tm.castK e (M.ren (liftL n0 Γ0 J' J hJ).ρ),
    mkD_eq (by rw [codeTm_castK]; exact (liftL n0 Γ0 J' J hJ).codeT M)⟩

theorem cdata_nonempty {n : Nat} (Γ : Ctx n) (ρ : Fin n → CT Γ0) (env : (CS Ax φ0).Env Γ ρ) :
    Nonempty (CData φ0 Γ ρ env) := by
  have hT : ∀ i, ∃ J, TyAt Γ0 J (ρ i).1 := fun i => (ρ i).2
  obtain ⟨Bt, hBt⟩ := fin_bound (fun i => Classical.choose (hT i))
  have hV : ∀ {L : Cat n} (x : Var Γ L), ∃ J, ∃ σ : Ty (chain n0 Γ0 J).n, ∃ M : Tm (chain n0 Γ0 J).Γ σ.1,
      ∃ h : codeCat 0 σ.1 = ((CS Ax φ0).tc L ρ).1, (CS Ax φ0).lookup x ρ env = mkD Γ0 σ M _ h :=
    fun x => mkD_surj _
  obtain ⟨Bv, hBv⟩ := var_bound Γ (fun x => Classical.choose (hV x))
  have hs0 : ∀ i, TyAt Γ0 (Bt + Bv) (ρ i).1 :=
    fun i => tyAt_mono (by have := hBt i; omega) (Classical.choose_spec (hT i))
  have hs : ∀ i, codeCat 0 (Classical.choose (hs0 i)).1 = (ρ i).1 := fun i => Classical.choose_spec (hs0 i)
  have hvar : ∀ {L : Cat n} (x : Var Γ L), ∃ N : Tm (chain n0 Γ0 (Bt + Bv)).Γ (L.sub (fun i => Classical.choose (hs0 i))),
      mkD Γ0 ⟨L.sub _, Cat.Simple_sub _ (Gen.var_simple x)⟩ N _ (tc_code φ0 hs L (Gen.var_simple x)) =
        (CS Ax φ0).lookup x ρ env := by
    intro L x
    obtain ⟨σx, Mx, hcx, ex⟩ := Classical.choose_spec (hV x)
    obtain ⟨N, hN⟩ := rep_at (Gen.var_simple x) hs (by have := hBv x; omega) σx Mx hcx
    exact ⟨N, hN.trans ex.symm⟩
  exact ⟨⟨Bt + Bv, fun i => Classical.choose (hs0 i), fun x => Classical.choose (hvar x), hs,
    fun x => Classical.choose_spec (hvar x)⟩⟩

variable (φ0)

/-- The canonical evaluation. -/
noncomputable def cev {n : Nat} {Γ : Ctx n} {K : Cat n} (hK : K.Simple) (M : Tm Γ K) (ρ : Fin n → CT Γ0)
    (env : (CS Ax φ0).Env Γ ρ) : (CS Ax φ0).D ((CS Ax φ0).tc K ρ) :=
  mkD Γ0 ⟨K.sub (Classical.choice (cdata_nonempty Γ ρ env)).s, Cat.Simple_sub _ hK⟩
    (M.sub (Classical.choice (cdata_nonempty Γ ρ env)).σs) _ (tc_code φ0 (Classical.choice (cdata_nonempty Γ ρ env)).hs K hK)

variable {φ0}

/-- **The evaluation lemma**: any matching data computes the evaluation. -/
theorem cev_eq {n : Nat} {Γ : Ctx n} {K : Cat n} (hK : K.Simple) (M : Tm Γ K) {ρ : Fin n → CT Γ0}
    {env : (CS Ax φ0).Env Γ ρ} (d : CData φ0 Γ ρ env) :
    cev φ0 hK M ρ env = mkD Γ0 ⟨K.sub d.s, Cat.Simple_sub _ hK⟩ (M.sub d.σs) _ (tc_code φ0 d.hs K hK) := by
  unfold cev mkD
  exact Quotient.sound (cdata_agree _ d hK M)

end Model

end Compl
end PIF
