import PIGeneral
import PIEnum

/-!
# Completeness for general models

If a formula is valid in every general model of PI⁻ + `Ax`, then PI⁻ + `Ax` proves it. The proof is
a Henkin construction. Starting from the context of the formula, a chain of contexts is built, each
extending the last by one fresh variable: a fresh item variable or type variable serves as a witness
for an existential formula, and a theory is built alongside, deciding every formula and containing a
witness axiom for each fresh variable. Formulas are compared across the chain by their codes, which
do not change as the context grows. The canonical general model has the type codes as its types, and
codes of terms, up to β-conversion, as its items.
-/
set_option autoImplicit false

namespace PIF
namespace Compl
open Derive

/-! ## Contexts in the chain -/

structure St where
  n : Nat
  Γ : Ctx n

/-- A one-step extension of a context, preserving codes. -/
structure Lift (S S' : St) where
  r : Fin S.n → Fin S'.n
  ρ : TRen r S.Γ S'.Γ
  codeT : ∀ {K : Cat S.n} (M : Tm S.Γ K), codeTm 0 0 (M.ren ρ) = codeTm 0 0 M
  codeC : ∀ (K : Cat S.n), codeCat 0 (K.ren r) = codeCat 0 K

def liftWk (S : St) (σ : Ty S.n) : Lift S ⟨S.n, S.Γ.ext σ⟩ :=
  ⟨fun i => i, wkRen σ, fun M => codeTm_ren M (InsAt_wk σ) InsT_id, fun K => codeCat_ren K InsT_id⟩

def liftTwk (S : St) : Lift S ⟨S.n + 1, S.Γ.text⟩ :=
  ⟨fs, twkRen S.Γ, fun M => codeTm_ren M (InsAt_twk S.Γ) InsT_fs, fun K => codeCat_ren K InsT_fs⟩

/-- A formula, lifted along an extension. -/
def liftF {S S' : St} (L : Lift S S') (φ : Fm S.Γ) : Fm S'.Γ := φ.ren L.ρ

structure StepRes (S : St) where
  S' : St
  L : Lift S S'
  W : Fm S'.Γ

def pairN (a b : Nat) : Nat := encL [a, b]

theorem pairN_inj {a b c d : Nat} (h : pairN a b = pairN c d) : a = c ∧ b = d := by
  have := encL_inj _ _ h
  simp at this
  exact this

theorem le_pairN_left (a b : Nat) : a ≤ pairN a b := by
  have h1 : a < 2 ^ a := Nat.lt_two_pow_self
  have h2 : 1 ≤ 2 * encL [b] + 1 := Nat.succ_pos _
  show a ≤ 2 ^ a * (2 * encL [b] + 1)
  have := Nat.mul_le_mul_left (2 ^ a) h2
  omega

theorem le_pairN_right (a b : Nat) : b ≤ pairN a b := by
  have h1 : b < 2 ^ b := Nat.lt_two_pow_self
  show b ≤ 2 ^ a * (2 * (2 ^ b * (2 * 0 + 1)) + 1)
  have h2 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have := Nat.mul_le_mul_right (2 * (2 ^ b * (2 * 0 + 1)) + 1) h2
  omega

/-- The task performed at step `k`: a kind (`0`: item witness, `1`: type witness, `2`: decision) and a code. -/
noncomputable def task (k : Nat) : Option (Nat × Nat) :=
  open Classical in
  if h : ∃ p : Nat × Nat × Nat, pairN p.1 (pairN p.2.1 p.2.2) = k then
    some ((Classical.choose h).1, (Classical.choose h).2.2)
  else none

theorem task_pairN (t j c : Nat) : task (pairN t (pairN j c)) = some (t, c) := by
  unfold task
  split
  · next h =>
    have hs := Classical.choose_spec h
    obtain ⟨e1, e2⟩ := pairN_inj hs
    obtain ⟨_, e3⟩ := pairN_inj e2
    rw [e1, e3]
  · next h => exact absurd ⟨(t, j, c), rfl⟩ h

noncomputable def stepEx (S : St) (c : Nat) : StepRes S :=
  open Classical in
  if h : ∃ p : (σ : Ty S.n) × Fm (S.Γ.ext σ), codeF (Tm.ex p.1 p.2) = c then
    ⟨_, liftWk S (Classical.choose h).1,
      Tm.imp ((Tm.ex (Classical.choose h).1 (Classical.choose h).2).wk (Classical.choose h).1) (Classical.choose h).2⟩
  else ⟨_, liftWk S tyT, topF⟩

noncomputable def stepTex (S : St) (c : Nat) : StepRes S :=
  open Classical in
  if h : ∃ φ : Fm S.Γ.text, codeF (Tm.tex φ) = c then
    ⟨_, liftTwk S, Tm.imp ((Tm.tex (Classical.choose h)).twk) (Classical.choose h)⟩
  else ⟨_, liftTwk S, topF⟩

def stepDummy (S : St) : StepRes S := ⟨_, liftWk S tyT, topF⟩

noncomputable def step (S : St) (k : Nat) : StepRes S :=
  match task k with
  | some (0, c) => stepEx S c
  | some (1, c) => stepTex S c
  | _ => stepDummy S

theorem step_cases (S : St) (k : Nat) :
    (∃ c, step S k = stepEx S c) ∨ (∃ c, step S k = stepTex S c) ∨ step S k = stepDummy S := by
  unfold step
  split
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact Or.inr (Or.inr rfl)

section Chain
variable (n0 : Nat) (Γ0 : Ctx n0)

noncomputable def chain : Nat → St
  | 0 => ⟨n0, Γ0⟩
  | k + 1 => (step (chain k) k).S'

end Chain


/-! ## The theory -/

section Theory
variable (Ax : Fm Ctx.nil → Prop)

/-- A list of formulas is consistent when it does not derive `⊥`. -/
def Cons {n : Nat} {Γ : Ctx n} (H : List (Fm Γ)) : Prop := ¬ Ent Ax Γ H botF

variable {Ax}

theorem cons_top {n : Nat} {Γ : Ctx n} {H : List (Fm Γ)} (hH : Cons Ax H) : Cons Ax (H ++ [topF]) :=
  fun h => hH (Ent.mp (Ent.intro h) Ent.top)

theorem cons_decide {n : Nat} {Γ : Ctx n} {H : List (Fm Γ)} (hH : Cons Ax H) (ψ : Fm Γ) :
    Cons Ax (H ++ [ψ]) ∨ Cons Ax (H ++ [ψ.neg]) := by
  refine Classical.byContradiction fun hn => ?_
  have h1 : Ent Ax Γ H (ψ.imp botF) := Ent.intro (Classical.byContradiction fun h => hn (Or.inl h))
  have h2 : Ent Ax Γ H (ψ.neg.imp botF) := Ent.intro (Classical.byContradiction fun h => hn (Or.inr h))
  exact hH (Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.atom 1)) (.imp (.imp (.neg (.atom 0)) (.atom 1)) (.atom 1)))
    (v2 ψ botF) (fun _ f g => Classical.byCases f g)) h1 h2)

theorem cons_wk {n : Nat} {Γ : Ctx n} {H : List (Fm Γ)} (hH : Cons Ax H) (σ : Ty n) :
    Cons Ax (H.map (fun h => h.wk σ)) :=
  fun h => hH (Ent.strengthen σ (φ := botF) h)

theorem cons_twk {n : Nat} {Γ : Ctx n} {H : List (Fm Γ)} (hH : Cons Ax H) :
    Cons Ax (H.map (fun h => (h.twk : Fm (.text Γ)))) :=
  fun h => hH (Ent.tstrengthen (φ := botF) h)

/-- From `(A → φ) → ⊥`, both `A` and `¬φ`. -/
theorem split_wit {n : Nat} {Γ : Ctx n} {H : List (Fm Γ)} {A φ : Fm Γ} (h : Ent Ax Γ H ((A.imp φ).imp botF)) :
    Ent Ax Γ H A ∧ Ent Ax Γ H φ.neg := by
  have ht : Ent Ax Γ H (botF : Fm Γ).neg := Ent.top
  refine ⟨Ent.mp2 (Ent.taut (.imp (.imp (.imp (.atom 0) (.atom 1)) (.atom 2)) (.imp (.neg (.atom 2)) (.atom 0)))
    (v3 A φ botF) (fun _ f g => Classical.byContradiction fun na => g (f fun a => (na a).elim))) h ht,
    Ent.mp2 (Ent.taut (.imp (.imp (.imp (.atom 0) (.atom 1)) (.atom 2)) (.imp (.neg (.atom 2)) (.neg (.atom 1))))
    (v3 A φ botF) (fun _ f g b => g (f fun _ => b))) h ht⟩

theorem cons_witEx {n : Nat} {Γ : Ctx n} {H : List (Fm Γ)} (hH : Cons Ax H) (σ : Ty n) (φ : Fm (.ext Γ σ)) :
    Cons Ax (H.map (fun h => h.wk σ) ++ [Tm.imp ((Tm.ex σ φ).wk σ) φ]) := by
  intro h
  obtain ⟨hA, hn⟩ := split_wit (Ent.intro h)
  have hall : Ent Ax Γ H (Tm.all σ φ.neg) := Ent.gen σ hn
  have hex : Ent Ax Γ H (Tm.ex σ φ) := Ent.strengthen σ hA
  have hd : Ent Ax Γ H (Tm.all σ φ.neg).neg := Ent.iffMp (Ent.ofProv (Prov.dualEx σ φ)) hex
  exact hH (Ent.absurd hall hd)

theorem cons_witTex {n : Nat} {Γ : Ctx n} {H : List (Fm Γ)} (hH : Cons Ax H) (φ : Fm (.text Γ)) :
    Cons Ax (H.map (fun h => (h.twk : Fm (.text Γ))) ++ [Tm.imp ((Tm.tex φ).twk) φ]) := by
  intro h
  obtain ⟨hA, hn⟩ := split_wit (Ent.intro h)
  have hall : Ent Ax Γ H (Tm.tall φ.neg) := Ent.tgen hn
  have hex : Ent Ax Γ H (Tm.tex φ) := Ent.tstrengthen hA
  have hd : Ent Ax Γ H (Tm.tall φ.neg).neg := Ent.iffMp (Ent.ofProv (Prov.dualTEx φ)) hex
  exact hH (Ent.absurd hall hd)

theorem stepEx_cases (S : St) (c : Nat) :
    (∃ σ φ, stepEx S c = ⟨⟨S.n, S.Γ.ext σ⟩, liftWk S σ, Tm.imp ((Tm.ex σ φ).wk σ) φ⟩) ∨
      stepEx S c = ⟨_, liftWk S tyT, topF⟩ := by
  by_cases h : ∃ p : (σ : Ty S.n) × Fm (S.Γ.ext σ), codeF (Tm.ex p.1 p.2) = c
  · exact Or.inl ⟨_, _, dite_eq_left h⟩
  · exact Or.inr (dite_eq_right h)

theorem stepTex_cases (S : St) (c : Nat) :
    (∃ φ, stepTex S c = ⟨⟨S.n + 1, S.Γ.text⟩, liftTwk S, Tm.imp ((Tm.tex φ).twk) φ⟩) ∨
      stepTex S c = ⟨_, liftTwk S, topF⟩ := by
  by_cases h : ∃ φ : Fm S.Γ.text, codeF (Tm.tex φ) = c
  · exact Or.inl ⟨_, dite_eq_left h⟩
  · exact Or.inr (dite_eq_right h)

theorem cons_res (S : St) (R : StepRes S)
    (hR : (∃ σ φ, R = ⟨⟨S.n, S.Γ.ext σ⟩, liftWk S σ, Tm.imp ((Tm.ex σ φ).wk σ) φ⟩) ∨
      (∃ φ, R = ⟨⟨S.n + 1, S.Γ.text⟩, liftTwk S, Tm.imp ((Tm.tex φ).twk) φ⟩) ∨
      R = ⟨_, liftWk S tyT, topF⟩ ∨ R = ⟨_, liftTwk S, topF⟩)
    {H : List (Fm S.Γ)} (hH : Cons Ax H) : Cons Ax (H.map (liftF R.L) ++ [R.W]) := by
  rcases hR with ⟨σ, φ, rfl⟩ | ⟨φ, rfl⟩ | rfl | rfl
  · exact cons_witEx hH _ _
  · exact cons_witTex hH _
  · exact cons_top (cons_wk hH _)
  · exact cons_top (cons_twk hH)

theorem step_shape (S : St) (k : Nat) :
    (∃ σ φ, step S k = ⟨⟨S.n, S.Γ.ext σ⟩, liftWk S σ, Tm.imp ((Tm.ex σ φ).wk σ) φ⟩) ∨
      (∃ φ, step S k = ⟨⟨S.n + 1, S.Γ.text⟩, liftTwk S, Tm.imp ((Tm.tex φ).twk) φ⟩) ∨
      step S k = ⟨_, liftWk S tyT, topF⟩ ∨ step S k = ⟨_, liftTwk S, topF⟩ := by
  rcases step_cases S k with ⟨c, e⟩ | ⟨c, e⟩ | e <;> rw [e]
  · rcases stepEx_cases S c with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases stepTex_cases S c with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl rfl))

theorem cons_step (S : St) (k : Nat) {H : List (Fm S.Γ)} (hH : Cons Ax H) :
    Cons Ax (H.map (liftF (step S k).L) ++ [(step S k).W]) :=
  cons_res S (step S k) (step_shape S k) hH

variable (Ax) {n0 : Nat} {Γ0 : Ctx n0} (φ0 : Fm Γ0)

/-- Decide the formula with code `c`, if the task is a decision. -/
noncomputable def decideStep {n : Nat} {Γ : Ctx n} (H : List (Fm Γ)) : Option (Nat × Nat) → List (Fm Γ)
  | some (2, c) =>
    open Classical in
    if Cons Ax (H ++ [decodeF Γ c]) then H ++ [decodeF Γ c] else H ++ [(decodeF Γ c).neg]
  | _ => H

/-- The theory at each stage: `¬φ₀`, the witness axioms, and the decisions. -/
noncomputable def theory : (k : Nat) → List (Fm (chain n0 Γ0 k).Γ)
  | 0 => [Tm.neg φ0]
  | k + 1 => decideStep Ax ((theory k).map (liftF (step (chain n0 Γ0 k) k).L) ++ [(step (chain n0 Γ0 k) k).W]) (task k)

variable {Ax φ0}

theorem decideStep_cons {n : Nat} {Γ : Ctx n} {H : List (Fm Γ)} (hH : Cons Ax H) (o : Option (Nat × Nat)) :
    Cons Ax (decideStep Ax H o) := by
  unfold decideStep
  split
  · split
    · next hy => exact hy
    · next hn => exact (cons_decide hH _).resolve_left hn
  · exact hH

theorem theory_cons (h0 : ¬ Prov Ax Γ0 φ0) : ∀ k, Cons Ax (theory Ax φ0 k)
  | 0 => fun h => by
    have h' : Ent Ax Γ0 ([] ++ [Tm.neg φ0]) botF := h
    exact h0 (Ent.toProv (Ent.mp2 (Ent.taut (.imp (.imp (.neg (.atom 0)) (.atom 1)) (.imp (.neg (.atom 1)) (.atom 0)))
      (v2 φ0 botF) (fun _ f g => Classical.byContradiction fun na => g (f na))) (Ent.intro h') Ent.top))
  | k + 1 => decideStep_cons (cons_step (chain n0 Γ0 k) k (theory_cons h0 k)) (task k)

end Theory


/-! ## Lifting along the chain -/

theorem codeTm_heq {n : Nat} {Γ : Ctx n} {K K' : Cat n} (h : K = K') {M : Tm Γ K} {M' : Tm Γ K'} (hM : HEq M M')
    (d td : Nat) : codeTm d td M = codeTm d td M' := by
  subst h; cases hM; rfl

def Lift.id (S : St) : Lift S S :=
  ⟨fun i => i, idRen S.Γ, fun M => (codeTm_heq (Cat.ren_id _) (Tm.ren_id_heq M) 0 0),
    fun K => by rw [Cat.ren_id]⟩

def Lift.comp {S S' S'' : St} (L1 : Lift S S') (L2 : Lift S' S'') : Lift S S'' :=
  ⟨fun i => L2.r (L1.r i), fun x => Var.castK (Cat.ren_ren _ _ _) (L2.ρ (L1.ρ x)),
    fun M => (codeTm_heq (Cat.ren_ren _ _ _).symm
      (Tm.ren_ren_heq M L1.ρ L2.ρ _ (fun _ => rfl) (fun _ => (var_castK_heq' _ _).symm)).symm 0 0).trans
      ((L2.codeT _).trans (L1.codeT M)),
    fun K => by rw [← Cat.ren_ren, L2.codeC, L1.codeC]⟩

theorem liftF_comp {S S' S'' : St} (L1 : Lift S S') (L2 : Lift S' S'') (φ : Fm S.Γ) :
    liftF (L1.comp L2) φ = liftF L2 (liftF L1 φ) :=
  eq_of_heq (Tm.ren_ren_heq φ L1.ρ L2.ρ _ (fun _ => rfl) (fun _ => (var_castK_heq' _ _).symm)).symm

theorem codeF_liftF {S S' : St} (L : Lift S S') (φ : Fm S.Γ) : codeF (liftF L φ) = codeF φ :=
  congrArg encL (L.codeT φ)

theorem chain_liftF {S S' : St} (L : Lift S S') (Hs : List (Fm S.Γ)) (φ : Fm S.Γ) :
    Derive.chain (Hs.map (liftF L)) (liftF L φ) = liftF L (Derive.chain Hs φ) := by
  induction Hs with
  | nil => rfl
  | cons h hs ih => show (liftF L h).imp (Derive.chain (hs.map (liftF L)) (liftF L φ)) = _; rw [ih]; rfl

theorem ent_lift {Ax : Fm Ctx.nil → Prop} {S S' : St} (L : Lift S S') {Hs : List (Fm S.Γ)} {φ : Fm S.Γ}
    (h : Ent Ax S.Γ Hs φ) : Ent Ax S'.Γ (Hs.map (liftF L)) (liftF L φ) := by
  unfold Ent; rw [chain_liftF]; exact Prov.ren _ h

theorem ent_append {Ax : Fm Ctx.nil → Prop} {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)} {φ : Fm Γ}
    (h : Ent Ax Γ Hs φ) : ∀ (extra : List (Fm Γ)), Ent Ax Γ (Hs ++ extra) φ := by
  intro extra
  induction extra generalizing Hs with
  | nil => simpa using h
  | cons a l ih =>
    have e : Hs ++ a :: l = (Hs ++ [a]) ++ l := by simp
    rw [e]; exact ih (Ent.weaken h)

section Lifts
variable (n0 : Nat) (Γ0 : Ctx n0)

noncomputable def upd (k : Nat) : (d : Nat) → Lift (chain n0 Γ0 k) (chain n0 Γ0 (k + d))
  | 0 => Lift.id _
  | d + 1 => (upd k d).comp (step (chain n0 Γ0 (k + d)) (k + d)).L

/-- The lift from stage `k` to any later stage `J`. -/
noncomputable def liftL (k J : Nat) (h : k ≤ J) : Lift (chain n0 Γ0 k) (chain n0 Γ0 J) :=
  (Nat.add_sub_cancel' h) ▸ (upd n0 Γ0 k (J - k))

end Lifts

section Mono
variable {Ax : Fm Ctx.nil → Prop} {n0 : Nat} {Γ0 : Ctx n0} {φ0 : Fm Γ0}

theorem decideStep_ext {n : Nat} {Γ : Ctx n} (H : List (Fm Γ)) (o : Option (Nat × Nat)) :
    ∃ extra, decideStep Ax H o = H ++ extra := by
  unfold decideStep
  split
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨[], (List.append_nil _).symm⟩

theorem theory_step {k : Nat} {φ : Fm (chain n0 Γ0 k).Γ} (h : Ent Ax _ (theory Ax φ0 k) φ) :
    Ent Ax _ (theory Ax φ0 (k + 1)) (liftF (step (chain n0 Γ0 k) k).L φ) := by
  obtain ⟨extra, e⟩ := decideStep_ext (Ax := Ax)
    ((theory Ax φ0 k).map (liftF (step (chain n0 Γ0 k) k).L) ++ [(step (chain n0 Γ0 k) k).W]) (task k)
  have := ent_append (ent_append (ent_lift (Ax := Ax) (step (chain n0 Γ0 k) k).L h) [(step (chain n0 Γ0 k) k).W]) extra
  rw [← e] at this
  exact this

theorem theory_upd {k : Nat} {φ : Fm (chain n0 Γ0 k).Γ} (h : Ent Ax _ (theory Ax φ0 k) φ) :
    ∀ d, Ent Ax _ (theory Ax φ0 (k + d)) (liftF (upd n0 Γ0 k d) φ)
  | 0 => by
    show Ent Ax _ (theory Ax φ0 k) (liftF (Lift.id _) φ)
    have : liftF (Lift.id (chain n0 Γ0 k)) φ = φ := eq_of_heq (Tm.ren_id_heq φ)
    rw [this]; exact h
  | d + 1 => by
    have e : (liftF (upd n0 Γ0 k (d + 1)) φ : Fm (chain n0 Γ0 (k + d + 1)).Γ) =
        (liftF (step (chain n0 Γ0 (k + d)) (k + d)).L (liftF (upd n0 Γ0 k d) φ) : Fm (chain n0 Γ0 (k + d + 1)).Γ) :=
      liftF_comp _ _ _
    show Ent Ax (chain n0 Γ0 (k + d + 1)).Γ (theory Ax φ0 (k + d + 1)) (liftF (upd n0 Γ0 k (d + 1)) φ)
    rw [e]
    exact theory_step (theory_upd h d)

theorem theory_liftL {k : Nat} {φ : Fm (chain n0 Γ0 k).Γ} (h : Ent Ax _ (theory Ax φ0 k) φ) (J : Nat) (hJ : k ≤ J) :
    Ent Ax _ (theory Ax φ0 J) (liftF (liftL n0 Γ0 k J hJ) φ) := by
  have key : ∀ (d j : Nat) (e : k + d = j), Ent Ax _ (theory Ax φ0 j)
      (liftF (e ▸ upd n0 Γ0 k d : Lift (chain n0 Γ0 k) (chain n0 Γ0 j)) φ) := by
    intro d j e; subst e; exact theory_upd h d
  exact key _ _ _

end Mono

end Compl
end PIF
