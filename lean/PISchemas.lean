import PIDerivations

/-!
# Schemas: Theorem 3 and the second half of Theorem 11

These results are about an arbitrary polymorphic predicate `P`. Lean cannot compute inside `P`, so
the derivations use the fact that a closed term, renamed or substituted into any context, is the
same as the term simply moved into that context (`Pc`).
-/
set_option autoImplicit false

namespace PIF

section Closed

/-- The category `Πγ:∗.γ→t` of polymorphic predicates. -/
abbrev PK {n : Nat} : Cat n := .pi (.arr (.var fz) .t)

/-- A renaming out of the empty context is unique. -/
theorem closed_ren_heq {K : Cat 0} (M : Tm Ctx.nil K) {m : Nat} {r : Fin 0 → Fin m} {Θ : Ctx m}
    (ρ : TRen r Ctx.nil Θ) : HEq (M.ren ρ) (M.ren (Derive.nilRen Θ)) := by
  have hr : r = (fun i => i.elim0) := funext (fun i => i.elim0)
  subst hr
  have hρ : @ρ = @Derive.nilRen m Θ := by funext K x; cases x
  rw [hρ]

/-- A substitution out of the empty context is a renaming. -/
theorem closed_sub_heq {K : Cat 0} (M : Tm Ctx.nil K) {m : Nat} {s : Fin 0 → Ty m} {Θ : Ctx m}
    (σs : TSub s Ctx.nil Θ) : HEq (M.sub σs) (M.ren (Derive.nilRen Θ)) := by
  have hs : s = (fun i => tvar (i.elim0)) := funext (fun i => i.elim0)
  subst hs
  exact (Tm.ren_eq_sub_heq M (Derive.nilRen Θ) rfl σs (fun i => i.elim0) (fun x => nomatch x)).symm

/-- A renaming as a substitution. -/
def TRen.asSub {n m : Nat} {r : Fin n → Fin m} {Γ : Ctx n} {Δ : Ctx m} (ρ : TRen r Γ Δ) :
    TSub (fun i => tvar (r i)) Γ Δ := fun {K} x =>
  Tm.castK (Cat.ren_eq_sub K (fun _ => rfl)) (Tm.var (ρ x))

theorem closed_ren_ren_heq {K : Cat 0} (M : Tm Ctx.nil K) {m k : Nat} {r0 : Fin 0 → Fin m} {Δ : Ctx m}
    (ρ0 : TRen r0 Ctx.nil Δ) {r : Fin m → Fin k} {Θ : Ctx k} (ρ : TRen r Δ Θ) :
    HEq ((M.ren ρ0).ren ρ) (M.ren (Derive.nilRen Θ)) := by
  refine (Tm.ren_eq_sub_heq (M.ren ρ0) ρ rfl (TRen.asSub ρ) (fun _ => rfl)
    (fun x => (castK_heq _ _).symm)).trans ?_
  refine (Tm.sub_ren_heq M ρ0 rfl (TRen.asSub ρ) (s' := fun i => i.elim0) (fun x => nomatch x) (fun i => i.elim0) (fun x => nomatch x)).trans ?_
  exact closed_sub_heq M _

theorem closed_ren_sub_heq {K : Cat 0} (M : Tm Ctx.nil K) {m k : Nat} {r0 : Fin 0 → Fin m} {Δ : Ctx m}
    (ρ0 : TRen r0 Ctx.nil Δ) {s : Fin m → Ty k} {Θ : Ctx k} (σs : TSub s Δ Θ) :
    HEq ((M.ren ρ0).sub σs) (M.ren (Derive.nilRen Θ)) :=
  (Tm.sub_ren_heq M ρ0 rfl σs (s' := fun i => i.elim0) (fun x => nomatch x) (fun i => i.elim0) (fun x => nomatch x)).trans
    (closed_sub_heq M _)

variable (P : Tm Ctx.nil PK)

/-- `P`, moved into the context `Θ`. -/
def Pc {m : Nat} (Θ : Ctx m) : Tm Θ PK := P.ren (Derive.nilRen Θ)

theorem Pc_ren {m k : Nat} {Δ : Ctx m} {r : Fin m → Fin k} {Θ : Ctx k} (ρ : TRen r Δ Θ) :
    (Pc P Δ).ren ρ = Pc P Θ := eq_of_heq (closed_ren_ren_heq P _ ρ)

theorem Pc_sub {m k : Nat} {Δ : Ctx m} {s : Fin m → Ty k} {Θ : Ctx k} (σs : TSub s Δ Θ) :
    (Pc P Δ).sub σs = Pc P Θ := eq_of_heq (closed_ren_sub_heq P _ σs)

theorem P_ren {m : Nat} {r : Fin 0 → Fin m} {Θ : Ctx m} (ρ : TRen r Ctx.nil Θ) : P.ren ρ = Pc P Θ :=
  eq_of_heq (closed_ren_heq P ρ)

theorem Pc_twk {m : Nat} {Δ : Ctx m} : (Pc P Δ).twk = Pc P Δ.text := Pc_ren P _
theorem Pc_wk {m : Nat} {Δ : Ctx m} (σ : Ty m) : (Pc P Δ).wk σ = Pc P (Δ.ext σ) := Pc_ren P _
theorem P_twk : P.twk = Pc P Ctx.nil.text := P_ren P _

end Closed

section PcHEq
variable (P : Tm Ctx.nil PK)

theorem heq_Pc_ren {m k : Nat} {Δ : Ctx m} {K : Cat m} {X : Tm Δ K} (hK : K = PK) (hX : HEq X (Pc P Δ))
    {r : Fin m → Fin k} {Θ : Ctx k} (ρ : TRen r Δ Θ) : HEq (X.ren ρ) (Pc P Θ) := by
  subst hK; cases eq_of_heq hX; exact closed_ren_ren_heq P _ ρ

theorem heq_Pc_sub {m k : Nat} {Δ : Ctx m} {K : Cat m} {X : Tm Δ K} (hK : K = PK) (hX : HEq X (Pc P Δ))
    {s : Fin m → Ty k} {Θ : Ctx k} (σs : TSub s Δ Θ) : HEq (X.sub σs) (Pc P Θ) := by
  subst hK; cases eq_of_heq hX; exact closed_ren_sub_heq P _ σs

theorem heq_Pc_wk {m : Nat} {Δ : Ctx m} {K : Cat m} {X : Tm Δ K} (hK : K = PK) (hX : HEq X (Pc P Δ))
    (σ : Ty m) : HEq (X.wk σ) (Pc P (Δ.ext σ)) :=
  (castK_heq _ _).trans (heq_Pc_ren P hK hX _)

theorem heq_P_ren {m : Nat} {r : Fin 0 → Fin m} {Θ : Ctx m} (ρ : TRen r Ctx.nil Θ) : HEq (P.ren ρ) (Pc P Θ) :=
  closed_ren_heq P ρ

theorem heq_P_self : HEq P (Pc P Ctx.nil) :=
  (Tm.sub_id_heq P rfl (s := fun i => i.elim0) (fun x => nomatch x) (fun i => i.elim0) (fun x => nomatch x)).trans
    (closed_sub_heq P _)

/-- A formula equal to a provable one is provable. -/
theorem Derive.Ent.congr {Ax : Fm Ctx.nil → Prop} {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)} {φ ψ : Fm Γ}
    (h : Derive.Ent Ax Γ Hs φ) (e : φ = ψ) : Derive.Ent Ax Γ Hs ψ := e ▸ h

end PcHEq

/-- Close goals `HEq X (Pc P Θ)` where `X` is `P` moved by renamings and substitutions. -/
macro "pc_heq" : tactic => `(tactic| repeat (first
  | exact HEq.rfl
  | refine heq_Pc_wk _ rfl ?_ _
  | refine heq_Pc_ren _ rfl ?_ _
  | refine heq_Pc_sub _ rfl ?_ _
  | exact heq_P_ren _ _
  | exact heq_P_self _))

section Bridge
open Tm Derive
variable (P : Tm Ctx.nil PK)

abbrev Γb : Ctx 2 := (Δ2.ext tv1).ext tv0
/-- The body of LL≡/≈ for the predicate `p`: `(x ≡ y ∧ α ≈ β) → (p_α x → p_β y)`. -/
def BridgeB (p : Tm Γb PK) : Fm Γb :=
  imp (conj (eqv tv1 tv0 (.var (.there .here)) (.var .here)) (teq tv1 tv0))
    (imp (.app (.tapp p tv1) (.var (.there .here))) (.app (.tapp p tv0) (.var .here)))

def BridgeT (p : Tm Γb PK) : Fm Ctx.nil := tall (tall (all tv1 (all tv0 (BridgeB p))))

theorem bridge_eq : Bridge P = BridgeT (Pc P Γb) := by
  refine (congrArg BridgeT (?_ : ((P.twk.twk.wk tv1).wk tv0 : Tm Γb PK) = Pc P Γb) : _)
  exact eq_of_heq (by pc_heq)

abbrev Γq : Ctx 3 := (Δ3.ext tv2).ext tv0
/-- The body of `Q`: `x ≡ y → (p_α x → p_γ y)`, for `x : α`, `y : γ`. -/
def QB (p : Tm Γq PK) : Fm Γq :=
  imp (eqv tv2 tv0 (.var (.there .here)) (.var .here))
    (imp (.app (.tapp p tv2) (.var (.there .here))) (.app (.tapp p tv0) (.var .here)))
def QP : Tm Δ2 (.pi .t) := .tlam (all tv2 (all tv0 (QB (Pc P Γq))))

def QT (a b : Tm Γq PK) : Fm Δ2 :=
  imp (teq tv1 tv0) (imp (.tapp (.tlam (all tv2 (all tv0 (QB a)))) tv1) (.tapp (.tlam (all tv2 (all tv0 (QB b)))) tv0))

theorem QT_congr {a b a' b' : Tm Γq PK} (ha : a = a') (hb : b = b') : QT a b = QT a' b' := by rw [ha, hb]

/-- `x ≡ y → (p_σ x → p_τ y)`, for `x : σ`, `y : τ` the two innermost variables. -/
def QBg {Γ0 : Ctx 2} (σ τ : Ty 2) (p : Tm ((Γ0.ext σ).ext τ) PK) : Fm ((Γ0.ext σ).ext τ) :=
  imp (eqv σ τ (.var (.there .here)) (.var .here))
    (imp (.app (.tapp p σ) (.var (.there .here))) (.app (.tapp p τ) (.var .here)))

abbrev Γa : Ctx 2 := (Δ2.ext tv1).ext tv1

def QT2 (a : Tm Γa PK) (b : Tm Γb PK) : Fm Δ2 :=
  imp (teq tv1 tv0) (imp (all tv1 (all tv1 (QBg tv1 tv1 a))) (all tv1 (all tv0 (QBg tv1 tv0 b))))

theorem QT2_congr {a a' : Tm Γa PK} {b b' : Tm Γb PK} (ha : a = a') (hb : b = b') : QT2 a b = QT2 a' b' := by
  rw [ha, hb]

abbrev Γw : Ctx 2 := (Γb.ext tv1).ext tv0

def W1 (a : Tm Γw PK) : Fm Γb := imp (teq tv1 tv0) (all tv1 (all tv0 (QBg tv1 tv0 a)))
theorem W1_congr {a a' : Tm Γw PK} (ha : a = a') : W1 a = W1 a' := by rw [ha]

def W2 (a : Tm Γb PK) : Fm Γb := imp (teq tv1 tv0) (QBg tv1 tv0 a)
theorem W2_congr {a a' : Tm Γb PK} (ha : a = a') : W2 a = W2 a' := by rw [ha]

variable {S : Fm Ctx.nil → Prop}

set_option maxHeartbeats 4000000 in
/-- The body of LL≡/≈, from LL≡ and LL≈ with `Q = λγ.∀_α x ∀_γ y (x ≡ y → (P_α x → P_γ y))`. -/
theorem d_BridgeB (hLL : S LLEqv) : Ent S Γb [] (BridgeB (Pc P Γb)) := by
  -- the instance of LL≈
  have hQ : Ent S Δ2 [] (LLTeq (QP P)) := Ent.ofProv (Prov.llTeq _)
  have h1 : Ent S Δ2 [] (QT (Pc P Γq) (Pc P Γq)) := by
    refine Ent.congr ((hQ.tinst tv1).tinst tv0) (QT_congr ?_ ?_) <;> exact eq_of_heq (by pc_heq)
  have h2 : Ent S Δ2 [] (QT2 (Pc P Γa) (Pc P Γb)) := by
    refine Ent.congr (Ent.beta h1 (BetaEq.imp (.refl _) (BetaEq.imp (BetaEq.tbeta _ _) (BetaEq.tbeta _ _))))
      (QT2_congr ?_ ?_) <;> exact eq_of_heq (by pc_heq)
  -- `Q α`, from LL≡ with `F := P_α`
  have h3 : Ent S Γa [] ((eqv tv1 tv1 (.var (.there .here)) (.var .here)).imp
      (all tv1.pred (imp (.app (.var .here) (.var (.there (.there .here)))) (.app (.var .here) (.var (.there .here)))))) :=
    (((Ent.axm (Γ := Γa) (Hs := []) hLL).tinst tv1).inst (.var (.there .here))).inst (.var .here)
  have h4 : Ent S Γa [] (QBg tv1 tv1 (Pc P Γa)) := Ent.impInst h3 (.tapp (Pc P Γa) tv1)
  have h5 : Ent S Δ2 [] (all tv1 (all tv1 (QBg tv1 tv1 (Pc P Γa)))) := Ent.gen tv1 (Ent.gen tv1 h4)
  have h6 : Ent S Δ2 [] (imp (teq tv1 tv0) (all tv1 (all tv0 (QBg tv1 tv0 (Pc P Γb))))) :=
    Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2))) (.imp (.atom 1) (.imp (.atom 0) (.atom 2))))
      (v3 (teq tv1 tv0) (all tv1 (all tv1 (QBg tv1 tv1 (Pc P Γa)))) (all tv1 (all tv0 (QBg tv1 tv0 (Pc P Γb)))))
      (fun _ f b a => f a b)) h2 h5
  -- move into the context `α β x y`, and instantiate
  have h7 : Ent S Γb [] (W1 (Pc P Γw)) := by
    refine Ent.congr (Prov.ren (wkRen tv0) (Prov.ren (wkRen tv1) h6)) (W1_congr ?_)
    exact eq_of_heq (by pc_heq)
  have h8 : Ent S Γb [] (W2 (Pc P Γb)) := by
    refine Ent.congr (Ent.impInst (Ent.impInst h7 (.var (.there .here))) (.var .here)) (W2_congr ?_)
    exact eq_of_heq (by pc_heq)
  exact Ent.mp (Ent.taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.imp (.atom 2) (.atom 3))))
      (.imp (.conj (.atom 1) (.atom 0)) (.imp (.atom 2) (.atom 3))))
    (v4 (teq tv1 tv0) (eqv tv1 tv0 (.var (.there .here)) (.var .here))
      (.app (.tapp (Pc P Γb) tv1) (.var (.there .here))) (.app (.tapp (Pc P Γb) tv0) (.var .here)))
    (fun _ f h => f h.2 h.1)) h8

/-- Theorem 3: LL≡ proves every instance of LL≡/≈. -/
theorem d_Bridge (hLL : S LLEqv) : Prov S Ctx.nil (Bridge P) := by
  rw [bridge_eq]
  exact Ent.toProv (Ent.tgen (Ent.tgen (Ent.gen tv1 (Ent.gen tv0 (d_BridgeB P hLL)))))

/-- The body of LL≡-Poly for the predicate `p`. -/
def LLPolyT (p : Tm Γb PK) : Fm Ctx.nil := tall (tall (all tv1 (all tv0 (QBg tv1 tv0 p))))

theorem llPoly_eq : LLPoly P = LLPolyT (Pc P Γb) := by
  refine (congrArg LLPolyT (?_ : ((P.twk.twk.wk tv1).wk tv0 : Tm Γb PK) = Pc P Γb) : _)
  exact eq_of_heq (by pc_heq)

set_option maxHeartbeats 4000000 in
/-- Theorem 11, second half: Disjoint and LL≡ prove every instance of LL≡-Poly. -/
theorem d_LLPoly_of_Disjoint (hLL : S LLEqv) (hD : S Disjoint) : Prov S Ctx.nil (LLPoly P) := by
  have h1 : Ent S Γb [] ((neg (teq tv1 tv0)).imp (all tv1 (all tv0 (neg (eqv tv1 tv0 (.var (.there .here)) (.var .here)))))) :=
    ((Ent.axm (Γ := Γb) (Hs := []) hD).tinst tv1).tinst tv0
  have h2 : Ent S Γb [] ((neg (teq tv1 tv0)).imp (neg (eqv tv1 tv0 (.var (.there .here)) (.var .here)))) :=
    Ent.impInst (Ent.impInst h1 (.var (.there .here))) (.var .here)
  have h3 : Ent S Γb [] (QBg tv1 tv0 (Pc P Γb)) :=
    Ent.mp2 (Ent.taut (.imp (.imp (.neg (.atom 0)) (.neg (.atom 1)))
        (.imp (.imp (.conj (.atom 1) (.atom 0)) (.imp (.atom 2) (.atom 3))) (.imp (.atom 1) (.imp (.atom 2) (.atom 3)))))
      (v4 (teq tv1 tv0) (eqv tv1 tv0 (.var (.there .here)) (.var .here))
        (.app (.tapp (Pc P Γb) tv1) (.var (.there .here))) (.app (.tapp (Pc P Γb) tv0) (.var .here)))
      (fun _ f g e => g ⟨e, Classical.byContradiction fun nt => f nt e⟩)) h2 (d_BridgeB P hLL)
  rw [llPoly_eq]
  exact Ent.toProv (Ent.tgen (Ent.tgen (Ent.gen tv1 (Ent.gen tv0 h3))))

end Bridge

end PIF
