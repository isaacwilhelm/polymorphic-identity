import PIFoundation

/-!
# Derivations in PI

The derivations of *Formal Results*, written out in the proof system of `PIFoundation.lean` and
checked by Lean.
-/
set_option autoImplicit false

namespace PIF

/-! ## 14. Derivations

A small toolkit for writing derivations in PI, and then the derivations of *Formal Results*.

`Ent Ax Γ Hs φ` says that PI⁻ + `Ax` derives `H₁ → (H₂ → ⋯ → φ)` in context `Γ`, where `Hs` is the list
`H₁, H₂, …`: that is, it derives `φ` from the hypotheses `Hs`. Since this is just a derivation of an
implication, discharging a hypothesis costs nothing. -/

/-! ## Substitution lemmas for terms

General facts about renaming and substitution of terms, needed for derivations of schemas (which
mention an arbitrary predicate `P`, inside which Lean cannot compute). Since categories are only
propositionally equal after these operations, the lemmas are stated with `HEq`. -/

section TermLemmas

theorem heq_app' {n : Nat} {Γ Γ' : Ctx n} {K K' L L' : Cat n} (hΓ : Γ = Γ') (hK : K = K') (hL : L = L')
    {f : Tm Γ (.arr K L)} {f' : Tm Γ' (.arr K' L')} {a : Tm Γ K} {a' : Tm Γ' K'}
    (hf : HEq f f') (ha : HEq a a') : HEq (Tm.app f a) (Tm.app f' a') := by
  subst hΓ; subst hK; subst hL; cases hf; cases ha; rfl

theorem heq_lam' {n : Nat} {Γ Γ' : Ctx n} {σ σ' : Ty n} {L L' : Cat n} (hΓ : Γ = Γ') (hσ : σ = σ') (hL : L = L')
    {b : Tm (.ext Γ σ) L} {b' : Tm (.ext Γ' σ') L'} (hb : HEq b b') : HEq (Tm.lam σ b) (Tm.lam σ' b') := by
  subst hΓ; subst hσ; subst hL; cases hb; rfl

theorem heq_tlam' {n : Nat} {Γ Γ' : Ctx n} {K K' : Cat (n+1)} (hΓ : Γ = Γ') (hK : K = K')
    {b : Tm (.text Γ) K} {b' : Tm (.text Γ') K'} (hb : HEq b b') : HEq (Tm.tlam b) (Tm.tlam b') := by
  subst hΓ; subst hK; cases hb; rfl

theorem heq_tapp' {n : Nat} {Γ Γ' : Ctx n} {K K' : Cat (n+1)} (hΓ : Γ = Γ') (hK : K = K')
    {f : Tm Γ (.pi K)} {f' : Tm Γ' (.pi K')} (hf : HEq f f') {σ σ' : Ty n} (hσ : σ = σ') :
    HEq (Tm.tapp f σ) (Tm.tapp f' σ') := by
  subst hΓ; subst hK; subst hσ; cases hf; rfl

theorem castK_heq {n : Nat} {Γ : Ctx n} {K K' : Cat n} (h : K = K') (M : Tm Γ K) : HEq (Tm.castK h M) M := by
  subst h; rfl

theorem sub_castK_heq {n m : Nat} {s : Fin n → Ty m} {Γ : Ctx n} {Δ : Ctx m} (σs : TSub s Γ Δ) {K K' : Cat n}
    (h : K = K') (M : Tm Γ K) : HEq ((Tm.castK h M).sub σs) (M.sub σs) := by
  subst h; rfl

theorem tsub_varCast_heq {n m : Nat} {s : Fin n → Ty m} {Γ : Ctx n} {Δ : Ctx m} (σs : TSub s Γ Δ) {K K' : Cat n}
    (h : K = K') (x : Var Γ K) : HEq (σs (Var.castK h x)) (σs x) := by
  subst h; rfl

theorem heq_var_here {n : Nat} {Θ Θ' : Ctx n} {τ τ' : Ty n} (hΘ : Θ = Θ') (hτ : τ = τ') :
    HEq (Tm.var (Γ := .ext Θ τ) .here) (Tm.var (Γ := .ext Θ' τ') .here) := by
  subst hΘ; subst hτ; rfl

theorem heq_wk {n : Nat} {Θ Θ' : Ctx n} {τ τ' : Ty n} {L L' : Cat n} (hΘ : Θ = Θ') (hτ : τ = τ') (hL : L = L')
    {M : Tm Θ L} {M' : Tm Θ' L'} (h : HEq M M') : HEq (M.wk τ) (M'.wk τ') := by
  subst hΘ; subst hτ; subst hL; cases h; rfl

theorem heq_twk {n : Nat} {Θ Θ' : Ctx n} {L L' : Cat n} (hΘ : Θ = Θ') (hL : L = L')
    {M : Tm Θ L} {M' : Tm Θ' L'} (h : HEq M M') : HEq (M.twk) (M'.twk) := by
  subst hΘ; subst hL; cases h; rfl

theorem heq_castK_both {n : Nat} {Γ Γ' : Ctx n} {K K' L L' : Cat n} (h1 : K = L) (h2 : K' = L')
    {M : Tm Γ K} {M' : Tm Γ' K'} (h : HEq M M') : HEq (Tm.castK h1 M) (Tm.castK h2 M') :=
  (castK_heq h1 M).trans (h.trans (castK_heq h2 M').symm)

theorem Cat.sub_ren_congr {n m k : Nat} (K : Cat n) {r : Fin n → Fin m} {s : Fin m → Ty k} {s' : Fin n → Ty k}
    (hs : ∀ i, (s (r i)).1 = (s' i).1) : (K.ren r).sub s = K.sub s' := by
  rw [Cat.sub_ren]; exact Cat.sub_congr K hs

/-- Substitution after renaming is substitution. -/
theorem Tm.sub_ren_heq {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) :
    ∀ {m k : Nat} {r : Fin n → Fin m} {Δ : Ctx m} (ρr : TRen r Γ Δ) {s : Fin m → Ty k} {Θ Θ' : Ctx k}
      (_ : Θ = Θ') (σs : TSub s Δ Θ) {s' : Fin n → Ty k} (σs' : TSub s' Γ Θ'),
      (∀ i, (s (r i)).1 = (s' i).1) → (∀ {L : Cat n} (x : Var Γ L), HEq (σs (ρr x)) (σs' x)) →
      HEq ((M.ren ρr).sub σs) (M.sub σs') := by
  induction M with
  | var x => intro m k r Δ ρr s Θ Θ' _ σs s' σs' _ hx; exact hx x
  | const c => intro m k r Δ ρr s Θ Θ' hΘ σs s' σs' _ _; subst hΘ; cases c <;> exact HEq.rfl
  | app f a ihf iha =>
    intro m k r Δ ρr s Θ Θ' hΘ σs s' σs' hs hx
    exact heq_app' hΘ (Cat.sub_ren_congr _ hs) (Cat.sub_ren_congr _ hs) (ihf ρr hΘ σs σs' hs hx) (iha ρr hΘ σs σs' hs hx)
  | lam σ b ih =>
    intro m k r Δ ρr s Θ Θ' hΘ σs s' σs' hs hx
    have hσ : (σ.ren r).sub s = σ.sub s' := Subtype.ext (Cat.sub_ren_congr σ.1 hs)
    refine heq_lam' hΘ hσ (Cat.sub_ren_congr _ hs) (ih (ρr.lift σ) (by rw [hΘ, hσ]) (σs.lift _) (σs'.lift σ) hs ?_)
    intro L x
    cases x with
    | here => exact heq_var_here hΘ hσ
    | there y => exact heq_wk hΘ hσ (Cat.sub_ren_congr _ hs) (hx y)
  | tlam b ih =>
    intro m k r Δ ρr s Θ Θ' hΘ σs s' σs' hs hx
    have hs' : ∀ i, (liftT s (liftR r i)).1 = (liftT s' i).1 :=
      fin_cases rfl (fun i => by show ((s (r i)).1.ren fs) = ((s' i).1.ren fs); rw [hs i])
    refine heq_tlam' hΘ (Cat.sub_ren_congr _ hs') (ih ρr.tlift (by rw [hΘ]) σs.tlift σs'.tlift hs' ?_)
    intro L x
    cases x with
    | tthere y =>
      refine (tsub_varCast_heq _ _ _).trans ?_
      exact heq_castK_both _ _ (heq_twk hΘ (Cat.sub_ren_congr _ hs) (hx y))
  | tapp f σ ih =>
    intro m k r Δ ρr s Θ Θ' hΘ σs s' σs' hs hx
    have hs' : ∀ i, (liftT s (liftR r i)).1 = (liftT s' i).1 :=
      fin_cases rfl (fun i => by show ((s (r i)).1.ren fs) = ((s' i).1.ren fs); rw [hs i])
    refine (sub_castK_heq σs _ _).trans ?_
    refine heq_castK_both _ _ ?_
    exact heq_tapp' hΘ (Cat.sub_ren_congr _ hs') (ih ρr hΘ σs σs' hs hx) (Subtype.ext (Cat.sub_ren_congr σ.1 hs))

theorem var_castK_heq {n : Nat} {Γ : Ctx n} {K K' : Cat n} (h : K = K') (x : Var Γ K) :
    HEq (Tm.var (Var.castK h x)) (Tm.var x) := by
  subst h; rfl

/-- Weakening a variable gives the next variable. -/
theorem wk_var_heq {n : Nat} {Γ : Ctx n} {K : Cat n} (τ : Ty n) (x : Var Γ K) :
    HEq ((Tm.var x).wk τ) (Tm.var (Γ := .ext Γ τ) (.there x)) :=
  (castK_heq _ _).trans (var_castK_heq _ _)

theorem Cat.ren_eq_sub {n : Nat} (K : Cat n) : ∀ {m : Nat} {r : Fin n → Fin m} {s : Fin n → Ty m},
    (∀ i, (s i).1 = Cat.var (r i)) → K.ren r = K.sub s := by
  induction K with
  | e => intros; rfl
  | t => intros; rfl
  | var i => intro m r s h; exact (h i).symm
  | arr a b iha ihb => intro m r s h; simp only [Cat.ren, Cat.sub, iha h, ihb h]
  | pi K ih =>
    intro m r s h
    simp only [Cat.ren, Cat.sub]
    congr 1
    exact ih (fin_cases rfl (fun i => by show (s i).1.ren fs = _; rw [h i]; rfl))

theorem Cat.sub_id_of {n : Nat} (K : Cat n) {s : Fin n → Ty n} (h : ∀ i, (s i).1 = Cat.var i) : K = K.sub s :=
  (Cat.ren_id K).symm.trans (Cat.ren_eq_sub K h)

/-- Substituting variables for variables is renaming. -/
theorem Tm.ren_eq_sub_heq {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) :
    ∀ {m : Nat} {r : Fin n → Fin m} {Δ : Ctx m} (ρr : TRen r Γ Δ) {s : Fin n → Ty m} {Θ : Ctx m}
      (_ : Δ = Θ) (σs : TSub s Γ Θ), (∀ i, (s i).1 = Cat.var (r i)) →
      (∀ {L : Cat n} (x : Var Γ L), HEq (Tm.var (ρr x)) (σs x)) → HEq (M.ren ρr) (M.sub σs) := by
  induction M with
  | var x => intro m r Δ ρr s Θ _ σs _ hx; exact hx x
  | const c => intro m r Δ ρr s Θ hΘ σs hs _; subst hΘ; cases c <;> exact HEq.rfl
  | app f a ihf iha =>
    intro m r Δ ρr s Θ hΘ σs hs hx
    exact heq_app' hΘ (Cat.ren_eq_sub _ hs) (Cat.ren_eq_sub _ hs) (ihf ρr hΘ σs hs hx) (iha ρr hΘ σs hs hx)
  | lam σ b ih =>
    intro m r Δ ρr s Θ hΘ σs hs hx
    have hσ : σ.ren r = σ.sub s := Subtype.ext (Cat.ren_eq_sub σ.1 hs)
    refine heq_lam' hΘ hσ (Cat.ren_eq_sub _ hs) (ih (ρr.lift σ) (by rw [hΘ, hσ]) (σs.lift σ) hs ?_)
    intro L x
    cases x with
    | here => exact heq_var_here hΘ hσ
    | there y => exact (wk_var_heq _ (ρr y)).symm.trans (heq_wk hΘ hσ (Cat.ren_eq_sub _ hs) (hx y))
  | tlam b ih =>
    intro m r Δ ρr s Θ hΘ σs hs hx
    have hs' : ∀ i, (liftT s i).1 = Cat.var (liftR r i) :=
      fin_cases rfl (fun i => by show (s i).1.ren fs = _; rw [hs i]; rfl)
    refine heq_tlam' hΘ (Cat.ren_eq_sub _ hs') (ih ρr.tlift (by rw [hΘ]) σs.tlift hs' ?_)
    intro L x
    cases x with
    | tthere y =>
      refine (var_castK_heq _ _).trans ?_
      refine HEq.trans ?_ (castK_heq _ _).symm
      exact heq_twk hΘ (Cat.ren_eq_sub _ hs) (hx y)
  | tapp f σ ih =>
    intro m r Δ ρr s Θ hΘ σs hs hx
    have hs' : ∀ i, (liftT s i).1 = Cat.var (liftR r i) :=
      fin_cases rfl (fun i => by show (s i).1.ren fs = _; rw [hs i]; rfl)
    exact heq_castK_both _ _ (heq_tapp' hΘ (Cat.ren_eq_sub _ hs') (ih ρr hΘ σs hs hx)
      (Subtype.ext (Cat.ren_eq_sub σ.1 hs)))

/-- The identity substitution changes nothing. -/
theorem Tm.sub_id_heq {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) :
    ∀ {s : Fin n → Ty n} {Θ : Ctx n} (_ : Γ = Θ) (σs : TSub s Γ Θ), (∀ i, (s i).1 = Cat.var i) →
      (∀ {L : Cat n} (x : Var Γ L), HEq (Tm.var x) (σs x)) → HEq M (M.sub σs) := by
  induction M with
  | var x => intro s Θ _ σs _ hx; exact hx x
  | const c => intro s Θ hΘ σs hs _; subst hΘ; cases c <;> exact HEq.rfl
  | app f a ihf iha =>
    intro s Θ hΘ σs hs hx
    exact heq_app' hΘ (Cat.sub_id_of _ hs) (Cat.sub_id_of _ hs) (ihf hΘ σs hs hx) (iha hΘ σs hs hx)
  | lam σ b ih =>
    intro s Θ hΘ σs hs hx
    have hσ : σ = σ.sub s := Subtype.ext (Cat.sub_id_of σ.1 hs)
    refine heq_lam' hΘ hσ (Cat.sub_id_of _ hs) (ih (by rw [hΘ, ← hσ]) (σs.lift σ) hs ?_)
    intro L x
    cases x with
    | here => exact heq_var_here hΘ hσ
    | there y => exact (wk_var_heq _ y).symm.trans (heq_wk hΘ hσ (Cat.sub_id_of _ hs) (hx y))
  | tlam b ih =>
    intro s Θ hΘ σs hs hx
    have hs' : ∀ i, (liftT s i).1 = Cat.var i :=
      fin_cases rfl (fun i => by show (s i).1.ren fs = _; rw [hs i]; rfl)
    refine heq_tlam' hΘ (Cat.sub_id_of _ hs') (ih (by rw [hΘ]) σs.tlift hs' ?_)
    intro L x
    cases x with
    | tthere y =>
      refine HEq.trans ?_ (castK_heq _ _).symm
      exact heq_twk hΘ (Cat.sub_id_of _ hs) (hx y)
  | tapp f σ ih =>
    intro s Θ hΘ σs hs hx
    refine HEq.trans ?_ (castK_heq _ _).symm
    have hs' : ∀ i, (liftT s i).1 = Cat.var i :=
      fin_cases rfl (fun i => by show (s i).1.ren fs = _; rw [hs i]; rfl)
    exact heq_tapp' hΘ (Cat.sub_id_of _ hs') (ih hΘ σs hs hx) (Subtype.ext (Cat.sub_id_of σ.1 hs))

end TermLemmas

namespace Derive
open Tm

variable {Ax : Fm Ctx.nil → Prop}

/-- `H₁ → (H₂ → ⋯ → φ)`. -/
def chain {n : Nat} {Γ : Ctx n} : List (Fm Γ) → Fm Γ → Fm Γ
  | [], φ => φ
  | h :: hs, φ => h.imp (chain hs φ)

def Ent (Ax : Fm Ctx.nil → Prop) {n : Nat} (Γ : Ctx n) (Hs : List (Fm Γ)) (φ : Fm Γ) : Prop :=
  Prov Ax Γ (chain Hs φ)

section Taut
variable {n : Nat} {Γ : Ctx n}

def v2 (a b : Fm Γ) : Fin 2 → Fm Γ := fun i => if i.val = 0 then a else b
def v3 (a b c : Fm Γ) : Fin 3 → Fm Γ := fun i => if i.val = 0 then a else if i.val = 1 then b else c
def v4 (a b c d : Fm Γ) : Fin 4 → Fm Γ :=
  fun i => if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d

theorem K (φ ψ : Fm Γ) : Prov Ax Γ (φ.imp (ψ.imp φ)) :=
  Prov.taut (.imp (.atom 0) (.imp (.atom 1) (.atom 0))) (v2 φ ψ) (fun _ h _ => h)

theorem I (φ : Fm Γ) : Prov Ax Γ (φ.imp φ) :=
  Prov.taut (.imp (.atom 0) (.atom 0)) (v2 φ φ) (fun _ h => h)

/-- `(A → B → C) → ((h → A) → (h → B) → (h → C))` -/
theorem liftS (h A B C : Fm Γ) :
    Prov Ax Γ ((A.imp (B.imp C)).imp ((h.imp A).imp ((h.imp B).imp (h.imp C)))) :=
  Prov.taut (.imp (.imp (.atom 1) (.imp (.atom 2) (.atom 3)))
    (.imp (.imp (.atom 0) (.atom 1)) (.imp (.imp (.atom 0) (.atom 2)) (.imp (.atom 0) (.atom 3)))))
    (v4 h A B C) (fun _ f g k x => f (g x) (k x))

/-- `(A → B) → ((h → A) → (h → B))` -/
theorem liftI (h A B : Fm Γ) : Prov Ax Γ ((A.imp B).imp ((h.imp A).imp (h.imp B))) :=
  Prov.taut (.imp (.imp (.atom 1) (.atom 2)) (.imp (.imp (.atom 0) (.atom 1)) (.imp (.atom 0) (.atom 2))))
    (v3 h A B) (fun _ f g x => f (g x))

/-- `(φ ↔ ψ) → (φ → ψ)` -/
theorem iffMp (φ ψ : Fm Γ) : Prov Ax Γ ((φ.iff ψ).imp (φ.imp ψ)) :=
  Prov.taut (.imp (.iff (.atom 0) (.atom 1)) (.imp (.atom 0) (.atom 1))) (v2 φ ψ) (fun _ h => h.mp)

/-- `(A → B) → ((B → C) → (A → C))` -/
theorem sylT (A B C : Fm Γ) : Prov Ax Γ ((A.imp B).imp ((B.imp C).imp (A.imp C))) :=
  Prov.taut (.imp (.imp (.atom 0) (.atom 1)) (.imp (.imp (.atom 1) (.atom 2)) (.imp (.atom 0) (.atom 2))))
    (v3 A B C) (fun _ f g x => g (f x))

theorem syl {A B C : Fm Γ} (h1 : Prov Ax Γ (A.imp B)) (h2 : Prov Ax Γ (B.imp C)) : Prov Ax Γ (A.imp C) :=
  Prov.mp h2 (Prov.mp h1 (sylT A B C))

end Taut

section Chain
variable {n : Nat} {Γ : Ctx n}

theorem chain_K (Hs : List (Fm Γ)) (φ : Fm Γ) : Prov Ax Γ (φ.imp (chain Hs φ)) := by
  induction Hs with
  | nil => exact I φ
  | cons h hs ih =>
    exact Prov.mp ih (Prov.taut (.imp (.imp (.atom 0) (.atom 1)) (.imp (.atom 0) (.imp (.atom 2) (.atom 1))))
      (v3 φ (chain hs φ) h) (fun _ f x _ => f x))

theorem chain_S (Hs : List (Fm Γ)) (A B : Fm Γ) :
    Prov Ax Γ ((chain Hs (A.imp B)).imp ((chain Hs A).imp (chain Hs B))) := by
  induction Hs with
  | nil => exact I _
  | cons h hs ih => exact Prov.mp ih (liftS h _ _ _)

theorem chain_append (Hs : List (Fm Γ)) (h φ : Fm Γ) : chain (Hs ++ [h]) φ = chain Hs (h.imp φ) := by
  induction Hs with
  | nil => rfl
  | cons k ks ih => show k.imp (chain (ks ++ [h]) φ) = k.imp (chain ks (h.imp φ)); rw [ih]

theorem Ent.mp {Hs : List (Fm Γ)} {A B : Fm Γ} (h1 : Ent Ax Γ Hs (A.imp B)) (h2 : Ent Ax Γ Hs A) : Ent Ax Γ Hs B :=
  Prov.mp h2 (Prov.mp h1 (chain_S Hs A B))

theorem Ent.ofProv {Hs : List (Fm Γ)} {A : Fm Γ} (h : Prov Ax Γ A) : Ent Ax Γ Hs A :=
  Prov.mp h (chain_K Hs A)

theorem Ent.toProv {A : Fm Γ} (h : Ent Ax Γ [] A) : Prov Ax Γ A := h

/-- The `i`th hypothesis. -/
theorem Ent.hyp : ∀ (Hs : List (Fm Γ)) (i : Nat) (hi : i < Hs.length), Ent Ax Γ Hs (Hs.get ⟨i, hi⟩)
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | h :: hs, 0, _ => chain_K hs h
  | h :: hs, i+1, hi => Prov.mp (Ent.hyp hs i (Nat.lt_of_succ_lt_succ hi)) (K _ h)

/-- Discharging the last hypothesis. -/
theorem Ent.intro {Hs : List (Fm Γ)} {h φ : Fm Γ} (H : Ent Ax Γ (Hs ++ [h]) φ) : Ent Ax Γ Hs (h.imp φ) := by
  unfold Ent at *; rw [chain_append] at H; exact H

/-- Adding a hypothesis at the end. -/
theorem Ent.weaken {Hs : List (Fm Γ)} {h φ : Fm Γ} (H : Ent Ax Γ Hs φ) : Ent Ax Γ (Hs ++ [h]) φ := by
  unfold Ent; rw [chain_append]; exact Ent.mp (Ent.ofProv (K φ h)) H

theorem Ent.taut {Hs : List (Fm Γ)} {k : Nat} (P : PF k) (as : Fin k → Fm Γ) (hP : P.Taut) :
    Ent Ax Γ Hs (P.inst as) := Ent.ofProv (Prov.taut P as hP)

theorem Ent.inst {Hs : List (Fm Γ)} {σ : Ty n} {φ : Fm (.ext Γ σ)} (H : Ent Ax Γ Hs (Tm.all σ φ)) (κ : Tm Γ σ.1) :
    Ent Ax Γ Hs (φ.subst0 κ) := Ent.mp (Ent.ofProv (Prov.instAll σ φ κ)) H

theorem Ent.tinst {Hs : List (Fm Γ)} {φ : Fm (.text Γ)} (H : Ent Ax Γ Hs (Tm.tall φ)) (σ : Ty n) :
    Ent Ax Γ Hs (φ.tinst σ) := Ent.mp (Ent.ofProv (Prov.instTAll φ σ)) H

theorem Ent.beta {Hs : List (Fm Γ)} {φ ψ : Fm Γ} (H : Ent Ax Γ Hs φ) (h : BetaEq φ ψ) : Ent Ax Γ Hs ψ :=
  Ent.mp (Ent.ofProv (Prov.mp (Prov.beta h) (iffMp φ ψ))) H

theorem genL (σ : Ty n) (Hs : List (Fm Γ)) (φ : Fm (.ext Γ σ)) :
    Prov Ax Γ ((Tm.all σ (chain (Hs.map (fun h => h.wk σ)) φ)).imp (chain Hs (Tm.all σ φ))) := by
  induction Hs with
  | nil => exact I _
  | cons h hs ih => exact syl (Prov.distAll σ h _) (Prov.mp ih (liftI h _ _))

/-- Generalization over a term variable, under hypotheses in which it does not occur. -/
theorem Ent.gen (σ : Ty n) {Hs : List (Fm Γ)} {φ : Fm (.ext Γ σ)}
    (H : Ent Ax (.ext Γ σ) (Hs.map (fun h => h.wk σ)) φ) : Ent Ax Γ Hs (Tm.all σ φ) :=
  Prov.mp (Prov.genAll σ H) (genL σ Hs φ)

theorem tgenL (Hs : List (Fm Γ)) (φ : Fm (.text Γ)) :
    Prov Ax Γ ((Tm.tall (chain (Hs.map (fun h => (h.twk : Fm (.text Γ)))) φ)).imp (chain Hs (Tm.tall φ))) := by
  induction Hs with
  | nil => exact I _
  | cons h hs ih => exact syl (Prov.distTAll h _) (Prov.mp ih (liftI h _ _))

/-- Generalization over a type variable, under hypotheses in which it does not occur. -/
theorem Ent.tgen {Hs : List (Fm Γ)} {φ : Fm (.text Γ)}
    (H : Ent Ax (.text Γ) (Hs.map (fun h => (h.twk : Fm (.text Γ)))) φ) : Ent Ax Γ Hs (Tm.tall φ) :=
  Prov.mp (Prov.genTAll H) (tgenL Hs φ)

/-- The renaming from the empty context into any context. -/
def nilRen (Γ : Ctx n) : TRen (fun i => i.elim0) Ctx.nil Γ := fun x => nomatch x

/-- A sentence PI⁻ + `Ax` proves may be used in any context. -/
theorem Ent.closed {Hs : List (Fm Γ)} {φ : Fm Ctx.nil} (h : Prov Ax Ctx.nil φ) : Ent Ax Γ Hs (φ.ren (nilRen Γ)) :=
  Ent.ofProv (Prov.ren (nilRen Γ) h)

end Chain

/-! ### β-conversion in context -/

section BetaCongr
variable {n : Nat} {Γ : Ctx n}

theorem BetaEq.appL {K L : Cat n} {f f' : Tm Γ (.arr K L)} (a : Tm Γ K) (h : BetaEq f f') :
    BetaEq (.app f a) (.app f' a) := by
  induction h with
  | refl => exact .refl _
  | step s => exact .step (.appL a s)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem BetaEq.appR {K L : Cat n} (f : Tm Γ (.arr K L)) {a a' : Tm Γ K} (h : BetaEq a a') :
    BetaEq (.app f a) (.app f a') := by
  induction h with
  | refl => exact .refl _
  | step s => exact .step (.appR f s)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem BetaEq.lamC (σ : Ty n) {L : Cat n} {b b' : Tm (.ext Γ σ) L} (h : BetaEq b b') :
    BetaEq (.lam σ b) (.lam σ b') := by
  induction h with
  | refl => exact .refl _
  | step s => exact .step (.lam σ s)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem BetaEq.tlamC {K : Cat (n+1)} {b b' : Tm (.text Γ) K} (h : BetaEq b b') :
    BetaEq (Tm.tlam b) (Tm.tlam b') := by
  induction h with
  | refl => exact .refl _
  | step s => exact .step (.tlam s)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem BetaEq.app2 {K L : Cat n} {f f' : Tm Γ (.arr K L)} {a a' : Tm Γ K} (h1 : BetaEq f f') (h2 : BetaEq a a') :
    BetaEq (.app f a) (.app f' a') := (BetaEq.appL a h1).trans (BetaEq.appR f' h2)

theorem BetaEq.imp {φ φ' ψ ψ' : Fm Γ} (h1 : BetaEq φ φ') (h2 : BetaEq ψ ψ') : BetaEq (φ.imp ψ) (φ'.imp ψ') :=
  BetaEq.app2 (BetaEq.appR _ h1) h2

theorem BetaEq.tbeta {K : Cat (n+1)} (b : Tm (.text Γ) K) (σ : Ty n) : BetaEq (Tm.tapp (Tm.tlam b) σ) (b.tinst σ) :=
  .step (.tbeta b σ)

end BetaCongr

/-! ### Propositional and quantifier rules under hypotheses -/

section Rules
variable {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)}

theorem Ent.mp2 {A B C : Fm Γ} (h : Ent Ax Γ Hs (A.imp (B.imp C))) (ha : Ent Ax Γ Hs A) (hb : Ent Ax Γ Hs B) :
    Ent Ax Γ Hs C := Ent.mp (Ent.mp h ha) hb

theorem Ent.andI {A B : Fm Γ} (ha : Ent Ax Γ Hs A) (hb : Ent Ax Γ Hs B) : Ent Ax Γ Hs (A.conj B) :=
  Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.conj (.atom 0) (.atom 1)))) (v2 A B)
    (fun _ x y => ⟨x, y⟩)) ha hb

theorem Ent.andE1 {A B : Fm Γ} (h : Ent Ax Γ Hs (A.conj B)) : Ent Ax Γ Hs A :=
  Ent.mp (Ent.taut (.imp (.conj (.atom 0) (.atom 1)) (.atom 0)) (v2 A B) (fun _ x => x.1)) h

theorem Ent.andE2 {A B : Fm Γ} (h : Ent Ax Γ Hs (A.conj B)) : Ent Ax Γ Hs B :=
  Ent.mp (Ent.taut (.imp (.conj (.atom 0) (.atom 1)) (.atom 1)) (v2 A B) (fun _ x => x.2)) h

theorem Ent.iffMpr {A B : Fm Γ} (h : Ent Ax Γ Hs (A.iff B)) (hb : Ent Ax Γ Hs B) : Ent Ax Γ Hs A :=
  Ent.mp2 (Ent.taut (.imp (.iff (.atom 0) (.atom 1)) (.imp (.atom 1) (.atom 0))) (v2 A B) (fun _ x => x.mpr)) h hb

theorem Ent.iffMp {A B : Fm Γ} (h : Ent Ax Γ Hs (A.iff B)) (ha : Ent Ax Γ Hs A) : Ent Ax Γ Hs B :=
  Ent.mp2 (Ent.taut (.imp (.iff (.atom 0) (.atom 1)) (.imp (.atom 0) (.atom 1))) (v2 A B) (fun _ x => x.mp)) h ha

/-- Modus tollens: from `A → ¬B` and `B`, infer `¬A`. -/
theorem Ent.mtN {A B : Fm Γ} (h : Ent Ax Γ Hs (A.imp B.neg)) (hb : Ent Ax Γ Hs B) : Ent Ax Γ Hs A.neg :=
  Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.neg (.atom 1))) (.imp (.atom 1) (.neg (.atom 0)))) (v2 A B)
    (fun _ f b a => f a b)) h hb

/-- From `B` and `¬B` (under the last hypothesis `A`), infer `¬A`. -/
theorem Ent.notI {A B : Fm Γ} (h1 : Ent Ax Γ (Hs ++ [A]) B) (h2 : Ent Ax Γ (Hs ++ [A]) B.neg) : Ent Ax Γ Hs A.neg :=
  Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.atom 1)) (.imp (.imp (.atom 0) (.neg (.atom 1))) (.neg (.atom 0))))
    (v2 A B) (fun _ f g a => g a (f a))) (Ent.intro h1) (Ent.intro h2)

/-- Proof by contradiction. -/
theorem Ent.byContra {A B : Fm Γ} (h1 : Ent Ax Γ (Hs ++ [A.neg]) B) (h2 : Ent Ax Γ (Hs ++ [A.neg]) B.neg) :
    Ent Ax Γ Hs A :=
  Ent.mp2 (Ent.taut (.imp (.imp (.neg (.atom 0)) (.atom 1)) (.imp (.imp (.neg (.atom 0)) (.neg (.atom 1))) (.atom 0)))
    (v2 A B) (fun _ f g => Classical.byContradiction fun na => g na (f na))) (Ent.intro h1) (Ent.intro h2)

/-- From `B` and `¬B`, anything. -/
theorem Ent.absurd {A B : Fm Γ} (h1 : Ent Ax Γ Hs B) (h2 : Ent Ax Γ Hs B.neg) : Ent Ax Γ Hs A :=
  Ent.mp2 (Ent.taut (.imp (.atom 1) (.imp (.neg (.atom 1)) (.atom 0))) (v2 A B) (fun _ b nb => (nb b).elim)) h1 h2

/-- `∃`-introduction. -/
theorem Ent.exI {σ : Ty n} {φ : Fm (.ext Γ σ)} (κ : Tm Γ σ.1) (h : Ent Ax Γ Hs (φ.subst0 κ)) :
    Ent Ax Γ Hs (Tm.ex σ φ) :=
  Ent.iffMpr (Ent.ofProv (Prov.dualEx σ φ)) (Ent.mtN (Ent.ofProv (Prov.instAll σ φ.neg κ)) h)

/-- `∃`-elimination: if `χ` follows from `φ(x)` for a fresh `x`, then `χ` follows from `∃x φ(x)`. -/
theorem Ent.exE {σ : Ty n} {φ : Fm (.ext Γ σ)} {χ : Fm Γ} (h : Ent Ax Γ Hs (Tm.ex σ φ))
    (H : Ent Ax (.ext Γ σ) (Hs.map (fun h => h.wk σ) ++ [φ]) (χ.wk σ)) : Ent Ax Γ Hs χ := by
  -- `∀x(¬χ → ¬φ)`
  have h1 : Ent Ax Γ Hs (Tm.all σ ((χ.neg.wk σ).imp φ.neg)) :=
    Ent.gen σ (Ent.mp (Ent.taut (.imp (.imp (.atom 0) (.atom 1)) (.imp (.neg (.atom 1)) (.neg (.atom 0))))
      (v2 φ (χ.wk σ)) (fun _ f nb a => nb (f a))) (Ent.intro H))
  have h2 : Ent Ax Γ Hs (χ.neg.imp (Tm.all σ φ.neg)) := Ent.mp (Ent.ofProv (Prov.distAll σ χ.neg φ.neg)) h1
  have h3 : Ent Ax Γ Hs (Tm.all σ φ.neg).neg := Ent.iffMp (Ent.ofProv (Prov.dualEx σ φ)) h
  exact Ent.mp2 (Ent.taut (.imp (.imp (.neg (.atom 0)) (.atom 1)) (.imp (.neg (.atom 1)) (.atom 0)))
    (v2 χ (Tm.all σ φ.neg)) (fun _ f nb => Classical.byContradiction fun nc => nb (f nc))) h2 h3

end Rules

/-! ### Basic theory: Lemma 9 and Theorem 2 -/

section Basic
variable {S : Fm Ctx.nil → Prop}

abbrev Δ1 : Ctx 1 := Ctx.nil.text
abbrev Δ2 : Ctx 2 := Ctx.nil.text.text
abbrev Δ3 : Ctx 3 := Ctx.nil.text.text.text

/-- (Sym≈), Lemma 9: with `Q = λγ.(γ ≈ α)` in LL≈, and Ref≈. -/
theorem d_SymTeq : Prov S Ctx.nil SymTeq := by
  have hQ : Ent S Δ2 [] (LLTeq (Tm.tlam (Tm.teq tv0 tv2))) := Ent.ofProv (Prov.llTeq _)
  have h1 : Ent S Δ2 [] ((Tm.teq tv1 tv0).imp ((Tm.teq tv1 tv1).imp (Tm.teq tv0 tv1))) :=
    Ent.beta ((hQ.tinst tv1).tinst tv0) (BetaEq.imp (.refl _) (BetaEq.imp (BetaEq.tbeta _ _) (BetaEq.tbeta _ _)))
  have hr : Ent S Δ2 [] (Tm.teq tv1 tv1) := (Ent.closed (Γ := Δ2) Prov.refTeq).tinst tv1
  have h2 : Ent S Δ2 [] ((Tm.teq tv1 tv0).imp (Tm.teq tv0 tv1)) :=
    Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2))) (.imp (.atom 1) (.imp (.atom 0) (.atom 2))))
      (v3 (Tm.teq tv1 tv0) (Tm.teq tv1 tv1) (Tm.teq tv0 tv1)) (fun _ f b a => f a b)) h1 hr
  exact Ent.toProv (Ent.tgen (Ent.tgen h2))

/-- (Trans≈), Lemma 9: with `Q = λδ.(α ≈ δ)` in LL≈. -/
theorem d_TransTeq : Prov S Ctx.nil TransTeq := by
  have hQ : Ent S Δ3 [] (LLTeq (Tm.tlam (Tm.teq tv3 tv0))) := Ent.ofProv (Prov.llTeq _)
  have h1 : Ent S Δ3 [] ((Tm.teq tv1 tv0).imp ((Tm.teq tv2 tv1).imp (Tm.teq tv2 tv0))) :=
    Ent.beta ((hQ.tinst tv1).tinst tv0) (BetaEq.imp (.refl _) (BetaEq.imp (BetaEq.tbeta _ _) (BetaEq.tbeta _ _)))
  have h2 : Ent S Δ3 [] (((Tm.teq tv2 tv1).conj (Tm.teq tv1 tv0)).imp (Tm.teq tv2 tv0)) :=
    Ent.mp (Ent.taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2))) (.imp (.conj (.atom 1) (.atom 0)) (.atom 2)))
      (v3 (Tm.teq tv1 tv0) (Tm.teq tv2 tv1) (Tm.teq tv2 tv0)) (fun _ f h => f h.2 h.1)) h1
  exact Ent.toProv (Ent.tgen (Ent.tgen (Ent.tgen h2)))

/-- Theorem 2 (Link): with `Q = λγ.∀_α x ∃_γ y (x ≡ y)` in LL≈, and Ref≡. -/
theorem d_Link : Prov S Ctx.nil Link := by
  have hQ : Ent S Δ2 [] (LLTeq (Tm.tlam (Tm.all tv2 (Tm.ex tv0 (Tm.eqv tv2 tv0 (.var (.there .here)) (.var .here))))))
    := Ent.ofProv (Prov.llTeq _)
  have h1 : Ent S Δ2 [] ((Tm.teq tv1 tv0).imp
      ((Tm.all tv1 (Tm.ex tv1 (Tm.eqv tv1 tv1 (.var (.there .here)) (.var .here)))).imp
       (Tm.all tv1 (Tm.ex tv0 (Tm.eqv tv1 tv0 (.var (.there .here)) (.var .here)))))) :=
    Ent.beta ((hQ.tinst tv1).tinst tv0) (BetaEq.imp (.refl _) (BetaEq.imp (BetaEq.tbeta _ _) (BetaEq.tbeta _ _)))
  -- `∀_α x ∃_α y (x ≡ y)`, from Ref≡ with `y := x`
  have hr : Ent S (.ext Δ2 tv1) [] (Tm.eqv tv1 tv1 (.var .here) (.var .here)) :=
    ((Ent.closed (Γ := .ext Δ2 tv1) Prov.refEqv).tinst tv1).inst (.var .here)
  have h2 : Ent S Δ2 [] (Tm.all tv1 (Tm.ex tv1 (Tm.eqv tv1 tv1 (.var (.there .here)) (.var .here)))) :=
    Ent.gen tv1 (Ent.exI (.var .here) hr)
  exact Ent.toProv (Ent.tgen (Ent.tgen (Ent.mp2 (Ent.taut
    (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2))) (.imp (.atom 1) (.imp (.atom 0) (.atom 2)))) (v3 _ _ _)
    (fun _ f b a => f a b)) h1 h2)))

end Basic
/-! ### More rules -/

section Rules2
variable {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)}

theorem chain_wk (σ : Ty n) (Hs : List (Fm Γ)) (φ : Fm Γ) :
    chain (Hs.map (fun h => h.wk σ)) (φ.wk σ) = (chain Hs φ).wk σ := by
  induction Hs with
  | nil => rfl
  | cons h hs ih => show (h.wk σ).imp (chain (hs.map _) (φ.wk σ)) = _; rw [ih]; rfl

theorem chain_twk (Hs : List (Fm Γ)) (φ : Fm Γ) :
    chain (Hs.map (fun h => (h.twk : Fm (.text Γ)))) (φ.twk : Fm (.text Γ)) = ((chain Hs φ).twk : Fm (.text Γ)) := by
  induction Hs with
  | nil => rfl
  | cons h hs ih => show (h.twk : Fm (.text Γ)).imp (chain (hs.map _) φ.twk) = _; rw [ih]; rfl

/-- Discarding a term variable which occurs in neither the hypotheses nor the conclusion. -/
theorem Ent.strengthen (σ : Ty n) {φ : Fm Γ} (H : Ent Ax (.ext Γ σ) (Hs.map (fun h => h.wk σ)) (φ.wk σ)) :
    Ent Ax Γ Hs φ := by
  unfold Ent at *; rw [chain_wk] at H; exact Prov.strengthen σ H

/-- Discarding a type variable which occurs in neither the hypotheses nor the conclusion. -/
theorem Ent.tstrengthen {φ : Fm Γ}
    (H : Ent Ax (.text Γ) (Hs.map (fun h => (h.twk : Fm (.text Γ)))) (φ.twk : Fm (.text Γ))) : Ent Ax Γ Hs φ := by
  unfold Ent at *; rw [chain_twk] at H; exact Prov.tstrengthen H

/-- `𝔼`-introduction. -/
theorem Ent.texI {φ : Fm (.text Γ)} (σ : Ty n) (h : Ent Ax Γ Hs (φ.tinst σ)) : Ent Ax Γ Hs (Tm.tex φ) :=
  Ent.iffMpr (Ent.ofProv (Prov.dualTEx φ)) (Ent.mtN (Ent.ofProv (Prov.instTAll φ.neg σ)) h)

/-- `𝔼`-elimination. -/
theorem Ent.texE {φ : Fm (.text Γ)} {χ : Fm Γ} (h : Ent Ax Γ Hs (Tm.tex φ))
    (H : Ent Ax (.text Γ) (Hs.map (fun h => (h.twk : Fm (.text Γ))) ++ [φ]) (χ.twk : Fm (.text Γ))) : Ent Ax Γ Hs χ := by
  have h1 : Ent Ax Γ Hs (Tm.tall (((χ.neg).twk : Fm (.text Γ)).imp φ.neg)) :=
    Ent.tgen (Ent.mp (Ent.taut (.imp (.imp (.atom 0) (.atom 1)) (.imp (.neg (.atom 1)) (.neg (.atom 0))))
      (v2 φ (χ.twk : Fm (.text Γ))) (fun _ f nb a => nb (f a))) (Ent.intro H))
  have h2 : Ent Ax Γ Hs (χ.neg.imp (Tm.tall φ.neg)) := Ent.mp (Ent.ofProv (Prov.distTAll χ.neg φ.neg)) h1
  have h3 : Ent Ax Γ Hs (Tm.tall φ.neg).neg := Ent.iffMp (Ent.ofProv (Prov.dualTEx φ)) h
  exact Ent.mp2 (Ent.taut (.imp (.imp (.neg (.atom 0)) (.atom 1)) (.imp (.neg (.atom 1)) (.atom 0)))
    (v2 χ (Tm.tall φ.neg)) (fun _ f nb => Classical.byContradiction fun nc => nb (f nc))) h2 h3

/-- The last hypothesis. -/
theorem Ent.last {A : Fm Γ} : Ent Ax Γ (Hs ++ [A]) A := by
  unfold Ent; rw [chain_append]; exact Ent.ofProv (I A)

/-- A sentence which is one of the extra axioms may be used in any context. -/
theorem Ent.axm {φ : Fm Ctx.nil} (h : Ax φ) : Ent Ax Γ Hs (φ.ren (nilRen Γ)) := Ent.closed (Prov.ax h)

/-- `⊤`. -/
theorem Ent.top : Ent Ax Γ Hs topF := by
  have h1 : Ent Ax Γ ([] ++ [botF]) botF := Ent.last
  have h2 : Ent Ax Γ ([] ++ [botF]) (botF (Γ := Γ)).neg := Ent.inst (σ := tyT) h1 botF.neg
  exact Ent.ofProv (Ent.notI h1 h2)

end Rules2

/-! ### Consequences of LL≡, and the congruence family -/

section Cong
variable {S : Fm Ctx.nil → Prop}

abbrev Δ4 : Ctx 4 := Ctx.nil.text.text.text.text
abbrev tv4' {n : Nat} : Ty (n+5) := tvar (fs (fs (fs (fs fz))))

/-- (Truth) follows from LL≡: the instance at `t` with `λp.p` for `F`. -/
theorem d_Truth (hLL : S LLEqv) : Prov S Ctx.nil Truth := by
  have h0 := ((Ent.axm (Γ := (Ctx.nil.ext tyT).ext tyT) (Hs := []) hLL).tinst tyT).inst (.var (.there .here))
  have h1 := Ent.inst h0 (.var .here)
  have h2 : Ent S ((Ctx.nil.ext tyT).ext tyT) ([] ++ [Tm.eqv tyT tyT (.var (.there .here)) (.var .here)])
      ((Tm.var (.there .here)).imp (Tm.var .here)) := by
    have h3 := Ent.inst (Ent.mp (Ent.weaken h1) Ent.last) (.lam tyT (.var .here))
    exact Ent.beta h3 (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  exact Ent.toProv (Ent.gen tyT (Ent.gen tyT (Ent.intro h2)))

/-- Lemma 13: `⊤ ≢ ⊥` follows from LL≡. -/
theorem d_TopBot (hLL : S LLEqv) : Prov S Ctx.nil TopBot := by
  have h0 := Ent.inst (Ent.inst ((Ent.ofProv (Γ := Ctx.nil) (Hs := [Tm.eqv tyT tyT topF botF]) (Prov.ax hLL)).tinst tyT) topF) botF
  have h1 := Ent.inst (Ent.mp h0 (Ent.hyp _ 0 (by decide))) (.lam tyT (.var .here))
  have h2 : Ent S Ctx.nil ([] ++ [Tm.eqv tyT tyT topF botF]) (topF.imp botF) :=
    Ent.beta h1 (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  have h3 : Ent S Ctx.nil ([] ++ [Tm.eqv tyT tyT topF botF]) botF := Ent.mp h2 Ent.top
  exact Ent.toProv (Ent.notI h3 Ent.top)

set_option maxHeartbeats 4000000 in
/-- Theorem 27(a): PCong follows from Cong (with Ref≡). -/
theorem d_PCong (hC : S Cong) : Prov S Ctx.nil PCong := by
  -- context: α γ δ, f : α→γ, g : α→δ, x : α
  have h0 := (((((Ent.axm (Γ := (((Δ3.ext (tv2.arrow tv1)).ext (tv2.arrow tv0)).ext tv2)) (Hs := []) hC).tinst tv2).tinst tv2).tinst tv1).tinst tv0)
  have h1 := Ent.inst (Ent.inst (Ent.inst (Ent.inst h0 (.var (.there (.there .here)))) (.var (.there .here))) (.var .here)) (.var .here)
  have hr := ((Ent.closed (Γ := (((Δ3.ext (tv2.arrow tv1)).ext (tv2.arrow tv0)).ext tv2)) (Hs := []) (Ax := S)
    Prov.refEqv).tinst tv2).inst (.var .here)
  have h2 := Ent.mp2 (Ent.taut (.imp (.imp (.conj (.atom 0) (.atom 1)) (.atom 2)) (.imp (.atom 1) (.imp (.atom 0) (.atom 2))))
    (v3 _ _ _) (fun _ f b a => f ⟨a, b⟩)) h1 hr
  exact Ent.toProv (Ent.tgen (Ent.tgen (Ent.tgen (Ent.gen (tv2.arrow tv1) (Ent.gen (tv2.arrow tv0) (Ent.gen tv2 h2))))))

/-- Recovery follows from Inj≈. -/
theorem d_Recovery (hI : S Inj) : Prov S Ctx.nil Recovery := by
  have h0 := ((((Ent.axm (Γ := Δ4) (Hs := []) hI).tinst tv3).tinst tv2).tinst tv1).tinst tv0
  refine Ent.toProv (Ent.tgen (Ent.tgen (Ent.tgen (Ent.tgen ?_))))
  exact Ent.mp (Ent.taut (.imp (.imp (.atom 0) (.conj (.atom 1) (.atom 2))) (.imp (.conj (.atom 0) (.atom 1)) (.atom 2)))
    (v3 _ _ _) (fun _ f h => (f h.1).2)) h0

abbrev C22 : Ctx 1 := ((Δ1.ext tv0).ext tv0).ext tv0.pred
abbrev E22 : Fm ((Δ1.ext tv0).ext tv0) := Tm.eqv tv0 tv0 (.var (.there .here)) (.var .here)
abbrev E22' : Fm C22 := Tm.eqv tv0 tv0 (.var (.there (.there .here))) (.var (.there .here))
abbrev Fx22 : Fm C22 := .app (.var .here) (.var (.there (.there .here)))
abbrev Fy22 : Fm C22 := .app (.var .here) (.var (.there .here))

set_option maxHeartbeats 4000000 in
/-- Theorem 22: LL≡ follows from Cong and Truth. -/
theorem d_LLEqv_of_Cong_Truth (hC : S Cong) (hT : S Truth) : Prov S Ctx.nil LLEqv := by
  have hc0 : Ent S C22 [E22', Fx22] _ := ((((Ent.axm (Γ := C22) (Hs := [E22', Fx22]) hC).tinst tv0).tinst tv0).tinst tyT).tinst tyT
  have hc : Ent S C22 [E22', Fx22] (((Tm.eqv tv0.pred tv0.pred (.var .here) (.var .here)).conj E22').imp
      (Tm.eqv tyT tyT Fx22 Fy22)) :=
    Ent.inst (Ent.inst (Ent.inst (Ent.inst hc0 (.var .here)) (.var .here)) (.var (.there (.there .here)))) (.var (.there .here))
  have hr : Ent S C22 [E22', Fx22] (Tm.eqv tv0.pred tv0.pred (.var .here) (.var .here)) :=
    ((Ent.closed (Γ := C22) (Hs := [E22', Fx22]) (Ax := S) Prov.refEqv).tinst tv0.pred).inst (.var .here)
  have he : Ent S C22 [E22', Fx22] E22' := Ent.hyp _ 0 (by decide)
  have hfx : Ent S C22 [E22', Fx22] Fx22 := Ent.hyp _ 1 (by decide)
  have ht : Ent S C22 [E22', Fx22] ((Tm.eqv tyT tyT Fx22 Fy22).imp (Fx22.imp Fy22)) :=
    Ent.inst (Ent.inst (Ent.axm (Γ := C22) (Hs := [E22', Fx22]) hT) Fx22) Fy22
  have h2 : Ent S C22 ([E22'] ++ [Fx22]) Fy22 := Ent.mp2 ht (Ent.mp hc (Ent.andI hr he)) hfx
  have h3 : Ent S ((Δ1.ext tv0).ext tv0) ([] ++ [E22]) (Tm.all tv0.pred (Fx22.imp Fy22)) :=
    Ent.gen (Hs := [] ++ [E22]) tv0.pred (Ent.intro (Hs := [E22']) h2)
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen (Hs := []) tv0 (Ent.gen (Hs := []) tv0 (Ent.intro (Hs := []) h3))))

end Cong

/-! ### Disjoint and LL≡-Poly: Theorem 11, first half -/

section Disj
variable {S : Fm Ctx.nil → Prop}

/-- The predicate `λγ.λz.(γ ≈ α)`, with `α` free. -/
def PredA : Tm Δ1 (.pi (.arr (.var fz) .t)) := Tm.tlam (Tm.lam tv0 (Tm.teq tv0 tv1))

abbrev C11 : Ctx 2 := (Δ2.ext tv1).ext tv0
abbrev Exy11 : Fm C11 := Tm.eqv tv1 tv0 (.var (.there .here)) (.var .here)

/-- Theorem 11, first half: Disjoint follows from the instances of LL≡-Poly (here, the one for
`λγ.λz.(γ ≈ α)`), with Ref≈ and Sym≈. -/
theorem d_Disjoint_of_LLPoly (hP : S (Tm.tall (LLPoly PredA))) : Prov S Ctx.nil Disjoint := by
  have h0 := Ent.inst (Ent.inst ((((Ent.axm (Γ := C11) (Hs := []) hP).tinst tv1).tinst tv1).tinst tv0) (.var (.there .here))) (.var .here)
  have h1 : Ent S C11 [] (Exy11.imp ((Tm.teq tv1 tv1).imp (Tm.teq tv0 tv1))) :=
    Ent.beta h0 (BetaEq.imp (.refl _) (BetaEq.imp
      ((BetaEq.appL _ (BetaEq.tbeta _ _)).trans (.step (.beta _ _)))
      ((BetaEq.appL _ (BetaEq.tbeta _ _)).trans (.step (.beta _ _)))))
  have hr : Ent S C11 [] (Tm.teq tv1 tv1) := (Ent.closed (Γ := C11) (Hs := []) (Ax := S) Prov.refTeq).tinst tv1
  have hs : Ent S C11 [] ((Tm.teq tv0 tv1).imp (Tm.teq tv1 tv0)) :=
    ((Ent.closed (Γ := C11) (Hs := []) (Ax := S) d_SymTeq).tinst tv0).tinst tv1
  have h2 : Ent S C11 [] ((Tm.teq tv1 tv0).neg.imp Exy11.neg) :=
    Ent.mp2 (Ent.mp (Ent.taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2)))
      (.imp (.atom 1) (.imp (.imp (.atom 2) (.atom 3)) (.imp (.neg (.atom 3)) (.neg (.atom 0))))))
      (v4 Exy11 (Tm.teq tv1 tv1) (Tm.teq tv0 tv1) (Tm.teq tv1 tv0))
      (fun _ f r g nb a => nb (g (f a r)))) h1) hr hs
  have h3 : Ent S C11 ([] ++ [(Tm.teq tv1 tv0).neg]) Exy11.neg := Ent.mp (Ent.weaken h2) Ent.last
  have h4 : Ent S Δ2 ([] ++ [(Tm.teq tv1 tv0).neg]) (Tm.all tv1 (Tm.all tv0 Exy11.neg)) :=
    Ent.gen (Hs := [] ++ [(Tm.teq tv1 tv0).neg]) tv1 (Ent.gen (Hs := [(Tm.teq tv1 tv0).neg]) tv0 h3)
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.intro (Hs := []) h4)))

end Disj


/-! ### Cantor: Theorem 6 -/

section Cantor
variable {S : Fm Ctx.nil → Prop}

/-- `R = λx:α.∃_{α→t}F (F ≡ x ∧ ¬F x)`, in any context with one type variable. -/
abbrev RC (Γ : Ctx 1) : Tm Γ (.arr (.var fz) .t) :=
  Tm.lam tv0 (Tm.ex tv0.pred (Tm.conj (Tm.eqv tv0.pred tv0 (.var .here) (.var (.there .here)))
    (Tm.neg (.app (.var .here) (.var (.there .here))))))

abbrev Cy : Ctx 1 := Δ1.ext tv0
abbrev CF : Ctx 1 := Cy.ext tv0.pred
/-- `R ≡ y` and `R y`, in the context `α, y`. -/
abbrev H1 : Fm Cy := Tm.eqv tv0.pred tv0 (RC Cy) (.var .here)
abbrev Ry : Fm Cy := .app (RC Cy) (.var .here)
abbrev E1 : Fm Cy := Tm.ex tv0.pred (Tm.conj (Tm.eqv tv0.pred tv0 (.var .here) (.var (.there .here)))
    (Tm.neg (.app (.var .here) (.var (.there .here)))))
/-- The same, in the context `α, y, F`. -/
abbrev H1' : Fm CF := Tm.eqv tv0.pred tv0 (RC CF) (.var (.there .here))
abbrev Ry' : Fm CF := .app (RC CF) (.var (.there .here))
abbrev Fy : Fm CF := .app (.var .here) (.var (.there .here))
abbrev Fiy : Fm CF := Tm.eqv tv0.pred tv0 (.var .here) (.var (.there .here))

set_option maxHeartbeats 4000000 in
theorem cantor_step (hLL : S LLEqv) : Ent S CF [H1', Ry', Fiy.conj Fy.neg] botF := by
  have hφ : Ent S CF [H1', Ry', Fiy.conj Fy.neg] (Fiy.conj Fy.neg) := Ent.hyp _ 2 (by decide)
  have hFy : Ent S CF [H1', Ry', Fiy.conj Fy.neg] Fiy := Ent.andE1 hφ
  have hnF : Ent S CF [H1', Ry', Fiy.conj Fy.neg] Fy.neg := Ent.andE2 hφ
  have hH : Ent S CF [H1', Ry', Fiy.conj Fy.neg] H1' := Ent.hyp _ 0 (by decide)
  have hR : Ent S CF [H1', Ry', Fiy.conj Fy.neg] Ry' := Ent.hyp _ 1 (by decide)
  -- y ≡ F, by Sym≡
  have hsym : Ent S CF [H1', Ry', Fiy.conj Fy.neg]
      (Fiy.imp (Tm.eqv tv0 tv0.pred (.var (.there .here)) (.var .here))) :=
    Ent.inst (Ent.inst (((Ent.closed (Γ := CF) (Hs := [H1', Ry', Fiy.conj Fy.neg]) (Ax := S) Prov.symEqv).tinst tv0.pred).tinst tv0)
      (.var .here)) (.var (.there .here))
  have hyF := Ent.mp hsym hFy
  -- R ≡ F, by Trans≡
  have htr : Ent S CF [H1', Ry', Fiy.conj Fy.neg]
      ((H1'.conj (Tm.eqv tv0 tv0.pred (.var (.there .here)) (.var .here))).imp
        (Tm.eqv tv0.pred tv0.pred (RC CF) (.var .here))) :=
    Ent.inst (Ent.inst (Ent.inst ((((Ent.closed (Γ := CF) (Hs := [H1', Ry', Fiy.conj Fy.neg]) (Ax := S) Prov.transEqv).tinst tv0.pred).tinst tv0).tinst tv0.pred)
      (RC CF)) (.var (.there .here))) (.var .here)
  have hRF := Ent.mp htr (Ent.andI hH hyF)
  -- LL≡ with `λZ. Z y`: R y → F y
  have hll : Ent S CF [H1', Ry', Fiy.conj Fy.neg]
      ((Tm.eqv tv0.pred tv0.pred (RC CF) (.var .here)).imp
        (Tm.all tv0.pred.pred (Tm.imp (.app (.var .here) (RC (CF.ext tv0.pred.pred)))
          (.app (.var .here) (.var (.there .here)))))) :=
    Ent.inst (Ent.inst ((Ent.axm (Γ := CF) (Hs := [H1', Ry', Fiy.conj Fy.neg]) hLL).tinst tv0.pred) (RC CF)) (.var .here)
  have h2 : Ent S CF [H1', Ry', Fiy.conj Fy.neg] (Ry'.imp Fy) :=
    Ent.beta (Ent.inst (Ent.mp hll hRF) (Tm.lam tv0.pred (.app (.var .here) (.var (.there (.there .here))))))
      (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  exact Ent.absurd (Ent.mp h2 hR) hnF

set_option maxHeartbeats 4000000 in
/-- Theorem 6 (Cantor), from LL≡. -/
theorem d_Cantor (hLL : S LLEqv) : Prov S Ctx.nil Cantor := by
  -- (a) R ≡ y ⊢ ¬ R y
  have hE : Ent S Cy ([H1] ++ [Ry]) E1 := Ent.beta (Ent.last (Hs := [H1])) (.step (.beta _ _))
  have hbot : Ent S Cy ([H1] ++ [Ry]) botF :=
    Ent.exE (Hs := [H1] ++ [Ry]) hE (cantor_step hLL)
  have ha : Ent S Cy ([] ++ [H1]) Ry.neg := Ent.notI (Hs := [H1]) hbot Ent.top
  -- (b) R ≡ y ⊢ R y
  have hb : Ent S Cy ([] ++ [H1]) Ry :=
    Ent.beta (Ent.exI (σ := tv0.pred) (φ := Fiy.conj Fy.neg) (RC Cy) (Ent.andI (Ent.last (Hs := [])) ha)) (.symm (.step (.beta _ _)))
  have hn : Ent S Cy [] H1.neg := Ent.notI (Hs := []) hb ha
  have hall : Ent S Δ1 [] (Tm.all tv0 (Tm.eqv tv0.pred tv0 (RC Cy) (.var .here)).neg) := Ent.gen (Hs := []) tv0 hn
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.exI (σ := tv0.pred) (RC Δ1) hall))

end Cantor

/-! ### Corollary 6, Theorem 26, and two inconsistencies -/

section Hae
variable {S : Fm Ctx.nil → Prop}

/-- `∀α ¬(α ≈ α→t)`. -/
abbrev NoSelfF : Fm Ctx.nil := Tm.tall (Tm.teq tv0 tv0.pred).neg

abbrev NS {Γ : Ctx 1} : Fm Γ := Tm.teq tv0 tv0.pred
abbrev CG : Ctx 1 := Δ1.ext tv0.pred
abbrev CGy : Ctx 1 := CG.ext tv0
abbrev AllNotG : Fm CG := Tm.all tv0 (Tm.eqv tv0.pred tv0 (.var (.there .here)) (.var .here)).neg
abbrev AllNotG' : Fm CGy := Tm.all tv0 (Tm.eqv tv0.pred tv0 (.var (.there (.there .here))) (.var .here)).neg
abbrev GeqY : Fm CGy := Tm.eqv tv0.pred tv0 (.var (.there .here)) (.var .here)
abbrev ExY : Fm CG := Tm.ex tv0 (Tm.eqv tv0.pred tv0 (.var (.there .here)) (.var .here))

set_option maxHeartbeats 4000000 in
/-- Corollary 6: no type is identical to the type of its properties (from Cantor, Link, Sym≈). -/
theorem d_NoSelf (hCan : S Cantor) : Prov S Ctx.nil NoSelfF := by
  -- inside: G : α→t with ∀y ¬(G ≡ y); and hypothesis α ≈ α→t
  have hN : Ent S CG [NS, AllNotG] NS := Ent.hyp _ 0 (by decide)
  have hsym : Ent S CG [NS, AllNotG] (NS.imp (Tm.teq tv0.pred tv0)) :=
    ((Ent.closed (Γ := CG) (Hs := [NS, AllNotG]) (Ax := S) d_SymTeq).tinst tv0).tinst tv0.pred
  have hlink : Ent S CG [NS, AllNotG] ((Tm.teq tv0.pred tv0).imp
      (Tm.all tv0.pred (Tm.ex tv0 (Tm.eqv tv0.pred tv0 (.var (.there .here)) (.var .here))))) :=
    ((Ent.closed (Γ := CG) (Hs := [NS, AllNotG]) (Ax := S) d_Link).tinst tv0.pred).tinst tv0
  have hex : Ent S CG [NS, AllNotG] ExY := Ent.inst (Ent.mp hlink (Ent.mp hsym hN)) (.var .here)
  have hinner : Ent S CGy [NS, AllNotG', GeqY] botF := by
    have hA : Ent S CGy [NS, AllNotG', GeqY] AllNotG' := Ent.hyp _ 1 (by decide)
    have hB : Ent S CGy [NS, AllNotG', GeqY] GeqY := Ent.hyp _ 2 (by decide)
    exact Ent.absurd hB (Ent.inst hA (.var .here))
  have hbot1 : Ent S CG ([NS] ++ [AllNotG]) botF := Ent.exE (Hs := [NS, AllNotG]) hex hinner
  have hcan : Ent S Δ1 [NS] (Tm.ex tv0.pred AllNotG) := (Ent.axm (Γ := Δ1) (Hs := [NS]) hCan).tinst tv0
  have hbot : Ent S Δ1 ([] ++ [NS]) botF := Ent.exE (Hs := [NS]) hcan hbot1
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.notI (Hs := []) hbot Ent.top))

abbrev Cx : Ctx 1 := Δ1.ext tv0
abbrev HaeX : Tm Cx (Cat.arr (Cat.var fz) Cat.t) := Tm.lam tv0 (Tm.eqv tv0 tv0 (.var .here) (.var (.there .here)))

set_option maxHeartbeats 4000000 in
/-- Theorem 26: Twin follows from Haecceitism (with Corollary 6, hence Cantor). -/
theorem d_Twin (hH : S Hae) (hCan : S Cantor) : Prov S Ctx.nil Twin := by
  have hh : Ent S Cx [] (Tm.eqv tv0 tv0.pred (.var .here) HaeX) :=
    Ent.inst ((Ent.axm (Γ := Cx) (Hs := []) hH).tinst tv0) (.var .here)
  have hex : Ent S Cx [] (Tm.ex tv0.pred (Tm.eqv tv0 tv0.pred (.var (.there .here)) (.var .here))) :=
    Ent.exI (σ := tv0.pred) (φ := Tm.eqv tv0 tv0.pred (.var (.there .here)) (.var .here)) HaeX hh
  have hns : Ent S Cx [] (Tm.teq tv0 tv0.pred).neg := (Ent.closed (Γ := Cx) (Hs := []) (Ax := S) (d_NoSelf hCan)).tinst tv0
  have hc : Ent S Cx [] (Tm.tex (Tm.conj (Tm.neg (Tm.teq tv1 tv0))
      (Tm.ex tv0 (Tm.eqv tv1 tv0 (.var (.there (.tthere .here))) (.var .here))))) :=
    Ent.texI tv0.pred (Ent.andI hns hex)
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen (Hs := []) tv0 hc))

abbrev Ψ {Γ : Ctx 1} : Fm Γ := Tm.conj (Tm.neg (Tm.teq tyT tv0)) (Tm.ex tv0 (Tm.eqv tyT tv0 topF (.var .here)))
abbrev C1y : Ctx 1 := Δ1.ext tv0

set_option maxHeartbeats 4000000 in
/-- Twin and Disjoint are jointly inconsistent: take the item ⊤ of type t. -/
theorem d_Twin_Disjoint (hT : S Twin) (hD : S Disjoint) : Prov S Ctx.nil Bot := by
  have htw : Ent S Ctx.nil [] (Tm.tex Ψ) := Ent.inst ((Ent.ofProv (Γ := Ctx.nil) (Hs := []) (Prov.ax hT)).tinst tyT) topF
  have hin : Ent S Δ1 ([] ++ [Ψ]) botF := by
    have hψ : Ent S Δ1 [Ψ] Ψ := Ent.hyp _ 0 (by decide)
    have hd : Ent S Δ1 [Ψ] ((Tm.teq tyT tv0).neg.imp (Tm.all tyT (Tm.all tv0 (Tm.eqv tyT tv0 (.var (.there .here)) (.var .here)).neg))) :=
      ((Ent.axm (Γ := Δ1) (Hs := [Ψ]) hD).tinst tyT).tinst tv0
    have hall : Ent S Δ1 [Ψ] (Tm.all tv0 (Tm.eqv tyT tv0 topF (.var .here)).neg) :=
      Ent.inst (Ent.mp hd (Ent.andE1 hψ)) topF
    have hinner : Ent S C1y [Ψ, Tm.all tv0 (Tm.eqv tyT tv0 topF (.var .here)).neg, Tm.eqv tyT tv0 topF (.var .here)] botF := by
      have hA : Ent S C1y [Ψ, Tm.all tv0 (Tm.eqv tyT tv0 topF (.var .here)).neg, Tm.eqv tyT tv0 topF (.var .here)]
          (Tm.all tv0 (Tm.eqv tyT tv0 topF (.var .here)).neg) := Ent.hyp _ 1 (by decide)
      have hB : Ent S C1y [Ψ, Tm.all tv0 (Tm.eqv tyT tv0 topF (.var .here)).neg, Tm.eqv tyT tv0 topF (.var .here)]
          (Tm.eqv tyT tv0 topF (.var .here)) := Ent.hyp _ 2 (by decide)
      exact Ent.absurd hB (Ent.inst hA (.var .here))
    have hb := Ent.exE (Hs := [Ψ] ++ [Tm.all tv0 (Tm.eqv tyT tv0 topF (.var .here)).neg]) (χ := botF)
      (Ent.weaken (Ent.andE2 hψ)) hinner
    exact Ent.mp (Ent.intro hb) hall
  exact Ent.toProv (Ent.texE (Hs := []) htw hin)

abbrev Ce : Ctx 0 := Ctx.nil.ext tyE
abbrev HaeE : Tm Ce (Cat.arr Cat.e Cat.t) := Tm.lam tyE (Tm.eqv tyE tyE (.var .here) (.var (.there .here)))

set_option maxHeartbeats 4000000 in
/-- Slogan and Haecceitism are jointly inconsistent (observed, not stated in the notes): each entity
would be identical to its haecceity, a property of entities. -/
theorem d_Slogan_Hae (hS : S Slogan) (hH : S Hae) : Prov S Ctx.nil Bot := by
  have hh : Ent S Ce [] (Tm.eqv tyE tyE.pred (.var .here) HaeE) :=
    Ent.inst ((Ent.axm (Γ := Ce) (Hs := []) hH).tinst tyE) (.var .here)
  have hs : Ent S Ce [] (Tm.eqv tyE tyE.pred (.var .here) HaeE).neg :=
    Ent.inst ((Ent.inst (Ent.axm (Γ := Ce) (Hs := []) hS) (.var .here)).tinst tyE) HaeE
  have hb : Ent S Ce [] botF := Ent.absurd hh hs
  exact Ent.toProv (Ent.strengthen (Hs := []) tyE hb)

end Hae

/-! ### Theorem 25: Haecceitism and Cong are incompatible -/

section Thm25
variable {S : Fm Ctx.nil → Prop}

theorem BetaEq.eqvC {n : Nat} {Γ : Ctx n} {σ τ : Ty n} {x x' : Tm Γ σ.1} {y y' : Tm Γ τ.1}
    (h1 : BetaEq x x') (h2 : BetaEq y y') : BetaEq (Tm.eqv σ τ x y) (Tm.eqv σ τ x' y') :=
  BetaEq.app2 (BetaEq.appR _ h1) h2

/-- `a = λy:t.(y ≡ ⊥)`, the haecceity of `⊥`; `b = λz:t.⊤`; and `H_b = λw:t→t.(w ≡ b)`. -/
abbrev a25 {n : Nat} {Γ : Ctx n} : Tm Γ (.arr .t .t) := Tm.lam tyT (Tm.eqv tyT tyT (.var .here) botF)
abbrev b25 {n : Nat} {Γ : Ctx n} : Tm Γ (.arr .t .t) := Tm.lam tyT topF
abbrev Hb25 : Tm Ctx.nil (.arr (.arr .t .t) .t) := Tm.lam tyT.pred (Tm.eqv tyT.pred tyT.pred (.var .here) b25)

set_option maxHeartbeats 8000000 in
/-- Theorem 25: given LL≡, Haecceitism and Cong are jointly inconsistent. -/
theorem d_Hae_Cong (hLL : S LLEqv) (hH : S Hae) (hC : S Cong) : Prov S Ctx.nil Bot := by
  have h1 : Ent S Ctx.nil [] (Tm.eqv tyT tyT.pred botF a25) :=
    Ent.inst ((Ent.ofProv (Prov.ax hH)).tinst tyT) botF
  have h2 : Ent S Ctx.nil [] (Tm.eqv tyT.pred tyT.pred.pred b25 Hb25) :=
    Ent.inst ((Ent.ofProv (Prov.ax hH)).tinst tyT.pred) b25
  have hc : Ent S Ctx.nil [] (((Tm.eqv tyT.pred tyT.pred.pred b25 Hb25).conj (Tm.eqv tyT tyT.pred botF a25)).imp
      (Tm.eqv tyT tyT (.app b25 botF) (.app Hb25 a25))) :=
    Ent.inst (Ent.inst (Ent.inst (Ent.inst ((((((Ent.ofProv (Γ := Ctx.nil) (Hs := []) (Prov.ax hC)).tinst tyT).tinst tyT.pred).tinst tyT).tinst tyT))
      b25) Hb25) botF) a25
  -- ⊤ ≡ (a ≡ b)
  have h3 : Ent S Ctx.nil [] (Tm.eqv tyT tyT topF (Tm.eqv tyT.pred tyT.pred a25 b25)) :=
    Ent.beta (Ent.mp hc (Ent.andI h2 h1)) (BetaEq.eqvC (.step (.beta _ _)) (.step (.beta _ _)))
  -- so a ≡ b, by LL≡ at t with λv.v
  have h4 : Ent S Ctx.nil [] (topF.imp (Tm.eqv tyT.pred tyT.pred a25 b25)) :=
    Ent.beta (Ent.inst (Ent.mp (Ent.inst (Ent.inst ((Ent.ofProv (Prov.ax hLL)).tinst tyT) topF)
      (Tm.eqv tyT.pred tyT.pred a25 b25)) h3) (Tm.lam tyT (.var .here)))
      (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  have hab : Ent S Ctx.nil [] (Tm.eqv tyT.pred tyT.pred a25 b25) := Ent.mp h4 Ent.top
  -- LL≡ at t→t with λX.¬(X ⊤): ¬(⊤ ≡ ⊥) → ¬⊤
  have h5 : Ent S Ctx.nil [] ((Tm.eqv tyT tyT topF botF).neg.imp topF.neg) :=
    Ent.beta (Ent.inst (Ent.mp (Ent.inst (Ent.inst ((Ent.ofProv (Prov.ax hLL)).tinst tyT.pred) a25) b25) hab)
      (Tm.lam tyT.pred (Tm.neg (.app (.var .here) topF))))
      (BetaEq.imp
        ((Step.beta _ _ |> BetaEq.step).trans (BetaEq.appR _ (.step (.beta _ _))))
        ((Step.beta _ _ |> BetaEq.step).trans (BetaEq.appR _ (.step (.beta _ _)))))
  have h6 : Ent S Ctx.nil [] topF.neg := Ent.mp h5 (Ent.ofProv (d_TopBot hLL))
  exact Ent.toProv (Ent.absurd Ent.top h6)

end Thm25

/-! ### Theorem 4: WCong -/

section WCong
variable {S : Fm Ctx.nil → Prop}

/-- Context `α β γ δ, f : α→γ, g : β→δ, x : α, y : β`. -/
abbrev C4 : Ctx 4 := (((Δ4.ext (tv3.arrow tv1)).ext (tv2.arrow tv0)).ext tv3).ext tv2
/-- … extended by `h : α→γ, z : α`. -/
abbrev C4h : Ctx 4 := (C4.ext (tv3.arrow tv1)).ext tv3

abbrev fH : Fm C4h := Tm.eqv (tv3.arrow tv1) (tv3.arrow tv1) (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there .here))
abbrev xZ : Fm C4h := Tm.eqv tv3 tv3 (.var (.there (.there (.there .here)))) (.var .here)
abbrev fx4 : Tm C4h tv1.1 := .app (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there .here))))
abbrev fz4 : Tm C4h tv1.1 := .app (.var (.there (.there (.there (.there (.there .here)))))) (.var .here)
abbrev hz4 : Tm C4h tv1.1 := .app (.var (.there .here)) (.var .here)

set_option maxHeartbeats 8000000 in
/-- `f ≡ h ∧ x ≡ z → f x ≡ h z`, within types, from LL≡ (twice) and Ref≡. -/
theorem wcong_hstep (hLL : S LLEqv) : Ent S C4h ([] ++ [fH.conj xZ]) (Tm.eqv tv1 tv1 fx4 hz4) := by
  have hc : Ent S C4h [fH.conj xZ] (fH.conj xZ) := Ent.hyp _ 0 (by decide)
  have ha : Ent S C4h [fH.conj xZ] ((Tm.eqv tv1 tv1 fx4 fx4).imp (Tm.eqv tv1 tv1 fx4 fz4)) :=
    Ent.beta (Ent.inst (Ent.mp (Ent.inst (Ent.inst ((Ent.axm (Γ := C4h) (Hs := [fH.conj xZ]) hLL).tinst tv3)
        (.var (.there (.there (.there .here))))) (.var .here)) (Ent.andE2 hc))
      (Tm.lam tv3 (Tm.eqv tv1 tv1 (.app (.var (.there (.there (.there (.there (.there (.there .here))))))) (.var (.there (.there (.there (.there .here))))))
        (.app (.var (.there (.there (.there (.there (.there (.there .here))))))) (.var .here)))))
      (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  have hr : Ent S C4h [fH.conj xZ] (Tm.eqv tv1 tv1 fx4 fx4) :=
    ((Ent.closed (Γ := C4h) (Hs := [fH.conj xZ]) (Ax := S) Prov.refEqv).tinst tv1).inst fx4
  have hb : Ent S C4h [fH.conj xZ] ((Tm.eqv tv1 tv1 fx4 fz4).imp (Tm.eqv tv1 tv1 fx4 hz4)) :=
    Ent.beta (Ent.inst (Ent.mp (Ent.inst (Ent.inst ((Ent.axm (Γ := C4h) (Hs := [fH.conj xZ]) hLL).tinst (tv3.arrow tv1))
        (.var (.there (.there (.there (.there (.there .here))))))) (.var (.there .here))) (Ent.andE1 hc))
      (Tm.lam (tv3.arrow tv1) (Tm.eqv tv1 tv1 (.app (.var (.there (.there (.there (.there (.there (.there .here))))))) (.var (.there (.there (.there (.there .here))))))
        (.app (.var .here) (.var (.there .here))))))
      (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  exact Ent.mp hb (Ent.mp ha hr)

/-- The formulas `Q₁ γ` (= hstep) , `Q₁ δ` (= Q₂ α), and `Q₂ β`, in the context `C4`. -/
abbrev Qg : Fm C4 := Tm.all (tv3.arrow tv1) (Tm.all tv3 (Tm.imp
  (Tm.conj (Tm.eqv (tv3.arrow tv1) (tv3.arrow tv1) (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there .here)))
           (Tm.eqv tv3 tv3 (.var (.there (.there (.there .here)))) (.var .here)))
  (Tm.eqv tv1 tv1 (.app (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there .here)))))
                  (.app (.var (.there .here)) (.var .here)))))
abbrev Qd : Fm C4 := Tm.all (tv3.arrow tv0) (Tm.all tv3 (Tm.imp
  (Tm.conj (Tm.eqv (tv3.arrow tv1) (tv3.arrow tv0) (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there .here)))
           (Tm.eqv tv3 tv3 (.var (.there (.there (.there .here)))) (.var .here)))
  (Tm.eqv tv1 tv0 (.app (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there .here)))))
                  (.app (.var (.there .here)) (.var .here)))))
abbrev Qb : Fm C4 := Tm.all (tv2.arrow tv0) (Tm.all tv2 (Tm.imp
  (Tm.conj (Tm.eqv (tv3.arrow tv1) (tv2.arrow tv0) (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there .here)))
           (Tm.eqv tv3 tv2 (.var (.there (.there (.there .here)))) (.var .here)))
  (Tm.eqv tv1 tv0 (.app (.var (.there (.there (.there (.there (.there .here)))))) (.var (.there (.there (.there .here)))))
                  (.app (.var (.there .here)) (.var .here)))))

/-- The two predicates of kind `Πρ:∗.t` used with LL≈. -/
abbrev Q1 : Tm C4 (.pi .t) := Tm.tlam (Tm.all (tv4'.arrow tv0) (Tm.all tv4' (Tm.imp
  (Tm.conj (Tm.eqv (tv4'.arrow tv2) (tv4'.arrow tv0) (.var (.there (.there (.tthere (.there (.there (.there .here))))))) (.var (.there .here)))
           (Tm.eqv tv4' tv4' (.var (.there (.there (.tthere (.there .here))))) (.var .here)))
  (Tm.eqv tv2 tv0 (.app (.var (.there (.there (.tthere (.there (.there (.there .here))))))) (.var (.there (.there (.tthere (.there .here))))))
                  (.app (.var (.there .here)) (.var .here))))))
abbrev Q2 : Tm C4 (.pi .t) := Tm.tlam (Tm.all (tv0.arrow tv1) (Tm.all tv0 (Tm.imp
  (Tm.conj (Tm.eqv (tv4'.arrow tv2) (tv0.arrow tv1) (.var (.there (.there (.tthere (.there (.there (.there .here))))))) (.var (.there .here)))
           (Tm.eqv tv4' tv0 (.var (.there (.there (.tthere (.there .here))))) (.var .here)))
  (Tm.eqv tv2 tv1 (.app (.var (.there (.there (.tthere (.there (.there (.there .here))))))) (.var (.there (.there (.tthere (.there .here))))))
                  (.app (.var (.there .here)) (.var .here))))))

abbrev Hyp4 : Fm C4 := Tm.conj (Tm.conj (Tm.teq tv3 tv2) (Tm.teq tv1 tv0))
  (Tm.conj (Tm.eqv (tv3.arrow tv1) (tv2.arrow tv0) (.var (.there (.there (.there .here)))) (.var (.there (.there .here))))
           (Tm.eqv tv3 tv2 (.var (.there .here)) (.var .here)))
abbrev Concl4 : Fm C4 := Tm.eqv tv1 tv0 (.app (.var (.there (.there (.there .here)))) (.var (.there .here)))
  (.app (.var (.there (.there .here))) (.var .here))

set_option maxHeartbeats 16000000 in
/-- Theorem 4 (WCong), from LL≡. -/
theorem d_WCong (hLL : S LLEqv) : Prov S Ctx.nil WCong := by
  have hstep : Ent S C4 [Hyp4] Qg :=
    Ent.ofProv (Ent.gen (Hs := []) (tv3.arrow tv1) (Ent.gen (Hs := []) tv3 (Ent.intro (Hs := []) (wcong_hstep hLL))))
  have hH : Ent S C4 [Hyp4] Hyp4 := Ent.hyp _ 0 (by decide)
  have hab : Ent S C4 [Hyp4] (Tm.teq tv3 tv2) := Ent.andE1 (Ent.andE1 hH)
  have hgd : Ent S C4 [Hyp4] (Tm.teq tv1 tv0) := Ent.andE2 (Ent.andE1 hH)
  have l1 : Ent S C4 [Hyp4] ((Tm.teq tv1 tv0).imp (Qg.imp Qd)) :=
    Ent.beta (((Ent.ofProv (Prov.llTeq Q1)).tinst tv1).tinst tv0)
      (BetaEq.imp (.refl _) (BetaEq.imp (BetaEq.tbeta _ _) (BetaEq.tbeta _ _)))
  have mid : Ent S C4 [Hyp4] Qd := Ent.mp2 l1 hgd hstep
  have l2 : Ent S C4 [Hyp4] ((Tm.teq tv3 tv2).imp (Qd.imp Qb)) :=
    Ent.beta (((Ent.ofProv (Prov.llTeq Q2)).tinst tv3).tinst tv2)
      (BetaEq.imp (.refl _) (BetaEq.imp (BetaEq.tbeta _ _) (BetaEq.tbeta _ _)))
  have fin : Ent S C4 [Hyp4] Qb := Ent.mp2 l2 hab mid
  have hg : Ent S C4 [Hyp4] ((Tm.conj (Tm.eqv (tv3.arrow tv1) (tv2.arrow tv0) (.var (.there (.there (.there .here)))) (.var (.there (.there .here))))
           (Tm.eqv tv3 tv2 (.var (.there .here)) (.var .here))).imp Concl4) :=
    Ent.inst (Ent.inst fin (.var (.there (.there .here)))) (.var .here)
  have hc : Ent S C4 ([] ++ [Hyp4]) Concl4 := Ent.mp hg (Ent.andE2 hH)
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.tgen (Hs := [])
    (Ent.gen (Hs := []) (tv3.arrow tv1) (Ent.gen (Hs := []) (tv2.arrow tv0) (Ent.gen (Hs := []) tv3
      (Ent.gen (Hs := []) tv2 (Ent.intro (Hs := []) hc)))))))))

end WCong

/-! ### Theorem 20: given LL≡ and LL≡-Poly, Cong is equivalent to Recovery -/

section Thm20
variable {S : Fm Ctx.nil → Prop}

/-- Instantiating a universal quantifier under an implication. -/
theorem Ent.impInst {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)} {A : Fm Γ} {σ : Ty n} {φ : Fm (.ext Γ σ)}
    (h : Ent S Γ Hs (A.imp (Tm.all σ φ))) (κ : Tm Γ σ.1) : Ent S Γ Hs (A.imp (φ.subst0 κ)) :=
  Ent.intro (Ent.inst (Ent.mp (Ent.weaken h) Ent.last) κ)

/-- From `¬A → ¬B` and `B`, infer `A`. -/
theorem teq_of_eqv {n : Nat} {Γ : Ctx n} {Hs : List (Fm Γ)} {A B : Fm Γ}
    (hd : Ent S Γ Hs (A.neg.imp B.neg)) (hb : Ent S Γ Hs B) : Ent S Γ Hs A :=
  Ent.mp2 (Ent.taut (.imp (.imp (.neg (.atom 0)) (.neg (.atom 1))) (.imp (.atom 1) (.atom 0))) (v2 A B)
    (fun _ f b => Classical.byContradiction fun na => f na b)) hd hb

abbrev fg4 : Fm C4 := Tm.eqv (tv3.arrow tv1) (tv2.arrow tv0) (.var (.there (.there (.there .here)))) (.var (.there (.there .here)))
abbrev xy4 : Fm C4 := Tm.eqv tv3 tv2 (.var (.there .here)) (.var .here)
abbrev R4 {Γ : Ctx 4} : Fm Γ := Tm.conj (Tm.teq (tv3.arrow tv1) (tv2.arrow tv0)) (Tm.teq tv3 tv2)

set_option maxHeartbeats 16000000 in
/-- Theorem 20, first half: Cong follows from LL≡, LL≡-Poly, and Recovery. -/
theorem d_Cong_of_Recovery (hLL : S LLEqv) (hP : S (Tm.tall (LLPoly PredA))) (hR : S Recovery) :
    Prov S Ctx.nil Cong := by
  have hH : Ent S C4 [fg4.conj xy4] (fg4.conj xy4) := Ent.hyp _ 0 (by decide)
  have hdab : Ent S C4 [fg4.conj xy4] ((Tm.teq tv3 tv2).neg.imp
      (Tm.all tv3 (Tm.all tv2 (Tm.eqv tv3 tv2 (.var (.there .here)) (.var .here)).neg))) :=
    ((Ent.closed (Γ := C4) (Hs := [fg4.conj xy4]) (Ax := S) (d_Disjoint_of_LLPoly hP)).tinst tv3).tinst tv2
  have hd1 : Ent S C4 [fg4.conj xy4] ((Tm.teq tv3 tv2).neg.imp xy4.neg) :=
    Ent.impInst (Ent.impInst hdab (.var (.there .here))) (.var .here)
  have hab : Ent S C4 [fg4.conj xy4] (Tm.teq tv3 tv2) := teq_of_eqv hd1 (Ent.andE2 hH)
  have hdfg : Ent S C4 [fg4.conj xy4] ((Tm.teq (tv3.arrow tv1) (tv2.arrow tv0)).neg.imp
      (Tm.all (tv3.arrow tv1) (Tm.all (tv2.arrow tv0) (Tm.eqv (tv3.arrow tv1) (tv2.arrow tv0) (.var (.there .here)) (.var .here)).neg))) :=
    ((Ent.closed (Γ := C4) (Hs := [fg4.conj xy4]) (Ax := S) (d_Disjoint_of_LLPoly hP)).tinst (tv3.arrow tv1)).tinst (tv2.arrow tv0)
  have hd2 : Ent S C4 [fg4.conj xy4] ((Tm.teq (tv3.arrow tv1) (tv2.arrow tv0)).neg.imp fg4.neg) :=
    Ent.impInst (Ent.impInst hdfg (.var (.there (.there (.there .here))))) (.var (.there (.there .here)))
  have harr : Ent S C4 [fg4.conj xy4] (Tm.teq (tv3.arrow tv1) (tv2.arrow tv0)) := teq_of_eqv hd2 (Ent.andE1 hH)
  have hrec : Ent S C4 [fg4.conj xy4] (R4.imp (Tm.teq tv1 tv0)) :=
    ((((Ent.axm (Γ := C4) (Hs := [fg4.conj xy4]) hR).tinst tv3).tinst tv2).tinst tv1).tinst tv0
  have hgd : Ent S C4 [fg4.conj xy4] (Tm.teq tv1 tv0) := Ent.mp hrec (Ent.andI harr hab)
  have hw : Ent S C4 [fg4.conj xy4] ((Tm.conj (Tm.conj (Tm.teq tv3 tv2) (Tm.teq tv1 tv0)) (fg4.conj xy4)).imp Concl4) :=
    Ent.inst (Ent.inst (Ent.inst (Ent.inst ((((((Ent.closed (Γ := C4) (Hs := [fg4.conj xy4]) (Ax := S) (d_WCong hLL)).tinst tv3).tinst tv2).tinst tv1).tinst tv0))
      (.var (.there (.there (.there .here))))) (.var (.there (.there .here)))) (.var (.there .here))) (.var .here)
  have hc : Ent S C4 ([] ++ [fg4.conj xy4]) Concl4 := Ent.mp hw (Ent.andI (Ent.andI hab hgd) hH)
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.tgen (Hs := [])
    (Ent.gen (Hs := []) (tv3.arrow tv1) (Ent.gen (Hs := []) (tv2.arrow tv0) (Ent.gen (Hs := []) tv3
      (Ent.gen (Hs := []) tv2 (Ent.intro (Hs := []) hc)))))))))

abbrev Cf : Ctx 4 := Δ4.ext (tv3.arrow tv1)
abbrev Cfx : Ctx 4 := Cf.ext tv3
abbrev Cfxy : Ctx 4 := Cfx.ext tv2
abbrev Cfxyg : Ctx 4 := Cfxy.ext (tv2.arrow tv0)
abbrev ExyR : Fm Cfxy := Tm.eqv tv3 tv2 (.var (.there .here)) (.var .here)
abbrev ExyR' : Fm Cfxyg := Tm.eqv tv3 tv2 (.var (.there (.there .here))) (.var (.there .here))
abbrev EfgR : Fm Cfxyg := Tm.eqv (tv3.arrow tv1) (tv2.arrow tv0) (.var (.there (.there (.there .here)))) (.var .here)
abbrev fxR : Tm Cfxyg tv1.1 := .app (.var (.there (.there (.there .here)))) (.var (.there (.there .here)))
abbrev gyR : Tm Cfxyg tv0.1 := .app (.var .here) (.var (.there .here))

set_option maxHeartbeats 16000000 in
/-- Theorem 20, second half: Recovery follows from LL≡, LL≡-Poly, and Cong. -/
theorem d_Recovery_of_Cong (hP : S (Tm.tall (LLPoly PredA))) (hC : S Cong) : Prov S Ctx.nil Recovery := by
  -- innermost: f x y g, with x ≡ y and f ≡ g
  have inner : Ent S Cfxyg ([R4, ExyR'] ++ [EfgR]) (Tm.teq tv1 tv0) := by
    have hxy : Ent S Cfxyg [R4, ExyR', EfgR] ExyR' := Ent.hyp _ 1 (by decide)
    have hfg : Ent S Cfxyg [R4, ExyR', EfgR] EfgR := Ent.hyp _ 2 (by decide)
    have hc : Ent S Cfxyg [R4, ExyR', EfgR] ((EfgR.conj ExyR').imp (Tm.eqv tv1 tv0 fxR gyR)) :=
      Ent.inst (Ent.inst (Ent.inst (Ent.inst (((((Ent.axm (Γ := Cfxyg) (Hs := [R4, ExyR', EfgR]) hC).tinst tv3).tinst tv2).tinst tv1).tinst tv0)
        (.var (.there (.there (.there .here))))) (.var .here)) (.var (.there (.there .here)))) (.var (.there .here))
    have hd : Ent S Cfxyg [R4, ExyR', EfgR] ((Tm.teq tv1 tv0).neg.imp
        (Tm.all tv1 (Tm.all tv0 (Tm.eqv tv1 tv0 (.var (.there .here)) (.var .here)).neg))) :=
      ((Ent.closed (Γ := Cfxyg) (Hs := [R4, ExyR', EfgR]) (Ax := S) (d_Disjoint_of_LLPoly hP)).tinst tv1).tinst tv0
    exact teq_of_eqv (Ent.impInst (Ent.impInst hd fxR) gyR) (Ent.mp hc (Ent.andI hfg hxy))
  -- ∃g (f ≡ g), from Link at the function types
  have hexg : Ent S Cfxy [R4, ExyR] (Tm.ex (tv2.arrow tv0)
      (Tm.eqv (tv3.arrow tv1) (tv2.arrow tv0) (.var (.there (.there (.there .here)))) (.var .here))) :=
    Ent.inst (Ent.mp (((Ent.closed (Γ := Cfxy) (Hs := [R4, ExyR]) (Ax := S) d_Link).tinst (tv3.arrow tv1)).tinst (tv2.arrow tv0))
      (Ent.andE1 (Ent.hyp (Ax := S) [R4, ExyR] 0 (by decide)))) (.var (.there (.there .here)))
  have h2 : Ent S Cfxy ([R4] ++ [ExyR]) (Tm.teq tv1 tv0) := Ent.exE (Hs := [R4, ExyR]) hexg inner
  -- ∃y (x ≡ y), from Link
  have hexy : Ent S Cfx [R4] (Tm.ex tv2 ExyR) :=
    Ent.inst (Ent.mp (((Ent.closed (Γ := Cfx) (Hs := [R4]) (Ax := S) d_Link).tinst tv3).tinst tv2)
      (Ent.andE2 (Ent.hyp (Ax := S) [R4] 0 (by decide)))) (.var .here)
  have h3 : Ent S Cfx [R4] (Tm.teq tv1 tv0) := Ent.exE (Hs := [R4]) hexy h2
  have h4 : Ent S Δ4 ([] ++ [R4]) (Tm.teq tv1 tv0) :=
    Ent.strengthen (Hs := [R4]) (tv3.arrow tv1) (Ent.strengthen (Hs := [R4]) tv3 h3)
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.tgen (Hs := [])
    (Ent.intro (Hs := []) h4)))))

end Thm20


/-! ### Found while exploring: Disjoint yields Ext≈ -/

section Explore
variable {S : Fm Ctx.nil → Prop}

abbrev HypE {Γ : Ctx 2} : Fm Γ := Tm.conj subT supT
abbrev Cx2 : Ctx 2 := Δ2.ext tv1
abbrev Cx2y : Ctx 2 := Cx2.ext tv0
abbrev ExyE : Fm Cx2y := Tm.eqv tv1 tv0 (.var (.there .here)) (.var .here)

set_option maxHeartbeats 16000000 in
/-- Disjoint yields Ext≈: if every item of `α` is identical to an item of `β`, then since `α` is
non-empty some item of `α` is identical to some item of `β`, and Disjoint gives `α ≈ β`. -/
theorem d_ExtT_of_Disjoint (hD : S Disjoint) : Prov S Ctx.nil ExtT := by
  have inner : Ent S Cx2y ([HypE] ++ [ExyE]) (Tm.teq tv1 tv0) := by
    have hd : Ent S Cx2y [HypE, ExyE] ((Tm.teq tv1 tv0).neg.imp
        (Tm.all tv1 (Tm.all tv0 (Tm.eqv tv1 tv0 (.var (.there .here)) (.var .here)).neg))) :=
      ((Ent.axm (Γ := Cx2y) (Hs := [HypE, ExyE]) hD).tinst tv1).tinst tv0
    exact teq_of_eqv (Ent.impInst (Ent.impInst hd (.var (.there .here))) (.var .here))
      (Ent.hyp (Ax := S) [HypE, ExyE] 1 (by decide))
  have hex : Ent S Cx2 [HypE] (Tm.ex tv0 (Tm.eqv tv1 tv0 (.var (.there .here)) (.var .here))) :=
    Ent.inst (Ent.andE1 (Ent.hyp (Ax := S) [HypE] 0 (by decide))) (.var .here)
  have h2 : Ent S Cx2 [HypE] (Tm.teq tv1 tv0) := Ent.exE (Hs := [HypE]) hex inner
  have h3 : Ent S Δ2 ([] ++ [HypE]) (Tm.teq tv1 tv0) := Ent.strengthen (Hs := [HypE]) tv1 h2
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.intro (Hs := []) h3)))

abbrev HypI {Γ : Ctx 2} : Fm Γ := Tm.conj (boxF subT) (boxF supT)

set_option maxHeartbeats 16000000 in
/-- `□φ → φ` for `φ = subT`, from LL≡ (with Sym≡): from `φ ≡ ⊤` get `⊤ ≡ φ`, and LL≡ with `λv.v` gives `⊤ → φ`. -/
theorem unbox_sub (hLL : S LLEqv) (h : Ent S Δ2 [HypI] (boxF (subT : Fm Δ2))) : Ent S Δ2 [HypI] (subT : Fm Δ2) := by
  have hs : Ent S Δ2 [HypI] ((Tm.eqv tyT tyT (subT : Fm Δ2) topF).imp (Tm.eqv tyT tyT topF (subT : Fm Δ2))) :=
    Ent.inst (Ent.inst (((Ent.closed (Γ := Δ2) (Hs := [HypI]) (Ax := S) Prov.symEqv).tinst tyT).tinst tyT) (subT : Fm Δ2)) topF
  have hl : Ent S Δ2 [HypI] (topF.imp (subT : Fm Δ2)) :=
    Ent.beta (Ent.inst (Ent.mp (Ent.inst (Ent.inst ((Ent.axm (Γ := Δ2) (Hs := [HypI]) hLL).tinst tyT) topF) (subT : Fm Δ2)) (Ent.mp hs h))
      (Tm.lam tyT (.var .here))) (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  exact Ent.mp hl Ent.top

set_option maxHeartbeats 16000000 in
/-- `□φ → φ` for `φ = supT`, from LL≡ (with Sym≡): from `φ ≡ ⊤` get `⊤ ≡ φ`, and LL≡ with `λv.v` gives `⊤ → φ`. -/
theorem unbox_sup (hLL : S LLEqv) (h : Ent S Δ2 [HypI] (boxF (supT : Fm Δ2))) : Ent S Δ2 [HypI] (supT : Fm Δ2) := by
  have hs : Ent S Δ2 [HypI] ((Tm.eqv tyT tyT (supT : Fm Δ2) topF).imp (Tm.eqv tyT tyT topF (supT : Fm Δ2))) :=
    Ent.inst (Ent.inst (((Ent.closed (Γ := Δ2) (Hs := [HypI]) (Ax := S) Prov.symEqv).tinst tyT).tinst tyT) (supT : Fm Δ2)) topF
  have hl : Ent S Δ2 [HypI] (topF.imp (supT : Fm Δ2)) :=
    Ent.beta (Ent.inst (Ent.mp (Ent.inst (Ent.inst ((Ent.axm (Γ := Δ2) (Hs := [HypI]) hLL).tinst tyT) topF) (supT : Fm Δ2)) (Ent.mp hs h))
      (Tm.lam tyT (.var .here))) (BetaEq.imp (.step (.beta _ _)) (.step (.beta _ _)))
  exact Ent.mp hl Ent.top

set_option maxHeartbeats 16000000 in
/-- Given LL≡, Ext≈ yields Int≈ (found while exploring). -/
theorem d_IntT_of_ExtT (hLL : S LLEqv) (hE : S ExtT) : Prov S Ctx.nil IntT := by
  have hH : Ent S Δ2 [HypI] HypI := Ent.hyp _ 0 (by decide)
  have h1 : Ent S Δ2 [HypI] (Tm.conj subT supT) :=
    Ent.andI (unbox_sub hLL (Ent.andE1 hH)) (unbox_sup hLL (Ent.andE2 hH))
  have he : Ent S Δ2 [HypI] ((Tm.conj subT supT).imp (Tm.teq tv1 tv0)) :=
    ((Ent.axm (Γ := Δ2) (Hs := [HypI]) hE).tinst tv1).tinst tv0
  have h2 : Ent S Δ2 ([] ++ [HypI]) (Tm.teq tv1 tv0) := Ent.mp he h1
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.intro (Hs := []) h2)))

end Explore

end Derive


end PIF
