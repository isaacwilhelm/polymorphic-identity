import PISchemas

/-!
# Substitution metatheory

Composition laws for renaming and substitution of terms, and the preservation of β-conversion by
them. These are needed for the completeness theorem for general models.
-/
set_option autoImplicit false

namespace PIF

section SubLemmas

theorem Cat.ren_sub_congr {n m k : Nat} (K : Cat n) {s : Fin n → Ty m} {r : Fin m → Fin k} {s' : Fin n → Ty k}
    (h : ∀ i, (s i).1.ren r = (s' i).1) : (K.sub s).ren r = K.sub s' := by
  rw [Cat.ren_sub]; exact Cat.sub_congr K h

theorem Cat.sub_sub_congr {n m k : Nat} (K : Cat n) {s1 : Fin n → Ty m} {s2 : Fin m → Ty k} {s3 : Fin n → Ty k}
    (h : ∀ i, (s1 i).1.sub s2 = (s3 i).1) : (K.sub s1).sub s2 = K.sub s3 := by
  rw [Cat.sub_sub]; exact Cat.sub_congr K h

theorem heq_var_of {n : Nat} {Θ : Ctx n} {A B : Cat n} (hAB : A = B) {x : Var Θ A} {y : Var Θ B} (h : HEq x y) :
    HEq (Tm.var x) (Tm.var y) := by
  subst hAB; cases h; rfl

theorem var_castK_heq' {n : Nat} {Γ : Ctx n} {K K' : Cat n} (h : K = K') (x : Var Γ K) : HEq (Var.castK h x) x := by
  subst h; rfl

theorem ren_castK_heq {n m : Nat} {r : Fin n → Fin m} {Γ : Ctx n} {Δ : Ctx m} (ρ : TRen r Γ Δ) {K K' : Cat n}
    (h : K = K') (M : Tm Γ K) : HEq ((Tm.castK h M).ren ρ) (M.ren ρ) := by
  subst h; rfl

/-- Renaming after renaming is renaming. -/
theorem Tm.ren_ren_heq {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) {m : Nat} {r1 : Fin n → Fin m} {Δ : Ctx m}
    (ρ1 : TRen r1 Γ Δ) {k : Nat} {r2 : Fin m → Fin k} {Θ : Ctx k} (ρ2 : TRen r2 Δ Θ) {r3 : Fin n → Fin k}
    (ρ3 : TRen r3 Γ Θ) (hr : ∀ i, r2 (r1 i) = r3 i) (hx : ∀ {L : Cat n} (x : Var Γ L), HEq (ρ2 (ρ1 x)) (ρ3 x)) :
    HEq ((M.ren ρ1).ren ρ2) (M.ren ρ3) := by
  have h1 : HEq ((M.ren ρ1).ren ρ2) ((M.ren ρ1).sub (TRen.asSub ρ2)) :=
    Tm.ren_eq_sub_heq (M.ren ρ1) ρ2 rfl (TRen.asSub ρ2) (fun _ => rfl) (fun _ => (castK_heq _ _).symm)
  have h2 : HEq ((M.ren ρ1).sub (TRen.asSub ρ2)) (M.sub (TRen.asSub ρ3)) :=
    Tm.sub_ren_heq M ρ1 rfl (TRen.asSub ρ2) (TRen.asSub ρ3)
      (fun i => by show Cat.var (r2 (r1 i)) = Cat.var (r3 i); rw [hr])
      (fun {L} x => (castK_heq _ _).trans ((heq_var_of
        (by rw [Cat.ren_ren]; exact Cat.ren_congr L hr) (hx x)).trans (castK_heq _ _).symm))
  have h3 : HEq (M.sub (TRen.asSub ρ3)) (M.ren ρ3) :=
    (Tm.ren_eq_sub_heq M ρ3 rfl (TRen.asSub ρ3) (fun _ => rfl) (fun _ => (castK_heq _ _).symm)).symm
  exact h1.trans (h2.trans h3)

/-- The identity renaming. -/
def idRen {n : Nat} (Γ : Ctx n) : TRen (fun i => i) Γ Γ := fun x => Var.castK (Cat.ren_id _).symm x

theorem Tm.ren_id_heq {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) : HEq (M.ren (idRen Γ)) M :=
  (Tm.ren_eq_sub_heq M (idRen Γ) rfl (TRen.asSub (idRen Γ)) (fun _ => rfl) (fun _ => (castK_heq _ _).symm)).trans
    (Tm.sub_id_heq M rfl (TRen.asSub (idRen Γ)) (fun _ => rfl)
      (fun _ => ((var_castK_heq _ _).symm.trans (castK_heq _ _).symm).trans HEq.rfl)).symm

/-- Substitutions which agree pointwise give the same result. -/
theorem Tm.sub_congr_heq {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) {m : Nat} {sa sb : Fin n → Ty m}
    {Θ Θ' : Ctx m} (hΘ : Θ = Θ') (σa : TSub sa Γ Θ) (σb : TSub sb Γ Θ') (hs : ∀ i, (sa i).1 = (sb i).1)
    (hx : ∀ {L : Cat n} (x : Var Γ L), HEq (σa x) (σb x)) : HEq (M.sub σa) (M.sub σb) :=
  (Tm.sub_ren_heq M (idRen Γ) rfl σa σa (fun _ => rfl) (fun x => tsub_varCast_heq σa _ x)).symm.trans
    (Tm.sub_ren_heq M (idRen Γ) hΘ σa σb hs (fun x => (tsub_varCast_heq σa _ x).trans (hx x)))


theorem tren_castK_heq {n m : Nat} {r : Fin n → Fin m} {Γ : Ctx n} {Δ : Ctx m} (ρ : TRen r Γ Δ) {K K' : Cat n}
    (h : K = K') (x : Var Γ K) : HEq (ρ (Var.castK h x)) (ρ x) := by
  subst h; rfl

/-- Weakening commutes with renaming. -/
theorem wk_ren_heq {n m : Nat} {r : Fin n → Fin m} {Δ : Ctx n} {Θ : Ctx m} (ρ : TRen r Δ Θ) (τ : Ty n)
    {L : Cat n} (N : Tm Δ L) : HEq ((N.wk τ).ren (ρ.lift τ)) ((N.ren ρ).wk (τ.ren r)) := by
  have h1 : HEq ((N.wk τ).ren (ρ.lift τ)) ((N.ren (wkRen τ)).ren (ρ.lift τ)) := ren_castK_heq _ _ _
  have h2 : HEq ((N.ren (wkRen τ)).ren (ρ.lift τ)) (N.ren (fun x => (Var.there (ρ x) : Var (Θ.ext (τ.ren r)) _))) :=
    Tm.ren_ren_heq N (wkRen τ) (ρ.lift τ) _ (fun _ => rfl) (fun x => tren_castK_heq (ρ.lift τ) _ (Var.there x))
  have h3 : HEq ((N.ren ρ).wk (τ.ren r)) ((N.ren ρ).ren (wkRen (τ.ren r))) := castK_heq _ _
  have h4 : HEq ((N.ren ρ).ren (wkRen (τ.ren r))) (N.ren (fun x => (Var.there (ρ x) : Var (Θ.ext (τ.ren r)) _))) :=
    Tm.ren_ren_heq N ρ (wkRen (τ.ren r)) _ (fun _ => rfl) (fun x => var_castK_heq' _ _)
  exact h1.trans (h2.trans (h4.symm.trans h3.symm))


/-- Type weakening commutes with renaming. -/
theorem twk_ren_heq {n m : Nat} {r : Fin n → Fin m} {Δ : Ctx n} {Θ : Ctx m} (ρ : TRen r Δ Θ)
    {L : Cat n} (N : Tm Δ L) : HEq (N.twk.ren ρ.tlift) (N.ren ρ).twk := by
  let ρ3 : TRen (fun i => fs (r i)) Δ (.text Θ) := fun x => Var.castK (Cat.ren_ren _ _ _) (Var.tthere (ρ x))
  have h1 : HEq (N.twk.ren ρ.tlift) (N.ren ρ3) :=
    Tm.ren_ren_heq N (twkRen Δ) ρ.tlift ρ3 (fun _ => rfl) (fun x =>
      (var_castK_heq' _ _).trans (var_castK_heq' _ _).symm)
  have h2 : HEq ((N.ren ρ).twk) (N.ren ρ3) :=
    Tm.ren_ren_heq N ρ (twkRen Θ) ρ3 (fun _ => rfl) (fun x => (var_castK_heq' _ _).symm)
  exact h1.trans h2.symm

/-- Renaming after substitution is substitution. -/
theorem Tm.ren_sub_heq {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) :
    ∀ {m k : Nat} {s : Fin n → Ty m} {Δ : Ctx m} (σs : TSub s Γ Δ) {r : Fin m → Fin k} {Θ Θ' : Ctx k}
      (_ : Θ = Θ') (ρ : TRen r Δ Θ) {s' : Fin n → Ty k} (σs' : TSub s' Γ Θ'),
      (∀ i, (s i).1.ren r = (s' i).1) → (∀ {L : Cat n} (x : Var Γ L), HEq ((σs x).ren ρ) (σs' x)) →
      HEq ((M.sub σs).ren ρ) (M.sub σs') := by
  induction M with
  | var x => intro m k s Δ σs r Θ Θ' _ ρ s' σs' _ hx; exact hx x
  | const c => intro m k s Δ σs r Θ Θ' hΘ ρ s' σs' _ _; subst hΘ; cases c <;> exact HEq.rfl
  | app f a ihf iha =>
    intro m k s Δ σs r Θ Θ' hΘ ρ s' σs' hs hx
    exact heq_app' hΘ (Cat.ren_sub_congr _ hs) (Cat.ren_sub_congr _ hs) (ihf σs hΘ ρ σs' hs hx) (iha σs hΘ ρ σs' hs hx)
  | lam σ b ih =>
    intro m k s Δ σs r Θ Θ' hΘ ρ s' σs' hs hx
    have hσ : (σ.sub s).ren r = σ.sub s' := Subtype.ext (Cat.ren_sub_congr σ.1 hs)
    refine heq_lam' hΘ hσ (Cat.ren_sub_congr _ hs) (ih (σs.lift σ) (by rw [hΘ, hσ]) (ρ.lift _) (σs'.lift σ) hs ?_)
    intro L x
    cases x with
    | here => exact heq_var_here hΘ hσ
    | there y =>
      exact (wk_ren_heq ρ (σ.sub s) (σs y)).trans (heq_wk hΘ hσ (Cat.ren_sub_congr _ hs) (hx y))
  | tlam b ih =>
    intro m k s Δ σs r Θ Θ' hΘ ρ s' σs' hs hx
    have hs' : ∀ i, (liftT s i).1.ren (liftR r) = (liftT s' i).1 :=
      fin_cases rfl (fun i => by
        show ((s i).1.ren fs).ren (liftR r) = (s' i).1.ren fs
        rw [Cat.ren_ren, ← hs i, Cat.ren_ren]; rfl)
    refine heq_tlam' hΘ (Cat.ren_sub_congr _ hs') (ih σs.tlift (by rw [hΘ]) ρ.tlift σs'.tlift hs' ?_)
    intro L x
    cases x with
    | tthere y =>
      refine (ren_castK_heq _ _ _).trans ?_
      refine HEq.trans ?_ (castK_heq _ _).symm
      exact (twk_ren_heq ρ (σs y)).trans (heq_twk hΘ (Cat.ren_sub_congr _ hs) (hx y))
  | tapp f σ ih =>
    intro m k s Δ σs r Θ Θ' hΘ ρ s' σs' hs hx
    have hs' : ∀ i, (liftT s i).1.ren (liftR r) = (liftT s' i).1 :=
      fin_cases rfl (fun i => by
        show ((s i).1.ren fs).ren (liftR r) = (s' i).1.ren fs
        rw [Cat.ren_ren, ← hs i, Cat.ren_ren]; rfl)
    refine (ren_castK_heq _ _ _).trans ?_
    refine heq_castK_both _ _ ?_
    exact heq_tapp' hΘ (Cat.ren_sub_congr _ hs') (ih σs hΘ ρ σs' hs hx) (Subtype.ext (Cat.ren_sub_congr σ.1 hs))


theorem wk_sub_heq {n m : Nat} {s : Fin n → Ty m} {Δ : Ctx n} {Θ : Ctx m} (σ2 : TSub s Δ Θ) (τ : Ty n)
    {L : Cat n} (N : Tm Δ L) : HEq ((N.wk τ).sub (σ2.lift τ)) ((N.sub σ2).wk (τ.sub s)) := by
  have h1 : HEq ((N.wk τ).sub (σ2.lift τ)) (N.sub (fun x => (σ2 x).wk (τ.sub s))) :=
    (sub_castK_heq _ _ _).trans (Tm.sub_ren_heq N (wkRen τ) rfl (σ2.lift τ) (fun x => (σ2 x).wk (τ.sub s))
      (fun _ => rfl) (fun x => tsub_varCast_heq (σ2.lift τ) _ (Var.there x)))
  have h2 : HEq ((N.sub σ2).wk (τ.sub s)) (N.sub (fun x => (σ2 x).wk (τ.sub s))) :=
    (castK_heq _ _).trans (Tm.ren_sub_heq N σ2 rfl (wkRen (τ.sub s)) (fun x => (σ2 x).wk (τ.sub s))
      (fun i => Cat.ren_id _) (fun x => (castK_heq _ _).symm))
  exact h1.trans h2.symm

theorem twk_sub_heq {n m : Nat} {s : Fin n → Ty m} {Δ : Ctx n} {Θ : Ctx m} (σ2 : TSub s Δ Θ)
    {L : Cat n} (N : Tm Δ L) : HEq (N.twk.sub σ2.tlift) (N.sub σ2).twk := by
  let σt : TSub (fun i => (s i).ren fs) Δ (.text Θ) := fun {L} x => Tm.castK (Cat.ren_sub L s fs) (σ2 x).twk
  have h1 : HEq (N.twk.sub σ2.tlift) (N.sub σt) :=
    Tm.sub_ren_heq N (twkRen Δ) rfl σ2.tlift σt (fun _ => rfl)
      (fun x => (castK_heq _ _).trans (castK_heq _ _).symm)
  have h2 : HEq ((N.sub σ2).twk) (N.sub σt) :=
    Tm.ren_sub_heq N σ2 rfl (twkRen Θ) σt (fun _ => rfl) (fun x => (castK_heq _ _).symm)
  exact h1.trans h2.symm

/-- Substitution after substitution is substitution. -/
theorem Tm.sub_sub_heq {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) :
    ∀ {m k : Nat} {s1 : Fin n → Ty m} {Δ : Ctx m} (σ1 : TSub s1 Γ Δ) {s2 : Fin m → Ty k} {Θ Θ' : Ctx k}
      (_ : Θ = Θ') (σ2 : TSub s2 Δ Θ) {s3 : Fin n → Ty k} (σ3 : TSub s3 Γ Θ'),
      (∀ i, (s1 i).1.sub s2 = (s3 i).1) → (∀ {L : Cat n} (x : Var Γ L), HEq ((σ1 x).sub σ2) (σ3 x)) →
      HEq ((M.sub σ1).sub σ2) (M.sub σ3) := by
  induction M with
  | var x => intro m k s1 Δ σ1 s2 Θ Θ' _ σ2 s3 σ3 _ hx; exact hx x
  | const c => intro m k s1 Δ σ1 s2 Θ Θ' hΘ σ2 s3 σ3 _ _; subst hΘ; cases c <;> exact HEq.rfl
  | app f a ihf iha =>
    intro m k s1 Δ σ1 s2 Θ Θ' hΘ σ2 s3 σ3 hs hx
    exact heq_app' hΘ (Cat.sub_sub_congr _ hs) (Cat.sub_sub_congr _ hs) (ihf σ1 hΘ σ2 σ3 hs hx) (iha σ1 hΘ σ2 σ3 hs hx)
  | lam σ b ih =>
    intro m k s1 Δ σ1 s2 Θ Θ' hΘ σ2 s3 σ3 hs hx
    have hσ : (σ.sub s1).sub s2 = σ.sub s3 := Subtype.ext (Cat.sub_sub_congr σ.1 hs)
    refine heq_lam' hΘ hσ (Cat.sub_sub_congr _ hs) (ih (σ1.lift σ) (by rw [hΘ, hσ]) (σ2.lift _) (σ3.lift σ) hs ?_)
    intro L x
    cases x with
    | here => exact heq_var_here hΘ hσ
    | there y =>
      exact (wk_sub_heq σ2 (σ.sub s1) (σ1 y)).trans (heq_wk hΘ hσ (Cat.sub_sub_congr _ hs) (hx y))
  | tlam b ih =>
    intro m k s1 Δ σ1 s2 Θ Θ' hΘ σ2 s3 σ3 hs hx
    have hs' : ∀ i, (liftT s1 i).1.sub (liftT s2) = (liftT s3 i).1 :=
      fin_cases rfl (fun i => by
        show ((s1 i).1.ren fs).sub (liftT s2) = (s3 i).1.ren fs
        rw [← hs i, Cat.sub_ren, Cat.ren_sub]; rfl)
    refine heq_tlam' hΘ (Cat.sub_sub_congr _ hs') (ih σ1.tlift (by rw [hΘ]) σ2.tlift σ3.tlift hs' ?_)
    intro L x
    cases x with
    | tthere y =>
      refine (sub_castK_heq _ _ _).trans ?_
      refine HEq.trans ?_ (castK_heq _ _).symm
      exact (twk_sub_heq σ2 (σ1 y)).trans (heq_twk hΘ (Cat.sub_sub_congr _ hs) (hx y))
  | tapp f σ ih =>
    intro m k s1 Δ σ1 s2 Θ Θ' hΘ σ2 s3 σ3 hs hx
    have hs' : ∀ i, (liftT s1 i).1.sub (liftT s2) = (liftT s3 i).1 :=
      fin_cases rfl (fun i => by
        show ((s1 i).1.ren fs).sub (liftT s2) = (s3 i).1.ren fs
        rw [← hs i, Cat.sub_ren, Cat.ren_sub]; rfl)
    refine (sub_castK_heq _ _ _).trans ?_
    refine heq_castK_both _ _ ?_
    exact heq_tapp' hΘ (Cat.sub_sub_congr _ hs') (ih σ1 hΘ σ2 σ3 hs hx) (Subtype.ext (Cat.sub_sub_congr σ.1 hs))


/-! ### β-conversion under renaming and substitution -/

theorem Step.castKC {n : Nat} {Γ : Ctx n} {K K' : Cat n} (h : K = K') {M N : Tm Γ K} (s : Step M N) :
    Step (Tm.castK h M) (Tm.castK h N) := by
  subst h; exact s

theorem BetaEq.castKC {n : Nat} {Γ : Ctx n} {K K' : Cat n} (h : K = K') {M N : Tm Γ K} (e : BetaEq M N) :
    BetaEq (Tm.castK h M) (Tm.castK h N) := by
  subst h; exact e

theorem BetaEq.congr {n : Nat} {Γ : Ctx n} {K : Cat n} {m : Nat} {Δ : Ctx m} {L : Cat m} (F : Tm Γ K → Tm Δ L)
    (hF : ∀ {M N : Tm Γ K}, Step M N → Step (F M) (F N)) {M N : Tm Γ K} (e : BetaEq M N) : BetaEq (F M) (F N) := by
  induction e with
  | refl => exact .refl _
  | step s => exact .step (hF s)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem BetaEq.app2' {n : Nat} {Γ : Ctx n} {K L : Cat n} {f f' : Tm Γ (.arr K L)} {a a' : Tm Γ K}
    (h1 : BetaEq f f') (h2 : BetaEq a a') : BetaEq (.app f a) (.app f' a') :=
  (BetaEq.congr (fun g => Tm.app g a) (fun s => Step.appL a s) h1).trans
    (BetaEq.congr (fun b => Tm.app f' b) (fun s => Step.appR f' s) h2)

theorem BetaEq.lamC' {n : Nat} {Γ : Ctx n} (σ : Ty n) {L : Cat n} {b b' : Tm (.ext Γ σ) L} (h : BetaEq b b') :
    BetaEq (.lam σ b) (.lam σ b') := BetaEq.congr (fun c => Tm.lam σ c) (fun s => Step.lam σ s) h

theorem BetaEq.tlamC' {n : Nat} {Γ : Ctx n} {K : Cat (n+1)} {b b' : Tm (.text Γ) K} (h : BetaEq b b') :
    BetaEq (Tm.tlam b) (Tm.tlam b') := BetaEq.congr (fun c => Tm.tlam c) (fun s => Step.tlam s) h

theorem BetaEq.tappC {n : Nat} {Γ : Ctx n} {K : Cat (n+1)} {f f' : Tm Γ (.pi K)} (σ : Ty n) (h : BetaEq f f') :
    BetaEq (Tm.tapp f σ) (Tm.tapp f' σ) := BetaEq.congr (fun g => Tm.tapp g σ) (fun s => Step.tapp σ s) h

/-- Substituting for `here` after renaming with a lift is renaming after substituting. -/
theorem subst0_ren_heq {n m : Nat} {r : Fin n → Fin m} {Γ : Ctx n} {Δ : Ctx m} (ρ : TRen r Γ Δ) {σ : Ty n}
    {L : Cat n} (b : Tm (.ext Γ σ) L) (a : Tm Γ σ.1) :
    HEq ((b.ren (ρ.lift σ)).subst0 (a.ren ρ)) ((b.subst0 a).ren ρ) := by
  let σx : TSub (fun i => tvar (r i)) (.ext Γ σ) Δ := fun {L'} y =>
    Tm.castK (Cat.sub_ren_congr L' (fun _ => rfl)) ((sub0 (a.ren ρ)) ((ρ.lift σ) y))
  have h1 : HEq ((b.ren (ρ.lift σ)).subst0 (a.ren ρ)) (b.sub σx) :=
    (castK_heq _ _).trans (Tm.sub_ren_heq b (ρ.lift σ) rfl (sub0 (a.ren ρ)) σx (fun _ => rfl)
      (fun _ => (castK_heq _ _).symm))
  have h2 : HEq ((b.subst0 a).ren ρ) (b.sub σx) := by
    refine (ren_castK_heq _ _ _).trans (Tm.ren_sub_heq b (sub0 a) rfl ρ σx (fun _ => rfl) ?_)
    intro L' x
    cases x with
    | here => exact (ren_castK_heq _ _ _).trans ((castK_heq _ _).symm.trans (castK_heq _ _).symm)
    | there y => exact (ren_castK_heq _ _ _).trans ((castK_heq _ _).symm.trans (castK_heq _ _).symm)
  exact h1.trans h2.symm

theorem tinst_ren_heq {n m : Nat} {r : Fin n → Fin m} {Γ : Ctx n} {Δ : Ctx m} (ρ : TRen r Γ Δ)
    {K : Cat (n+1)} (b : Tm (.text Γ) K) (σ : Ty n) :
    HEq ((b.ren ρ.tlift).tinst (σ.ren r)) ((b.tinst σ).ren ρ) := by
  let st : Fin (n+1) → Ty m := fun i => (inst σ i).ren r
  let σx : TSub st (.text Γ) Δ := fun {L'} y =>
    Tm.castK (Cat.sub_ren_congr L' (fin_cases rfl (fun _ => rfl))) ((tsub0 Δ (σ.ren r)) (ρ.tlift y))
  have h1 : HEq ((b.ren ρ.tlift).tinst (σ.ren r)) (b.sub σx) :=
    Tm.sub_ren_heq b ρ.tlift rfl (tsub0 Δ (σ.ren r)) σx (fin_cases rfl (fun _ => rfl))
      (fun _ => (castK_heq _ _).symm)
  have h2 : HEq ((b.tinst σ).ren ρ) (b.sub σx) := by
    refine Tm.ren_sub_heq b (tsub0 Γ σ) rfl ρ σx (fun _ => rfl) ?_
    intro L' x
    cases x with
    | tthere y =>
      refine (ren_castK_heq _ _ _).trans ?_
      refine HEq.trans ?_ (castK_heq _ _).symm
      show HEq (Tm.var (ρ y)) ((tsub0 Δ (σ.ren r)) (Var.castK _ (Var.tthere (ρ y))))
      exact HEq.trans (by exact (castK_heq _ _).symm) (tsub_varCast_heq (tsub0 Δ (σ.ren r)) _ (Var.tthere (ρ y))).symm
  exact h1.trans h2.symm

theorem Step.ren {n : Nat} {Γ : Ctx n} {K : Cat n} {M N : Tm Γ K} (st : Step M N) :
    ∀ {m : Nat} {r : Fin n → Fin m} {Δ : Ctx m} (ρ : TRen r Γ Δ), Step (M.ren ρ) (N.ren ρ) := by
  induction st with
  | beta b a =>
    intro m r Δ ρ
    have e := eq_of_heq (subst0_ren_heq ρ b a)
    show Step (Tm.app (Tm.lam _ (b.ren (ρ.lift _))) (a.ren ρ)) _
    rw [← e]; exact Step.beta _ _
  | tbeta b σ =>
    intro m r Δ ρ
    show Step (Tm.castK _ (Tm.tapp (Tm.tlam (b.ren ρ.tlift)) (σ.ren r))) _
    have e := eq_of_heq ((castK_heq (Cat.tapp_ren _ σ r) ((b.ren ρ.tlift).tinst (σ.ren r))).trans (tinst_ren_heq ρ b σ))
    rw [← e]; exact Step.castKC _ (Step.tbeta _ _)
  | appL a _ ih => intro m r Δ ρ; exact Step.appL _ (ih ρ)
  | appR f _ ih => intro m r Δ ρ; exact Step.appR _ (ih ρ)
  | lam σ _ ih => intro m r Δ ρ; exact Step.lam _ (ih (ρ.lift σ))
  | tlam _ ih => intro m r Δ ρ; exact Step.tlam (ih ρ.tlift)
  | tapp σ _ ih => intro m r Δ ρ; exact Step.castKC _ (Step.tapp _ (ih ρ))

theorem BetaEq.ren {n : Nat} {Γ : Ctx n} {K : Cat n} {M N : Tm Γ K} (e : BetaEq M N)
    {m : Nat} {r : Fin n → Fin m} {Δ : Ctx m} (ρ : TRen r Γ Δ) : BetaEq (M.ren ρ) (N.ren ρ) :=
  BetaEq.congr (fun P => P.ren ρ) (fun s => Step.ren s ρ) e


/-- Extending a substitution by a term for `here`. -/
def TSub.cons {n m : Nat} {s : Fin n → Ty m} {Γ : Ctx n} {Δ : Ctx m} (σs : TSub s Γ Δ) {σ : Ty n}
    (N : Tm Δ (σ.1.sub s)) : TSub s (.ext Γ σ) Δ := fun {_} x =>
  match x with
  | .here => N
  | .there y => σs y

theorem wk_subst0_heq {n : Nat} {Γ : Ctx n} {τ : Ty n} {L : Cat n} (N : Tm Γ L) (κ : Tm Γ τ.1) :
    HEq ((N.wk τ).sub (sub0 κ)) N := by
  let σi : TSub tvar Γ Γ := fun {L'} x => Tm.castK (Cat.sub_var L').symm (Tm.var x)
  have h1 : HEq ((N.wk τ).sub (sub0 κ)) (N.sub σi) :=
    (sub_castK_heq _ _ _).trans (Tm.sub_ren_heq N (wkRen τ) rfl (sub0 κ) σi (fun _ => rfl)
      (fun x => tsub_varCast_heq (sub0 κ) _ (Var.there x)))
  exact h1.trans (Tm.sub_id_heq N rfl σi (fun _ => rfl) (fun _ => (castK_heq _ _).symm)).symm

theorem twk_tinst_heq {n : Nat} {Γ : Ctx n} (σ : Ty n) {L : Cat n} (N : Tm Γ L) :
    HEq (N.twk.sub (tsub0 Γ σ)) N := by
  let σi : TSub tvar Γ Γ := fun {L'} x => Tm.castK (Cat.sub_var L').symm (Tm.var x)
  have h1 : HEq (N.twk.sub (tsub0 Γ σ)) (N.sub σi) :=
    Tm.sub_ren_heq N (twkRen Γ) rfl (tsub0 Γ σ) σi (fun _ => rfl)
      (fun _ => (castK_heq _ _).trans (castK_heq _ _).symm)
  exact h1.trans (Tm.sub_id_heq N rfl σi (fun _ => rfl) (fun _ => (castK_heq _ _).symm)).symm

theorem subst0_sub_heq {n m : Nat} {s : Fin n → Ty m} {Γ : Ctx n} {Δ : Ctx m} (σs : TSub s Γ Δ) {σ : Ty n}
    {L : Cat n} (b : Tm (.ext Γ σ) L) (a : Tm Γ σ.1) :
    HEq ((b.sub (σs.lift σ)).subst0 (a.sub σs)) ((b.subst0 a).sub σs) := by
  have h1 : HEq ((b.sub (σs.lift σ)).subst0 (a.sub σs)) (b.sub (σs.cons (a.sub σs))) := by
    refine (castK_heq _ _).trans (Tm.sub_sub_heq b (σs.lift σ) rfl (sub0 (a.sub σs)) (σs.cons (a.sub σs))
      (fun i => Cat.sub_var _) ?_)
    intro L' x
    cases x with
    | here => exact castK_heq _ _
    | there y => exact wk_subst0_heq (τ := σ.sub s) (σs y) (a.sub σs)
  have h2 : HEq ((b.subst0 a).sub σs) (b.sub (σs.cons (a.sub σs))) := by
    refine (sub_castK_heq _ _ _).trans (Tm.sub_sub_heq b (sub0 a) rfl σs (σs.cons (a.sub σs)) (fun _ => rfl) ?_)
    intro L' x
    cases x with
    | here => exact sub_castK_heq _ _ _
    | there y => exact sub_castK_heq _ _ _
  exact h1.trans h2.symm

theorem tinst_sub_heq {n m : Nat} {s : Fin n → Ty m} {Γ : Ctx n} {Δ : Ctx m} (σs : TSub s Γ Δ)
    {K : Cat (n+1)} (b : Tm (.text Γ) K) (σ : Ty n) :
    HEq ((b.sub σs.tlift).tinst (σ.sub s)) ((b.tinst σ).sub σs) := by
  let st : Fin (n+1) → Ty m := fun i => (inst σ i).sub s
  let σy : TSub st (.text Γ) Δ := fun {_} x =>
    match x with
    | .tthere (K := L') y => Tm.castK (Cat.sub_ren_congr (r := fs) (s := st) (s' := s) L' (fun _ => rfl)).symm (σs y)
  have h1 : HEq ((b.sub σs.tlift).tinst (σ.sub s)) (b.sub σy) := by
    refine Tm.sub_sub_heq b σs.tlift rfl (tsub0 Δ (σ.sub s)) σy
      (fin_cases rfl (fun i => Cat.ren_fs_inst _ _)) ?_
    intro L' x
    cases x with
    | tthere y =>
      exact (sub_castK_heq _ _ _).trans ((twk_tinst_heq (σ.sub s) (σs y)).trans (castK_heq _ _).symm)
  have h2 : HEq ((b.tinst σ).sub σs) (b.sub σy) := by
    refine Tm.sub_sub_heq b (tsub0 Γ σ) rfl σs σy (fun _ => rfl) ?_
    intro L' x
    cases x with
    | tthere y => exact (sub_castK_heq _ _ _).trans (castK_heq _ _).symm
  exact h1.trans h2.symm

theorem Step.sub {n : Nat} {Γ : Ctx n} {K : Cat n} {M N : Tm Γ K} (st : Step M N) :
    ∀ {m : Nat} {s : Fin n → Ty m} {Δ : Ctx m} (σs : TSub s Γ Δ), Step (M.sub σs) (N.sub σs) := by
  induction st with
  | beta b a =>
    intro m s Δ σs
    have e := eq_of_heq (subst0_sub_heq σs b a)
    show Step (Tm.app (Tm.lam _ (b.sub (σs.lift _))) (a.sub σs)) _
    rw [← e]; exact Step.beta _ _
  | tbeta b σ =>
    intro m s Δ σs
    show Step (Tm.castK _ (Tm.tapp (Tm.tlam (b.sub σs.tlift)) (σ.sub s))) _
    have e := eq_of_heq ((castK_heq (Cat.tapp_sub _ σ s) ((b.sub σs.tlift).tinst (σ.sub s))).trans (tinst_sub_heq σs b σ))
    rw [← e]; exact Step.castKC _ (Step.tbeta _ _)
  | appL a _ ih => intro m s Δ σs; exact Step.appL _ (ih σs)
  | appR f _ ih => intro m s Δ σs; exact Step.appR _ (ih σs)
  | lam σ _ ih => intro m s Δ σs; exact Step.lam _ (ih (σs.lift σ))
  | tlam _ ih => intro m s Δ σs; exact Step.tlam (ih σs.tlift)
  | tapp σ _ ih => intro m s Δ σs; exact Step.castKC _ (Step.tapp _ (ih σs))

theorem BetaEq.sub {n : Nat} {Γ : Ctx n} {K : Cat n} {M N : Tm Γ K} (e : BetaEq M N)
    {m : Nat} {s : Fin n → Ty m} {Δ : Ctx m} (σs : TSub s Γ Δ) : BetaEq (M.sub σs) (N.sub σs) :=
  BetaEq.congr (fun P => P.sub σs) (fun st => Step.sub st σs) e

/-- Substituting β-equivalent terms gives β-equivalent results. -/
theorem Tm.sub_betaEq {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) :
    ∀ {m : Nat} {s : Fin n → Ty m} {Δ : Ctx m} (σa σb : TSub s Γ Δ),
      (∀ {L : Cat n} (x : Var Γ L), BetaEq (σa x) (σb x)) → BetaEq (M.sub σa) (M.sub σb) := by
  induction M with
  | var x => intro m s Δ σa σb hx; exact hx x
  | const c => intro m s Δ σa σb _; exact .refl _
  | app f a ihf iha => intro m s Δ σa σb hx; exact BetaEq.app2' (ihf σa σb hx) (iha σa σb hx)
  | lam σ b ih =>
    intro m s Δ σa σb hx
    refine BetaEq.lamC' _ (ih (σa.lift σ) (σb.lift σ) ?_)
    intro L x
    cases x with
    | here => exact .refl _
    | there y => exact BetaEq.castKC _ (BetaEq.ren (hx y) _)
  | tlam b ih =>
    intro m s Δ σa σb hx
    refine BetaEq.tlamC' (ih σa.tlift σb.tlift ?_)
    intro L x
    cases x with
    | tthere y => exact BetaEq.castKC _ (BetaEq.ren (hx y) _)
  | tapp f σ ih => intro m s Δ σa σb hx; exact BetaEq.castKC _ (BetaEq.tappC _ (ih σa σb hx))


/-- Derivability is closed under substitution. -/
theorem Prov.subst {Ax : Fm Ctx.nil → Prop} : ∀ {n : Nat} (Γ : Ctx n) (φ : Fm Γ), Prov Ax Γ φ →
    ∀ {m : Nat} {s : Fin n → Ty m} {Δ : Ctx m} (σs : TSub s Γ Δ), Prov Ax Δ (φ.sub σs)
  | _, .nil, φ, h, m, s, Δ, σs => by
    have e : φ.sub σs = φ.ren (Derive.nilRen Δ) := eq_of_heq (closed_sub_heq φ σs)
    rw [e]; exact Prov.ren _ h
  | _, .ext Γ τ, φ, h, m, s, Δ, σs => by
    let σs' : TSub s Γ Δ := fun x => σs (Var.there x)
    have h2 := Prov.subst Γ (Tm.all τ φ) (Prov.genAll τ h) σs'
    have h3 : Prov Ax Δ ((φ.sub (σs'.lift τ)).subst0 (σs .here)) := Prov.mp h2 (Prov.instAll (τ.sub s) _ (σs .here))
    have e : (φ.sub (σs'.lift τ)).subst0 (σs .here) = φ.sub σs := by
      refine eq_of_heq ((castK_heq _ _).trans (Tm.sub_sub_heq φ (σs'.lift τ) rfl (sub0 (σs .here)) σs
        (fun i => Cat.sub_var _) ?_))
      intro L x
      cases x with
      | here => exact castK_heq _ _
      | there y => exact wk_subst0_heq (τ := τ.sub s) (σs' y) (σs .here)
    rw [← e]; exact h3
  | _, .text Γ, φ, h, m, s, Δ, σs => by
    let σs' : TSub (fun i => s (fs i)) Γ Δ := fun {L} x =>
      Tm.castK (Cat.sub_ren_congr (r := fs) (s := s) (s' := fun i => s (fs i)) L (fun _ => rfl)) (σs (Var.tthere x))
    have h2 := Prov.subst Γ (Tm.tall φ) (Prov.genTAll h) σs'
    have h3 : Prov Ax Δ ((φ.sub σs'.tlift).tinst (s fz)) := Prov.mp h2 (Prov.instTAll _ (s fz))
    have e : (φ.sub σs'.tlift).tinst (s fz) = φ.sub σs := by
      refine eq_of_heq (Tm.sub_sub_heq φ σs'.tlift rfl (tsub0 Δ (s fz)) σs
        (fin_cases rfl (fun i => Cat.ren_fs_inst _ _)) ?_)
      intro L x
      cases x with
      | tthere y =>
        exact (sub_castK_heq _ _ _).trans ((twk_tinst_heq (s fz) (σs' y)).trans (castK_heq _ _))
    rw [← e]; exact h3

end SubLemmas

end PIF
