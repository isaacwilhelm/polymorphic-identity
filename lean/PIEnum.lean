import PISyntax

/-!
# Codes for terms

Each term gets a code, a list of natural numbers, and each list a number. Free variables are coded by
their *level* (counting from the start of the context) and bound variables by their index, so a term
keeps its code when its context is extended by a new variable at the end. Codes are injective within
a context. This gives, for each context, an enumeration of its formulas which is stable under the
extensions used in the Henkin construction.
-/
set_option autoImplicit false

namespace PIF

def Ctx.len {n : Nat} : Ctx n → Nat
  | .nil => 0
  | .ext Γ _ => Γ.len + 1
  | .text Γ => Γ.len + 1

def Var.pos {n : Nat} {Γ : Ctx n} {K : Cat n} : Var Γ K → Nat
  | .here => 0
  | .there y => y.pos + 1
  | .tthere y => y.pos + 1

theorem Var.pos_lt {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) : x.pos < Γ.len := by
  induction x with
  | here => exact Nat.succ_pos _
  | there _ ih => exact Nat.succ_lt_succ ih
  | tthere _ ih => exact Nat.succ_lt_succ ih

theorem Var.pos_castK {n : Nat} {Γ : Ctx n} {K K' : Cat n} (h : K = K') (x : Var Γ K) : (Var.castK h x).pos = x.pos := by
  subst h; rfl

theorem Var.pos_inj {n : Nat} {Γ : Ctx n} {K : Cat n} (x : Var Γ K) :
    ∀ {K' : Cat n} (y : Var Γ K'), x.pos = y.pos → K = K' ∧ HEq x y := by
  induction x with
  | here => intro K' y h; cases y with
    | here => exact ⟨rfl, HEq.rfl⟩
    | there _ => cases h
  | there x ih => intro K' y h; cases y with
    | here => cases h
    | there y => obtain ⟨e, h2⟩ := ih y (Nat.succ.inj h); subst e; cases h2; exact ⟨rfl, HEq.rfl⟩
  | tthere x ih => intro K' y h; cases y with
    | tthere y => obtain ⟨e, h2⟩ := ih y (Nat.succ.inj h); subst e; cases h2; exact ⟨rfl, HEq.rfl⟩

def Const.tag {n : Nat} {K : Cat n} : Const n K → Nat
  | .neg => 0 | .imp => 1 | .and => 2 | .or => 3 | .iff => 4 | .all => 5 | .ex => 6
  | .tall => 7 | .tex => 8 | .eqv => 9 | .teq => 10

theorem Const.tag_inj {n : Nat} {K K' : Cat n} (c : Const n K) (c' : Const n K') (h : c.tag = c'.tag) :
    K = K' ∧ HEq c c' := by
  cases c <;> cases c' <;> first | exact ⟨rfl, HEq.rfl⟩ | (simp [Const.tag] at h)

theorem Const.tag_ren {n m : Nat} (r : Fin n → Fin m) {K : Cat n} (c : Const n K) : (c.ren r).tag = c.tag := by
  cases c <;> rfl

/-- Codes of categories; `td` is the number of type binders above. -/
def codeCat {n : Nat} (td : Nat) : Cat n → List Nat
  | .e => [0]
  | .t => [1]
  | .var i => if i.val < td then [2, i.val] else [3, n - 1 - i.val]
  | .arr K L => 4 :: (codeCat td K ++ codeCat td L)
  | .pi K => 5 :: codeCat (td + 1) K

/-- Codes of terms; `d` is the number of binder entries above, and `td` the number of type binders. -/
def codeTm {n : Nat} {Γ : Ctx n} (d td : Nat) : {K : Cat n} → Tm Γ K → List Nat
  | _, .var x => if x.pos < d then [0, x.pos] else [1, Γ.len - 1 - x.pos]
  | _, .const c => [2, c.tag]
  | _, .app f a => 3 :: (codeTm d td f ++ codeTm d td a)
  | _, .lam σ b => 4 :: (codeCat td σ.1 ++ codeTm (d + 1) td b)
  | _, .tlam b => 5 :: codeTm (d + 1) (td + 1) b
  | _, .tapp f σ => 6 :: (codeTm d td f ++ codeCat td σ.1)

theorem codeTm_castK {n : Nat} {Γ : Ctx n} {K K' : Cat n} (h : K = K') (M : Tm Γ K) (d td : Nat) :
    codeTm d td (Tm.castK h M) = codeTm d td M := by
  subst h; rfl

/-! ## Injectivity -/

theorem codeCat_inj {n : Nat} (K : Cat n) : ∀ (K' : Cat n) (td : Nat) (l l' : List Nat),
    codeCat td K ++ l = codeCat td K' ++ l' → K = K' ∧ l = l' := by
  induction K with
  | e => intro K' td l l' h; cases K' <;> simp [codeCat] at h <;> (try split at h) <;> simp_all
  | t => intro K' td l l' h; cases K' <;> simp [codeCat] at h <;> (try split at h) <;> simp_all
  | var i =>
    intro K' td l l' h
    cases K' with
    | var j =>
      simp only [codeCat] at h
      split at h <;> split at h
      · simp at h; exact ⟨congrArg Cat.var (Fin.ext h.1), h.2⟩
      · simp at h
      · simp at h
      · simp at h
        have hi := i.isLt; have hj := j.isLt
        exact ⟨congrArg Cat.var (Fin.ext (by omega)), h.2⟩
    | _ => simp [codeCat] at h; split at h <;> simp at h
  | arr a b iha ihb =>
    intro K' td l l' h
    cases K' with
    | arr a' b' =>
      simp only [codeCat, List.cons_append, List.cons.injEq, List.append_assoc, true_and] at h
      obtain ⟨e1, h1⟩ := iha a' td _ _ h
      obtain ⟨e2, h2⟩ := ihb b' td _ _ h1
      subst e1; subst e2; exact ⟨rfl, h2⟩
    | var j => simp [codeCat] at h; split at h <;> simp at h
    | _ => simp [codeCat] at h
  | pi K ih =>
    intro K' td l l' h
    cases K' with
    | pi K' =>
      simp only [codeCat, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨e, h1⟩ := ih K' (td + 1) _ _ h
      subst e; exact ⟨rfl, h1⟩
    | var j => simp [codeCat] at h; split at h <;> simp at h
    | _ => simp [codeCat] at h


theorem codeVar_inj {n : Nat} {Γ : Ctx n} {K K' : Cat n} (x : Var Γ K) (y : Var Γ K') (d : Nat) (l l' : List Nat)
    (h : (if x.pos < d then [0, x.pos] else [1, Γ.len - 1 - x.pos]) ++ l =
      (if y.pos < d then [0, y.pos] else [1, Γ.len - 1 - y.pos]) ++ l') : K = K' ∧ HEq x y ∧ l = l' := by
  have hx := x.pos_lt; have hy := y.pos_lt
  split at h <;> split at h <;> simp at h
  · obtain ⟨e, h2⟩ := x.pos_inj y h.1; exact ⟨e, h2, h.2⟩
  · obtain ⟨e, h2⟩ := x.pos_inj y (by omega); exact ⟨e, h2, h.2⟩

theorem codeTm_inj {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) : ∀ {K' : Cat n} (M' : Tm Γ K') (d td : Nat)
    (l l' : List Nat), codeTm d td M ++ l = codeTm d td M' ++ l' → K = K' ∧ HEq M M' ∧ l = l' := by
  induction M with
  | var x =>
    intro K' M' d td l l' h
    cases M' with
    | var y => obtain ⟨e, h2, h3⟩ := codeVar_inj x y d l l' h; subst e; cases h2; exact ⟨rfl, HEq.rfl, h3⟩
    | _ => simp only [codeTm] at h; split at h <;> simp at h
  | const c =>
    intro K' M' d td l l' h
    cases M' with
    | const c' =>
      simp only [codeTm, List.cons_append, List.cons.injEq, true_and, List.nil_append] at h
      obtain ⟨e, h2⟩ := Const.tag_inj c c' h.1; subst e; cases h2; exact ⟨rfl, HEq.rfl, h.2⟩
    | var y => simp only [codeTm] at h; split at h <;> simp at h
    | _ => simp [codeTm] at h
  | app f a ihf iha =>
    intro K' M' d td l l' h
    cases M' with
    | app f' a' =>
      simp only [codeTm, List.cons_append, List.cons.injEq, List.append_assoc, true_and] at h
      obtain ⟨e1, h1, h2⟩ := ihf f' d td _ _ h
      obtain ⟨eA, eK⟩ := Cat.arr.inj e1
      subst eA; subst eK; cases h1
      obtain ⟨_, h3, h4⟩ := iha a' d td _ _ h2
      cases h3; exact ⟨rfl, HEq.rfl, h4⟩
    | var y => simp only [codeTm] at h; split at h <;> simp at h
    | _ => simp [codeTm] at h
  | lam σ b ih =>
    intro K' M' d td l l' h
    cases M' with
    | lam σ' b' =>
      simp only [codeTm, List.cons_append, List.cons.injEq, List.append_assoc, true_and] at h
      obtain ⟨e1, h1⟩ := codeCat_inj σ.1 σ'.1 td _ _ h
      have e : σ = σ' := Subtype.ext e1
      subst e
      obtain ⟨e2, h2, h3⟩ := ih b' (d + 1) td _ _ h1
      subst e2; cases h2; exact ⟨rfl, HEq.rfl, h3⟩
    | var y => simp only [codeTm] at h; split at h <;> simp at h
    | _ => simp [codeTm] at h
  | tlam b ih =>
    intro K' M' d td l l' h
    cases M' with
    | tlam b' =>
      simp only [codeTm, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨e2, h2, h3⟩ := ih b' (d + 1) (td + 1) _ _ h
      subst e2; cases h2; exact ⟨rfl, HEq.rfl, h3⟩
    | var y => simp only [codeTm] at h; split at h <;> simp at h
    | _ => simp [codeTm] at h
  | tapp f σ ih =>
    intro K' M' d td l l' h
    cases M' with
    | tapp f' σ' =>
      simp only [codeTm, List.cons_append, List.cons.injEq, List.append_assoc, true_and] at h
      obtain ⟨e1, h1, h2⟩ := ih f' d td _ _ h
      have eK := Cat.pi.inj e1
      subst eK; cases h1
      obtain ⟨e3, h3⟩ := codeCat_inj σ.1 σ'.1 td _ _ h2
      have e : σ = σ' := Subtype.ext e3
      subst e; exact ⟨rfl, HEq.rfl, h3⟩
    | var y => simp only [codeTm] at h; split at h <;> simp at h
    | _ => simp [codeTm] at h

theorem codeTm_inj' {n : Nat} {Γ : Ctx n} {K : Cat n} (M M' : Tm Γ K) (h : codeTm 0 0 M = codeTm 0 0 M') : M = M' := by
  have := codeTm_inj M M' 0 0 [] [] (by simpa using h)
  exact eq_of_heq this.2.1


/-! ## Stability under extending the context -/

/-- `ρ` inserts one new entry beneath `d` binder entries. -/
def InsAt {n m : Nat} {r : Fin n → Fin m} {Γ : Ctx n} {Δ : Ctx m} (d : Nat) (ρ : TRen r Γ Δ) : Prop :=
  (∀ {L : Cat n} (x : Var Γ L), (ρ x).pos = if x.pos < d then x.pos else x.pos + 1) ∧ Δ.len = Γ.len + 1

/-- `r` inserts `δ` new type variables beneath `td` type binders. -/
def InsT {n m : Nat} (td δ : Nat) (r : Fin n → Fin m) : Prop :=
  m = n + δ ∧ ∀ i, (r i).val = if i.val < td then i.val else i.val + δ

theorem InsT_liftR {n m : Nat} {td δ : Nat} {r : Fin n → Fin m} (h : InsT td δ r) : InsT (td + 1) δ (liftR r) := by
  refine ⟨by rw [h.1]; omega, fin_cases ?_ (fun i => ?_)⟩
  · show (0 : Nat) = if (0 : Nat) < td + 1 then 0 else 0 + δ
    simp
  · show (fs (r i)).val = if (fs i).val < td + 1 then (fs i).val else (fs i).val + δ
    have e : (r i).val = if i.val < td then i.val else i.val + δ := h.2 i
    simp only [fs]
    by_cases hi : i.val < td
    · simp [hi] at e; simp [hi, e]
    · simp [hi] at e; simp [hi, e]; omega

theorem InsAt_lift {n m : Nat} {r : Fin n → Fin m} {Γ : Ctx n} {Δ : Ctx m} {d : Nat} {ρ : TRen r Γ Δ}
    (h : InsAt d ρ) (σ : Ty n) : InsAt (d + 1) (ρ.lift σ) := by
  refine ⟨fun {L} x => ?_, by simp [Ctx.len, h.2]⟩
  cases x with
  | here =>
    show (0 : Nat) = if (0 : Nat) < d + 1 then 0 else 0 + 1
    simp
  | there y =>
    show (ρ y).pos + 1 = if y.pos + 1 < d + 1 then y.pos + 1 else y.pos + 1 + 1
    have e : (ρ y).pos = if y.pos < d then y.pos else y.pos + 1 := h.1 y
    by_cases hy : y.pos < d
    · simp [hy] at e; simp [hy, e]
    · simp [hy] at e; simp [hy, e]

theorem InsAt_tlift {n m : Nat} {r : Fin n → Fin m} {Γ : Ctx n} {Δ : Ctx m} {d : Nat} {ρ : TRen r Γ Δ}
    (h : InsAt d ρ) : InsAt (d + 1) ρ.tlift := by
  refine ⟨fun {L} x => ?_, by simp [Ctx.len, h.2]⟩
  cases x with
  | tthere y =>
    show (Var.castK _ (Var.tthere (ρ y))).pos = if y.pos + 1 < d + 1 then y.pos + 1 else y.pos + 1 + 1
    rw [Var.pos_castK]
    show (ρ y).pos + 1 = _
    have e : (ρ y).pos = if y.pos < d then y.pos else y.pos + 1 := h.1 y
    by_cases hy : y.pos < d
    · simp [hy] at e; simp [hy, e]
    · simp [hy] at e; simp [hy, e]

theorem codeCat_ren {n : Nat} (K : Cat n) : ∀ {m : Nat} {td δ : Nat} {r : Fin n → Fin m}, InsT td δ r →
    codeCat td (K.ren r) = codeCat td K := by
  induction K with
  | e => intros; rfl
  | t => intros; rfl
  | var i =>
    intro m td δ r h
    simp only [Cat.ren, codeCat]
    have e : (r i).val = if i.val < td then i.val else i.val + δ := h.2 i
    have e2 := h.1
    have hi := i.isLt
    by_cases hit : i.val < td
    · rw [ite_eq_left hit] at e; rw [ite_eq_left hit, ite_eq_left (show (r i).val < td by omega), e]
    · rw [ite_eq_right hit] at e
      rw [ite_eq_right hit, ite_eq_right (show ¬ (r i).val < td by omega), e]
      simp only [List.cons.injEq, and_true, true_and]
      omega
  | arr a b iha ihb =>
    intro m td δ r h
    show 4 :: (codeCat td (a.ren r) ++ codeCat td (b.ren r)) = _
    rw [iha h, ihb h]; rfl
  | pi K ih =>
    intro m td δ r h
    show 5 :: codeCat (td + 1) (K.ren (liftR r)) = _
    rw [ih (InsT_liftR h)]; rfl

theorem codeTm_ren {n : Nat} {Γ : Ctx n} {K : Cat n} (M : Tm Γ K) : ∀ {m : Nat} {r : Fin n → Fin m} {Δ : Ctx m}
    {ρ : TRen r Γ Δ} {d td δ : Nat}, InsAt d ρ → InsT td δ r → codeTm d td (M.ren ρ) = codeTm d td M := by
  induction M with
  | var x =>
    intro m r Δ ρ d td δ h ht
    show (if (ρ x).pos < d then [0, (ρ x).pos] else [1, Δ.len - 1 - (ρ x).pos]) =
      (if x.pos < d then [0, x.pos] else [1, _ - 1 - x.pos])
    have e : (ρ x).pos = if x.pos < d then x.pos else x.pos + 1 := h.1 x
    have e2 : Δ.len = _ := h.2
    have := x.pos_lt
    by_cases hx : x.pos < d
    · rw [ite_eq_left hx] at e; rw [ite_eq_left hx, ite_eq_left (show (ρ x).pos < d by omega), e]
    · rw [ite_eq_right hx] at e
      rw [ite_eq_right hx, ite_eq_right (show ¬ (ρ x).pos < d by omega), e, e2]
      simp only [List.cons.injEq, and_true, true_and]
      omega
  | const c => intro m r Δ ρ d td δ h ht; show [2, (c.ren r).tag] = [2, c.tag]; rw [Const.tag_ren]
  | app f a ihf iha =>
    intro m r Δ ρ d td δ h ht
    show 3 :: (codeTm d td (f.ren ρ) ++ codeTm d td (a.ren ρ)) = _
    rw [ihf h ht, iha h ht]; rfl
  | lam σ b ih =>
    intro m r Δ ρ d td δ h ht
    show 4 :: (codeCat td (σ.1.ren r) ++ codeTm (d + 1) td (b.ren (ρ.lift σ))) = _
    rw [codeCat_ren σ.1 ht, ih (InsAt_lift h σ) ht]; rfl
  | tlam b ih =>
    intro m r Δ ρ d td δ h ht
    show 5 :: codeTm (d + 1) (td + 1) (b.ren ρ.tlift) = _
    rw [ih (InsAt_tlift h) (InsT_liftR ht)]; rfl
  | tapp f σ ih =>
    intro m r Δ ρ d td δ h ht
    show codeTm d td (Tm.castK _ (Tm.tapp (f.ren ρ) (σ.ren r))) = _
    rw [codeTm_castK]
    show 6 :: (codeTm d td (f.ren ρ) ++ codeCat td (σ.1.ren r)) = _
    rw [ih h ht, codeCat_ren σ.1 ht]; rfl

theorem InsAt_wk {n : Nat} {Γ : Ctx n} (τ : Ty n) : InsAt 0 (wkRen (Γ := Γ) τ) :=
  ⟨fun x => by show (Var.castK _ (Var.there x)).pos = _; rw [Var.pos_castK]; simp [Var.pos], rfl⟩

theorem InsAt_twk {n : Nat} (Γ : Ctx n) : InsAt 0 (twkRen Γ) := ⟨fun x => by simp [twkRen, Var.pos], rfl⟩

theorem InsT_id {n : Nat} : InsT (n := n) 0 0 (fun i => i) := ⟨rfl, fun i => by simp⟩

theorem InsT_fs {n : Nat} : InsT (n := n) 0 1 fs := ⟨rfl, fun i => by simp [fs]⟩

/-! ## Numbers for codes -/

theorem pow_odd_inj : ∀ (a b c d : Nat), 2 ^ a * (2 * b + 1) = 2 ^ c * (2 * d + 1) → a = c ∧ b = d
  | 0, b, 0, d, h => by simp at h; omega
  | 0, b, c + 1, d, h => by
    have : 2 ^ (c + 1) * (2 * d + 1) = 2 * (2 ^ c * (2 * d + 1)) := by rw [Nat.pow_succ]; rw [Nat.mul_comm (2 ^ c) 2, Nat.mul_assoc]
    simp at h; omega
  | a + 1, b, 0, d, h => by
    have : 2 ^ (a + 1) * (2 * b + 1) = 2 * (2 ^ a * (2 * b + 1)) := by rw [Nat.pow_succ]; rw [Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]
    simp at h; omega
  | a + 1, b, c + 1, d, h => by
    have h1 : 2 ^ (a + 1) * (2 * b + 1) = 2 * (2 ^ a * (2 * b + 1)) := by rw [Nat.pow_succ]; rw [Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]
    have h2 : 2 ^ (c + 1) * (2 * d + 1) = 2 * (2 ^ c * (2 * d + 1)) := by rw [Nat.pow_succ]; rw [Nat.mul_comm (2 ^ c) 2, Nat.mul_assoc]
    have := pow_odd_inj a b c d (by omega)
    exact ⟨by omega, this.2⟩

def encL : List Nat → Nat
  | [] => 0
  | a :: l => 2 ^ a * (2 * encL l + 1)

theorem encL_pos (a : Nat) (l : List Nat) : 0 < encL (a :: l) :=
  Nat.mul_pos (Nat.two_pow_pos _) (Nat.succ_pos _)

theorem encL_inj : ∀ (l l' : List Nat), encL l = encL l' → l = l'
  | [], [], _ => rfl
  | [], a :: l', h => absurd h (Nat.ne_of_lt (encL_pos a l'))
  | a :: l, [], h => absurd h.symm (Nat.ne_of_lt (encL_pos a l))
  | a :: l, a' :: l', h => by
    obtain ⟨e1, e2⟩ := pow_odd_inj _ _ _ _ h
    rw [e1, encL_inj l l' e2]

/-- The number of a formula in its context. -/
def codeF {n : Nat} {Γ : Ctx n} (φ : Fm Γ) : Nat := encL (codeTm 0 0 φ)

theorem codeF_inj {n : Nat} {Γ : Ctx n} (φ ψ : Fm Γ) (h : codeF φ = codeF ψ) : φ = ψ :=
  codeTm_inj' φ ψ (encL_inj _ _ h)

theorem codeF_wk {n : Nat} {Γ : Ctx n} (τ : Ty n) (φ : Fm Γ) : codeF (φ.wk τ) = codeF φ :=
  congrArg encL ((codeTm_castK _ _ _ _).trans (codeTm_ren φ (InsAt_wk τ) InsT_id))

theorem codeF_twk {n : Nat} {Γ : Ctx n} (φ : Fm Γ) : codeF φ.twk = codeF φ :=
  congrArg encL (codeTm_ren φ (InsAt_twk Γ) InsT_fs)

/-- The formula with a given number, if there is one. -/
noncomputable def decodeF {n : Nat} (Γ : Ctx n) (c : Nat) : Fm Γ :=
  open Classical in if h : ∃ φ : Fm Γ, codeF φ = c then Classical.choose h else topF

theorem decodeF_codeF {n : Nat} {Γ : Ctx n} (φ : Fm Γ) : decodeF Γ (codeF φ) = φ := by
  unfold decodeF
  split
  · next h => exact codeF_inj _ _ (Classical.choose_spec h)
  · next h => exact absurd ⟨φ, rfl⟩ h

end PIF
