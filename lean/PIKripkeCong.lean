import PIKripkeHae

/-!
# Cong without LL≡/≈ (PI⁻)

`𝔐_k,cong`: three worlds; the actual world sees the other two, which see only themselves. There
are three entities, `0`, `1`, `2`. At the second world `0` and `1` are identical, and at the third
`1` and `2`. Any two items of one type are identified (`≡` is identity of types), and `≈` is
identity of types; so Cong holds trivially. A function on `e` must respect identity at every world,
and there are just eight such functions. Every one of them which is not constant takes the value
`1`, but one of them never takes the value `0`. So the polymorphic predicate "`z` is a value of every
non-constant function from its type to itself" is true of `1` and false of `0`, though `0 ≡ 1`.
-/
set_option autoImplicit false

namespace PIF
namespace Kr
open Tm

inductive W3 | a | b | c
deriving DecidableEq

def R1 (x y : Fin 3) : Prop := (x.val < 2 ∧ y.val < 2) ∨ x = y
def R2 (x y : Fin 3) : Prop := (0 < x.val ∧ 0 < y.val) ∨ x = y

def reC : W3 → Fin 3 → Fin 3 → Prop
  | .a => fun x y => x = y
  | .b => R1
  | .c => R2

theorem fin_eq_iff {x y : Fin 3} : x = y ↔ x.val = y.val := ⟨fun h => h ▸ rfl, Fin.ext⟩

def UC : Univ where
  W := W3
  w0 := .a
  R := fun w v => w = .a ∨ w = v
  Rrefl := fun _ => Or.inr rfl
  Rtrans := by
    intro u v w h1 h2
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · subst h1; exact h2
  E := Fin 3
  Base := Empty
  B := Empty.elim
  neE := ⟨0⟩
  neB := fun b => b.elim
  re := reC
  rb := fun _ b => b.elim
  re_refl := fun w x => by cases w <;> simp [reC, R1, R2]
  re_symm := fun w x y h => by
    cases w <;> simp only [reC, R1, R2, fin_eq_iff] at h ⊢ <;> omega
  re_trans := fun w x y z h1 h2 => by
    cases w <;> simp only [reC, R1, R2, fin_eq_iff] at h1 h2 ⊢ <;> omega
  re_mono := fun w v x y h hx => by
    rcases h with h | h
    · subst h; simp only [reC] at hx; subst hx; cases v <;> simp [reC, R1, R2]
    · subst h; exact hx
  rb_refl := fun _ b => b.elim
  rb_symm := fun _ b => b.elim
  rb_trans := fun _ b => b.elim
  rb_mono := fun _ _ b => b.elim
  D := fun _ _ => True
  D_e := fun _ => trivial
  D_t := fun _ => trivial
  D_arr := fun _ _ _ _ _ => trivial
  D_mono := fun _ _ _ _ _ => trivial

def KC : Frame where
  U := UC
  eqv := fun a b _ _ _ => a = b
  teq := fun a b _ => a = b
  eqv_resp := fun _ _ _ _ _ _ _ _ _ => Iff.rfl

theorem KC_isModelAt : KC.IsModelAt := by
  obtain ⟨h1, h2, h3⟩ := KC.idAx_of (fun _ _ _ _ => rfl) (fun _ _ _ _ _ h => h.symm)
    (fun _ _ _ _ _ _ _ h1 h2 => h1.trans h2)
  exact ⟨h1, h2, h3, KC.refTeq_of fun _ _ => rfl, fun Q => KC.llTeq_of_eq (fun _ _ _ h => h) Q⟩

/-- Leibniz identity. -/
def leib {n : Nat} {Γ : Ctx n} (σ : Ty n) (p q : Tm Γ σ.1) : Fm Γ :=
  all σ.pred (imp (.app (.var .here) (p.wk σ.pred)) (.app (.var .here) (q.wk σ.pred)))

/-- `λγ.λz:γ. ∀g:γ→γ ((∃w ∃w' ¬(g w = g w')) → ∃u (g u = z))`, with `=` Leibniz identity. -/
def PredC : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (all (tv0.arrow tv0)
    (imp (ex tv0 (ex tv0 (neg (leib tv0 (.app (.var (.there (.there .here))) (.var (.there .here)))
                                        (.app (.var (.there (.there .here))) (.var .here))))))
         (ex tv0 (leib tv0 (.app (.var (.there .here)) (.var .here)) (.var (.there (.there .here))))))))

/-- Leibniz identity at the actual world, on `e`. -/
def LeibS (p q : Fin 3) : Prop := ∀ F : Fin 3 → W3 → Prop, UC.rel (.arr .e .t) .a F F → F p .a → F q .a

def PCsem (x : Fin 3) : Prop :=
  ∀ g : Fin 3 → Fin 3, UC.rel (.arr .e .e) .a g g →
    (∃ w : Fin 3, UC.rel .e .a w w ∧ ∃ w' : Fin 3, UC.rel .e .a w' w' ∧ ¬ LeibS (g w) (g w')) →
    ∃ u : Fin 3, UC.rel .e .a u u ∧ LeibS (g u) x

set_option maxHeartbeats 4000000 in
theorem PredC_iff (x y : Fin 3) :
    KC.HoldsAt (.app (.tapp ((PredC.twk.twk.wk tv1).wk tv0) tv1) (.var (.there .here)))
      (scons .e (scons .e (fun i => i.elim0))) (((), x), y) .a ↔ PCsem x := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem PredC_iff0 (x y : Fin 3) :
    KC.HoldsAt (.app (.tapp ((PredC.twk.twk.wk tv1).wk tv0) tv0) (.var .here))
      (scons .e (scons .e (fun i => i.elim0))) (((), x), y) .a ↔ PCsem y := Iff.rfl

theorem LeibS_iff (p q : Fin 3) : LeibS p q ↔ p = q := by
  constructor
  · intro h
    have hF : UC.rel (.arr .e .t) .a (fun x (w : W3) => w = .a → x = p) (fun x (w : W3) => w = .a → x = p) := by
      intro v _ x y hxy u hu
      show (u = .a → x = p) ↔ (u = .a → y = p)
      by_cases hua : u = .a
      · subst hua
        have hva : v = .a := hu.elim id id
        subst hva
        have e : x = y := hxy
        subst e; exact Iff.rfl
      · exact ⟨fun _ h => absurd h hua, fun _ h => absurd h hua⟩
    have := h _ hF (fun _ => rfl)
    exact (this rfl).symm
  · intro e; subst e; exact fun _ _ h => h

theorem adm_ee {g : Fin 3 → Fin 3} (hg : UC.rel (.arr .e .e) .a g g) :
    R1 (g 0) (g 1) ∧ R2 (g 1) (g 2) :=
  ⟨hg .b (Or.inl rfl) (0 : Fin 3) (1 : Fin 3) (Or.inl ⟨by decide, by decide⟩),
    hg .c (Or.inl rfl) (1 : Fin 3) (2 : Fin 3) (Or.inl ⟨by decide, by decide⟩)⟩

theorem PCsem_one : PCsem 1 := by
  intro g hg ⟨w, _, w', _, hne⟩
  obtain ⟨h1, h2⟩ := adm_ee hg
  by_cases e0 : g 0 = 1
  · exact ⟨0, rfl, (LeibS_iff _ _).mpr e0⟩
  by_cases e1 : g 1 = 1
  · exact ⟨1, rfl, (LeibS_iff _ _).mpr e1⟩
  by_cases e2 : g 2 = 1
  · exact ⟨2, rfl, (LeibS_iff _ _).mpr e2⟩
  exfalso
  simp only [R1, R2, fin_eq_iff] at h1 h2 e0 e1 e2
  have hb0 := (g 0).isLt; have hb1 := (g 1).isLt; have hb2 := (g 2).isLt
  have c01 : g 0 = g 1 := Fin.ext (by omega)
  have c12 : g 1 = g 2 := Fin.ext (by omega)
  have hall : ∀ v : Fin 3, g v = g 0 := fun v => match v with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => c01.symm
    | ⟨2, _⟩ => (c01.trans c12).symm
  exact hne ((LeibS_iff _ _).mpr ((hall w).trans (hall w').symm))

def gC : Fin 3 → Fin 3 := fun i => if i.val = 0 then 1 else i

theorem gC_val (i : Fin 3) : (gC i).val = if i.val = 0 then 1 else i.val := by
  unfold gC; split <;> rfl

theorem gC_R1 (x y : Fin 3) (h : R1 x y) : R1 (gC x) (gC y) := by
  simp only [R1, fin_eq_iff] at h ⊢
  rw [gC_val, gC_val]
  have := x.isLt; have := y.isLt
  split <;> split <;> omega

theorem gC_R2 (x y : Fin 3) (h : R2 x y) : R2 (gC x) (gC y) := by
  simp only [R2, fin_eq_iff] at h ⊢
  rw [gC_val, gC_val]
  have := x.isLt; have := y.isLt
  split <;> split <;> omega

theorem gC_adm : UC.rel (.arr .e .e) .a gC gC := by
  intro v _ x y hxy
  cases v with
  | a => have e : x = y := hxy; subst e; rfl
  | b => exact gC_R1 x y hxy
  | c => exact gC_R2 x y hxy

theorem not_PCsem_zero : ¬ PCsem 0 := fun h => by
  have hne : ∃ w : Fin 3, UC.rel .e .a w w ∧ ∃ w' : Fin 3, UC.rel .e .a w' w' ∧ ¬ LeibS (gC w) (gC w') :=
    ⟨0, rfl, 2, rfl, fun hl => absurd ((LeibS_iff _ _).mp hl) (by decide)⟩
  obtain ⟨u, _, hu⟩ := h gC gC_adm hne
  have e := congrArg Fin.val ((LeibS_iff _ _).mp hu)
  rw [gC_val] at e
  split at e <;> simp at e <;> omega

/-- LL≡/≈ fails in `𝔐_k,cong`. -/
theorem KC_not_Bridge : ¬ KC.Valid (Bridge PredC) := fun h => by
  have h0 := h (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (KC.holdsAt_tall _ _ _ _).mp ((KC.holdsAt_tall _ _ _ _).mp h0 .e trivial) .e trivial
  have h2 := (KC.holdsAt_all _ _ _ _ _).mp ((KC.holdsAt_all _ _ _ _ _).mp h1 (1 : Fin 3) rfl) (0 : Fin 3) rfl
  have h3 := (KC.holdsAt_imp _ _ _ _ _).mp h2 ((KC.holdsAt_conj _ _ _ _ _).mpr
    ⟨(KC.holdsAt_eqv _ _ _ _ _ _ _).mpr rfl, (KC.holdsAt_teq _ _ _ _ _).mpr rfl⟩)
  have h4 := (KC.holdsAt_imp _ _ _ _ _).mp h3 ((PredC_iff 1 0).mpr PCsem_one)
  exact not_PCsem_zero ((PredC_iff0 1 0).mp h4)

theorem KC_Cong : KC.Valid Cong := by
  intro ρ _ env _
  refine (KC.holdsAt_tall _ _ _ _).mpr fun a _ => (KC.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (KC.holdsAt_tall _ _ _ _).mpr fun c _ => (KC.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (KC.holdsAt_all _ _ _ _ _).mpr fun f _ => (KC.holdsAt_all _ _ _ _ _).mpr fun g _ =>
    (KC.holdsAt_all _ _ _ _ _).mpr fun x _ => (KC.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (KC.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hc := (KC.holdsAt_conj _ _ _ _ _).mp h
  have e : (Code.arr a c : Code Empty) = .arr b d := (KC.holdsAt_eqv _ _ _ _ _ _ _).mp hc.1
  exact (KC.holdsAt_eqv _ _ _ _ _ _ _).mpr (Code.arr.inj e).2

end Kr
end PIF
