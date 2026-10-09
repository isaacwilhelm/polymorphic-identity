import PIAlg

/-!
# Models in the algebraic semantics

Countermodels for questions about Collapse, Booleanism, the Identity Identity, the necessity of
identity and distinctness, and Haecceitism, which the earlier semantics cannot settle.
-/
set_option autoImplicit false

namespace PIF
namespace Al

namespace Frame
variable (F : Frame)

theorem cast_all_eq {c : Code F.U.Base} {A' : Type} (hA : F.U.El c = A')
    (h : ((F.U.El c → F.U.P) → F.U.P) = ((A' → F.U.P) → F.U.P)) (Q : A' → F.U.P) :
    cast h (fun R => F.all c R) Q = F.all c (fun x => Q (cast hA x)) := by
  subst hA; rfl

/-- The value of a universal quantification. -/
theorem eval_all {n : Nat} {Γ : Ctx n} (σ : Ty n) (φ : Fm (.ext Γ σ)) (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) :
    F.eval (Tm.all σ φ) ρ env = F.all (F.U.code σ.1 ρ) (fun x => F.eval φ ρ (env, cast (Univ.El_code ρ σ.2) x)) :=
  F.cast_all_eq (Univ.El_code ρ σ.2) _ _

theorem holds_topF {n : Nat} {Γ : Ctx n} (ρ : F.U.TEnv n) (env : F.U.Env Γ ρ) (hp : ∃ p, ¬ F.U.V p) :
    F.Holds (topF : Fm Γ) ρ env :=
  (F.holds_neg _ ρ env).mpr fun hb => let ⟨p, hp⟩ := hp; hp ((F.holds_all _ _ ρ env).mp hb p)

end Frame

/-! ## `𝔐_cl`: Collapse and LL≡ without Booleanism

There is exactly one true proposition, `⊤`; the false propositions carry a tag, which is `true`
for the values of the connectives and of `≡` and `≈`, and `false` for the values of the
quantifiers. Identity is identity. -/

open Classical in
noncomputable def mkA (c : Prop) : Option Bool := if c then none else some true
open Classical in
noncomputable def qA (c : Prop) : Option Bool := if c then none else some false

theorem mkA_V (c : Prop) : mkA c = none ↔ c := by unfold mkA; by_cases h : c <;> simp [h]
theorem qA_V (c : Prop) : qA c = none ↔ c := by unfold qA; by_cases h : c <;> simp [h]
theorem mkA_neg {c : Prop} (h : ¬ c) : mkA c = some true := by unfold mkA; simp [h]
theorem mkA_pos {c : Prop} (h : c) : mkA c = none := by unfold mkA; simp [h]
theorem qA_neg {c : Prop} (h : ¬ c) : qA c = some false := by unfold qA; simp [h]

def univA : Univ where
  P := Option Bool
  V := fun p => p = none
  p0 := none
  E := Unit
  Base := Empty
  B := Empty.elim
  neE := ⟨()⟩
  neB := fun b => b.elim

noncomputable def MclF : Frame where
  U := univA
  eqv := fun a b x y => mkA (a = b ∧ HEq x y)
  teq := fun a b => mkA (a = b)
  neg := fun p => mkA (¬ p = none)
  imp := fun p q => mkA (p = none → q = none)
  cnj := fun p q => mkA (p = none ∧ q = none)
  dsj := fun p q => mkA (p = none ∨ q = none)
  bic := fun p q => mkA (p = none ↔ q = none)
  all := fun _ f => qA (∀ x, f x = none)
  ex := fun _ f => qA (∃ x, f x = none)
  tall := fun Q => qA (∀ a, Q a = none)
  tex := fun Q => qA (∃ a, Q a = none)
  hneg := fun _ => mkA_V _
  himp := fun _ _ => mkA_V _
  hcnj := fun _ _ => mkA_V _
  hdsj := fun _ _ => mkA_V _
  hbic := fun _ _ => mkA_V _
  hall := fun _ _ => qA_V _
  hex := fun _ _ => qA_V _
  htall := fun _ => qA_V _
  htex := fun _ => qA_V _

theorem Mcl_model : MclF.IsModelPIm :=
  MclF.model_of_equiv (fun _ _ => mkA_V _) (fun _ _ => (mkA_V _).mpr ⟨rfl, HEq.rfl⟩)
    (fun _ _ _ _ h => (mkA_V _).mpr (((mkA_V _).mp h).elim fun e h' => ⟨e.symm, h'.symm⟩))
    (fun _ _ _ _ _ _ h1 h2 => (mkA_V _).mpr (((mkA_V _).mp h1).elim fun e1 h1' =>
      ((mkA_V _).mp h2).elim fun e2 h2' => ⟨e1.trans e2, h1'.trans h2'⟩))

theorem Mcl_topF {n : Nat} {Γ : Ctx n} (ρ : MclF.U.TEnv n) (env : MclF.U.Env Γ ρ) :
    MclF.eval (topF : Fm Γ) ρ env = none :=
  MclF.holds_topF ρ env ⟨some true, fun h => nomatch (h : (some true : Option Bool) = none)⟩

theorem Mcl_LLEqv : MclF.Valid LLEqv := by
  intro ρ env
  refine (MclF.holds_tall _ _ _).mpr fun a => ?_
  refine (MclF.holds_all _ _ _ _).mpr fun x => (MclF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MclF.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (MclF.holds_all _ _ _ _).mpr fun G => (MclF.holds_imp _ _ _ _).mpr fun hGx => ?_
  have h := ((mkA_V _).mp ((MclF.holds_eqv _ _ _ _ _ _).mp hxy)).2
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.trans (cast_heq _ _)))
  subst e
  exact hGx

theorem Mcl_Collapse : MclF.Valid Collapse := by
  intro ρ env
  refine (MclF.holds_all _ _ _ _).mpr fun p => (MclF.holds_imp _ _ _ _).mpr fun hp => ?_
  refine (MclF.holds_eqv_t _ _ _ _).mpr ((mkA_V _).mpr ⟨rfl, ?_⟩)
  have hp' : p = none := hp
  exact heq_of_eq (hp'.trans (Mcl_topF (Γ := Ctx.nil.ext tyT) ρ (env, p)).symm)

theorem Mcl_not_DNeg : ¬ MclF.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MclF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (some false)
  have e := eq_of_heq ((mkA_V _).mp ((MclF.holds_eqv_t _ _ _ _).mp h0)).2
  have e1 : MclF.neg (some false) = none := mkA_pos (fun h => nomatch (h : (some false : Option Bool) = none))
  have e2 : MclF.neg none = some true := mkA_neg (fun h => h rfl)
  have e3 : MclF.eval (Tm.neg (Tm.neg (.var .here)) : Fm (Ctx.nil.ext tyT)) (fun i => i.elim0) ((), some false) = some true := by
    show MclF.neg (MclF.neg (some false)) = some true
    rw [e1, e2]
  rw [e3] at e
  exact Bool.noConfusion (Option.some.inj e)

theorem Mcl_not_Bool : ¬ ∀ φ, BoolSch φ → MclF.Valid φ := fun h => Mcl_not_DNeg (h _ DNeg_bool)

theorem Mcl_not_IdId : ¬ MclF.Valid IdId := fun h => by
  have h0 := (MclF.holds_all _ _ _ _).mp ((MclF.holds_all _ _ _ _).mp
    ((MclF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) none) (some false)
  have e := eq_of_heq ((mkA_V _).mp ((MclF.holds_eqv_t _ _ _ _).mp h0)).2
  have hE : MclF.eqv .t .t none (some false) = some true :=
    mkA_neg (fun h => nomatch (eq_of_heq h.2 : (none : Option Bool) = some false))
  have hA : MclF.all (.arr .t .t) (fun G => MclF.imp (G none) (G (some false))) = some false :=
    qA_neg (fun h => nomatch ((mkA_V _).mp (h (fun p => p)) rfl : (some false : Option Bool) = none))
  exact Bool.noConfusion (Option.some.inj (hE.symm.trans ((MclF.eval_eqv _ _ _ _ _ _).symm.trans
    (e.trans ((MclF.eval_all _ _ _ _).trans hA)))))

/-! ## `𝔐_ii`: the Identity Identity without NI≡ or Booleanism

Propositions are truth values with a tag; the values of `≡` and of the quantifiers have tag
`false`, those of `≈` and the connectives tag `true`. Identity is identity. -/

def univI : Univ where
  P := Prop × Bool
  V := fun p => p.1
  p0 := (True, true)
  E := Unit
  Base := Empty
  B := Empty.elim
  neE := ⟨()⟩
  neB := fun b => b.elim

def MiiF : Frame where
  U := univI
  eqv := fun a b x y => (a = b ∧ HEq x y, false)
  teq := fun a b => (a = b, true)
  neg := fun p => (¬ p.1, true)
  imp := fun p q => (p.1 → q.1, true)
  cnj := fun p q => (p.1 ∧ q.1, true)
  dsj := fun p q => (p.1 ∨ q.1, true)
  bic := fun p q => (p.1 ↔ q.1, true)
  all := fun _ f => (∀ x, (f x).1, false)
  ex := fun _ f => (∃ x, (f x).1, false)
  tall := fun Q => (∀ a, (Q a).1, false)
  tex := fun Q => (∃ a, (Q a).1, false)
  hneg := fun _ => Iff.rfl
  himp := fun _ _ => Iff.rfl
  hcnj := fun _ _ => Iff.rfl
  hdsj := fun _ _ => Iff.rfl
  hbic := fun _ _ => Iff.rfl
  hall := fun _ _ => Iff.rfl
  hex := fun _ _ => Iff.rfl
  htall := fun _ => Iff.rfl
  htex := fun _ => Iff.rfl

theorem Mii_model : MiiF.IsModelPIm :=
  MiiF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => ⟨rfl, HEq.rfl⟩) (fun _ _ _ _ h => ⟨h.1.symm, h.2.symm⟩)
    (fun _ _ _ _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)

theorem Mii_LLEqv : MiiF.Valid LLEqv := by
  intro ρ env
  refine (MiiF.holds_tall _ _ _).mpr fun a => ?_
  refine (MiiF.holds_all _ _ _ _).mpr fun x => (MiiF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MiiF.holds_imp _ _ _ _).mpr fun hxy => ?_
  refine (MiiF.holds_all _ _ _ _).mpr fun G => (MiiF.holds_imp _ _ _ _).mpr fun hGx => ?_
  have h := ((MiiF.holds_eqv _ _ _ _ _ _).mp hxy).2
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.trans (cast_heq _ _)))
  subst e
  exact hGx

theorem Mii_IdId : MiiF.Valid IdId := by
  intro ρ env
  refine (MiiF.holds_tall _ _ _).mpr fun a => ?_
  refine (MiiF.holds_all _ _ _ _).mpr fun x => (MiiF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MiiF.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine (MiiF.eval_eqv _ _ _ _ _ _).trans (Eq.trans ?_ (MiiF.eval_all _ _ _ _).symm)
  refine Prod.ext (propext ⟨fun h G hG => ?_, fun h => ?_⟩) rfl
  · have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (h.2.trans (cast_heq _ _)))
    subst e; exact hG
  · have hy : HEq y x := h (fun z => (HEq z x, true)) (by exact HEq.rfl)
    exact ⟨rfl, (cast_heq _ _).trans (hy.symm.trans (cast_heq _ _).symm)⟩

theorem Mii_not_NIEqv : ¬ MiiF.Valid NIEqv := fun h => by
  have h0 := (MiiF.holds_all _ _ _ _).mp ((MiiF.holds_all _ _ _ _).mp
    ((MiiF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()) ()
  have hb := (MiiF.holds_imp _ _ _ _).mp h0 ((MiiF.holds_eqv _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩)
  have e := eq_of_heq ((MiiF.holds_eqv_t _ _ _ _).mp hb).2
  exact Bool.noConfusion (congrArg Prod.snd e : false = true)

theorem Mii_not_DNeg : ¬ MiiF.Valid DNeg := fun h => by
  rw [DNeg_eq] at h
  have h0 := (MiiF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (True, false)
  have e := eq_of_heq ((MiiF.holds_eqv_t _ _ _ _).mp h0).2
  exact Bool.noConfusion (congrArg Prod.snd e : true = false)

theorem Mii_not_Bool : ¬ ∀ φ, BoolSch φ → MiiF.Valid φ := fun h => Mii_not_DNeg (h _ DNeg_bool)

end Al
end PIF

/-! ## The Identity Identity in some standard models (PI⁻) -/

namespace PIF

theorem Mall_IdId : Mall.Valid IdId :=
  (Mall.valid_iff_tr _).mpr <| Mall.tr_IdId.mpr fun _ _ _ => trivial

/-- `𝔐_E,k` with, in addition, all propositions identified with each other. -/
def SEkT : (c : Code Empty) → univ3.El c → Prop
  | .e, v => v = (0 : Fin 3) ∨ v = (1 : Fin 3)
  | .arr .e .e, f => f = k1 ∨ f = k2
  | .t, _ => True
  | _, _ => False

def MEkTD : IdentData := classIdent univ3 SEkT
abbrev MEkT : Frame := MEkTD.frame
theorem MEkT_model : MEkT.IsModelPIm := MEkTD.model

theorem MEkT_IdId : MEkT.Valid IdId :=
  (MEkT.valid_iff_tr _).mpr <| MEkT.tr_IdId.mpr fun _ _ _ => ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩

theorem MEkT_K0 : MEkT.Kf .e (0 : Fin 3) :=
  ⟨k1, k2, ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩, fun P h => (show k1 0 = 0 by decide) ▸ h,
    fun hL => absurd (hL (fun v : Fin 3 => v = 1) (show k2 0 = 1 by decide)) (show ¬ (0 : Fin 3) = 1 by decide)⟩

theorem MEkT_not_K1 : ¬ MEkT.Kf .e (1 : Fin 3) := by
  rintro ⟨f, g, ⟨_, hfg⟩, hf, hg⟩
  rcases hfg with hfg | ⟨hS, _⟩
  · have e : f = g := eq_of_heq hfg
    subst e; exact hg hf
  · have key : ∀ u : Fin 3 → Fin 3, (u = k1 ∨ u = k2) → u 1 = (0 : Fin 3) := by
      intro u hu; rcases hu with rfl | rfl <;> decide
    exact absurd (hf (fun v : Fin 3 => v = (0 : Fin 3)) (key f hS)) (show ¬ (1 : Fin 3) = 0 by decide)

theorem MEkT_not_Bridge : ¬ MEkT.Valid (Bridge PredK) := fun h =>
  MEkT_not_K1 (MEkT.tr_BridgeK.mp ((MEkT.valid_iff_tr _).mp h) .e .e (0 : Fin 3) (1 : Fin 3)
    ⟨⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩, rfl⟩ MEkT_K0)

theorem MEkT_not_WCong : ¬ MEkT.Valid WCong := fun h => by
  have := MEkT.tr_WCong.mp ((MEkT.valid_iff_tr _).mp h) .e .e .e .e
    (fun v : Fin 3 => if v = 0 then (0 : Fin 3) else (2 : Fin 3)) (fun v : Fin 3 => if v = 0 then (0 : Fin 3) else (2 : Fin 3))
    (0 : Fin 3) (1 : Fin 3)
    ⟨⟨rfl, rfl⟩, ⟨⟨rfl, Or.inl HEq.rfl⟩, ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩⟩⟩
  rcases this.2 with e | ⟨_, s⟩
  · have e' : (if (0 : Fin 3) = 0 then (0 : Fin 3) else (2 : Fin 3)) = (if (1 : Fin 3) = 0 then (0 : Fin 3) else (2 : Fin 3)) :=
      eq_of_heq e
    exact absurd e' (by decide)
  · have s' : (if (1 : Fin 3) = 0 then (0 : Fin 3) else (2 : Fin 3)) = 0 ∨
        (if (1 : Fin 3) = 0 then (0 : Fin 3) else (2 : Fin 3)) = 1 := s
    exact absurd s' (by decide)

end PIF
