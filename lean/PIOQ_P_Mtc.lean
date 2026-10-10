import PIBF

/-!
# The profile of `𝔐_tc`

The model `MtcF` of `PIWorlds.lean`: tagged propositions (`PITagged.lean`), `E = 1`, every
quantified proposition carries the tag `false`, `≈` is identity of types, and `≡` relates two items
just when they are items of the same type and either identical or both true propositions.

* Since everything identified with `⊤` is true, and every true proposition is identified with `⊤`,
  `□φ` (that is, `φ ≡_t ⊤`) is equivalent to `φ`: so T and the Barcan formulas hold.
* Nothing is identified across types, so Disjoint, Slogan, Cantor, Ext≈ and Int≈ hold, and Twin
  and Haecceitism fail.
* The true propositions `(⊤, true)` and `(⊤, false)` are identified but differ in their tags; the
  full function spaces contain functions that tell them apart. So LL≡, Cong, WCong and PExt fail,
  and so does the polymorphic Leibniz law (the constant function to `x` at `e → t` is identical
  to the constant function to `⊤` just when `x` is `⊤` itself).
-/
set_option autoImplicit false

namespace PIF
namespace Tg
open Tm

/-! ## Identity of propositions, and `□` -/

/-- Identity of propositions in `𝔐_tc`. -/
theorem Mtc_eqv_t (p q : TV) : MtcF.eqv .t .t p q ↔ (p = q ∨ (p.1 ∧ q.1)) := by
  constructor
  · rintro ⟨_, e | ⟨s1, s2⟩⟩
    · exact Or.inl (eq_of_heq e)
    · exact Or.inr ⟨s1, s2⟩
  · rintro (e | ⟨h1, h2⟩)
    · exact ⟨rfl, Or.inl (heq_of_eq e)⟩
    · exact ⟨rfl, Or.inr ⟨h1, h2⟩⟩

/-- `⊤` is true. -/
theorem Mtc_top {n : Nat} {Γ : Ctx n} (ρ : MtcF.U.TEnv n) (env : MtcF.U.Env Γ ρ) :
    MtcF.Holds (topF : Fm Γ) ρ env :=
  (MtcF.holds_neg _ _ _).mpr fun hb => (MtcF.holds_all _ _ _ _).mp hb (False, true)

/-- `□φ` is equivalent to `φ`. -/
theorem Mtc_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MtcF.U.TEnv n) (env : MtcF.U.Env Γ ρ) :
    MtcF.Holds (boxF φ) ρ env ↔ MtcF.Holds φ ρ env := by
  refine (MtcF.holds_eqv_t _ _ _ _).trans ⟨fun h => ?_, fun h => ⟨rfl, Or.inr ⟨h, Mtc_top ρ env⟩⟩⟩
  rcases h.2 with e | ⟨s, _⟩
  · exact (congrArg Prod.fst (eq_of_heq e)).mpr (Mtc_top ρ env)
  · exact s

/-- A function that reads off the tag of a proposition. -/
def Mtc_tagF : TV → TV := fun p => ((p.2 = true : Prop), true)

/-- `(⊤, true)` and `(⊤, false)` are identified. -/
theorem Mtc_eqv_tags : MtcF.eqv .t .t ((True : Prop), true) ((True : Prop), false) :=
  (Mtc_eqv_t _ _).mpr (Or.inr ⟨trivial, trivial⟩)

/-- Their tags are not identified. -/
theorem Mtc_tagF_ne : ¬ MtcF.eqv .t .t (Mtc_tagF ((True : Prop), true)) (Mtc_tagF ((True : Prop), false)) :=
  fun h => by
    rcases (Mtc_eqv_t _ _).mp h with e | ⟨_, s⟩
    · exact Bool.noConfusion (cast (congrArg Prod.fst e) rfl : false = true)
    · exact Bool.noConfusion (s : false = true)

/-! ## T and Truth -/

theorem Mtc_TAx : MtcF.Valid TAx := by
  intro ρ env
  exact (MtcF.holds_all _ _ _ _).mpr fun _ => (MtcF.holds_imp _ _ _ _).mpr fun hb => (Mtc_box _ _ _).mp hb

theorem Mtc_Truth : MtcF.Valid Truth := by
  intro ρ env
  refine (MtcF.holds_all _ _ _ _).mpr fun p => (MtcF.holds_all _ _ _ _).mpr fun q => ?_
  refine (MtcF.holds_imp _ _ _ _).mpr fun h => (MtcF.holds_imp _ _ _ _).mpr fun hp => ?_
  rcases ((MtcF.holds_eqv_t _ _ _ _).mp h).2 with e | ⟨_, hq⟩
  · exact cast (congrArg Prod.fst (eq_of_heq e)) hp
  · exact hq

theorem Mtc_TopBot : MtcF.Valid TopBot := by
  intro ρ env h
  rcases ((MtcF.holds_eqv_t _ _ _ _).mp h).2 with e | ⟨_, s⟩
  · have e' := congrArg Prod.snd (eq_of_heq e)
    exact Bool.noConfusion (e'.trans (MtcF.eval_all_snd _ _ _ _) : true = false)
  · exact (MtcF.holds_all (Γ := Ctx.nil) tyT (.var .here) ρ env).mp s (False, true)

/-! ## Identity across types, and identity of types -/

theorem Mtc_Disjoint : MtcF.Valid Disjoint :=
  (MtcF.valid_iff_tr _).mpr <| MtcF.tr_Disjoint.mpr fun _ _ hn _ _ h => hn h.1

theorem Mtc_Slogan : MtcF.Valid Slogan :=
  (MtcF.valid_iff_tr _).mpr <| MtcF.tr_Slogan.mpr fun _ _ _ h => nomatch h.1

theorem Mtc_tr_Cantor : MtcF.Tr Cantor ↔ ∀ a, ∃ G : univU.El a → TV,
    ∀ y : univU.El a, ¬ MtcF.eqv (.arr a .t) a G y := Iff.rfl

theorem Mtc_Cantor : MtcF.Valid Cantor :=
  (MtcF.valid_iff_tr _).mpr <| Mtc_tr_Cantor.mpr fun a =>
    ⟨fun _ => ((True : Prop), true), fun _ h => Code.arr_ne_left a .t h.1⟩

theorem Mtc_not_Twin : ¬ MtcF.Valid Twin := fun h => by
  obtain ⟨_, hn, _, hy⟩ := MtcF.tr_Twin.mp ((MtcF.valid_iff_tr _).mp h) .e ()
  exact hn hy.1

theorem Mtc_not_Hae : ¬ MtcF.Valid Hae := fun h => by
  have e := (MtcF.tr_Hae.mp ((MtcF.valid_iff_tr _).mp h) .e ()).1
  cases e

theorem Mtc_Inj : MtcF.Valid Inj := (MtcF.valid_iff_tr _).mpr <| MtcF.tr_Inj.mpr fun _ _ _ _ h => by
  injection h with h1 h2; exact ⟨h1, h2⟩

theorem Mtc_Recovery : MtcF.Valid Recovery := (MtcF.valid_iff_tr _).mpr <|
  (show MtcF.Tr Recovery ↔ ∀ a b c d, MtcF.teq (.arr a c) (.arr b d) ∧ MtcF.teq a b → MtcF.teq c d
    from Iff.rfl).mpr fun _ _ _ _ ⟨h, _⟩ => by injection h

theorem Mtc_ExtT : MtcF.Valid ExtT := (MtcF.valid_iff_tr _).mpr <| MtcF.tr_ExtT.mpr fun a _ ⟨h, _⟩ => by
  obtain ⟨x0⟩ := Univ.El_nonempty (U := univU) a
  obtain ⟨_, hy⟩ := h x0
  exact hy.1

theorem Mtc_IntT : MtcF.Valid IntT := by
  intro ρ env a b hc
  have hc' := (MtcF.holds_conj _ _ _ _).mp hc
  exact Mtc_ExtT ρ env a b ⟨(Mtc_box _ _ _).mp hc'.1, (Mtc_box _ _ _).mp hc'.2⟩

/-! ## Leibniz's law and the congruence principles -/

theorem Mtc_not_LLEqv : ¬ MtcF.Valid LLEqv := fun h =>
  Bool.noConfusion (MtcF.tr_LLEqv.mp ((MtcF.valid_iff_tr _).mp h) .t ((True : Prop), true)
    ((True : Prop), false) Mtc_eqv_tags Mtc_tagF rfl : false = true)

theorem Mtc_not_Cong : ¬ MtcF.Valid Cong := fun h =>
  Mtc_tagF_ne (MtcF.tr_Cong.mp ((MtcF.valid_iff_tr _).mp h) .t .t .t .t Mtc_tagF Mtc_tagF
    ((True : Prop), true) ((True : Prop), false) ⟨⟨rfl, Or.inl HEq.rfl⟩, Mtc_eqv_tags⟩)

theorem Mtc_tr_WCong : MtcF.Tr WCong ↔ ∀ a b c d (f : univU.El a → univU.El c) (g : univU.El b → univU.El d) x y,
    (MtcF.teq a b ∧ MtcF.teq c d) ∧ (MtcF.eqv (.arr a c) (.arr b d) f g ∧ MtcF.eqv a b x y) →
    MtcF.eqv c d (f x) (g y) := Iff.rfl

theorem Mtc_not_WCong : ¬ MtcF.Valid WCong := fun h =>
  Mtc_tagF_ne (Mtc_tr_WCong.mp ((MtcF.valid_iff_tr _).mp h) .t .t .t .t Mtc_tagF Mtc_tagF
    ((True : Prop), true) ((True : Prop), false) ⟨⟨rfl, rfl⟩, ⟨rfl, Or.inl HEq.rfl⟩, Mtc_eqv_tags⟩)

theorem Mtc_PCong : MtcF.Valid PCong := by
  refine (MtcF.valid_iff_tr _).mpr ?_
  show ∀ a c d (f : univU.El a → univU.El c) (g : univU.El a → univU.El d) x,
    MtcF.eqv (.arr a c) (.arr a d) f g → MtcF.eqv c d (f x) (g x)
  intro a c d f g x h
  obtain ⟨e, h2⟩ := h
  injection e with _ ecd
  subst ecd
  rcases h2 with h2 | ⟨s, _⟩
  · rw [eq_of_heq h2]; exact clsEqv_refl Scol _ _
  · exact (s : False).elim

/-- `λx.(⊤, true)` and `λx.(⊤, false)` have identified values but are distinct functions. -/
theorem Mtc_not_PExt : ¬ MtcF.Valid PExt := fun h => by
  have h0 := MtcF.tr_PExt.mp ((MtcF.valid_iff_tr _).mp h) .e .t .t (fun _ => ((True : Prop), true))
    (fun _ => ((True : Prop), false)) (fun _ => Mtc_eqv_tags)
  rcases h0.2 with e | ⟨s, _⟩
  · exact Bool.noConfusion (congrArg Prod.snd (congrFun (eq_of_heq e) ()) : true = false)
  · exact (s : False).elim

/-! ## The polymorphic Leibniz law fails

The polymorphic predicate `λγ.λz:γ. (λu:e.z) ≡_{e→γ, e→t} (λu:e.⊤)` is true of `⊤` and false of
the true proposition `(⊤, false)` (functions are identified only with themselves). -/

def Mtc_PredTop : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (eqv (Ty.arrow tyE tv0) (Ty.arrow tyE tyT) (.lam tyE (.var (.there .here))) (.lam tyE topF)))

theorem Mtc_tr_LLPoly : MtcF.Tr (LLPoly Mtc_PredTop) ↔ ∀ a b (x : univU.El a) (y : univU.El b),
    MtcF.eqv a b x y →
    MtcF.eqv (.arr .e a) (.arr .e .t) (fun _ => x) (fun _ => ((¬ ∀ p : TV, p.1 : Prop), true)) →
    MtcF.eqv (.arr .e b) (.arr .e .t) (fun _ => y) (fun _ => ((¬ ∀ p : TV, p.1 : Prop), true)) := Iff.rfl

theorem Mtc_tr_Bridge : MtcF.Tr (Bridge Mtc_PredTop) ↔ ∀ a b (x : univU.El a) (y : univU.El b),
    MtcF.eqv a b x y ∧ MtcF.teq a b →
    MtcF.eqv (.arr .e a) (.arr .e .t) (fun _ => x) (fun _ => ((¬ ∀ p : TV, p.1 : Prop), true)) →
    MtcF.eqv (.arr .e b) (.arr .e .t) (fun _ => y) (fun _ => ((¬ ∀ p : TV, p.1 : Prop), true)) := Iff.rfl

/-- `⊤` and `(⊤, false)` are identified. -/
theorem Mtc_eqv_top : MtcF.eqv .t .t ((¬ ∀ p : TV, p.1 : Prop), true) ((True : Prop), false) :=
  (Mtc_eqv_t _ _).mpr (Or.inr ⟨fun hall => hall (False, true), trivial⟩)

/-- The constant function to `(⊤, false)` is not identified with the constant function to `⊤`. -/
theorem Mtc_const_ne : ¬ MtcF.eqv (.arr .e .t) (.arr .e .t) (fun _ => ((True : Prop), false))
    (fun _ => ((¬ ∀ p : TV, p.1 : Prop), true)) := fun h => by
  rcases h.2 with e | ⟨s, _⟩
  · exact Bool.noConfusion (congrArg Prod.snd (congrFun (eq_of_heq e) ()) : false = true)
  · exact (s : False).elim

theorem Mtc_not_LLPoly : ¬ MtcF.Valid (LLPoly Mtc_PredTop) := fun h =>
  Mtc_const_ne (Mtc_tr_LLPoly.mp ((MtcF.valid_iff_tr _).mp h) .t .t _ _ Mtc_eqv_top ⟨rfl, Or.inl HEq.rfl⟩)

theorem Mtc_not_Bridge : ¬ MtcF.Valid (Bridge Mtc_PredTop) := fun h =>
  Mtc_const_ne (Mtc_tr_Bridge.mp ((MtcF.valid_iff_tr _).mp h) .t .t _ _ ⟨Mtc_eqv_top, rfl⟩ ⟨rfl, Or.inl HEq.rfl⟩)

/-! ## The Identity Identity fails

`x ≡ y` has the tag `true` and `∀F(Fx → Fy)` has the tag `false`; so they are identified only when
both are true. At `x := ⊤`, `y := (⊥, true)` both are false. -/

theorem Mtc_tr_IdId : MtcF.Tr IdId ↔ ∀ a (x y : univU.El a), MtcF.eqv .t .t (MtcF.eqv a a x y, true)
    ((∀ P : univU.El a → TV, (P x).1 → (P y).1 : Prop), false) := Iff.rfl

theorem Mtc_not_IdId : ¬ MtcF.Valid IdId := fun h => by
  have h0 := Mtc_tr_IdId.mp ((MtcF.valid_iff_tr _).mp h) .t ((True : Prop), true) ((False : Prop), true)
  rcases (Mtc_eqv_t _ _).mp h0 with e | ⟨hxy, _⟩
  · exact Bool.noConfusion (congrArg Prod.snd e : true = false)
  · rcases (Mtc_eqv_t ((True : Prop), true) ((False : Prop), true)).mp hxy with e | ⟨_, hf⟩
    · exact cast (congrArg Prod.fst e) trivial
    · exact hf

/-! ## The Barcan formulas -/

theorem Mtc_TBF : ∀ χ, TBFSch χ → MtcF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MtcF.holds_imp _ _ _ _).mpr fun h => ?_
  exact (Mtc_box _ _ _).mpr ((MtcF.holds_tall _ _ _).mpr fun a =>
    (Mtc_box _ _ _).mp ((MtcF.holds_tall _ _ _).mp h a))

theorem Mtc_TCBF : ∀ χ, TCBFSch χ → MtcF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MtcF.holds_imp _ _ _ _).mpr fun h => ?_
  exact (MtcF.holds_tall _ _ _).mpr fun a => (Mtc_box _ _ _).mpr
    ((MtcF.holds_tall _ _ _).mp ((Mtc_box _ _ _).mp h) a)

theorem Mtc_BF : MtcF.Valid BF := by
  intro ρ env
  refine (MtcF.holds_tall _ _ _).mpr fun a => (MtcF.holds_all _ _ _ _).mpr fun G => ?_
  refine (MtcF.holds_imp _ _ _ _).mpr fun h => (Mtc_box _ _ _).mpr ?_
  exact (MtcF.holds_all _ _ _ _).mpr fun x => (Mtc_box _ _ _).mp ((MtcF.holds_all _ _ _ _).mp h x)

theorem Mtc_CBF : MtcF.Valid CBF := by
  intro ρ env
  refine (MtcF.holds_tall _ _ _).mpr fun a => (MtcF.holds_all _ _ _ _).mpr fun G => ?_
  refine (MtcF.holds_imp _ _ _ _).mpr fun h => (MtcF.holds_all _ _ _ _).mpr fun x => (Mtc_box _ _ _).mpr ?_
  exact (MtcF.holds_all _ _ _ _).mp ((Mtc_box _ _ _).mp h) x

end Tg
end PIF
