import PIBF
set_option autoImplicit false

namespace PIF
namespace Wd

/-!
# Open questions: the profile of `𝔐_nec`

`𝔐_nec` (`lean/PIBF.lean`, `MNecF`): two worlds, the actual one `true`, and two entities. At the
actual world, identity of items is identity (same type, same item); at the other world, items of a
type are identified just in case they are distinct. `≈` is identity of types, at every world.

So at the actual world nothing is identified across types: Disjoint, the Slogan, LL≡-Poly, Cong,
PCong, PExt, Inj≈, Recovery, Ext≈ and Int≈ hold, while Twin and Haecceitism fail. Identity of
propositions is identity, so Booleanism and TBF hold. `≈` does not depend on the world, so NI≈,
ND≈, TCBF and TNec hold. But two distinct entities are identified at the other world, so ND×
fails; and an entity is not self-identical there, so the Identity Identity fails.
-/

/-! ## Basic facts -/

/-- Where identity of propositions is identity, `□φ` is truth at both worlds. -/
theorem MNec_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MNecF.U.TEnv n) (env : MNecF.U.Env Γ ρ) :
    MNecF.Holds (boxF φ) ρ env ↔ ∀ w, MNecF.HoldsAt φ ρ env w := by
  refine ⟨fun h w => MNecF.box_all (fun p q hpq => (MNec_hb p q).mp hpq) φ ρ env h w, fun h => ?_⟩
  refine (MNecF.holdsAt_eqv_t φ topF ρ env _).mpr ?_
  rw [MNecF.eval_topF]
  exact ⟨rfl, heq_of_eq (funext fun w => propext ⟨fun _ => trivial, fun _ => h w⟩)⟩

theorem MNec_holdsAt_tex {n : Nat} {Γ : Ctx n} (φ : Fm Γ.text) (ρ : MNecF.U.TEnv n) (env : MNecF.U.Env Γ ρ)
    (w : Bool) : MNecF.HoldsAt (Tm.tex φ) ρ env w ↔ ∃ a, MNecF.HoldsAt φ (scons a ρ) env w := Iff.rfl

/-! ## Identity across types -/

theorem MNec_Disjoint : MNecF.Valid Disjoint :=
  (MNecF.valid_iff_tr _).mpr <| MNecF.tr_Disjoint.mpr fun _ _ hn _ _ h => hn h.1

theorem MNec_Slogan : MNecF.Valid Slogan :=
  (MNecF.valid_iff_tr _).mpr <| MNecF.tr_Slogan.mpr fun _ _ _ h => nomatch h.1

theorem MNec_tr_Twin : MNecF.Tr Twin ↔ ∀ a (x : MNecF.U.El a), ∃ b, ¬ MNecF.teq a b MNecF.U.w0 ∧
    ∃ y : MNecF.U.El b, MNecF.eqv a b x y MNecF.U.w0 := Iff.rfl

/-- At the actual world an item is identified only with items of its own type. -/
theorem MNec_not_Twin : ¬ MNecF.Valid Twin := fun h => by
  obtain ⟨_, hb, _, hy⟩ := MNec_tr_Twin.mp ((MNecF.valid_iff_tr _).mp h) .e (true : MNecF.U.El .e)
  exact hb hy.1

theorem MNec_tr_Hae : MNecF.Tr Hae ↔
    ∀ a (x : MNecF.U.El a), MNecF.eqv a (.arr a .t) x (fun y => MNecF.eqv a a y x) MNecF.U.w0 := Iff.rfl

/-- Haecceitism fails: `e` and `e→t` are distinct types. -/
theorem MNec_not_Hae : ¬ MNecF.Valid Hae := fun h =>
  nomatch (MNec_tr_Hae.mp ((MNecF.valid_iff_tr _).mp h) .e (true : MNecF.U.El .e)).1

/-- Every instance of LL≡-Poly, parameters allowed: at the actual world, identified items are the
same item of the same type. -/
theorem MNec_LLPoly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : MNecF.Valid (LLPoly P) := by
  intro ρ env
  refine (MNecF.holds_tall _ _ _).mpr fun a => (MNecF.holds_tall _ _ _).mpr fun b => ?_
  refine (MNecF.holds_all _ _ _ _).mpr fun x => (MNecF.holds_all _ _ _ _).mpr fun y => ?_
  refine (MNecF.holds_imp _ _ _ _).mpr fun hxy => (MNecF.holds_imp _ _ _ _).mpr fun hPx => ?_
  obtain ⟨hab, hxy'⟩ := (MNecF.holds_eqv _ _ _ _ _ _).mp hxy
  have hab' : a = b := hab
  subst hab'
  have hxy'' : HEq (cast (Univ.El_code (scons a (scons a ρ)) tv1.2).symm x)
      (cast (Univ.El_code (scons a (scons a ρ)) tv0.2).symm y) := hxy'
  have e : x = y := eq_of_heq ((cast_heq _ _).symm.trans (hxy''.trans (cast_heq _ _)))
  subst e
  exact hPx

/-! ## Congruence and extensionality -/

theorem MNec_cong_core (a b c d : Code Empty) (f : MNecF.U.El a → MNecF.U.El c) (g : MNecF.U.El b → MNecF.U.El d)
    (x : MNecF.U.El a) (y : MNecF.U.El b)
    (h1 : MNecF.eqv (.arr a c) (.arr b d) f g MNecF.U.w0) (h2 : MNecF.eqv a b x y MNecF.U.w0) :
    MNecF.eqv c d (f x) (g y) MNecF.U.w0 := by
  obtain ⟨e1, hf⟩ := h1
  obtain ⟨_, hx⟩ := h2
  injection e1 with ea ec
  subst ea; subst ec
  exact ⟨rfl, heq_app rfl rfl hf hx⟩

/-- At the actual world identified functions are the same function, so Cong holds. -/
theorem MNec_Cong : MNecF.Valid Cong :=
  (MNecF.valid_iff_tr _).mpr <| MNecF.tr_Cong.mpr fun a b c d f g x y ⟨h1, h2⟩ =>
    MNec_cong_core a b c d f g x y h1 h2

theorem MNec_tr_PCong : MNecF.Tr PCong ↔ ∀ a c d (f : MNecF.U.El a → MNecF.U.El c)
    (g : MNecF.U.El a → MNecF.U.El d) x,
    MNecF.eqv (.arr a c) (.arr a d) f g MNecF.U.w0 → MNecF.eqv c d (f x) (g x) MNecF.U.w0 := Iff.rfl

theorem MNec_PCong : MNecF.Valid PCong :=
  (MNecF.valid_iff_tr _).mpr <| MNec_tr_PCong.mpr fun a c d f g x h =>
    MNec_cong_core a a c d f g x x h ⟨rfl, HEq.rfl⟩

/-- Functions that agree argument by argument, at the actual world, have the same codomain and are
equal. -/
theorem MNec_PExt : MNecF.Valid PExt :=
  (MNecF.valid_iff_tr _).mpr <| MNecF.tr_PExt.mpr fun a c d f g h => by
    have x0 := Classical.choice (Univ.El_nonempty (U := univNB) a)
    have ec : c = d := (h x0).1
    subst ec
    exact ⟨rfl, heq_of_eq (funext fun x => eq_of_heq (h x).2)⟩

/-- Ext≈: if some item of `α` is identified with an item of `β`, then `α` is `β`. -/
theorem MNec_ExtT : MNecF.Valid ExtT :=
  (MNecF.valid_iff_tr _).mpr <| MNecF.tr_ExtT.mpr fun a _ ⟨h1, _⟩ => by
    obtain ⟨_, hy⟩ := h1 (Classical.choice (Univ.El_nonempty (U := univNB) a))
    exact hy.1

/-- Int≈: necessarily-`α ⊑ β` gives `α ⊑ β` at the actual world, and so `α` is `β`. -/
theorem MNec_IntT : MNecF.Valid IntT := by
  intro ρ env
  refine (MNecF.holds_tall _ _ _).mpr fun a => (MNecF.holds_tall _ _ _).mpr fun b => ?_
  refine (MNecF.holds_imp _ _ _ _).mpr fun h => ?_
  have h1 := (MNec_box _ _ _).mp ((MNecF.holds_conj _ _ _ _).mp h).1 MNecF.U.w0
  obtain ⟨_, hy⟩ := (MNecF.holdsAt_ex _ _ _ _ _).mp ((MNecF.holdsAt_all _ _ _ _ _).mp h1
    (Classical.choice (Univ.CatVal_nonempty (U := MNecF.U) _ _)))
  exact (MNecF.holds_teq _ _ _ _).mpr ((MNecF.holdsAt_eqv _ _ _ _ _ _ _).mp hy).1

/-! ## Identity of types -/

theorem MNec_Inj : MNecF.Valid Inj := MNecF.Inj_of fun _ _ _ => Iff.rfl

theorem MNec_tr_Recovery : MNecF.Tr Recovery ↔ ∀ a b c d, MNecF.teq (.arr a c) (.arr b d) MNecF.U.w0 ∧
    MNecF.teq a b MNecF.U.w0 → MNecF.teq c d MNecF.U.w0 := Iff.rfl

theorem MNec_Recovery : MNecF.Valid Recovery :=
  (MNecF.valid_iff_tr _).mpr <| MNec_tr_Recovery.mpr fun a b c d ⟨h, _⟩ => by
    have e : Code.arr a c = Code.arr b d := h
    exact (Code.arr.inj e).2

/-- `≈` is the same at both worlds. -/
theorem MNec_NITeq : MNecF.Valid NITeq :=
  (MNecF.valid_iff_tr _).mpr <| MNecF.tr_NITeq.mpr fun a b h => by
    have e : MNecF.teq a b = MNecF.eval (topF : Fm Ctx.nil) (fun i => i.elim0) () := by
      refine Eq.trans ?_ (MNecF.eval_topF (Γ := Ctx.nil) _ _).symm
      funext w
      exact propext ⟨fun _ => trivial, fun _ => h⟩
    exact ⟨rfl, heq_of_eq e⟩

theorem MNec_NDTeq : MNecF.Valid NDTeq := MNecF.NDTeq_of (fun _ => ⟨rfl, HEq.rfl⟩) fun _ _ _ => Iff.rfl

/-! ## Modal principles for items -/

/-- ND× fails: the two entities are distinct at the actual world, but identified at the other. -/
theorem MNec_not_NDX : ¬ MNecF.Valid NDX :=
  MNecF.not_NDX_of (fun p q h => (MNec_hb p q).mp h) (a := .e) (b := .e) (true : MNecF.U.El .e)
    (false : MNecF.U.El .e) (fun h => Bool.noConfusion (eq_of_heq h.2)) false
    ⟨rfl, fun h => Bool.noConfusion (eq_of_heq h)⟩

theorem MNec_Bool : ∀ φ, BoolSch φ → MNecF.Valid φ := MNecF.bool_valid fun _ => ⟨rfl, HEq.rfl⟩

theorem MNec_tr_IdId : MNecF.Tr IdId ↔ ∀ a (x y : MNecF.U.El a), MNecF.eqv .t .t (MNecF.eqv a a x y)
    (fun w => ∀ G : MNecF.U.El a → Bool → Prop, G x w → G y w) MNecF.U.w0 := Iff.rfl

/-- The Identity Identity fails: at the other world an entity is not identified with itself, though
it has every property it has. -/
theorem MNec_not_IdId : ¬ MNecF.Valid IdId := fun h => by
  have h0 := MNec_tr_IdId.mp ((MNecF.valid_iff_tr _).mp h) .e true true
  have e := congrFun (eq_of_heq h0.2) false
  exact (cast e.symm (fun _ hG => hG)).2 HEq.rfl

/-! ## The Barcan formulas for types, and Type Necessitism -/

theorem MNec_TBF : ∀ χ, TBFSch χ → MNecF.Valid χ := MNecF.TBF_of MNec_hb

theorem MNec_TCBF : ∀ χ, TCBFSch χ → MNecF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MNecF.holds_imp _ _ _ _).mpr fun h => ?_
  exact (MNecF.holds_tall _ _ _).mpr fun a => (MNec_box _ _ _).mpr fun w =>
    (MNecF.holdsAt_tall _ _ _ w).mp ((MNec_box _ _ _).mp h w) a

/-- Every type is, at each world, `≈` itself. -/
theorem MNec_TNec : MNecF.Valid TNec := by
  intro ρ env
  refine (MNecF.holds_tall _ _ _).mpr fun a => (MNec_box _ _ _).mpr fun w => ?_
  exact (MNec_holdsAt_tex _ _ _ w).mpr ⟨a, (MNecF.holdsAt_teq _ _ _ _ w).mpr rfl⟩

end Wd
end PIF
