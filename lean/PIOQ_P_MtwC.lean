import PIBF
set_option autoImplicit false

namespace PIF
namespace Wd

/-!
# `𝔐_twin,c` (`MtwCF`): the rest of its profile

Two worlds; entities are the sets of worlds; each type `a` is paired with its twin `sw a`, got by
swapping its leftmost `e` and `t`, which has the very same items, and each item is identified with
itself in the twin type. Identity of items does not depend on the world, and `≈` is identity of
types at every world.

Within a type, identity is identity; so Cong, PCong, Inj≈, Recovery and NDT≈ hold, and so do the
Barcan formulas (identity of propositions is identity). An entity is a set of worlds, identified
only with itself as a proposition, never with a property; so the Slogan holds. Haecceitism, PExt,
Ext≈ and Int≈ fail.
-/

theorem MtwC_refl : ∀ a (x : MtwCF.U.El a) w, MtwCF.eqv a a x x w := fun _ _ _ => ⟨Or.inl rfl, HEq.rfl⟩

/-- Identity of propositions is identity. -/
theorem MtwC_hb : ∀ p q, MtwCF.eqv .t .t p q MtwCF.U.w0 ↔ p = q :=
  fun p _ => ⟨fun h => eq_of_heq h.2, fun h => h ▸ MtwC_refl .t p _⟩

/-! ## The Slogan and Haecceitism -/

/-- An entity is identified only with itself, and with the same set of worlds as a proposition, of
type `t`: never with a property. -/
theorem MtwC_Slogan : MtwCF.Valid Slogan :=
  (MtwCF.valid_iff_tr _).mpr <| MtwCF.tr_Slogan.mpr fun _ _ _ h =>
    h.1.elim (fun e => nomatch e) (fun e => nomatch e)

theorem MtwC_tr_Hae : MtwCF.Tr Hae ↔
    ∀ a (x : MtwCF.U.El a), MtwCF.eqv a (.arr a .t) x (fun y => MtwCF.eqv a a y x) MtwCF.U.w0 := Iff.rfl

/-- Haecceitism fails: an entity is identified with nothing of type `e→t`. -/
theorem MtwC_not_Hae : ¬ MtwCF.Valid Hae := fun h =>
  (MtwC_tr_Hae.mp ((MtwCF.valid_iff_tr _).mp h) .e (fun _ => True)).1.elim
    (fun e => nomatch e) (fun e => nomatch e)

/-! ## Congruence and extensionality -/

/-- Identified functions are the same function, on types that differ only by the swap, and
identified arguments are the same item; so the values are the same item, of type `c`. -/
theorem MtwC_cong_core (a b c d : Code Empty) (f : MtwCF.U.El a → MtwCF.U.El c)
    (g : MtwCF.U.El b → MtwCF.U.El d) (x : MtwCF.U.El a) (y : MtwCF.U.El b) (w : Bool)
    (h1 : MtwCF.eqv (.arr a c) (.arr b d) f g w) (h2 : MtwCF.eqv a b x y w) :
    MtwCF.eqv c d (f x) (g y) w := by
  obtain ⟨e1 | e1, hf⟩ := h1
  · injection e1 with eb ed
    subst eb; subst ed
    exact ⟨Or.inl rfl, heq_app rfl rfl hf h2.2⟩
  · change Code.arr b d = Code.arr (sw a) c at e1
    injection e1 with eb ed
    subst eb; subst ed
    exact ⟨Or.inl rfl, heq_app (El_sw a).symm rfl hf h2.2⟩

theorem MtwC_Cong : MtwCF.Valid Cong :=
  (MtwCF.valid_iff_tr _).mpr <| MtwCF.tr_Cong.mpr fun a b c d f g x y ⟨h1, h2⟩ =>
    MtwC_cong_core a b c d f g x y _ h1 h2

theorem MtwC_tr_PCong : MtwCF.Tr PCong ↔ ∀ a c d (f : MtwCF.U.El a → MtwCF.U.El c)
    (g : MtwCF.U.El a → MtwCF.U.El d) x,
    MtwCF.eqv (.arr a c) (.arr a d) f g MtwCF.U.w0 → MtwCF.eqv c d (f x) (g x) MtwCF.U.w0 := Iff.rfl

theorem MtwC_PCong : MtwCF.Valid PCong :=
  (MtwCF.valid_iff_tr _).mpr <| MtwC_tr_PCong.mpr fun a c d f g x h =>
    MtwC_cong_core a a c d f g x x _ h (MtwC_refl a x _)

/-- PExt fails: the identity function on `e` and the identity function from `e` to `t` agree
argument by argument, but `e→e` and `e→t` are not twins. -/
theorem MtwC_not_PExt : ¬ MtwCF.Valid PExt := fun h => by
  have h0 := MtwCF.tr_PExt.mp ((MtwCF.valid_iff_tr _).mp h) .e .e .t (fun x : MtwCF.U.El .e => x)
    (fun x : MtwCF.U.El .e => (x : MtwCF.U.El .t)) (fun _ => ⟨Or.inr rfl, HEq.rfl⟩)
  rcases h0.1 with e | e
  · exact nomatch e
  · exact nomatch e

/-- Ext≈ fails: `e` and its twin `t` have the same items, but are distinct. -/
theorem MtwC_not_ExtT : ¬ MtwCF.Valid ExtT := fun h => by
  have h0 := MtwCF.tr_ExtT.mp ((MtwCF.valid_iff_tr _).mp h) .e .t
    ⟨fun x => ⟨x, Or.inr rfl, HEq.rfl⟩, fun y => ⟨y, Or.inr rfl, HEq.rfl⟩⟩
  exact nomatch (show (Code.e : Code Empty) = .t from h0)

/-- `□φ` is truth at both worlds. -/
theorem MtwC_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MtwCF.U.TEnv n) (env : MtwCF.U.Env Γ ρ) :
    MtwCF.Holds (boxF φ) ρ env ↔ ∀ w, MtwCF.HoldsAt φ ρ env w := by
  refine ⟨fun h w => MtwCF.box_all (fun p q h => (MtwC_hb p q).mp h) φ ρ env h w, fun h => ?_⟩
  refine (MtwCF.holdsAt_eqv_t φ topF ρ env _).mpr ?_
  rw [MtwCF.eval_topF]
  exact ⟨Or.inl rfl, heq_of_eq (funext fun w => propext ⟨fun _ => trivial, fun _ => h w⟩)⟩

/-- Int≈ fails: `e` and `t` necessarily have the same items. -/
theorem MtwC_not_IntT : ¬ MtwCF.Valid IntT := fun h => by
  have h0 := (MtwCF.holds_tall _ _ _).mp ((MtwCF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .t
  have h1 := (MtwCF.holds_imp _ _ _ _).mp h0 ((MtwCF.holds_conj _ _ _ _).mpr
    ⟨(MtwC_box _ _ _).mpr fun w => (MtwCF.holdsAt_all _ _ _ _ w).mpr fun x => (MtwCF.holdsAt_ex _ _ _ _ w).mpr
        ⟨x, (MtwCF.holdsAt_eqv _ _ _ _ _ _ w).mpr ⟨Or.inr rfl, (cast_heq _ _).trans (cast_heq _ _).symm⟩⟩,
     (MtwC_box _ _ _).mpr fun w => (MtwCF.holdsAt_all _ _ _ _ w).mpr fun y => (MtwCF.holdsAt_ex _ _ _ _ w).mpr
        ⟨y, (MtwCF.holdsAt_eqv _ _ _ _ _ _ w).mpr ⟨Or.inr rfl, (cast_heq _ _).trans (cast_heq _ _).symm⟩⟩⟩)
  exact nomatch (show (Code.e : Code Empty) = .t from (MtwCF.holds_teq _ _ _ _).mp h1)

/-! ## Identity of types -/

theorem MtwC_Inj : MtwCF.Valid Inj := MtwCF.Inj_of fun _ _ _ => Iff.rfl

theorem MtwC_tr_Recovery : MtwCF.Tr Recovery ↔ ∀ a b c d, MtwCF.teq (.arr a c) (.arr b d) MtwCF.U.w0 ∧
    MtwCF.teq a b MtwCF.U.w0 → MtwCF.teq c d MtwCF.U.w0 := Iff.rfl

theorem MtwC_Recovery : MtwCF.Valid Recovery :=
  (MtwCF.valid_iff_tr _).mpr <| MtwC_tr_Recovery.mpr fun a b c d ⟨h, _⟩ => by
    have e : Code.arr a c = Code.arr b d := h
    exact (Code.arr.inj e).2

theorem MtwC_NDTeq : MtwCF.Valid NDTeq := MtwCF.NDTeq_of (fun p => MtwC_refl .t p _) fun _ _ _ => Iff.rfl

/-! ## The Barcan formulas -/

theorem MtwC_TBF : ∀ χ, TBFSch χ → MtwCF.Valid χ := MtwCF.TBF_of MtwC_hb

theorem MtwC_BF : MtwCF.Valid BF := MtwCF.BF_of MtwC_hb

end Wd
end PIF
