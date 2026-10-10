import PIBF
set_option autoImplicit false

namespace PIF
namespace Wd

/-!
# More about `𝔐_hae,nd`

In `𝔐_hae,nd` (two worlds, the actual one `true`, one entity), items are identified, at both
worlds, just in case they have the same root (got by stripping off haecceities). At the actual
world `≈` is identity of types; at the other world every type is `≈` every type. Identity of
propositions is identity, so `□φ` is truth at both worlds.
-/

open Classical

/-! ## Roots -/

/-- Each root is either the item itself, or of a smaller type. -/
theorem MhND_root_cases : ∀ (a : Code Empty) (x : univHC.El a), root a x = ⟨a, x⟩ ∨ csz (root a x).1 < csz a
  | .e, _ => Or.inl rfl
  | .t, _ => Or.inl rfl
  | .base b, _ => b.elim
  | .arr _ .e, _ => Or.inl rfl
  | .arr _ (.base b), _ => b.elim
  | .arr _ (.arr _ _), _ => Or.inl rfl
  | .arr a .t, f => by
    by_cases hf : ∃ z, f = hcy a z
    · obtain ⟨z, rfl⟩ := hf
      refine Or.inr ?_
      rw [root_hcy]
      have := root_sz a z
      simp only [csz]
      omega
    · refine Or.inl ?_
      show (if h : ∃ z, f = hcy a z then root a (Classical.choose h) else ⟨.arr a .t, f⟩) = _
      split
      · exact absurd ‹_› hf
      · rfl

/-- Each type has an item which is its own root. -/
theorem MhND_root_self : ∀ a : Code Empty, ∃ x : univHC.El a, root a x = ⟨a, x⟩
  | .e => ⟨(), rfl⟩
  | .t => ⟨fun _ => True, rfl⟩
  | .base b => b.elim
  | .arr _ .e => ⟨fun _ => (), rfl⟩
  | .arr _ (.base b) => b.elim
  | .arr a (.arr c d) => ⟨Classical.choice (Univ.El_nonempty (U := univHC) (.arr a (.arr c d))), rfl⟩
  | .arr a .t => ⟨fun _ _ => False, by
      show (if h : ∃ z, (fun _ _ => False : univHC.El (.arr a .t)) = hcy a z then root a (Classical.choose h)
        else ⟨.arr a .t, fun _ _ => False⟩) = _
      split
      · rename_i h
        obtain ⟨z, hz⟩ := h
        exact (cast (congrFun (congrFun hz z) true).symm (rfl : z = z) : False).elim
      · rfl⟩

/-- The root of a function is the function itself, or (for a haecceity) of size at most its domain. -/
theorem MhND_root_arr : ∀ (a c : Code Empty) (f : univHC.El (.arr a c)),
    root (.arr a c) f = ⟨.arr a c, f⟩ ∨ (c = .t ∧ csz (root (.arr a c) f).1 ≤ csz a)
  | _, .e, _ => Or.inl rfl
  | _, .base b, _ => b.elim
  | _, .arr _ _, _ => Or.inl rfl
  | a, .t, f => by
    by_cases hf : ∃ z, f = hcy a z
    · obtain ⟨z, rfl⟩ := hf
      refine Or.inr ⟨rfl, ?_⟩
      rw [root_hcy]
      exact root_sz a z
    · refine Or.inl ?_
      show (if h : ∃ z, f = hcy a z then root a (Classical.choose h) else ⟨.arr a .t, f⟩) = _
      split
      · exact absurd ‹_› hf
      · rfl

/-- Two types whose items are identified, each with some item of the other, are the same. -/
theorem MhND_coext (a b : Code Empty) (h1 : ∀ x : univHC.El a, ∃ y : univHC.El b, root a x = root b y)
    (h2 : ∀ y : univHC.El b, ∃ x : univHC.El a, root a x = root b y) : a = b := by
  obtain ⟨x0, hx0⟩ := MhND_root_self a
  obtain ⟨y0, hy0⟩ := MhND_root_self b
  obtain ⟨y, hy⟩ := h1 x0
  obtain ⟨x, hx⟩ := h2 y0
  rw [hx0] at hy
  rw [hy0] at hx
  rcases MhND_root_cases b y with e1 | e1
  · rw [e1] at hy
    exact congrArg Sigma.fst hy
  · rcases MhND_root_cases a x with e2 | e2
    · rw [e2] at hx
      exact congrArg Sigma.fst hx
    · rw [← hy] at e1
      rw [hx] at e2
      exact absurd (Nat.lt_trans e1 e2) (Nat.lt_irrefl _)

/-! ## Identity of propositions, and `□` -/

theorem MhND_hb : ∀ p q : MhND.U.El .t, MhND.eqv .t .t p q MhND.U.w0 ↔ p = q :=
  fun p q => ⟨root_inj .t p q, fun h => h ▸ rfl⟩

/-- `□φ` is true just when `φ` is true at both worlds. -/
theorem MhND_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MhND.U.TEnv n) (env : MhND.U.Env Γ ρ) :
    MhND.Holds (boxF φ) ρ env ↔ ∀ w, MhND.HoldsAt φ ρ env w := by
  refine (MhND.holdsAt_eqv_t φ topF ρ env _).trans ?_
  rw [MhND.eval_topF]
  refine (MhND_hb _ _).trans ⟨fun e w => cast (congrFun e w).symm trivial, fun h => ?_⟩
  exact funext fun w => propext ⟨fun _ => trivial, fun _ => h w⟩

theorem MhND_holdsAt_tex {n : Nat} {Γ : Ctx n} (φ : Fm Γ.text) (ρ : MhND.U.TEnv n) (env : MhND.U.Env Γ ρ)
    (w : Bool) : MhND.HoldsAt (Tm.tex φ) ρ env w ↔ ∃ a, MhND.HoldsAt φ (scons a ρ) env w := Iff.rfl

/-! ## Congruence and extensionality for functions -/

theorem MhND_tr_PCong : MhND.Tr PCong ↔ ∀ a c d (f : MhND.U.El a → MhND.U.El c) (g : MhND.U.El a → MhND.U.El d) x,
    MhND.eqv (.arr a c) (.arr a d) f g MhND.U.w0 → MhND.eqv c d (f x) (g x) MhND.U.w0 := Iff.rfl

/-- Functions on the same domain with the same root have the same codomain, and so are the same. -/
theorem MhND_PCong : MhND.Valid PCong :=
  (MhND.valid_iff_tr _).mpr <| MhND_tr_PCong.mpr fun a c d f g x h => by
    have h' : root (.arr a c) f = root (.arr a d) g := h
    have hcd : c = d := by
      rcases MhND_root_arr a c f with e1 | ⟨hc, l1⟩ <;> rcases MhND_root_arr a d g with e2 | ⟨hd, l2⟩
      · have e := congrArg Sigma.fst ((e1.symm.trans h').trans e2)
        exact (Code.arr.inj e).2
      · rw [← h', e1] at l2
        simp only [csz] at l2
        omega
      · rw [h', e2] at l1
        simp only [csz] at l1
        omega
      · exact hc.trans hd.symm
    subst hcd
    have hfg : f = g := root_inj (.arr a c) f g h'
    subst hfg
    rfl

/-- The constant function to the entity and the constant function to its haecceity agree pointwise,
but have different types. -/
theorem MhND_not_PExt : ¬ MhND.Valid PExt := fun h => by
  have h0 := MhND.tr_PExt.mp ((MhND.valid_iff_tr _).mp h) .e .e (.arr .e .t)
    (fun _ => ()) (fun _ => hcy .e ()) (fun _ => (root_hcy .e ()).symm)
  have e : (Code.arr .e .e : Code Empty) = .arr .e (.arr .e .t) := congrArg Sigma.fst h0
  cases e

/-! ## Identity of types -/

theorem MhND_Inj : MhND.Valid Inj :=
  (MhND.valid_iff_tr _).mpr <| MhND.tr_Inj.mpr fun _ _ _ _ h =>
    ⟨fun _ => (Code.arr.inj (h rfl)).1, fun _ => (Code.arr.inj (h rfl)).2⟩

theorem MhND_tr_Recovery : MhND.Tr Recovery ↔ ∀ a b c d, MhND.teq (.arr a c) (.arr b d) MhND.U.w0 ∧
    MhND.teq a b MhND.U.w0 → MhND.teq c d MhND.U.w0 := Iff.rfl

theorem MhND_Recovery : MhND.Valid Recovery :=
  (MhND.valid_iff_tr _).mpr <| MhND_tr_Recovery.mpr fun _ _ _ _ ⟨h, _⟩ _ => (Code.arr.inj (h rfl)).2

theorem MhND_ExtT : MhND.Valid ExtT :=
  (MhND.valid_iff_tr _).mpr <| MhND.tr_ExtT.mpr fun a b ⟨h1, h2⟩ _ => MhND_coext a b h1 h2

theorem MhND_IntT : MhND.Valid IntT := by
  intro ρ env
  refine (MhND.holds_tall _ _ _).mpr fun a => (MhND.holds_tall _ _ _).mpr fun b => ?_
  refine (MhND.holds_imp _ _ _ _).mpr fun h => (MhND.holds_teq _ _ _ _).mpr fun _ => ?_
  have hs := (MhND_box _ _ _).mp ((MhND.holds_conj _ _ _ _).mp h).1 true
  have hp := (MhND_box _ _ _).mp ((MhND.holds_conj _ _ _ _).mp h).2 true
  refine MhND_coext a b (fun x => ?_) (fun y => ?_)
  · obtain ⟨y, hy⟩ := (MhND.holdsAt_ex _ _ _ _ true).mp ((MhND.holdsAt_all _ _ _ _ true).mp hs x)
    exact ⟨y, (MhND.holdsAt_eqv _ _ _ _ _ _ true).mp hy⟩
  · obtain ⟨x, hx⟩ := (MhND.holdsAt_ex _ _ _ _ true).mp ((MhND.holdsAt_all _ _ _ _ true).mp hp y)
    exact ⟨x, (MhND.holdsAt_eqv _ _ _ _ _ _ true).mp hx⟩

/-- A type is `≈` itself at both worlds. -/
theorem MhND_NITeq : MhND.Valid NITeq :=
  (MhND.valid_iff_tr _).mpr <| MhND.tr_NITeq.mpr fun _ _ h => (MhND_hb _ _).mpr <| by
    refine Eq.trans ?_ (MhND.eval_topF (Γ := Ctx.nil) _ _).symm
    funext w
    exact propext ⟨fun _ => trivial, fun _ _ => h rfl⟩

/-! ## Booleanism and the Identity Identity -/

theorem MhND_Bool : ∀ φ, BoolSch φ → MhND.Valid φ := MhND.bool_valid fun _ => rfl

theorem MhND_tr_IdId : MhND.Tr IdId ↔ ∀ a (x y : MhND.U.El a), MhND.eqv .t .t (MhND.eqv a a x y)
    (fun w => ∀ G : MhND.U.El a → Bool → Prop, G x w → G y w) MhND.U.w0 := Iff.rfl

theorem MhND_IdId : MhND.Valid IdId :=
  (MhND.valid_iff_tr _).mpr <| MhND_tr_IdId.mpr fun a x y => (MhND_hb _ _).mpr <| by
    funext w
    exact propext ⟨fun h _ hG => root_inj a x y h ▸ hG, fun h => h (fun z _ => root a x = root a z) rfl⟩

/-! ## The Barcan formulas, and Necessitism -/

theorem MhND_TBF : ∀ χ, TBFSch χ → MhND.Valid χ := MhND.TBF_of MhND_hb

theorem MhND_TCBF : ∀ χ, TCBFSch χ → MhND.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MhND.holds_imp _ _ _ _).mpr fun h => ?_
  exact (MhND.holds_tall _ _ _).mpr fun a => (MhND_box _ _ _).mpr fun w =>
    (MhND.holdsAt_tall _ _ _ w).mp ((MhND_box _ _ _).mp h w) a

theorem MhND_TNec : MhND.Valid TNec := by
  intro ρ env
  refine (MhND.holds_tall _ _ _).mpr fun a => (MhND_box _ _ _).mpr fun w => ?_
  exact (MhND_holdsAt_tex _ _ _ w).mpr ⟨a, (MhND.holdsAt_teq (Γ := Ctx.nil.text.text) tv1 tv0 _ _ w).mpr fun _ => rfl⟩

theorem MhND_BF : MhND.Valid BF := MhND.BF_of MhND_hb
theorem MhND_CBF : MhND.Valid CBF := MhND.CBF_of MhND_hb
theorem MhND_Nec : MhND.Valid Nec := MhND.Nec_of MhND_hb fun _ _ _ => rfl

/-! ## Classicism fails

PI proves Link, `𝔸α𝔸β(α ≈ β → ∀_α x ∃_β y (x ≡ y))`, so Classicism gives `Link ≡ ⊤`. But Link
is false at the other world, where `t ≈ e`, while no proposition is identified with the entity. -/

open Derive in
theorem MhND_Link_class : ClassSch (Tm.eqv tyT tyT Link topF : Fm Ctx.nil) := by
  refine Or.inl ⟨0, Ctx.nil, Link, topF, ?_, rfl⟩
  have ha : Ent (fun χ => χ = LLEqv) Ctx.nil [] Link := Ent.ofProv d_Link
  exact Ent.toProv (Ent.mp2 (Ent.taut (.imp (.atom 0) (.imp (.atom 1) (.iff (.atom 0) (.atom 1))))
    (v2 Link topF) (fun _ a b => ⟨fun _ => b, fun _ => a⟩)) ha Ent.top)

theorem MhND_Link_at (w : Bool) : MhND.HoldsAt Link (fun i => i.elim0) () w ↔
    ∀ a b, MhND.teq a b w → ∀ x : MhND.U.El a, ∃ y : MhND.U.El b, MhND.eqv a b x y w := Iff.rfl

theorem MhND_not_Class : ¬ ∀ χ, ClassSch χ → MhND.Valid χ := fun h => by
  have h0 := h _ MhND_Link_class (fun i => i.elim0) ()
  have e := ((MhND_hb _ _).mp ((MhND.holdsAt_eqv_t _ _ _ _ _).mp h0)).trans (MhND.eval_topF (Γ := Ctx.nil) _ _)
  have hl := (MhND_Link_at false).mp (cast (congrFun e false).symm trivial)
  obtain ⟨y, hy⟩ := hl .t .e (fun h => absurd h Bool.false_ne_true) (fun _ => False)
  have e2 : (Code.t : Code Empty) = Code.e := congrArg Sigma.fst (show root .t (fun _ => False) = root .e y from hy)
  cases e2

end Wd
end PIF
