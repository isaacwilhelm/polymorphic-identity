import PIBF
set_option autoImplicit false

/-!
# Open questions: the profile of `𝔐_E,k,t`

The standard model `𝔐_E,k,t` of `PIAlgModels.lean`: as `𝔐_E,k` (`E = {0,1,2}`, `0 ∼ 1`, and
`k₁ ∼ k₂` at `e→e`), with in addition all propositions identified with each other. Items are
identified only within a type, and `≈` is identity of types.

* Since items are identified only within a type: Disjoint, Slogan, Cantor and Ext≈ hold, while
  Twin and Hae fail; and Inj≈ and Recovery hold, since `≈` is identity.
* PCong holds, as in `𝔐_E,k`: the values of `k₁` and `k₂` at each argument are identified.
* Every two propositions are identified, so ⊤≢⊥ and Int≈ fail, while PropExt≡, Bool, TBF, TCBF,
  BF and CBF hold trivially.
* PExt fails: `λx.⊤` and `λx.⊥` have identified values but are distinct, and nothing at `e→t` is
  identified with anything else.
* Classicism fails: PI proves `(x ≡ y) ↔ ∀G(Gx → Gy)`, so Classicism gives
  `λy.(x ≡ y) ≡ λy.∀G(Gx → Gy)`; but at `x = 0` these predicates differ at `1`.
-/

namespace PIF

section MEkTP
open Derive

/-! ## Identification across types -/

theorem MEkT_Disjoint : MEkT.Valid Disjoint := classIdent_Disjoint univ3 SEkT
theorem MEkT_Slogan : MEkT.Valid Slogan := cI_Slogan _ _
theorem MEkT_Cantor : MEkT.Valid Cantor := cI_Cantor _ _
theorem MEkT_not_Twin : ¬ MEkT.Valid Twin := cI_not_Twin _ _
theorem MEkT_not_Hae : ¬ MEkT.Valid Hae := cI_not_Hae _ _
theorem MEkT_ExtT : MEkT.Valid ExtT := cI_ExtT _ _

/-! ## Type identity -/

theorem MEkT_Inj : MEkT.Valid Inj := MEkTD.Inj_valid

theorem MEkT_Recovery : MEkT.Valid Recovery :=
  (MEkT.valid_iff_tr _).mpr <| MEkT.tr_Recovery.mpr fun _ _ _ _ ⟨h1, _⟩ => by
    injection h1

/-- Int≈ fails: every two propositions are identified, so `□(e ⊑ t)` and `□(t ⊑ e)` are true. -/
theorem MEkT_not_IntT : ¬ MEkT.Valid IntT := fun h =>
  absurd (MEkT.tr_IntT.mp ((MEkT.valid_iff_tr _).mp h) .e .t
    ⟨⟨rfl, Or.inr ⟨trivial, trivial⟩⟩, ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩⟩) (fun e => by cases e)

/-! ## Congruence -/

theorem MEkT_eqv_e (u v : Fin 3) (h : u = v ∨ ((u = 0 ∨ u = 1) ∧ (v = 0 ∨ v = 1))) :
    MEkT.eqv .e .e u v :=
  ⟨rfl, h.elim (fun e => Or.inl (heq_of_eq e)) (fun ⟨p, q⟩ => Or.inr ⟨p, q⟩)⟩

theorem MEkT_PCong : MEkT.Valid PCong := by
  refine (MEkT.valid_iff_tr _).mpr <| MEkT.tr_PCong.mpr fun a c d f g x ⟨h, hfg⟩ => ?_
  injection h with _ hcd
  subst hcd
  rcases hfg with hfg | ⟨hS, hS'⟩
  · have e : f = g := eq_of_heq hfg
    subst e; exact ⟨rfl, Or.inl HEq.rfl⟩
  · cases a with
    | e => cases c with
      | e =>
        have hv : ∀ u v : Fin 3 → Fin 3, (u = k1 ∨ u = k2) → (v = k1 ∨ v = k2) → ∀ y,
            u y = v y ∨ ((u y = 0 ∨ u y = 1) ∧ (v y = 0 ∨ v y = 1)) := by
          intro u v hu hv y
          rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
          · exact Or.inl rfl
          · exact k_vals y
          · exact (k_vals y).elim (fun e => Or.inl e.symm) (fun ⟨p, q⟩ => Or.inr ⟨q, p⟩)
          · exact Or.inl rfl
        exact MEkT_eqv_e _ _ (hv f g hS hS' x)
      | t => exact hS.elim
      | base b => exact b.elim
      | arr _ _ => exact hS.elim
    | t => exact hS.elim
    | base b => exact b.elim
    | arr _ _ => exact hS.elim

/-- PExt fails: `λx.⊤` and `λx.⊥` have identified values, but they are distinct predicates. -/
theorem MEkT_not_PExt : ¬ MEkT.Valid PExt := fun h => by
  have := MEkT.tr_PExt.mp ((MEkT.valid_iff_tr _).mp h) .e .t .t (fun _ => True) (fun _ => False)
    (fun _ => ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩)
  rcases this.2 with e | ⟨s, _⟩
  · have e' : (fun _ : Fin 3 => True) = (fun _ : Fin 3 => False) := eq_of_heq e
    exact cast (congrFun e' (0 : Fin 3)) trivial
  · exact s

/-! ## Propositions -/

theorem MEkT_not_TopBot : ¬ MEkT.Valid TopBot := fun h =>
  MEkT.tr_TopBot.mp ((MEkT.valid_iff_tr _).mp h) ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩

theorem MEkT_PropExt : MEkT.Valid PropExt := MEkT.PropExt_valid MEkT_model

theorem MEkT_Bool : ∀ φ, BoolSch φ → MEkT.Valid φ := fun φ hφ =>
  MEkT.soundness MEkT_model (Ax := (· = PropExt)) (fun _ h => h ▸ MEkT_PropExt)
    (d_Bool_of_PropExt (S := (· = PropExt)) rfl φ hφ)

/-! ## Barcan formulas: every `□`-formula is true, since all propositions are identified -/

theorem MEkT_TBF : ∀ χ, TBFSch χ → MEkT.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env _
  exact (MEkT.holds_eqv tyT tyT _ _ _ _).mpr ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩

theorem MEkT_TCBF : ∀ χ, TCBFSch χ → MEkT.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env _ a
  exact (MEkT.holds_eqv tyT tyT _ _ _ _).mpr ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩

theorem MEkT_BF : MEkT.Valid BF := by
  intro ρ env a
  refine (MEkT.holds_all _ _ _ _).mpr fun _ => (MEkT.holds_imp _ _ _ _).mpr fun _ => ?_
  exact (MEkT.holds_eqv tyT tyT _ _ _ _).mpr ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩

theorem MEkT_CBF : MEkT.Valid CBF := by
  intro ρ env a
  refine (MEkT.holds_all _ _ _ _).mpr fun _ => (MEkT.holds_imp _ _ _ _).mpr fun _ => ?_
  refine (MEkT.holds_all _ _ _ _).mpr fun _ => ?_
  exact (MEkT.holds_eqv tyT tyT _ _ _ _).mpr ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩

/-! ## Classicism fails

PI proves `(x ≡ y) ↔ ∀_{α→t} G (G x → G y)`, so Classicism has the instance
`𝔸α ∀_α x (λy.(x ≡ y) ≡ λy.∀G(G x → G y))`. In `𝔐_E,k,t`, nothing at `e→t` is identified with
anything else, and at `x = 0` the two predicates differ at `1`. -/

theorem MEkT_cls : ClassSch (closeCtx (Δ1.ext tv0) (Tm.eqv tv0.pred tv0.pred (Tm.lam tv0 Exy) (Tm.lam tv0 Axy))) :=
  Or.inr ⟨1, Δ1.ext tv0, tv0, Exy, Axy, iff_IdId rfl, rfl⟩

theorem MEkT_tr_cls (F : Frame) :
    F.Tr (closeCtx (Δ1.ext tv0) (Tm.eqv tv0.pred tv0.pred (Tm.lam tv0 Exy) (Tm.lam tv0 Axy))) ↔
      ∀ a (x : F.U.El a), F.eqv (.arr a .t) (.arr a .t) (fun y => F.eqv a a x y)
        (fun y => ∀ G : F.U.El a → Prop, G x → G y) := Iff.rfl

theorem MEkT_not_Class : ¬ ∀ χ, ClassSch χ → MEkT.Valid χ := fun h => by
  have h0 := (MEkT_tr_cls MEkT).mp ((MEkT.valid_iff_tr _).mp (h _ MEkT_cls)) .e (0 : Fin 3)
  rcases h0.2 with e | ⟨s, _⟩
  · have e' := congrFun (eq_of_heq e) (1 : Fin 3)
    have h1 : ∀ G : Fin 3 → Prop, G 0 → G 1 := cast e' (MEkT_eqv_e 0 1 (Or.inr ⟨Or.inl rfl, Or.inr rfl⟩))
    exact absurd (h1 (fun v => v = 0) rfl) (by decide)
  · exact s

end MEkTP

end PIF
