import PIHae

/-!
# LL≡/≈ in PI⁻

Models of PI⁻ in which LL≡/≈ fails while PCong, or Haecceitism, holds.
-/
set_option autoImplicit false

namespace PIF
open Tm

/-- The polymorphic predicate `λγ.λz. ∃f,g:γ→γ (f ≡ g ∧ f z ≐ z ∧ ¬ g z ≐ z)`, where `u ≐ v` is
`∀F:γ→t (F u → F v)`. -/
def PredK : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (ex (tv0.arrow tv0) (ex (tv0.arrow tv0)
    (conj (eqv (tv0.arrow tv0) (tv0.arrow tv0) (.var (.there .here)) (.var .here))
      (conj (all tv0.pred (imp (.app (.var .here) (.app (.var (.there (.there .here))) (.var (.there (.there (.there .here))))))
                               (.app (.var .here) (.var (.there (.there (.there .here)))))))
            (neg (all tv0.pred (imp (.app (.var .here) (.app (.var (.there .here)) (.var (.there (.there (.there .here))))))
                               (.app (.var .here) (.var (.there (.there (.there .here)))))))))))))

namespace Frame
variable (F : Frame)

def Kf (a : Code F.U.Base) (z : F.U.El a) : Prop :=
  ∃ f : F.U.El a → F.U.El a, ∃ g : F.U.El a → F.U.El a, F.eqv (.arr a a) (.arr a a) f g ∧
    (∀ P : F.U.El a → Prop, P (f z) → P z) ∧ ¬ (∀ P : F.U.El a → Prop, P (g z) → P z)

theorem tr_BridgeK : F.Tr (Bridge PredK) ↔
    ∀ a b (x : F.U.El a) (y : F.U.El b), F.eqv a b x y ∧ F.teq a b → F.Kf a x → F.Kf b y := Iff.rfl

end Frame

/-! ## `𝔐_E,k`: PCong without LL≡/≈

As `𝔐_E` (`E = {0,1,2}`, `0 ∼ 1`), and in addition two functions `k₁, k₂ : e→e` are identified, where
`k₁ = (0↦0, 1↦0, 2↦2)` and `k₂ = (0↦1, 1↦0, 2↦2)`. Their values at each argument are identified, so
PCong holds. But `0` is a fixed point of `k₁` and not of `k₂`, while `1` is a fixed point of neither;
so `PredK` holds of `0` and not of `1`, though `0 ≡ 1`. -/

def k1 : Fin 3 → Fin 3 := fun v => if v = 2 then 2 else 0
def k2 : Fin 3 → Fin 3 := fun v => if v = 0 then 1 else if v = 1 then 0 else 2

def SEk : (c : Code Empty) → univ3.El c → Prop
  | .e, v => v = (0 : Fin 3) ∨ v = (1 : Fin 3)
  | .arr .e .e, f => f = k1 ∨ f = k2
  | _, _ => False

def MEkD : IdentData := classIdent univ3 SEk
abbrev MEk : Frame := MEkD.frame
theorem MEk_model : MEk.IsModelPIm := MEkD.model
theorem MEk_Inj : MEk.Valid Inj := MEkD.Inj_valid

theorem k_vals : ∀ x : Fin 3, k1 x = k2 x ∨ ((k1 x = 0 ∨ k1 x = 1) ∧ (k2 x = 0 ∨ k2 x = 1)) := by decide

theorem MEk_eqv_e (u v : Fin 3) (h : u = v ∨ ((u = 0 ∨ u = 1) ∧ (v = 0 ∨ v = 1))) :
    MEk.eqv .e .e u v :=
  ⟨rfl, h.elim (fun e => Or.inl (heq_of_eq e)) (fun ⟨p, q⟩ => Or.inr ⟨p, q⟩)⟩

theorem MEk_PCong : MEk.Valid PCong := by
  refine (MEk.valid_iff_tr _).mpr <| MEk.tr_PCong.mpr fun a c d f g x ⟨h, hfg⟩ => ?_
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
        exact MEk_eqv_e _ _ (hv f g hS hS' x)
      | t => exact hS.elim
      | base b => exact b.elim
      | arr _ _ => exact hS.elim
    | t => exact hS.elim
    | base b => exact b.elim
    | arr _ _ => exact hS.elim

theorem MEk_K0 : MEk.Kf .e (0 : Fin 3) :=
  ⟨k1, k2, ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩, fun P h => (show k1 0 = 0 by decide) ▸ h,
    fun hL => absurd (hL (fun v : Fin 3 => v = 1) (show k2 0 = 1 by decide)) (show ¬ (0 : Fin 3) = 1 by decide)⟩

theorem MEk_not_K1 : ¬ MEk.Kf .e (1 : Fin 3) := by
  rintro ⟨f, g, ⟨_, hfg⟩, hf, hg⟩
  rcases hfg with hfg | ⟨hS, _⟩
  · have e : f = g := eq_of_heq hfg
    subst e; exact hg hf
  · have key : ∀ u : Fin 3 → Fin 3, (u = k1 ∨ u = k2) → u 1 = (0 : Fin 3) := by
      intro u hu; rcases hu with rfl | rfl <;> decide
    exact absurd (hf (fun v : Fin 3 => v = (0 : Fin 3)) (key f hS)) (show ¬ (1 : Fin 3) = 0 by decide)

theorem MEk_not_Bridge : ¬ MEk.Valid (Bridge PredK) := fun h =>
  MEk_not_K1 (MEk.tr_BridgeK.mp ((MEk.valid_iff_tr _).mp h) .e .e (0 : Fin 3) (1 : Fin 3)
    ⟨⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩, rfl⟩ MEk_K0)


/-! ## `𝔐_hae,R`: Haecceitism without LL≡/≈

A haecceity tower (as in `PIHae.lean`) over `E = {0,1,2}`, in which `1` has the root of `0`, and the
property `λy.(y = 1)`, which is not a haecceity, also has the root of `0`. Then `R(0)` (Thm 12's
predicate) holds, witnessed by the haecceity of `0` and `λy.(y = 1)`; but `R(1)` fails, since every
property identified with a different one holds of `1`. -/

theorem fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  have : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  exact this x
theorem f01 : (0 : Fin 3) ≠ 1 := by decide
theorem f02 : (0 : Fin 3) ≠ 2 := by decide
theorem f12 : (1 : Fin 3) ≠ 2 := by decide

abbrev E3 := univ3.El .e
abbrev P3 := univ3.El (.arr .e .t)
def ind1 : P3 := fun v => v = (1 : Fin 3)
abbrev R3 := Σ c : Code univ3.Base, univ3.El c

noncomputable def ovB : (c : Code univ3.Base) → univ3.El c → R3
  | .e, x => @ite _ (x = (1 : Fin 3)) (Classical.propDecidable _) ⟨.e, (0 : Fin 3)⟩ ⟨.e, x⟩
  | .arr .e .t, G => @ite _ (G = ind1) (Classical.propDecidable _) ⟨.e, (0 : Fin 3)⟩ ⟨.arr .e .t, G⟩
  | c, x => ⟨c, x⟩

noncomputable def MhbD : IdentData := towerIdent (U := univ3) ovB
noncomputable abbrev Mhb : Frame := MhbD.frame
theorem Mhb_model : Mhb.IsModelPIm := MhbD.model
theorem Mhb_Hae : Mhb.Valid Hae := tower_Hae (U := univ3) ovB
theorem Mhb_Twin : Mhb.Valid Twin := tower_Twin (U := univ3) ovB
theorem Mhb_Inj : Mhb.Valid Inj := MhbD.Inj_valid

theorem hrB_e (x : E3) :
    hr ovB .e x = @ite _ (x = (1 : Fin 3)) (Classical.propDecidable _) ⟨.e, (0 : Fin 3)⟩ ⟨.e, x⟩ := rfl
theorem ovB_et (G : P3) :
    ovB (.arr .e .t) G = @ite _ (G = ind1) (Classical.propDecidable _) ⟨.e, (0 : Fin 3)⟩ ⟨.arr .e .t, G⟩ := rfl

theorem hrB_e0 : hr ovB .e (0 : Fin 3) = (⟨.e, (0 : Fin 3)⟩ : R3) := by
  refine (hrB_e (0 : Fin 3)).trans ?_; split
  · next h => exact absurd h f01
  · rfl
theorem hrB_e1 : hr ovB .e (1 : Fin 3) = (⟨.e, (0 : Fin 3)⟩ : R3) := by
  refine (hrB_e (1 : Fin 3)).trans ?_; split
  · rfl
  · next h => exact absurd rfl h
theorem hrB_e2 : hr ovB .e (2 : Fin 3) = (⟨.e, (2 : Fin 3)⟩ : R3) := by
  refine (hrB_e (2 : Fin 3)).trans ?_; split
  · next h => exact absurd h.symm f12
  · rfl

theorem sig_ne {x y : Fin 3} (h : x ≠ y) : (⟨.e, x⟩ : R3) ≠ ⟨.e, y⟩ :=
  fun e => h (eq_of_heq (Sigma.mk.inj e).2)

theorem hrB_cases (x : E3) : hr ovB .e x = (⟨.e, (0 : Fin 3)⟩ : R3) ∨ hr ovB .e x = (⟨.e, (2 : Fin 3)⟩ : R3) := by
  rcases fin3_cases x with h | h | h
  · exact Or.inl (h ▸ hrB_e0)
  · exact Or.inl (h ▸ hrB_e1)
  · exact Or.inr (h ▸ hrB_e2)

/-- The roots of the properties of entities. -/
theorem rootB (G : P3) :
    (hr ovB (.arr .e .t) G = (⟨.e, (0 : Fin 3)⟩ : R3) ∧ G (1 : Fin 3)) ∨
    (hr ovB (.arr .e .t) G = (⟨.e, (2 : Fin 3)⟩ : R3) ∧ ¬ G (1 : Fin 3)) ∨
    hr ovB (.arr .e .t) G = (⟨.arr .e .t, G⟩ : R3) := by
  rw [hr_arr_t]
  split
  · next h =>
    have hG1 : G (1 : Fin 3) ↔ hr ovB .e (1 : Fin 3) = hr ovB .e (Classical.choose h) :=
      Iff.of_eq (congrFun (Classical.choose_spec h) (1 : Fin 3))
    rcases hrB_cases (Classical.choose h) with h0 | h2
    · exact Or.inl ⟨h0, hG1.mpr (hrB_e1.trans h0.symm)⟩
    · exact Or.inr (Or.inl ⟨h2, fun g => sig_ne f02 (hrB_e1.symm.trans ((hG1.mp g).trans h2))⟩)
  · rw [ovB_et]
    split
    · next hg => exact Or.inl ⟨rfl, (congrFun hg (1 : Fin 3)).mpr rfl⟩
    · exact Or.inr (Or.inr rfl)

theorem hrB_ind1 : hr ovB (.arr .e .t) ind1 = (⟨.e, (0 : Fin 3)⟩ : R3) := by
  rw [hr_arr_t]
  split
  · next hh =>
    exfalso
    have hc := Classical.choose_spec hh
    rcases hrB_cases (Classical.choose hh) with h0 | h2
    · have : ind1 (0 : Fin 3) := (congrFun hc (0 : Fin 3)).mpr (hrB_e0.trans h0.symm)
      exact f01 this
    · have : hr ovB .e (1 : Fin 3) = hr ovB .e (Classical.choose hh) := (congrFun hc (1 : Fin 3)).mp rfl
      exact sig_ne f02 (hrB_e1.symm.trans (this.trans h2))
  · rw [ovB_et]
    split
    · rfl
    · next hn => exact absurd rfl hn

theorem Mhb_R0 : Mhb.Rf .e (0 : Fin 3) :=
  ⟨haeF ovB .e (0 : Fin 3), rfl, ind1,
    (show hr ovB (.arr .e .t) (haeF ovB .e (0 : Fin 3)) = hr ovB (.arr .e .t) ind1 from
      (hr_hae ovB .e (0 : Fin 3)).trans (hrB_e0.trans hrB_ind1.symm)),
    fun h => f01 h⟩

theorem Mhb_not_R1 : ¬ Mhb.Rf .e (1 : Fin 3) := by
  rintro ⟨P, hP, G, hPG, hG⟩
  have hPG' : hr ovB (.arr .e .t) P = hr ovB (.arr .e .t) G := hPG
  rcases rootB G with ⟨_, g1⟩ | ⟨hg, _⟩ | hg
  · exact hG g1
  · rcases rootB P with ⟨hp, _⟩ | ⟨_, np⟩ | hp
    · exact sig_ne f02 (hp.symm.trans (hPG'.trans hg))
    · exact np hP
    · cases congrArg Sigma.fst (hp.symm.trans (hPG'.trans hg))
  · rcases rootB P with ⟨hp, _⟩ | ⟨hp, _⟩ | hp
    · cases congrArg Sigma.fst (hp.symm.trans (hPG'.trans hg))
    · cases congrArg Sigma.fst (hp.symm.trans (hPG'.trans hg))
    · have e : P = G := eq_of_heq (Sigma.mk.inj (hp.symm.trans (hPG'.trans hg))).2
      exact hG (e ▸ hP)

theorem Mhb_not_Bridge : ¬ Mhb.Valid (Bridge PredR) := fun h =>
  Mhb_not_R1 (Mhb.tr_BridgeR.mp ((Mhb.valid_iff_tr _).mp h) .e .e (0 : Fin 3) (1 : Fin 3)
    ⟨(hrB_e0.trans hrB_e1.symm : hr ovB .e (0 : Fin 3) = hr ovB .e (1 : Fin 3)), rfl⟩ Mhb_R0)

end PIF

namespace PIF
theorem MEk_Disjoint : MEk.Valid Disjoint := classIdent_Disjoint univ3 SEk
end PIF
