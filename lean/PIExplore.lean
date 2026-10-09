import PISchemas

/-!
# Exploring PI⁻

Further models of PI⁻ (in which LL≡ fails), and further truth values for the models of PI⁻ in
*Formal Results*, found while building the site.
-/
set_option autoImplicit false

namespace PIF

theorem Code.arr_ne_left {B : Type} : ∀ (a c : Code B), Code.arr a c ≠ a
  | .e, _, h => by cases h
  | .t, _, h => by cases h
  | .base _, _, h => by cases h
  | .arr a1 c1, c, h => by injection h with h1 _; exact Code.arr_ne_left a1 c1 h1

/-! ## LL≡/≈ from invariance -/

namespace Invariance
variable {F : Frame} (I : Invariance F)

/-- **LL≡/≈ holds** in a frame with a family of admissible relations, if any two identified items
of types identified by `≈` are related by some admissible relation. -/
theorem bridge_valid (hE : ∀ a b u v, F.eqv a b u v → F.teq a b → ∃ R, I.Adm a b R ∧ R u v) {n : Nat} {Γ : Ctx n}
    (P : Tm Γ (.pi (.arr (.var fz) .t))) : F.Valid (Bridge P) := by
  intro ρ env a b
  refine (F.holds_all _ _ _ _).mpr fun x => (F.holds_all _ _ _ _).mpr fun y => ?_
  intro hc hPx
  obtain ⟨hxy, hab⟩ := (F.holds_conj _ _ _ _).mp hc
  obtain ⟨R, hR, hRxy⟩ := hE a b _ _ ((F.holds_eqv _ _ _ _ _ _).mp hxy) ((F.holds_teq _ _ _ _).mp hab)
  have hrel := I.fundamental P ρ ρ _ (fun i => I.refl (ρ i)) env env (I.envRel_refl Γ ρ env) a b R hR _ _ hRxy
  have hG : HEq (F.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y)) (F.eval P ρ env) :=
    (heq_of_eq ((F.eval_wk _ _ _ _ _).trans (F.eval_wk _ _ _ _ _))).trans
      ((F.eval_twk P.twk b (scons a ρ) env).trans (F.eval_twk P a ρ env))
  have h1 : F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (scons b (scons a ρ)) ((env, x), y) = F.eval P ρ env a :=
    eq_of_heq ((F.heq_eval_tapp (K := Cat.arr (Cat.var fz) Cat.t) ((P.twk.twk.wk tv1).wk tv0) tv1 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => F.U.El c → Prop) (Q := fun c => F.U.El c → Prop) (fun _ => rfl) hG rfl))
  have h0 : F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (scons b (scons a ρ)) ((env, x), y) = F.eval P ρ env b :=
    eq_of_heq ((F.heq_eval_tapp (K := Cat.arr (Cat.var fz) Cat.t) ((P.twk.twk.wk tv1).wk tv0) tv0 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => F.U.El c → Prop) (Q := fun c => F.U.El c → Prop) (fun _ => rfl) hG rfl))
  show F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (scons b (scons a ρ)) ((env, x), y) y
  have hPx' : F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (scons b (scons a ρ)) ((env, x), y) x := hPx
  rw [h1] at hPx'
  rw [h0]
  exact hrel.mp hPx'

end Invariance

namespace IdentData
variable (D : IdentData)

theorem Bridge_perm (allowed : (a : Code D.U.Base) → Perm (D.U.El a) → Prop)
    (hid : ∀ a, allowed a Perm.idp)
    (harr : ∀ a c θ φ, allowed a θ → allowed c φ → allowed (.arr a c) (Perm.arrow θ φ))
    (hrel : ∀ a b (θ : Perm (D.U.El a)) (φ : Perm (D.U.El b)) x y, allowed a θ → allowed b φ →
      (D.rel ⟨a, x⟩ ⟨b, y⟩ ↔ D.rel ⟨a, θ.f x⟩ ⟨b, φ.f y⟩))
    (hcrit : ∀ a (x y : D.U.El a), D.rel ⟨a, x⟩ ⟨a, y⟩ → ∃ θ : Perm (D.U.El a), allowed a θ ∧ θ.f x = y)
    {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : D.frame.Valid (Bridge P) :=
  (D.permInv allowed hid harr hrel).bridge_valid (fun a b u v huv hab => by
    change a = b at hab
    subst hab
    obtain ⟨θ, hθ, hx⟩ := hcrit a u v huv
    exact ⟨fun x y => HEq (θ.f x) y, ⟨rfl, θ, hθ, fun _ _ => Iff.rfl⟩, heq_of_eq hx⟩) P

end IdentData

/-! ## Identifications within each type

General facts about `classIdent`, where items are identified only within a type. -/

section ClassIdent
variable (U : Univ) (S : (c : Code U.Base) → U.El c → Prop)

theorem cI_Cantor : (classIdent U S).frame.Valid Cantor :=
  ((classIdent U S).frame.valid_iff_tr _).mpr <| (classIdent U S).frame.tr_Cantor.mpr
    fun a => ⟨fun _ => True, fun _ h => Code.arr_ne_left a .t h.1⟩

theorem cI_Slogan : (classIdent U S).frame.Valid Slogan :=
  ((classIdent U S).frame.valid_iff_tr _).mpr <| (classIdent U S).frame.tr_Slogan.mpr
    fun _ _ _ h => by cases h.1

theorem cI_not_Hae : ¬ (classIdent U S).frame.Valid Hae := fun h => by
  have := (classIdent U S).frame.tr_Hae.mp (((classIdent U S).frame.valid_iff_tr _).mp h) .e (Classical.choice U.neE)
  cases this.1

theorem cI_not_Twin : ¬ (classIdent U S).frame.Valid Twin := fun h => by
  obtain ⟨_, hb, _, h'⟩ := (classIdent U S).frame.tr_Twin.mp (((classIdent U S).frame.valid_iff_tr _).mp h) .e
    (Classical.choice U.neE)
  exact hb h'.1

theorem cI_ExtT : (classIdent U S).frame.Valid ExtT :=
  ((classIdent U S).frame.valid_iff_tr _).mpr <| (classIdent U S).frame.tr_ExtT.mpr fun a _ ⟨h1, _⟩ =>
    (h1 (Classical.choice (Univ.El_nonempty (U := U) a))).elim fun _ h => h.1

variable {U S} (hS : ∀ p, ¬ S .t p)
include hS

theorem cI_eqv_t (p q : Prop) : (classIdent U S).frame.eqv .t .t p q ↔ p = q :=
  ⟨fun ⟨_, h⟩ => h.elim eq_of_heq (fun ⟨s, _⟩ => (hS _ s).elim), fun h => h ▸ (classIdent U S).refl _⟩

theorem cI_Truth : (classIdent U S).frame.Valid Truth :=
  ((classIdent U S).frame.valid_iff_tr _).mpr <| (classIdent U S).frame.tr_Truth.mpr
    fun p q h hp => (cI_eqv_t hS p q).mp h ▸ hp

theorem cI_TopBot : (classIdent U S).frame.Valid TopBot :=
  ((classIdent U S).frame.valid_iff_tr _).mpr <| (classIdent U S).frame.tr_TopBot.mpr fun h => by
    have e := (cI_eqv_t hS _ _).mp h
    exact (e ▸ (fun hall : ∀ p : Prop, p => hall False) : ¬ ∀ p : Prop, p) (e ▸ (fun hall => hall False))

theorem cI_IntT : (classIdent U S).frame.Valid IntT :=
  ((classIdent U S).frame.IntT_iff_ExtT (cI_eqv_t hS)).mpr (cI_ExtT U S)

end ClassIdent

/-! ## Further values for `𝔐_D`, `𝔐_E`, `𝔐_tot`, `𝔐_fn` -/

theorem MD_Cantor : MD.Valid Cantor := cI_Cantor _ _
theorem MD_Slogan : MD.Valid Slogan := cI_Slogan _ _
theorem MD_not_Hae : ¬ MD.Valid Hae := cI_not_Hae _ _
theorem MD_not_Twin : ¬ MD.Valid Twin := cI_not_Twin _ _
theorem MD_ExtT : MD.Valid ExtT := cI_ExtT _ _
theorem MD_Truth : MD.Valid Truth := cI_Truth (U := univ3) (S := SD) (fun _ h => h)
theorem MD_TopBot : MD.Valid TopBot := cI_TopBot (U := univ3) (S := SD) (fun _ h => h)
theorem MD_IntT : MD.Valid IntT := cI_IntT (U := univ3) (S := SD) (fun _ h => h)
theorem MD_not_PCong : ¬ MD.Valid PCong := fun h => by
  have := MD.tr_PCong.mp ((MD.valid_iff_tr _).mp h) .e .t .t chi0 zeta0 (0 : Fin 3)
    ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩
  exact cast ((cI_eqv_t (U := univ3) (S := SD) (fun _ h => h) _ _).mp this) (show chi0 0 from rfl)
theorem MD_not_WCong : ¬ MD.Valid WCong := fun h => by
  have := MD.tr_WCong.mp ((MD.valid_iff_tr _).mp h) .e .e .t .t chi0 zeta0 (0 : Fin 3) (0 : Fin 3)
    ⟨⟨rfl, rfl⟩, ⟨⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩, ⟨rfl, Or.inl HEq.rfl⟩⟩⟩
  exact cast ((cI_eqv_t (U := univ3) (S := SD) (fun _ h => h) _ _).mp this) (show chi0 0 from rfl)

theorem ME_Cantor : ME.Valid Cantor := cI_Cantor _ _
theorem ME_Slogan : ME.Valid Slogan := cI_Slogan _ _
theorem ME_not_Hae : ¬ ME.Valid Hae := cI_not_Hae _ _
theorem ME_not_Twin : ¬ ME.Valid Twin := cI_not_Twin _ _
theorem ME_ExtT : ME.Valid ExtT := cI_ExtT _ _
theorem ME_Truth : ME.Valid Truth := cI_Truth (U := univ3) (S := SE) (fun _ h => h)
theorem ME_TopBot : ME.Valid TopBot := cI_TopBot (U := univ3) (S := SE) (fun _ h => h)
theorem ME_IntT : ME.Valid IntT := cI_IntT (U := univ3) (S := SE) (fun _ h => h)

theorem Mtot_Cantor : Mtot.Valid Cantor := cI_Cantor _ _
theorem Mtot_Slogan : Mtot.Valid Slogan := cI_Slogan _ _
theorem Mtot_not_Hae : ¬ Mtot.Valid Hae := cI_not_Hae _ _
theorem Mtot_not_Twin : ¬ Mtot.Valid Twin := cI_not_Twin _ _

theorem Mfn_Cantor : Mfn.Valid Cantor := cI_Cantor _ _
theorem Mfn_Slogan : Mfn.Valid Slogan := cI_Slogan _ _
theorem Mfn_not_Hae : ¬ Mfn.Valid Hae := cI_not_Hae _ _
theorem Mfn_not_Twin : ¬ Mfn.Valid Twin := cI_not_Twin _ _
theorem Mfn_ExtT : Mfn.Valid ExtT := cI_ExtT _ _
theorem Mfn_Truth : Mfn.Valid Truth := cI_Truth (U := unitUniv) (S := fun c _ => isArr c) (fun _ h => h)
theorem Mfn_TopBot : Mfn.Valid TopBot := cI_TopBot (U := unitUniv) (S := fun c _ => isArr c) (fun _ h => h)
theorem Mfn_IntT : Mfn.Valid IntT := cI_IntT (U := unitUniv) (S := fun c _ => isArr c) (fun _ h => h)
theorem Mfn_not_PCong : ¬ Mfn.Valid PCong := fun h => by
  have := Mfn.tr_PCong.mp ((Mfn.valid_iff_tr _).mp h) .e .t .t (fun _ => False) (fun _ => True) ()
    ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩
  exact cast ((cI_eqv_t (U := unitUniv) (S := fun c _ => isArr c) (fun _ h => h) _ _).mp this).symm trivial

/-! ## `𝔐_all`: everything is identified with everything -/

def MallD : IdentData where
  U := unitUniv
  rel := fun _ _ => True
  refl := fun _ => trivial
  symm := fun _ => trivial
  trans := fun _ _ => trivial

abbrev Mall : Frame := MallD.frame
theorem Mall_model : Mall.IsModelPIm := MallD.model
theorem Mall_Inj : Mall.Valid Inj := MallD.Inj_valid
theorem Mall_Cong : Mall.Valid Cong := (Mall.valid_iff_tr _).mpr <| Mall.tr_Cong.mpr fun _ _ _ _ _ _ _ _ _ => trivial
theorem Mall_WCong : Mall.Valid WCong := (Mall.valid_iff_tr _).mpr <| Mall.tr_WCong.mpr fun _ _ _ _ _ _ _ _ _ => trivial
theorem Mall_PCong : Mall.Valid PCong := (Mall.valid_iff_tr _).mpr <| Mall.tr_PCong.mpr fun _ _ _ _ _ _ _ => trivial
theorem Mall_Hae : Mall.Valid Hae := (Mall.valid_iff_tr _).mpr <| Mall.tr_Hae.mpr fun _ _ => trivial
theorem Mall_Twin : Mall.Valid Twin := (Mall.valid_iff_tr _).mpr <| Mall.tr_Twin.mpr fun a _ =>
  ⟨.arr a .t, fun h => Code.arr_ne_left a .t h.symm, fun _ => True, trivial⟩
theorem Mall_not_LLEqv : ¬ Mall.Valid LLEqv := fun h =>
  Mall.tr_LLEqv.mp ((Mall.valid_iff_tr _).mp h) .t True False trivial (fun p => p) trivial
theorem Mall_not_Truth : ¬ Mall.Valid Truth := fun h =>
  Mall.tr_Truth.mp ((Mall.valid_iff_tr _).mp h) True False trivial trivial
theorem Mall_not_TopBot : ¬ Mall.Valid TopBot := fun h => Mall.tr_TopBot.mp ((Mall.valid_iff_tr _).mp h) trivial
theorem Mall_not_Cantor : ¬ Mall.Valid Cantor := fun h => by
  obtain ⟨_, hG⟩ := Mall.tr_Cantor.mp ((Mall.valid_iff_tr _).mp h) .e
  exact hG () trivial
theorem Mall_not_Disjoint : ¬ Mall.Valid Disjoint := fun h =>
  Mall.tr_Disjoint.mp ((Mall.valid_iff_tr _).mp h) .e .t (fun e => by cases e) () True trivial
theorem Mall_not_Slogan : ¬ Mall.Valid Slogan := fun h =>
  Mall.tr_Slogan.mp ((Mall.valid_iff_tr _).mp h) () .e (fun _ => True) trivial
theorem Mall_not_ExtT : ¬ Mall.Valid ExtT := fun h => by
  have := Mall.tr_ExtT.mp ((Mall.valid_iff_tr _).mp h) .e .t ⟨fun _ => ⟨True, trivial⟩, fun _ => ⟨(), trivial⟩⟩
  cases this
theorem Mall_not_IntT : ¬ Mall.Valid IntT := fun h => by
  have := Mall.tr_IntT.mp ((Mall.valid_iff_tr _).mp h) .e .t ⟨trivial, trivial⟩
  cases this
theorem Mall_not_LLPoly : ¬ Mall.Valid (LLPoly PredE) := fun h => by
  have := Mall.tr_LLPolyE.mp ((Mall.valid_iff_tr _).mp h) .e .t () True trivial rfl
  cases this
theorem Mall_Bridge {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : Mall.Valid (Bridge P) :=
  MallD.Bridge_perm (fun _ _ => True) (fun _ => trivial) (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => Iff.rfl) (fun _ x y _ => ⟨Perm.swap x y, trivial, swapF_u x y⟩) P

/-! ## `𝔐_can`: Cantor fails

`e` (one entity) and `e→t` (its two properties) form a single class of identified items; nothing
else is identified with anything other than itself. -/

def canC (p : Σ c : Code Empty, unitUniv.El c) : Prop := p.1 = .e ∨ p.1 = .arr .e .t

def McanD : IdentData where
  U := unitUniv
  rel := fun p q => p = q ∨ (canC p ∧ canC q)
  refl := fun _ => Or.inl rfl
  symm := fun h => h.elim (fun e => Or.inl e.symm) (fun ⟨a, b⟩ => Or.inr ⟨b, a⟩)
  trans := by
    rintro p q r (rfl | ⟨_, hq⟩) (rfl | ⟨hq', hr⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hq', hr⟩
    · exact Or.inr ⟨by assumption, hq⟩
    · exact Or.inr ⟨by assumption, hr⟩

abbrev Mcan : Frame := McanD.frame
theorem Mcan_model : Mcan.IsModelPIm := McanD.model
theorem Mcan_Inj : Mcan.Valid Inj := McanD.Inj_valid

theorem Mcan_eqv_t (p q : Prop) : Mcan.eqv .t .t p q ↔ p = q := by
  refine ⟨fun h => ?_, fun h => h ▸ Or.inl rfl⟩
  rcases h with h | ⟨h | h, _⟩
  · exact eq_of_heq (Sigma.mk.inj h).2
  · cases h
  · cases h

theorem Mcan_Truth : Mcan.Valid Truth := (Mcan.valid_iff_tr _).mpr <| Mcan.tr_Truth.mpr
  fun p q h hp => (Mcan_eqv_t p q).mp h ▸ hp
theorem Mcan_TopBot : Mcan.Valid TopBot := (Mcan.valid_iff_tr _).mpr <| Mcan.tr_TopBot.mpr fun h => by
  have e := (Mcan_eqv_t _ _).mp h
  exact (e ▸ (fun hall : ∀ p : Prop, p => hall False) : ¬ ∀ p : Prop, p) (e ▸ (fun hall => hall False))
theorem Mcan_not_Cantor : ¬ Mcan.Valid Cantor := fun h => by
  obtain ⟨_, hG⟩ := Mcan.tr_Cantor.mp ((Mcan.valid_iff_tr _).mp h) .e
  exact hG () (Or.inr ⟨Or.inr rfl, Or.inl rfl⟩)
theorem Mcan_not_LLEqv : ¬ Mcan.Valid LLEqv := fun h =>
  Mcan.tr_LLEqv.mp ((Mcan.valid_iff_tr _).mp h) (.arr .e .t) (fun _ => False) (fun _ => True)
    (Or.inr ⟨Or.inr rfl, Or.inr rfl⟩) (fun g => ¬ g ()) id trivial
theorem Mcan_not_Disjoint : ¬ Mcan.Valid Disjoint := fun h =>
  Mcan.tr_Disjoint.mp ((Mcan.valid_iff_tr _).mp h) .e (.arr .e .t) (fun e => by cases e) () (fun _ => True)
    (Or.inr ⟨Or.inl rfl, Or.inr rfl⟩)
theorem Mcan_not_Slogan : ¬ Mcan.Valid Slogan := fun h =>
  Mcan.tr_Slogan.mp ((Mcan.valid_iff_tr _).mp h) () .e (fun _ => True) (Or.inr ⟨Or.inl rfl, Or.inr rfl⟩)
theorem Mcan_not_PCong : ¬ Mcan.Valid PCong := fun h => by
  have := Mcan.tr_PCong.mp ((Mcan.valid_iff_tr _).mp h) .e .t .t (fun _ => False) (fun _ => True) ()
    (Or.inr ⟨Or.inr rfl, Or.inr rfl⟩)
  exact cast ((Mcan_eqv_t _ _).mp this).symm trivial
theorem Mcan_not_WCong : ¬ Mcan.Valid WCong := fun h => by
  have := Mcan.tr_WCong.mp ((Mcan.valid_iff_tr _).mp h) .e .e .t .t (fun _ => False) (fun _ => True) () ()
    ⟨⟨rfl, rfl⟩, ⟨Or.inr ⟨Or.inr rfl, Or.inr rfl⟩, Or.inl rfl⟩⟩
  exact cast ((Mcan_eqv_t _ _).mp this).symm trivial
theorem Mcan_not_Twin : ¬ Mcan.Valid Twin := fun h => by
  obtain ⟨b, hb, y, hy⟩ := Mcan.tr_Twin.mp ((Mcan.valid_iff_tr _).mp h) .t True
  rcases hy with hy | ⟨hy | hy, _⟩
  · exact hb (congrArg Sigma.fst hy)
  · cases hy
  · cases hy
theorem Mcan_not_Hae : ¬ Mcan.Valid Hae := fun h => by
  have hy := Mcan.tr_Hae.mp ((Mcan.valid_iff_tr _).mp h) .t True
  rcases hy with hy | ⟨hy | hy, _⟩
  · cases congrArg Sigma.fst hy
  · cases hy
  · cases hy
theorem Mcan_not_ExtT : ¬ Mcan.Valid ExtT := fun h => by
  have := Mcan.tr_ExtT.mp ((Mcan.valid_iff_tr _).mp h) .e (.arr .e .t)
    ⟨fun _ => ⟨fun _ => True, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩, fun _ => ⟨(), Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩⟩
  cases this
theorem Mcan_not_IntT : ¬ Mcan.Valid IntT := fun h => Mcan_not_ExtT ((Mcan.IntT_iff_ExtT Mcan_eqv_t).mp h)
theorem Mcan_not_LLPoly : ¬ Mcan.Valid (LLPoly PredE) := fun h => by
  have := Mcan.tr_LLPolyE.mp ((Mcan.valid_iff_tr _).mp h) .e (.arr .e .t) () (fun _ => True)
    (Or.inr ⟨Or.inl rfl, Or.inr rfl⟩) rfl
  cases this

end PIF
