import PISchemas

/-!
# Exploring PI⁻

Further models of PI⁻ (in which LL≡ fails), and further truth values for the models of PI⁻.
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


/-! ## Two derivations in PI⁻ -/

section MoreDerivations
open Tm Derive
variable {S : Fm Ctx.nil → Prop}

/-- Truth proves `⊤ ≢ ⊥`: if `⊤ ≡ ⊥`, Truth gives `⊤ → ⊥`. -/
theorem d_TopBot_of_Truth (hT : S Truth) : Prov S Ctx.nil TopBot := by
  have h0 := Ent.inst (Ent.inst (Ent.ofProv (Γ := Ctx.nil) (Hs := [Tm.eqv tyT tyT topF botF]) (Prov.ax hT)) topF) botF
  have h2 : Ent S Ctx.nil ([] ++ [Tm.eqv tyT tyT topF botF]) (topF.imp botF) := Ent.mp h0 (Ent.hyp _ 0 (by decide))
  have h3 : Ent S Ctx.nil ([] ++ [Tm.eqv tyT tyT topF botF]) botF := Ent.mp h2 Ent.top
  exact Ent.toProv (Ent.notI h3 Ent.top)

abbrev Γc : Ctx 4 := (((Δ4.ext (tv3.arrow tv1)).ext (tv2.arrow tv0)).ext tv3).ext tv2

set_option maxHeartbeats 4000000 in
/-- Cong proves WCong, which is Cong with two further premises. -/
theorem d_WCong_of_Cong (hC : S Cong) : Prov S Ctx.nil WCong := by
  have h0 := (((((Ent.axm (Γ := Γc) (Hs := []) hC).tinst tv3).tinst tv2).tinst tv1).tinst tv0)
  have h1 := Ent.inst (Ent.inst (Ent.inst (Ent.inst h0 (.var (.there (.there (.there .here))))) (.var (.there (.there .here))))
    (.var (.there .here))) (.var .here)
  have h2 := Ent.mp (Ent.taut (.imp (.imp (.atom 0) (.atom 1)) (.imp (.conj (.atom 2) (.atom 0)) (.atom 1)))
    (v3 _ _ ((teq tv3 tv2).conj (teq tv1 tv0))) (fun _ f h => f h.2)) h1
  exact Ent.toProv (Ent.tgen (Ent.tgen (Ent.tgen (Ent.tgen (Ent.gen (tv3.arrow tv1) (Ent.gen (tv2.arrow tv0)
    (Ent.gen tv3 (Ent.gen tv2 h2))))))))

end MoreDerivations

/-! ## `𝔐_cant`: Cantor fails at `t`, while Slogan, Ext≈ and Int≈ hold

`⊤` and every function from `t` to `t` form a single class of identified items; nothing else is
identified with anything but itself. -/

def cantC (p : Σ c : Code Empty, unitUniv.El c) : Prop := (p.1 = .t ∧ HEq p.2 True) ∨ p.1 = .arr .t .t

def MctD : IdentData where
  U := unitUniv
  rel := fun p q => p = q ∨ (cantC p ∧ cantC q)
  refl := fun _ => Or.inl rfl
  symm := fun h => h.elim (fun e => Or.inl e.symm) (fun ⟨a, b⟩ => Or.inr ⟨b, a⟩)
  trans := by
    rintro p q r (rfl | ⟨_, hq⟩) (rfl | ⟨hq', hr⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hq', hr⟩
    · exact Or.inr ⟨by assumption, hq⟩
    · exact Or.inr ⟨by assumption, hr⟩

abbrev Mct : Frame := MctD.frame
theorem Mct_model : Mct.IsModelPIm := MctD.model
theorem Mct_Inj : Mct.Valid Inj := MctD.Inj_valid

theorem cantC_t {p : Prop} (h : cantC ⟨.t, p⟩) : p = True := by
  rcases h with ⟨_, h⟩ | h
  · exact eq_of_heq h
  · cases h

theorem Mct_eqv_t (p q : Prop) : Mct.eqv .t .t p q ↔ p = q := by
  refine ⟨fun h => ?_, fun h => h ▸ Or.inl rfl⟩
  rcases h with h | ⟨hp, hq⟩
  · exact eq_of_heq (Sigma.mk.inj h).2
  · exact (cantC_t hp).trans (cantC_t hq).symm

theorem Mct_Truth : Mct.Valid Truth := (Mct.valid_iff_tr _).mpr <| Mct.tr_Truth.mpr
  fun p q h hp => (Mct_eqv_t p q).mp h ▸ hp
theorem Mct_TopBot : Mct.Valid TopBot := (Mct.valid_iff_tr _).mpr <| Mct.tr_TopBot.mpr fun h => by
  have e := (Mct_eqv_t _ _).mp h
  exact (e ▸ (fun hall : ∀ p : Prop, p => hall False) : ¬ ∀ p : Prop, p) (e ▸ (fun hall => hall False))
theorem Mct_not_Cantor : ¬ Mct.Valid Cantor := fun h => by
  obtain ⟨_, hG⟩ := Mct.tr_Cantor.mp ((Mct.valid_iff_tr _).mp h) .t
  exact hG True (Or.inr ⟨Or.inr rfl, Or.inl ⟨rfl, HEq.rfl⟩⟩)
theorem Mct_Slogan : Mct.Valid Slogan := (Mct.valid_iff_tr _).mpr <| Mct.tr_Slogan.mpr fun _ _ _ h => by
  rcases h with h | ⟨⟨h, _⟩ | h, _⟩
  · cases congrArg Sigma.fst h
  · cases h
  · cases h

/-- Outside `t→t`, each type has an item identified only with itself. -/
theorem Mct_loner (c : Code Empty) (hc : c ≠ .arr .t .t) : ∃ z : unitUniv.El c, ¬ cantC ⟨c, z⟩ := by
  by_cases ht : c = .t
  · subst ht
    exact ⟨False, fun h => by have := cantC_t h; exact this ▸ trivial⟩
  · exact ⟨Classical.choice (Univ.El_nonempty (U := unitUniv) c), fun h => h.elim (fun h => ht h.1) hc⟩

theorem Mct_ExtT : Mct.Valid ExtT := (Mct.valid_iff_tr _).mpr <| Mct.tr_ExtT.mpr fun a b ⟨h1, h2⟩ => by
  show a = b
  refine Classical.byContradiction fun hab => ?_
  by_cases ha : a = .arr .t .t
  · have hb : b ≠ .arr .t .t := fun hb => hab (ha.trans hb.symm)
    obtain ⟨y, hy⟩ := Mct_loner b hb
    obtain ⟨x, hx⟩ := h2 y
    rcases hx with hx | ⟨_, hy'⟩
    · exact hab (congrArg Sigma.fst hx)
    · exact hy hy'
  · obtain ⟨x, hx⟩ := Mct_loner a ha
    obtain ⟨y, hy⟩ := h1 x
    rcases hy with hy | ⟨hx', _⟩
    · exact hab (congrArg Sigma.fst hy)
    · exact hx hx'
theorem Mct_IntT : Mct.Valid IntT := (Mct.IntT_iff_ExtT Mct_eqv_t).mpr Mct_ExtT
theorem Mct_not_LLEqv : ¬ Mct.Valid LLEqv := fun h =>
  Mct.tr_LLEqv.mp ((Mct.valid_iff_tr _).mp h) (.arr .t .t) (fun _ => False) (fun _ => True)
    (Or.inr ⟨Or.inr rfl, Or.inr rfl⟩) (fun g => ¬ g True) id trivial
theorem Mct_not_Disjoint : ¬ Mct.Valid Disjoint := fun h =>
  Mct.tr_Disjoint.mp ((Mct.valid_iff_tr _).mp h) .t (.arr .t .t) (fun e => by cases e) True (fun p => p)
    (Or.inr ⟨Or.inl ⟨rfl, HEq.rfl⟩, Or.inr rfl⟩)
theorem Mct_not_Twin : ¬ Mct.Valid Twin := fun h => by
  obtain ⟨b, hb, y, hy⟩ := Mct.tr_Twin.mp ((Mct.valid_iff_tr _).mp h) .t False
  rcases hy with hy | ⟨hy, _⟩
  · exact hb (congrArg Sigma.fst hy)
  · exact (cantC_t hy) ▸ trivial
theorem Mct_not_Hae : ¬ Mct.Valid Hae := fun h => by
  have hy := Mct.tr_Hae.mp ((Mct.valid_iff_tr _).mp h) .t False
  rcases hy with hy | ⟨hy, _⟩
  · cases congrArg Sigma.fst hy
  · exact (cantC_t hy) ▸ trivial
theorem Mct_not_PCong : ¬ Mct.Valid PCong := fun h => by
  have := Mct.tr_PCong.mp ((Mct.valid_iff_tr _).mp h) .t .t .t (fun _ => False) (fun _ => True) True
    (Or.inr ⟨Or.inr rfl, Or.inr rfl⟩)
  exact cast ((Mct_eqv_t _ _).mp this).symm trivial
theorem Mct_not_WCong : ¬ Mct.Valid WCong := fun h => by
  have := Mct.tr_WCong.mp ((Mct.valid_iff_tr _).mp h) .t .t .t .t (fun _ => False) (fun _ => True) True True
    ⟨⟨rfl, rfl⟩, ⟨Or.inr ⟨Or.inr rfl, Or.inr rfl⟩, Or.inl rfl⟩⟩
  exact cast ((Mct_eqv_t _ _).mp this).symm trivial

/-! ## `𝔐_D,twin`: `𝔐_D` with twins

Each of `e` and `t` has a duplicate type with the same items; every item is identified with its copy
in the duplicate type, and, as in `𝔐_D`, `0 ∼ 1` at `e` and `χ ∼ ζ` at `e→t`. -/

inductive DB : Type where
  | de | dt
  deriving DecidableEq

def DBEl : DB → Type
  | .de => Fin 3
  | .dt => Prop

def univDtw : Univ :=
  { E := Fin 3, Base := DB, B := DBEl, neE := ⟨0⟩, neB := fun b => match b with | .de => ⟨(show Fin 3 from 0)⟩ | .dt => ⟨(show Prop from True)⟩ }

def kc : Code DB → Code DB
  | .e => .e
  | .t => .t
  | .base .de => .e
  | .base .dt => .t
  | .arr a c => .arr (kc a) (kc c)

theorem El_kc : ∀ c, univDtw.El (kc c) = univDtw.El c
  | .e => rfl
  | .t => rfl
  | .base .de => rfl
  | .base .dt => rfl
  | .arr a c => by show (univDtw.El (kc a) → univDtw.El (kc c)) = _; rw [El_kc a, El_kc c]; rfl

def twc : Code DB → Code DB
  | .e => .base .de
  | .t => .base .dt
  | .base .de => .e
  | .base .dt => .t
  | .arr a c => .arr (twc a) c

theorem kc_twc : ∀ c, kc (twc c) = kc c
  | .e => rfl
  | .t => rfl
  | .base .de => rfl
  | .base .dt => rfl
  | .arr a c => by show Code.arr (kc (twc a)) (kc c) = _; rw [kc_twc a]; rfl

theorem twc_ne : ∀ c, twc c ≠ c
  | .e => fun h => by cases h
  | .t => fun h => by cases h
  | .base .de => fun h => by cases h
  | .base .dt => fun h => by cases h
  | .arr a c => fun h => by injection h with h1 _; exact twc_ne a h1

def chiT : Fin 3 → Prop := fun v => v = 0
def zetaT : Fin 3 → Prop := fun _ => False

/-- The two non-trivial classes of `𝔐_D`, up to duplication. -/
def SDk (p : Σ c : Code DB, univDtw.El c) : Prop :=
  (kc p.1 = .e ∧ (HEq p.2 (0 : Fin 3) ∨ HEq p.2 (1 : Fin 3))) ∨
  (kc p.1 = .arr .e .t ∧ (HEq p.2 chiT ∨ HEq p.2 zetaT))

theorem SDk_of {p q : Σ c : Code DB, univDtw.El c} (hk : kc p.1 = kc q.1) (h : HEq p.2 q.2) (hq : SDk q) : SDk p :=
  hq.elim (fun ⟨h1, h2⟩ => Or.inl ⟨hk.trans h1, h2.elim (fun e => Or.inl (h.trans e)) (fun e => Or.inr (h.trans e))⟩)
    (fun ⟨h1, h2⟩ => Or.inr ⟨hk.trans h1, h2.elim (fun e => Or.inl (h.trans e)) (fun e => Or.inr (h.trans e))⟩)

def MDtwD : IdentData where
  U := univDtw
  rel := fun p q => kc p.1 = kc q.1 ∧ (HEq p.2 q.2 ∨ (SDk p ∧ SDk q))
  refl := fun _ => ⟨rfl, Or.inl HEq.rfl⟩
  symm := fun ⟨h, h'⟩ => ⟨h.symm, h'.elim (fun e => Or.inl e.symm) (fun ⟨a, b⟩ => Or.inr ⟨b, a⟩)⟩
  trans := by
    rintro p q r ⟨h1, a1⟩ ⟨h2, a2⟩
    refine ⟨h1.trans h2, ?_⟩
    rcases a1 with e1 | ⟨s1, s2⟩ <;> rcases a2 with e2 | ⟨s3, s4⟩
    · exact Or.inl (e1.trans e2)
    · exact Or.inr ⟨SDk_of h1 e1 s3, s4⟩
    · exact Or.inr ⟨s1, SDk_of h2.symm e2.symm s2⟩
    · exact Or.inr ⟨s1, s4⟩

abbrev MDtw : Frame := MDtwD.frame
theorem MDtw_model : MDtw.IsModelPIm := MDtwD.model
theorem MDtw_Inj : MDtw.Valid Inj := MDtwD.Inj_valid

theorem MDtw_eqv_t (p q : Prop) : MDtw.eqv .t .t p q ↔ p = q := by
  refine ⟨fun ⟨_, h⟩ => ?_, fun h => h ▸ MDtwD.refl _⟩
  rcases h with h | ⟨h, _⟩
  · exact eq_of_heq h
  · rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h

theorem MDtw_Twin : MDtw.Valid Twin := (MDtw.valid_iff_tr _).mpr <| MDtw.tr_Twin.mpr fun a x =>
  have hE : univDtw.El a = univDtw.El (twc a) := (El_kc a).symm.trans ((congrArg univDtw.El (kc_twc a)).symm.trans (El_kc _))
  ⟨twc a, fun h => twc_ne a h.symm, cast hE x, (kc_twc a).symm, Or.inl (cast_heq _ _).symm⟩
theorem MDtw_Truth : MDtw.Valid Truth := (MDtw.valid_iff_tr _).mpr <| MDtw.tr_Truth.mpr
  fun p q h hp => (MDtw_eqv_t p q).mp h ▸ hp
theorem MDtw_TopBot : MDtw.Valid TopBot := (MDtw.valid_iff_tr _).mpr <| MDtw.tr_TopBot.mpr fun h => by
  have e := (MDtw_eqv_t _ _).mp h
  exact (e ▸ (fun hall : ∀ p : Prop, p => hall False) : ¬ ∀ p : Prop, p) (e ▸ (fun hall => hall False))
theorem MDtw_not_LLEqv : ¬ MDtw.Valid LLEqv := fun h =>
  absurd (MDtw.tr_LLEqv.mp ((MDtw.valid_iff_tr _).mp h) .e (0 : Fin 3) (1 : Fin 3)
    ⟨rfl, Or.inr ⟨Or.inl ⟨rfl, Or.inl HEq.rfl⟩, Or.inl ⟨rfl, Or.inr HEq.rfl⟩⟩⟩ (fun (v : Fin 3) => v = 0) rfl) (by decide)
theorem MDtw_not_Disjoint : ¬ MDtw.Valid Disjoint := fun h =>
  MDtw.tr_Disjoint.mp ((MDtw.valid_iff_tr _).mp h) .e (.base .de) (fun e => by cases e) (0 : Fin 3) (0 : Fin 3)
    ⟨rfl, Or.inl HEq.rfl⟩
theorem MDtw_not_ExtT : ¬ MDtw.Valid ExtT := fun h => by
  have := MDtw.tr_ExtT.mp ((MDtw.valid_iff_tr _).mp h) .e (.base .de)
    ⟨fun x => ⟨x, rfl, Or.inl HEq.rfl⟩, fun y => ⟨y, rfl, Or.inl HEq.rfl⟩⟩
  cases this
theorem MDtw_not_IntT : ¬ MDtw.Valid IntT := fun h => MDtw_not_ExtT ((MDtw.IntT_iff_ExtT MDtw_eqv_t).mp h)
theorem MDtw_Cantor : MDtw.Valid Cantor := (MDtw.valid_iff_tr _).mpr <| MDtw.tr_Cantor.mpr
  fun a => ⟨fun _ => True, fun _ h => Code.arr_ne_left (kc a) .t h.1⟩
theorem MDtw_Slogan : MDtw.Valid Slogan := (MDtw.valid_iff_tr _).mpr <| MDtw.tr_Slogan.mpr
  fun _ _ _ h => by cases h.1
theorem MDtw_not_Hae : ¬ MDtw.Valid Hae := fun h => by
  have := MDtw.tr_Hae.mp ((MDtw.valid_iff_tr _).mp h) .e (0 : Fin 3)
  cases this.1
theorem MDtw_not_PCong : ¬ MDtw.Valid PCong := fun h => by
  have := MDtw.tr_PCong.mp ((MDtw.valid_iff_tr _).mp h) .e .t .t chiT zetaT (0 : Fin 3)
    ⟨rfl, Or.inr ⟨Or.inr ⟨rfl, Or.inl HEq.rfl⟩, Or.inr ⟨rfl, Or.inr HEq.rfl⟩⟩⟩
  exact cast ((MDtw_eqv_t _ _).mp this) (show chiT 0 from rfl)
theorem MDtw_not_WCong : ¬ MDtw.Valid WCong := fun h => by
  have := MDtw.tr_WCong.mp ((MDtw.valid_iff_tr _).mp h) .e .e .t .t chiT zetaT (0 : Fin 3) (0 : Fin 3)
    ⟨⟨rfl, rfl⟩, ⟨⟨rfl, Or.inr ⟨Or.inr ⟨rfl, Or.inl HEq.rfl⟩, Or.inr ⟨rfl, Or.inr HEq.rfl⟩⟩⟩, ⟨rfl, Or.inl HEq.rfl⟩⟩⟩
  exact cast ((MDtw_eqv_t _ _).mp this) (show chiT 0 from rfl)

theorem MDtw_R0 : MDtw.Rf .e (0 : Fin 3) :=
  ⟨chiT, rfl, zetaT, ⟨rfl, Or.inr ⟨Or.inr ⟨rfl, Or.inl HEq.rfl⟩, Or.inr ⟨rfl, Or.inr HEq.rfl⟩⟩⟩, id⟩
theorem MDtw_not_R1 : ¬ MDtw.Rf .e (1 : Fin 3) := by
  rintro ⟨P, hP, G, ⟨_, hPG⟩, hG⟩
  rcases hPG with h | ⟨hS, _⟩
  · have e : P = G := eq_of_heq h
    exact hG (e ▸ hP)
  · rcases hS with ⟨h, _⟩ | ⟨_, h | h⟩
    · cases h
    · have e : P = chiT := eq_of_heq h
      subst e
      exact absurd (show (1 : Fin 3) = 0 from hP) (show ¬ (1 : Fin 3) = 0 by decide)
    · have e : P = zetaT := eq_of_heq h
      subst e
      exact hP
theorem MDtw_not_Bridge : ¬ MDtw.Valid (Bridge PredR) := fun h =>
  MDtw_not_R1 (MDtw.tr_BridgeR.mp ((MDtw.valid_iff_tr _).mp h) .e .e (0 : Fin 3) (1 : Fin 3)
    ⟨⟨rfl, Or.inr ⟨Or.inl ⟨rfl, Or.inl HEq.rfl⟩, Or.inl ⟨rfl, Or.inr HEq.rfl⟩⟩⟩, rfl⟩ MDtw_R0)

end PIF
