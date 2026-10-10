import PIBF
set_option autoImplicit false

/-!
# Open questions: the profile of `𝔐_pb`

The normal-form model `𝔐_pb` of `PINF.lean`: `E = {0,1,2}` with `0 ∼ 1`; the normal form of a
function is the map from its domain to the normal forms of its values, except that
`h₁ = (0↦2, 1↦0, 2↦0)` gets the normal form of the constant function `0`; items are identified just
in case their normal forms agree, and `≈` is identity of types.

A normal form determines the type of its item (`Mpb_ty_N3`), so items are identified only within a
type: Disjoint, Slogan, Cantor, Ext≈ and Int≈ hold, while Twin and Hae fail. At `t` the normal form is
the proposition itself, so `≡_t` is identity: Truth, ⊤≢⊥, PropExt hold, and with them T, Bool, TBF,
TCBF, BF and CBF. Cong, WCong and PCong fail at `h₁ ≡ h₂` applied to `0`. IdId fails at `0 ≡ 1`, and
so Classicism fails.
-/

namespace PIF

section MpbP

/-- The type of an item, read off its normal form. -/
noncomputable def Mpb_ty : NF univ3 → C3
  | .base c _ => c
  | .fn a φ => .arr a (Mpb_ty (φ (Classical.choice (Univ.El_nonempty (U := univ3) a))))

theorem Mpb_ty_fn (a : C3) (φ : univ3.El a → NF univ3) :
    Mpb_ty (.fn a φ) = .arr a (Mpb_ty (φ (Classical.choice (Univ.El_nonempty (U := univ3) a)))) := by
  rw [Mpb_ty]

theorem Mpb_ty_N3 : ∀ (c : C3) (x : univ3.El c), Mpb_ty (N3 c x) = c
  | .e, _ => rfl
  | .t, _ => rfl
  | .base b, _ => b.elim
  | .arr a c, f => by
    rw [N3_arr]; unfold N3fun; split
    · next h =>
      obtain ⟨ha, hf⟩ := h
      subst ha
      have ef : (fun x => N3 c (f x)) = φ1 := eq_of_heq hf
      have e0 : N3 c (f (0 : Fin 3)) = NF.base (U := univ3) .e (nz (h1f (0 : Fin 3))) := congrFun ef (0 : Fin 3)
      have hc : c = .e := (Mpb_ty_N3 c (f (0 : Fin 3))).symm.trans (congrArg Mpb_ty e0)
      subst hc
      rw [Mpb_ty_fn]; rfl
    · rw [Mpb_ty_fn, Mpb_ty_N3 c]

/-- Items are identified only within a type. -/
theorem Mpb_eqv_code {a b : C3} {x : univ3.El a} {y : univ3.El b} (h : Mpb.eqv a b x y) : a = b :=
  (Mpb_ty_N3 a x).symm.trans ((congrArg Mpb_ty (h : N3 a x = N3 b y)).trans (Mpb_ty_N3 b y))

theorem Mpb_eqv_t (p q : Prop) : Mpb.eqv .t .t p q ↔ p = q :=
  ⟨fun h => by injection (h : NF.base (U := univ3) .t p = NF.base .t q),
   fun h => by subst h; exact rfl⟩

/-- `h₁ ≡ h₂`, while `h₁ 0 = 2` and `h₂ 0 = 0` are not identified. -/
theorem Mpb_h12 : Mpb.eqv (.arr .e .e) (.arr .e .e) h1f h2f := N3_h1.trans N3_h2.symm

theorem Mpb_not_h12_0 : ¬ Mpb.eqv .e .e (h1f (0 : Fin 3)) (h2f (0 : Fin 3)) := fun h =>
  absurd (nb_inj (h : N3 .e (h1f 0) = N3 .e (h2f 0))) (show ¬ nz (h1f 0) = nz (h2f 0) by decide)

/-! ## Identification across types -/

theorem Mpb_Disjoint : Mpb.Valid Disjoint :=
  (Mpb.valid_iff_tr _).mpr <| Mpb.tr_Disjoint.mpr fun _ _ hab _ _ h => hab (Mpb_eqv_code h)

theorem Mpb_Slogan : Mpb.Valid Slogan :=
  (Mpb.valid_iff_tr _).mpr <| Mpb.tr_Slogan.mpr fun _ _ _ h => by
    have := Mpb_eqv_code h
    cases this

theorem Mpb_not_Twin : ¬ Mpb.Valid Twin := fun h => by
  obtain ⟨_, hb, _, hy⟩ := Mpb.tr_Twin.mp ((Mpb.valid_iff_tr _).mp h) .t True
  exact hb (Mpb_eqv_code hy)

theorem Mpb_not_Hae : ¬ Mpb.Valid Hae := fun h =>
  Code.arr_ne_left (Code.e : C3) .t (Mpb_eqv_code (Mpb.tr_Hae.mp ((Mpb.valid_iff_tr _).mp h) .e (0 : Fin 3))).symm

theorem Mpb_Cantor : Mpb.Valid Cantor :=
  (Mpb.valid_iff_tr _).mpr <| Mpb.tr_Cantor.mpr fun a => ⟨fun _ => True, fun _ h =>
    Code.arr_ne_left a .t (Mpb_eqv_code h)⟩

theorem Mpb_ExtT : Mpb.Valid ExtT :=
  (Mpb.valid_iff_tr _).mpr <| Mpb.tr_ExtT.mpr fun a _ ⟨h1, _⟩ =>
    (h1 (Classical.choice (Univ.El_nonempty (U := univ3) a))).elim fun _ h => Mpb_eqv_code h

theorem Mpb_IntT : Mpb.Valid IntT := (Mpb.IntT_iff_ExtT Mpb_eqv_t).mpr Mpb_ExtT

/-! ## Congruence -/

theorem Mpb_not_PCong : ¬ Mpb.Valid PCong := fun h =>
  Mpb_not_h12_0 (Mpb.tr_PCong.mp ((Mpb.valid_iff_tr _).mp h) .e .e .e h1f h2f (0 : Fin 3) Mpb_h12)

theorem Mpb_not_WCong : ¬ Mpb.Valid WCong := fun h =>
  Mpb_not_h12_0 (Mpb.tr_WCong.mp ((Mpb.valid_iff_tr _).mp h) .e .e .e .e h1f h2f (0 : Fin 3) (0 : Fin 3)
    ⟨⟨rfl, rfl⟩, ⟨Mpb_h12, rfl⟩⟩)

theorem Mpb_not_Cong : ¬ Mpb.Valid Cong := fun h =>
  Mpb_not_h12_0 (Mpb.tr_Cong.mp ((Mpb.valid_iff_tr _).mp h) .e .e .e .e h1f h2f (0 : Fin 3) (0 : Fin 3)
    ⟨Mpb_h12, rfl⟩)

/-! ## Propositions -/

theorem Mpb_Truth : Mpb.Valid Truth :=
  (Mpb.valid_iff_tr _).mpr <| Mpb.tr_Truth.mpr fun _ _ h hp => cast ((Mpb_eqv_t _ _).mp h) hp

theorem Mpb_TopBot : Mpb.Valid TopBot :=
  (Mpb.valid_iff_tr _).mpr <| Mpb.tr_TopBot.mpr fun h => by
    have e : (¬ ∀ p : Prop, p) = (∀ p : Prop, p) := (Mpb_eqv_t _ _).mp h
    exact (cast e (fun hall => hall False)) False

theorem Mpb_PropExt : Mpb.Valid PropExt := Mpb.PropExt_valid Mpb_model

theorem Mpb_Collapse : Mpb.Valid Collapse := Mpb.Collapse_valid Mpb_model

/-- IdId fails: `0 ≡ 1` is true, but `0` and `1` differ in their properties. -/
theorem Mpb_not_IdId : ¬ Mpb.Valid IdId := fun h => by
  have := Mpb.tr_IdId.mp ((Mpb.valid_iff_tr _).mp h) .e (0 : Fin 3) (1 : Fin 3)
  have e := (Mpb_eqv_t _ _).mp this
  have h01 : Mpb.eqv .e .e (0 : Fin 3) (1 : Fin 3) := (rfl : N3 .e (0 : Fin 3) = N3 .e (1 : Fin 3))
  have h2 : (1 : Fin 3) = 0 := cast e h01 (fun z => z = (0 : Fin 3)) rfl
  exact absurd h2 (by decide)

/-! ### By soundness -/

theorem Mpb_of_prov {S : Fm Ctx.nil → Prop} (hS : ∀ ψ, S ψ → Mpb.Valid ψ) {φ : Fm Ctx.nil}
    (h : Prov S Ctx.nil φ) : Mpb.Valid φ :=
  Mpb.soundness Mpb_model hS h

/-- Classicism fails, since it proves IdId (in PI⁻). -/
theorem Mpb_not_Class : ¬ ∀ χ, ClassSch χ → Mpb.Valid χ := fun h =>
  Mpb_not_IdId (Mpb_of_prov h (d_IdId_of_Class (S := ClassSch) (fun _ hc => hc)))

theorem Mpb_TAx : Mpb.Valid TAx :=
  Mpb_of_prov (S := (· = Truth)) (fun _ h => h ▸ Mpb_Truth) (d_TAx_of_Truth rfl)

theorem Mpb_Bool : ∀ φ, BoolSch φ → Mpb.Valid φ := fun φ hφ =>
  Mpb_of_prov (S := (· = PropExt)) (fun _ h => h ▸ Mpb_PropExt) (d_Bool_of_PropExt (S := (· = PropExt)) rfl φ hφ)

theorem Mpb_TBF : ∀ χ, TBFSch χ → Mpb.Valid χ := fun χ hχ =>
  Mpb_of_prov (S := (· = PropExt)) (fun _ h => h ▸ Mpb_PropExt) (d_TBF_of_PropExt (S := (· = PropExt)) rfl χ hχ)

theorem Mpb_TCBF : ∀ χ, TCBFSch χ → Mpb.Valid χ := fun χ hχ =>
  Mpb_of_prov (S := (· = PropExt)) (fun _ h => h ▸ Mpb_PropExt) (d_TCBF_of_PropExt (S := (· = PropExt)) rfl χ hχ)

theorem Mpb_BF : Mpb.Valid BF :=
  Mpb_of_prov (S := fun ψ => ψ = Collapse ∨ ψ = TAx)
    (fun _ h => h.elim (fun e => e ▸ Mpb_Collapse) (fun e => e ▸ Mpb_TAx))
    (d_BF_of_Collapse (Or.inl rfl) (Or.inr rfl))

theorem Mpb_CBF : Mpb.Valid CBF :=
  Mpb_of_prov (S := fun ψ => ψ = Collapse ∨ ψ = TAx)
    (fun _ h => h.elim (fun e => e ▸ Mpb_Collapse) (fun e => e ▸ Mpb_TAx))
    (d_CBF_of_Collapse (Or.inl rfl) (Or.inr rfl))

end MpbP

end PIF
