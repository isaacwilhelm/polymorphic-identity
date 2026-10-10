import PIBF

/-!
# Small facts about existing models

* `𝔐_hae,c` (worlds): identity at `t` is identity, so BF and CBF hold.
* `𝔐_int` (tagged): NI× holds, as in `𝔐_int0`.
* `𝔐_tot` and `𝔐_all` (standard): any two propositions are identified, so every `□`-formula is
  true, and BF and CBF hold trivially.
* `𝔐_k,cong` (Kripke): every proposition is identified with `⊤`, so BF and CBF hold trivially.
* `𝔐_⊤⊥,hae` (algebraic): the only true proposition is `0 = ⊤`, so Collapse holds; and a true
  universal quantification has only true instances, so CBF holds.
-/
set_option autoImplicit false

namespace PIF
open Tm

/-! ## `𝔐_hae,c`: BF and CBF -/

namespace Wd

theorem MhaeC_hb : ∀ p q, MhaeCF.eqv .t .t p q MhaeCF.U.w0 ↔ p = q :=
  fun p q => ⟨MhaeC_eq .t p q _, fun h => h ▸ rfl⟩

theorem MhaeC_BF : MhaeCF.Valid BF := MhaeCF.BF_of MhaeC_hb
theorem MhaeC_CBF : MhaeCF.Valid CBF := MhaeCF.CBF_of MhaeC_hb

end Wd

/-! ## `𝔐_int`: NI× -/

namespace Tg

theorem Mi_NIX : MiF.Valid NIX := by
  intro ρ env a b
  refine (MiF.holds_all _ _ _ _).mpr fun x => (MiF.holds_all _ _ _ _).mpr fun y h => ?_
  exact (MiF.holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq (Prod.ext (propext ⟨fun _ hall => hall (False, true), fun _ => h⟩) rfl)⟩

end Tg

/-! ## `𝔐_tot` and `𝔐_all`: BF and CBF -/

theorem Mtot_BF : Mtot.Valid BF := by
  intro ρ env a
  refine (Mtot.holds_all _ _ _ _).mpr fun _ => (Mtot.holds_imp _ _ _ _).mpr fun _ => ?_
  exact (Mtot.holds_eqv tyT tyT _ _ _ _).mpr ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩

theorem Mtot_CBF : Mtot.Valid CBF := by
  intro ρ env a
  refine (Mtot.holds_all _ _ _ _).mpr fun _ => (Mtot.holds_imp _ _ _ _).mpr fun _ => ?_
  refine (Mtot.holds_all _ _ _ _).mpr fun _ => ?_
  exact (Mtot.holds_eqv tyT tyT _ _ _ _).mpr ⟨rfl, Or.inr ⟨trivial, trivial⟩⟩

theorem Mall_BF : Mall.Valid BF := by
  intro ρ env a
  refine (Mall.holds_all _ _ _ _).mpr fun _ => (Mall.holds_imp _ _ _ _).mpr fun _ => ?_
  exact (Mall.holds_eqv tyT tyT _ _ _ _).mpr trivial

theorem Mall_CBF : Mall.Valid CBF := by
  intro ρ env a
  refine (Mall.holds_all _ _ _ _).mpr fun _ => (Mall.holds_imp _ _ _ _).mpr fun _ => ?_
  refine (Mall.holds_all _ _ _ _).mpr fun _ => ?_
  exact (Mall.holds_eqv tyT tyT _ _ _ _).mpr trivial

/-! ## `𝔐_k,cong`: BF and CBF -/

namespace Kr

theorem KC_BF : KC.Valid BF := by
  intro ρ _ env _
  refine (KC.holdsAt_tall _ _ _ _).mpr fun a _ => (KC.holdsAt_all _ _ _ _ _).mpr fun _ _ => ?_
  refine (KC.holdsAt_imp _ _ _ _ _).mpr fun _ => ?_
  exact (KC.holdsAt_eqv _ _ _ _ _ _ _).mpr rfl

theorem KC_CBF : KC.Valid CBF := by
  intro ρ _ env _
  refine (KC.holdsAt_tall _ _ _ _).mpr fun a _ => (KC.holdsAt_all _ _ _ _ _).mpr fun _ _ => ?_
  refine (KC.holdsAt_imp _ _ _ _ _).mpr fun _ => (KC.holdsAt_all _ _ _ _ _).mpr fun _ _ => ?_
  exact (KC.holdsAt_eqv _ _ _ _ _ _ _).mpr rfl

end Kr

/-! ## `𝔐_⊤⊥,hae`: Collapse and CBF -/

namespace Al

/-- A proposition of the form `mk3 c` identified with `0` is `0`. -/
theorem mk3_simB {c : Prop} (h : simB (mk3 c) 0) : VB (mk3 c) := by
  by_cases hc : c
  · exact mk3_eq0 hc
  · rw [mk3_eq2 hc] at h
    rcases h with h | ⟨h, _⟩
    · exact absurd h (by decide)
    · exact absurd rfl h

theorem MBH_Collapse : MBH.Valid Collapse := by
  intro ρ env
  refine (MBH.holds_all _ _ _ _).mpr fun p => (MBH.holds_imp _ _ _ _).mpr fun hp => ?_
  refine (MBH.holds_eqv_t _ _ _ _).mpr ((F3_eqT VB VB0 VB2 simB _ _ simB_refl).mpr ?_)
  rw [F3_top VB VB0 VB2 simB (Γ := Ctx.nil.ext tyT) ρ (env, p)]
  exact Or.inl hp

theorem MBH_CBF : MBH.Valid CBF := by
  intro ρ env
  refine (MBH.holds_tall _ _ _).mpr fun a => (MBH.holds_all _ _ _ _).mpr fun G => ?_
  refine (MBH.holds_imp _ _ _ _).mpr fun h => (MBH.holds_all _ _ _ _).mpr fun x => ?_
  have hq := (F3_eqT VB VB0 VB2 simB _ _ simB_refl).mp ((MBH.holds_eqv_t _ _ _ _).mp h)
  rw [F3_top VB VB0 VB2 simB (Γ := (Ctx.nil.text).ext tv0.pred) (scons a ρ) (env, G)] at hq
  have e := MBH.eval_all (Γ := (Ctx.nil.text).ext tv0.pred) tv0 (Tm.app (.var (.there .here)) (.var .here))
    (scons a ρ) (env, G)
  rw [e] at hq
  have hall : MBH.Holds (all tv0 (Tm.app (.var (.there .here)) (.var .here)) : Fm ((Ctx.nil.text).ext tv0.pred))
      (scons a ρ) (env, G) := cast (congrArg MBH.U.V e).symm (mk3_simB hq)
  have hx : VB (MBH.eval (Tm.app (.var (.there .here)) (.var .here) : Fm (((Ctx.nil.text).ext tv0.pred).ext tv0))
      (scons a ρ) ((env, G), x)) := (MBH.holds_all _ _ _ _).mp hall x
  refine (MBH.holds_eqv_t _ _ _ _).mpr ((F3_eqT VB VB0 VB2 simB _ _ simB_refl).mpr ?_)
  rw [F3_top VB VB0 VB2 simB (Γ := ((Ctx.nil.text).ext tv0.pred).ext tv0) (scons a ρ) ((env, G), x)]
  exact Or.inl hx

end Al

end PIF
