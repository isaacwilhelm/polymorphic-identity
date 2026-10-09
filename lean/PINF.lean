import PINew

/-!
# Normal forms

Models in which each item has a *normal form*, and items are identified just in case their normal
forms agree. The normal form of a function depends only on its domain and on the normal forms of its
values, so PExt holds in each.
-/
set_option autoImplicit false

namespace PIF

/-- Normal forms: an item of a base type, or a function from a type into normal forms. -/
inductive NF (U : Univ) : Type where
  | base (c : Code U.Base) (x : U.El c)
  | fn (a : Code U.Base) (φ : U.El a → NF U)

def NF.sz {U : Univ} : NF U → Nat
  | .base _ _ => 0
  | .fn a _ => csz a + 1

/-! ## `𝔐_hae,x`: Haecceitism and PExt, in PI

`E = 1`. The normal form of a function is the normal form of `x` if its values have the normal forms
of the values of the haecceity of `x`, and otherwise the function from its domain to the normal forms
of its values. -/

section Mhx
attribute [local instance] Classical.propDecidable

noncomputable def Nx : (c : Code unitUniv.Base) → unitUniv.El c → NF unitUniv
  | .arr a c, f =>
    if h : ∃ x0, (fun x => Nx c (f x)) = (fun y => NF.base .t ((Nx a y = Nx a x0 : Prop)))
    then Nx a (Classical.choose h) else NF.fn a (fun x => Nx c (f x))
  | c, x => NF.base c x

noncomputable def Nfun (a : Code unitUniv.Base) (φ : unitUniv.El a → NF unitUniv) : NF unitUniv :=
  if h : ∃ x0, φ = (fun y => NF.base .t ((Nx a y = Nx a x0 : Prop))) then Nx a (Classical.choose h) else NF.fn a φ

theorem Nx_arr (a c : Code unitUniv.Base) (f : unitUniv.El (.arr a c)) : Nx (.arr a c) f = Nfun a (fun x => Nx c (f x)) := by
  rw [Nx.eq_def]; rfl

theorem Nx_t (p : Prop) : Nx .t p = NF.base .t p := rfl

theorem Nx_sz : ∀ (c : Code unitUniv.Base) (x : unitUniv.El c), (Nx c x).sz ≤ csz c
  | .arr a c, f => by
    rw [Nx_arr]; unfold Nfun; split
    · exact Nat.le_trans (Nx_sz a _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_succ _))
    · exact Nat.succ_le_succ (Nat.le_add_right _ _)
  | .e, _ => Nat.zero_le _
  | .t, _ => Nat.zero_le _
  | .base b, _ => b.elim

theorem Nx_inj : ∀ (c : Code unitUniv.Base) (x y : unitUniv.El c), Nx c x = Nx c y → x = y
  | .arr a c, f, g, h => by
    rw [Nx_arr, Nx_arr] at h
    unfold Nfun at h
    have pw : (fun x => Nx c (f x)) = (fun x => Nx c (g x)) → f = g := fun e =>
      funext fun x => Nx_inj c _ _ (congrFun e x)
    split at h <;> split at h
    · next h1 h2 =>
      apply pw
      rw [Classical.choose_spec h1, Classical.choose_spec h2]
      funext y; rw [h]
    · next h1 _ =>
      have := Nx_sz a (Classical.choose h1)
      rw [h] at this
      exact absurd this (Nat.not_succ_le_self _)
    · next _ h2 =>
      have := Nx_sz a (Classical.choose h2)
      rw [← h] at this
      exact absurd this (Nat.not_succ_le_self _)
    · injection h with _ h2
      exact pw h2
  | .e, (), (), _ => rfl
  | .t, x, y, h => by injection h
  | .base b, _, _, _ => b.elim

theorem Nx_hae (a : Code unitUniv.Base) (x : unitUniv.El a) :
    Nx (.arr a .t) (show unitUniv.El (.arr a .t) from fun y => Nx a y = Nx a x) = Nx a x := by
  refine (Nx_arr a .t _).trans ?_; unfold Nfun
  split
  · next h =>
    have hc := congrFun (Classical.choose_spec h) (Classical.choose h)
    injection hc with _ h2
    exact h2.mpr rfl
  · next h => exact absurd ⟨x, rfl⟩ h

noncomputable def MhxD : IdentData where
  U := unitUniv
  rel := fun p q => Nx p.1 p.2 = Nx q.1 q.2
  refl := fun _ => rfl
  symm := fun h => h.symm
  trans := fun h1 h2 => h1.trans h2

noncomputable abbrev Mhx : Frame := MhxD.frame
theorem Mhx_model : Mhx.IsModelPIm := MhxD.model
theorem Mhx_LLEqv : Mhx.Valid LLEqv := MhxD.LLEqv_valid Nx_inj
theorem Mhx_Hae : Mhx.Valid Hae := (Mhx.valid_iff_tr _).mpr <| Mhx.tr_Hae.mpr fun a x => (Nx_hae a x).symm
theorem Mhx_PExt : Mhx.Valid PExt := (Mhx.valid_iff_tr _).mpr <| Mhx.tr_PExt.mpr fun a c d f g h => by
  exact (Nx_arr a c f).trans ((congrArg (Nfun a) (funext h)).trans (Nx_arr a d g).symm)
theorem Mhx_Twin : Mhx.Valid Twin := (Mhx.valid_iff_tr _).mpr <| Mhx.tr_Twin.mpr fun a x =>
  ⟨.arr a .t, fun h => Code.arr_ne_left a .t h.symm, fun y => Nx a y = Nx a x, (Nx_hae a x).symm⟩
theorem Mhx_Inj : Mhx.Valid Inj := MhxD.Inj_valid

end Mhx


/-! ## `𝔐_pb`: PExt without LL≡/≈, in PI⁻

`E = {0,1,2}` with `0 ∼ 1`; normal forms of functions are the functions from their domains to the
normal forms of their values, except that `h₁ = (0↦2, 1↦0, 2↦0)` (and whatever agrees with it up to
`0 ∼ 1`) gets the normal form of `h₂ = (x ↦ 0)`. So `h₁ ≡ h₂`, though `h₁ 0 = 2` and `h₂ 0 = 0` are not
identified, while no two identified functions on `e` take unidentified values at `1`. -/

/-- The polymorphic predicate `λγ.λz. ∃f,g:γ→γ (f ≡ g ∧ ¬ f z ≡ g z)`. -/
def PredK2 : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (Tm.ex (tv0.arrow tv0) (Tm.ex (tv0.arrow tv0)
    (Tm.conj (Tm.eqv (tv0.arrow tv0) (tv0.arrow tv0) (.var (.there .here)) (.var .here))
      (Tm.neg (Tm.eqv tv0 tv0 (.app (.var (.there .here)) (.var (.there (.there .here))))
        (.app (.var .here) (.var (.there (.there .here))))))))))

namespace Frame
variable (F : Frame)
def Kf2 (a : Code F.U.Base) (z : F.U.El a) : Prop :=
  ∃ f : F.U.El a → F.U.El a, ∃ g : F.U.El a → F.U.El a, F.eqv (.arr a a) (.arr a a) f g ∧ ¬ F.eqv a a (f z) (g z)
theorem tr_BridgeK2 : F.Tr (Bridge PredK2) ↔
    ∀ a b (x : F.U.El a) (y : F.U.El b), F.eqv a b x y ∧ F.teq a b → F.Kf2 a x → F.Kf2 b y := Iff.rfl
end Frame

section Mpb
attribute [local instance] Classical.propDecidable

def nz (x : Fin 3) : Fin 3 := if x = 1 then 0 else x
def h1f : Fin 3 → Fin 3 := fun x => if x = 0 then 2 else 0
def h2f : Fin 3 → Fin 3 := fun _ => 0
abbrev C3 := Code univ3.Base
def φ1 : univ3.El .e → NF univ3 := fun x => NF.base .e (nz (h1f x))
def φ2 : univ3.El .e → NF univ3 := fun x => NF.base .e (nz (h2f x))

noncomputable def N3 : (c : C3) → univ3.El c → NF univ3
  | .e, x => NF.base .e (nz x)
  | .arr a c, f => @dite _ (a = .e ∧ HEq (fun x => N3 c (f x)) φ1) (Classical.propDecidable _)
      (fun _ => NF.fn .e φ2) (fun _ => NF.fn a (fun x => N3 c (f x)))
  | c, x => NF.base c x

noncomputable def N3fun (a : C3) (φ : univ3.El a → NF univ3) : NF univ3 :=
  @dite _ (a = .e ∧ HEq φ φ1) (Classical.propDecidable _) (fun _ => NF.fn .e φ2) (fun _ => NF.fn a φ)

theorem N3_arr (a c : C3) (f : univ3.El (.arr a c)) : N3 (.arr a c) f = N3fun a (fun x => N3 c (f x)) := by
  rw [N3.eq_def]; rfl

noncomputable def MpbD : IdentData where
  U := univ3
  rel := fun p q => N3 p.1 p.2 = N3 q.1 q.2
  refl := fun _ => rfl
  symm := fun h => h.symm
  trans := fun h1 h2 => h1.trans h2

noncomputable abbrev Mpb : Frame := MpbD.frame
theorem Mpb_model : Mpb.IsModelPIm := MpbD.model
theorem Mpb_Inj : Mpb.Valid Inj := MpbD.Inj_valid
theorem Mpb_PExt : Mpb.Valid PExt := (Mpb.valid_iff_tr _).mpr <| Mpb.tr_PExt.mpr fun a c d f g h =>
  (N3_arr a c f).trans ((congrArg (N3fun a) (funext h)).trans (N3_arr a d g).symm)

theorem N3_e (x : Fin 3) : N3 .e x = (NF.base (U := univ3) .e (nz x)) := rfl

theorem N3_h1 : N3 (.arr .e .e) h1f = NF.fn .e φ2 := by
  refine (N3_arr .e .e h1f).trans ?_
  unfold N3fun; split
  · rfl
  · next hn => exact absurd ⟨rfl, HEq.rfl⟩ hn
theorem N3_h2 : N3 (.arr .e .e) h2f = NF.fn .e φ2 := by
  refine (N3_arr .e .e h2f).trans ?_
  unfold N3fun; split
  · rfl
  · rfl

theorem nb_inj {x y : Fin 3} (h : (NF.base (U := univ3) .e x) = NF.base (U := univ3) .e y) : x = y := by
  injection h

theorem Mpb_K0 : Mpb.Kf2 .e (0 : Fin 3) :=
  ⟨h1f, h2f, N3_h1.trans N3_h2.symm, fun h => absurd (nb_inj (h : N3 .e (h1f 0) = N3 .e (h2f 0)))
    (show ¬ nz (h1f 0) = nz (h2f 0) by decide)⟩

theorem Mpb_not_K1 : ¬ Mpb.Kf2 .e (1 : Fin 3) := by
  rintro ⟨f, g, hfg, hn⟩
  have hfg' : N3fun .e (fun x => N3 .e (f x)) = N3fun .e (fun x => N3 .e (g x)) :=
    (N3_arr .e .e f).symm.trans (hfg.trans (N3_arr .e .e g))
  apply hn
  show N3 .e (f (1 : Fin 3)) = N3 .e (g (1 : Fin 3))
  have v1 : φ1 (1 : Fin 3) = NF.base (U := univ3) .e (0 : Fin 3) := rfl
  have v2 : φ2 (1 : Fin 3) = NF.base (U := univ3) .e (0 : Fin 3) := rfl
  unfold N3fun at hfg'
  split at hfg' <;> split at hfg'
  · next hf hg =>
    have ef : (fun x => N3 .e (f x)) = φ1 := eq_of_heq hf.2
    have eg : (fun x => N3 .e (g x)) = φ1 := eq_of_heq hg.2
    exact (congrFun ef (1 : Fin 3)).trans (congrFun eg (1 : Fin 3)).symm
  · next hf _ =>
    have ef : (fun x => N3 .e (f x)) = φ1 := eq_of_heq hf.2
    injection hfg' with _ h2
    exact (congrFun ef (1 : Fin 3)).trans (v1.trans (v2.symm.trans (congrFun h2 (1 : Fin 3))))
  · next _ hg =>
    have eg : (fun x => N3 .e (g x)) = φ1 := eq_of_heq hg.2
    injection hfg' with _ h2
    exact (congrFun h2 (1 : Fin 3)).trans (v2.trans (v1.symm.trans (congrFun eg (1 : Fin 3)).symm))
  · injection hfg' with _ h2
    exact congrFun h2 (1 : Fin 3)

theorem Mpb_not_Bridge : ¬ Mpb.Valid (Bridge PredK2) := fun h =>
  Mpb_not_K1 (Mpb.tr_BridgeK2.mp ((Mpb.valid_iff_tr _).mp h) .e .e (0 : Fin 3) (1 : Fin 3)
    ⟨(rfl : N3 .e (0 : Fin 3) = N3 .e (1 : Fin 3)), rfl⟩ Mpb_K0)

end Mpb

end PIF
