import PIBF
set_option autoImplicit false

/-!
# `𝔐_r2`: Recovery and Slogan without Inj≈, in PIᶜ

The model `𝔐_hae,r` of `PIHaeQs.lean` without haecceities. `E = 1`, with one further base type `D`,
also with one item. `≈` is sameness of type once `D` is replaced by `e` in every argument position:
so `D→t ≈ e→t`, while `D` and `e` differ. Items are identified just in case they agree once `D` is
replaced by `e` everywhere in their types: so the item of `D` is identified with the entity.
-/

namespace PIF

section Mr2
attribute [local instance] Classical.propDecidable

def Mr2F : Frame where
  U := univHR
  eqv := fun a b x y => ownRR a x = ownRR b y
  teq := fun a b => TnR a = TnR b

theorem Mr2_ownRR_iff {c c' : CHR} (x : univHR.El c) (x' : univHR.El c') :
    ownRR c x = ownRR c' x' ↔ TrR c = TrR c' ∧ HEq x x' := by
  constructor
  · intro h
    have h1 := Sigma.mk.inj h
    exact ⟨h1.1, (cast_heq _ _).symm.trans (h1.2.trans (cast_heq _ _))⟩
  · rintro ⟨h1, h2⟩
    exact ownRR_congr h1 h2

theorem Mr2_El {a b : CHR} (h : TrR a = TrR b) : univHR.El a = univHR.El b :=
  (El_TrR a).symm.trans ((congrArg univHR.El h).trans (El_TrR b))

theorem Mr2_heq_app {A A' C C' : Type} (hA : A = A') (hC : C = C') {f : A → C} {f' : A' → C'} {x : A} {x' : A'}
    (hf : HEq f f') (hx : HEq x x') : HEq (f x) (f' x') := by
  subst hA; subst hC
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hx
  exact HEq.rfl

theorem Mr2_heq_funext {A C C' : Type} (hC : C = C') {f : A → C} {g : A → C'} (h : ∀ x, HEq (f x) (g x)) :
    HEq f g := by
  subst hC
  exact heq_of_eq (funext fun x => eq_of_heq (h x))

def Mr2I : Invariance Mr2F where
  Adm := fun a a' R => TnR a = TnR a' ∧ ∀ x y, R x y ↔ HEq x y
  refl := fun _ => ⟨rfl, fun _ _ => ⟨fun h => h ▸ HEq.rfl, eq_of_heq⟩⟩
  arrow := by
    rintro a a' c c' R S ⟨h1, hR⟩ ⟨h2, hS⟩
    refine ⟨?_, fun f f' => fun_heq_iff (hrEl h1) (hrEl h2) hR hS f f'⟩
    show Code.arr (TrR a) (TnR c) = Code.arr (TrR a') (TnR c')
    rw [TrR_of_TnR h1, h2]
  total := by
    rintro a a' R ⟨h, hR⟩ u
    exact ⟨cast (hrEl h) u, (hR _ _).mpr (cast_heq _ _).symm⟩
  onto := by
    rintro a a' R ⟨h, hR⟩ u
    exact ⟨cast (hrEl h).symm u, (hR _ _).mpr (cast_heq _ _)⟩
  teq := by
    rintro a a' b b' R S ⟨h1, -⟩ ⟨h2, -⟩
    show TnR a = TnR b ↔ TnR a' = TnR b'
    rw [h1, h2]
  eqv := by
    rintro a a' b b' R S ⟨h1, hR⟩ ⟨h2, hS⟩ u u' v v' hu hv
    show ownRR a u = ownRR b v ↔ ownRR a' u' = ownRR b' v'
    rw [ownRR_congr (TrR_of_TnR h1) ((hR u u').mp hu), ownRR_congr (TrR_of_TnR h2) ((hS v v').mp hv)]

abbrev Mr2 : Frame := Mr2F

theorem Mr2_model : Mr2.IsModelPIm :=
  Frame.isModelPIm_of_invariance Mr2F Mr2I (fun _ _ h => ⟨fun x y => HEq x y, h, fun _ _ => Iff.rfl⟩)
    ((Mr2F.valid_iff_tr _).mpr (Mr2F.tr_RefEqv.mpr fun _ _ => rfl))
    ((Mr2F.valid_iff_tr _).mpr (Mr2F.tr_SymEqv.mpr fun _ _ _ _ h => h.symm))
    ((Mr2F.valid_iff_tr _).mpr (Mr2F.tr_TransEqv.mpr fun _ _ _ _ _ _ ⟨h1, h2⟩ => h1.trans h2))
    ((Mr2F.valid_iff_tr _).mpr (Mr2F.tr_RefTeq.mpr fun _ => rfl))

theorem Mr2_LLEqv : Mr2.Valid LLEqv :=
  (Mr2.valid_iff_tr _).mpr <| Mr2.tr_LLEqv.mpr fun _ _ _ h _ hP => ownRR_inj h ▸ hP

theorem Mr2_Class : ∀ χ, ClassSch χ → Mr2.Valid χ := Mr2.Class_valid Mr2_model Mr2_LLEqv

theorem Mr2_Recovery : Mr2.Valid Recovery :=
  (Mr2.valid_iff_tr _).mpr <| Mr2.tr_Recovery.mpr fun _ _ _ _ ⟨h, _⟩ => by
    injection h

theorem Mr2_not_Inj : ¬ Mr2.Valid Inj := fun h => by
  have := Mr2.tr_Inj.mp ((Mr2.valid_iff_tr _).mp h) (.base ()) .e .t .t rfl
  cases this.1

/-- An entity is never identified with a property: the type of the one is `e` once `D` is replaced
by `e`, while that of the other is an arrow. -/
theorem Mr2_Slogan : Mr2.Valid Slogan :=
  (Mr2.valid_iff_tr _).mpr <| Mr2.tr_Slogan.mpr fun x b y h => by
    have := ((Mr2_ownRR_iff (c := .e) (c' := .arr b .t) x y).mp h).1
    cases this

theorem Mr2_Cong : Mr2.Valid Cong :=
  (Mr2.valid_iff_tr _).mpr <| Mr2.tr_Cong.mpr fun a b c d f g x y ⟨h1, h2⟩ => by
    obtain ⟨e1, hf⟩ := (Mr2_ownRR_iff (c := .arr a c) (c' := .arr b d) f g).mp h1
    obtain ⟨_, hx⟩ := (Mr2_ownRR_iff (c := a) (c' := b) x y).mp h2
    injection e1 with ea ec
    exact ownRR_congr ec (Mr2_heq_app (Mr2_El ea) (Mr2_El ec) hf hx)

theorem Mr2_WCong : Mr2.Valid WCong :=
  (Mr2.valid_iff_tr _).mpr <| Mr2.tr_WCong.mpr fun a b c d f g x y ⟨_, h⟩ =>
    Mr2.tr_Cong.mp ((Mr2.valid_iff_tr _).mp Mr2_Cong) a b c d f g x y h

theorem Mr2_PCong : Mr2.Valid PCong :=
  (Mr2.valid_iff_tr _).mpr <| Mr2.tr_PCong.mpr fun a c d f g x h =>
    Mr2.tr_Cong.mp ((Mr2.valid_iff_tr _).mp Mr2_Cong) a a c d f g x x ⟨h, rfl⟩

theorem Mr2_PExt : Mr2.Valid PExt :=
  (Mr2.valid_iff_tr _).mpr <| Mr2.tr_PExt.mpr fun a c d f g h => by
    obtain ⟨x0⟩ := Univ.El_nonempty (U := univHR) a
    have hc : TrR c = TrR d := ((Mr2_ownRR_iff (c := c) (c' := d) (f x0) (g x0)).mp (h x0)).1
    refine ownRR_congr (show Code.arr (TrR a) (TrR c) = Code.arr (TrR a) (TrR d) by rw [hc]) ?_
    exact Mr2_heq_funext (Mr2_El hc) fun x => ((Mr2_ownRR_iff (c := c) (c' := d) (f x) (g x)).mp (h x)).2

/-- The item of `D` and the entity are identified, although `D` and `e` are not `≈`. -/
theorem Mr2_not_Disjoint : ¬ Mr2.Valid Disjoint := fun h =>
  Mr2.tr_Disjoint.mp ((Mr2.valid_iff_tr _).mp h) (.base ()) .e (fun e => by cases e) () ()
    (ownRR_congr (c := .base ()) (c' := .e) rfl HEq.rfl)

/-- `e` and `D` are coextensive, but not `≈`. -/
theorem Mr2_not_ExtT : ¬ Mr2.Valid ExtT := fun h => by
  have := Mr2.tr_ExtT.mp ((Mr2.valid_iff_tr _).mp h) .e (.base ())
    ⟨fun x => ⟨x, ownRR_congr (c := .e) (c' := .base ()) rfl HEq.rfl⟩,
     fun y => ⟨y, ownRR_congr (c := .e) (c' := .base ()) rfl HEq.rfl⟩⟩
  cases this

theorem Mr2_eqv_t (p q : Prop) : Mr2.eqv .t .t p q ↔ p = q :=
  ⟨fun h => ownRR_inj h, fun h => by subst h; exact rfl⟩

theorem Mr2_not_IntT : ¬ Mr2.Valid IntT := fun h =>
  Mr2_not_ExtT ((Mr2.IntT_iff_ExtT Mr2_eqv_t).mp h)

/-- LL≡-Poly fails, for the predicate `λγ.λz.(γ ≈ e)`: the entity is identified with the item of
`D`, but `e ≈ e` while not `D ≈ e`. -/
theorem Mr2_not_LLPoly : ¬ Mr2.Valid (LLPoly PredE) := fun h => by
  have := Mr2.tr_LLPolyE.mp ((Mr2.valid_iff_tr _).mp h) .e (.base ()) () ()
    (ownRR_congr (c := .e) (c' := .base ()) rfl HEq.rfl) rfl
  cases this

theorem Mr2_Truth : Mr2.Valid Truth :=
  (Mr2.valid_iff_tr _).mpr <| Mr2.tr_Truth.mpr fun _ _ h hp => cast (ownRR_inj h) hp

theorem Mr2_TopBot : Mr2.Valid TopBot :=
  (Mr2.valid_iff_tr _).mpr <| Mr2.tr_TopBot.mpr fun h => by
    have e : (¬ ∀ p : Prop, p) = (∀ p : Prop, p) := ownRR_inj h
    exact (cast e (fun hall => hall False)) False

theorem Mr2_TrR_ne_pred (a : CHR) : TrR (.arr a .t) ≠ TrR a := fun h => by
  have := congrArg csz h
  rw [csz_TrR, csz_TrR] at this
  change csz a + csz (Code.t : CHR) + 1 = csz a at this
  omega

theorem Mr2_Cantor : Mr2.Valid Cantor :=
  (Mr2.valid_iff_tr _).mpr <| Mr2.tr_Cantor.mpr fun a => ⟨fun _ => True, fun y h =>
    Mr2_TrR_ne_pred a ((Mr2_ownRR_iff (c := .arr a .t) (c' := a) _ y).mp h).1⟩

/-- Without haecceities, nothing is identified with its haecceity. -/
theorem Mr2_not_Hae : ¬ Mr2.Valid Hae := fun h => by
  have := Mr2.tr_Hae.mp ((Mr2.valid_iff_tr _).mp h) .e ()
  exact Mr2_TrR_ne_pred .e ((Mr2_ownRR_iff (c := .e) (c' := .arr .e .t) _ _).mp this).1.symm

/-- Every truth value is identified only with truth values. -/
theorem Mr2_not_Twin : ¬ Mr2.Valid Twin := fun h => by
  obtain ⟨b, hb, y, hy⟩ := Mr2.tr_Twin.mp ((Mr2.valid_iff_tr _).mp h) .t True
  have e := TrR_eq_t b ((Mr2_ownRR_iff (c := .t) (c' := b) _ y).mp hy).1.symm
  subst e
  exact hb rfl

theorem Mr2_PropExt : Mr2.Valid PropExt := Mr2.PropExt_valid Mr2_model

theorem Mr2_Choice : Mr2.Valid Choice := Mr2.Choice_valid

theorem Mr2_Collapse : Mr2.Valid Collapse := Mr2.Collapse_valid Mr2_model

/-! ### Modal principles, by soundness from PropExt, Collapse, Truth, and LL≡ -/

theorem Mr2_of_prov {S : Fm Ctx.nil → Prop} (hS : ∀ ψ, S ψ → Mr2.Valid ψ) {φ : Fm Ctx.nil}
    (h : Prov S Ctx.nil φ) : Mr2.Valid φ :=
  Mr2.soundness Mr2_model hS h

theorem Mr2_TAx : Mr2.Valid TAx :=
  Mr2_of_prov (S := (· = Truth)) (fun _ h => h ▸ Mr2_Truth) (d_TAx_of_Truth rfl)

theorem Mr2_NIEqv : Mr2.Valid NIEqv :=
  Mr2_of_prov (S := (· = Collapse)) (fun _ h => h ▸ Mr2_Collapse) (d_NIEqv_of_Collapse rfl)

theorem Mr2_NITeq : Mr2.Valid NITeq :=
  Mr2_of_prov (S := (· = Collapse)) (fun _ h => h ▸ Mr2_Collapse) (d_NITeq_of_Collapse rfl)

theorem Mr2_NDTeq : Mr2.Valid NDTeq :=
  Mr2_of_prov (S := (· = Collapse)) (fun _ h => h ▸ Mr2_Collapse) (d_NDTeq_of_Collapse rfl)

theorem Mr2_NIX : Mr2.Valid NIX :=
  Mr2_of_prov (S := (· = Collapse)) (fun _ h => h ▸ Mr2_Collapse) (d_NIX_of_Collapse rfl)

theorem Mr2_NDX : Mr2.Valid NDX :=
  Mr2_of_prov (S := (· = Collapse)) (fun _ h => h ▸ Mr2_Collapse) (d_NDX_of_Collapse rfl)

theorem Mr2_TNec : Mr2.Valid TNec :=
  Mr2_of_prov (S := (· = Collapse)) (fun _ h => h ▸ Mr2_Collapse) (d_TNec rfl)

theorem Mr2_Nec : Mr2.Valid Nec :=
  Mr2_of_prov (S := (· = Collapse)) (fun _ h => h ▸ Mr2_Collapse) (d_Nec_of_Collapse rfl)

theorem Mr2_Bool : ∀ φ, BoolSch φ → Mr2.Valid φ := fun φ hφ =>
  Mr2_of_prov (S := (· = PropExt)) (fun _ h => h ▸ Mr2_PropExt) (d_Bool_of_PropExt (S := (· = PropExt)) rfl φ hφ)

theorem Mr2_TBF : ∀ χ, TBFSch χ → Mr2.Valid χ := fun χ hχ =>
  Mr2_of_prov (S := (· = PropExt)) (fun _ h => h ▸ Mr2_PropExt) (d_TBF_of_PropExt (S := (· = PropExt)) rfl χ hχ)

theorem Mr2_TCBF : ∀ χ, TCBFSch χ → Mr2.Valid χ := fun χ hχ =>
  Mr2_of_prov (S := (· = PropExt)) (fun _ h => h ▸ Mr2_PropExt) (d_TCBF_of_PropExt (S := (· = PropExt)) rfl χ hχ)

theorem Mr2_IdId : Mr2.Valid IdId :=
  Mr2_of_prov (S := fun ψ => ψ = PropExt ∨ ψ = LLEqv)
    (fun _ h => h.elim (fun e => e ▸ Mr2_PropExt) (fun e => e ▸ Mr2_LLEqv))
    (d_IdId_of_PropExt (Or.inl rfl) (Or.inr rfl))

theorem Mr2_BF : Mr2.Valid BF :=
  Mr2_of_prov (S := fun ψ => ψ = Collapse ∨ ψ = TAx)
    (fun _ h => h.elim (fun e => e ▸ Mr2_Collapse) (fun e => e ▸ Mr2_TAx))
    (d_BF_of_Collapse (Or.inl rfl) (Or.inr rfl))

theorem Mr2_CBF : Mr2.Valid CBF :=
  Mr2_of_prov (S := fun ψ => ψ = Collapse ∨ ψ = TAx)
    (fun _ h => h.elim (fun e => e ▸ Mr2_Collapse) (fun e => e ▸ Mr2_TAx))
    (d_CBF_of_Collapse (Or.inl rfl) (Or.inr rfl))

end Mr2

end PIF
