import PIBF
set_option autoImplicit false

namespace PIF
namespace Wd

/-!
# `𝔐_tw,ni`: Twin and the Slogan, without NI≈

As `𝔐_tw,c` (`MtwCF`): two worlds, the actual one `true`; entities are propositions (sets of
worlds); each type `a` is paired with its twin `sw a`, got by swapping its leftmost `e` and `t`,
which has the very same items, and each item is identified with itself in the twin type. Identity
of items does not depend on the world. Only `≈` changes: it is `TeNI`, which is identity of types
at the actual world, while at the other world no type is `≈` anything.

So this is a model of PI in which Twin and the Slogan hold, while NI≈ fails: `e ≈ e` at the actual
world but not at the other. Identity of items is the same at both worlds, so NI×, ND×, NI≡ hold,
and so do the Barcan formulas; but TNec fails (at the other world, no type is `≈` anything), and
with it Classicism. Within a type, identity is identity; so Cong, PCong, Inj≈, Recovery, Truth,
⊤≢⊥, Cantor, LL≡/≈, the Identity Identity and Booleanism hold. Disjoint, Ext≈, Int≈, PExt,
Haecceitism, LL≡-Poly, Collapse and PropExt≡ fail.
-/

def MtwNIF : Frame where
  U := univTW
  eqv := MtwCF.eqv
  teq := TeNI

/-! ## The frame is a model of PI -/

theorem MtwNI_teq_w0 : ∀ a b, MtwNIF.teq a b MtwNIF.U.w0 ↔ a = b := fun _ _ => ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

theorem MtwNI_refl : ∀ a (x : MtwNIF.U.El a) w, MtwNIF.eqv a a x x w := fun _ _ _ => ⟨Or.inl rfl, HEq.rfl⟩

/-- Identity at a type is identity. -/
theorem MtwNI_eq : ∀ a x y w, MtwNIF.eqv a a x y w → x = y := fun _ _ _ _ h => eq_of_heq h.2

/-- Identity of propositions is identity. -/
theorem MtwNI_hb : ∀ p q, MtwNIF.eqv .t .t p q MtwNIF.U.w0 → p = q := fun _ _ h => eq_of_heq h.2

theorem MtwNI_model : MtwNIF.IsModelPIm :=
  MtwNIF.model_of_equiv MtwNI_teq_w0 (fun a x => MtwNI_refl a x _)
    (fun a b x y h => MtwC_sym a b x y true h) (fun a b c x y z h1 h2 => MtwC_trans a b c x y z true h1 h2)

theorem MtwNI_LLEqv : MtwNIF.Valid LLEqv := fun ρ env => MtwNIF.LLEqv_validAt_of MtwNI_eq _ ρ env

/-- Whatever PI proves is valid. -/
theorem MtwNI_of_prov {φ : Fm Ctx.nil} (h : Prov (· = LLEqv) Ctx.nil φ) : MtwNIF.Valid φ :=
  MtwNIF.soundness MtwNI_model (fun χ (e : χ = LLEqv) => e ▸ MtwNI_LLEqv) h

/-- `□φ` is truth at both worlds. -/
theorem MtwNI_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MtwNIF.U.TEnv n) (env : MtwNIF.U.Env Γ ρ) :
    MtwNIF.Holds (boxF φ) ρ env ↔ ∀ w, MtwNIF.HoldsAt φ ρ env w := by
  refine ⟨fun h w => MtwNIF.box_all MtwNI_hb φ ρ env h w, fun h => ?_⟩
  refine (MtwNIF.holdsAt_eqv_t φ topF ρ env _).mpr ?_
  rw [MtwNIF.eval_topF]
  exact ⟨Or.inl rfl, heq_of_eq (funext fun w => propext ⟨fun _ => trivial, fun _ => h w⟩)⟩

theorem MtwNI_holdsAt_tex {n : Nat} {Γ : Ctx n} (φ : Fm Γ.text) (ρ : MtwNIF.U.TEnv n) (env : MtwNIF.U.Env Γ ρ)
    (w : Bool) : MtwNIF.HoldsAt (Tm.tex φ) ρ env w ↔ ∃ a, MtwNIF.HoldsAt φ (scons a ρ) env w := Iff.rfl

/-! ## Twin and the Slogan -/

theorem MtwNI_Twin : MtwNIF.Valid Twin := by
  intro ρ env
  show ∀ a (x : univTW.El a), ∃ b, ¬ (TeNI a b true) ∧ ∃ y : univTW.El b, (b = a ∨ b = sw a) ∧ HEq x y
  intro a x
  exact ⟨sw a, fun h => sw_ne a h.1.symm, cast (El_sw a).symm x, ⟨Or.inr rfl, (cast_heq _ _).symm⟩⟩

/-- An entity is identified only with itself, and with the same set of worlds as a proposition, of
type `t`: never with a property. -/
theorem MtwNI_Slogan : MtwNIF.Valid Slogan :=
  (MtwNIF.valid_iff_tr _).mpr <| MtwNIF.tr_Slogan.mpr fun _ _ _ h =>
    h.1.elim (fun e => nomatch e) (fun e => nomatch e)

theorem MtwNI_not_Disjoint : ¬ MtwNIF.Valid Disjoint := fun h =>
  MtwNIF.tr_Disjoint.mp ((MtwNIF.valid_iff_tr _).mp h) .e .t (fun h => nomatch h.1)
    (fun _ => True) (fun _ => True) ⟨Or.inr rfl, HEq.rfl⟩

theorem MtwNI_tr_Hae : MtwNIF.Tr Hae ↔
    ∀ a (x : MtwNIF.U.El a), MtwNIF.eqv a (.arr a .t) x (fun y => MtwNIF.eqv a a y x) MtwNIF.U.w0 := Iff.rfl

theorem MtwNI_not_Hae : ¬ MtwNIF.Valid Hae := fun h =>
  (MtwNI_tr_Hae.mp ((MtwNIF.valid_iff_tr _).mp h) .e (fun _ => True)).1.elim
    (fun e => nomatch e) (fun e => nomatch e)

/-! ## Congruence and extensionality -/

/-- Identified functions are the same function, on types that differ only by the swap, and
identified arguments are the same item; so the values are the same item, of types `c` and `c`. -/
theorem MtwNI_cong_core (a b c d : Code Empty) (f : MtwNIF.U.El a → MtwNIF.U.El c)
    (g : MtwNIF.U.El b → MtwNIF.U.El d) (x : MtwNIF.U.El a) (y : MtwNIF.U.El b) (w : Bool)
    (h1 : MtwNIF.eqv (.arr a c) (.arr b d) f g w) (h2 : MtwNIF.eqv a b x y w) :
    MtwNIF.eqv c d (f x) (g y) w := by
  obtain ⟨e1 | e1, hf⟩ := h1
  · injection e1 with eb ed
    subst eb; subst ed
    exact ⟨Or.inl rfl, heq_app rfl rfl hf h2.2⟩
  · change Code.arr b d = Code.arr (sw a) c at e1
    injection e1 with eb ed
    subst eb; subst ed
    exact ⟨Or.inl rfl, heq_app (El_sw a).symm rfl hf h2.2⟩

theorem MtwNI_Cong : MtwNIF.Valid Cong :=
  (MtwNIF.valid_iff_tr _).mpr <| MtwNIF.tr_Cong.mpr fun a b c d f g x y ⟨h1, h2⟩ =>
    MtwNI_cong_core a b c d f g x y _ h1 h2

theorem MtwNI_tr_PCong : MtwNIF.Tr PCong ↔ ∀ a c d (f : MtwNIF.U.El a → MtwNIF.U.El c)
    (g : MtwNIF.U.El a → MtwNIF.U.El d) x,
    MtwNIF.eqv (.arr a c) (.arr a d) f g MtwNIF.U.w0 → MtwNIF.eqv c d (f x) (g x) MtwNIF.U.w0 := Iff.rfl

theorem MtwNI_PCong : MtwNIF.Valid PCong :=
  (MtwNIF.valid_iff_tr _).mpr <| MtwNI_tr_PCong.mpr fun a c d f g x h =>
    MtwNI_cong_core a a c d f g x x _ h (MtwNI_refl a x _)

theorem MtwNI_WCong : MtwNIF.Valid WCong := MtwNI_of_prov (Derive.d_WCong rfl)

/-- PExt fails: the identity function on `e` and the identity function from `e` to `t` agree
argument by argument, but `e→e` and `e→t` are not twins. -/
theorem MtwNI_not_PExt : ¬ MtwNIF.Valid PExt := fun h => by
  have h0 := MtwNIF.tr_PExt.mp ((MtwNIF.valid_iff_tr _).mp h) .e .e .t (fun x : MtwNIF.U.El .e => x)
    (fun x : MtwNIF.U.El .e => (x : MtwNIF.U.El .t)) (fun _ => ⟨Or.inr rfl, HEq.rfl⟩)
  rcases h0.1 with e | e
  · exact nomatch e
  · exact nomatch e

/-- Ext≈ fails: `e` and its twin `t` have the same items, but are distinct. -/
theorem MtwNI_not_ExtT : ¬ MtwNIF.Valid ExtT := fun h => by
  have h0 := MtwNIF.tr_ExtT.mp ((MtwNIF.valid_iff_tr _).mp h) .e .t
    ⟨fun x => ⟨x, Or.inr rfl, HEq.rfl⟩, fun y => ⟨y, Or.inr rfl, HEq.rfl⟩⟩
  exact nomatch h0.1

/-- Int≈ fails: `e` and `t` necessarily have the same items. -/
theorem MtwNI_not_IntT : ¬ MtwNIF.Valid IntT := fun h => by
  have h0 := (MtwNIF.holds_tall _ _ _).mp ((MtwNIF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) .t
  have h1 := (MtwNIF.holds_imp _ _ _ _).mp h0 ((MtwNIF.holds_conj _ _ _ _).mpr
    ⟨(MtwNI_box _ _ _).mpr fun w => (MtwNIF.holdsAt_all _ _ _ _ w).mpr fun x => (MtwNIF.holdsAt_ex _ _ _ _ w).mpr
        ⟨x, (MtwNIF.holdsAt_eqv _ _ _ _ _ _ w).mpr ⟨Or.inr rfl, (cast_heq _ _).trans (cast_heq _ _).symm⟩⟩,
     (MtwNI_box _ _ _).mpr fun w => (MtwNIF.holdsAt_all _ _ _ _ w).mpr fun y => (MtwNIF.holdsAt_ex _ _ _ _ w).mpr
        ⟨y, (MtwNIF.holdsAt_eqv _ _ _ _ _ _ w).mpr ⟨Or.inr rfl, (cast_heq _ _).trans (cast_heq _ _).symm⟩⟩⟩)
  exact nomatch ((MtwNIF.holds_teq _ _ _ _).mp h1).1

/-! ## Identity of types -/

theorem MtwNI_Inj : MtwNIF.Valid Inj :=
  (MtwNIF.valid_iff_tr _).mpr <| MtwNIF.tr_Inj.mpr fun a b c d h => by
    have e : Code.arr a c = Code.arr b d := h.1
    injection e with e1 e2
    exact ⟨⟨e1, rfl⟩, ⟨e2, rfl⟩⟩

theorem MtwNI_tr_Recovery : MtwNIF.Tr Recovery ↔ ∀ a b c d, MtwNIF.teq (.arr a c) (.arr b d) MtwNIF.U.w0 ∧
    MtwNIF.teq a b MtwNIF.U.w0 → MtwNIF.teq c d MtwNIF.U.w0 := Iff.rfl

theorem MtwNI_Recovery : MtwNIF.Valid Recovery :=
  (MtwNIF.valid_iff_tr _).mpr <| MtwNI_tr_Recovery.mpr fun a b c d ⟨h, _⟩ => by
    have e : Code.arr a c = Code.arr b d := h.1
    exact ⟨(Code.arr.inj e).2, rfl⟩

/-- LL≡-Poly fails, for `λγ.λz:γ.(γ ≈ e)`: an entity is identified with itself as a proposition. -/
theorem MtwNI_tr_LLPolyE : MtwNIF.Tr (LLPoly PredE) ↔ ∀ a b (x : MtwNIF.U.El a) (y : MtwNIF.U.El b),
    MtwNIF.eqv a b x y MtwNIF.U.w0 → MtwNIF.teq a .e MtwNIF.U.w0 → MtwNIF.teq b .e MtwNIF.U.w0 := Iff.rfl

theorem MtwNI_not_LLPoly : ¬ MtwNIF.Valid (LLPoly PredE) := fun h =>
  nomatch (MtwNI_tr_LLPolyE.mp ((MtwNIF.valid_iff_tr _).mp h) .e .t (fun _ => True) (fun _ => True)
    ⟨Or.inr rfl, HEq.rfl⟩ ⟨rfl, rfl⟩).1

/-! ## What PI proves -/

theorem MtwNI_Truth : MtwNIF.Valid Truth := MtwNI_of_prov (Derive.d_Truth rfl)
theorem MtwNI_TopBot : MtwNIF.Valid TopBot := MtwNI_of_prov (Derive.d_TopBot rfl)
theorem MtwNI_Cantor : MtwNIF.Valid Cantor := MtwNI_of_prov (Derive.d_Cantor rfl)
theorem MtwNI_Bridge (P : Tm Ctx.nil (.pi (.arr (.var fz) .t))) : MtwNIF.Valid (Bridge P) :=
  MtwNI_of_prov (d_Bridge P rfl)

theorem MtwNI_Choice : MtwNIF.Valid Choice := MtwNIF.Choice_valid

theorem MtwNI_Bool : ∀ φ, BoolSch φ → MtwNIF.Valid φ := MtwNIF.bool_valid fun p => MtwNI_refl .t p _

/-- The Identity Identity: `x ≡ y` and `∀F (F x → F y)` are, at each world, the proposition that
`x` is `y`. -/
theorem MtwNI_tr_IdId : MtwNIF.Tr IdId ↔ ∀ a (x y : MtwNIF.U.El a), MtwNIF.eqv .t .t (MtwNIF.eqv a a x y)
    (fun w => ∀ G : MtwNIF.U.El a → Bool → Prop, G x w → G y w) MtwNIF.U.w0 := Iff.rfl

theorem MtwNI_IdId : MtwNIF.Valid IdId :=
  (MtwNIF.valid_iff_tr _).mpr <| MtwNI_tr_IdId.mpr fun a x y => by
    have e : MtwNIF.eqv a a x y = fun w => ∀ G : MtwNIF.U.El a → Bool → Prop, G x w → G y w := by
      funext w
      refine propext ⟨fun h => ?_, fun h => ?_⟩
      · have exy : x = y := MtwNI_eq a x y w h
        subst exy
        exact fun _ hG => hG
      · have eyx : y = x := h (fun z _ => z = x) rfl
        subst eyx
        exact MtwNI_refl a y w
    exact ⟨Or.inl rfl, heq_of_eq e⟩

/-! ## Modal principles -/

theorem MtwNI_TAx : MtwNIF.Valid TAx := by
  intro ρ env
  refine (MtwNIF.holds_all _ _ _ _).mpr fun p => (MtwNIF.holds_imp _ _ _ _).mpr fun h => ?_
  exact (MtwNI_box _ _ _).mp h MtwNIF.U.w0

theorem MtwNI_not_Collapse : ¬ MtwNIF.Valid Collapse := fun h => by
  have h0 := (MtwNIF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (fun w => w = true)
  have hb := (MtwNIF.holds_imp _ _ _ _).mp h0 (show true = true from rfl)
  exact Bool.false_ne_true ((MtwNI_box _ _ _).mp hb false)

theorem MtwNI_not_PropExt : ¬ MtwNIF.Valid PropExt := fun h =>
  MtwNI_not_Collapse (MtwNIF.soundness MtwNI_model (Ax := (· = PropExt)) (fun χ (e : χ = PropExt) => e ▸ h)
    (d_Collapse_of_PropExt rfl))

/-- Identity of items is the same at both worlds. -/
theorem MtwNI_NIX : MtwNIF.Valid NIX :=
  MtwNIF.NIX_of (fun p => MtwNI_refl .t p _) fun _ _ _ _ h _ => h

theorem MtwNI_NDX : MtwNIF.Valid NDX :=
  MtwNIF.NDX_of (fun p => MtwNI_refl .t p _) fun _ _ _ _ h _ => h

theorem MtwNI_NIEqv : MtwNIF.Valid NIEqv :=
  MtwNIF.soundness MtwNI_model (Ax := (· = NIX)) (fun χ (e : χ = NIX) => e ▸ MtwNI_NIX) (d_NIEqv_of_NIX rfl)

/-- NI≈ fails: `e ≈ e` at the actual world, but not at the other. -/
theorem MtwNI_not_NITeq : ¬ MtwNIF.Valid NITeq := fun hv => by
  have h0 := MtwNIF.tr_NITeq.mp ((MtwNIF.valid_iff_tr _).mp hv) .e .e ⟨rfl, rfl⟩
  have e : TeNI .e .e = MtwNIF.eval (topF : Fm Ctx.nil) (fun i => i.elim0) () := MtwNI_hb _ _ h0
  have e2 := e.trans (MtwNIF.eval_topF (Γ := Ctx.nil) _ _)
  exact Bool.false_ne_true (cast (congrFun e2 false).symm trivial).2

theorem MtwNI_NDTeq : MtwNIF.Valid NDTeq :=
  (MtwNIF.valid_iff_tr _).mpr <| MtwNIF.tr_NDTeq.mpr fun a b hn => by
    have e : (fun w => ¬ MtwNIF.teq a b w) = MtwNIF.eval (topF : Fm Ctx.nil) (fun i => i.elim0) () := by
      refine Eq.trans ?_ (MtwNIF.eval_topF (Γ := Ctx.nil) _ _).symm
      funext w
      exact propext ⟨fun _ => trivial, fun _ hw => hn ⟨hw.1, rfl⟩⟩
    exact ⟨Or.inl rfl, heq_of_eq e⟩

/-- Classicism fails, since PI with Classicism proves NI≈. -/
theorem MtwNI_not_Class : ¬ ∀ χ, ClassSch χ → MtwNIF.Valid χ := fun h =>
  MtwNI_not_NITeq (MtwNIF.soundness MtwNI_model (Ax := ClassSch) h (d_NITeq_of_Class fun _ hc => hc))

/-! ## The Barcan formulas -/

theorem MtwNI_TBF : ∀ χ, TBFSch χ → MtwNIF.Valid χ :=
  MtwNIF.TBF_of fun p q => ⟨MtwNI_hb p q, fun e => by subst e; exact MtwNI_refl .t p _⟩

theorem MtwNI_TCBF : ∀ χ, TCBFSch χ → MtwNIF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MtwNIF.holds_imp _ _ _ _).mpr fun h => ?_
  exact (MtwNIF.holds_tall _ _ _).mpr fun a => (MtwNI_box _ _ _).mpr fun w =>
    (MtwNIF.holdsAt_tall _ _ _ w).mp ((MtwNI_box _ _ _).mp h w) a

/-- TNec fails: at the other world, no type is `≈` anything. -/
theorem MtwNI_not_TNec : ¬ MtwNIF.Valid TNec := fun h => by
  have h0 := (MtwNI_box _ _ _).mp ((MtwNIF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) false
  obtain ⟨_, hb⟩ := (MtwNI_holdsAt_tex _ _ _ false).mp h0
  exact Bool.false_ne_true ((MtwNIF.holdsAt_teq _ _ _ _ false).mp hb).2

theorem MtwNI_BF : MtwNIF.Valid BF := by
  intro ρ env
  refine (MtwNIF.holds_tall _ _ _).mpr fun a => (MtwNIF.holds_all _ _ _ _).mpr fun G => ?_
  refine (MtwNIF.holds_imp _ _ _ _).mpr fun h => (MtwNI_box _ _ _).mpr fun w => ?_
  exact (MtwNIF.holdsAt_all _ _ _ _ w).mpr fun x => (MtwNI_box _ _ _).mp ((MtwNIF.holds_all _ _ _ _).mp h x) w

theorem MtwNI_CBF : MtwNIF.Valid CBF := by
  intro ρ env
  refine (MtwNIF.holds_tall _ _ _).mpr fun a => (MtwNIF.holds_all _ _ _ _).mpr fun G => ?_
  refine (MtwNIF.holds_imp _ _ _ _).mpr fun h => (MtwNIF.holds_all _ _ _ _).mpr fun x =>
    (MtwNI_box _ _ _).mpr fun w => ?_
  exact (MtwNIF.holdsAt_all _ _ _ _ w).mp ((MtwNI_box _ _ _).mp h w) x

theorem MtwNI_Nec : MtwNIF.Valid Nec := by
  intro ρ env
  refine (MtwNIF.holds_tall _ _ _).mpr fun a => (MtwNIF.holds_all _ _ _ _).mpr fun x =>
    (MtwNI_box _ _ _).mpr fun w => ?_
  exact (MtwNIF.holdsAt_ex _ _ _ _ w).mpr ⟨x, (MtwNIF.holdsAt_eqv _ _ _ _ _ _ w).mpr
    ⟨Or.inl rfl, (cast_heq _ _).trans (cast_heq _ _).symm⟩⟩

end Wd
end PIF
