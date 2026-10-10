import PIBF

/-!
# `𝔐_tt,T`: `⊤ ≢ ⊥` and T, without Truth

Two worlds, the actual one `true`. The proposition true only at the actual world is identified with
the proposition true only at the other world; otherwise identity is identity, and the same at both
worlds; `≈` is identity of types. So `⊤` is identified only with itself, and `□φ` (that is,
`φ ≡ ⊤`) is true just when `φ` is true at both worlds. Hence T holds, while Truth fails: the two
identified propositions differ in truth value at the actual world. Since identity of items and of
types is rigid, the modal principles about identity and the Barcan formulas all hold.
-/
set_option autoImplicit false

namespace PIF
namespace Wd

/-! ## The model -/

/-- The two propositions true at exactly one world. -/
def StT : (c : Code Empty) → (univW Bool true).El c → Prop
  | .t, x => x = (fun w => w = true) ∨ x = (fun w => w = false)
  | _, _ => False

def MttTF : Frame where
  U := univW Bool true
  eqv := fun a b x y _ => a = b ∧ (HEq x y ∨ (StT a x ∧ StT b y))
  teq := fun a b _ => a = b

theorem MttT_model : MttTF.IsModelPIm :=
  MttTF.model_of_equiv (fun _ _ => Iff.rfl) (fun _ _ => ⟨rfl, Or.inl HEq.rfl⟩)
    (fun _ _ _ _ h => ⟨h.1.symm, h.2.elim (fun e => Or.inl e.symm) (fun ⟨p, q⟩ => Or.inr ⟨q, p⟩)⟩)
    (fun a b c x y z h1 h2 => by
      obtain ⟨hab, e1⟩ := h1
      obtain ⟨hbc, e2⟩ := h2
      subst hab; subst hbc
      refine ⟨rfl, ?_⟩
      rcases e1 with e1 | ⟨s1, s2⟩ <;> rcases e2 with e2 | ⟨s3, s4⟩
      · exact Or.inl (e1.trans e2)
      · exact Or.inr ⟨eq_of_heq e1 ▸ s3, s4⟩
      · exact Or.inr ⟨s1, eq_of_heq e2 ▸ s2⟩
      · exact Or.inr ⟨s1, s4⟩)

/-- `⊤` is not one of the two identified propositions. -/
theorem MttT_not_St_top : ¬ StT .t (fun _ => True) := by
  intro h
  rcases h with e | e
  · exact Bool.noConfusion (cast (congrFun e false) trivial : false = true)
  · exact Bool.noConfusion (cast (congrFun e true) trivial : true = false)

/-- Only `⊤` is identified with `⊤`. -/
theorem MttT_top_iff (p : MttTF.U.El .t) :
    MttTF.eqv .t .t p (fun _ => True) MttTF.U.w0 ↔ p = fun _ => True :=
  ⟨fun h => h.2.elim eq_of_heq (fun h' => absurd h'.2 MttT_not_St_top),
   fun h => by subst h; exact ⟨rfl, Or.inl HEq.rfl⟩⟩

theorem MttT_eqv_top {n : Nat} {Γ : Ctx n} (ρ : MttTF.U.TEnv n) (env : MttTF.U.Env Γ ρ) (p : MttTF.U.El .t) :
    MttTF.eqv .t .t p (MttTF.eval (topF : Fm Γ) ρ env) MttTF.U.w0 ↔ p = fun _ => True := by
  rw [MttTF.eval_topF]
  exact MttT_top_iff p

/-- `□φ` is true just when `φ` is true at both worlds. -/
theorem MttT_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : MttTF.U.TEnv n) (env : MttTF.U.Env Γ ρ) :
    MttTF.Holds (boxF φ) ρ env ↔ ∀ w, MttTF.HoldsAt φ ρ env w := by
  refine (MttTF.holdsAt_eqv_t φ topF ρ env _).trans ?_
  refine (MttT_eqv_top ρ env _).trans ⟨fun e w => cast (congrFun e w).symm trivial, fun h => ?_⟩
  exact funext fun w => propext ⟨fun _ => trivial, fun _ => h w⟩

theorem MttT_holdsAt_tex {n : Nat} {Γ : Ctx n} (φ : Fm Γ.text) (ρ : MttTF.U.TEnv n) (env : MttTF.U.Env Γ ρ) (w : Bool) :
    MttTF.HoldsAt (Tm.tex φ) ρ env w ↔ ∃ a, MttTF.HoldsAt φ (scons a ρ) env w := Iff.rfl

/-! ## T and Truth -/

theorem MttT_TAx : MttTF.Valid TAx := by
  intro ρ env
  refine (MttTF.holds_all _ _ _ _).mpr fun p => (MttTF.holds_imp _ _ _ _).mpr fun hb => ?_
  exact (MttT_box _ _ _).mp hb MttTF.U.w0

/-- The proposition true only at the actual world is identified with the one true only at the
other world: the first is true, the second false. -/
theorem MttT_not_Truth : ¬ MttTF.Valid Truth := fun h => by
  have h0 := (MttTF.holds_all _ _ _ _).mp ((MttTF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ())
    (fun w => w = true)) (fun w => w = false)
  have h1 := (MttTF.holds_imp _ _ _ _).mp h0
    ((MttTF.holdsAt_eqv_t _ _ _ _ _).mpr ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩)
  exact Bool.noConfusion ((MttTF.holds_imp _ _ _ _).mp h1 (rfl : true = true) : true = false)

theorem MttT_TopBot : MttTF.Valid TopBot := by
  intro ρ env
  refine (MttTF.holds_neg _ _ _).mpr fun h => ?_
  have h' := ((MttTF.holdsAt_eqv_t _ _ _ _ _).mp h).2
  rw [MttTF.eval_topF, MttTF.eval_botF] at h'
  rcases h' with e | ⟨s, _⟩
  · exact cast (congrFun (eq_of_heq e) true) trivial
  · exact MttT_not_St_top s

theorem MttT_Bool : ∀ φ, BoolSch φ → MttTF.Valid φ := MttTF.bool_valid fun _ => ⟨rfl, Or.inl HEq.rfl⟩

/-! ## Necessity of identity and distinctness -/

theorem MttT_NIX : MttTF.Valid NIX :=
  MttTF.NIX_of (fun _ => ⟨rfl, Or.inl HEq.rfl⟩) fun _ _ _ _ h _ => h
theorem MttT_NDX : MttTF.Valid NDX :=
  MttTF.NDX_of (fun _ => ⟨rfl, Or.inl HEq.rfl⟩) fun _ _ _ _ h _ => h

theorem MttT_NIEqv : MttTF.Valid NIEqv :=
  (MttTF.valid_iff_tr _).mpr <| MttTF.tr_NIEqv.mpr fun _ _ _ h =>
    (MttT_eqv_top _ _ _).mpr (funext fun _ => propext ⟨fun _ => trivial, fun _ => h⟩)

theorem MttT_NITeq : MttTF.Valid NITeq :=
  (MttTF.valid_iff_tr _).mpr <| MttTF.tr_NITeq.mpr fun _ _ h =>
    (MttT_eqv_top _ _ _).mpr (funext fun _ => propext ⟨fun _ => trivial, fun _ => h⟩)

theorem MttT_NDTeq : MttTF.Valid NDTeq := MttTF.NDTeq_of (fun _ => ⟨rfl, Or.inl HEq.rfl⟩) fun _ _ _ => Iff.rfl

/-! ## Identity across types, and identity of types -/

theorem MttT_Disjoint : MttTF.Valid Disjoint :=
  (MttTF.valid_iff_tr _).mpr <| MttTF.tr_Disjoint.mpr fun _ _ hn _ _ h => hn h.1

theorem MttT_Slogan : MttTF.Valid Slogan :=
  (MttTF.valid_iff_tr _).mpr <| MttTF.tr_Slogan.mpr fun _ _ _ h => nomatch h.1

theorem MttT_tr_Cantor : MttTF.Tr Cantor ↔ ∀ a, ∃ G : MttTF.U.El a → Bool → Prop,
    ∀ y : MttTF.U.El a, ¬ MttTF.eqv (.arr a .t) a G y MttTF.U.w0 := Iff.rfl

theorem MttT_Cantor : MttTF.Valid Cantor :=
  (MttTF.valid_iff_tr _).mpr <| MttT_tr_Cantor.mpr fun a =>
    ⟨fun _ _ => True, fun _ h => Code.arr_ne_left a .t h.1⟩

theorem MttT_Inj : MttTF.Valid Inj := MttTF.Inj_of fun _ _ _ => Iff.rfl

theorem MttT_tr_Recovery : MttTF.Tr Recovery ↔ ∀ a b c d, MttTF.teq (.arr a c) (.arr b d) MttTF.U.w0 ∧
    MttTF.teq a b MttTF.U.w0 → MttTF.teq c d MttTF.U.w0 := Iff.rfl

theorem MttT_Recovery : MttTF.Valid Recovery :=
  (MttTF.valid_iff_tr _).mpr <| MttT_tr_Recovery.mpr fun a b c d ⟨h, _⟩ => by
    have h' : Code.arr a c = Code.arr b d := h
    exact (Code.arr.inj h').2

theorem MttT_ExtT : MttTF.Valid ExtT :=
  (MttTF.valid_iff_tr _).mpr <| MttTF.tr_ExtT.mpr fun a _ ⟨h, _⟩ => by
    have x0 := Classical.choice (Univ.El_nonempty (U := MttTF.U) a)
    obtain ⟨_, hy⟩ := h x0
    exact hy.1

theorem MttT_IntT : MttTF.Valid IntT := by
  intro ρ env
  refine (MttTF.holds_tall _ _ _).mpr fun a => (MttTF.holds_tall _ _ _).mpr fun b => ?_
  refine (MttTF.holds_imp _ _ _ _).mpr fun h => (MttTF.holds_teq _ _ _ _).mpr ?_
  have hs := (MttT_box _ _ _).mp ((MttTF.holds_conj _ _ _ _).mp h).1 MttTF.U.w0
  have x0 := Classical.choice (Univ.El_nonempty (U := MttTF.U) a)
  obtain ⟨_, hy⟩ := (MttTF.holds_ex _ _ _ _).mp ((MttTF.holds_all _ _ _ _).mp hs x0)
  exact ((MttTF.holds_eqv _ _ _ _ _ _).mp hy).1

/-! ## The Barcan formulas, and Necessitism -/

theorem MttT_TBF : ∀ χ, TBFSch χ → MttTF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MttTF.holds_imp _ _ _ _).mpr fun h => ?_
  exact (MttT_box _ _ _).mpr fun w => (MttTF.holdsAt_tall _ _ _ w).mpr fun a =>
    (MttT_box _ _ _).mp ((MttTF.holds_tall _ _ _).mp h a) w

theorem MttT_TCBF : ∀ χ, TCBFSch χ → MttTF.Valid χ := by
  rintro _ ⟨φ, rfl⟩ ρ env
  refine (MttTF.holds_imp _ _ _ _).mpr fun h => ?_
  exact (MttTF.holds_tall _ _ _).mpr fun a => (MttT_box _ _ _).mpr fun w =>
    (MttTF.holdsAt_tall _ _ _ w).mp ((MttT_box _ _ _).mp h w) a

theorem MttT_TNec : MttTF.Valid TNec := by
  intro ρ env
  refine (MttTF.holds_tall _ _ _).mpr fun a => (MttT_box _ _ _).mpr fun w => ?_
  exact (MttT_holdsAt_tex _ _ _ w).mpr ⟨a, (MttTF.holdsAt_teq (Γ := Ctx.nil.text.text) tv1 tv0 _ _ w).mpr rfl⟩

theorem MttT_BF : MttTF.Valid BF := by
  intro ρ env
  refine (MttTF.holds_tall _ _ _).mpr fun a => (MttTF.holds_all _ _ _ _).mpr fun G => ?_
  refine (MttTF.holds_imp _ _ _ _).mpr fun h => (MttT_box _ _ _).mpr fun w => ?_
  exact (MttTF.holdsAt_all _ _ _ _ w).mpr fun x => (MttT_box _ _ _).mp ((MttTF.holds_all _ _ _ _).mp h x) w

theorem MttT_CBF : MttTF.Valid CBF := by
  intro ρ env
  refine (MttTF.holds_tall _ _ _).mpr fun a => (MttTF.holds_all _ _ _ _).mpr fun G => ?_
  refine (MttTF.holds_imp _ _ _ _).mpr fun h => (MttTF.holds_all _ _ _ _).mpr fun x => (MttT_box _ _ _).mpr fun w => ?_
  exact (MttTF.holdsAt_all _ _ _ _ w).mp ((MttT_box _ _ _).mp h w) x

theorem MttT_Nec : MttTF.Valid Nec := by
  intro ρ env
  refine (MttTF.holds_tall _ _ _).mpr fun a => (MttTF.holds_all _ _ _ _).mpr fun x => (MttT_box _ _ _).mpr fun w => ?_
  exact (MttTF.holdsAt_ex _ _ _ _ w).mpr ⟨x, (MttTF.holdsAt_eqv _ _ _ _ _ _ w).mpr ⟨rfl, Or.inl HEq.rfl⟩⟩

theorem MttT_Choice : MttTF.Valid Choice := MttTF.Choice_valid

/-! ## Failures: Collapse, PropExt, LL≡, the Identity Identity, Classicism -/

theorem MttT_not_Collapse : ¬ MttTF.Valid Collapse := fun h => by
  have h0 := (MttTF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ()) (fun w => w = true)
  have hb := (MttTF.holds_imp _ _ _ _).mp h0 (rfl : true = true)
  exact Bool.noConfusion ((MttT_box _ _ _).mp hb false : false = true)

theorem MttT_not_PropExt : ¬ MttTF.Valid PropExt := fun h => by
  have h0 := (MttTF.holds_all _ _ _ _).mp ((MttTF.holds_all _ _ _ _).mp (h (fun i => i.elim0) ())
    (fun w => w = true)) (fun _ => True)
  have hb := (MttTF.holds_imp _ _ _ _).mp h0
    ((MttTF.holds_iff _ _ _ _).mpr ⟨fun _ => trivial, fun _ => (rfl : true = true)⟩)
  have e := (MttT_top_iff (fun w => w = true)).mp ((MttTF.holdsAt_eqv_t _ _ _ _ _).mp hb)
  exact Bool.noConfusion (cast (congrFun e false).symm trivial : false = true)

/-- Truth is an instance of LL≡ (PI⁻ derives it from LL≡), so LL≡ fails. -/
theorem MttT_not_LLEqv : ¬ MttTF.Valid LLEqv := fun h =>
  MttT_not_Truth (MttTF.soundness (Ax := fun χ => χ = LLEqv) MttT_model (fun _ e => by subst e; exact h)
    (Derive.d_Truth rfl))

theorem MttT_not_IdId : ¬ MttTF.Valid IdId := fun h => by
  have h0 := (MttTF.holds_all _ _ _ _).mp ((MttTF.holds_all _ _ _ _).mp
    ((MttTF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .t) (fun w => w = true)) (fun w => w = false)
  have hE : ∀ w, MttTF.HoldsAt (RD.Ex : Fm (((Ctx.nil.text).ext tv0).ext tv0)) (scons .t (fun i => i.elim0))
      (((), (fun w => w = true)), (fun w => w = false)) w := fun w =>
    (MttTF.holdsAt_eqv _ _ _ _ _ _ w).mpr ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩
  rcases ((MttTF.holdsAt_eqv_t _ _ _ _ _).mp h0).2 with e | ⟨s, _⟩
  · have hA : MttTF.HoldsAt (RD.Ax' : Fm (((Ctx.nil.text).ext tv0).ext tv0)) (scons .t (fun i => i.elim0))
        (((), (fun w => w = true)), (fun w => w = false)) true := cast (congrFun (eq_of_heq e) true) (hE true)
    have h2 := (MttTF.holdsAt_imp _ _ _ _ _).mp ((MttTF.holdsAt_all _ _ _ _ _).mp hA (fun z => z)) (rfl : true = true)
    exact Bool.noConfusion (h2 : true = false)
  · rcases s with e | e
    · exact Bool.noConfusion (cast (congrFun e false) (hE false) : false = true)
    · exact Bool.noConfusion (cast (congrFun e true) (hE true) : true = false)

/-- Classicism proves the Identity Identity, which fails. -/
theorem MttT_not_Class : ¬ ∀ χ, ClassSch χ → MttTF.Valid χ := fun h =>
  MttT_not_IdId (MttTF.soundness MttT_model h (d_IdId_of_Class (S := ClassSch) (fun _ hχ => hχ)))

/-! ## Congruence and extensionality for functions -/

theorem MttT_not_Cong : ¬ MttTF.Valid Cong := fun h => by
  have h0 := MttTF.tr_Cong.mp ((MttTF.valid_iff_tr _).mp h) .t .t .t .t (fun z _ => z true) (fun z _ => z true)
    (fun w => w = true) (fun w => w = false) ⟨⟨rfl, Or.inl HEq.rfl⟩, ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩⟩
  rcases h0.2 with e | ⟨s, _⟩
  · exact Bool.noConfusion (cast (congrFun (eq_of_heq e) true) (rfl : true = true) : true = false)
  · rcases s with e | e
    · exact Bool.noConfusion (cast (congrFun e false) (rfl : true = true) : false = true)
    · exact Bool.noConfusion (cast (congrFun e true) (rfl : true = true) : true = false)

theorem MttT_tr_WCong : MttTF.Tr WCong ↔ ∀ a b c d (f : MttTF.U.El a → MttTF.U.El c) (g : MttTF.U.El b → MttTF.U.El d) x y,
    (MttTF.teq a b MttTF.U.w0 ∧ MttTF.teq c d MttTF.U.w0) ∧
      (MttTF.eqv (.arr a c) (.arr b d) f g MttTF.U.w0 ∧ MttTF.eqv a b x y MttTF.U.w0) →
    MttTF.eqv c d (f x) (g y) MttTF.U.w0 := Iff.rfl

theorem MttT_not_WCong : ¬ MttTF.Valid WCong := fun h => by
  have h0 := MttT_tr_WCong.mp ((MttTF.valid_iff_tr _).mp h) .t .t .t .t (fun z _ => z true) (fun z _ => z true)
    (fun w => w = true) (fun w => w = false)
    ⟨⟨rfl, rfl⟩, ⟨⟨rfl, Or.inl HEq.rfl⟩, ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩⟩⟩
  rcases h0.2 with e | ⟨s, _⟩
  · exact Bool.noConfusion (cast (congrFun (eq_of_heq e) true) (rfl : true = true) : true = false)
  · rcases s with e | e
    · exact Bool.noConfusion (cast (congrFun e false) (rfl : true = true) : false = true)
    · exact Bool.noConfusion (cast (congrFun e true) (rfl : true = true) : true = false)

theorem MttT_tr_PCong : MttTF.Tr PCong ↔ ∀ a c d (f : MttTF.U.El a → MttTF.U.El c) (g : MttTF.U.El a → MttTF.U.El d) x,
    MttTF.eqv (.arr a c) (.arr a d) f g MttTF.U.w0 → MttTF.eqv c d (f x) (g x) MttTF.U.w0 := Iff.rfl

theorem MttT_PCong : MttTF.Valid PCong :=
  (MttTF.valid_iff_tr _).mpr <| MttT_tr_PCong.mpr fun a c d f g x ⟨e, h⟩ => by
    have ecd : c = d := (Code.arr.inj e).2
    subst ecd
    rcases h with h | ⟨s, _⟩
    · have efg : f = g := eq_of_heq h
      subst efg
      exact ⟨rfl, Or.inl HEq.rfl⟩
    · exact (show False from s).elim

theorem MttT_not_PExt : ¬ MttTF.Valid PExt := fun h => by
  have h0 := MttTF.tr_PExt.mp ((MttTF.valid_iff_tr _).mp h) .e .t .t (fun _ w => w = true) (fun _ w => w = false)
    (fun _ => ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩)
  rcases h0.2 with e | ⟨s, _⟩
  · exact Bool.noConfusion (cast (congrFun (congrFun (eq_of_heq e) ()) true) (rfl : true = true) : true = false)
  · exact (show False from s)

/-! ## Haecceitism and Twin fail, since nothing is identified with an item of another type -/

theorem MttT_not_Hae : ¬ MttTF.Valid Hae := fun h => by
  have h0 := (MttTF.holds_all _ _ _ _).mp ((MttTF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  exact Code.arr_ne_left (B := Empty) .e .t ((MttTF.holds_eqv _ _ _ _ _ _).mp h0).1.symm

theorem MttT_not_Twin : ¬ MttTF.Valid Twin := fun h => by
  have h0 := (MttTF.holds_all _ _ _ _).mp ((MttTF.holds_tall _ _ _).mp (h (fun i => i.elim0) ()) .e) ()
  obtain ⟨_, hb⟩ := (MttTF.holds_tex _ _ _).mp h0
  obtain ⟨hn, hy⟩ := (MttTF.holds_conj _ _ _ _).mp hb
  obtain ⟨_, hy⟩ := (MttTF.holds_ex _ _ _ _).mp hy
  exact (MttTF.holds_neg _ _ _).mp hn ((MttTF.holds_teq _ _ _ _).mpr ((MttTF.holds_eqv _ _ _ _ _ _).mp hy).1)

/-! ## LL≡-Poly fails

The instance for the polymorphic predicate `λγ:∗.λz:γ.∃_{γ→t}F (F ≡_{γ→t,t→t} λp:t.p ∧ F z)`: at
`t`, the only item of type `t → t` identified with the identity function is that function itself,
so the predicate holds of a proposition just when it is true; it holds of the proposition true only
at the actual world, but not of the one identified with it. -/

/-- `λγ:∗.λz:γ.∃_{γ→t}F (F ≡_{γ→t,t→t} λp:t.p ∧ F z)` -/
def MttT_PredId : Tm Ctx.nil (.pi (.arr (.var fz) .t)) :=
  .tlam (.lam tv0 (Tm.ex tv0.pred (Tm.conj (Tm.eqv tv0.pred tyT.pred (.var .here) (.lam tyT (.var .here)))
    (.app (.var .here) (.var (.there .here))))))

theorem MttT_tr_LLPolyId : MttTF.Tr (LLPoly MttT_PredId) ↔ ∀ a b (x : MttTF.U.El a) (y : MttTF.U.El b),
    MttTF.eqv a b x y MttTF.U.w0 →
    (∃ F : MttTF.U.El a → Bool → Prop, MttTF.eqv (.arr a .t) (.arr .t .t) F (fun v => v) MttTF.U.w0 ∧ F x MttTF.U.w0) →
    (∃ F : MttTF.U.El b → Bool → Prop, MttTF.eqv (.arr b .t) (.arr .t .t) F (fun v => v) MttTF.U.w0 ∧ F y MttTF.U.w0) :=
  Iff.rfl

theorem MttT_not_LLPoly : ¬ MttTF.Valid (LLPoly MttT_PredId) := fun h => by
  obtain ⟨F, ⟨_, hF⟩, hq⟩ := MttT_tr_LLPolyId.mp ((MttTF.valid_iff_tr _).mp h) .t .t
    (fun w => w = true) (fun w => w = false) ⟨rfl, Or.inr ⟨Or.inl rfl, Or.inr rfl⟩⟩
    ⟨fun v => v, ⟨rfl, Or.inl HEq.rfl⟩, (rfl : true = true)⟩
  rcases hF with e | ⟨s, _⟩
  · have e' : F = fun v => v := eq_of_heq e
    subst e'
    exact Bool.noConfusion (hq : true = false)
  · exact (show False from s)

end Wd
end PIF
