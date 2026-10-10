import PIBF
set_option autoImplicit false

/-!
# A Kripke model of PIᶜ in which Inj≈ and Recovery fail, with two worlds

`𝔐_k,ir`: two worlds, the actual world `T` and another world `F`, each seeing both. Propositions
are sets of worlds, and identity of items within a type is identity (so all functions are items, at
every world). There is one entity, and three base types: `d`, a copy of `t` (its items are sets of
worlds), and `p` and `q`, copies of `e`.

Items are identified, at a world `w`, just in case they are the same value and their types have the
same `w`-key, where the `w`-key of a type sends `d` to `t`, and, at `T`, `p` to `e`, and, at `F`,
`q` to `e`. So the items of `d` are identified with the matching items of `t` at both worlds; those
of `p` with the entity at the actual world only; and those of `q` with the entity at the other world
only. `≈` does not depend on the world: two types are identified just in case they have the same
`≈`-key, which sends `e → d` (inside any type) to `e → t`. So `e → t ≈ e → d`, while `t` and `d` are
distinct: Inj≈ and Recovery fail.

LL≈ holds at every world by the fundamental lemma for the admissible relations "same `≈`-key, and
the same value". Since identity within a type is identity, LL≡ and Classicism hold. The world-
dependence of identity across types refutes NI× and ND×; the two worlds refute Collapse and
PropExt≡; and `t` and `d`, whose items are necessarily identified, refute Ext≈ and Int≈.

The full profile. Valid: LL≡, Classicism (and with it Bool, IdId, NI≡, NI≈, TNec, TCBF, Nec, CBF,
Truth, ⊤≢⊥, Cantor, WCong), LL≡/≈ (for every polymorphic predicate, with parameters), ND≈, TBF, T,
Slogan, Cong, PCong→, PCong←, BF and Functional Choice. Refuted: Inj≈, Recovery, Collapse,
PropExt≡, NI×, ND×, Ext≈, Int≈, Disjoint, Twin (the item of `q` has no partner at the actual world),
Haecceitism, and LL≡-Poly (for `λγ.λz.(γ ≈ e)`: the entity and the item of `p`).
-/

namespace PIF
namespace Kr
open Tm

/-! ## The universe -/

/-- The base types: `d` (a copy of `t`), and `p` and `q` (copies of `e`). -/
inductive XIW_B : Type where
  | d | p | q
  deriving DecidableEq

def XIW_BEl : XIW_B → Type
  | .d => Bool → Prop
  | .p => Unit
  | .q => Unit

theorem XIW_BEl_ne : ∀ b, Nonempty (XIW_BEl b)
  | .d => ⟨fun _ => True⟩
  | .p => ⟨()⟩
  | .q => ⟨()⟩

def XIW_U : Univ where
  W := Bool
  w0 := true
  R := fun _ _ => True
  Rrefl := fun _ => trivial
  Rtrans := fun _ _ _ _ _ => trivial
  E := Unit
  Base := XIW_B
  B := XIW_BEl
  neE := ⟨()⟩
  neB := XIW_BEl_ne
  re := fun _ x y => x = y
  rb := fun _ _ x y => x = y
  re_refl := fun _ _ => rfl
  re_symm := fun _ _ _ h => h.symm
  re_trans := fun _ _ _ _ h1 h2 => h1.trans h2
  re_mono := fun _ _ _ _ _ h => h
  rb_refl := fun _ _ _ => rfl
  rb_symm := fun _ _ _ _ h => h.symm
  rb_trans := fun _ _ _ _ _ h1 h2 => h1.trans h2
  rb_mono := fun _ _ _ _ _ _ h => h
  D := fun _ _ => True
  D_e := fun _ => trivial
  D_t := fun _ => trivial
  D_arr := fun _ _ _ _ _ => trivial
  D_mono := fun _ _ _ _ _ => trivial

/-- Identity at a world, within a type, is identity. -/
theorem XIW_rel_eq : ∀ (a : Code XIW_B) (w : Bool) (x y : XIW_U.El a), XIW_U.rel a w x y ↔ x = y
  | .e, _, _, _ => Iff.rfl
  | .t, _, p, q => by
    show (∀ v, True → (p v ↔ q v)) ↔ p = q
    exact ⟨fun h => funext fun v => propext (h v trivial), fun h => h ▸ fun _ _ => Iff.rfl⟩
  | .base _, _, _, _ => Iff.rfl
  | .arr a c, _, f, g => by
    show (∀ v, True → ∀ x y, XIW_U.rel a v x y → XIW_U.rel c v (f x) (g y)) ↔ f = g
    constructor
    · intro h
      exact funext fun x => (XIW_rel_eq c true _ _).mp (h true trivial x x ((XIW_rel_eq a true x x).mpr rfl))
    · intro h v _ x y hxy
      have e := (XIW_rel_eq a v x y).mp hxy
      subst e; subst h
      exact (XIW_rel_eq c v _ _).mpr rfl

/-! ## Keys -/

/-- The `w`-key of a type: `d` goes to `t`; at the actual world `p` goes to `e`, and at the other
world `q` goes to `e`. -/
def XIW_K : Bool → Code XIW_B → Code XIW_B
  | _, .e => .e
  | _, .t => .t
  | _, .base .d => .t
  | true, .base .p => .e
  | false, .base .p => .base .p
  | true, .base .q => .base .q
  | false, .base .q => .e
  | w, .arr a c => .arr (XIW_K w a) (XIW_K w c)

theorem XIW_El_K : ∀ (w : Bool) (a : Code XIW_B), XIW_U.El (XIW_K w a) = XIW_U.El a
  | _, .e => rfl
  | _, .t => rfl
  | _, .base .d => rfl
  | true, .base .p => rfl
  | false, .base .p => rfl
  | true, .base .q => rfl
  | false, .base .q => rfl
  | w, .arr a c => by
    show (XIW_U.El (XIW_K w a) → XIW_U.El (XIW_K w c)) = (XIW_U.El a → XIW_U.El c)
    rw [XIW_El_K w a, XIW_El_K w c]

theorem XIW_El_of_K {w : Bool} {a b : Code XIW_B} (h : XIW_K w a = XIW_K w b) : XIW_U.El a = XIW_U.El b :=
  (XIW_El_K w a).symm.trans ((congrArg XIW_U.El h).trans (XIW_El_K w b))

/-- The `≈`-key step: `e → d` goes to `e → t`. -/
def XIW_sp (x y : Code XIW_B) : Code XIW_B := if x = .e ∧ y = .base .d then .arr .e .t else .arr x y

/-- The `≈`-key of a type. -/
def XIW_T : Code XIW_B → Code XIW_B
  | .e => .e
  | .t => .t
  | .base b => .base b
  | .arr a c => XIW_sp (XIW_T a) (XIW_T c)

theorem XIW_K_sp (w : Bool) (x y : Code XIW_B) : XIW_K w (XIW_sp x y) = XIW_K w (.arr x y) := by
  unfold XIW_sp
  split
  · next h => obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl
  · rfl

theorem XIW_K_T (w : Bool) : ∀ a, XIW_K w (XIW_T a) = XIW_K w a
  | .e => rfl
  | .t => rfl
  | .base _ => rfl
  | .arr a c => by
    show XIW_K w (XIW_sp (XIW_T a) (XIW_T c)) = Code.arr (XIW_K w a) (XIW_K w c)
    rw [XIW_K_sp]
    show Code.arr (XIW_K w (XIW_T a)) (XIW_K w (XIW_T c)) = _
    rw [XIW_K_T w a, XIW_K_T w c]

theorem XIW_KT {a b : Code XIW_B} (h : XIW_T a = XIW_T b) (w : Bool) : XIW_K w a = XIW_K w b :=
  (XIW_K_T w a).symm.trans ((congrArg (XIW_K w) h).trans (XIW_K_T w b))

theorem XIW_El_of_T {a b : Code XIW_B} (h : XIW_T a = XIW_T b) : XIW_U.El a = XIW_U.El b :=
  XIW_El_of_K (XIW_KT h true)

/-! ## The frame -/

def XIW_eqv (a b : Code XIW_B) (x : XIW_U.El a) (y : XIW_U.El b) (w : Bool) : Prop :=
  XIW_K w a = XIW_K w b ∧ HEq x y

def XIW_F : Frame where
  U := XIW_U
  eqv := XIW_eqv
  teq := fun a b _ => XIW_T a = XIW_T b
  eqv_resp := by
    intro u a b x x' y y' hx hy
    have e1 := (XIW_rel_eq a u x x').mp hx
    have e2 := (XIW_rel_eq b u y y').mp hy
    subst e1; subst e2
    exact Iff.rfl

theorem XIW_heq : ∀ a x y w, XIW_F.eqv a a x y w ↔ XIW_F.U.rel a w x y := fun a x y w =>
  ⟨fun h => (XIW_rel_eq a w x y).mpr (eq_of_heq h.2),
   fun h => ⟨rfl, heq_of_eq ((XIW_rel_eq a w x y).mp h)⟩⟩

theorem XIW_symm {a b : Code XIW_B} {x : XIW_U.El a} {y : XIW_U.El b} {w : Bool}
    (h : XIW_eqv a b x y w) : XIW_eqv b a y x w := ⟨h.1.symm, h.2.symm⟩

theorem XIW_trans {a b c : Code XIW_B} {x : XIW_U.El a} {y : XIW_U.El b} {z : XIW_U.El c} {w : Bool}
    (h1 : XIW_eqv a b x y w) (h2 : XIW_eqv b c y z w) : XIW_eqv a c x z w :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

/-- The admissible relations: between types with the same `≈`-key, the same value. -/
def XIW_Inv : KInv XIW_F where
  Adm := fun _ a a' S => XIW_T a = XIW_T a' ∧ ∀ u x y, S u x y ↔ HEq x y
  amono := fun h _ => h
  smono := fun hA u u' x x' _ _ hs => (hA.2 u' x x').mpr ((hA.2 u x x').mp hs)
  refl := fun _ a => ⟨rfl, fun u x y => (XIW_rel_eq a u x y).trans ⟨heq_of_eq, eq_of_heq⟩⟩
  arrow := by
    intro w a a' c c' S T hS hT
    obtain ⟨h1, h2⟩ := hS
    obtain ⟨k1, k2⟩ := hT
    refine ⟨by show XIW_sp (XIW_T a) (XIW_T c) = XIW_sp (XIW_T a') (XIW_T c'); rw [h1, k1], fun u f f' => ?_⟩
    have e : (∀ v, XIW_U.R u v → ∀ x x', S v x x' → T v (f x) (f' x')) ↔ (∀ x x', HEq x x' → HEq (f x) (f' x')) :=
      ⟨fun h x x' hx => (k2 u _ _).mp (h u trivial x x' ((h2 u x x').mpr hx)),
       fun h v _ x x' hx => (k2 v _ _).mpr (h x x' ((h2 v x x').mp hx))⟩
    exact e.trans (fun_heq_iff (XIW_El_of_T h1) (XIW_El_of_T k1) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) f f')
  total := by
    intro w a a' S hS u _ x _
    exact ⟨cast (XIW_El_of_T hS.1) x, (XIW_rel_eq a' u _ _).mpr rfl, (hS.2 u x _).mpr (cast_heq _ _).symm⟩
  onto := by
    intro w a a' S hS u _ x' _
    exact ⟨cast (XIW_El_of_T hS.1).symm x', (XIW_rel_eq a u _ _).mpr rfl, (hS.2 u _ x').mpr (cast_heq _ _)⟩
  teq := by
    intro w a a' b b' S T hS hT u _
    show XIW_T a = XIW_T b ↔ XIW_T a' = XIW_T b'
    rw [hS.1, hT.1]
  eqv := by
    intro w a a' b b' S T hS hT u _ x x' y y' hx hy
    show (XIW_K u a = XIW_K u b ∧ HEq x y) ↔ (XIW_K u a' = XIW_K u b' ∧ HEq x' y')
    rw [XIW_KT hS.1 u, XIW_KT hT.1 u]
    have hx' := (hS.2 u x x').mp hx
    have hy' := (hT.2 u y y').mp hy
    exact and_congr Iff.rfl ⟨fun h => hx'.symm.trans (h.trans hy'), fun h => hx'.trans (h.trans hy'.symm)⟩

theorem XIW_isModelAt : XIW_F.IsModelAt := by
  obtain ⟨h1, h2, h3⟩ := XIW_F.idAx_of (fun a x w hx => (XIW_heq a x x w).mpr hx)
    (fun _ _ _ _ _ h => XIW_symm h) (fun _ _ _ _ _ _ _ h1 h2 => XIW_trans h1 h2)
  refine ⟨h1, h2, h3, XIW_F.refTeq_of fun _ _ => rfl, ?_⟩
  intro n Γ Q w ρ _ env henv
  refine XIW_F.holdsAt_tall _ _ _ w |>.mpr fun a _ => XIW_F.holdsAt_tall _ _ _ w |>.mpr fun b _ => ?_
  refine (XIW_F.holdsAt_imp _ _ _ _ w).mpr fun hab => ?_
  have e : XIW_T a = XIW_T b := (XIW_F.holdsAt_teq (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env w).mp hab
  refine (XIW_F.holdsAt_imp _ _ _ _ w).mpr fun hq => ?_
  exact XIW_Inv.llTeq_at Q w ρ env henv a b (fun _ x y => HEq x y) ⟨e, fun _ _ _ => Iff.rfl⟩ hq

theorem XIW_LLEqv : XIW_F.Valid LLEqv := fun ρ hρ env henv => XIW_F.LLEqv_of XIW_heq _ ρ hρ env henv

theorem XIW_Class : ∀ χ, ClassSch χ → XIW_F.Valid χ :=
  XIW_F.Class_valid XIW_isModelAt (XIW_F.LLEqv_of XIW_heq) XIW_heq

/-! ## Basic facts -/

theorem XIW_Valid_of {φ : Fm Ctx.nil} (h : XIW_F.HoldsAt φ (fun i => i.elim0) () true) : XIW_F.Valid φ := by
  intro ρ _ env _
  have e1 : ρ = fun i => i.elim0 := funext fun i => i.elim0
  subst e1
  exact h

/-- `□φ` is truth at both worlds. -/
theorem XIW_box {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : XIW_F.U.TEnv n) (env : XIW_F.U.Env Γ ρ) (w : Bool) :
    XIW_F.HoldsAt (boxF φ) ρ env w ↔ ∀ v, XIW_F.HoldsAt φ ρ env v :=
  (XIW_F.box_of XIW_heq φ ρ env w).trans ⟨fun h v => h v trivial, fun h v _ => h v⟩

/-! ## Every theorem of PIᶜ is valid -/

theorem XIW_validAt_closeCtx (F : Frame) : ∀ {n : Nat} (Γ : Ctx n) (χ : Fm Γ),
    (∀ w ρ, (∀ i, F.U.D w (ρ i)) → ∀ env, F.EnvAdm Γ ρ w env → F.HoldsAt χ ρ env w) →
    F.ValidAt (closeCtx Γ χ)
  | _, .nil, _, h => h
  | _, .ext Γ σ, χ, h => XIW_validAt_closeCtx F Γ (Tm.all σ χ) fun w ρ hρ env henv =>
      (F.holdsAt_all σ χ ρ env w).mpr fun v hv => h w ρ hρ (env, v) ⟨henv, F.adm_of_rel σ ρ w v hv⟩
  | _, .text Γ, χ, h => XIW_validAt_closeCtx F Γ (Tm.tall χ) fun w ρ hρ env henv =>
      (F.holdsAt_tall χ ρ env w).mpr fun a ha => h w (scons a ρ) (fin_cases ha hρ) env henv

/-- Classicism, at every world. -/
theorem XIW_Class_validAt (F : Frame) (hM : F.IsModelAt) (hLL : F.ValidAt LLEqv)
    (heq : ∀ a x y w, F.eqv a a x y w ↔ F.U.rel a w x y) : ∀ χ, ClassSch χ → F.ValidAt χ := by
  have sound : ∀ {n : Nat} {Γ : Ctx n} {θ : Fm Γ}, PIP Γ θ → F.ValidAt θ := fun h =>
    F.soundnessAt hM (fun χ (e : χ = LLEqv) => e ▸ hLL) h
  rintro _ (⟨n, Γ, φ, ψ, hp, rfl⟩ | ⟨n, Γ, σ, φ, ψ, hp, rfl⟩)
  · refine XIW_validAt_closeCtx F Γ _ fun w ρ hρ env henv => ?_
    refine ((F.holdsAt_eqv tyT tyT φ ψ ρ env _).trans (heq _ _ _ _)).mpr ?_
    intro v hv
    exact sound hp v ρ (fun i => F.U.D_mono _ _ _ hv (hρ i)) env (F.EnvAdm_mono ρ _ v hv env henv)
  · refine XIW_validAt_closeCtx F Γ _ fun w ρ hρ env henv => ?_
    refine ((F.holdsAt_eqv σ.pred σ.pred _ _ ρ env _).trans (heq _ _ _ _)).mpr ?_
    refine (F.relV_iff σ.pred ρ _ _ _).mp ?_
    intro v hv u u' huu x hx
    have hA := F.adm_eval (Tm.lam σ φ) ρ _ env henv v hv u u' huu x hx
    have hu' : F.hom.Rel σ.1 ρ ρ (F.homRs ρ) x u' u' := by
      have h1 := (F.relV_iff σ ρ v u u').mp huu
      have h2 := F.U.rel_mono _ v x _ _ hx (F.U.rel_refl_right _ v _ _ h1)
      exact (F.relV_iff σ ρ x u' u').mpr h2
    have hρx : ∀ i, F.U.D x (ρ i) := fun i => F.U.D_mono _ _ _ (F.U.Rtrans _ _ _ hv hx) (hρ i)
    have henvx := F.EnvAdm_mono ρ _ x (F.U.Rtrans _ _ _ hv hx) env henv
    exact hA.trans (sound hp x ρ hρx (env, u') ⟨henvx, hu'⟩)

/-- PIᶜ: Classicism and LL≡. -/
abbrev XIW_S : Fm Ctx.nil → Prop := fun χ => ClassSch χ ∨ χ = LLEqv

theorem XIW_S_C : ∀ χ, ClassSch χ → XIW_S χ := fun _ h => Or.inl h
theorem XIW_S_LL : XIW_S LLEqv := Or.inr rfl

theorem XIW_of_prov {φ : Fm Ctx.nil} (h : Prov XIW_S Ctx.nil φ) : XIW_F.Valid φ := fun ρ hρ env henv =>
  XIW_F.soundnessAt XIW_isModelAt (fun χ hχ => hχ.elim
    (XIW_Class_validAt XIW_F XIW_isModelAt (XIW_F.LLEqv_of XIW_heq) XIW_heq χ)
    (fun e => e ▸ XIW_F.LLEqv_of XIW_heq)) h _ ρ hρ env henv

theorem XIW_Bool : ∀ φ, BoolSch φ → XIW_F.Valid φ := fun φ h => XIW_of_prov (d_Bool_of_Class XIW_S_C φ h)
theorem XIW_IdId : XIW_F.Valid IdId := XIW_of_prov (d_IdId_of_Class XIW_S_C)
theorem XIW_NIEqv : XIW_F.Valid NIEqv := XIW_of_prov (d_NIEqv_of_Class XIW_S_C XIW_S_LL)
theorem XIW_NITeq : XIW_F.Valid NITeq := XIW_of_prov (d_NITeq_of_Class XIW_S_C)
theorem XIW_TNec : XIW_F.Valid TNec := XIW_of_prov (d_TNec_of_Class XIW_S_C)
theorem XIW_TCBF : ∀ χ, TCBFSch χ → XIW_F.Valid χ := fun χ h => XIW_of_prov (d_TCBF_of_Class XIW_S_C XIW_S_LL χ h)
theorem XIW_Nec : XIW_F.Valid Nec := XIW_of_prov (d_Nec_of_Class XIW_S_C)
theorem XIW_CBF : XIW_F.Valid CBF := XIW_of_prov (d_CBF_of_Class XIW_S_C XIW_S_LL)
theorem XIW_Truth : XIW_F.Valid Truth := XIW_of_prov (Derive.d_Truth XIW_S_LL)
theorem XIW_TopBot : XIW_F.Valid TopBot := XIW_of_prov (Derive.d_TopBot XIW_S_LL)
theorem XIW_Cantor : XIW_F.Valid Cantor := XIW_of_prov (Derive.d_Cantor XIW_S_LL)
theorem XIW_WCong : XIW_F.Valid WCong := XIW_of_prov (Derive.d_WCong XIW_S_LL)

/-! ## `≈`: Inj≈ and Recovery fail -/

/-- `e → t ≈ e → d`, but not `t ≈ d`. -/
theorem XIW_not_Inj : ¬ XIW_F.Valid Inj := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIW_F.holdsAt_tall _ _ _ _).mp ((XIW_F.holdsAt_tall _ _ _ _).mp ((XIW_F.holdsAt_tall _ _ _ _).mp
    ((XIW_F.holdsAt_tall _ _ _ _).mp h .e trivial) .e trivial) .t trivial) (.base .d) trivial
  have h2 := (XIW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIW_F.holdsAt_teq _ _ _ _ _).mpr
    (show XIW_T (.arr .e .t) = XIW_T (.arr .e (.base .d)) by decide))
  have e : XIW_T .t = XIW_T (.base .d) := (XIW_F.holdsAt_teq _ _ _ _ _).mp ((XIW_F.holdsAt_conj _ _ _ _ _).mp h2).2
  exact absurd e (by decide)

theorem XIW_not_Recovery : ¬ XIW_F.Valid Recovery := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIW_F.holdsAt_tall _ _ _ _).mp ((XIW_F.holdsAt_tall _ _ _ _).mp ((XIW_F.holdsAt_tall _ _ _ _).mp
    ((XIW_F.holdsAt_tall _ _ _ _).mp h .e trivial) .e trivial) .t trivial) (.base .d) trivial
  have h2 := (XIW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIW_F.holdsAt_conj _ _ _ _ _).mpr
    ⟨(XIW_F.holdsAt_teq _ _ _ _ _).mpr (show XIW_T (.arr .e .t) = XIW_T (.arr .e (.base .d)) by decide),
     (XIW_F.holdsAt_teq _ _ _ _ _).mpr (show XIW_T .e = XIW_T .e from rfl)⟩)
  have e : XIW_T .t = XIW_T (.base .d) := (XIW_F.holdsAt_teq _ _ _ _ _).mp h2
  exact absurd e (by decide)

/-- `≈` does not depend on the world. -/
theorem XIW_NDTeq : XIW_F.Valid NDTeq := by
  refine XIW_Valid_of ?_
  refine (XIW_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XIW_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XIW_F.holdsAt_imp _ _ _ _ _).mpr fun hn => (XIW_box _ _ _ _).mpr fun v => ?_
  refine (XIW_F.holdsAt_neg _ _ _ _).mpr fun ht => (XIW_F.holdsAt_neg _ _ _ _).mp hn ?_
  have e : XIW_T a = XIW_T b := (XIW_F.holdsAt_teq _ _ _ _ v).mp ht
  exact (XIW_F.holdsAt_teq _ _ _ _ _).mpr e

/-- With constant domains of types, the Barcan formula for types holds. -/
theorem XIW_TBF : ∀ χ, TBFSch χ → XIW_F.Valid χ := by
  rintro _ ⟨φ, rfl⟩
  refine XIW_Valid_of ?_
  refine (XIW_F.holdsAt_imp _ _ _ _ _).mpr fun h => (XIW_box _ _ _ _).mpr fun v => ?_
  refine (XIW_F.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  exact (XIW_box _ _ _ _).mp ((XIW_F.holdsAt_tall _ _ _ _).mp h a trivial) v

/-! ## Modal principles -/

theorem XIW_TAx : XIW_F.Valid TAx := by
  refine XIW_Valid_of ?_
  refine (XIW_F.holdsAt_all _ _ _ _ _).mpr fun p _ => (XIW_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  exact (XIW_box _ _ _ _).mp h true

/-- The proposition true just at the actual world is true, but not necessary. -/
theorem XIW_not_Collapse : ¬ XIW_F.Valid Collapse := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIW_F.holdsAt_all _ _ _ _ _).mp h (fun w => w = true) (fun _ _ => Iff.rfl)
  have h2 := (XIW_box _ _ _ _).mp ((XIW_F.holdsAt_imp _ _ _ _ _).mp h1 rfl) false
  have h3 : false = true := h2
  exact Bool.false_ne_true h3

/-- `⊤` and the proposition true just at the actual world are equivalent, but not identical. -/
theorem XIW_not_PropExt : ¬ XIW_F.Valid PropExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIW_F.holdsAt_all _ _ _ _ _).mp ((XIW_F.holdsAt_all _ _ _ _ _).mp h (fun _ => True)
    (fun _ _ => Iff.rfl)) (fun w => w = true) (fun _ _ => Iff.rfl)
  have h2 := (XIW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIW_F.holdsAt_iff _ _ _ _ _).mpr
    (show True ↔ true = true from ⟨fun _ => rfl, fun _ => trivial⟩))
  have h3 := (XIW_heq .t _ _ _).mp ((XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mp h2)
  have h4 : True ↔ false = true := h3 false trivial
  exact Bool.false_ne_true (h4.mp trivial)

/-! ## Identity across types depends on the world -/

/-- The entity and the item of `p` are identical at the actual world only. -/
theorem XIW_not_NIX : ¬ XIW_F.Valid NIX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIW_F.holdsAt_tall _ _ _ _).mp ((XIW_F.holdsAt_tall _ _ _ _).mp h .e trivial) (.base .p) trivial
  have h2 := (XIW_F.holdsAt_all _ _ _ _ _).mp ((XIW_F.holdsAt_all _ _ _ _ _).mp h1 () rfl) () rfl
  have h3 := (XIW_box _ _ _ _).mp ((XIW_F.holdsAt_imp _ _ _ _ _).mp h2
    ((XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩)) false
  have h4 : XIW_K false .e = XIW_K false (.base .p) := ((XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mp h3).1
  exact absurd h4 (by decide)

/-- The entity and the item of `q` are distinct at the actual world, but identical at the other. -/
theorem XIW_not_NDX : ¬ XIW_F.Valid NDX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIW_F.holdsAt_tall _ _ _ _).mp ((XIW_F.holdsAt_tall _ _ _ _).mp h .e trivial) (.base .q) trivial
  have h2 := (XIW_F.holdsAt_all _ _ _ _ _).mp ((XIW_F.holdsAt_all _ _ _ _ _).mp h1 () rfl) () rfl
  have h3 := (XIW_box _ _ _ _).mp ((XIW_F.holdsAt_imp _ _ _ _ _).mp h2
    ((XIW_F.holdsAt_neg _ _ _ _).mpr fun he => by
      have h4 : XIW_K true .e = XIW_K true (.base .q) := ((XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mp he).1
      exact absurd h4 (by decide))) false
  exact (XIW_F.holdsAt_neg _ _ _ _).mp h3 ((XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩)

/-! ## `t` and `d`: Ext≈ and Int≈ fail -/

/-- At every world, each item of `t` is identified with the same value, of type `d`, and
conversely. -/
theorem XIW_td {n : Nat} {Γ : Ctx n} (ρ : XIW_F.U.TEnv n) (env : XIW_F.U.Env Γ ρ) (w : Bool) :
    XIW_F.HoldsAt (Tm.conj (subT : Fm (Γ.text.text)) supT) (scons (.base .d) (scons .t ρ)) env w := by
  refine (XIW_F.holdsAt_conj _ _ _ _ _).mpr ⟨?_, ?_⟩
  · refine (XIW_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XIW_F.holdsAt_ex _ _ _ _ _).mpr ⟨x, (XIW_rel_eq _ _ _ _).mpr rfl, ?_⟩
    exact (XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩
  · refine (XIW_F.holdsAt_all _ _ _ _ _).mpr fun y _ => (XIW_F.holdsAt_ex _ _ _ _ _).mpr ⟨y, (XIW_rel_eq _ _ _ _).mpr rfl, ?_⟩
    exact (XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩

theorem XIW_not_ExtT : ¬ XIW_F.Valid ExtT := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIW_F.holdsAt_tall _ _ _ _).mp ((XIW_F.holdsAt_tall _ _ _ _).mp h .t trivial) (.base .d) trivial
  have h2 := (XIW_F.holdsAt_imp _ _ _ _ _).mp h1 (XIW_td (Γ := Ctx.nil) _ () true)
  have e : XIW_T .t = XIW_T (.base .d) := (XIW_F.holdsAt_teq _ _ _ _ _).mp h2
  exact absurd e (by decide)

theorem XIW_not_IntT : ¬ XIW_F.Valid IntT := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIW_F.holdsAt_tall _ _ _ _).mp ((XIW_F.holdsAt_tall _ _ _ _).mp h .t trivial) (.base .d) trivial
  have h2 := (XIW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIW_F.holdsAt_conj _ _ _ _ _).mpr
    ⟨(XIW_box _ _ _ _).mpr fun v => ((XIW_F.holdsAt_conj _ _ _ _ _).mp (XIW_td (Γ := Ctx.nil) _ () v)).1,
     (XIW_box _ _ _ _).mpr fun v => ((XIW_F.holdsAt_conj _ _ _ _ _).mp (XIW_td (Γ := Ctx.nil) _ () v)).2⟩)
  have e : XIW_T .t = XIW_T (.base .d) := (XIW_F.holdsAt_teq _ _ _ _ _).mp h2
  exact absurd e (by decide)

/-! ## Identity across types -/

/-- `t` and `d` are distinct, but `⊤` is identified with the same value, of type `d`. -/
theorem XIW_not_Disjoint : ¬ XIW_F.Valid Disjoint := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIW_F.holdsAt_tall _ _ _ _).mp ((XIW_F.holdsAt_tall _ _ _ _).mp h .t trivial) (.base .d) trivial
  have h2 := (XIW_F.holdsAt_imp _ _ _ _ _).mp h1 ((XIW_F.holdsAt_neg _ _ _ _).mpr fun ht => by
    have e : XIW_T .t = XIW_T (.base .d) := (XIW_F.holdsAt_teq _ _ _ _ _).mp ht
    exact absurd e (by decide))
  have h3 := (XIW_F.holdsAt_all _ _ _ _ _).mp ((XIW_F.holdsAt_all _ _ _ _ _).mp h2 (fun _ => True)
    ((XIW_rel_eq _ _ _ _).mpr rfl)) (fun _ => True) ((XIW_rel_eq _ _ _ _).mpr rfl)
  exact (XIW_F.holdsAt_neg _ _ _ _).mp h3 ((XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩)

/-- No entity is identified with an item of a type `β → t`. -/
theorem XIW_Slogan : XIW_F.Valid Slogan := by
  refine XIW_Valid_of ?_
  refine (XIW_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XIW_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XIW_F.holdsAt_all _ _ _ _ _).mpr fun y _ => (XIW_F.holdsAt_neg _ _ _ _).mpr fun hxy => ?_
  have e : (Code.e : Code XIW_B) = .arr (XIW_K true b) .t := ((XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mp hxy).1
  exact nomatch e

theorem XIW_K_true_q : ∀ b : Code XIW_B, XIW_K true b = .base .q → b = .base .q
  | .e, h => nomatch h
  | .t, h => nomatch h
  | .base .d, h => nomatch h
  | .base .p, h => nomatch h
  | .base .q, _ => rfl
  | .arr _ _, h => nomatch h

/-- At the actual world, the item of `q` is identified with nothing of another type. -/
theorem XIW_not_Twin : ¬ XIW_F.Valid Twin := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIW_F.holdsAt_all _ _ _ _ _).mp ((XIW_F.holdsAt_tall _ _ _ _).mp h (.base .q) trivial) () rfl
  obtain ⟨b, _, h2⟩ := (XIW_F.holdsAt_tex _ _ _ _).mp h1
  have h3 := (XIW_F.holdsAt_conj _ _ _ _ _).mp h2
  obtain ⟨y, _, h4⟩ := (XIW_F.holdsAt_ex _ _ _ _ _).mp h3.2
  have e : XIW_K true (.base .q) = XIW_K true b := ((XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mp h4).1
  have eb := XIW_K_true_q b e.symm
  subst eb
  exact (XIW_F.holdsAt_neg _ _ _ _).mp h3.1 ((XIW_F.holdsAt_teq _ _ _ _ _).mpr rfl)

/-- No item is identified with an item of `α → t`. -/
theorem XIW_not_Hae : ¬ XIW_F.Valid Hae := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIW_F.holdsAt_all _ _ _ _ _).mp ((XIW_F.holdsAt_tall _ _ _ _).mp h .e trivial) () rfl
  have e : (Code.e : Code XIW_B) = .arr .e .t := ((XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mp h1).1
  exact nomatch e

theorem XIW_cong {a b c d : Code XIW_B} {f : XIW_U.El (.arr a c)} {g : XIW_U.El (.arr b d)} {x : XIW_U.El a}
    {y : XIW_U.El b} {w : Bool} (h1 : XIW_eqv (.arr a c) (.arr b d) f g w) (h2 : XIW_eqv a b x y w) :
    XIW_eqv c d (f x) (g y) w := by
  obtain ⟨e1, r1⟩ := h1
  obtain ⟨_, r2⟩ := h2
  injection e1 with ea ec
  exact ⟨ec, heq_app (XIW_El_of_K ea) (XIW_El_of_K ec) r1 r2⟩

theorem XIW_Cong : XIW_F.Valid Cong := by
  refine XIW_Valid_of ?_
  refine (XIW_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XIW_F.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (XIW_F.holdsAt_tall _ _ _ _).mpr fun c _ => (XIW_F.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (XIW_F.holdsAt_all _ _ _ _ _).mpr fun f _ => (XIW_F.holdsAt_all _ _ _ _ _).mpr fun g _ =>
    (XIW_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XIW_F.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (XIW_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hc := (XIW_F.holdsAt_conj _ _ _ _ _).mp h
  have h1 := (XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mp hc.1
  have h2 := (XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mp hc.2
  have h3 := XIW_cong h1 h2
  exact (XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr h3

theorem XIW_PCong : XIW_F.Valid PCong := by
  refine XIW_Valid_of ?_
  refine (XIW_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XIW_F.holdsAt_tall _ _ _ _).mpr fun c _ =>
    (XIW_F.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (XIW_F.holdsAt_all _ _ _ _ _).mpr fun f _ => (XIW_F.holdsAt_all _ _ _ _ _).mpr fun g _ =>
    (XIW_F.holdsAt_all _ _ _ _ _).mpr fun x _ => ?_
  refine (XIW_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have h1 := (XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mp h
  have h3 := XIW_cong h1 (show XIW_eqv a a x x true from ⟨rfl, HEq.rfl⟩)
  exact (XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr h3

theorem XIW_PExt : XIW_F.Valid PExt := by
  refine XIW_Valid_of ?_
  refine (XIW_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XIW_F.holdsAt_tall _ _ _ _).mpr fun c _ =>
    (XIW_F.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (XIW_F.holdsAt_all _ _ _ _ _).mpr fun f _ => (XIW_F.holdsAt_all _ _ _ _ _).mpr fun g _ => ?_
  refine (XIW_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hx : ∀ x : XIW_U.El a, XIW_eqv c d (f x) (g x) true := fun x =>
    (XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mp ((XIW_F.holdsAt_all _ _ _ _ _).mp h x ((XIW_rel_eq _ _ _ _).mpr rfl))
  obtain ⟨x0⟩ := Univ.El_nonempty (U := XIW_U) a
  have ec : XIW_K true c = XIW_K true d := (hx x0).1
  refine (XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ⟨?_, ?_⟩
  · show Code.arr (XIW_K true a) (XIW_K true c) = Code.arr (XIW_K true a) (XIW_K true d)
    rw [ec]
  · exact heq_funext rfl (XIW_El_of_K ec) fun u u' hu => by
      cases hu
      exact (hx u).2

/-! ## The Barcan formula and Functional Choice -/

/-- With constant domains, and every function an item, the Barcan formula holds. -/
theorem XIW_BF : XIW_F.Valid BF := by
  refine XIW_Valid_of ?_
  refine (XIW_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XIW_F.holdsAt_all _ _ _ _ _).mpr fun G _ => ?_
  refine (XIW_F.holdsAt_imp _ _ _ _ _).mpr fun h => (XIW_box _ _ _ _).mpr fun v => ?_
  refine (XIW_F.holdsAt_all _ _ _ _ _).mpr fun x _ => ?_
  exact (XIW_box _ _ _ _).mp ((XIW_F.holdsAt_all _ _ _ _ _).mp h x ((XIW_rel_eq _ _ _ _).mpr rfl)) v

/-- Every function is an item, so a choice function exists. -/
theorem XIW_Choice : XIW_F.Valid Choice := by
  refine XIW_Valid_of ?_
  refine (XIW_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XIW_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XIW_F.holdsAt_all _ _ _ _ _).mpr fun R _ => (XIW_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hc : ∀ x : XIW_U.El a, ∃ y : XIW_U.El b, R x y true := fun x => by
    obtain ⟨y, _, hy⟩ := (XIW_F.holdsAt_ex _ _ _ _ _).mp
      ((XIW_F.holdsAt_all _ _ _ _ _).mp h x ((XIW_rel_eq _ _ _ _).mpr rfl))
    exact ⟨y, hy⟩
  refine (XIW_F.holdsAt_ex _ _ _ _ _).mpr ⟨fun x => Classical.choose (hc x), (XIW_rel_eq _ _ _ _).mpr rfl, ?_⟩
  exact (XIW_F.holdsAt_all _ _ _ _ _).mpr fun x _ => Classical.choose_spec (hc x)

/-! ## Polymorphic Leibniz laws -/

/-- The predicate of a polymorphic Leibniz law, at its two types. -/
theorem XIW_evalP {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XIW_F.U.TEnv n)
    (env : XIW_F.U.Env Γ ρ) (a b : Code XIW_B) (x : XIW_U.El a) (y : XIW_U.El b) :
    HEq (XIW_F.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y)) (XIW_F.eval P ρ env) := by
  have e1 : XIW_F.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y) =
      XIW_F.eval (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) :=
    XIW_F.eval_wk tv0 (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) y
  have e2 : XIW_F.eval (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) =
      XIW_F.eval P.twk.twk (scons b (scons a ρ)) env := XIW_F.eval_wk tv1 P.twk.twk (scons b (scons a ρ)) env x
  exact (heq_of_eq (e1.trans e2)).trans ((XIW_F.eval_twk P.twk b (scons a ρ) env).trans (XIW_F.eval_twk P a ρ env))

theorem XIW_evalP1 {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XIW_F.U.TEnv n)
    (env : XIW_F.U.Env Γ ρ) (a b : Code XIW_B) (x : XIW_U.El a) (y : XIW_U.El b) (w : Bool) :
    XIW_F.HoldsAt (.app (.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (.var (.there .here))) (scons b (scons a ρ))
      ((env, x), y) w ↔ XIW_F.eval P ρ env a x w := by
  have h1 : HEq (XIW_F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (scons b (scons a ρ)) ((env, x), y))
      (XIW_F.eval P ρ env a) :=
    (XIW_F.heq_eval_tapp ((P.twk.twk.wk tv1).wk tv0) tv1 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => XIW_U.El c → Bool → Prop) (Q := fun c => XIW_U.El c → Bool → Prop)
        (fun _ => rfl) (XIW_evalP P ρ env a b x y) rfl)
  exact Iff.of_eq (congrFun (congrFun (eq_of_heq h1) x) w)

theorem XIW_evalP0 {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XIW_F.U.TEnv n)
    (env : XIW_F.U.Env Γ ρ) (a b : Code XIW_B) (x : XIW_U.El a) (y : XIW_U.El b) (w : Bool) :
    XIW_F.HoldsAt (.app (.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (.var .here)) (scons b (scons a ρ))
      ((env, x), y) w ↔ XIW_F.eval P ρ env b y w := by
  have h1 : HEq (XIW_F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (scons b (scons a ρ)) ((env, x), y))
      (XIW_F.eval P ρ env b) :=
    (XIW_F.heq_eval_tapp ((P.twk.twk.wk tv1).wk tv0) tv0 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => XIW_U.El c → Bool → Prop) (Q := fun c => XIW_U.El c → Bool → Prop)
        (fun _ => rfl) (XIW_evalP P ρ env a b x y) rfl)
  exact Iff.of_eq (congrFun (congrFun (eq_of_heq h1) y) w)

/-- A polymorphic predicate does not tell apart the same value at two types with the same
`≈`-key. -/
theorem XIW_poly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XIW_F.U.TEnv n)
    (env : XIW_F.U.Env Γ ρ) (henv : XIW_F.EnvAdm Γ ρ true env) (a b : Code XIW_B) (hab : XIW_T a = XIW_T b)
    (x : XIW_U.El a) (y : XIW_U.El b) (hxy : HEq x y) :
    XIW_F.eval P ρ env a x true → XIW_F.eval P ρ env b y true := by
  have hrel := XIW_Inv.fundamental P ρ ρ (XIW_F.homRs ρ) true (fun i => XIW_Inv.refl true (ρ i)) env env
    (KInv.EnvRel_indep XIW_F.hom XIW_Inv Γ ρ ρ _ true env env henv) true trivial a b
    (fun _ x y => HEq x y) ⟨hab, fun _ _ _ => Iff.rfl⟩ true trivial x y hxy true trivial
  exact hrel.mp

/-- LL≡/≈ holds, for every polymorphic predicate, with parameters. -/
theorem XIW_Bridge {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : XIW_F.Valid (Bridge P) := by
  intro ρ _ env henv
  refine (XIW_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XIW_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XIW_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XIW_F.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (XIW_F.holdsAt_imp _ _ _ _ _).mpr fun h => (XIW_F.holdsAt_imp _ _ _ _ _).mpr fun hPx => ?_
  obtain ⟨h1, h2⟩ := (XIW_F.holdsAt_conj _ _ _ _ _).mp h
  have hab : XIW_T a = XIW_T b := (XIW_F.holdsAt_teq _ _ _ _ _).mp h2
  have hxy : HEq x y := ((XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mp h1).2
  exact (XIW_evalP0 P ρ env a b x y true).mpr
    (XIW_poly P ρ env henv a b hab x y hxy ((XIW_evalP1 P ρ env a b x y true).mp hPx))

/-- The predicate `λγ.λz.(γ ≈ e)`. -/
theorem XIW_PredE (ρ : XIW_F.U.TEnv 0) (a : Code XIW_B) (x : XIW_U.El a) (w : Bool) :
    XIW_F.eval PredE ρ () a x w ↔ XIW_T a = XIW_T .e :=
  XIW_F.holdsAt_teq (Γ := Ctx.nil.text.ext tv0) tv0 tyE (scons a ρ) ((), x) w

/-- The entity and the item of `p` are identified at the actual world, but only the first is of a
type `≈ e`. -/
theorem XIW_not_LLPoly : ¬ XIW_F.Valid (LLPoly PredE) := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XIW_F.holdsAt_tall _ _ _ _).mp ((XIW_F.holdsAt_tall _ _ _ _).mp h .e trivial) (.base .p) trivial
  have h2 := (XIW_F.holdsAt_all _ _ _ _ _).mp ((XIW_F.holdsAt_all _ _ _ _ _).mp h1 () rfl) () rfl
  have h3 := (XIW_F.holdsAt_imp _ _ _ _ _).mp h2 ((XIW_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ⟨rfl, HEq.rfl⟩)
  have h4 := (XIW_F.holdsAt_imp _ _ _ _ _).mp h3
    ((XIW_evalP1 PredE _ () .e (.base .p) () () true).mpr ((XIW_PredE _ .e () true).mpr rfl))
  have e := (XIW_PredE _ (.base .p) () true).mp ((XIW_evalP0 PredE _ () .e (.base .p) () () true).mp h4)
  exact absurd e (by decide)

end Kr
end PIF
