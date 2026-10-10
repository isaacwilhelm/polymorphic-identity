import PIBF

/-!
# A Kripke model of PIᶜ with NI× and Int≈ but not Ext≈

`𝔐_k,ie`: three worlds `0, 1, 2`; the actual world `0` sees all three, and `1` and `2` see only
themselves. Entities are booleans, and there is one base type `d`, whose items are booleans too;
identity of entities, and of items of `d`, is equality at every world. So `A := t → e` and
`B := t → d` name the same set of functions. An item of `A` at the actual world must respect
agreement of propositions at world `1` and at world `2`, so it is constant; at world `1`, the
function `f₁` sending `p` to whether `p` is true at `1` is an item, though it is not constant.

`≈` is identity of types. Items of one type are identified at a world when they are identical
there. Besides that, an item of `A` and an item of `B` are identified, at every world, when they
have the same graph and that graph is an item of `A` at the actual world.

At the actual world, `A` and `B` are coextensive: every item of either is a constant function,
identified with the same constant function of the other. But `A` and `B` are distinct, so Ext≈
fails. Int≈ holds: at world `1`, `f₁` is an item of `A` identified with nothing of type `B`, since
its graph is not an item at the actual world. Identity across types does not depend on the world,
and identity within a type persists, so NI× holds.

Since identity within a type is identity at the world, the frame validates Classicism at every
world, and so every theorem of PIᶜ (Bool, IdId, NI≡, NI≈, TNec, TCBF, Nec, CBF, LL≡/≈, Truth,
⊤≢⊥, Cantor, WCong). It also validates Inj≈, Recovery, ND≈, TBF, T and Slogan. It refutes
Disjoint, Cong, PCong, PExt, Twin, Haecceitism, LL≡-Poly, Collapse, ND×, PropExt≡, the Barcan
formula (every item of `A` at the actual world is necessarily constant, but `f₁` is an item of `A`
at world `1`) and Functional Choice (no item of `t → e` at the actual world picks out the truth
value of each proposition, since such items are constant).
-/
set_option autoImplicit false

namespace PIF
namespace Kr
open Tm

def UIE : Univ where
  W := Fin 3
  w0 := 0
  R := fun w u => w = u ∨ w = 0
  Rrefl := fun _ => Or.inl rfl
  Rtrans := by
    intro u v w h1 h2
    rcases h1 with rfl | h1
    · exact h2
    · exact Or.inr h1
  E := Bool
  Base := Unit
  B := fun _ => Bool
  neE := ⟨true⟩
  neB := fun _ => ⟨true⟩
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

/-- `A := t → e`. -/
abbrev ieA : Code Unit := .arr .t .e
/-- `B := t → d`. -/
abbrev ieB : Code Unit := .arr .t (.base ())

/-- The set that `A` and `B` both name. -/
abbrev GIE : Type := (Fin 3 → Prop) → Bool

/-- The graph of an item of `A` or of `B`. -/
def toGIE : (a : Code Unit) → UIE.El a → Option GIE
  | .arr .t .e, f => some f
  | .arr .t (.base _), f => some f
  | _, _ => none

theorem toGIE_resp : ∀ (a : Code Unit) (u : UIE.W) (x x' : UIE.El a), UIE.rel a u x x' → toGIE a x = toGIE a x'
  | .arr .t .e, u, _, _, h => congrArg some (funext fun p => h u (UIE.Rrefl u) p p (fun _ _ => Iff.rfl))
  | .arr .t (.base _), u, _, _, h => congrArg some (funext fun p => h u (UIE.Rrefl u) p p (fun _ _ => Iff.rfl))
  | .e, _, _, _, _ => rfl
  | .t, _, _, _, _ => rfl
  | .base _, _, _, _, _ => rfl
  | .arr .e _, _, _, _, _ => rfl
  | .arr (.base _) _, _, _, _, _ => rfl
  | .arr (.arr _ _) _, _, _, _, _ => rfl
  | .arr .t .t, _, _, _, _ => rfl
  | .arr .t (.arr _ _), _, _, _, _ => rfl

theorem toGIE_some : ∀ (a : Code Unit) (x : UIE.El a) (f : GIE), toGIE a x = some f → a = ieA ∨ a = ieB
  | .arr .t .e, _, _, _ => Or.inl rfl
  | .arr .t (.base ()), _, _, _ => Or.inr rfl
  | .e, _, _, h => nomatch h
  | .t, _, _, h => nomatch h
  | .base _, _, _, h => nomatch h
  | .arr .e _, _, _, h => nomatch h
  | .arr (.base _) _, _, _, h => nomatch h
  | .arr (.arr _ _) _, _, _, h => nomatch h
  | .arr .t .t, _, _, h => nomatch h
  | .arr .t (.arr _ _), _, _, h => nomatch h

/-- Two items of `A` or of `B` with one graph, which is an item of `A` at the actual world, are
identical at every world. -/
theorem toGIE_rel : ∀ (a : Code Unit) (x z : UIE.El a) (f : GIE) (w : UIE.W), toGIE a x = some f →
    toGIE a z = some f → UIE.rel ieA UIE.w0 f f → UIE.rel a w x z
  | .arr .t .e, x, z, f, w, hx, hz, hf => by
    have e1 : x = f := Option.some.inj hx
    have e2 : z = f := Option.some.inj hz
    subst e1; subst e2
    exact UIE.rel_mono ieA UIE.w0 w _ _ (Or.inr rfl) hf
  | .arr .t (.base _), x, z, f, w, hx, hz, hf => by
    have e1 : x = f := Option.some.inj hx
    have e2 : z = f := Option.some.inj hz
    subst e1; subst e2
    exact UIE.rel_mono ieA UIE.w0 w _ _ (Or.inr rfl) hf
  | .e, _, _, _, _, h, _, _ => nomatch h
  | .t, _, _, _, _, h, _, _ => nomatch h
  | .base _, _, _, _, _, h, _, _ => nomatch h
  | .arr .e _, _, _, _, _, h, _, _ => nomatch h
  | .arr (.base _) _, _, _, _, _, h, _, _ => nomatch h
  | .arr (.arr _ _) _, _, _, _, _, h, _, _ => nomatch h
  | .arr .t .t, _, _, _, _, h, _, _ => nomatch h
  | .arr .t (.arr _ _), _, _, _, _, h, _, _ => nomatch h

/-- Identity at a world in `𝔐_k,ie`. -/
def eqvIE (a b : Code Unit) (x : UIE.El a) (y : UIE.El b) (w : UIE.W) : Prop :=
  (∃ h : a = b, UIE.rel b w (cast (congrArg UIE.El h) x) y) ∨
  (a ≠ b ∧ ∃ f : GIE, toGIE a x = some f ∧ toGIE b y = some f ∧ UIE.rel ieA UIE.w0 f f)

theorem eqvIE_resp (u : UIE.W) (a b : Code Unit) (x x' : UIE.El a) (y y' : UIE.El b)
    (hx : UIE.rel a u x x') (hy : UIE.rel b u y y') : eqvIE a b x y u ↔ eqvIE a b x' y' u := by
  constructor
  · rintro (⟨h, hr⟩ | ⟨hne, f, h1, h2, h3⟩)
    · subst h
      exact Or.inl ⟨rfl, UIE.rel_trans _ u _ _ _ (UIE.rel_trans _ u _ _ _ (UIE.rel_symm _ u _ _ hx) hr) hy⟩
    · exact Or.inr ⟨hne, f, (toGIE_resp a u x x' hx).symm.trans h1, (toGIE_resp b u y y' hy).symm.trans h2, h3⟩
  · rintro (⟨h, hr⟩ | ⟨hne, f, h1, h2, h3⟩)
    · subst h
      exact Or.inl ⟨rfl, UIE.rel_trans _ u _ _ _ (UIE.rel_trans _ u _ _ _ hx hr) (UIE.rel_symm _ u _ _ hy)⟩
    · exact Or.inr ⟨hne, f, (toGIE_resp a u x x' hx).trans h1, (toGIE_resp b u y y' hy).trans h2, h3⟩

theorem eqvIE_same (a : Code Unit) (x y : UIE.El a) (w : UIE.W) : eqvIE a a x y w ↔ UIE.rel a w x y := by
  constructor
  · rintro (⟨_, hr⟩ | ⟨hne, _⟩)
    · exact hr
    · exact absurd rfl hne
  · intro h; exact Or.inl ⟨rfl, h⟩

theorem eqvIE_symm {a b : Code Unit} {x : UIE.El a} {y : UIE.El b} {w : UIE.W} (h : eqvIE a b x y w) :
    eqvIE b a y x w := by
  rcases h with ⟨e, r⟩ | ⟨n, f, hx, hy, hf⟩
  · subst e; exact Or.inl ⟨rfl, UIE.rel_symm _ w _ _ r⟩
  · exact Or.inr ⟨fun e => n e.symm, f, hy, hx, hf⟩

theorem eqvIE_trans {a b c : Code Unit} {x : UIE.El a} {y : UIE.El b} {z : UIE.El c} {w : UIE.W}
    (h1 : eqvIE a b x y w) (h2 : eqvIE b c y z w) : eqvIE a c x z w := by
  rcases h1 with ⟨e1, r1⟩ | ⟨n1, f, hx, hy, hf⟩
  · subst e1
    rcases h2 with ⟨e2, r2⟩ | ⟨n2, g, hy', hz, hg⟩
    · subst e2; exact Or.inl ⟨rfl, UIE.rel_trans _ w _ _ _ r1 r2⟩
    · exact Or.inr ⟨n2, g, (toGIE_resp a w x y r1).trans hy', hz, hg⟩
  · rcases h2 with ⟨e2, r2⟩ | ⟨_, g, hy', hz, _⟩
    · subst e2; exact Or.inr ⟨n1, f, hx, (toGIE_resp b w y z r2).symm.trans hy, hf⟩
    · have efg : f = g := Option.some.inj (hy.symm.trans hy')
      subst efg
      by_cases hac : a = c
      · subst hac; exact Or.inl ⟨rfl, toGIE_rel a x z f w hx hz hf⟩
      · exact Or.inr ⟨hac, f, hx, hz, hf⟩

theorem eqvIE_mono {a b : Code Unit} {x : UIE.El a} {y : UIE.El b} {w v : UIE.W} (hv : UIE.R w v)
    (h : eqvIE a b x y w) : eqvIE a b x y v := by
  rcases h with ⟨e, r⟩ | h
  · exact Or.inl ⟨e, UIE.rel_mono _ w v _ _ hv r⟩
  · exact Or.inr h

/-- `𝔐_k,ie`. -/
def MkIEF : Frame where
  U := UIE
  eqv := eqvIE
  teq := fun a b _ => a = b
  eqv_resp := eqvIE_resp

theorem MkIE_heq : ∀ a x y w, MkIEF.eqv a a x y w ↔ MkIEF.U.rel a w x y := eqvIE_same

theorem MkIE_isModelAt : MkIEF.IsModelAt := by
  obtain ⟨h1, h2, h3⟩ := MkIEF.idAx_of (fun a x w hx => (MkIE_heq a x x w).mpr hx)
    (fun _ _ _ _ _ h => eqvIE_symm h) (fun _ _ _ _ _ _ _ h1 h2 => eqvIE_trans h1 h2)
  exact ⟨h1, h2, h3, MkIEF.refTeq_of fun _ _ => rfl, fun Q => MkIEF.llTeq_of_eq (fun _ _ _ h => h) Q⟩

theorem MkIE_LLEqv : MkIEF.Valid LLEqv := fun ρ hρ env henv => MkIEF.LLEqv_of MkIE_heq _ ρ hρ env henv
theorem MkIE_Class : ∀ χ, ClassSch χ → MkIEF.Valid χ :=
  MkIEF.Class_valid MkIE_isModelAt (MkIEF.LLEqv_of MkIE_heq) MkIE_heq

theorem MkIE_Valid_of {φ : Fm Ctx.nil} (h : MkIEF.HoldsAt φ (fun i => i.elim0) () UIE.w0) : MkIEF.Valid φ := by
  intro ρ _ env _
  have e1 : ρ = fun i => i.elim0 := funext fun i => i.elim0
  subst e1
  exact h

/-- Identity persists: within a type by monotonicity, and across types it does not depend on the
world. -/
theorem MkIE_NIX : MkIEF.Valid NIX := by
  refine MkIE_Valid_of ?_
  refine (MkIEF.holdsAt_tall _ _ _ _).mpr fun a _ => (MkIEF.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MkIEF.holdsAt_all _ _ _ _ _).mpr fun x _ => (MkIEF.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (MkIEF.holdsAt_imp _ _ _ _ _).mpr fun h => (MkIEF.box_of MkIE_heq _ _ _ _).mpr fun v hv => ?_
  exact (MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mpr (eqvIE_mono hv ((MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mp h))

/-! ### Int≈ holds, Ext≈ fails -/

open Classical in
/-- The function sending `p` to whether `p` is true at world `1`. -/
noncomputable def f1IE (p : Fin 3 → Prop) : Bool := if p (1 : Fin 3) then true else false

theorem f1IE_pos (p : Fin 3 → Prop) (hp : p (1 : Fin 3)) : f1IE p = true := by
  unfold f1IE
  split
  · rfl
  · rename_i h; exact absurd hp h

theorem f1IE_neg (p : Fin 3 → Prop) (hp : ¬ p (1 : Fin 3)) : f1IE p = false := by
  unfold f1IE
  split
  · rename_i h; exact absurd h hp
  · rfl

/-- At world `1`, `f₁` is an item of `A`. -/
theorem f1IE_adm : UIE.rel ieA (1 : Fin 3) f1IE f1IE := by
  intro v hv p q hpq
  have hv' : v = (1 : Fin 3) := by
    rcases hv with h | h
    · exact h.symm
    · exact absurd h (by decide)
  subst hv'
  have e : p (1 : Fin 3) = q (1 : Fin 3) := propext (hpq (1 : Fin 3) (Or.inl rfl))
  show f1IE p = f1IE q
  unfold f1IE
  rw [e]

/-- At the actual world, `f₁` is not an item of `A`. -/
theorem f1IE_not_adm : ¬ UIE.rel ieA UIE.w0 f1IE f1IE := by
  intro h
  have h2 : f1IE (fun _ => True) = f1IE (fun w => w = (2 : Fin 3)) :=
    h (2 : Fin 3) (Or.inr rfl) (fun _ => True) (fun w => w = (2 : Fin 3)) (fun u hu => by
      rcases hu with rfl | hu
      · exact ⟨fun _ => rfl, fun _ => trivial⟩
      · exact absurd hu (by decide))
  rw [f1IE_pos _ trivial, f1IE_neg _ (show ¬ ((1 : Fin 3) = 2) by decide)] at h2
  exact Bool.noConfusion h2

/-- If every item of `a` is identified with an item of `b` at every world, `a` is `b`. -/
theorem MkIE_boxsub_eq (a b : Code Unit)
    (hsub : ∀ v, UIE.R UIE.w0 v → ∀ x : UIE.El a, UIE.rel a v x x →
      ∃ y : UIE.El b, UIE.rel b v y y ∧ eqvIE a b x y v) : a = b := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨x0, hx0⟩ := UIE.adm_nonempty a
  obtain ⟨y0, _, hxy0⟩ := hsub UIE.w0 (UIE.Rrefl _) x0 (hx0 _)
  rcases hxy0 with ⟨e, _⟩ | ⟨_, g, hg1, _, _⟩
  · exact hne e
  · rcases toGIE_some a x0 g hg1 with rfl | rfl
    · obtain ⟨y, _, hxy⟩ := hsub (1 : Fin 3) (Or.inr rfl) f1IE f1IE_adm
      rcases hxy with ⟨e, _⟩ | ⟨_, g', hg', _, hrel⟩
      · exact hne e
      · have e' : f1IE = g' := Option.some.inj hg'
        subst e'
        exact f1IE_not_adm hrel
    · obtain ⟨y, _, hxy⟩ := hsub (1 : Fin 3) (Or.inr rfl) f1IE f1IE_adm
      rcases hxy with ⟨e, _⟩ | ⟨_, g', hg', _, hrel⟩
      · exact hne e
      · have e' : f1IE = g' := Option.some.inj hg'
        subst e'
        exact f1IE_not_adm hrel

theorem MkIE_sub {n : Nat} {Γ : Ctx n} (ρ : UIE.TEnv n) (env : UIE.Env Γ ρ) (w : UIE.W) (a b : Code Unit)
    (h : MkIEF.HoldsAt (subT : Fm (Γ.text.text)) (scons b (scons a ρ)) env w) :
    ∀ x : UIE.El a, UIE.rel a w x x → ∃ y : UIE.El b, UIE.rel b w y y ∧ eqvIE a b x y w := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := (MkIEF.holdsAt_ex _ _ _ _ _).mp ((MkIEF.holdsAt_all _ _ _ _ _).mp h x hx)
  exact ⟨y, hy, (MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mp hxy⟩

theorem MkIE_IntT : MkIEF.Valid IntT := by
  refine MkIE_Valid_of ?_
  refine (MkIEF.holdsAt_tall _ _ _ _).mpr fun a _ => (MkIEF.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MkIEF.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hs := (MkIEF.box_of MkIE_heq _ _ _ _).mp ((MkIEF.holdsAt_conj _ _ _ _ _).mp h).1
  exact (MkIEF.holdsAt_teq _ _ _ _ _).mpr (MkIE_boxsub_eq a b fun v hv => MkIE_sub _ _ v a b (hs v hv))

/-- At the actual world, each item of `A` is identified with the same function, of type `B`. -/
theorem MkIE_AB (x : GIE) (hx : UIE.rel ieA UIE.w0 x x) : eqvIE ieA ieB x x UIE.w0 :=
  Or.inr ⟨by decide, x, rfl, rfl, hx⟩

theorem MkIE_not_ExtT : ¬ MkIEF.Valid ExtT := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MkIEF.holdsAt_tall _ _ _ _).mp ((MkIEF.holdsAt_tall _ _ _ _).mp h ieA trivial) ieB trivial
  have hc : MkIEF.HoldsAt (Tm.conj (subT : Fm (Ctx.nil.text.text)) supT)
      (scons ieB (scons ieA (fun i => i.elim0))) () UIE.w0 := by
    refine (MkIEF.holdsAt_conj _ _ _ _ _).mpr ⟨?_, ?_⟩
    · refine (MkIEF.holdsAt_all _ _ _ _ _).mpr fun x hx => (MkIEF.holdsAt_ex _ _ _ _ _).mpr ⟨x, hx, ?_⟩
      exact (MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mpr (MkIE_AB x hx)
    · refine (MkIEF.holdsAt_all _ _ _ _ _).mpr fun y hy => (MkIEF.holdsAt_ex _ _ _ _ _).mpr ⟨y, hy, ?_⟩
      exact (MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mpr (MkIE_AB y hy)
  have h2 := (MkIEF.holdsAt_imp _ _ _ _ _).mp h1 hc
  have e : ieA = ieB := (MkIEF.holdsAt_teq _ _ _ _ _).mp h2
  exact absurd e (by decide)

/-! ### Every theorem of PIᶜ is valid

A Kripke frame satisfying the identity axioms at every world, with LL≡ at every world and identity
within a type given by identity at the world, validates Classicism at every world; so, by soundness
at every world, it validates every theorem of PIᶜ at the actual world. -/

namespace KIE
variable (F : Frame)

theorem validAt_closeCtx : ∀ {n : Nat} (Γ : Ctx n) (χ : Fm Γ),
    (∀ w ρ, (∀ i, F.U.D w (ρ i)) → ∀ env, F.EnvAdm Γ ρ w env → F.HoldsAt χ ρ env w) →
    F.ValidAt (closeCtx Γ χ)
  | _, .nil, _, h => h
  | _, .ext Γ σ, χ, h => validAt_closeCtx Γ (Tm.all σ χ) fun w ρ hρ env henv =>
      (F.holdsAt_all σ χ ρ env w).mpr fun v hv => h w ρ hρ (env, v) ⟨henv, F.adm_of_rel σ ρ w v hv⟩
  | _, .text Γ, χ, h => validAt_closeCtx Γ (Tm.tall χ) fun w ρ hρ env henv =>
      (F.holdsAt_tall χ ρ env w).mpr fun a ha => h w (scons a ρ) (fin_cases ha hρ) env henv

/-- Classicism, at every world. -/
theorem Class_validAt (hM : F.IsModelAt) (hLL : F.ValidAt LLEqv)
    (heq : ∀ a x y w, F.eqv a a x y w ↔ F.U.rel a w x y) : ∀ χ, ClassSch χ → F.ValidAt χ := by
  have sound : ∀ {n : Nat} {Γ : Ctx n} {θ : Fm Γ}, PIP Γ θ → F.ValidAt θ := fun h =>
    F.soundnessAt hM (fun χ (e : χ = LLEqv) => e ▸ hLL) h
  rintro _ (⟨n, Γ, φ, ψ, hp, rfl⟩ | ⟨n, Γ, σ, φ, ψ, hp, rfl⟩)
  · refine validAt_closeCtx F Γ _ fun w ρ hρ env henv => ?_
    refine ((F.holdsAt_eqv tyT tyT φ ψ ρ env _).trans (heq _ _ _ _)).mpr ?_
    intro v hv
    exact sound hp v ρ (fun i => F.U.D_mono _ _ _ hv (hρ i)) env (F.EnvAdm_mono ρ _ v hv env henv)
  · refine validAt_closeCtx F Γ _ fun w ρ hρ env henv => ?_
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

/-- Every theorem of PIᶜ is valid. -/
theorem valid_of_PIc (hM : F.IsModelAt) (hLL : F.ValidAt LLEqv)
    (heq : ∀ a x y w, F.eqv a a x y w ↔ F.U.rel a w x y) {φ : Fm Ctx.nil}
    (h : Prov (fun χ => ClassSch χ ∨ χ = LLEqv) Ctx.nil φ) : F.Valid φ := fun ρ hρ env henv =>
  F.soundnessAt hM (fun χ hχ => hχ.elim (Class_validAt F hM hLL heq χ) (fun e => e ▸ hLL)) h _ ρ hρ env henv

end KIE

/-- PIᶜ: Classicism and LL≡. -/
abbrev SIE : Fm Ctx.nil → Prop := fun χ => ClassSch χ ∨ χ = LLEqv

theorem SIE_C : ∀ χ, ClassSch χ → SIE χ := fun _ h => Or.inl h
theorem SIE_LL : SIE LLEqv := Or.inr rfl

theorem MkIE_of_prov {φ : Fm Ctx.nil} (h : Prov SIE Ctx.nil φ) : MkIEF.Valid φ :=
  KIE.valid_of_PIc MkIEF MkIE_isModelAt (MkIEF.LLEqv_of MkIE_heq) MkIE_heq h

open Derive in
theorem MkIE_Bool : ∀ φ, BoolSch φ → MkIEF.Valid φ := fun φ h => MkIE_of_prov (d_Bool_of_Class SIE_C φ h)
theorem MkIE_IdId : MkIEF.Valid IdId := MkIE_of_prov (d_IdId_of_Class SIE_C)
theorem MkIE_NIEqv : MkIEF.Valid NIEqv := MkIE_of_prov (d_NIEqv_of_Class SIE_C SIE_LL)
theorem MkIE_NITeq : MkIEF.Valid NITeq := MkIE_of_prov (d_NITeq_of_Class SIE_C)
theorem MkIE_TNec : MkIEF.Valid TNec := MkIE_of_prov (d_TNec_of_Class SIE_C)
theorem MkIE_TCBF : ∀ χ, TCBFSch χ → MkIEF.Valid χ := fun χ h => MkIE_of_prov (d_TCBF_of_Class SIE_C SIE_LL χ h)
theorem MkIE_Nec : MkIEF.Valid Nec := MkIE_of_prov (d_Nec_of_Class SIE_C)
theorem MkIE_CBF : MkIEF.Valid CBF := MkIE_of_prov (d_CBF_of_Class SIE_C SIE_LL)
theorem MkIE_Bridge (P : Tm Ctx.nil (.pi (.arr (.var fz) .t))) : MkIEF.Valid (Bridge P) :=
  MkIE_of_prov (d_Bridge P SIE_LL)
theorem MkIE_Truth : MkIEF.Valid Truth := MkIE_of_prov (Derive.d_Truth SIE_LL)
theorem MkIE_TopBot : MkIEF.Valid TopBot := MkIE_of_prov (Derive.d_TopBot SIE_LL)
theorem MkIE_Cantor : MkIEF.Valid Cantor := MkIE_of_prov (Derive.d_Cantor SIE_LL)
theorem MkIE_WCong : MkIEF.Valid WCong := MkIE_of_prov (Derive.d_WCong SIE_LL)

/-! ### Principles about `≈`, which is identity of types -/

theorem MkIE_Inj : MkIEF.Valid Inj := by
  refine MkIE_Valid_of ?_
  refine (MkIEF.holdsAt_tall _ _ _ _).mpr fun a _ => (MkIEF.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (MkIEF.holdsAt_tall _ _ _ _).mpr fun c _ => (MkIEF.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MkIEF.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code Unit) = .arr b d := (MkIEF.holdsAt_teq _ _ _ _ _).mp h
  exact (MkIEF.holdsAt_conj _ _ _ _ _).mpr ⟨(MkIEF.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).1,
    (MkIEF.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).2⟩

theorem MkIE_Recovery : MkIEF.Valid Recovery := by
  refine MkIE_Valid_of ?_
  refine (MkIEF.holdsAt_tall _ _ _ _).mpr fun a _ => (MkIEF.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (MkIEF.holdsAt_tall _ _ _ _).mpr fun c _ => (MkIEF.holdsAt_tall _ _ _ _).mpr fun d _ => ?_
  refine (MkIEF.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have e : (Code.arr a c : Code Unit) = .arr b d :=
    (MkIEF.holdsAt_teq _ _ _ _ _).mp ((MkIEF.holdsAt_conj _ _ _ _ _).mp h).1
  exact (MkIEF.holdsAt_teq _ _ _ _ _).mpr (Code.arr.inj e).2

theorem MkIE_NDTeq : MkIEF.Valid NDTeq := by
  refine MkIE_Valid_of ?_
  refine (MkIEF.holdsAt_tall _ _ _ _).mpr fun a _ => (MkIEF.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MkIEF.holdsAt_imp _ _ _ _ _).mpr fun hn => (MkIEF.box_of MkIE_heq _ _ _ _).mpr fun v _ => ?_
  refine (MkIEF.holdsAt_neg _ _ _ _).mpr fun ht => (MkIEF.holdsAt_neg _ _ _ _).mp hn ?_
  have e : a = b := (MkIEF.holdsAt_teq _ _ _ _ v).mp ht
  exact (MkIEF.holdsAt_teq _ _ _ _ _).mpr e

/-- With constant domains of types, the Barcan formula for types holds. -/
theorem MkIE_TBF : ∀ χ, TBFSch χ → MkIEF.Valid χ := by
  rintro _ ⟨φ, rfl⟩
  refine MkIE_Valid_of ?_
  refine (MkIEF.holdsAt_imp _ _ _ _ _).mpr fun h => (MkIEF.box_of MkIE_heq _ _ _ _).mpr fun v hv => ?_
  refine (MkIEF.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  exact (MkIEF.box_of MkIE_heq _ _ _ _).mp ((MkIEF.holdsAt_tall _ _ _ _).mp h a trivial) v hv

/-! ### Modal principles -/

theorem MkIE_TAx : MkIEF.Valid TAx := by
  refine MkIE_Valid_of ?_
  refine (MkIEF.holdsAt_all _ _ _ _ _).mpr fun p _ => (MkIEF.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  exact (MkIEF.box_of MkIE_heq _ _ _ _).mp h UIE.w0 (UIE.Rrefl _)

/-- The proposition true just at the actual world is not necessary. -/
theorem MkIE_not_Collapse : ¬ MkIEF.Valid Collapse := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MkIEF.holdsAt_all _ _ _ _ _).mp h (fun (w : Fin 3) => w = 0) (fun _ _ => Iff.rfl)
  have h2 := (MkIEF.box_of MkIE_heq _ _ _ _).mp ((MkIEF.holdsAt_imp _ _ _ _ _).mp h1 rfl) (1 : Fin 3) (Or.inr rfl)
  have h3 : (1 : Fin 3) = 0 := h2
  exact absurd h3 (by decide)

/-- `⊤` and the proposition false just at the actual world are distinct, but identical at world `1`. -/
theorem MkIE_not_NDX : ¬ MkIEF.Valid NDX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MkIEF.holdsAt_tall _ _ _ _).mp ((MkIEF.holdsAt_tall _ _ _ _).mp h .t trivial) .t trivial
  have h2 := (MkIEF.holdsAt_all _ _ _ _ _).mp ((MkIEF.holdsAt_all _ _ _ _ _).mp h1 (fun _ => True)
    (fun _ _ => Iff.rfl)) (fun (w : Fin 3) => w = 1) (fun _ _ => Iff.rfl)
  refine (MkIEF.holdsAt_neg _ _ _ _).mp ((MkIEF.box_of MkIE_heq _ _ _ _).mp ((MkIEF.holdsAt_imp _ _ _ _ _).mp h2
    ((MkIEF.holdsAt_neg _ _ _ _).mpr fun he => ?_)) (1 : Fin 3) (Or.inr rfl)) ?_
  · have he' := (MkIE_heq .t _ _ _).mp ((MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mp he)
    have h3 : True ↔ (0 : Fin 3) = 1 := he' (0 : Fin 3) (Or.inl rfl)
    exact absurd (h3.mp trivial) (by decide)
  · refine (MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mpr ((MkIE_heq .t _ _ _).mpr fun u hu => ?_)
    rcases hu with rfl | hu
    · exact ⟨fun _ => rfl, fun _ => trivial⟩
    · exact absurd hu (by decide)

/-- `⊤` and the proposition false just at world `1` are equivalent but not identical. -/
theorem MkIE_not_PropExt : ¬ MkIEF.Valid PropExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MkIEF.holdsAt_all _ _ _ _ _).mp ((MkIEF.holdsAt_all _ _ _ _ _).mp h (fun _ => True)
    (fun _ _ => Iff.rfl)) (fun (w : Fin 3) => w ≠ 1) (fun _ _ => Iff.rfl)
  have h2 := (MkIEF.holdsAt_imp _ _ _ _ _).mp h1 ((MkIEF.holdsAt_iff _ _ _ _ _).mpr
    (show True ↔ (0 : Fin 3) ≠ 1 from ⟨fun _ => by decide, fun _ => trivial⟩))
  have h3 := (MkIE_heq .t _ _ _).mp ((MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mp h2)
  have h4 : True ↔ (1 : Fin 3) ≠ 1 := h3 (1 : Fin 3) (Or.inr rfl)
  exact h4.mp trivial rfl

/-! ### Principles about identity across types -/

/-- The constant function. -/
def kIE : GIE := fun _ => true

theorem kIE_adm (w : UIE.W) : UIE.rel ieA w kIE kIE := fun _ _ _ _ _ => rfl

/-- `A` and `B` are distinct, but their constant functions are identified. -/
theorem MkIE_not_Disjoint : ¬ MkIEF.Valid Disjoint := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MkIEF.holdsAt_tall _ _ _ _).mp ((MkIEF.holdsAt_tall _ _ _ _).mp h ieA trivial) ieB trivial
  have h2 := (MkIEF.holdsAt_imp _ _ _ _ _).mp h1 ((MkIEF.holdsAt_neg _ _ _ _).mpr fun ht => by
    have e : ieA = ieB := (MkIEF.holdsAt_teq _ _ _ _ _).mp ht
    exact absurd e (by decide))
  have h3 := (MkIEF.holdsAt_all _ _ _ _ _).mp ((MkIEF.holdsAt_all _ _ _ _ _).mp h2 kIE (kIE_adm _)) kIE (kIE_adm _)
  exact (MkIEF.holdsAt_neg _ _ _ _).mp h3 ((MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mpr (MkIE_AB kIE (kIE_adm _)))

/-- No entity is identified with anything of another type. -/
theorem MkIE_Slogan : MkIEF.Valid Slogan := by
  refine MkIE_Valid_of ?_
  refine (MkIEF.holdsAt_all _ _ _ _ _).mpr fun x _ => (MkIEF.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MkIEF.holdsAt_all _ _ _ _ _).mpr fun y _ => (MkIEF.holdsAt_neg _ _ _ _).mpr fun hxy => ?_
  rcases (MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mp hxy with ⟨h, _⟩ | ⟨_, f, hf, _, _⟩
  · exact nomatch h
  · exact nomatch hf

/-- The constant functions of `A` and `B` are identified, but their values, of types `e` and `d`,
are not. -/
theorem MkIE_not_Cong : ¬ MkIEF.Valid Cong := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MkIEF.holdsAt_tall _ _ _ _).mp ((MkIEF.holdsAt_tall _ _ _ _).mp ((MkIEF.holdsAt_tall _ _ _ _).mp
    ((MkIEF.holdsAt_tall _ _ _ _).mp h .t trivial) .t trivial) .e trivial) (.base ()) trivial
  have h2 := (MkIEF.holdsAt_all _ _ _ _ _).mp ((MkIEF.holdsAt_all _ _ _ _ _).mp ((MkIEF.holdsAt_all _ _ _ _ _).mp
    ((MkIEF.holdsAt_all _ _ _ _ _).mp h1 kIE (kIE_adm _)) kIE (kIE_adm _)) (fun _ => True) (fun _ _ => Iff.rfl))
    (fun _ => True) (fun _ _ => Iff.rfl)
  have h3 := (MkIEF.holdsAt_imp _ _ _ _ _).mp h2 ((MkIEF.holdsAt_conj _ _ _ _ _).mpr
    ⟨(MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mpr (MkIE_AB kIE (kIE_adm _)),
     (MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mpr ((MkIE_heq .t _ _ _).mpr fun _ _ => Iff.rfl)⟩)
  rcases (MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mp h3 with ⟨e, _⟩ | ⟨_, f, hf, _, _⟩
  · exact nomatch e
  · exact nomatch hf

theorem MkIE_not_PCong : ¬ MkIEF.Valid PCong := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MkIEF.holdsAt_tall _ _ _ _).mp ((MkIEF.holdsAt_tall _ _ _ _).mp
    ((MkIEF.holdsAt_tall _ _ _ _).mp h .t trivial) .e trivial) (.base ()) trivial
  have h2 := (MkIEF.holdsAt_all _ _ _ _ _).mp ((MkIEF.holdsAt_all _ _ _ _ _).mp
    ((MkIEF.holdsAt_all _ _ _ _ _).mp h1 kIE (kIE_adm _)) kIE (kIE_adm _)) (fun _ => True) (fun _ _ => Iff.rfl)
  have h3 := (MkIEF.holdsAt_imp _ _ _ _ _).mp h2 ((MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mpr (MkIE_AB kIE (kIE_adm _)))
  rcases (MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mp h3 with ⟨e, _⟩ | ⟨_, f, hf, _, _⟩
  · exact nomatch e
  · exact nomatch hf

/-- No entity is identified with an item of another type. -/
theorem MkIE_not_Twin : ¬ MkIEF.Valid Twin := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MkIEF.holdsAt_all _ _ _ _ _).mp ((MkIEF.holdsAt_tall _ _ _ _).mp h .e trivial) true rfl
  obtain ⟨b, _, h2⟩ := (MkIEF.holdsAt_tex _ _ _ _).mp h1
  have h3 := (MkIEF.holdsAt_conj _ _ _ _ _).mp h2
  obtain ⟨y, _, h4⟩ := (MkIEF.holdsAt_ex _ _ _ _ _).mp h3.2
  rcases (MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mp h4 with ⟨e, _⟩ | ⟨_, f, hf, _, _⟩
  · exact (MkIEF.holdsAt_neg _ _ _ _).mp h3.1 ((MkIEF.holdsAt_teq _ _ _ _ _).mpr e)
  · exact nomatch hf

theorem MkIE_not_Hae : ¬ MkIEF.Valid Hae := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MkIEF.holdsAt_all _ _ _ _ _).mp ((MkIEF.holdsAt_tall _ _ _ _).mp h .e trivial) true rfl
  rcases (MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mp h1 with ⟨e, _⟩ | ⟨_, f, hf, _, _⟩
  · exact nomatch e
  · exact nomatch hf

/-- The constantly-constant functions from `e` to `A` and to `B` agree pointwise up to identity,
but are not identified. -/
theorem MkIE_not_PExt : ¬ MkIEF.Valid PExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MkIEF.holdsAt_tall _ _ _ _).mp ((MkIEF.holdsAt_tall _ _ _ _).mp
    ((MkIEF.holdsAt_tall _ _ _ _).mp h .e trivial) ieA trivial) ieB trivial
  have hk : ∀ w, UIE.rel (.arr .e ieA) w (fun _ => kIE) (fun _ => kIE) := fun _ _ _ _ _ _ => kIE_adm _
  have h2 := (MkIEF.holdsAt_all _ _ _ _ _).mp ((MkIEF.holdsAt_all _ _ _ _ _).mp h1 (fun _ => kIE) (hk _))
    (fun _ => kIE) (hk _)
  have h3 := (MkIEF.holdsAt_imp _ _ _ _ _).mp h2 ((MkIEF.holdsAt_all _ _ _ _ _).mpr fun _ _ =>
    (MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mpr (MkIE_AB kIE (kIE_adm _)))
  rcases (MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mp h3 with ⟨e, _⟩ | ⟨_, f, hf, _, _⟩
  · have e' : (Code.arr .e ieA : Code Unit) = .arr .e ieB := e
    exact absurd e' (by decide)
  · exact nomatch hf

/-! ### The Barcan formula and Functional Choice fail -/

/-- Identity at a world, at `A`, implies equality. -/
theorem relA_eq {v : UIE.W} {x y : GIE} (h : UIE.rel ieA v x y) : x = y :=
  funext fun p => h v (UIE.Rrefl v) p p (fun _ _ => Iff.rfl)

/-- The proposition true at `1` where `p` is, and elsewhere where `q` is. -/
def mixIE (p q : Fin 3 → Prop) : Fin 3 → Prop := fun w => (w = 1 ∧ p w) ∨ (w ≠ 1 ∧ q w)

/-- An item of `A` at the actual world is constant. -/
theorem const_of_adm0 {x : GIE} (h : UIE.rel ieA UIE.w0 x x) (p q : Fin 3 → Prop) : x p = x q := by
  have h1 : x p = x (mixIE p q) := h (1 : Fin 3) (Or.inr rfl) p (mixIE p q) (fun u hu => by
    rcases hu with rfl | hu
    · exact ⟨fun hp => Or.inl ⟨rfl, hp⟩, fun h' => h'.elim (fun h'' => h''.2) (fun h'' => absurd rfl h''.1)⟩
    · exact absurd hu (by decide))
  have h2 : x (mixIE p q) = x q := h (2 : Fin 3) (Or.inr rfl) (mixIE p q) q (fun u hu => by
    rcases hu with rfl | hu
    · exact ⟨fun h' => h'.elim (fun h'' => absurd h''.1 (by decide)) (fun h'' => h''.2),
        fun hq => Or.inr ⟨by decide, hq⟩⟩
    · exact absurd hu (by decide))
  exact h1.trans h2

/-- The property of being constant, of items of `A`. -/
def FIE : UIE.El (.arr ieA .t) := fun (x : GIE) (_ : Fin 3) => ∀ p q, x p = x q

theorem FIE_adm : UIE.rel (.arr ieA .t) UIE.w0 FIE FIE := by
  intro v _ x y hxy
  have e : x = y := relA_eq hxy
  subst e
  exact fun _ _ => Iff.rfl

/-- Every item of `A` at the actual world is necessarily constant, but at world `1`, `f₁` is an
item of `A` which is not constant. -/
theorem MkIE_not_BF : ¬ MkIEF.Valid BF := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MkIEF.holdsAt_all _ _ _ _ _).mp ((MkIEF.holdsAt_tall _ _ _ _).mp h ieA trivial) FIE FIE_adm
  have h2 := (MkIEF.holdsAt_imp _ _ _ _ _).mp h1 ((MkIEF.holdsAt_all _ _ _ _ _).mpr fun _ hx =>
    (MkIEF.box_of MkIE_heq _ _ _ _).mpr fun _ _ => const_of_adm0 hx)
  have h3 := (MkIEF.box_of MkIE_heq _ _ _ _).mp h2 (1 : Fin 3) (Or.inr rfl)
  have h4 := (MkIEF.holdsAt_all _ _ _ _ _).mp h3 f1IE f1IE_adm
  have h5 : ∀ p q : Fin 3 → Prop, f1IE p = f1IE q := h4
  have h6 := h5 (fun _ => True) (fun _ => False)
  rw [f1IE_pos _ trivial, f1IE_neg _ (fun h => h)] at h6
  exact Bool.noConfusion h6

/-- The relation between a proposition and whether it is true. -/
def RIE : UIE.El (.arr .t (.arr .e .t)) := fun (p : Fin 3 → Prop) (y : Bool) (u : Fin 3) => (y = true ↔ p u)

theorem RIE_adm : UIE.rel (.arr .t (.arr .e .t)) UIE.w0 RIE RIE := by
  intro v _ p q hpq v' hv' y y' hyy' u hu
  have e : y = y' := hyy'
  subst e
  exact iff_congr Iff.rfl (hpq u (UIE.Rtrans _ _ _ hv' hu))

/-- Each proposition is related by `R` to an entity, but no item of `t → e` at the actual world
chooses one: such an item is constant. -/
theorem MkIE_not_Choice : ¬ MkIEF.Valid Choice := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MkIEF.holdsAt_all _ _ _ _ _).mp ((MkIEF.holdsAt_tall _ _ _ _).mp
    ((MkIEF.holdsAt_tall _ _ _ _).mp h .t trivial) .e trivial) RIE RIE_adm
  have h2 := (MkIEF.holdsAt_imp _ _ _ _ _).mp h1 ((MkIEF.holdsAt_all _ _ _ _ _).mpr fun p _ => by
    refine (MkIEF.holdsAt_ex _ _ _ _ _).mpr ?_
    rcases Classical.em (p (0 : Fin 3)) with hp | hp
    · exact ⟨true, rfl, show (true = true ↔ p (0 : Fin 3)) from ⟨fun _ => hp, fun _ => rfl⟩⟩
    · exact ⟨false, rfl, show (false = true ↔ p (0 : Fin 3)) from ⟨fun e => Bool.noConfusion e, fun h => absurd h hp⟩⟩)
  obtain ⟨f, hf, h3⟩ := (MkIEF.holdsAt_ex _ _ _ _ _).mp h2
  have hc := const_of_adm0 hf
  have h4 : f (fun _ => True) = true ↔ True := (MkIEF.holdsAt_all _ _ _ _ _).mp h3 (fun _ => True) (fun _ _ => Iff.rfl)
  have h5 : f (fun _ => False) = true ↔ False :=
    (MkIEF.holdsAt_all _ _ _ _ _).mp h3 (fun _ => False) (fun _ _ => Iff.rfl)
  exact h5.mp ((hc _ _).symm.trans (h4.mpr trivial))

/-! ### LL≡-Poly fails -/

open Derive in
set_option maxHeartbeats 4000000 in
theorem PredA_iff1 (x y : GIE) :
    MkIEF.HoldsAt (.app (.tapp ((PredA.twk.twk.wk tv1).wk tv0) tv1) (.var (.there .here)))
      (scons ieB (scons ieA (scons ieA (fun i => i.elim0)))) (((), x), y) UIE.w0 ↔ ieA = ieA := Iff.rfl

open Derive in
set_option maxHeartbeats 4000000 in
theorem PredA_iff0 (x y : GIE) :
    MkIEF.HoldsAt (.app (.tapp ((PredA.twk.twk.wk tv1).wk tv0) tv0) (.var .here))
      (scons ieB (scons ieA (scons ieA (fun i => i.elim0)))) (((), x), y) UIE.w0 ↔ ieB = ieA := Iff.rfl

open Derive in
/-- With `P := λγ.λz.(γ ≈ A)`, the constant functions of `A` and `B` are identified, but only one
has `P`. -/
theorem MkIE_not_LLPoly : ¬ MkIEF.Valid (Tm.tall (LLPoly PredA)) := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MkIEF.holdsAt_tall _ _ _ _).mp ((MkIEF.holdsAt_tall _ _ _ _).mp
    ((MkIEF.holdsAt_tall _ _ _ _).mp h ieA trivial) ieA trivial) ieB trivial
  have h2 := (MkIEF.holdsAt_all _ _ _ _ _).mp ((MkIEF.holdsAt_all _ _ _ _ _).mp h1 kIE (kIE_adm _)) kIE (kIE_adm _)
  have h3 := (MkIEF.holdsAt_imp _ _ _ _ _).mp h2 ((MkIEF.holdsAt_eqv _ _ _ _ _ _ _).mpr (MkIE_AB kIE (kIE_adm _)))
  have h4 := (MkIEF.holdsAt_imp _ _ _ _ _).mp h3 ((PredA_iff1 kIE kIE).mpr rfl)
  exact absurd ((PredA_iff0 kIE kIE).mp h4) (by decide)

end Kr
end PIF
