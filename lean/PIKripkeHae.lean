import PIKripkeND

/-!
# Haecceities in Kripke models

Given a Kripke frame in which identity within a type is identity, we add haecceities at the actual
world: there, each item is identified with its haecceity `λy.(y ≡ x)`, which is identified with its
own haecceity in turn, and so on. Two items are identified at the actual world just in case
stripping off haecceities leads to items of one type which are identical there. At the other worlds
nothing changes. Applied to `𝔐_k,bf` and `𝔐_k,nd`, this gives models of PI + Classicism with
Haecceitism, in which the Barcan formula for types, or Necessity of Distinctness, fails.
-/
set_option autoImplicit false

namespace PIF
namespace Kr

def Csz {β : Type} : Code β → Nat
  | .arr a c => Csz a + Csz c + 1
  | _ => 0

namespace Univ
variable (U : Univ)

/-- The haecceity of `z`. -/
def hcy (a : Code U.Base) (z : U.El a) : U.El (.arr a .t) := fun y w => U.rel a w y z

theorem hcy_resp (a : Code U.Base) (z z' : U.El a) (h : U.rel a U.w0 z z') (hall : ∀ v, U.R U.w0 v) :
    U.rel (.arr a .t) U.w0 (U.hcy a z) (U.hcy a z') := by
  intro v _ y y' hy u hu
  have hyu := U.rel_mono a v u y y' hu hy
  have hzu := U.rel_mono a U.w0 u z z' (hall u) h
  exact ⟨fun h1 => U.rel_trans a u _ _ _ (U.rel_trans a u _ _ _ (U.rel_symm a u _ _ hyu) h1) hzu,
    fun h1 => U.rel_trans a u _ _ _ (U.rel_trans a u _ _ _ hyu h1) (U.rel_symm a u _ _ hzu)⟩

theorem hcy_inj (a : Code U.Base) (z z' : U.El a) (hz : U.rel a U.w0 z z)
    (h : U.rel (.arr a .t) U.w0 (U.hcy a z) (U.hcy a z')) : U.rel a U.w0 z z' :=
  (h U.w0 (U.Rrefl _) z z hz U.w0 (U.Rrefl _)).mp hz

open Classical in
/-- The root of an item: strip off haecceities, up to identity at the actual world. -/
noncomputable def Root : (a : Code U.Base) → U.El a → (Σ b : Code U.Base, U.El b)
  | .arr a .t, f => if h : ∃ z, U.rel a U.w0 z z ∧ U.rel (.arr a .t) U.w0 f (U.hcy a z)
      then Root a (Classical.choose h) else ⟨.arr a .t, f⟩
  | a, x => ⟨a, x⟩

/-- Identity of roots, at the actual world. -/
def RR (p q : Σ b : Code U.Base, U.El b) : Prop :=
  ∃ h : p.1 = q.1, U.rel q.1 U.w0 (cast (congrArg U.El h) p.2) q.2

theorem RR_symm {p q : Σ b : Code U.Base, U.El b} (h : U.RR p q) : U.RR q p := by
  obtain ⟨b, x⟩ := p; obtain ⟨c, y⟩ := q
  obtain ⟨e, r⟩ := h
  dsimp only at e; subst e
  exact ⟨rfl, U.rel_symm _ _ _ _ r⟩

theorem RR_trans {p q r : Σ b : Code U.Base, U.El b} (h1 : U.RR p q) (h2 : U.RR q r) : U.RR p r := by
  obtain ⟨b, x⟩ := p; obtain ⟨c, y⟩ := q; obtain ⟨d, z⟩ := r
  obtain ⟨e1, r1⟩ := h1; obtain ⟨e2, r2⟩ := h2
  dsimp only at e1 e2; subst e1; subst e2
  exact ⟨rfl, U.rel_trans _ _ _ _ _ r1 r2⟩

theorem RR_mk {b : Code U.Base} {x y : U.El b} : U.RR ⟨b, x⟩ ⟨b, y⟩ ↔ U.rel b U.w0 x y :=
  ⟨fun ⟨_, r⟩ => r, fun r => ⟨rfl, r⟩⟩

theorem Root_sz : ∀ (a : Code U.Base) (x : U.El a), Csz (U.Root a x).1 ≤ Csz a
  | .arr a .t, f => by
    unfold Root
    split
    · rename_i h; have := Root_sz a (Classical.choose h); simp only [Csz]; omega
    · exact Nat.le_refl _
  | .arr _ .e, _ => Nat.le_refl _
  | .arr _ (.base _), _ => Nat.le_refl _
  | .arr _ (.arr _ _), _ => Nat.le_refl _
  | .e, _ => Nat.le_refl _
  | .t, _ => Nat.le_refl _
  | .base _, _ => Nat.le_refl _

theorem Root_arr_pos (a : Code U.Base) (f : U.El (.arr a .t))
    (h : ∃ z, U.rel a U.w0 z z ∧ U.rel (.arr a .t) U.w0 f (U.hcy a z)) :
    U.Root (.arr a .t) f = U.Root a (Classical.choose h) := by
  conv => lhs; unfold Root
  split
  · rfl
  · contradiction

theorem Root_arr_neg (a : Code U.Base) (f : U.El (.arr a .t))
    (h : ¬ ∃ z, U.rel a U.w0 z z ∧ U.rel (.arr a .t) U.w0 f (U.hcy a z)) :
    U.Root (.arr a .t) f = ⟨.arr a .t, f⟩ := by
  conv => lhs; unfold Root
  split
  · contradiction
  · rfl

theorem Root_other {a : Code U.Base} (x : U.El a) (ha : ∀ b, a ≠ .arr b .t) : U.Root a x = ⟨a, x⟩ := by
  cases a with
  | arr b c =>
    cases c with
    | t => exact absurd rfl (ha b)
    | e => rfl
    | base _ => rfl
    | arr _ _ => rfl
  | e => rfl
  | t => rfl
  | base _ => rfl

theorem Root_adm : ∀ (a : Code U.Base) (x : U.El a), U.rel a U.w0 x x → U.RR (U.Root a x) (U.Root a x)
  | .arr a .t, f, hf => by
    by_cases h : ∃ z, U.rel a U.w0 z z ∧ U.rel (.arr a .t) U.w0 f (U.hcy a z)
    · rw [U.Root_arr_pos a f h]; exact Root_adm a _ (Classical.choose_spec h).1
    · rw [U.Root_arr_neg a f h]; exact U.RR_mk.mpr hf
  | .arr _ .e, _, hf => ⟨rfl, hf⟩
  | .arr _ (.base _), _, hf => ⟨rfl, hf⟩
  | .arr _ (.arr _ _), _, hf => ⟨rfl, hf⟩
  | .e, _, hf => ⟨rfl, hf⟩
  | .t, _, hf => ⟨rfl, hf⟩
  | .base _, _, hf => ⟨rfl, hf⟩

theorem Root_resp : ∀ (a : Code U.Base) (x x' : U.El a), U.rel a U.w0 x x' → U.RR (U.Root a x) (U.Root a x')
  | .arr a .t, f, f', hff => by
    by_cases h : ∃ z, U.rel a U.w0 z z ∧ U.rel (.arr a .t) U.w0 f (U.hcy a z)
    · have h' : ∃ z, U.rel a U.w0 z z ∧ U.rel (.arr a .t) U.w0 f' (U.hcy a z) :=
        let ⟨z, hz, hfz⟩ := h; ⟨z, hz, U.rel_trans _ _ _ _ _ (U.rel_symm _ _ _ _ hff) hfz⟩
      rw [U.Root_arr_pos a f h, U.Root_arr_pos a f' h']
      obtain ⟨hz1, hf1⟩ := Classical.choose_spec h
      obtain ⟨_, hf2⟩ := Classical.choose_spec h'
      refine Root_resp a _ _ (U.hcy_inj a _ _ hz1 ?_)
      exact U.rel_trans _ _ _ _ _ (U.rel_symm _ _ _ _ hf1) (U.rel_trans _ _ _ _ _ hff hf2)
    · have h' : ¬ ∃ z, U.rel a U.w0 z z ∧ U.rel (.arr a .t) U.w0 f' (U.hcy a z) := fun ⟨z, hz, hfz⟩ =>
        h ⟨z, hz, U.rel_trans _ _ _ _ _ hff hfz⟩
      rw [U.Root_arr_neg a f h, U.Root_arr_neg a f' h']
      exact U.RR_mk.mpr hff
  | .arr _ .e, _, _, h => ⟨rfl, h⟩
  | .arr _ (.base _), _, _, h => ⟨rfl, h⟩
  | .arr _ (.arr _ _), _, _, h => ⟨rfl, h⟩
  | .e, _, _, h => ⟨rfl, h⟩
  | .t, _, _, h => ⟨rfl, h⟩
  | .base _, _, _, h => ⟨rfl, h⟩

theorem Root_hcy (hall : ∀ v, U.R U.w0 v) (a : Code U.Base) (z : U.El a) (hz : U.rel a U.w0 z z) :
    U.RR (U.Root (.arr a .t) (U.hcy a z)) (U.Root a z) := by
  have h : ∃ z', U.rel a U.w0 z' z' ∧ U.rel (.arr a .t) U.w0 (U.hcy a z) (U.hcy a z') :=
    ⟨z, hz, U.hcy_resp a z z hz hall⟩
  rw [U.Root_arr_pos a _ h]
  exact U.Root_resp a _ _ (U.rel_symm _ _ _ _ (U.hcy_inj a _ _ hz (Classical.choose_spec h).2))

theorem Root_inj (hall : ∀ v, U.R U.w0 v) : ∀ (a : Code U.Base) (x y : U.El a), U.rel a U.w0 x x → U.rel a U.w0 y y →
    U.RR (U.Root a x) (U.Root a y) → U.rel a U.w0 x y
  | .arr a .t, f, g, hf, hg, hr => by
    by_cases h1 : ∃ z, U.rel a U.w0 z z ∧ U.rel (.arr a .t) U.w0 f (U.hcy a z) <;>
      by_cases h2 : ∃ z, U.rel a U.w0 z z ∧ U.rel (.arr a .t) U.w0 g (U.hcy a z)
    · rw [U.Root_arr_pos a f h1, U.Root_arr_pos a g h2] at hr
      obtain ⟨hz1, hf1⟩ := Classical.choose_spec h1
      obtain ⟨hz2, hg2⟩ := Classical.choose_spec h2
      have hzz := Root_inj hall a _ _ hz1 hz2 hr
      exact U.rel_trans _ _ _ _ _ hf1 (U.rel_trans _ _ _ _ _ (U.hcy_resp a _ _ hzz hall) (U.rel_symm _ _ _ _ hg2))
    · rw [U.Root_arr_pos a f h1, U.Root_arr_neg a g h2] at hr
      have := U.Root_sz a (Classical.choose h1)
      rw [hr.1] at this; simp only [Csz] at this; omega
    · rw [U.Root_arr_neg a f h1, U.Root_arr_pos a g h2] at hr
      have := U.Root_sz a (Classical.choose h2)
      rw [← hr.1] at this; simp only [Csz] at this; omega
    · rw [U.Root_arr_neg a f h1, U.Root_arr_neg a g h2] at hr
      exact U.RR_mk.mp hr
  | .arr _ .e, _, _, _, _, hr => U.RR_mk.mp hr
  | .arr _ (.base _), _, _, _, _, hr => U.RR_mk.mp hr
  | .arr _ (.arr _ _), _, _, _, _, hr => U.RR_mk.mp hr
  | .e, _, _, _, _, hr => U.RR_mk.mp hr
  | .t, _, _, _, _, hr => U.RR_mk.mp hr
  | .base _, _, _, _, _, hr => U.RR_mk.mp hr

/-- Identity at the actual world, with haecceities. -/
def HR (a b : Code U.Base) (x : U.El a) (y : U.El b) : Prop :=
  U.rel a U.w0 x x ∧ U.rel b U.w0 y y ∧ U.RR (U.Root a x) (U.Root b y)

theorem HR_same (hall : ∀ v, U.R U.w0 v) (a : Code U.Base) (x y : U.El a) : U.HR a a x y ↔ U.rel a U.w0 x y :=
  ⟨fun ⟨hx, hy, hr⟩ => U.Root_inj hall a x y hx hy hr,
   fun h => ⟨U.rel_refl_left a _ _ _ h, U.rel_refl_right a _ _ _ h, U.Root_resp a x y h⟩⟩

theorem HR_resp (a b : Code U.Base) (x x' : U.El a) (y y' : U.El b) (hx : U.rel a U.w0 x x')
    (hy : U.rel b U.w0 y y') : U.HR a b x y ↔ U.HR a b x' y' := by
  have r1 := U.Root_resp a x x' hx
  have r2 := U.Root_resp b y y' hy
  constructor
  · rintro ⟨_, _, hr⟩
    exact ⟨U.rel_refl_right a _ _ _ hx, U.rel_refl_right b _ _ _ hy,
      U.RR_trans (U.RR_symm r1) (U.RR_trans hr r2)⟩
  · rintro ⟨_, _, hr⟩
    exact ⟨U.rel_refl_left a _ _ _ hx, U.rel_refl_left b _ _ _ hy,
      U.RR_trans r1 (U.RR_trans hr (U.RR_symm r2))⟩

theorem HR_symm {a b : Code U.Base} {x : U.El a} {y : U.El b} (h : U.HR a b x y) : U.HR b a y x :=
  ⟨h.2.1, h.1, U.RR_symm h.2.2⟩

theorem HR_trans {a b c : Code U.Base} {x : U.El a} {y : U.El b} {z : U.El c} (h1 : U.HR a b x y)
    (h2 : U.HR b c y z) : U.HR a c x z := ⟨h1.1, h2.2.1, U.RR_trans h1.2.2 h2.2.2⟩

end Univ
namespace Frame
variable (F : Frame)

/-- The identity axioms other than LL≈ hold at every world, given the matching facts about items. -/
theorem idAx_of (hr : ∀ a x w, F.U.rel a w x x → F.eqv a a x x w)
    (hs : ∀ a b x y w, F.eqv a b x y w → F.eqv b a y x w)
    (ht : ∀ a b c x y z w, F.eqv a b x y w → F.eqv b c y z w → F.eqv a c x z w) :
    F.ValidAt RefEqv ∧ F.ValidAt SymEqv ∧ F.ValidAt TransEqv := by
  refine ⟨?_, ?_, ?_⟩
  · intro w ρ _ env _
    refine F.holdsAt_tall _ _ _ w |>.mpr fun a _ => (F.holdsAt_all _ _ _ _ w).mpr fun x hx => ?_
    exact (F.holdsAt_eqv _ _ _ _ _ _ w).mpr (hr _ _ _ hx)
  · intro w ρ _ env _
    refine F.holdsAt_tall _ _ _ w |>.mpr fun a _ => F.holdsAt_tall _ _ _ w |>.mpr fun b _ => ?_
    refine (F.holdsAt_all _ _ _ _ w).mpr fun x _ => (F.holdsAt_all _ _ _ _ w).mpr fun y _ => ?_
    refine (F.holdsAt_imp _ _ _ _ w).mpr fun h => ?_
    exact (F.holdsAt_eqv _ _ _ _ _ _ w).mpr (hs _ _ _ _ _ ((F.holdsAt_eqv _ _ _ _ _ _ w).mp h))
  · intro w ρ _ env _
    refine F.holdsAt_tall _ _ _ w |>.mpr fun a _ => F.holdsAt_tall _ _ _ w |>.mpr fun b _ =>
      F.holdsAt_tall _ _ _ w |>.mpr fun c _ => ?_
    refine (F.holdsAt_all _ _ _ _ w).mpr fun x _ => (F.holdsAt_all _ _ _ _ w).mpr fun y _ =>
      (F.holdsAt_all _ _ _ _ w).mpr fun z _ => ?_
    refine (F.holdsAt_imp _ _ _ _ w).mpr fun h => ?_
    have hc := (F.holdsAt_conj _ _ _ _ w).mp h
    have h1 := (F.holdsAt_eqv (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv2 tv1
      (.var (.there (.there .here))) (.var (.there .here)) (scons c (scons b (scons a ρ))) (((env, x), y), z) w).mp hc.1
    have h2 := (F.holdsAt_eqv (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv1 tv0
      (.var (.there .here)) (.var .here) (scons c (scons b (scons a ρ))) (((env, x), y), z) w).mp hc.2
    exact (F.holdsAt_eqv _ _ _ _ _ _ w).mpr (ht _ _ _ _ _ _ _ h1 h2)

theorem refTeq_of (hT : ∀ a w, F.teq a a w) : F.ValidAt RefTeq := by
  intro w ρ _ env _
  exact F.holdsAt_tall _ _ _ w |>.mpr fun a _ => (F.holdsAt_teq _ _ _ _ w).mpr (hT a w)

theorem llTeq_of_eq (hT : ∀ a b w, F.teq a b w → a = b) {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)) :
    F.ValidAt (LLTeq Q) := by
  intro w ρ _ env _
  refine F.holdsAt_tall _ _ _ w |>.mpr fun a _ => F.holdsAt_tall _ _ _ w |>.mpr fun b _ => ?_
  refine (F.holdsAt_imp _ _ _ _ w).mpr fun hab => ?_
  have hab' : a = b := hT a b w ((F.holdsAt_teq (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env w).mp hab)
  subst hab'
  refine (F.holdsAt_imp _ _ _ _ w).mpr fun hq => ?_
  have e1 : HEq (F.eval (Tm.tapp Q.twk.twk tv1) (scons a (scons a ρ)) env) (F.eval Q.twk.twk (scons a (scons a ρ)) env a) :=
    F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv1 (scons a (scons a ρ)) env
  have e2 : HEq (F.eval (Tm.tapp Q.twk.twk tv0) (scons a (scons a ρ)) env) (F.eval Q.twk.twk (scons a (scons a ρ)) env a) :=
    F.heq_eval_tapp (K := Cat.t) Q.twk.twk tv0 (scons a (scons a ρ)) env
  exact cast (F.holdsAt_of_heq (e1.trans e2.symm) w) hq

/-- Add haecceities at the actual world. -/
def hae : Frame where
  U := F.U
  eqv := fun a b x y w => (w = F.U.w0 → F.U.HR a b x y) ∧ (w ≠ F.U.w0 → F.eqv a b x y w)
  teq := F.teq
  eqv_resp := by
    intro u a b x x' y y' hx hy
    have hA : u = F.U.w0 → (F.U.HR a b x y ↔ F.U.HR a b x' y') := fun hw => by
      subst hw; exact F.U.HR_resp a b x x' y y' hx hy
    have hB := F.eqv_resp u a b x x' y y' hx hy
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun hw => (hA hw).mp (h1 hw), fun hw => hB.mp (h2 hw)⟩,
      fun ⟨h1, h2⟩ => ⟨fun hw => (hA hw).mpr (h1 hw), fun hw => hB.mpr (h2 hw)⟩⟩

variable (hall : ∀ v, F.U.R F.U.w0 v) (heq : ∀ a x y w, F.eqv a a x y w ↔ F.U.rel a w x y)
include hall heq

theorem hae_heq : ∀ a x y w, F.hae.eqv a a x y w ↔ F.hae.U.rel a w x y := by
  intro a x y w
  by_cases hw : w = F.U.w0
  · subst hw
    exact ⟨fun h => (F.U.HR_same hall a x y).mp (h.1 rfl),
      fun h => ⟨fun _ => (F.U.HR_same hall a x y).mpr h, fun h' => absurd rfl h'⟩⟩
  · exact ⟨fun h => (heq a x y w).mp (h.2 hw), fun h => ⟨fun h' => absurd h' hw, fun _ => (heq a x y w).mpr h⟩⟩

omit hall heq in
theorem hae_symm (hs : ∀ a b x y w, F.eqv a b x y w → F.eqv b a y x w) :
    ∀ a b x y w, F.hae.eqv a b x y w → F.hae.eqv b a y x w :=
  fun a b x y w ⟨h1, h2⟩ => ⟨fun hw => F.U.HR_symm (h1 hw), fun hw => hs a b x y w (h2 hw)⟩

omit hall heq in
theorem hae_trans (ht : ∀ a b c x y z w, F.eqv a b x y w → F.eqv b c y z w → F.eqv a c x z w) :
    ∀ a b c x y z w, F.hae.eqv a b x y w → F.hae.eqv b c y z w → F.hae.eqv a c x z w :=
  fun _ _ _ _ _ _ w ⟨h1, h2⟩ ⟨k1, k2⟩ => ⟨fun hw => F.U.HR_trans (h1 hw) (k1 hw), fun hw => ht _ _ _ _ _ _ w (h2 hw) (k2 hw)⟩

/-- Haecceitism holds at the actual world. -/
theorem hae_Hae : F.hae.Valid Hae := by
  intro ρ _ env _
  refine (F.hae.holdsAt_tall _ _ _ _).mpr fun a _ => (F.hae.holdsAt_all _ _ _ _ _).mpr fun x hx => ?_
  refine (F.hae.holdsAt_eqv _ _ _ _ _ _ _).mpr ⟨fun _ => ?_, fun h => absurd rfl h⟩
  have hx' : F.U.rel a F.U.w0 x x := hx
  have eL : (fun (y : F.U.El a) (w : F.U.W) => F.hae.eqv a a y x w) = F.U.hcy a x :=
    funext fun y => funext fun w => propext (F.hae_heq hall heq a y x w)
  have key : F.U.HR a (.arr a .t) x (F.U.hcy a x) :=
    ⟨hx', F.U.hcy_resp a x x hx' hall, F.U.RR_symm (F.U.Root_hcy hall a x hx')⟩
  have key' : F.U.HR a (.arr a .t) x (fun (y : F.U.El a) (w : F.U.W) => F.hae.eqv a a y x w) := eL ▸ key
  exact key'

end Frame

end Kr
end PIF

namespace PIF
namespace Kr
open Tm

/-! ## `𝔐_k,bf,h`: Haecceitism without the Barcan formula for types -/

abbrev MbfH : Frame := MbfK.hae

theorem UBF_all : ∀ v, UBF.R UBF.w0 v := fun _ => Or.inl rfl
theorem UND_all : ∀ v, UND.R UND.w0 v := fun _ => Or.inl rfl

theorem MbfH_heq : ∀ a x y w, MbfH.eqv a a x y w ↔ MbfH.U.rel a w x y :=
  MbfK.hae_heq UBF_all (fun a x y w => Frame.simple_eqv_same UBF a x y w)

theorem MbfH_isModelAt : MbfH.IsModelAt := by
  obtain ⟨h1, h2, h3⟩ := MbfH.idAx_of (fun a x w hx => (MbfH_heq a x x w).mpr hx)
    (MbfK.hae_symm fun _ _ _ _ _ h => Frame.simple_symm UBF h)
    (MbfK.hae_trans fun _ _ _ _ _ _ _ h1 h2 => Frame.simple_trans UBF h1 h2)
  exact ⟨h1, h2, h3, MbfH.refTeq_of fun _ _ => rfl, fun Q => MbfH.llTeq_of_eq (fun _ _ _ h => h) Q⟩

theorem MbfH_LLEqv : MbfH.Valid LLEqv := fun ρ hρ env henv => MbfH.LLEqv_of MbfH_heq _ ρ hρ env henv
theorem MbfH_Class : ∀ χ, ClassSch χ → MbfH.Valid χ := MbfH.Class_valid MbfH_isModelAt (MbfH.LLEqv_of MbfH_heq) MbfH_heq
theorem MbfH_Hae : MbfH.Valid Hae := MbfK.hae_Hae UBF_all (fun a x y w => Frame.simple_eqv_same UBF a x y w)

theorem phiBFH_iff (a : Code Unit) (w : Bool) :
    MbfH.HoldsAt phiBF (scons a (fun i => i.elim0)) () w ↔
      ¬ ∀ x : UBF.El a, UBF.rel a w x x → ∀ y : UBF.El a, UBF.rel a w y y → UBF.rel a w x y := by
  refine (MbfH.holdsAt_neg _ _ _ _).trans (not_congr ?_)
  refine (MbfH.holdsAt_all _ _ _ _ _).trans (forall_congr' fun x => imp_congr Iff.rfl ?_)
  refine (MbfH.holdsAt_all _ _ _ _ _).trans (forall_congr' fun y => imp_congr Iff.rfl ?_)
  exact (MbfH.holdsAt_eqv _ _ _ _ _ _ _).trans (MbfH_heq _ _ _ _)

theorem MbfH_not_TBF : ¬ ∀ χ, TBFSch χ → MbfH.Valid χ := fun hv => by
  have h := hv _ ⟨phiBF, rfl⟩ (fun i => i.elim0) (fun i => i.elim0) () trivial
  have hA : MbfH.HoldsAt (tall (boxF phiBF)) (fun i => i.elim0) () UBF.w0 := by
    refine (MbfH.holdsAt_tall _ _ _ _).mpr fun a ha => (MbfH.box_of MbfH_heq _ _ _ _).mpr fun v _ => ?_
    have hna : noBase a := ha.resolve_left (fun h => Bool.noConfusion (h : true = false))
    obtain ⟨x, y, hx, hy, hxy⟩ := two_items a hna
    exact (phiBFH_iff a v).mpr fun h => hxy v (h x (hx v) y (hy v))
  have hB := (MbfH.box_of MbfH_heq _ _ _ _).mp ((MbfH.holdsAt_imp _ _ _ _ _).mp h hA) false (Or.inl rfl)
  have hd := (MbfH.holdsAt_tall _ _ _ _).mp hB (.base ()) (Or.inl rfl)
  exact (phiBFH_iff (.base ()) false).mp hd fun _ _ _ _ => trivial

/-! ## `𝔐_k,nd,h`: Haecceitism without Necessity of Distinctness for types -/

abbrev MndH : Frame := MndK.hae

theorem MndH_heq : ∀ a x y w, MndH.eqv a a x y w ↔ MndH.U.rel a w x y := MndK.hae_heq UND_all MndK_heq

theorem eqvND_symm {a b : Code Unit} {x : UND.El a} {y : UND.El b} {w : Bool} (h : eqvND a b x y w) :
    eqvND b a y x w := ⟨fun hw => (h.1 hw).symm, h.2.1.symm, CR_symm h.2.1 h.2.2⟩

theorem eqvND_trans {a b c : Code Unit} {x : UND.El a} {y : UND.El b} {z : UND.El c} {w : Bool}
    (h : eqvND a b x y w) (k : eqvND b c y z w) : eqvND a c x z w :=
  ⟨fun hw => (h.1 hw).trans (k.1 hw), h.2.1.trans k.2.1, CR_trans h.2.1 k.2.1 h.2.2 k.2.2⟩

/-- The admissible relations of `𝔐_k,nd`, for the frame with haecceities. -/
def ndInvH : KInv MndH where
  Adm := ndInv.Adm
  amono := ndInv.amono
  smono := ndInv.smono
  refl := ndInv.refl
  arrow := ndInv.arrow
  total := ndInv.total
  onto := ndInv.onto
  teq := ndInv.teq
  eqv := by
    intro w a a' b b' S T hS hT u hu x x' y y' hx hy
    by_cases hu0 : u = true
    · subst hu0
      obtain ⟨_, c1, s1⟩ := hS
      obtain ⟨_, c2, s2⟩ := hT
      have ea := c1 true hu rfl
      have eb := c2 true hu rfl
      subst ea; subst eb
      exact MndH.eqv_resp true _ _ x x' y y' ((CR_diag _ _ _ _).mpr ((s1 _ _ _).mp hx))
        ((CR_diag _ _ _ _).mpr ((s2 _ _ _).mp hy))
    · have hk := ndInv.eqv hS hT u hu x x' y y' hx hy
      exact ⟨fun ⟨_, h2⟩ => ⟨fun h => absurd h hu0, fun _ => hk.mp (h2 hu0)⟩,
        fun ⟨_, h2⟩ => ⟨fun h => absurd h hu0, fun _ => hk.mpr (h2 hu0)⟩⟩

theorem MndH_isModelAt : MndH.IsModelAt := by
  obtain ⟨h1, h2, h3⟩ := MndH.idAx_of (fun a x w hx => (MndH_heq a x x w).mpr hx)
    (MndK.hae_symm fun _ _ _ _ _ h => eqvND_symm h)
    (MndK.hae_trans fun _ _ _ _ _ _ _ h1 h2 => eqvND_trans h1 h2)
  refine ⟨h1, h2, h3, MndH.refTeq_of fun _ _ => ⟨fun _ => rfl, rfl⟩, ?_⟩
  intro n Γ Q w ρ _ env henv
  refine MndH.holdsAt_tall _ _ _ w |>.mpr fun a _ => MndH.holdsAt_tall _ _ _ w |>.mpr fun b _ => ?_
  refine (MndH.holdsAt_imp _ _ _ _ w).mpr fun hab => ?_
  obtain ⟨e1, e2⟩ := (MndH.holdsAt_teq (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env w).mp hab
  refine (MndH.holdsAt_imp _ _ _ _ w).mpr fun hq => ?_
  exact ndInvH.llTeq_at Q w ρ env henv a b (CR a b) ⟨e2, fun v hv hv' => e1 (R_true hv hv'), fun _ _ _ => Iff.rfl⟩ hq

theorem MndH_LLEqv : MndH.Valid LLEqv := fun ρ hρ env henv => MndH.LLEqv_of MndH_heq _ ρ hρ env henv
theorem MndH_Class : ∀ χ, ClassSch χ → MndH.Valid χ := MndH.Class_valid MndH_isModelAt (MndH.LLEqv_of MndH_heq) MndH_heq
theorem MndH_Hae : MndH.Valid Hae := MndK.hae_Hae UND_all MndK_heq

theorem MndH_not_NDTeq : ¬ MndH.Valid NDTeq := fun h => by
  have h0 := h (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MndH.holdsAt_tall _ _ _ _).mp ((MndH.holdsAt_tall _ _ _ _).mp h0 .e trivial) (.base ()) trivial
  have h2 := (MndH.holdsAt_imp _ _ _ _ _).mp h1 ((MndH.holdsAt_neg _ _ _ _).mpr fun ht =>
    nomatch ((MndH.holdsAt_teq _ _ _ _ _).mp ht).1 rfl)
  have h3 := (MndH.box_of MndH_heq _ _ _ _).mp h2 false (Or.inl rfl)
  exact (MndH.holdsAt_neg _ _ _ _).mp h3 ((MndH.holdsAt_teq _ _ _ _ _).mpr ⟨(fun h => nomatch h), rfl⟩)

end Kr
end PIF
