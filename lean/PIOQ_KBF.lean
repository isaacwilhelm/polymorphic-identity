import PIBF

/-!
# A Kripke model of PIᶜ in which the Barcan formula fails

`𝔐_k,bk`: three worlds `0, 1, 2`; the actual world `0` sees all three, and `1` and `2` see only
themselves. There are four entities `0, 1, 2, 3`; at world `2`, entities `0` and `1` are identical,
and elsewhere identity is equality. Every function on entities which is an item at the actual world
respects identity at world `2`, so it sends `0` and `1` to items identical at `2`. So the constant
proposition `F x := (x 0 ≡₂ x 1)` is necessary of each such `x`. But at world `1` every function is
an item, including one sending `0` and `1` to `2` and `3`; so `∀x F x` fails at world `1`, and
`□∀x F x` fails at the actual world: the Barcan formula fails.
-/
set_option autoImplicit false

namespace PIF
namespace Kr
open Tm

def UBk : Univ where
  W := Fin 3
  w0 := 0
  R := fun w u => w = u ∨ w = 0
  Rrefl := fun _ => Or.inl rfl
  Rtrans := by
    intro u v w h1 h2
    rcases h1 with rfl | h1
    · exact h2
    · exact Or.inr h1
  E := Fin 4
  Base := Empty
  B := Empty.elim
  neE := ⟨0⟩
  neB := fun b => b.elim
  re := fun w x y => x = y ∨ (w = 2 ∧ ((x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)))
  rb := fun _ b => b.elim
  re_refl := fun _ _ => Or.inl rfl
  re_symm := by
    intro w x y h
    rcases h with rfl | ⟨hw, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hw, Or.inr ⟨rfl, rfl⟩⟩
    · exact Or.inr ⟨hw, Or.inl ⟨rfl, rfl⟩⟩
  re_trans := by
    intro w x y z h1 h2
    rcases h1 with rfl | ⟨hw, h1⟩
    · exact h2
    · rcases h2 with rfl | ⟨_, h2⟩
      · exact Or.inr ⟨hw, h1⟩
      · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;>
          first | exact Or.inl rfl | exact absurd h (by decide)
  re_mono := by
    intro w v x y h hxy
    rcases hxy with e | ⟨rfl, hxy⟩
    · exact Or.inl e
    · rcases h with rfl | h
      · exact Or.inr ⟨rfl, hxy⟩
      · exact absurd h (by decide)
  rb_refl := fun _ b => b.elim
  rb_symm := fun _ b => b.elim
  rb_trans := fun _ b => b.elim
  rb_mono := fun _ _ b => b.elim
  D := fun _ _ => True
  D_e := fun _ => trivial
  D_t := fun _ => trivial
  D_arr := fun _ _ _ _ _ => trivial
  D_mono := fun _ _ _ _ _ => trivial

abbrev MbkK : Frame := Frame.simple UBk

/-- Identity at any world implies identity at world `2`. -/
theorem UBk_re_two {w : Fin 3} {x y : Fin 4} (h : UBk.re w x y) : UBk.re (2 : Fin 3) x y := by
  rcases h with e | ⟨_, h⟩
  · exact Or.inl e
  · exact Or.inr ⟨rfl, h⟩

/-- The constant proposition that `x 0` and `x 1` are identical at world `2`. -/
def FBk : UBk.El (.arr (.arr .e .e) .t) :=
  fun (x : Fin 4 → Fin 4) (_ : Fin 3) => UBk.re (2 : Fin 3) (x (0 : Fin 4)) (x (1 : Fin 4))

/-- `F` is an item at every world. -/
theorem FBk_adm (w : Fin 3) : UBk.rel (.arr (.arr .e .e) .t) w FBk FBk := by
  intro v _ x y hxy u _
  have hxy' : ∀ a b : Fin 4, UBk.re v a b → UBk.re v ((x : Fin 4 → Fin 4) a) ((y : Fin 4 → Fin 4) b) :=
    hxy v (UBk.Rrefl v)
  have h0 : UBk.re (2 : Fin 3) ((x : Fin 4 → Fin 4) (0 : Fin 4)) ((y : Fin 4 → Fin 4) (0 : Fin 4)) :=
    UBk_re_two (hxy' (0 : Fin 4) (0 : Fin 4) (Or.inl rfl))
  have h1 : UBk.re (2 : Fin 3) ((x : Fin 4 → Fin 4) (1 : Fin 4)) ((y : Fin 4 → Fin 4) (1 : Fin 4)) :=
    UBk_re_two (hxy' (1 : Fin 4) (1 : Fin 4) (Or.inl rfl))
  show UBk.re (2 : Fin 3) ((x : Fin 4 → Fin 4) (0 : Fin 4)) ((x : Fin 4 → Fin 4) (1 : Fin 4)) ↔
    UBk.re (2 : Fin 3) ((y : Fin 4 → Fin 4) (0 : Fin 4)) ((y : Fin 4 → Fin 4) (1 : Fin 4))
  constructor
  · intro h
    exact UBk.re_trans _ _ _ _ (UBk.re_trans _ _ _ _ (UBk.re_symm _ _ _ h0) h) h1
  · intro h
    exact UBk.re_trans _ _ _ _ (UBk.re_trans _ _ _ _ h0 h) (UBk.re_symm _ _ _ h1)

/-- A function sending `0` and `1` to `2` and `3`. -/
def fBk : UBk.El (.arr .e .e) := fun y : Fin 4 => (y + 2 : Fin 4)

/-- At world `1`, which sees only itself and where identity is equality, `f` is an item. -/
theorem fBk_adm : UBk.rel (.arr .e .e) (1 : Fin 3) fBk fBk := by
  intro v hv a b hab
  have hv' : v = (1 : Fin 3) := by
    rcases hv with h | h
    · exact h.symm
    · exact absurd h (by decide)
  subst hv'
  have e : a = b := by
    rcases hab with e | ⟨hw, _⟩
    · exact e
    · exact absurd hw (by decide)
  subst e
  exact Or.inl rfl

theorem FBk_fBk : ¬ FBk fBk (1 : Fin 3) := by
  show ¬ UBk.re (2 : Fin 3) ((2 : Fin 4)) ((3 : Fin 4))
  intro h
  rcases h with e | ⟨_, ⟨e, _⟩ | ⟨e, _⟩⟩
  · exact absurd e (by decide)
  · exact absurd e (by decide)
  · exact absurd e (by decide)

theorem Mbk_not_BF : ¬ MbkK.Valid BF := by
  refine Frame.simple_not_Valid UBk fun h => ?_
  have h1 := (MbkK.holdsAt_tall _ _ _ _).mp h (.arr .e .e) trivial
  have h2 := (MbkK.holdsAt_all _ _ _ _ _).mp h1 FBk (FBk_adm (0 : Fin 3))
  have h3 := (MbkK.holdsAt_imp _ _ _ _ _).mp h2 ((MbkK.holdsAt_all _ _ _ _ _).mpr fun x hx =>
    (Frame.simple_box UBk _ _ _ _).mpr fun _ _ => by
      have hx' : UBk.rel (.arr .e .e) (0 : Fin 3) x x := hx
      exact hx' (2 : Fin 3) (Or.inr rfl) (0 : Fin 4) (1 : Fin 4) (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩))
  have h4 := (Frame.simple_box UBk _ _ _ _).mp h3 (1 : Fin 3) (Or.inr rfl)
  have h5 := (MbkK.holdsAt_all _ _ _ _ _).mp h4 fBk fBk_adm
  exact FBk_fBk h5

theorem Mbk_not_NDX : ¬ MbkK.Valid NDX := by
  refine Frame.simple_not_Valid UBk fun h => ?_
  have h1 := (MbkK.holdsAt_tall _ _ _ _).mp ((MbkK.holdsAt_tall _ _ _ _).mp h .e trivial) .e trivial
  have h2 := (MbkK.holdsAt_all _ _ _ _ _).mp ((MbkK.holdsAt_all _ _ _ _ _).mp h1 (show Fin 4 from 0) (Or.inl rfl))
    (show Fin 4 from 1) (Or.inl rfl)
  refine (MbkK.holdsAt_neg _ _ _ _).mp ((Frame.simple_box UBk _ _ _ _).mp ((MbkK.holdsAt_imp _ _ _ _ _).mp h2
    ((MbkK.holdsAt_neg _ _ _ _).mpr fun he => ?_)) (2 : Fin 3) (Or.inr rfl)) ?_
  · have he' := (MbkK.holdsAt_eqv _ _ _ _ _ _ _).mp he
    have := (Frame.simple_eqv_same UBk .e (show Fin 4 from 0) (show Fin 4 from 1) (0 : Fin 3)).mp he'
    rcases this with e | ⟨hw, _⟩
    · exact absurd e (by decide)
    · exact absurd hw (by decide)
  · exact (MbkK.holdsAt_eqv _ _ _ _ _ _ _).mpr
      ((Frame.simple_eqv_same UBk .e (show Fin 4 from 0) (show Fin 4 from 1) (2 : Fin 3)).mpr
        (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩))

theorem Mbk_isModelAt : MbkK.IsModelAt := Frame.simple_isModelAt UBk
theorem Mbk_Class : ∀ χ, ClassSch χ → MbkK.Valid χ := Frame.simple_Class UBk
theorem Mbk_LLEqv : MbkK.Valid LLEqv := fun ρ hρ env henv => Frame.simple_LLEqv UBk _ ρ hρ env henv
theorem Mbk_Disjoint : MbkK.Valid Disjoint := Frame.simple_Disjoint UBk
theorem Mbk_Slogan : MbkK.Valid Slogan := Frame.simple_Slogan UBk
theorem Mbk_Cong : MbkK.Valid Cong := Frame.simple_Cong UBk
theorem Mbk_Inj : MbkK.Valid Inj := Frame.simple_Inj UBk
theorem Mbk_Recovery : MbkK.Valid Recovery := Frame.simple_Recovery UBk
theorem Mbk_ExtT : MbkK.Valid ExtT := Frame.simple_ExtT UBk
theorem Mbk_IntT : MbkK.Valid IntT := Frame.simple_IntT UBk
theorem Mbk_NIX : MbkK.Valid NIX := Frame.simple_NIX UBk

theorem Mbk_NDTeq : MbkK.Valid NDTeq := by
  refine Frame.simple_Valid_of UBk ?_
  refine (MbkK.holdsAt_tall _ _ _ _).mpr fun a _ => (MbkK.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (MbkK.holdsAt_imp _ _ _ _ _).mpr fun hn => (Frame.simple_box UBk _ _ _ _).mpr fun v _ => ?_
  refine (MbkK.holdsAt_neg _ _ _ _).mpr fun ht => (MbkK.holdsAt_neg _ _ _ _).mp hn ?_
  have e : a = b := (MbkK.holdsAt_teq _ _ _ _ v).mp ht
  exact (MbkK.holdsAt_teq _ _ _ _ _).mpr e

theorem Mbk_TBF : ∀ χ, TBFSch χ → MbkK.Valid χ := by
  rintro _ ⟨φ, rfl⟩
  refine Frame.simple_Valid_of UBk ?_
  refine (MbkK.holdsAt_imp _ _ _ _ _).mpr fun h => (Frame.simple_box UBk _ _ _ _).mpr fun v hv => ?_
  refine (MbkK.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  exact (Frame.simple_box UBk _ _ _ _).mp ((MbkK.holdsAt_tall _ _ _ _).mp h a trivial) v hv

/-! ### `𝔐_k,bk,h`: as `𝔐_k,bk`, with haecceities added at the actual world -/

abbrev MbkH : Frame := MbkK.hae

theorem UBk_all : ∀ v, UBk.R UBk.w0 v := fun _ => Or.inr rfl

theorem MbkH_heq : ∀ a x y w, MbkH.eqv a a x y w ↔ MbkH.U.rel a w x y :=
  MbkK.hae_heq UBk_all (fun a x y w => Frame.simple_eqv_same UBk a x y w)

theorem MbkH_isModelAt : MbkH.IsModelAt := by
  obtain ⟨h1, h2, h3⟩ := MbkH.idAx_of (fun a x w hx => (MbkH_heq a x x w).mpr hx)
    (MbkK.hae_symm fun _ _ _ _ _ h => Frame.simple_symm UBk h)
    (MbkK.hae_trans fun _ _ _ _ _ _ _ h1 h2 => Frame.simple_trans UBk h1 h2)
  exact ⟨h1, h2, h3, MbkH.refTeq_of fun _ _ => rfl, fun Q => MbkH.llTeq_of_eq (fun _ _ _ h => h) Q⟩

theorem MbkH_LLEqv : MbkH.Valid LLEqv := fun ρ hρ env henv => MbkH.LLEqv_of MbkH_heq _ ρ hρ env henv
theorem MbkH_Class : ∀ χ, ClassSch χ → MbkH.Valid χ :=
  MbkH.Class_valid MbkH_isModelAt (MbkH.LLEqv_of MbkH_heq) MbkH_heq
theorem MbkH_Hae : MbkH.Valid Hae := MbkK.hae_Hae UBk_all (fun a x y w => Frame.simple_eqv_same UBk a x y w)

theorem MbkH_not_BF : ¬ MbkH.Valid BF := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MbkH.holdsAt_tall _ _ _ _).mp h (.arr .e .e) trivial
  have h2 := (MbkH.holdsAt_all _ _ _ _ _).mp h1 FBk (FBk_adm (0 : Fin 3))
  have h3 := (MbkH.holdsAt_imp _ _ _ _ _).mp h2 ((MbkH.holdsAt_all _ _ _ _ _).mpr fun x hx =>
    (MbkH.box_of MbkH_heq _ _ _ _).mpr fun _ _ => by
      have hx' : UBk.rel (.arr .e .e) (0 : Fin 3) x x := hx
      exact hx' (2 : Fin 3) (Or.inr rfl) (0 : Fin 4) (1 : Fin 4) (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩))
  have h4 := (MbkH.box_of MbkH_heq _ _ _ _).mp h3 (1 : Fin 3) (Or.inr rfl)
  have h5 := (MbkH.holdsAt_all _ _ _ _ _).mp h4 fBk fBk_adm
  exact FBk_fBk h5

theorem MbkH_not_NDX : ¬ MbkH.Valid NDX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (MbkH.holdsAt_tall _ _ _ _).mp ((MbkH.holdsAt_tall _ _ _ _).mp h .e trivial) .e trivial
  have h2 := (MbkH.holdsAt_all _ _ _ _ _).mp ((MbkH.holdsAt_all _ _ _ _ _).mp h1 (show Fin 4 from 0) (Or.inl rfl))
    (show Fin 4 from 1) (Or.inl rfl)
  refine (MbkH.holdsAt_neg _ _ _ _).mp ((MbkH.box_of MbkH_heq _ _ _ _).mp ((MbkH.holdsAt_imp _ _ _ _ _).mp h2
    ((MbkH.holdsAt_neg _ _ _ _).mpr fun he => ?_)) (2 : Fin 3) (Or.inr rfl)) ?_
  · have he' := (MbkH_heq .e (show Fin 4 from 0) (show Fin 4 from 1) (0 : Fin 3)).mp
      ((MbkH.holdsAt_eqv _ _ _ _ _ _ _).mp he)
    rcases he' with e | ⟨hw, _⟩
    · exact absurd e (by decide)
    · exact absurd hw (by decide)
  · exact (MbkH.holdsAt_eqv _ _ _ _ _ _ _).mpr
      ((MbkH_heq .e (show Fin 4 from 0) (show Fin 4 from 1) (2 : Fin 3)).mpr (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩))

end Kr
end PIF
