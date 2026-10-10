import PIBF

/-!
# A Kripke model of PI in which Functional Choice fails, together with NI≡, NI≈, Nec, TNec and IdId

`𝔐_k,xch`: three worlds `0, 1, 2`; the actual world `0` sees all three, and `1` and `2` see only
themselves. There are four entities `0, 1, 2, 3`; at world `2`, entities `0` and `1` are identical,
and elsewhere identity of entities is equality. There are four base types: `d`, a copy of `e`;
`u₁` and `u₂`, two copies of the booleans (identity is equality); and `n`, with a single item,
which exists only at world `2`.

`≈` is sameness of type once `e → u₂` is replaced by `e → u₁` (as in `𝔐_κ`), except at world `1`,
where no two types are `≈`. So `e → u₁ ≈ e → u₂`, though `u₁` and `u₂` are not `≈`.

`≡` is a parameter of a Kripke frame, which must respect identity at each world. Here:

* Items of types with the same image are identified at a world when they correspond there (for
  items of one type: when they are identical there), except that at world `1` no entity is
  identified with an entity.
* An entity and an item of `d` are identified when they are identical (at the world in question);
  and, at the actual world, an item `f` of `t → e` and an item `g` of `t → d` are identified when
  `g p = f p + 2` for every `p`.

So the identity axioms, and LL≡, hold at the actual world (LL≈ by the Kripke invariance lemma, with
the correspondences between types with the same image as admissible relations), though Ref≡ fails
at world `1`. Soundness holds world by world, so every theorem of PI is valid. But

* NI≡ fails (`0 ≡ 0`, but not at world `1`), and with it Nec and IdId, and so Classicism; NI≈ and
  TNec fail since nothing is `≈` at world `1`; Inj≈ and Recovery fail.
* Functional Choice fails, as in `𝔐_k,ch`: the relation pairing each `x` with `x + 2` at the
  actual world contains no function respecting identity at world `2`.
* BF fails, as in `𝔐_k,bk`; ND× fails since `0` and `1` are identical at world `2`.
* TBF fails: every type at the actual world necessarily has two distinct items, but at world `2`
  the type `n` has only one.
* Ext≈ and Int≈ fail: `e` and `d` are necessarily coextensive, but not `≈`.
* PCong fails: the constant functions `0` of `t → e` and `2` of `t → d` are identified, but their
  values are not.

In any Kripke frame in which the identity axioms and LL≡ hold at the actual world, identity of
propositions there is agreement at every world it sees; so Booleanism, TCBF and CBF hold here.
-/
set_option autoImplicit false

namespace PIF
namespace Kr
open Tm

/-! ### The universe -/

/-- The base types: `d`, a copy of `e`; `n`, with one item, which exists only at world `2`; `u₁` and
`u₂`, two copies of the booleans. -/
inductive XCK_B : Type where
  | d : XCK_B
  | n : XCK_B
  | u1 : XCK_B
  | u2 : XCK_B

/-- The items of the base types. -/
def XCK_BT : XCK_B → Type
  | .d => Fin 4
  | .n => Unit
  | .u1 => Bool
  | .u2 => Bool

/-- Codes not mentioning `n`. -/
def XCK_noN : Code XCK_B → Prop
  | .base .n => False
  | .arr a b => XCK_noN a ∧ XCK_noN b
  | _ => True

/-- Identity of entities at a world: at world `2`, `0` and `1` are identical. -/
def XCK_re (w : Fin 3) (x y : Fin 4) : Prop := x = y ∨ (w = 2 ∧ x.val < 2 ∧ y.val < 2)

theorem XCK_re_refl (w : Fin 3) (x : Fin 4) : XCK_re w x x := Or.inl rfl

theorem XCK_re_symm {w : Fin 3} {x y : Fin 4} (h : XCK_re w x y) : XCK_re w y x :=
  h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.1, h.2.2, h.2.1⟩)

theorem XCK_re_trans {w : Fin 3} {x y z : Fin 4} (h1 : XCK_re w x y) (h2 : XCK_re w y z) : XCK_re w x z := by
  rcases h1 with rfl | ⟨hw, hx, hy⟩
  · exact h2
  · rcases h2 with rfl | ⟨_, _, hz⟩
    · exact Or.inr ⟨hw, hx, hy⟩
    · exact Or.inr ⟨hw, hx, hz⟩

theorem XCK_re_mono {w v : Fin 3} {x y : Fin 4} (h : w = v ∨ w = 0) (hxy : XCK_re w x y) : XCK_re v x y := by
  rcases hxy with e | ⟨hw, hx, hy⟩
  · exact Or.inl e
  · subst hw
    rcases h with h | h
    · subst h; exact Or.inr ⟨rfl, hx, hy⟩
    · exact absurd h (by decide)

theorem XCK_re0 {x y : Fin 4} (h : XCK_re 0 x y) : x = y :=
  h.elim id (fun h => absurd h.1 (by decide))

theorem XCK_re_two {w : Fin 3} {x y : Fin 4} (h : XCK_re w x y) : XCK_re 2 x y :=
  h.elim Or.inl (fun h => Or.inr ⟨rfl, h.2⟩)

/-- Identity of items of the base types at a world. -/
def XCK_rb (w : Fin 3) : (b : XCK_B) → XCK_BT b → XCK_BT b → Prop
  | .d => fun x y => XCK_re w x y
  | .n => fun _ _ => True
  | .u1 => fun x y => x = y
  | .u2 => fun x y => x = y

def XCK_U : Univ where
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
  Base := XCK_B
  B := XCK_BT
  neE := ⟨0⟩
  neB := fun b => match b with
    | .d => ⟨(0 : Fin 4)⟩
    | .n => ⟨()⟩
    | .u1 => ⟨true⟩
    | .u2 => ⟨true⟩
  re := XCK_re
  rb := XCK_rb
  re_refl := XCK_re_refl
  re_symm := fun _ _ _ h => XCK_re_symm h
  re_trans := fun _ _ _ _ h1 h2 => XCK_re_trans h1 h2
  re_mono := fun _ _ _ _ h hxy => XCK_re_mono h hxy
  rb_refl := by
    intro w b x
    cases b
    · exact XCK_re_refl w x
    · exact trivial
    · exact rfl
    · exact rfl
  rb_symm := by
    intro w b x y h
    cases b
    · exact XCK_re_symm h
    · exact trivial
    · exact Eq.symm h
    · exact Eq.symm h
  rb_trans := by
    intro w b x y z h1 h2
    cases b
    · exact XCK_re_trans h1 h2
    · exact trivial
    · exact Eq.trans h1 h2
    · exact Eq.trans h1 h2
  rb_mono := by
    intro w v b x y h hxy
    cases b
    · exact XCK_re_mono h hxy
    · exact trivial
    · exact hxy
    · exact hxy
  D := fun w a => w = 2 ∨ XCK_noN a
  D_e := fun _ => Or.inr trivial
  D_t := fun _ => Or.inr trivial
  D_arr := by
    intro w a c ha hc
    rcases ha with ha | ha
    · exact Or.inl ha
    · rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr ⟨ha, hc⟩
  D_mono := by
    intro w v a h ha
    rcases ha with ha | ha
    · subst ha
      rcases h with h | h
      · exact Or.inl h.symm
      · exact absurd h (by decide)
    · exact Or.inr ha

/-! ### The image of a type: `e → u₂` becomes `e → u₁` -/

/-- The codomain of the image of an arrow type, given the images of its two types. -/
def XCK_fix : Code XCK_B → Code XCK_B → Code XCK_B
  | .e, .base .u2 => .base .u1
  | .e, .base .d => .base .d
  | .e, .base .n => .base .n
  | .e, .base .u1 => .base .u1
  | .e, .e => .e
  | .e, .t => .t
  | .e, .arr a b => .arr a b
  | .t, Y => Y
  | .base _, Y => Y
  | .arr _ _, Y => Y

theorem XCK_fix_cases : ∀ X Y : Code XCK_B,
    (X = .e ∧ Y = .base .u2 ∧ XCK_fix X Y = .base .u1) ∨ XCK_fix X Y = Y
  | .e, .base .u2 => Or.inl ⟨rfl, rfl, rfl⟩
  | .e, .base .d => Or.inr rfl
  | .e, .base .n => Or.inr rfl
  | .e, .base .u1 => Or.inr rfl
  | .e, .e => Or.inr rfl
  | .e, .t => Or.inr rfl
  | .e, .arr _ _ => Or.inr rfl
  | .t, _ => Or.inr rfl
  | .base _, _ => Or.inr rfl
  | .arr _ _, _ => Or.inr rfl

/-- The image of a type. -/
def XCK_N : Code XCK_B → Code XCK_B
  | .e => .e
  | .t => .t
  | .base b => .base b
  | .arr a c => .arr (XCK_N a) (XCK_fix (XCK_N a) (XCK_N c))

theorem XCK_N_e : ∀ {a : Code XCK_B}, XCK_N a = .e → a = .e
  | .e, _ => rfl
  | .t, h => nomatch h
  | .base _, h => nomatch h
  | .arr _ _, h => nomatch h

theorem XCK_N_t : ∀ {a : Code XCK_B}, XCK_N a = .t → a = .t
  | .e, h => nomatch h
  | .t, _ => rfl
  | .base _, h => nomatch h
  | .arr _ _, h => nomatch h

theorem XCK_N_base {b : XCK_B} : ∀ {a : Code XCK_B}, XCK_N a = .base b → a = .base b
  | .e, h => nomatch h
  | .t, h => nomatch h
  | .base _, h => h
  | .arr _ _, h => nomatch h

theorem XCK_N_arr {X Y : Code XCK_B} : ∀ {a : Code XCK_B}, XCK_N a = .arr X Y →
    ∃ a1 c1, a = .arr a1 c1 ∧ XCK_N a1 = X ∧ XCK_fix X (XCK_N c1) = Y
  | .e, h => nomatch h
  | .t, h => nomatch h
  | .base _, h => nomatch h
  | .arr a1 c1, h => by
    injection h with h1 h2
    subst h1
    exact ⟨a1, c1, rfl, rfl, h2⟩

/-- Base types with the same items. -/
def XCK_XSb : XCK_B → XCK_B → Prop
  | .d, .d => True
  | .n, .n => True
  | .u1, .u1 => True
  | .u2, .u2 => True
  | .u1, .u2 => True
  | .u2, .u1 => True
  | _, _ => False

/-- Types with the same items, and the same identity at each world. -/
def XCK_XS : Code XCK_B → Code XCK_B → Prop
  | .e, .e => True
  | .t, .t => True
  | .base b, .base b' => XCK_XSb b b'
  | .arr a c, .arr a' c' => XCK_XS a a' ∧ XCK_XS c c'
  | _, _ => False

theorem XCK_N_XS : ∀ a a' : Code XCK_B, XCK_N a = XCK_N a' → XCK_XS a a' := by
  intro a
  induction a with
  | e => intro a' h; rw [XCK_N_e h.symm]; trivial
  | t => intro a' h; rw [XCK_N_t h.symm]; trivial
  | base b => intro a' h; rw [XCK_N_base h.symm]; cases b <;> trivial
  | arr a c iha ihc =>
    intro a' h
    obtain ⟨a1, c1, rfl, h1, h2⟩ := XCK_N_arr h.symm
    refine ⟨iha a1 h1.symm, ?_⟩
    rcases XCK_fix_cases (XCK_N a) (XCK_N c) with ⟨_, hY, hf⟩ | hf <;>
      rcases XCK_fix_cases (XCK_N a) (XCK_N c1) with ⟨_, hY', hf'⟩ | hf'
    · exact ihc c1 (hY.trans hY'.symm)
    · have e1 : XCK_N c1 = .base .u1 := hf'.symm.trans (h2.trans hf)
      rw [XCK_N_base hY, XCK_N_base e1]; trivial
    · have e1 : XCK_N c = .base .u1 := hf.symm.trans (h2.symm.trans hf')
      rw [XCK_N_base hY', XCK_N_base e1]; trivial
    · exact ihc c1 (hf.symm.trans (h2.symm.trans hf'))

theorem XCK_ElXS : ∀ a a' : Code XCK_B, XCK_XS a a' → XCK_U.El a = XCK_U.El a' := by
  intro a
  induction a with
  | e => intro a' h; cases a' <;> first | rfl | exact False.elim h
  | t => intro a' h; cases a' <;> first | rfl | exact False.elim h
  | base b =>
    intro a' h
    cases a' with
    | base b' => cases b <;> cases b' <;> first | rfl | exact False.elim h
    | _ => exact False.elim h
  | arr a c iha ihc =>
    intro a' h
    cases a' with
    | arr a' c' =>
      show (XCK_U.El a → XCK_U.El c) = (XCK_U.El a' → XCK_U.El c')
      rw [iha a' h.1, ihc c' h.2]
    | _ => exact False.elim h

/-- Types with the same image have the same items. -/
theorem XCK_ElN (a b : Code XCK_B) (h : XCK_N a = XCK_N b) : XCK_U.El a = XCK_U.El b :=
  XCK_ElXS a b (XCK_N_XS a b h)

theorem XCK_cast_fun {A A' C C' : Type} (hA : A = A') (hC : C = C') (h : (A → C) = (A' → C')) (f : A → C)
    (y : A') : cast h f y = cast hC (f (cast hA.symm y)) := by
  subst hA; subst hC; rfl

/-- Identity at a world is preserved by the correspondence between types with the same items. -/
theorem XCK_rel_cast : ∀ (a a' : Code XCK_B), XCK_XS a a' → ∀ (h : XCK_U.El a = XCK_U.El a') (w : Fin 3)
    (x y : XCK_U.El a), XCK_U.rel a w x y ↔ XCK_U.rel a' w (cast h x) (cast h y) := by
  intro a
  induction a with
  | e => intro a' hs h w x y; cases a' <;> first | exact Iff.rfl | exact False.elim hs
  | t => intro a' hs h w x y; cases a' <;> first | exact Iff.rfl | exact False.elim hs
  | base b =>
    intro a' hs h w x y
    cases a' with
    | base b' => cases b <;> cases b' <;> first | exact Iff.rfl | exact False.elim hs
    | _ => exact False.elim hs
  | arr a c iha ihc =>
    intro a' hs h w f g
    cases a' with
    | arr a' c' =>
      have ha := XCK_ElXS a a' hs.1
      have hc := XCK_ElXS c c' hs.2
      constructor
      · intro H v hv x' y' hxy'
        have e1 : cast h f x' = cast hc (f (cast ha.symm x')) := XCK_cast_fun ha hc h f x'
        have e2 : cast h g y' = cast hc (g (cast ha.symm y')) := XCK_cast_fun ha hc h g y'
        show XCK_U.rel c' v (cast h f x') (cast h g y')
        rw [e1, e2]
        refine (ihc c' hs.2 hc v _ _).mp (H v hv _ _ ((iha a' hs.1 ha v _ _).mpr ?_))
        rw [cast_cast, cast_cast, cast_eq, cast_eq]
        exact hxy'
      · intro H v hv x y hxy
        have H' := H v hv (cast ha x) (cast ha y) ((iha a' hs.1 ha v x y).mp hxy)
        have e1 : cast h f (cast ha x) = cast hc (f (cast ha.symm (cast ha x))) := XCK_cast_fun ha hc h f _
        have e2 : cast h g (cast ha y) = cast hc (g (cast ha.symm (cast ha y))) := XCK_cast_fun ha hc h g _
        have H'' : XCK_U.rel c' v (cast h f (cast ha x)) (cast h g (cast ha y)) := H'
        rw [e1, e2, cast_cast, cast_cast, cast_eq, cast_eq] at H''
        exact (ihc c' hs.2 hc v _ _).mpr H''
    | _ => exact False.elim hs

/-- The same, for types with the same image. -/
theorem XCK_rc {a b : Code XCK_B} (hN : XCK_N a = XCK_N b) (h : XCK_U.El a = XCK_U.El b) {w : Fin 3}
    {x y : XCK_U.El a} : XCK_U.rel a w x y ↔ XCK_U.rel b w (cast h x) (cast h y) :=
  XCK_rel_cast a b (XCK_N_XS a b hN) h w x y

/-! ### Identity across types -/

/-- The keys by which items of different types are matched. -/
abbrev XCK_K : Type := Fin 4 ⊕ ((Fin 3 → Prop) → Fin 4)

/-- `x ↦ x + 2`. -/
def XCK_sh (i : Fin 4) : Fin 4 := i + 2

theorem XCK_sh_inj : ∀ i j : Fin 4, XCK_sh i = XCK_sh j → i = j := by decide

/-- The key of an item: entities and items of `d` are their own keys; an item `f` of `t → e` has
key `f`, and an item `g` of `t → d` has key `p ↦ g p + 2`. -/
def XCK_key : (a : Code XCK_B) → XCK_U.El a → Option XCK_K
  | .e, x => some (.inl x)
  | .base .d, x => some (.inl x)
  | .base .n, _ => none
  | .base .u1, _ => none
  | .base .u2, _ => none
  | .t, _ => none
  | .arr .t .e, f => some (.inr f)
  | .arr .t (.base .d), g => some (.inr (fun p => XCK_sh (g p)))
  | .arr .t (.base .n), _ => none
  | .arr .t (.base .u1), _ => none
  | .arr .t (.base .u2), _ => none
  | .arr .t .t, _ => none
  | .arr .t (.arr _ _), _ => none
  | .arr .e _, _ => none
  | .arr (.base _) _, _ => none
  | .arr (.arr _ _) _, _ => none

/-- When two keys match at a world. -/
def XCK_gm (w : Fin 3) : XCK_K → XCK_K → Prop
  | .inl i, .inl j => XCK_re w i j
  | .inr f, .inr g => w = 0 ∧ f = g
  | .inl _, .inr _ => False
  | .inr _, .inl _ => False

theorem XCK_gm_symm {w : Fin 3} : ∀ {k k' : XCK_K}, XCK_gm w k k' → XCK_gm w k' k
  | .inl _, .inl _, h => XCK_re_symm h
  | .inr _, .inr _, h => ⟨h.1, h.2.symm⟩
  | .inl _, .inr _, h => h.elim
  | .inr _, .inl _, h => h.elim

theorem XCK_gm_trans {w : Fin 3} : ∀ {k1 k2 k3 : XCK_K}, XCK_gm w k1 k2 → XCK_gm w k2 k3 → XCK_gm w k1 k3
  | .inl _, .inl _, .inl _, h1, h2 => XCK_re_trans h1 h2
  | .inr _, .inr _, .inr _, h1, h2 => ⟨h1.1, h1.2.trans h2.2⟩
  | .inl _, .inr _, _, h1, _ => h1.elim
  | .inr _, .inl _, _, h1, _ => h1.elim
  | .inl _, .inl _, .inr _, _, h2 => h2.elim
  | .inr _, .inr _, .inl _, _, h2 => h2.elim

/-- Two optional keys match the same keys at a world. -/
def XCK_kr (u : Fin 3) (o o' : Option XCK_K) : Prop :=
  ∀ h, (∃ k, o = some k ∧ XCK_gm u k h) ↔ (∃ k, o' = some k ∧ XCK_gm u k h)

theorem XCK_kr_inl {u : Fin 3} {i j : Fin 4} (hij : XCK_re u i j) :
    XCK_kr u (some (.inl i)) (some (.inl j)) := by
  intro h
  constructor
  · rintro ⟨k, hk, hg⟩
    cases hk
    refine ⟨.inl j, rfl, ?_⟩
    cases h with
    | inl l => exact XCK_re_trans (XCK_re_symm hij) hg
    | inr _ => exact hg
  · rintro ⟨k, hk, hg⟩
    cases hk
    refine ⟨.inl i, rfl, ?_⟩
    cases h with
    | inl l => exact XCK_re_trans hij hg
    | inr _ => exact hg

theorem XCK_kr_inr {u : Fin 3} {f g : (Fin 3 → Prop) → Fin 4} (hfg : u = 0 → f = g) :
    XCK_kr u (some (.inr f)) (some (.inr g)) := by
  intro h
  constructor
  · rintro ⟨k, hk, hg⟩
    cases hk
    refine ⟨.inr g, rfl, ?_⟩
    cases h with
    | inl _ => exact hg
    | inr f2 => exact ⟨hg.1, (hfg hg.1).symm.trans hg.2⟩
  · rintro ⟨k, hk, hg⟩
    cases hk
    refine ⟨.inr f, rfl, ?_⟩
    cases h with
    | inl _ => exact hg
    | inr f2 => exact ⟨hg.1, (hfg hg.1).trans hg.2⟩

/-- Keys respect identity at each world. -/
theorem XCK_key_resp : ∀ (a : Code XCK_B) (u : Fin 3) (x x' : XCK_U.El a), XCK_U.rel a u x x' →
    XCK_kr u (XCK_key a x) (XCK_key a x')
  | .e, _, _, _, hx => XCK_kr_inl hx
  | .base .d, _, _, _, hx => XCK_kr_inl hx
  | .base .n, _, _, _, _ => fun _ => Iff.rfl
  | .base .u1, _, _, _, _ => fun _ => Iff.rfl
  | .base .u2, _, _, _, _ => fun _ => Iff.rfl
  | .t, _, _, _, _ => fun _ => Iff.rfl
  | .arr .t .e, _, f, f', hf => XCK_kr_inr fun hu => by
      subst hu
      funext p
      exact XCK_re0 (hf (0 : Fin 3) (Or.inl rfl) p p (fun _ _ => Iff.rfl))
  | .arr .t (.base .d), _, g, g', hg => XCK_kr_inr fun hu => by
      subst hu
      funext p
      exact congrArg XCK_sh (XCK_re0 (hg (0 : Fin 3) (Or.inl rfl) p p (fun _ _ => Iff.rfl)))
  | .arr .t (.base .n), _, _, _, _ => fun _ => Iff.rfl
  | .arr .t (.base .u1), _, _, _, _ => fun _ => Iff.rfl
  | .arr .t (.base .u2), _, _, _, _ => fun _ => Iff.rfl
  | .arr .t .t, _, _, _, _ => fun _ => Iff.rfl
  | .arr .t (.arr _ _), _, _, _, _ => fun _ => Iff.rfl
  | .arr .e _, _, _, _, _ => fun _ => Iff.rfl
  | .arr (.base _) _, _, _, _, _ => fun _ => Iff.rfl
  | .arr (.arr _ _) _, _, _, _, _ => fun _ => Iff.rfl

/-- At the actual world, items of one type with matching keys are identical. -/
theorem XCK_key_inj0 : ∀ (a : Code XCK_B) (x z : XCK_U.El a) (k k' : XCK_K), XCK_key a x = some k →
    XCK_key a z = some k' → XCK_gm 0 k k' → XCK_U.rel a (0 : Fin 3) x x → XCK_U.rel a (0 : Fin 3) x z
  | .e, _, _, _, _, hx, hz, hg, _ => by cases hx; cases hz; exact hg
  | .base .d, _, _, _, _, hx, hz, hg, _ => by cases hx; cases hz; exact hg
  | .base .n, _, _, _, _, hx, _, _, _ => by cases hx
  | .base .u1, _, _, _, _, hx, _, _, _ => by cases hx
  | .base .u2, _, _, _, _, hx, _, _, _ => by cases hx
  | .t, _, _, _, _, hx, _, _, _ => by cases hx
  | .arr .t .e, _, _, _, _, hx, hz, hg, hxx => by
      cases hx; cases hz
      obtain ⟨_, e⟩ := hg
      subst e
      exact hxx
  | .arr .t (.base .d), x, z, _, _, hx, hz, hg, hxx => by
      cases hx; cases hz
      have e : x = z := funext fun p => XCK_sh_inj _ _ (congrFun hg.2 p)
      subst e
      exact hxx
  | .arr .t (.base .n), _, _, _, _, hx, _, _, _ => by cases hx
  | .arr .t (.base .u1), _, _, _, _, hx, _, _, _ => by cases hx
  | .arr .t (.base .u2), _, _, _, _, hx, _, _, _ => by cases hx
  | .arr .t .t, _, _, _, _, hx, _, _, _ => by cases hx
  | .arr .t (.arr _ _), _, _, _, _, hx, _, _, _ => by cases hx
  | .arr .e _, _, _, _, _, hx, _, _, _ => by cases hx
  | .arr (.base _) _, _, _, _, _, hx, _, _, _ => by cases hx
  | .arr (.arr _ _) _, _, _, _, _, hx, _, _, _ => by cases hx

/-- A type whose items have keys is the only type with its image. -/
theorem XCK_key_rigid : ∀ (a : Code XCK_B) (x : XCK_U.El a) (k : XCK_K), XCK_key a x = some k →
    ∀ a', XCK_N a' = XCK_N a → a' = a
  | .e, _, _, _, _, h => XCK_N_e h
  | .base .d, _, _, _, _, h => XCK_N_base h
  | .base .n, _, _, hx, _, _ => by cases hx
  | .base .u1, _, _, hx, _, _ => by cases hx
  | .base .u2, _, _, hx, _, _ => by cases hx
  | .t, _, _, hx, _, _ => by cases hx
  | .arr .t .e, _, _, _, _, h => by
      obtain ⟨a1, c1, rfl, h1, h2⟩ := XCK_N_arr h
      rw [XCK_N_t h1, XCK_N_e h2]
  | .arr .t (.base .d), _, _, _, _, h => by
      obtain ⟨a1, c1, rfl, h1, h2⟩ := XCK_N_arr h
      rw [XCK_N_t h1, XCK_N_base h2]
  | .arr .t (.base .n), _, _, hx, _, _ => by cases hx
  | .arr .t (.base .u1), _, _, hx, _, _ => by cases hx
  | .arr .t (.base .u2), _, _, hx, _, _ => by cases hx
  | .arr .t .t, _, _, hx, _, _ => by cases hx
  | .arr .t (.arr _ _), _, _, hx, _, _ => by cases hx
  | .arr .e _, _, _, hx, _, _ => by cases hx
  | .arr (.base _) _, _, _, hx, _, _ => by cases hx
  | .arr (.arr _ _) _, _, _, hx, _, _ => by cases hx

/-- An item of `β → t` has no key. -/
theorem XCK_key_pred : ∀ (b : Code XCK_B) (y : XCK_U.El (.arr b .t)), XCK_key (.arr b .t) y = none
  | .e, _ => rfl
  | .t, _ => rfl
  | .base _, _ => rfl
  | .arr _ _, _ => rfl

/-! ### Identity -/

/-- Identity at a world. -/
def XCK_eqv (a b : Code XCK_B) (x : XCK_U.El a) (y : XCK_U.El b) (w : Fin 3) : Prop :=
  (∃ h : XCK_N a = XCK_N b, XCK_U.rel b w (cast (XCK_ElN a b h) x) y ∧ (w = 1 → XCK_N a ≠ .e)) ∨
  (XCK_N a ≠ XCK_N b ∧ XCK_U.rel a w x x ∧ XCK_U.rel b w y y ∧
    ∃ k k', XCK_key a x = some k ∧ XCK_key b y = some k' ∧ XCK_gm w k k')

theorem XCK_eqv_resp (u : Fin 3) (a b : Code XCK_B) (x x' : XCK_U.El a) (y y' : XCK_U.El b)
    (hx : XCK_U.rel a u x x') (hy : XCK_U.rel b u y y') : XCK_eqv a b x y u ↔ XCK_eqv a b x' y' u := by
  constructor
  · rintro (⟨h, hr, s⟩ | ⟨hne, _, _, k, k', hk, hk', hg⟩)
    · have hx' := (XCK_rc h (XCK_ElN a b h)).mp hx
      exact Or.inl ⟨h, XCK_U.rel_trans _ u _ _ _ (XCK_U.rel_trans _ u _ _ _ (XCK_U.rel_symm _ u _ _ hx') hr) hy, s⟩
    · obtain ⟨k1, hk1, hg1⟩ := (XCK_key_resp a u x x' hx k').mp ⟨k, hk, hg⟩
      obtain ⟨k2, hk2, hg2⟩ := (XCK_key_resp b u y y' hy k1).mp ⟨k', hk', XCK_gm_symm hg1⟩
      exact Or.inr ⟨hne, XCK_U.rel_refl_right _ u _ _ hx, XCK_U.rel_refl_right _ u _ _ hy, k1, k2, hk1, hk2,
        XCK_gm_symm hg2⟩
  · rintro (⟨h, hr, s⟩ | ⟨hne, _, _, k, k', hk, hk', hg⟩)
    · have hx' := (XCK_rc h (XCK_ElN a b h)).mp hx
      exact Or.inl ⟨h, XCK_U.rel_trans _ u _ _ _ (XCK_U.rel_trans _ u _ _ _ hx' hr) (XCK_U.rel_symm _ u _ _ hy), s⟩
    · obtain ⟨k1, hk1, hg1⟩ := (XCK_key_resp a u x x' hx k').mpr ⟨k, hk, hg⟩
      obtain ⟨k2, hk2, hg2⟩ := (XCK_key_resp b u y y' hy k1).mpr ⟨k', hk', XCK_gm_symm hg1⟩
      exact Or.inr ⟨hne, XCK_U.rel_refl_left _ u _ _ hx, XCK_U.rel_refl_left _ u _ _ hy, k1, k2, hk1, hk2,
        XCK_gm_symm hg2⟩

/-- `𝔐_k,xch`. -/
def XCK_F : Frame where
  U := XCK_U
  eqv := XCK_eqv
  teq := fun a b (w : Fin 3) => w ≠ 1 ∧ XCK_N a = XCK_N b
  eqv_resp := XCK_eqv_resp

theorem XCK_heq0 (a : Code XCK_B) (x y : XCK_U.El a) : XCK_F.eqv a a x y (0 : Fin 3) ↔ XCK_U.rel a (0 : Fin 3) x y := by
  constructor
  · rintro (⟨_, hr, _⟩ | ⟨hne, _⟩)
    · exact hr
    · exact absurd rfl hne
  · intro h; exact Or.inl ⟨rfl, h, fun h1 => absurd h1 (by decide)⟩

theorem XCK_eqv_of_rel {a : Code XCK_B} {x y : XCK_U.El a} {w : Fin 3} (h : XCK_U.rel a w x y)
    (hw : w = 1 → XCK_N a ≠ .e) : XCK_F.eqv a a x y w := Or.inl ⟨rfl, h, hw⟩

/-- Within a type, identity implies identity at the world in question. -/
theorem XCK_eqv_sub_rel (a : Code XCK_B) (x y : XCK_U.El a) (w : Fin 3) (h : XCK_F.eqv a a x y w) :
    XCK_U.rel a w x y := by
  rcases h with ⟨_, hr, _⟩ | ⟨hne, _⟩
  · exact hr
  · exact absurd rfl hne

/-- At world `1`, no entity is identified with an entity. -/
theorem XCK_eqv_e1 (x y : XCK_U.El .e) : ¬ XCK_F.eqv .e .e x y (1 : Fin 3) := by
  rintro (⟨_, _, h⟩ | ⟨hne, _⟩)
  · exact h rfl rfl
  · exact hne rfl

theorem XCK_eqv_symm {a b : Code XCK_B} {x : XCK_U.El a} {y : XCK_U.El b} {w : Fin 3} (h : XCK_F.eqv a b x y w) :
    XCK_F.eqv b a y x w := by
  rcases h with ⟨e, r, s⟩ | ⟨n, hx, hy, k, k', h1, h2, hg⟩
  · refine Or.inl ⟨e.symm, ?_, fun hw => e ▸ s hw⟩
    have r' := (XCK_rc e.symm (XCK_ElN b a e.symm)).mp r
    rw [cast_cast, cast_eq] at r'
    exact XCK_U.rel_symm _ w _ _ r'
  · exact Or.inr ⟨fun e => n e.symm, hy, hx, k', k, h2, h1, XCK_gm_symm hg⟩

theorem XCK_eqv_trans0 {a b c : Code XCK_B} {x : XCK_U.El a} {y : XCK_U.El b} {z : XCK_U.El c}
    (h1 : XCK_F.eqv a b x y (0 : Fin 3)) (h2 : XCK_F.eqv b c y z (0 : Fin 3)) : XCK_F.eqv a c x z (0 : Fin 3) := by
  have s0 : ∀ X : Code XCK_B, (0 : Fin 3) = 1 → XCK_N X ≠ .e := fun _ h => absurd h (by decide)
  rcases h1 with ⟨e1, r1, _⟩ | ⟨n1, hx, hy, k1, k2, hk1, hk2, hg1⟩
  · rcases h2 with ⟨e2, r2, _⟩ | ⟨n2, _, hz, k2', k3, hk2', hk3, hg2⟩
    · refine Or.inl ⟨e1.trans e2, ?_, s0 a⟩
      have r1' := (XCK_rc e2 (XCK_ElN b c e2)).mp r1
      rw [cast_cast] at r1'
      exact XCK_U.rel_trans _ _ _ _ _ r1' r2
    · have eab := XCK_key_rigid b y k2' hk2' a e1
      subst eab
      have r1' : XCK_U.rel a (0 : Fin 3) x y := r1
      obtain ⟨k1', hk1', hg1'⟩ := (XCK_key_resp a 0 y x (XCK_U.rel_symm _ _ _ _ r1') k3).mp ⟨k2', hk2', hg2⟩
      exact Or.inr ⟨n2, XCK_U.rel_refl_left _ _ _ _ r1', hz, k1', k3, hk1', hk3, hg1'⟩
  · rcases h2 with ⟨e2, r2, _⟩ | ⟨_, _, hz, k2', k3, hk2', hk3, hg2⟩
    · have ecb := XCK_key_rigid b y k2 hk2 c e2.symm
      subst ecb
      have r2' : XCK_U.rel c (0 : Fin 3) y z := r2
      obtain ⟨k3', hk3', hg3⟩ := (XCK_key_resp c 0 y z r2' k1).mp ⟨k2, hk2, XCK_gm_symm hg1⟩
      exact Or.inr ⟨n1, hx, XCK_U.rel_refl_right _ _ _ _ r2', k1, k3', hk1, hk3', XCK_gm_symm hg3⟩
    · have e : k2 = k2' := Option.some.inj (hk2.symm.trans hk2')
      subst e
      have hg := XCK_gm_trans hg1 hg2
      by_cases hac : XCK_N a = XCK_N c
      · have eca := XCK_key_rigid a x k1 hk1 c hac.symm
        subst eca
        exact Or.inl ⟨rfl, XCK_key_inj0 c x z k1 k3 hk1 hk3 hg hx, s0 c⟩
      · exact Or.inr ⟨hac, hx, hz, k1, k3, hk1, hk3, hg⟩

theorem XCK_teq0 (a b : Code XCK_B) : XCK_F.teq a b (0 : Fin 3) ↔ XCK_N a = XCK_N b :=
  ⟨fun h => h.2, fun h => ⟨by decide, h⟩⟩

/-! ### Invariance: types with the same image -/

/-- Identity is preserved by the correspondence between types with the same image. -/
theorem XCK_eqv_inv1 {u : Fin 3} {a a' b b' : Code XCK_B} (ha : XCK_N a = XCK_N a') (hb : XCK_N b = XCK_N b')
    {x : XCK_U.El a} {x' : XCK_U.El a'} {y : XCK_U.El b} {y' : XCK_U.El b'}
    (hx : XCK_U.rel a' u (cast (XCK_ElN a a' ha) x) x') (hy : XCK_U.rel b' u (cast (XCK_ElN b b' hb) y) y') :
    XCK_eqv a b x y u → XCK_eqv a' b' x' y' u := by
  rintro (⟨h, hr, s⟩ | ⟨hne, hxx, hyy, k, k', hk, hk', hg⟩)
  · have h' : XCK_N a' = XCK_N b' := ha.symm.trans (h.trans hb)
    refine Or.inl ⟨h', ?_, fun hw => ha ▸ s hw⟩
    have r1 := (XCK_rc h' (XCK_ElN a' b' h')).mp (XCK_U.rel_symm _ _ _ _ hx)
    have r2 := (XCK_rc hb (XCK_ElN b b' hb)).mp hr
    have e : cast (XCK_ElN a' b' h') (cast (XCK_ElN a a' ha) x) = cast (XCK_ElN b b' hb) (cast (XCK_ElN a b h) x) := by
      rw [cast_cast, cast_cast]
    rw [e] at r1
    exact XCK_U.rel_trans _ _ _ _ _ r1 (XCK_U.rel_trans _ _ _ _ _ r2 hy)
  · have ea := XCK_key_rigid a x k hk a' ha.symm
    have eb := XCK_key_rigid b y k' hk' b' hb.symm
    subst ea; subst eb
    exact (XCK_eqv_resp u _ _ x x' y y' hx hy).mp (Or.inr ⟨hne, hxx, hyy, k, k', hk, hk', hg⟩)

theorem XCK_rel_congr {a : Code XCK_B} {w : Fin 3} {x x' y y' : XCK_U.El a} (hx : x = x') (hy : y = y') :
    XCK_U.rel a w x y ↔ XCK_U.rel a w x' y' := by
  subst hx; subst hy; exact Iff.rfl

theorem XCK_cast_cancel {A B : Type} (h : A = B) (h' : B = A) (x : A) : cast h' (cast h x) = x := by
  subst h; rfl

/-- The correspondences between types with the same image, as admissible relations. -/
def XCK_Inv : KInv XCK_F where
  Adm := fun _ a a' S => ∃ h : XCK_N a = XCK_N a', S = fun u x y => XCK_U.rel a' u (cast (XCK_ElN a a' h) x) y
  amono := fun h _ => h
  smono := by
    intro w a a' S hA u u' x x' _ hu h
    obtain ⟨_, rfl⟩ := hA
    exact XCK_U.rel_mono _ u u' _ _ hu h
  refl := fun _ _ => ⟨rfl, rfl⟩
  arrow := by
    intro w a a' c c' S T hA hB
    obtain ⟨ha, rfl⟩ := hA
    obtain ⟨hc, rfl⟩ := hB
    have hac : XCK_N (.arr a c) = XCK_N (.arr a' c') := by
      show Code.arr (XCK_N a) (XCK_fix (XCK_N a) (XCK_N c)) = Code.arr (XCK_N a') (XCK_fix (XCK_N a') (XCK_N c'))
      rw [ha, hc]
    refine ⟨hac, ?_⟩
    funext v f f'
    apply propext
    have pa := XCK_ElN a a' ha
    have pc := XCK_ElN c c' hc
    constructor
    · intro H u hu y y' hyy
      have e1 : cast (XCK_ElN _ _ hac) f y = cast pc (f (cast pa.symm y)) := XCK_cast_fun pa pc (XCK_ElN _ _ hac) f y
      refine (XCK_rel_congr (a := c') (w := u) e1 rfl).mpr ?_
      exact H u hu (cast pa.symm y) y' ((XCK_rel_congr (XCK_cast_cancel _ _ _).symm rfl).mp hyy)
    · intro H u hu x x' hxx
      have H' : XCK_U.rel c' u (cast (XCK_ElN _ _ hac) f (cast pa x)) (f' x') := H u hu (cast pa x) x' hxx
      have e1 : cast (XCK_ElN _ _ hac) f (cast pa x) = cast pc (f (cast pa.symm (cast pa x))) :=
        XCK_cast_fun pa pc (XCK_ElN _ _ hac) f _
      have e2 : cast pc (f (cast pa.symm (cast pa x))) = cast (XCK_ElN c c' hc) (f x) :=
        congrArg (fun z => cast pc (f z)) (XCK_cast_cancel pa pa.symm x)
      exact (XCK_rel_congr (a := c') (w := u) (e1.trans e2) rfl).mp H'
  total := by
    intro w a a' S hA u _ x hx
    obtain ⟨ha, rfl⟩ := hA
    have hx' := (XCK_rc ha (XCK_ElN a a' ha)).mp hx
    exact ⟨_, hx', hx'⟩
  onto := by
    intro w a a' S hA u _ x' hx'
    obtain ⟨ha, rfl⟩ := hA
    have hx'' : XCK_U.rel a' u (cast (XCK_ElN a a' ha) (cast (XCK_ElN a a' ha).symm x'))
        (cast (XCK_ElN a a' ha) (cast (XCK_ElN a a' ha).symm x')) :=
      (XCK_rel_congr (XCK_cast_cancel _ _ _).symm (XCK_cast_cancel _ _ _).symm).mp hx'
    refine ⟨cast (XCK_ElN a a' ha).symm x', (XCK_rc ha (XCK_ElN a a' ha)).mpr hx'', ?_⟩
    exact (XCK_rel_congr (XCK_cast_cancel _ _ _).symm rfl).mp hx'
  teq := by
    intro w a a' b b' S T hA hB u _
    obtain ⟨ha, _⟩ := hA
    obtain ⟨hb, _⟩ := hB
    exact and_congr Iff.rfl (by rw [ha, hb])
  eqv := by
    intro w a a' b b' S T hA hB u _ x x' y y' hx hy
    obtain ⟨ha, rfl⟩ := hA
    obtain ⟨hb, rfl⟩ := hB
    constructor
    · exact XCK_eqv_inv1 ha hb hx hy
    · refine XCK_eqv_inv1 ha.symm hb.symm ?_ ?_
      · have hx1 := (XCK_rc ha.symm (XCK_ElN a' a ha.symm)).mp (XCK_U.rel_symm _ _ _ _ hx)
        exact (XCK_rel_congr rfl (XCK_cast_cancel _ _ _)).mp hx1
      · have hy1 := (XCK_rc hb.symm (XCK_ElN b' b hb.symm)).mp (XCK_U.rel_symm _ _ _ _ hy)
        exact (XCK_rel_congr rfl (XCK_cast_cancel _ _ _)).mp hy1

/-! ### Soundness at a single world -/

/-- Truth at the world `w`, under every valuation admissible there. -/
def XCK_ValidW (F : Frame) (w : F.U.W) {n : Nat} {Γ : Ctx n} (φ : Fm Γ) : Prop :=
  ∀ ρ, (∀ i, F.U.D w (ρ i)) → ∀ env, F.EnvAdm Γ ρ w env → F.HoldsAt φ ρ env w

/-- **Soundness at a single world**, given the identity axioms there. -/
theorem XCK_soundW (F : Frame) (w : F.U.W) {Ax : Fm Ctx.nil → Prop}
    (hRE : XCK_ValidW F w RefEqv) (hSE : XCK_ValidW F w SymEqv) (hTE : XCK_ValidW F w TransEqv)
    (hRT : XCK_ValidW F w RefTeq) (hLT : ∀ {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)), XCK_ValidW F w (LLTeq Q))
    (hAx : ∀ φ, Ax φ → XCK_ValidW F w φ) {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : Prov Ax Γ φ) :
    XCK_ValidW F w φ := by
  induction h with
  | taut P as hP => intro ρ _ env _; exact (F.holdsAt_inst P as ρ env w).mpr (hP _)
  | instAll σ φ κ =>
    intro ρ _ env henv h
    show F.HoldsAt (φ.subst0 κ) ρ env w
    unfold Frame.HoldsAt; rw [Frame.eval_subst0]
    exact (F.holdsAt_all σ φ ρ env w).mp h _ ((F.relV_iff σ ρ w _ _).mp (F.adm_eval κ ρ w env henv))
  | distAll σ φ ψ =>
    intro ρ _ env _ h hφ
    refine (F.holdsAt_all σ ψ ρ env w).mpr fun v hv => ?_
    have h' := (F.holdsAt_all σ _ ρ env w).mp h v hv
    have hw : F.HoldsAt (φ.wk σ) ρ (env, v) w := by unfold Frame.HoldsAt; rw [Frame.eval_wk]; exact hφ
    exact h' hw
  | dualEx σ φ =>
    intro ρ _ env _
    refine (F.holdsAt_ex σ φ ρ env w).trans ?_
    refine Iff.trans ?_ (not_congr (F.holdsAt_all σ φ.neg ρ env w)).symm
    constructor
    · rintro ⟨v, hv, h⟩ h'; exact h' v hv h
    · intro h; exact Classical.byContradiction fun hn => h fun v hv h' => hn ⟨v, hv, h'⟩
  | instTAll φ σ =>
    intro ρ hρ env _ h
    exact cast ((congrArg (fun f : F.U.W → Prop => f w)) (eq_of_heq (F.eval_tinst φ σ ρ env))).symm
      (h (F.U.code σ.1 ρ) (F.D_code σ.1 w ρ hρ σ.2))
  | distTAll φ ψ =>
    intro ρ _ env _ h hφ a ha
    exact h a ha (cast ((congrArg (fun f : F.U.W → Prop => f w)) (eq_of_heq (F.eval_twk φ a ρ env))).symm hφ)
  | dualTEx φ =>
    intro ρ _ env _
    show (∃ a, F.U.D w a ∧ F.HoldsAt φ (scons a ρ) env w) ↔ ¬ ∀ a, F.U.D w a → ¬ F.HoldsAt φ (scons a ρ) env w
    constructor
    · rintro ⟨a, ha, h⟩ h'; exact h' a ha h
    · intro h; exact Classical.byContradiction fun hn => h fun a ha h' => hn ⟨a, ha, h'⟩
  | beta h => intro ρ _ env _; exact Iff.of_eq ((congrArg (fun f : F.U.W → Prop => f w)) (F.eval_betaEq h ρ env))
  | refEqv => exact hRE
  | symEqv => exact hSE
  | transEqv => exact hTE
  | refTeq => exact hRT
  | llTeq Q => exact hLT Q
  | ax h => exact hAx _ h
  | mp _ _ ih1 ih2 => intro ρ hρ env henv; exact ih2 ρ hρ env henv (ih1 ρ hρ env henv)
  | genAll σ _ ih =>
    intro ρ hρ env henv
    exact (F.holdsAt_all σ _ ρ env w).mpr fun v hv => ih ρ hρ (env, v) ⟨henv, F.adm_of_rel σ ρ w v hv⟩
  | genTAll _ ih => intro ρ hρ env henv a ha; exact ih (scons a ρ) (fin_cases ha hρ) env henv
  | ren ρr _ ih =>
    intro ρ' hρ' env' henv'
    exact cast (F.holdsAt_of_heq (F.eval_ren _ ρr ρ' env' _ (F.pullEnv _ ρr ρ' env') (fun _ => rfl)
      (fun x => F.lookup_pull x ρr ρ' env')) w).symm
      (ih _ (fun i => hρ' _) _ (F.EnvAdm_pull _ ρr ρ' w env' henv'))
  | strengthen σ _ ih =>
    intro ρ hρ env henv
    obtain ⟨x, hx⟩ := F.U.adm_nonempty (F.U.code σ.1 ρ)
    have hv : F.U.rel (F.U.code σ.1 ρ) w (cast (Univ.El_code ρ σ.2).symm (cast (Univ.El_code ρ σ.2) x))
        (cast (Univ.El_code ρ σ.2).symm (cast (Univ.El_code ρ σ.2) x)) := by
      rw [cast_cast, cast_eq]; exact hx w
    have := ih ρ hρ (env, cast (Univ.El_code ρ σ.2) x) ⟨henv, F.adm_of_rel σ ρ w _ hv⟩
    unfold Frame.HoldsAt at this
    rwa [Frame.eval_wk] at this
  | tstrengthen _ ih =>
    intro ρ hρ env henv
    exact cast (F.holdsAt_of_heq (F.eval_twk _ .e ρ env) w) (ih (scons .e ρ) (fin_cases (F.U.D_e w) hρ) env henv)

/-! ### The identity axioms and LL≡ at the actual world -/

theorem XCK_refEqv0 : XCK_ValidW XCK_F (0 : Fin 3) RefEqv := by
  intro ρ _ env _
  refine (XCK_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XCK_F.holdsAt_all _ _ _ _ _).mpr fun x hx => ?_
  exact (XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ((XCK_heq0 _ _ _).mpr hx)

theorem XCK_symEqv0 : XCK_ValidW XCK_F (0 : Fin 3) SymEqv := by
  intro ρ _ env _
  refine (XCK_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XCK_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XCK_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XCK_F.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (XCK_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  exact (XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XCK_eqv_symm ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h))

theorem XCK_transEqv0 : XCK_ValidW XCK_F (0 : Fin 3) TransEqv := by
  intro ρ _ env _
  refine (XCK_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XCK_F.holdsAt_tall _ _ _ _).mpr fun b _ =>
    (XCK_F.holdsAt_tall _ _ _ _).mpr fun c _ => ?_
  refine (XCK_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XCK_F.holdsAt_all _ _ _ _ _).mpr fun y _ =>
    (XCK_F.holdsAt_all _ _ _ _ _).mpr fun z _ => ?_
  refine (XCK_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_
  have hc := (XCK_F.holdsAt_conj _ _ _ _ _).mp h
  have h1 := (XCK_F.holdsAt_eqv (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv2 tv1
    (.var (.there (.there .here))) (.var (.there .here)) (scons c (scons b (scons a ρ))) (((env, x), y), z) _).mp hc.1
  have h2 := (XCK_F.holdsAt_eqv (Γ := (((Ctx.nil.text.text.text).ext tv2).ext tv1).ext tv0) tv1 tv0
    (.var (.there .here)) (.var .here) (scons c (scons b (scons a ρ))) (((env, x), y), z) _).mp hc.2
  exact (XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XCK_eqv_trans0 h1 h2)

theorem XCK_refTeq0 : XCK_ValidW XCK_F (0 : Fin 3) RefTeq := by
  intro ρ _ env _
  exact (XCK_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XCK_F.holdsAt_teq _ _ _ _ _).mpr ((XCK_teq0 a a).mpr rfl)

theorem XCK_llTeq0 {n : Nat} {Γ : Ctx n} (Q : Tm Γ (.pi .t)) : XCK_ValidW XCK_F (0 : Fin 3) (LLTeq Q) := by
  intro ρ _ env henv
  refine (XCK_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XCK_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XCK_F.holdsAt_imp _ _ _ _ _).mpr fun hab => (XCK_F.holdsAt_imp _ _ _ _ _).mpr fun hq => ?_
  have hN : XCK_N a = XCK_N b :=
    (XCK_teq0 a b).mp ((XCK_F.holdsAt_teq (Γ := Γ.text.text) tv1 tv0 (scons b (scons a ρ)) env _).mp hab)
  exact KInv.llTeq_at XCK_Inv Q (0 : Fin 3) ρ env henv a b _ ⟨hN, rfl⟩ hq

theorem XCK_LLEqv0 : XCK_ValidW XCK_F (0 : Fin 3) LLEqv := by
  intro ρ _ env _
  refine (XCK_F.holdsAt_tall _ _ _ _).mpr fun a _ => ?_
  refine (XCK_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XCK_F.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (XCK_F.holdsAt_imp _ _ _ _ _).mpr fun hxy => ?_
  refine (XCK_F.holdsAt_all _ _ _ _ _).mpr fun G hG => (XCK_F.holdsAt_imp _ _ _ _ _).mpr fun hGx => ?_
  have hxy' : XCK_U.rel a (0 : Fin 3) x y := (XCK_heq0 _ _ _).mp ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp hxy)
  have hG' : XCK_U.rel (.arr a .t) (0 : Fin 3) G G := hG
  exact (hG' (0 : Fin 3) (XCK_U.Rrefl (0 : Fin 3)) x y hxy' (0 : Fin 3) (XCK_U.Rrefl (0 : Fin 3))).mp hGx

theorem XCK_LLEqv : XCK_F.Valid LLEqv := XCK_LLEqv0

/-- Every theorem of PI⁻ plus axioms valid at the actual world is valid. -/
theorem XCK_of_prov {Ax : Fm Ctx.nil → Prop} (hAx : ∀ φ, Ax φ → XCK_F.Valid φ) {n : Nat} {Γ : Ctx n} {φ : Fm Γ}
    (h : Prov Ax Γ φ) : XCK_F.Valid φ :=
  XCK_soundW XCK_F (0 : Fin 3) XCK_refEqv0 XCK_symEqv0 XCK_transEqv0 XCK_refTeq0 XCK_llTeq0 hAx h

/-- **A model of PI**: every theorem of PI is valid. -/
theorem XCK_model {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : PIP Γ φ) : XCK_F.Valid φ :=
  XCK_of_prov (fun χ (e : χ = LLEqv) => e ▸ XCK_LLEqv) h

/-! ### Basic facts -/

theorem XCK_Valid_of {φ : Fm Ctx.nil} (h : XCK_F.HoldsAt φ (fun i => i.elim0) () (0 : Fin 3)) : XCK_F.Valid φ := by
  intro ρ _ env _
  have e1 : ρ = fun i => i.elim0 := funext fun i => i.elim0
  subst e1
  exact h

/-- `□φ`, at the actual world: truth at every world. -/
theorem XCK_box0 {n : Nat} {Γ : Ctx n} (φ : Fm Γ) (ρ : XCK_F.U.TEnv n) (env : XCK_F.U.Env Γ ρ) :
    XCK_F.HoldsAt (boxF φ) ρ env (0 : Fin 3) ↔ ∀ v, XCK_U.R (0 : Fin 3) v → XCK_F.HoldsAt φ ρ env v := by
  refine (XCK_F.holdsAt_eqv tyT tyT φ topF ρ env _).trans ((XCK_heq0 _ _ _).trans ?_)
  show (∀ v, XCK_U.R (0 : Fin 3) v → (XCK_F.eval φ ρ env v ↔ XCK_F.eval topF ρ env v)) ↔ _
  have e := XCK_F.eval_topF ρ env
  refine forall_congr' fun v => imp_congr Iff.rfl ?_
  rw [e]
  exact ⟨fun h => h.mpr trivial, fun h => ⟨fun _ => trivial, fun _ => h⟩⟩

abbrev XCK_S : Fm Ctx.nil → Prop := fun χ => χ = LLEqv

theorem XCK_PI {n : Nat} {Γ : Ctx n} {φ : Fm Γ} (h : Prov XCK_S Γ φ) : XCK_F.Valid φ := XCK_model h

/-! ### Consequences of LL≡ -/

theorem XCK_Truth : XCK_F.Valid Truth := XCK_PI (Derive.d_Truth rfl)
theorem XCK_TopBot : XCK_F.Valid TopBot := XCK_PI (Derive.d_TopBot rfl)
theorem XCK_Cantor : XCK_F.Valid Cantor := XCK_PI (Derive.d_Cantor rfl)
theorem XCK_WCong : XCK_F.Valid WCong := XCK_PI (Derive.d_WCong rfl)

/-! ### NI≡, Nec, IdId, NI≈, TNec fail, and with them Classicism -/

theorem XCK_not_NIEqv : ¬ XCK_F.Valid NIEqv := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)
  have h2 := (XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_F.holdsAt_all _ _ _ _ _).mp h1 (show Fin 4 from 0) (Or.inl rfl))
    (show Fin 4 from 0) (Or.inl rfl)
  have h3 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h2
    ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ((XCK_heq0 _ _ _).mpr (Or.inl rfl)))
  have h4 := (XCK_box0 _ _ _).mp h3 (1 : Fin 3) (Or.inr rfl)
  exact XCK_eqv_e1 _ _ ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h4)

theorem XCK_not_NIX : ¬ XCK_F.Valid NIX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) .e (Or.inr trivial)
  have h2 := (XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_F.holdsAt_all _ _ _ _ _).mp h1 (show Fin 4 from 0) (Or.inl rfl))
    (show Fin 4 from 0) (Or.inl rfl)
  have h3 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h2
    ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ((XCK_heq0 _ _ _).mpr (Or.inl rfl)))
  have h4 := (XCK_box0 _ _ _).mp h3 (1 : Fin 3) (Or.inr rfl)
  exact XCK_eqv_e1 _ _ ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h4)

theorem XCK_not_Nec : ¬ XCK_F.Valid Nec := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (show Fin 4 from 0) (Or.inl rfl)
  have h2 := (XCK_box0 _ _ _).mp h1 (1 : Fin 3) (Or.inr rfl)
  obtain ⟨y, _, hy⟩ := (XCK_F.holdsAt_ex _ _ _ _ _).mp h2
  exact XCK_eqv_e1 _ _ ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp hy)

theorem XCK_not_IdId : ¬ XCK_F.Valid IdId := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_F.holdsAt_all _ _ _ _ _).mp
    ((XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) (show Fin 4 from 0) (Or.inl rfl)) (show Fin 4 from 0) (Or.inl rfl)
  have h2 := (XCK_heq0 _ _ _).mp ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h1) (1 : Fin 3) (Or.inr rfl)
  have hQ : XCK_F.HoldsAt (Γ := ((Ctx.nil.text).ext tv0).ext tv0) (all tv0.pred (imp (.app (.var .here) (.var (.there (.there .here))))
      (.app (.var .here) (.var (.there .here)))))
      (scons .e (fun i => i.elim0)) (((), (show Fin 4 from 0)), (show Fin 4 from 0)) (1 : Fin 3) :=
    (XCK_F.holdsAt_all _ _ _ _ _).mpr fun _ _ => (XCK_F.holdsAt_imp _ _ _ _ _).mpr fun hG => hG
  have hP : XCK_F.HoldsAt (Γ := ((Ctx.nil.text).ext tv0).ext tv0) (eqv tv0 tv0 (.var (.there .here)) (.var .here))
      (scons .e (fun i => i.elim0)) (((), (show Fin 4 from 0)), (show Fin 4 from 0)) (1 : Fin 3) := h2.mpr hQ
  exact XCK_eqv_e1 _ _ ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp hP)

theorem XCK_not_NITeq : ¬ XCK_F.Valid NITeq := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) .e (Or.inr trivial)
  have h2 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCK_F.holdsAt_teq _ _ _ _ _).mpr ((XCK_teq0 _ _).mpr rfl))
  have h3 := (XCK_F.holdsAt_teq _ _ _ _ _).mp ((XCK_box0 _ _ _).mp h2 (1 : Fin 3) (Or.inr rfl))
  exact h3.1 rfl

theorem XCK_not_TNec : ¬ XCK_F.Valid TNec := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_box0 _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) (1 : Fin 3) (Or.inr rfl)
  obtain ⟨b, _, hb⟩ := (XCK_F.holdsAt_tex _ _ _ _).mp h1
  exact ((XCK_F.holdsAt_teq _ _ _ _ _).mp hb).1 rfl

/-- Classicism fails: it proves IdId. -/
theorem XCK_not_Class : ¬ ∀ χ, ClassSch χ → XCK_F.Valid χ := fun h =>
  XCK_not_IdId (XCK_of_prov h (d_IdId_of_Class (S := ClassSch) (fun _ hc => hc)))

/-! ### Functional Choice fails -/

/-- The relation pairing `x` with `x + 2` at the actual world (and everything elsewhere). -/
def XCK_RCh : XCK_U.El (.arr .e (.arr .e .t)) := fun (x y : Fin 4) (w : Fin 3) => w ≠ 0 ∨ y = XCK_sh x

theorem XCK_RCh_adm : XCK_U.rel (.arr .e (.arr .e .t)) (0 : Fin 3) XCK_RCh XCK_RCh := by
  intro v _ x x' hx u hu y y' hy s hs
  by_cases h0 : s = (0 : Fin 3)
  · subst h0
    have hu' : u = (0 : Fin 3) := hs.elim id id
    subst hu'
    have hv' : v = (0 : Fin 3) := hu.elim id id
    subst hv'
    have ex : x = x' := XCK_re0 hx
    have ey : y = y' := XCK_re0 hy
    subst ex; subst ey
    exact Iff.rfl
  · exact ⟨fun _ => Or.inl h0, fun _ => Or.inl h0⟩

theorem XCK_re_23 : ¬ XCK_re 2 (XCK_sh 0) (XCK_sh 1) := by
  unfold XCK_re XCK_sh; decide

theorem XCK_not_Choice : ¬ XCK_F.Valid Choice := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)
  have h2 := (XCK_F.holdsAt_tall _ _ _ _).mp h1 .e (Or.inr trivial)
  have h3 := (XCK_F.holdsAt_all _ _ _ _ _).mp h2 XCK_RCh XCK_RCh_adm
  have h4 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h3 ((XCK_F.holdsAt_all _ _ _ _ _).mpr fun x _ =>
    (XCK_F.holdsAt_ex _ _ _ _ _).mpr ⟨XCK_sh x, Or.inl rfl, Or.inr rfl⟩)
  obtain ⟨f, hf, hfx⟩ := (XCK_F.holdsAt_ex _ _ _ _ _).mp h4
  have hall := (XCK_F.holdsAt_all _ _ _ _ _).mp hfx
  have f0 : (f : Fin 4 → Fin 4) (0 : Fin 4) = XCK_sh (0 : Fin 4) :=
    (show (0 : Fin 3) ≠ 0 ∨ (f : Fin 4 → Fin 4) (0 : Fin 4) = XCK_sh (0 : Fin 4) from
      hall (0 : Fin 4) (Or.inl rfl)).resolve_left (fun h => h rfl)
  have f1 : (f : Fin 4 → Fin 4) (1 : Fin 4) = XCK_sh (1 : Fin 4) :=
    (show (0 : Fin 3) ≠ 0 ∨ (f : Fin 4 → Fin 4) (1 : Fin 4) = XCK_sh (1 : Fin 4) from
      hall (1 : Fin 4) (Or.inl rfl)).resolve_left (fun h => h rfl)
  have hr : XCK_re 2 ((f : Fin 4 → Fin 4) (0 : Fin 4)) ((f : Fin 4 → Fin 4) (1 : Fin 4)) :=
    hf (2 : Fin 3) (Or.inr rfl) (0 : Fin 4) (1 : Fin 4) (Or.inr ⟨rfl, by decide, by decide⟩)
  rw [f0, f1] at hr
  exact XCK_re_23 hr

/-! ### BF fails -/

/-- The constant proposition that `x 0` and `x 1` are identical at world `2`. -/
def XCK_FBF : XCK_U.El (.arr (.arr .e .e) .t) :=
  fun (x : Fin 4 → Fin 4) (_ : Fin 3) => XCK_re 2 (x 0) (x 1)

theorem XCK_FBF_adm (w : Fin 3) : XCK_U.rel (.arr (.arr .e .e) .t) w XCK_FBF XCK_FBF := by
  intro v _ x y hxy u _
  have hxy' : ∀ a b : Fin 4, XCK_re v a b → XCK_re v ((x : Fin 4 → Fin 4) a) ((y : Fin 4 → Fin 4) b) :=
    hxy v (XCK_U.Rrefl v)
  have h0 : XCK_re 2 ((x : Fin 4 → Fin 4) (0 : Fin 4)) ((y : Fin 4 → Fin 4) (0 : Fin 4)) :=
    XCK_re_two (hxy' (0 : Fin 4) (0 : Fin 4) (Or.inl rfl))
  have h1 : XCK_re 2 ((x : Fin 4 → Fin 4) (1 : Fin 4)) ((y : Fin 4 → Fin 4) (1 : Fin 4)) :=
    XCK_re_two (hxy' (1 : Fin 4) (1 : Fin 4) (Or.inl rfl))
  show XCK_re 2 ((x : Fin 4 → Fin 4) (0 : Fin 4)) ((x : Fin 4 → Fin 4) (1 : Fin 4)) ↔
    XCK_re 2 ((y : Fin 4 → Fin 4) (0 : Fin 4)) ((y : Fin 4 → Fin 4) (1 : Fin 4))
  constructor
  · intro h
    exact XCK_re_trans (XCK_re_trans (XCK_re_symm h0) h) h1
  · intro h
    exact XCK_re_trans (XCK_re_trans h0 h) (XCK_re_symm h1)

/-- At world `1`, which sees only itself and where identity of entities is equality, the
function `x ↦ x + 2` is an item. -/
theorem XCK_sh_adm1 : XCK_U.rel (.arr .e .e) (1 : Fin 3) XCK_sh XCK_sh := by
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

theorem XCK_not_BF : ¬ XCK_F.Valid BF := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_tall _ _ _ _).mp h (.arr .e .e) (Or.inr ⟨trivial, trivial⟩)
  have h2 := (XCK_F.holdsAt_all _ _ _ _ _).mp h1 XCK_FBF (XCK_FBF_adm (0 : Fin 3))
  have h3 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h2 ((XCK_F.holdsAt_all _ _ _ _ _).mpr fun x hx =>
    (XCK_box0 _ _ _).mpr fun _ _ => by
      have hx' : XCK_U.rel (.arr .e .e) (0 : Fin 3) x x := hx
      exact hx' (2 : Fin 3) (Or.inr rfl) (0 : Fin 4) (1 : Fin 4) (Or.inr ⟨rfl, by decide, by decide⟩))
  have h4 := (XCK_box0 _ _ _).mp h3 (1 : Fin 3) (Or.inr rfl)
  have h5 := (XCK_F.holdsAt_all _ _ _ _ _).mp h4 XCK_sh XCK_sh_adm1
  exact XCK_re_23 h5

/-! ### ND× fails -/

theorem XCK_not_NDX : ¬ XCK_F.Valid NDX := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) .e (Or.inr trivial)
  have h2 := (XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_F.holdsAt_all _ _ _ _ _).mp h1 (show Fin 4 from 0) (Or.inl rfl))
    (show Fin 4 from 1) (Or.inl rfl)
  refine (XCK_F.holdsAt_neg _ _ _ _).mp ((XCK_box0 _ _ _).mp ((XCK_F.holdsAt_imp _ _ _ _ _).mp h2
    ((XCK_F.holdsAt_neg _ _ _ _).mpr fun he => ?_)) (2 : Fin 3) (Or.inr rfl)) ?_
  · have he' := XCK_re0 ((XCK_heq0 .e (show Fin 4 from 0) (show Fin 4 from 1)).mp
      ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp he))
    exact absurd he' (by decide)
  · exact (XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr
      (XCK_eqv_of_rel (a := .e) (x := (show Fin 4 from 0)) (y := (show Fin 4 from 1)) (w := (2 : Fin 3))
        (Or.inr ⟨rfl, by decide, by decide⟩) (fun h => absurd h (by decide)))

/-! ### TBF fails -/

/-- `α` has two distinct items. -/
abbrev XCK_phiBF : Fm Ctx.nil.text := neg (all tv0 (all tv0 (eqv tv0 tv0 (.var (.there .here)) (.var .here))))

theorem XCK_phiBF_iff (a : Code XCK_B) (w : Fin 3) :
    XCK_F.HoldsAt XCK_phiBF (scons a (fun i => i.elim0)) () w ↔
      ¬ ∀ x : XCK_U.El a, XCK_U.rel a w x x → ∀ y : XCK_U.El a, XCK_U.rel a w y y → XCK_F.eqv a a x y w := by
  refine (XCK_F.holdsAt_neg _ _ _ _).trans (not_congr ?_)
  refine (XCK_F.holdsAt_all _ _ _ _ _).trans (forall_congr' fun x => imp_congr Iff.rfl ?_)
  refine (XCK_F.holdsAt_all _ _ _ _ _).trans (forall_congr' fun y => imp_congr Iff.rfl ?_)
  exact XCK_F.holdsAt_eqv _ _ _ _ _ _ _

theorem XCK_re_02 (w : Fin 3) : ¬ XCK_re w 0 2 := by
  intro h
  rcases h with e | ⟨_, _, h⟩
  · exact absurd e (by decide)
  · exact absurd h (by decide)

/-- Each type not mentioning `n` has two items which are distinct at every world. -/
theorem XCK_two_items : ∀ a : Code XCK_B, XCK_noN a → ∃ x y : XCK_U.El a,
    (∀ w, XCK_U.rel a w x x) ∧ (∀ w, XCK_U.rel a w y y) ∧ ∀ w, ¬ XCK_U.rel a w x y
  | .e, _ => ⟨(0 : Fin 4), (2 : Fin 4), fun w => XCK_re_refl w 0, fun w => XCK_re_refl w 2, XCK_re_02⟩
  | .t, _ => ⟨fun _ => True, fun _ => False, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
      fun w h => (h w (XCK_U.Rrefl w)).mp trivial⟩
  | .base .d, _ => ⟨(0 : Fin 4), (2 : Fin 4), fun w => XCK_re_refl w 0, fun w => XCK_re_refl w 2, XCK_re_02⟩
  | .base .n, h => h.elim
  | .base .u1, _ => ⟨true, false, fun _ => rfl, fun _ => rfl, fun _ h => Bool.noConfusion h⟩
  | .base .u2, _ => ⟨true, false, fun _ => rfl, fun _ => rfl, fun _ h => Bool.noConfusion h⟩
  | .arr a c, ⟨_, hc⟩ => by
    obtain ⟨y1, y2, h1, h2, h12⟩ := XCK_two_items c hc
    obtain ⟨x0, hx0⟩ := XCK_U.adm_nonempty a
    refine ⟨fun _ => y1, fun _ => y2, fun _ v _ _ _ _ => h1 v, fun _ v _ _ _ _ => h2 v, fun w h => ?_⟩
    exact h12 w (h w (XCK_U.Rrefl w) x0 x0 (hx0 w))

/-- Every type at the actual world necessarily has two distinct items; but at world `2` the type
`n` has only one. -/
theorem XCK_not_TBFI : ¬ XCK_F.Valid (TBFI XCK_phiBF) := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have hA : XCK_F.HoldsAt (tall (boxF XCK_phiBF)) (fun i => i.elim0) () (0 : Fin 3) := by
    refine (XCK_F.holdsAt_tall _ _ _ _).mpr fun a ha => (XCK_box0 _ _ _).mpr fun v _ => ?_
    have hna : XCK_noN a := Or.resolve_left ha (fun h => absurd h (by decide))
    obtain ⟨x, y, hx, hy, hxy⟩ := XCK_two_items a hna
    exact (XCK_phiBF_iff a v).mpr fun h => hxy v (XCK_eqv_sub_rel a x y v (h x (hx v) y (hy v)))
  have hB := (XCK_box0 _ _ _).mp ((XCK_F.holdsAt_imp _ _ _ _ _).mp h hA) (2 : Fin 3) (Or.inr rfl)
  have hd := (XCK_F.holdsAt_tall _ _ _ _).mp hB (.base .n) (Or.inl rfl)
  exact (XCK_phiBF_iff (.base .n) (2 : Fin 3)).mp hd fun _ _ _ _ =>
    XCK_eqv_of_rel (a := .base .n) trivial (fun h => absurd h (by decide))

theorem XCK_not_TBF : ¬ ∀ χ, TBFSch χ → XCK_F.Valid χ := fun h => XCK_not_TBFI (h _ ⟨XCK_phiBF, rfl⟩)

/-! ### `e` and `d`: Ext≈, Int≈ and Disjoint fail -/

theorem XCK_e_ne_d : XCK_N (Code.e : Code XCK_B) ≠ XCK_N (.base .d) := fun h => nomatch h

theorem XCK_ed (w : Fin 3) (x : Fin 4) (hx : XCK_re w x x) : XCK_F.eqv .e (.base .d) x x w :=
  Or.inr ⟨XCK_e_ne_d, hx, hx, .inl x, .inl x, rfl, rfl, hx⟩

theorem XCK_de (w : Fin 3) (x : Fin 4) (hx : XCK_re w x x) : XCK_F.eqv (.base .d) .e x x w :=
  Or.inr ⟨fun h => XCK_e_ne_d h.symm, hx, hx, .inl x, .inl x, rfl, rfl, hx⟩

/-- At every world, `e` and `d` are coextensive. -/
theorem XCK_subT_ed (w : Fin 3) : XCK_F.HoldsAt (subT : Fm (Ctx.nil.text.text))
    (scons (.base .d) (scons .e (fun i => i.elim0))) () w :=
  (XCK_F.holdsAt_all _ _ _ _ _).mpr fun x hx => (XCK_F.holdsAt_ex _ _ _ _ _).mpr
    ⟨x, hx, (XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XCK_ed w x hx)⟩

theorem XCK_supT_ed (w : Fin 3) : XCK_F.HoldsAt (supT : Fm (Ctx.nil.text.text))
    (scons (.base .d) (scons .e (fun i => i.elim0))) () w :=
  (XCK_F.holdsAt_all _ _ _ _ _).mpr fun y hy => (XCK_F.holdsAt_ex _ _ _ _ _).mpr
    ⟨y, hy, (XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XCK_ed w y hy)⟩

theorem XCK_not_ExtT : ¬ XCK_F.Valid ExtT := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base .d) (Or.inr trivial)
  have h2 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h1
    ((XCK_F.holdsAt_conj _ _ _ _ _).mpr ⟨XCK_subT_ed (0 : Fin 3), XCK_supT_ed (0 : Fin 3)⟩)
  exact XCK_e_ne_d ((XCK_F.holdsAt_teq _ _ _ _ _).mp h2).2

theorem XCK_not_IntT : ¬ XCK_F.Valid IntT := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base .d) (Or.inr trivial)
  have h2 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCK_F.holdsAt_conj _ _ _ _ _).mpr
    ⟨(XCK_box0 _ _ _).mpr fun v _ => XCK_subT_ed v, (XCK_box0 _ _ _).mpr fun v _ => XCK_supT_ed v⟩)
  exact XCK_e_ne_d ((XCK_F.holdsAt_teq _ _ _ _ _).mp h2).2

theorem XCK_not_Disjoint : ¬ XCK_F.Valid Disjoint := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base .d) (Or.inr trivial)
  have h2 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCK_F.holdsAt_neg _ _ _ _).mpr fun ht =>
    XCK_e_ne_d ((XCK_F.holdsAt_teq _ _ _ _ _).mp ht).2)
  have h3 := (XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_F.holdsAt_all _ _ _ _ _).mp h2 (show Fin 4 from 0) (Or.inl rfl))
    (show Fin 4 from 0) (Or.inl rfl)
  exact (XCK_F.holdsAt_neg _ _ _ _).mp h3 ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XCK_ed _ _ (Or.inl rfl)))

/-! ### PCong→, Cong, PCong← fail -/

/-- The constant function `0` of `t → e`. -/
def XCK_k0 : XCK_U.El (.arr .t .e) := fun _ => (0 : Fin 4)
/-- The constant function `2` of `t → d`. -/
def XCK_k2 : XCK_U.El (.arr .t (.base .d)) := fun _ => (2 : Fin 4)

theorem XCK_k0_adm (w : Fin 3) : XCK_U.rel (.arr .t .e) w XCK_k0 XCK_k0 := fun _ _ _ _ _ => Or.inl rfl
theorem XCK_k2_adm (w : Fin 3) : XCK_U.rel (.arr .t (.base .d)) w XCK_k2 XCK_k2 := fun _ _ _ _ _ => Or.inl rfl

theorem XCK_sh2 : XCK_sh 2 = 0 := by decide

theorem XCK_Ntt : XCK_N (Code.arr .t .e : Code XCK_B) ≠ XCK_N (.arr .t (.base .d)) := fun h => nomatch h

/-- The constant functions `0` of `t → e` and `2` of `t → d` are identified. -/
theorem XCK_k0k2 : XCK_F.eqv (.arr .t .e) (.arr .t (.base .d)) XCK_k0 XCK_k2 (0 : Fin 3) :=
  Or.inr ⟨XCK_Ntt, XCK_k0_adm _, XCK_k2_adm _, .inr XCK_k0, .inr (fun p => XCK_sh (XCK_k2 p)), rfl, rfl,
    rfl, funext fun _ => XCK_sh2.symm⟩

/-- An entity and an item of `d` are identified at the actual world only if they are the same. -/
theorem XCK_ed_eq0 {x y : Fin 4} (h : XCK_F.eqv .e (.base .d) x y (0 : Fin 3)) : x = y := by
  rcases h with ⟨e, _⟩ | ⟨_, _, _, k, k', hk, hk', hg⟩
  · exact absurd e XCK_e_ne_d
  · cases hk; cases hk'; exact XCK_re0 hg

theorem XCK_not_PCong : ¬ XCK_F.Valid PCong := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp
    ((XCK_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)) .e (Or.inr trivial)) (.base .d) (Or.inr trivial)
  have h2 := (XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_F.holdsAt_all _ _ _ _ _).mp h1
    XCK_k0 (XCK_k0_adm _)) XCK_k2 (XCK_k2_adm _)) (fun _ => True) (fun _ _ => Iff.rfl)
  have h3 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h2 ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr XCK_k0k2)
  exact absurd (XCK_ed_eq0 ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h3)) (show ¬ (0 : Fin 4) = 2 by decide)

theorem XCK_not_Cong : ¬ XCK_F.Valid Cong := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp
    ((XCK_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial)) .t (Or.inr trivial)) .e (Or.inr trivial))
    (.base .d) (Or.inr trivial)
  have h2 := (XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_F.holdsAt_all _ _ _ _ _).mp
    ((XCK_F.holdsAt_all _ _ _ _ _).mp h1 XCK_k0 (XCK_k0_adm _)) XCK_k2 (XCK_k2_adm _)) (fun _ => True)
    (fun _ _ => Iff.rfl)) (fun _ => True) (fun _ _ => Iff.rfl)
  have h3 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h2 ((XCK_F.holdsAt_conj _ _ _ _ _).mpr
    ⟨(XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr XCK_k0k2,
     (XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr ((XCK_heq0 _ _ _).mpr (fun _ _ => Iff.rfl))⟩)
  exact absurd (XCK_ed_eq0 ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h3)) (show ¬ (0 : Fin 4) = 2 by decide)

/-- The identity functions of `e → e` and `e → d`. -/
def XCK_ide : XCK_U.El (.arr .e .e) := fun x => x
def XCK_idd : XCK_U.El (.arr .e (.base .d)) := fun (x : Fin 4) => x

theorem XCK_ide_adm (w : Fin 3) : XCK_U.rel (.arr .e .e) w XCK_ide XCK_ide := fun _ _ _ _ h => h
theorem XCK_idd_adm (w : Fin 3) : XCK_U.rel (.arr .e (.base .d)) w XCK_idd XCK_idd := fun _ _ _ _ h => h

/-- The identity functions of `e → e` and `e → d` are not identified, though their values are. -/
theorem XCK_not_PExt : ¬ XCK_F.Valid PExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp
    ((XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) .e (Or.inr trivial)) (.base .d) (Or.inr trivial)
  have h2 := (XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_F.holdsAt_all _ _ _ _ _).mp h1 XCK_ide (XCK_ide_adm _))
    XCK_idd (XCK_idd_adm _)
  have h3 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h2 ((XCK_F.holdsAt_all _ _ _ _ _).mpr fun x hx =>
    (XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XCK_ed _ x hx))
  rcases (XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h3 with ⟨e, _⟩ | ⟨_, _, _, k, _, hk, _⟩
  · exact nomatch e
  · exact nomatch (show (none : Option XCK_K) = some k from hk)

/-! ### Twin, Haecceitism, LL≡-Poly fail; Slogan holds -/

theorem XCK_not_Twin : ¬ XCK_F.Valid Twin := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp h .t (Or.inr trivial))
    (fun _ => True) (fun _ _ => Iff.rfl)
  obtain ⟨b, _, hb⟩ := (XCK_F.holdsAt_tex _ _ _ _).mp h1
  obtain ⟨hn, hy⟩ := (XCK_F.holdsAt_conj _ _ _ _ _).mp hb
  obtain ⟨y, _, hxy⟩ := (XCK_F.holdsAt_ex _ _ _ _ _).mp hy
  rcases (XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp hxy with ⟨e, _⟩ | ⟨_, _, _, k, _, hk, _⟩
  · exact (XCK_F.holdsAt_neg _ _ _ _).mp hn ((XCK_F.holdsAt_teq _ _ _ _ _).mpr ((XCK_teq0 _ _).mpr e))
  · exact nomatch (show (none : Option XCK_K) = some k from hk)

theorem XCK_not_Hae : ¬ XCK_F.Valid Hae := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (show Fin 4 from 0) (Or.inl rfl)
  rcases (XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h1 with ⟨e, _⟩ | ⟨_, _, _, _, k', _, hk', _⟩
  · exact nomatch e
  · exact nomatch ((XCK_key_pred .e _).symm.trans hk')

theorem XCK_Slogan : XCK_F.Valid Slogan := by
  refine XCK_Valid_of ?_
  refine (XCK_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XCK_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XCK_F.holdsAt_all _ _ _ _ _).mpr fun y _ => (XCK_F.holdsAt_neg _ _ _ _).mpr fun hxy => ?_
  rcases (XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp hxy with ⟨e, _⟩ | ⟨_, _, _, _, k', _, hk', _⟩
  · exact nomatch e
  · exact nomatch ((XCK_key_pred b _).symm.trans hk')

open Derive in
set_option maxHeartbeats 4000000 in
theorem XCK_PredE_iff1 (x y : Fin 4) :
    XCK_F.HoldsAt (.app (.tapp ((PredE.twk.twk.wk tv1).wk tv0) tv1) (.var (.there .here)))
      (scons (.base .d) (scons .e (fun i => i.elim0))) (((), x), y) (0 : Fin 3) ↔ XCK_F.teq .e .e (0 : Fin 3) :=
  Iff.rfl

open Derive in
set_option maxHeartbeats 4000000 in
theorem XCK_PredE_iff0 (x y : Fin 4) :
    XCK_F.HoldsAt (.app (.tapp ((PredE.twk.twk.wk tv1).wk tv0) tv0) (.var .here))
      (scons (.base .d) (scons .e (fun i => i.elim0))) (((), x), y) (0 : Fin 3) ↔ XCK_F.teq (.base .d) .e (0 : Fin 3) :=
  Iff.rfl

/-- With `P := λγ.λz.(γ ≈ e)`: the entity `0` and the item `0` of `d` are identified, but only one
has `P`. -/
theorem XCK_not_LLPoly : ¬ XCK_F.Valid (LLPoly PredE) := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial))
    (.base .d) (Or.inr trivial)
  have h2 := (XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_F.holdsAt_all _ _ _ _ _).mp h1 (show Fin 4 from 0) (Or.inl rfl))
    (show Fin 4 from 0) (Or.inl rfl)
  have h3 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h2 ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mpr (XCK_ed _ _ (Or.inl rfl)))
  have h4 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h3 ((XCK_PredE_iff1 0 0).mpr ((XCK_teq0 _ _).mpr rfl))
  exact XCK_e_ne_d ((XCK_teq0 _ _).mp ((XCK_PredE_iff0 0 0).mp h4)).symm

/-! ### LL≡/≈ holds, for every polymorphic predicate, with parameters -/

/-- At the actual world, a polymorphic predicate does not tell apart corresponding items of types
with the same image. -/
theorem XCK_poly {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XCK_F.U.TEnv n)
    (env : XCK_F.U.Env Γ ρ) (henv : XCK_F.EnvAdm Γ ρ (0 : Fin 3) env) (a b : Code XCK_B) (hN : XCK_N a = XCK_N b)
    (x : XCK_U.El a) (y : XCK_U.El b) (hxy : XCK_U.rel b (0 : Fin 3) (cast (XCK_ElN a b hN) x) y) :
    XCK_F.eval P ρ env a x (0 : Fin 3) → XCK_F.eval P ρ env b y (0 : Fin 3) :=
  (XCK_Inv.fundamental P ρ ρ (XCK_F.homRs ρ) (0 : Fin 3) (fun i => XCK_Inv.refl (0 : Fin 3) (ρ i)) env env
    (KInv.EnvRel_indep XCK_F.hom XCK_Inv Γ ρ ρ _ (0 : Fin 3) env env henv) (0 : Fin 3) (Or.inl rfl) a b _
    ⟨hN, rfl⟩ (0 : Fin 3) (Or.inl rfl) x y hxy (0 : Fin 3) (Or.inl rfl)).mp

theorem XCK_evalP {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XCK_F.U.TEnv n)
    (env : XCK_F.U.Env Γ ρ) (a b : Code XCK_B) (x : XCK_U.El a) (y : XCK_U.El b) :
    HEq (XCK_F.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y)) (XCK_F.eval P ρ env) := by
  have e1 : XCK_F.eval ((P.twk.twk.wk tv1).wk tv0) (scons b (scons a ρ)) ((env, x), y) =
      XCK_F.eval (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) :=
    XCK_F.eval_wk tv0 (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) y
  have e2 : XCK_F.eval (P.twk.twk.wk tv1) (scons b (scons a ρ)) (env, x) =
      XCK_F.eval P.twk.twk (scons b (scons a ρ)) env := XCK_F.eval_wk tv1 P.twk.twk (scons b (scons a ρ)) env x
  exact (heq_of_eq (e1.trans e2)).trans ((XCK_F.eval_twk P.twk b (scons a ρ) env).trans (XCK_F.eval_twk P a ρ env))

theorem XCK_evalP1 {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XCK_F.U.TEnv n)
    (env : XCK_F.U.Env Γ ρ) (a b : Code XCK_B) (x : XCK_U.El a) (y : XCK_U.El b) :
    XCK_F.HoldsAt (.app (.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (.var (.there .here))) (scons b (scons a ρ))
      ((env, x), y) (0 : Fin 3) ↔ XCK_F.eval P ρ env a x (0 : Fin 3) := by
  have h1 : HEq (XCK_F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv1) (scons b (scons a ρ)) ((env, x), y))
      (XCK_F.eval P ρ env a) :=
    (XCK_F.heq_eval_tapp ((P.twk.twk.wk tv1).wk tv0) tv1 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => XCK_U.El c → Fin 3 → Prop) (Q := fun c => XCK_U.El c → Fin 3 → Prop)
        (fun _ => rfl) (XCK_evalP P ρ env a b x y) rfl)
  have e := congrFun (congrFun (eq_of_heq h1) x) (0 : Fin 3)
  exact Iff.of_eq e

theorem XCK_evalP0 {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) (ρ : XCK_F.U.TEnv n)
    (env : XCK_F.U.Env Γ ρ) (a b : Code XCK_B) (x : XCK_U.El a) (y : XCK_U.El b) :
    XCK_F.HoldsAt (.app (.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (.var .here)) (scons b (scons a ρ))
      ((env, x), y) (0 : Fin 3) ↔ XCK_F.eval P ρ env b y (0 : Fin 3) := by
  have h1 : HEq (XCK_F.eval (Tm.tapp ((P.twk.twk.wk tv1).wk tv0) tv0) (scons b (scons a ρ)) ((env, x), y))
      (XCK_F.eval P ρ env b) :=
    (XCK_F.heq_eval_tapp ((P.twk.twk.wk tv1).wk tv0) tv0 (scons b (scons a ρ)) ((env, x), y)).trans
      (heq_dapp (P := fun c => XCK_U.El c → Fin 3 → Prop) (Q := fun c => XCK_U.El c → Fin 3 → Prop)
        (fun _ => rfl) (XCK_evalP P ρ env a b x y) rfl)
  have e := congrFun (congrFun (eq_of_heq h1) y) (0 : Fin 3)
  exact Iff.of_eq e

/-- LL≡/≈ holds, for every polymorphic predicate, with parameters. -/
theorem XCK_Bridge {n : Nat} {Γ : Ctx n} (P : Tm Γ (.pi (.arr (.var fz) .t))) : XCK_F.Valid (Bridge P) := by
  intro ρ _ env henv
  refine (XCK_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XCK_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine (XCK_F.holdsAt_all _ _ _ _ _).mpr fun x _ => (XCK_F.holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine (XCK_F.holdsAt_imp _ _ _ _ _).mpr fun h => (XCK_F.holdsAt_imp _ _ _ _ _).mpr fun hPx => ?_
  obtain ⟨h1, h2⟩ := (XCK_F.holdsAt_conj _ _ _ _ _).mp h
  have hN : XCK_N a = XCK_N b := (XCK_teq0 _ _).mp ((XCK_F.holdsAt_teq _ _ _ _ _).mp h2)
  rcases (XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h1 with ⟨_, hr, _⟩ | ⟨hne, _⟩
  · exact (XCK_evalP0 P ρ env a b x y).mpr (XCK_poly P ρ env henv a b hN x y hr ((XCK_evalP1 P ρ env a b x y).mp hPx))
  · exact absurd hN hne

/-! ### PropExt≡ and Collapse fail; T, ND≈, Inj≈, Recovery hold -/

theorem XCK_not_PropExt : ¬ XCK_F.Valid PropExt := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_F.holdsAt_all _ _ _ _ _).mp h (fun w : Fin 3 => w = 0)
    (fun _ _ => Iff.rfl)) (fun _ : Fin 3 => True) (fun _ _ => Iff.rfl)
  have h2 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCK_F.holdsAt_iff _ _ _ _ _).mpr ⟨fun _ => trivial, fun _ => rfl⟩)
  have h3 := (XCK_heq0 _ _ _).mp ((XCK_F.holdsAt_eqv _ _ _ _ _ _ _).mp h2)
  exact absurd (show (1 : Fin 3) = 0 from (h3 (1 : Fin 3) (Or.inr rfl)).mpr trivial) (by decide)

theorem XCK_not_Collapse : ¬ XCK_F.Valid Collapse := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_all _ _ _ _ _).mp h (fun w : Fin 3 => w = 0) (fun _ _ => Iff.rfl)
  have h2 := (XCK_box0 _ _ _).mp ((XCK_F.holdsAt_imp _ _ _ _ _).mp h1 rfl) (1 : Fin 3) (Or.inr rfl)
  exact absurd (show (1 : Fin 3) = 0 from h2) (by decide)

theorem XCK_TAx : XCK_F.Valid TAx :=
  XCK_Valid_of ((XCK_F.holdsAt_all _ _ _ _ _).mpr fun _ _ => (XCK_F.holdsAt_imp _ _ _ _ _).mpr fun h =>
    (XCK_box0 _ _ _).mp h (0 : Fin 3) (Or.inl rfl))

theorem XCK_NDTeq : XCK_F.Valid NDTeq := by
  refine XCK_Valid_of ((XCK_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XCK_F.holdsAt_tall _ _ _ _).mpr fun b _ => ?_)
  refine (XCK_F.holdsAt_imp _ _ _ _ _).mpr fun hn => (XCK_box0 _ _ _).mpr fun v _ => ?_
  refine (XCK_F.holdsAt_neg _ _ _ _).mpr fun ht => (XCK_F.holdsAt_neg _ _ _ _).mp hn ?_
  have e : XCK_N a = XCK_N b := ((XCK_F.holdsAt_teq _ _ _ _ v).mp ht).2
  exact (XCK_F.holdsAt_teq _ _ _ _ _).mpr ((XCK_teq0 _ _).mpr e)

/-- `e → u₁ ≈ e → u₂`, but `u₁` and `u₂` are not `≈`. -/
theorem XCK_teq_u : XCK_F.teq (.arr .e (.base .u1)) (.arr .e (.base .u2)) (0 : Fin 3) := (XCK_teq0 _ _).mpr rfl

theorem XCK_not_teq_u : ¬ XCK_F.teq (.base .u1) (.base .u2) (0 : Fin 3) := fun h => nomatch ((XCK_teq0 _ _).mp h)

theorem XCK_not_Inj : ¬ XCK_F.Valid Inj := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp
    ((XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) .e (Or.inr trivial)) (.base .u1) (Or.inr trivial))
    (.base .u2) (Or.inr trivial)
  have h2 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCK_F.holdsAt_teq _ _ _ _ _).mpr XCK_teq_u)
  exact XCK_not_teq_u ((XCK_F.holdsAt_teq _ _ _ _ _).mp ((XCK_F.holdsAt_conj _ _ _ _ _).mp h2).2)

theorem XCK_not_Recovery : ¬ XCK_F.Valid Recovery := fun hv => by
  have h := hv (fun i => i.elim0) (fun i => i.elim0) () trivial
  have h1 := (XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_F.holdsAt_tall _ _ _ _).mp
    ((XCK_F.holdsAt_tall _ _ _ _).mp h .e (Or.inr trivial)) .e (Or.inr trivial)) (.base .u1) (Or.inr trivial))
    (.base .u2) (Or.inr trivial)
  have h2 := (XCK_F.holdsAt_imp _ _ _ _ _).mp h1 ((XCK_F.holdsAt_conj _ _ _ _ _).mpr
    ⟨(XCK_F.holdsAt_teq _ _ _ _ _).mpr XCK_teq_u, (XCK_F.holdsAt_teq _ _ _ _ _).mpr ((XCK_teq0 _ _).mpr rfl)⟩)
  exact XCK_not_teq_u ((XCK_F.holdsAt_teq _ _ _ _ _).mp h2)

/-! ### Booleanism, TCBF and CBF hold -/

theorem XCK_closeAll : ∀ (k : Nat) (ψ : Fm (ctxT k)),
    (∀ env : XCK_F.U.Env (ctxT k) (fun i => i.elim0), XCK_F.HoldsAt ψ (fun i => i.elim0) env (0 : Fin 3)) →
    XCK_F.HoldsAt (closeAll k ψ) (fun i => i.elim0) () (0 : Fin 3)
  | 0, _, h => h ()
  | k + 1, ψ, h => XCK_closeAll k (all tyT ψ) fun env => (XCK_F.holdsAt_all _ _ _ _ _).mpr fun v _ => h (env, v)

theorem XCK_Bool : ∀ φ, BoolSch φ → XCK_F.Valid φ := by
  rintro _ ⟨k, P, Q, hT, rfl⟩
  refine XCK_Valid_of (XCK_closeAll k _ fun env => ?_)
  refine (XCK_F.holdsAt_eqv tyT tyT _ _ _ env _).mpr ((XCK_heq0 _ _ _).mpr ?_)
  intro v _
  exact Iff.trans (XCK_F.holdsAt_inst P (varsT k) _ env v)
    (Iff.trans (show P.evalP _ ↔ Q.evalP _ from hT _) (XCK_F.holdsAt_inst Q (varsT k) _ env v).symm)

theorem XCK_TCBF : ∀ χ, TCBFSch χ → XCK_F.Valid χ := by
  rintro _ ⟨φ, rfl⟩
  refine XCK_Valid_of ((XCK_F.holdsAt_imp _ _ _ _ _).mpr fun h => ?_)
  refine (XCK_F.holdsAt_tall _ _ _ _).mpr fun a ha => (XCK_box0 _ _ _).mpr fun v hv => ?_
  exact (XCK_F.holdsAt_tall _ _ _ _).mp ((XCK_box0 _ _ _).mp h v hv) a (XCK_U.D_mono _ _ _ hv ha)

theorem XCK_CBF : XCK_F.Valid CBF := by
  refine XCK_Valid_of ?_
  refine (XCK_F.holdsAt_tall _ _ _ _).mpr fun a _ => (XCK_F.holdsAt_all _ _ _ _ _).mpr fun _ _ => ?_
  refine (XCK_F.holdsAt_imp _ _ _ _ _).mpr fun h => (XCK_F.holdsAt_all _ _ _ _ _).mpr fun x hx => ?_
  refine (XCK_box0 _ _ _).mpr fun v hv => ?_
  exact (XCK_F.holdsAt_all _ _ _ _ _).mp ((XCK_box0 _ _ _).mp h v hv) x (XCK_U.rel_mono a (0 : Fin 3) v x x hv hx)

end Kr
end PIF
