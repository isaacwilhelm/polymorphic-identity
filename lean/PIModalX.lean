import PIHaeQs
import PICongQs

/-!
# Necessity of identity across types, and Functional Choice

Three further principles: the necessity of identity and of distinctness for items of any two
types (NI×, ND×), and Functional Choice (every total relation contains a function). In the
standard semantics, and in the semantics with worlds, with tags, and of algebras, every function
between the relevant sets is an item, and Functional Choice holds.
-/
set_option autoImplicit false

namespace PIF
open Tm

/-- (NI×) `𝔸α 𝔸β ∀_α x ∀_β y (x ≡ y → □(x ≡ y))` -/
def NIX : Fm Ctx.nil :=
  tall (tall (all tv1 (all tv0 (imp (eqv tv1 tv0 (.var (.there .here)) (.var .here))
    (boxF (eqv tv1 tv0 (.var (.there .here)) (.var .here)))))))

/-- (ND×) `𝔸α 𝔸β ∀_α x ∀_β y (¬ x ≡ y → □¬(x ≡ y))` -/
def NDX : Fm Ctx.nil :=
  tall (tall (all tv1 (all tv0 (imp (neg (eqv tv1 tv0 (.var (.there .here)) (.var .here)))
    (boxF (neg (eqv tv1 tv0 (.var (.there .here)) (.var .here))))))))

/-- (Choice) `𝔸α 𝔸β ∀_{α→β→t} R (∀_α x ∃_β y R x y → ∃_{α→β} f ∀_α x R x (f x))` -/
def Choice : Fm Ctx.nil :=
  tall (tall (all (tv1.arrow tv0.pred) (imp
    (all tv1 (ex tv0 (.app (.app (.var (.there (.there .here))) (.var (.there .here))) (.var .here))))
    (ex (tv1.arrow tv0) (all tv1 (.app (.app (.var (.there (.there .here))) (.var .here))
      (.app (.var (.there .here)) (.var .here))))))))

/-! ## Derivations -/

section Derivations
open Derive
variable {S : Fm Ctx.nil → Prop}

abbrev ExyX : Fm C11 := Tm.eqv tv1 tv0 (.var (.there .here)) (.var .here)

set_option maxHeartbeats 4000000 in
/-- Collapse proves NI×. -/
theorem d_NIX_of_Collapse (hC : S Collapse) : Prov S Ctx.nil NIX := by
  have h : Ent S C11 ([] ++ [ExyX]) (boxF ExyX) :=
    Ent.mp ((Ent.axm (Γ := C11) (Hs := [ExyX]) hC).inst ExyX) (Ent.hyp _ 0 (by decide))
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.gen tv1 (Hs := []) (Ent.gen tv0 (Hs := []) (Ent.intro h)))))

set_option maxHeartbeats 4000000 in
/-- Collapse proves ND×. -/
theorem d_NDX_of_Collapse (hC : S Collapse) : Prov S Ctx.nil NDX := by
  have h : Ent S C11 ([] ++ [neg ExyX]) (boxF (neg ExyX)) :=
    Ent.mp ((Ent.axm (Γ := C11) (Hs := [neg ExyX]) hC).inst (neg ExyX)) (Ent.hyp _ 0 (by decide))
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.gen tv1 (Hs := []) (Ent.gen tv0 (Hs := []) (Ent.intro h)))))

set_option maxHeartbeats 4000000 in
/-- NI× proves NI≡: take `β` to be `α`. -/
theorem d_NIEqv_of_NIX (hN : S NIX) : Prov S Ctx.nil NIEqv := by
  have h : Ent S Γxy [] (Exy.imp (boxF Exy)) :=
    ((((Ent.axm (Γ := Γxy) (Hs := []) hN).tinst tv0).tinst tv0).inst (.var (.there .here))).inst (.var .here)
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.gen tv0 (Hs := []) (Ent.gen tv0 (Hs := []) h)))

set_option maxHeartbeats 4000000 in
/-- Disjoint and NI≡ prove NI×: if `α ≈ β`, LL≈ carries NI≡ at `α` over to the pair `α, β`; if
not, Disjoint says that nothing of type `α` is identical to anything of type `β`. -/
theorem d_NIX_of_Disjoint (hD : S Disjoint) (hN : S NIEqv) : Prov S Ctx.nil NIX := by
  have hQ : Ent S C11 [Tm.teq tv1 tv0] (LLTeq (Tm.tlam (Tm.all tv2 (Tm.all tv0 (Tm.imp
      (Tm.eqv tv2 tv0 (.var (.there .here)) (.var .here)) (boxF (Tm.eqv tv2 tv0 (.var (.there .here)) (.var .here))))))
      : Tm C11 (.pi .t))) := Ent.ofProv (Prov.llTeq _)
  have h1 : Ent S C11 [Tm.teq tv1 tv0] ((Tm.teq tv1 tv0).imp
      ((Tm.all tv1 (Tm.all tv1 (Tm.imp (Tm.eqv tv1 tv1 (.var (.there .here)) (.var .here))
        (boxF (Tm.eqv tv1 tv1 (.var (.there .here)) (.var .here)))))).imp
      (Tm.all tv1 (Tm.all tv0 (Tm.imp (Tm.eqv tv1 tv0 (.var (.there .here)) (.var .here))
        (boxF (Tm.eqv tv1 tv0 (.var (.there .here)) (.var .here)))))))) :=
    Ent.beta ((hQ.tinst tv1).tinst tv0) (BetaEq.imp (.refl _) (BetaEq.imp (BetaEq.tbeta _ _) (BetaEq.tbeta _ _)))
  have hA := (Ent.axm (Γ := C11) (Hs := [Tm.teq tv1 tv0]) hN).tinst tv1
  have hB := Ent.mp2 h1 (Ent.hyp _ 0 (by decide)) hA
  have hE : Ent S C11 ([] ++ [Tm.teq tv1 tv0]) (ExyX.imp (boxF ExyX)) :=
    (hB.inst (.var (.there .here))).inst (.var .here)
  have hpos : Ent S C11 [] ((Tm.teq tv1 tv0).imp (ExyX.imp (boxF ExyX))) := Ent.intro hE
  have hDj : Ent S C11 ([] ++ [neg (Tm.teq tv1 tv0)]) (neg ExyX) :=
    ((Ent.mp (((Ent.axm (Γ := C11) (Hs := [neg (Tm.teq tv1 tv0)]) hD).tinst tv1).tinst tv0)
      (Ent.hyp _ 0 (by decide))).inst (.var (.there .here))).inst (.var .here)
  have hneg : Ent S C11 [] ((neg (Tm.teq tv1 tv0)).imp (neg ExyX)) := Ent.intro hDj
  have hfin : Ent S C11 [] (ExyX.imp (boxF ExyX)) :=
    Ent.mp2 (Ent.taut (.imp (.imp (.atom 0) (.imp (.atom 1) (.atom 2)))
      (.imp (.imp (.neg (.atom 0)) (.neg (.atom 1))) (.imp (.atom 1) (.atom 2))))
      (v3 (Tm.teq tv1 tv0) ExyX (boxF ExyX))
      (fun v f g e => (Classical.em (v 0)).elim (fun a => f a e) (fun a => absurd e (g a)))) hpos hneg
  exact Ent.toProv (Ent.tgen (Hs := []) (Ent.tgen (Hs := []) (Ent.gen tv1 (Hs := []) (Ent.gen tv0 (Hs := []) hfin))))

end Derivations

/-! ## The standard semantics -/

namespace Frame
variable (F : Frame)

theorem tr_Choice : F.Tr Choice ↔ ∀ a b (R : F.U.El a → F.U.El b → Prop),
    (∀ x, ∃ y, R x y) → ∃ f : F.U.El a → F.U.El b, ∀ x, R x (f x) := Iff.rfl

theorem tr_Collapse : F.Tr Collapse ↔ ∀ p : Prop, p → F.eqv .t .t p (¬ ∀ q : Prop, q) := Iff.rfl

/-- Collapse holds in every standard model: a truth is the proposition `⊤`. -/
theorem Collapse_valid (hM : F.IsModelPIm) : F.Valid Collapse :=
  (F.valid_iff_tr _).mpr <| F.tr_Collapse.mpr fun p hp =>
    (propext ⟨fun _ h => h False, fun _ => hp⟩ : p = ¬ ∀ q : Prop, q) ▸ F.tr_RefEqv.mp ((F.valid_iff_tr _).mp hM.refEqv) .t p

/-- Functional Choice holds in every standard frame. -/
theorem Choice_valid : F.Valid Choice :=
  (F.valid_iff_tr _).mpr <| F.tr_Choice.mpr fun _ _ _ h => ⟨fun x => Classical.choose (h x), fun x => Classical.choose_spec (h x)⟩

end Frame

/-! ## Worlds -/

namespace Wd
namespace Frame
variable (F : Frame)

theorem tr_Choice : F.Tr Choice ↔ ∀ a b (R : F.U.El a → F.U.El b → F.U.W → Prop),
    (∀ x, ∃ y, R x y F.U.w0) → ∃ f : F.U.El a → F.U.El b, ∀ x, R x (f x) F.U.w0 := Iff.rfl

theorem Choice_valid : F.Valid Choice :=
  (F.valid_iff_tr _).mpr <| F.tr_Choice.mpr fun _ _ _ h => ⟨fun x => Classical.choose (h x), fun x => Classical.choose_spec (h x)⟩

theorem tr_NIX : F.Tr NIX ↔ ∀ a b (x : F.U.El a) (y : F.U.El b), F.eqv a b x y F.U.w0 →
    F.eqv .t .t (F.eqv a b x y) (F.eval (topF : Fm Ctx.nil) (fun i => i.elim0) ()) F.U.w0 := Iff.rfl

theorem tr_NDX : F.Tr NDX ↔ ∀ a b (x : F.U.El a) (y : F.U.El b), ¬ F.eqv a b x y F.U.w0 →
    F.eqv .t .t (fun w => ¬ F.eqv a b x y w) (F.eval (topF : Fm Ctx.nil) (fun i => i.elim0) ()) F.U.w0 := Iff.rfl

/-- NI× holds when identity at the actual world persists to every world. -/
theorem NIX_of (hr : ∀ p, F.eqv .t .t p p F.U.w0)
    (h : ∀ a b (x : F.U.El a) (y : F.U.El b), F.eqv a b x y F.U.w0 → ∀ w, F.eqv a b x y w) : F.Valid NIX :=
  (F.valid_iff_tr _).mpr <| F.tr_NIX.mpr fun a b x y hxy => by
    have e : F.eqv a b x y = F.eval (topF : Fm Ctx.nil) (fun i => i.elim0) () := by
      refine Eq.trans ?_ (F.eval_topF (Γ := Ctx.nil) _ _).symm; funext w; exact propext ⟨fun _ => trivial, fun _ => h a b x y hxy w⟩
    rw [e]; exact hr _

/-- ND× holds when distinctness at the actual world persists to every world. -/
theorem NDX_of (hr : ∀ p, F.eqv .t .t p p F.U.w0)
    (h : ∀ a b (x : F.U.El a) (y : F.U.El b), ¬ F.eqv a b x y F.U.w0 → ∀ w, ¬ F.eqv a b x y w) : F.Valid NDX :=
  (F.valid_iff_tr _).mpr <| F.tr_NDX.mpr fun a b x y hxy => by
    have e : (fun w => ¬ F.eqv a b x y w) = F.eval (topF : Fm Ctx.nil) (fun i => i.elim0) () := by
      refine Eq.trans ?_ (F.eval_topF (Γ := Ctx.nil) _ _).symm; funext w; exact propext ⟨fun _ => trivial, fun _ => h a b x y hxy w⟩
    rw [e]; exact hr _

/-- NI× fails when two items are identical at the actual world but not at another. -/
theorem not_NIX_of (hb : ∀ p q, F.eqv .t .t p q F.U.w0 → p = q) {a b : Code F.U.Base} (x : F.U.El a) (y : F.U.El b)
    (h0 : F.eqv a b x y F.U.w0) (w : F.U.W) (hw : ¬ F.eqv a b x y w) : ¬ F.Valid NIX := fun hv => by
  have e := (hb _ _ (F.tr_NIX.mp ((F.valid_iff_tr _).mp hv) a b x y h0)).trans (F.eval_topF (Γ := Ctx.nil) _ _)
  exact hw (cast (congrFun e w).symm trivial)

/-- ND× fails when two items are distinct at the actual world but identical at another. -/
theorem not_NDX_of (hb : ∀ p q, F.eqv .t .t p q F.U.w0 → p = q) {a b : Code F.U.Base} (x : F.U.El a) (y : F.U.El b)
    (h0 : ¬ F.eqv a b x y F.U.w0) (w : F.U.W) (hw : F.eqv a b x y w) : ¬ F.Valid NDX := fun hv => by
  have e := (hb _ _ (F.tr_NDX.mp ((F.valid_iff_tr _).mp hv) a b x y h0)).trans (F.eval_topF (Γ := Ctx.nil) _ _)
  exact cast (congrFun e w).symm trivial hw

end Frame

theorem RD.NDX_valid (D : RD) : D.frame.Valid NDX :=
  D.frame.NDX_of (fun _ => ⟨rfl, HEq.rfl, D.hE⟩) fun _ _ _ _ h _ hw => h ⟨hw.1, hw.2.1, D.hE⟩
theorem RD.NIX_valid (D : RD) (hE : ∀ w, D.Ee w) : D.frame.Valid NIX :=
  D.frame.NIX_of (fun _ => ⟨rfl, HEq.rfl, D.hE⟩) fun _ _ _ _ h w => ⟨h.1, h.2.1, hE w⟩

theorem Mw_NIX : DW.frame.Valid NIX := DW.NIX_valid fun _ => trivial
theorem Mw_NDX : DW.frame.Valid NDX := DW.NDX_valid
theorem Mnd_NIX : DND.frame.Valid NIX := DND.NIX_valid fun _ => trivial
theorem Mnd_NDX : DND.frame.Valid NDX := DND.NDX_valid
theorem Mni_NIX : DNI.frame.Valid NIX := DNI.NIX_valid fun _ => trivial
theorem Mni_NDX : DNI.frame.Valid NDX := DNI.NDX_valid
theorem Mie_NDX : DIE.frame.Valid NDX := DIE.NDX_valid

theorem Mtt_NIX : MttF.Valid NIX :=
  MttF.NIX_of (fun _ => ⟨rfl, Or.inl HEq.rfl⟩) fun _ _ _ _ h _ => h
theorem Mtt_NDX : MttF.Valid NDX :=
  MttF.NDX_of (fun _ => ⟨rfl, Or.inl HEq.rfl⟩) fun _ _ _ _ h _ => h

theorem MtwC_NIX : MtwCF.Valid NIX := MtwCF.NIX_of (fun _ => ⟨Or.inl rfl, HEq.rfl⟩) fun _ _ _ _ h _ => h
theorem MtwC_NDX : MtwCF.Valid NDX := MtwCF.NDX_of (fun _ => ⟨Or.inl rfl, HEq.rfl⟩) fun _ _ _ _ h _ => h
theorem MhaeC_NIX : MhaeCF.Valid NIX := MhaeCF.NIX_of (fun _ => rfl) fun _ _ _ _ h _ => h
theorem MhaeC_NDX : MhaeCF.Valid NDX := MhaeCF.NDX_of (fun _ => rfl) fun _ _ _ _ h _ => h

theorem MieC_not_NIX : ¬ MieCF.Valid NIX :=
  MieCF.not_NIX_of (fun _ _ h => MieC_eq _ _ _ _ h) (a := .e) (b := .base ()) () ()
    (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩) false (fun h => h.elim (fun h => nomatch h.1) (fun h => Bool.noConfusion h.1))
theorem MieC_NDX : MieCF.Valid NDX :=
  MieCF.NDX_of (fun _ => Or.inl ⟨rfl, HEq.rfl⟩) fun _ _ _ _ h _ hw =>
    h (hw.elim Or.inl (fun hw' => Or.inr ⟨rfl, hw'.2⟩))
theorem MieX_not_NIX : ¬ MieXF.Valid NIX :=
  MieXF.not_NIX_of (fun _ _ h => MieX_eq _ _ _ _ h) (a := .e) (b := .base ()) () ()
    (Or.inr ⟨rfl, ⟨(fun e => nomatch e), rfl, trivial⟩⟩) false
    (fun h => h.elim (fun h => nomatch h.1) (fun h => Bool.noConfusion h.1))
theorem MieX_NDX : MieXF.Valid NDX :=
  MieXF.NDX_of (fun _ => Or.inl ⟨rfl, HEq.rfl⟩) fun _ _ _ _ h _ hw =>
    h (hw.elim Or.inl (fun hw' => Or.inr ⟨rfl, hw'.2⟩))
theorem MhieC_not_NIX : ¬ MhieF.Valid NIX :=
  MhieF.not_NIX_of (fun _ _ h => MhieC_eq _ _ _ _ h) (a := .e) (b := .base ()) () () (Or.inr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩)
    false (fun h => h.elim (fun h => nomatch congrArg Sigma.fst h) (fun h => Bool.noConfusion h.1))
theorem MhieC_NDX : MhieF.Valid NDX :=
  MhieF.NDX_of (fun _ => Or.inl rfl) fun _ _ _ _ h _ hw =>
    h (hw.elim Or.inl (fun hw' => Or.inr ⟨rfl, hw'.2⟩))

end Wd

namespace Al
namespace Frame
variable (F : Frame)

/-- Functional Choice holds in every frame of this semantics. -/
theorem Choice_valid : F.Valid Choice := by
  intro ρ env
  refine (F.holds_tall _ _ _).mpr fun a => (F.holds_tall _ _ _).mpr fun b => ?_
  refine (F.holds_all _ _ _ _).mpr fun R => (F.holds_imp _ _ _ _).mpr fun h => ?_
  have h' := fun x => (F.holds_ex _ _ _ _).mp ((F.holds_all _ _ _ _).mp h x)
  exact (F.holds_ex _ _ _ _).mpr ⟨fun x => Classical.choose (h' x),
    (F.holds_all _ _ _ _).mpr fun x => Classical.choose_spec (h' x)⟩

end Frame
end Al

namespace Tg
namespace Frame
variable (F : Frame)

/-- Functional Choice holds in every frame of this semantics. -/
theorem Choice_valid : F.Valid Choice := by
  intro ρ env
  refine (F.holds_tall _ _ _).mpr fun a => (F.holds_tall _ _ _).mpr fun b => ?_
  refine (F.holds_all _ _ _ _).mpr fun R => (F.holds_imp _ _ _ _).mpr fun h => ?_
  have h' := fun x => (F.holds_ex _ _ _ _).mp ((F.holds_all _ _ _ _).mp h x)
  exact (F.holds_ex _ _ _ _).mpr ⟨fun x => Classical.choose (h' x),
    (F.holds_all _ _ _ _).mpr fun x => Classical.choose_spec (h' x)⟩

end Frame
end Tg

namespace AlI
namespace Frame
variable (F : Frame)

/-- Functional Choice holds in every frame with intensional functions. -/
theorem Choice_valid : F.Valid Choice := by
  intro ρ env
  refine (F.holds_tall _ _ _).mpr fun a => (F.holds_tall _ _ _).mpr fun b => ?_
  refine (F.holds_all _ _ _ _).mpr fun R => (F.holds_imp _ _ _ _).mpr fun h => ?_
  have h' := fun x => (F.holds_ex _ _ _ _).mp ((F.holds_all _ _ _ _).mp h x)
  exact (F.holds_ex _ _ _ _).mpr ⟨(fun x => Classical.choose (h' x), true),
    (F.holds_all _ _ _ _).mpr fun x => Classical.choose_spec (h' x)⟩

end Frame
end AlI

/-! ## Kripke models -/

namespace Kr
namespace Frame
variable (U : Univ)

theorem simple_eqv_mono {a b : Code U.Base} {x : U.El a} {y : U.El b} {w v : U.W} (hv : U.R w v)
    (h : (Frame.simple U).eqv a b x y w) : (Frame.simple U).eqv a b x y v :=
  let ⟨e, hr⟩ := h; ⟨e, U.rel_mono _ w v _ _ hv hr⟩

/-- In a simple Kripke frame, identity persists along `R`, so NI× holds. -/
theorem simple_NIX : (S U).Valid NIX := by
  refine simple_Valid_of U ?_
  refine ((S U).holdsAt_tall _ _ _ _).mpr fun a _ => ((S U).holdsAt_tall _ _ _ _).mpr fun b _ => ?_
  refine ((S U).holdsAt_all _ _ _ _ _).mpr fun x _ => ((S U).holdsAt_all _ _ _ _ _).mpr fun y _ => ?_
  refine ((S U).holdsAt_imp _ _ _ _ _).mpr fun h => (simple_box U _ _ _ _).mpr fun v hv => ?_
  exact ((S U).holdsAt_eqv _ _ _ _ _ _ _).mpr (simple_eqv_mono U hv (((S U).holdsAt_eqv _ _ _ _ _ _ _).mp h))

end Frame

/-! ### `𝔐_k,ch`: Functional Choice fails

Two worlds; the actual world sees both, and the other sees only itself. There are four entities
`0, 1, 2, 3`, distinct at the actual world; at the other world, `0` and `1` are identical. The
relation `R x y`, which at the actual world says that `y` is `2` if `x` is even and `3` if `x` is
odd, and holds everywhere at the other world, relates each entity to some entity. But a function
choosing these values would send `0` and `1` to `2` and `3`, which are distinct at the other world,
where `0` and `1` are identical; so it is not an item. -/

def UCh : Univ where
  W := Bool
  w0 := true
  R := fun w v => w = true ∨ v = false
  Rrefl := fun w => by cases w <;> simp
  Rtrans := by
    intro u v w h1 h2
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · rcases h2 with h2 | h2
      · exact absurd (h1.symm.trans h2) Bool.false_ne_true
      · exact Or.inr h2
  E := Fin 4
  Base := Empty
  B := Empty.elim
  neE := ⟨0⟩
  neB := fun b => b.elim
  re := fun w x y => x = y ∨ (w = false ∧ x.val < 2 ∧ y.val < 2)
  rb := fun _ b => b.elim
  re_refl := fun _ _ => Or.inl rfl
  re_symm := fun _ _ _ h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.1, h.2.2, h.2.1⟩)
  re_trans := by
    intro w x y z h1 h2
    rcases h1 with rfl | ⟨hw, hx, _⟩
    · exact h2
    · rcases h2 with rfl | ⟨_, _, hz⟩
      · exact Or.inr ⟨hw, hx, by assumption⟩
      · exact Or.inr ⟨hw, hx, hz⟩
  re_mono := by
    intro w v x y h hxy
    rcases hxy with e | ⟨hw, hx, hy⟩
    · exact Or.inl e
    · subst hw
      rcases h with h | h
      · exact absurd h Bool.false_ne_true
      · exact Or.inr ⟨h, hx, hy⟩
  rb_refl := fun _ b => b.elim
  rb_symm := fun _ b => b.elim
  rb_trans := fun _ b => b.elim
  rb_mono := fun _ _ b => b.elim
  D := fun _ _ => True
  D_e := fun _ => trivial
  D_t := fun _ => trivial
  D_arr := fun _ _ _ _ _ => trivial
  D_mono := fun _ _ _ _ _ => trivial

abbrev MchK : Frame := Frame.simple UCh

/-- The chosen value. -/
def gCh (x : Fin 4) : Fin 4 := if x.val % 2 = 0 then 2 else 3

def RCh : UCh.El (.arr .e (.arr .e .t)) := fun x y w => w = false ∨ y = gCh x

theorem RCh_adm : UCh.rel (.arr .e (.arr .e .t)) true RCh RCh := by
  intro v hv x x' hx u hu y y' hy s hs
  cases s
  · exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩
  · have hu' : u = true := hs.elim id (fun h => absurd h (by decide))
    subst hu'
    have hv' : v = true := hu.elim id (fun h => absurd h (by decide))
    subst hv'
    have ex : x = x' := hx.elim id (fun h => absurd h.1 (by decide))
    have ey : y = y' := hy.elim id (fun h => absurd h.1 (by decide))
    subst ex; subst ey
    exact Iff.rfl

theorem Mch_not_Choice : ¬ MchK.Valid Choice := by
  refine Frame.simple_not_Valid UCh fun h => ?_
  have h1 := (MchK.holdsAt_tall _ _ _ _).mp h .e trivial
  have h2 := (MchK.holdsAt_tall _ _ _ _).mp h1 .e trivial
  have h3 := (MchK.holdsAt_all _ _ _ _ _).mp h2 RCh RCh_adm
  have h4 := (MchK.holdsAt_imp _ _ _ _ _).mp h3 ((MchK.holdsAt_all _ _ _ _ _).mpr fun x _ =>
    (MchK.holdsAt_ex _ _ _ _ _).mpr ⟨gCh x, Or.inl rfl, Or.inr rfl⟩)
  obtain ⟨f, hf, hfx⟩ := (MchK.holdsAt_ex _ _ _ _ _).mp h4
  have hall := (MchK.holdsAt_all _ _ _ _ _).mp hfx
  have f0 : (f : Fin 4 → Fin 4) (0 : Fin 4) = gCh (0 : Fin 4) :=
    (show true = false ∨ (f : Fin 4 → Fin 4) (0 : Fin 4) = gCh (0 : Fin 4) from
      hall (0 : Fin 4) (Or.inl rfl)).resolve_left (fun h => Bool.noConfusion h)
  have f1 : (f : Fin 4 → Fin 4) (1 : Fin 4) = gCh (1 : Fin 4) :=
    (show true = false ∨ (f : Fin 4 → Fin 4) (1 : Fin 4) = gCh (1 : Fin 4) from
      hall (1 : Fin 4) (Or.inl rfl)).resolve_left (fun h => Bool.noConfusion h)
  have hr : UCh.re false ((f : Fin 4 → Fin 4) (0 : Fin 4)) ((f : Fin 4 → Fin 4) (1 : Fin 4)) :=
    hf false (Or.inr rfl) (0 : Fin 4) (1 : Fin 4) (Or.inr ⟨rfl, by decide, by decide⟩)
  rw [f0, f1] at hr
  rcases hr with e | ⟨_, _, h3⟩
  · exact absurd e (by decide)
  · exact absurd h3 (by decide)

theorem Mch_not_NDX : ¬ MchK.Valid NDX := by
  refine Frame.simple_not_Valid UCh fun h => ?_
  have h1 := (MchK.holdsAt_tall _ _ _ _).mp ((MchK.holdsAt_tall _ _ _ _).mp h .e trivial) .e trivial
  have h2 := (MchK.holdsAt_all _ _ _ _ _).mp ((MchK.holdsAt_all _ _ _ _ _).mp h1 (show Fin 4 from 0) (Or.inl rfl))
    (show Fin 4 from 1) (Or.inl rfl)
  refine (MchK.holdsAt_neg _ _ _ _).mp ((Frame.simple_box UCh _ _ _ _).mp ((MchK.holdsAt_imp _ _ _ _ _).mp h2
    ((MchK.holdsAt_neg _ _ _ _).mpr fun he => ?_)) false (Or.inr rfl)) ?_
  · have he' := (MchK.holdsAt_eqv _ _ _ _ _ _ _).mp he
    have := (Frame.simple_eqv_same UCh .e (show Fin 4 from 0) (show Fin 4 from 1) true).mp he'
    rcases this with e | ⟨hw, _⟩
    · exact absurd e (by decide)
    · exact absurd hw (by decide)
  · exact (MchK.holdsAt_eqv _ _ _ _ _ _ _).mpr
      ((Frame.simple_eqv_same UCh .e (show Fin 4 from 0) (show Fin 4 from 1) false).mpr
        (Or.inr ⟨rfl, by decide, by decide⟩))

theorem Mch_NIX : MchK.Valid NIX := Frame.simple_NIX UCh
theorem Mch_Class : ∀ χ, ClassSch χ → MchK.Valid χ := Frame.simple_Class UCh
theorem Mch_LLEqv : MchK.Valid LLEqv := fun ρ hρ env henv => Frame.simple_LLEqv UCh _ ρ hρ env henv
theorem Mch_isModelAt : MchK.IsModelAt := Frame.simple_isModelAt UCh
theorem Mch_Disjoint : MchK.Valid Disjoint := Frame.simple_Disjoint UCh
theorem Mch_Cong : MchK.Valid Cong := Frame.simple_Cong UCh
theorem Mch_Inj : MchK.Valid Inj := Frame.simple_Inj UCh
theorem Mch_ExtT : MchK.Valid ExtT := Frame.simple_ExtT UCh

end Kr

namespace Al

section MqX
variable (TA TE : (Code Empty → (Bool → Prop)) → Prop)

/-- In `𝔐_q`, identity is rigid, so NI× holds. -/
theorem Mq_NIX : (MqF TA TE).Valid NIX := by
  intro ρ env
  refine ((MqF TA TE).holds_tall _ _ _).mpr fun a => ((MqF TA TE).holds_tall _ _ _).mpr fun b => ?_
  refine ((MqF TA TE).holds_all _ _ _ _).mpr fun x => ((MqF TA TE).holds_all _ _ _ _).mpr fun y => ?_
  refine ((MqF TA TE).holds_imp _ _ _ _).mpr fun hxy => ?_
  refine ((MqF TA TE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  exact (((MqF TA TE).eval_eqv _ _ _ _ _ _).trans (funext fun _ => propext ⟨fun _ => trivial, fun _ => hxy⟩)).trans
    (Mq_top TA TE (Γ := ((Ctx.nil.text.text).ext tv1).ext tv0) _ _).symm

/-- In `𝔐_q`, distinctness is rigid, so ND× holds. -/
theorem Mq_NDX : (MqF TA TE).Valid NDX := by
  intro ρ env
  refine ((MqF TA TE).holds_tall _ _ _).mpr fun a => ((MqF TA TE).holds_tall _ _ _).mpr fun b => ?_
  refine ((MqF TA TE).holds_all _ _ _ _).mpr fun x => ((MqF TA TE).holds_all _ _ _ _).mpr fun y => ?_
  refine ((MqF TA TE).holds_imp _ _ _ _).mpr fun hxy => ?_
  refine ((MqF TA TE).holds_eqv_t _ _ _ _).mpr ⟨rfl, heq_of_eq ?_⟩
  refine Eq.trans ?_ (Mq_top TA TE (Γ := ((Ctx.nil.text.text).ext tv1).ext tv0) _ _).symm
  funext w
  refine propext ⟨fun _ => trivial, fun _ hw => ((MqF TA TE).holds_neg _ _ _).mp hxy ?_⟩
  have e := (MqF TA TE).eval_eqv (Γ := ((Ctx.nil.text.text).ext tv1).ext tv0) tv1 tv0 (.var (.there .here)) (.var .here)
    (scons b (scons a ρ)) ((env, x), y)
  have hw' := congrFun e w ▸ hw
  exact cast (congrFun e true).symm hw'

end MqX
end Al

namespace Kr
theorem Mbf_NIX : MbfK.Valid NIX := Frame.simple_NIX UBF
end Kr

end PIF
