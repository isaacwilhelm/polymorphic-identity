import PIBF
set_option autoImplicit false

namespace PIF

/-- In `𝔐_tow,2`, no entity is identified with a property: the key of the entity is `(false, e)`, and
the key of a property is either `(_, β → K)` or `(true, e)`. -/
theorem Mtow2_Slogan : Mtow2.Valid Slogan := by
  refine (Mtow2.valid_iff_tr _).mpr ?_
  show ∀ (x : unitUniv.E) (b : Code Empty) (y : unitUniv.El b → Prop), ¬ tow2Rel ⟨.e, x⟩ ⟨.arr b .t, y⟩
  intro x b y h
  rcases h with h | ⟨k, h1, h2⟩
  · exact nomatch congrArg Sigma.fst h
  · have hk : k = (false, .e) := by
      have e : (some (false, .e) : Option (Bool × Code Empty)) = some k := h1
      injection e with e; exact e.symm
    subst hk
    rcases skey_arr (show skey (.arr b .t) y = some (false, .e) from h2) with ⟨K, e, _⟩ | ⟨_, hs⟩
    · injection e with _ e2; exact nomatch e2
    · exact Bool.noConfusion (congrArg Prod.fst (seedK_eq hs).1)

end PIF
