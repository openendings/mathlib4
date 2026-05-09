import Mathlib.CategoryTheory.Monad.Basic

namespace CategoryTheory

variable {C : Type*} [Category* C]

section

variable (T : Monad C) (U : Comonad C)
variable (S : Monad C)

variable (X Y : C)

/-! These tests check that the basic `Monad`(/`Comonad`) API can be used in downstream `simp` code
as-is (without e.g. `dsimp%`, `erw`).
-/

section _Monad

#guard_msgs in
example : T.map (T.μ.app X) ≫ T.μ.app X = T.μ.app _ ≫ T.μ.app _ := by
  simp [T.assoc]

-- TODO: isolate left_unit
-- TODO: isolate right_unit

/-! Tests isolatint Monad.unit_naturality -/

#guard_msgs in
#defeq_abuse in
example :
    T.μ.app X ≫ T.η.app (T.obj X) = T.η.app _ ≫ T.map (T.μ.app X) := by
  simp [← T.unit_naturality]

#guard_msgs in
#defeq_abuse in
example (f : X ⟶ T.obj Y) :
    f = T.η.app X ≫ T.map f ≫ T.μ.app Y := by
  simp [← T.unit_naturality_assoc]

-- TODO: isolate mu_naturality
-- TODO: isolate mu_naturality_assoc

end _Monad

section _Comonad

-- TODO: isolate left_counit
-- TODO: isolate right_counit

#guard_msgs in
example : U.δ.app X ≫ U.map (U.δ.app X) = U.δ.app _ ≫ U.δ.app _ := by
  simp [U.coassoc]

#guard_msgs in
example (f : U.obj X ⟶ Y) :
    U.ε.app (U.obj X) ≫ f = U.map f ≫ U.ε.app Y := by
  simp [U.counit_naturality]

end _Comonad

end
