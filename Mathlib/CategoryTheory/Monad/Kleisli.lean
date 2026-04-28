/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monad.Basic

import Batteries.Tactic.PrintPrefix
import Mathlib.Tactic.Check

/-! # Kleisli category on a (co)monad

This file defines the Kleisli category on a monad `(T, η_ T, μ_ T)` as well as the co-Kleisli
category on a comonad `(U, ε_ U, δ_ U)`. It also defines the Kleisli adjunction which gives rise to
the monad `(T, η_ T, μ_ T)` as well as the co-Kleisli adjunction which gives rise to the comonad
`(U, ε_ U, δ_ U)`.

## References
* [Riehl, *Category theory in context*, Definition 5.2.9][riehl2017]
-/

@[expose] public section


namespace CategoryTheory

universe v u

-- morphism levels before object levels. See note [category theory universes].
variable {C : Type u} [Category.{v} C]

/-- The objects for the Kleisli category of the monad `T : Monad C`, which are the same
thing as objects of the base category `C`.
-/
structure Kleisli (T : Monad C) where mk (T) ::
  /-- The underlying object of the base category. -/
  of : C

namespace Kleisli

variable {T : Monad C}

@[simp] lemma mk_of (c : Kleisli T) : Kleisli.mk T c.of = c := rfl
lemma of_mk (c : C) : (Kleisli.mk T c).of = c := rfl

theorem comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ T.η.app Y) ≫ T.map (g ≫ T.η.app Z) ≫ T.μ.app Z = (f ≫ g) ≫ T.η.app Z := by
  simp [Monad.unit_naturality, Monad.mu_naturality, Monad.right_unit_assoc]

theorem map_map_of (X : Kleisli T) : (T.toFunctor ⋙ T.toFunctor).obj X.of = T.obj (T.obj X.of) := by
  rfl

/-- For (T : Monad C), morphisms `c ⟶ c'` in the Kleisli category of `T` are
morphisms ` c ⟶ T.obj c'` in `C`. -/
structure Hom (c c' : Kleisli T) where
  /-- The morphism in C underlying the morphism in the Kleisli category. -/
  of : c.of ⟶ T.obj c'.of

instance [Inhabited C] (T : Monad C) : Inhabited (Kleisli T) := ⟨.mk T default⟩

variable (T)

set_option backward.isDefEq.respectTransparency false in
attribute [local ext] Hom in
/-- The Kleisli category on a monad `T`.
cf Definition 5.2.9 in [Riehl][riehl2017]. -/
@[simps!]
instance category : Category (Kleisli T) where
  Hom X Y := Hom X Y
  id X := .mk <| T.η.app X.of
  comp {_} {_} {Z} f g := .mk <| f.of ≫ T.map g.of ≫ T.μ.app Z.of
  id_comp {X} {Y} f := by
    ext
    dsimp
    rw [← T.η.naturality_assoc f.of, T.left_unit]
    apply Category.comp_id
  assoc f g h := by
    simp [Monad.assoc, T.mu_naturality_assoc]

variable {T} in
attribute [local ext] Hom in
@[ext]
lemma hom_ext {x y : Kleisli T} {f g : x ⟶ y} (h : f.of = g.of) : f = g :=
  Hom.ext h

namespace Adjunction

attribute [local ext] Hom in
/-- The left adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps]
def toKleisli : C ⥤ Kleisli T where
  obj X := .mk T X
  map {X} {Y} f := .mk <| f ≫ T.η.app Y
  map_comp {X} {Y} {Z} f g := by
    unfold_projs
    rw [comp]

@[simp]
theorem toKleisli_foo {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Y ⟶ T.obj (of ?m.10)
    X Y:= by
  trivial

theorem foo {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ T.obj Z) :
    Hom.mk (f ≫ g) = (toKleisli T).map f ≫ Hom.mk g := by
  unfold_projs
  apply hom_ext
  simp [toKleisli_map_of]
  set_option pp.explicit true in
    #defeq_abuse in
    simp [Functor.map_id]
  simp_rw [←(T.η.naturality_assoc g)]
  hint

/-- The right adjoint of the adjunction which induces the monad `(T, η_ T, μ_ T)`. -/
@[simps]
def fromKleisli : Kleisli T ⥤ C where
  obj X := T.obj X.of
  map {_} {Y} f := T.map f.of ≫ T.μ.app Y.of
  map_id _ := T.right_unit _
  map_comp {X} {Y} {Z} f g := by
    simp only [category_comp_of, Functor.map_comp, Category.assoc]
    congrm T.map f.of ≫ ?_
    apply Iff.mp <| Eq.congr
      (Eq.symm <| CategoryTheory.whisker_eq _ (T.assoc Z.of))
      (T.μ.naturality_assoc g.of _)
    rfl

  ❌️ (X ⟶ T.obj Z.of) ≃ ((toKleisli T).obj X ⟶ Z) =?= (X ⟶ (fromKleisli T).obj Z) ≃ ((toKleisli T).obj X ⟶ Z)

/- #defeq_abuse in -/
set_option backward.isDefEq.respectTransparency false in
/-- The Kleisli adjunction which gives rise to the monad `(T, η_ T, μ_ T)`.
cf Lemma 5.2.11 of [Riehl][riehl2017]. -/
def adj : toKleisli T ⊣ fromKleisli T :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y := { toFun f := f.of, invFun f := .mk f }
      homEquiv_naturality_left_symm := fun {X} {Y} {Z} f g => by
        simp only [Equiv.coe_fn_symm_mk]
        show_term
          suffices f ≫ g = f ≫ T.η.app Y ≫ T.map g ≫ T.μ.app Z.of by

            simp_all? only [toKleisli_obj_of, fromKleisli_obj]
            simp only [category_comp_of, toKleisli_obj_of, toKleisli_map_of, Category.assoc]
            simp_all
        simp [← T.η.naturality_assoc g] }

set_option backward.isDefEq.respectTransparency false in
/-- The composition of the adjunction gives the original functor. -/
def toKleisliCompFromKleisliIsoSelf : toKleisli T ⋙ fromKleisli T ≅ T :=
  NatIso.ofComponents fun _ => Iso.refl _

theorem fromKleisliCompToKleisli_obj (X : Kleisli T) :
  (fromKleisli T ⋙ toKleisli T).obj X = Kleisli.mk T (T.toFunctor.1 X.of) := by rfl

/--
The counit of `toKleisli T ⊣ fromKleisli T` is pointwise given by `T 𝟭`.
-/
theorem kleisli_counit_app (X : Kleisli T) :
  (adj T).counit.app X = Kleisli.Hom.mk (𝟙 (T.obj X.of)) := by rfl

@[inherit_doc kleisli_counit_app]
theorem kleisli_counit_app_of (X : Kleisli T) :
  ((adj T).counit.app X).of = 𝟙 (T.obj X.of)
  := by rfl

theorem even_here ⦃X Y : Kleisli T⦄ (f : X ⟶ Y)
  (h : (fromKleisli T ⋙ toKleisli T).map f ≫ { of := 𝟙 (T.obj Y.of) } = (adj
  T).counit.app X ≫ (𝟭 (Kleisli T)).map f ) :
  (fromKleisli T ⋙ toKleisli T).map f ≫ { of := 𝟙 (T.obj Y.of) } = (adj
  T).counit.app X ≫ (𝟭 (Kleisli T)).map f := by
  conv_rhs =>
    equals (CategoryStruct.comp ((adj T).counit.app X) ((Functor.id (Kleisli T)).map
        f)) =>
      rw [← (adj T).counit.naturality]
  exact h

theorem even_here? ⦃X Y : Kleisli T⦄ (f : X ⟶ Y)
  (g)
  (h : g = (adj
  T).counit.app X ≫ (𝟭 (Kleisli T)).map f ) :
  g = (adj
  T).counit.app X ≫ (𝟭 (Kleisli T)).map f := by
  conv_rhs =>
    equals (CategoryStruct.comp ((adj T).counit.app X) ((Functor.id (Kleisli T)).map
        f)) =>
      rw [← (adj T).counit.naturality]
  exact h

theorem id_mk_naturality
  ⦃X Y : Kleisli T⦄ (f : X ⟶ Y) :
    (Adjunction.fromKleisli T ⋙ Adjunction.toKleisli T).map
    f ≫ Hom.mk ( 𝟙 (T.obj Y.of) )  =
    Hom.mk ( 𝟙 (T.obj X.of)) ≫ (𝟭 (Kleisli T)).map f := by
  simp_all only [← Adjunction.kleisli_counit_app]
  /- apply even_here? -/
  conv_rhs =>
    equals (CategoryStruct.comp ((adj T).counit.app X) ((Functor.id (Kleisli T)).map
        f)) =>
      clear * - f
      fail_if_success simp_rw [this]
      fail_if_success rw [← (adj T).counit.naturality]
      erw? [← (adj T).counit.naturality]
  skip
  simp_all?
  sorry
  /- simp only [fromKleisliCompToKleisli_obj] -/

theorem HELPME ⦃X Y : Kleisli T⦄ (f : X ⟶ Y) : (Adjunction.fromKleisli T ⋙ Adjunction.toKleisli T).map
    f ≫ Hom.mk ( 𝟙 (T.obj Y.of) )  =
    Hom.mk ( 𝟙 (T.obj X.of)) ≫ (𝟭 (Kleisli T)).map f := by
  simp_all only [← Adjunction.kleisli_counit_app]
  extract_goal using before
  conv_rhs =>
    equals (CategoryStruct.comp ((adj T).counit.app X) ((Functor.id (Kleisli T)).map
        f)) =>
      -- simp_rw [fromKleisliCompToKleisli_obj]
      -- have := fromKleisliCompToKleisli_obj T
      clear * - f
      fail_if_success simp_rw [this]
      fail_if_success rw [← (adj T).counit.naturality]
      erw? [← (adj T).counit.naturality]
  extract_goal using after



end Adjunction

end Kleisli

/-- The objects for the co-Kleisli category of the comonad `U : Comonad C`, which are the same
thing as objects of the base category `C`.
-/
structure Cokleisli (U : Comonad C) where mk (U) ::
  /-- The underlying object of the base category. -/
  of : C

namespace Cokleisli

variable (U : Comonad C)

@[simp] lemma mk_of (c : Cokleisli U) : Cokleisli.mk U c.of = c := rfl
lemma of_mk (c : C) : (Cokleisli.mk U c).of = c := rfl

variable {U} in
/-- For (U : Comonad C), morphisms `c ⟶ c'` in the Cokleisli category of `U` are
morphisms ` U.obj c ⟶ c'` in `C`. -/
structure Hom (c c' : Cokleisli U) where
  /-- The morphism in C underlying the morphism in the Kleisli category. -/
  of : U.obj c.of ⟶ c'.of

instance [Inhabited C] (U : Comonad C) : Inhabited (Cokleisli U) := ⟨.mk U default⟩

set_option backward.isDefEq.respectTransparency false in
/-- The co-Kleisli category on a comonad `U`. -/
@[simps!]
instance category : Category (Cokleisli U) where
  Hom X Y := Hom X Y
  id X := .mk <| U.ε.app X.of
  comp f g := .mk <| U.δ.app _ ≫ (U : C ⥤ C).map f.of ≫ g.of

variable {T} in
attribute [local ext] Hom in
@[ext]
lemma hom_ext {x y : Cokleisli U} {f g : x ⟶ y} (h : f.of = g.of) : f = g :=
  Hom.ext h

namespace Adjunction

set_option backward.isDefEq.respectTransparency false in
/-- The right adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps]
def toCokleisli : C ⥤ Cokleisli U where
  obj X := .mk U X
  map {X} {_} f := .mk (U.ε.app X ≫ f)

set_option backward.isDefEq.respectTransparency false in
/-- The left adjoint of the adjunction which induces the comonad `(U, ε_ U, δ_ U)`. -/
@[simps]
def fromCokleisli : Cokleisli U ⥤ C where
  obj X := U.obj X.of
  map {X} {_} f := U.δ.app X.of ≫ U.map f.of
  map_id _ := U.right_counit _

set_option backward.isDefEq.respectTransparency false in
/-- The co-Kleisli adjunction which gives rise to the comonad `(U, ε_ U, δ_ U)`. -/
def adj : fromCokleisli U ⊣ toCokleisli U :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y := { toFun f := .mk f, invFun f := f.of }
      homEquiv_naturality_right := fun {X} {Y} {_} f g => by cat_disch }

/-- The composition of the adjunction gives the original functor. -/
def toCokleisliCompFromCokleisliIsoSelf : toCokleisli U ⋙ fromCokleisli U ≅ U :=
  NatIso.ofComponents fun _ => Iso.refl _

end Adjunction

end Cokleisli

end CategoryTheory
#lint
