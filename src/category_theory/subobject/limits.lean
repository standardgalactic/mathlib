/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison
-/
import category_theory.subobject.factor_thru

/-!
# Specific subobjects

We define `equalizer_subobject`, `kernel_subobject` and `image_subobject`, which are the subobjects
represented by the equalizer, kernel and image of (a pair of) morphism(s) and provide conditions
for `P.factors f`, where `P` is one of these special subobjects.

TODO: Add conditions for when `P` is a pullback subobject.
TODO: an iff characterisation of `(image_subobject f).factors h`

-/

universes v u

noncomputable theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u} [category.{v} C] {X Y Z : C}

namespace category_theory

namespace limits

section equalizer
variables (f g : X ⟶ Y) [has_equalizer f g]

/-- The equalizer of morphisms `f g : X ⟶ Y` as a `subobject X`. -/
def equalizer_subobject : subobject X :=
subobject.mk (equalizer.ι f g)

/-- The underlying object of `equalizer_subobject f g` is (up to isomorphism!)
the same as the chosen object `equalizer f g`. -/
def equalizer_subobject_iso : (equalizer_subobject f g : C) ≅ equalizer f g :=
subobject.underlying_iso (equalizer.ι f g)

lemma equalizer_subobject_arrow :
  (equalizer_subobject f g).arrow = (equalizer_subobject_iso f g).hom ≫ equalizer.ι f g :=
(over.w (subobject.representative_iso (mono_over.mk' (equalizer.ι f g))).hom).symm

@[simp] lemma equalizer_subobject_arrow' :
  (equalizer_subobject_iso f g).inv ≫ (equalizer_subobject f g).arrow = equalizer.ι f g :=
over.w (subobject.representative_iso (mono_over.mk' (equalizer.ι f g))).inv

@[reassoc]
lemma equalizer_subobject_arrow_comp :
  (equalizer_subobject f g).arrow ≫ f = (equalizer_subobject f g).arrow ≫ g :=
by simp [equalizer_subobject_arrow, equalizer.condition]

lemma equalizer_subobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = h ≫ g) :
  (equalizer_subobject f g).factors h :=
⟨equalizer.lift h w, by simp⟩

lemma equalizer_subobject_factors_iff {W : C} (h : W ⟶ X) :
  (equalizer_subobject f g).factors h ↔ h ≫ f = h ≫ g :=
⟨λ w, by rw [←subobject.factor_thru_arrow _ _ w, category.assoc,
  equalizer_subobject_arrow_comp, category.assoc],
equalizer_subobject_factors f g h⟩

end equalizer

section kernel
variables [has_zero_morphisms C] (f : X ⟶ Y) [has_kernel f]

/-- The kernel of a morphism `f : X ⟶ Y` as a `subobject X`. -/
def kernel_subobject : subobject X :=
subobject.mk (kernel.ι f)

/-- The underlying object of `kernel_subobject f` is (up to isomorphism!)
the same as the chosen object `kernel f`. -/
def kernel_subobject_iso :
  (kernel_subobject f : C) ≅ kernel f :=
subobject.underlying_iso (kernel.ι f)

lemma kernel_subobject_arrow :
  (kernel_subobject f).arrow = (kernel_subobject_iso f).hom ≫ kernel.ι f :=
(over.w (subobject.representative_iso (mono_over.mk' (kernel.ι f))).hom).symm

@[simp] lemma kernel_subobject_arrow' :
  (kernel_subobject_iso f).inv ≫ (kernel_subobject f).arrow = kernel.ι f :=
over.w (subobject.representative_iso (mono_over.mk' (kernel.ι f))).inv

@[simp, reassoc]
lemma kernel_subobject_arrow_comp :
  (kernel_subobject f).arrow ≫ f = 0 :=
by simp [kernel_subobject_arrow, kernel.condition]

lemma kernel_subobject_factors {W : C} (h : W ⟶ X) (w : h ≫ f = 0) :
  (kernel_subobject f).factors h :=
⟨kernel.lift _ h w, by simp⟩

lemma kernel_subobject_factors_iff {W : C} (h : W ⟶ X) :
  (kernel_subobject f).factors h ↔ h ≫ f = 0 :=
⟨λ w, by rw [←subobject.factor_thru_arrow _ _ w, category.assoc,
  kernel_subobject_arrow_comp, comp_zero],
kernel_subobject_factors f h⟩

lemma le_kernel_subobject (A : subobject X) (h : A.arrow ≫ f = 0) : A ≤ kernel_subobject f :=
subobject.le_mk_of_comm (kernel.lift f A.arrow h) (by simp)

/-- Postcomposing by an monomorphism does not change the kernel subobject. -/
@[simp]
lemma kernel_subobject_comp_mono
  {f : X ⟶ Y} [has_kernel f] {Z : C} (h : Y ⟶ Z) [mono h] :
  kernel_subobject (f ≫ h) = kernel_subobject f :=
le_antisymm
  (le_kernel_subobject _ _ ((cancel_mono h).mp (by simp)))
  (le_kernel_subobject _ _ (by simp))

end kernel

section image
variables (f : X ⟶ Y) [has_image f]

/-- The image of a morphism `f g : X ⟶ Y` as a `subobject Y`. -/
def image_subobject : subobject Y :=
subobject.mk (image.ι f)

/-- The underlying object of `image_subobject f` is (up to isomorphism!)
the same as the chosen object `image f`. -/
def image_subobject_iso :
  (image_subobject f : C) ≅ image f :=
subobject.underlying_iso (image.ι f)

lemma image_subobject_arrow :
  (image_subobject f).arrow = (image_subobject_iso f).hom ≫ image.ι f :=
(over.w (subobject.representative_iso (mono_over.mk' (image.ι f))).hom).symm

@[simp] lemma image_subobject_arrow' :
  (image_subobject_iso f).inv ≫ (image_subobject f).arrow = image.ι f :=
over.w (subobject.representative_iso (mono_over.mk' (image.ι f))).inv

/-- A factorisation of `f : X ⟶ Y` through `image_subobject f`. -/
def factor_thru_image_subobject : X ⟶ image_subobject f :=
factor_thru_image f ≫ (image_subobject_iso f).inv

lemma image_subobject_arrow_comp :
  factor_thru_image_subobject f ≫ (image_subobject f).arrow = f :=
by simp [factor_thru_image_subobject, image_subobject_arrow]

lemma image_subobject_factors_comp_self {W : C} (k : W ⟶ X)  :
  (image_subobject f).factors (k ≫ f) :=
⟨k ≫ factor_thru_image f, by simp⟩

/-- Precomposing by an isomorphism does not change the image subobject. -/
lemma image_subobject_iso_comp [has_equalizers C]
  {f : X ⟶ Y} [has_image f] {X' : C} (h : X' ⟶ X) [is_iso h] :
  image_subobject (h ≫ f) = image_subobject f :=
le_antisymm
  (subobject.mk_le_mk_of_comm (image.pre_comp h f) (by simp))
  (subobject.mk_le_mk_of_comm (inv (image.pre_comp h f)) (by simp))

lemma image_subobject_le {A B : C} {X : subobject B} (f : A ⟶ B) [has_image f]
  (h : A ⟶ X) (w : h ≫ X.arrow = f) :
  image_subobject f ≤ X :=
subobject.le_of_comm
  ((image_subobject_iso f).hom ≫ image.lift { I := (X : C), e := h, m := X.arrow, })
  (by simp [←image_subobject_arrow f])

lemma image_subobject_le_mk {A B : C} {X : C} (g : X ⟶ B) [mono g] (f : A ⟶ B) [has_image f]
  (h : A ⟶ X) (w : h ≫ g = f) :
  image_subobject f ≤ subobject.mk g :=
image_subobject_le f (h ≫ (subobject.underlying_iso g).inv) (by simp [w])

/-- Given a commutative square between morphisms `f` and `g`,
we have a morphism in the category from `image_subobject f` to `image_subobject g`. -/
def image_subobject_map {W X Y Z : C} {f : W ⟶ X} [has_image f] {g : Y ⟶ Z} [has_image g]
  (sq : arrow.mk f ⟶ arrow.mk g) [has_image_map sq] :
  (image_subobject f : C) ⟶ (image_subobject g : C) :=
(image_subobject_iso f).hom ≫ image.map sq ≫ (image_subobject_iso g).inv

@[simp, reassoc]
lemma image_subobject_map_arrow {W X Y Z : C} {f : W ⟶ X} [has_image f] {g : Y ⟶ Z} [has_image g]
  (sq : arrow.mk f ⟶ arrow.mk g) [has_image_map sq] :
  image_subobject_map sq ≫ (image_subobject g).arrow = (image_subobject f).arrow ≫ sq.right :=
begin
  simp only [image_subobject_map, category.assoc, image_subobject_arrow'],
  erw [image.map_ι, ←category.assoc, ←image_subobject_arrow],
end

end image

end limits

end category_theory
