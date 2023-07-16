/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.category.Group.basic
import category_theory.single_obj
import category_theory.limits.functor_category
import category_theory.limits.preserves.basic
import category_theory.adjunction.limits
import category_theory.monoidal.functor_category
import category_theory.monoidal.transport
import category_theory.monoidal.rigid.of_equivalence
import category_theory.monoidal.rigid.functor_category
import category_theory.monoidal.linear
import category_theory.monoidal.braided
import category_theory.monoidal.types
import category_theory.abelian.functor_category
import category_theory.abelian.transfer
import category_theory.conj
import category_theory.linear.functor_category

/-!
# `Action V G`, the category of actions of a monoid `G` inside some category `V`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The prototypical example is `V = Module R`,
where `Action (Module R) G` is the category of `R`-linear representations of `G`.

We check `Action V G ≌ (single_obj G ⥤ V)`,
and construct the restriction functors `res {G H : Mon} (f : G ⟶ H) : Action V H ⥤ Action V G`.

* When `V` has (co)limits so does `Action V G`.
* When `V` is monoidal, braided, or symmetric, so is `Action V G`.
* When `V` is preadditive, linear, or abelian so is `Action V G`.
-/

universes u v

open category_theory
open category_theory.limits

variables (V : Type (u+1)) [large_category V]

/--
An `Action V G` represents a bundled action of
the monoid `G` on an object of some category `V`.

As an example, when `V = Module R`, this is an `R`-linear representation of `G`,
while when `V = Type` this is a `G`-action.
-/
-- Note: this is _not_ a categorical action of `G` on `V`.
structure Action (G : Mon.{u}) :=
(V : V)
(ρ : G ⟶ Mon.of (End V))

namespace Action
variable {V}

@[simp]
lemma ρ_one {G : Mon.{u}} (A : Action V G) : A.ρ 1 = 𝟙 A.V :=
by { rw [monoid_hom.map_one], refl, }

/-- When a group acts, we can lift the action to the group of automorphisms. -/
@[simps]
def ρ_Aut {G : Group.{u}} (A : Action V (Mon.of G)) : G ⟶ Group.of (Aut A.V) :=
{ to_fun := λ g,
  { hom := A.ρ g,
    inv := A.ρ (g⁻¹ : G),
    hom_inv_id' := ((A.ρ).map_mul (g⁻¹ : G) g).symm.trans (by rw [inv_mul_self, ρ_one]),
    inv_hom_id' := ((A.ρ).map_mul g (g⁻¹ : G)).symm.trans (by rw [mul_inv_self, ρ_one]), },
  map_one' := by { ext, exact A.ρ.map_one },
  map_mul' := λ x y, by { ext, exact A.ρ.map_mul x y }, }

variable (G : Mon.{u})

section

instance inhabited' : inhabited (Action (Type u) G) := ⟨⟨punit, 1⟩⟩

/-- The trivial representation of a group. -/
def trivial : Action AddCommGroup G :=
{ V := AddCommGroup.of punit,
  ρ := 1, }

instance : inhabited (Action AddCommGroup G) := ⟨trivial G⟩
end

variables {G V}

/--
A homomorphism of `Action V G`s is a morphism between the underlying objects,
commuting with the action of `G`.
-/
@[ext]
structure hom (M N : Action V G) :=
(hom : M.V ⟶ N.V)
(comm' : ∀ g : G, M.ρ g ≫ hom = hom ≫ N.ρ g . obviously)

restate_axiom hom.comm'

namespace hom

/-- The identity morphism on a `Action V G`. -/
@[simps]
def id (M : Action V G) : Action.hom M M :=
{ hom := 𝟙 M.V }

instance (M : Action V G) : inhabited (Action.hom M M) := ⟨id M⟩

/--
The composition of two `Action V G` homomorphisms is the composition of the underlying maps.
-/
@[simps]
def comp {M N K : Action V G} (p : Action.hom M N) (q : Action.hom N K) :
  Action.hom M K :=
{ hom := p.hom ≫ q.hom,
  comm' := λ g, by rw [←category.assoc, p.comm, category.assoc, q.comm, ←category.assoc] }

end hom

instance : category (Action V G) :=
{ hom := λ M N, hom M N,
  id := λ M, hom.id M,
  comp := λ M N K f g, hom.comp f g, }

@[simp]
lemma id_hom (M : Action V G) : (𝟙 M : hom M M).hom = 𝟙 M.V := rfl
@[simp]
lemma comp_hom {M N K : Action V G} (f : M ⟶ N) (g : N ⟶ K) :
  (f ≫ g : hom M K).hom = f.hom ≫ g.hom :=
rfl

/-- Construct an isomorphism of `G` actions/representations
from an isomorphism of the the underlying objects,
where the forward direction commutes with the group action. -/
@[simps]
def mk_iso {M N : Action V G} (f : M.V ≅ N.V) (comm : ∀ g : G, M.ρ g ≫ f.hom = f.hom ≫ N.ρ g) :
  M ≅ N :=
{ hom :=
  { hom := f.hom,
    comm' := comm, },
  inv :=
  { hom := f.inv,
    comm' := λ g, by { have w := comm g =≫ f.inv, simp at w, simp [w], }, }}

@[priority 100]
instance is_iso_of_hom_is_iso {M N : Action V G} (f : M ⟶ N) [is_iso f.hom] : is_iso f :=
by { convert is_iso.of_iso (mk_iso (as_iso f.hom) f.comm), ext, refl, }

instance is_iso_hom_mk {M N : Action V G} (f : M.V ⟶ N.V) [is_iso f] (w) :
  @is_iso _ _ M N ⟨f, w⟩ :=
is_iso.of_iso (mk_iso (as_iso f) w)

namespace functor_category_equivalence

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def functor : Action V G ⥤ (single_obj G ⥤ V) :=
{ obj := λ M,
  { obj := λ _, M.V,
    map := λ _ _ g, M.ρ g,
    map_id' := λ _, M.ρ.map_one,
    map_comp' := λ _ _ _ g h, M.ρ.map_mul h g, },
  map := λ M N f,
  { app := λ _, f.hom,
    naturality' := λ _ _ g, f.comm g, } }

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def inverse : (single_obj G ⥤ V) ⥤ Action V G :=
{ obj := λ F,
  { V := F.obj punit.star,
    ρ :=
    { to_fun := λ g, F.map g,
      map_one' := F.map_id punit.star,
      map_mul' := λ g h, F.map_comp h g, } },
  map := λ M N f,
  { hom := f.app punit.star,
    comm' := λ g, f.naturality g, } }.

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def unit_iso : 𝟭 (Action V G) ≅ functor ⋙ inverse :=
nat_iso.of_components (λ M, mk_iso ((iso.refl _)) (by tidy)) (by tidy).

/-- Auxilliary definition for `functor_category_equivalence`. -/
@[simps]
def counit_iso : inverse ⋙ functor ≅ 𝟭 (single_obj G ⥤ V) :=
nat_iso.of_components (λ M, nat_iso.of_components (by tidy) (by tidy)) (by tidy).

end functor_category_equivalence

section
open functor_category_equivalence

variables (V G)

/--
The category of actions of `G` in the category `V`
is equivalent to the functor category `single_obj G ⥤ V`.
-/
def functor_category_equivalence : Action V G ≌ (single_obj G ⥤ V) :=
{ functor := functor,
  inverse := inverse,
  unit_iso := unit_iso,
  counit_iso := counit_iso, }

attribute [simps] functor_category_equivalence

lemma functor_category_equivalence.functor_def :
  (functor_category_equivalence V G).functor = functor_category_equivalence.functor := rfl

lemma functor_category_equivalence.inverse_def :
  (functor_category_equivalence V G).inverse = functor_category_equivalence.inverse := rfl

instance [has_finite_products V] : has_finite_products (Action V G) :=
{ out := λ n, adjunction.has_limits_of_shape_of_equivalence
    (Action.functor_category_equivalence _ _).functor }

instance [has_finite_limits V] : has_finite_limits (Action V G) :=
{ out := λ J _ _, by exactI adjunction.has_limits_of_shape_of_equivalence
    (Action.functor_category_equivalence _ _).functor }

instance [has_limits V] : has_limits (Action V G) :=
adjunction.has_limits_of_equivalence (Action.functor_category_equivalence _ _).functor

instance [has_colimits V] : has_colimits (Action V G) :=
adjunction.has_colimits_of_equivalence (Action.functor_category_equivalence _ _).functor

end

section forget

variables (V G)

/-- (implementation) The forgetful functor from bundled actions to the underlying objects.

Use the `category_theory.forget` API provided by the `concrete_category` instance below,
rather than using this directly.
-/
@[simps]
def forget : Action V G ⥤ V :=
{ obj := λ M, M.V,
  map := λ M N f, f.hom, }

instance : faithful (forget V G) :=
{ map_injective' := λ X Y f g w, hom.ext _ _ w, }

instance [concrete_category V] : concrete_category (Action V G) :=
{ forget := forget V G ⋙ (concrete_category.forget V), }

instance has_forget_to_V [concrete_category V] : has_forget₂ (Action V G) V :=
{ forget₂ := forget V G }

/-- The forgetful functor is intertwined by `functor_category_equivalence` with
evaluation at `punit.star`. -/
def functor_category_equivalence_comp_evaluation :
  (functor_category_equivalence V G).functor ⋙ (evaluation _ _).obj punit.star ≅ forget V G :=
iso.refl _

noncomputable instance [has_limits V] : limits.preserves_limits (forget V G) :=
limits.preserves_limits_of_nat_iso
  (Action.functor_category_equivalence_comp_evaluation V G)

noncomputable instance [has_colimits V] : preserves_colimits (forget V G) :=
preserves_colimits_of_nat_iso
  (Action.functor_category_equivalence_comp_evaluation V G)

-- TODO construct categorical images?

end forget

lemma iso.conj_ρ {M N : Action V G} (f : M ≅ N) (g : G) :
   N.ρ g = (((forget V G).map_iso f).conj (M.ρ g)) :=
by { rw [iso.conj_apply, iso.eq_inv_comp], simp [f.hom.comm'] }

section has_zero_morphisms
variables [has_zero_morphisms V]

instance : has_zero_morphisms (Action V G) :=
{ has_zero := λ X Y, ⟨⟨0, by { intro g, simp }⟩⟩,
  comp_zero' := λ P Q f R, by { ext1, simp },
  zero_comp' := λ P Q R f, by { ext1, simp }, }

instance forget_preserves_zero_morphisms : functor.preserves_zero_morphisms (forget V G) := {}
instance forget₂_preserves_zero_morphisms [concrete_category V] :
  functor.preserves_zero_morphisms (forget₂ (Action V G) V) := {}
instance functor_category_equivalence_preserves_zero_morphisms :
  functor.preserves_zero_morphisms (functor_category_equivalence V G).functor := {}

end has_zero_morphisms

section preadditive
variables [preadditive V]

instance : preadditive (Action V G) :=
{ hom_group := λ X Y,
  { zero := ⟨0, by simp⟩,
    add := λ f g, ⟨f.hom + g.hom, by simp [f.comm, g.comm]⟩,
    neg := λ f, ⟨-f.hom, by simp [f.comm]⟩,
    zero_add := by { intros, ext, exact zero_add _, },
    add_zero := by { intros, ext, exact add_zero _, },
    add_assoc := by { intros, ext, exact add_assoc _ _ _, },
    add_left_neg := by { intros, ext, exact add_left_neg _, },
    add_comm := by { intros, ext, exact add_comm _ _, }, },
  add_comp' := by { intros, ext, exact preadditive.add_comp _ _ _ _ _ _, },
  comp_add' := by { intros, ext, exact preadditive.comp_add _ _ _ _ _ _, }, }

instance forget_additive :
  functor.additive (forget V G) := {}
instance forget₂_additive [concrete_category V] :
  functor.additive (forget₂ (Action V G) V) := {}
instance functor_category_equivalence_additive :
  functor.additive (functor_category_equivalence V G).functor := {}

@[simp] lemma zero_hom {X Y : Action V G} : (0 : X ⟶ Y).hom = 0 := rfl
@[simp] lemma neg_hom {X Y : Action V G} (f : X ⟶ Y) : (-f).hom = -f.hom := rfl
@[simp] lemma add_hom {X Y : Action V G} (f g : X ⟶ Y) : (f + g).hom = f.hom + g.hom := rfl
@[simp] lemma sum_hom {X Y : Action V G} {ι : Type*} (f : ι → (X ⟶ Y)) (s : finset ι) :
  (s.sum f).hom = s.sum (λ i, (f i).hom) := (forget V G).map_sum f s

end preadditive

section linear
variables [preadditive V] {R : Type*} [semiring R] [linear R V]

instance : linear R (Action V G) :=
{ hom_module := λ X Y,
  { smul := λ r f, ⟨r • f.hom, by simp [f.comm]⟩,
    one_smul := by { intros, ext, exact one_smul _ _, },
    smul_zero := by { intros, ext, exact smul_zero _, },
    zero_smul := by { intros, ext, exact zero_smul _ _, },
    add_smul := by { intros, ext, exact add_smul _ _ _, },
    smul_add := by { intros, ext, exact smul_add _ _ _, },
    mul_smul := by { intros, ext, exact mul_smul _ _ _, }, },
  smul_comp' := by { intros, ext, exact linear.smul_comp _ _ _ _ _ _, },
  comp_smul' := by { intros, ext, exact linear.comp_smul _ _ _ _ _ _, }, }

instance forget_linear :
  functor.linear R (forget V G) := {}
instance forget₂_linear [concrete_category V] :
  functor.linear R (forget₂ (Action V G) V) := {}
instance functor_category_equivalence_linear :
  functor.linear R (functor_category_equivalence V G).functor := {}

@[simp] lemma smul_hom {X Y : Action V G} (r : R) (f : X ⟶ Y) : (r • f).hom = r • f.hom := rfl

end linear

section abelian
/-- Auxilliary construction for the `abelian (Action V G)` instance. -/
def abelian_aux : Action V G ≌ (ulift.{u} (single_obj G) ⥤ V) :=
(functor_category_equivalence V G).trans (equivalence.congr_left ulift.equivalence)

noncomputable instance [abelian V] : abelian (Action V G) :=
abelian_of_equivalence abelian_aux.functor

end abelian

section monoidal
variables [monoidal_category V]

instance : monoidal_category (Action V G) :=
monoidal.transport (Action.functor_category_equivalence _ _).symm

@[simp] lemma tensor_unit_V : (𝟙_ (Action V G)).V = 𝟙_ V := rfl
@[simp] lemma tensor_unit_rho {g : G} : (𝟙_ (Action V G)).ρ g = 𝟙 (𝟙_ V) := rfl
@[simp] lemma tensor_V {X Y : Action V G} : (X ⊗ Y).V = X.V ⊗ Y.V := rfl
@[simp] lemma tensor_rho {X Y : Action V G} {g : G} : (X ⊗ Y).ρ g = X.ρ g ⊗ Y.ρ g := rfl
@[simp] lemma tensor_hom {W X Y Z : Action V G} (f : W ⟶ X) (g : Y ⟶ Z) :
  (f ⊗ g).hom = f.hom ⊗ g.hom := rfl
@[simp] lemma associator_hom_hom {X Y Z : Action V G} :
  hom.hom (α_ X Y Z).hom = (α_ X.V Y.V Z.V).hom :=
begin
  dsimp [monoidal.transport_associator],
  simp,
end
@[simp] lemma associator_inv_hom {X Y Z : Action V G} :
  hom.hom (α_ X Y Z).inv = (α_ X.V Y.V Z.V).inv :=
begin
  dsimp [monoidal.transport_associator],
  simp,
end
@[simp] lemma left_unitor_hom_hom {X : Action V G} :
  hom.hom (λ_ X).hom = (λ_ X.V).hom :=
begin
  dsimp [monoidal.transport_left_unitor],
  simp,
end
@[simp] lemma left_unitor_inv_hom {X : Action V G} :
  hom.hom (λ_ X).inv = (λ_ X.V).inv :=
begin
  dsimp [monoidal.transport_left_unitor],
  simp,
end
@[simp] lemma right_unitor_hom_hom {X : Action V G} :
  hom.hom (ρ_ X).hom = (ρ_ X.V).hom :=
begin
  dsimp [monoidal.transport_right_unitor],
  simp,
end
@[simp] lemma right_unitor_inv_hom {X : Action V G} :
  hom.hom (ρ_ X).inv = (ρ_ X.V).inv :=
begin
  dsimp [monoidal.transport_right_unitor],
  simp,
end

/-- Given an object `X` isomorphic to the tensor unit of `V`, `X` equipped with the trivial action
is isomorphic to the tensor unit of `Action V G`. -/
def tensor_unit_iso {X : V} (f : 𝟙_ V ≅ X) :
  𝟙_ (Action V G) ≅ Action.mk X 1 :=
Action.mk_iso f (λ g, by simp only [monoid_hom.one_apply, End.one_def, category.id_comp f.hom,
  tensor_unit_rho, category.comp_id])

variables (V G)

/-- When `V` is monoidal the forgetful functor `Action V G` to `V` is monoidal. -/
@[simps]
def forget_monoidal : monoidal_functor (Action V G) V :=
{ ε := 𝟙 _,
  μ := λ X Y, 𝟙 _,
  ..Action.forget _ _, }

instance forget_monoidal_faithful : faithful (forget_monoidal V G).to_functor :=
by { change faithful (forget V G), apply_instance, }

section
variables [braided_category V]

instance : braided_category (Action V G) :=
braided_category_of_faithful (forget_monoidal V G) (λ X Y, mk_iso (β_ _ _) (by tidy)) (by tidy)

/-- When `V` is braided the forgetful functor `Action V G` to `V` is braided. -/
@[simps]
def forget_braided : braided_functor (Action V G) V :=
{ ..forget_monoidal _ _, }

instance forget_braided_faithful : faithful (forget_braided V G).to_functor :=
by { change faithful (forget V G), apply_instance, }

end

instance [symmetric_category V] : symmetric_category (Action V G) :=
symmetric_category_of_faithful (forget_braided V G)

section
variables [preadditive V] [monoidal_preadditive V]

local attribute [simp] monoidal_preadditive.tensor_add monoidal_preadditive.add_tensor

instance : monoidal_preadditive (Action V G) := {}

variables {R : Type*} [semiring R] [linear R V] [monoidal_linear R V]

instance : monoidal_linear R (Action V G) := {}

end

variables (V G)
noncomputable theory

/-- Upgrading the functor `Action V G ⥤ (single_obj G ⥤ V)` to a monoidal functor. -/
def functor_category_monoidal_equivalence : monoidal_functor (Action V G) (single_obj G ⥤ V) :=
monoidal.from_transported (Action.functor_category_equivalence _ _).symm

instance : is_equivalence ((functor_category_monoidal_equivalence V G).to_functor) :=
by { change is_equivalence (Action.functor_category_equivalence _ _).functor, apply_instance, }

@[simp] lemma functor_category_monoidal_equivalence.μ_app (A B : Action V G) :
  ((functor_category_monoidal_equivalence V G).μ A B).app punit.star = 𝟙 _ :=
begin
  dunfold functor_category_monoidal_equivalence,
  simp only [monoidal.from_transported_to_lax_monoidal_functor_μ],
  show (𝟙 A.V ⊗ 𝟙 B.V) ≫ 𝟙 (A.V ⊗ B.V) ≫ (𝟙 A.V ⊗ 𝟙 B.V) = 𝟙 (A.V ⊗ B.V),
  simp only [monoidal_category.tensor_id, category.comp_id],
end

@[simp] lemma functor_category_monoidal_equivalence.μ_iso_inv_app (A B : Action V G) :
  ((functor_category_monoidal_equivalence V G).μ_iso A B).inv.app punit.star = 𝟙 _ :=
begin
  rw [←nat_iso.app_inv, ←is_iso.iso.inv_hom],
  refine is_iso.inv_eq_of_hom_inv_id _,
  rw [category.comp_id, nat_iso.app_hom, monoidal_functor.μ_iso_hom,
    functor_category_monoidal_equivalence.μ_app],
end

@[simp] lemma functor_category_monoidal_equivalence.ε_app :
  (functor_category_monoidal_equivalence V G).ε.app punit.star = 𝟙 _ :=
begin
  dunfold functor_category_monoidal_equivalence,
  simp only [monoidal.from_transported_to_lax_monoidal_functor_ε],
  show 𝟙 (monoidal_category.tensor_unit V) ≫ _ = 𝟙 (monoidal_category.tensor_unit V),
  rw [nat_iso.is_iso_inv_app, category.id_comp],
  exact is_iso.inv_id,
end

@[simp] lemma functor_category_monoidal_equivalence.inv_counit_app_hom (A : Action V G) :
  ((functor_category_monoidal_equivalence _ _).inv.adjunction.counit.app A).hom = 𝟙 _ :=
rfl

@[simp] lemma functor_category_monoidal_equivalence.counit_app (A : single_obj G ⥤ V) :
  ((functor_category_monoidal_equivalence _ _).adjunction.counit.app A).app punit.star = 𝟙 _ := rfl

@[simp] lemma functor_category_monoidal_equivalence.inv_unit_app_app
  (A : single_obj G ⥤ V) :
  ((functor_category_monoidal_equivalence _ _).inv.adjunction.unit.app A).app
  punit.star = 𝟙 _ := rfl

@[simp] lemma functor_category_monoidal_equivalence.unit_app_hom (A : Action V G) :
  ((functor_category_monoidal_equivalence _ _).adjunction.unit.app A).hom = 𝟙 _ :=
rfl

@[simp] lemma functor_category_monoidal_equivalence.functor_map {A B : Action V G} (f : A ⟶ B) :
  (functor_category_monoidal_equivalence _ _).map f
    = functor_category_equivalence.functor.map f := rfl

@[simp] lemma functor_category_monoidal_equivalence.inverse_map
  {A B : single_obj G ⥤ V} (f : A ⟶ B) :
  (functor_category_monoidal_equivalence _ _).inv.map f
    = functor_category_equivalence.inverse.map f := rfl

variables (H : Group.{u})

instance [right_rigid_category V] : right_rigid_category (single_obj (H : Mon.{u}) ⥤ V) :=
by { change right_rigid_category (single_obj H ⥤ V), apply_instance }

/-- If `V` is right rigid, so is `Action V G`. -/
instance [right_rigid_category V] : right_rigid_category (Action V H) :=
right_rigid_category_of_equivalence (functor_category_monoidal_equivalence V _)

instance [left_rigid_category V] : left_rigid_category (single_obj (H : Mon.{u}) ⥤ V) :=
by { change left_rigid_category (single_obj H ⥤ V), apply_instance }

/-- If `V` is left rigid, so is `Action V G`. -/
instance [left_rigid_category V] : left_rigid_category (Action V H) :=
left_rigid_category_of_equivalence (functor_category_monoidal_equivalence V _)

instance [rigid_category V] : rigid_category (single_obj (H : Mon.{u}) ⥤ V) :=
by { change rigid_category (single_obj H ⥤ V), apply_instance }

/-- If `V` is rigid, so is `Action V G`. -/
instance [rigid_category V] : rigid_category (Action V H) :=
rigid_category_of_equivalence (functor_category_monoidal_equivalence V _)

variables {V H} (X : Action V H)

@[simp] lemma right_dual_V [right_rigid_category V] : (Xᘁ).V = (X.V)ᘁ := rfl

@[simp] lemma left_dual_V [left_rigid_category V] : (ᘁX).V = ᘁ(X.V) := rfl

@[simp] lemma right_dual_ρ [right_rigid_category V] (h : H) : (Xᘁ).ρ h = (X.ρ (h⁻¹ : H))ᘁ :=
by { rw ←single_obj.inv_as_inv, refl }

@[simp] lemma left_dual_ρ [left_rigid_category V] (h : H) : (ᘁX).ρ h = ᘁ(X.ρ (h⁻¹ : H)) :=
by { rw ←single_obj.inv_as_inv, refl }

end monoidal

/-- Actions/representations of the trivial group are just objects in the ambient category. -/
def Action_punit_equivalence : Action V (Mon.of punit) ≌ V :=
{ functor := forget V _,
  inverse :=
  { obj := λ X, ⟨X, 1⟩,
    map := λ X Y f, ⟨f, λ ⟨⟩, by simp⟩, },
  unit_iso := nat_iso.of_components (λ X, mk_iso (iso.refl _) (λ ⟨⟩, by simpa using ρ_one X))
    (by tidy),
  counit_iso := nat_iso.of_components (λ X, iso.refl _) (by tidy), }

variables (V)
/--
The "restriction" functor along a monoid homomorphism `f : G ⟶ H`,
taking actions of `H` to actions of `G`.

(This makes sense for any homomorphism, but the name is natural when `f` is a monomorphism.)
-/
@[simps]
def res {G H : Mon} (f : G ⟶ H) : Action V H ⥤ Action V G :=
{ obj := λ M,
  { V := M.V,
    ρ := f ≫ M.ρ },
  map := λ M N p,
  { hom := p.hom,
    comm' := λ g, p.comm (f g) } }

/--
The natural isomorphism from restriction along the identity homomorphism to
the identity functor on `Action V G`.
-/
def res_id {G : Mon} : res V (𝟙 G) ≅ 𝟭 (Action V G) :=
nat_iso.of_components (λ M, mk_iso (iso.refl _) (by tidy)) (by tidy)

attribute [simps] res_id

/--
The natural isomorphism from the composition of restrictions along homomorphisms
to the restriction along the composition of homomorphism.
-/
def res_comp {G H K : Mon} (f : G ⟶ H) (g : H ⟶ K) : res V g ⋙ res V f ≅ res V (f ≫ g) :=
nat_iso.of_components (λ M, mk_iso (iso.refl _) (by tidy)) (by tidy)

attribute [simps] res_comp

-- TODO promote `res` to a pseudofunctor from
-- the locally discrete bicategory constructed from `Monᵒᵖ` to `Cat`, sending `G` to `Action V G`.

variables {G} {H : Mon.{u}} (f : G ⟶ H)

instance res_additive [preadditive V] : (res V f).additive := {}

variables {R : Type*} [semiring R]

instance res_linear [preadditive V] [linear R V] : (res V f).linear R := {}

/-- Bundles a type `H` with a multiplicative action of `G` as an `Action`. -/
def of_mul_action (G H : Type u) [monoid G] [mul_action G H] : Action (Type u) (Mon.of G) :=
{ V := H,
  ρ := @mul_action.to_End_hom _ _ _ (by assumption) }

@[simp] lemma of_mul_action_apply {G H : Type u} [monoid G] [mul_action G H] (g : G) (x : H) :
  (of_mul_action G H).ρ g x = (g • x : H) :=
rfl

/-- Given a family `F` of types with `G`-actions, this is the limit cone demonstrating that the
product of `F` as types is a product in the category of `G`-sets. -/
def of_mul_action_limit_cone {ι : Type v} (G : Type (max v u)) [monoid G]
  (F : ι → Type (max v u)) [Π i : ι, mul_action G (F i)] :
  limit_cone (discrete.functor (λ i : ι, Action.of_mul_action G (F i))) :=
{ cone :=
  { X := Action.of_mul_action G (Π i : ι, F i),
    π :=
    { app := λ i, ⟨λ x, x i.as, λ g, by ext; refl⟩,
      naturality' := λ i j x,
      begin
        ext,
        discrete_cases,
        cases x,
        congr
      end } },
  is_limit :=
  { lift := λ s,
    { hom := λ x i, (s.π.app ⟨i⟩).hom x,
      comm' := λ g,
      begin
        ext x j,
        dsimp,
        exact congr_fun ((s.π.app ⟨j⟩).comm g) x,
      end },
    fac' := λ s j,
    begin
      ext,
      dsimp,
      congr,
      rw discrete.mk_as,
    end,
    uniq' := λ s f h,
    begin
      ext x j,
      dsimp at *,
      rw ←h ⟨j⟩,
      congr,
    end } }

/-- The `G`-set `G`, acting on itself by left multiplication. -/
@[simps] def left_regular (G : Type u) [monoid G] : Action (Type u) (Mon.of G) :=
Action.of_mul_action G G

/-- The `G`-set `Gⁿ`, acting on itself by left multiplication. -/
@[simps] def diagonal (G : Type u) [monoid G] (n : ℕ) : Action (Type u) (Mon.of G) :=
Action.of_mul_action G (fin n → G)

/-- We have `fin 1 → G ≅ G` as `G`-sets, with `G` acting by left multiplication. -/
def diagonal_one_iso_left_regular (G : Type u) [monoid G] :
  diagonal G 1 ≅ left_regular G := Action.mk_iso (equiv.fun_unique _ _).to_iso (λ g, rfl)

/-- Given `X : Action (Type u) (Mon.of G)` for `G` a group, then `G × X` (with `G` acting as left
multiplication on the first factor and by `X.ρ` on the second) is isomorphic as a `G`-set to
`G × X` (with `G` acting as left multiplication on the first factor and trivially on the second).
The isomorphism is given by `(g, x) ↦ (g, g⁻¹ • x)`. -/
@[simps] def left_regular_tensor_iso (G : Type u) [group G]
  (X : Action (Type u) (Mon.of G)) :
  left_regular G ⊗ X ≅ left_regular G ⊗ Action.mk X.V 1 :=
{ hom :=
  { hom := λ g, ⟨g.1, (X.ρ (g.1⁻¹ : G) g.2 : X.V)⟩,
    comm' := λ g, funext $ λ x, prod.ext rfl $
      show (X.ρ ((g * x.1)⁻¹ : G) * X.ρ g) x.2 = _,
      by simpa only [mul_inv_rev, ←X.ρ.map_mul, inv_mul_cancel_right] },
  inv :=
  { hom := λ g, ⟨g.1, X.ρ g.1 g.2⟩,
    comm' := λ g, funext $ λ x, prod.ext rfl $
      by simpa only [tensor_rho, types_comp_apply, tensor_apply, left_regular_ρ_apply, map_mul] },
  hom_inv_id' := hom.ext _ _ (funext $ λ x, prod.ext rfl $
    show (X.ρ x.1 * X.ρ (x.1⁻¹ : G)) x.2 = _,
      by simpa only [←X.ρ.map_mul, mul_inv_self, X.ρ.map_one]),
  inv_hom_id' := hom.ext _ _ (funext $ λ x, prod.ext rfl $
    show (X.ρ (x.1⁻¹ : G) * X.ρ x.1) _ = _,
      by simpa only [←X.ρ.map_mul, inv_mul_self, X.ρ.map_one]) }

/-- The natural isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left multiplication on
each factor. -/
@[simps] def diagonal_succ (G : Type u) [monoid G] (n : ℕ) :
  diagonal G (n + 1) ≅ left_regular G ⊗ diagonal G n :=
mk_iso (equiv.pi_fin_succ_above_equiv _ 0).to_iso (λ g, rfl)

end Action

namespace category_theory.functor

variables {V} {W : Type (u+1)} [large_category W]

/-- A functor between categories induces a functor between
the categories of `G`-actions within those categories. -/
@[simps]
def map_Action (F : V ⥤ W) (G : Mon.{u}) : Action V G ⥤ Action W G :=
{ obj := λ M,
  { V := F.obj M.V,
    ρ :=
    { to_fun := λ g, F.map (M.ρ g),
      map_one' := by simp only [End.one_def, Action.ρ_one, F.map_id],
      map_mul' := λ g h, by simp only [End.mul_def, F.map_comp, map_mul], }, },
  map := λ M N f,
  { hom := F.map f.hom,
    comm' := λ g, by { dsimp, rw [←F.map_comp, f.comm, F.map_comp], }, },
  map_id' := λ M, by { ext, simp only [Action.id_hom, F.map_id], },
  map_comp' := λ M N P f g, by { ext, simp only [Action.comp_hom, F.map_comp], }, }

variables (F : V ⥤ W) (G : Mon.{u}) [preadditive V] [preadditive W]

instance map_Action_preadditive [F.additive] : (F.map_Action G).additive := {}

variables {R : Type*} [semiring R] [category_theory.linear R V] [category_theory.linear R W]

instance map_Action_linear [F.additive] [F.linear R] : (F.map_Action G).linear R := {}

end category_theory.functor

namespace category_theory.monoidal_functor

open Action
variables {V} {W : Type (u+1)} [large_category W] [monoidal_category V] [monoidal_category W]
  (F : monoidal_functor V W) (G : Mon.{u})

/-- A monoidal functor induces a monoidal functor between
the categories of `G`-actions within those categories. -/
@[simps] def map_Action :
  monoidal_functor (Action V G) (Action W G) :=
{ ε :=
  { hom := F.ε,
    comm' := λ g,
    by { dsimp, erw [category.id_comp, category_theory.functor.map_id, category.comp_id], }, },
  μ := λ X Y,
  { hom := F.μ X.V Y.V,
    comm' := λ g, F.to_lax_monoidal_functor.μ_natural (X.ρ g) (Y.ρ g), },
  ε_is_iso := by apply_instance,
  μ_is_iso := by apply_instance,
  μ_natural' := by { intros, ext, dsimp, simp, },
  associativity' := by { intros, ext, dsimp, simp, dsimp, simp, }, -- See note [dsimp, simp].
  left_unitality' := by { intros, ext, dsimp, simp, dsimp, simp, },
  right_unitality' := by { intros, ext, dsimp, simp, dsimp, simp, },
  ..F.to_functor.map_Action G, }

@[simp] lemma map_Action_ε_inv_hom :
  (inv (F.map_Action G).ε).hom = inv F.ε :=
begin
  ext,
  simp only [←F.map_Action_to_lax_monoidal_functor_ε_hom G, ←Action.comp_hom,
    is_iso.hom_inv_id, id_hom],
end

@[simp] lemma map_Action_μ_inv_hom (X Y : Action V G) :
  (inv ((F.map_Action G).μ X Y)).hom = inv (F.μ X.V Y.V) :=
begin
  ext,
  simpa only [←F.map_Action_to_lax_monoidal_functor_μ_hom G, ←Action.comp_hom,
    is_iso.hom_inv_id, id_hom],
end

end category_theory.monoidal_functor
