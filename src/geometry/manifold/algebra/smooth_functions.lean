/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import geometry.manifold.algebra.structures
import geometry.manifold.times_cont_mdiff_map

/-!
# Algebraic structures over smooth functions

In this file, we define instances of algebraic structures over smooth functions.
-/

noncomputable theory

open_locale manifold

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{N : Type*} [topological_space N] [charted_space H N]

namespace smooth_map

@[to_additive]
instance has_mul {G : Type*} [has_mul G] [topological_space G] [charted_space H' G]
  [has_smooth_mul I' G] :
  has_mul C^∞⟮I, N; I', G⟯ :=
⟨λ f g, ⟨f * g, f.smooth.mul g.smooth⟩⟩

@[simp, to_additive]
lemma coe_mul {G : Type*} [has_mul G] [topological_space G] [charted_space H' G]
  [has_smooth_mul I' G] (f g : C^∞⟮I, N; I', G⟯) :
  ⇑(f * g) = f * g := rfl

@[to_additive]
instance has_one {G : Type*} [monoid G] [topological_space G] [charted_space H' G] :
  has_one C^∞⟮I, N; I', G⟯ :=
⟨times_cont_mdiff_map.const (1 : G)⟩

@[simp, to_additive]
lemma coe_one {G : Type*} [monoid G] [topological_space G] [charted_space H' G] :
  ⇑(1 : C^∞⟮I, N; I', G⟯) = 1 := rfl

end smooth_map

section group_structure

/-!
### Group structure

In this section we show that smooth functions valued in a Lie group inherit a group structure
under pointwise multiplication.
-/

@[to_additive]
instance smooth_map_semigroup {G : Type*} [semigroup G] [topological_space G]
  [charted_space H' G] [has_smooth_mul I' G] :
  semigroup C^∞⟮I, N; I', G⟯ :=
{ mul_assoc := λ a b c, by ext; exact mul_assoc _ _ _,
  ..smooth_map.has_mul}

@[to_additive]
instance smooth_map_monoid {G : Type*} [monoid G] [topological_space G]
  [charted_space H' G] [has_smooth_mul I' G] :
  monoid C^∞⟮I, N; I', G⟯ :=
{ one_mul := λ a, by ext; exact one_mul _,
  mul_one := λ a, by ext; exact mul_one _,
  ..smooth_map_semigroup,
  ..smooth_map.has_one }

@[to_additive]
instance smooth_map_comm_monoid {G : Type*} [comm_monoid G] [topological_space G]
  [charted_space H' G] [has_smooth_mul I' G] :
  comm_monoid C^∞⟮I, N; I', G⟯ :=
{ mul_comm := λ a b, by ext; exact mul_comm _ _,
  ..smooth_map_monoid,
  ..smooth_map.has_one }

@[to_additive]
instance smooth_map_group {G : Type*} [group G] [topological_space G]
  [charted_space H' G] [lie_group I' G] :
  group C^∞⟮I, N; I', G⟯ :=
{ inv := λ f, ⟨λ x, (f x)⁻¹, f.smooth.inv⟩,
  mul_left_inv := λ a, by ext; exact mul_left_inv _,
  div := λ f g, ⟨f / g, f.smooth.div g.smooth⟩,
  div_eq_mul_inv := λ f g, by ext; exact div_eq_mul_inv _ _,
  .. smooth_map_monoid }

@[simp, to_additive]
lemma smooth_map.coe_inv {G : Type*} [group G] [topological_space G]
  [charted_space H' G] [lie_group I' G] (f : C^∞⟮I, N; I', G⟯) :
  ⇑f⁻¹ = f⁻¹ := rfl

@[simp, to_additive]
lemma smooth_map.coe_div {G : Type*} [group G] [topological_space G]
  [charted_space H' G] [lie_group I' G] (f g : C^∞⟮I, N; I', G⟯) :
  ⇑(f / g) = f / g :=
rfl

@[to_additive]
instance smooth_map_comm_group {G : Type*} [comm_group G] [topological_space G]
  [charted_space H' G] [lie_group I' G] :
  comm_group C^∞⟮I, N; I', G⟯ :=
{ ..smooth_map_group,
  ..smooth_map_comm_monoid }

end group_structure

section ring_structure

/-!
### Ring stucture

In this section we show that smooth functions valued in a smooth ring `R` inherit a ring structure
under pointwise multiplication.
-/

instance smooth_map_semiring {R : Type*} [semiring R] [topological_space R]
  [charted_space H' R] [smooth_semiring I' R] :
  semiring C^∞⟮I, N; I', R⟯ :=
{ left_distrib := λ a b c, by ext; exact left_distrib _ _ _,
  right_distrib := λ a b c, by ext; exact right_distrib _ _ _,
  zero_mul := λ a, by ext; exact zero_mul _,
  mul_zero := λ a, by ext; exact mul_zero _,
  ..smooth_map_add_comm_monoid,
  ..smooth_map_monoid }

instance smooth_map_ring {R : Type*} [ring R] [topological_space R]
  [charted_space H' R] [smooth_ring I' R] :
  ring C^∞⟮I, N; I', R⟯ :=
{ ..smooth_map_semiring,
  ..smooth_map_add_comm_group, }

instance smooth_map_comm_ring {R : Type*} [comm_ring R] [topological_space R]
  [charted_space H' R] [smooth_ring I' R] :
  comm_ring C^∞⟮I, N; I', R⟯ :=
{ ..smooth_map_semiring,
  ..smooth_map_add_comm_group,
  ..smooth_map_comm_monoid,}

end ring_structure

section module_structure

/-!
### Semiodule stucture

In this section we show that smooth functions valued in a vector space `M` over a normed
field `𝕜` inherit a vector space structure.
-/

instance smooth_map_has_scalar
  {V : Type*} [normed_group V] [normed_space 𝕜 V] :
  has_scalar 𝕜 C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
⟨λ r f, ⟨r • f, smooth_const.smul f.smooth⟩⟩

@[simp]
lemma smooth_map.coe_smul
  {V : Type*} [normed_group V] [normed_space 𝕜 V] (r : 𝕜) (f : C^∞⟮I, N; 𝓘(𝕜, V), V⟯) :
  ⇑(r • f) = r • f := rfl

instance smooth_map_module
  {V : Type*} [normed_group V] [normed_space 𝕜 V] :
  module 𝕜 C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
module.of_core $
{ smul     := (•),
  smul_add := λ c f g, by ext x; exact smul_add c (f x) (g x),
  add_smul := λ c₁ c₂ f, by ext x; exact add_smul c₁ c₂ (f x),
  mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul c₁ c₂ (f x),
  one_smul := λ f, by ext x; exact one_smul 𝕜 (f x), }

end module_structure

section algebra_structure

/-!
### Algebra structure

In this section we show that smooth functions valued in a normed algebra `A` over a normed field `𝕜`
inherit an algebra structure.
-/

variables {A : Type*} [normed_ring A] [normed_algebra 𝕜 A] [smooth_ring 𝓘(𝕜, A) A]

/-- Smooth constant functions as a `ring_hom`. -/
def smooth_map.C : 𝕜 →+* C^∞⟮I, N; 𝓘(𝕜, A), A⟯ :=
{ to_fun    := λ c : 𝕜, ⟨λ x, ((algebra_map 𝕜 A) c), smooth_const⟩,
  map_one'  := by ext x; exact (algebra_map 𝕜 A).map_one,
  map_mul'  := λ c₁ c₂, by ext x; exact (algebra_map 𝕜 A).map_mul _ _,
  map_zero' := by ext x; exact (algebra_map 𝕜 A).map_zero,
  map_add'  := λ c₁ c₂, by ext x; exact (algebra_map 𝕜 A).map_add _ _ }

instance : algebra 𝕜 C^∞⟮I, N; 𝓘(𝕜, A), A⟯ :=
{ smul := λ r f,
  ⟨r • f, smooth_const.smul f.smooth⟩,
  to_ring_hom := smooth_map.C,
  commutes' := λ c f, by ext x; exact algebra.commutes' _ _,
  smul_def' := λ c f, by ext x; exact algebra.smul_def' _ _,
  ..smooth_map_semiring }

end algebra_structure

section module_over_continuous_functions

/-!
### Structure as module over scalar functions

If `V` is a module over `𝕜`, then we show that the space of smooth functions from `N` to `V`
is naturally a vector space over the ring of smooth functions from `N` to `𝕜`. -/

instance smooth_map_has_scalar'
  {V : Type*} [normed_group V] [normed_space 𝕜 V] :
  has_scalar C^∞⟮I, N; 𝓘(𝕜), 𝕜⟯ C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
⟨λ f g, ⟨λ x, (f x) • (g x), (smooth.smul f.2 g.2)⟩⟩

instance smooth_map_module'
  {V : Type*} [normed_group V] [normed_space 𝕜 V] :
  module C^∞⟮I, N; 𝓘(𝕜), 𝕜⟯ C^∞⟮I, N; 𝓘(𝕜, V), V⟯ :=
{ smul     := (•),
  smul_add := λ c f g, by ext x; exact smul_add (c x) (f x) (g x),
  add_smul := λ c₁ c₂ f, by ext x; exact add_smul (c₁ x) (c₂ x) (f x),
  mul_smul := λ c₁ c₂ f, by ext x; exact mul_smul (c₁ x) (c₂ x) (f x),
  one_smul := λ f, by ext x; exact one_smul 𝕜 (f x),
  zero_smul := λ f, by ext x; exact zero_smul _ _,
  smul_zero := λ r, by ext x; exact smul_zero _, }

end module_over_continuous_functions
