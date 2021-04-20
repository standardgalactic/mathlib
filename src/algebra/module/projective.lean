/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import algebra.module.basic
import linear_algebra.finsupp
import linear_algebra.basis

/-!

# Projective modules

This file contains a definition of a projective module, the proof that
our definition is equivalent to a lifting property, and the
proof that all free modules are projective.

## Main definitions

Let `R` be a ring (or a semiring) and let `M` be an `R`-module (or a semimodule).

* `is_projective R M` : the proposition saying that `M` is a projective `R`-module.

## Main theorems

* `is_projective.lifting_property` : a map from a projective module can be lifted along
  a surjection.

* `is_projective.of_lifting_property` : If for all R-module surjections `A →ₗ B`, all
  maps `M →ₗ B` lift to `M →ₗ A`, then `M` is projective.

* `is_projective.of_free` : Free modules are projective

## Implementation notes

The actual definition of projective we use is that the natural R-module map
from the free R-module on the type M down to M splits. This is more convenient
than certain other definitions which involve quantifying over universes,
and also universe-polymorphic (the ring and module can be in different universes).

Everything works for semirings and semimodules except that apparently
we don't have free semimodules, so here we stick to rings.

## References

https://en.wikipedia.org/wiki/Projective_module

## TODO

- Direct sum of two projective modules is projective.
- Arbitrary sum of projective modules is projective.
- Any module admits a surjection from a projective module.

All of these should be relatively straightforward.

## Tags

projective module

-/

universes u v

/- The actual implementation we choose: `P` is projective if the natural surjection
   from the free `R`-module on `P` to `P` splits. -/
/-- An R-module is projective if it is a direct summand of a free module, or equivalently
  if maps from the module lift along surjections. There are several other equivalent
  definitions. -/
def is_projective
  (R : Type u) [semiring R] (P : Type v) [add_comm_monoid P] [semimodule R P] : Prop :=
∃ s : P →ₗ[R] (P →₀ R), function.left_inverse (finsupp.total P P R id) s

namespace is_projective

section semiring

variables {R : Type u} [semiring R] {P : Type v} [add_comm_monoid P] [semimodule R P]
  {M : Type*} [add_comm_group M] [semimodule R M] {N : Type*} [add_comm_group N] [semimodule R N]

/-- A projective R-module has the property that maps from it lift along surjections. -/
theorem lifting_property (h : is_projective R P) (f : M →ₗ[R] N) (g : P →ₗ[R] N)
  (hf : function.surjective f) : ∃ (h : P →ₗ[R] M), f.comp h = g :=
begin
  /-
  Here's the first step of the proof.
  Recall that `X →₀ R` is Lean's way of talking about the free `R`-module
  on a type `X`. The universal property `finsupp.total` says that to a map
  `X → N` from a type to an `R`-module, we get an associated R-module map
  `(X →₀ R) →ₗ N`. Apply this to a (noncomputable) map `P → M` coming from the map
  `P →ₗ N` and a random splitting of the surjection `M →ₗ N`, and we get
  a map `φ : (P →₀ R) →ₗ M`.
  -/
  let φ : (P →₀ R) →ₗ[R] M := finsupp.total _ _ _ (λ p, function.surj_inv hf (g p)),
  -- By projectivity we have a map `P →ₗ (P →₀ R)`;
  cases h with s hs,
  -- Compose to get `P →ₗ M`. This works.
  use φ.comp s,
  ext p,
  conv_rhs {rw ← hs p},
  simp [φ, finsupp.total_apply, function.surj_inv_eq hf],
end

/-- A module which satisfies the universal property is projective. Note that the universe variables
in `huniv` are somewhat restricted. -/
theorem of_lifting_property {R : Type u} [semiring R]
  {P : Type v} [add_comm_monoid P] [semimodule R P]
  -- If for all surjections of `R`-modules `M →ₗ N`, all maps `P →ₗ N` lift to `P →ₗ M`,
  (huniv : ∀ {M : Type (max v u)} {N : Type v} [add_comm_monoid M] [add_comm_monoid N],
    by exactI
    ∀ [semimodule R M] [semimodule R N],
    by exactI
    ∀ (f : M →ₗ[R] N) (g : P →ₗ[R] N),
  function.surjective f → ∃ (h : P →ₗ[R] M), f.comp h = g) :
  -- then `P` is projective.
  is_projective R P :=
begin
  -- let `s` be the universal map `(P →₀ R) →ₗ P` coming from the identity map `P →ₗ P`.
  obtain ⟨s, hs⟩ : ∃ (s : P →ₗ[R] P →₀ R),
    (finsupp.total P P R id).comp s = linear_map.id :=
    huniv (finsupp.total P P R (id : P → P)) (linear_map.id : P →ₗ[R] P) _,
  -- This `s` works.
  { use s,
    rwa linear_map.ext_iff at hs },
  { intro p,
    use finsupp.single p 1,
    simp },
end

end semiring

section ring

variables {R : Type u} [ring R] {P : Type v} [add_comm_group P] [module R P]

/-- Free modules are projective. -/
theorem of_free {ι : Type*} {b : ι → P} (hb : is_basis R b) : is_projective R P :=
begin
  -- need P →ₗ (P →₀ R) for definition of projective.
  -- get it from `ι → (P →₀ R)` coming from `b`.
  use hb.constr (λ i, finsupp.single (b i) 1),
  intro m,
  simp only [hb.constr_apply, mul_one, id.def, finsupp.smul_single', finsupp.total_single,
    linear_map.map_finsupp_sum],
  exact hb.total_repr m,
end

end ring

end is_projective
