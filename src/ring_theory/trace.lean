/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import linear_algebra.bilinear_form
import ring_theory.power_basis

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the trace is defined specifically for finite field extensions.
The definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the trace for left multiplication (`algebra.left_mul_matrix`,
i.e. `algebra.lmul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't matter anyway.

## References

 * https://en.wikipedia.org/wiki/Field_trace

-/

universes u v w

variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
variables [algebra R S] [algebra R T]
variables {K L : Type*} [field K] [field L] [algebra K L]
variables {ι : Type w} [fintype ι]

open finite_dimensional
open linear_map
open matrix

open_locale big_operators
open_locale matrix

namespace algebra

variables (b : basis ι R S)

variables (R S)

/-- The trace of an element `s` of an `R`-algebra is the trace of `(*) s`,
as an `R`-linear map. -/
@[simps]
noncomputable def trace : S →ₗ[R] R :=
(linear_map.trace R S).comp (lmul R S).to_linear_map

variables {S}

lemma trace_eq_zero_of_not_exists_basis
  (h : ¬ ∃ (s : set S) (b : basis s R S), s.finite) : trace R S = 0 :=
by { ext s, simp [linear_map.trace, h] }

include b

variables {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
lemma trace_eq_matrix_trace [decidable_eq ι] (b : basis ι R S) (s : S) :
  trace R S s = matrix.trace _ R _ (algebra.left_mul_matrix b s) :=
by rw [trace_apply, linear_map.trace_eq_matrix_trace _ b, to_matrix_lmul_eq]

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
lemma trace_algebra_map_of_basis (x : R) :
  trace R S (algebra_map R S x) = fintype.card ι • x :=
begin
  haveI := classical.dec_eq ι,
  rw [trace_apply, linear_map.trace_eq_matrix_trace R b, trace_diag],
  convert finset.sum_const _,
  ext i,
  simp,
end
omit b

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`.

(If `L` is not finite-dimensional over `K`, then `trace` and `finrank` return `0`.)
-/
@[simp]
lemma trace_algebra_map (x : K) : trace K L (algebra_map K L x) = finrank K L • x :=
begin
  by_cases H : ∃ (s : set L) (b : basis s K L), s.finite,
  { haveI : fintype H.some := H.some_spec.some_spec.some,
    rw [trace_algebra_map_of_basis H.some_spec.some, finrank_eq_card_basis H.some_spec.some] },
  { simp [trace_eq_zero_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis_finite H] }
end

section trace_form

variables (R S)

/-- The `trace_form` maps `x y : S` to the trace of `x * y`.
It is a symmetric bilinear form and is nondegenerate if the extension is separable. -/
noncomputable def trace_form : bilin_form R S :=
(linear_map.compr₂ (lmul R S).to_linear_map (trace R S)).to_bilin

variables {S}

-- This is a nicer lemma than the one produced by `@[simps] def trace_form`.
@[simp] lemma trace_form_apply (x y : S) : trace_form R S x y = trace R S (x * y) := rfl

lemma trace_form_is_sym : sym_bilin_form.is_sym (trace_form R S) :=
λ x y, congr_arg (trace R S) (mul_comm _ _)

lemma trace_form_to_matrix [decidable_eq ι] (i j) :
  bilin_form.to_matrix b (trace_form R S) i j = trace R S (b i * b j) :=
by rw [bilin_form.to_matrix_apply, trace_form_apply]

lemma trace_form_to_matrix_power_basis (h : power_basis R S) :
  bilin_form.to_matrix h.basis (trace_form R S) = λ i j, (trace R S (h.gen ^ (i + j : ℕ))) :=
by { ext, rw [trace_form_to_matrix, pow_add, h.basis_eq_pow, h.basis_eq_pow] }

end trace_form

end algebra
