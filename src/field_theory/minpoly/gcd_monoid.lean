/-
Copyright (c) 2019 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import data.polynomial.field_division
import ring_theory.adjoin_root
import field_theory.minpoly.field
import ring_theory.polynomial.gauss_lemma

/-!
# Minimal polynomials over a GCD monoid

This file specializes the theory of minpoly to the case of an algebra over a GCD monoid.

## Main results

 * `gcd_domain_eq_field_fractions`: For GCD domains, the minimal polynomial over the ring is the
    same as the minimal polynomial over the fraction field.

 * `gcd_domain_dvd` : For GCD domains, the minimal polynomial divides any primitive polynomial
    that has the integral element as root.

 * `gcd_domain_unique` : The minimal polynomial of an element `x` is uniquely characterized by
    its defining property: if there is another monic polynomial of minimal degree that has `x` as a
    root, then this polynomial is equal to the minimal polynomial of `x`.
-/

open_locale classical polynomial
open polynomial set function minpoly

namespace minpoly

variables {R S : Type*} [comm_ring R] [comm_ring S] [is_domain R] [is_domain S] [algebra R S]

section gcd_domain

variables (K L : Type*) [normalized_gcd_monoid R] [field K] [algebra R K] [is_fraction_ring R K]
  [field L] [algebra S L] [algebra K L] [algebra R L] [is_scalar_tower R K L]
  [is_scalar_tower R S L] {s : S} (hs : is_integral R s)

include hs

/-- For GCD domains, the minimal polynomial over the ring is the same as the minimal polynomial
over the fraction field. See `minpoly.gcd_domain_eq_field_fractions'` if `S` is already a
`K`-algebra. -/
lemma gcd_domain_eq_field_fractions :
  minpoly K (algebra_map S L s) = (minpoly R s).map (algebra_map R K) :=
begin
  refine (eq_of_irreducible_of_monic _ _ _).symm,
  { exact (polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map
      (polynomial.monic.is_primitive (monic hs))).1 (irreducible hs) },
   { rw [aeval_map_algebra_map, aeval_algebra_map_apply, aeval, map_zero] },
  { exact (monic hs).map _ }
end

/-- For GCD domains, the minimal polynomial over the ring is the same as the minimal polynomial
over the fraction field. Compared to `minpoly.gcd_domain_eq_field_fractions`, this version is useful
if the element is in a ring that is already a `K`-algebra. -/
lemma gcd_domain_eq_field_fractions' [algebra K S] [is_scalar_tower R K S] :
  minpoly K s = (minpoly R s).map (algebra_map R K) :=
begin
  let L := fraction_ring S,
  rw [← gcd_domain_eq_field_fractions K L hs],
  refine minpoly.eq_of_algebra_map_eq (is_fraction_ring.injective S L)
    (is_integral_of_is_scalar_tower hs) rfl
end

variable [no_zero_smul_divisors R S]

/-- For GCD domains, the minimal polynomial divides any primitive polynomial that has the integral
element as root. See also `minpoly.dvd` which relaxes the assumptions on `S` in exchange for
stronger assumptions on `R`. -/
lemma gcd_domain_dvd {P : R[X]} (hP : P ≠ 0) (hroot : polynomial.aeval s P = 0) : minpoly R s ∣ P :=
begin
  let K := fraction_ring R,
  let L := fraction_ring S,
  let P₁ := P.prim_part,
  suffices : minpoly R s ∣ P₁,
  { exact dvd_trans this (prim_part_dvd _) },
  apply (is_primitive.dvd_iff_fraction_map_dvd_fraction_map K (monic hs).is_primitive
    P.is_primitive_prim_part).2,
  let y := algebra_map S L s,
  have hy : is_integral R y := hs.algebra_map,
  rw [← gcd_domain_eq_field_fractions K L hs],
  refine dvd _ _ _,
  rw [aeval_map_algebra_map, aeval_algebra_map_apply, aeval_prim_part_eq_zero hP hroot, map_zero]
end

/-- If an element `x` is a root of a nonzero polynomial `p`, then the degree of `p` is at least the
degree of the minimal polynomial of `x`. See also `minpoly.degree_le_of_ne_zero` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
lemma gcd_domain_degree_le_of_ne_zero {p : R[X]} (hp0 : p ≠ 0) (hp : polynomial.aeval s p = 0) :
  degree (minpoly R s) ≤ degree p :=
begin
  rw [degree_eq_nat_degree (minpoly.ne_zero hs), degree_eq_nat_degree hp0],
  norm_cast,
  exact nat_degree_le_of_dvd (gcd_domain_dvd hs hp0 hp) hp0
end

omit hs

/-- The minimal polynomial of an element `x` is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has `x` as a root, then this polynomial
is equal to the minimal polynomial of `x`. See also `minpoly.unique` which relaxes the
assumptions on `S` in exchange for stronger assumptions on `R`. -/
lemma gcd_domain_unique {P : R[X]} (hmo : P.monic) (hP : polynomial.aeval s P = 0)
  (Pmin : ∀ Q : R[X], Q.monic → polynomial.aeval s Q = 0 → degree P ≤ degree Q) :
  P = minpoly R s :=
begin
  have hs : is_integral R s := ⟨P, hmo, hP⟩,
  symmetry, apply eq_of_sub_eq_zero,
  by_contra hnz,
  have := gcd_domain_degree_le_of_ne_zero hs hnz (by simp [hP]),
  contrapose! this,
  refine degree_sub_lt _ (ne_zero hs) _,
  { exact le_antisymm (min R s hmo hP)
      (Pmin (minpoly R s) (monic hs) (aeval R s)) },
  { rw [(monic hs).leading_coeff, hmo.leading_coeff] }
end

end gcd_domain

section adjoin_root

noncomputable theory

open algebra polynomial adjoin_root

variables {R} {x : S} [normalized_gcd_monoid R] [no_zero_smul_divisors R S]

lemma to_adjoin.injective (hx : is_integral R x) :
  function.injective (minpoly.to_adjoin R x) :=
begin
  refine (injective_iff_map_eq_zero _).2 (λ P₁ hP₁, _),
  obtain ⟨P, hP⟩ := mk_surjective (minpoly.monic hx) P₁,
  by_cases hPzero : P = 0,
  { simpa [hPzero] using hP.symm },
  have hPcont : P.content ≠ 0 := λ h, hPzero (content_eq_zero_iff.1 h),
  rw [← hP, minpoly.to_adjoin_apply', lift_hom_mk, ← subalgebra.coe_eq_zero,
    aeval_subalgebra_coe, set_like.coe_mk, P.eq_C_content_mul_prim_part, aeval_mul, aeval_C] at hP₁,
  replace hP₁ := eq_zero_of_ne_zero_of_mul_left_eq_zero
    ((map_ne_zero_iff _ (no_zero_smul_divisors.algebra_map_injective R S)).2 hPcont) hP₁,
  obtain ⟨Q, hQ⟩ := minpoly.gcd_domain_dvd hx P.is_primitive_prim_part.ne_zero hP₁,
  rw [P.eq_C_content_mul_prim_part] at hP,
  simpa [hQ] using hP.symm
end

/-- The algebra isomorphism `adjoin_root (minpoly R x) ≃ₐ[R] adjoin R x` -/
@[simps] def equiv_adjoin (hx : is_integral R x) :
  adjoin_root (minpoly R x) ≃ₐ[R] adjoin R ({x} : set S) :=
alg_equiv.of_bijective (minpoly.to_adjoin R x)
  ⟨minpoly.to_adjoin.injective hx, minpoly.to_adjoin.surjective R x⟩

/-- The `power_basis` of `adjoin R {x}` given by `x`. See `algebra.adjoin.power_basis` for a version
over a field. -/
@[simps] def _root_.algebra.adjoin.power_basis' (hx : _root_.is_integral R x) :
  _root_.power_basis R (algebra.adjoin R ({x} : set S)) :=
power_basis.map (adjoin_root.power_basis' (minpoly.monic hx)) (minpoly.equiv_adjoin hx)

/-- The power basis given by `x` if `B.gen ∈ adjoin R {x}`. -/
@[simps] noncomputable def _root_.power_basis.of_gen_mem_adjoin' (B : _root_.power_basis R S)
  (hint : is_integral R x) (hx : B.gen ∈ adjoin R ({x} : set S)) :
  _root_.power_basis R S :=
(algebra.adjoin.power_basis' hint).map $
  (subalgebra.equiv_of_eq _ _ $ power_basis.adjoin_eq_top_of_gen_mem_adjoin hx).trans
  subalgebra.top_equiv

end adjoin_root

end minpoly