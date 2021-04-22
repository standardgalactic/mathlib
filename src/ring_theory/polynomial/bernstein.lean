/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.polynomial.derivative
import data.polynomial.algebra_map
import data.mv_polynomial.pderiv
import data.nat.choose.sum
import linear_algebra.basis
import ring_theory.polynomial.pochhammer
import tactic.omega

/-!
# Bernstein polynomials

The definition of the Bernstein polynomials
```
bernstein_polynomial (R : Type*) [comm_ring R] (n ν : ℕ) : polynomial R :=
(choose n ν) * X^ν * (1 - X)^(n - ν)
```
and the fact that for `ν : fin (n+1)` these are linearly independent over `ℚ`.

We prove the basic identities
* `(finset.range (n + 1)).sum (λ ν, bernstein_polynomial R n ν) = 1`
* `(finset.range (n + 1)).sum (λ ν, ν • bernstein_polynomial R n ν) = n • X`
* `(finset.range (n + 1)).sum (λ ν, (ν * (ν-1)) • bernstein_polynomial R n ν) = (n * (n-1)) • X^2`

## Notes

See also `analysis.special_functions.bernstein`, which defines the Bernstein approximations
of a continuous function `f : C([0,1], ℝ)`, and shows that these converge uniformly to `f`.
-/

noncomputable theory


open nat (choose)
open polynomial (X)

variables (R : Type*) [comm_ring R]

/--
`bernstein_polynomial R n ν` is `(choose n ν) * X^ν * (1 - X)^(n - ν)`.

Although the coefficients are integers, it is convenient to work over an arbitrary commutative ring.
-/
def bernstein_polynomial (n ν : ℕ) : polynomial R := choose n ν * X^ν * (1 - X)^(n - ν)

example : bernstein_polynomial ℤ 3 2 = 3 * X^2 - 3 * X^3 :=
begin
  norm_num [bernstein_polynomial, choose],
  ring,
end

namespace bernstein_polynomial

lemma eq_zero_of_lt {n ν : ℕ} (h : n < ν) : bernstein_polynomial R n ν = 0 :=
by simp [bernstein_polynomial, nat.choose_eq_zero_of_lt h]

section
variables {R} {S : Type*} [comm_ring S]

@[simp] lemma map (f : R →+* S) (n ν : ℕ) :
  (bernstein_polynomial R n ν).map f = bernstein_polynomial S n ν :=
by simp [bernstein_polynomial]

end

lemma flip (n ν : ℕ) (h : ν ≤ n) :
  (bernstein_polynomial R n ν).comp (1-X) = bernstein_polynomial R n (n-ν) :=
begin
  dsimp [bernstein_polynomial],
  simp [h, nat.sub_sub_assoc, mul_right_comm],
end

lemma flip' (n ν : ℕ) (h : ν ≤ n) :
  bernstein_polynomial R n ν = (bernstein_polynomial R n (n-ν)).comp (1-X) :=
begin
  rw [←flip _ _ _ h, polynomial.comp_assoc],
  simp,
end

lemma eval_at_0 (n ν : ℕ) : (bernstein_polynomial R n ν).eval 0 = if ν = 0 then 1 else 0 :=
begin
  dsimp [bernstein_polynomial],
  split_ifs,
  { subst h, simp, },
  { simp [zero_pow (nat.pos_of_ne_zero h)], },
end

lemma eval_at_1 (n ν : ℕ) : (bernstein_polynomial R n ν).eval 1 = if ν = n then 1 else 0 :=
begin
  dsimp [bernstein_polynomial],
  split_ifs,
  { subst h, simp, },
  { by_cases w : 0 < n - ν,
    { simp [zero_pow w], },
    { simp [(show n < ν, by omega), nat.choose_eq_zero_of_lt], }, },
end.

lemma derivative_succ_aux (n ν : ℕ) :
  (bernstein_polynomial R (n+1) (ν+1)).derivative =
    (n+1) * (bernstein_polynomial R n ν - bernstein_polynomial R n (ν + 1)) :=
begin
  dsimp [bernstein_polynomial],
  suffices :
    ↑((n + 1).choose (ν + 1)) * ((↑ν + 1) * X ^ ν) * (1 - X) ^ (n - ν)
      -(↑((n + 1).choose (ν + 1)) * X ^ (ν + 1) * (↑(n - ν) * (1 - X) ^ (n - ν - 1))) =
    (↑n + 1) * (↑(n.choose ν) * X ^ ν * (1 - X) ^ (n - ν) -
         ↑(n.choose (ν + 1)) * X ^ (ν + 1) * (1 - X) ^ (n - (ν + 1))),
  { simpa [polynomial.derivative_pow, ←sub_eq_add_neg], },
  conv_rhs { rw mul_sub, },
  -- We'll prove the two terms match up separately.
  refine congr (congr_arg has_sub.sub _) _,
  { simp only [←mul_assoc],
    refine congr (congr_arg (*) (congr (congr_arg (*) _) rfl)) rfl,
    -- Now it's just about binomial coefficients
    exact_mod_cast congr_arg (λ m : ℕ, (m : polynomial R)) (nat.succ_mul_choose_eq n ν).symm, },
  { rw nat.sub_sub, rw [←mul_assoc,←mul_assoc], congr' 1,
    rw mul_comm , rw [←mul_assoc,←mul_assoc],  congr' 1,
    norm_cast,
    congr' 1,
    convert (nat.choose_mul_succ_eq n (ν + 1)).symm using 1,
    { convert mul_comm _ _ using 2,
      simp, },
    { apply mul_comm, }, },
end

lemma derivative_succ (n ν : ℕ) :
  (bernstein_polynomial R n (ν+1)).derivative =
    n * (bernstein_polynomial R (n-1) ν - bernstein_polynomial R (n-1) (ν+1)) :=
begin
  cases n,
  { simp [bernstein_polynomial], },
  { apply derivative_succ_aux, }
end

lemma derivative_zero (n : ℕ) :
  (bernstein_polynomial R n 0).derivative = -n * bernstein_polynomial R (n-1) 0 :=
begin
  dsimp [bernstein_polynomial],
  simp [polynomial.derivative_pow],
end

lemma iterate_derivative_at_0_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
  k < ν → (polynomial.derivative^[k] (bernstein_polynomial R n ν)).eval 0 = 0 :=
begin
  cases ν,
  { rintro ⟨⟩, },
  { intro w,
    replace w := nat.lt_succ_iff.mp w,
    revert w,
    induction k with k ih generalizing n ν,
    { simp [eval_at_0], },
    { simp only [derivative_succ, int.coe_nat_eq_zero, int.nat_cast_eq_coe_nat, mul_eq_zero,
        function.comp_app, function.iterate_succ,
        polynomial.iterate_derivative_sub, polynomial.iterate_derivative_cast_nat_mul,
        polynomial.eval_mul, polynomial.eval_nat_cast, polynomial.eval_sub],
      intro h,
      apply mul_eq_zero_of_right,
      rw ih,
      simp only [sub_zero],
      convert @ih (n-1) (ν-1) _,
      { omega, },
      { omega, },
      { exact le_of_lt h, }, }, },
end

@[simp]
lemma iterate_derivative_succ_at_0_eq_zero (n ν : ℕ) :
  (polynomial.derivative^[ν] (bernstein_polynomial R n (ν+1))).eval 0 = 0 :=
iterate_derivative_at_0_eq_zero_of_lt R n (lt_add_one ν)

open polynomial

/-- A Pochhammer identity that is useful for `bernstein_polynomial.iterate_derivative_at_0_aux₂`. -/
lemma iterate_derivative_at_0_aux₁ (n k : ℕ) :
  k * polynomial.eval (k-n) (pochhammer ℕ n) = (k-n) * polynomial.eval (k-n+1) (pochhammer ℕ n) :=
begin
  have p :=
    congr_arg (eval (k-n)) ((pochhammer_succ_right ℕ n).symm.trans (pochhammer_succ_left ℕ n)),
  simp only [nat.cast_id, eval_X, eval_one, eval_mul, eval_nat_cast, eval_add, eval_comp] at p,
  rw [mul_comm] at p,
  rw ←p,
  by_cases h : n ≤ k,
  { rw nat.sub_add_cancel h, },
  { simp only [not_le] at h,
    simp only [mul_eq_mul_right_iff],
    right,
    rw nat.sub_eq_zero_of_le (le_of_lt h),
    simp only [pochhammer_eval_zero, ite_eq_right_iff],
    rintro rfl,
    cases h, },
end

lemma iterate_derivative_at_0_aux₂ (n k : ℕ) :
  (↑k) * polynomial.eval ↑(k-n) (pochhammer R n) =
    ↑(k-n) * polynomial.eval (↑(k-n+1)) (pochhammer R n) :=
by simpa using congr_arg (algebra_map ℕ R) (iterate_derivative_at_0_aux₁ n k)

@[simp]
lemma iterate_derivative_at_0 (n ν : ℕ) :
  (polynomial.derivative^[ν] (bernstein_polynomial R n ν)).eval 0 =
    (pochhammer R ν).eval (n - (ν - 1) : ℕ) :=
begin
  by_cases h : ν ≤ n,
  { induction ν with ν ih generalizing n h,
    { simp [eval_at_0], },
    { simp only [nat.succ_eq_add_one] at h,
      have h' : ν ≤ n-1 := nat.le_sub_right_of_add_le h,
      have w₁ : ((n - ν : ℕ) + 1 : R) = (n - ν + 1 : ℕ), { push_cast, },
      simp only [derivative_succ, ih (n-1) h', iterate_derivative_succ_at_0_eq_zero,
        nat.succ_sub_succ_eq_sub, nat.sub_zero, sub_zero,
        iterate_derivative_sub, iterate_derivative_cast_nat_mul,
        eval_one, eval_mul, eval_add, eval_sub, eval_X, eval_comp, eval_nat_cast,
        function.comp_app, function.iterate_succ, pochhammer_succ_left],
      rw [w₁],
      by_cases h'' : ν = 0,
      { subst h'', simp, },
      { have w₂ : n - 1 - (ν - 1) = n - ν, { rw [nat.sub_sub], rw nat.add_sub_cancel', omega, },
        simpa [w₂] using (iterate_derivative_at_0_aux₂ R ν n), }, }, },
  { simp only [not_le] at h,
    have w₁ : n - (ν - 1) = 0, { omega, },
    have w₂ : ν ≠ 0, { omega, },
    rw [w₁, eq_zero_of_lt R h],
    simp [w₂], }
end

lemma iterate_derivative_at_0_ne_zero [char_zero R] (n ν : ℕ) (h : ν ≤ n) :
  (polynomial.derivative^[ν] (bernstein_polynomial R n ν)).eval 0 ≠ 0 :=
begin
  simp only [int.coe_nat_eq_zero, bernstein_polynomial.iterate_derivative_at_0, ne.def,
    nat.cast_eq_zero],
  simp only [←pochhammer_eval_cast],
  norm_cast,
  apply ne_of_gt,
  by_cases h : ν = 0,
  { subst h, simp, },
  { apply pochhammer_pos,
    omega, },
end

/-!
Rather than redoing the work of evaluating the derivatives at 1,
we use the symmetry of the Bernstein polynomials.
-/
lemma iterate_derivative_at_1_eq_zero_of_lt (n : ℕ) {ν k : ℕ} :
  k < n - ν → (polynomial.derivative^[k] (bernstein_polynomial R n ν)).eval 1 = 0 :=
begin
  intro w,
  rw flip' _ _ _ (show ν ≤ n, by omega),
  simp [polynomial.eval_comp, iterate_derivative_at_0_eq_zero_of_lt R n w],
end

@[simp]
lemma iterate_derivative_at_1 (n ν : ℕ) (h : ν ≤ n) :
  (polynomial.derivative^[n-ν] (bernstein_polynomial R n ν)).eval 1 =
    (-1)^(n-ν) * (pochhammer R (n - ν)).eval (ν + 1) :=
begin
  rw flip' _ _ _ h,
  simp [polynomial.eval_comp, h],
  by_cases h' : n = ν,
  { subst h', simp, },
  { replace h : ν < n, { omega, },
    congr,
    norm_cast,
    congr,
    omega, },
end

lemma iterate_derivative_at_1_ne_zero [char_zero R] (n ν : ℕ) (h : ν ≤ n) :
  (polynomial.derivative^[n-ν] (bernstein_polynomial R n ν)).eval 1 ≠ 0 :=
begin
  simp only [bernstein_polynomial.iterate_derivative_at_1 _ _ _ h, ne.def,
    int.coe_nat_eq_zero, neg_one_pow_mul_eq_zero_iff, nat.cast_eq_zero],
    rw ←nat.cast_succ,
  simp only [←pochhammer_eval_cast],
  norm_cast,
  apply ne_of_gt,
  apply pochhammer_pos,
  exact nat.succ_pos ν,
end

open submodule

lemma linear_independent_aux (n k : ℕ) (h : k ≤ n + 1):
  linear_independent ℚ (λ ν : fin k, bernstein_polynomial ℚ n ν) :=
begin
  induction k with k ih,
  { apply linear_independent_empty_type,
    rintro ⟨⟨n, ⟨⟩⟩⟩, },
  { apply linear_independent_fin_succ'.mpr,
    fsplit,
    { exact ih (le_of_lt h), },
    { -- The actual work!
      -- We show that the (n-k)-th derivative at 1 doesn't vanish,
      -- but vanishes for everything in the span.
      clear ih,
      simp only [nat.succ_eq_add_one, add_le_add_iff_right] at h,
      simp only [fin.coe_last, fin.init_def],
      dsimp,
      apply not_mem_span_of_apply_not_mem_span_image ((polynomial.derivative_lhom ℚ)^(n-k)),
      simp only [not_exists, not_and, submodule.mem_map, submodule.span_image],
      intros p m,
      apply_fun (polynomial.eval (1 : ℚ)),
      simp only [polynomial.derivative_lhom_coe, linear_map.pow_apply],
      -- The right hand side is nonzero,
      -- so it will suffice to show the left hand side is always zero.
      suffices : (polynomial.derivative^[n-k] p).eval 1 = 0,
      { rw [this],
        exact (iterate_derivative_at_1_ne_zero ℚ n k h).symm, },
      apply span_induction m,
      { simp,
        rintro ⟨a, w⟩, simp only [fin.coe_mk],
        rw [iterate_derivative_at_1_eq_zero_of_lt ℚ _ (show n - k < n - a, by omega)], },
      { simp, },
      { intros x y hx hy, simp [hx, hy], },
      { intros a x h, simp [h], }, }, },
end

/--
The Bernstein polynomials are linearly independent.

We prove by induction that the collection of `bernstein_polynomial n ν` for `ν = 0, ..., k`
are linearly independent.
The inductive step relies on the observation that the `(n-k)`-th derivative, evaluated at 1,
annihilates `bernstein_polynomial n ν` for `ν < k`, but has a nonzero value at `ν = k`.
-/

lemma linear_independent (n : ℕ) :
  linear_independent ℚ (λ ν : fin (n+1), bernstein_polynomial ℚ n ν) :=
linear_independent_aux n (n+1) (le_refl _)

lemma sum (n : ℕ) : (finset.range (n + 1)).sum (λ ν, bernstein_polynomial R n ν) = 1 :=
begin
  -- We calculate `(x + (1-x))^n` in two different ways.
  conv { congr, congr, skip, funext, dsimp [bernstein_polynomial], rw [mul_assoc, mul_comm], },
  rw ←add_pow,
  simp,
end


open polynomial
open mv_polynomial

lemma sum_smul (n : ℕ) :
  (finset.range (n + 1)).sum (λ ν, ν • bernstein_polynomial R n ν) = n • X :=
begin
  -- We calculate the `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.

  -- We'll work in `mv_polynomial bool R`.
  let x : mv_polynomial bool R := mv_polynomial.X tt,
  let y : mv_polynomial bool R := mv_polynomial.X ff,

  have pderiv_tt_x : pderiv tt x = 1, { simp [x], },
  have pderiv_tt_y : pderiv tt y = 0, { simp [pderiv_X, y], },

  let e : bool → polynomial R := λ i, cond i X (1-X),

  -- Start with `(x+y)^n = (x+y)^n`,
  -- take the `x`-derivative, evaluate at `x=X, y=1-X`, and multiply by `X`:
  have h : (x+y)^n = (x+y)^n := rfl,
  apply_fun (pderiv tt) at h,
  apply_fun (aeval e) at h,
  apply_fun (λ p, p * X) at h,

  -- On the left hand side we'll use the binomial theorem, then simplify.

  -- We first prepare a tedious rewrite:
  have w : ∀ k : ℕ,
    ↑k * polynomial.X ^ (k - 1) * (1 - polynomial.X) ^ (n - k) * ↑(n.choose k) * polynomial.X =
      k • bernstein_polynomial R n k,
  { rintro (_|k),
    { simp, },
    { dsimp [bernstein_polynomial],
      simp only [←nat_cast_mul, nat.succ_eq_add_one, nat.add_succ_sub_one, add_zero, pow_succ],
      push_cast,
      ring, }, },

  conv at h {
    to_lhs,
    rw [add_pow, (pderiv tt).map_sum, (mv_polynomial.aeval e).map_sum, finset.sum_mul],
    -- Step inside the sum:
    apply_congr, skip,
    simp [pderiv_mul, pderiv_tt_x, pderiv_tt_y, e, w], },
  -- On the right hand side, we'll just simplify.
  conv at h {
    to_rhs,
    rw [pderiv_pow, (pderiv tt).map_add, pderiv_tt_x, pderiv_tt_y],
    simp [e] },
  simpa using h,
end

lemma sum_mul_smul (n : ℕ) :
  (finset.range (n + 1)).sum (λ ν, (ν * (ν-1)) • bernstein_polynomial R n ν) =
    (n * (n-1)) • X^2 :=
begin
  -- We calculate the second `x`-derivative of `(x+y)^n`, evaluated at `y=(1-x)`,
  -- either directly or by using the binomial theorem.

  -- We'll work in `mv_polynomial bool R`.
  let x : mv_polynomial bool R := mv_polynomial.X tt,
  let y : mv_polynomial bool R := mv_polynomial.X ff,

  have pderiv_tt_x : pderiv tt x = 1, { simp [x], },
  have pderiv_tt_y : pderiv tt y = 0, { simp [pderiv_X, y], },

  let e : bool → polynomial R := λ i, cond i X (1-X),

  -- Start with `(x+y)^n = (x+y)^n`,
  -- take the second `x`-derivative, evaluate at `x=X, y=1-X`, and multiply by `X`:
  have h : (x+y)^n = (x+y)^n := rfl,
  apply_fun (pderiv tt) at h,
  apply_fun (pderiv tt) at h,
  apply_fun (aeval e) at h,
  apply_fun (λ p, p * X^2) at h,

  -- On the left hand side we'll use the binomial theorem, then simplify.

  -- We first prepare a tedious rewrite:
  have w : ∀ k : ℕ,
    ↑k * (↑(k-1) * polynomial.X ^ (k - 1 - 1)) *
      (1 - polynomial.X) ^ (n - k) * ↑(n.choose k) * polynomial.X^2 =
      (k * (k-1)) • bernstein_polynomial R n k,
  { rintro (_|k),
    { simp, },
    { rcases k with (_|k),
      { simp, },
      { dsimp [bernstein_polynomial],
        simp only [←nat_cast_mul, nat.succ_eq_add_one, nat.add_succ_sub_one, add_zero, pow_succ],
        push_cast,
        ring, }, }, },

  conv at h {
    to_lhs,
    rw [add_pow, (pderiv tt).map_sum, (pderiv tt).map_sum, (mv_polynomial.aeval e).map_sum,
      finset.sum_mul],
    -- Step inside the sum:
    apply_congr, skip,
    simp [pderiv_mul, pderiv_tt_x, pderiv_tt_y, e, w] },
  -- On the right hand side, we'll just simplify.
  conv at h {
    to_rhs,
    simp only [pderiv_one, pderiv_mul, pderiv_pow, pderiv_nat_cast, (pderiv tt).map_add,
      pderiv_tt_x, pderiv_tt_y],
    simp [e, smul_smul] },
  simpa using h,
end

/--
A certain linear combination of the previous three identities,
which we'll want later.
-/
lemma variance (n : ℕ) :
  (finset.range (n+1)).sum (λ ν, (n • polynomial.X - ν)^2 * bernstein_polynomial R n ν) =
    n • polynomial.X * (1 - polynomial.X) :=
begin
  have p :
    (finset.range (n+1)).sum (λ ν, (ν * (ν-1)) • bernstein_polynomial R n ν) +
    (1 - (2 * n) • polynomial.X) * (finset.range (n+1)).sum (λ ν, ν • bernstein_polynomial R n ν) +
    (n^2 • X^2) * (finset.range (n+1)).sum (λ ν, bernstein_polynomial R n ν) = _ := rfl,
  conv at p { to_lhs,
    rw [finset.mul_sum, finset.mul_sum, ←finset.sum_add_distrib, ←finset.sum_add_distrib],
    simp only [←nat_cast_mul],
    simp only [←mul_assoc],
    simp only [←add_mul], },
  conv at p { to_rhs,
    rw [sum, sum_smul, sum_mul_smul, ←nat_cast_mul], },
  calc _ = _ : finset.sum_congr rfl (λ k m, _)
     ... = _ : p
     ... = _ : _,
  { congr' 1, simp only [←nat_cast_mul] with push_cast,
    cases k; { simp, ring, }, },
  { simp only [←nat_cast_mul] with push_cast,
    cases n; { simp, ring, }, },
end

end bernstein_polynomial
