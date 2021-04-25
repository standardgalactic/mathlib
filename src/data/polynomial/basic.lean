/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import tactic.ring_exp
import tactic.chain
import algebra.monoid_algebra
import data.finset.sort

/-!
# Theory of univariate polynomials

Polynomials are represented as `add_monoid_algebra R ℕ`, where `R` is a commutative semiring.
In this file, we define `polynomial`, provide basic instances, and prove an `ext` lemma.
-/

noncomputable theory

/-- `polynomial R` is the type of univariate polynomials over `R`.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
def polynomial (R : Type*) [semiring R] := add_monoid_algebra R ℕ

open finsupp add_monoid_algebra
open_locale big_operators

namespace polynomial
universes u
variables {R : Type u} {a : R} {m n : ℕ}

section semiring
variables [semiring R] {p q : polynomial R}

instance : inhabited (polynomial R) := add_monoid_algebra.inhabited _ _
instance : semiring (polynomial R) := add_monoid_algebra.semiring
instance {S} [semiring S] [module S R] : module S (polynomial R) :=
add_monoid_algebra.module
instance {S₁ S₂} [semiring S₁] [semiring S₂] [module S₁ R] [module S₂ R]
  [smul_comm_class S₁ S₂ R] : smul_comm_class S₁ S₂ (polynomial R) :=
add_monoid_algebra.smul_comm_class
instance {S₁ S₂} [has_scalar S₁ S₂] [semiring S₁] [semiring S₂] [module S₁ R] [module S₂ R]
  [is_scalar_tower S₁ S₂ R] : is_scalar_tower S₁ S₂ (polynomial R) :=
add_monoid_algebra.is_scalar_tower

instance [subsingleton R] : unique (polynomial R) := add_monoid_algebra.unique

/--
The set of all `n` such that `X^n` has a non-zero coefficient.
-/
def support (p : polynomial R) : finset ℕ :=
p.support

@[simp] lemma support_zero : (0 : polynomial R).support = ∅ := rfl

@[simp] lemma support_eq_empty : p.support = ∅ ↔ p = 0 :=
by simp [support]

lemma card_support_eq_zero : p.support.card = 0 ↔ p = 0 :=
by simp

/-- `monomial s a` is the monomial `a * X^s` -/
def monomial (n : ℕ) : R →ₗ[R] polynomial R := finsupp.lsingle n

@[simp]
lemma monomial_zero_right (n : ℕ) :
  monomial n (0 : R) = 0 :=
finsupp.single_zero

-- This is not a `simp` lemma as `monomial_zero_left` is more general.
lemma monomial_zero_one : monomial 0 (1 : R) = 1 := rfl

lemma monomial_def (n : ℕ) (a : R) : monomial n a = finsupp.single n a := rfl

lemma monomial_add (n : ℕ) (r s : R) :
  monomial n (r + s) = monomial n r + monomial n s :=
finsupp.single_add

lemma monomial_mul_monomial (n m : ℕ) (r s : R) :
  monomial n r * monomial m s = monomial (n + m) (r * s) :=
add_monoid_algebra.single_mul_single

@[simp]
lemma monomial_pow (n : ℕ) (r : R) (k : ℕ) :
  (monomial n r)^k = monomial (n*k) (r^k) :=
begin
  rw mul_comm,
  exact add_monoid_algebra.single_pow k,
end

lemma smul_monomial {S} [semiring S] [module S R] (a : S) (n : ℕ) (b : R) :
  a • monomial n b = monomial n (a • b) :=
finsupp.smul_single _ _ _

lemma support_add : (p + q).support ⊆ p.support ∪ q.support := support_add

/-- `X` is the polynomial variable (aka indeterminant). -/
def X : polynomial R := monomial 1 1

lemma monomial_one_one_eq_X : monomial 1 (1 : R) = X := rfl
lemma monomial_one_right_eq_X_pow (n : ℕ) : monomial n 1 = X^n :=
begin
  induction n with n ih,
  { simp [monomial_zero_one], },
  { rw [pow_succ, ←ih, ←monomial_one_one_eq_X, monomial_mul_monomial, add_comm, one_mul], }
end

/-- `X` commutes with everything, even when the coefficients are noncommutative. -/
lemma X_mul : X * p = p * X :=
by { ext, simp [X, monomial, add_monoid_algebra.mul_apply, sum_single_index, add_comm] }

lemma X_pow_mul {n : ℕ} : X^n * p = p * X^n :=
begin
  induction n with n ih,
  { simp, },
  { conv_lhs { rw pow_succ', },
    rw [mul_assoc, X_mul, ←mul_assoc, ih, mul_assoc, ←pow_succ'], }
end

lemma X_pow_mul_assoc {n : ℕ} : (p * X^n) * q = (p * q) * X^n :=
by rw [mul_assoc, X_pow_mul, ←mul_assoc]

lemma commute_X (p : polynomial R) : commute X p := X_mul

@[simp]
lemma monomial_mul_X (n : ℕ) (r : R) : monomial n r * X = monomial (n+1) r :=
by erw [monomial_mul_monomial, mul_one]

@[simp]
lemma monomial_mul_X_pow (n : ℕ) (r : R) (k : ℕ) : monomial n r * X^k = monomial (n+k) r :=
begin
  induction k with k ih,
  { simp, },
  { simp [ih, pow_succ', ←mul_assoc, add_assoc], },
end

@[simp]
lemma X_mul_monomial (n : ℕ) (r : R) : X * monomial n r = monomial (n+1) r :=
by rw [X_mul, monomial_mul_X]

@[simp]
lemma X_pow_mul_monomial (k n : ℕ) (r : R) : X^k * monomial n r = monomial (n+k) r :=
by rw [X_pow_mul, monomial_mul_X_pow]

/-- coeff p n is the coefficient of X^n in p -/
def coeff (p : polynomial R) : ℕ → R := @coe_fn (ℕ →₀ R) _ p

@[simp] lemma coeff_mk (s) (f) (h) : coeff (finsupp.mk s f h : polynomial R) = f := rfl

lemma coeff_monomial : coeff (monomial n a) m = if n = m then a else 0 :=
finsupp.single_apply

@[simp] lemma coeff_zero (n : ℕ) : coeff (0 : polynomial R) n = 0 := rfl

@[simp] lemma coeff_one_zero : coeff (1 : polynomial R) 0 = 1 := coeff_monomial

@[simp] lemma coeff_X_one : coeff (X : polynomial R) 1 = 1 := coeff_monomial

@[simp] lemma coeff_X_zero : coeff (X : polynomial R) 0 = 0 := coeff_monomial

@[simp] lemma coeff_monomial_succ : coeff (monomial (n+1) a) 0 = 0 :=
by simp [coeff_monomial]

lemma coeff_X : coeff (X : polynomial R) n = if 1 = n then 1 else 0 := coeff_monomial

lemma coeff_X_of_ne_one {n : ℕ} (hn : n ≠ 1) : coeff (X : polynomial R) n = 0 :=
by rw [coeff_X, if_neg hn.symm]

theorem ext_iff {p q : polynomial R} : p = q ↔ ∀ n, coeff p n = coeff q n :=
finsupp.ext_iff

@[ext] lemma ext {p q : polynomial R} : (∀ n, coeff p n = coeff q n) → p = q :=
finsupp.ext

@[ext] lemma add_hom_ext' {M : Type*} [add_monoid M] {f g : polynomial R →+ M}
  (h : ∀ n, f.comp (monomial n).to_add_monoid_hom = g.comp (monomial n).to_add_monoid_hom) :
  f = g :=
finsupp.add_hom_ext' h

lemma add_hom_ext {M : Type*} [add_monoid M] {f g : polynomial R →+ M}
  (h : ∀ n a, f (monomial n a) = g (monomial n a)) :
  f = g :=
finsupp.add_hom_ext h

@[ext] lemma lhom_ext' {M : Type*} [add_comm_monoid M] [module R M] {f g : polynomial R →ₗ[R] M}
  (h : ∀ n, f.comp (monomial n) = g.comp (monomial n)) :
  f = g :=
finsupp.lhom_ext' h

-- this has the same content as the subsingleton
lemma eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : polynomial R) : p = 0 :=
by rw [←one_smul R p, ←h, zero_smul]

lemma support_monomial (n) (a : R) (H : a ≠ 0) : (monomial n a).support = singleton n :=
finsupp.support_single_ne_zero H

lemma support_monomial' (n) (a : R) : (monomial n a).support ⊆ singleton n :=
finsupp.support_single_subset

lemma X_pow_eq_monomial (n) : X ^ n = monomial n (1:R) :=
begin
  induction n with n hn,
  { refl, },
  { rw [pow_succ', hn, X, monomial_mul_monomial, one_mul] },
end

lemma support_X_pow (H : ¬ (1:R) = 0) (n : ℕ) : (X^n : polynomial R).support = singleton n :=
begin
  convert support_monomial n 1 H,
  exact X_pow_eq_monomial n,
end

lemma support_X_empty (H : (1:R)=0) : (X : polynomial R).support = ∅ :=
begin
  rw [X, H, monomial_zero_right, support_zero],
end

lemma support_X (H : ¬ (1 : R) = 0) : (X : polynomial R).support = singleton 1 :=
begin
  rw [← pow_one X, support_X_pow H 1],
end

lemma monomial_left_inj {R : Type*} [semiring R] {a : R} (ha : a ≠ 0) {i j : ℕ} :
  (monomial i a) = (monomial j a) ↔ i = j :=
finsupp.single_left_inj ha

lemma nat_cast_mul {R : Type*} [semiring R] (n : ℕ) (p : polynomial R) :
  (n : polynomial R) * p = n • p :=
(nsmul_eq_mul _ _).symm

end semiring

section comm_semiring
variables [comm_semiring R]

instance : comm_semiring (polynomial R) := add_monoid_algebra.comm_semiring

end comm_semiring

section ring
variables [ring R]

instance : ring (polynomial R) := add_monoid_algebra.ring

@[simp] lemma coeff_neg (p : polynomial R) (n : ℕ) : coeff (-p) n = -coeff p n := rfl

@[simp]
lemma coeff_sub (p q : polynomial R) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n := rfl

@[simp] lemma monomial_neg (n : ℕ) (a : R) : monomial n (-a) = -(monomial n a) :=
by rw [eq_neg_iff_add_eq_zero, ←monomial_add, neg_add_self, monomial_zero_right]

@[simp] lemma support_neg {p : polynomial R} : (-p).support = p.support :=
by simp [support]

end ring

instance [comm_ring R] : comm_ring (polynomial R) := add_monoid_algebra.comm_ring

section nonzero_semiring

variables [semiring R] [nontrivial R]
instance : nontrivial (polynomial R) := add_monoid_algebra.nontrivial

lemma X_ne_zero : (X : polynomial R) ≠ 0 :=
mt (congr_arg (λ p, coeff p 1)) (by simp)

end nonzero_semiring

section repr
variables [semiring R]
local attribute [instance, priority 100] classical.prop_decidable

instance [has_repr R] : has_repr (polynomial R) :=
⟨λ p, if p = 0 then "0"
  else (p.support.sort (≤)).foldr
    (λ n a, a ++ (if a = "" then "" else " + ") ++
      if n = 0
        then "C (" ++ repr (coeff p n) ++ ")"
        else if n = 1
          then if (coeff p n) = 1 then "X" else "C (" ++ repr (coeff p n) ++ ") * X"
          else if (coeff p n) = 1 then "X ^ " ++ repr n
            else "C (" ++ repr (coeff p n) ++ ") * X ^ " ++ repr n) ""⟩

end repr

end polynomial
