/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import data.matrix.block
import data.matrix.notation
import linear_algebra.std_basis
import ring_theory.algebra_tower
import algebra.module.algebra
import algebra.algebra.subalgebra.tower

/-!
# Linear maps and matrices

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the maps to send matrices to a linear map,
and to send linear maps between modules with a finite bases
to matrices. This defines a linear equivalence between linear maps
between finite-dimensional vector spaces and matrices indexed by
the respective bases.

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

 * `linear_map.to_matrix`: given bases `v₁ : ι → M₁` and `v₂ : κ → M₂`,
   the `R`-linear equivalence from `M₁ →ₗ[R] M₂` to `matrix κ ι R`
 * `matrix.to_lin`: the inverse of `linear_map.to_matrix`
 * `linear_map.to_matrix'`: the `R`-linear equivalence from `(m → R) →ₗ[R] (n → R)`
   to `matrix m n R` (with the standard basis on `m → R` and `n → R`)
 * `matrix.to_lin'`: the inverse of `linear_map.to_matrix'`
 * `alg_equiv_matrix`: given a basis indexed by `n`, the `R`-algebra equivalence between
   `R`-endomorphisms of `M` and `matrix n n R`

## Issues

This file was originally written without attention to non-commutative rings,
and so mostly only works in the commutative setting. This should be fixed.

In particular, `matrix.mul_vec` gives us a linear equivalence
`matrix m n R ≃ₗ[R] (n → R) →ₗ[Rᵐᵒᵖ] (m → R)`
while `matrix.vec_mul` gives us a linear equivalence
`matrix m n R ≃ₗ[Rᵐᵒᵖ] (m → R) →ₗ[R] (n → R)`.
At present, the first equivalence is developed in detail but only for commutative rings
(and we omit the distinction between `Rᵐᵒᵖ` and `R`),
while the second equivalence is developed only in brief, but for not-necessarily-commutative rings.

Naming is slightly inconsistent between the two developments.
In the original (commutative) development `linear` is abbreviated to `lin`,
although this is not consistent with the rest of mathlib.
In the new (non-commutative) development `linear` is not abbreviated, and declarations use `_right`
to indicate they use the right action of matrices on vectors (via `matrix.vec_mul`).
When the two developments are made uniform, the names should be made uniform, too,
by choosing between `linear` and `lin` consistently,
and (presumably) adding `_left` where necessary.

## Tags

linear_map, matrix, linear_equiv, diagonal, det, trace
-/

noncomputable theory

open linear_map matrix set submodule
open_locale big_operators
open_locale matrix

universes u v w

instance {n m} [fintype m] [decidable_eq m] [fintype n] [decidable_eq n] (R) [fintype R] :
  fintype (matrix m n R) := by unfold matrix; apply_instance

section to_matrix_right

variables {R : Type*} [semiring R]
variables {l m n : Type*}

/-- `matrix.vec_mul M` is a linear map. -/
@[simps] def matrix.vec_mul_linear [fintype m] (M : matrix m n R) : (m → R) →ₗ[R] (n → R) :=
{ to_fun := λ x, M.vec_mul x,
  map_add' := λ v w, funext (λ i, add_dot_product _ _ _),
  map_smul' := λ c v, funext (λ i, smul_dot_product _ _ _) }

variables [fintype m] [decidable_eq m]

@[simp] lemma matrix.vec_mul_std_basis (M : matrix m n R) (i j) :
  M.vec_mul (std_basis R (λ _, R) i 1) j = M i j :=
begin
  have : (∑ i', (if i = i' then 1 else 0) * M i' j) = M i j,
  { simp_rw [boole_mul, finset.sum_ite_eq, finset.mem_univ, if_true] },
  convert this,
  ext,
  split_ifs with h; simp only [std_basis_apply],
  { rw [h, function.update_same] },
  { rw [function.update_noteq (ne.symm h), pi.zero_apply] }
end

/--
Linear maps `(m → R) →ₗ[R] (n → R)` are linearly equivalent over `Rᵐᵒᵖ` to `matrix m n R`,
by having matrices act by right multiplication.
 -/
def linear_map.to_matrix_right' : ((m → R) →ₗ[R] (n → R)) ≃ₗ[Rᵐᵒᵖ] matrix m n R :=
{ to_fun := λ f i j, f (std_basis R (λ _, R) i 1) j,
  inv_fun := matrix.vec_mul_linear,
  right_inv := λ M, by
  { ext i j, simp only [matrix.vec_mul_std_basis, matrix.vec_mul_linear_apply] },
  left_inv := λ f, begin
    apply (pi.basis_fun R m).ext,
    intro j, ext i,
    simp only [pi.basis_fun_apply, matrix.vec_mul_std_basis, matrix.vec_mul_linear_apply]
  end,
  map_add' := λ f g, by { ext i j, simp only [pi.add_apply, linear_map.add_apply] },
  map_smul' := λ c f, by { ext i j, simp only [pi.smul_apply, linear_map.smul_apply,
                                               ring_hom.id_apply] } }

/-- A `matrix m n R` is linearly equivalent over `Rᵐᵒᵖ` to a linear map `(m → R) →ₗ[R] (n → R)`,
by having matrices act by right multiplication. -/
abbreviation matrix.to_linear_map_right' : matrix m n R ≃ₗ[Rᵐᵒᵖ] ((m → R) →ₗ[R] (n → R)) :=
linear_map.to_matrix_right'.symm

@[simp] lemma matrix.to_linear_map_right'_apply (M : matrix m n R) (v : m → R) :
  matrix.to_linear_map_right' M v = M.vec_mul v := rfl

@[simp] lemma matrix.to_linear_map_right'_mul [fintype l] [decidable_eq l] (M : matrix l m R)
  (N : matrix m n R) : matrix.to_linear_map_right' (M ⬝ N) =
  (matrix.to_linear_map_right' N).comp (matrix.to_linear_map_right' M) :=
linear_map.ext $ λ x, (vec_mul_vec_mul _ M N).symm

lemma matrix.to_linear_map_right'_mul_apply [fintype l] [decidable_eq l] (M : matrix l m R)
  (N : matrix m n R) (x) : matrix.to_linear_map_right' (M ⬝ N) x =
    (matrix.to_linear_map_right' N (matrix.to_linear_map_right' M x)) :=
(vec_mul_vec_mul _ M N).symm

@[simp] lemma matrix.to_linear_map_right'_one :
  matrix.to_linear_map_right' (1 : matrix m m R) = id :=
by { ext, simp [linear_map.one_apply, std_basis_apply] }

/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `n → A`
and `m → A` corresponding to `M.vec_mul` and `M'.vec_mul`. -/
@[simps]
def matrix.to_linear_equiv_right'_of_inv [fintype n] [decidable_eq n]
  {M : matrix m n R} {M' : matrix n m R}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  (n → R) ≃ₗ[R] (m → R) :=
{ to_fun := M'.to_linear_map_right',
  inv_fun := M.to_linear_map_right',
  left_inv := λ x, by
    rw [← matrix.to_linear_map_right'_mul_apply, hM'M, matrix.to_linear_map_right'_one, id_apply],
  right_inv := λ x, by
    rw [← matrix.to_linear_map_right'_mul_apply, hMM', matrix.to_linear_map_right'_one, id_apply],
  ..linear_map.to_matrix_right'.symm M' }

end to_matrix_right

/-!
From this point on, we only work with commutative rings,
and fail to distinguish between `Rᵐᵒᵖ` and `R`.
This should eventually be remedied.
-/

section to_matrix'

variables {R : Type*} [comm_semiring R]
variables {l m n : Type*}

/-- `matrix.mul_vec M` is a linear map. -/
@[simps] def matrix.mul_vec_lin [fintype n] (M : matrix m n R) : (n → R) →ₗ[R] (m → R) :=
{ to_fun := M.mul_vec,
  map_add' := λ v w, funext (λ i, dot_product_add _ _ _),
  map_smul' := λ c v, funext (λ i, dot_product_smul _ _ _) }

variables [fintype n] [decidable_eq n]

lemma matrix.mul_vec_std_basis (M : matrix m n R) (i j) :
  M.mul_vec (std_basis R (λ _, R) j 1) i = M i j :=
(congr_fun (matrix.mul_vec_single _ _ (1 : R)) i).trans $ mul_one _

@[simp] lemma matrix.mul_vec_std_basis_apply (M : matrix m n R) (j) :
  M.mul_vec (std_basis R (λ _, R) j 1) = Mᵀ j :=
funext $ λ i, matrix.mul_vec_std_basis M i j

/-- Linear maps `(n → R) →ₗ[R] (m → R)` are linearly equivalent to `matrix m n R`. -/
def linear_map.to_matrix' : ((n → R) →ₗ[R] (m → R)) ≃ₗ[R] matrix m n R :=
{ to_fun := λ f, of (λ i j, f (std_basis R (λ _, R) j 1) i),
  inv_fun := matrix.mul_vec_lin,
  right_inv := λ M, by { ext i j, simp only [matrix.mul_vec_std_basis, matrix.mul_vec_lin_apply,
                                             of_apply] },
  left_inv := λ f, begin
    apply (pi.basis_fun R n).ext,
    intro j, ext i,
    simp only [pi.basis_fun_apply, matrix.mul_vec_std_basis, matrix.mul_vec_lin_apply,
      of_apply]
  end,
  map_add' := λ f g, by { ext i j, simp only [pi.add_apply, linear_map.add_apply, of_apply] },
  map_smul' := λ c f, by { ext i j, simp only [pi.smul_apply, linear_map.smul_apply,
                                               ring_hom.id_apply, of_apply] } }

/-- A `matrix m n R` is linearly equivalent to a linear map `(n → R) →ₗ[R] (m → R)`. -/
def matrix.to_lin' : matrix m n R ≃ₗ[R] ((n → R) →ₗ[R] (m → R)) :=
linear_map.to_matrix'.symm

@[simp] lemma linear_map.to_matrix'_symm :
  (linear_map.to_matrix'.symm : matrix m n R ≃ₗ[R] _) = matrix.to_lin' :=
rfl

@[simp] lemma matrix.to_lin'_symm :
  (matrix.to_lin'.symm : ((n → R) →ₗ[R] (m → R)) ≃ₗ[R] _) = linear_map.to_matrix' :=
rfl

@[simp] lemma linear_map.to_matrix'_to_lin' (M : matrix m n R) :
  linear_map.to_matrix' (matrix.to_lin' M) = M :=
linear_map.to_matrix'.apply_symm_apply M

@[simp] lemma matrix.to_lin'_to_matrix' (f : (n → R) →ₗ[R] (m → R)) :
  matrix.to_lin' (linear_map.to_matrix' f) = f :=
matrix.to_lin'.apply_symm_apply f

@[simp] lemma linear_map.to_matrix'_apply (f : (n → R) →ₗ[R] (m → R)) (i j) :
  linear_map.to_matrix' f i j = f (λ j', if j' = j then 1 else 0) i :=
begin
  simp only [linear_map.to_matrix', linear_equiv.coe_mk, of_apply],
  congr,
  ext j',
  split_ifs with h,
  { rw [h, std_basis_same] },
  apply std_basis_ne _ _ _ _ h
end

@[simp] lemma matrix.to_lin'_apply (M : matrix m n R) (v : n → R) :
  matrix.to_lin' M v = M.mul_vec v := rfl

@[simp] lemma matrix.to_lin'_one :
  matrix.to_lin' (1 : matrix n n R) = id :=
by { ext, simp [linear_map.one_apply, std_basis_apply] }

@[simp] lemma linear_map.to_matrix'_id :
  (linear_map.to_matrix' (linear_map.id : (n → R) →ₗ[R] (n → R))) = 1 :=
by { ext, rw [matrix.one_apply, linear_map.to_matrix'_apply, id_apply] }

@[simp] lemma matrix.to_lin'_mul [fintype m] [decidable_eq m] (M : matrix l m R)
  (N : matrix m n R) : matrix.to_lin' (M ⬝ N) = (matrix.to_lin' M).comp (matrix.to_lin' N) :=
linear_map.ext $ λ x, (mul_vec_mul_vec _ _ _).symm

/-- Shortcut lemma for `matrix.to_lin'_mul` and `linear_map.comp_apply` -/
lemma matrix.to_lin'_mul_apply [fintype m] [decidable_eq m] (M : matrix l m R)
  (N : matrix m n R) (x) : matrix.to_lin' (M ⬝ N) x = (matrix.to_lin' M (matrix.to_lin' N x)) :=
by rw [matrix.to_lin'_mul, linear_map.comp_apply]

lemma linear_map.to_matrix'_comp [fintype l] [decidable_eq l]
  (f : (n → R) →ₗ[R] (m → R)) (g : (l → R) →ₗ[R] (n → R)) :
  (f.comp g).to_matrix' = f.to_matrix' ⬝ g.to_matrix' :=
suffices (f.comp g) = (f.to_matrix' ⬝ g.to_matrix').to_lin',
  by rw [this, linear_map.to_matrix'_to_lin'],
by rw [matrix.to_lin'_mul, matrix.to_lin'_to_matrix', matrix.to_lin'_to_matrix']

lemma linear_map.to_matrix'_mul [fintype m] [decidable_eq m]
  (f g : (m → R) →ₗ[R] (m → R)) :
  (f * g).to_matrix' = f.to_matrix' ⬝ g.to_matrix' :=
linear_map.to_matrix'_comp f g

@[simp] lemma linear_map.to_matrix'_algebra_map (x : R) :
  linear_map.to_matrix' (algebra_map R (module.End R (n → R)) x) = scalar n x :=
by simp [module.algebra_map_End_eq_smul_id]

lemma matrix.ker_to_lin'_eq_bot_iff {M : matrix n n R} :
  M.to_lin'.ker = ⊥ ↔ ∀ v, M.mul_vec v = 0 → v = 0 :=
by simp only [submodule.eq_bot_iff, linear_map.mem_ker, matrix.to_lin'_apply]

lemma matrix.range_to_lin' (M : matrix m n R) : M.to_lin'.range = span R (range Mᵀ) :=
by simp_rw [range_eq_map, ←supr_range_std_basis, submodule.map_supr, range_eq_map,
  ←ideal.span_singleton_one, ideal.span, submodule.map_span, image_image, image_singleton,
  matrix.to_lin'_apply, M.mul_vec_std_basis_apply, supr_span, range_eq_Union]

/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `m → A`
and `n → A` corresponding to `M.mul_vec` and `M'.mul_vec`. -/
@[simps]
def matrix.to_lin'_of_inv [fintype m] [decidable_eq m]
  {M : matrix m n R} {M' : matrix n m R}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  (m → R) ≃ₗ[R] (n → R) :=
{ to_fun := matrix.to_lin' M',
  inv_fun := M.to_lin',
  left_inv := λ x, by rw [← matrix.to_lin'_mul_apply, hMM', matrix.to_lin'_one, id_apply],
  right_inv := λ x, by rw [← matrix.to_lin'_mul_apply, hM'M, matrix.to_lin'_one, id_apply],
  .. matrix.to_lin' M' }

/-- Linear maps `(n → R) →ₗ[R] (n → R)` are algebra equivalent to `matrix n n R`. -/
def linear_map.to_matrix_alg_equiv' : ((n → R) →ₗ[R] (n → R)) ≃ₐ[R] matrix n n R :=
alg_equiv.of_linear_equiv linear_map.to_matrix' linear_map.to_matrix'_mul
  linear_map.to_matrix'_algebra_map

/-- A `matrix n n R` is algebra equivalent to a linear map `(n → R) →ₗ[R] (n → R)`. -/
def matrix.to_lin_alg_equiv' : matrix n n R ≃ₐ[R] ((n → R) →ₗ[R] (n → R)) :=
linear_map.to_matrix_alg_equiv'.symm

@[simp] lemma linear_map.to_matrix_alg_equiv'_symm :
  (linear_map.to_matrix_alg_equiv'.symm : matrix n n R ≃ₐ[R] _) = matrix.to_lin_alg_equiv' :=
rfl

@[simp] lemma matrix.to_lin_alg_equiv'_symm :
  (matrix.to_lin_alg_equiv'.symm : ((n → R) →ₗ[R] (n → R)) ≃ₐ[R] _) =
    linear_map.to_matrix_alg_equiv' :=
rfl

@[simp] lemma linear_map.to_matrix_alg_equiv'_to_lin_alg_equiv' (M : matrix n n R) :
  linear_map.to_matrix_alg_equiv' (matrix.to_lin_alg_equiv' M) = M :=
linear_map.to_matrix_alg_equiv'.apply_symm_apply M

@[simp] lemma matrix.to_lin_alg_equiv'_to_matrix_alg_equiv' (f : (n → R) →ₗ[R] (n → R)) :
  matrix.to_lin_alg_equiv' (linear_map.to_matrix_alg_equiv' f) = f :=
matrix.to_lin_alg_equiv'.apply_symm_apply f

@[simp] lemma linear_map.to_matrix_alg_equiv'_apply (f : (n → R) →ₗ[R] (n → R)) (i j) :
  linear_map.to_matrix_alg_equiv' f i j = f (λ j', if j' = j then 1 else 0) i :=
by simp [linear_map.to_matrix_alg_equiv']

@[simp] lemma matrix.to_lin_alg_equiv'_apply (M : matrix n n R) (v : n → R) :
  matrix.to_lin_alg_equiv' M v = M.mul_vec v := rfl

@[simp] lemma matrix.to_lin_alg_equiv'_one :
  matrix.to_lin_alg_equiv' (1 : matrix n n R) = id :=
matrix.to_lin'_one

@[simp] lemma linear_map.to_matrix_alg_equiv'_id :
  (linear_map.to_matrix_alg_equiv' (linear_map.id : (n → R) →ₗ[R] (n → R))) = 1 :=
linear_map.to_matrix'_id

@[simp] lemma matrix.to_lin_alg_equiv'_mul (M N : matrix n n R) :
  matrix.to_lin_alg_equiv' (M ⬝ N) =
    (matrix.to_lin_alg_equiv' M).comp (matrix.to_lin_alg_equiv' N) :=
matrix.to_lin'_mul _ _

lemma linear_map.to_matrix_alg_equiv'_comp (f g : (n → R) →ₗ[R] (n → R)) :
  (f.comp g).to_matrix_alg_equiv' = f.to_matrix_alg_equiv' ⬝ g.to_matrix_alg_equiv' :=
linear_map.to_matrix'_comp _ _

lemma linear_map.to_matrix_alg_equiv'_mul
  (f g : (n → R) →ₗ[R] (n → R)) :
  (f * g).to_matrix_alg_equiv' = f.to_matrix_alg_equiv' ⬝ g.to_matrix_alg_equiv' :=
linear_map.to_matrix_alg_equiv'_comp f g

end to_matrix'

section to_matrix

variables {R : Type*} [comm_semiring R]
variables {l m n : Type*} [fintype n] [fintype m] [decidable_eq n]
variables {M₁ M₂ : Type*} [add_comm_monoid M₁] [add_comm_monoid M₂] [module R M₁] [module R M₂]
variables (v₁ : basis n R M₁) (v₂ : basis m R M₂)

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between linear maps `M₁ →ₗ M₂` and matrices over `R` indexed by the bases. -/
def linear_map.to_matrix : (M₁ →ₗ[R] M₂) ≃ₗ[R] matrix m n R :=
linear_equiv.trans (linear_equiv.arrow_congr v₁.equiv_fun v₂.equiv_fun) linear_map.to_matrix'

/-- `linear_map.to_matrix'` is a particular case of `linear_map.to_matrix`, for the standard basis
`pi.basis_fun R n`. -/
lemma linear_map.to_matrix_eq_to_matrix' :
  linear_map.to_matrix (pi.basis_fun R n) (pi.basis_fun R n) = linear_map.to_matrix' :=
rfl

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between matrices over `R` indexed by the bases and linear maps `M₁ →ₗ M₂`. -/
def matrix.to_lin : matrix m n R ≃ₗ[R] (M₁ →ₗ[R] M₂) :=
(linear_map.to_matrix v₁ v₂).symm

/-- `matrix.to_lin'` is a particular case of `matrix.to_lin`, for the standard basis
`pi.basis_fun R n`. -/
lemma matrix.to_lin_eq_to_lin' :
  matrix.to_lin (pi.basis_fun R n) (pi.basis_fun R m) = matrix.to_lin' :=
rfl

@[simp] lemma linear_map.to_matrix_symm :
  (linear_map.to_matrix v₁ v₂).symm = matrix.to_lin v₁ v₂ :=
rfl

@[simp] lemma matrix.to_lin_symm :
  (matrix.to_lin v₁ v₂).symm = linear_map.to_matrix v₁ v₂ :=
rfl

@[simp] lemma matrix.to_lin_to_matrix (f : M₁ →ₗ[R] M₂) :
  matrix.to_lin v₁ v₂ (linear_map.to_matrix v₁ v₂ f) = f :=
by rw [← matrix.to_lin_symm, linear_equiv.apply_symm_apply]

@[simp] lemma linear_map.to_matrix_to_lin (M : matrix m n R) :
  linear_map.to_matrix v₁ v₂ (matrix.to_lin v₁ v₂ M) = M :=
by rw [← matrix.to_lin_symm, linear_equiv.symm_apply_apply]

lemma linear_map.to_matrix_apply (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
  linear_map.to_matrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i :=
begin
  rw [linear_map.to_matrix, linear_equiv.trans_apply, linear_map.to_matrix'_apply,
      linear_equiv.arrow_congr_apply, basis.equiv_fun_symm_apply, finset.sum_eq_single j,
      if_pos rfl, one_smul, basis.equiv_fun_apply],
  { intros j' _ hj',
    rw [if_neg hj', zero_smul] },
  { intro hj,
    have := finset.mem_univ j,
    contradiction }
end

lemma linear_map.to_matrix_transpose_apply (f : M₁ →ₗ[R] M₂) (j : n) :
  (linear_map.to_matrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
funext $ λ i, f.to_matrix_apply _ _ i j

lemma linear_map.to_matrix_apply' (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
  linear_map.to_matrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i :=
linear_map.to_matrix_apply v₁ v₂ f i j

lemma linear_map.to_matrix_transpose_apply' (f : M₁ →ₗ[R] M₂) (j : n) :
  (linear_map.to_matrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
linear_map.to_matrix_transpose_apply v₁ v₂ f j

lemma matrix.to_lin_apply (M : matrix m n R) (v : M₁) :
  matrix.to_lin v₁ v₂ M v = ∑ j, M.mul_vec (v₁.repr v) j • v₂ j :=
show v₂.equiv_fun.symm (matrix.to_lin' M (v₁.repr v)) = _,
by rw [matrix.to_lin'_apply, v₂.equiv_fun_symm_apply]

@[simp] lemma matrix.to_lin_self (M : matrix m n R) (i : n) :
  matrix.to_lin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j :=
begin
  rw [matrix.to_lin_apply, finset.sum_congr rfl (λ j hj, _)],
  rw [basis.repr_self, matrix.mul_vec, dot_product, finset.sum_eq_single i,
      finsupp.single_eq_same, mul_one],
  { intros i' _ i'_ne, rw [finsupp.single_eq_of_ne i'_ne.symm, mul_zero] },
  { intros,
    have := finset.mem_univ i,
    contradiction },
end

/-- This will be a special case of `linear_map.to_matrix_id_eq_basis_to_matrix`. -/
lemma linear_map.to_matrix_id : linear_map.to_matrix v₁ v₁ id = 1 :=
begin
  ext i j,
  simp [linear_map.to_matrix_apply, matrix.one_apply, finsupp.single_apply, eq_comm]
end

lemma linear_map.to_matrix_one : linear_map.to_matrix v₁ v₁ 1 = 1 :=
linear_map.to_matrix_id v₁

@[simp]
lemma matrix.to_lin_one : matrix.to_lin v₁ v₁ 1 = id :=
by rw [← linear_map.to_matrix_id v₁, matrix.to_lin_to_matrix]

theorem linear_map.to_matrix_reindex_range [decidable_eq M₁] [decidable_eq M₂]
  (f : M₁ →ₗ[R] M₂) (k : m) (i : n) :
  linear_map.to_matrix v₁.reindex_range v₂.reindex_range f
      ⟨v₂ k, mem_range_self k⟩ ⟨v₁ i, mem_range_self i⟩ =
    linear_map.to_matrix v₁ v₂ f k i :=
by simp_rw [linear_map.to_matrix_apply, basis.reindex_range_self, basis.reindex_range_repr]

variables {M₃ : Type*} [add_comm_monoid M₃] [module R M₃] (v₃ : basis l R M₃)

lemma linear_map.to_matrix_comp [fintype l] [decidable_eq m] (f : M₂ →ₗ[R] M₃) (g : M₁ →ₗ[R] M₂) :
  linear_map.to_matrix v₁ v₃ (f.comp g) =
  linear_map.to_matrix v₂ v₃ f ⬝ linear_map.to_matrix v₁ v₂ g :=
by simp_rw [linear_map.to_matrix, linear_equiv.trans_apply,
            linear_equiv.arrow_congr_comp _ v₂.equiv_fun, linear_map.to_matrix'_comp]

lemma linear_map.to_matrix_mul (f g : M₁ →ₗ[R] M₁) :
  linear_map.to_matrix v₁ v₁ (f * g) =
    linear_map.to_matrix v₁ v₁ f ⬝ linear_map.to_matrix v₁ v₁ g :=
by { rw [show (@has_mul.mul (M₁ →ₗ[R] M₁) _) = linear_map.comp, from rfl,
         linear_map.to_matrix_comp v₁ v₁ v₁ f g] }

@[simp] lemma linear_map.to_matrix_algebra_map (x : R) :
  linear_map.to_matrix v₁ v₁ (algebra_map R (module.End R M₁) x) = scalar n x :=
by simp [module.algebra_map_End_eq_smul_id, linear_map.to_matrix_id]

lemma linear_map.to_matrix_mul_vec_repr (f : M₁ →ₗ[R] M₂) (x : M₁) :
  (linear_map.to_matrix v₁ v₂ f).mul_vec (v₁.repr x) = v₂.repr (f x) :=
by { ext i,
     rw [← matrix.to_lin'_apply, linear_map.to_matrix, linear_equiv.trans_apply,
         matrix.to_lin'_to_matrix', linear_equiv.arrow_congr_apply, v₂.equiv_fun_apply],
     congr,
     exact v₁.equiv_fun.symm_apply_apply x }

@[simp] lemma linear_map.to_matrix_basis_equiv [fintype l] [decidable_eq l]
  (b : basis l R M₁) (b' : basis l R M₂) :
  linear_map.to_matrix b' b (b'.equiv b (equiv.refl l) : M₂ →ₗ[R] M₁) = 1 :=
begin
  ext i j,
  simp [linear_map.to_matrix_apply, matrix.one_apply, finsupp.single_apply, eq_comm],
end

lemma matrix.to_lin_mul [fintype l] [decidable_eq m] (A : matrix l m R) (B : matrix m n R) :
  matrix.to_lin v₁ v₃ (A ⬝ B) =
  (matrix.to_lin v₂ v₃ A).comp (matrix.to_lin v₁ v₂ B) :=
begin
  apply (linear_map.to_matrix v₁ v₃).injective,
  haveI : decidable_eq l := λ _ _, classical.prop_decidable _,
  rw linear_map.to_matrix_comp v₁ v₂ v₃,
  repeat { rw linear_map.to_matrix_to_lin },
end

/-- Shortcut lemma for `matrix.to_lin_mul` and `linear_map.comp_apply`. -/
lemma matrix.to_lin_mul_apply [fintype l] [decidable_eq m]
  (A : matrix l m R) (B : matrix m n R) (x) :
  matrix.to_lin v₁ v₃ (A ⬝ B) x =
    (matrix.to_lin v₂ v₃ A) (matrix.to_lin v₁ v₂ B x) :=
by rw [matrix.to_lin_mul v₁ v₂, linear_map.comp_apply]

/-- If `M` and `M` are each other's inverse matrices, `matrix.to_lin M` and `matrix.to_lin M'`
form a linear equivalence. -/
@[simps]
def matrix.to_lin_of_inv [decidable_eq m]
  {M : matrix m n R} {M' : matrix n m R}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  M₁ ≃ₗ[R] M₂ :=
{ to_fun := matrix.to_lin v₁ v₂ M,
  inv_fun := matrix.to_lin v₂ v₁ M',
  left_inv := λ x, by rw [← matrix.to_lin_mul_apply, hM'M, matrix.to_lin_one, id_apply],
  right_inv := λ x, by rw [← matrix.to_lin_mul_apply, hMM', matrix.to_lin_one, id_apply],
  .. matrix.to_lin v₁ v₂ M }

/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between linear maps `M₁ →ₗ M₁` and square matrices over `R` indexed by the basis. -/
def linear_map.to_matrix_alg_equiv :
  (M₁ →ₗ[R] M₁) ≃ₐ[R] matrix n n R :=
alg_equiv.of_linear_equiv (linear_map.to_matrix v₁ v₁) (linear_map.to_matrix_mul v₁)
  (linear_map.to_matrix_algebra_map v₁)

/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between square matrices over `R` indexed by the basis and linear maps `M₁ →ₗ M₁`. -/
def matrix.to_lin_alg_equiv : matrix n n R ≃ₐ[R] (M₁ →ₗ[R] M₁) :=
(linear_map.to_matrix_alg_equiv v₁).symm

@[simp] lemma linear_map.to_matrix_alg_equiv_symm :
  (linear_map.to_matrix_alg_equiv v₁).symm = matrix.to_lin_alg_equiv v₁ :=
rfl

@[simp] lemma matrix.to_lin_alg_equiv_symm :
  (matrix.to_lin_alg_equiv v₁).symm = linear_map.to_matrix_alg_equiv v₁ :=
rfl

@[simp] lemma matrix.to_lin_alg_equiv_to_matrix_alg_equiv (f : M₁ →ₗ[R] M₁) :
  matrix.to_lin_alg_equiv v₁ (linear_map.to_matrix_alg_equiv v₁ f) = f :=
by rw [← matrix.to_lin_alg_equiv_symm, alg_equiv.apply_symm_apply]

@[simp] lemma linear_map.to_matrix_alg_equiv_to_lin_alg_equiv (M : matrix n n R) :
  linear_map.to_matrix_alg_equiv v₁ (matrix.to_lin_alg_equiv v₁ M) = M :=
by rw [← matrix.to_lin_alg_equiv_symm, alg_equiv.symm_apply_apply]

lemma linear_map.to_matrix_alg_equiv_apply (f : M₁ →ₗ[R] M₁) (i j : n) :
  linear_map.to_matrix_alg_equiv v₁ f i j = v₁.repr (f (v₁ j)) i :=
by simp [linear_map.to_matrix_alg_equiv, linear_map.to_matrix_apply]

lemma linear_map.to_matrix_alg_equiv_transpose_apply (f : M₁ →ₗ[R] M₁) (j : n) :
  (linear_map.to_matrix_alg_equiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
funext $ λ i, f.to_matrix_apply _ _ i j

lemma linear_map.to_matrix_alg_equiv_apply' (f : M₁ →ₗ[R] M₁) (i j : n) :
  linear_map.to_matrix_alg_equiv v₁ f i j = v₁.repr (f (v₁ j)) i :=
linear_map.to_matrix_alg_equiv_apply v₁ f i j

lemma linear_map.to_matrix_alg_equiv_transpose_apply' (f : M₁ →ₗ[R] M₁) (j : n) :
  (linear_map.to_matrix_alg_equiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
linear_map.to_matrix_alg_equiv_transpose_apply v₁ f j

lemma matrix.to_lin_alg_equiv_apply (M : matrix n n R) (v : M₁) :
  matrix.to_lin_alg_equiv v₁ M v = ∑ j, M.mul_vec (v₁.repr v) j • v₁ j :=
show v₁.equiv_fun.symm (matrix.to_lin_alg_equiv' M (v₁.repr v)) = _,
by rw [matrix.to_lin_alg_equiv'_apply, v₁.equiv_fun_symm_apply]

@[simp] lemma matrix.to_lin_alg_equiv_self (M : matrix n n R) (i : n) :
  matrix.to_lin_alg_equiv v₁ M (v₁ i) = ∑ j, M j i • v₁ j :=
matrix.to_lin_self _ _ _ _

lemma linear_map.to_matrix_alg_equiv_id : linear_map.to_matrix_alg_equiv v₁ id = 1 :=
by simp_rw [linear_map.to_matrix_alg_equiv, alg_equiv.of_linear_equiv_apply,
            linear_map.to_matrix_id]

@[simp]
lemma matrix.to_lin_alg_equiv_one : matrix.to_lin_alg_equiv v₁ 1 = id :=
by rw [← linear_map.to_matrix_alg_equiv_id v₁, matrix.to_lin_alg_equiv_to_matrix_alg_equiv]

theorem linear_map.to_matrix_alg_equiv_reindex_range [decidable_eq M₁]
  (f : M₁ →ₗ[R] M₁) (k i : n) :
  linear_map.to_matrix_alg_equiv v₁.reindex_range f
      ⟨v₁ k, mem_range_self k⟩ ⟨v₁ i, mem_range_self i⟩ =
    linear_map.to_matrix_alg_equiv v₁ f k i :=
by simp_rw [linear_map.to_matrix_alg_equiv_apply,
            basis.reindex_range_self, basis.reindex_range_repr]

lemma linear_map.to_matrix_alg_equiv_comp (f g : M₁ →ₗ[R] M₁) :
  linear_map.to_matrix_alg_equiv v₁ (f.comp g) =
  linear_map.to_matrix_alg_equiv v₁ f ⬝ linear_map.to_matrix_alg_equiv v₁ g :=
by simp [linear_map.to_matrix_alg_equiv, linear_map.to_matrix_comp v₁ v₁ v₁ f g]

lemma linear_map.to_matrix_alg_equiv_mul (f g : M₁ →ₗ[R] M₁) :
  linear_map.to_matrix_alg_equiv v₁ (f * g) =
    linear_map.to_matrix_alg_equiv v₁ f ⬝ linear_map.to_matrix_alg_equiv v₁ g :=
by { rw [show (@has_mul.mul (M₁ →ₗ[R] M₁) _) = linear_map.comp, from rfl,
         linear_map.to_matrix_alg_equiv_comp v₁ f g] }

lemma matrix.to_lin_alg_equiv_mul (A B : matrix n n R) :
  matrix.to_lin_alg_equiv v₁ (A ⬝ B) =
  (matrix.to_lin_alg_equiv v₁ A).comp (matrix.to_lin_alg_equiv v₁ B) :=
by convert matrix.to_lin_mul v₁ v₁ v₁ A B

@[simp] lemma matrix.to_lin_fin_two_prod_apply (a b c d : R) (x : R × R) :
  matrix.to_lin (basis.fin_two_prod R) (basis.fin_two_prod R) !![a, b; c, d] x =
    (a * x.fst + b * x.snd, c * x.fst + d * x.snd) :=
by simp [matrix.to_lin_apply, matrix.mul_vec, matrix.dot_product]

lemma matrix.to_lin_fin_two_prod (a b c d : R) :
  matrix.to_lin (basis.fin_two_prod R) (basis.fin_two_prod R) !![a, b; c, d] =
    (a • linear_map.fst R R R + b • linear_map.snd R R R).prod
    (c • linear_map.fst R R R + d • linear_map.snd R R R) :=
linear_map.ext $ matrix.to_lin_fin_two_prod_apply _ _ _ _

@[simp] lemma to_matrix_distrib_mul_action_to_linear_map (x : R) :
  linear_map.to_matrix v₁ v₁ (distrib_mul_action.to_linear_map R M₁ x) = matrix.diagonal (λ _, x) :=
begin
  ext,
  rw [linear_map.to_matrix_apply, distrib_mul_action.to_linear_map_apply, linear_equiv.map_smul,
    basis.repr_self, finsupp.smul_single_one, finsupp.single_eq_pi_single, matrix.diagonal_apply,
    pi.single_apply],
end

end to_matrix

namespace algebra

section lmul

variables {R S : Type*} [comm_ring R] [ring S] [algebra R S]
variables {m : Type*} [fintype m] [decidable_eq m] (b : basis m R S)

lemma to_matrix_lmul' (x : S) (i j) :
  linear_map.to_matrix b b (lmul R S x) i j = b.repr (x * b j) i :=
by simp only [linear_map.to_matrix_apply', coe_lmul_eq_mul, linear_map.mul_apply']

@[simp] lemma to_matrix_lsmul (x : R) :
  linear_map.to_matrix b b (algebra.lsmul R S x) = matrix.diagonal (λ _, x) :=
to_matrix_distrib_mul_action_to_linear_map b x

/-- `left_mul_matrix b x` is the matrix corresponding to the linear map `λ y, x * y`.

`left_mul_matrix_eq_repr_mul` gives a formula for the entries of `left_mul_matrix`.

This definition is useful for doing (more) explicit computations with `linear_map.mul_left`,
such as the trace form or norm map for algebras.
-/
noncomputable def left_mul_matrix : S →ₐ[R] matrix m m R :=
{ to_fun := λ x, linear_map.to_matrix b b (algebra.lmul R S x),
  map_zero' := by rw [alg_hom.map_zero, linear_equiv.map_zero],
  map_one' := by rw [alg_hom.map_one, linear_map.to_matrix_one],
  map_add' := λ x y, by rw [alg_hom.map_add, linear_equiv.map_add],
  map_mul' := λ x y, by rw [alg_hom.map_mul, linear_map.to_matrix_mul, matrix.mul_eq_mul],
  commutes' := λ r, by { ext, rw [lmul_algebra_map, to_matrix_lsmul, algebra_map_eq_diagonal,
                                  pi.algebra_map_def, algebra.id.map_eq_self] } }

lemma left_mul_matrix_apply (x : S) :
  left_mul_matrix b x = linear_map.to_matrix b b (lmul R S x) := rfl

lemma left_mul_matrix_eq_repr_mul (x : S) (i j) :
  left_mul_matrix b x i j = b.repr (x * b j) i :=
-- This is defeq to just `to_matrix_lmul' b x i j`,
-- but the unfolding goes a lot faster with this explicit `rw`.
by rw [left_mul_matrix_apply, to_matrix_lmul' b x i j]

lemma left_mul_matrix_mul_vec_repr (x y : S) :
  (left_mul_matrix b x).mul_vec (b.repr y) = b.repr (x * y) :=
(linear_map.mul_left R x).to_matrix_mul_vec_repr b b y

@[simp] lemma to_matrix_lmul_eq (x : S) :
  linear_map.to_matrix b b (linear_map.mul_left R x) = left_mul_matrix b x :=
rfl

lemma left_mul_matrix_injective : function.injective (left_mul_matrix b) :=
λ x x' h, calc x = algebra.lmul R S x 1 : (mul_one x).symm
             ... = algebra.lmul R S x' 1 : by rw (linear_map.to_matrix b b).injective h
             ... = x' : mul_one x'

end lmul

section lmul_tower

variables {R S T : Type*} [comm_ring R] [comm_ring S] [ring T]
variables [algebra R S] [algebra S T] [algebra R T] [is_scalar_tower R S T]
variables {m n : Type*} [fintype m] [fintype n] [decidable_eq m] [decidable_eq n]
variables (b : basis m R S) (c : basis n S T)

lemma smul_left_mul_matrix (x) (ik jk) :
  left_mul_matrix (b.smul c) x ik jk =
    left_mul_matrix b (left_mul_matrix c x ik.2 jk.2) ik.1 jk.1 :=
by simp only [left_mul_matrix_apply, linear_map.to_matrix_apply, mul_comm, basis.smul_apply,
  basis.smul_repr, finsupp.smul_apply, id.smul_eq_mul, linear_equiv.map_smul, mul_smul_comm,
  coe_lmul_eq_mul, linear_map.mul_apply']

lemma smul_left_mul_matrix_algebra_map (x : S) :
  left_mul_matrix (b.smul c) (algebra_map _ _ x) = block_diagonal (λ k, left_mul_matrix b x) :=
begin
  ext ⟨i, k⟩ ⟨j, k'⟩,
  rw [smul_left_mul_matrix, alg_hom.commutes, block_diagonal_apply, algebra_map_matrix_apply],
  split_ifs with h; simp [h],
end

lemma smul_left_mul_matrix_algebra_map_eq (x : S) (i j k) :
  left_mul_matrix (b.smul c) (algebra_map _ _ x) (i, k) (j, k) = left_mul_matrix b x i j :=
by rw [smul_left_mul_matrix_algebra_map, block_diagonal_apply_eq]

lemma smul_left_mul_matrix_algebra_map_ne (x : S) (i j) {k k'}
  (h : k ≠ k') : left_mul_matrix (b.smul c) (algebra_map _ _ x) (i, k) (j, k') = 0 :=
by rw [smul_left_mul_matrix_algebra_map, block_diagonal_apply_ne _ _ _ h]

end lmul_tower

end algebra

section

variables {R : Type v} [comm_ring R] {n : Type*} [decidable_eq n]
variables {M M₁ M₂ : Type*} [add_comm_group M] [module R M]
variables [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂]

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the algebra structures. -/
def alg_equiv_matrix' [fintype n] : module.End R (n → R) ≃ₐ[R] matrix n n R :=
{ map_mul'  := linear_map.to_matrix'_comp,
  map_add'  := linear_map.to_matrix'.map_add,
  commutes' := λ r, by { change (r • (linear_map.id : module.End R _)).to_matrix' = r • 1,
                         rw ←linear_map.to_matrix'_id, refl, apply_instance },
  ..linear_map.to_matrix' }

/-- A linear equivalence of two modules induces an equivalence of algebras of their
endomorphisms. -/
def linear_equiv.alg_conj (e : M₁ ≃ₗ[R] M₂) :
  module.End R M₁ ≃ₐ[R] module.End R M₂ :=
{ map_mul'  := λ f g, by apply e.arrow_congr_comp,
  map_add'  := e.conj.map_add,
  commutes' := λ r, by { change e.conj (r • linear_map.id) = r • linear_map.id,
                         rw [linear_equiv.map_smul, linear_equiv.conj_id], },
  ..e.conj }

/-- A basis of a module induces an equivalence of algebras from the endomorphisms of the module to
square matrices. -/
def alg_equiv_matrix [fintype n] (h : basis n R M) : module.End R M ≃ₐ[R] matrix n n R :=
h.equiv_fun.alg_conj.trans alg_equiv_matrix'

end
