/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.cartan_subalgebra
import algebra.lie.tensor_product
import linear_algebra.eigenspace
import tactic.omega

/-!
# Weights and roots of Lie modules and Lie algebras

Foo

## Main definitions

  * `foo`
  * `bar`

## Tags

lie character, eigenvalue, eigenspace, weight, weight vector, root, root vector, root system
-/

universes u v w w₁ w₂ w₃

variables (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L]
variables (H : lie_subalgebra R L) [lie_algebra.is_nilpotent R H]
variables (M : Type w) [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]

open finset
open lie_algebra
open lie_module
open tensor_product.lie_module

open_locale big_operators
open_locale tensor_product

variables {R L} (M₁ : Type w₁) (M₂ : Type w₂) (M₃ : Type w₃)
variables [add_comm_group M₁] [module R M₁] [lie_ring_module L M₁] [lie_module R L M₁]
variables [add_comm_group M₂] [module R M₂] [lie_ring_module L M₂] [lie_module R L M₂]
variables [add_comm_group M₃] [module R M₃] [lie_ring_module L M₃] [lie_module R L M₃]

variables {M}

lemma linear_map.iterate_map_zero_of_le
  {f : module.End R M} {m : M} {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) (hm : (f^k₁) m = 0) : (f^k₂) m = 0 :=
begin
  have h : k₂ = (k₂ - k₁) + k₁, { rw ← nat.sub_eq_iff_eq_add hk, },
  rw [h, pow_add f, linear_map.mul_apply, hm, linear_map.map_zero],
end

lemma nat_foo (a b i : ℕ) : a ≤ i ∨ b ≤ a + b - 1 - i :=
begin
  cases le_or_lt a i with h h; [left, right],
  { exact h },
  { rw [nat.add_comm, nat.sub_sub, nat.add_comm 1, nat.add_sub_assoc (nat.succ_le_of_lt h)],
    exact nat.le_add_right _ _, },
end

-- TODO Relocate to beside commute.add_pow
lemma commute.add_pow' {R : Type*} [semiring R] {x y : R} (h : commute x y) (n : ℕ) :
  (x + y) ^ n = ∑ m in range (n + 1), nat.choose n m • (x ^ m * y ^ (n - m)) :=
by simp_rw [nsmul_eq_mul, nat.cast_comm, h.add_pow n]

variables (M)

/-- Maybe should call this `pre_weight_space` or `weight_space_aux`? -/
def wt_space (χ : L → R) : submodule R M :=
⨅ (x : L), (to_endomorphism R L M x).maximal_generalized_eigenspace (χ x)

-- Odd statement: `g` must be `L`-equivariant but we coerce this away immediately.
-- Note also that we don't need any structure on `L` and that we also don't need the Lie (ring)
-- module structures on the `Mᵢ`: just that the elements of `L` act linearly. Probably not worth
-- introducing all the classes necessary to do this neatly (in a bundled way) though.
lemma key_identity (g : M₁ ⊗[R] M₂ →ₗ⁅R,L⁆ M₃) (χ₁ χ₂ : L → R) :
  ((g : M₁ ⊗[R] M₂ →ₗ[R] M₃).comp
    (tensor_product.map_incl (wt_space M₁ χ₁) (wt_space M₂ χ₂))).range ≤ wt_space M₃ (χ₁ + χ₂) :=
begin
  intros m₃ hm₃,
  simp only [wt_space, module.End.mem_maximal_generalized_eigenspace, submodule.mem_infi],
  intros x,
  simp only [lie_module_hom.coe_to_linear_map, function.comp_app, linear_map.coe_comp,
    linear_map.mem_range] at hm₃,
  obtain ⟨t, rfl⟩ := hm₃,
  apply t.induction_on,
  { use 0, simp only [linear_map.map_zero, lie_module_hom.map_zero], },
  swap,
  { rintros t₁ t₂ ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩,
    use max k₁ k₂,
    simp only [lie_module_hom.map_add, linear_map.map_add],
    rw [linear_map.iterate_map_zero_of_le (le_max_left k₁ k₂) hk₁,
        linear_map.iterate_map_zero_of_le (le_max_right k₁ k₂) hk₂, add_zero], },

  -- Finally the main argument:

  let f₁ : L → module.End R (M₁ ⊗[R] M₂) := λ x, (to_endomorphism R L M₁ x - (χ₁ x) • 1).rtensor M₂,
  let f₂ : L → module.End R (M₁ ⊗[R] M₂) := λ x, (to_endomorphism R L M₂ x - (χ₂ x) • 1).ltensor M₁,
  let F : L → module.End R M₃ := λ x, (to_endomorphism R L M₃ x) - ((χ₁ + χ₂) x) • 1,

  have hF : ∀ (x : L), (g : M₁ ⊗[R] M₂ →ₗ[R] M₃).comp ((f₁ + f₂) x) = (F x).comp ↑g,
  { intros x, ext m₁ m₂,
    simp only [←g.map_lie x (m₁ ⊗ₜ[R] m₂), add_smul, lie_tmul_right, tensor_product.sub_tmul,
      tensor_product.tmul_sub, tensor_product.smul_tmul, tensor_product.tmul_smul,
      to_endomorphism_apply_apply, tensor_product.mk_apply, lie_module_hom.map_smul,
      linear_map.one_apply, lie_module_hom.coe_to_linear_map, linear_map.compr₂_apply, pi.add_apply,
      linear_map.smul_apply, function.comp_app, linear_map.coe_comp, linear_map.rtensor_tmul,
      lie_module_hom.map_add, linear_map.add_apply, lie_module_hom.map_sub, linear_map.sub_apply,
      linear_map.ltensor_tmul],
    abel, },

  have hF' : ∀ (x : L) (t : M₁ ⊗[R] M₂) (k : ℕ), ((F x)^k) (g t) = g (((f₁ x + f₂ x)^k) t),
  { intros x t k,
    induction k with k ih,
    { simp only [linear_map.one_apply, pow_zero], },
    { simp only [pow_succ, linear_map.mul_apply, ih],
      rw [← function.comp_app (F x) g, ← function.comp_app g ⇑(f₁ x + f₂ x)],
      replace hF := linear_map.congr_fun (hF x),
      simp only [linear_map.coe_comp, lie_module_hom.coe_to_linear_map] at hF,
      rw ← hF, refl, }, },

  have hf_comm : ∀ x, commute (f₁ x) (f₂ x),
  { intros x, ext m₁ m₂,
    simp only [smul_comm (χ₁ x) (χ₂ x), linear_map.rtensor_smul, to_endomorphism_apply_apply,
      tensor_product.mk_apply, linear_map.mul_apply, linear_map.one_apply, linear_map.ltensor_sub,
      linear_map.compr₂_apply, linear_map.smul_apply, linear_map.ltensor_smul,
      linear_map.rtensor_tmul, linear_map.map_sub, linear_map.map_smul, linear_map.rtensor_sub,
      linear_map.sub_apply, linear_map.ltensor_tmul], },

  rintros ⟨m₁, hm₁⟩ ⟨m₂, hm₂⟩,
  change ∃ k, ((F x)^k) _ = 0,
  simp_rw [hF' x, (hf_comm x).add_pow'],
  simp only [tensor_product.map_incl, submodule.subtype_apply, sum_apply,
    submodule.coe_mk, linear_map.coe_fn_sum, tensor_product.map_tmul, linear_map.smul_apply],
  simp only [wt_space, submodule.mem_infi, module.End.mem_maximal_generalized_eigenspace]
    at hm₁ hm₂,
  obtain ⟨k₁, hk₁⟩ := hm₁ x,
  obtain ⟨k₂, hk₂⟩ := hm₂ x,
  use k₁ + k₂ - 1,

  suffices : ∀ (i : ℕ), (f₁ x ^ i * f₂ x ^ (k₁ + k₂ - 1 - i)) (m₁ ⊗ₜ[R] m₂) = 0,
  { simp only [this, lie_module_hom.map_zero, sum_const_zero, smul_zero], },
  intros i,

  cases nat_foo k₁ k₂ i with hi hi,
  { simp only [linear_map.mul_apply, linear_map.rtensor_tmul, linear_map.rtensor_pow,
      linear_map.ltensor_pow, linear_map.ltensor_tmul, linear_map.iterate_map_zero_of_le hi hk₁,
      tensor_product.zero_tmul], },
  { simp only [linear_map.mul_apply, linear_map.rtensor_tmul, linear_map.rtensor_pow,
      linear_map.ltensor_pow, linear_map.ltensor_tmul, linear_map.iterate_map_zero_of_le hi hk₂,
      tensor_product.tmul_zero, linear_map.map_zero], },
end

lemma key_identity_corollary [lie_algebra.is_nilpotent R L] (χ : L → R) :
  ((to_module_hom R L M : L ⊗[R] M →ₗ[R] M).comp
    (tensor_product.map_incl ⊤ (wt_space M χ))).range ≤ wt_space M χ :=
begin
  have h₁ : wt_space L (0 : L → R) = ⊤,
  { exact lie_algebra.infi_max_gen_zero_eigenspace_eq_top_of_nilpotent R L, }, rw ← h₁,
  have h₂ := key_identity L M M (to_module_hom R L M) 0 χ,
  rw zero_add at h₂,
  exact h₂,
end

variables (R L)

abbreviation lie_character := L →ₗ⁅R⁆ R

lemma lie_character_foo (χ : lie_character R L) (x y : L) : χ ⁅x, y⁆ = 0 :=
by rw [lie_hom.map_lie, lie_ring.of_associative_ring_bracket, mul_comm, sub_self]

def lie_character_equiv_linear_dual [is_lie_abelian L] :
  lie_character R L ≃ module.dual R L :=
{ to_fun    := λ χ, (χ : L →ₗ[R] R),
  inv_fun   := λ ψ,
  { map_lie' := λ x y, by
    rw [lie_module.is_trivial.trivial, lie_ring.of_associative_ring_bracket, mul_comm, sub_self,
      linear_map.to_fun_eq_coe, linear_map.map_zero],
    .. ψ, },
  left_inv  := λ χ, by { ext, refl, },
  right_inv := λ ψ, by { ext, refl, }, }

variables {R L}

/-- TODO Perhaps comment that `lie_character` is more than we need: `∀ x y, χ ⁅x, y⁆ = ⁅χ x, χ y⁆`
(and no linearity) would suffice. -/
def weight_space [lie_algebra.is_nilpotent R L] (χ : lie_character R L) : lie_submodule R L M :=
{ lie_mem := λ x m hm,
  begin
    simp only [set_like.mem_coe, submodule.mem_carrier] at hm ⊢,
    apply key_identity_corollary M χ,
    simp only [tensor_product.map_incl, lie_module_hom.coe_to_linear_map, function.comp_app,
      linear_map.coe_comp, linear_map.mem_range],
    use (⟨x, submodule.mem_top⟩ : (⊤ : submodule R L)) ⊗ₜ (⟨m, hm⟩ : wt_space M χ),
    simp only [submodule.subtype_apply, to_module_hom_apply, submodule.coe_mk,
      tensor_product.map_tmul],
  end,
  .. wt_space M χ }

structure lie_weight :=
(χ : lie_character R H)
(weight_space_ne_bot : weight_space M χ ≠ ⊥)

abbreviation lie_root := lie_weight H L
