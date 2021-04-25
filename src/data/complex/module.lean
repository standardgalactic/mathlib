/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel
-/
import data.complex.basic
import algebra.algebra.ordered
import data.matrix.notation
import field_theory.tower
import linear_algebra.finite_dimensional

/-!
# Complex number as a vector space over `ℝ`

This file contains the following instances:
* Any `•`-structure (`has_scalar`, `mul_action`, `distrib_mul_action`, `module`, `algebra`) on
  `ℝ` imbues a corresponding structure on `ℂ`. This includes the statement that `ℂ` is an `ℝ`
  algebra.
* any complex vector space is a real vector space;
* any finite dimensional complex vector space is a finite dimensional real vector space;
* the space of `ℝ`-linear maps from a real vector space to a complex vector space is a complex
  vector space.

It also defines three linear maps:

* `complex.re_lm`;
* `complex.im_lm`;
* `complex.of_real_lm`;
* `complex.conj_lm`.

They are bundled versions of the real part, the imaginary part, the embedding of `ℝ` in `ℂ`, and
the complex conjugate as `ℝ`-linear maps.
-/
noncomputable theory

namespace complex

variables {R : Type*} {S : Type*}

section

variables [has_scalar R ℝ]

/- The useless `0` multiplication in `smul` is to make sure that
`restrict_scalars.module ℝ ℂ ℂ  = complex.module` definitionally. -/
instance : has_scalar R ℂ :=
{ smul := λ r x, ⟨r • x.re - 0 * x.im, r • x.im + 0 * x.re⟩ }

lemma smul_re (r : R) (z : ℂ) : (r • z).re = r • z.re := by simp [(•)]
lemma smul_im (r : R) (z : ℂ) : (r • z).im = r • z.im := by simp [(•)]

@[simp] lemma smul_coe {x : ℝ} {z : ℂ} : x • z = x * z :=
by ext; simp [smul_re, smul_im]

end

instance [has_scalar R ℝ] [has_scalar S ℝ] [smul_comm_class R S ℝ] : smul_comm_class R S ℂ :=
{ smul_comm := λ r s x, by ext; simp [smul_re, smul_im, smul_comm] }

instance [has_scalar R S] [has_scalar R ℝ] [has_scalar S ℝ] [is_scalar_tower R S ℝ] :
  is_scalar_tower R S ℂ :=
{ smul_assoc := λ r s x, by ext; simp [smul_re, smul_im, smul_assoc] }

instance [monoid R] [mul_action R ℝ] : mul_action R ℂ :=
{ one_smul := λ x, by ext; simp [smul_re, smul_im, one_smul],
  mul_smul := λ r s x, by ext; simp  [smul_re, smul_im, mul_smul] }

instance [semiring R] [distrib_mul_action R ℝ] : distrib_mul_action R ℂ :=
{ smul_add := λ r x y, by ext; simp [smul_re, smul_im, smul_add],
  smul_zero := λ r, by ext; simp [smul_re, smul_im, smul_zero] }

instance [semiring R] [module R ℝ] : module R ℂ :=
{ add_smul := λ r s x, by ext; simp [smul_re, smul_im, add_smul],
  zero_smul := λ r, by ext; simp [smul_re, smul_im, zero_smul] }

instance [comm_semiring R] [algebra R ℝ] : algebra R ℂ :=
{ smul := (•),
  smul_def' := λ r x, by ext; simp [smul_re, smul_im, algebra.smul_def],
  commutes' := λ r ⟨xr, xi⟩, by ext; simp [smul_re, smul_im, algebra.commutes],
  ..complex.of_real.comp (algebra_map R ℝ) }

section
open_locale complex_order

lemma complex_ordered_module : ordered_module ℝ ℂ :=
{ smul_lt_smul_of_pos := λ z w x h₁ h₂,
  begin
    obtain ⟨y, l, rfl⟩ := lt_def.mp h₁,
    refine lt_def.mpr ⟨x * y, _, _⟩,
    exact mul_pos h₂ l,
    ext; simp [mul_add],
  end,
  lt_of_smul_lt_smul_of_pos := λ z w x h₁ h₂,
  begin
    obtain ⟨y, l, e⟩ := lt_def.mp h₁,
    by_cases h : x = 0,
    { subst h, exfalso, apply lt_irrefl 0 h₂, },
    { refine lt_def.mpr ⟨y / x, div_pos l h₂, _⟩,
      replace e := congr_arg (λ z, (x⁻¹ : ℂ) * z) e,
      simp only [mul_add, ←mul_assoc, h, one_mul, of_real_eq_zero, smul_coe, ne.def,
        not_false_iff, inv_mul_cancel] at e,
      convert e,
      simp only [div_eq_iff_mul_eq, h, of_real_eq_zero, of_real_div, ne.def, not_false_iff],
      norm_cast,
      simp [mul_comm _ y, mul_assoc, h],
    },
  end }

localized "attribute [instance] complex_ordered_module" in complex_order

end


@[simp] lemma coe_algebra_map : ⇑(algebra_map ℝ ℂ) = complex.of_real := rfl

open submodule finite_dimensional

lemma is_basis_one_I : is_basis ℝ ![1, I] :=
begin
  refine ⟨linear_independent_fin2.2 ⟨I_ne_zero, λ a, mt (congr_arg re) $ by simp⟩,
    eq_top_iff'.2 $ λ z, _⟩,
  suffices : ∃ a b : ℝ, z = a • I + b • 1,
    by simpa [mem_span_insert, mem_span_singleton, -set.singleton_one],
  use [z.im, z.re],
  simp [algebra.smul_def, add_comm]
end

instance : finite_dimensional ℝ ℂ := of_fintype_basis is_basis_one_I

@[simp] lemma finrank_real_complex : finite_dimensional.finrank ℝ ℂ = 2 :=
by rw [finrank_eq_card_basis is_basis_one_I, fintype.card_fin]

@[simp] lemma dim_real_complex : module.rank ℝ ℂ = 2 :=
by simp [← finrank_eq_dim, finrank_real_complex]

lemma {u} dim_real_complex' : cardinal.lift.{0 u} (module.rank ℝ ℂ) = 2 :=
by simp [← finrank_eq_dim, finrank_real_complex, bit0]

/-- `fact` version of the dimension of `ℂ` over `ℝ`, locally useful in the definition of the
circle. -/
lemma finrank_real_complex_fact : fact (finrank ℝ ℂ = 2) := ⟨finrank_real_complex⟩

end complex

/- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
@[priority 900]
instance module.complex_to_real (E : Type*) [add_comm_group E] [module ℂ E] : module ℝ E :=
restrict_scalars.module ℝ ℂ E

instance module.real_complex_tower (E : Type*) [add_comm_group E] [module ℂ E] :
  is_scalar_tower ℝ ℂ E :=
restrict_scalars.is_scalar_tower ℝ ℂ E

@[priority 100]
instance finite_dimensional.complex_to_real (E : Type*) [add_comm_group E] [module ℂ E]
  [finite_dimensional ℂ E] : finite_dimensional ℝ E :=
finite_dimensional.trans ℝ ℂ E

lemma dim_real_of_complex (E : Type*) [add_comm_group E] [module ℂ E] :
  module.rank ℝ E = 2 * module.rank ℂ E :=
cardinal.lift_inj.1 $
  by { rw [← dim_mul_dim' ℝ ℂ E, complex.dim_real_complex], simp [bit0] }

lemma finrank_real_of_complex (E : Type*) [add_comm_group E] [module ℂ E] :
  finite_dimensional.finrank ℝ E = 2 * finite_dimensional.finrank ℂ E :=
by rw [← finite_dimensional.finrank_mul_finrank ℝ ℂ E, complex.finrank_real_complex]

namespace complex

/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def re_lm : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.re,
  map_add' := add_re,
  map_smul' := by simp, }

@[simp] lemma re_lm_coe : ⇑re_lm = re := rfl

/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def im_lm : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.im,
  map_add' := add_im,
  map_smul' := by simp, }

@[simp] lemma im_lm_coe : ⇑im_lm = im := rfl

/-- Linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def of_real_lm : ℝ →ₗ[ℝ] ℂ :=
{ to_fun := coe,
  map_add' := of_real_add,
  map_smul' := λc x, by simp [algebra.smul_def] }

@[simp] lemma of_real_lm_coe : ⇑of_real_lm = coe := rfl

/-- `ℝ`-linear map version of the complex conjugation function from `ℂ` to `ℂ`. -/
def conj_lm : ℂ →ₗ[ℝ] ℂ :=
{ map_smul' := by simp [restrict_scalars_smul_def],
  ..conj }

@[simp] lemma conj_lm_coe : ⇑conj_lm = conj := rfl

end complex
