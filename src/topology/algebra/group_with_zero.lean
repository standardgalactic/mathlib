/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import topology.algebra.monoid
import algebra.group.pi
import algebra.group_with_zero.power
import topology.homeomorph

/-!
# Topological group with zero

In this file we define `has_continuous_inv'` to be a mixin typeclass a type with `has_inv` and
`has_zero` (e.g., a `group_with_zero`) such that `λ x, x⁻¹` is continuous at all nonzero points. Any
normed (semi)field has this property. Currently the only example of `has_continuous_inv'` in
`mathlib` which is not a normed field is the type `nnnreal` (a.k.a. `ℝ≥0`) of nonnegative real
numbers.

Then we prove lemmas about continuity of `x ↦ x⁻¹` and `f / g` providing dot-style `*.inv'` and
`*.div` operations on `filter.tendsto`, `continuous_at`, `continuous_within_at`, `continuous_on`,
and `continuous`. As a special case, we provide `*.div_const` operations that require only
`group_with_zero` and `has_continuous_mul` instances.

All lemmas about `(⁻¹)` use `inv'` in their names because lemmas without `'` are used for
`topological_group`s. We also use `'` in the typeclass name `has_continuous_inv'` for the sake of
consistency of notation.

On a `group_with_zero` with continuous multiplication, we also define left and right multiplication
as homeomorphisms.
-/

open_locale topological_space
open filter

/-!
### A group with zero with continuous multiplication

If `G₀` is a group with zero with continuous `(*)`, then `(/y)` is continuous for any `y`. In this
section we prove lemmas that immediately follow from this fact providing `*.div_const` dot-style
operations on `filter.tendsto`, `continuous_at`, `continuous_within_at`, `continuous_on`, and
`continuous`.
-/

variables {α G₀ : Type*}

section div_const

variables [group_with_zero G₀] [topological_space G₀] [has_continuous_mul G₀]
  {f : α → G₀} {s : set α} {l : filter α}

lemma filter.tendsto.div_const {x y : G₀} (hf : tendsto f l (𝓝 x)) :
  tendsto (λa, f a / y) l (𝓝 (x / y)) :=
by simpa only [div_eq_mul_inv] using hf.mul tendsto_const_nhds

variables [topological_space α]

lemma continuous_at.div_const (hf : continuous f) {y : G₀} : continuous (λ x, f x / y) :=
by simpa only [div_eq_mul_inv] using hf.mul continuous_const

lemma continuous_within_at.div_const {a} (hf : continuous_within_at f s a) {y : G₀} :
  continuous_within_at (λ x, f x / y) s a :=
hf.div_const

lemma continuous_on.div_const (hf : continuous_on f s) {y : G₀} : continuous_on (λ x, f x / y) s :=
by simpa only [div_eq_mul_inv] using hf.mul continuous_on_const

@[continuity] lemma continuous.div_const (hf : continuous f) {y : G₀} :
  continuous (λ x, f x / y) :=
by simpa only [div_eq_mul_inv] using hf.mul continuous_const

end div_const

/-- A type with `0` and `has_inv` such that `λ x, x⁻¹` is continuous at all nonzero points. Any
normed (semi)field has this property. -/
class has_continuous_inv' (G₀ : Type*) [has_zero G₀] [has_inv G₀] [topological_space G₀] :=
(continuous_at_inv' : ∀ ⦃x : G₀⦄, x ≠ 0 → continuous_at has_inv.inv x)

export has_continuous_inv' (continuous_at_inv')

section inv'

variables [has_zero G₀] [has_inv G₀] [topological_space G₀] [has_continuous_inv' G₀]
  {l : filter α} {f : α → G₀} {s : set α} {a : α}

/-!
### Continuity of `λ x, x⁻¹` at a non-zero point

We define `topological_group_with_zero` to be a `group_with_zero` such that the operation `x ↦ x⁻¹`
is continuous at all nonzero points. In this section we prove dot-style `*.inv'` lemmas for
`filter.tendsto`, `continuous_at`, `continuous_within_at`, `continuous_on`, and `continuous`.
-/

lemma tendsto_inv' {x : G₀}  (hx : x ≠ 0) : tendsto has_inv.inv (𝓝 x) (𝓝 x⁻¹) :=
continuous_at_inv' hx

lemma continuous_on_inv' : continuous_on (has_inv.inv : G₀ → G₀) {0}ᶜ :=
λ x hx, (continuous_at_inv' hx).continuous_within_at

/-- If a function converges to a nonzero value, its inverse converges to the inverse of this value.
We use the name `tendsto.inv'` as `tendsto.inv` is already used in multiplicative topological
groups. -/
lemma filter.tendsto.inv' {a : G₀} (hf : tendsto f l (𝓝 a))
  (ha : a ≠ 0) :
  tendsto (λ x, (f x)⁻¹) l (𝓝 a⁻¹) :=
(tendsto_inv' ha).comp hf

variables [topological_space α]

lemma continuous_within_at.inv' (hf : continuous_within_at f s a) (ha : f a ≠ 0) :
  continuous_within_at (λ x, (f x)⁻¹) s a :=
hf.inv' ha

lemma continuous_at.inv' (hf : continuous_at f a) (ha : f a ≠ 0) :
  continuous_at (λ x, (f x)⁻¹) a :=
hf.inv' ha

@[continuity] lemma continuous.inv' (hf : continuous f) (h0 : ∀ x, f x ≠ 0) :
  continuous (λ x, (f x)⁻¹) :=
continuous_iff_continuous_at.2 $ λ x, (hf.tendsto x).inv' (h0 x)

lemma continuous_on.inv' (hf : continuous_on f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
  continuous_on (λ x, (f x)⁻¹) s :=
λ x hx, (hf x hx).inv' (h0 x hx)

end inv'

/-!
### Continuity of division

If `G₀` is a `group_with_zero` with `x ↦ x⁻¹` continuous at all nonzero points and `(*)`, then
division `(/)` is continuous at any point where the denominator is continuous.
-/

section div

variables [group_with_zero G₀] [topological_space G₀] [has_continuous_inv' G₀]
  [has_continuous_mul G₀] {f g : α → G₀}

lemma filter.tendsto.div {l : filter α} {a b : G₀} (hf : tendsto f l (𝓝 a))
  (hg : tendsto g l (𝓝 b)) (hy : b ≠ 0) :
  tendsto (f / g) l (𝓝 (a / b)) :=
by simpa only [div_eq_mul_inv] using hf.mul (hg.inv' hy)

variables [topological_space α] {s : set α} {a : α}

lemma continuous_within_at.div (hf : continuous_within_at f s a) (hg : continuous_within_at g s a)
  (h₀ : g a ≠ 0) :
  continuous_within_at (f / g) s a :=
hf.div hg h₀

lemma continuous_on.div (hf : continuous_on f s) (hg : continuous_on g s) (h₀ : ∀ x ∈ s, g x ≠ 0) :
  continuous_on (f / g) s :=
λ x hx, (hf x hx).div (hg x hx) (h₀ x hx)

/-- Continuity at a point of the result of dividing two functions continuous at that point, where
the denominator is nonzero. -/
lemma continuous_at.div (hf : continuous_at f a) (hg : continuous_at g a) (h₀ : g a ≠ 0) :
  continuous_at (f / g) a :=
hf.div hg h₀

@[continuity] lemma continuous.div (hf : continuous f) (hg : continuous g) (h₀ : ∀ x, g x ≠ 0) :
  continuous (f / g) :=
by simpa only [div_eq_mul_inv] using hf.mul (hg.inv' h₀)

lemma continuous_on_div : continuous_on (λ p : G₀ × G₀, p.1 / p.2) {p | p.2 ≠ 0} :=
continuous_on_fst.div continuous_on_snd $ λ _, id

end div

/-! ### Left and right multiplication as homeomorphisms -/

namespace homeomorph

variables [topological_space α] [group_with_zero α] [has_continuous_mul α]

/-- Left multiplication by a nonzero element in a `group_with_zero` with continuous multiplication
is a homeomorphism of the underlying type. -/
protected def mul_left' (c : α) (hc : c ≠ 0) : α ≃ₜ α :=
{ continuous_to_fun := continuous_mul_left _,
  continuous_inv_fun := continuous_mul_left _,
  .. equiv.mul_left' c hc }

/-- Right multiplication by a nonzero element in a `group_with_zero` with continuous multiplication
is a homeomorphism of the underlying type. -/
protected def mul_right' (c : α) (hc : c ≠ 0) : α ≃ₜ α :=
{ continuous_to_fun := continuous_mul_right _,
  continuous_inv_fun := continuous_mul_right _,
  .. equiv.mul_right' c hc }

@[simp] lemma coe_mul_left' (c : α) (hc : c ≠ 0) : ⇑(homeomorph.mul_left' c hc) = (*) c := rfl

@[simp] lemma mul_left'_symm_apply (c : α) (hc : c ≠ 0) :
  ((homeomorph.mul_left' c hc).symm : α → α) = (*) c⁻¹ := rfl

@[simp] lemma coe_mul_right' (c : α) (hc : c ≠ 0) :
  ⇑(homeomorph.mul_right' c hc) = λ x, x * c := rfl

@[simp] lemma mul_right'_symm_apply (c : α) (hc : c ≠ 0) :
  ((homeomorph.mul_right' c hc).symm : α → α) = λ x, x * c⁻¹ := rfl

end homeomorph

section fpow

variables [group_with_zero G₀] [topological_space G₀] [has_continuous_inv' G₀]
  [has_continuous_mul G₀]

lemma tendsto_fpow {x : G₀} (hx : x ≠ 0) (m : ℤ) : tendsto (λ x, x ^ m) (𝓝 x) (𝓝 (x ^ m)) :=
begin
  have : ∀ y : G₀, ∀ m : ℤ, 0 < m → tendsto (λ x, x ^ m) (𝓝 y) (𝓝 (y ^ m)),
  { assume y m hm,
    lift m to ℕ using (le_of_lt hm) with k,
    simp only [gpow_coe_nat],
    exact (continuous_pow k).continuous_at.tendsto },
  rcases lt_trichotomy m 0 with hm | hm | hm,
  { have hm' : 0 < - m := by rwa neg_pos,
    convert (this _ (-m) hm').comp (tendsto_inv' hx) using 1,
    { ext y,
      simp },
    { congr' 1,
      simp } },
  { simpa [hm] using tendsto_const_nhds },
  { exact this _ m hm }
end

lemma continuous_at_fpow {x : G₀} (hx : x ≠ 0) (m : ℤ) : continuous_at (λ x, x ^ m) x :=
tendsto_fpow hx m

lemma continuous_on_fpow (m : ℤ) : continuous_on (λ x : G₀, x ^ m) {0}ᶜ :=
λ x hx, (continuous_at_fpow hx m).continuous_within_at

variables {f : α → G₀}

lemma filter.tendsto.fpow {l : filter α} {a : G₀} (hf : tendsto f l (𝓝 a)) (ha : a ≠ 0) (m : ℤ) :
  tendsto (λ x, (f x) ^ m) l (𝓝 (a ^ m)) :=
(tendsto_fpow ha m).comp hf

variables [topological_space α] {a : α}

lemma continuous_at.fpow (hf : continuous_at f a) (ha : f a ≠ 0) (m : ℤ) :
  continuous_at (λ x, (f x) ^ m) a :=
(continuous_at_fpow ha m).comp hf

@[continuity] lemma continuous.fpow (hf : continuous f) (h0 : ∀ a, f a ≠ 0) (m : ℤ) :
  continuous (λ x, (f x) ^ m) :=
continuous_iff_continuous_at.2 $ λ x, (hf.tendsto x).fpow (h0 x) m

end fpow
