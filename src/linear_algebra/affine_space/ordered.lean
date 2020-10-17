/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import linear_algebra.affine_space.basic
import algebra.module.ordered

/-!
# Ordered modules as affine spaces

In this file we define the slope of a function `f : k → PE` taking values in an affine space over
`k` and prove some theorems about `slope` and `line_map` in the case when `PE` is an ordered
semimodule over `k`.

## Implementation notes

We do not introduce the notion of ordered affine spaces (yet?). Instead, we prove various theorems
for an ordered semimodule interpreted as an affine space.

## Tags

affine space, ordered semimodule, slope
-/

open affine_map

variables {k E PE : Type*}

/-!
### Definition of `slope` and basic properties

In this section we define `slope f a b` and prove some properties that do not require order on the
codomain.  -/

section no_order

variables [field k] [add_comm_group E] [semimodule k E] [add_torsor E PE]

include E

/-- `slope f a b = (b - a)⁻¹ • (f b -ᵥ f a)` is the slope of a function `f` on the interval
`[a, b]`. Note that `slope f a a = 0`, not the derivative of `f` at `a`. -/
def slope (f : k → PE) (a b : k) : E := (b - a)⁻¹ • (f b -ᵥ f a)

@[simp] lemma slope_same (f : k → PE) (a : k) : (slope f a a : E) = 0 :=
by rw [slope, sub_self, inv_zero, zero_smul]

lemma slope_comm (f : k → PE) (a b : k) : slope f a b = slope f b a :=
by rw [slope, slope, ← neg_vsub_eq_vsub_rev, smul_neg, ← neg_smul, neg_inv, neg_sub]

/-- `slope f a c` is a linear combination of `slope f a b` and `slope f b c`. This version
explicitly provides coefficients. If `a ≠ c`, then the sum of the coefficients is `1`, so it is
actually an affine combination, see `line_map_slope_slope_sub_div_sub`. -/
lemma sub_div_sub_smul_slope_add_sub_div_sub_smul_slope (f : k → PE) (a b c : k) :
  ((b - a) / (c - a)) • slope f a b + ((c - b) / (c - a)) • slope f b c = slope f a c :=
begin
  by_cases hab : a = b,
  { subst hab,
    rw [sub_self, zero_div, zero_smul, zero_add],
    by_cases hac : a = c,
    { simp [hac] },
    { rw [div_self (sub_ne_zero.2 $ ne.symm hac), one_smul] } },
  by_cases hbc : b = c, { subst hbc, simp [sub_ne_zero.2 (ne.symm hab)] },
  rw [add_comm],
  simp_rw [slope, div_eq_inv_mul, mul_smul, ← smul_add,
    smul_inv_smul' (sub_ne_zero.2 $ ne.symm hab), smul_inv_smul' (sub_ne_zero.2 $ ne.symm hbc),
    vsub_add_vsub_cancel],
end

/-- `slope f a c` is an affine combination of `slope f a b` and `slope f b c`. This version uses
`line_map` to express this property. -/
lemma line_map_slope_slope_sub_div_sub (f : k → PE) (a b c : k) (h : a ≠ c) :
  line_map (slope f a b) (slope f b c) ((c - b) / (c - a)) = slope f a c :=
by  field_simp [sub_ne_zero.2 h.symm, ← sub_div_sub_smul_slope_add_sub_div_sub_smul_slope f a b c,
  line_map_apply_module]

/-- `slope f a b` is an affine combination of `slope f a (line_map a b r)` and
`slope f (line_map a b r) b`. We use `line_map` to express this property. -/
lemma line_map_slope_line_map_slope_line_map (f : k → PE) (a b r : k) :
  line_map (slope f (line_map a b r) b) (slope f a (line_map a b r)) r = slope f a b :=
begin
  obtain (rfl|hab) : a = b ∨ a ≠ b := classical.em _, { simp },
  rw [slope_comm _ a, slope_comm _ a, slope_comm _ _ b],
  convert line_map_slope_slope_sub_div_sub f b (line_map a b r) a hab.symm using 2,
  rw [line_map_apply_ring, eq_div_iff (sub_ne_zero.2 hab), sub_mul, one_mul, mul_sub, ← sub_sub,
    sub_sub_cancel]
end

end no_order

/-!
### Monotonicity of `line_map`

In this section we prove that `line_map a b r` is monotone (strictly or not) in its arguments if
other arguments belong to specific domains.
-/

section ordered_ring

variables [ordered_ring k] [ordered_add_comm_group E] [ordered_semimodule k E]

variables {a a' b b' : E} {r r' : k}

lemma line_map_mono_left (ha : a ≤ a') (hr : r ≤ 1) :
  line_map a b r ≤ line_map a' b r :=
begin
  simp only [line_map_apply_module],
  exact add_le_add_right (smul_le_smul_of_nonneg ha (sub_nonneg.2 hr)) _
end

lemma line_map_strict_mono_left (ha : a < a') (hr : r < 1) :
  line_map a b r < line_map a' b r :=
begin
  simp only [line_map_apply_module],
  exact add_lt_add_right (smul_lt_smul_of_pos ha (sub_pos.2 hr)) _
end

lemma line_map_mono_right (hb : b ≤ b') (hr : 0 ≤ r) :
  line_map a b r ≤ line_map a b' r :=
begin
  simp only [line_map_apply_module],
  exact add_le_add_left (smul_le_smul_of_nonneg hb hr) _
end

lemma line_map_strict_mono_right (hb : b < b') (hr : 0 < r) :
  line_map a b r < line_map a b' r :=
begin
  simp only [line_map_apply_module],
  exact add_lt_add_left (smul_lt_smul_of_pos hb hr) _
end

lemma line_map_mono_endpoints (ha : a ≤ a') (hb : b ≤ b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
  line_map a b r ≤ line_map a' b' r :=
(line_map_mono_left ha h₁).trans (line_map_mono_right hb h₀)

lemma line_map_strict_mono_endpoints (ha : a < a') (hb : b < b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
  line_map a b r < line_map a' b' r :=
begin
  rcases h₀.eq_or_lt with (rfl|h₀), { simpa },
  exact (line_map_mono_left ha.le h₁).trans_lt (line_map_strict_mono_right hb h₀)
end

lemma line_map_lt_line_map_iff_of_lt (h : r < r') :
  line_map a b r < line_map a b r' ↔ a < b :=
begin
  simp only [line_map_apply_module],
  rw [← lt_sub_iff_add_lt, add_sub_assoc, ← sub_lt_iff_lt_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_lt_smul_iff_of_pos (sub_pos.2 h)]
end

lemma left_lt_line_map_iff_lt (h : 0 < r) : a < line_map a b r ↔ a < b :=
iff.trans (by rw line_map_apply_zero) (line_map_lt_line_map_iff_of_lt h)

lemma line_map_lt_left_iff_lt (h : 0 < r) : line_map a b r < a ↔ b < a :=
@left_lt_line_map_iff_lt k (order_dual E) _ _ _ _ _ _ h

lemma line_map_lt_right_iff_lt (h : r < 1) : line_map a b r < b ↔ a < b :=
iff.trans (by rw line_map_apply_one) (line_map_lt_line_map_iff_of_lt h)

lemma right_lt_line_map_iff_lt (h : r < 1) : b < line_map a b r ↔ b < a :=
@line_map_lt_right_iff_lt k (order_dual E) _ _ _ _ _ _ h

end ordered_ring

section linear_ordered_field

variables [linear_ordered_field k] [ordered_add_comm_group E] [ordered_semimodule k E]

section

variables {a b : E} {r r' : k}

lemma line_map_le_line_map_iff_of_lt (h : r < r') :
  line_map a b r ≤ line_map a b r' ↔ a ≤ b :=
begin
  simp only [line_map_apply_module],
  rw [← le_sub_iff_add_le, add_sub_assoc, ← sub_le_iff_le_add', ← sub_smul, ← sub_smul,
    sub_sub_sub_cancel_left, smul_le_smul_iff_of_pos (sub_pos.2 h)]
end

lemma left_le_line_map_iff_le (h : 0 < r) : a ≤ line_map a b r ↔ a ≤ b :=
iff.trans (by rw line_map_apply_zero) (line_map_le_line_map_iff_of_lt h)

lemma line_map_le_left_iff_le (h : 0 < r) : line_map a b r ≤ a ↔ b ≤ a :=
@left_le_line_map_iff_le k (order_dual E) _ _ _ _ _ _ h

lemma line_map_le_right_iff_le (h : r < 1) : line_map a b r ≤ b ↔ a ≤ b :=
iff.trans (by rw line_map_apply_one) (line_map_le_line_map_iff_of_lt h)

lemma right_le_line_map_iff_le (h : r < 1) : b ≤ line_map a b r ↔ b ≤ a :=
@line_map_le_right_iff_le k (order_dual E) _ _ _ _ _ _ h

end

/-!
### Convexity and slope

In this section we prove inequality that relate `f (line_map a b r) ≤ line_map (f a) (f b) r` and
`f (line_map a b r) < line_map (f a) (f b) r` to inequalities on slopes of `f`. For each inequality
we provide 3 lemmas:

* `*_left` relates it to an inequality on `slope f a (line_map a b r)` and `slope f a b`;
* `*_right` relates it to an inequality on `slope f a b` and `slope f (line_map a b r) b`;
* no-suffix version relates it to an inequality on `slope f a (line_map a b r)` and
  `slope f (line_map a b r) b`.

Later these inequalities will be used in to restate `convex_on` in terms of monotonicity of the
slope.
-/

variables {f : k → E} {a b r : k}

lemma map_le_line_map_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
  f (line_map a b r) ≤ line_map (f a) (f b) r ↔ slope f a (line_map a b r) ≤ slope f a b :=
by simp_rw [line_map_apply, slope, vsub_eq_sub, vadd_eq_add, smul_eq_mul, add_sub_cancel, smul_sub,
  sub_le_iff_le_add, mul_inv_rev', mul_smul, ← smul_sub, ← smul_add, smul_smul, ← mul_inv_rev',
  smul_le_iff_of_pos (inv_pos.2 h), inv_inv', smul_smul,
  mul_inv_cancel_right' (right_ne_zero_of_mul h.ne'), smul_add,
  smul_inv_smul' (left_ne_zero_of_mul h.ne')]

lemma line_map_le_map_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
  line_map (f a) (f b) r ≤ f (line_map a b r) ↔ slope f a b ≤ slope f a (line_map a b r) :=
@map_le_line_map_iff_slope_le_slope_left k (order_dual E) _ _ _ f a b r h

lemma map_lt_line_map_iff_slope_lt_slope_left (h : 0 < r * (b - a)) :
  f (line_map a b r) < line_map (f a) (f b) r ↔ slope f a (line_map a b r) < slope f a b :=
lt_iff_lt_of_le_iff_le' (line_map_le_map_iff_slope_le_slope_left h)
  (map_le_line_map_iff_slope_le_slope_left h)

lemma line_map_lt_map_iff_slope_lt_slope_left (h : 0 < r * (b - a)) :
  line_map (f a) (f b) r < f (line_map a b r) ↔ slope f a b < slope f a (line_map a b r) :=
@map_lt_line_map_iff_slope_lt_slope_left k (order_dual E) _ _ _ f a b r h

lemma map_le_line_map_iff_slope_le_slope_right (h : (1 - r) * (b - a) < 0) :
  f (line_map a b r) ≤ line_map (f a) (f b) r ↔ slope f (line_map a b r) b ≤ slope f a b :=
begin
  rw [← neg_pos, neg_mul_eq_mul_neg, neg_sub] at h,
  rw [← line_map_apply_one_sub b, ← line_map_apply_one_sub (f b),
    map_le_line_map_iff_slope_le_slope_left h, slope_comm _ _ b, slope_comm _ _ b]
end

lemma line_map_le_map_iff_slope_le_slope_right (h : (1 - r) * (b - a) < 0) :
  line_map (f a) (f b) r ≤ f (line_map a b r) ↔ slope f a b ≤ slope f (line_map a b r) b :=
@map_le_line_map_iff_slope_le_slope_right k (order_dual E) _ _ _ f a b r h

lemma map_lt_line_map_iff_slope_lt_slope_right (h : (1 - r) * (b - a) < 0) :
  f (line_map a b r) < line_map (f a) (f b) r ↔ slope f (line_map a b r) b < slope f a b :=
lt_iff_lt_of_le_iff_le' (line_map_le_map_iff_slope_le_slope_right h)
  (map_le_line_map_iff_slope_le_slope_right h)

lemma line_map_lt_map_iff_slope_lt_slope_right (h : (1 - r) * (b - a) < 0) :
  line_map (f a) (f b) r < f (line_map a b r) ↔ slope f a b < slope f (line_map a b r) b :=
@map_lt_line_map_iff_slope_lt_slope_right k (order_dual E) _ _ _ f a b r h

lemma map_le_line_map_iff_slope_le_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
  f (line_map a b r) ≤ line_map (f a) (f b) r ↔
    slope f a (line_map a b r) ≤ slope f (line_map a b r) b :=
by rw [map_le_line_map_iff_slope_le_slope_left (mul_pos h₀ (sub_pos.2 hab)),
  ← line_map_slope_line_map_slope_line_map f a b r, right_le_line_map_iff_le h₁]

lemma line_map_le_map_iff_slope_le_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
  line_map (f a) (f b) r ≤ f (line_map a b r) ↔
    slope f (line_map a b r) b ≤ slope f a (line_map a b r) :=
@map_le_line_map_iff_slope_le_slope k (order_dual E) _ _ _ _ _ _ _ hab h₀ h₁

lemma map_lt_line_map_iff_slope_lt_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
  f (line_map a b r) < line_map (f a) (f b) r ↔
    slope f a (line_map a b r) < slope f (line_map a b r) b :=
lt_iff_lt_of_le_iff_le' (line_map_le_map_iff_slope_le_slope hab h₀ h₁)
  (map_le_line_map_iff_slope_le_slope hab h₀ h₁)

lemma line_map_lt_map_iff_slope_lt_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
  line_map (f a) (f b) r < f (line_map a b r) ↔
    slope f (line_map a b r) b < slope f a (line_map a b r) :=
@map_lt_line_map_iff_slope_lt_slope k (order_dual E) _ _ _ _ _ _ _ hab h₀ h₁

end linear_ordered_field
