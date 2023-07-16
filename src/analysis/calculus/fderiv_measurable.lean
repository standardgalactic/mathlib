/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import analysis.calculus.deriv
import measure_theory.constructions.borel_space
import measure_theory.function.strongly_measurable.basic
import tactic.ring_exp

/-!
# Derivative is measurable

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that the derivative of any function with complete codomain is a measurable
function. Namely, we prove:

* `measurable_set_of_differentiable_at`: the set `{x | differentiable_at 𝕜 f x}` is measurable;
* `measurable_fderiv`: the function `fderiv 𝕜 f` is measurable;
* `measurable_fderiv_apply_const`: for a fixed vector `y`, the function `λ x, fderiv 𝕜 f x y`
  is measurable;
* `measurable_deriv`: the function `deriv f` is measurable (for `f : 𝕜 → F`).

We also show the same results for the right derivative on the real line
(see `measurable_deriv_within_Ici` and ``measurable_deriv_within_Ioi`), following the same
proof strategy.

## Implementation

We give a proof that avoids second-countability issues, by expressing the differentiability set
as a function of open sets in the following way. Define `A (L, r, ε)` to be the set of points
where, on a ball of radius roughly `r` around `x`, the function is uniformly approximated by the
linear map `L`, up to `ε r`. It is an open set.
Let also `B (L, r, s, ε) = A (L, r, ε) ∩ A (L, s, ε)`: we require that at two possibly different
scales `r` and `s`, the function is well approximated by the linear map `L`. It is also open.

We claim that the differentiability set of `f` is exactly
`D = ⋂ ε > 0, ⋃ δ > 0, ⋂ r, s < δ, ⋃ L, B (L, r, s, ε)`.
In other words, for any `ε > 0`, we require that there is a size `δ` such that, for any two scales
below this size, the function is well approximated by a linear map, common to the two scales.

The set `⋃ L, B (L, r, s, ε)` is open, as a union of open sets. Converting the intersections and
unions to countable ones (using real numbers of the form `2 ^ (-n)`), it follows that the
differentiability set is measurable.

To prove the claim, there are two inclusions. One is trivial: if the function is differentiable
at `x`, then `x` belongs to `D` (just take `L` to be the derivative, and use that the
differentiability exactly says that the map is well approximated by `L`). This is proved in
`mem_A_of_differentiable` and `differentiable_set_subset_D`.

For the other direction, the difficulty is that `L` in the union may depend on `ε, r, s`. The key
point is that, in fact, it doesn't depend too much on them. First, if `x` belongs both to
`A (L, r, ε)` and `A (L', r, ε)`, then `L` and `L'` have to be close on a shell, and thus
`‖L - L'‖` is bounded by `ε` (see `norm_sub_le_of_mem_A`). Assume now `x ∈ D`. If one has two maps
`L` and `L'` such that `x` belongs to `A (L, r, ε)` and to `A (L', r', ε')`, one deduces that `L` is
close to `L'` by arguing as follows. Consider another scale `s` smaller than `r` and `r'`. Take a
linear map `L₁` that approximates `f` around `x` both at scales `r` and `s` w.r.t. `ε` (it exists as
`x` belongs to `D`). Take also `L₂` that approximates `f` around `x` both at scales `r'` and `s`
w.r.t. `ε'`. Then `L₁` is close to `L` (as they are close on a shell of radius `r`), and `L₂` is
close to `L₁` (as they are close on a shell of radius `s`), and `L'` is close to `L₂` (as they are
close on a shell of radius `r'`). It follows that `L` is close to `L'`, as we claimed.

It follows that the different approximating linear maps that show up form a Cauchy sequence when
`ε` tends to `0`. When the target space is complete, this sequence converges, to a limit `f'`.
With the same kind of arguments, one checks that `f` is differentiable with derivative `f'`.

To show that the derivative itself is measurable, add in the definition of `B` and `D` a set
`K` of continuous linear maps to which `L` should belong. Then, when `K` is complete, the set `D K`
is exactly the set of points where `f` is differentiable with a derivative in `K`.

## Tags

derivative, measurable function, Borel σ-algebra
-/

noncomputable theory

open set metric asymptotics filter continuous_linear_map
open topological_space (second_countable_topology) measure_theory
open_locale topology

namespace continuous_linear_map

variables {𝕜 E F : Type*} [nontrivially_normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E] [normed_add_comm_group F] [normed_space 𝕜 F]

lemma measurable_apply₂ [measurable_space E] [opens_measurable_space E]
  [second_countable_topology E] [second_countable_topology (E →L[𝕜] F)]
  [measurable_space F] [borel_space F] :
  measurable (λ p : (E →L[𝕜] F) × E, p.1 p.2) :=
is_bounded_bilinear_map_apply.continuous.measurable

end continuous_linear_map

section fderiv

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {f : E → F} (K : set (E →L[𝕜] F))

namespace fderiv_measurable_aux

/-- The set `A f L r ε` is the set of points `x` around which the function `f` is well approximated
at scale `r` by the linear map `L`, up to an error `ε`. We tweak the definition to make sure that
this is an open set.-/
def A (f : E → F) (L : E →L[𝕜] F) (r ε : ℝ) : set E :=
{x | ∃ r' ∈ Ioc (r/2) r, ∀ y z ∈ ball x r', ‖f z - f y - L (z-y)‖ ≤ ε * r}

/-- The set `B f K r s ε` is the set of points `x` around which there exists a continuous linear map
`L` belonging to `K` (a given set of continuous linear maps) that approximates well the
function `f` (up to an error `ε`), simultaneously at scales `r` and `s`. -/
def B (f : E → F) (K : set (E →L[𝕜] F)) (r s ε : ℝ) : set E :=
⋃ (L ∈ K), (A f L r ε) ∩ (A f L s ε)

/-- The set `D f K` is a complicated set constructed using countable intersections and unions. Its
main use is that, when `K` is complete, it is exactly the set of points where `f` is differentiable,
with a derivative in `K`. -/
def D (f : E → F) (K : set (E →L[𝕜] F)) : set E :=
⋂ (e : ℕ), ⋃ (n : ℕ), ⋂ (p ≥ n) (q ≥ n), B f K ((1/2) ^ p) ((1/2) ^ q) ((1/2) ^ e)

lemma is_open_A (L : E →L[𝕜] F) (r ε : ℝ) : is_open (A f L r ε) :=
begin
  rw metric.is_open_iff,
  rintros x ⟨r', r'_mem, hr'⟩,
  obtain ⟨s, s_gt, s_lt⟩ : ∃ (s : ℝ), r / 2 < s ∧ s < r' := exists_between r'_mem.1,
  have : s ∈ Ioc (r/2) r := ⟨s_gt, le_of_lt (s_lt.trans_le r'_mem.2)⟩,
  refine ⟨r' - s, by linarith, λ x' hx', ⟨s, this, _⟩⟩,
  have B : ball x' s ⊆ ball x r' := ball_subset (le_of_lt hx'),
  assume y hy z hz,
  exact hr' y (B hy) z (B hz)
end

lemma is_open_B {K : set (E →L[𝕜] F)} {r s ε : ℝ} : is_open (B f K r s ε) :=
by simp [B, is_open_Union, is_open.inter, is_open_A]

lemma A_mono (L : E →L[𝕜] F) (r : ℝ) {ε δ : ℝ} (h : ε ≤ δ) :
  A f L r ε ⊆ A f L r δ :=
begin
  rintros x ⟨r', r'r, hr'⟩,
  refine ⟨r', r'r, λ y hy z hz, (hr' y hy z hz).trans (mul_le_mul_of_nonneg_right h _)⟩,
  linarith [mem_ball.1 hy, r'r.2, @dist_nonneg _ _ y x],
end

lemma le_of_mem_A {r ε : ℝ} {L : E →L[𝕜] F} {x : E} (hx : x ∈ A f L r ε)
  {y z : E} (hy : y ∈ closed_ball x (r/2)) (hz : z ∈ closed_ball x (r/2)) :
  ‖f z - f y - L (z-y)‖ ≤ ε * r :=
begin
  rcases hx with ⟨r', r'mem, hr'⟩,
  exact hr' _ ((mem_closed_ball.1 hy).trans_lt r'mem.1) _ ((mem_closed_ball.1 hz).trans_lt r'mem.1)
end

lemma mem_A_of_differentiable {ε : ℝ} (hε : 0 < ε) {x : E} (hx : differentiable_at 𝕜 f x) :
  ∃ R > 0, ∀ r ∈ Ioo (0 : ℝ) R, x ∈ A f (fderiv 𝕜 f x) r ε :=
begin
  have := hx.has_fderiv_at,
  simp only [has_fderiv_at, has_fderiv_at_filter, is_o_iff] at this,
  rcases eventually_nhds_iff_ball.1 (this (half_pos hε)) with ⟨R, R_pos, hR⟩,
  refine ⟨R, R_pos, λ r hr, _⟩,
  have : r ∈ Ioc (r/2) r := ⟨half_lt_self hr.1, le_rfl⟩,
  refine ⟨r, this, λ y hy z hz, _⟩,
  calc  ‖f z - f y - (fderiv 𝕜 f x) (z - y)‖
      = ‖(f z - f x - (fderiv 𝕜 f x) (z - x)) - (f y - f x - (fderiv 𝕜 f x) (y - x))‖ :
    by { congr' 1, simp only [continuous_linear_map.map_sub], abel }
  ... ≤ ‖(f z - f x - (fderiv 𝕜 f x) (z - x))‖ + ‖f y - f x - (fderiv 𝕜 f x) (y - x)‖ :
    norm_sub_le _ _
  ... ≤ ε / 2 * ‖z - x‖ + ε / 2 * ‖y - x‖ :
    add_le_add (hR _ (lt_trans (mem_ball.1 hz) hr.2)) (hR _ (lt_trans (mem_ball.1 hy) hr.2))
  ... ≤ ε / 2 * r + ε / 2 * r :
    add_le_add
      (mul_le_mul_of_nonneg_left (le_of_lt (mem_ball_iff_norm.1 hz)) (le_of_lt (half_pos hε)))
      (mul_le_mul_of_nonneg_left (le_of_lt (mem_ball_iff_norm.1 hy)) (le_of_lt (half_pos hε)))
  ... = ε * r : by ring
end

lemma norm_sub_le_of_mem_A {c : 𝕜} (hc : 1 < ‖c‖)
  {r ε : ℝ} (hε : 0 < ε) (hr : 0 < r) {x : E} {L₁ L₂ : E →L[𝕜] F}
  (h₁ : x ∈ A f L₁ r ε) (h₂ : x ∈ A f L₂ r ε) : ‖L₁ - L₂‖ ≤ 4 * ‖c‖ * ε :=
begin
  have : 0 ≤ 4 * ‖c‖ * ε :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (norm_nonneg _)) hε.le,
  refine op_norm_le_of_shell (half_pos hr) this hc _,
  assume y ley ylt,
  rw [div_div,
      div_le_iff' (mul_pos (by norm_num : (0 : ℝ) < 2) (zero_lt_one.trans hc))] at ley,
  calc ‖(L₁ - L₂) y‖
        = ‖(f (x + y) - f x - L₂ ((x + y) - x)) - (f (x + y) - f x - L₁ ((x + y) - x))‖ : by simp
    ... ≤ ‖(f (x + y) - f x - L₂ ((x + y) - x))‖ + ‖(f (x + y) - f x - L₁ ((x + y) - x))‖ :
      norm_sub_le _ _
    ... ≤ ε * r + ε * r :
      begin
        apply add_le_add,
        { apply le_of_mem_A h₂,
          { simp only [le_of_lt (half_pos hr), mem_closed_ball, dist_self] },
          { simp only [dist_eq_norm, add_sub_cancel', mem_closed_ball, ylt.le], } },
        { apply le_of_mem_A h₁,
          { simp only [le_of_lt (half_pos hr), mem_closed_ball, dist_self] },
          { simp only [dist_eq_norm, add_sub_cancel', mem_closed_ball, ylt.le] } },
      end
    ... = 2 * ε * r : by ring
    ... ≤ 2 * ε * (2 * ‖c‖ * ‖y‖) : mul_le_mul_of_nonneg_left ley (mul_nonneg (by norm_num) hε.le)
    ... = 4 * ‖c‖ * ε * ‖y‖ : by ring
end

/-- Easy inclusion: a differentiability point with derivative in `K` belongs to `D f K`. -/
lemma differentiable_set_subset_D : {x | differentiable_at 𝕜 f x ∧ fderiv 𝕜 f x ∈ K} ⊆ D f K :=
begin
  assume x hx,
  rw [D, mem_Inter],
  assume e,
  have : (0 : ℝ) < (1/2) ^ e := pow_pos (by norm_num) _,
  rcases mem_A_of_differentiable this hx.1 with ⟨R, R_pos, hR⟩,
  obtain ⟨n, hn⟩ : ∃ (n : ℕ), (1/2) ^ n < R :=
    exists_pow_lt_of_lt_one R_pos (by norm_num : (1 : ℝ)/2 < 1),
  simp only [mem_Union, mem_Inter, B, mem_inter_iff],
  refine ⟨n, λ p hp q hq, ⟨fderiv 𝕜 f x, hx.2, ⟨_, _⟩⟩⟩;
  { refine hR _ ⟨pow_pos (by norm_num) _, lt_of_le_of_lt _ hn⟩,
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by assumption) }
end

/-- Harder inclusion: at a point in `D f K`, the function `f` has a derivative, in `K`. -/
lemma D_subset_differentiable_set {K : set (E →L[𝕜] F)} (hK : is_complete K) :
  D f K ⊆ {x | differentiable_at 𝕜 f x ∧ fderiv 𝕜 f x ∈ K} :=
begin
  have P : ∀ {n : ℕ}, (0 : ℝ) < (1/2) ^ n := pow_pos (by norm_num),
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  have cpos : 0 < ‖c‖ := lt_trans zero_lt_one hc,
  assume x hx,
  have : ∀ (e : ℕ), ∃ (n : ℕ), ∀ p q, n ≤ p → n ≤ q → ∃ L ∈ K,
    x ∈ A f L ((1/2) ^ p) ((1/2) ^ e) ∩ A f L ((1/2) ^ q) ((1/2) ^ e),
  { assume e,
    have := mem_Inter.1 hx e,
    rcases mem_Union.1 this with ⟨n, hn⟩,
    refine ⟨n, λ p q hp hq, _⟩,
    simp only [mem_Inter, ge_iff_le] at hn,
    rcases mem_Union.1 (hn p hp q hq) with ⟨L, hL⟩,
    exact ⟨L, mem_Union.1 hL⟩, },
  /- Recast the assumptions: for each `e`, there exist `n e` and linear maps `L e p q` in `K`
  such that, for `p, q ≥ n e`, then `f` is well approximated by `L e p q` at scale `2 ^ (-p)` and
  `2 ^ (-q)`, with an error `2 ^ (-e)`. -/
  choose! n L hn using this,
  /- All the operators `L e p q` that show up are close to each other. To prove this, we argue
    that `L e p q` is close to `L e p r` (where `r` is large enough), as both approximate `f` at
    scale `2 ^(- p)`. And `L e p r` is close to `L e' p' r` as both approximate `f` at scale
    `2 ^ (- r)`. And `L e' p' r` is close to `L e' p' q'` as both approximate `f` at scale
    `2 ^ (- p')`. -/
  have M : ∀ e p q e' p' q', n e ≤ p → n e ≤ q → n e' ≤ p' → n e' ≤ q' → e ≤ e' →
    ‖L e p q - L e' p' q'‖ ≤ 12 * ‖c‖ * (1/2) ^ e,
  { assume e p q e' p' q' hp hq hp' hq' he',
    let r := max (n e) (n e'),
    have I : ((1:ℝ)/2)^e' ≤ (1/2)^e := pow_le_pow_of_le_one (by norm_num) (by norm_num) he',
    have J1 : ‖L e p q - L e p r‖ ≤ 4 * ‖c‖ * (1/2)^e,
    { have I1 : x ∈ A f (L e p q) ((1 / 2) ^ p) ((1/2)^e) :=
        (hn e p q hp hq).2.1,
      have I2 : x ∈ A f (L e p r) ((1 / 2) ^ p) ((1/2)^e) :=
        (hn e p r hp (le_max_left _ _)).2.1,
      exact norm_sub_le_of_mem_A hc P P I1 I2 },
    have J2 : ‖L e p r - L e' p' r‖ ≤ 4 * ‖c‖ * (1/2)^e,
    { have I1 : x ∈ A f (L e p r) ((1 / 2) ^ r) ((1/2)^e) :=
        (hn e p r hp (le_max_left _ _)).2.2,
      have I2 : x ∈ A f (L e' p' r) ((1 / 2) ^ r) ((1/2)^e') :=
        (hn e' p' r hp' (le_max_right _ _)).2.2,
      exact norm_sub_le_of_mem_A hc P P I1 (A_mono _ _ I I2) },
    have J3 : ‖L e' p' r - L e' p' q'‖ ≤ 4 * ‖c‖ * (1/2)^e,
    { have I1 : x ∈ A f (L e' p' r) ((1 / 2) ^ p') ((1/2)^e') :=
        (hn e' p' r hp' (le_max_right _ _)).2.1,
      have I2 : x ∈ A f (L e' p' q') ((1 / 2) ^ p') ((1/2)^e') :=
        (hn e' p' q' hp' hq').2.1,
      exact norm_sub_le_of_mem_A hc P P (A_mono _ _ I I1) (A_mono _ _ I I2) },
    calc ‖L e p q - L e' p' q'‖
          = ‖(L e p q - L e p r) + (L e p r - L e' p' r) + (L e' p' r - L e' p' q')‖ :
        by { congr' 1, abel }
      ... ≤ ‖L e p q - L e p r‖ + ‖L e p r - L e' p' r‖ + ‖L e' p' r - L e' p' q'‖ :
        le_trans (norm_add_le _ _) (add_le_add_right (norm_add_le _ _) _)
      ... ≤ 4 * ‖c‖ * (1/2)^e + 4 * ‖c‖ * (1/2)^e + 4 * ‖c‖ * (1/2)^e :
        by apply_rules [add_le_add]
      ... = 12 * ‖c‖ * (1/2)^e : by ring },
  /- For definiteness, use `L0 e = L e (n e) (n e)`, to have a single sequence. We claim that this
  is a Cauchy sequence. -/
  let L0 : ℕ → (E →L[𝕜] F) := λ e, L e (n e) (n e),
  have : cauchy_seq L0,
  { rw metric.cauchy_seq_iff',
    assume ε εpos,
    obtain ⟨e, he⟩ : ∃ (e : ℕ), (1/2) ^ e < ε / (12 * ‖c‖) :=
      exists_pow_lt_of_lt_one (div_pos εpos (mul_pos (by norm_num) cpos)) (by norm_num),
    refine ⟨e, λ e' he', _⟩,
    rw [dist_comm, dist_eq_norm],
    calc ‖L0 e - L0 e'‖
          ≤ 12 * ‖c‖ * (1/2)^e : M _ _ _ _ _ _ le_rfl le_rfl le_rfl le_rfl he'
      ... < 12 * ‖c‖ * (ε / (12 * ‖c‖)) :
        mul_lt_mul' le_rfl he (le_of_lt P) (mul_pos (by norm_num) cpos)
      ... = ε : by { field_simp [(by norm_num : (12 : ℝ) ≠ 0), ne_of_gt cpos], ring } },
  /- As it is Cauchy, the sequence `L0` converges, to a limit `f'` in `K`.-/
  obtain ⟨f', f'K, hf'⟩ : ∃ f' ∈ K, tendsto L0 at_top (𝓝 f') :=
    cauchy_seq_tendsto_of_is_complete hK (λ e, (hn e (n e) (n e) le_rfl le_rfl).1) this,
  have Lf' : ∀ e p, n e ≤ p → ‖L e (n e) p - f'‖ ≤ 12 * ‖c‖ * (1/2)^e,
  { assume e p hp,
    apply le_of_tendsto (tendsto_const_nhds.sub hf').norm,
    rw eventually_at_top,
    exact ⟨e, λ e' he', M _ _ _ _ _ _ le_rfl hp le_rfl le_rfl he'⟩ },
  /- Let us show that `f` has derivative `f'` at `x`. -/
  have : has_fderiv_at f f' x,
  { simp only [has_fderiv_at_iff_is_o_nhds_zero, is_o_iff],
    /- to get an approximation with a precision `ε`, we will replace `f` with `L e (n e) m` for
    some large enough `e` (yielding a small error by uniform approximation). As one can vary `m`,
    this makes it possible to cover all scales, and thus to obtain a good linear approximation in
    the whole ball of radius `(1/2)^(n e)`. -/
    assume ε εpos,
    have pos : 0 < 4 + 12 * ‖c‖ :=
      add_pos_of_pos_of_nonneg (by norm_num) (mul_nonneg (by norm_num) (norm_nonneg _)),
    obtain ⟨e, he⟩ : ∃ (e : ℕ), (1 / 2) ^ e < ε / (4 + 12 * ‖c‖) :=
      exists_pow_lt_of_lt_one (div_pos εpos pos) (by norm_num),
    rw eventually_nhds_iff_ball,
    refine ⟨(1/2) ^ (n e + 1), P, λ y hy, _⟩,
    -- We need to show that `f (x + y) - f x - f' y` is small. For this, we will work at scale
    -- `k` where `k` is chosen with `‖y‖ ∼ 2 ^ (-k)`.
    by_cases y_pos : y = 0, {simp [y_pos] },
    have yzero : 0 < ‖y‖ := norm_pos_iff.mpr y_pos,
    have y_lt : ‖y‖ < (1/2) ^ (n e + 1), by simpa using mem_ball_iff_norm.1 hy,
    have yone : ‖y‖ ≤ 1 :=
      le_trans (y_lt.le) (pow_le_one _ (by norm_num) (by norm_num)),
    -- define the scale `k`.
    obtain ⟨k, hk, h'k⟩ : ∃ (k : ℕ), (1/2) ^ (k + 1) < ‖y‖ ∧ ‖y‖ ≤ (1/2) ^ k :=
      exists_nat_pow_near_of_lt_one yzero yone (by norm_num : (0 : ℝ) < 1/2)
      (by norm_num : (1 : ℝ)/2 < 1),
    -- the scale is large enough (as `y` is small enough)
    have k_gt : n e < k,
    { have : ((1:ℝ)/2) ^ (k + 1) < (1/2) ^ (n e + 1) := lt_trans hk y_lt,
      rw pow_lt_pow_iff_of_lt_one (by norm_num : (0 : ℝ) < 1/2) (by norm_num) at this,
      linarith },
    set m := k - 1 with hl,
    have m_ge : n e ≤ m := nat.le_pred_of_lt k_gt,
    have km : k = m + 1 := (nat.succ_pred_eq_of_pos (lt_of_le_of_lt (zero_le _) k_gt)).symm,
    rw km at hk h'k,
    -- `f` is well approximated by `L e (n e) k` at the relevant scale
    -- (in fact, we use `m = k - 1` instead of `k` because of the precise definition of `A`).
    have J1 : ‖f (x + y) - f x - L e (n e) m ((x + y) - x)‖ ≤ (1/2) ^ e * (1/2) ^ m,
    { apply le_of_mem_A (hn e (n e) m le_rfl m_ge).2.2,
      { simp only [mem_closed_ball, dist_self],
        exact div_nonneg (le_of_lt P) (zero_le_two) },
      { simpa only [dist_eq_norm, add_sub_cancel', mem_closed_ball, pow_succ', mul_one_div]
          using h'k } },
    have J2 : ‖f (x + y) - f x - L e (n e) m y‖ ≤ 4 * (1/2) ^ e * ‖y‖ := calc
      ‖f (x + y) - f x - L e (n e) m y‖ ≤ (1/2) ^ e * (1/2) ^ m :
        by simpa only [add_sub_cancel'] using J1
      ... = 4 * (1/2) ^ e * (1/2) ^ (m + 2) : by { field_simp, ring_exp }
      ... ≤ 4 * (1/2) ^ e * ‖y‖ :
        mul_le_mul_of_nonneg_left (le_of_lt hk) (mul_nonneg (by norm_num) (le_of_lt P)),
    -- use the previous estimates to see that `f (x + y) - f x - f' y` is small.
    calc ‖f (x + y) - f x - f' y‖
        = ‖(f (x + y) - f x - L e (n e) m y) + (L e (n e) m - f') y‖ :
      congr_arg _ (by simp)
    ... ≤ 4 * (1/2) ^ e * ‖y‖ + 12 * ‖c‖ * (1/2) ^ e * ‖y‖ :
      norm_add_le_of_le J2
        ((le_op_norm _ _).trans (mul_le_mul_of_nonneg_right (Lf' _ _ m_ge) (norm_nonneg _)))
    ... = (4 + 12 * ‖c‖) * ‖y‖ * (1/2) ^ e : by ring
    ... ≤ (4 + 12 * ‖c‖) * ‖y‖ * (ε / (4 + 12 * ‖c‖)) :
      mul_le_mul_of_nonneg_left he.le
        (mul_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) (norm_nonneg _)))
          (norm_nonneg _))
    ... = ε * ‖y‖ : by { field_simp [ne_of_gt pos], ring } },
  rw ← this.fderiv at f'K,
  exact ⟨this.differentiable_at, f'K⟩
end

theorem differentiable_set_eq_D (hK : is_complete K) :
  {x | differentiable_at 𝕜 f x ∧ fderiv 𝕜 f x ∈ K} = D f K :=
subset.antisymm (differentiable_set_subset_D _) (D_subset_differentiable_set hK)

end fderiv_measurable_aux

open fderiv_measurable_aux

variables [measurable_space E] [opens_measurable_space E]
variables (𝕜 f)

/-- The set of differentiability points of a function, with derivative in a given complete set,
is Borel-measurable. -/
theorem measurable_set_of_differentiable_at_of_is_complete
  {K : set (E →L[𝕜] F)} (hK : is_complete K) :
  measurable_set {x | differentiable_at 𝕜 f x ∧ fderiv 𝕜 f x ∈ K} :=
by simp [differentiable_set_eq_D K hK, D, is_open_B.measurable_set, measurable_set.Inter,
         measurable_set.Union]

variable [complete_space F]

/-- The set of differentiability points of a function taking values in a complete space is
Borel-measurable. -/
theorem measurable_set_of_differentiable_at :
  measurable_set {x | differentiable_at 𝕜 f x} :=
begin
  have : is_complete (univ : set (E →L[𝕜] F)) := complete_univ,
  convert measurable_set_of_differentiable_at_of_is_complete 𝕜 f this,
  simp
end

@[measurability] lemma measurable_fderiv : measurable (fderiv 𝕜 f) :=
begin
  refine measurable_of_is_closed (λ s hs, _),
  have : fderiv 𝕜 f ⁻¹' s = {x | differentiable_at 𝕜 f x ∧ fderiv 𝕜 f x ∈ s} ∪
    ({x | ¬differentiable_at 𝕜 f x} ∩ {x | (0 : E →L[𝕜] F) ∈ s}) :=
    set.ext (λ x, mem_preimage.trans fderiv_mem_iff),
  rw this,
  exact (measurable_set_of_differentiable_at_of_is_complete _ _ hs.is_complete).union
    ((measurable_set_of_differentiable_at _ _).compl.inter (measurable_set.const _))
end

@[measurability] lemma measurable_fderiv_apply_const [measurable_space F] [borel_space F] (y : E) :
  measurable (λ x, fderiv 𝕜 f x y) :=
(continuous_linear_map.measurable_apply y).comp (measurable_fderiv 𝕜 f)

variable {𝕜}

@[measurability] lemma measurable_deriv [measurable_space 𝕜] [opens_measurable_space 𝕜]
  [measurable_space F] [borel_space F] (f : 𝕜 → F) : measurable (deriv f) :=
by simpa only [fderiv_deriv] using measurable_fderiv_apply_const 𝕜 f 1

lemma strongly_measurable_deriv [measurable_space 𝕜] [opens_measurable_space 𝕜]
  [second_countable_topology F] (f : 𝕜 → F) :
  strongly_measurable (deriv f) :=
by { borelize F, exact (measurable_deriv f).strongly_measurable }

lemma ae_measurable_deriv [measurable_space 𝕜] [opens_measurable_space 𝕜] [measurable_space F]
  [borel_space F] (f : 𝕜 → F) (μ : measure 𝕜) : ae_measurable (deriv f) μ :=
(measurable_deriv f).ae_measurable

lemma ae_strongly_measurable_deriv [measurable_space 𝕜] [opens_measurable_space 𝕜]
  [second_countable_topology F] (f : 𝕜 → F) (μ : measure 𝕜) :
  ae_strongly_measurable (deriv f) μ :=
(strongly_measurable_deriv f).ae_strongly_measurable

end fderiv

section right_deriv

variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
variables {f : ℝ → F} (K : set F)

namespace right_deriv_measurable_aux

/-- The set `A f L r ε` is the set of points `x` around which the function `f` is well approximated
at scale `r` by the linear map `h ↦ h • L`, up to an error `ε`. We tweak the definition to
make sure that this is open on the right. -/
def A (f : ℝ → F) (L : F) (r ε : ℝ) : set ℝ :=
{x | ∃ r' ∈ Ioc (r/2) r, ∀ y z ∈ Icc x (x + r'), ‖f z - f y - (z-y) • L‖ ≤ ε * r}

/-- The set `B f K r s ε` is the set of points `x` around which there exists a vector
`L` belonging to `K` (a given set of vectors) such that `h • L` approximates well `f (x + h)`
(up to an error `ε`), simultaneously at scales `r` and `s`. -/
def B (f : ℝ → F) (K : set F) (r s ε : ℝ) : set ℝ :=
⋃ (L ∈ K), (A f L r ε) ∩ (A f L s ε)

/-- The set `D f K` is a complicated set constructed using countable intersections and unions. Its
main use is that, when `K` is complete, it is exactly the set of points where `f` is differentiable,
with a derivative in `K`. -/
def D (f : ℝ → F) (K : set F) : set ℝ :=
⋂ (e : ℕ), ⋃ (n : ℕ), ⋂ (p ≥ n) (q ≥ n), B f K ((1/2) ^ p) ((1/2) ^ q) ((1/2) ^ e)

lemma A_mem_nhds_within_Ioi {L : F} {r ε x : ℝ} (hx : x ∈ A f L r ε) :
  A f L r ε ∈ 𝓝[>] x :=
begin
  rcases hx with ⟨r', rr', hr'⟩,
  rw mem_nhds_within_Ioi_iff_exists_Ioo_subset,
  obtain ⟨s, s_gt, s_lt⟩ : ∃ (s : ℝ), r / 2 < s ∧ s < r' := exists_between rr'.1,
  have : s ∈ Ioc (r/2) r := ⟨s_gt, le_of_lt (s_lt.trans_le rr'.2)⟩,
  refine ⟨x + r' - s, by { simp only [mem_Ioi], linarith }, λ x' hx', ⟨s, this, _⟩⟩,
  have A : Icc x' (x' + s) ⊆ Icc x (x + r'),
  { apply Icc_subset_Icc hx'.1.le,
    linarith [hx'.2] },
  assume y hy z hz,
  exact hr' y (A hy) z (A hz)
end

lemma B_mem_nhds_within_Ioi {K : set F} {r s ε x : ℝ} (hx : x ∈ B f K r s ε) :
  B f K r s ε ∈ 𝓝[>] x :=
begin
  obtain ⟨L, LK, hL₁, hL₂⟩ : ∃ (L : F), L ∈ K ∧ x ∈ A f L r ε ∧ x ∈ A f L s ε,
    by simpa only [B, mem_Union, mem_inter_iff, exists_prop] using hx,
  filter_upwards [A_mem_nhds_within_Ioi hL₁, A_mem_nhds_within_Ioi hL₂] with y hy₁ hy₂,
  simp only [B, mem_Union, mem_inter_iff, exists_prop],
  exact ⟨L, LK, hy₁, hy₂⟩
end

lemma measurable_set_B {K : set F} {r s ε : ℝ} : measurable_set (B f K r s ε) :=
measurable_set_of_mem_nhds_within_Ioi (λ x hx, B_mem_nhds_within_Ioi hx)

lemma A_mono (L : F) (r : ℝ) {ε δ : ℝ} (h : ε ≤ δ) :
  A f L r ε ⊆ A f L r δ :=
begin
  rintros x ⟨r', r'r, hr'⟩,
  refine ⟨r', r'r, λ y hy z hz, (hr' y hy z hz).trans (mul_le_mul_of_nonneg_right h _)⟩,
  linarith [hy.1, hy.2, r'r.2],
end

lemma le_of_mem_A {r ε : ℝ} {L : F} {x : ℝ} (hx : x ∈ A f L r ε)
  {y z : ℝ} (hy : y ∈ Icc x (x + r/2)) (hz : z ∈ Icc x (x + r/2)) :
  ‖f z - f y - (z-y) • L‖ ≤ ε * r :=
begin
  rcases hx with ⟨r', r'mem, hr'⟩,
  have A : x + r / 2 ≤ x + r', by linarith [r'mem.1],
  exact hr' _ ((Icc_subset_Icc le_rfl A) hy) _ ((Icc_subset_Icc le_rfl A) hz),
end

lemma mem_A_of_differentiable {ε : ℝ} (hε : 0 < ε) {x : ℝ}
  (hx : differentiable_within_at ℝ f (Ici x) x) :
  ∃ R > 0, ∀ r ∈ Ioo (0 : ℝ) R, x ∈ A f (deriv_within f (Ici x) x) r ε :=
begin
  have := hx.has_deriv_within_at,
  simp_rw [has_deriv_within_at_iff_is_o, is_o_iff] at this,
  rcases mem_nhds_within_Ici_iff_exists_Ico_subset.1 (this (half_pos hε)) with ⟨m, xm, hm⟩,
  refine ⟨m - x, by linarith [show x < m, from xm], λ r hr, _⟩,
  have : r ∈ Ioc (r/2) r := ⟨half_lt_self hr.1, le_rfl⟩,
  refine ⟨r, this, λ y hy z hz, _⟩,
  calc  ‖f z - f y - (z - y) • deriv_within f (Ici x) x‖
      = ‖(f z - f x - (z - x) • deriv_within f (Ici x) x)
           - (f y - f x - (y - x) • deriv_within f (Ici x) x)‖ :
    by { congr' 1, simp only [sub_smul], abel }
  ... ≤ ‖f z - f x - (z - x) • deriv_within f (Ici x) x‖
         + ‖f y - f x - (y - x) • deriv_within f (Ici x) x‖ :
    norm_sub_le _ _
  ... ≤ ε / 2 * ‖z - x‖ + ε / 2 * ‖y - x‖ :
    add_le_add (hm ⟨hz.1, hz.2.trans_lt (by linarith [hr.2])⟩)
               (hm ⟨hy.1, hy.2.trans_lt (by linarith [hr.2])⟩)
  ... ≤ ε / 2 * r + ε / 2 * r :
  begin
    apply add_le_add,
    { apply mul_le_mul_of_nonneg_left _ (le_of_lt (half_pos hε)),
      rw [real.norm_of_nonneg];
      linarith [hz.1, hz.2] },
    { apply mul_le_mul_of_nonneg_left _ (le_of_lt (half_pos hε)),
      rw [real.norm_of_nonneg];
      linarith [hy.1, hy.2] },
   end
  ... = ε * r : by ring
end

lemma norm_sub_le_of_mem_A
  {r x : ℝ} (hr : 0 < r) (ε : ℝ) {L₁ L₂ : F}
  (h₁ : x ∈ A f L₁ r ε) (h₂ : x ∈ A f L₂ r ε) : ‖L₁ - L₂‖ ≤ 4 * ε :=
begin
  suffices H : ‖(r/2) • (L₁ - L₂)‖ ≤ (r / 2) * (4 * ε),
    by rwa [norm_smul, real.norm_of_nonneg (half_pos hr).le, mul_le_mul_left (half_pos hr)] at H,
  calc
  ‖(r/2) • (L₁ - L₂)‖
      = ‖(f (x + r/2) - f x - (x + r/2 - x) • L₂) - (f (x + r/2) - f x - (x + r/2 - x) • L₁)‖ :
    by simp [smul_sub]
  ... ≤ ‖f (x + r/2) - f x - (x + r/2 - x) • L₂‖ + ‖f (x + r/2) - f x - (x + r/2 - x) • L₁‖ :
    norm_sub_le _ _
  ... ≤ ε * r + ε * r :
    begin
      apply add_le_add,
      { apply le_of_mem_A h₂;
        simp [(half_pos hr).le] },
      { apply le_of_mem_A h₁;
        simp [(half_pos hr).le] },
    end
  ... = (r / 2) * (4 * ε) : by ring
end

/-- Easy inclusion: a differentiability point with derivative in `K` belongs to `D f K`. -/
lemma differentiable_set_subset_D :
  {x | differentiable_within_at ℝ f (Ici x) x ∧ deriv_within f (Ici x) x ∈ K} ⊆ D f K :=
begin
  assume x hx,
  rw [D, mem_Inter],
  assume e,
  have : (0 : ℝ) < (1/2) ^ e := pow_pos (by norm_num) _,
  rcases mem_A_of_differentiable this hx.1 with ⟨R, R_pos, hR⟩,
  obtain ⟨n, hn⟩ : ∃ (n : ℕ), (1/2) ^ n < R :=
    exists_pow_lt_of_lt_one R_pos (by norm_num : (1 : ℝ)/2 < 1),
  simp only [mem_Union, mem_Inter, B, mem_inter_iff],
  refine ⟨n, λ p hp q hq, ⟨deriv_within f (Ici x) x, hx.2, ⟨_, _⟩⟩⟩;
  { refine hR _ ⟨pow_pos (by norm_num) _, lt_of_le_of_lt _ hn⟩,
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by assumption) }
end

/-- Harder inclusion: at a point in `D f K`, the function `f` has a derivative, in `K`. -/
lemma D_subset_differentiable_set {K : set F} (hK : is_complete K) :
  D f K ⊆ {x | differentiable_within_at ℝ f (Ici x) x ∧ deriv_within f (Ici x) x ∈ K} :=
begin
  have P : ∀ {n : ℕ}, (0 : ℝ) < (1/2) ^ n := pow_pos (by norm_num),
  assume x hx,
  have : ∀ (e : ℕ), ∃ (n : ℕ), ∀ p q, n ≤ p → n ≤ q → ∃ L ∈ K,
    x ∈ A f L ((1/2) ^ p) ((1/2) ^ e) ∩ A f L ((1/2) ^ q) ((1/2) ^ e),
  { assume e,
    have := mem_Inter.1 hx e,
    rcases mem_Union.1 this with ⟨n, hn⟩,
    refine ⟨n, λ p q hp hq, _⟩,
    simp only [mem_Inter, ge_iff_le] at hn,
    rcases mem_Union.1 (hn p hp q hq) with ⟨L, hL⟩,
    exact ⟨L, mem_Union.1 hL⟩, },
  /- Recast the assumptions: for each `e`, there exist `n e` and linear maps `L e p q` in `K`
  such that, for `p, q ≥ n e`, then `f` is well approximated by `L e p q` at scale `2 ^ (-p)` and
  `2 ^ (-q)`, with an error `2 ^ (-e)`. -/
  choose! n L hn using this,
  /- All the operators `L e p q` that show up are close to each other. To prove this, we argue
    that `L e p q` is close to `L e p r` (where `r` is large enough), as both approximate `f` at
    scale `2 ^(- p)`. And `L e p r` is close to `L e' p' r` as both approximate `f` at scale
    `2 ^ (- r)`. And `L e' p' r` is close to `L e' p' q'` as both approximate `f` at scale
    `2 ^ (- p')`. -/
  have M : ∀ e p q e' p' q', n e ≤ p → n e ≤ q → n e' ≤ p' → n e' ≤ q' → e ≤ e' →
    ‖L e p q - L e' p' q'‖ ≤ 12 * (1/2) ^ e,
  { assume e p q e' p' q' hp hq hp' hq' he',
    let r := max (n e) (n e'),
    have I : ((1:ℝ)/2)^e' ≤ (1/2)^e := pow_le_pow_of_le_one (by norm_num) (by norm_num) he',
    have J1 : ‖L e p q - L e p r‖ ≤ 4 * (1/2)^e,
    { have I1 : x ∈ A f (L e p q) ((1 / 2) ^ p) ((1/2)^e) :=
        (hn e p q hp hq).2.1,
      have I2 : x ∈ A f (L e p r) ((1 / 2) ^ p) ((1/2)^e) :=
        (hn e p r hp (le_max_left _ _)).2.1,
      exact norm_sub_le_of_mem_A P _ I1 I2 },
    have J2 : ‖L e p r - L e' p' r‖ ≤ 4 * (1/2)^e,
    { have I1 : x ∈ A f (L e p r) ((1 / 2) ^ r) ((1/2)^e) :=
        (hn e p r hp (le_max_left _ _)).2.2,
      have I2 : x ∈ A f (L e' p' r) ((1 / 2) ^ r) ((1/2)^e') :=
        (hn e' p' r hp' (le_max_right _ _)).2.2,
      exact norm_sub_le_of_mem_A P _ I1 (A_mono _ _ I I2) },
    have J3 : ‖L e' p' r - L e' p' q'‖ ≤ 4 * (1/2)^e,
    { have I1 : x ∈ A f (L e' p' r) ((1 / 2) ^ p') ((1/2)^e') :=
        (hn e' p' r hp' (le_max_right _ _)).2.1,
      have I2 : x ∈ A f (L e' p' q') ((1 / 2) ^ p') ((1/2)^e') :=
        (hn e' p' q' hp' hq').2.1,
      exact norm_sub_le_of_mem_A P _ (A_mono _ _ I I1) (A_mono _ _ I I2) },
    calc ‖L e p q - L e' p' q'‖
          = ‖(L e p q - L e p r) + (L e p r - L e' p' r) + (L e' p' r - L e' p' q')‖ :
        by { congr' 1, abel }
      ... ≤ ‖L e p q - L e p r‖ + ‖L e p r - L e' p' r‖ + ‖L e' p' r - L e' p' q'‖ :
        le_trans (norm_add_le _ _) (add_le_add_right (norm_add_le _ _) _)
      ... ≤ 4 * (1/2)^e + 4 * (1/2)^e + 4 * (1/2)^e :
        by apply_rules [add_le_add]
      ... = 12 * (1/2)^e : by ring },
  /- For definiteness, use `L0 e = L e (n e) (n e)`, to have a single sequence. We claim that this
  is a Cauchy sequence. -/
  let L0 : ℕ → F := λ e, L e (n e) (n e),
  have : cauchy_seq L0,
  { rw metric.cauchy_seq_iff',
    assume ε εpos,
    obtain ⟨e, he⟩ : ∃ (e : ℕ), (1/2) ^ e < ε / 12 :=
      exists_pow_lt_of_lt_one (div_pos εpos (by norm_num)) (by norm_num),
    refine ⟨e, λ e' he', _⟩,
    rw [dist_comm, dist_eq_norm],
    calc ‖L0 e - L0 e'‖
          ≤ 12 * (1/2)^e : M _ _ _ _ _ _ le_rfl le_rfl le_rfl le_rfl he'
      ... < 12 * (ε / 12) :
        mul_lt_mul' le_rfl he (le_of_lt P) (by norm_num)
      ... = ε : by { field_simp [(by norm_num : (12 : ℝ) ≠ 0)], ring } },
  /- As it is Cauchy, the sequence `L0` converges, to a limit `f'` in `K`.-/
  obtain ⟨f', f'K, hf'⟩ : ∃ f' ∈ K, tendsto L0 at_top (𝓝 f') :=
    cauchy_seq_tendsto_of_is_complete hK (λ e, (hn e (n e) (n e) le_rfl le_rfl).1) this,
  have Lf' : ∀ e p, n e ≤ p → ‖L e (n e) p - f'‖ ≤ 12 * (1/2)^e,
  { assume e p hp,
    apply le_of_tendsto (tendsto_const_nhds.sub hf').norm,
    rw eventually_at_top,
    exact ⟨e, λ e' he', M _ _ _ _ _ _ le_rfl hp le_rfl le_rfl he'⟩ },
  /- Let us show that `f` has right derivative `f'` at `x`. -/
  have : has_deriv_within_at f f' (Ici x) x,
  { simp only [has_deriv_within_at_iff_is_o, is_o_iff],
    /- to get an approximation with a precision `ε`, we will replace `f` with `L e (n e) m` for
    some large enough `e` (yielding a small error by uniform approximation). As one can vary `m`,
    this makes it possible to cover all scales, and thus to obtain a good linear approximation in
    the whole interval of length `(1/2)^(n e)`. -/
    assume ε εpos,
    obtain ⟨e, he⟩ : ∃ (e : ℕ), (1 / 2) ^ e < ε / 16 :=
      exists_pow_lt_of_lt_one (div_pos εpos (by norm_num)) (by norm_num),
    have xmem : x ∈ Ico x (x + (1/2)^(n e + 1)),
      by simp only [one_div, left_mem_Ico, lt_add_iff_pos_right, inv_pos, pow_pos, zero_lt_bit0,
        zero_lt_one],
    filter_upwards [Icc_mem_nhds_within_Ici xmem] with y hy,
    -- We need to show that `f y - f x - f' (y - x)` is small. For this, we will work at scale
    -- `k` where `k` is chosen with `‖y - x‖ ∼ 2 ^ (-k)`.
    rcases eq_or_lt_of_le hy.1 with rfl|xy,
    { simp only [sub_self, zero_smul, norm_zero, mul_zero]},
    have yzero : 0 < y - x := sub_pos.2 xy,
    have y_le : y - x ≤ (1/2) ^ (n e + 1), by linarith [hy.2],
    have yone : y - x ≤ 1 := le_trans y_le (pow_le_one _ (by norm_num) (by norm_num)),
    -- define the scale `k`.
    obtain ⟨k, hk, h'k⟩ : ∃ (k : ℕ), (1/2) ^ (k + 1) < y - x ∧ y - x ≤ (1/2) ^ k :=
      exists_nat_pow_near_of_lt_one yzero yone (by norm_num : (0 : ℝ) < 1/2)
      (by norm_num : (1 : ℝ)/2 < 1),
    -- the scale is large enough (as `y - x` is small enough)
    have k_gt : n e < k,
    { have : ((1:ℝ)/2) ^ (k + 1) < (1/2) ^ (n e + 1) := lt_of_lt_of_le hk y_le,
      rw pow_lt_pow_iff_of_lt_one (by norm_num : (0 : ℝ) < 1/2) (by norm_num) at this,
      linarith },
    set m := k - 1 with hl,
    have m_ge : n e ≤ m := nat.le_pred_of_lt k_gt,
    have km : k = m + 1 := (nat.succ_pred_eq_of_pos (lt_of_le_of_lt (zero_le _) k_gt)).symm,
    rw km at hk h'k,
    -- `f` is well approximated by `L e (n e) k` at the relevant scale
    -- (in fact, we use `m = k - 1` instead of `k` because of the precise definition of `A`).
    have J : ‖f y - f x - (y - x) • L e (n e) m‖ ≤ 4 * (1/2) ^ e * ‖y - x‖ := calc
      ‖f y - f x - (y - x) • L e (n e) m‖ ≤ (1/2) ^ e * (1/2) ^ m :
        begin
          apply le_of_mem_A (hn e (n e) m le_rfl m_ge).2.2,
          { simp only [one_div, inv_pow, left_mem_Icc, le_add_iff_nonneg_right],
            exact div_nonneg (inv_nonneg.2 (pow_nonneg zero_le_two _)) zero_le_two },
          { simp only [pow_add, tsub_le_iff_left] at h'k,
            simpa only [hy.1, mem_Icc, true_and, one_div, pow_one] using h'k }
        end
      ... = 4 * (1/2) ^ e * (1/2) ^ (m + 2) : by { field_simp, ring_exp }
      ... ≤ 4 * (1/2) ^ e * (y - x) :
        mul_le_mul_of_nonneg_left (le_of_lt hk) (mul_nonneg (by norm_num) (le_of_lt P))
      ... = 4 * (1/2) ^ e * ‖y - x‖ : by rw [real.norm_of_nonneg yzero.le],
    calc ‖f y - f x - (y - x) • f'‖
        = ‖(f y - f x - (y - x) • L e (n e) m) + (y - x) • (L e (n e) m - f')‖ :
      by simp only [smul_sub, sub_add_sub_cancel]
    ... ≤ 4 * (1/2) ^ e * ‖y - x‖ + ‖y - x‖ * (12 * (1/2) ^ e) : norm_add_le_of_le J
      (by { rw [norm_smul], exact mul_le_mul_of_nonneg_left (Lf' _ _ m_ge) (norm_nonneg _) })
    ... = 16 * ‖y - x‖ * (1/2) ^ e : by ring
    ... ≤ 16 * ‖y - x‖ * (ε / 16) :
      mul_le_mul_of_nonneg_left he.le (mul_nonneg (by norm_num) (norm_nonneg _))
    ... = ε * ‖y - x‖ : by ring },
  rw ← this.deriv_within (unique_diff_on_Ici x x le_rfl) at f'K,
  exact ⟨this.differentiable_within_at, f'K⟩,
end

theorem differentiable_set_eq_D (hK : is_complete K) :
  {x | differentiable_within_at ℝ f (Ici x) x ∧ deriv_within f (Ici x) x ∈ K} = D f K :=
subset.antisymm (differentiable_set_subset_D _) (D_subset_differentiable_set hK)

end right_deriv_measurable_aux

open right_deriv_measurable_aux

variables (f)

/-- The set of right differentiability points of a function, with derivative in a given complete
set, is Borel-measurable. -/
theorem measurable_set_of_differentiable_within_at_Ici_of_is_complete
  {K : set F} (hK : is_complete K) :
  measurable_set {x | differentiable_within_at ℝ f (Ici x) x ∧ deriv_within f (Ici x) x ∈ K} :=
by simp [differentiable_set_eq_D K hK, D, measurable_set_B, measurable_set.Inter,
         measurable_set.Union]

variable [complete_space F]

/-- The set of right differentiability points of a function taking values in a complete space is
Borel-measurable. -/
theorem measurable_set_of_differentiable_within_at_Ici :
  measurable_set {x | differentiable_within_at ℝ f (Ici x) x} :=
begin
  have : is_complete (univ : set F) := complete_univ,
  convert measurable_set_of_differentiable_within_at_Ici_of_is_complete f this,
  simp
end

@[measurability] lemma measurable_deriv_within_Ici [measurable_space F] [borel_space F] :
  measurable (λ x, deriv_within f (Ici x) x) :=
begin
  refine measurable_of_is_closed (λ s hs, _),
  have : (λ x, deriv_within f (Ici x) x) ⁻¹' s =
    {x | differentiable_within_at ℝ f (Ici x) x ∧ deriv_within f (Ici x) x ∈ s} ∪
    ({x | ¬differentiable_within_at ℝ f (Ici x) x} ∩ {x | (0 : F) ∈ s}) :=
    set.ext (λ x, mem_preimage.trans deriv_within_mem_iff),
  rw this,
  exact (measurable_set_of_differentiable_within_at_Ici_of_is_complete _ hs.is_complete).union
    ((measurable_set_of_differentiable_within_at_Ici _).compl.inter (measurable_set.const _))
end

lemma strongly_measurable_deriv_within_Ici [second_countable_topology F] :
  strongly_measurable (λ x, deriv_within f (Ici x) x) :=
by { borelize F, exact (measurable_deriv_within_Ici f).strongly_measurable }

lemma ae_measurable_deriv_within_Ici [measurable_space F] [borel_space F]
  (μ : measure ℝ) : ae_measurable (λ x, deriv_within f (Ici x) x) μ :=
(measurable_deriv_within_Ici f).ae_measurable

lemma ae_strongly_measurable_deriv_within_Ici [second_countable_topology F] (μ : measure ℝ) :
  ae_strongly_measurable (λ x, deriv_within f (Ici x) x) μ :=
(strongly_measurable_deriv_within_Ici f).ae_strongly_measurable

/-- The set of right differentiability points of a function taking values in a complete space is
Borel-measurable. -/
theorem measurable_set_of_differentiable_within_at_Ioi :
  measurable_set {x | differentiable_within_at ℝ f (Ioi x) x} :=
by simpa [differentiable_within_at_Ioi_iff_Ici]
  using measurable_set_of_differentiable_within_at_Ici f

@[measurability] lemma measurable_deriv_within_Ioi [measurable_space F] [borel_space F] :
  measurable (λ x, deriv_within f (Ioi x) x) :=
by simpa [deriv_within_Ioi_eq_Ici] using measurable_deriv_within_Ici f

lemma strongly_measurable_deriv_within_Ioi [second_countable_topology F] :
  strongly_measurable (λ x, deriv_within f (Ioi x) x) :=
by { borelize F, exact (measurable_deriv_within_Ioi f).strongly_measurable }

lemma ae_measurable_deriv_within_Ioi [measurable_space F] [borel_space F]
  (μ : measure ℝ) : ae_measurable (λ x, deriv_within f (Ioi x) x) μ :=
(measurable_deriv_within_Ioi f).ae_measurable

lemma ae_strongly_measurable_deriv_within_Ioi [second_countable_topology F] (μ : measure ℝ) :
  ae_strongly_measurable (λ x, deriv_within f (Ioi x) x) μ :=
(strongly_measurable_deriv_within_Ioi f).ae_strongly_measurable

end right_deriv
