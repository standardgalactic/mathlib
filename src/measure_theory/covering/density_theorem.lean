/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import measure_theory.measure.doubling
import measure_theory.covering.vitali
import measure_theory.covering.differentiation

/-!
# Uniformly locally doubling measures and Lebesgue's density theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Lebesgue's density theorem states that given a set `S` in a sigma compact metric space with
locally-finite uniformly locally doubling measure `μ` then for almost all points `x` in `S`, for any
sequence of closed balls `B₀, B₁, B₂, ...` containing `x`, the limit `μ (S ∩ Bⱼ) / μ (Bⱼ) → 1` as
`j → ∞`.

In this file we combine general results about existence of Vitali families for uniformly locally
doubling measures with results about differentiation along a Vitali family to obtain an explicit
form of Lebesgue's density theorem.

## Main results
  * `is_unif_loc_doubling_measure.ae_tendsto_measure_inter_div`: a version of Lebesgue's density
  theorem for sequences of balls converging on a point but whose centres are not required to be
  fixed.

-/

noncomputable theory

open set filter metric measure_theory topological_space
open_locale nnreal topology

namespace is_unif_loc_doubling_measure

variables {α : Type*} [metric_space α] [measurable_space α]
          (μ : measure α) [is_unif_loc_doubling_measure μ]

section
variables [second_countable_topology α] [borel_space α] [is_locally_finite_measure μ]

open_locale topology

/-- A Vitali family in a space with a uniformly locally doubling measure, designed so that the sets
at `x` contain all `closed_ball y r` when `dist x y ≤ K * r`. -/
@[irreducible] def vitali_family (K : ℝ) : vitali_family μ :=
begin
  /- the Vitali covering theorem gives a family that works well at small scales, thanks to the
  doubling property. We enlarge this family to add large sets, to make sure that all balls and not
  only small ones belong to the family, for convenience. -/
  let R := scaling_scale_of μ (max (4 * K + 3) 3),
  have Rpos : 0 < R := scaling_scale_of_pos _ _,
  have A : ∀ (x : α), ∃ᶠ r in 𝓝[>] (0 : ℝ),
    μ (closed_ball x (3 * r)) ≤ scaling_constant_of μ (max (4 * K + 3) 3) * μ (closed_ball x r),
  { assume x,
    apply frequently_iff.2 (λ U hU, _),
    obtain ⟨ε, εpos, hε⟩ := mem_nhds_within_Ioi_iff_exists_Ioc_subset.1 hU,
    refine ⟨min ε R, hε ⟨lt_min εpos Rpos, min_le_left _ _⟩, _⟩,
    exact measure_mul_le_scaling_constant_of_mul μ
      ⟨zero_lt_three, le_max_right _ _⟩ (min_le_right _ _) },
  exact (vitali.vitali_family μ (scaling_constant_of μ (max (4 * K + 3) 3)) A).enlarge
    (R / 4) (by linarith),
end

/-- In the Vitali family `is_unif_loc_doubling_measure.vitali_family K`, the sets based at `x`
contain all balls `closed_ball y r` when `dist x y ≤ K * r`. -/
lemma closed_ball_mem_vitali_family_of_dist_le_mul
  {K : ℝ} {x y : α} {r : ℝ} (h : dist x y ≤ K * r) (rpos : 0 < r) :
  closed_ball y r ∈ (vitali_family μ K).sets_at x :=
begin
  let R := scaling_scale_of μ (max (4 * K + 3) 3),
  simp only [vitali_family, vitali_family.enlarge, vitali.vitali_family, mem_union, mem_set_of_eq,
    is_closed_ball, true_and, (nonempty_ball.2 rpos).mono ball_subset_interior_closed_ball,
    measurable_set_closed_ball],
  /- The measure is doubling on scales smaller than `R`. Therefore, we treat differently small
  and large balls. For large balls, this follows directly from the enlargement we used in the
  definition. -/
  by_cases H : closed_ball y r ⊆ closed_ball x (R / 4),
  swap, { exact or.inr H },
  left,
  /- For small balls, there is the difficulty that `r` could be large but still the ball could be
  small, if the annulus `{y | ε ≤ dist y x ≤ R/4}` is empty. We split between the cases `r ≤ R`
  and `r < R`, and use the doubling for the former and rough estimates for the latter. -/
  rcases le_or_lt r R with hr|hr,
  { refine ⟨(K + 1) * r, _⟩,
    split,
    { apply closed_ball_subset_closed_ball',
      rw dist_comm,
      linarith },
    { have I1 : closed_ball x (3 * ((K + 1) * r)) ⊆ closed_ball y ((4 * K + 3) * r),
      { apply closed_ball_subset_closed_ball',
        linarith },
      have I2 : closed_ball y ((4 * K + 3) * r) ⊆ closed_ball y ((max (4 * K + 3) 3) * r),
      { apply closed_ball_subset_closed_ball,
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) rpos.le },
      apply (measure_mono (I1.trans I2)).trans,
      exact measure_mul_le_scaling_constant_of_mul _
        ⟨zero_lt_three.trans_le (le_max_right _ _), le_rfl⟩ hr } },
  { refine ⟨R / 4, H, _⟩,
    have : closed_ball x (3 * (R / 4)) ⊆ closed_ball y r,
    { apply closed_ball_subset_closed_ball',
      have A : y ∈ closed_ball y r, from mem_closed_ball_self rpos.le,
      have B := mem_closed_ball'.1 (H A),
      linarith },
    apply (measure_mono this).trans _,
    refine le_mul_of_one_le_left (zero_le _) _,
    exact ennreal.one_le_coe_iff.2 (le_max_right _ _) }
end

lemma tendsto_closed_ball_filter_at {K : ℝ} {x : α} {ι : Type*} {l : filter ι}
  (w : ι → α) (δ : ι → ℝ) (δlim : tendsto δ l (𝓝[>] 0))
  (xmem : ∀ᶠ j in l, x ∈ closed_ball (w j) (K * δ j)) :
  tendsto (λ j, closed_ball (w j) (δ j)) l ((vitali_family μ K).filter_at x) :=
begin
  refine (vitali_family μ K).tendsto_filter_at_iff.mpr ⟨_, λ ε hε, _⟩,
  { filter_upwards [xmem, δlim self_mem_nhds_within] with j hj h'j,
    exact closed_ball_mem_vitali_family_of_dist_le_mul μ hj h'j },
  { by_cases l.ne_bot,
    swap, { simp [not_ne_bot.1 h] },
    have hK : 0 ≤ K,
    { resetI,
      rcases (xmem.and (δlim self_mem_nhds_within)).exists with ⟨j, hj, h'j⟩,
      have : 0 ≤ K * δ j := nonempty_closed_ball.1 ⟨x, hj⟩,
      exact (mul_nonneg_iff_left_nonneg_of_pos (mem_Ioi.1 h'j)).1 this },
    have δpos := eventually_mem_of_tendsto_nhds_within δlim,
    replace δlim := tendsto_nhds_of_tendsto_nhds_within δlim,
    replace hK : 0 < K + 1, by linarith,
    apply (((metric.tendsto_nhds.mp δlim _ (div_pos hε hK)).and δpos).and xmem).mono,
    rintros j ⟨⟨hjε, hj₀ : 0 < δ j⟩, hx⟩ y hy,
    replace hjε : (K + 1) * δ j < ε :=
      by simpa [abs_eq_self.mpr hj₀.le] using (lt_div_iff' hK).mp hjε,
    simp only [mem_closed_ball] at hx hy ⊢,
    linarith [dist_triangle_right y x (w j)] }
end

end

section applications
variables [second_countable_topology α] [borel_space α] [is_locally_finite_measure μ]
  {E : Type*} [normed_add_comm_group E]

/-- A version of *Lebesgue's density theorem* for a sequence of closed balls whose centers are
not required to be fixed.

See also `besicovitch.ae_tendsto_measure_inter_div`. -/
lemma ae_tendsto_measure_inter_div (S : set α) (K : ℝ) :
  ∀ᵐ x ∂μ.restrict S, ∀ {ι : Type*} {l : filter ι} (w : ι → α) (δ : ι → ℝ)
    (δlim : tendsto δ l (𝓝[>] 0))
    (xmem : ∀ᶠ j in l, x ∈ closed_ball (w j) (K * δ j)),
    tendsto (λ j, μ (S ∩ closed_ball (w j) (δ j)) / μ (closed_ball (w j) (δ j))) l (𝓝 1) :=
by filter_upwards [(vitali_family μ K).ae_tendsto_measure_inter_div S] with x hx ι l w δ δlim xmem
using hx.comp (tendsto_closed_ball_filter_at μ _ _ δlim xmem)

/-- A version of *Lebesgue differentiation theorem* for a sequence of closed balls whose
centers are not required to be fixed. -/
lemma ae_tendsto_average_norm_sub {f : α → E} (hf : integrable f μ) (K : ℝ) :
  ∀ᵐ x ∂μ, ∀ {ι : Type*} {l : filter ι} (w : ι → α) (δ : ι → ℝ)
    (δlim : tendsto δ l (𝓝[>] 0))
    (xmem : ∀ᶠ j in l, x ∈ closed_ball (w j) (K * δ j)),
    tendsto (λ j, ⨍ y in closed_ball (w j) (δ j), ‖f y - f x‖ ∂μ) l (𝓝 0) :=
by filter_upwards [(vitali_family μ K).ae_tendsto_average_norm_sub hf] with x hx ι l w δ δlim xmem
using hx.comp (tendsto_closed_ball_filter_at μ _ _ δlim xmem)

/-- A version of *Lebesgue differentiation theorem* for a sequence of closed balls whose
centers are not required to be fixed. -/
lemma ae_tendsto_average [normed_space ℝ E] [complete_space E]
  {f : α → E} (hf : integrable f μ) (K : ℝ) :
  ∀ᵐ x ∂μ, ∀ {ι : Type*} {l : filter ι} (w : ι → α) (δ : ι → ℝ)
    (δlim : tendsto δ l (𝓝[>] 0))
    (xmem : ∀ᶠ j in l, x ∈ closed_ball (w j) (K * δ j)),
    tendsto (λ j, ⨍ y in closed_ball (w j) (δ j), f y ∂μ) l (𝓝 (f x)) :=
by filter_upwards [(vitali_family μ K).ae_tendsto_average hf] with x hx ι l w δ δlim xmem
using hx.comp (tendsto_closed_ball_filter_at μ _ _ δlim xmem)

end applications

end is_unif_loc_doubling_measure
