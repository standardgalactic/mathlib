/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.inner_product_space.pi_L2
import analysis.special_functions.sqrt

/-!
# Calculus in inner product spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that the inner product and square of the norm in an inner space are
infinitely `ℝ`-smooth. In order to state these results, we need a `normed_space ℝ E`
instance. Though we can deduce this structure from `inner_product_space 𝕜 E`, this instance may be
not definitionally equal to some other “natural” instance. So, we assume `[normed_space ℝ E]`.

We also prove that functions to a `euclidean_space` are (higher) differentiable if and only if
their components are. This follows from the corresponding fact for finite product of normed spaces,
and from the equivalence of norms in finite dimensions.

## TODO

The last part of the file should be generalized to `pi_Lp`.
-/

noncomputable theory

open is_R_or_C real filter
open_locale big_operators classical topology

section deriv_inner

variables {𝕜 E F : Type*} [is_R_or_C 𝕜]
variables [normed_add_comm_group E] [inner_product_space 𝕜 E]
variables [normed_add_comm_group F] [inner_product_space ℝ F]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

variables (𝕜) [normed_space ℝ E]

/-- Derivative of the inner product. -/
def fderiv_inner_clm (p : E × E) : E × E →L[ℝ] 𝕜 := is_bounded_bilinear_map_inner.deriv p

@[simp] lemma fderiv_inner_clm_apply (p x : E × E) :
  fderiv_inner_clm 𝕜 p x = ⟪p.1, x.2⟫ + ⟪x.1, p.2⟫ := rfl

lemma cont_diff_inner {n} : cont_diff ℝ n (λ p : E × E, ⟪p.1, p.2⟫) :=
is_bounded_bilinear_map_inner.cont_diff

lemma cont_diff_at_inner {p : E × E} {n} :
  cont_diff_at ℝ n (λ p : E × E, ⟪p.1, p.2⟫) p :=
cont_diff_inner.cont_diff_at

lemma differentiable_inner : differentiable ℝ (λ p : E × E, ⟪p.1, p.2⟫) :=
is_bounded_bilinear_map_inner.differentiable_at

variables {G : Type*} [normed_add_comm_group G] [normed_space ℝ G]
  {f g : G → E} {f' g' : G →L[ℝ] E} {s : set G} {x : G} {n : ℕ∞}

include 𝕜

lemma cont_diff_within_at.inner (hf : cont_diff_within_at ℝ n f s x)
  (hg : cont_diff_within_at ℝ n g s x) :
  cont_diff_within_at ℝ n (λ x, ⟪f x, g x⟫) s x :=
cont_diff_at_inner.comp_cont_diff_within_at x (hf.prod hg)

lemma cont_diff_at.inner (hf : cont_diff_at ℝ n f x)
  (hg : cont_diff_at ℝ n g x) :
  cont_diff_at ℝ n (λ x, ⟪f x, g x⟫) x :=
hf.inner 𝕜 hg

lemma cont_diff_on.inner (hf : cont_diff_on ℝ n f s) (hg : cont_diff_on ℝ n g s) :
  cont_diff_on ℝ n (λ x, ⟪f x, g x⟫) s :=
λ x hx, (hf x hx).inner 𝕜 (hg x hx)

lemma cont_diff.inner (hf : cont_diff ℝ n f) (hg : cont_diff ℝ n g) :
  cont_diff ℝ n (λ x, ⟪f x, g x⟫) :=
cont_diff_inner.comp (hf.prod hg)

lemma has_fderiv_within_at.inner (hf : has_fderiv_within_at f f' s x)
  (hg : has_fderiv_within_at g g' s x) :
  has_fderiv_within_at (λ t, ⟪f t, g t⟫) ((fderiv_inner_clm 𝕜 (f x, g x)).comp $ f'.prod g') s x :=
(is_bounded_bilinear_map_inner.has_fderiv_at (f x, g x)).comp_has_fderiv_within_at x (hf.prod hg)

lemma has_strict_fderiv_at.inner (hf : has_strict_fderiv_at f f' x)
  (hg : has_strict_fderiv_at g g' x) :
  has_strict_fderiv_at (λ t, ⟪f t, g t⟫) ((fderiv_inner_clm 𝕜 (f x, g x)).comp $ f'.prod g') x :=
(is_bounded_bilinear_map_inner.has_strict_fderiv_at (f x, g x)).comp x (hf.prod hg)

lemma has_fderiv_at.inner (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) :
  has_fderiv_at (λ t, ⟪f t, g t⟫) ((fderiv_inner_clm 𝕜 (f x, g x)).comp $ f'.prod g') x :=
(is_bounded_bilinear_map_inner.has_fderiv_at (f x, g x)).comp x (hf.prod hg)

lemma has_deriv_within_at.inner {f g : ℝ → E} {f' g' : E} {s : set ℝ} {x : ℝ}
  (hf : has_deriv_within_at f f' s x) (hg : has_deriv_within_at g g' s x) :
  has_deriv_within_at (λ t, ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) s x :=
by simpa using (hf.has_fderiv_within_at.inner 𝕜 hg.has_fderiv_within_at).has_deriv_within_at

lemma has_deriv_at.inner {f g : ℝ → E} {f' g' : E} {x : ℝ} :
  has_deriv_at f f' x →  has_deriv_at g g' x →
  has_deriv_at (λ t, ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) x :=
by simpa only [← has_deriv_within_at_univ] using has_deriv_within_at.inner 𝕜

lemma differentiable_within_at.inner (hf : differentiable_within_at ℝ f s x)
  (hg : differentiable_within_at ℝ g s x) :
  differentiable_within_at ℝ (λ x, ⟪f x, g x⟫) s x :=
((differentiable_inner _).has_fderiv_at.comp_has_fderiv_within_at x
  (hf.prod hg).has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.inner (hf : differentiable_at ℝ f x) (hg : differentiable_at ℝ g x) :
  differentiable_at ℝ (λ x, ⟪f x, g x⟫) x :=
(differentiable_inner _).comp x (hf.prod hg)

lemma differentiable_on.inner (hf : differentiable_on ℝ f s) (hg : differentiable_on ℝ g s) :
  differentiable_on ℝ (λ x, ⟪f x, g x⟫) s :=
λ x hx, (hf x hx).inner 𝕜 (hg x hx)

lemma differentiable.inner (hf : differentiable ℝ f) (hg : differentiable ℝ g) :
  differentiable ℝ (λ x, ⟪f x, g x⟫) :=
λ x, (hf x).inner 𝕜 (hg x)

lemma fderiv_inner_apply (hf : differentiable_at ℝ f x) (hg : differentiable_at ℝ g x) (y : G) :
  fderiv ℝ (λ t, ⟪f t, g t⟫) x y = ⟪f x, fderiv ℝ g x y⟫ + ⟪fderiv ℝ f x y, g x⟫ :=
by { rw [(hf.has_fderiv_at.inner 𝕜 hg.has_fderiv_at).fderiv], refl }

lemma deriv_inner_apply {f g : ℝ → E} {x : ℝ} (hf : differentiable_at ℝ f x)
  (hg : differentiable_at ℝ g x) :
  deriv (λ t, ⟪f t, g t⟫) x = ⟪f x, deriv g x⟫ + ⟪deriv f x, g x⟫ :=
(hf.has_deriv_at.inner 𝕜 hg.has_deriv_at).deriv

lemma cont_diff_norm_sq : cont_diff ℝ n (λ x : E, ‖x‖ ^ 2) :=
begin
  simp only [sq, ← @inner_self_eq_norm_mul_norm 𝕜],
  exact (re_clm : 𝕜 →L[ℝ] ℝ).cont_diff.comp (cont_diff_id.inner 𝕜 cont_diff_id)
end

lemma cont_diff.norm_sq (hf : cont_diff ℝ n f) :
  cont_diff ℝ n (λ x, ‖f x‖ ^ 2) :=
(cont_diff_norm_sq 𝕜).comp hf

lemma cont_diff_within_at.norm_sq (hf : cont_diff_within_at ℝ n f s x) :
  cont_diff_within_at ℝ n (λ y, ‖f y‖ ^ 2) s x :=
(cont_diff_norm_sq 𝕜).cont_diff_at.comp_cont_diff_within_at x hf

lemma cont_diff_at.norm_sq (hf : cont_diff_at ℝ n f x) :
  cont_diff_at ℝ n (λ y, ‖f y‖ ^ 2) x :=
hf.norm_sq 𝕜

lemma cont_diff_at_norm {x : E} (hx : x ≠ 0) : cont_diff_at ℝ n norm x :=
have ‖id x‖ ^ 2 ≠ 0, from pow_ne_zero _ (norm_pos_iff.2 hx).ne',
by simpa only [id, sqrt_sq, norm_nonneg] using (cont_diff_at_id.norm_sq 𝕜).sqrt this

lemma cont_diff_at.norm (hf : cont_diff_at ℝ n f x) (h0 : f x ≠ 0) :
  cont_diff_at ℝ n (λ y, ‖f y‖) x :=
(cont_diff_at_norm 𝕜 h0).comp x hf

lemma cont_diff_at.dist (hf : cont_diff_at ℝ n f x) (hg : cont_diff_at ℝ n g x)
  (hne : f x ≠ g x) :
  cont_diff_at ℝ n (λ y, dist (f y) (g y)) x :=
by { simp only [dist_eq_norm], exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne) }

lemma cont_diff_within_at.norm (hf : cont_diff_within_at ℝ n f s x) (h0 : f x ≠ 0) :
  cont_diff_within_at ℝ n (λ y, ‖f y‖) s x :=
(cont_diff_at_norm 𝕜 h0).comp_cont_diff_within_at x hf

lemma cont_diff_within_at.dist (hf : cont_diff_within_at ℝ n f s x)
  (hg : cont_diff_within_at ℝ n g s x) (hne : f x ≠ g x) :
  cont_diff_within_at ℝ n (λ y, dist (f y) (g y)) s x :=
by { simp only [dist_eq_norm], exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne) }

lemma cont_diff_on.norm_sq (hf : cont_diff_on ℝ n f s) :
  cont_diff_on ℝ n (λ y, ‖f y‖ ^ 2) s :=
(λ x hx, (hf x hx).norm_sq 𝕜)

lemma cont_diff_on.norm (hf : cont_diff_on ℝ n f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
  cont_diff_on ℝ n (λ y, ‖f y‖) s :=
λ x hx, (hf x hx).norm 𝕜 (h0 x hx)

lemma cont_diff_on.dist (hf : cont_diff_on ℝ n f s)
  (hg : cont_diff_on ℝ n g s) (hne : ∀ x ∈ s, f x ≠ g x) :
  cont_diff_on ℝ n (λ y, dist (f y) (g y)) s :=
λ x hx, (hf x hx).dist 𝕜 (hg x hx) (hne x hx)

lemma cont_diff.norm (hf : cont_diff ℝ n f) (h0 : ∀ x, f x ≠ 0) :
  cont_diff ℝ n (λ y, ‖f y‖) :=
cont_diff_iff_cont_diff_at.2 $ λ x, hf.cont_diff_at.norm 𝕜 (h0 x)

lemma cont_diff.dist (hf : cont_diff ℝ n f) (hg : cont_diff ℝ n g)
  (hne : ∀ x, f x ≠ g x) :
  cont_diff ℝ n (λ y, dist (f y) (g y)) :=
cont_diff_iff_cont_diff_at.2 $
  λ x, hf.cont_diff_at.dist 𝕜 hg.cont_diff_at (hne x)

omit 𝕜
lemma has_strict_fderiv_at_norm_sq (x : F) :
  has_strict_fderiv_at (λ x, ‖x‖ ^ 2) (bit0 (innerSL ℝ x)) x :=
begin
  simp only [sq, ← @inner_self_eq_norm_mul_norm ℝ],
  convert (has_strict_fderiv_at_id x).inner ℝ (has_strict_fderiv_at_id x),
  ext y,
  simp [bit0, real_inner_comm],
end
include 𝕜

lemma differentiable_at.norm_sq (hf : differentiable_at ℝ f x) :
  differentiable_at ℝ (λ y, ‖f y‖ ^ 2) x :=
((cont_diff_at_id.norm_sq 𝕜).differentiable_at le_rfl).comp x hf

lemma differentiable_at.norm (hf : differentiable_at ℝ f x) (h0 : f x ≠ 0) :
  differentiable_at ℝ (λ y, ‖f y‖) x :=
((cont_diff_at_norm 𝕜 h0).differentiable_at le_rfl).comp x hf

lemma differentiable_at.dist (hf : differentiable_at ℝ f x) (hg : differentiable_at ℝ g x)
  (hne : f x ≠ g x) :
  differentiable_at ℝ (λ y, dist (f y) (g y)) x :=
by { simp only [dist_eq_norm], exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne) }

lemma differentiable.norm_sq (hf : differentiable ℝ f) : differentiable ℝ (λ y, ‖f y‖ ^ 2) :=
λ x, (hf x).norm_sq 𝕜

lemma differentiable.norm (hf : differentiable ℝ f) (h0 : ∀ x, f x ≠ 0) :
  differentiable ℝ (λ y, ‖f y‖) :=
λ x, (hf x).norm 𝕜 (h0 x)

lemma differentiable.dist (hf : differentiable ℝ f) (hg : differentiable ℝ g)
  (hne : ∀ x, f x ≠ g x) :
  differentiable ℝ (λ y, dist (f y) (g y)) :=
λ x, (hf x).dist 𝕜 (hg x) (hne x)

lemma differentiable_within_at.norm_sq (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ y, ‖f y‖ ^ 2) s x :=
((cont_diff_at_id.norm_sq 𝕜).differentiable_at le_rfl).comp_differentiable_within_at x hf

lemma differentiable_within_at.norm (hf : differentiable_within_at ℝ f s x) (h0 : f x ≠ 0) :
  differentiable_within_at ℝ (λ y, ‖f y‖) s x :=
((cont_diff_at_id.norm 𝕜 h0).differentiable_at le_rfl).comp_differentiable_within_at x hf

lemma differentiable_within_at.dist (hf : differentiable_within_at ℝ f s x)
  (hg : differentiable_within_at ℝ g s x) (hne : f x ≠ g x) :
  differentiable_within_at ℝ (λ y, dist (f y) (g y)) s x :=
by { simp only [dist_eq_norm], exact (hf.sub hg).norm 𝕜 (sub_ne_zero.2 hne) }

lemma differentiable_on.norm_sq (hf : differentiable_on ℝ f s) :
  differentiable_on ℝ (λ y, ‖f y‖ ^ 2) s :=
λ x hx, (hf x hx).norm_sq 𝕜

lemma differentiable_on.norm (hf : differentiable_on ℝ f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
  differentiable_on ℝ (λ y, ‖f y‖) s :=
λ x hx, (hf x hx).norm 𝕜 (h0 x hx)

lemma differentiable_on.dist (hf : differentiable_on ℝ f s) (hg : differentiable_on ℝ g s)
  (hne : ∀ x ∈ s, f x ≠ g x) :
  differentiable_on ℝ (λ y, dist (f y) (g y)) s :=
λ x hx, (hf x hx).dist 𝕜 (hg x hx) (hne x hx)

end deriv_inner

section pi_like

open continuous_linear_map

variables {𝕜 ι H : Type*} [is_R_or_C 𝕜] [normed_add_comm_group H] [normed_space 𝕜 H]
  [fintype ι] {f : H → euclidean_space 𝕜 ι} {f' : H →L[𝕜] euclidean_space 𝕜 ι} {t : set H} {y : H}

lemma differentiable_within_at_euclidean :
  differentiable_within_at 𝕜 f t y ↔ ∀ i, differentiable_within_at 𝕜 (λ x, f x i) t y :=
begin
  rw [← (euclidean_space.equiv ι 𝕜).comp_differentiable_within_at_iff, differentiable_within_at_pi],
  refl
end

lemma differentiable_at_euclidean :
  differentiable_at 𝕜 f y ↔ ∀ i, differentiable_at 𝕜 (λ x, f x i) y :=
begin
  rw [← (euclidean_space.equiv ι 𝕜).comp_differentiable_at_iff, differentiable_at_pi],
  refl
end

lemma differentiable_on_euclidean :
  differentiable_on 𝕜 f t ↔ ∀ i, differentiable_on 𝕜 (λ x, f x i) t :=
begin
  rw [← (euclidean_space.equiv ι 𝕜).comp_differentiable_on_iff, differentiable_on_pi],
  refl
end

lemma differentiable_euclidean :
  differentiable 𝕜 f ↔ ∀ i, differentiable 𝕜 (λ x, f x i) :=
begin
  rw [← (euclidean_space.equiv ι 𝕜).comp_differentiable_iff, differentiable_pi],
  refl
end

lemma has_strict_fderiv_at_euclidean :
  has_strict_fderiv_at f f' y ↔ ∀ i, has_strict_fderiv_at (λ x, f x i)
    (euclidean_space.proj i ∘L f') y :=
begin
  rw [← (euclidean_space.equiv ι 𝕜).comp_has_strict_fderiv_at_iff, has_strict_fderiv_at_pi'],
  refl
end

lemma has_fderiv_within_at_euclidean :
  has_fderiv_within_at f f' t y ↔ ∀ i, has_fderiv_within_at (λ x, f x i)
    (euclidean_space.proj i ∘L f') t y :=
begin
  rw [← (euclidean_space.equiv ι 𝕜).comp_has_fderiv_within_at_iff, has_fderiv_within_at_pi'],
  refl
end

lemma cont_diff_within_at_euclidean {n : ℕ∞} :
  cont_diff_within_at 𝕜 n f t y ↔ ∀ i, cont_diff_within_at 𝕜 n (λ x, f x i) t y :=
begin
  rw [← (euclidean_space.equiv ι 𝕜).comp_cont_diff_within_at_iff, cont_diff_within_at_pi],
  refl
end

lemma cont_diff_at_euclidean {n : ℕ∞} :
  cont_diff_at 𝕜 n f y ↔ ∀ i, cont_diff_at 𝕜 n (λ x, f x i) y :=
begin
  rw [← (euclidean_space.equiv ι 𝕜).comp_cont_diff_at_iff, cont_diff_at_pi],
  refl
end

lemma cont_diff_on_euclidean {n : ℕ∞} :
  cont_diff_on 𝕜 n f t ↔ ∀ i, cont_diff_on 𝕜 n (λ x, f x i) t :=
begin
  rw [← (euclidean_space.equiv ι 𝕜).comp_cont_diff_on_iff, cont_diff_on_pi],
  refl
end

lemma cont_diff_euclidean {n : ℕ∞} :
  cont_diff 𝕜 n f ↔ ∀ i, cont_diff 𝕜 n (λ x, f x i) :=
begin
  rw [← (euclidean_space.equiv ι 𝕜).comp_cont_diff_iff, cont_diff_pi],
  refl
end

end pi_like

section diffeomorph_unit_ball

open metric (hiding mem_nhds_iff)

variables {n : ℕ∞} {E : Type*} [normed_add_comm_group E] [inner_product_space ℝ E]

lemma cont_diff_homeomorph_unit_ball :
  cont_diff ℝ n $ λ (x : E), (homeomorph_unit_ball x : E) :=
begin
  suffices : cont_diff ℝ n (λ x, (1 + ‖x‖^2).sqrt⁻¹), { exact this.smul cont_diff_id, },
  have h : ∀ (x : E), 0 < 1 + ‖x‖ ^ 2 := λ x, by positivity,
  refine cont_diff.inv _ (λ x, real.sqrt_ne_zero'.mpr (h x)),
  exact (cont_diff_const.add $ cont_diff_norm_sq ℝ).sqrt (λ x, (h x).ne.symm),
end

lemma cont_diff_on_homeomorph_unit_ball_symm
  {f : E → E} (h : ∀ y (hy : y ∈ ball (0 : E) 1), f y = homeomorph_unit_ball.symm ⟨y, hy⟩) :
  cont_diff_on ℝ n f $ ball 0 1 :=
begin
  intros y hy,
  apply cont_diff_at.cont_diff_within_at,
  have hf : f =ᶠ[𝓝 y] λ y, (1 - ‖(y : E)‖^2).sqrt⁻¹ • (y : E),
  { rw eventually_eq_iff_exists_mem,
    refine ⟨ball (0 : E) 1, mem_nhds_iff.mpr ⟨ball (0 : E) 1, set.subset.refl _, is_open_ball, hy⟩,
      λ z hz, _⟩,
    rw h z hz,
    refl, },
  refine cont_diff_at.congr_of_eventually_eq _ hf,
  suffices : cont_diff_at ℝ n (λy, (1 - ‖(y : E)‖^2).sqrt⁻¹) y, { exact this.smul cont_diff_at_id },
  have h : 0 < 1 - ‖(y : E)‖^2, by rwa [mem_ball_zero_iff, ← _root_.abs_one, ← abs_norm_eq_norm,
    ← sq_lt_sq, one_pow, ← sub_pos] at hy,
  refine cont_diff_at.inv _ (real.sqrt_ne_zero'.mpr h),
  refine cont_diff_at.comp _ (cont_diff_at_sqrt h.ne.symm) _,
  exact cont_diff_at_const.sub (cont_diff_norm_sq ℝ).cont_diff_at,
end

end diffeomorph_unit_ball
