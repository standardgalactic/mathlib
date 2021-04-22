/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import topology.continuous_on
import group_theory.submonoid.operations
import algebra.group.prod
import algebra.pointwise
import algebra.big_operators.finprod

/-!
# Theory of topological monoids

In this file we define mixin classes `has_continuous_mul` and `has_continuous_add`. While in many
applications the underlying type is a monoid (multiplicative or additive), we do not require this in
the definitions.
-/

open classical set filter topological_space
open_locale classical topological_space big_operators

variables {ι α X M N : Type*} [topological_space X]

/-- Basic hypothesis to talk about a topological additive monoid or a topological additive
semigroup. A topological additive monoid over `M`, for example, is obtained by requiring both the
instances `add_monoid M` and `has_continuous_add M`. -/
class has_continuous_add (M : Type*) [topological_space M] [has_add M] : Prop :=
(continuous_add : continuous (λ p : M × M, p.1 + p.2))

/-- Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `M`, for example, is obtained by requiring both the instances `monoid M`
and `has_continuous_mul M`. -/
@[to_additive]
class has_continuous_mul (M : Type*) [topological_space M] [has_mul M] : Prop :=
(continuous_mul : continuous (λ p : M × M, p.1 * p.2))

section has_continuous_mul

variables [topological_space M] [has_mul M] [has_continuous_mul M]

@[to_additive]
lemma continuous_mul : continuous (λp:M×M, p.1 * p.2) :=
has_continuous_mul.continuous_mul

@[continuity, to_additive]
lemma continuous.mul {f g : X → M} (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x * g x) :=
continuous_mul.comp (hf.prod_mk hg : _)

-- should `to_additive` be doing this?
attribute [continuity] continuous.add

@[to_additive]
lemma continuous_mul_left (a : M) : continuous (λ b:M, a * b) :=
continuous_const.mul continuous_id

@[to_additive]
lemma continuous_mul_right (a : M) : continuous (λ b:M, b * a) :=
continuous_id.mul continuous_const

@[to_additive]
lemma continuous_on.mul {f g : X → M} {s : set X} (hf : continuous_on f s)
  (hg : continuous_on g s) :
  continuous_on (λx, f x * g x) s :=
(continuous_mul.comp_continuous_on (hf.prod hg) : _)

@[to_additive]
lemma tendsto_mul {a b : M} : tendsto (λp:M×M, p.fst * p.snd) (𝓝 (a, b)) (𝓝 (a * b)) :=
continuous_iff_continuous_at.mp has_continuous_mul.continuous_mul (a, b)

@[to_additive]
lemma filter.tendsto.mul {f g : α → M} {x : filter α} {a b : M}
  (hf : tendsto f x (𝓝 a)) (hg : tendsto g x (𝓝 b)) :
  tendsto (λx, f x * g x) x (𝓝 (a * b)) :=
tendsto_mul.comp (hf.prod_mk_nhds hg)

@[to_additive]
lemma filter.tendsto.const_mul (b : M) {c : M} {f : α → M} {l : filter α}
  (h : tendsto (λ (k:α), f k) l (𝓝 c)) : tendsto (λ (k:α), b * f k) l (𝓝 (b * c)) :=
tendsto_const_nhds.mul h

@[to_additive]
lemma filter.tendsto.mul_const (b : M) {c : M} {f : α → M} {l : filter α}
  (h : tendsto (λ (k:α), f k) l (𝓝 c)) : tendsto (λ (k:α), f k * b) l (𝓝 (c * b)) :=
h.mul tendsto_const_nhds

@[to_additive]
lemma continuous_at.mul {f g : X → M} {x : X} (hf : continuous_at f x) (hg : continuous_at g x) :
  continuous_at (λx, f x * g x) x :=
hf.mul hg

@[to_additive]
lemma continuous_within_at.mul {f g : X → M} {s : set X} {x : X} (hf : continuous_within_at f s x)
  (hg : continuous_within_at g s x) :
  continuous_within_at (λx, f x * g x) s x :=
hf.mul hg

@[to_additive]
instance [topological_space N] [has_mul N] [has_continuous_mul N] : has_continuous_mul (M × N) :=
⟨((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).prod_mk
 ((continuous_snd.comp continuous_fst).mul (continuous_snd.comp continuous_snd))⟩

@[to_additive]
instance pi.has_continuous_mul {C : ι → Type*} [∀ i, topological_space (C i)]
  [∀ i, has_mul (C i)] [∀ i, has_continuous_mul (C i)] : has_continuous_mul (Π i, C i) :=
{ continuous_mul := continuous_pi (λ i, continuous.mul
    ((continuous_apply i).comp continuous_fst) ((continuous_apply i).comp continuous_snd)) }

@[priority 100, to_additive]
instance has_continuous_mul_of_discrete_topology [topological_space N]
  [has_mul N] [discrete_topology N] : has_continuous_mul N :=
⟨continuous_of_discrete_topology⟩

open_locale filter

open function

@[to_additive]
lemma has_continuous_mul.of_nhds_one {M : Type*} [monoid M] [topological_space M]
  (hmul : tendsto (uncurry ((*) : M → M → M)) (𝓝 1 ×ᶠ 𝓝 1) $ 𝓝 1)
  (hleft : ∀ x₀ : M, 𝓝 x₀ = map (λ x, x₀*x) (𝓝 1))
  (hright : ∀ x₀ : M, 𝓝 x₀ = map (λ x, x*x₀) (𝓝 1)) : has_continuous_mul M :=
⟨begin
    rw continuous_iff_continuous_at,
    rintros ⟨x₀, y₀⟩,
    have key : (λ p : M × M, x₀ * p.1 * (p.2 * y₀)) = ((λ x, x₀*x) ∘ (λ x, x*y₀)) ∘ (uncurry (*)),
    { ext p, simp [uncurry, mul_assoc] },
    have key₂ : (λ x, x₀*x) ∘ (λ x, y₀*x) = λ x, (x₀ *y₀)*x,
    { ext x, simp },
    calc map (uncurry (*)) (𝓝 (x₀, y₀))
        = map (uncurry (*)) (𝓝 x₀ ×ᶠ 𝓝 y₀) : by rw nhds_prod_eq
    ... = map (λ (p : M × M), x₀ * p.1 * (p.2 * y₀)) ((𝓝 1) ×ᶠ (𝓝 1))
            : by rw [uncurry, hleft x₀, hright y₀, prod_map_map_eq, filter.map_map]
    ... = map ((λ x, x₀ * x) ∘ λ x, x * y₀) (map (uncurry (*)) (𝓝 1 ×ᶠ 𝓝 1))
            : by { rw [key, ← filter.map_map], }
    ... ≤ map ((λ (x : M), x₀ * x) ∘ λ x, x * y₀) (𝓝 1) : map_mono hmul
    ... = 𝓝 (x₀*y₀) : by rw [← filter.map_map, ← hright, hleft y₀, filter.map_map, key₂, ← hleft]
  end⟩

@[to_additive]
lemma has_continuous_mul_of_comm_of_nhds_one (M : Type*) [comm_monoid M] [topological_space M]
  (hmul : tendsto (uncurry ((*) : M → M → M)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1))
  (hleft : ∀ x₀ : M, 𝓝 x₀ = map (λ x, x₀*x) (𝓝 1)) : has_continuous_mul M :=
begin
  apply has_continuous_mul.of_nhds_one hmul hleft,
  intros x₀,
  simp_rw [mul_comm, hleft x₀]
end

end has_continuous_mul

section has_continuous_mul

variables [topological_space M] [monoid M] [has_continuous_mul M]

@[to_additive]
lemma submonoid.top_closure_mul_self_subset (s : submonoid M) :
  (closure (s : set M)) * closure (s : set M) ⊆ closure (s : set M) :=
calc
(closure (s : set M)) * closure (s : set M)
    = (λ p : M × M, p.1 * p.2) '' (closure ((s : set M).prod s)) : by simp [closure_prod_eq]
... ⊆ closure ((λ p : M × M, p.1 * p.2) '' ((s : set M).prod s)) :
  image_closure_subset_closure_image continuous_mul
... = closure s : by simp [s.coe_mul_self_eq]

@[to_additive]
lemma submonoid.top_closure_mul_self_eq (s : submonoid M) :
  (closure (s : set M)) * closure (s : set M) = closure (s : set M) :=
subset.antisymm
  s.top_closure_mul_self_subset
  (λ x hx, ⟨x, 1, hx, subset_closure s.one_mem, mul_one _⟩)

/-- The (topological-space) closure of a submonoid of a space `M` with `has_continuous_mul` is
itself a submonoid. -/
@[to_additive "The (topological-space) closure of an additive submonoid of a space `M` with
`has_continuous_add` is itself an additive submonoid."]
def submonoid.topological_closure (s : submonoid M) : submonoid M :=
{ carrier := closure (s : set M),
  one_mem' := subset_closure s.one_mem,
  mul_mem' := λ a b ha hb, s.top_closure_mul_self_subset ⟨a, b, ha, hb, rfl⟩ }

@[to_additive]
instance submonoid.topological_closure_has_continuous_mul (s : submonoid M) :
  has_continuous_mul (s.topological_closure) :=
{ continuous_mul :=
  begin
    apply continuous_induced_rng,
    change continuous (λ p : s.topological_closure × s.topological_closure, (p.1 : M) * (p.2 : M)),
    continuity,
  end }

lemma submonoid.submonoid_topological_closure (s : submonoid M) :
  s ≤ s.topological_closure :=
subset_closure

lemma submonoid.is_closed_topological_closure (s : submonoid M) :
  is_closed (s.topological_closure : set M) :=
by convert is_closed_closure

lemma submonoid.topological_closure_minimal
  (s : submonoid M) {t : submonoid M} (h : s ≤ t) (ht : is_closed (t : set M)) :
  s.topological_closure ≤ t :=
closure_minimal h ht

@[to_additive exists_open_nhds_zero_half]
lemma exists_open_nhds_one_split {s : set M} (hs : s ∈ 𝓝 (1 : M)) :
  ∃ V : set M, is_open V ∧ (1 : M) ∈ V ∧ ∀ (v ∈ V) (w ∈ V), v * w ∈ s :=
have ((λa:M×M, a.1 * a.2) ⁻¹' s) ∈ 𝓝 ((1, 1) : M × M),
  from tendsto_mul (by simpa only [one_mul] using hs),
by simpa only [prod_subset_iff] using exists_nhds_square this

@[to_additive exists_nhds_zero_half]
lemma exists_nhds_one_split {s : set M} (hs : s ∈ 𝓝 (1 : M)) :
  ∃ V ∈ 𝓝 (1 : M), ∀ (v ∈ V) (w ∈ V), v * w ∈ s :=
let ⟨V, Vo, V1, hV⟩ := exists_open_nhds_one_split hs
in ⟨V, mem_nhds_sets Vo V1, hV⟩

@[to_additive exists_nhds_zero_quarter]
lemma exists_nhds_one_split4 {u : set M} (hu : u ∈ 𝓝 (1 : M)) :
  ∃ V ∈ 𝓝 (1 : M),
    ∀ {v w s t}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → v * w * s * t ∈ u :=
begin
  rcases exists_nhds_one_split hu with ⟨W, W1, h⟩,
  rcases exists_nhds_one_split W1 with ⟨V, V1, h'⟩,
  use [V, V1],
  intros v w s t v_in w_in s_in t_in,
  simpa only [mul_assoc] using h _ (h' v v_in w w_in) _ (h' s s_in t t_in)
end

/-- Given a neighborhood `U` of `1` there is an open neighborhood `V` of `1`
such that `VV ⊆ U`. -/
@[to_additive "Given a open neighborhood `U` of `0` there is a open neighborhood `V` of `0`
  such that `V + V ⊆ U`."]
lemma exists_open_nhds_one_mul_subset {U : set M} (hU : U ∈ 𝓝 (1 : M)) :
  ∃ V : set M, is_open V ∧ (1 : M) ∈ V ∧ V * V ⊆ U :=
begin
  rcases exists_open_nhds_one_split hU with ⟨V, Vo, V1, hV⟩,
  use [V, Vo, V1],
  rintros _ ⟨x, y, hx, hy, rfl⟩,
  exact hV _ hx _ hy
end

@[to_additive]
lemma tendsto_list_prod {f : ι → α → M} {x : filter α} {a : ι → M} :
  ∀ l:list ι, (∀i∈l, tendsto (f i) x (𝓝 (a i))) →
    tendsto (λb, (l.map (λc, f c b)).prod) x (𝓝 ((l.map a).prod))
| []       _ := by simp [tendsto_const_nhds]
| (f :: l) h :=
  begin
    simp only [list.map_cons, list.prod_cons],
    exact (h f (list.mem_cons_self _ _)).mul
      (tendsto_list_prod l (assume c hc, h c (list.mem_cons_of_mem _ hc)))
  end

@[to_additive]
lemma continuous_list_prod {f : ι → X → M} (l : list ι)
  (h : ∀i∈l, continuous (f i)) :
  continuous (λa, (l.map (λi, f i a)).prod) :=
continuous_iff_continuous_at.2 $ assume x, tendsto_list_prod l $ assume c hc,
  continuous_iff_continuous_at.1 (h c hc) x

-- @[to_additive continuous_smul]
@[continuity]
lemma continuous_pow : ∀ n : ℕ, continuous (λ a : M, a ^ n)
| 0 := by simpa using continuous_const
| (k+1) := by { simp only [pow_succ], exact continuous_id.mul (continuous_pow _) }

@[continuity]
lemma continuous.pow {f : X → M} (h : continuous f) (n : ℕ) :
  continuous (λ b, (f b) ^ n) :=
(continuous_pow n).comp h

lemma continuous_on_pow {s : set M} (n : ℕ) : continuous_on (λ x, x ^ n) s :=
(continuous_pow n).continuous_on

end has_continuous_mul

section op

open opposite

/-- Put the same topological space structure on the opposite monoid as on the original space. -/
instance [_i : topological_space α] : topological_space αᵒᵖ :=
topological_space.induced (unop : αᵒᵖ → α) _i

variables [topological_space α]

lemma continuous_unop : continuous (unop : αᵒᵖ → α) := continuous_induced_dom
lemma continuous_op : continuous (op : α → αᵒᵖ) := continuous_induced_rng continuous_id

variables [monoid α] [has_continuous_mul α]

/-- If multiplication is continuous in the monoid `α`, then it also is in the monoid `αᵒᵖ`. -/
instance : has_continuous_mul αᵒᵖ :=
⟨ let h₁ := @continuous_mul α _ _ _ in
  let h₂ : continuous (λ p : α × α, _) := continuous_snd.prod_mk continuous_fst in
  continuous_induced_rng $ (h₁.comp h₂).comp (continuous_unop.prod_map continuous_unop) ⟩

end op

namespace units

open opposite

variables [topological_space α] [monoid α]

/-- The units of a monoid are equipped with a topology, via the embedding into `α × α`. -/
instance : topological_space (units α) :=
topological_space.induced (embed_product α) (by apply_instance)

lemma continuous_embed_product : continuous (embed_product α) :=
continuous_induced_dom

lemma continuous_coe : continuous (coe : units α → α) :=
by convert continuous_fst.comp continuous_induced_dom

variables [has_continuous_mul α]

/-- If multiplication on a monoid is continuous, then multiplication on the units of the monoid,
with respect to the induced topology, is continuous.

Inversion is also continuous, but we register this in a later file, `topology.algebra.group`,
because the predicate `has_continuous_inv` has not yet been defined. -/
instance : has_continuous_mul (units α) :=
⟨ let h := @continuous_mul (α × αᵒᵖ) _ _ _ in
  continuous_induced_rng $ h.comp $ continuous_embed_product.prod_map continuous_embed_product ⟩

end units

section

variables [topological_space M] [comm_monoid M]

@[to_additive]
lemma submonoid.mem_nhds_one (S : submonoid M) (oS : is_open (S : set M)) :
  (S : set M) ∈ 𝓝 (1 : M) :=
mem_nhds_sets oS S.one_mem

variable [has_continuous_mul M]

@[to_additive]
lemma tendsto_multiset_prod {f : ι → α → M} {x : filter α} {a : ι → M} (s : multiset ι) :
  (∀ i ∈ s, tendsto (f i) x (𝓝 (a i))) →
    tendsto (λb, (s.map (λc, f c b)).prod) x (𝓝 ((s.map a).prod)) :=
by { rcases s with ⟨l⟩, simpa using tendsto_list_prod l }

@[to_additive]
lemma tendsto_finset_prod {f : ι → α → M} {x : filter α} {a : ι → M} (s : finset ι) :
  (∀ i ∈ s, tendsto (f i) x (𝓝 (a i))) → tendsto (λb, ∏ c in s, f c b) x (𝓝 (∏ c in s, a c)) :=
tendsto_multiset_prod _

@[to_additive, continuity]
lemma continuous_multiset_prod {f : ι → X → M} (s : multiset ι) :
  (∀i ∈ s, continuous (f i)) → continuous (λ a, (s.map (λ i, f i a)).prod) :=
by { rcases s with ⟨l⟩, simpa using continuous_list_prod l }

attribute [continuity] continuous_multiset_sum

@[continuity, to_additive]
lemma continuous_finset_prod {f : ι → X → M} (s : finset ι) :
  (∀ i ∈ s, continuous (f i)) → continuous (λa, ∏ i in s, f i a) :=
continuous_multiset_prod _

-- should `to_additive` be doing this?
attribute [continuity] continuous_finset_sum

open function

@[to_additive] lemma continuous_finprod {f : ι → X → M} (hc : ∀ i, continuous (f i))
  (hf : locally_finite (λ i, mul_support (f i))) :
  continuous (λ x, ∏ᶠ i, f i x) :=
begin
  refine continuous_iff_continuous_at.2 (λ x, _),
  rcases hf x with ⟨U, hxU, hUf⟩,
  have : continuous_at (λ x, ∏ i in hUf.to_finset, f i x) x,
    from tendsto_finset_prod _ (λ i hi, (hc i).continuous_at),
  refine this.congr (mem_sets_of_superset hxU $ λ y hy, _),
  refine (finprod_eq_prod_of_mul_support_subset _ (λ i hi, _)).symm,
  rw [hUf.coe_to_finset],
  exact ⟨y, hi, hy⟩
end

@[to_additive] lemma continuous_finprod_cond {f : ι → X → M} {p : ι → Prop}
  (hc : ∀ i, p i → continuous (f i)) (hf : locally_finite (λ i, mul_support (f i))) :
  continuous (λ x, ∏ᶠ i (hi : p i), f i x) :=
begin
  simp only [← finprod_subtype_eq_finprod_cond],
  exact continuous_finprod (λ i, hc i i.2) (hf.comp_injective subtype.coe_injective)
end

end

instance additive.has_continuous_add {M} [h : topological_space M] [has_mul M]
  [has_continuous_mul M] : @has_continuous_add (additive M) h _ :=
{ continuous_add := @continuous_mul M _ _ _  }

instance multiplicative.has_continuous_mul {M} [h : topological_space M] [has_add M]
  [has_continuous_add M] : @has_continuous_mul (multiplicative M) h _ :=
{ continuous_mul := @continuous_add M _ _ _  }
