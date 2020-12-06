/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller.
-/
import combinatorics.simple_graph.basic
import algebra.big_operators.basic
/-!
# Degree-sum formula and handshaking lemma

The degree-sum formula is that the sum of the degrees of a finite
graph is equal to twice the number of edges.  The handshaking lemma is
a corollary, which is that the number of odd-degree vertices is even.

## Main definitions

- A `dart` is a directed edge, consisting of a vertex and an edge incident to it.
- `simple_graph.sum_degrees_eq_twice_card_edges` is the degree-sum formula.
- `simple_graph.card_odd_degree_vertices_is_even` is the handshaking lemma.
- `simple_graph.card_odd_degree_vertices_ne_is_odd` is that the number of odd-degree
  vertices different from a given odd-degree vertex is odd.
- `simple_graph.exists_ne_odd_degree_if_exists_odd` is that the existence of an
  odd-degree vertex implies the existence of another one.

## Implementation notes

We give a combinatorial proof by using the fact that the map from
darts to vertices has fibers whose cardinalities are the degrees and
that the map from darts to edges is 2-to-1.

## Tags

simple graphs, sums
-/
open finset

open_locale big_operators

namespace simple_graph
universes u v
variables {V : Type u} (G : simple_graph V)

/-- A `dart` is a directed edge, consisting of a vertex and an edge incident to it -/
@[reducible]
def dart := Σ (v : V), G.incidence_set v

/-- Gets the vertex at the start of the dart. -/
def dart_vert : G.dart → V := sigma.fst

/-- Gets the edge that the dart runs through. -/
def dart_edge : G.dart → sym2 V := λ d, d.snd

lemma dart_vert_mem (d : G.dart) : G.dart_vert d ∈ G.dart_edge d :=
by { rcases d with ⟨v,e,he,hv⟩, simp [dart_vert, dart_edge, hv] }

lemma dart_edge_mem (d : G.dart) : G.dart_edge d ∈ G.edge_set :=
by { rcases d with ⟨v,e,he,hv⟩, exact he }

lemma dart_edge_mem_incidence_set (d : G.dart) : G.dart_edge d ∈ G.incidence_set (G.dart_vert d) :=
d.snd.property

lemma dart.ext {d₁ d₂ : G.dart}
  (hv : G.dart_vert d₁ = G.dart_vert d₂) (he : G.dart_edge d₁ = G.dart_edge d₂) :
  d₁ = d₂ :=
by { rcases d₁ with ⟨v₁, e₁, he₁, hv₁⟩, rcases d₂ with ⟨v₂, e₂, he₂, hv₂⟩,
     dsimp only [dart_vert, dart_edge, subtype.coe_mk] at hv he, subst v₂, subst e₂, }

lemma dart.ext_iff (d₁ d₂ : G.dart) :
  d₁ = d₂ ↔ G.dart_vert d₁ = G.dart_vert d₂ ∧ G.dart_edge d₁ = G.dart_edge d₂ :=
by { split, rintro rfl, tauto, rintro ⟨hv, he⟩, apply dart.ext G hv he }

def dart_rev [decidable_eq V] (d : G.dart) : G.dart :=
⟨sym2.mem.other' (G.dart_vert_mem d), G.dart_edge d, G.edge_mem_other_incident_set d.snd.property⟩

@[simp]
lemma dart_edge_of_dart_rev [decidable_eq V] (d : G.dart) :
  G.dart_edge (G.dart_rev d) = G.dart_edge d := rfl

lemma dart_rev_invol [decidable_eq V] (d : G.dart) : G.dart_rev (G.dart_rev d) = d :=
begin
  apply dart.ext,
  apply sym2.other_invol',
  rcases d with ⟨v, e, he, hv⟩,
  simp [dart_edge, dart_rev],
end

lemma dart_rev_no_fixedpoints [decidable_eq V] (d : G.dart) : d ≠ G.dart_rev d :=
begin
  intro h, rw dart.ext_iff at h,
  dsimp [dart_vert, dart_rev] at h,
  apply G.edge_other_ne (G.dart_edge_mem d) (G.dart_vert_mem d),
  convert h.1.symm, rw sym2.other_eq_other',
end

lemma dart_edge_eq_iff [decidable_eq V] (d₁ d₂ : G.dart) :
  G.dart_edge d₁ = G.dart_edge d₂ ↔ d₁ = d₂ ∨ d₁ = G.dart_rev d₂ :=
begin
  split,
  { rw [dart.ext_iff, dart.ext_iff],
    rcases d₁ with ⟨v₁, e₁, he₁, hv₁⟩,
    rcases d₂ with ⟨v₂, e₂, he₂, hv₂⟩,
    dsimp [dart_edge, dart_vert, dart_rev],
    rintro rfl, simp only [and_true, eq_self_iff_true],
    by_cases hveq : v₁ = v₂,
    { left, subst hveq, },
    { right,
      have he : e₁ = ⟦(v₁, v₂)⟧ := (sym2.elems_iff_eq hveq).mp ⟨hv₁, hv₂⟩,
      subst e₁,
      have h' := sym2.mem_other_spec' hv₂,
      rw [sym2.eq_swap, sym2.congr_left] at h',
      convert h'.symm, }, },
  { intro h, cases h; subst d₁, refl, },
end

def dart_from_incidence_set (v : V) : G.incidence_set v → G.dart := λ ee, ⟨v, ee⟩

lemma dart_from_incidence_set_inj (v : V) : function.injective (G.dart_from_incidence_set v) :=
by { dsimp only [dart_from_incidence_set], exact sigma_mk_injective }

variables [fintype V] [decidable_eq V] [decidable_rel G.adj]

lemma dart_vert_fiber_card_eq_degree (v : V) :
  (univ.filter (λ d, G.dart_vert d = v)).card = G.degree v :=
begin
  have hh := card_image_of_injective univ (G.dart_from_incidence_set_inj v),
  rw [finset.card_univ, card_incidence_set_eq_degree] at hh,
  convert hh,
  ext d, simp,
  split,
  { rintro rfl, use G.dart_edge d, use G.dart_edge_mem_incidence_set d,
    apply dart.ext; simp [dart_from_incidence_set, dart_vert, dart_edge], },
  { rintro ⟨e, he, rfl⟩, simp [dart_from_incidence_set, dart_vert] },
end

lemma dart_card_eq_sum_degrees : fintype.card G.dart = ∑ v, G.degree v :=
begin
  convert_to (univ : finset G.dart).card = _,
  rw @card_eq_sum_card_fiberwise _ _ _ G.dart_vert _ univ (λ d h, mem_univ _),
  simp [G.dart_vert_fiber_card_eq_degree],
end

lemma dart_edge_fiber_card_eq_2 (e : sym2 V) (h : e ∈ G.edge_set) :
  (filter (λ (d : G.dart), G.dart_edge d = e) univ).card = 2 :=
begin
  refine quotient.ind (λ p h, _) e h, cases p with v w,
  let d : G.dart := ⟨v, ⟦(v, w)⟧, h, sym2.mk_has_mem _ _⟩,
  convert_to _ = finset.card {d, G.dart_rev d},
  { rw [card_insert_of_not_mem, card_singleton], simp [G.dart_rev_no_fixedpoints d], },
  congr, ext d',
  simp only [true_and, mem_filter, mem_insert, mem_univ, mem_singleton],
  exact G.dart_edge_eq_iff d' d,
end

lemma dart_card_eq_twice_card_edges : fintype.card G.dart = 2 * G.edge_finset.card :=
begin
  convert_to (univ : finset G.dart).card = _,
  rw @card_eq_sum_card_fiberwise _ _ _ G.dart_edge _ G.edge_finset
    (λ d h, by { rw mem_edge_finset, apply G.dart_edge_mem }),
  rw @sum_congr _ _ G.edge_finset G.edge_finset
    (λ e, (univ.filter (λ (x : G.dart), G.dart_edge x = e)).card) (λ e, 2) _ rfl,
  simp [mul_comm],
  intros e h, rw mem_edge_finset at h,
  exact G.dart_edge_fiber_card_eq_2 e h,
end

/-- The degree-sum formula. -/
theorem sum_degrees_eq_twice_card_edges : ∑ v, G.degree v = 2 * G.edge_finset.card :=
G.dart_card_eq_sum_degrees.symm.trans G.dart_card_eq_twice_card_edges

/- TODO nat.odd and nat.even used to be decidable predicates -- where did those go? -/
instance odd_decidable (n : ℕ) : decidable (odd n) :=
begin
  sorry
end

theorem card_odd_degree_vertices_is_even : even (univ.filter (λ v, odd (G.degree v))).card :=
begin
  sorry
end

theorem card_odd_degree_vertices_ne_is_odd (v : V) (h : odd (G.degree v)) :
  odd (univ.filter (λ w, w ≠ v ∧ odd (G.degree w))).card :=
begin
  sorry
end

theorem exists_ne_odd_degree_if_exists_odd (v : V) (h : odd (G.degree v)) :
  ∃ (w : V), w ≠ v ∧ odd (G.degree w) :=
begin
  sorry
end

end simple_graph
