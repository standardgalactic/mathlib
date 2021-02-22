/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Martin Zinkevich
-/
import measure_theory.measure_space
import tactic.fin_cases

--import algebra.big_operators.intervals
--import data.finset.intervals

/-!
# Lemmas regarding `is_pi_system`.

`is_pi_system` is similar, but not identical to, the classic π-system encountered in measure
theory. In particular, it is not required to be nonempty, and it isn't closed under disjoint
intersection (thus neither more nor less general than a typical π-system).

## Main statements

* `generate_pi_system g` gives the minimal pi system containing `g`.
  This can be considered a Galois insertion into both measurable spaces and sets.

* `generate_from_generate_pi_system_eq` proves that if you generate a pi_system
  then a measurable space versus generating a measurable space gives the same result. This
  is useful because there are connections between a independent sets that are pi systems
  the generated independent spaces.

* `mem_generate_pi_system_Union_elim` and `mem_generate_pi_system_Union_elim'` are theorems
  that show that any element of the supremum of the union of a set of pi systems can be
  represented as the intersection of a finite number of elements from these sets.

## Implementation details

* is_pi_system is a predicate, not a type. Thus, we don't explicitly define the galois
  insertion, nor do we define a complete lattice. In theory, we could define a complete
  lattice and galois insertion on subtype is_pi_system.

-/

open measure_theory measurable_space
open_locale classical

lemma is_pi_system.singleton {α} (S : set α) : is_pi_system ({S} : set (set α)) :=
begin
  intros s t h_s h_t h_ne,
  rw [set.mem_singleton_iff.1 h_s, set.mem_singleton_iff.1 h_t, set.inter_self,
      set.mem_singleton_iff],
end

inductive generate_pi_system {α} (g : set (set α)) : set (set α)
| base {s : set α} (h_s : s ∈ g) : generate_pi_system s
| inter {s t : set α} (h_s : generate_pi_system s)  (h_t : generate_pi_system t)
  (h_nonempty : (s ∩ t).nonempty) : generate_pi_system (s ∩ t)

lemma is_pi_system_generate_pi_system {α} (g : set (set α)) :
  is_pi_system (generate_pi_system g) :=
  λ s t h_s h_t h_nonempty, generate_pi_system.inter h_s h_t h_nonempty

lemma generate_pi_system_subset {α} {g t : set (set α)} (h_t : is_pi_system t)
  (h_sub : g ⊆ t) : (generate_pi_system g : (set (set α))) ⊆ t := begin
  rw set.subset_def,
  intros x h,
  induction h with s h_s s u h_gen_s h_gen_u h_nonempty h_s h_u,
  apply h_sub h_s,
  apply h_t _ _ h_s h_u h_nonempty
end

lemma generate_pi_system_eq {α} {g : set (set α)} (h_pi : is_pi_system g) :
  generate_pi_system g = g := begin
  apply le_antisymm,
  apply generate_pi_system_subset,
  apply h_pi,
  apply set.subset.refl,
  apply generate_pi_system.base,
end

lemma generate_pi_system_measurable_set {α} [M : measurable_space α] {g : set (set α)}
  (h_meas_g : ∀ s ∈ g, measurable_set s) (t : set α)
  (h_in_pi : generate_pi_system g t) : measurable_set t :=
begin
  induction h_in_pi with s h_s s u h_gen_s h_gen_u h_nonempty h_s h_u,
  apply h_meas_g _ h_s,
  apply measurable_set.inter h_s h_u,
end

lemma generate_from_measurable_set_of_generate_pi_system {α} {g : set (set α)} (t : set α) : generate_pi_system g t →
  (measurable_space.generate_from g).measurable_set' t := begin
  apply generate_pi_system_measurable_set,
  intros s h_s_in_g,
  apply measurable_space.measurable_set_generate_from h_s_in_g,
end

lemma generate_from_generate_pi_system_eq {α} {g : set (set α)} :
  (measurable_space.generate_from (generate_pi_system g)) =
  (measurable_space.generate_from g) := begin
  apply le_antisymm;apply measurable_space.generate_from_le,
  { intros t h_t,
    apply generate_from_measurable_set_of_generate_pi_system,
    apply h_t },
  { intros t h_t, apply measurable_space.measurable_set_generate_from,
    apply generate_pi_system.base h_t },
end

/- This theorem shows that every element of the pi system generated by the union of the
   pi systems can be represented by a finite union of elements from the pi systems. -/
lemma mem_generate_pi_system_Union_elim {α} {β : Type*} {g : β → (set (set α))}
  (h_pi : ∀ b : β, is_pi_system (g b))
  (t : set α)
  (h_t : t ∈ generate_pi_system (⋃ (b : β), g b)) :
  (∃ (T : finset β) (f : β → set α), (t = ⋂ b ∈ T, f b) ∧ (∀ b ∈ T, f b ∈ (g b))) :=
begin
  induction h_t with s h_s s t' h_gen_s h_gen_t' h_nonempty h_s h_t',
  { rcases h_s with ⟨t', ⟨⟨b, rfl⟩, h_s_in_t'⟩⟩,
    apply exists.intro {b},
    use (λ b', s),
    split,
    { ext a, split; intros h1, simp, apply (λ _ _, h1),
      simp at h1, apply h1 b (finset.mem_singleton_self _) },
    { intros b' h_b', rw finset.mem_singleton at h_b',
      rw h_b', apply h_s_in_t' } },
  { rcases h_t' with ⟨T_t', ⟨f_t', ⟨rfl, h_t'⟩⟩⟩,
    rcases h_s with ⟨T_s, ⟨f_s, ⟨rfl, h_s⟩ ⟩ ⟩,
    use [(T_s ∪ T_t'), (λ (b:β),
      if (b ∈ T_s) then (if (b ∈ T_t') then (f_s b ∩ (f_t' b)) else (f_s b))
      else (if (b ∈ T_t') then (f_t' b) else (∅:set α)))],
    split,
    { ext a,
      split; intros h1; simp at h1; simp [h1],
      { intros b h_b_in, split_ifs,
        apply set.mem_inter (h1.left b h) (h1.right b h_1),
        apply h1.left b h,
        apply h1.right b h_1,
        apply false.elim (h_b_in.elim h h_1) },
      split,
      { intros b h_b_in,
        have h2 := h1 b (or.inl h_b_in),
        rw if_pos h_b_in at h2,
        split_ifs at h2, apply h2.left, apply h2 },
      { intros b h_b_in,
        have h2 := h1 b (or.inr h_b_in),
        rw if_pos h_b_in at h2,
        split_ifs at h2, apply h2.right, apply h2 } },
    intros b h_b,
    split_ifs,
    apply h_pi b _ _ (h_s b h) (h_t' b h_1) (set.nonempty.mono _ h_nonempty),
    apply set.inter_subset_inter,
    { apply set.subset.trans,
      apply set.Inter_subset, apply b,
      apply set.Inter_subset (λ (H : b ∈ T_s), f_s b) h },
    { apply set.subset.trans, apply set.Inter_subset, apply b, apply set.Inter_subset, apply h_1 },
    apply h_s _ h, apply h_t' _ h_1,
    rw finset.mem_union at h_b,
    apply false.elim (h_b.elim h h_1) },
end

/- This is similar to mem_generate_pi_system_Union_elim', but
   focuses on a set of elements in b, as opposed to the whole type. -/
lemma mem_generate_pi_system_Union_elim' {α} {β : Type*} {g : β → (set (set α))} {s: set β}
  (h_pi : ∀ b ∈ s, is_pi_system (g b))
  (t : set α)
  (h_t : t ∈ generate_pi_system (⋃ b ∈ s, g b)) :
  (∃ (T : finset β) (f : β → set α), (↑T ⊆ s) ∧ (t = ⋂ b ∈ T, f b) ∧ (∀ b ∈ T, f b ∈ (g b))) :=
begin
  classical,
  have h1 := @mem_generate_pi_system_Union_elim α (subtype s) (g ∘ subtype.val) _ t _,
  rcases h1 with ⟨T, ⟨f,⟨ rfl, h_t'⟩ ⟩⟩,
  use (T.image subtype.val),
  use (function.extend subtype.val f (λ (b:β), (∅ : set α))),
  split,
  { simp },
  split,
  { ext a, split;
    { simp only [set.mem_Inter, subtype.forall, finset.set_bInter_finset_image],
      intros h1 b h_b h_b_in_T,
      have h2 := h1 b h_b h_b_in_T, revert h2,
      rw function.extend_apply subtype.val_injective, apply id } },
  { intros b h_b,
    simp_rw [finset.mem_image, exists_prop, subtype.exists,
             exists_and_distrib_right, exists_eq_right] at h_b,
    cases h_b,
    have h_b_alt : b = (subtype.mk b h_b_w).val := rfl,
    rw h_b_alt,
    rw function.extend_apply subtype.val_injective,
    apply h_t', apply h_b_h },
  { intros b, apply h_pi b.val b.property, },
  { have h1 : (⋃ (b : subtype s), (g ∘ subtype.val) b) = (⋃ (b : β) (H : b ∈ s), g b),
    { ext x, simp only [exists_prop, set.mem_Union, function.comp_app, subtype.exists,
        subtype.coe_mk], refl },
    rw h1, apply h_t },
end
