/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/

import field_theory.intermediate_field
import field_theory.separable
import field_theory.splitting_field
import ring_theory.tensor_product

/-!
# Adjoining Elements to Fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we introduce the notion of adjoining elements to fields.
This isn't quite the same as adjoining elements to rings.
For example, `algebra.adjoin K {x}` might not include `x⁻¹`.

## Main results

- `adjoin_adjoin_left`: adjoining S and then T is the same as adjoining `S ∪ T`.
- `bot_eq_top_of_rank_adjoin_eq_one`: if `F⟮x⟯` has dimension `1` over `F` for every `x`
  in `E` then `F = E`

## Notation

 - `F⟮α⟯`: adjoin a single element `α` to `F`.
-/

open finite_dimensional polynomial
open_locale classical polynomial

namespace intermediate_field

section adjoin_def
variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)

/-- `adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`. -/
def adjoin : intermediate_field F E :=
{ algebra_map_mem' := λ x, subfield.subset_closure (or.inl (set.mem_range_self x)),
  ..subfield.closure (set.range (algebra_map F E) ∪ S) }

end adjoin_def

section lattice
variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

@[simp] lemma adjoin_le_iff {S : set E} {T : intermediate_field F E} : adjoin F S ≤ T ↔ S ≤ T :=
⟨λ H, le_trans (le_trans (set.subset_union_right _ _) subfield.subset_closure) H,
  λ H, (@subfield.closure_le E _ (set.range (algebra_map F E) ∪ S) T.to_subfield).mpr
  (set.union_subset (intermediate_field.set_range_subset T) H)⟩

lemma gc : galois_connection (adjoin F : set E → intermediate_field F E) coe := λ _ _, adjoin_le_iff

/-- Galois insertion between `adjoin` and `coe`. -/
def gi : galois_insertion (adjoin F : set E → intermediate_field F E) coe :=
{ choice := λ s hs, (adjoin F s).copy s $ le_antisymm (gc.le_u_l s) hs,
  gc := intermediate_field.gc,
  le_l_u := λ S, (intermediate_field.gc (S : set E) (adjoin F S)).1 $ le_rfl,
  choice_eq := λ _ _, copy_eq _ _ _ }

instance : complete_lattice (intermediate_field F E) :=
galois_insertion.lift_complete_lattice intermediate_field.gi

instance : inhabited (intermediate_field F E) := ⟨⊤⟩

lemma coe_bot : ↑(⊥ : intermediate_field F E) = set.range (algebra_map F E) :=
begin
  change ↑(subfield.closure (set.range (algebra_map F E) ∪ ∅)) = set.range (algebra_map F E),
  simp [←set.image_univ, ←ring_hom.map_field_closure]
end

lemma mem_bot {x : E} : x ∈ (⊥ : intermediate_field F E) ↔ x ∈ set.range (algebra_map F E) :=
set.ext_iff.mp coe_bot x

@[simp] lemma bot_to_subalgebra : (⊥ : intermediate_field F E).to_subalgebra = ⊥ :=
by { ext, rw [mem_to_subalgebra, algebra.mem_bot, mem_bot] }

@[simp] lemma coe_top : ↑(⊤ : intermediate_field F E) = (set.univ : set E) := rfl

@[simp] lemma mem_top {x : E} : x ∈ (⊤ : intermediate_field F E) :=
trivial

@[simp] lemma top_to_subalgebra : (⊤ : intermediate_field F E).to_subalgebra = ⊤ :=
rfl

@[simp] lemma top_to_subfield : (⊤ : intermediate_field F E).to_subfield = ⊤ :=
rfl

@[simp, norm_cast]
lemma coe_inf (S T : intermediate_field F E) : (↑(S ⊓ T) : set E) = S ∩ T := rfl

@[simp]
lemma mem_inf {S T : intermediate_field F E} {x : E} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := iff.rfl

@[simp] lemma inf_to_subalgebra (S T : intermediate_field F E) :
  (S ⊓ T).to_subalgebra = S.to_subalgebra ⊓ T.to_subalgebra :=
rfl

@[simp] lemma inf_to_subfield (S T : intermediate_field F E) :
  (S ⊓ T).to_subfield = S.to_subfield ⊓ T.to_subfield :=
rfl

@[simp, norm_cast]
lemma coe_Inf (S : set (intermediate_field F E)) : (↑(Inf S) : set E) = Inf (coe '' S) := rfl

@[simp] lemma Inf_to_subalgebra (S : set (intermediate_field F E)) :
  (Inf S).to_subalgebra = Inf (to_subalgebra '' S) :=
set_like.coe_injective $ by simp [set.sUnion_image]

@[simp] lemma Inf_to_subfield (S : set (intermediate_field F E)) :
  (Inf S).to_subfield = Inf (to_subfield '' S) :=
set_like.coe_injective $ by simp [set.sUnion_image]

@[simp, norm_cast]
lemma coe_infi {ι : Sort*} (S : ι → intermediate_field F E) : (↑(infi S) : set E) = ⋂ i, (S i) :=
by simp [infi]

@[simp] lemma infi_to_subalgebra {ι : Sort*} (S : ι → intermediate_field F E) :
  (infi S).to_subalgebra = ⨅ i, (S i).to_subalgebra :=
set_like.coe_injective $ by simp [infi]

@[simp] lemma infi_to_subfield {ι : Sort*} (S : ι → intermediate_field F E) :
  (infi S).to_subfield = ⨅ i, (S i).to_subfield :=
set_like.coe_injective $ by simp [infi]

/--  Construct an algebra isomorphism from an equality of intermediate fields -/
@[simps apply]
def equiv_of_eq {S T : intermediate_field F E} (h : S = T) : S ≃ₐ[F] T :=
by refine { to_fun := λ x, ⟨x, _⟩, inv_fun := λ x, ⟨x, _⟩, .. }; tidy

@[simp] lemma equiv_of_eq_symm {S T : intermediate_field F E} (h : S = T) :
  (equiv_of_eq h).symm = equiv_of_eq h.symm :=
rfl

@[simp] lemma equiv_of_eq_rfl (S : intermediate_field F E) :
  equiv_of_eq (rfl : S = S) = alg_equiv.refl :=
by { ext, refl }

@[simp] lemma equiv_of_eq_trans {S T U : intermediate_field F E} (hST : S = T) (hTU : T = U) :
  (equiv_of_eq hST).trans (equiv_of_eq hTU) = equiv_of_eq (trans hST hTU) :=
rfl

variables (F E)
/-- The bottom intermediate_field is isomorphic to the field. -/
noncomputable def bot_equiv : (⊥ : intermediate_field F E) ≃ₐ[F] F :=
(subalgebra.equiv_of_eq _ _ bot_to_subalgebra).trans (algebra.bot_equiv F E)
variables {F E}

@[simp] lemma bot_equiv_def (x : F) :
  bot_equiv F E (algebra_map F (⊥ : intermediate_field F E) x) = x :=
alg_equiv.commutes (bot_equiv F E) x

@[simp] lemma bot_equiv_symm (x : F) :
  (bot_equiv F E).symm x = algebra_map F _ x :=
rfl

noncomputable instance algebra_over_bot : algebra (⊥ : intermediate_field F E) F :=
(intermediate_field.bot_equiv F E).to_alg_hom.to_ring_hom.to_algebra

lemma coe_algebra_map_over_bot :
  (algebra_map (⊥ : intermediate_field F E) F : (⊥ : intermediate_field F E) → F) =
    (intermediate_field.bot_equiv F E) :=
rfl

instance is_scalar_tower_over_bot : is_scalar_tower (⊥ : intermediate_field F E) F E :=
is_scalar_tower.of_algebra_map_eq
begin
  intro x,
  obtain ⟨y, rfl⟩ := (bot_equiv F E).symm.surjective x,
  rw [coe_algebra_map_over_bot, (bot_equiv F E).apply_symm_apply, bot_equiv_symm,
      is_scalar_tower.algebra_map_apply F (⊥ : intermediate_field F E) E]
end

/-- The top intermediate_field is isomorphic to the field.

This is the intermediate field version of `subalgebra.top_equiv`. -/
@[simps apply] def top_equiv : (⊤ : intermediate_field F E) ≃ₐ[F] E :=
(subalgebra.equiv_of_eq _ _ top_to_subalgebra).trans subalgebra.top_equiv

@[simp] lemma top_equiv_symm_apply_coe (a : E) :
  ↑((top_equiv.symm) a : (⊤ : intermediate_field F E)) = a := rfl

@[simp] lemma restrict_scalars_bot_eq_self (K : intermediate_field F E) :
  (⊥ : intermediate_field K E).restrict_scalars _ = K :=
by { ext, rw [mem_restrict_scalars, mem_bot], exact set.ext_iff.mp subtype.range_coe x }

@[simp] lemma restrict_scalars_top {K : Type*} [field K] [algebra K E] [algebra K F]
  [is_scalar_tower K F E] :
  (⊤ : intermediate_field F E).restrict_scalars K = ⊤ :=
rfl

lemma _root_.alg_hom.field_range_eq_map {K : Type*} [field K] [algebra F K] (f : E →ₐ[F] K) :
  f.field_range = intermediate_field.map f ⊤ :=
set_like.ext' set.image_univ.symm

lemma _root_.alg_hom.map_field_range {K L : Type*} [field K] [field L] [algebra F K] [algebra F L]
  (f : E →ₐ[F] K) (g : K →ₐ[F] L) : f.field_range.map g = (g.comp f).field_range :=
set_like.ext' (set.range_comp g f).symm

end lattice

section adjoin_def
variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E] (S : set E)

lemma adjoin_eq_range_algebra_map_adjoin :
  (adjoin F S : set E) = set.range (algebra_map (adjoin F S) E) := (subtype.range_coe).symm

lemma adjoin.algebra_map_mem (x : F) : algebra_map F E x ∈ adjoin F S :=
intermediate_field.algebra_map_mem (adjoin F S) x

lemma adjoin.range_algebra_map_subset : set.range (algebra_map F E) ⊆ adjoin F S :=
begin
  intros x hx,
  cases hx with f hf,
  rw ← hf,
  exact adjoin.algebra_map_mem F S f,
end

instance adjoin.field_coe : has_coe_t F (adjoin F S) :=
{coe := λ x, ⟨algebra_map F E x, adjoin.algebra_map_mem F S x⟩}

lemma subset_adjoin : S ⊆ adjoin F S :=
λ x hx, subfield.subset_closure (or.inr hx)

instance adjoin.set_coe : has_coe_t S (adjoin F S) :=
{coe := λ x, ⟨x,subset_adjoin F S (subtype.mem x)⟩}

@[mono] lemma adjoin.mono (T : set E) (h : S ⊆ T) : adjoin F S ≤ adjoin F T :=
galois_connection.monotone_l gc h

lemma adjoin_contains_field_as_subfield (F : subfield E) : (F : set E) ⊆ adjoin F S :=
λ x hx, adjoin.algebra_map_mem F S ⟨x, hx⟩

lemma subset_adjoin_of_subset_left {F : subfield E} {T : set E} (HT : T ⊆ F) : T ⊆ adjoin F S :=
λ x hx, (adjoin F S).algebra_map_mem ⟨x, HT hx⟩

lemma subset_adjoin_of_subset_right {T : set E} (H : T ⊆ S) : T ⊆ adjoin F S :=
λ x hx, subset_adjoin F S (H hx)

@[simp] lemma adjoin_empty (F E : Type*) [field F] [field E] [algebra F E] :
  adjoin F (∅ : set E) = ⊥ :=
eq_bot_iff.mpr (adjoin_le_iff.mpr (set.empty_subset _))

@[simp] lemma adjoin_univ (F E : Type*) [field F] [field E] [algebra F E] :
  adjoin F (set.univ : set E) = ⊤ :=
eq_top_iff.mpr $ subset_adjoin _ _

/-- If `K` is a field with `F ⊆ K` and `S ⊆ K` then `adjoin F S ≤ K`. -/
lemma adjoin_le_subfield {K : subfield E} (HF : set.range (algebra_map F E) ⊆ K)
  (HS : S ⊆ K) : (adjoin F S).to_subfield ≤ K :=
begin
  apply subfield.closure_le.mpr,
  rw set.union_subset_iff,
  exact ⟨HF, HS⟩,
end

lemma adjoin_subset_adjoin_iff {F' : Type*} [field F'] [algebra F' E]
  {S S' : set E} : (adjoin F S : set E) ⊆ adjoin F' S' ↔
  set.range (algebra_map F E) ⊆ adjoin F' S' ∧ S ⊆ adjoin F' S' :=
⟨λ h, ⟨trans (adjoin.range_algebra_map_subset _ _) h, trans (subset_adjoin _ _) h⟩,
  λ ⟨hF, hS⟩, subfield.closure_le.mpr (set.union_subset hF hS)⟩

/-- `F[S][T] = F[S ∪ T]` -/
lemma adjoin_adjoin_left (T : set E) :
  (adjoin (adjoin F S) T).restrict_scalars _ = adjoin F (S ∪ T) :=
begin
  rw set_like.ext'_iff,
  change ↑(adjoin (adjoin F S) T) = _,
  apply set.eq_of_subset_of_subset; rw adjoin_subset_adjoin_iff; split,
  { rintros _ ⟨⟨x, hx⟩, rfl⟩, exact adjoin.mono _ _ _ (set.subset_union_left _ _) hx },
  { exact subset_adjoin_of_subset_right _ _ (set.subset_union_right _ _) },
  { exact subset_adjoin_of_subset_left _ (adjoin.range_algebra_map_subset _ _) },
  { exact set.union_subset
            (subset_adjoin_of_subset_left _ (subset_adjoin _ _))
            (subset_adjoin _ _) },
end

@[simp] lemma adjoin_insert_adjoin (x : E) :
  adjoin F (insert x (adjoin F S : set E)) = adjoin F (insert x S) :=
le_antisymm
  (adjoin_le_iff.mpr (set.insert_subset.mpr ⟨subset_adjoin _ _ (set.mem_insert _ _),
   adjoin_le_iff.mpr (subset_adjoin_of_subset_right _ _ (set.subset_insert _ _))⟩))
  (adjoin.mono _ _ _ (set.insert_subset_insert (subset_adjoin _ _)))

/-- `F[S][T] = F[T][S]` -/
lemma adjoin_adjoin_comm (T : set E) :
  (adjoin (adjoin F S) T).restrict_scalars F = (adjoin (adjoin F T) S).restrict_scalars F :=
by rw [adjoin_adjoin_left, adjoin_adjoin_left, set.union_comm]

lemma adjoin_map {E' : Type*} [field E'] [algebra F E'] (f : E →ₐ[F] E') :
  (adjoin F S).map f = adjoin F (f '' S) :=
begin
  ext x,
  show x ∈ (subfield.closure (set.range (algebra_map F E) ∪ S)).map (f : E →+* E') ↔
       x ∈ subfield.closure (set.range (algebra_map F E') ∪ f '' S),
  rw [ring_hom.map_field_closure, set.image_union, ← set.range_comp, ← ring_hom.coe_comp,
      f.comp_algebra_map],
  refl,
end

lemma algebra_adjoin_le_adjoin : algebra.adjoin F S ≤ (adjoin F S).to_subalgebra :=
algebra.adjoin_le (subset_adjoin _ _)

lemma adjoin_eq_algebra_adjoin (inv_mem : ∀ x ∈ algebra.adjoin F S, x⁻¹ ∈ algebra.adjoin F S) :
  (adjoin F S).to_subalgebra = algebra.adjoin F S :=
le_antisymm
  (show adjoin F S ≤
      { neg_mem' := λ x, (algebra.adjoin F S).neg_mem, inv_mem' := inv_mem, .. algebra.adjoin F S},
    from adjoin_le_iff.mpr (algebra.subset_adjoin))
  (algebra_adjoin_le_adjoin _ _)

lemma eq_adjoin_of_eq_algebra_adjoin (K : intermediate_field F E)
  (h : K.to_subalgebra = algebra.adjoin F S) : K = adjoin F S :=
begin
  apply to_subalgebra_injective,
  rw h,
  refine (adjoin_eq_algebra_adjoin _ _ _).symm,
  intros x,
  convert K.inv_mem,
  rw ← h,
  refl
end

@[elab_as_eliminator]
lemma adjoin_induction {s : set E} {p : E → Prop} {x} (h : x ∈ adjoin F s)
  (Hs : ∀ x ∈ s, p x) (Hmap : ∀ x, p (algebra_map F E x))
  (Hadd : ∀ x y, p x → p y → p (x + y))
  (Hneg : ∀ x, p x → p (-x))
  (Hinv : ∀ x, p x → p x⁻¹)
  (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
subfield.closure_induction h (λ x hx, or.cases_on hx (λ ⟨x, hx⟩, hx ▸ Hmap x) (Hs x))
  ((algebra_map F E).map_one ▸ Hmap 1)
  Hadd Hneg Hinv Hmul

/--
Variation on `set.insert` to enable good notation for adjoining elements to fields.
Used to preferentially use `singleton` rather than `insert` when adjoining one element.
-/
--this definition of notation is courtesy of Kyle Miller on zulip
class insert {α : Type*} (s : set α) :=
(insert : α → set α)

@[priority 1000]
instance insert_empty {α : Type*} : insert (∅ : set α) :=
{ insert := λ x, @singleton _ _ set.has_singleton x }

@[priority 900]
instance insert_nonempty {α : Type*} (s : set α) : insert s :=
{ insert := λ x, has_insert.insert x s }

notation K`⟮`:std.prec.max_plus l:(foldr `, ` (h t, insert.insert t h) ∅) `⟯` := adjoin K l

section adjoin_simple
variables (α : E)

lemma mem_adjoin_simple_self : α ∈ F⟮α⟯ :=
subset_adjoin F {α} (set.mem_singleton α)

/-- generator of `F⟮α⟯` -/
def adjoin_simple.gen : F⟮α⟯ := ⟨α, mem_adjoin_simple_self F α⟩

@[simp] lemma adjoin_simple.algebra_map_gen : algebra_map F⟮α⟯ E (adjoin_simple.gen F α) = α := rfl

@[simp] lemma adjoin_simple.is_integral_gen :
  is_integral F (adjoin_simple.gen F α) ↔ is_integral F α :=
by { conv_rhs { rw ← adjoin_simple.algebra_map_gen F α },
     rw is_integral_algebra_map_iff (algebra_map F⟮α⟯ E).injective,
     apply_instance }

lemma adjoin_simple_adjoin_simple (β : E) : F⟮α⟯⟮β⟯.restrict_scalars F = F⟮α, β⟯ :=
adjoin_adjoin_left _ _ _

lemma adjoin_simple_comm (β : E) : F⟮α⟯⟮β⟯.restrict_scalars F = F⟮β⟯⟮α⟯.restrict_scalars F :=
adjoin_adjoin_comm _ _ _

variables {F} {α}

lemma adjoin_algebraic_to_subalgebra
  {S : set E} (hS : ∀ x ∈ S, is_algebraic F x) :
  (intermediate_field.adjoin F S).to_subalgebra = algebra.adjoin F S :=
begin
  simp only [is_algebraic_iff_is_integral] at hS,
  have : algebra.is_integral F (algebra.adjoin F S) :=
  by rwa [←le_integral_closure_iff_is_integral, algebra.adjoin_le_iff],
  have := is_field_of_is_integral_of_is_field' this (field.to_is_field F),
  rw ← ((algebra.adjoin F S).to_intermediate_field' this).eq_adjoin_of_eq_algebra_adjoin F S; refl,
end

lemma adjoin_simple_to_subalgebra_of_integral (hα : is_integral F α) :
  (F⟮α⟯).to_subalgebra = algebra.adjoin F {α} :=
begin
  apply adjoin_algebraic_to_subalgebra,
  rintro x (rfl : x = α),
  rwa is_algebraic_iff_is_integral,
end

lemma is_splitting_field_iff {p : F[X]} {K : intermediate_field F E} :
  p.is_splitting_field F K ↔ p.splits (algebra_map F K) ∧ K = adjoin F (p.root_set E) :=
begin
  suffices : _ → ((algebra.adjoin F (p.root_set K) = ⊤ ↔ K = adjoin F (p.root_set E))),
  { exact ⟨λ h, ⟨h.1, (this h.1).mp h.2⟩, λ h, ⟨h.1, (this h.1).mpr h.2⟩⟩ },
  simp_rw [set_like.ext_iff, ←mem_to_subalgebra, ←set_like.ext_iff],
  rw [←K.range_val, adjoin_algebraic_to_subalgebra (λ x, is_algebraic_of_mem_root_set)],
  exact λ hp, (adjoin_root_set_eq_range hp K.val).symm.trans eq_comm,
end

lemma adjoin_root_set_is_splitting_field {p : F[X]} (hp : p.splits (algebra_map F E)) :
  p.is_splitting_field F (adjoin F (p.root_set E)) :=
is_splitting_field_iff.mpr ⟨splits_of_splits hp (λ x hx, subset_adjoin F (p.root_set E) hx), rfl⟩

open_locale big_operators

/-- A compositum of splitting fields is a splitting field -/
lemma is_splitting_field_supr {ι : Type*} {t : ι → intermediate_field F E} {p : ι → F[X]}
  {s : finset ι} (h0 : ∏ i in s, p i ≠ 0) (h : ∀ i ∈ s, (p i).is_splitting_field F (t i)) :
  (∏ i in s, p i).is_splitting_field F (⨆ i ∈ s, t i : intermediate_field F E) :=
begin
  let K : intermediate_field F E := ⨆ i ∈ s, t i,
  have hK : ∀ i ∈ s, t i ≤ K := λ i hi, le_supr_of_le i (le_supr (λ _, t i) hi),
  simp only [is_splitting_field_iff] at h ⊢,
  refine ⟨splits_prod (algebra_map F K) (λ i hi, polynomial.splits_comp_of_splits
    (algebra_map F (t i)) (inclusion (hK i hi)).to_ring_hom (h i hi).1), _⟩,
  simp only [root_set_prod p s h0, ←set.supr_eq_Union, (@gc F _ E _ _).l_supr₂],
  exact supr_congr (λ i, supr_congr (λ hi, (h i hi).2)),
end

open set complete_lattice

@[simp] lemma adjoin_simple_le_iff {K : intermediate_field F E} : F⟮α⟯ ≤ K ↔ α ∈ K :=
adjoin_le_iff.trans singleton_subset_iff

/-- Adjoining a single element is compact in the lattice of intermediate fields. -/
lemma adjoin_simple_is_compact_element (x : E) : is_compact_element F⟮x⟯ :=
begin
  rw is_compact_element_iff_le_of_directed_Sup_le,
  rintros s ⟨F₀, hF₀⟩ hs hx,
  simp only [adjoin_simple_le_iff] at hx ⊢,
  let F : intermediate_field F E :=
  { carrier := ⋃ E ∈ s, ↑E,
    add_mem' := by
    { rintros x₁ x₂ ⟨-, ⟨F₁, rfl⟩, ⟨-, ⟨hF₁, rfl⟩, hx₁⟩⟩ ⟨-, ⟨F₂, rfl⟩, ⟨-, ⟨hF₂, rfl⟩, hx₂⟩⟩,
      obtain ⟨F₃, hF₃, h₁₃, h₂₃⟩ := hs F₁ hF₁ F₂ hF₂,
      exact mem_Union_of_mem F₃ (mem_Union_of_mem hF₃ (F₃.add_mem (h₁₃ hx₁) (h₂₃ hx₂))) },
    neg_mem' := by
    { rintros x ⟨-, ⟨E, rfl⟩, ⟨-, ⟨hE, rfl⟩, hx⟩⟩,
      exact mem_Union_of_mem E (mem_Union_of_mem hE (E.neg_mem hx)) },
    mul_mem' := by
    { rintros x₁ x₂ ⟨-, ⟨F₁, rfl⟩, ⟨-, ⟨hF₁, rfl⟩, hx₁⟩⟩ ⟨-, ⟨F₂, rfl⟩, ⟨-, ⟨hF₂, rfl⟩, hx₂⟩⟩,
      obtain ⟨F₃, hF₃, h₁₃, h₂₃⟩ := hs F₁ hF₁ F₂ hF₂,
      exact mem_Union_of_mem F₃ (mem_Union_of_mem hF₃ (F₃.mul_mem (h₁₃ hx₁) (h₂₃ hx₂))) },
    inv_mem' := by
    { rintros x ⟨-, ⟨E, rfl⟩, ⟨-, ⟨hE, rfl⟩, hx⟩⟩,
      exact mem_Union_of_mem E (mem_Union_of_mem hE (E.inv_mem hx)) },
    algebra_map_mem' := λ x, mem_Union_of_mem F₀ (mem_Union_of_mem hF₀ (F₀.algebra_map_mem x)) },
  have key : Sup s ≤ F := Sup_le (λ E hE, subset_Union_of_subset E (subset_Union _ hE)),
  obtain ⟨-, ⟨E, rfl⟩, -, ⟨hE, rfl⟩, hx⟩ := key hx,
  exact ⟨E, hE, hx⟩,
end

/-- Adjoining a finite subset is compact in the lattice of intermediate fields. -/
lemma adjoin_finset_is_compact_element (S : finset E) :
  is_compact_element (adjoin F S : intermediate_field F E) :=
begin
  have key : adjoin F ↑S = ⨆ x ∈ S, F⟮x⟯ :=
  le_antisymm (adjoin_le_iff.mpr (λ x hx, set_like.mem_coe.mpr (adjoin_simple_le_iff.mp
      (le_supr_of_le x (le_supr_of_le hx le_rfl)))))
      (supr_le (λ x, supr_le (λ hx, adjoin_simple_le_iff.mpr (subset_adjoin F S hx)))),
  rw [key, ←finset.sup_eq_supr],
  exact finset_sup_compact_of_compact S (λ x hx, adjoin_simple_is_compact_element x),
end

/-- Adjoining a finite subset is compact in the lattice of intermediate fields. -/
lemma adjoin_finite_is_compact_element {S : set E} (h : S.finite) :
  is_compact_element (adjoin F S) :=
finite.coe_to_finset h ▸ (adjoin_finset_is_compact_element h.to_finset)

/-- The lattice of intermediate fields is compactly generated. -/
instance : is_compactly_generated (intermediate_field F E) :=
⟨λ s, ⟨(λ x, F⟮x⟯) '' s, ⟨by rintros t ⟨x, hx, rfl⟩; exact adjoin_simple_is_compact_element x,
  Sup_image.trans (le_antisymm (supr_le (λ i, supr_le (λ hi, adjoin_simple_le_iff.mpr hi)))
    (λ x hx, adjoin_simple_le_iff.mp (le_supr_of_le x (le_supr_of_le hx le_rfl))))⟩⟩⟩

lemma exists_finset_of_mem_supr {ι : Type*} {f : ι → intermediate_field F E}
  {x : E} (hx : x ∈ ⨆ i, f i) : ∃ s : finset ι, x ∈ ⨆ i ∈ s, f i :=
begin
  have := (adjoin_simple_is_compact_element x).exists_finset_of_le_supr (intermediate_field F E) f,
  simp only [adjoin_simple_le_iff] at this,
  exact this hx,
end

lemma exists_finset_of_mem_supr' {ι : Type*} {f : ι → intermediate_field F E}
  {x : E} (hx : x ∈ ⨆ i, f i) : ∃ s : finset (Σ i, f i), x ∈ ⨆ i ∈ s, F⟮(i.2 : E)⟯ :=
exists_finset_of_mem_supr (set_like.le_def.mp (supr_le
  (λ i x h, set_like.le_def.mp (le_supr_of_le ⟨i, x, h⟩ le_rfl) (mem_adjoin_simple_self F x))) hx)

lemma exists_finset_of_mem_supr'' {ι : Type*} {f : ι → intermediate_field F E}
  (h : ∀ i, algebra.is_algebraic F (f i)) {x : E} (hx : x ∈ ⨆ i, f i) :
  ∃ s : finset (Σ i, f i), x ∈ ⨆ i ∈ s, adjoin F ((minpoly F (i.2 : _)).root_set E) :=
begin
  refine exists_finset_of_mem_supr (set_like.le_def.mp (supr_le (λ i x hx, set_like.le_def.mp
    (le_supr_of_le ⟨i, x, hx⟩ le_rfl) (subset_adjoin F _ _))) hx),
  rw [intermediate_field.minpoly_eq, subtype.coe_mk, mem_root_set_of_ne, minpoly.aeval],
  exact minpoly.ne_zero (is_integral_iff.mp (is_algebraic_iff_is_integral.mp (h i ⟨x, hx⟩)))
end

end adjoin_simple
end adjoin_def

section adjoin_intermediate_field_lattice
variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E] {α : E} {S : set E}

@[simp] lemma adjoin_eq_bot_iff : adjoin F S = ⊥ ↔ S ⊆ (⊥ : intermediate_field F E) :=
by { rw [eq_bot_iff, adjoin_le_iff], refl, }

@[simp] lemma adjoin_simple_eq_bot_iff : F⟮α⟯ = ⊥ ↔ α ∈ (⊥ : intermediate_field F E) :=
by { rw adjoin_eq_bot_iff, exact set.singleton_subset_iff }

@[simp] lemma adjoin_zero : F⟮(0 : E)⟯ = ⊥ :=
adjoin_simple_eq_bot_iff.mpr (zero_mem ⊥)

@[simp] lemma adjoin_one : F⟮(1 : E)⟯ = ⊥ :=
adjoin_simple_eq_bot_iff.mpr (one_mem ⊥)

@[simp] lemma adjoin_int (n : ℤ) : F⟮(n : E)⟯ = ⊥ :=
adjoin_simple_eq_bot_iff.mpr (coe_int_mem ⊥ n)

@[simp] lemma adjoin_nat (n : ℕ) : F⟮(n : E)⟯ = ⊥ :=
adjoin_simple_eq_bot_iff.mpr (coe_nat_mem ⊥ n)

section adjoin_rank
open finite_dimensional module

variables {K L : intermediate_field F E}

@[simp] lemma rank_eq_one_iff : module.rank F K = 1 ↔ K = ⊥ :=
by rw [← to_subalgebra_eq_iff, ← rank_eq_rank_subalgebra,
  subalgebra.rank_eq_one_iff, bot_to_subalgebra]

@[simp] lemma finrank_eq_one_iff : finrank F K = 1 ↔ K = ⊥ :=
by rw [← to_subalgebra_eq_iff, ← finrank_eq_finrank_subalgebra,
  subalgebra.finrank_eq_one_iff, bot_to_subalgebra]

@[simp] lemma rank_bot : module.rank F (⊥ : intermediate_field F E) = 1 :=
by rw rank_eq_one_iff

@[simp] lemma finrank_bot : finrank F (⊥ : intermediate_field F E) = 1 :=
by rw finrank_eq_one_iff

lemma rank_adjoin_eq_one_iff : module.rank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : intermediate_field F E) :=
iff.trans rank_eq_one_iff adjoin_eq_bot_iff

lemma rank_adjoin_simple_eq_one_iff : module.rank F F⟮α⟯ = 1 ↔ α ∈ (⊥ : intermediate_field F E) :=
by { rw rank_adjoin_eq_one_iff, exact set.singleton_subset_iff }

lemma finrank_adjoin_eq_one_iff : finrank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : intermediate_field F E) :=
iff.trans finrank_eq_one_iff adjoin_eq_bot_iff

lemma finrank_adjoin_simple_eq_one_iff : finrank F F⟮α⟯ = 1 ↔ α ∈ (⊥ : intermediate_field F E) :=
by { rw [finrank_adjoin_eq_one_iff], exact set.singleton_subset_iff }

/-- If `F⟮x⟯` has dimension `1` over `F` for every `x ∈ E` then `F = E`. -/
lemma bot_eq_top_of_rank_adjoin_eq_one (h : ∀ x : E, module.rank F F⟮x⟯ = 1) :
  (⊥ : intermediate_field F E) = ⊤ :=
begin
  ext,
  rw iff_true_right intermediate_field.mem_top,
  exact rank_adjoin_simple_eq_one_iff.mp (h x),
end

lemma bot_eq_top_of_finrank_adjoin_eq_one (h : ∀ x : E, finrank F F⟮x⟯ = 1) :
  (⊥ : intermediate_field F E) = ⊤ :=
begin
  ext,
  rw iff_true_right intermediate_field.mem_top,
  exact finrank_adjoin_simple_eq_one_iff.mp (h x),
end

lemma subsingleton_of_rank_adjoin_eq_one (h : ∀ x : E, module.rank F F⟮x⟯ = 1) :
  subsingleton (intermediate_field F E) :=
subsingleton_of_bot_eq_top (bot_eq_top_of_rank_adjoin_eq_one h)

lemma subsingleton_of_finrank_adjoin_eq_one (h : ∀ x : E, finrank F F⟮x⟯ = 1) :
  subsingleton (intermediate_field F E) :=
subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_eq_one h)

/-- If `F⟮x⟯` has dimension `≤1` over `F` for every `x ∈ E` then `F = E`. -/
lemma bot_eq_top_of_finrank_adjoin_le_one [finite_dimensional F E]
  (h : ∀ x : E, finrank F F⟮x⟯ ≤ 1) : (⊥ : intermediate_field F E) = ⊤ :=
begin
  apply bot_eq_top_of_finrank_adjoin_eq_one,
  exact λ x, by linarith [h x, show 0 < finrank F F⟮x⟯, from finrank_pos],
end

lemma subsingleton_of_finrank_adjoin_le_one [finite_dimensional F E]
  (h : ∀ x : E, finrank F F⟮x⟯ ≤ 1) : subsingleton (intermediate_field F E) :=
subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_le_one h)

end adjoin_rank
end adjoin_intermediate_field_lattice

section adjoin_integral_element

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E] {α : E}
variables {K : Type*} [field K] [algebra F K]

lemma minpoly_gen {α : E} (h : is_integral F α) :
  minpoly F (adjoin_simple.gen F α) = minpoly F α :=
begin
  rw ← adjoin_simple.algebra_map_gen F α at h,
  have inj := (algebra_map F⟮α⟯ E).injective,
  exact minpoly.eq_of_algebra_map_eq inj ((is_integral_algebra_map_iff inj).mp h)
    (adjoin_simple.algebra_map_gen _ _).symm
end

variables (F)
lemma aeval_gen_minpoly (α : E) :
  aeval (adjoin_simple.gen F α) (minpoly F α) = 0 :=
begin
  ext,
  convert minpoly.aeval F α,
  conv in (aeval α) { rw [← adjoin_simple.algebra_map_gen F α] },
  exact (aeval_algebra_map_apply E (adjoin_simple.gen F α) _).symm
end

/-- algebra isomorphism between `adjoin_root` and `F⟮α⟯` -/
noncomputable def adjoin_root_equiv_adjoin (h : is_integral F α) :
  adjoin_root (minpoly F α) ≃ₐ[F] F⟮α⟯ :=
alg_equiv.of_bijective
  (adjoin_root.lift_hom (minpoly F α) (adjoin_simple.gen F α) (aeval_gen_minpoly F α))
  (begin
    set f := adjoin_root.lift _ _ (aeval_gen_minpoly F α : _),
    haveI := fact.mk (minpoly.irreducible h),
    split,
    { exact ring_hom.injective f },
    { suffices : F⟮α⟯.to_subfield ≤ ring_hom.field_range ((F⟮α⟯.to_subfield.subtype).comp f),
      { exact λ x, Exists.cases_on (this (subtype.mem x)) (λ y hy, ⟨y, subtype.ext hy⟩) },
      exact subfield.closure_le.mpr (set.union_subset (λ x hx, Exists.cases_on hx (λ y hy,
        ⟨y, by { rw [ring_hom.comp_apply, adjoin_root.lift_of], exact hy }⟩))
        (set.singleton_subset_iff.mpr ⟨adjoin_root.root (minpoly F α),
        by { rw [ring_hom.comp_apply, adjoin_root.lift_root], refl }⟩)) } end)

lemma adjoin_root_equiv_adjoin_apply_root (h : is_integral F α) :
  adjoin_root_equiv_adjoin F h (adjoin_root.root (minpoly F α)) =
    adjoin_simple.gen F α :=
adjoin_root.lift_root (aeval_gen_minpoly F α)

section power_basis

variables {L : Type*} [field L] [algebra K L]

/-- The elements `1, x, ..., x ^ (d - 1)` form a basis for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def power_basis_aux {x : L} (hx : is_integral K x) :
  basis (fin (minpoly K x).nat_degree) K K⟮x⟯ :=
(adjoin_root.power_basis (minpoly.ne_zero hx)).basis.map
  (adjoin_root_equiv_adjoin K hx).to_linear_equiv

/-- The power basis `1, x, ..., x ^ (d - 1)` for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
@[simps]
noncomputable def adjoin.power_basis {x : L} (hx : is_integral K x) :
  power_basis K K⟮x⟯ :=
{ gen := adjoin_simple.gen K x,
  dim := (minpoly K x).nat_degree,
  basis := power_basis_aux hx,
  basis_eq_pow := λ i,
    by rw [power_basis_aux, basis.map_apply, power_basis.basis_eq_pow,
           alg_equiv.to_linear_equiv_apply, alg_equiv.map_pow, adjoin_root.power_basis_gen,
           adjoin_root_equiv_adjoin_apply_root] }

lemma adjoin.finite_dimensional {x : L} (hx : is_integral K x) : finite_dimensional K K⟮x⟯ :=
power_basis.finite_dimensional (adjoin.power_basis hx)

lemma adjoin.finrank {x : L} (hx : is_integral K x) :
  finite_dimensional.finrank K K⟮x⟯ = (minpoly K x).nat_degree :=
begin
  rw power_basis.finrank (adjoin.power_basis hx : _),
  refl
end

lemma _root_.minpoly.nat_degree_le {x : L} [finite_dimensional K L] (hx : is_integral K x) :
  (minpoly K x).nat_degree ≤ finrank K L :=
le_of_eq_of_le (intermediate_field.adjoin.finrank hx).symm K⟮x⟯.to_submodule.finrank_le

lemma _root_.minpoly.degree_le {x : L} [finite_dimensional K L] (hx : is_integral K x) :
  (minpoly K x).degree ≤ finrank K L :=
degree_le_of_nat_degree_le (minpoly.nat_degree_le hx)

end power_basis

/-- Algebra homomorphism `F⟮α⟯ →ₐ[F] K` are in bijection with the set of roots
of `minpoly α` in `K`. -/
noncomputable def alg_hom_adjoin_integral_equiv (h : is_integral F α) :
  (F⟮α⟯ →ₐ[F] K) ≃ {x // x ∈ ((minpoly F α).map (algebra_map F K)).roots} :=
(adjoin.power_basis h).lift_equiv'.trans ((equiv.refl _).subtype_equiv (λ x,
  by rw [adjoin.power_basis_gen, minpoly_gen h, equiv.refl_apply]))

/-- Fintype of algebra homomorphism `F⟮α⟯ →ₐ[F] K` -/
noncomputable def fintype_of_alg_hom_adjoin_integral (h : is_integral F α) :
  fintype (F⟮α⟯ →ₐ[F] K) :=
power_basis.alg_hom.fintype (adjoin.power_basis h)

lemma card_alg_hom_adjoin_integral (h : is_integral F α) (h_sep : (minpoly F α).separable)
  (h_splits : (minpoly F α).splits (algebra_map F K)) :
  @fintype.card (F⟮α⟯ →ₐ[F] K) (fintype_of_alg_hom_adjoin_integral F h) =
    (minpoly F α).nat_degree :=
begin
  rw alg_hom.card_of_power_basis;
    simp only [adjoin.power_basis_dim, adjoin.power_basis_gen, minpoly_gen h, h_sep, h_splits],
end

end adjoin_integral_element

section induction

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

/-- An intermediate field `S` is finitely generated if there exists `t : finset E` such that
`intermediate_field.adjoin F t = S`. -/
def fg (S : intermediate_field F E) : Prop := ∃ (t : finset E), adjoin F ↑t = S

lemma fg_adjoin_finset (t : finset E) : (adjoin F (↑t : set E)).fg :=
⟨t, rfl⟩

theorem fg_def {S : intermediate_field F E} : S.fg ↔ ∃ t : set E, set.finite t ∧ adjoin F t = S :=
iff.symm set.exists_finite_iff_finset

theorem fg_bot : (⊥ : intermediate_field F E).fg :=
⟨∅, adjoin_empty F E⟩

lemma fg_of_fg_to_subalgebra (S : intermediate_field F E)
  (h : S.to_subalgebra.fg) : S.fg :=
begin
  cases h with t ht,
  exact ⟨t, (eq_adjoin_of_eq_algebra_adjoin _ _ _ ht.symm).symm⟩
end

lemma fg_of_noetherian (S : intermediate_field F E)
  [is_noetherian F E] : S.fg :=
S.fg_of_fg_to_subalgebra S.to_subalgebra.fg_of_noetherian

lemma induction_on_adjoin_finset (S : finset E) (P : intermediate_field F E → Prop) (base : P ⊥)
  (ih : ∀ (K : intermediate_field F E) (x ∈ S), P K → P (K⟮x⟯.restrict_scalars F)) :
  P (adjoin F ↑S) :=
begin
  apply finset.induction_on' S,
  { exact base },
  { intros a s h1 _ _ h4,
    rw [finset.coe_insert, set.insert_eq, set.union_comm, ←adjoin_adjoin_left],
    exact ih (adjoin F s) a h1 h4 }
end

lemma induction_on_adjoin_fg (P : intermediate_field F E → Prop)
  (base : P ⊥) (ih : ∀ (K : intermediate_field F E) (x : E), P K → P (K⟮x⟯.restrict_scalars F))
  (K : intermediate_field F E) (hK : K.fg) : P K :=
begin
  obtain ⟨S, rfl⟩ := hK,
  exact induction_on_adjoin_finset S P base (λ K x _ hK, ih K x hK),
end

lemma induction_on_adjoin [fd : finite_dimensional F E] (P : intermediate_field F E → Prop)
  (base : P ⊥) (ih : ∀ (K : intermediate_field F E) (x : E), P K → P (K⟮x⟯.restrict_scalars F))
  (K : intermediate_field F E) : P K :=
begin
  letI : is_noetherian F E := is_noetherian.iff_fg.2 infer_instance,
  exact induction_on_adjoin_fg P base ih K K.fg_of_noetherian
end

end induction

section alg_hom_mk_adjoin_splits

variables (F E K : Type*) [field F] [field E] [field K] [algebra F E] [algebra F K] {S : set E}

/-- Lifts `L → K` of `F → K` -/
def lifts := Σ (L : intermediate_field F E), (L →ₐ[F] K)

variables {F E K}

instance : partial_order (lifts F E K) :=
{ le := λ x y, x.1 ≤ y.1 ∧ (∀ (s : x.1) (t : y.1), (s : E) = t → x.2 s = y.2 t),
  le_refl := λ x, ⟨le_refl x.1, λ s t hst, congr_arg x.2 (subtype.ext hst)⟩,
  le_trans := λ x y z hxy hyz, ⟨le_trans hxy.1 hyz.1, λ s u hsu, eq.trans
    (hxy.2 s ⟨s, hxy.1 s.mem⟩ rfl) (hyz.2 ⟨s, hxy.1 s.mem⟩ u hsu)⟩,
  le_antisymm :=
  begin
    rintros ⟨x1, x2⟩ ⟨y1, y2⟩ ⟨hxy1, hxy2⟩ ⟨hyx1, hyx2⟩,
    obtain rfl : x1 = y1 := le_antisymm hxy1 hyx1,
    congr,
    exact alg_hom.ext (λ s, hxy2 s s rfl),
  end }

noncomputable instance : order_bot (lifts F E K) :=
{ bot := ⟨⊥, (algebra.of_id F K).comp (bot_equiv F E).to_alg_hom⟩,
  bot_le := λ x, ⟨bot_le, λ s t hst,
  begin
    cases intermediate_field.mem_bot.mp s.mem with u hu,
    rw [show s = (algebra_map F _) u, from subtype.ext hu.symm, alg_hom.commutes],
    rw [show t = (algebra_map F _) u, from subtype.ext (eq.trans hu hst).symm, alg_hom.commutes],
  end⟩ }

noncomputable instance : inhabited (lifts F E K) := ⟨⊥⟩

lemma lifts.eq_of_le {x y : lifts F E K} (hxy : x ≤ y) (s : x.1) :
  x.2 s = y.2 ⟨s, hxy.1 s.mem⟩ := hxy.2 s ⟨s, hxy.1 s.mem⟩ rfl

lemma lifts.exists_max_two {c : set (lifts F E K)} {x y : lifts F E K} (hc : is_chain (≤) c)
  (hx : x ∈ has_insert.insert ⊥ c) (hy : y ∈ has_insert.insert ⊥ c) :
  ∃ z : lifts F E K, z ∈ has_insert.insert ⊥ c ∧ x ≤ z ∧ y ≤ z :=
begin
  cases (hc.insert $ λ _ _ _, or.inl bot_le).total hx hy with hxy hyx,
  { exact ⟨y, hy, hxy, le_refl y⟩ },
  { exact ⟨x, hx, le_refl x, hyx⟩ },
end

lemma lifts.exists_max_three {c : set (lifts F E K)} {x y z : lifts F E K} (hc : is_chain (≤) c)
  (hx : x ∈ has_insert.insert ⊥ c) (hy : y ∈ has_insert.insert ⊥ c)
  (hz : z ∈ has_insert.insert ⊥ c) :
  ∃ w  : lifts F E K, w ∈ has_insert.insert ⊥ c ∧ x ≤ w ∧ y ≤ w ∧ z ≤ w :=
begin
  obtain ⟨v, hv, hxv, hyv⟩ := lifts.exists_max_two hc hx hy,
  obtain ⟨w, hw, hzw, hvw⟩ := lifts.exists_max_two hc hz hv,
  exact ⟨w, hw, le_trans hxv hvw, le_trans hyv hvw, hzw⟩,
end

/-- An upper bound on a chain of lifts -/
def lifts.upper_bound_intermediate_field {c : set (lifts F E K)} (hc : is_chain (≤) c) :
  intermediate_field F E :=
{ carrier := λ s, ∃ x : (lifts F E K), x ∈ has_insert.insert ⊥ c ∧ (s ∈ x.1 : Prop),
  zero_mem' := ⟨⊥, set.mem_insert ⊥ c, zero_mem ⊥⟩,
  one_mem' := ⟨⊥, set.mem_insert ⊥ c, one_mem ⊥⟩,
  neg_mem' := by { rintros _ ⟨x, y, h⟩, exact ⟨x, ⟨y, x.1.neg_mem h⟩⟩ },
  inv_mem' := by { rintros _ ⟨x, y, h⟩, exact ⟨x, ⟨y, x.1.inv_mem h⟩⟩ },
  add_mem' := by
  { rintros _ _ ⟨x, hx, ha⟩ ⟨y, hy, hb⟩,
    obtain ⟨z, hz, hxz, hyz⟩ := lifts.exists_max_two hc hx hy,
    exact ⟨z, hz, z.1.add_mem (hxz.1 ha) (hyz.1 hb)⟩ },
  mul_mem' := by
  { rintros _ _ ⟨x, hx, ha⟩ ⟨y, hy, hb⟩,
    obtain ⟨z, hz, hxz, hyz⟩ := lifts.exists_max_two hc hx hy,
    exact ⟨z, hz, z.1.mul_mem (hxz.1 ha) (hyz.1 hb)⟩ },
  algebra_map_mem' := λ s, ⟨⊥, set.mem_insert ⊥ c, algebra_map_mem ⊥ s⟩ }

/-- The lift on the upper bound on a chain of lifts -/
noncomputable def lifts.upper_bound_alg_hom {c : set (lifts F E K)} (hc : is_chain (≤) c) :
  lifts.upper_bound_intermediate_field hc →ₐ[F] K :=
{ to_fun := λ s, (classical.some s.mem).2 ⟨s, (classical.some_spec s.mem).2⟩,
  map_zero' := alg_hom.map_zero _,
  map_one' := alg_hom.map_one _,
  map_add' := λ s t, begin
    obtain ⟨w, hw, hxw, hyw, hzw⟩ := lifts.exists_max_three hc
      (classical.some_spec s.mem).1 (classical.some_spec t.mem).1
      (classical.some_spec (s + t).mem).1,
    rw [lifts.eq_of_le hxw, lifts.eq_of_le hyw, lifts.eq_of_le hzw, ←w.2.map_add],
    refl,
  end,
  map_mul' := λ s t, begin
    obtain ⟨w, hw, hxw, hyw, hzw⟩ := lifts.exists_max_three hc
      (classical.some_spec s.mem).1 (classical.some_spec t.mem).1
      (classical.some_spec (s * t).mem).1,
    rw [lifts.eq_of_le hxw, lifts.eq_of_le hyw, lifts.eq_of_le hzw, ←w.2.map_mul],
    refl,
  end,
  commutes' := λ _, alg_hom.commutes _ _ }

/-- An upper bound on a chain of lifts -/
noncomputable def lifts.upper_bound {c : set (lifts F E K)} (hc : is_chain (≤) c) :
  lifts F E K :=
⟨lifts.upper_bound_intermediate_field hc, lifts.upper_bound_alg_hom hc⟩

lemma lifts.exists_upper_bound (c : set (lifts F E K)) (hc : is_chain (≤) c) :
  ∃ ub, ∀ a ∈ c, a ≤ ub :=
⟨lifts.upper_bound hc,
begin
  intros x hx,
  split,
  { exact λ s hs, ⟨x, set.mem_insert_of_mem ⊥ hx, hs⟩ },
  { intros s t hst,
    change x.2 s = (classical.some t.mem).2 ⟨t, (classical.some_spec t.mem).2⟩,
    obtain ⟨z, hz, hxz, hyz⟩ := lifts.exists_max_two hc (set.mem_insert_of_mem ⊥ hx)
      (classical.some_spec t.mem).1,
    rw [lifts.eq_of_le hxz, lifts.eq_of_le hyz],
    exact congr_arg z.2 (subtype.ext hst) },
end⟩

/-- Extend a lift `x : lifts F E K` to an element `s : E` whose conjugates are all in `K` -/
noncomputable def lifts.lift_of_splits (x : lifts F E K) {s : E} (h1 : is_integral F s)
  (h2 : (minpoly F s).splits (algebra_map F K)) : lifts F E K :=
let h3 : is_integral x.1 s := is_integral_of_is_scalar_tower h1 in
let key : (minpoly x.1 s).splits x.2.to_ring_hom :=
  splits_of_splits_of_dvd _ (map_ne_zero (minpoly.ne_zero h1))
  ((splits_map_iff _ _).mpr (by {convert h2, exact ring_hom.ext (λ y, x.2.commutes y)}))
  (minpoly.dvd_map_of_is_scalar_tower _ _ _) in
⟨x.1⟮s⟯.restrict_scalars F, (@alg_hom_equiv_sigma F x.1 (x.1⟮s⟯.restrict_scalars F) K _ _ _ _ _ _ _
  (intermediate_field.algebra x.1⟮s⟯) (is_scalar_tower.of_algebra_map_eq (λ _, rfl))).inv_fun
  ⟨x.2, (@alg_hom_adjoin_integral_equiv x.1 _ E _ _ s K _ x.2.to_ring_hom.to_algebra
  h3).inv_fun ⟨root_of_splits x.2.to_ring_hom key (ne_of_gt (minpoly.degree_pos h3)), by
{ simp_rw [mem_roots (map_ne_zero (minpoly.ne_zero h3)), is_root, ←eval₂_eq_eval_map],
  exact map_root_of_splits x.2.to_ring_hom key (ne_of_gt (minpoly.degree_pos h3)) }⟩⟩⟩

lemma lifts.le_lifts_of_splits (x : lifts F E K) {s : E} (h1 : is_integral F s)
  (h2 : (minpoly F s).splits (algebra_map F K)) : x ≤ x.lift_of_splits h1 h2 :=
⟨λ z hz, algebra_map_mem x.1⟮s⟯ ⟨z, hz⟩, λ t u htu, eq.symm begin
  rw [←(show algebra_map x.1 x.1⟮s⟯ t = u, from subtype.ext htu)],
  letI : algebra x.1 K := x.2.to_ring_hom.to_algebra,
  exact (alg_hom.commutes _ t),
end⟩

lemma lifts.mem_lifts_of_splits (x : lifts F E K) {s : E} (h1 : is_integral F s)
  (h2 : (minpoly F s).splits (algebra_map F K)) : s ∈ (x.lift_of_splits h1 h2).1 :=
mem_adjoin_simple_self x.1 s

lemma lifts.exists_lift_of_splits (x : lifts F E K) {s : E} (h1 : is_integral F s)
  (h2 : (minpoly F s).splits (algebra_map F K)) : ∃ y, x ≤ y ∧ s ∈ y.1 :=
⟨x.lift_of_splits h1 h2, x.le_lifts_of_splits h1 h2, x.mem_lifts_of_splits h1 h2⟩

lemma alg_hom_mk_adjoin_splits
  (hK : ∀ s ∈ S, is_integral F (s : E) ∧ (minpoly F s).splits (algebra_map F K)) :
  nonempty (adjoin F S →ₐ[F] K) :=
begin
  obtain ⟨x : lifts F E K, hx⟩ := zorn_partial_order lifts.exists_upper_bound,
  refine ⟨alg_hom.mk (λ s, x.2 ⟨s, adjoin_le_iff.mpr (λ s hs, _) s.mem⟩) x.2.map_one (λ s t,
    x.2.map_mul ⟨s, _⟩ ⟨t, _⟩) x.2.map_zero (λ s t, x.2.map_add ⟨s, _⟩ ⟨t, _⟩) x.2.commutes⟩,
  rcases (x.exists_lift_of_splits (hK s hs).1 (hK s hs).2) with ⟨y, h1, h2⟩,
  rwa hx y h1 at h2
end

lemma alg_hom_mk_adjoin_splits' (hS : adjoin F S = ⊤)
  (hK : ∀ x ∈ S, is_integral F (x : E) ∧ (minpoly F x).splits (algebra_map F K)) :
  nonempty (E →ₐ[F] K) :=
begin
  cases alg_hom_mk_adjoin_splits hK with ϕ,
  rw hS at ϕ,
  exact ⟨ϕ.comp top_equiv.symm.to_alg_hom⟩,
end

end alg_hom_mk_adjoin_splits

section supremum

variables {K L : Type*} [field K] [field L] [algebra K L] (E1 E2 : intermediate_field K L)

lemma le_sup_to_subalgebra :
  E1.to_subalgebra ⊔ E2.to_subalgebra ≤ (E1 ⊔ E2).to_subalgebra :=
sup_le (show E1 ≤ E1 ⊔ E2, from le_sup_left) (show E2 ≤ E1 ⊔ E2, from le_sup_right)

lemma sup_to_subalgebra [h1 : finite_dimensional K E1] [h2 : finite_dimensional K E2] :
  (E1 ⊔ E2).to_subalgebra = E1.to_subalgebra ⊔ E2.to_subalgebra :=
begin
  let S1 := E1.to_subalgebra,
  let S2 := E2.to_subalgebra,
  refine le_antisymm (show _ ≤ (S1 ⊔ S2).to_intermediate_field _, from (sup_le (show S1 ≤ _,
    from le_sup_left) (show S2 ≤ _, from le_sup_right))) (le_sup_to_subalgebra E1 E2),
  suffices : is_field ↥(S1 ⊔ S2),
  { intros x hx,
    by_cases hx' : (⟨x, hx⟩ : S1 ⊔ S2) = 0,
    { rw [←subtype.coe_mk x hx, hx', subalgebra.coe_zero, inv_zero],
      exact (S1 ⊔ S2).zero_mem },
    { obtain ⟨y, h⟩ := this.mul_inv_cancel hx',
      exact (congr_arg (∈ S1 ⊔ S2) $ eq_inv_of_mul_eq_one_right $ subtype.ext_iff.mp h).mp y.2 } },
  exact is_field_of_is_integral_of_is_field'
    (is_integral_sup.mpr ⟨algebra.is_integral_of_finite K E1, algebra.is_integral_of_finite K E2⟩)
    (field.to_is_field K),
end

instance finite_dimensional_sup [h1 : finite_dimensional K E1] [h2 : finite_dimensional K E2] :
  finite_dimensional K ↥(E1 ⊔ E2) :=
begin
  let g := algebra.tensor_product.product_map E1.val E2.val,
  suffices : g.range = (E1 ⊔ E2).to_subalgebra,
  { have h : finite_dimensional K g.range.to_submodule := g.to_linear_map.finite_dimensional_range,
    rwa this at h },
  rw [algebra.tensor_product.product_map_range, E1.range_val, E2.range_val, sup_to_subalgebra],
end

instance finite_dimensional_supr_of_finite
  {ι : Type*} {t : ι → intermediate_field K L} [h : finite ι] [Π i, finite_dimensional K (t i)] :
  finite_dimensional K (⨆ i, t i : intermediate_field K L) :=
begin
  rw ← supr_univ,
  let P : set ι → Prop := λ s, finite_dimensional K (⨆ i ∈ s, t i : intermediate_field K L),
  change P set.univ,
  apply set.finite.induction_on,
  { exact set.finite_univ },
  all_goals { dsimp only [P] },
  { rw supr_emptyset,
    exact (bot_equiv K L).symm.to_linear_equiv.finite_dimensional },
  { intros _ s _ _ hs,
    rw supr_insert,
    exactI intermediate_field.finite_dimensional_sup _ _ },
end

instance finite_dimensional_supr_of_finset {ι : Type*}
  {f : ι → intermediate_field K L} {s : finset ι} [h : Π i ∈ s, finite_dimensional K (f i)] :
  finite_dimensional K (⨆ i ∈ s, f i : intermediate_field K L) :=
begin
  haveI : Π i : {i // i ∈ s}, finite_dimensional K (f i) := λ i, h i i.2,
  have : (⨆ i ∈ s, f i) = ⨆ i : {i // i ∈ s}, f i :=
  le_antisymm (supr_le (λ i, supr_le (λ h, le_supr (λ i : {i // i ∈ s}, f i) ⟨i, h⟩)))
    (supr_le (λ i, le_supr_of_le i (le_supr_of_le i.2 le_rfl))),
  exact this.symm ▸ intermediate_field.finite_dimensional_supr_of_finite,
end

/-- A compositum of algebraic extensions is algebraic -/
lemma is_algebraic_supr {ι : Type*} {f : ι → intermediate_field K L}
  (h : ∀ i, algebra.is_algebraic K (f i)) :
  algebra.is_algebraic K (⨆ i, f i : intermediate_field K L) :=
begin
  rintros ⟨x, hx⟩,
  obtain ⟨s, hx⟩ := exists_finset_of_mem_supr' hx,
  rw [is_algebraic_iff, subtype.coe_mk, ←subtype.coe_mk x hx, ←is_algebraic_iff],
  haveI : ∀ i : (Σ i, f i), finite_dimensional K K⟮(i.2 : L)⟯ :=
  λ ⟨i, x⟩, adjoin.finite_dimensional (is_integral_iff.1 (is_algebraic_iff_is_integral.1 (h i x))),
  apply algebra.is_algebraic_of_finite,
end

end supremum

end intermediate_field

section power_basis

variables {K L : Type*} [field K] [field L] [algebra K L]

namespace power_basis

open intermediate_field

/-- `pb.equiv_adjoin_simple` is the equivalence between `K⟮pb.gen⟯` and `L` itself. -/
noncomputable def equiv_adjoin_simple (pb : power_basis K L) :
  K⟮pb.gen⟯ ≃ₐ[K] L :=
(adjoin.power_basis pb.is_integral_gen).equiv_of_minpoly pb
  (minpoly.eq_of_algebra_map_eq (algebra_map K⟮pb.gen⟯ L).injective
    (adjoin.power_basis pb.is_integral_gen).is_integral_gen
    (by rw [adjoin.power_basis_gen, adjoin_simple.algebra_map_gen]))

@[simp]
lemma equiv_adjoin_simple_aeval (pb : power_basis K L) (f : K[X]) :
  pb.equiv_adjoin_simple (aeval (adjoin_simple.gen K pb.gen) f) = aeval pb.gen f :=
equiv_of_minpoly_aeval _ pb _ f

@[simp]
lemma equiv_adjoin_simple_gen (pb : power_basis K L) :
  pb.equiv_adjoin_simple (adjoin_simple.gen K pb.gen) = pb.gen :=
equiv_of_minpoly_gen _ pb _

@[simp]
lemma equiv_adjoin_simple_symm_aeval (pb : power_basis K L) (f : K[X]) :
  pb.equiv_adjoin_simple.symm (aeval pb.gen f) = aeval (adjoin_simple.gen K pb.gen) f :=
by rw [equiv_adjoin_simple, equiv_of_minpoly_symm, equiv_of_minpoly_aeval, adjoin.power_basis_gen]

@[simp]
lemma equiv_adjoin_simple_symm_gen (pb : power_basis K L) :
  pb.equiv_adjoin_simple.symm pb.gen = (adjoin_simple.gen K pb.gen) :=
by rw [equiv_adjoin_simple, equiv_of_minpoly_symm, equiv_of_minpoly_gen, adjoin.power_basis_gen]

end power_basis

end power_basis
