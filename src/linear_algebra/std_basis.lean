/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import linear_algebra.basic
import linear_algebra.basis
import linear_algebra.pi

/-!
# The standard basis

This file defines the standard basis `std_basis R φ i b j`, which is `b` where `i = j` and `0`
elsewhere.

To give a concrete example, `std_basis R (λ (i : fin 3), R) i 1` gives the `i`th unit basis vector
in `R³`, and `pi.is_basis_fun` proves this is a basis over `fin 3 → R`.

## Main definitions

 - `linear_map.std_basis R ϕ i b`: the `i`'th standard `R`-basis vector on `Π i, ϕ i`,
   scaled by `b`.

## Main results

 - `pi.is_basis_std_basis`: `std_basis` turns a component-wise basis into a basis on the product
   type.
 - `pi.is_basis_fun`: `std_basis R (λ _, R) i 1` is a basis for `n → R`.

-/

open function submodule
open_locale big_operators
open_locale big_operators

namespace linear_map

variables (R : Type*) {ι : Type*} [semiring R] (φ : ι → Type*)
  [Π i, add_comm_monoid (φ i)] [Π i, module R (φ i)] [decidable_eq ι]

/-- The standard basis of the product of `φ`. -/
def std_basis : Π (i : ι), φ i →ₗ[R] (Πi, φ i) := single

lemma std_basis_apply (i : ι) (b : φ i) : std_basis R φ i b = update 0 i b :=
rfl

lemma coe_std_basis (i : ι) : ⇑(std_basis R φ i) = pi.single i :=
funext $ std_basis_apply R φ i

@[simp] lemma std_basis_same (i : ι) (b : φ i) : std_basis R φ i b i = b :=
by rw [std_basis_apply, update_same]

lemma std_basis_ne (i j : ι) (h : j ≠ i) (b : φ i) : std_basis R φ i b j = 0 :=
by rw [std_basis_apply, update_noteq h]; refl

lemma std_basis_eq_pi_diag (i : ι) : std_basis R φ i = pi (diag i) :=
begin
  ext x j,
  convert (update_apply 0 x i j _).symm,
  refl,
end

lemma ker_std_basis (i : ι) : ker (std_basis R φ i) = ⊥ :=
ker_eq_bot_of_injective $ assume f g hfg,
  have std_basis R φ i f i = std_basis R φ i g i := hfg ▸ rfl,
  by simpa only [std_basis_same]

lemma proj_comp_std_basis (i j : ι) : (proj i).comp (std_basis R φ j) = diag j i :=
by rw [std_basis_eq_pi_diag, proj_pi]

lemma proj_std_basis_same (i : ι) : (proj i).comp (std_basis R φ i) = id :=
by ext b; simp

lemma proj_std_basis_ne (i j : ι) (h : i ≠ j) : (proj i).comp (std_basis R φ j) = 0 :=
by ext b; simp [std_basis_ne R φ _ _ h]

lemma supr_range_std_basis_le_infi_ker_proj (I J : set ι) (h : disjoint I J) :
  (⨆i∈I, range (std_basis R φ i)) ≤ (⨅i∈J, ker (proj i)) :=
begin
  refine (supr_le $ assume i, supr_le $ assume hi, range_le_iff_comap.2 _),
  simp only [(ker_comp _ _).symm, eq_top_iff, set_like.le_def, mem_ker, comap_infi, mem_infi],
  assume b hb j hj,
  have : i ≠ j := assume eq, h ⟨hi, eq.symm ▸ hj⟩,
  rw [proj_std_basis_ne R φ j i this.symm, zero_apply]
end

lemma infi_ker_proj_le_supr_range_std_basis {I : finset ι} {J : set ι} (hu : set.univ ⊆ ↑I ∪ J) :
  (⨅ i∈J, ker (proj i)) ≤ (⨆i∈I, range (std_basis R φ i)) :=
set_like.le_def.2
begin
  assume b hb,
  simp only [mem_infi, mem_ker, proj_apply] at hb,
  rw ← show ∑ i in I, std_basis R φ i (b i) = b,
  { ext i,
    rw [finset.sum_apply, ← std_basis_same R φ i (b i)],
    refine finset.sum_eq_single i (assume j hjI ne, std_basis_ne _ _ _ _ ne.symm _) _,
    assume hiI,
    rw [std_basis_same],
    exact hb _ ((hu trivial).resolve_left hiI) },
  exact sum_mem _ (assume i hiI, mem_supr_of_mem i $ mem_supr_of_mem hiI $
    (std_basis R φ i).mem_range_self (b i))
end

lemma supr_range_std_basis_eq_infi_ker_proj {I J : set ι}
  (hd : disjoint I J) (hu : set.univ ⊆ I ∪ J) (hI : set.finite I) :
  (⨆i∈I, range (std_basis R φ i)) = (⨅i∈J, ker (proj i)) :=
begin
  refine le_antisymm (supr_range_std_basis_le_infi_ker_proj _ _ _ _ hd) _,
  have : set.univ ⊆ ↑hI.to_finset ∪ J, { rwa [hI.coe_to_finset] },
  refine le_trans (infi_ker_proj_le_supr_range_std_basis R φ this) (supr_le_supr $ assume i, _),
  rw [set.finite.mem_to_finset],
  exact le_refl _
end

lemma supr_range_std_basis [fintype ι] : (⨆i:ι, range (std_basis R φ i)) = ⊤ :=
have (set.univ : set ι) ⊆ ↑(finset.univ : finset ι) ∪ ∅ := by rw [finset.coe_univ, set.union_empty],
begin
  apply top_unique,
  convert (infi_ker_proj_le_supr_range_std_basis R φ this),
  exact infi_emptyset.symm,
  exact (funext $ λi, (@supr_pos _ _ _ (λh, range (std_basis R φ i)) $ finset.mem_univ i).symm)
end

lemma disjoint_std_basis_std_basis (I J : set ι) (h : disjoint I J) :
  disjoint (⨆i∈I, range (std_basis R φ i)) (⨆i∈J, range (std_basis R φ i)) :=
begin
  refine disjoint.mono
    (supr_range_std_basis_le_infi_ker_proj _ _ _ _ $ disjoint_compl_right)
    (supr_range_std_basis_le_infi_ker_proj _ _ _ _ $ disjoint_compl_right) _,
  simp only [disjoint, set_like.le_def, mem_infi, mem_inf, mem_ker, mem_bot, proj_apply,
    funext_iff],
  rintros b ⟨hI, hJ⟩ i,
  classical,
  by_cases hiI : i ∈ I,
  { by_cases hiJ : i ∈ J,
    { exact (h ⟨hiI, hiJ⟩).elim },
    { exact hJ i hiJ } },
  { exact hI i hiI }
end

lemma std_basis_eq_single {a : R} :
  (λ (i : ι), (std_basis R (λ _ : ι, R) i) a) = λ (i : ι), (finsupp.single i a) :=
begin
  ext i j,
  rw [std_basis_apply, finsupp.single_apply],
  split_ifs,
  { rw [h, function.update_same] },
  { rw [function.update_noteq (ne.symm h)], refl },
end

end linear_map

namespace pi
open linear_map
open set

variables {R : Type*}

section module
variables {η : Type*} {ιs : η → Type*} {Ms : η → Type*}
variables [ring R] [∀i, add_comm_group (Ms i)] [∀i, module R (Ms i)]

lemma linear_independent_std_basis [decidable_eq η]
  (v : Πj, ιs j → (Ms j)) (hs : ∀i, linear_independent R (v i)) :
  linear_independent R (λ (ji : Σ j, ιs j), std_basis R Ms ji.1 (v ji.1 ji.2)) :=
begin
  have hs' : ∀j : η, linear_independent R (λ i : ιs j, std_basis R Ms j (v j i)),
  { intro j,
    exact (hs j).map' _ (ker_std_basis _ _ _) },
  apply linear_independent_Union_finite hs',
  { assume j J _ hiJ,
    simp [(set.Union.equations._eqn_1 _).symm, submodule.span_image, submodule.span_Union],
    have h₀ : ∀ j, span R (range (λ (i : ιs j), std_basis R Ms j (v j i)))
        ≤ range (std_basis R Ms j),
    { intro j,
      rw [span_le, linear_map.range_coe],
      apply range_comp_subset_range },
    have h₁ : span R (range (λ (i : ιs j), std_basis R Ms j (v j i)))
        ≤ ⨆ i ∈ {j}, range (std_basis R Ms i),
    { rw @supr_singleton _ _ _ (λ i, linear_map.range (std_basis R (λ (j : η), Ms j) i)),
      apply h₀ },
    have h₂ : (⨆ j ∈ J, span R (range (λ (i : ιs j), std_basis R Ms j (v j i)))) ≤
               ⨆ j ∈ J, range (std_basis R (λ (j : η), Ms j) j) :=
      supr_le_supr (λ i, supr_le_supr (λ H, h₀ i)),
    have h₃ : disjoint (λ (i : η), i ∈ {j}) J,
    { convert set.disjoint_singleton_left.2 hiJ using 0 },
    exact (disjoint_std_basis_std_basis _ _ _ _ h₃).mono h₁ h₂ }
end

@[to_additive add_equiv.Pi_congr_right]
def mul_equiv.Pi_congr_right
  {Ms Ns : η → Type*} [Π j, monoid (Ms j)] [Π j, monoid (Ns j)]
  (es : ∀ j, Ms j ≃* Ns j) : (Π j, Ms j) ≃* (Π j, Ns j) :=
{ map_mul' := λ x y,
    by { ext j, simp_rw [equiv.Pi_congr_right, pi.mul_apply, mul_equiv.coe_to_equiv, mul_equiv.map_mul] },
  .. equiv.Pi_congr_right (λ j, (es j).to_equiv) }

@[simp, to_additive add_equiv.Pi_congr_right_apply]
lemma mul_equiv.Pi_congr_right_apply
  {Ms Ns : η → Type*} [Π j, monoid (Ms j)] [Π j, monoid (Ns j)]
  (es : ∀ j, Ms j ≃* Ns j) (x j) :
  mul_equiv.Pi_congr_right es x j = es j (x j) := rfl

def linear_equiv.Pi_congr_right {Ms Ns : η → Type*}
  [Π j, add_comm_monoid (Ms j)] [Π j, module R (Ms j)]
  [Π j, add_comm_monoid (Ns j)] [Π j, module R (Ns j)]
  (es : ∀ j, Ms j ≃ₗ[R] Ns j) : (Π j, Ms j) ≃ₗ[R] (Π j, Ns j) :=
{ map_smul' := λ m x, by { ext j, simp },
  .. add_equiv.Pi_congr_right (λ j, (es j).to_add_equiv) }

@[simp]
lemma linear_equiv.Pi_congr_right_apply
  {Ms Ns : η → Type*}
  [Π j, add_comm_monoid (Ms j)] [Π j, module R (Ms j)]
  [Π j, add_comm_monoid (Ns j)] [Π j, module R (Ns j)]
  (es : ∀ j, Ms j ≃ₗ[R] Ns j) (x j) :
  linear_equiv.Pi_congr_right es x j = es j (x j) := rfl

variable [fintype η]

noncomputable def finsupp.sigma_finsupp_equiv_pi_finsupp
  {α : Type*} {ιs : η → Type*} [has_zero α] :
  ((Σ j, ιs j) →₀ α) ≃ Π j, (ιs j →₀ α) :=
{ to_fun := λ f j, f.split j,
  inv_fun := λ f, finsupp.on_finset
    (finset.sigma finset.univ (λ j, (f j).support))
    (λ ji, f ji.1 ji.2)
    (λ g hg, finset.mem_sigma.mpr ⟨finset.mem_univ _, finsupp.mem_support_iff.mpr hg⟩),
  left_inv := λ f, by { ext, simp [finsupp.split] },
  right_inv := λ f, by { ext, simp [finsupp.split] } }

@[simp] lemma finsupp.sigma_finsupp_equiv_pi_finsupp_apply
  {α : Type*} {ιs : η → Type*} [has_zero α] (f : (Σ j, ιs j) →₀ α) (j i) :
  finsupp.sigma_finsupp_equiv_pi_finsupp f j i = f ⟨j, i⟩ := rfl

noncomputable def finsupp.sigma_finsupp_add_equiv_pi_finsupp
  {α : Type*} {ιs : η → Type*} [add_monoid α] :
  ((Σ j, ιs j) →₀ α) ≃+ Π j, (ιs j →₀ α) :=
{ map_add' := λ f g, by { ext, simp },
  .. finsupp.sigma_finsupp_equiv_pi_finsupp }

@[simp] lemma finsupp.sigma_finsupp_add_equiv_pi_finsupp_apply
{α : Type*} {ιs : η → Type*} [add_monoid α] (f : (Σ j, ιs j) →₀ α) (j i) :
  finsupp.sigma_finsupp_add_equiv_pi_finsupp f j i = f ⟨j, i⟩ := rfl

section

variables (R)

noncomputable def finsupp.sigma_finsupp_lequiv_pi_finsupp
  {M : Type*} {ιs : η → Type*} [add_comm_monoid M] [module R M] :
  ((Σ j, ιs j) →₀ M) ≃ₗ[R] Π j, (ιs j →₀ M) :=
{ map_smul' := λ c f, by { ext, simp },
  .. finsupp.sigma_finsupp_add_equiv_pi_finsupp }

@[simp] lemma finsupp.sigma_finsupp_lequiv_pi_finsupp_apply
  {M : Type*} {ιs : η → Type*} [add_comm_monoid M] [module R M]
  (f : (Σ j, ιs j) →₀ M) (j i) :
  finsupp.sigma_finsupp_lequiv_pi_finsupp R f j i = f ⟨j, i⟩ := rfl

@[simp] lemma finsupp.sigma_finsupp_lequiv_pi_finsupp_symm_apply
  {M : Type*} {ιs : η → Type*} [add_comm_monoid M] [module R M]
  (f : Π j, (ιs j →₀ M)) (ji) :
  (finsupp.sigma_finsupp_lequiv_pi_finsupp R).symm f ji = f ji.1 ji.2 := rfl

end

section

-- FIXME: we have to do some hacks to make the typeclass inference work
local attribute [-instance] mul_zero_class.to_has_zero
/-- `pi.basis (s : ∀ j, basis (ιs j) R (Ms j))` is the `Σ j, ιs j`-indexed basis on `Π j, Ms j`
given by `s j` on each component. -/
protected noncomputable def basis (s : ∀ j, basis (ιs j) R (Ms j)) :
  basis (Σ j, ιs j) R (Π j, Ms j) :=
let e₁ := ((linear_equiv.Pi_congr_right (λ j, (s j).repr))) in
basis.of_repr (@linear_equiv.trans _ _ (Π i, ιs i →₀ R) _ _ _ _ _ _ _ _ e₁
  (finsupp.sigma_finsupp_lequiv_pi_finsupp R).symm)

@[simp] lemma basis_repr_std_basis [decidable_eq η] (s : ∀ j, basis (ιs j) R (Ms j)) (j i) :
  (pi.basis s).repr (std_basis R _ j (s j i)) = finsupp.single ⟨j, i⟩ 1 :=
begin
  ext ⟨j', i'⟩,
  by_cases hj : j = j',
  { subst hj,
    simp only [pi.basis, linear_equiv.trans_apply, basis.repr_self, std_basis_same,
        linear_equiv.Pi_congr_right_apply, finsupp.sigma_finsupp_lequiv_pi_finsupp_symm_apply],
    symmetry,
    exact basis.finsupp.single_apply_left
      (λ i i' (h : (⟨j, i⟩ : Σ j, ιs j) = ⟨j, i'⟩), eq_of_heq (sigma.mk.inj h).2) _ _ _ },
  simp only [pi.basis, linear_equiv.trans_apply, finsupp.sigma_finsupp_lequiv_pi_finsupp_symm_apply,
      linear_equiv.Pi_congr_right_apply],
  dsimp,
  rw [std_basis_ne _ _ _ _ (ne.symm hj), linear_equiv.map_zero, finsupp.zero_apply,
      finsupp.single_eq_of_ne],
  rintros ⟨⟩,
  contradiction
end

@[simp] lemma basis_apply [decidable_eq η] (s : ∀ j, basis (ιs j) R (Ms j)) (ji) :
  pi.basis s ji = std_basis R _ ji.1 (s ji.1 ji.2) :=
basis.apply_eq_iff.mpr (by simp)

@[simp] lemma basis_repr (s : ∀ j, basis (ιs j) R (Ms j)) (x) (ji) :
  (pi.basis s).repr x ji = (s ji.1).repr (x ji.1) ji.2 :=
rfl

end

section
variables (R η)

noncomputable def basis_fun₀ : basis (Σ (j : η), unit) R (Π (j : η), R) :=
pi.basis (λ j, basis.singleton unit R)

@[simp] lemma basis_fun₀_apply [decidable_eq η] (ji) :
  basis_fun₀ R η ji = std_basis R (λ (i : η), R) ji.fst 1 :=
by rw [basis_fun₀, pi.basis_apply, basis.singleton_apply]

@[simp] lemma basis_fun₀_repr (x i) :
  (basis_fun₀ R η).repr x i = x i.1 :=
by { rcases i with ⟨j, ⟨⟩⟩, simp [basis_fun₀] }

noncomputable def finsupp.add_equiv_fun_on_fintype (α M : Type*) [fintype α] [add_monoid M] :
  (α →₀ M) ≃+ (α → M) :=
{ map_add' := λ x y, by simp [finsupp.equiv_fun_on_fintype],
  .. finsupp.equiv_fun_on_fintype }

noncomputable def finsupp.lequiv_fun_on_fintype (α M : Type*) [fintype α]
  [add_comm_monoid M] [module R M] :
  (α →₀ M) ≃ₗ[R] (α → M) :=
{ map_smul' := λ x y, by simp [finsupp.add_equiv_fun_on_fintype, finsupp.equiv_fun_on_fintype],
  .. finsupp.add_equiv_fun_on_fintype α M }

noncomputable def basis_fun : basis η R (Π (j : η), R) :=
(basis_fun₀ R η).reindex
  { to_fun := sigma.fst,
    inv_fun := λ i, ⟨i, punit.star⟩,
    left_inv := λ ⟨j, i⟩, by simp,
    right_inv := λ j, rfl }

@[simp] lemma basis_fun_apply [decidable_eq η] (i) :
  basis_fun R η i = std_basis R (λ (i : η), R) i 1 :=
by simp [basis_fun]

@[simp] lemma basis_fun_repr (x : η → R) (i : η) :
  (pi.basis_fun R η).repr x i = x i :=
by simp [basis_fun]

end

end module

end pi
