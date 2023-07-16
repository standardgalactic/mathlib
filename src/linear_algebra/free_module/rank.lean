/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import linear_algebra.dimension

/-!

# Extra results about `module.rank`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some extra results not in `linear_algebra.dimension`.

-/

universes u v w

variables (R : Type u) (M : Type v) (N : Type w)

open_locale tensor_product direct_sum big_operators cardinal

open cardinal

section ring

variables [ring R] [strong_rank_condition R]
variables [add_comm_group M] [module R M] [module.free R M]
variables [add_comm_group N] [module R N] [module.free R N]

open module.free

@[simp] lemma rank_finsupp (ι : Type w) :
  module.rank R (ι →₀ M) = cardinal.lift.{v} #ι * cardinal.lift.{w} (module.rank R M) :=
begin
  obtain ⟨⟨_, bs⟩⟩ := module.free.exists_basis R M,
  rw [← bs.mk_eq_rank'', ← (finsupp.basis (λa:ι, bs)).mk_eq_rank'',
    cardinal.mk_sigma, cardinal.sum_const]
end

lemma rank_finsupp' (ι : Type v) : module.rank R (ι →₀ M) = #ι * module.rank R M :=
by simp [rank_finsupp]

/-- The rank of `(ι →₀ R)` is `(# ι).lift`. -/
@[simp] lemma rank_finsupp_self (ι : Type w) : module.rank R (ι →₀ R) = (# ι).lift :=
by simp [rank_finsupp]

/-- If `R` and `ι` lie in the same universe, the rank of `(ι →₀ R)` is `# ι`. -/
lemma rank_finsupp_self' {ι : Type u} : module.rank R (ι →₀ R) = # ι := by simp

/-- The rank of the direct sum is the sum of the ranks. -/
@[simp] lemma rank_direct_sum  {ι : Type v} (M : ι → Type w) [Π (i : ι), add_comm_group (M i)]
  [Π (i : ι), module R (M i)] [Π (i : ι), module.free R (M i)] :
  module.rank R (⨁ i, M i) = cardinal.sum (λ i, module.rank R (M i)) :=
begin
  let B := λ i, choose_basis R (M i),
  let b : basis _ R (⨁ i, M i) := dfinsupp.basis (λ i, B i),
  simp [← b.mk_eq_rank'', λ i, (B i).mk_eq_rank''],
end

/-- If `m` and `n` are `fintype`, the rank of `m × n` matrices is `(# m).lift * (# n).lift`. -/
@[simp] lemma rank_matrix (m : Type v) (n : Type w) [finite m] [finite n] :
  module.rank R (matrix m n R) = (lift.{(max v w u) v} (# m)) * (lift.{(max v w u) w} (# n)) :=
begin
  casesI nonempty_fintype m,
  casesI nonempty_fintype n,
  have h := (matrix.std_basis R m n).mk_eq_rank,
  rw [← lift_lift.{(max v w u) (max v w)}, lift_inj] at h,
  simpa using h.symm,
end

/-- If `m` and `n` are `fintype` that lie in the same universe, the rank of `m × n` matrices is
  `(# n * # m).lift`. -/
@[simp] lemma rank_matrix' (m n : Type v) [finite m] [finite n] :
  module.rank R (matrix m n R) =  (# m * # n).lift :=
by rw [rank_matrix, lift_mul, lift_umax]

/-- If `m` and `n` are `fintype` that lie in the same universe as `R`, the rank of `m × n` matrices
  is `# m * # n`. -/
@[simp] lemma rank_matrix'' (m n : Type u) [finite m] [finite n] :
  module.rank R (matrix m n R) =  # m * # n := by simp

end ring

section comm_ring

variables [comm_ring R] [strong_rank_condition R]
variables [add_comm_group M] [module R M] [module.free R M]
variables [add_comm_group N] [module R N] [module.free R N]

open module.free

/-- The rank of `M ⊗[R] N` is `(module.rank R M).lift * (module.rank R N).lift`. -/
@[simp] lemma rank_tensor_product : module.rank R (M ⊗[R] N) = lift.{w v} (module.rank R M) *
  lift.{v w} (module.rank R N) :=
begin
  let ιM := choose_basis_index R M,
  let ιN := choose_basis_index R N,

  have h₁ := linear_equiv.lift_rank_eq (tensor_product.congr (repr R M) (repr R N)),
  let b : basis (ιM × ιN) R (_ →₀ R) := finsupp.basis_single_one,
  rw [linear_equiv.rank_eq (finsupp_tensor_finsupp' R ιM ιN), ← b.mk_eq_rank, mk_prod] at h₁,
  rw [lift_inj.1 h₁, rank_eq_card_choose_basis_index R M, rank_eq_card_choose_basis_index R N],
end

/-- If `M` and `N` lie in the same universe, the rank of `M ⊗[R] N` is
  `(module.rank R M) * (module.rank R N)`. -/
lemma rank_tensor_product' (N : Type v) [add_comm_group N] [module R N] [module.free R N] :
  module.rank R (M ⊗[R] N) = (module.rank R M) * (module.rank R N) := by simp

end comm_ring
