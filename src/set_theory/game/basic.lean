/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Scott Morrison, Apurva Nakade
-/
import set_theory.game.pgame
import tactic.abel

/-!
# Combinatorial games.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the quotient of pre-games by the equivalence relation
`p ≈ q ↔ p ≤ q ∧ q ≤ p` (its `antisymmetrization`), and construct an instance `add_comm_group game`,
as well as an instance `partial_order game`.

## Multiplication on pre-games

We define the operations of multiplication and inverse on pre-games, and prove a few basic theorems
about them. Multiplication is not well-behaved under equivalence of pre-games i.e. `x ≈ y` does not
imply `x * z ≈ y * z`. Hence, multiplication is not a well-defined operation on games. Nevertheless,
the abelian group structure on games allows us to simplify many proofs for pre-games.
-/

open function pgame

open_locale pgame

universes u

instance pgame.setoid : setoid pgame :=
⟨(≈), equiv_refl, @pgame.equiv.symm, @pgame.equiv.trans⟩

/-- The type of combinatorial games. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a combinatorial pre-game is built
  inductively from two families of combinatorial games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC.
  A combinatorial game is then constructed by quotienting by the equivalence
  `x ≈ y ↔ x ≤ y ∧ y ≤ x`. -/
abbreviation game := quotient pgame.setoid

namespace game

instance : add_comm_group_with_one game :=
{ zero := ⟦0⟧,
  one := ⟦1⟧,
  neg := quot.lift (λ x, ⟦-x⟧) (λ x y h, quot.sound ((@neg_equiv_neg_iff x y).2 h)),
  add := quotient.lift₂ (λ x y : pgame, ⟦x + y⟧)
    (λ x₁ y₁ x₂ y₂ hx hy, quot.sound (pgame.add_congr hx hy)),
  add_zero := by { rintro ⟨x⟩, exact quot.sound (add_zero_equiv x) },
  zero_add := by { rintro ⟨x⟩, exact quot.sound (zero_add_equiv x) },
  add_assoc := by { rintros ⟨x⟩ ⟨y⟩ ⟨z⟩, exact quot.sound add_assoc_equiv },
  add_left_neg := by { rintro ⟨x⟩, exact quot.sound (add_left_neg_equiv x) },
  add_comm := by { rintros ⟨x⟩ ⟨y⟩, exact quot.sound add_comm_equiv } }

instance : inhabited game := ⟨0⟩

instance : partial_order game :=
{ le := quotient.lift₂ (≤) (λ x₁ y₁ x₂ y₂ hx hy, propext (le_congr hx hy)),
  le_refl := by { rintro ⟨x⟩, exact le_refl x },
  le_trans := by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩, exact @le_trans _ _ x y z },
  le_antisymm := by { rintro ⟨x⟩ ⟨y⟩ h₁ h₂, apply quot.sound, exact ⟨h₁, h₂⟩ },
  lt := quotient.lift₂ (<) (λ x₁ y₁ x₂ y₂ hx hy, propext (lt_congr hx hy)),
  lt_iff_le_not_le := by { rintro ⟨x⟩ ⟨y⟩, exact @lt_iff_le_not_le _ _ x y }, }

/-- The less or fuzzy relation on games.

If `0 ⧏ x` (less or fuzzy with), then Left can win `x` as the first player. -/
def lf : game → game → Prop :=
quotient.lift₂ lf (λ x₁ y₁ x₂ y₂ hx hy, propext (lf_congr hx hy))

local infix ` ⧏ `:50 := lf

/-- On `game`, simp-normal inequalities should use as few negations as possible. -/
@[simp] theorem not_le : ∀ {x y : game}, ¬ x ≤ y ↔ y ⧏ x :=
by { rintro ⟨x⟩ ⟨y⟩, exact pgame.not_le }

/-- On `game`, simp-normal inequalities should use as few negations as possible. -/
@[simp] theorem not_lf : ∀ {x y : game}, ¬ x ⧏ y ↔ y ≤ x :=
by { rintro ⟨x⟩ ⟨y⟩, exact not_lf }

instance : is_trichotomous game (⧏) :=
⟨by { rintro ⟨x⟩ ⟨y⟩, change _ ∨ ⟦x⟧ = ⟦y⟧ ∨ _, rw quotient.eq, apply lf_or_equiv_or_gf }⟩

/-! It can be useful to use these lemmas to turn `pgame` inequalities into `game` inequalities, as
the `add_comm_group` structure on `game` often simplifies many proofs. -/

theorem _root_.pgame.le_iff_game_le {x y : pgame} : x ≤ y ↔ ⟦x⟧ ≤ ⟦y⟧ := iff.rfl
theorem _root_.pgame.lf_iff_game_lf {x y : pgame} : pgame.lf x y ↔ ⟦x⟧ ⧏ ⟦y⟧ := iff.rfl
theorem _root_.pgame.lt_iff_game_lt {x y : pgame} : x < y ↔ ⟦x⟧ < ⟦y⟧ := iff.rfl
theorem _root_.pgame.equiv_iff_game_eq {x y : pgame} : x ≈ y ↔ ⟦x⟧ = ⟦y⟧ :=
(@quotient.eq _ _ x y).symm

/-- The fuzzy, confused, or incomparable relation on games.

If `x ‖ 0`, then the first player can always win `x`. -/
def fuzzy : game → game → Prop :=
quotient.lift₂ fuzzy (λ x₁ y₁ x₂ y₂ hx hy, propext (fuzzy_congr hx hy))

local infix ` ‖ `:50 := fuzzy

theorem _root_.pgame.fuzzy_iff_game_fuzzy {x y : pgame} : pgame.fuzzy x y ↔ ⟦x⟧ ‖ ⟦y⟧ := iff.rfl

instance covariant_class_add_le : covariant_class game game (+) (≤) :=
⟨by { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h, exact @add_le_add_left _ _ _ _ b c h a }⟩

instance covariant_class_swap_add_le : covariant_class game game (swap (+)) (≤) :=
⟨by { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h, exact @add_le_add_right _ _ _ _ b c h a }⟩

instance covariant_class_add_lt : covariant_class game game (+) (<) :=
⟨by { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h, exact @add_lt_add_left _ _ _ _ b c h a }⟩

instance covariant_class_swap_add_lt : covariant_class game game (swap (+)) (<) :=
⟨by { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ h, exact @add_lt_add_right _ _ _ _ b c h a }⟩

theorem add_lf_add_right : ∀ {b c : game} (h : b ⧏ c) (a), b + a ⧏ c + a :=
by { rintro ⟨b⟩ ⟨c⟩ h ⟨a⟩, apply add_lf_add_right h }

theorem add_lf_add_left : ∀ {b c : game} (h : b ⧏ c) (a), a + b ⧏ a + c :=
by { rintro ⟨b⟩ ⟨c⟩ h ⟨a⟩, apply add_lf_add_left h }

instance ordered_add_comm_group : ordered_add_comm_group game :=
{ add_le_add_left := @add_le_add_left _ _ _ game.covariant_class_add_le,
  ..game.add_comm_group_with_one,
  ..game.partial_order }

end game

namespace pgame

@[simp] lemma quot_neg (a : pgame) : ⟦-a⟧ = -⟦a⟧ := rfl

@[simp] lemma quot_add (a b : pgame) : ⟦a + b⟧ = ⟦a⟧ + ⟦b⟧ := rfl

@[simp] lemma quot_sub (a b : pgame) : ⟦a - b⟧ = ⟦a⟧ - ⟦b⟧ := rfl

theorem quot_eq_of_mk_quot_eq {x y : pgame}
  (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves)
  (hl : ∀ i, ⟦x.move_left i⟧ = ⟦y.move_left (L i)⟧)
  (hr : ∀ j, ⟦x.move_right j⟧ = ⟦y.move_right (R j)⟧) : ⟦x⟧ = ⟦y⟧ :=
by { simp_rw [quotient.eq] at hl hr, exact quot.sound (equiv_of_mk_equiv L R hl hr) }

/-! Multiplicative operations can be defined at the level of pre-games,
but to prove their properties we need to use the abelian group structure of games.
Hence we define them here. -/

/-- The product of `x = {xL | xR}` and `y = {yL | yR}` is
`{xL*y + x*yL - xL*yL, xR*y + x*yR - xR*yR | xL*y + x*yR - xL*yR, x*yL + xR*y - xR*yL }`. -/
instance : has_mul pgame.{u} :=
⟨λ x y, begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  have y := mk yl yr yL yR,
  refine ⟨xl × yl ⊕ xr × yr, xl × yr ⊕ xr × yl, _, _⟩; rintro (⟨i, j⟩ | ⟨i, j⟩),
  { exact IHxl i y + IHyl j - IHxl i (yL j) },
  { exact IHxr i y + IHyr j - IHxr i (yR j) },
  { exact IHxl i y + IHyr j - IHxl i (yR j) },
  { exact IHxr i y + IHyl j - IHxr i (yL j) }
end⟩

theorem left_moves_mul : ∀ (x y : pgame.{u}), (x * y).left_moves
  = (x.left_moves × y.left_moves ⊕ x.right_moves × y.right_moves)
| ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ := rfl

theorem right_moves_mul : ∀ (x y : pgame.{u}), (x * y).right_moves
  = (x.left_moves × y.right_moves ⊕ x.right_moves × y.left_moves)
| ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ := rfl

/-- Turns two left or right moves for `x` and `y` into a left move for `x * y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def to_left_moves_mul {x y : pgame} :
  x.left_moves × y.left_moves ⊕ x.right_moves × y.right_moves ≃ (x * y).left_moves :=
equiv.cast (left_moves_mul x y).symm

/-- Turns a left and a right move for `x` and `y` into a right move for `x * y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def to_right_moves_mul {x y : pgame} :
  x.left_moves × y.right_moves ⊕ x.right_moves × y.left_moves ≃ (x * y).right_moves :=
equiv.cast (right_moves_mul x y).symm

@[simp] lemma mk_mul_move_left_inl {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_left (sum.inl (i, j)) =
  xL i * mk yl yr yL yR + mk xl xr xL xR * yL j - xL i * yL j :=
rfl

@[simp] lemma mul_move_left_inl {x y : pgame} {i j} :
   (x * y).move_left (to_left_moves_mul (sum.inl (i, j))) =
   x.move_left i * y + x * y.move_left j - x.move_left i * y.move_left j :=
by { cases x, cases y, refl }

@[simp] lemma mk_mul_move_left_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_left (sum.inr (i, j)) =
  xR i * mk yl yr yL yR + mk xl xr xL xR * yR j - xR i * yR j :=
rfl

@[simp] lemma mul_move_left_inr {x y : pgame} {i j} :
  (x * y).move_left (to_left_moves_mul (sum.inr (i, j))) =
  x.move_right i * y + x * y.move_right j - x.move_right i * y.move_right j :=
by { cases x, cases y, refl }

@[simp] lemma mk_mul_move_right_inl {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inl (i, j)) =
  xL i * mk yl yr yL yR + mk xl xr xL xR * yR j - xL i * yR j :=
rfl

@[simp] lemma mul_move_right_inl {x y : pgame} {i j} :
  (x * y).move_right (to_right_moves_mul (sum.inl (i, j))) =
  x.move_left i * y + x * y.move_right j - x.move_left i * y.move_right j :=
by { cases x, cases y, refl }

@[simp] lemma mk_mul_move_right_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inr (i, j)) =
  xR i * mk yl yr yL yR + mk xl xr xL xR * yL j - xR i * yL j :=
rfl

@[simp] lemma mul_move_right_inr {x y : pgame} {i j} :
  (x * y).move_right (to_right_moves_mul (sum.inr (i, j))) =
  x.move_right i * y + x * y.move_left j - x.move_right i * y.move_left j :=
by { cases x, cases y, refl }

@[simp] lemma neg_mk_mul_move_left_inl {xl xr yl yr} {xL xR yL yR} {i j} :
  (-(mk xl xr xL xR * mk yl yr yL yR)).move_left (sum.inl (i, j)) =
  -(xL i * mk yl yr yL yR + mk xl xr xL xR * yR j - xL i * yR j) :=
rfl

@[simp] lemma neg_mk_mul_move_left_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (-(mk xl xr xL xR * mk yl yr yL yR)).move_left (sum.inr (i, j)) =
  -(xR i * mk yl yr yL yR + mk xl xr xL xR * yL j - xR i * yL j) :=
rfl

@[simp] lemma neg_mk_mul_move_right_inl {xl xr yl yr} {xL xR yL yR} {i j} :
  (-(mk xl xr xL xR * mk yl yr yL yR)).move_right (sum.inl (i, j)) =
  -(xL i * mk yl yr yL yR + mk xl xr xL xR * yL j - xL i * yL j) :=
rfl

@[simp] lemma neg_mk_mul_move_right_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (-(mk xl xr xL xR * mk yl yr yL yR)).move_right (sum.inr (i, j)) =
  -(xR i * mk yl yr yL yR + mk xl xr xL xR * yR j - xR i * yR j) :=
rfl

lemma left_moves_mul_cases {x y : pgame} (k) {P : (x * y).left_moves → Prop}
  (hl : ∀ ix iy, P $ to_left_moves_mul (sum.inl ⟨ix, iy⟩))
  (hr : ∀ jx jy, P $ to_left_moves_mul (sum.inr ⟨jx, jy⟩)) : P k :=
begin
  rw ←to_left_moves_mul.apply_symm_apply k,
  rcases to_left_moves_mul.symm k with ⟨ix, iy⟩ | ⟨jx, jy⟩,
  { apply hl },
  { apply hr }
end

lemma right_moves_mul_cases {x y : pgame} (k) {P : (x * y).right_moves → Prop}
  (hl : ∀ ix jy, P $ to_right_moves_mul (sum.inl ⟨ix, jy⟩))
  (hr : ∀ jx iy, P $ to_right_moves_mul (sum.inr ⟨jx, iy⟩)) : P k :=
begin
  rw ←to_right_moves_mul.apply_symm_apply k,
  rcases to_right_moves_mul.symm k with ⟨ix, iy⟩ | ⟨jx, jy⟩,
  { apply hl },
  { apply hr }
end

/-- `x * y` and `y * x` have the same moves. -/
def mul_comm_relabelling : Π (x y : pgame.{u}), x * y ≡r y * x
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ := begin
  refine ⟨equiv.sum_congr (equiv.prod_comm _ _) (equiv.prod_comm _ _),
    (equiv.sum_comm _ _).trans (equiv.sum_congr (equiv.prod_comm _ _) (equiv.prod_comm _ _)), _, _⟩;
  rintro (⟨i, j⟩ | ⟨i, j⟩);
  dsimp;
  exact ((add_comm_relabelling _ _).trans $ (mul_comm_relabelling _ _).add_congr
    (mul_comm_relabelling _ _)).sub_congr (mul_comm_relabelling _ _)
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem quot_mul_comm (x y : pgame.{u}) : ⟦x * y⟧ = ⟦y * x⟧ :=
quot.sound (mul_comm_relabelling x y).equiv

/-- `x * y` is equivalent to `y * x`. -/
theorem mul_comm_equiv (x y : pgame) : x * y ≈ y * x :=
quotient.exact $ quot_mul_comm _ _

instance is_empty_mul_zero_left_moves (x : pgame.{u}) : is_empty (x * 0).left_moves :=
by { cases x, apply sum.is_empty }
instance is_empty_mul_zero_right_moves (x : pgame.{u}) : is_empty (x * 0).right_moves :=
by { cases x, apply sum.is_empty }
instance is_empty_zero_mul_left_moves (x : pgame.{u}) : is_empty (0 * x).left_moves :=
by { cases x, apply sum.is_empty }
instance is_empty_zero_mul_right_moves (x : pgame.{u}) : is_empty (0 * x).right_moves :=
by { cases x, apply sum.is_empty }

/-- `x * 0` has exactly the same moves as `0`. -/
def mul_zero_relabelling (x : pgame) : x * 0 ≡r 0 := relabelling.is_empty _

/-- `x * 0` is equivalent to `0`. -/
theorem mul_zero_equiv (x : pgame) : x * 0 ≈ 0 := (mul_zero_relabelling x).equiv

@[simp] theorem quot_mul_zero (x : pgame) : ⟦x * 0⟧ = ⟦0⟧ :=
@quotient.sound _ _ (x * 0) _ x.mul_zero_equiv

/-- `0 * x` has exactly the same moves as `0`. -/
def zero_mul_relabelling (x : pgame) : 0 * x ≡r 0 := relabelling.is_empty _

/-- `0 * x` is equivalent to `0`. -/
theorem zero_mul_equiv (x : pgame) : 0 * x ≈ 0 := (zero_mul_relabelling x).equiv

@[simp] theorem quot_zero_mul (x : pgame) : ⟦0 * x⟧ = ⟦0⟧ :=
@quotient.sound _ _ (0 * x) _ x.zero_mul_equiv

/-- `-x * y` and `-(x * y)` have the same moves. -/
def neg_mul_relabelling : Π (x y : pgame.{u}), -x * y ≡r -(x * y)
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ := begin
  refine ⟨equiv.sum_comm _ _, equiv.sum_comm _ _, _, _⟩;
  rintro (⟨i, j⟩ | ⟨i, j⟩);
  dsimp;
  apply ((neg_add_relabelling _ _).trans _).symm;
  apply ((neg_add_relabelling _ _).trans (relabelling.add_congr _ _)).sub_congr;
  exact (neg_mul_relabelling _ _).symm
end
using_well_founded { dec_tac := pgame_wf_tac }

@[simp] theorem quot_neg_mul (x y : pgame) : ⟦-x * y⟧ = -⟦x * y⟧ :=
quot.sound (neg_mul_relabelling x y).equiv

/-- `x * -y` and `-(x * y)` have the same moves. -/
def mul_neg_relabelling (x y : pgame) : x * -y ≡r -(x * y) :=
(mul_comm_relabelling x _).trans $
  (neg_mul_relabelling _ x).trans (mul_comm_relabelling y x).neg_congr

@[simp] theorem quot_mul_neg (x y : pgame) : ⟦x * -y⟧ = -⟦x * y⟧ :=
quot.sound (mul_neg_relabelling x y).equiv

@[simp] theorem quot_left_distrib : Π (x y z : pgame), ⟦x * (y + z)⟧ = ⟦x * y⟧ + ⟦x * z⟧
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  let z := mk zl zr zL zR,
  refine quot_eq_of_mk_quot_eq _ _ _ _,
  { fsplit,
    { rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩); refl },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩); refl } },
  { fsplit,
    { rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩); refl },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩); refl } },
  { rintro (⟨i, j | k⟩ | ⟨i, j | k⟩),
    { change ⟦xL i * (y + z) + x * (yL j + z) - xL i * (yL j + z)⟧
             = ⟦xL i * y + x * yL j - xL i * yL j + x * z⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xL i * (y + z) + x * (y + zL k) - xL i * (y + zL k)⟧
             = ⟦x * y + (xL i * z + x * zL k - xL i * zL k)⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xR i * (y + z) + x * (yR j + z) - xR i * (yR j + z)⟧
             = ⟦xR i * y + x * yR j - xR i * yR j + x * z⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xR i * (y + z) + x * (y + zR k) - xR i * (y + zR k)⟧
             = ⟦x * y + (xR i * z + x * zR k - xR i * zR k)⟧,
      simp [quot_left_distrib], abel } },
  { rintro (⟨i, j | k⟩ | ⟨i, j | k⟩),
    { change ⟦xL i * (y + z) + x * (yR j + z) - xL i * (yR j + z)⟧
             = ⟦xL i * y + x * yR j - xL i * yR j + x * z⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xL i * (y + z) + x * (y + zR k) - xL i * (y + zR k)⟧
             = ⟦x * y + (xL i * z + x * zR k - xL i * zR k)⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xR i * (y + z) + x * (yL j + z) - xR i * (yL j + z)⟧
             = ⟦xR i * y + x * yL j - xR i * yL j + x * z⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xR i * (y + z) + x * (y + zL k) - xR i * (y + zL k)⟧
             = ⟦x * y + (xR i * z + x * zL k - xR i * zL k)⟧,
      simp [quot_left_distrib], abel } }
end
using_well_founded { dec_tac := pgame_wf_tac }

/-- `x * (y + z)` is equivalent to `x * y + x * z.`-/
theorem left_distrib_equiv (x y z : pgame) : x * (y + z) ≈ x * y + x * z :=
quotient.exact $ quot_left_distrib _ _ _

@[simp] theorem quot_left_distrib_sub (x y z : pgame) : ⟦x * (y - z)⟧ = ⟦x * y⟧ - ⟦x * z⟧ :=
by { change  ⟦x * (y + -z)⟧ = ⟦x * y⟧ + -⟦x * z⟧, rw [quot_left_distrib, quot_mul_neg] }

@[simp] theorem quot_right_distrib (x y z : pgame) : ⟦(x + y) * z⟧ = ⟦x * z⟧ + ⟦y * z⟧ :=
by simp only [quot_mul_comm, quot_left_distrib]

/-- `(x + y) * z` is equivalent to `x * z + y * z.`-/
theorem right_distrib_equiv (x y z : pgame) : (x + y) * z ≈ x * z + y * z :=
quotient.exact $ quot_right_distrib _ _ _

@[simp] theorem quot_right_distrib_sub (x y z : pgame) : ⟦(y - z) * x⟧ = ⟦y * x⟧ - ⟦z * x⟧ :=
by { change ⟦(y + -z) * x⟧ = ⟦y * x⟧ + -⟦z * x⟧, rw [quot_right_distrib, quot_neg_mul] }

/-- `x * 1` has the same moves as `x`. -/
def mul_one_relabelling : Π (x : pgame.{u}), x * 1 ≡r x
| ⟨xl, xr, xL, xR⟩ := begin
  unfold has_one.one,
  refine ⟨(equiv.sum_empty _ _).trans (equiv.prod_punit _),
    (equiv.empty_sum _ _).trans (equiv.prod_punit _), _, _⟩;
  try { rintro (⟨i, ⟨ ⟩⟩ | ⟨i, ⟨ ⟩⟩) }; try { intro i };
  dsimp;
  apply (relabelling.sub_congr (relabelling.refl _) (mul_zero_relabelling _)).trans;
  rw sub_zero;
  exact (add_zero_relabelling _).trans (((mul_one_relabelling _).add_congr
    (mul_zero_relabelling _)).trans $ add_zero_relabelling _)
end

@[simp] theorem quot_mul_one (x : pgame) : ⟦x * 1⟧ = ⟦x⟧ := quot.sound $ mul_one_relabelling x

/-- `x * 1` is equivalent to `x`. -/
theorem mul_one_equiv (x : pgame) : x * 1 ≈ x := quotient.exact $ quot_mul_one x

/-- `1 * x` has the same moves as `x`. -/
def one_mul_relabelling (x : pgame) : 1 * x ≡r x :=
(mul_comm_relabelling 1 x).trans $ mul_one_relabelling x

@[simp] theorem quot_one_mul (x : pgame) : ⟦1 * x⟧ = ⟦x⟧ := quot.sound $ one_mul_relabelling x

/-- `1 * x` is equivalent to `x`. -/
theorem one_mul_equiv (x : pgame) : 1 * x ≈ x := quotient.exact $ quot_one_mul x

theorem quot_mul_assoc : Π (x y z : pgame), ⟦x * y * z⟧ = ⟦x * (y * z)⟧
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  let z := mk zl zr zL zR,
  refine quot_eq_of_mk_quot_eq _ _ _ _,
  { fsplit,
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 7 } },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_,⟨_, _⟩ | ⟨_, _⟩⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 7 } },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_,_⟩ | ⟨_, _⟩,_⟩); refl },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_,⟨_, _⟩ | ⟨_, _⟩⟩); refl } },
  { fsplit,
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩,_⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 7 } },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 7 } },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩,_⟩); refl },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩); refl } },
  { rintro (⟨⟨i, j⟩ | ⟨i, j⟩, k⟩ | ⟨⟨i, j⟩ | ⟨i, j⟩, k⟩),
    { change ⟦(xL i * y + x * yL j - xL i * yL j) * z + (x * y) * zL k
               - (xL i * y + x * yL j - xL i * yL j) * zL k⟧
             = ⟦xL i * (y * z) + x * (yL j * z + y * zL k - yL j * zL k)
               - xL i * (yL j * z + y * zL k - yL j * zL k)⟧,
      simp [quot_mul_assoc], abel },
    { change ⟦(xR i * y + x * yR j - xR i * yR j) * z + (x * y) * zL k
               - (xR i * y + x * yR j - xR i * yR j) * zL k⟧
             = ⟦xR i * (y * z) + x * (yR j * z + y * zL k - yR j * zL k)
               - xR i * (yR j * z + y * zL k - yR j * zL k)⟧,
      simp [quot_mul_assoc], abel },
    { change ⟦(xL i * y + x * yR j - xL i * yR j) * z + (x * y) * zR k
               - (xL i * y + x * yR j - xL i * yR j) * zR k⟧
             = ⟦xL i * (y * z) + x * (yR j * z + y * zR k - yR j * zR k)
               - xL i * (yR j * z + y * zR k - yR j * zR k)⟧,
      simp [quot_mul_assoc], abel },
    { change ⟦(xR i * y + x * yL j - xR i * yL j) * z + (x * y) * zR k
               - (xR i * y + x * yL j - xR i * yL j) * zR k⟧
             = ⟦xR i * (y * z) + x * (yL j * z + y * zR k - yL j * zR k)
               - xR i * (yL j * z + y * zR k - yL j * zR k)⟧,
      simp [quot_mul_assoc], abel } },
  { rintro (⟨⟨i, j⟩ | ⟨i, j⟩, k⟩ | ⟨⟨i, j⟩ | ⟨i, j⟩, k⟩),
    { change ⟦(xL i * y + x * yL j - xL i * yL j) * z + (x * y) * zR k
               - (xL i * y + x * yL j - xL i * yL j) * zR k⟧
             = ⟦xL i * (y * z) + x * (yL j * z + y * zR k - yL j * zR k)
               - xL i * (yL j * z + y * zR k - yL j * zR k)⟧,
      simp [quot_mul_assoc], abel },
    { change ⟦(xR i * y + x * yR j - xR i * yR j) * z + (x * y) * zR k
               - (xR i * y + x * yR j - xR i * yR j) * zR k⟧
             = ⟦xR i * (y * z) + x * (yR j * z + y * zR k - yR j * zR k)
               - xR i * (yR j * z + y * zR k - yR j * zR k)⟧,
      simp [quot_mul_assoc], abel },
    { change ⟦(xL i * y + x * yR j - xL i * yR j) * z + (x * y) * zL k
               - (xL i * y + x * yR j - xL i * yR j) * zL k⟧
             = ⟦xL i * (y * z) + x * (yR j * z + y * zL k - yR j * zL k)
               - xL i * (yR j * z + y * zL k - yR j * zL k)⟧,
      simp [quot_mul_assoc], abel },
    { change ⟦(xR i * y + x * yL j - xR i * yL j) * z + (x * y) * zL k
               - (xR i * y + x * yL j - xR i * yL j) * zL k⟧
             = ⟦xR i * (y * z) + x * (yL j * z + y * zL k - yL j * zL k)
               - xR i * (yL j * z + y * zL k - yL j * zL k)⟧,
      simp [quot_mul_assoc], abel } }
end
using_well_founded { dec_tac := pgame_wf_tac }

/-- `x * y * z` is equivalent to `x * (y * z).`-/
theorem mul_assoc_equiv (x y z : pgame) : x * y * z ≈ x * (y * z) :=
quotient.exact $ quot_mul_assoc _ _ _

/-- Because the two halves of the definition of `inv` produce more elements
on each side, we have to define the two families inductively.
This is the indexing set for the function, and `inv_val` is the function part. -/
inductive inv_ty (l r : Type u) : bool → Type u
| zero : inv_ty ff
| left₁ : r → inv_ty ff → inv_ty ff
| left₂ : l → inv_ty tt → inv_ty ff
| right₁ : l → inv_ty ff → inv_ty tt
| right₂ : r → inv_ty tt → inv_ty tt

instance (l r : Type u) [is_empty l] [is_empty r] : is_empty (inv_ty l r tt) :=
⟨by rintro (_|_|_|a|a); exact is_empty_elim a⟩

instance (l r : Type u) : inhabited (inv_ty l r ff) := ⟨inv_ty.zero⟩

instance unique_inv_ty (l r : Type u) [is_empty l] [is_empty r] : unique (inv_ty l r ff) :=
{ uniq := by { rintro (a|a|a), refl, all_goals { exact is_empty_elim a } },
  ..inv_ty.inhabited l r }

/-- Because the two halves of the definition of `inv` produce more elements
of each side, we have to define the two families inductively.
This is the function part, defined by recursion on `inv_ty`. -/
def inv_val {l r} (L : l → pgame) (R : r → pgame)
  (IHl : l → pgame) (IHr : r → pgame) : ∀ {b}, inv_ty l r b → pgame
| _ inv_ty.zero := 0
| _ (inv_ty.left₁ i j) := (1 + (R i - mk l r L R) * inv_val j) * IHr i
| _ (inv_ty.left₂ i j) := (1 + (L i - mk l r L R) * inv_val j) * IHl i
| _ (inv_ty.right₁ i j) := (1 + (L i - mk l r L R) * inv_val j) * IHl i
| _ (inv_ty.right₂ i j) := (1 + (R i - mk l r L R) * inv_val j) * IHr i

@[simp] theorem inv_val_is_empty {l r : Type u} {b} (L R IHl IHr) (i : inv_ty l r b)
  [is_empty l] [is_empty r] : inv_val L R IHl IHr i = 0 :=
begin
  cases i with a _ a _ a _ a,
  { refl },
  all_goals { exact is_empty_elim a }
end

/-- The inverse of a positive surreal number `x = {L | R}` is
given by `x⁻¹ = {0,
  (1 + (R - x) * x⁻¹L) * R, (1 + (L - x) * x⁻¹R) * L |
  (1 + (L - x) * x⁻¹L) * L, (1 + (R - x) * x⁻¹R) * R}`.
Because the two halves `x⁻¹L, x⁻¹R` of `x⁻¹` are used in their own
definition, the sets and elements are inductively generated. -/
def inv' : pgame → pgame
| ⟨l, r, L, R⟩ :=
  let l' := {i // 0 < L i},
      L' : l' → pgame := λ i, L i.1,
      IHl' : l' → pgame := λ i, inv' (L i.1),
      IHr := λ i, inv' (R i) in
  ⟨inv_ty l' r ff, inv_ty l' r tt,
    inv_val L' R IHl' IHr, inv_val L' R IHl' IHr⟩

theorem zero_lf_inv' : ∀ (x : pgame), 0 ⧏ inv' x
| ⟨xl, xr, xL, xR⟩ := by { convert lf_mk _ _ inv_ty.zero, refl }

/-- `inv' 0` has exactly the same moves as `1`. -/
def inv'_zero : inv' 0 ≡r 1 :=
begin
  change mk _ _ _ _ ≡r 1,
  refine ⟨_, _, λ i, _, is_empty.elim _⟩,
  { apply equiv.equiv_punit (inv_ty _ _ _),
    apply_instance },
  { apply equiv.equiv_pempty (inv_ty _ _ _),
    apply_instance },
  { simp },
  { dsimp,
    apply_instance }
end

theorem inv'_zero_equiv : inv' 0 ≈ 1 := inv'_zero.equiv

/-- `inv' 1` has exactly the same moves as `1`. -/
def inv'_one : inv' 1 ≡r (1 : pgame.{u}) :=
begin
  change relabelling (mk _ _ _ _) 1,
  haveI : is_empty {i : punit.{u+1} // (0 : pgame.{u}) < 0},
  { rw lt_self_iff_false, apply_instance },
  refine ⟨_, _, λ i, _, is_empty.elim _⟩; dsimp,
  { apply equiv.equiv_punit },
  { apply equiv.equiv_of_is_empty },
  { simp },
  { apply_instance }
end

theorem inv'_one_equiv : inv' 1 ≈ 1 := inv'_one.equiv

/-- The inverse of a pre-game in terms of the inverse on positive pre-games. -/
noncomputable instance : has_inv pgame :=
⟨by { classical, exact λ x, if x ≈ 0 then 0 else if 0 < x then inv' x else -inv' (-x) }⟩

noncomputable instance : has_div pgame := ⟨λ x y, x * y⁻¹⟩

theorem inv_eq_of_equiv_zero {x : pgame} (h : x ≈ 0) : x⁻¹ = 0 :=
by { classical, exact if_pos h }

@[simp] theorem inv_zero : (0 : pgame)⁻¹ = 0 :=
inv_eq_of_equiv_zero (equiv_refl _)

theorem inv_eq_of_pos {x : pgame} (h : 0 < x) : x⁻¹ = inv' x :=
by { classical, exact (if_neg h.lf.not_equiv').trans (if_pos h) }

theorem inv_eq_of_lf_zero {x : pgame} (h : x ⧏ 0) : x⁻¹ = -inv' (-x) :=
by { classical, exact (if_neg h.not_equiv).trans (if_neg h.not_gt) }

/-- `1⁻¹` has exactly the same moves as `1`. -/
def inv_one : 1⁻¹ ≡r 1 :=
by { rw inv_eq_of_pos pgame.zero_lt_one, exact inv'_one }

theorem inv_one_equiv : 1⁻¹ ≈ 1 := inv_one.equiv

end pgame
