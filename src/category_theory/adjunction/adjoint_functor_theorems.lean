/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.adjunction.basic
import category_theory.limits.shapes
import category_theory.limits.preserves.basic
import category_theory.limits.creates
import category_theory.punit

universes v u

namespace category_theory

variables {J : Type v}
variables {C : Type u} [category.{v} C]

open category limits

section

/-- The type of objects for the diagram indexing a wide (co)equalizer. -/
@[derive decidable_eq, derive inhabited] inductive walking_parallel_chunk (J : Type v) : Type v
| zero : walking_parallel_chunk
| one : walking_parallel_chunk

open walking_parallel_chunk

/-- The type family of morphisms for the diagram indexing a wide (co)equalizer. -/
@[derive decidable_eq] inductive walking_parallel_chunk.hom (J : Type v) :
  walking_parallel_chunk J → walking_parallel_chunk J → Type v
| id : Π X : walking_parallel_chunk.{v} J, walking_parallel_chunk.hom X X
| line : Π (j : J), walking_parallel_chunk.hom zero one

open walking_parallel_chunk.hom

/-- Composition of morphisms in the indexing diagram for wide (co)equalizers. -/
def walking_parallel_chunk.hom.comp :
  Π (X Y Z : walking_parallel_chunk J)
    (f : walking_parallel_chunk.hom J X Y) (g : walking_parallel_chunk.hom J Y Z),
    walking_parallel_chunk.hom J X Z
  | _ _ _ (id _)   h := h
  | _ _ _ (line j) (id one) := line j.

local attribute [tidy] tactic.case_bash

instance walking_parallel_pair.hom.category  :
  small_category (walking_parallel_chunk J) :=
{ hom  := walking_parallel_chunk.hom J,
  id   := walking_parallel_chunk.hom.id,
  comp := walking_parallel_chunk.hom.comp }

@[simp]
lemma walking_parallel_chunk.hom_id (X : walking_parallel_chunk J) :
  walking_parallel_chunk.hom.id X = 𝟙 X :=
rfl

/--
`parallel_chunk f` is the diagram in `C` consisting of the family of morphisms, each with
common domain and codomain.
-/
def parallel_chunk {X Y : C} (f : J → (X ⟶ Y)) : walking_parallel_chunk J ⥤ C :=
{ obj := λ x, walking_parallel_chunk.cases_on x X Y,
  map := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, (line j) := f j
  end,
  map_comp' :=
  begin
    rintro _ _ _ ⟨⟩ ⟨⟩;
    { unfold_aux, simp; refl },
  end }

lemma trident.is_limit.hom_ext {X Y : C} (f : J → (X ⟶ Y)) {s : cone (parallel_chunk f)}
  (hs : is_limit s) {W : C}
  {k l : W ⟶ s.X}
  (h : k ≫ fork.ι s = l ≫ fork.ι s) : k = l :=
hs.hom_ext $ fork.equalizer_ext _ h

end

open walking_parallel_chunk

/--
If `C` has (small) limits and a small weakly initial set of objects, then it has an initial object.
-/
lemma has_initial_of_weakly_initial_and_has_limits (C : Type u) [category.{v} C] [has_limits C]
  {ι : Type v} (B : ι → C) (weakly_initial : ∀ (A : C), ∃ i, nonempty (B i ⟶ A)) :
  has_initial C :=
begin
  have fromP : Π (X : C), (∏ B ⟶ X),
  { intro X,
    exact pi.π _ (weakly_initial X).some ≫ (weakly_initial X).some_spec.some },
  let endos := ∏ B ⟶ ∏ B,
  let F : walking_parallel_chunk endos ⥤ C := parallel_chunk (id : endos → endos),
  let i : limit F ⟶ ∏ B := limit.π F zero,
  have : mono i,
  { refine ⟨λ T f g eq, _⟩,
    apply limit.hom_ext,
    rintro (_ | _),
    apply eq,
    rw ← limit.w _ (_ : zero ⟶ one),
    rw reassoc_of eq,
    apply hom.line (𝟙 _) },
  have : ∀ (X : C), inhabited (limit F ⟶ X),
    intro X,
    refine ⟨i ≫ fromP X⟩,
  resetI,
  have : ∀ (X : C), unique (limit F ⟶ X),
    intro X,
    refine ⟨by apply_instance, λ a, _⟩,
    let E := equalizer a (default (limit F ⟶ X)),
    let e : E ⟶ limit F := equalizer.ι _ _,
    let h : ∏ B ⟶ E := fromP _,
    have : ((i ≫ h) ≫ e) ≫ i = i ≫ 𝟙 _,
      rw category.assoc,
      rw category.assoc,
      erw limit.w F (hom.line (h ≫ e ≫ i)),
      erw limit.w F (hom.line (𝟙 _)),
    rw [category.comp_id, cancel_mono_id i] at this,
    haveI : split_epi e := ⟨i ≫ h, this⟩,
    rw ← cancel_epi e,
    apply equalizer.condition,
  exactI has_initial_of_unique (limit F),
end

/--
The functor `G : D ⥤ C` satisfies the *solution set condition* if for every `A : C`, there is a
family of morphisms `{f_i : A ⟶ G (B_i) // i ∈ ι}` such that given any morphism `h : A ⟶ G X`,
there is some `i ∈ ι` such that `h` factors through `f_i`.

The key part of this definition is that the indexing set `ι` lives in `Type v`, where `v` is the
universe of morphisms of the category: this is the "smallness" condition which allows the general
adjoint functor theorem to go through.
-/
def solution_set_condition {D : Type u} [category.{v} D] (G : D ⥤ C) : Prop :=
  ∀ (A : C), ∃ (ι : Type v) (B : ι → D) (f : Π (i : ι), A ⟶ G.obj (B i)),
  ∀ X (h : A ⟶ G.obj X), ∃ (i : ι) (g : B i ⟶ X), f i ≫ G.map g = h

variables {D : Type u} [category.{v} D]

-- TODO: Move this to category_theory/comma.lean
instance (G : D ⥤ C) (A : C) : faithful (comma.snd (functor.from_punit A) G) := {}.

-- TODO: Move this to category_theory/comma.lean
instance comma_reflects_isos (G : D ⥤ C) (A : C) :
  reflects_isomorphisms (comma.snd (functor.from_punit A) G) :=
{ reflects := λ X Y f i, by exactI
  { inv :=
    { left := eq_to_hom (subsingleton.elim _ _),
      right := inv ((comma.snd (functor.from_punit A) G).map f),
      w' :=
      begin
        dsimp,
        simp only [id_comp, is_iso.comp_is_iso_eq],
        rw ← f.w,
        dsimp,
        simp,
      end } } }

section create

variables [small_category J] (G : D ⥤ C) [preserves_limits_of_shape J G]
variables (A : C) (F : J ⥤ comma (functor.from_punit A) G)
variables (c : cone (F ⋙ comma.snd _ G)) (t : is_limit c)

def new_cone : cone ((F ⋙ comma.snd _ _) ⋙ G) :=
{ X := A,
  π :=
  { app := λ j, (F.obj j).hom,
    naturality' := λ j₁ j₂ α, (F.map α).w } }

-- TODO: dualise and move to category_theory/limits/comma.lean
def four_ten_aux : creates_limit F (comma.snd (functor.from_punit A) G) :=
creates_limit_of_reflects_iso $ λ c t,
{ lifted_cone :=
  { X :=
    { left := ⟨⟩,
      right := c.X,
      hom := (is_limit_of_preserves G t).lift (new_cone G A F) },
    π :=
    { app := λ j,
      { left := eq_to_hom (subsingleton.elim _ _),
        right := c.π.app j,
        w' :=
        begin
          change 𝟙 A ≫ (F.obj j).hom = _,
          rw id_comp,
          apply ((is_limit_of_preserves G t).fac (new_cone G A F) j).symm,
        end },
      naturality' := λ j₁ j₂ α,
      begin
        ext,
        apply c.π.naturality α,
      end } },
  valid_lift :=
  begin
    refine cones.ext (iso.refl _) _,
    intro j,
    dsimp,
    simp,
  end,
  makes_limit :=
  { lift := λ c',
    { left := eq_to_hom (subsingleton.elim _ _),
      right :=
      begin
        apply t.lift ⟨_, λ j, _, _⟩,
        { apply (c'.π.app j).right },
        { intros j₁ j₂ α,
          rw ← c'.w α,
          dsimp,
          simp },
      end,
      w' :=
      begin
        dsimp,
        rw id_comp,
        symmetry,
        refine (is_limit_of_preserves G t).uniq (new_cone G A F) _ _,
        intro j,
        dsimp [new_cone],
        rw [assoc, ← G.map_comp],
        simp only [is_limit.fac],
        apply (c'.π.app j).w.symm.trans _,
        dsimp,
        simp,
      end },
    fac' := λ c' j,
    begin
      ext,
      dsimp,
      apply t.fac,
    end,
    uniq' := λ s m w,
    begin
      ext,
      apply t.uniq ⟨_, _⟩ _ _,
      intro j,
      dsimp at *,
      rw ← w j,
      refl,
    end } }

instance : creates_limits_of_shape J (comma.snd (functor.from_punit A) G) :=
{ creates_limit := λ F, four_ten_aux G A F }

instance [has_limits_of_shape J D] : has_limits_of_shape J (comma (functor.from_punit A) G) :=
has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape
  (comma.snd (functor.from_punit A) G)

end create

-- TODO: move this section somewhere.
-- TODO: consider showing the converse
-- TODO: dualise
-- This section proves that if each comma category (A ↓ G) has an initial object then `G` has a
-- left adjoint

section initials
noncomputable theory

variables (G : D ⥤ C)
variables [∀ A, has_initial (comma (functor.from_punit A) G)]

def F : C → D := λ A, (⊥_ (comma (functor.from_punit A) G)).right
def η (A : C) : A ⟶ G.obj (F G A) := (⊥_ (comma (functor.from_punit A) G)).hom

def init_equivalence (A : C) (B : D) :
  (F G A ⟶ B) ≃ (A ⟶ G.obj B) :=
{ to_fun := λ g, η G A ≫ G.map g,
  inv_fun := λ f,
  begin
    let B' : comma (functor.from_punit A) G := { right := B, hom := f },
    apply comma_morphism.right (initial.to B'),
  end,
  left_inv := λ g,
  begin
    let B' : comma (functor.from_punit A) G :=
      { left := punit.star, right := B, hom := η G A ≫ G.map g },
    let g' : (⊥_ (comma (functor.from_punit A) G)) ⟶ B' :=
      ⟨eq_to_hom (subsingleton.elim _ _), g, id_comp _⟩,
    have : initial.to _ = g',
    { apply colimit.hom_ext, rintro ⟨⟩ },
    change comma_morphism.right (initial.to B') = _,
    rw this,
  end,
  right_inv := λ f,
  begin
    let B' : comma (functor.from_punit A) G := { right := B, hom := f },
    apply (comma_morphism.w (initial.to B')).symm.trans _,
    dsimp,
    simp,
  end }

def init_to_adj :=
adjunction.left_adjoint_of_equiv (init_equivalence G) $
begin
  intros X Y Y' g h,
  dsimp [init_equivalence],
  simp,
end

def is_right_adjoint_of_initials : is_right_adjoint G :=
{ left := init_to_adj G,
  adj := adjunction.adjunction_of_equiv_left _ _ }
end initials

section gaft

variables (G : D ⥤ C) [has_limits D] [preserves_limits G]

/--
The general adjoint functor theorem says that if `G : D ⥤ C` preserves limits and `D` has them,
then `G` is a right adjoint.

Strictly speaking, it also gives the converse: if `G : D ⥤ C` is a right adjoint then `G` preserves
them and it satisfies the solution set condition; though this version is not shown here.
-/
noncomputable def gaft (hG : solution_set_condition G) : is_right_adjoint G :=
begin
  apply is_right_adjoint_of_initials _,
  intro A,
  specialize hG A,
  choose ι B f g hg₁ hg₂ using hG,
  apply gaft_aux _ _ _,
  { refine ⟨_⟩,
    introsI J 𝒥,
    apply_instance },
  { apply ι },
  { intro i,
    refine ⟨⟨⟩, _, f i⟩ },
  { intro L,
    refine ⟨g _ L.hom, ⟨_⟩⟩,
    refine ⟨eq_to_hom (subsingleton.elim _ _), hg₁ _ _, _⟩,
    dsimp,
    rw [hg₂, id_comp] }
end

end gaft

end category_theory
