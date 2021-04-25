/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.category.Top.opens
import category_theory.filtered

open category_theory
open topological_space
open opposite

universe u

variables {X Y : Top.{u}} (f : X ⟶ Y)

namespace topological_space

def open_nhds (x : X) := { U : opens X // x ∈ U }

namespace open_nhds

instance (x : X) : partial_order (open_nhds x) :=
{ le := λ U V, U.1 ≤ V.1,
  le_refl := λ _, le_refl _,
  le_trans := λ _ _ _, le_trans,
  le_antisymm := λ _ _ i j, subtype.eq $ le_antisymm i j }

instance (x : X) : lattice (open_nhds x) :=
{ inf := λ U V, ⟨U.1 ⊓ V.1, ⟨U.2, V.2⟩⟩,
  le_inf := λ U V W, @le_inf _ _ U.1.1 V.1.1 W.1.1,
  inf_le_left := λ U V, @inf_le_left _ _ U.1.1 V.1.1,
  inf_le_right := λ U V, @inf_le_right _ _ U.1.1 V.1.1,
  sup := λ U V, ⟨U.1 ⊔ V.1, V.1.1.mem_union_left U.2⟩,
  sup_le := λ U V W, @sup_le _ _ U.1.1 V.1.1 W.1.1,
  le_sup_left := λ U V, @le_sup_left _ _ U.1.1 V.1.1,
  le_sup_right := λ U V, @le_sup_right _ _ U.1.1 V.1.1,
  ..open_nhds.partial_order x }

instance (x : X) : order_top (open_nhds x) :=
{ top := ⟨⊤, trivial⟩,
  le_top := λ U, @le_top _ _ U.1.1,
  ..open_nhds.partial_order x }

instance open_nhds_category (x : X) : category.{u} (open_nhds x) :=
by {unfold open_nhds, apply_instance}

instance opens_nhds_hom_has_coe_to_fun {x : X} {U V : open_nhds x} : has_coe_to_fun (U ⟶ V) :=
{ F := λ f, U.1 → V.1,
  coe := λ f x, ⟨x, (le_of_hom f) x.2⟩ }

/--
The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets.
-/
def inf_le_left {x : X} (U V : open_nhds x) : U ⊓ V ⟶ U :=
hom_of_le inf_le_left

/--
The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets.
-/
def inf_le_right {x : X} (U V : open_nhds x) : U ⊓ V ⟶ V :=
hom_of_le inf_le_right

def inclusion (x : X) : open_nhds x ⥤ opens X :=
full_subcategory_inclusion _

@[simp] lemma inclusion_obj (x : X) (U) (p) : (inclusion x).obj ⟨U,p⟩ = U := rfl

lemma open_embedding {x : X} (U : open_nhds x) : open_embedding (U.1.inclusion) :=
U.1.open_embedding

instance open_nhds_is_filtered (x : X) : is_filtered (open_nhds x)ᵒᵖ :=
{ nonempty := ⟨op ⊤⟩,
  cocone_objs := λ U V, ⟨op (unop U ⊓ unop V),
    (inf_le_left (unop U) (unop V)).op, (inf_le_right (unop U) (unop V)).op, trivial⟩ ,
  cocone_maps := λ U V i j, ⟨V, 𝟙 V, rfl⟩, }

def map (x : X) : open_nhds (f x) ⥤ open_nhds x :=
{ obj := λ U, ⟨(opens.map f).obj U.1, by tidy⟩,
  map := λ U V i, (opens.map f).map i }

@[simp] lemma map_obj (x : X) (U) (q) : (map f x).obj ⟨U, q⟩ = ⟨(opens.map f).obj U, by tidy⟩ :=
rfl
@[simp] lemma map_id_obj (x : X) (U) : (map (𝟙 X) x).obj U = U :=
by tidy
@[simp] lemma map_id_obj' (x : X) (U) (p) (q) : (map (𝟙 X) x).obj ⟨⟨U, p⟩, q⟩ = ⟨⟨U, p⟩, q⟩ :=
rfl

@[simp] lemma map_id_obj_unop (x : X) (U : (open_nhds x)ᵒᵖ) : (map (𝟙 X) x).obj (unop U) = unop U :=
by simp
@[simp] lemma op_map_id_obj (x : X) (U : (open_nhds x)ᵒᵖ) : (map (𝟙 X) x).op.obj U = U :=
by simp

def inclusion_map_iso (x : X) : inclusion (f x) ⋙ opens.map f ≅ map f x ⋙ inclusion x :=
nat_iso.of_components
  (λ U, begin split, exact 𝟙 _, exact 𝟙 _ end)
  (by tidy)

@[simp] lemma inclusion_map_iso_hom (x : X) : (inclusion_map_iso f x).hom = 𝟙 _ := rfl
@[simp] lemma inclusion_map_iso_inv (x : X) : (inclusion_map_iso f x).inv = 𝟙 _ := rfl

end open_nhds
end topological_space
