import category_theory.monoidal.braided
import category_theory.reflects_isomorphisms
import category_theory.monoidal.End
import combinatorics.quiver
import tactic

open category_theory
open category_theory.monoidal_category

universes v v₁ v₂ v₃ u u₁ u₂ u₃
noncomputable theory

namespace category_theory

variables {C : Type u₁} [category.{v₁} C] [monoidal_category C]

inductive word₀
| blank : word₀
| concat : word₀ → word₀ → word₀

open word₀
infixr ` □ `:80 := concat

@[simp]
lemma concat_ne_right : ∀ {u v : word₀}, u □ v ≠ v
| u blank h := word₀.no_confusion h
| u (v □ w) h := concat.inj_arrow h (λ _, concat_ne_right)

@[simp]
lemma concat_ne_left : ∀ {u v : word₀}, u □ v ≠ u
| blank v h := word₀.no_confusion h
| (u □ v) w h := concat.inj_arrow h (λ h₁ _, concat_ne_left h₁)

@[simp] lemma ne_concat_right {u v} : v ≠ u □ v := concat_ne_right.symm
@[simp] lemma ne_concat_left {u v} : u ≠ u □ v := concat_ne_left.symm

inductive hom₀ : word₀ → word₀ → Sort*
| α_hom : ∀ (u v w : word₀), hom₀ ((u □ v) □ w) (u □ (v □ w))
| α_inv : ∀ (u v w : word₀), hom₀ (u □ (v □ w)) ((u □ v) □ w)
| tensor_id : ∀ {u v} (w), hom₀ u v → hom₀ (u □ w) (v □ w)
| id_tensor : ∀ (u) {v w}, hom₀ v w → hom₀ (u □ v) (u □ w)

lemma hom₀.ne {u v} (s : hom₀ u v) : u ≠ v :=
by { induction s; simp * }

@[simp]
def special : ℕ → word₀
| 0 := blank
| (n+1) := blank □ special n

@[simp]
def word₀.length : word₀ → ℕ
| blank := 0
| (v □ w) := v.length + w.length + 1

@[simp] lemma word₀.length_eq_zero_iff : ∀ (u : word₀), u.length = 0 ↔ u = blank
| blank := by simp
| (u □ v) := by simp

@[simp] lemma word₀.special_eq_blank_iff : ∀ n, special n = blank ↔ n = 0
| 0 := by simp
| (n+1) := by simp

@[simp]
def word₀.rank : word₀ → ℕ
| blank := 0
| (v □ w) := v.rank + w.rank + v.length


lemma hom₀.same_length : ∀ {u v : word₀} (s : hom₀ u v), u.length = v.length
| _ _ (hom₀.α_hom u v w) := by { dsimp, linarith }
| _ _ (hom₀.α_inv u v w) := by { dsimp, linarith }
| (u □ _) (v □ _) (hom₀.tensor_id w s) := by { dsimp, linarith [s.same_length] }
| (_ □ u) (_ □ v) (hom₀.id_tensor w s) := by { dsimp, linarith [s.same_length] }

lemma word₀.rank_eq_zero_iff : ∀ (u : word₀), u.rank = 0 ↔ u = special u.length
| blank := by simp
| (u □ v) :=
  begin
    simp only [u.rank_eq_zero_iff, v.rank_eq_zero_iff, word₀.length, special, word₀.rank,
      add_eq_zero_iff, word₀.length_eq_zero_iff],
    rw and_comm,
    apply and_congr_right,
    rintro rfl,
    simp
  end

-- inductive hom₀.is_directed : ∀ {v w : word₀}, hom₀ v w → Prop
-- | α : ∀ {u v w}, hom₀.is_directed (hom₀.α_hom u v w)
-- | tensor_id : ∀ (u) {v w} (s : hom₀ v w), hom₀.is_directed s → hom₀.is_directed (hom₀.tensor_id u s)
-- | id_tensor : ∀ {u v} (w) (s : hom₀ u v), hom₀.is_directed s → hom₀.is_directed (hom₀.id_tensor w s)

@[simp]
def hom₀.is_directed : ∀ {u v}, hom₀ u v → Prop
| _ _ (hom₀.α_hom _ _ _) := true
| _ _ (hom₀.α_inv _ _ _) := false
| _ _ (hom₀.tensor_id _ s) := s.is_directed
| _ _ (hom₀.id_tensor _ s) := s.is_directed

@[simp]
def hom₀.inv : ∀ {u v}, hom₀ u v → hom₀ v u
| _ _ (hom₀.α_hom _ _ _) := hom₀.α_inv _ _ _
| _ _ (hom₀.α_inv _ _ _) := hom₀.α_hom _ _ _
| _ _ (hom₀.tensor_id _ s) := hom₀.tensor_id _ s.inv
| _ _ (hom₀.id_tensor _ s) := hom₀.id_tensor _ s.inv

lemma hom₀.inv_inv : ∀ {u v} (s : hom₀ u v), s.inv.inv = s
| _ _ (hom₀.α_hom _ _ _) := rfl
| _ _ (hom₀.α_inv _ _ _) := rfl
| _ _ (hom₀.tensor_id _ s) := congr_arg (hom₀.tensor_id _) s.inv_inv
| _ _ (hom₀.id_tensor _ s) := congr_arg (hom₀.id_tensor _) s.inv_inv

lemma hom₀.inv_directed : ∀ {u v} (s : hom₀ u v), s.inv.is_directed ↔ ¬s.is_directed
| _ _ (hom₀.α_hom _ _ _) := by simp
| _ _ (hom₀.α_inv _ _ _) := by simp
| _ _ (hom₀.tensor_id _ s) := by simp [s.inv_directed]
| _ _ (hom₀.id_tensor _ s) := by simp [s.inv_directed]

def hom₀.is_directed.rank_lt_rank : ∀ {u v : word₀} {s : hom₀ u v}, s.is_directed → v.rank < u.rank
| _ _ (hom₀.α_hom u v w) hs := by { dsimp, linarith }
| _ _ (hom₀.α_inv u v w) hs := hs.elim
| (u □ _) (v □ _) (hom₀.tensor_id w s) hs :=
    by { dsimp at hs, simpa [s.same_length] using hs.rank_lt_rank }
| (_ □ u) (_ □ v) (hom₀.id_tensor w s) hs :=
    by { dsimp at hs, simpa [s.same_length] using hs.rank_lt_rank }

def as_quiver : quiver word₀ := ⟨hom₀⟩

lemma hom₀.subsingleton_aux :
  ∀ {u u' v v' : word₀} (s : hom₀ u v) (s' : hom₀ u' v') (hu : u = u') (hv : v = v'),
    s.is_directed → s'.is_directed → s == s'
| _ _ _ _ (hom₀.α_hom _ _ _) (hom₀.α_hom _ _ _) rfl _ _ _ := heq.rfl
| _ _ _ _ (hom₀.α_hom _ _ _) (hom₀.tensor_id _ _) rfl hv _ _ :=
    concat.inj_arrow hv (λ _ h₂, (concat_ne_right h₂).elim)
| _ _ _ _ (hom₀.α_hom u v w) (hom₀.id_tensor _ _) rfl hv _ _ :=
    concat.inj_arrow hv (λ h₁ _, (ne_concat_left h₁).elim)
| _ _ _ _ (hom₀.tensor_id u' s) (hom₀.tensor_id _ s') rfl rfl hs hs' :=
    by rw eq_of_heq (s.subsingleton_aux s' rfl rfl hs hs')
| _ _ _ _ (hom₀.tensor_id _ s) (hom₀.α_hom u v w) rfl hv _ _ :=
    concat.inj_arrow hv (λ _ h₂, (ne_concat_right h₂).elim)
| _ _ _ _ (hom₀.tensor_id w s) (hom₀.id_tensor w' s') rfl hv _ _ :=
    concat.inj_arrow hv (λ h₁ _, (s.ne h₁.symm).elim)
| _ _ _ _ (hom₀.id_tensor _ s) (hom₀.id_tensor _ s') rfl rfl hs hs' :=
    by rw eq_of_heq (s.subsingleton_aux s' rfl rfl hs hs')
| _ _ _ _ (hom₀.id_tensor _ s) (hom₀.α_hom u v w) rfl hv _ _ :=
    concat.inj_arrow hv (λ h₁ _, (concat_ne_left h₁).elim)
| _ _ _ _ (hom₀.id_tensor w s) (hom₀.tensor_id w' s') rfl hv _ _ :=
    concat.inj_arrow hv (λ h₁ _, (s'.ne h₁).elim)

lemma hom₀.subsingleton {u v} (s s' : hom₀ u v) (hs : s.is_directed) (hs' : s'.is_directed) :
  s = s' :=
eq_of_heq (s.subsingleton_aux s' rfl rfl hs hs')

def id_tensor_path (w : word₀) :
  ∀ {u v}, as_quiver.path u v → as_quiver.path (w □ u) (w □ v)
| _ _ quiver.path.nil := quiver.path.nil
| u v (quiver.path.cons t (h : hom₀ w _)) := quiver.path.cons (id_tensor_path _ t) (hom₀.id_tensor _ h)

def canonical : ∀ (u : word₀), as_quiver.path u (special u.length)
| blank := quiver.path.nil
| ((u □ v) □ w) := quiver.path.comp (quiver.arrow.to_path (hom₀.α_hom _ _ _)) sorry
| (blank □ u) :=
  begin
    change as_quiver.path _ (blank □ special (0 + u.length)),

  end

-- inductive path {V} (G : quiver.{v u} V) (a : V) : V → Sort (max (u+1) v)
-- | nil  : path a
-- | cons : Π {b c : V}, path b → G.arrow b c → path c


-- def hom₀.is_directed : ∀ {v w : word₀}, hom₀ v w → Prop
-- | _ _ hom₀.α_hom := true
-- | _ _ hom₀.α_inv := false
-- | _ _ (hom₀.tensor_id _ s) := s.is_directed
-- | _ _ (hom₀.id_tensor _ s) := s.is_directed

#reduce special 8


end category_theory
