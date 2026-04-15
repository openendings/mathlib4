module

public import Mathlib.Order.CompletePartialOrder

@[expose]
public section

namespace Order

universe u

/--
`x << y` ("`x` is way below `y`") when,
given that `y ≤ sup s` for some nonempty directed set `s`,
there exists a witness `x ≤ z ∈ s`.
-/
@[match_pattern]
def IsWayBelow {α : Type u} [PartialOrder α] (x y : α) : Prop :=
  ∀ (s : Set α) (u : α), s.Nonempty → DirectedOn (· ≤ ·) s → IsLUB s u →
  y ≤ u → ∃ z ∈ s, x ≤ z

@[simp]
theorem IsWayBelow.iff {α : Type u} [PartialOrder α] (x y : α) :
    (IsWayBelow x y) ↔ ∀ (s : Set α) (u : α), s.Nonempty →
    DirectedOn (· ≤ ·) s → IsLUB s u → y ≤ u → ∃ z ∈ s, x ≤ z
  := by rfl

/--
`x << y` implies `x ≤ y`.
-/
theorem IsWayBelow.le {α : Type u} [inst : PartialOrder α] {{x y : α}}
    (h : IsWayBelow x y) : x ≤ y := by
  specialize h {y} y (Set.singleton_nonempty y) (directedOn_singleton y)
    (isLUB_singleton) (le_refl y)
  rcases h with ⟨y', ⟨hy, hxy⟩⟩
  exact le_of_le_of_eq hxy hy

/--
`z ≤ x << y` implies `z << y`.
-/
theorem IsWayBelow.monotone_left {α : Type u} [PartialOrder α]
    {{x y z : α}} (hxy : IsWayBelow x y) (hzx : z ≤ x) : IsWayBelow z y := by
  intros s lub h_ne h_dir h_lub hy
  specialize hxy s lub h_ne h_dir h_lub hy
  have this : ∀ (u : α), x ≤ u → z ≤ u := forall_ge_iff_le.mpr hzx
  tauto

/--
`x << y ≤ z` implies `z << y`.
-/
theorem IsWayBelow.monotone_right {α : Type u} [PartialOrder α]
    {{x y z : α}} (hxy : IsWayBelow x y) (hyz : y ≤ z) : IsWayBelow x z := by
  intros s lub h_ne h_dir h_lub hy
  specialize hxy s lub h_ne h_dir h_lub (hyz.trans hy)
  exact Set.inter_nonempty.mp hxy

-- TODO: projections
def IsWayBelowGeneratedBy {α : Type u}
  [PartialOrder α] [SupSet α] (y : α) (s : Set α) : Prop :=
  {x ∈ s | IsWayBelow x y}.Nonempty
  ∧
  DirectedOn (· ≤ ·) {x ∈ s | IsWayBelow x y}
  ∧
  IsLUB {x ∈ s | IsWayBelow x y} y
-- TODO is there a weaker interpolation property?
-- TODO should we just skip straight to "basis of a subset"

-- TODO basis
--proof_wanted isWayBelow_interpolation

end Order

end
