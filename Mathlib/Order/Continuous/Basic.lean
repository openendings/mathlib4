import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Order.Continuous.Defs
import Mathlib.Order.UpperLower.Principal

namespace Order

universe u

theorem isWayBelow_iff_principal_filter_intersects {α : Type u}
  [PartialOrder α] (x y : α) : (IsWayBelow x y) ↔
  ∀ (s : Set α) (u : α), s.Nonempty → DirectedOn (· ≤ ·) s →
  IsLUB s u → y ≤ u → (s ∩ UpperSet.Ici x).Nonempty
  := by rfl -- TODO: ???

-- TODO: product of way-below relation

/--
The way-below relation generalizes compactness.
-/
theorem isWayBelow_refl_iff_compact {α : Type u} [PartialOrder α] (x : α) :
    (IsWayBelow x x) ↔ IsCompactElement x := by rfl

theorem compact_element_wayBelow_iff {α : Type u} [PartialOrder α] {x : α}
    (h : IsCompactElement x) (y : α) : IsWayBelow x y ↔ x ≤ y := by
  exact Iff.intro (IsWayBelow.le ·) (IsWayBelow.monotone_right h ·)

end Order
