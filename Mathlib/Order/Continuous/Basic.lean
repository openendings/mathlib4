import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Order.Continuous.Defs

namespace Order

universe u

/--
The way-below relation generalizes compactness.
-/
theorem IsWayBelow.refl_iff_compact {α : Type u} [PartialOrder α] (x : α) :
    (IsWayBelow x x) ↔ IsCompactElement x := by rfl

theorem isWayBelow_iff_principal_filter_intersects {α : Type u}
  [PartialOrder α] (x y : α) : (IsWayBelow x y) ↔
  ∀ (s : Set α) (u : α), s.Nonempty → DirectedOn (· ≤ ·) s →
  IsLUB s u → y ≤ u → (s ∩ UpperSet.Ici x).Nonempty
  := by rfl -- TODO: ???

end Order
