import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Order.Continuous.Defs
import Mathlib.Order.DirSupClosed
import Mathlib.Order.ScottContinuity
import Mathlib.Order.UpperLower.Principal

/-
# The way-below relation and continuous partial orders
-/
-- TODO
/-

## Main results

* `wayBelowBasis_separation_not_le`
* `ScottContinuous.wayBelowBasis_unique_extension`

## References

* [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]

## Tags

domain theory, way below, order of approximation, continuous partial order, continuous domain
-/

namespace Order

universe u v

theorem isWayBelow_iff_principal_filter_intersects {α : Type u}
  [PartialOrder α] (x y : α) : (IsWayBelow x y) ↔
  ∀ (s : Set α) (u : α), s.Nonempty → DirectedOn (· ≤ ·) s →
  IsLUB s u → y ≤ u → (s ∩ UpperSet.Ici x).Nonempty
  := by rfl -- TODO(style): is this a moral use of `rfl`, or is `tauto` preferred?

-- TODO: finite products of way-below relation

/--
The way-below relation generalizes compactness.
-/
theorem isWayBelow_refl_iff_compact {α : Type u} [PartialOrder α] (x : α) :
    (IsWayBelow x x) ↔ IsCompactElement x := by rfl

theorem compact_element_wayBelow_iff {α : Type u} [PartialOrder α] {x : α}
    (h : IsCompactElement x) (y : α) : IsWayBelow x y ↔ x ≤ y := by
  exact Iff.intro (IsWayBelow.le ·) (IsWayBelow.monotone_right h ·)

/- IsWayBelowBasis -/

proof_wanted wayBelowBasis_directed {α : Type u}
    [PartialOrder α] (b : Set α) (hb : IsWayBelowBasis b) : DirectedOn (· ≤ ·) b

-- TODO basis separation


proof_wanted le_dirSupOfWayBelow_separation {α : Type u} [PartialOrder α]
    (b : Set α) {{x y : α}} (hxy : ¬x ≤ y) (hy : IsDirSupOfWayBelow y b) :
    ∃ z ∈ b, IsWayBelow z x ∧ ¬z ≤ y

/--
`¬x ≤ y` is witnessed by a basis element.
-/
proof_wanted wayBelowBasis_separation_not_le {α : Type u} [PartialOrder α]
    (b : Set α) {{x y : α}} (hxy : ¬x ≤ y) (hb : IsWayBelowBasis b) :
    ∃ z ∈ b, IsWayBelow z x ∧ ¬z ≤ y

-- TODO basis interpolation

/--
A Scott-continuous function is determined by its action on the basis.
-/
-- TODO: this should be "exists at most one", if codomain isn't DirSupClosed.
proof_wanted ScottContinuous.wayBelowBasis_unique_extension
    {α : Type u} {β : Type v} [PartialOrder
    α] [PartialOrder β] {s : Set α} (hb : IsWayBelowBasis s) (f : s →
    β) (h : ScottContinuous f) :
    ∃! g : α → β,
    ScottContinuous g ∧ s.restrict g = f

section _DirSup

-- TODO in a continuous domain, way-below iff Scott-open interior contains

end _DirSup

end Order
