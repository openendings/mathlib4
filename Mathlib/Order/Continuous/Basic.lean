import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Order.CompletePartialOrder
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

section

universe u v

variable {α : Type u} [PartialOrder α]

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

/--
A compact element is way below its upper bounds.
-/
theorem compact_element_wayBelow_iff {α : Type u} [PartialOrder α] {x : α}
    (h : IsCompactElement x) (y : α) : IsWayBelow x y ↔ x ≤ y := by
  exact Iff.intro (IsWayBelow.le ·) (IsWayBelow.monotone_right h ·)

section _WayBelowBasis

proof_wanted wayBelowBasis_directed (b : Set α) (hb : IsWayBelowBasis b) : DirectedOn (· ≤ ·) b

proof_wanted compact_element_mem_wayBelowBasis {x : α} (h : IsCompactElement x)
    (b : Set α) (hb : IsWayBelowBasis b) : x ∈ b

/-
prop 2.2.4(3), CPO case
TODO: docs.
TODO: weaken this to the non OrderBot ("DCPO") case
TODO: analogue for ConditionallyComplete
-/
proof_wanted CompletePartialOrder.wayBelowBasis_supset_isWayBelowBasis
    [CompletePartialOrder α]
    {b : Set α}
    (hb : IsWayBelowBasis b)
    {s : Set α}
    (h : b ⊆ s)
    :
    IsWayBelowBasis s
-- TODO: add the specialisation to IsWayBelowBasis (Set.univ : Set α)

theorem le_dirSupOfWayBelow_separation {α : Type u} [PartialOrder α]
    (b : Set α) {{x y : α}} (hx : IsDirSupOfWayBelow x b) :
    (x ≤ y) ↔
    ∀ z ∈ b, IsWayBelow z x → z ≤ y := by
  apply Iff.intro
  case mp =>
    intros h z hz hzx
    exact hzx.le.trans h
  case mpr =>
    intro h
    rcases hx with ⟨h_ne, h_dir, h_sup⟩
    -- TODO : weaken hx by h_dir
    apply ((isLUB_iff_le_iff.mp h_sup) y).mpr _
    apply mem_upperBounds.mpr
    simp only [Set.mem_setOf_eq, and_imp]
    exact h

/--
`¬x ≤ y` is witnessed by a basis element.
-/
theorem wayBelowBasis_separation_not_le {α : Type u} [PartialOrder α]
    (b : Set α) {{x y : α}} (hb : IsWayBelowBasis b)
    (hxy : ∀ z ∈ b, IsWayBelow z x → z ≤ y) :
    x ≤ y := by
  exact (le_dirSupOfWayBelow_separation b (hb x)).mpr hxy


-- TODO: weaken this to the non OrderBot ("DCPO") case
proof_wanted wayBelow_interpolation' {α : Type u} [CompletePartialOrder α] (b : Set α)
    (hb : IsWayBelowBasis b) (y : α) :
    DirectedOn IsWayBelow {z ∈ b | IsWayBelow z y}

/--
The interpolation property: the way-belows of an element are boundedly-directed

TODO: weaken this to the non OrderBot ("DCPO") case
-/
proof_wanted wayBelow_interpolation {α : Type u} [CompletePartialOrder α] (b : Set α)
    (hb : IsWayBelowBasis b) (s : Finset α) (y : α) (h : ∀ x ∈ s, IsWayBelow x y) :
    Nonempty {z ∈ b | (∀ x ∈ s, IsWayBelow x z) ∧ IsWayBelow z y}

/--
A Scott-continuous function is determined by its action on the basis.
-/
proof_wanted ScottContinuous.wayBelowBasis_restrict_uniq
    {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β]
    {s : Set α}
    {f : s → β} (h : ScottContinuous f)
    (hb : IsWayBelowBasis s) :
    Subsingleton { g : α → β | ScottContinuous g ∧ s.restrict g = f}

/--
A Scott-continuous function on the basis uniquely extends to a Scott-continuous function on the
partial order.
-/
proof_wanted ScottContinuous.wayBelowBasis_uniq_extension
    {α : Type u} {β : Type v} [ConditionallyCompletePartialOrder α]
    [ConditionallyCompletePartialOrder β] [OrderTop β]
    {s : Set α}
    {f : s → β} (h : ScottContinuous f)
    (hb : IsWayBelowBasis s) :
    ∃! g : α → β, ScottContinuous g ∧ s.restrict g = f

end _WayBelowBasis

section _DirSup

-- TODO in a continuous dcpo, neighbourhood base

-- TODO in a continuous dcpo, way-below iff Scott-open interior contains

-- TODO in a continuous dcpo, every Scott-open set is a union of Scott-open filters

end _DirSup

end

end Order
