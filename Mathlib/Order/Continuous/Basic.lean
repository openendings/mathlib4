import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Continuous.Defs
import Mathlib.Order.DirSupClosed
import Mathlib.Order.ScottContinuity
import Mathlib.Order.UpperLower.Principal

/-
# The way-below relation and continuous partial orders

This file provides basic results about the way-below relation and continuous partial orders
([Domain Theory, 2.2][abramsky_gabbay_maibaum_1994]).
Definitions are in `Defs.lean`.

## Main results

* `wayBelowBasis_separation_not_le`
* `ScottContinuous.wayBelowBasis_restrict_inj`
* `ScottContinuous.wayBelowBasis_unique_extension`
* `proof_wanted scott_open_iff_eq_union_of_way_above_mem`

TODO: `Mathlib/Topology/Order/ScottTopology/Continuous.lean`
[Domain Theory, Lemma 2.3.8][abramsky_gabbay_maibaum_1994]: "In a continuous [and OrderTop] CondCPO,
every Scott-open set is a union of Scott-open filters."

## References

* [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]

## Tags

domain theory, way below, order of approximation, continuous partial order, continuous domain
-/

namespace Order

section

universe u v

variable {α : Type u}

theorem isWayBelow_subrelation [inst : PartialOrder α] :
    Subrelation IsWayBelow inst.le := (IsWayBelow.le ·)

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

proof_wanted compact_element_mem_wayBelowBasis [PartialOrder α] {x : α} (h : IsCompactElement x)
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

theorem isWayBelowBasis_iff_csSup
    [inst : ConditionallyCompleteLattice α]
    (s : Set α) : IsWayBelowBasis s ↔ ∀ y : α,
    {x ∈ s | IsWayBelow x y}.Nonempty
    --TODO
    ∧
    DirectedOn (· ≤ ·) {x ∈ s | IsWayBelow x y}
    ∧
    y = sSup {x ∈ s | IsWayBelow x y} := by
  simp_all only [isWayBelowBasis_iff]
  congrm ∀ y, ?_
  simp only [and_congr_right_iff]
  intro h_ne h_dir
  show IsLUB {x ∈ s | IsWayBelow x y} y ↔ y = sSup {x ∈ s | IsWayBelow x y}
  refine ⟨?mp, ?mpr⟩
  case mp =>
    intro h
    exact Eq.symm <| IsLUB.csSup_eq  h h_ne
  case mpr =>
    intro h
    obtain h' : BddAbove {x | x ∈ s ∧ IsWayBelow x y} := by
      apply (bddAbove_iff_exists_ge y).mpr
      use y
      apply And.intro (le_refl y)
      suffices ∀ x, (x ∈ s ∧ IsWayBelow x y) → x ≤ y by
        exact fun y_2 a ↦ le_of_eq_of_le rfl (this y_2 a)
      intro x
      clear h_ne h_dir h
      grind only [isWayBelow_le]
    generalize {x | x ∈ s ∧ IsWayBelow x y} = b_y at *
    subst h
    exact ConditionallyCompletePartialOrderSup.isLUB_csSup_of_directed b_y h_dir h_ne h'

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
proof_wanted wayBelow_interpolation {α : Type u} [ConditionallyCompletePartialOrder α] [OrderTop α]
  (b : Set α) (hb : IsWayBelowBasis b) (s : Finset α) (y : α) (h : ∀ x ∈ s, IsWayBelow x y) :
    Nonempty {z ∈ b | (∀ x ∈ s, IsWayBelow x z) ∧ IsWayBelow z y}

/--
A Scott-continuous function is determined by its action on the basis.
-/
proof_wanted ScottContinuous.wayBelowBasis_restrict_inj
    {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β]
    {b : Set α}
    (hb : IsWayBelowBasis b)
    {f : α → β} (hf : ScottContinuous f)
    {g : α → β} (hg : ScottContinuous g)
  :
    b.restrict f = b.restrict g ↔ f = g

/--
A Scott-continuous function on the basis uniquely extends to a Scott-continuous function on the
partial order.
-/
proof_wanted ScottContinuous.wayBelowBasis_uniq_extension
    {α : Type u} {β : Type v} [PartialOrder α]
    [ConditionallyCompletePartialOrder β] [OrderTop β]
    {b : Set α}
    {f : b → β} (h : ScottContinuous f)
    (hb : IsWayBelowBasis b) :
    ∃! g : α → β, ScottContinuous g ∧ b.restrict g = f

end _WayBelowBasis

section _DirSup

namespace Continuous

proof_wanted dirSupInacc_iff_forall_mem_nonempty_way_belows
    [ConditionallyCompletePartialOrder α] (hc : IsContinuousPartialOrder α)
    {s : Set α} :
    DirSupInacc s ↔ ∀ y ∈ s, Nonempty {x ∈ s | IsWayBelow x y}

proof_wanted scott_open_iff_eq_union_of_way_above_mem
    [ConditionallyCompletePartialOrder α] (hc : IsContinuousPartialOrder α)
    {s : Set α} :
    IsUpperSet s ∧ DirSupInacc s ↔ s = Set.sUnion {{y ∈ s | IsWayBelow x y} | x ∈ s}

-- TODO in a continuous dcpo, way-below iff Scott-open interior contains

-- TODO in a continuous dcpo, every Scott-open set is a union of Scott-open filters

end Continuous

end _DirSup

end

end Order
