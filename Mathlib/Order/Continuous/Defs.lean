module

public import Mathlib.Order.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Directed

/-!
# The way-below relation and continuous partial orders

This file defines the way-below relation ("order of approximation") and continuous partial orders,
together with basic properties.

## Main definitions

* `IsWayBelow`: the way-below relation (aka order of approximation) induced by a `PartialOrder`.
  `IsWayBelow x y` denotes, loosely speaking, that every "cover" of `y` contains a finite "subcover"
  of `x`.

* `IsWayBelowBasis`

* `IsContinuousPartialOrder`

-/

@[expose]
public section

namespace Order

universe u

/-
TODO(style): Is this an appropriate use case for
`variable {α : Type u} [PartialOrder α]`?
-/

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
theorem isWayBelow_iff {α : Type u} [PartialOrder α] (x y : α) :
    (IsWayBelow x y) ↔ ∀ (s : Set α) (u : α), s.Nonempty →
    DirectedOn (· ≤ ·) s → IsLUB s u → y ≤ u → ∃ z ∈ s, x ≤ z
  := by rfl

/--
`x << y` implies `x ≤ y`.
-/
theorem isWayBelow_le {α : Type u} [inst : PartialOrder α] (x y : α)
    (h : IsWayBelow x y) : x ≤ y := by
  specialize h {y} y (Set.singleton_nonempty y) (directedOn_singleton y)
    (isLUB_singleton) (le_refl y)
  simp_all only [Set.mem_singleton_iff, exists_eq_left]

theorem IsWayBelow.le {α : Type u} [inst : PartialOrder α] {{x y : α}}
    (h : IsWayBelow x y) : x ≤ y := isWayBelow_le x y h

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

@[trans]
theorem IsWayBelow.trans {α : Type u} [PartialOrder α] {{x y z : α}}
    (hxy : IsWayBelow x y) (hyz : IsWayBelow y z) : IsWayBelow x z := by
  exact hxy.monotone_right hyz.le

/--
A basis is a set with the property that every element in the poset is the
directed sup of the basis elements way below it.
-/
def IsWayBelowBasis {α : Type u} [PartialOrder α] (b : Set α) : Prop :=
  ∀ y : α,
  {x ∈ b | IsWayBelow x y}.Nonempty
  ∧
  DirectedOn (· ≤ ·) {x ∈ b | IsWayBelow x y}
  ∧
  IsLUB {x ∈ b | IsWayBelow x y} y

theorem isWayBelowBasis_iff {α : Type u}
    [PartialOrder α] (s : Set α) : IsWayBelowBasis s ↔ ∀ y : α,
    {x ∈ s | IsWayBelow x y}.Nonempty
    ∧
    DirectedOn (· ≤ ·) {x ∈ s | IsWayBelow x y}
    ∧
    IsLUB {x ∈ s | IsWayBelow x y} y := by rfl

/--
A continuous partial order ("continuous poset") is a partial order that admits a way-below basis.
-/
def IsContinuousPartialOrder (α : Type u)
  [PartialOrder α] : Prop :=
Nonempty {s : Set α | IsWayBelowBasis s}

-- TODO a bundled Order.ContinuousPartialOrder

abbrev IsDirSupOfWayBelow {α : Type u}
  [PartialOrder α] (y : α) (s : Set α) : Prop :=
  {x ∈ s | IsWayBelow x y}.Nonempty
  ∧
  DirectedOn (· ≤ ·) {x ∈ s | IsWayBelow x y}
  ∧
  IsLUB {x ∈ s | IsWayBelow x y} y

end Order

end
