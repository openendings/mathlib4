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
theorem isWayBelow_iff {α : Type u} [PartialOrder α] (x y : α) :
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

@[trans]
theorem IsWayBelow.trans {α : Type u} [PartialOrder α] {{x y z : α}}
    (hxy : IsWayBelow x y) (hyz : IsWayBelow y z) : IsWayBelow x z := by
  exact hxy.monotone_right hyz.le

def IsDirSupOfWayBelow {α : Type u}
  [PartialOrder α] (y : α) (s : Set α) : Prop :=
  {x ∈ s | IsWayBelow x y}.Nonempty
  ∧
  DirectedOn (· ≤ ·) {x ∈ s | IsWayBelow x y}
  ∧
  IsLUB {x ∈ s | IsWayBelow x y} y

-- TODO: iff for the SupSet case

-- TODO: projections for the conjuncts of IsDirSupOfWayBelow


proof_wanted le_dirSupOfWayBelow_separation {α : Type u} [PartialOrder α]
    (s : Set α) {{x y : α}} (hxy : x ≤ y) (hy : IsDirSupOfWayBelow y s) :
    ∃ z ∈ s, IsWayBelow z y ∧ ¬z ≤ x

/--
A basis is a set with the property that every element in the poset is the
directed sup of the basis elements way below it.
-/
def IsWayBelowBasis {α : Type u}
    [PartialOrder α] (s : Set α) : Prop :=
  ∀ y : α,
  {x ∈ s | IsWayBelow x y}.Nonempty
  ∧
  DirectedOn (· ≤ ·) {x ∈ s | IsWayBelow x y}
  ∧
  IsLUB {x ∈ s | IsWayBelow x y} y

-- TODO: `IsWayBelowBasis` iff for the SupSet case

theorem isWayBelowBasis_iff {α : Type u}
    [PartialOrder α] (s : Set α) : IsWayBelowBasis s ↔ ∀ y : α,
    {x ∈ s | IsWayBelow x y}.Nonempty
    ∧
    DirectedOn (· ≤ ·) {x ∈ s | IsWayBelow x y}
    ∧
    IsLUB {x ∈ s | IsWayBelow x y} y := by rfl

theorem isWayBelowBasis_iff_all_dirSupOfWayBelow_self {α : Type u}
    [PartialOrder α] (s : Set α) :
    IsWayBelowBasis s ↔ ∀ y : α, IsDirSupOfWayBelow y s := by rfl
/-
TODO(style): is this rfl too implementation dependent?
-/

/--
Convenience projection method for `this.dirSupOfWayBelow`.
-/
theorem IsWayBelowBasis.dirSupOfWayBelow {α : Type u} [PartialOrder α]
    (s : Set α) (hs : IsWayBelowBasis s) (y : α) :
    IsDirSupOfWayBelow y s := by tauto

/--
A continuous partial order ("continuous poset") is a partial order that admits a way-below basis.
-/
def IsContinuousPartialOrder (α : Type u)
    [PartialOrder α] : Prop :=
  ∃ s : Set α, IsWayBelowBasis s

-- TODO a bundled Order.ContinuousPartialOrder

end Order

end
