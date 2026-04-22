/-
Copyright (c) 2026 Chris Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Chen
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.DirectedCompletePartialOrder.Defs
public import Mathlib.Order.ScottContinuity

/-!
# Basic results on directed complete partial orders

This file contains some basic results on directed complete partial orders
and their interaction with `ScottContinuous` functions.

Definitions are in `Mathlib/Order/DirectedCompletePartialOrder/Defs.lean`.
-/

@[expose] public section

variable {ι : Sort*} {α : Type*} [DirectedCompletePartialOrder α]

-- TODO: Scott continuous homset is a dcpo

-- TODO: mk of Refl

-- TODO: closure under Prod

-- TODO: ckosure under Disjoint

-- TODO: WithBot induces an adjunction with CompletePartialOrder

end
