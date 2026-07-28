import Mathlib

/-!
# Strong Roberson conjecture for split-off minors

This module is the starting point for the formalization. Definitions and theorem
statements extracted from the accompanying paper will be introduced here and
split into focused modules as the development grows.
-/

namespace StrongRoberson

-- A small compile-time check that the pinned Mathlib dependency is available.
example (p : Prop) : p → p := id

end StrongRoberson
