import Mathlib

/-!
# The sites of the cube and its axis steps

The sites are the points of `ℤ × ℤ × ℤ`. The only hop is the axis step `p ↦ p + e_i`; a diagonal is
a composition of two of them.
-/

namespace NRS3Hidrogeno

/-- The three axis steps of the cube: the only elementary hop. -/
def axis : Fin 3 → ℤ × ℤ × ℤ
  | 0 => (1, 0, 0)
  | 1 => (0, 1, 0)
  | 2 => (0, 0, 1)

end NRS3Hidrogeno
