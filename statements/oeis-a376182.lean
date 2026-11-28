import Mathlib

/-! The triangle of Werner Schulte, OEIS A376182.
Source: https://oeis.org/A376182
The position type contains exactly the cells in row order, from (1,1).
The offset and first term are 1. One occurrence in the row-major list
is equivalent to one position in the triangle. -/

namespace OMA.S_oeis_a376182

abbrev Cell := {p : ℕ × ℕ // 1 ≤ p.2 ∧ p.2 ≤ p.1}

/-- The integer (-1)^n. -/
def paritySign (n : ℕ) : ℤ := if n % 2 = 0 then 1 else -1

def entry (p : Cell) : ℤ :=
  let n : ℤ := p.val.1
  let k : ℤ := p.val.2
  (2*n^2 + 4*n + 1 - paritySign p.val.1) / 4 -
    (1 + paritySign p.val.2) * (n-k) - k

theorem main : (∀ p : Cell, 0 < entry p) ∧
    ∀ u : ℤ, 0 < u → ∃! p : Cell, entry p = u := by
  sorry

end OMA.S_oeis_a376182
