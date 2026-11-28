import Mathlib

/-!
# A309054: a(1) = 0; a(3m) = 1; a(3m-1) = 2*a(m-1), a(3m+1) = 2*a(m+1)

Source: https://oeis.org/A309054 (conjecture in the formula section of the entry)

Entry (offset 0): a(1) = 0; for m >= 0, a(3m) = 1; for m >= 1, a(3m-1) = 2*a(m-1),
a(3m+1) = 2*a(m+1). The sequence extends to negative n by defining a(n) = a(-n).
Conjecture: Sum_{n=-3m..3m-1} (a(n) + 1) = 4 * Sum_{n=-m..m-1} (a(n) + 1).

Conventions:
* `a : ℕ → ℕ` is defined by the recursion of the title: a(0) = 1 (the case m = 0 of
  a(3m) = 1), a(1) = 0, and for n >= 2, a(n) = 1 if n = 3m, a(n) = 2*a(m-1) if n = 3m-1
  (m = (n+1)/3), a(n) = 2*a(m+1) if n = 3m+1 (m = (n-1)/3 >= 1).
* `aZ` is the extension to the integers, aZ(n) = a(|n|), as in the entry.
* The sum over n = -3m..3m-1 is over the integer interval `Finset.Ico (-3m) (3m)`; the
  statement is for every m >= 0.
-/

namespace OMA.S_oeis_a309054

/-- A309054 on the nonnegative integers. -/
def a : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 =>
    if (n + 2) % 3 = 0 then 1
    else if (n + 2) % 3 = 2 then 2 * a ((n + 2 + 1) / 3 - 1)
    else 2 * a ((n + 2 - 1) / 3 + 1)
decreasing_by all_goals omega

/-- The extension a(n) = a(-n) to the integers. -/
def aZ (n : ℤ) : ℕ := a n.natAbs

theorem main : ∀ m : ℕ,
    ∑ n ∈ Finset.Ico (-(3 * m : ℤ)) (3 * m), (aZ n + 1) =
      4 * ∑ n ∈ Finset.Ico (-(m : ℤ)) m, (aZ n + 1) := by
  sorry

end OMA.S_oeis_a309054
