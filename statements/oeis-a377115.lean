import Mathlib

/-!
# A377115: coefficient of √3 in (3 + √2 + √3)^n, prime divisibility of the terms

Source: https://oeis.org/A377115
Credit: @xor2k
Sibling of OEIS A377118 (same conjecture wording); statement modelled on the accepted one for that entry.

OEIS name: a(n) = coefficient of sqrt(3) in the expansion of (3 + sqrt(2) + sqrt(3))^n.

Conjecture as OEIS words it: every prime divides a(n) for infinitely many n, and if
K(p) = (k(1), k(2),...) is the maximal subsequence of indices n such that p divides a(n), then
the difference sequence of K(p) is eventually periodic; indeed, K(p) is purely periodic for the
first 4 primes, with respective period lengths 4,8,10,10 and these periods:
p = 2: (2, 1, 1, 2); p = 3: (6, 1, 1, 3, 1, 4, 2, 6); p = 5: (6, 2, 7, 3, 10, 2, 12, 3, 9, 6);
p = 7: (14, 4, 4, 2, 12, 1, 11, 5, 1, 18).

Conventions: the OEIS offset is zero. The powers are tracked in the basis 1, √2, √3, √6, starting
from the power 1 = (1, 0, 0, 0); multiplying by 3 + √2 + √3 gives the four-coordinate recurrence
below, and `a n` is the √3 coordinate. K(p) is the increasing enumeration of all `n` with
`p ∣ a n` (including `n = 0`, as `a 0 = 0`), via `Nat.nth`; the j-th gap is the distance from its
j-th to its next element. The four displayed blocks are transcribed as printed, with their prime
labels. A block may start at any phase (a cyclic word), and its length is claimed to be the least
positive period of the full gap sequence.
-/

namespace OMA.S_oeis_a377115

/-- Coordinates of (3 + √2 + √3)^n in the basis 1, √2, √3, √6. -/
def coords : ℕ → ℕ × ℕ × ℕ × ℕ
  | 0 => (1, 0, 0, 0)
  | n + 1 =>
    let (a, b, c, d) := coords n
    (3 * a + 2 * b + 3 * c, a + 3 * b + 3 * d, a + 3 * c + 2 * d, b + c + 3 * d)

/-- The coefficient of √3. -/
def a (n : ℕ) : ℕ := (coords n).2.2.1

/-- Distance from the j-th to the next index at which p divides the term. -/
noncomputable def gap (p j : ℕ) : ℕ :=
  Nat.nth (fun n => p ∣ a n) (j + 1) - Nat.nth (fun n => p ∣ a n) j

def displayed : List (ℕ × List ℕ) := [
  (2, [2, 1, 1, 2]),
  (3, [6, 1, 1, 3, 1, 4, 2, 6]),
  (5, [6, 2, 7, 3, 10, 2, 12, 3, 9, 6]),
  (7, [14, 4, 4, 2, 12, 1, 11, 5, 1, 18])]

def generalClaim (p : ℕ) : Prop :=
    {n : ℕ | p ∣ a n}.Infinite ∧
      ∃ d > 0, ∃ N : ℕ, ∀ j ≥ N, gap p (j + d) = gap p j

def purePeriod (p d : ℕ) : Prop := 0 < d ∧ ∀ j, gap p (j + d) = gap p j

/-- The infinitude, eventual-period and four explicit pure-period claims. -/
theorem main : ∀ p : ℕ, p.Prime → generalClaim p ∧
    ∀ w : List ℕ, (p, w) ∈ displayed →
      (∃ phase : ℕ, ∀ j, gap p j = w.getD ((j + phase) % w.length) 0) ∧
      purePeriod p w.length ∧ (∀ d, purePeriod p d → w.length ≤ d) := by
  sorry

end OMA.S_oeis_a377115
