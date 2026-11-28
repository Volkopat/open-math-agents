import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# OEIS A061078

For $N=5^a 2^b p$ with $a\ge1$ and $p$ a positive integer divisible by
neither $2$ nor $5$, Luca Onnis conjectures that the partial sums are
constant from index $N-1$ to index $N+55\ldots5$. The block of fives has
$b$ digits if $a>b$, and $a-1$ digits otherwise. Equivalently, its length
is $\min(a-1,b)$.

Source: https://oeis.org/A061078
-/

namespace OMA.S_oeis_a061078

/-- The sum of digit products of the first `n` positive even numbers. -/
def partialSum (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, (Nat.digits 10 (2 * (i + 1))).prod

/-- The number with exactly `r` digits, all equal to five. -/
def fives (r : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate r 5)

theorem main : ∀ a b p : ℕ, 1 ≤ a → ¬ (2 ∣ p) → ¬ (5 ∣ p) →
    ∀ j : ℕ, j ≤ fives (min (a - 1) b) →
    partialSum (5 ^ a * 2 ^ b * p + j) = partialSum (5 ^ a * 2 ^ b * p - 1) := by
  sorry

end OMA.S_oeis_a061078
