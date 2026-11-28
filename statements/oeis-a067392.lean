import Mathlib

/-!
# A067392: Sum of numbers <= n which have common prime factors with n.

Source: https://oeis.org/A067392
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a067392

/-- A067392: a(n) = sum of the numbers `k ≤ n` with `gcd(n, k) > 1` (offset 1; a(1) = 0, a(2) = 2, a(3) = 3,
a(4) = 6, a(5) = 5, a(6) = 15, ...). -/
def a (n : ℕ) : ℕ := ∑ k ∈ (Finset.Icc 1 n).filter (fun k => 1 < Nat.gcd n k), k

/-- Conjecture (V. S. Guba, per Max Alekseyev, May 2024): for any positive `n` and prime `p`,
`a(n) ≠ a(n + p)`. -/
theorem main : ∀ n p : ℕ, 0 < n → p.Prime → a n ≠ a (n + p) := by
  sorry

end OMA.S_oeis_a067392
