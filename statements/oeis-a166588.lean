import Mathlib

/-!
# A166588: Partial sums of A097331; binomial transform of A166587.

Source: https://oeis.org/A166588
Credit: @vivanpoddar

The sequence (offset 0) is 1, 2, 2, 3, 3, 5, 5, 10, 10, 24, 24, 66, ...: the partial sums of
A097331 = 1, 1, 0, 1, 0, 2, 0, 5, 0, 14, ..., where A097331(0) = 1, A097331(n) = Catalan((n-1)/2)
for odd n, and A097331(n) = 0 for even n >= 2 (https://oeis.org/A097331).

The conjecture (R. J. Mathar, Nov 15 2012) reads
(-n-1)*a(n) + (n+1)*a(n-1) + 4*(n-2)*a(n-2) + 4*(-n+2)*a(n-3) = 0.
It involves a(n-3), so it is stated for n >= 3, over the integers.
-/

namespace OMA.S_oeis_a166588

/-- A097331 (offset 0): 1, then Catalan((n-1)/2) at odd n and 0 at even n >= 2. -/
def b (n : ℕ) : ℤ :=
  if n = 0 then 1 else if n % 2 = 1 then (catalan ((n - 1) / 2) : ℤ) else 0

/-- A166588 (offset 0): a(n) = Sum_{k=0..n} A097331(k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), b k

/-- Mathar's conjectured recurrence for A166588. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (-(n : ℤ) - 1) * a n + ((n : ℤ) + 1) * a (n - 1) + 4 * ((n : ℤ) - 2) * a (n - 2)
      + 4 * (-(n : ℤ) + 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a166588
