import Mathlib

/-!
# A104722: Self-convolution of repeated Catalan numbers.

Source: https://oeis.org/A104722
Credit: @vivanpoddar

The sequence (offset 0) is 1, 2, 3, 4, 7, 10, 19, 28, 56, 84, 174, 264, ...: the self-convolution of the
repeated Catalan numbers b = 1, 1, 1, 1, 2, 2, 5, 5, 14, 14, ..., b(n) = Catalan(floor(n/2)), that is
a(n) = Sum_{k=0..n} b(k)*b(n-k) (the formula of the entry).

The conjecture (R. J. Mathar, Nov 09 2012) reads
(n+4)*a(n) + (n+1)*a(n-1) - 4*(n+1)*a(n-2) + 4*(2-n)*a(n-3) = 0.
It is stated for n >= 4: at n = 3 the left-hand side is 7*4 + 4*3 - 16*2 - 4*1 = 4, so the recurrence
starts one step after the first index where all its terms are defined.
-/

namespace OMA.S_oeis_a104722

/-- The repeated Catalan numbers 1, 1, 1, 1, 2, 2, 5, 5, ...: b(n) = Catalan(floor(n/2)). -/
def b (n : ℕ) : ℕ := catalan (n / 2)

/-- A104722 (offset 0): a(n) = Sum_{k=0..n} b(k)*b(n-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (b k : ℤ) * (b (n - k) : ℤ)

/-- Mathar's conjectured recurrence for A104722. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 4) * a n + ((n : ℤ) + 1) * a (n - 1) - 4 * ((n : ℤ) + 1) * a (n - 2)
      + 4 * (2 - (n : ℤ)) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a104722
