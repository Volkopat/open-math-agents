import Mathlib

/-!
# A132900: Colored Motzkin paths where each of the steps has three possible colors.

Source: https://oeis.org/A132900
Credit: @vivanpoddar

The sequence (offset 0) is 1, 3, 18, 108, 729, 5103, 37179, ... The entry gives a(n) = 3^n * A001006(n),
where A001006 = 1, 1, 2, 4, 9, 21, 51, ... are the Motzkin numbers, M(0) = M(1) = 1 and
M(n+2) = M(n+1) + Sum_{k=0..n} M(k)*M(n-k). This is used here as the definition.

The conjecture (R. J. Mathar) reads
(n+2)*a(n) - 3*(2*n+1)*a(n-1) + 27*(1-n)*a(n-2) = 0.
It involves a(n-2), so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a132900

/-- The Motzkin numbers A001006: M(0) = M(1) = 1, M(n+2) = M(n+1) + Sum_{k=0..n} M(k)*M(n-k). -/
def motzkin : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) => motzkin (n + 1) + ∑ k : Fin (n + 1), motzkin k * motzkin (n - k)

/-- A132900 (offset 0): a(n) = 3^n * Motzkin(n). -/
def a (n : ℕ) : ℤ := 3 ^ n * (motzkin n : ℤ)

/-- Mathar's conjectured recurrence for A132900. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℤ) + 2) * a n - 3 * (2 * (n : ℤ) + 1) * a (n - 1) + 27 * (1 - (n : ℤ)) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a132900
