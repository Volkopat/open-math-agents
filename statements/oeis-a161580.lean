import Mathlib

/-!
# A161580: Positions n such that A010060(n) + A010060(n+3) = 1.

Source: https://oeis.org/A161580
Credit: @agchua

Comment line of A161580 (Vladimir Shevelev, Jul 31 2009), verbatim:
  Conjecture: In every sequence of numbers n such that A010060(n) + A010060(n+k) = 1, for fixed
  odd k, the odious (A000069) and evil (A001969) terms alternate.
A010060 is the Thue-Morse sequence, a(n) = A000120(n) mod 2 (the number of 1's in the binary
expansion of n, mod 2), offset 0; the odious numbers are the n with A010060(n) = 1, the evil
numbers the n with A010060(n) = 0. For a fixed odd k, the sequence in question lists all n >= 0
with A010060(n) + A010060(n+k) = 1 in increasing order (for k = 3 it is A161580, offset 1,
which starts 2, 5, 7, 10, 14). Alternation means: any two consecutive terms n < m of that
sequence (no term strictly between them) have different values A010060(n), A010060(m).
-/

namespace OMA.S_oeis_a161580

/-- A010060: the Thue-Morse sequence, the sum of the binary digits of n, mod 2. -/
def A010060 (n : ℕ) : ℕ := (Nat.digits 2 n).sum % 2

/-- For odd k, two consecutive n < m with A010060(n) + A010060(n+k) = 1 and
A010060(m) + A010060(m+k) = 1 have different Thue-Morse values. -/
theorem main : ∀ k : ℕ, k % 2 = 1 → ∀ n m : ℕ, n < m →
    A010060 n + A010060 (n + k) = 1 → A010060 m + A010060 (m + k) = 1 →
    (∀ j : ℕ, n < j → j < m → A010060 j + A010060 (j + k) ≠ 1) →
    A010060 m ≠ A010060 n := by
  sorry

end OMA.S_oeis_a161580
