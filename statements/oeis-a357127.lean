import Mathlib

/-!
# A357127: a(n) = A081257(n) if A081257(n) > n, otherwise a(n) = 1.

Source: https://oeis.org/A357127
Credit: @agchua

Formula lines of A357127 (Mohammed Bouras, Sep 13 2022), verbatim:
  Conjecture 1: If a(n) != 1, then a(n) = a(a(n) - n - 1).
  Conjecture 2: If n != m and a(n) = a(m), then
  a(n) = gcd(n^2 + n + 1, m^2 + m + 1) = n + m + 1.
Offset 2, so n, m >= 2. A081257(n) is the greatest prime factor of (n^3 - 1) (offset 2).
Both conjectures are stated literally, as one conjunction. Conjecture 2 is false: for n = 35,
m = 61 one has a(35) = a(61) = 97 = 35 + 61 + 1, but gcd(35^2+35+1, 61^2+61+1) =
gcd(1261, 3783) = 1261 = 13*97. (It also fails trivially at n = 16, m = 18, where
a(16) = a(18) = 1.)
-/

namespace OMA.S_oeis_a357127

/-- A081257: the greatest prime factor of n^3 - 1. -/
noncomputable def A081257 (n : ℕ) : ℕ := (n ^ 3 - 1).primeFactors.sup id

/-- A357127: a(n) = A081257(n) if A081257(n) > n, otherwise 1. -/
noncomputable def a (n : ℕ) : ℕ := if n < A081257 n then A081257 n else 1

/-- Conjecture 1 and Conjecture 2 of the entry, as printed. -/
theorem main :
    (∀ n : ℕ, 2 ≤ n → a n ≠ 1 → a n = a (a n - n - 1)) ∧
    (∀ n m : ℕ, 2 ≤ n → 2 ≤ m → n ≠ m → a n = a m →
      a n = Nat.gcd (n ^ 2 + n + 1) (m ^ 2 + m + 1) ∧
        Nat.gcd (n ^ 2 + n + 1) (m ^ 2 + m + 1) = n + m + 1) := by
  sorry

end OMA.S_oeis_a357127
