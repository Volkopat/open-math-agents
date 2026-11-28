import Mathlib

/-!
# A379818: a(2n+1) = a(n) for n >= 0, a(2n) = a(n) + a(n - 2^f(n)) + a(2n - 2^f(n)) + a(A025480(n-1)) for n > 0 with a(0) = 1 where f(n) = A007814(n).

Source: https://oeis.org/A379818
Credit: @agchua

Formula section of A379818 (unsigned line; the entry is by Mikhail Kurkov, Jan 03 2025):
  Conjecture: a(2^m*(2k+1)) = Sum_{j=0..m} (binomial(m+2, j+1) - binomial(m, j))*a(2^j*k)
  for m >= 0, k >= 0 with a(0) = 1.
Offset 0. The claim is stated for all m >= 0 and k >= 0, as printed, over the integers
(the coefficients binomial(m+2, j+1) - binomial(m, j) are differences).

Definitions, from the name of A379818 and its referenced sequences:
* A007814(n), the 2-adic valuation of n, is padicValNat 2 n.
* A025480 (offset 0, name: a(2n) = n, a(2n+1) = a(n)) is written with the formula
  a(n) = floor(n / 2^A001511(n+1)) of its entry (Adam Shelly), where A001511(m) = A007814(m) + 1
  is the 2-adic valuation of 2m; this closed form satisfies a(2n) = n and a(2n+1) = a(n).
* a(0) = 1; for odd n, a(n) = a((n-1)/2); for even n = 2h with h > 0,
  a(n) = a(h) + a(h - 2^f(h)) + a(n - 2^f(h)) + a(A025480(h-1)), f = A007814.
  All arguments on the right are smaller than n. This gives all 62 listed terms.
-/

namespace OMA.S_oeis_a379818

/-- A007814: the 2-adic valuation of n. -/
noncomputable def A007814 (n : ℕ) : ℕ := padicValNat 2 n

/-- A025480(n) = floor(n / 2^A001511(n+1)), with A001511(m) = A007814(m) + 1. -/
noncomputable def A025480 (n : ℕ) : ℕ := n / 2 ^ (A007814 (n + 1) + 1)

/-- A379818: a(0) = 1, a(2h+1) = a(h), and for h > 0
a(2h) = a(h) + a(h - 2^f(h)) + a(2h - 2^f(h)) + a(A025480(h-1)), f = A007814. -/
noncomputable def a (n : ℕ) : ℕ :=
  if _h0 : n = 0 then 1
  else if _h1 : n % 2 = 1 then a (n / 2)
  else a (n / 2) + a (n / 2 - 2 ^ A007814 (n / 2)) + a (n - 2 ^ A007814 (n / 2)) +
    a (A025480 (n / 2 - 1))
termination_by n
decreasing_by
  all_goals
    have h2 : 0 < 2 ^ A007814 (n / 2) := Nat.two_pow_pos _
    have h3 : A025480 (n / 2 - 1) ≤ n / 2 - 1 :=
      Nat.div_le_self (n / 2 - 1) (2 ^ (A007814 (n / 2 - 1 + 1) + 1))
    omega

/-- The conjecture: a(2^m*(2k+1)) = Sum_{j=0..m} (binomial(m+2, j+1) - binomial(m, j))*a(2^j*k)
for m >= 0, k >= 0. -/
theorem main : ∀ m k : ℕ, (a (2 ^ m * (2 * k + 1)) : ℤ) =
    ∑ j ∈ Finset.range (m + 1),
      (((Nat.choose (m + 2) (j + 1) : ℕ) : ℤ) - ((Nat.choose m j : ℕ) : ℤ)) *
        (a (2 ^ j * k) : ℤ) := by
  sorry

end OMA.S_oeis_a379818
