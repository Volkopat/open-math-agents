import Mathlib

/-!
# A074162: a(1) = 1; a(n) = smallest multiple of n (>n) using all nonprime digits (1,4,6,8,9 and 0) if n is a prime else using all prime digits and 1 if n is composite; or 0 if no such number exists.

Source: https://oeis.org/A074162
Credit: @agchua

Comment of A074162 (by Sean A. Irvine, Jan 13 2025):
  Conjecture (contradicts Zucker statement): a(k*5^6) = 0.
As the listed data show (a(2) = 4, a(4) = 12, a(8) = 32, a(11) = 44), a number uses the digits
of a set when each of its decimal digits lies in that set: for a prime n the set is
{0, 1, 4, 6, 8, 9}, otherwise it is {1, 2, 3, 5, 7}. For n > 1, a(n) is the least m > n with
n | m whose digits all lie in the set, and 0 if there is none; this is sInf of the set of such m,
as sInf of the empty set of natural numbers is 0. The offset is 1, so the claim is stated for
every k >= 1 (then k*5^6 is composite).
-/

namespace OMA.S_oeis_a074162

/-- The allowed digits for n: the nonprime digits if n is prime, else the prime digits and 1. -/
def D (n : ℕ) : Finset ℕ := if Nat.Prime n then {0, 1, 4, 6, 8, 9} else {1, 2, 3, 5, 7}

/-- A074162(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 1 then 1 else sInf {m : ℕ | n < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d ∈ D n}

/-- Irvine's conjecture: a(k*5^6) = 0 for every k >= 1. -/
theorem main : ∀ k : ℕ, 1 ≤ k → a (k * 5 ^ 6) = 0 := by
  sorry

end OMA.S_oeis_a074162
