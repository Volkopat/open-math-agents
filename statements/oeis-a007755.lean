import Mathlib

/-!
# Shapiro's primality conjecture for A007755

Source: https://oeis.org/A007755.
The n-th term is the least positive start whose totient trajectory
first reaches 1 after n-1 applications, counting both the start
and 1 in the length. The value 1 is fixed by the totient, so for
n ≥ 2 it suffices to check the last two iterates.
Shapiro's conjecture asserts that this least start is prime for
every n > 1.
-/

namespace OMA.S_oeis_a007755

def starts (n : ℕ) : Set ℕ := {m | 0 < m ∧
  (Nat.totient^[n-1]) m = 1 ∧ (Nat.totient^[n-2]) m ≠ 1}

theorem main : ∀ n : ℕ, 1 < n → ∀ m : ℕ, IsLeast (starts n) m → m.Prime := by
  sorry

end OMA.S_oeis_a007755
