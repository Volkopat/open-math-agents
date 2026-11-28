import Mathlib

/-!
# A242033: a(n) = lpf(A245024(n)-1), where lpf = least prime factor (A020639).

Source: https://oeis.org/A242033
Credit: @bnb9001

A245024 lists the even numbers n for which lpf(n-1) < lpf(n-3) (offset 1: 10, 16, 22, 26, ...);
lpf is the least prime factor A020639, with lpf(1) = 1, which is `Nat.minFac` on positive
integers. The condition n > 3 keeps n - 3 a positive integer, as the definition requires (it
excludes nothing: 4, 6 and 8 fail the inequality). Then a(n) = lpf(A245024(n) - 1)
(offset 1: 3, 3, 3, 5, 3, 3, 3, 3, 7, ...).

Conjecture: the sequence contains all odd primes. Robert Israel notes that the conjecture is true:
take A245024(n) - 1 = p*q with q a prime > p and q == p^(-1) modulo every odd prime r < p, which
exists by Dirichlet's theorem.
-/

namespace OMA.S_oeis_a242033

/-- Membership in A245024: `n` is even, `n > 3`, and `lpf(n-1) < lpf(n-3)`. -/
def IsTerm (n : ℕ) : Prop := Even n ∧ 3 < n ∧ Nat.minFac (n - 1) < Nat.minFac (n - 3)

/-- A245024 (offset 1). -/
noncomputable def seq (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- A242033 (offset 1): the least prime factor of `A245024(n) - 1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.minFac (seq n - 1)

/-- The conjecture, proved: every odd prime occurs in the sequence. -/
theorem main : ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ n, 1 ≤ n ∧ a n = p := by
  sorry

end OMA.S_oeis_a242033
