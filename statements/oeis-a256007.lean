import Mathlib

/-!
# OEIS A256007

Source: https://oeis.org/A256007 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Haruzame0

a(n) is the n-th nonnegative integer k, in increasing order, such that
|k + 1 - 2 F| <= 1 for some positive Fibonacci number F. Those values are
2 F - 2, 2 F - 1, and 2 F. Positive Fibonacci numbers are Nat.fib i for
i > 0, so fib 0 = 0 is excluded. The OEIS offset is 0, so term n is the
value with index n.

Colin Barker conjectured that a(n) = 2 a(n - 3) - a(n - 9) for n > 12.
That identity holds for the first fifty terms.
-/

namespace OMA.S_oeis_a256007

def positiveFib (k : ℕ) : Prop := ∃ i : ℕ, 0 < i ∧ Nat.fib i = k

def good (m : ℕ) : Prop :=
  ∃ f : ℕ, positiveFib f ∧ (m = 2 * f - 2 ∨ m = 2 * f - 1 ∨ m = 2 * f)

noncomputable def term (n : ℕ) : ℕ := Nat.nth good n

theorem main : ∀ n : ℕ, 12 < n →
    (term n : ℤ) = 2 * (term (n - 3) : ℤ) - (term (n - 9) : ℤ) := by
  sorry

end OMA.S_oeis_a256007
