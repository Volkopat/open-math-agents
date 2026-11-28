import Mathlib

/-!
# OEIS A226857

Source: https://oeis.org/A226857 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Haruzame0

a(n) is the n-th nonnegative integer, in increasing order, that is both a sum
of two Fibonacci numbers and a product of two Fibonacci numbers. Fibonacci
numbers are Nat.fib, including fib 0 = 0. The two summands may be equal, and
so may the two factors. The OEIS offset is 1, so term n is the value with
index n - 1.

Colin Barker conjectured that a(n) = a(n - 3) + a(n - 6) for n > 12.
That identity holds for the first forty terms.
-/

namespace OMA.S_oeis_a226857

def isFib (k : ℕ) : Prop := ∃ i : ℕ, Nat.fib i = k

def good (m : ℕ) : Prop :=
  (∃ a b : ℕ, isFib a ∧ isFib b ∧ a + b = m) ∧
  (∃ c d : ℕ, isFib c ∧ isFib d ∧ c * d = m)

noncomputable def term (n : ℕ) : ℕ := Nat.nth good (n - 1)

theorem main : ∀ n : ℕ, 12 < n →
    term n = term (n - 3) + term (n - 6) := by
  sorry

end OMA.S_oeis_a226857
