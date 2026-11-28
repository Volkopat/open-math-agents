import Mathlib

/-!
# A204187: the sum of the (n-1)-th powers modulo n

Source: https://oeis.org/A204187 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A204187 (offset 1): a(n) = Sum_{m=1..n-1} m^(n-1) modulo n.
Data 0, 1, 2, 0, 4, 3, 6, 0, 6, 5, 10, 0, 12, 7, 10, 0, 16, 9, 18, 0, 14, 11, 22, 0, 20, 13, ...

Formula section: a(n) = n/2 iff n is of the form 4k+2 (conjectured).
- Ivan Neretin, Sep 23 2016

Formalization notes.
* `a n` is the remainder of Sum_{m=1..n-1} m^(n-1) modulo n.
* `main` is the conjecture of Neretin: a(n) = n/2 exactly when n = 4k + 2. The equation
  a(n) = n/2 is written as 2 a(n) = n (for odd n the number n/2 is not an integer, so the
  equation is false), and "n is of the form 4k+2" as n mod 4 = 2.
* The comments of the entry also mention the conjecture of Giuga (a(n) = n - 1 only for n = 1
  and for primes). That is a different, famous open conjecture; it is NOT stated here.
-/

namespace OMA.S_oeis_a204187

/-- A204187: Sum_{m=1..n-1} m^(n-1) modulo n. -/
def a (n : ℕ) : ℕ := (∑ m ∈ Finset.Ico 1 n, m ^ (n - 1)) % n

/-- Conjecture of Neretin: a(n) = n/2 if and only if n = 4k + 2. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (2 * a n = n ↔ n % 4 = 2) := by
  sorry

end OMA.S_oeis_a204187
