import Mathlib

/-!
# A231883: Number of ways to write n = x + y (x, y > 0) with x^2 + (n-2)*y^2 prime.

Source: https://oeis.org/A231883
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A231883 (Zhi-Wei Sun, Nov 21 2013), part (i): a(n) > 0
for all n > 2, and a(n) = 1 only for n = 8, 12, 16. Moreover, if m and n are positive integers
with m >= max{2, n-1} and gcd(m, n+1) = 1, then x^2 + n*y^2 is prime for some positive integers x
and y with x + y = m, except for the case m = n + 3 = 29.

Conventions:
* The sequence has offset 1 (data 0, 0, 2, 2, 2, 2, 4, 1, 5, 2, 5, 1, ...). `a n` is the number of
  pairs (x, y) of positive integers with n = x + y and x^2 + (n-2)*y^2 prime, exactly as in the
  OEIS name.
* The natural-number subtraction n - 2 in the definition is exact whenever a pair (x, y) of
  positive integers with x + y = n exists (then n >= 2); in the `Moreover` sentence n - 1 is exact
  since n >= 1.
* The exceptional case m = n + 3 = 29 is the single pair (m, n) = (29, 26).
* The positivity part is stated for n > 2 and the only-if part for every n >= 1 (the offset). Both
  sentences of part (i) are formalized, as a conjunction; part (ii) is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a231883

/-- The condition in the name of A231883 on a tuple, for a given n. -/
def P (n : ℕ) (x y : ℕ) : Prop :=
  0 < x ∧ 0 < y ∧ x + y = n ∧ (x ^ 2 + (n - 2) * y ^ 2).Prime

/-- A231883: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A231883. -/
theorem main : (∀ n : ℕ, 0 < n → ((2 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({8, 12, 16} : Finset ℕ)))) ∧
    (∀ m n : ℕ, 0 < m → 0 < n → max 2 (n - 1) ≤ m → Nat.gcd m (n + 1) = 1 →
      ¬ (m = 29 ∧ n = 26) →
      ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = m ∧ (x ^ 2 + n * y ^ 2).Prime) := by
  sorry

end OMA.S_oeis_a231883
