import Mathlib

/-!
# A258139: Number of ways to write n as p^2 + q with p and q both prime.

Source: https://oeis.org/A258139
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry; verified for n up to 10^9): for any integer n > 0, we
have a(n+r) > 0 for some r = 0, 1, 2, 3, 4, 5. Moreover, if n = 6*k + 2, then a(n) > 0 except for
k = 0, 1, 12, 28, 102, 117, 168, 4079.

Formalization notes:
* a(m) > 0 is stated as: m = p^2 + q for primes p, q.
* The second claim is stated as an equivalence for every k ≥ 0: 6k + 2 is represented iff k is
  not in the exceptional set.
* Controls (computed): the first claim holds for n < 100000; for k < 20000 the exceptions are
  exactly the listed k.
-/

namespace OMA.S_oeis_a258139



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ r p q : ℕ, r ≤ 5 ∧ p.Prime ∧ q.Prime ∧ p ^ 2 + q = n + r) ∧
      ∀ k : ℕ, (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ^ 2 + q = 6 * k + 2) ↔
        k ∉ ({0, 1, 12, 28, 102, 117, 168, 4079} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a258139
