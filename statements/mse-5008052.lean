import Mathlib

/-!
# Is it known that all primes can be expressed as a square number minus a prime number?

Source: https://math.stackexchange.com/questions/5008052/is-it-known-that-all-primes-can-be-expressed-as-a-square-number-minus-a-prime-nu
Credit: @SulkBash

## The problem, as the source states it

Conjecture: for every prime `p`, there exists an integer `n` such that `p = n² - q`, where `q`
is prime. For example `57593 = 240² - 7`. The asker checked every prime up to `1 000 000`
without finding a counterexample (for instance `999983 = 1000² - 17`).

The accepted view in the answers and comments is that this is open: it asks whether, for each
prime `p`, the quadratic polynomial `x² - p` takes at least one prime value, a special case of
the open Bunyakovsky conjecture, and the standard probabilistic heuristic predicts infinitely
many such representations. OEIS A157480 lists the least prime `q` such that `prime(k) + q` is a
square.

## Formalization notes

* `p` and `q` range over the natural-number primes (`Nat.Prime`), and `n` over the integers,
  as in the source. The equation `p = n² - q` is read in `ℤ`, so no truncated subtraction is
  involved. Since `n² = (-n)²`, taking `n` in `ℕ` instead would give an equivalent statement.
* `q` is not required to differ from `p` or to be smaller than `p`: the source asks for any
  prime `q`. For example `2 = 2² - 2` uses `q = p`.
* `main` is the conjectured affirmative answer. A disproof is a prime `p` such that `n² - p`
  is prime for no integer `n`.
-/

namespace OMA.S_mse_5008052

theorem main : ∀ p : ℕ, p.Prime → ∃ n : ℤ, ∃ q : ℕ, q.Prime ∧ (p : ℤ) = n ^ 2 - q := by
  sorry

end OMA.S_mse_5008052
