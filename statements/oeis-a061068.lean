import Mathlib

/-!
# A061068: Primes which are the sum of a prime and its subscript.

Source: https://oeis.org/A061068
Credit: @luciusacarr

Conjecture (Jonathan Vos Post, Nov 22 2004). This sequence is the intersection of A014688 with the
set of primes. Conjecture: this sequence is infinite, yet derives from arbitrarily long "prime
deserts" such as the 11 composites in A014688 between a(6) = 19 and a(18) = 79 and the 17
composites in A014688 between a(48) = 271 and a(66) = 383.

Reading of the source:
* A014688 is `b(k) = prime(k) + k` for `k ≥ 1`, with `prime(1) = 2`; here
  `prime(k) = Nat.nth Nat.Prime (k - 1)`. The sequence consists of the primes of this form.
* `main` states the two claims of the comment: the sequence is infinite, and the "prime deserts"
  are arbitrarily long, i.e. for every `L` there are `L` consecutive indices `k` for which
  `b(k)` is not prime (the deserts are runs of consecutive terms of A014688 lying between two
  consecutive terms of this sequence; every `b(k)` with `k ≥ 1` is at least 3, so "not prime"
  means composite).
-/

namespace OMA.S_oeis_a061068

/-- A014688: `prime(k) + k` (meaningful for `k ≥ 1`). -/
noncomputable def b (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1) + k

theorem main :
    -- The sequence (primes of the form prime(k) + k) is infinite.
    {q : ℕ | q.Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ q = b k}.Infinite ∧
    -- Arbitrarily long runs of consecutive composite terms of A014688.
    (∀ L : ℕ, ∃ k : ℕ, 1 ≤ k ∧ ∀ i : ℕ, i < L → ¬ (b (k + i)).Prime) := by
  sorry

end OMA.S_oeis_a061068
