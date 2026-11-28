import Mathlib

/-!
# A354846: first composite k such that exactly n primes are the sum of all but one of the numbers from 1 to k-1 that are coprime to k

Source: https://oeis.org/A354846
Credit: @jagraj28

Conjecture (stated in A354846): for every composite `k` there is at least one such prime, that
is, a prime of the form `S(k) - t`, where `S(k)` is the sum of the numbers from `1` to `k - 1`
that are coprime to `k`, and `t` is one of these numbers.

Formalization notes:
* `totativeSum k` is the sum of the `t` with `1 ≤ t ≤ k - 1` and `Nat.Coprime t k`.
* "Composite" is `1 < k ∧ ¬ k.Prime`.
* "The sum of all but one" of the numbers is `totativeSum k - t` for one of them, `t`. For
  `k ≥ 2` each such `t` is at most the sum, so the subtraction in `ℕ` is the true difference.
* A direct search confirms the conjecture for every composite `k ≤ 6000`.
-/

namespace OMA.S_oeis_a354846

/-- The sum of the numbers from `1` to `k - 1` that are coprime to `k`. -/
def totativeSum (k : ℕ) : ℕ :=
  ∑ t ∈ (Finset.Ico 1 k).filter (fun t => Nat.Coprime t k), t

/-- The conjecture of A354846: for every composite `k`, removing one of the numbers coprime to
`k` from their sum gives a prime for at least one choice. -/
theorem main :
    ∀ k : ℕ, 1 < k → ¬ k.Prime →
      ∃ t ∈ (Finset.Ico 1 k).filter (fun t => Nat.Coprime t k), (totativeSum k - t).Prime := by
  sorry

end OMA.S_oeis_a354846
