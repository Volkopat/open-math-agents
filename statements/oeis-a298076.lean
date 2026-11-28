import Mathlib

/-!
# OEIS A298076: Conjecture of T. Ordowski (2018) on divisors of (b^n - 1)/(b - 1)

Source: https://oeis.org/A298076 (OEIS Foundation, CC BY-SA 4.0).
Conjecture (T. Ordowski, 2018): Let `b` be an integer with `|b| > 1`. Then the number
`(b^n - 1)/(b - 1)` has all positive divisors `d ≡ 1 (mod n)` for a composite `n` if and only if
`n` is a weak Fermat pseudoprime to base `|b|` (i.e., `|b|^n ≡ |b| (mod n)`) such that, for each
prime divisor `p` of `n`, `(b^p - 1)/(b - 1)` has all prime divisors `q ≡ 1 (mod n)`.
-/

namespace OMA.S_oeis_a298076

/-- Conjecture (T. Ordowski, 2018, OEIS A298076): for every integer `b` with `|b| > 1` and
every composite `n > 1`, all positive divisors of `|(b^n - 1)/(b - 1)|` are congruent to
`1 (mod n)` iff `n` is a weak Fermat pseudoprime to base `|b|` (`|b|^n ≡ |b| (mod n)`) and for
every prime `p ∣ n`, every prime divisor `q` of `|(b^p - 1)/(b - 1)|` satisfies
`q ≡ 1 (mod n)`. -/
theorem main :
    ∀ b : ℤ, 1 < b.natAbs → ∀ n : ℕ, 1 < n → ¬ n.Prime →
      ((∀ d : ℕ, d ∣ ((b ^ n - 1) / (b - 1)).natAbs → d % n = 1) ↔
        (b.natAbs ^ n % n = b.natAbs % n ∧
          ∀ p : ℕ, p.Prime → p ∣ n →
            ∀ q : ℕ, q.Prime → q ∣ ((b ^ p - 1) / (b - 1)).natAbs → q % n = 1)) := by
  sorry

end OMA.S_oeis_a298076
