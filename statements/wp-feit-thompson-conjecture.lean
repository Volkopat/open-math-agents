import Mathlib

/-!
# Feit–Thompson conjecture

Source: https://en.wikipedia.org/wiki/Feit–Thompson_conjecture
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source (Wikipedia, "Feit–Thompson conjecture"): for all distinct prime numbers p and q,

    (p^q − 1)/(p − 1)  does not divide  (q^p − 1)/(q − 1).

The quotients are natural numbers: p − 1 ∣ p^q − 1 (geometric-sum factorization,
`Nat.sub_dvd_pow_sub_pow` 1 p q), and p prime gives p ≥ 2 so p − 1 ≥ 1; symmetrically for q.
-/

namespace OMA.S_wp_feit_thompson_conjecture

/--
Feit–Thompson: for distinct primes p and q, (p^q − 1)/(p − 1) does not divide (q^p − 1)/(q − 1).
-/
theorem main :
    ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      ¬ ((p ^ q - 1) / (p - 1) ∣ (q ^ p - 1) / (q - 1)) := by
  sorry

end OMA.S_wp_feit_thompson_conjecture
