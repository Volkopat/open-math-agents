import Mathlib

/-!
# A055078: Write n as a sum of terms of the form (p^2-1)/24 where p is a prime > 4; sequence gives those n which require at least 4 terms.

Source: https://oeis.org/A055078
Credit: @keiichisince1986-bot

A055078 is the sequence `a(n)` named in the title. The entry states:
Chowla conjectures that all numbers are the sum of no more than four terms of the form (p^2-1)/24
where p is a prime > 3.

Conventions:
- For a prime `p ≥ 5`, `24` divides `p^2 - 1`, so `(p^2 - 1)/24` is exact (and at least `1`).
- A sum of no more than four such terms is the sum over a list of at most four primes `p ≥ 5`. The
  claim is stated for every `n ≥ 1` (for `n = 0` the empty sum works).
-/

namespace OMA.S_oeis_a055078

theorem main :
    ∀ n : ℕ, ∃ l : List ℕ, l.length ≤ 4 ∧ (∀ p ∈ l, p.Prime ∧ 5 ≤ p) ∧
      (l.map (fun p => (p ^ 2 - 1) / 24)).sum = n := by
  sorry

end OMA.S_oeis_a055078
