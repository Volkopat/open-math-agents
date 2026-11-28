import Mathlib

/-!
# A238576: Number of odd primes p < 2*n with prime(n*(p-1)/2)^2 - 2 prime.

Source: https://oeis.org/A238576
Credit: @luciusacarr

Data: 0, 1, 2, 3, 2, 3, 1, 4, 3, 2, 2, 4, 2, 2, 2, 3, 2, 2, 4, 5, ... (offset 1).

The entry's comment (Zhi-Wei Sun) states a two-part conjecture. `main` states both parts, as a
conjunction, in the order the source gives them.

Conjecture: (i) a(n) > 0 for all n > 1, and a(n) = 1 only for n = 2, 7, 23, 61, 73.
(ii) For any integer n > 1, there is an odd prime p < 2*n with prime(n*(p+1)/2)^2 - 2 prime.

Reading of the source:
* `prime(j)` is the j-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (j - 1)`. For an odd
  prime `p`, `(p - 1)/2` and `(p + 1)/2` are integers, so the indices are `n * ((p - 1)/2)` and
  `n * ((p + 1)/2)`.
* a(n) counts the odd primes `p < 2n` with `prime(n(p-1)/2)^2 - 2` prime. The first 30 data
  values were recomputed from this definition.
* "a(n) = 1 only for n = 2, 7, 23, 61, 73" is stated, for every `n ≥ 1`, as: a(n) = 1 if and only
  if n is one of these five values (the data show that each of them has a(n) = 1).
-/

namespace OMA.S_oeis_a238576

/-- The j-th prime, 1-indexed: `prime 1 = 2`. -/
noncomputable def prime (j : ℕ) : ℕ := Nat.nth Nat.Prime (j - 1)

/-- A238576(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n)).filter (fun p =>
    p.Prime ∧ Odd p ∧ (prime (n * ((p - 1) / 2)) ^ 2 - 2).Prime)).card

theorem main :
    -- (i) a(n) > 0 for all n > 1,
    (∀ n : ℕ, 1 < n → 0 < a n) ∧
    -- and a(n) = 1 only for n = 2, 7, 23, 61, 73.
    (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n ∈ ({2, 7, 23, 61, 73} : Finset ℕ))) ∧
    -- (ii) for n > 1 some odd prime p < 2n has prime(n(p+1)/2)^2 - 2 prime.
    (∀ n : ℕ, 1 < n → ∃ p : ℕ, p.Prime ∧ Odd p ∧ p < 2 * n ∧
      (prime (n * ((p + 1) / 2)) ^ 2 - 2).Prime) := by
  sorry

end OMA.S_oeis_a238576
