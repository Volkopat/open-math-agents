import Mathlib

/-!
# A237367: Number of ordered ways to write n = k + m with k > 0 and m > 0 such that 2*k - 1, prime(k)^2 - 2 and prime(m)^2 - 2 are all prime.

Source: https://oeis.org/A237367
Credit: @luciusacarr

Data: 0, 0, 1, 2, 3, 3, 3, 3, 2, 3, 2, 4, 3, 5, 2, 6, 3, 6, 2, 4, ... (offset 1).

The entry's comment (Zhi-Wei Sun) states a three-part conjecture. `main` states all three parts,
as a conjunction, in the order the source gives them.

Conjecture: (i) a(n) > 0 for all n > 2, and a(n) = 1 only for n = 3, 73, 81, 534.
(ii) Any integer n > 2 can be written as k + m with k > 0 and m > 0 such that 2*k - 1,
prime(k) + k*(k-1) and prime(m) + m*(m-1) are all prime.
(iii) Every n = 9, 10, ... can be written as k + m with k > 0 and m > 0 such that 6*k - 1,
prime(k) + 2*k and prime(m) + 2*m are all prime.

Reading of the source:
* `prime(k)` is the k-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`.
* a(n) counts the `k` with `0 < k < n` (and `m = n - k`) satisfying the three conditions. The
  first 25 data values were recomputed from this definition.
* "a(n) = 1 only for n = 3, 73, 81, 534" is stated, for every `n ≥ 1`, as: a(n) = 1 if and only
  if n is one of these four values (the data show that each of them does have a(n) = 1).
-/

namespace OMA.S_oeis_a237367

/-- The k-th prime, 1-indexed: `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- A237367(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter (fun k =>
    (2 * k - 1).Prime ∧ (prime k ^ 2 - 2).Prime ∧ (prime (n - k) ^ 2 - 2).Prime)).card

theorem main :
    -- (i) a(n) > 0 for all n > 2,
    (∀ n : ℕ, 2 < n → 0 < a n) ∧
    -- and a(n) = 1 only for n = 3, 73, 81, 534.
    (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n ∈ ({3, 73, 81, 534} : Finset ℕ))) ∧
    -- (ii) every n > 2 is k + m with 2k - 1, prime(k) + k(k-1), prime(m) + m(m-1) all prime.
    (∀ n : ℕ, 2 < n → ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ n = k + m ∧ (2 * k - 1).Prime ∧
      (prime k + k * (k - 1)).Prime ∧ (prime m + m * (m - 1)).Prime) ∧
    -- (iii) every n ≥ 9 is k + m with 6k - 1, prime(k) + 2k, prime(m) + 2m all prime.
    (∀ n : ℕ, 9 ≤ n → ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ n = k + m ∧ (6 * k - 1).Prime ∧
      (prime k + 2 * k).Prime ∧ (prime m + 2 * m).Prime) := by
  sorry

end OMA.S_oeis_a237367
