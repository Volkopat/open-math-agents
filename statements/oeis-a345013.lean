import Mathlib

namespace OMA.S_oeis_a345013

/-- Triangle entry from OEIS A345013:
`T(n, k) = (n - k) * C(n, k) * C(2*n - k, n - 1) / n` for `n ≥ 1` and `0 ≤ k < n`. -/
def T345013 (n k : ℕ) : ℕ :=
  ((n - k) * Nat.choose n k * Nat.choose (2 * n - k) (n - 1)) / n

/-- Triangle entry from OEIS A062196: `A062196(m, k) = C(m, k) * C(m + 2, k)`. -/
def A062196 (m k : ℕ) : ℕ :=
  Nat.choose m k * Nat.choose (m + 2) k

/-- Sequence OEIS A089849: `a(2r) = C(2r, r)` (central binomial A000984) and
`a(2r + 1) = C(2r, r) / (r + 1)` (Catalan number A000108). -/
def A089849 (n : ℕ) : ℕ :=
  if n % 2 = 0 then
    Nat.choose n (n / 2)
  else
    Nat.choose (2 * (n / 2)) (n / 2) / (n / 2 + 1)

/-- Chapoton's conjectures / Peter Bala's identities (OEIS A345013, Jun 24 2023):
For every `n ≥ 1` and every `x : ℤ`:
1. `∑_{k = 0}^{n - 1} T(n, k) * (x - 1)^k = ∑_{k = 0}^{n - 1} A062196(n - 1, k) * x^k`.
2. `∑_{k = 0}^{n - 1} T(n, k) * (-2)^k = (-1)^(n / 2) * A089849(n)`. -/
theorem main :
    (∀ (n : ℕ), 1 ≤ n → ∀ x : ℤ,
      (∑ k ∈ Finset.range n, (T345013 n k : ℤ) * (x - 1) ^ k) =
        ∑ k ∈ Finset.range n, (A062196 (n - 1) k : ℤ) * x ^ k) ∧
    (∀ (n : ℕ), 1 ≤ n →
      (∑ k ∈ Finset.range n, (T345013 n k : ℤ) * (-2 : ℤ) ^ k) =
        (-1 : ℤ) ^ (n / 2) * (A089849 n : ℤ)) := by
  sorry

end OMA.S_oeis_a345013
