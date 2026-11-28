import Mathlib

/-!
# A099940: a(n) = 2 * A056855(n) / (phi(n) * n)

Source: https://oeis.org/A099940

Conjecture (OEIS A099940):
For every `n ≥ 1`, `a(n) = 2 * A056855(n) / (φ(n) * n)` is an integer, where
`A056855(n) = (∏_{k} k) * (∑_{k} 1/k)` with `k` ranging over the integers in `1..n`
coprime to `n`.

Conventions:
- Offset: `1`; first terms: `2, 1, 1, 1, 5, 1, 84, 11, 184, 15, 193248, 23, ...`.
- Writing `T(n) = {k ∈ [1, n] | gcd(k, n) = 1}`, we have the exact integer identity
  `A056855(n) = ∑ k ∈ T(n), ∏ j ∈ (T(n)).erase k, j`, so integrality of `a(n)` is
  equivalent to `(Nat.totient n * n) ∣ (2 * a056855 n)`.
-/

namespace OMA.S_oeis_a099940

/-- The finite set of positive integers `≤ n` coprime to `n`. -/
def totatives (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun k => Nat.Coprime k n)

/-- Numerator `(∏_{k ∈ T(n)} k) * (∑_{k ∈ T(n)} 1 / k)` expressed as an exact integer
(OEIS A056855). -/
def a056855 (n : ℕ) : ℕ :=
  ∑ k ∈ totatives n, ∏ j ∈ (totatives n).erase k, j

/-- Conjecture: `2 * A056855(n) / (φ(n) * n)` is an integer for every `n ≥ 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → (Nat.totient n * n) ∣ (2 * a056855 n) := by
  sorry

end OMA.S_oeis_a099940
