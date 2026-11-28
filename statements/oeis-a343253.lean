import Mathlib

/-!
# OEIS A343253: Least cutoff k₀ recovering v₁₁(n) from binomial(n, k) / n

Source: https://oeis.org/A343253 (OEIS Foundation, CC BY-SA 4.0).
For `n ≥ 1` and `k₀ ≥ 1`, let `L₁₁(k₀, n)` be the least common denominator of the reduced
fractions `(1 / n) * binomial(n, k)` over `0 < k ≤ k₀` with `11 ∤ k`.
Let `a(n)` be the least `k₀` (with `1 ≤ k₀ ≤ n`) such that `v₁₁(n) = log₁₁(n / L₁₁(k₀, n))`,
equivalently `L₁₁(k₀, n) * 11 ^ v₁₁(n) = n`.

Conjecture (OEIS A343253): for every `n ≥ 1`, `a(n)` is the greatest prime power `q^e` dividing
`n` with prime `q ≠ 11` (and `1` when `n` is a power of `11`).
-/

namespace OMA.S_oeis_a343253

/-- Lowest common denominator `L_p(k₀, n)` of `{(1/n) * C(n, k) : 0 < k ≤ k₀, ¬ p ∣ k}`. -/
def L (p k₀ n : ℕ) : ℕ :=
  ((Finset.Icc 1 k₀).filter (fun k => ¬ p ∣ k)).lcm (fun k => ((Nat.choose n k : ℚ) / (n : ℚ)).den)

/-- The greatest prime power `q^e ∣ n` with prime `q ≠ p`, or `1` if none exists. -/
def maxOtherPrimePow (p n : ℕ) : ℕ :=
  (n.primeFactors.erase p).sup (fun q => q ^ (n.factorization q)) ⊔ 1

/-- Conjecture on OEIS A343253: for every `n ≥ 1`, `k₀ = maxOtherPrimePow 11 n` is the least
`k₀ ∈ [1, n]` such that `L 11 k₀ n * 11 ^ (n.factorization 11) = n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    let k₀ := maxOtherPrimePow 11 n
    1 ≤ k₀ ∧ k₀ ≤ n ∧
    L 11 k₀ n * 11 ^ (n.factorization 11) = n ∧
    ∀ k : ℕ, 1 ≤ k → k < k₀ → L 11 k n * 11 ^ (n.factorization 11) ≠ n := by
  sorry

end OMA.S_oeis_a343253
