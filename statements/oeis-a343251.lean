import Mathlib

/-!
# OEIS A343251: Least cutoff k₀ recovering v₅(n) from binomial(n, k) / n

Source: https://oeis.org/A343251 (OEIS Foundation, CC BY-SA 4.0).
For `n ≥ 1` and `k₀ ≥ 1`, let `L₅(k₀, n)` be the least common denominator of the reduced
fractions `(1 / n) * binomial(n, k)` over `0 < k ≤ k₀` with `5 ∤ k`.
Let `a(n)` be the least `k₀` (with `1 ≤ k₀ ≤ n`) such that `v₅(n) = log₅(n / L₅(k₀, n))`,
equivalently `L₅(k₀, n) * 5 ^ v₅(n) = n`.

Conjecture (OEIS A343251): for every `n ≥ 1`, `a(n)` is the greatest prime power `q^e` dividing
`n` with prime `q ≠ 5` (and `1` when `n` is a power of `5`).
-/

namespace OMA.S_oeis_a343251

/-- Lowest common denominator `L_p(k₀, n)` of `{(1/n) * C(n, k) : 0 < k ≤ k₀, ¬ p ∣ k}`. -/
def L (p k₀ n : ℕ) : ℕ :=
  ((Finset.Icc 1 k₀).filter (fun k => ¬ p ∣ k)).lcm (fun k => ((Nat.choose n k : ℚ) / (n : ℚ)).den)

/-- The greatest prime power `q^e ∣ n` with prime `q ≠ p`, or `1` if none exists. -/
def maxOtherPrimePow (p n : ℕ) : ℕ :=
  (n.primeFactors.erase p).sup (fun q => q ^ (n.factorization q)) ⊔ 1

/-- Conjecture on OEIS A343251: for every `n ≥ 1`, `k₀ = maxOtherPrimePow 5 n` is the least
`k₀ ∈ [1, n]` such that `L 5 k₀ n * 5 ^ (n.factorization 5) = n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    let k₀ := maxOtherPrimePow 5 n
    1 ≤ k₀ ∧ k₀ ≤ n ∧
    L 5 k₀ n * 5 ^ (n.factorization 5) = n ∧
    ∀ k : ℕ, 1 ≤ k → k < k₀ → L 5 k n * 5 ^ (n.factorization 5) ≠ n := by
  sorry

end OMA.S_oeis_a343251
