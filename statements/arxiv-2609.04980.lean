import Mathlib

/-!
# A generalized Erdős–Sierpiński conjecture: σ(n + h) = k σ(n) infinitely often

Amirali Fatehizadeh and Florian Luca, On the divisibility relation σ(n) ∣ σ(n + h) and a
generalized Erdős–Sierpiński conjecture, https://arxiv.org/abs/2609.04980, Conjecture 5.4.
Credit: @pyaf

σ is the sum-of-divisors function. The case (h, k) = (1, 1) is the classical
Erdős–Sierpiński conjecture that σ(n + 1) = σ(n) infinitely often.
-/

namespace OMA.S_arxiv_2609_04980

theorem main :
    ∀ h k : ℕ, 1 ≤ h → 1 ≤ k →
      {n : ℕ | 1 ≤ n ∧ ArithmeticFunction.sigma 1 (n + h) = k * ArithmeticFunction.sigma 1 n}.Infinite := by
  sorry

end OMA.S_arxiv_2609_04980
