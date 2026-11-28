import Mathlib

/-!
# OEIS A087788: counting 3-Carmichael numbers

Source: https://oeis.org/A087788
3-Carmichael numbers: Carmichael numbers `k = p q r` with primes `p < q < r` and
`a^(k-1) ≡ 1 (mod k)` for all `a` coprime to `k` (561, 1105, 1729, …). Granville and
Pomerance conjecture that there are `~ c x^(1/3) / (log x)^3` such numbers up to `x`
(Heath-Brown proved `O(x^(7/20 + ε))`). `main` states that the count is asymptotic to
`c x^(1/3)/(log x)^3` for some constant `c > 0`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a087788

open Filter Asymptotics Real

/-- `k` is a 3-Carmichael number. -/
def Is3Carmichael (k : ℕ) : Prop :=
  (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧ k = p * q * r) ∧
    ∀ a : ℕ, Nat.Coprime a k → a ^ (k - 1) ≡ 1 [MOD k]

theorem main :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℕ => (Set.ncard {k : ℕ | k ≤ x ∧ Is3Carmichael k} : ℝ)) ~[atTop]
        fun x : ℕ => c * (x : ℝ) ^ (1 / 3 : ℝ) / log x ^ 3 := by
  sorry

end OMA.S_oeis_a087788
