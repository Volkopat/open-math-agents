import OMAStatements.S_oeis_a090518
import Mathlib

/-! Proof for OEIS A090518: `k = 5 · 10^(n-1)` gives `10^n / k = 2`, which is prime, so `A090517(n)`
is the least admissible `k`, which is nonzero, and `A090518(n)` is a prime, hence nonzero.
Credit: Sudharsan Rajendiran -/

theorem OMA.solution : type_of% @OMA.S_oeis_a090518.main := by
  intro n hn
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hk : 10 ^ (m + 1) / (5 * 10 ^ m) = 2 := by
    rw [pow_succ, show 10 ^ m * 10 = 2 * (5 * 10 ^ m) by ring]
    exact Nat.mul_div_cancel _ (by positivity)
  have h : ∃ k : ℕ, (10 ^ (m + 1) / k).Prime := ⟨5 * 10 ^ m, by rw [hk]; exact Nat.prime_two⟩
  have hspec : (10 ^ (m + 1) / OMA.S_oeis_a090518.b (m + 1)).Prime := Nat.sInf_mem h
  have hb : OMA.S_oeis_a090518.b (m + 1) ≠ 0 := by
    intro h0; rw [h0, Nat.div_zero] at hspec; exact Nat.not_prime_zero hspec
  unfold OMA.S_oeis_a090518.a
  rw [if_neg hb]
  exact hspec.ne_zero
