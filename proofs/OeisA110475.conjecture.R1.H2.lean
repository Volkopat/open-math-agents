import OMAReductions.R_OeisA110475_conjecture_R1
import Mathlib

-- Step OeisA110475.conjecture.R1.H2: hypothesis H2 of reduction OeisA110475.conjecture.R1
-- Credit: @ivillar. The indices n <= 11 with a(n) = 1 are 4, 6, 8, 9, 10 (a vanishes at 0, 1 and at primes), and no two of them sum to an element of {1, ..., 7, 9, 11}.

/-! Step OeisA110475.conjecture.R1.H2. -/

namespace P8A110475

open OeisA110475

lemma a_prime {p : ℕ} (hp : p.Prime) : a p = 0 := by
  dsimp [a]
  simp [Nat.Prime.primeFactors hp, Nat.Prime.factorization hp]

lemma a_zero : a 0 = 0 := by
  dsimp [a]
  simp

lemma a_one : a 1 = 0 := by
  dsimp [a]
  simp

lemma small (n : ℕ) (hn : n ≤ 11) (h : a n = 1) :
    n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 9 ∨ n = 10 := by
  interval_cases n <;> first
    | omega
    | (rw [a_zero] at h; omega)
    | (rw [a_one] at h; omega)
    | (rw [a_prime (by norm_num)] at h; omega)

theorem backward : ∀ m : ℕ, 0 < m → (∃ x y : ℕ, a x = 1 ∧ a y = 1 ∧ m = x + y) →
    m ∉ exceptionalSet := by
  rintro m _ ⟨x, y, hx, hy, rfl⟩ hmem
  simp only [exceptionalSet, Finset.mem_insert, Finset.mem_singleton] at hmem
  have hx' : x ≤ 11 := by omega
  have hy' : y ≤ 11 := by omega
  rcases small x hx' hx with h1 | h1 | h1 | h1 | h1 <;>
    rcases small y hy' hy with h2 | h2 | h2 | h2 | h2 <;> omega

end P8A110475

theorem OMA.solution : OMA.R_OeisA110475_conjecture_R1.H2 :=
  P8A110475.backward
