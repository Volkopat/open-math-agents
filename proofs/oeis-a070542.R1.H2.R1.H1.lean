import OMAReductions.R_oeis_a070542_R1_H2_R1

-- Step oeis-a070542.R1.H2.R1.H1: hypothesis H1 of reduction oeis-a070542.R1.H2.R1
-- Credit: @luciusacarr
-- H1 := ∀ n : ℕ, 1 ≤ n → n ≤ 49 →     (∀ p ∈ Finset.range (2 * n + 1), ∀ q ∈ Finset.range (2 * n + 1),       ¬ (p.Prime ∧ q.Prime ∧ p ≠ q ∧ p ∣ Nat.choose (2 * n) n ∧         q ∣ Nat.choose (2 * n) n ∧ p + q = 2 * n)) →     n ∈ ({1, 2, 3, 4, 6, 10, 15, 26, 28, 64} : Set ℕ)

/-! Finite check: for each `n ≤ 49` outside the exceptional list, an explicit pair of distinct
primes `p + q = 2n` dividing `C(2n, n)` contradicts the hypothesis. Divisibility of the
central binomial coefficient is checked through `C(2n,n) = (2n)! / (n! n!)`. -/

namespace OMA.S70542H1

theorem cd (n p : ℕ) (h : p ∣ (2 * n).factorial / (n.factorial * n.factorial)) :
    p ∣ Nat.choose (2 * n) n := by
  rw [Nat.choose_eq_factorial_div_factorial (by omega), show 2 * n - n = n by omega]
  exact h

end OMA.S70542H1

open OMA.S70542H1 in
theorem OMA.solution : OMA.R_oeis_a070542_R1_H2_R1.H1 := by
  intro n h1 h49 h
  interval_cases n
  · simp
  · simp
  · simp
  · simp
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 5 3 (by decide +kernel), cd 5 7 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 7 (by simp))
  · simp
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 7 3 (by decide +kernel), cd 7 11 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 11 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 8 3 (by decide +kernel), cd 8 13 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 13 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 9 5 (by decide +kernel), cd 9 13 (by decide +kernel), by norm_num⟩ (h 5 (by simp) 13 (by simp))
  · simp
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 11 3 (by decide +kernel), cd 11 19 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 19 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 12 7 (by decide +kernel), cd 12 17 (by decide +kernel), by norm_num⟩ (h 7 (by simp) 17 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 13 7 (by decide +kernel), cd 13 19 (by decide +kernel), by norm_num⟩ (h 7 (by simp) 19 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 14 5 (by decide +kernel), cd 14 23 (by decide +kernel), by norm_num⟩ (h 5 (by simp) 23 (by simp))
  · simp
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 16 3 (by decide +kernel), cd 16 29 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 29 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 17 3 (by decide +kernel), cd 17 31 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 31 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 18 5 (by decide +kernel), cd 18 31 (by decide +kernel), by norm_num⟩ (h 5 (by simp) 31 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 19 7 (by decide +kernel), cd 19 31 (by decide +kernel), by norm_num⟩ (h 7 (by simp) 31 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 20 3 (by decide +kernel), cd 20 37 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 37 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 21 5 (by decide +kernel), cd 21 37 (by decide +kernel), by norm_num⟩ (h 5 (by simp) 37 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 22 3 (by decide +kernel), cd 22 41 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 41 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 23 3 (by decide +kernel), cd 23 43 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 43 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 24 5 (by decide +kernel), cd 24 43 (by decide +kernel), by norm_num⟩ (h 5 (by simp) 43 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 25 3 (by decide +kernel), cd 25 47 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 47 (by simp))
  · simp
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 27 7 (by decide +kernel), cd 27 47 (by decide +kernel), by norm_num⟩ (h 7 (by simp) 47 (by simp))
  · simp
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 29 5 (by decide +kernel), cd 29 53 (by decide +kernel), by norm_num⟩ (h 5 (by simp) 53 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 30 7 (by decide +kernel), cd 30 53 (by decide +kernel), by norm_num⟩ (h 7 (by simp) 53 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 31 19 (by decide +kernel), cd 31 43 (by decide +kernel), by norm_num⟩ (h 19 (by simp) 43 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 32 3 (by decide +kernel), cd 32 61 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 61 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 33 5 (by decide +kernel), cd 33 61 (by decide +kernel), by norm_num⟩ (h 5 (by simp) 61 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 34 7 (by decide +kernel), cd 34 61 (by decide +kernel), by norm_num⟩ (h 7 (by simp) 61 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 35 3 (by decide +kernel), cd 35 67 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 67 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 36 13 (by decide +kernel), cd 36 59 (by decide +kernel), by norm_num⟩ (h 13 (by simp) 59 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 37 7 (by decide +kernel), cd 37 67 (by decide +kernel), by norm_num⟩ (h 7 (by simp) 67 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 38 3 (by decide +kernel), cd 38 73 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 73 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 39 5 (by decide +kernel), cd 39 73 (by decide +kernel), by norm_num⟩ (h 5 (by simp) 73 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 40 7 (by decide +kernel), cd 40 73 (by decide +kernel), by norm_num⟩ (h 7 (by simp) 73 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 41 3 (by decide +kernel), cd 41 79 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 79 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 42 5 (by decide +kernel), cd 42 79 (by decide +kernel), by norm_num⟩ (h 5 (by simp) 79 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 43 3 (by decide +kernel), cd 43 83 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 83 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 44 5 (by decide +kernel), cd 44 83 (by decide +kernel), by norm_num⟩ (h 5 (by simp) 83 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 45 7 (by decide +kernel), cd 45 83 (by decide +kernel), by norm_num⟩ (h 7 (by simp) 83 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 46 3 (by decide +kernel), cd 46 89 (by decide +kernel), by norm_num⟩ (h 3 (by simp) 89 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 47 5 (by decide +kernel), cd 47 89 (by decide +kernel), by norm_num⟩ (h 5 (by simp) 89 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 48 7 (by decide +kernel), cd 48 89 (by decide +kernel), by norm_num⟩ (h 7 (by simp) 89 (by simp))
  · exact absurd ⟨by norm_num, by norm_num, by norm_num, cd 49 19 (by decide +kernel), cd 49 79 (by decide +kernel), by norm_num⟩ (h 19 (by simp) 79 (by simp))
