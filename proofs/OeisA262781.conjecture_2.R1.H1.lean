import OMAReductions.R_OeisA262781_conjecture_2_R1

open Finset
-- Credit: @dreamzzz-dev

namespace A262781Check

-- Euler's product for the totient of a square uses the prime factors of its root.
def weight (k : ℕ) : ℕ :=
  (k ^ 2 / ∏ p ∈ k.primeFactors, p) * ∏ p ∈ k.primeFactors, (p - 1)

theorem weight_eq (k : ℕ) : weight k = Nat.totient (k ^ 2) := by
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.primeFactors_pow_succ k 1]
  rfl

def roots (n : ℕ) : Finset ℕ :=
  (Ico 1 (n + 1)).filter (fun k => weight k ≤ n)

def term (n x y z : ℕ) : ℕ :=
  if (y.Prime ∨ z.Prime) ∧ x ^ 2 + weight y + weight z = n then 1 else 0

def count (n : ℕ) : ℕ :=
  ∑ x ∈ (range (n + 1)).filter (fun x => x ^ 2 ≤ n),
    ∑ y ∈ roots n, ∑ z ∈ roots n, if y ≤ z then term n x y z else 0

theorem count_eq (n : ℕ) : count n = OeisA262781.a n := by
  unfold count OeisA262781.a
  simp only [← weight_eq]
  change _ = ∑ x ∈ range (n + 1), ∑ y ∈ Ico 1 (n + 1),
    ∑ z ∈ Ico y (n + 1), term n x y z
  rw [sum_filter]
  apply sum_congr rfl
  intro x hx
  by_cases hxs : x ^ 2 ≤ n
  · rw [if_pos hxs, roots, sum_filter]
    apply sum_congr rfl
    intro y hy
    have hy1 := (mem_Ico.mp hy).1
    by_cases hys : weight y ≤ n
    · rw [if_pos hys, sum_filter]
      have domain : Ico y (n + 1) =
          (Ico 1 (n + 1)).filter (fun z => y ≤ z) := by
        ext z
        simp only [mem_Ico, mem_filter]
        omega
      rw [domain, sum_filter]
      apply sum_congr rfl
      intro z hz
      by_cases hzs : weight z ≤ n
      · rw [if_pos hzs]
      · have ne : x ^ 2 + weight y + weight z ≠ n := by omega
        simp [hzs, term, ne]
    · have ne (z : ℕ) : x ^ 2 + weight y + weight z ≠ n := by omega
      simp [hys, term, ne]
  · have ne (y z : ℕ) : x ^ 2 + weight y + weight z ≠ n := by omega
    simp [hxs, term, ne]

end A262781Check

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : OMA.R_OeisA262781_conjecture_2_R1.H1 := by
  intro n hn
  rw [← A262781Check.count_eq]
  fin_cases hn <;> decide +kernel
