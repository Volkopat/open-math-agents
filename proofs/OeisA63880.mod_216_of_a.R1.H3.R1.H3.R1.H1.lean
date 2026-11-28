import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H3_R1_H3_R1

-- Step OeisA63880.mod_216_of_a.R1.H3.R1.H3.R1.H1: hypothesis H1 of reduction OeisA63880.mod_216_of_a.R1.H3.R1.H3.R1
-- Credit: @luciusacarr
-- H1 := ∀ t : ℕ, Odd t → ¬ 3 ∣ t → Squarefree t → ¬ IsPrimePow t →   91 * σ 1 t ≠ 100 * usigma t

/-! For squarefree `t` every divisor `d` is unitary (`d * (t / d) = t` squarefree forces
`gcd(d, t / d) = 1`), so `usigma t = σ 1 t ≥ t > 0`, and `91 x = 100 x` forces `x = 0`. -/

open OeisA63880
open scoped ArithmeticFunction.sigma

theorem OMA.solution : OMA.R_OeisA63880_mod_216_of_a_R1_H3_R1_H3_R1.H1 := by
  intro t ht _ hsq _
  have ht0 : t ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero ht)
  have hu : usigma t = σ 1 t := by
    rw [usigma, ArithmeticFunction.sigma_one_apply, unitaryDivisors]
    congr 1
    apply Finset.filter_true_of_mem
    intro d hd
    have hdt : d ∣ t := Nat.dvd_of_mem_divisors hd
    have hmul : d * (t / d) = t := Nat.mul_div_cancel' hdt
    rw [← hmul] at hsq
    exact (Nat.squarefree_mul_iff.mp hsq).1
  have hpos : 0 < σ 1 t := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨t, Nat.mem_divisors_self t ht0, Nat.pos_of_ne_zero ht0⟩
  rw [hu]
  omega
