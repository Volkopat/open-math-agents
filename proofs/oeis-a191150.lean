import OMAStatements.S_oeis_a191150
import Mathlib

open OMA.S_oeis_a191150

theorem OMA.solution : type_of% @OMA.S_oeis_a191150.main := by
  intro a g H ⟨ha1, ha⟩ hg ⟨hH1, hH⟩
  have hg1 : g 1 = 1 := by
    rw [hg 1 le_rfl]
    simp
  have key : ∀ n : ℕ, 2 ≤ n → a n - g n + H n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have h1 : (1 : ℕ) ∈ n.properDivisors := by
        rw [Nat.mem_properDivisors]; exact ⟨one_dvd n, by omega⟩
      have hsum : ∑ d ∈ n.properDivisors, (a d - g d + H d) = 1 := by
        rw [← Finset.add_sum_erase _ _ h1, ha1, hg1, hH1]
        rw [Finset.sum_eq_zero]
        · ring
        · intro d hd
          have hd' := Finset.mem_of_mem_erase hd
          have hne := Finset.ne_of_mem_erase hd
          rw [Nat.mem_properDivisors] at hd'
          have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd'.1 (by omega)
          exact ih d hd'.2 (by omega)
      have hsig : (ArithmeticFunction.sigma 1 n : ℤ) = ∑ d ∈ n.properDivisors, (d : ℤ) + n := by
        rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
        push_cast; ring
      rw [ha n hn, hg n (by omega), hH n hn, hsig]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum ⊢
      linarith
  intro n hn
  linarith [key n hn]
