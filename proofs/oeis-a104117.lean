import OMAStatements.S_oeis_a104117

open ArithmeticFunction OMA.S_oeis_a104117

namespace OMA.P_oeis_a104117

lemma log2_pow (i : ℕ) : (2 ^ i).log2 = i := by
  first
  | exact Nat.log2_two_pow
  | (rw [Nat.log2_eq_log_two]; exact Nat.log_pow (by norm_num) i)
  | (have h0 : (2 ^ i) ≠ 0 := by positivity
     have hp : 0 < 2 ^ i := by positivity
     apply le_antisymm
     · have h1 : 2 ^ i < 2 ^ (i + 1) := by rw [pow_succ]; omega
       have := (Nat.log2_lt h0).2 h1
       omega
     · exact (Nat.le_log2 h0).2 le_rfl)

lemma pi_apply (n : ℕ) : powerIndicator n = if n = 2 ^ n.log2 then 1 else 0 := rfl

lemma pi_two_pow (i : ℕ) : powerIndicator (2 ^ i) = 1 := by
  rw [pi_apply, log2_pow]
  simp

lemma key (n : ℕ) :
    (∑ k ∈ n.divisors, coefficient (n / k)) = (powerIndicator * powerIndicator) n := by
  have h1 : (∑ k ∈ n.divisors, coefficient (n / k)) = ∑ k ∈ n.divisors, coefficient k :=
    Nat.sum_div_divisors n (fun k => coefficient k)
  have h2 : (coefficient * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n =
      ∑ k ∈ n.divisors, coefficient k :=
    ArithmeticFunction.coe_mul_zeta_apply
  have h3 : coefficient * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) =
      powerIndicator * powerIndicator := by
    rw [show coefficient = moebius * powerIndicator * powerIndicator from rfl]
    calc moebius * powerIndicator * powerIndicator * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)
        = (moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) *
            (powerIndicator * powerIndicator) := by ring
      _ = powerIndicator * powerIndicator := by
        rw [ArithmeticFunction.moebius_mul_coe_zeta, one_mul]
  rw [h1, ← h2, h3]

lemma pp_apply (n : ℕ) :
    (powerIndicator * powerIndicator) n = if n = 2 ^ n.log2 then (n.log2 : ℤ) + 1 else 0 := by
  rw [ArithmeticFunction.mul_apply]
  split_ifs with h
  · obtain ⟨m, hm⟩ : ∃ m, n = 2 ^ m := ⟨_, h⟩
    subst hm
    rw [log2_pow]
    rw [Nat.sum_divisorsAntidiagonal (fun a b => powerIndicator a * powerIndicator b),
      Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map]
    have hterm : ∀ x ∈ Finset.range (m + 1),
        powerIndicator (2 ^ x) * powerIndicator (2 ^ m / 2 ^ x) = 1 := by
      intro x hx
      have hxm : x ≤ m := by
        have := Finset.mem_range.mp hx
        omega
      rw [Nat.pow_div hxm (by norm_num), pi_two_pow, pi_two_pow, mul_one]
    simp only [Function.Embedding.coeFn_mk]
    rw [Finset.sum_congr rfl hterm]
    simp
  · apply Finset.sum_eq_zero
    intro x hx
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    by_cases h1 : x.1 = 2 ^ x.1.log2
    · by_cases h2 : x.2 = 2 ^ x.2.log2
      · exfalso
        apply h
        have e : n = 2 ^ (x.1.log2 + x.2.log2) := by
          rw [← hx'.1, pow_add, ← h1, ← h2]
        rw [e, log2_pow]
      · simp [pi_apply, h2]
    · simp [pi_apply, h1]

end OMA.P_oeis_a104117

theorem OMA.solution : type_of% @OMA.S_oeis_a104117.main := by
  intro n _
  rw [OMA.P_oeis_a104117.key n]
  exact OMA.P_oeis_a104117.pp_apply n
