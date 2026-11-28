import OMAStatements.S_oeis_a084091
import Mathlib

namespace OMA.Helpers

open PowerSeries

/-- The nontrivial character modulo 3, as a rational number. -/
def chi3 (d : ℕ) : ℚ := if d % 3 = 1 then 1 else if d % 3 = 2 then -1 else 0

theorem chi3_rec (m : ℕ) : chi3 (m + 2) + chi3 (m + 1) + chi3 m = 0 := by
  unfold chi3
  have h := Nat.mod_lt m (show 0 < 3 by norm_num)
  interval_cases hm : m % 3 <;> simp [Nat.add_mod, hm]

theorem mk_chi3_mul : mk chi3 * (1 + X + X ^ 2 : ℚ⟦X⟧) = X := by
  ext m
  rw [mul_add, mul_add, mul_one, map_add, map_add, coeff_mul_X_pow', coeff_X]
  rcases m with _ | _ | m
  · simp [chi3]
  · simp [chi3]
  · rw [show m + 2 = (m + 1) + 1 by ring, coeff_succ_mul_X]
    simp only [coeff_mk, show 2 ≤ m + 1 + 1 by omega, if_true, show m + 1 + 1 - 2 = m by omega,
      show m + 1 + 1 ≠ 1 by omega, if_false]
    exact chi3_rec m

theorem coeff_gen (m : ℕ) : coeff m (X * (1 + X + X ^ 2 : ℚ⟦X⟧)⁻¹) = chi3 m := by
  have hc : constantCoeff (1 + X + X ^ 2 : ℚ⟦X⟧) ≠ 0 := by simp
  have e : X * (1 + X + X ^ 2 : ℚ⟦X⟧)⁻¹ = mk chi3 :=
    calc X * (1 + X + X ^ 2 : ℚ⟦X⟧)⁻¹ = mk chi3 * (1 + X + X ^ 2) * (1 + X + X ^ 2 : ℚ⟦X⟧)⁻¹ := by
          rw [mk_chi3_mul]
      _ = mk chi3 := by rw [mul_assoc, PowerSeries.mul_inv_cancel _ hc, mul_one]
  rw [e, coeff_mk]

theorem pow_two_of_primeFactors {m : ℕ} (h0 : m ≠ 0) (h : m.primeFactors ⊆ {2}) :
    ∃ k, m = 2 ^ k := by
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd m with h1 | ⟨p, hp, hpd, hodd⟩
  · exact h1
  · exfalso
    have : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, h0⟩
    have h2 := h this
    rw [Finset.mem_singleton] at h2
    subst h2
    exact (Nat.not_even_iff_odd.mpr hodd) even_two

theorem primeFactors_two_pow (k : ℕ) : (2 ^ k).primeFactors ⊆ {2} := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  rw [Finset.mem_singleton]
  exact (Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_two).mp (hp.1.dvd_of_dvd_pow hp.2.1)

end OMA.Helpers

open OMA.Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a084091.main := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  simp only [coeff_gen]
  change (∑ k ∈ Finset.range (n + 1), if 2 ^ k ∣ n then chi3 (n / 2 ^ k) else 0) =
    ∑ d ∈ n.divisors, if (n / d).primeFactors ⊆ {2} then chi3 d else 0
  rw [← Finset.sum_filter (fun k => 2 ^ k ∣ n) (fun k => chi3 (n / 2 ^ k)),
    ← Finset.sum_filter (fun d => (n / d).primeFactors ⊆ {2}) chi3]
  -- the quotient `n / d` of a divisor `d` with only the prime factor `2`
  have key : ∀ d ∈ n.divisors.filter (fun d => (n / d).primeFactors ⊆ {2}),
      d ∣ n ∧ n / d = 2 ^ Nat.log 2 (n / d) := by
    intro d hd
    obtain ⟨hdn, hpf⟩ := Finset.mem_filter.mp hd
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hdn).1
    have hm0 : n / d ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (Nat.pos_of_dvd_of_pos hdvd (by omega))).ne'
    obtain ⟨k, hk⟩ := pow_two_of_primeFactors hm0 hpf
    exact ⟨hdvd, by rw [hk, Nat.log_pow (by norm_num)]⟩
  refine Finset.sum_nbij' (fun k => n / 2 ^ k) (fun d => Nat.log 2 (n / d)) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    obtain ⟨-, hkd⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hkd, hn0⟩, ?_⟩
    rw [Nat.div_div_self hkd hn0]
    exact primeFactors_two_pow k
  · intro d hd
    obtain ⟨hdvd, he⟩ := key d hd
    have h2dvd : 2 ^ Nat.log 2 (n / d) ∣ n := he ▸ Nat.div_dvd_of_dvd hdvd
    have h1 : 2 ^ Nat.log 2 (n / d) ≤ n := Nat.le_of_dvd (by omega) h2dvd
    have h2 : Nat.log 2 (n / d) < 2 ^ Nat.log 2 (n / d) := Nat.lt_two_pow_self
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h2dvd⟩
  · intro k hk
    obtain ⟨-, hkd⟩ := Finset.mem_filter.mp hk
    show Nat.log 2 (n / (n / 2 ^ k)) = k
    rw [Nat.div_div_self hkd hn0, Nat.log_pow (by norm_num)]
  · intro d hd
    obtain ⟨hdvd, he⟩ := key d hd
    show n / 2 ^ Nat.log 2 (n / d) = d
    rw [← he, Nat.div_div_self hdvd hn0]
  · intro k _
    rfl
