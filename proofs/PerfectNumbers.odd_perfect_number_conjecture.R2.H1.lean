import OMAReductions.R_PerfectNumbers_odd_perfect_number_conjecture_R2

-- Step PerfectNumbers.odd_perfect_number_conjecture.R2.H1: hypothesis H1 of reduction PerfectNumbers.odd_perfect_number_conjecture.R2
-- Credit: @swaymun
-- H1 := ∀ n : ℕ, Nat.Perfect n → Odd n → ¬ 105 ∣ n

open Finset

/-- The abundancy `σ(n) / n` does not decrease along divisibility, written without division. -/
lemma abundancy_mono (m n : ℕ) (hmn : m ∣ n) (hn : 0 < n) :
    n * ∑ d ∈ m.divisors, d ≤ m * ∑ d ∈ n.divisors, d := by
  calc n * ∑ d ∈ m.divisors, d = n * ∑ d ∈ m.divisors, m / d := by
        rw [Nat.sum_div_divisors m (fun x => x)]
    _ = ∑ d ∈ m.divisors, n * (m / d) := Finset.mul_sum _ _ _
    _ = ∑ d ∈ m.divisors, m * (n / d) := by
        refine Finset.sum_congr rfl fun d hd => ?_
        have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
        have hdn : d ∣ n := hdm.trans hmn
        rw [← Nat.mul_div_assoc _ hdm, ← Nat.mul_div_assoc _ hdn, Nat.mul_comm]
    _ ≤ ∑ d ∈ n.divisors, m * (n / d) :=
        Finset.sum_le_sum_of_subset (Nat.divisors_subset_of_dvd hn.ne' hmn)
    _ = m * ∑ d ∈ n.divisors, n / d := (Finset.mul_sum _ _ _).symm
    _ = m * ∑ d ∈ n.divisors, d := by rw [Nat.sum_div_divisors n (fun x => x)]

/-- In an odd perfect number, a prime `p ≡ 3 (mod 4)` that divides it divides it twice. -/
lemma sq_dvd_of_odd_perfect (n p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3) (hn : Nat.Perfect n)
    (hodd : Odd n) (hpn : p ∣ n) : p ^ 2 ∣ n := by
  by_contra h
  have h2n : ∑ d ∈ n.divisors, d = 2 * n := (Nat.perfect_iff_sum_divisors_eq_two_mul hn.2).1 hn
  obtain ⟨m, rfl⟩ := hpn
  have hpm : ¬ p ∣ m := fun hd => h (by obtain ⟨k, rfl⟩ := hd; exact ⟨k, by ring⟩)
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
  have hS := Nat.Coprime.sum_divisors_mul hcop
  have hSp : ∑ d ∈ p.divisors, d = p + 1 := by
    rw [Nat.Prime.divisors hp, Finset.sum_pair hp.one_lt.ne]
    ring
  have h4 : 4 ∣ p + 1 := by omega
  have h4' : 4 ∣ 2 * (p * m) := by
    rw [← h2n, hS, hSp]
    exact Dvd.dvd.mul_right h4 _
  have h2 : 2 ∣ p * m := by omega
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

theorem OMA.solution : OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R2.H1 := by
  unfold OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R2.H1
  intro n hn hodd h105
  have h3 : 3 ∣ n := Dvd.dvd.trans (by norm_num) h105
  have h5 : 5 ∣ n := Dvd.dvd.trans (by norm_num) h105
  have h7 : 7 ∣ n := Dvd.dvd.trans (by norm_num) h105
  have h9 : 3 ^ 2 ∣ n := sq_dvd_of_odd_perfect n 3 (by norm_num) (by norm_num) hn hodd h3
  have h49 : 7 ^ 2 ∣ n := sq_dvd_of_odd_perfect n 7 (by norm_num) (by norm_num) hn hodd h7
  have h441 : 3 ^ 2 * 7 ^ 2 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h9 h49
  have h2205 : 3 ^ 2 * 7 ^ 2 * 5 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h441 h5
  have key := abundancy_mono (3 ^ 2 * 7 ^ 2 * 5) n h2205 hn.2
  have h2n : ∑ d ∈ n.divisors, d = 2 * n := (Nat.perfect_iff_sum_divisors_eq_two_mul hn.2).1 hn
  have hS : ∑ d ∈ (3 ^ 2 * 7 ^ 2 * 5 : ℕ).divisors, d = 4446 := by
    rw [Nat.Coprime.sum_divisors_mul (by norm_num : Nat.Coprime (3 ^ 2 * 7 ^ 2) 5),
      Nat.Coprime.sum_divisors_mul (by norm_num : Nat.Coprime (3 ^ 2) (7 ^ 2))]
    decide
  rw [h2n, hS] at key
  have hpos := hn.2
  omega
