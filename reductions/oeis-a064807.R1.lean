import OMAStatements.S_oeis_a064807
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open OMA.S_oeis_a064807

namespace OMA.R_oeis_a064807_R1

/-- An odd multiperfect number cannot have an even digital root. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → n ∣ ArithmeticFunction.sigma 1 n → Odd n →
    n % 9 = 2 ∨ n % 9 = 4 ∨ n % 9 = 6 ∨ n % 9 = 8 → False

/-- For even multiperfect numbers beyond the perfect case, roots 4 and 8
reduce to the corresponding power of two. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → n ∣ ArithmeticFunction.sigma 1 n → Even n →
    ArithmeticFunction.sigma 1 n ≠ 2 * n →
    (n % 9 = 4 → 4 ∣ n) ∧ (n % 9 = 8 → 8 ∣ n)

/-- The remaining odd prime digital roots are 5 and 7. -/
def H3 : Prop :=
  ∀ n : ℕ, 0 < n → n ∣ ArithmeticFunction.sigma 1 n →
    (Odd n ∨ ArithmeticFunction.sigma 1 n ≠ 2 * n) →
    (n % 9 = 5 → 5 ∣ n) ∧ (n % 9 = 7 → 7 ∣ n)

theorem digital_root_residue (n : ℕ) (hn : 0 < n) :
    digitalRoot n = if n % 9 = 0 then 9 else n % 9 := by
  unfold digitalRoot
  split <;> omega

theorem geometric_two_sum (k : ℕ) : (∑ i ∈ Finset.range (k + 1), (2 : ℕ) ^ i) = 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have hpow : 0 < (2 : ℕ) ^ (k + 1) := pow_pos (by decide) _
      omega

/-- Three distinct divisors already contribute at least their sum. -/
theorem sigma_ge_three_divisors (n v : ℕ) (hn : 0 < n) (hv : 1 < v)
    (hvn : v < n) (hdvd : v ∣ n) :
    1 + v + n ≤ ArithmeticFunction.sigma 1 n := by
  have hsubset : ({1, v, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨one_dvd _, hn.ne'⟩
    · exact Nat.mem_divisors.mpr ⟨hdvd, hn.ne'⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_refl _, hn.ne'⟩
  have hvn' : v ≠ n := hvn.ne
  have honev : 1 ≠ v := hv.ne
  have honen : 1 ≠ n := (hv.trans hvn).ne
  have hsum : (∑ x ∈ ({1, v, n} : Finset ℕ), x) ≤ ∑ x ∈ n.divisors, x :=
    Finset.sum_le_sum_of_subset hsubset
  rw [ArithmeticFunction.sigma_one_apply]
  simpa [Finset.sum_insert, honev, honen, hvn', add_assoc] using hsum

/-- The even perfect factorization obtained by comparing the divisor sums. -/
theorem even_perfect_shape (n : ℕ) (hn : 0 < n) (heven : Even n)
    (hσ : ArithmeticFunction.sigma 1 n = 2 * n) :
    ∃ k : ℕ, 0 < k ∧ (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) := by
  obtain ⟨k, b, hbOdd, hnEq⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  have hk : 0 < k := by
    by_contra! hk'
    have hzero : k = 0 := by omega
    rw [hzero, pow_zero, one_mul] at hnEq
    exact (Nat.not_even_iff_odd.mpr hbOdd) (hnEq ▸ heven)
  have hb : 0 < b := by
    by_contra! hb'
    have hzero : b = 0 := by omega
    rw [hzero, mul_zero] at hnEq
    omega
  let M := mersenne (k + 1)
  have hM : 1 < M := one_lt_mersenne.mpr (by omega)
  have hMpos : 0 < M := by omega
  have h2b : Nat.Coprime 2 b := Nat.prime_two.coprime_iff_not_dvd.mpr
    hbOdd.not_two_dvd_nat
  have hσn : ArithmeticFunction.sigma 1 n = M * ArithmeticFunction.sigma 1 b := by
    rw [hnEq, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (h2b.pow_left k),
      ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two, geometric_two_sum]
    rfl
  have hmajor : M * ArithmeticFunction.sigma 1 b = (M + 1) * b := by
    rw [← hσn, hσ, hnEq, show M + 1 = 2 ^ (k + 1) from succ_mersenne (k + 1), pow_succ]
    ring
  have hdivSum : M ∣ M * b + b := by
    have hdiv : M ∣ (M + 1) * b := hmajor ▸ dvd_mul_right M _
    simpa [Nat.add_mul] using hdiv
  have hdiv : M ∣ b := (Nat.dvd_add_iff_right (dvd_mul_right M b)).mpr hdivSum
  obtain ⟨v, hv⟩ := hdiv
  have hvpos : 0 < v := by
    by_contra! hv'
    have hzero : v = 0 := by omega
    rw [hzero, mul_zero] at hv
    omega
  have hvb : v < b := by
    rw [hv]
    simpa using Nat.mul_lt_mul_of_pos_right hM hvpos
  have hσb : ArithmeticFunction.sigma 1 b = b + v := by
    apply Nat.eq_of_mul_eq_mul_left hMpos
    calc
      _ = (M + 1) * b := hmajor
      _ = _ := by rw [hv]; ring
  have hvone : v = 1 := by
    by_contra hne
    have hgt : 1 < v := by omega
    have hdvd : v ∣ b := hv ▸ dvd_mul_left v M
    have hbound := sigma_ge_three_divisors b v hb hgt hvb hdvd
    omega
  have hbM : b = M := by simpa [hvone] using hv
  have hσone : ArithmeticFunction.sigma 1 b = b + 1 := by simpa [hvone] using hσb
  have hbPrime : b.Prime := by
    apply Nat.prime_def_lt'.mpr
    refine ⟨by omega, ?_⟩
    intro u hu hub hdu
    have hbound := sigma_ge_three_divisors b u hb (by omega) hub hdu
    omega
  refine ⟨k, hk, ?_, by simpa [hbM] using hnEq⟩
  change M.Prime
  exact hbM ▸ hbPrime

theorem four_power_mod_nine (l : ℕ) : (4 ^ l : ℕ) % 9 = 1 ∨
    (4 ^ l : ℕ) % 9 = 4 ∨ (4 ^ l : ℕ) % 9 = 7 := by
  induction l with
  | zero => decide
  | succ l ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h | h <;> rw [h] <;> decide

theorem even_perfect_digital_root (n : ℕ) (hn : 0 < n) (heven : Even n)
    (hs : ArithmeticFunction.sigma 1 n = 2 * n) : digitalRoot n ∣ n := by
  obtain ⟨k, hk, hp, hnEq⟩ := even_perfect_shape n hn heven hs
  rcases hp.of_mersenne.eq_two_or_odd' with htwo | hodd
  · have hk1 : k = 1 := by omega
    rw [hnEq, hk1]
    decide
  obtain ⟨l, hl⟩ := hodd
  have hkEq : k = 2 * l := by omega
  have hfour : (2 : ℕ) ^ k = 4 ^ l := by rw [hkEq, pow_mul]; norm_num
  have hpow : 0 < (2 : ℕ) ^ k := pow_pos (by decide) _
  have hm : mersenne (k + 1) = 2 * 2 ^ k - 1 := by
    rw [mersenne, pow_succ, mul_comm]
  have hmod : n % 9 = 1 := by
    have hcases := four_power_mod_nine l
    rw [← hfour] at hcases
    rw [hnEq, Nat.mul_mod]
    rcases hcases with h | h | h
    · have hm9 : mersenne (k + 1) % 9 = 1 := by rw [hm]; omega
      rw [h, hm9]
    · have hm9 : mersenne (k + 1) % 9 = 7 := by rw [hm]; omega
      rw [h, hm9]
    · have hm9 : mersenne (k + 1) % 9 = 4 := by rw [hm]; omega
      rw [h, hm9]
  rw [digital_root_residue n hn, hmod]
  exact one_dvd _

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a064807.main := by
  intro hOdd hTwo hPrimes n hn hmul
  by_cases hEven : Even n
  · by_cases hPerfect : ArithmeticFunction.sigma 1 n = 2 * n
    · exact even_perfect_digital_root n hn hEven hPerfect
    have h2 := even_iff_two_dvd.mp hEven
    have hz := Nat.dvd_iff_mod_eq_zero.mp h2
    obtain ⟨h4, h8⟩ := hTwo n hn hmul hEven hPerfect
    obtain ⟨h5, h7⟩ := hPrimes n hn hmul (Or.inr hPerfect)
    have hbound := Nat.mod_lt n (by decide : 0 < 9)
    rw [digital_root_residue n hn]
    interval_cases h : n % 9
    · exact Nat.dvd_iff_mod_eq_zero.mpr h
    · exact one_dvd _
    · exact h2
    · change 3 ∣ n
      exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    · exact h4 rfl
    · exact h5 rfl
    · change 6 ∣ n
      exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    · exact h7 rfl
    · exact h8 rfl
  have hodd := Nat.not_even_iff_odd.mp hEven
  obtain ⟨h5, h7⟩ := hPrimes n hn hmul (Or.inl hodd)
  have hbound := Nat.mod_lt n (by decide : 0 < 9)
  rw [digital_root_residue n hn]
  interval_cases h : n % 9
  · exact Nat.dvd_iff_mod_eq_zero.mpr h
  · exact one_dvd _
  · exact (hOdd n hn hmul hodd (Or.inl h)).elim
  · change 3 ∣ n
    exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  · exact (hOdd n hn hmul hodd (Or.inr (Or.inl h))).elim
  · exact h5 rfl
  · exact (hOdd n hn hmul hodd (Or.inr (Or.inr (Or.inl h)))).elim
  · exact h7 rfl
  · exact (hOdd n hn hmul hodd (Or.inr (Or.inr (Or.inr h)))).elim

end OMA.R_oeis_a064807_R1
