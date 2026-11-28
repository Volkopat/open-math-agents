import OMAReductions.R_mo_342609_R1

-- Reduction mo-342609.R1.H1.R1 of step mo-342609.R1.H1
-- Credit: @prasledi
-- H1 of mo-342609.R1 asks that no odd square u > 1 satisfies sigma(u) = u + phi(u).
-- Proved here: prime powers (sigma(p^a) < p^a + phi(p^a) for odd p), every u divisible by 15
-- (sigma(u)/u >= (4/3)(6/5) = 24/15 > 23/15 >= 1 + phi(u)/u), and every square divisible by 21
-- (sigma(u)/u >= (13/9)(57/49) = 741/441 > 693/441 >= 1 + phi(u)/u).
-- Left: odd squares prime to 3 (H1) and odd squares divisible by 3 but not by 5 or 7 (H2),
-- in both cases not prime powers.

namespace OMA.R_mo_342609_R1_H1_R1

open ArithmeticFunction Finset

/-- Odd squares prime to 3 that are not prime powers. -/
def H1 : Prop := ∀ u : ℕ, 1 < u → Odd u → IsSquare u → ¬ 3 ∣ u → ¬ IsPrimePow u →
  sigma 1 u ≠ u + u.totient

/-- Odd squares divisible by 3 but by neither 5 nor 7 that are not prime powers. -/
def H2 : Prop := ∀ u : ℕ, Odd u → IsSquare u → 3 ∣ u → ¬ 5 ∣ u → ¬ 7 ∣ u → ¬ IsPrimePow u →
  sigma 1 u ≠ u + u.totient

lemma geom (q : ℕ) : ∀ n : ℕ, (∑ k ∈ range n, (q + 1) ^ k) * q + 1 = (q + 1) ^ n
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ, add_mul, pow_succ, add_right_comm, geom q n]
    ring

lemma sig_ge1 {p : ℕ} (hp : p.Prime) (c : ℕ) : p ^ c * (p + 1) ≤ sigma 1 (p ^ (c + 1)) := by
  rw [sigma_one_apply_prime_pow hp, sum_range_succ, sum_range_succ, pow_succ]
  have := Nat.zero_le (∑ k ∈ range c, p ^ k)
  nlinarith

lemma sig_ge2 {p : ℕ} (hp : p.Prime) (c : ℕ) :
    p ^ c * (p * p + p + 1) ≤ sigma 1 (p ^ (c + 1 + 1)) := by
  rw [sigma_one_apply_prime_pow hp, sum_range_succ, sum_range_succ, sum_range_succ]
  simp only [pow_succ]
  have := Nat.zero_le (∑ k ∈ range c, p ^ k)
  nlinarith

lemma le_sig {w : ℕ} (hw : w ≠ 0) : w ≤ sigma 1 w := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors_self w hw)

lemma split {u p : ℕ} (hp : p.Prime) (hu : u ≠ 0) (hd : p ∣ u) :
    ∃ c w, ¬ p ∣ w ∧ u = p ^ (c + 1) * w := by
  obtain ⟨e, w, hw, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hu p hp.ne_one
  cases e with
  | zero => simp at hd; exact absurd hd hw
  | succ c => exact ⟨c, w, hw, rfl⟩

lemma sq_dvd {u p : ℕ} (hp : p.Prime) (hs : IsSquare u) (hd : p ∣ u) : p * p ∣ u := by
  obtain ⟨k, rfl⟩ := hs
  have hpk : p ∣ k := by
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h <;> exact h
  exact Nat.mul_dvd_mul hpk hpk

lemma sq_split {u p : ℕ} (hp : p.Prime) (hu : u ≠ 0) (hd : p * p ∣ u) :
    ∃ c w, ¬ p ∣ w ∧ u = p ^ (c + 1 + 1) * w := by
  obtain ⟨c, w, hw, rfl⟩ := split hp hu (dvd_trans (dvd_mul_right p p) hd)
  cases c with
  | succ c => exact ⟨c, w, hw, rfl⟩
  | zero =>
    exfalso
    rw [zero_add, pow_one] at hd
    exact hw (Nat.dvd_of_mul_dvd_mul_left hp.pos hd)

lemma pp_case {p : ℕ} (hp : p.Prime) (hodd : Odd p) (c : ℕ) :
    sigma 1 (p ^ (c + 1)) ≠ p ^ (c + 1) + (p ^ (c + 1)).totient := by
  rw [Nat.totient_prime_pow_succ hp, sigma_one_apply_prime_pow hp, sum_range_succ]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hq : 2 ≤ q := by
    have := hp.two_le
    rcases hodd with ⟨t, ht⟩
    omega
  simp only [Nat.add_sub_cancel]
  intro h
  have hS : ∑ k ∈ range (c + 1), (q + 1) ^ k = (q + 1) ^ c * q := by omega
  have g := geom q (c + 1)
  rw [hS, pow_succ] at g
  have hle : q + 1 ≤ q * q := by nlinarith
  have hm := Nat.mul_le_mul_left ((q + 1) ^ c) hle
  have e : (q + 1) ^ c * q * q = (q + 1) ^ c * (q * q) := by ring
  rw [e] at g
  linarith

lemma case15 {u : ℕ} (hu : u ≠ 0) (h3 : 3 ∣ u) (h5 : 5 ∣ u) :
    sigma 1 u ≠ u + u.totient := by
  have p5 : Nat.Prime 5 := by norm_num
  obtain ⟨a, v, hv, rfl⟩ := split Nat.prime_three hu h3
  have hv0 : v ≠ 0 := by rintro rfl; simp at hu
  have h5v : 5 ∣ v := by
    rcases (Nat.Prime.dvd_mul p5).mp h5 with h | h
    · exact absurd (Nat.Prime.dvd_of_dvd_pow p5 h) (by norm_num)
    · exact h
  obtain ⟨b, w, hw, rfl⟩ := split p5 hv0 h5v
  have hw0 : w ≠ 0 := by rintro rfl; simp at hv0
  have c35 : Nat.Coprime (3 ^ (a + 1)) (5 ^ (b + 1) * w) :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hv).pow_left _
  have c5w : Nat.Coprime (5 ^ (b + 1)) w :=
    ((Nat.Prime.coprime_iff_not_dvd p5).mpr hw).pow_left _
  rw [isMultiplicative_sigma.map_mul_of_coprime c35, isMultiplicative_sigma.map_mul_of_coprime c5w,
    Nat.totient_mul c35, Nat.totient_mul c5w, Nat.totient_prime_pow_succ Nat.prime_three,
    Nat.totient_prime_pow_succ p5]
  have s3 := sig_ge1 Nat.prime_three a
  have s5 := sig_ge1 p5 b
  have sw := le_sig hw0
  have tw := Nat.totient_le w
  have lower := Nat.mul_le_mul (Nat.mul_le_mul s3 s5) sw
  have upper := Nat.mul_le_mul_left (3 ^ a * 5 ^ b) tw
  have pos : 0 < 3 ^ a * 5 ^ b * w := by positivity
  generalize sigma 1 (3 ^ (a + 1)) = S3 at lower ⊢
  generalize sigma 1 (5 ^ (b + 1)) = S5 at lower ⊢
  generalize sigma 1 w = Sw at lower ⊢
  rw [pow_succ, pow_succ]
  intro h
  norm_num at lower h
  nlinarith

lemma case21 {u : ℕ} (hu : u ≠ 0) (hs : IsSquare u) (h3 : 3 ∣ u) (h7 : 7 ∣ u) :
    sigma 1 u ≠ u + u.totient := by
  have p7 : Nat.Prime 7 := by norm_num
  have h49 := sq_dvd p7 hs h7
  obtain ⟨a, v, hv, rfl⟩ := sq_split Nat.prime_three hu (sq_dvd Nat.prime_three hs h3)
  have hv0 : v ≠ 0 := by rintro rfl; simp at hu
  have h49v : 7 * 7 ∣ v := by
    have hc : Nat.Coprime (7 * 7) (3 ^ (a + 1 + 1)) := by
      apply Nat.Coprime.pow_right
      norm_num
    exact hc.dvd_of_dvd_mul_left h49
  obtain ⟨b, w, hw, rfl⟩ := sq_split p7 hv0 h49v
  have hw0 : w ≠ 0 := by rintro rfl; simp at hv0
  have c37 : Nat.Coprime (3 ^ (a + 1 + 1)) (7 ^ (b + 1 + 1) * w) :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hv).pow_left _
  have c7w : Nat.Coprime (7 ^ (b + 1 + 1)) w :=
    ((Nat.Prime.coprime_iff_not_dvd p7).mpr hw).pow_left _
  rw [isMultiplicative_sigma.map_mul_of_coprime c37, isMultiplicative_sigma.map_mul_of_coprime c7w,
    Nat.totient_mul c37, Nat.totient_mul c7w, Nat.totient_prime_pow_succ Nat.prime_three,
    Nat.totient_prime_pow_succ p7]
  have s3 := sig_ge2 Nat.prime_three a
  have s7 := sig_ge2 p7 b
  have sw := le_sig hw0
  have tw := Nat.totient_le w
  have lower := Nat.mul_le_mul (Nat.mul_le_mul s3 s7) sw
  have upper := Nat.mul_le_mul_left (3 ^ a * 7 ^ b) tw
  have pos : 0 < 3 ^ a * 7 ^ b * w := by positivity
  generalize sigma 1 (3 ^ (a + 1 + 1)) = S3 at lower ⊢
  generalize sigma 1 (7 ^ (b + 1 + 1)) = S7 at lower ⊢
  generalize sigma 1 w = Sw at lower ⊢
  simp only [pow_succ]
  intro h
  norm_num at lower h
  nlinarith

theorem main : H1 → H2 → OMA.R_mo_342609_R1.H1 := by
  intro h1 h2 u hu1 hodd hsq
  have hu0 : u ≠ 0 := by omega
  by_cases hpp : IsPrimePow u
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff u).mp hpp
    obtain ⟨c, rfl⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
    have hpo : Odd p := (Nat.odd_pow_iff (Nat.succ_ne_zero c)).mp hodd
    exact pp_case hp hpo c
  by_cases h3 : 3 ∣ u
  · by_cases h5 : 5 ∣ u
    · exact case15 hu0 h3 h5
    by_cases h7 : 7 ∣ u
    · exact case21 hu0 hsq h3 h7
    exact h2 u hodd hsq h3 h5 h7 hpp
  · exact h1 u hu1 hodd hsq h3 hpp

end OMA.R_mo_342609_R1_H1_R1
