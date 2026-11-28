import OMAStatements.S_oeis_a224832

-- Counterexample: M = 2^15·3^5·5^2·7^2·11·13·17·19·31·43·257 is 6-perfect (σ M = 6M).
-- The even divisors of 2M are 2d with d ∣ M, so recipEven (2M) = σ(M)/(2M) = 3, an integer ≠ 2,
-- and M is not perfect, so 2M is not twice an even perfect number.

namespace OMA.A224832
open OMA.S_oeis_a224832 ArithmeticFunction

lemma recip_sum (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, (1 : ℚ) / d = (sigma 1 n : ℚ) / n := by
  rw [sigma_eq_sum_div, eq_div_iff (by positivity), Finset.sum_mul]
  push_cast
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (d : ℚ) ≠ 0 := by
    have := Nat.pos_of_mem_divisors hd; positivity
  rw [pow_one, Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0]
  field_simp

lemma even_filter (m : ℕ) (hm : 0 < m) :
    (2 * m).divisors.filter Even = m.divisors.map ⟨(2 * ·), fun a b h => by simpa using h⟩ := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_map]
  constructor
  · rintro ⟨⟨hd, _⟩, e, rfl⟩
    refine ⟨e, ⟨?_, hm.ne'⟩, by show 2 * e = e + e; ring⟩
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) (by rw [two_mul]; exact hd)
  · rintro ⟨e, ⟨he, _⟩, rfl⟩
    exact ⟨⟨Nat.mul_dvd_mul_left 2 he, by omega⟩, e, by show 2 * e = e + e; ring⟩

lemma recipEven_two_mul (m : ℕ) (hm : 0 < m) :
    recipEven (2 * m) = (sigma 1 m : ℚ) / m / 2 := by
  rw [recipEven, even_filter m hm, Finset.sum_map, ← recip_sum m hm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  show (1 : ℚ) / ((2 * d : ℕ) : ℚ) = 1 / d / 2
  push_cast
  field_simp

lemma hmul (a b : ℕ) (h : Nat.Coprime a b) : sigma 1 (a * b) = sigma 1 a * sigma 1 b :=
  isMultiplicative_sigma.map_mul_of_coprime h

lemma hp1 (p : ℕ) (hp : p.Prime) : sigma 1 p = p + 1 := by
  rw [sigma_one_apply, Nat.Prime.sum_divisors hp]

lemma hpk (p k : ℕ) (hp : p.Prime) : sigma 1 (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i :=
  sigma_one_apply_prime_pow hp

def M : ℕ := 2^15 * 3^5 * 5^2 * 7^2 * 11 * 13 * 17 * 19 * 31 * 43 * 257

lemma sigmaM : sigma 1 M = 6 * M := by
  rw [M, hmul _ _ (by norm_num), hmul _ _ (by norm_num), hmul _ _ (by norm_num),
    hmul _ _ (by norm_num), hmul _ _ (by norm_num), hmul _ _ (by norm_num),
    hmul _ _ (by norm_num), hmul _ _ (by norm_num), hmul _ _ (by norm_num),
    hmul _ _ (by norm_num), hpk 2 15 (by norm_num), hpk 3 5 (by norm_num),
    hpk 5 2 (by norm_num), hpk 7 2 (by norm_num), hp1 11 (by norm_num), hp1 13 (by norm_num),
    hp1 17 (by norm_num), hp1 19 (by norm_num), hp1 31 (by norm_num), hp1 43 (by norm_num),
    hp1 257 (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

end OMA.A224832

open OMA.A224832 OMA.S_oeis_a224832 ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a224832.main := by
  intro hC
  have hM : 0 < M := by norm_num [M]
  have h3 : recipEven (2 * M) = 3 := by
    rw [recipEven_two_mul M hM, sigmaM]; push_cast; field_simp; ring
  have hnot : ¬ TwiceEvenPerfect (2 * M) := by
    rintro ⟨P, _, hP, hk⟩
    have : P = M := by omega
    subst this
    rw [Nat.perfect_iff_sum_divisors_eq_two_mul hM, ← sigma_one_apply, sigmaM] at hP
    omega
  have := hC (2 * M) ⟨by omega, even_two_mul M, 3, by rw [h3]; norm_num⟩ hnot
  rw [h3] at this
  norm_num at this

