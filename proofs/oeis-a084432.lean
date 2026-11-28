import OMAStatements.S_oeis_a084432
import Mathlib

/-!
# A084432: a(n) counts the solutions of 2^x * (y + z) = n with 0 ≤ x, y, z ≤ n

Write h(t) = t^2 (3 - t) / (1 + t) / (1 - t)^2. Then:
* h = mk c with c(0) = 0 and c(m) = m + 1 - 2 [m odd] for m ≥ 1: the power series mk c times
  (1 + t)(1 - t)^2 = 1 - t - t^2 + t^3 is t^2 (3 - t), compared coefficient by coefficient.
* `term k` is h expanded by 2^k (`PowerSeries.expand`, an algebra map that also commutes with
  inverses of power series with nonzero constant coefficient), so its coefficient of x^n is
  c(n / 2^k) when 2^k divides n and 0 otherwise. Hence the finsum is a finite sum over k ≤ n.
* The coefficient of 2/(1-x) is always 2, so a(n) = 2 + sum over k ≤ n with 2^k | n of c(n/2^k).
* The number of solutions is the sum over x ≤ n with 2^x | n of n/2^x + 1 (for fixed x the pairs
  (y, z) form the antidiagonal of n / 2^x).
* The two sums differ by 2 [n/2^k odd] in the k-th place, and n / 2^k is odd for exactly one k
  with 2^k | n, namely the 2-adic valuation of n. So the difference is 2 = the constant 2.
-/

namespace OMA.P084432

open OMA.S_oeis_a084432 PowerSeries

/-- The coefficients of h(t) = t^2(3-t)/(1+t)/(1-t)^2. -/
noncomputable def c (m : ℕ) : ℚ := if m = 0 then 0 else (m : ℚ) + 1 - (if m % 2 = 1 then 2 else 0)

/-- h(t) = t^2(3-t)/(1+t)/(1-t)^2. -/
noncomputable def h : PowerSeries ℚ := X ^ 2 * (3 - X) * (1 + X)⁻¹ * ((1 - X) ^ 2)⁻¹

lemma mk_c_mul : mk c * ((1 + X) * (1 - X) ^ 2) = (X ^ 2 * (3 - X) : PowerSeries ℚ) := by
  have e : mk c * ((1 + X) * (1 - X) ^ 2) =
      mk c - mk c * X ^ 1 - mk c * X ^ 2 + mk c * X ^ 3 := by ring
  have e2 : (X ^ 2 * (3 - X) : PowerSeries ℚ) = C (3 : ℚ) * X ^ 2 - X ^ 3 := by
    rw [map_ofNat]
    ring
  rw [e, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  rcases n with _ | _ | _ | _ | n
  · norm_num [c]
  · norm_num [c]
  · norm_num [c]
  · norm_num [c]
  · simp [c]
    split_ifs <;> first | (exfalso; omega) | ring

lemma h_eq : h = mk c := by
  have hB : constantCoeff ((1 + X) * (1 - X) ^ 2 : PowerSeries ℚ) ≠ 0 := by simp
  have hc : mk c = X ^ 2 * (3 - X) * ((1 + X) * (1 - X) ^ 2 : PowerSeries ℚ)⁻¹ := by
    rw [← mk_c_mul, mul_assoc, PowerSeries.mul_inv_cancel _ hB, mul_one]
  rw [hc, PowerSeries.mul_inv_rev, h]
  ring

/-- Expansion commutes with the inverse of a power series with nonzero constant coefficient. -/
lemma expand_inv (p : ℕ) (hp : p ≠ 0) (φ : PowerSeries ℚ) (h0 : constantCoeff φ ≠ 0) :
    expand p hp φ⁻¹ = (expand p hp φ)⁻¹ := by
  symm
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by rwa [constantCoeff_expand])]
  rw [← map_mul, PowerSeries.inv_mul_cancel _ h0, map_one]

/-- The k-th summand is h(x^(2^k)). -/
lemma term_eq (k : ℕ) : term k = expand (2 ^ k) (pow_ne_zero k two_ne_zero) h := by
  unfold term h
  rw [map_mul, map_mul, map_mul, expand_inv _ _ _ (by simp), expand_inv _ _ _ (by simp)]
  simp only [map_pow, map_sub, map_add, map_one, expand_X, map_ofNat]

lemma coeff_term (k n : ℕ) : coeff n (term k) = if 2 ^ k ∣ n then c (n / 2 ^ k) else 0 := by
  rw [term_eq, coeff_expand, h_eq]
  simp only [coeff_mk]

lemma coeff_first (n : ℕ) : coeff n (2 * (1 - X)⁻¹ : PowerSeries ℚ) = 2 := by
  have e : ((1 : PowerSeries ℚ) - X)⁻¹ = mk 1 := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp)]
    exact mk_one_mul_one_sub_eq_one ℚ
  rw [e, two_mul, map_add, coeff_mk]
  norm_num

lemma c_pos (m : ℕ) (hm : m ≠ 0) : c m = (m : ℚ) + 1 - (if m % 2 = 1 then 2 else 0) := by
  simp [c, hm]

/-- a(n) as a finite sum over k ≤ n. -/
lemma a_eq (n : ℕ) (hn : 1 ≤ n) :
    a n = 2 + ∑ k ∈ Finset.Icc 0 n, (if 2 ^ k ∣ n then c (n / 2 ^ k) else 0) := by
  unfold a
  rw [coeff_first]
  congr 1
  rw [finsum_eq_sum_of_support_subset (s := Finset.Icc 0 n)]
  · exact Finset.sum_congr rfl (fun k _ => coeff_term k n)
  · intro k hk
    rw [Function.mem_support, coeff_term] at hk
    simp only [Finset.coe_Icc, Set.mem_Icc, zero_le, true_and]
    by_contra hkn
    apply hk
    have hnd : ¬ 2 ^ k ∣ n := by
      intro hd
      have h1 := Nat.le_of_dvd (by omega) hd
      have h2 : k < 2 ^ k := Nat.lt_two_pow_self
      omega
    simp [hnd]

/-- For fixed x, the pairs (y, z) form the antidiagonal of n / 2^x (when 2^x divides n). -/
lemma inner_count (x n : ℕ) :
    ((Finset.Icc 0 n ×ˢ Finset.Icc 0 n).filter
      (fun q : ℕ × ℕ => 2 ^ x * (q.1 + q.2) = n)).card =
      if 2 ^ x ∣ n then n / 2 ^ x + 1 else 0 := by
  have hpos : 0 < 2 ^ x := by positivity
  split_ifs with hd
  · obtain ⟨m, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left _ hpos, ← Finset.Nat.card_antidiagonal m]
    congr 1
    ext ⟨y, z⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, zero_le, true_and,
      Finset.HasAntidiagonal.mem_antidiagonal]
    constructor
    · rintro ⟨_, heq⟩
      exact Nat.eq_of_mul_eq_mul_left hpos heq
    · intro heq
      have hm : m ≤ 2 ^ x * m := Nat.le_mul_of_pos_left m hpos
      refine ⟨⟨by omega, by omega⟩, by rw [heq]⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨y, z⟩ _ heq
    exact hd ⟨y + z, heq.symm⟩

lemma count_eq (n : ℕ) :
    ((Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n).filter
      (fun s : ℕ × ℕ × ℕ => 2 ^ s.1 * (s.2.1 + s.2.2) = n)).card =
      ∑ x ∈ Finset.Icc 0 n, (if 2 ^ x ∣ n then n / 2 ^ x + 1 else 0) := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← inner_count x n, Finset.card_filter]

/-- If 2^k divides n then n / 2^k is odd exactly when k is the 2-adic valuation of n. -/
lemma odd_iff (n k : ℕ) (hn : n ≠ 0) (hd : 2 ^ k ∣ n) :
    (n / 2 ^ k) % 2 = 1 ↔ k = padicValNat 2 n := by
  obtain ⟨m, rfl⟩ := hd
  have hpos : 0 < 2 ^ k := by positivity
  have hm : m ≠ 0 := by
    rintro rfl
    simp at hn
  rw [Nat.mul_div_cancel_left _ hpos, padicValNat.mul (by positivity) hm, padicValNat.prime_pow]
  have : padicValNat 2 m = 0 ↔ ¬ 2 ∣ m := by
    rw [padicValNat.eq_zero_iff]
    omega
  omega

lemma sum_parity (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 0 n,
      (if 2 ^ k ∣ n then (if (n / 2 ^ k) % 2 = 1 then (2 : ℚ) else 0) else 0) = 2 := by
  have hdv : 2 ^ padicValNat 2 n ∣ n := pow_padicValNat_dvd
  have hv : padicValNat 2 n ∈ Finset.Icc 0 n := by
    simp only [Finset.mem_Icc, zero_le, true_and]
    have h1 := Nat.le_of_dvd (by omega) hdv
    have h2 : padicValNat 2 n < 2 ^ padicValNat 2 n := Nat.lt_two_pow_self
    omega
  rw [Finset.sum_eq_single (padicValNat 2 n)]
  · rw [if_pos hdv, if_pos ((odd_iff n _ (by omega) hdv).mpr rfl)]
  · intro k _ hk
    split_ifs with hd hodd
    · exact absurd ((odd_iff n k (by omega) hd).mp hodd) hk
    · rfl
    · rfl
  · intro hnot
    exact absurd hv hnot

theorem sol : type_of% @OMA.S_oeis_a084432.main := by
  intro n hn
  rw [a_eq n hn, count_eq n]
  have key : ∀ k ∈ Finset.Icc 0 n, (if 2 ^ k ∣ n then c (n / 2 ^ k) else 0) =
      ((if 2 ^ k ∣ n then n / 2 ^ k + 1 else 0 : ℕ) : ℚ) -
        (if 2 ^ k ∣ n then (if (n / 2 ^ k) % 2 = 1 then (2 : ℚ) else 0) else 0) := by
    intro k _
    by_cases hd : 2 ^ k ∣ n
    · have hne : n / 2 ^ k ≠ 0 := by
        have h1 := Nat.le_of_dvd (by omega) hd
        have h2 : 0 < n / 2 ^ k := Nat.div_pos h1 (by positivity)
        omega
      rw [if_pos hd, if_pos hd, if_pos hd, c_pos _ hne]
      push_cast
      ring
    · simp [hd]
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, sum_parity n hn, Nat.cast_sum]
  ring

end OMA.P084432

theorem OMA.solution : type_of% @OMA.S_oeis_a084432.main := OMA.P084432.sol

