import OMAStatements.S_oeis_a210247

/-!
Robert Israel gave the counterexample at 578 and 606 to Mikhail Kurkov's
proposed sign reversal in OEIS A210247 on September 5, 2018.
https://oeis.org/A210247/internal

The analytic tail bound and the original formalization are by @grp06 (PR #28343).
-/

open scoped BigOperators

namespace A210247Certificate

open OMA.S_oeis_a210247 (term polylog a)

private def step (n k : ℕ) (b : ℤ) : ℤ :=
  3 * b + (-1 : ℤ)^k * (k : ℤ)^n

private def B (n : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => step n (k + 1) (B n k)

private lemma partial_sum (n k : ℕ) :
    (∑ i ∈ Finset.range k, term n (i + 1)) = (B n k : ℝ) / 3^k := by
  induction k with
  | zero => simp [B]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, B]
    simp only [step, term, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_neg,
      Int.cast_one, Int.cast_ofNat, Int.cast_natCast, div_pow, pow_succ (3 : ℝ) k]
    have h : (3 : ℝ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp [h]

-- A pair consists of one negative summand followed by one positive summand.
-- Natural powers let the kernel evaluate each summand by binary exponentiation.
private def paired (n : ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => 9 * paired n k - 3 * ((2*k+1)^n : ℕ) + ((2*k+2)^n : ℕ)

private theorem paired_eq (n k : ℕ) : paired n k = B n (2*k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k+1) = 2*k+1+1 by omega, B, B, paired, ih]
    have evenSign : (-1 : ℤ)^(2*k) = 1 := by rw [pow_mul]; norm_num
    simp only [step, pow_succ (-1 : ℤ), evenSign, Nat.cast_pow, Nat.cast_add,
      Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    ring

set_option maxRecDepth 24576 in
private theorem prefix_578 : 3 * B 578 2000 + 2 * (2001 : ℤ)^578 < 0 := by
  rw [← paired_eq 578 1000]
  decide +kernel

set_option maxRecDepth 24576 in
private theorem prefix_606 : 3 * B 606 2000 + 2 * (2001 : ℤ)^606 < 0 := by
  rw [← paired_eq 606 1000]
  decide +kernel

private theorem ratio_578 : 2 * (2002 : ℕ)^578 < 3 * 2001^578 := by decide +kernel

private theorem ratio_606 : 2 * (2002 : ℕ)^606 < 3 * 2001^606 := by decide +kernel


private lemma abs_term (n k : ℕ) :
    |term n k| = (k : ℝ)^n * (1 / 3 : ℝ)^k := by
  have hk : 0 ≤ (k : ℝ)^n := pow_nonneg (Nat.cast_nonneg k) n
  rw [term, abs_mul, abs_of_nonneg hk, abs_pow]
  have h : |(-1 / 3 : ℝ)| = (1 / 3 : ℝ) := by norm_num
  rw [h]

private lemma term_step (n k : ℕ) (hk : 2001 ≤ k)
    (h : 2 * (2002 : ℕ)^n < 3 * 2001^n) :
    |term n (k + 1)| ≤ |term n k| * (1 / 2 : ℝ) := by
  have hreal : 2 * (2002 : ℝ)^n < 3 * 2001^n := by exact_mod_cast h
  have hkreal : (2001 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hbase : ((k : ℝ) + 1) / k ≤ (2002 : ℝ) / 2001 := by
    apply (div_le_div_iff₀ hkpos (by norm_num : (0 : ℝ) < 2001)).2
    linarith
  have hpow := pow_le_pow_left₀
    (div_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) hkpos.le) hbase n
  have hratio : (((k : ℝ) + 1) / k)^n ≤ (3 / 2 : ℝ) := by
    refine hpow.trans ?_
    rw [div_pow]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2001^n)).2
    linarith only [hreal]
  rw [div_pow] at hratio
  have hnext := (div_le_iff₀ (pow_pos hkpos n)).1 hratio
  have hscaled := mul_le_mul_of_nonneg_right hnext
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3) k)
  rw [abs_term, abs_term, Nat.cast_add, Nat.cast_one, pow_succ (1 / 3 : ℝ) k]
  calc
    ((k : ℝ) + 1)^n * ((1 / 3 : ℝ)^k * (1 / 3)) =
        (((k : ℝ) + 1)^n * (1 / 3 : ℝ)^k) * (1 / 3) := by ring
    _ ≤ ((3 / 2 : ℝ) * (k : ℝ)^n * (1 / 3 : ℝ)^k) * (1 / 3) :=
      mul_le_mul_of_nonneg_right hscaled (by norm_num)
    _ = (k : ℝ)^n * (1 / 3 : ℝ)^k * (1 / 2) := by ring

private lemma tail_bound (n : ℕ) (h : 2 * (2002 : ℕ)^n < 3 * 2001^n) (j : ℕ) :
    |term n (j + 2000 + 1)| ≤
      ((2001 : ℝ)^n * (1 / 3 : ℝ)^2001) * (1 / 2 : ℝ)^j := by
  induction j with
  | zero =>
    change |term n 2001| ≤ ((2001 : ℝ)^n * (1 / 3 : ℝ)^2001) * (1 / 2 : ℝ)^0
    simp only [abs_term, Nat.cast_ofNat, pow_zero, mul_one, le_refl]
  | succ j ih =>
    have he : j + 1 + 2000 + 1 = (j + 2000 + 1) + 1 := by omega
    rw [he, pow_succ (1 / 2 : ℝ) j, ← mul_assoc]
    exact (term_step n (j + 2000 + 1) (by omega) h).trans
      (mul_le_mul_of_nonneg_right ih (by norm_num))

private lemma join_bounds (b c d : ℝ) (hd : 0 < d) (h : 3 * b + 2 * c < 0) :
    b / d + 2 * (c * (1 / (d * 3))) < 0 := by
  calc
    b / d + 2 * (c * (1 / (d * 3))) = (3 * b + 2 * c) / (d * 3) := by
      field_simp [ne_of_gt hd]
    _ < 0 := div_neg_of_neg_of_pos h (by positivity)

private lemma polylog_neg (n : ℕ)
    (hp : 3 * B n 2000 + 2 * (2001 : ℤ)^n < 0)
    (hr : 2 * (2002 : ℕ)^n < 3 * 2001^n) : polylog n < 0 := by
  let R : ℝ := (2001 : ℝ)^n * (1 / 3 : ℝ)^2001
  have hs : Summable (fun k : ℕ ↦ term n k) :=
    summable_pow_mul_geometric_of_norm_lt_one n (r := (-1 / 3 : ℝ)) (by norm_num)
  have hs1 : Summable (fun k : ℕ ↦ term n (k + 1)) :=
    (summable_nat_add_iff 1).2 hs
  have hs2 : Summable (fun j : ℕ ↦ term n (j + 2000 + 1)) :=
    (summable_nat_add_iff 2000).2 hs1
  have hg : HasSum (fun j : ℕ ↦ R * (1 / 2 : ℝ)^j) (R * 2) :=
    hasSum_geometric_two.mul_left R
  have htail : (∑' j : ℕ, term n (j + 2000 + 1)) ≤ R * 2 := by
    rw [← hg.tsum_eq]
    exact hs2.tsum_le_tsum (fun j ↦ (le_abs_self _).trans (tail_bound n hr j)) hg.summable
  have hpreal : 3 * (B n 2000 : ℝ) + 2 * (2001 : ℝ)^n < 0 := by exact_mod_cast hp
  have hR : R = (2001 : ℝ)^n * (1 / ((3 : ℝ)^2000 * 3)) := by
    change (2001 : ℝ)^n * (1 / 3 : ℝ)^(2000 + 1) = _
    rw [div_pow, one_pow, pow_succ (3 : ℝ) 2000]
  have htotal : (B n 2000 : ℝ) / (3 : ℝ)^2000 + R * 2 < 0 := by
    rw [hR, mul_comm _ (2 : ℝ)]
    exact join_bounds _ _ _ (pow_pos (by norm_num) _) hpreal
  unfold polylog
  rw [← Summable.sum_add_tsum_nat_add 2000 hs1, partial_sum]
  exact (add_le_add (le_refl ((B n 2000 : ℝ) / 3^2000)) htail).trans_lt htotal

lemma sign_578 : a 578 = -1 := by
  have h := polylog_neg 578 prefix_578 ratio_578
  simp [a, h]

lemma sign_606 : a 606 = -1 := by
  have h := polylog_neg 606 prefix_606 ratio_606
  simp [a, h]

end A210247Certificate

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a210247.main) := by
  intro h
  have hh := h 578
  change OMA.S_oeis_a210247.a 606 = -OMA.S_oeis_a210247.a 578 at hh
  rw [A210247Certificate.sign_606, A210247Certificate.sign_578] at hh
  norm_num at hh
