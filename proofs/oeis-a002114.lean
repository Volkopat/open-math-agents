import OMAStatements.S_oeis_a002114

open Finset OMA.S_oeis_a002114

private lemma pow_stab {m : ℕ} (hm : 0 < m) (b n d : ℕ) (hn : m ≤ n) (hd : m.totient ∣ d) :
    b ^ (n + d) ≡ b ^ n [MOD m] := by
  induction m using Nat.recOnPrimeCoprime generalizing n d with
  | zero => omega
  | prime_pow p e hp =>
    by_cases hb : p ∣ b
    · have he : e ≤ n := by have := Nat.lt_two_pow_self (n := e); have := Nat.pow_le_pow_left hp.two_le e; omega
      have h : p ^ e ∣ b ^ n := (pow_dvd_pow_of_dvd hb e).trans (pow_dvd_pow b he)
      exact (h.trans (pow_dvd_pow b (by omega : n ≤ n + d))).modEq_zero_nat.trans h.modEq_zero_nat.symm
    · obtain ⟨t, rfl⟩ := hd
      simpa [pow_add, pow_mul] using ((Nat.ModEq.pow_totient ((hp.coprime_iff_not_dvd.2 hb).symm.pow_right _)).pow t).mul_left (b ^ n)
  | coprime u v hu hv huv ihu ihv =>
    exact (Nat.modEq_and_modEq_iff_modEq_mul huv).1
      ⟨ihu (by omega) n d ((Nat.le_of_dvd hm (dvd_mul_right u v)).trans hn) ((Nat.totient_dvd_of_dvd (dvd_mul_right u v)).trans hd),
       ihv (by omega) n d ((Nat.le_of_dvd hm (dvd_mul_left v u)).trans hn) ((Nat.totient_dvd_of_dvd (dvd_mul_left v u)).trans hd)⟩

private def T (n k j : ℕ) : ℤ := (-1) ^ j * ((2 * k).choose j : ℤ) * ((k : ℤ) - j) ^ (2 * n)
private def R (n k : ℕ) : ℤ := (-1 : ℤ) ^ (n + k) * ∑ j ∈ range k, T n k j

private lemma neg1 {k j : ℕ} (h : j ≤ 2 * k) : (-1 : ℤ) ^ (2 * k - j) = (-1) ^ j := by
  rw [neg_one_pow_eq_pow_mod_two (2 * k - j), neg_one_pow_eq_pow_mod_two j]; congr 1; omega

private lemma dbl {n : ℕ} (hn : 0 < n) (k : ℕ) : ∑ j ∈ range (2 * k + 1), T n k j = 2 * ∑ j ∈ range k, T n k j := by
  have hm : T n k k = 0 := by simp [T, hn.ne']
  have hr : ∑ i ∈ range k, T n k (k + 1 + i) = ∑ i ∈ range k, T n k i := by
    rw [← sum_range_reflect (T n k) k]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    have hj : k + 1 + i ≤ 2 * k := by omega
    have hsub : 2 * k - (k + 1 + i) = k - 1 - i := by omega
    dsimp [T]; rw [← hsub, neg1 hj, Nat.choose_symm hj, Nat.cast_sub hj, pow_mul, pow_mul]
    congr 2; push_cast; ring
  rw [show 2 * k + 1 = (k + 1) + k by omega, sum_range_add, sum_range_succ, hm, hr]; ring

private lemma pad {n K : ℕ} (hn : 0 < n) (hK : n ≤ K) : glaisherHPrime n = ∑ k ∈ range (K + 1), R n k := by
  have h1 : glaisherHPrime n = ∑ k ∈ range (n + 1), R n k := by
    change (∑ k ∈ range (n + 1), (-1 : ℤ) ^ (n + k) * ∑ j ∈ range (2 * k + 1), T n k j) / 2 = _
    simp_rw [dbl hn]
    have : ∑ k ∈ range (n + 1), (-1 : ℤ) ^ (n + k) * (2 * ∑ j ∈ range k, T n k j) = 2 * ∑ k ∈ range (n + 1), R n k := by
      rw [mul_sum]; exact sum_congr rfl fun k _ => by dsimp [R]; ring
    rw [this]; omega
  rw [h1]
  refine sum_subset (range_mono (by omega)) fun k _ hk => ?_
  have hk' : n < k := by simp only [mem_range, not_lt] at hk; omega
  have h := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) (show 2 * n < 2 * k by omega)) (-(k : ℤ))
  rw [fwdDiff_iter_eq_sum_shift] at h
  have hz : ∑ j ∈ range (2 * k + 1), T n k j = 0 := by
    refine (sum_congr rfl fun j hj => ?_).trans h
    have hj' := mem_range.1 hj
    rw [neg1 (by omega : j ≤ 2 * k)]; simp only [T, zsmul_eq_mul, nsmul_eq_mul, mul_one, pow_mul]
    rw [show (-(k : ℤ) + j) ^ 2 = ((k : ℤ) - j) ^ 2 by ring]; norm_cast
  rw [dbl hn] at hz; dsimp [R]; rw [show ∑ j ∈ range k, T n k j = 0 by omega, mul_zero]

theorem OMA.solution : type_of% @OMA.S_oeis_a002114.main := by
  intro m hm
  refine ⟨m.totient, m, Nat.totient_pos.2 hm, dvd_rfl, hm, fun n hn => ?_⟩
  rw [pad (K := n + m.totient) (by omega) le_rfl, pad (K := n + m.totient) (by omega) (by omega)]
  apply (ZMod.intCast_eq_intCast_iff _ _ m).1
  have : NeZero m := ⟨hm.ne'⟩
  have hst (b : ZMod m) : b ^ (n + m.totient) = b ^ n := by
    simpa using (ZMod.natCast_eq_natCast_iff _ _ m).2 (pow_stab hm b.val n m.totient hn dvd_rfl)
  have hrp (a k : ℕ) : R a k = ∑ j ∈ range k, (-1 : ℤ) ^ (k + j) * ((2 * k).choose j : ℤ) * (-((k : ℤ) - j) ^ 2) ^ a := by
    dsimp [R]; rw [mul_sum]; refine sum_congr rfl fun j _ => ?_
    dsimp [T]; rw [show -((k : ℤ) - j) ^ 2 = -1 * ((k : ℤ) - j) ^ 2 by ring, mul_pow, pow_mul, pow_add, pow_add]; ring
  push_cast
  refine sum_congr rfl fun k _ => ?_
  rw [hrp, hrp]; push_cast
  exact sum_congr rfl fun j _ => by rw [hst]
