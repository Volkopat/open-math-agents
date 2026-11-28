import OMAStatements.S_oeis_a155200
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

namespace OMA.P_oeis_a155200

open OMA.S_oeis_a155200

private abbrev μ := ArithmeticFunction.moebius

/-- Integer sequence `c(n) = n! * a(n) / 2^n`. -/
private def c : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      ∑ k ∈ Finset.range (n + 1),
        (n.descFactorial k) * 2 ^ ((k + 1) ^ 2 - (k + 1)) * c (n - k)

private lemma c_odd : ∀ n : ℕ, Odd (c n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ⟨0, by simp [c]⟩
    | succ n =>
      rw [c, Finset.sum_range_succ']
      simp only [Nat.descFactorial_zero, one_mul, Nat.sub_zero, zero_add, one_pow,
        Nat.sub_self, pow_zero, mul_one]
      have h0 : Odd (c n) := ih n (Nat.lt_succ_self n)
      have heven : Even (∑ k ∈ Finset.range n,
          (n.descFactorial (k + 1)) * 2 ^ ((k + 1 + 1) ^ 2 - (k + 1 + 1)) * c (n - (k + 1))) := by
        have hdvd : 2 ∣ ∑ k ∈ Finset.range n,
            (n.descFactorial (k + 1)) * 2 ^ ((k + 1 + 1) ^ 2 - (k + 1 + 1)) * c (n - (k + 1)) := by
          refine Finset.dvd_sum (fun k _ => ?_)
          have hexp : 1 ≤ (k + 1 + 1) ^ 2 - (k + 1 + 1) := by
            have : (k + 1 + 1) + 1 ≤ (k + 1 + 1) ^ 2 := by nlinarith
            omega
          have h2 : 2 ∣ 2 ^ ((k + 1 + 1) ^ 2 - (k + 1 + 1)) := dvd_pow_self 2 (by omega)
          exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h2 _) _
        exact even_iff_two_dvd.mpr hdvd
      exact heven.add_odd h0

private lemma factorial_mul_a_eq (n : ℕ) :
    (n.factorial : ℚ) * a n = (2 : ℚ) ^ n * (c n : ℚ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [a, c]
    | succ n =>
      rw [a, c]
      have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      rw [Nat.factorial_succ, Nat.cast_mul, mul_comm ((n + 1 : ℕ) : ℚ), mul_assoc,
        mul_comm ((n + 1 : ℕ) : ℚ), div_mul_cancel₀ _ hn1,
        Finset.mul_sum, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hih := ih (n - k) (by omega)
      have hdesc : n.descFactorial k * (n - k).factorial = n.factorial := by
        clear hih hk
        induction k with
        | zero => simp
        | succ k ihk =>
          rw [Nat.descFactorial_succ]
          have hsub : n - k = (n - (k + 1)) + 1 := by omega
          have hfac_step : (n - k) * (n - (k + 1)).factorial = (n - k).factorial := by
            conv_rhs => rw [hsub, Nat.factorial_succ]
            rw [← hsub]
          calc (n - k) * n.descFactorial k * (n - (k + 1)).factorial
              = n.descFactorial k * ((n - k) * (n - (k + 1)).factorial) := by ring
            _ = n.descFactorial k * (n - k).factorial := by rw [hfac_step]
            _ = n.factorial := ihk (by omega)
      have hdesc_q : (n.factorial : ℚ) = (n.descFactorial k : ℚ) * ((n - k).factorial : ℚ) := by
        exact_mod_cast hdesc.symm
      have hexp : (k + 1) ^ 2 + (n - k) = (n + 1) + ((k + 1) ^ 2 - (k + 1)) := by
        have : k + 1 ≤ (k + 1) ^ 2 := by nlinarith
        omega
      have hpow : (2 : ℚ) ^ ((k + 1) ^ 2) * (2 : ℚ) ^ (n - k) =
          (2 : ℚ) ^ (n + 1) * (2 : ℚ) ^ ((k + 1) ^ 2 - (k + 1)) := by
        rw [← pow_add, ← pow_add, hexp]
      calc (n.factorial : ℚ) * ((2 : ℚ) ^ ((k + 1) ^ 2) * a (n - k))
          = (n.descFactorial k : ℚ) * (2 : ℚ) ^ ((k + 1) ^ 2) * (((n - k).factorial : ℚ) * a (n - k)) := by
            rw [hdesc_q]; ring
        _ = (n.descFactorial k : ℚ) * (2 : ℚ) ^ ((k + 1) ^ 2) * ((2 : ℚ) ^ (n - k) * (c (n - k) : ℚ)) := by
            rw [hih]
        _ = (n.descFactorial k : ℚ) * ((2 : ℚ) ^ ((k + 1) ^ 2) * (2 : ℚ) ^ (n - k)) * (c (n - k) : ℚ) := by
            ring
        _ = (2 : ℚ) ^ (n + 1) * ((n.descFactorial k * 2 ^ ((k + 1) ^ 2 - (k + 1)) * c (n - k) : ℕ) : ℚ) := by
            rw [hpow]; push_cast; ring

/-- Elementary Legendre formula for `p = 2`: `n! = 2^(n - popcount(n)) * r` with `r` odd. -/
private lemma digits_two_sum_le (n : ℕ) : (Nat.digits 2 n).sum ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · rw [Nat.digits_def' (by norm_num) hpos, List.sum_cons]
      have hlt : n / 2 < n := Nat.div_lt_self hpos (by norm_num)
      have hih := ih (n / 2) hlt
      omega

private lemma digits_two_sum_succ (n : ℕ) :
    ∀ k r : ℕ, Odd r → n + 1 = 2 ^ k * r →
      (Nat.digits 2 n).sum + 1 = (Nat.digits 2 (n + 1)).sum + k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k r hr hnr
    cases k with
    | zero =>
      -- n + 1 is odd, so n is even
      have heven : n % 2 = 0 := by
        obtain ⟨t, ht⟩ := hr
        omega
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · simp
      · have h1 : (Nat.digits 2 (n + 1)).sum = 1 + (Nat.digits 2 (n / 2)).sum := by
          rw [Nat.digits_def' (by norm_num) (by omega), List.sum_cons]
          have hmod : (n + 1) % 2 = 1 := by omega
          have hdiv : (n + 1) / 2 = n / 2 := by omega
          rw [hmod, hdiv]
        have h2 : (Nat.digits 2 n).sum = (Nat.digits 2 (n / 2)).sum := by
          rw [Nat.digits_def' (by norm_num) hpos, List.sum_cons, heven, zero_add]
        omega
    | succ k =>
      -- n + 1 = 2^(k+1) * r is even, so n is odd
      have h2 : n + 1 = 2 * (2 ^ k * r) := by rw [hnr, pow_succ']; ring
      have hodd : n % 2 = 1 := by omega
      have hdiv_succ : (n + 1) / 2 = n / 2 + 1 := by omega
      have hdiv_eq : n / 2 + 1 = 2 ^ k * r := by omega
      have hih := ih (n / 2) (by omega) k r hr hdiv_eq
      have h1 : (Nat.digits 2 (n + 1)).sum = (Nat.digits 2 (n / 2 + 1)).sum := by
        rw [Nat.digits_def' (by norm_num) (by omega), List.sum_cons]
        have hmod : (n + 1) % 2 = 0 := by omega
        rw [hmod, zero_add, hdiv_succ]
      have h2 : (Nat.digits 2 n).sum = 1 + (Nat.digits 2 (n / 2)).sum := by
        rw [Nat.digits_def' (by norm_num) (by omega), List.sum_cons, hodd]
      omega

private lemma factor_two_odd (n : ℕ) (hn : n ≠ 0) :
    ∃ k r : ℕ, Odd r ∧ n = 2 ^ k * r := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases he : 2 ∣ n
    · obtain ⟨m, rfl⟩ := he
      have hm : m ≠ 0 := by omega
      obtain ⟨k, r, hr, hmr⟩ := ih m (by omega) hm
      exact ⟨k + 1, r, hr, by rw [pow_succ', mul_assoc, ← hmr]⟩
    · exact ⟨0, n, Nat.odd_iff.mpr (by omega), by simp⟩

private lemma legendre_two (n : ℕ) :
    ∃ r : ℕ, Odd r ∧ n.factorial = 2 ^ (n - (Nat.digits 2 n).sum) * r := by
  induction n with
  | zero => exact ⟨1, ⟨0, by norm_num⟩, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr, hfac⟩ := ih
    obtain ⟨k, s, hs, hns⟩ := factor_two_odd (n + 1) (Nat.succ_ne_zero n)
    have hdig := digits_two_sum_succ n k s hs hns
    have hle1 := digits_two_sum_le n
    have hle2 := digits_two_sum_le (n + 1)
    have hexp : (n + 1) - (Nat.digits 2 (n + 1)).sum = (n - (Nat.digits 2 n).sum) + k := by omega
    refine ⟨s * r, hs.mul hr, ?_⟩
    rw [Nat.factorial_succ, hfac, hexp, pow_add, hns]
    ring

/-- Gauss congruence for `2^(n^2)`: `d ∣ ∑_{k | d} μ(d/k) * 2^(k^2)` for all `d ≥ 1`. -/
private lemma prime_pow_dvd_two_pow_sq_diff (p a j : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hj : 1 ≤ j) :
    (p ^ a : ℤ) ∣ ((2 : ℤ) ^ ((p ^ a * j) ^ 2) - (2 : ℤ) ^ ((p ^ (a - 1) * j) ^ 2)) := by
  by_cases hp2 : p = 2
  · subst hp2
    have hexp1 : a ≤ (2 ^ (a - 1) * j) ^ 2 := by
      have h1 : 1 ≤ 2 ^ (a - 1) := Nat.one_le_pow _ _ (by norm_num)
      have h2 : a ≤ 2 ^ (a - 1) * 2 ^ (a - 1) := by
        clear hj h1
        induction a with
        | zero => omega
        | succ a iha =>
          cases a with
          | zero => norm_num
          | succ a =>
            have hprev := iha (by omega)
            simp only [Nat.add_sub_cancel] at hprev ⊢
            rw [pow_succ]
            nlinarith [Nat.one_le_pow a 2 (by norm_num)]
      have h3 : 2 ^ (a - 1) * 2 ^ (a - 1) ≤ (2 ^ (a - 1) * j) ^ 2 := by
        rw [mul_pow, sq]
        have hj2 : 1 ≤ j ^ 2 := Nat.one_le_pow 2 j hj
        calc 2 ^ (a - 1) * 2 ^ (a - 1) = 2 ^ (a - 1) * 2 ^ (a - 1) * 1 := (mul_one _).symm
          _ ≤ 2 ^ (a - 1) * 2 ^ (a - 1) * j ^ 2 := Nat.mul_le_mul_left _ hj2
      exact le_trans h2 h3
    have hexp2 : a ≤ (2 ^ a * j) ^ 2 := by
      have hle : 2 ^ (a - 1) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact le_trans hexp1 (Nat.pow_le_pow_left (Nat.mul_le_mul_right j hle) 2)
    have hd1 : ((2 ^ a : ℕ) : ℤ) ∣ (2 : ℤ) ^ ((2 ^ a * j) ^ 2) := by
      exact_mod_cast Nat.pow_dvd_pow 2 hexp2
    have hd2 : ((2 ^ a : ℕ) : ℤ) ∣ (2 : ℤ) ^ ((2 ^ (a - 1) * j) ^ 2) := by
      exact_mod_cast Nat.pow_dvd_pow 2 hexp1
    exact_mod_cast dvd_sub hd1 hd2
  · have hcop : Nat.Coprime 2 (p ^ a) :=
      (hp.coprime_iff_not_dvd.mpr (fun h => hp2 (by
        have := Nat.le_of_dvd (by norm_num) h
        have := hp.two_le
        omega))).symm.pow_right a
    have heuler : 2 ^ Nat.totient (p ^ a) ≡ 1 [MOD p ^ a] :=
      Nat.ModEq.pow_totient hcop
    have hphi : Nat.totient (p ^ a) = p ^ (a - 1) * (p - 1) := Nat.totient_prime_pow hp ha
    have hle_exp : (p ^ (a - 1) * j) ^ 2 ≤ (p ^ a * j) ^ 2 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_right j (Nat.pow_le_pow_right hp.pos (by omega))) 2
    have hdiff_eq : (p ^ a * j) ^ 2 - (p ^ (a - 1) * j) ^ 2 =
        (p ^ (a - 1) * (p - 1)) * (p ^ (a - 1) * (p + 1) * j ^ 2) := by
      have hp1 : 1 ≤ p := hp.one_le
      have hpa : p ^ a = p ^ (a - 1) * p := by
        rw [← pow_succ, Nat.sub_add_cancel ha]
      rw [hpa]
      have h1 : (p ^ (a - 1) * p * j) ^ 2 = (p ^ (a - 1) * j) ^ 2 * p ^ 2 := by ring
      rw [h1]
      have h2 : (p ^ (a - 1) * j) ^ 2 * p ^ 2 - (p ^ (a - 1) * j) ^ 2 =
          (p ^ (a - 1) * j) ^ 2 * (p ^ 2 - 1) := by
        rw [Nat.mul_sub_left_distrib, mul_one]
      rw [h2]
      have hp2' : p ^ 2 - 1 = (p - 1) * (p + 1) := by
        have hp2_ge : 1 ≤ p ^ 2 := by nlinarith
        zify [hp1, hp2_ge]; ring
      rw [hp2']
      ring
    have hdvd_exp : Nat.totient (p ^ a) ∣ ((p ^ a * j) ^ 2 - (p ^ (a - 1) * j) ^ 2) := by
      rw [hphi, hdiff_eq]; exact dvd_mul_right _ _
    obtain ⟨q, hq⟩ := hdvd_exp
    have hpow_mod : 2 ^ ((p ^ a * j) ^ 2 - (p ^ (a - 1) * j) ^ 2) ≡ 1 [MOD p ^ a] := by
      rw [hq, pow_mul]
      simpa using heuler.pow q
    have hfull : 2 ^ ((p ^ a * j) ^ 2) ≡ 2 ^ ((p ^ (a - 1) * j) ^ 2) [MOD p ^ a] := by
      have h := hpow_mod.mul_left (2 ^ ((p ^ (a - 1) * j) ^ 2))
      rw [← pow_add, Nat.add_sub_cancel' hle_exp, mul_one] at h
      exact h
    have hmodz : ((2 : ℤ) ^ ((p ^ a * j) ^ 2)) ≡ ((2 : ℤ) ^ ((p ^ (a - 1) * j) ^ 2)) [ZMOD (p ^ a : ℤ)] := by
      exact_mod_cast hfull
    exact Int.modEq_iff_dvd.mp hmodz.symm

private lemma moebius_gauss_dvd (d : ℕ) (hd : 1 ≤ d) :
    (d : ℤ) ∣ ∑ k ∈ d.divisors, (μ (d / k) : ℤ) * (2 : ℤ) ^ (k ^ 2) := by
  have hpp : ∀ p : ℕ, p.Prime → p ∣ d →
      (p ^ (d.factorization p) : ℤ) ∣ ∑ k ∈ d.divisors, (μ (d / k) : ℤ) * (2 : ℤ) ^ (k ^ 2) := by
    intro p hp hpd
    set a := d.factorization p
    have ha : 1 ≤ a := by
      have := (hp.dvd_iff_one_le_factorization (by omega)).mp hpd
      exact this
    have hpa_dvd : p ^ a ∣ d := Nat.ordProj_dvd d p
    obtain ⟨m, hm⟩ := hpa_dvd
    have hm_pos : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp at hm; omega
      · exact hpos
    have hp_ndvd_m : ¬ p ∣ m := by
      intro hpm
      have h1 : p ^ (a + 1) ∣ d := by
        rw [hm, pow_succ]
        obtain ⟨t, rfl⟩ := hpm
        exact ⟨t, by ring⟩
      have h2 := (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega)).mp h1
      omega
    have hcop_pm : Nat.Coprime (p ^ a) m :=
      (hp.coprime_iff_not_dvd.mpr hp_ndvd_m).pow_left a
    -- Sum over divisors of `p^a * m` splits as double sum over `i ≤ a` and `j ∣ m`.
    have hsum_eq : ∑ k ∈ d.divisors, (μ (d / k) : ℤ) * (2 : ℤ) ^ (k ^ 2) =
        ∑ j ∈ m.divisors, (μ (m / j) : ℤ) *
          ((2 : ℤ) ^ ((p ^ a * j) ^ 2) - (2 : ℤ) ^ ((p ^ (a - 1) * j) ^ 2)) := by
      rw [hm]
      have hdiv_prod : (p ^ a * m).divisors =
          ((p ^ a).divisors ×ˢ m.divisors).image (fun x => x.1 * x.2) := by
        ext k
        simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_product, Prod.exists]
        constructor
        · rintro ⟨hk, hne⟩
          have hgcd1 : Nat.gcd k (p ^ a) ∣ p ^ a := Nat.gcd_dvd_right k (p ^ a)
          have hgcd2 : Nat.gcd k m ∣ m := Nat.gcd_dvd_right k m
          refine ⟨Nat.gcd k (p ^ a), Nat.gcd k m, ⟨⟨hgcd1, pow_ne_zero a hp.ne_zero⟩, ⟨hgcd2, by omega⟩⟩, ?_⟩
          have h1 : Nat.gcd k (p ^ a) * Nat.gcd k m = Nat.gcd k (p ^ a * m) :=
            (Nat.Coprime.gcd_mul k hcop_pm).symm
          rw [h1, Nat.gcd_eq_left hk]
        · rintro ⟨u, v, ⟨⟨hu, _⟩, ⟨hv, _⟩⟩, rfl⟩
          exact ⟨mul_dvd_mul hu hv, mul_ne_zero (pow_ne_zero a hp.ne_zero) (by omega)⟩
      have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) ↑((p ^ a).divisors ×ˢ m.divisors) := by
        rintro ⟨u1, v1⟩ h1 ⟨u2, v2⟩ h2 heq
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Nat.mem_divisors] at h1 h2
        have hc1 : Nat.Coprime u1 v2 := hcop_pm.coprime_dvd_left h1.1.1 |>.coprime_dvd_right h2.2.1
        have hc2 : Nat.Coprime u2 v1 := hcop_pm.coprime_dvd_left h2.1.1 |>.coprime_dvd_right h1.2.1
        have hu : u1 = u2 := Nat.dvd_antisymm
          (hc1.dvd_of_dvd_mul_right ⟨v1, by linarith⟩)
          (hc2.dvd_of_dvd_mul_right ⟨v2, by linarith⟩)
        subst hu
        have hu0 : u1 ≠ 0 := by
          rintro rfl
          exact pow_ne_zero a hp.ne_zero (zero_dvd_iff.mp h1.1.1)
        exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hu0) heq)
      rw [hdiv_prod, Finset.sum_image hinj, Finset.sum_product_right]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjm : j ∣ m := (Nat.mem_divisors.mp hj).1
      have hinner : ∑ u ∈ (p ^ a).divisors, (μ (p ^ a * m / (u * j)) : ℤ) * (2 : ℤ) ^ ((u * j) ^ 2) =
          (μ (m / j) : ℤ) * ((2 : ℤ) ^ ((p ^ a * j) ^ 2) - (2 : ℤ) ^ ((p ^ (a - 1) * j) ^ 2)) := by
        rw [Nat.divisors_prime_pow hp, Finset.sum_map]
        have hterm : ∀ i ∈ Finset.range (a + 1),
            (μ (p ^ a * m / (p ^ i * j)) : ℤ) * (2 : ℤ) ^ ((p ^ i * j) ^ 2) =
            (μ (p ^ (a - i)) : ℤ) * (μ (m / j) : ℤ) * (2 : ℤ) ^ ((p ^ i * j) ^ 2) := by
          intro i hi
          have hia : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hdiv_eq : p ^ a * m / (p ^ i * j) = p ^ (a - i) * (m / j) := by
            have h1 : p ^ a = p ^ i * p ^ (a - i) := by rw [← pow_add, Nat.add_sub_cancel' hia]
            obtain ⟨q, hq⟩ := hjm
            have hj0 : j ≠ 0 := by rintro rfl; simp at hq; omega
            rw [h1, hq, show p ^ i * p ^ (a - i) * (j * q) = (p ^ i * j) * (p ^ (a - i) * q) by ring,
              Nat.mul_div_cancel_left _ (Nat.mul_pos (pow_pos hp.pos i) (Nat.pos_of_ne_zero hj0)),
              Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hj0)]
          have hcop_ij : Nat.Coprime (p ^ (a - i)) (m / j) :=
            (hcop_pm.coprime_dvd_left (Nat.pow_dvd_pow p (Nat.sub_le a i))).coprime_dvd_right (Nat.div_dvd_of_dvd hjm)
          rw [hdiv_eq, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_ij]
        have hsum_rew : ∑ i ∈ Finset.range (a + 1),
            (μ (p ^ a * m / (p ^ i * j)) : ℤ) * (2 : ℤ) ^ ((p ^ i * j) ^ 2) =
            ∑ i ∈ Finset.range (a + 1),
              (μ (p ^ (a - i)) : ℤ) * (μ (m / j) : ℤ) * (2 : ℤ) ^ ((p ^ i * j) ^ 2) :=
          Finset.sum_congr rfl hterm
        simp only [Function.Embedding.coeFn_mk]
        rw [hsum_rew]
        -- Only `i = a` (`μ(1) = 1`) and `i = a - 1` (`μ(p) = -1`) survive!
        have ha_eq : a + 1 = (a - 1) + 1 + 1 := by omega
        rw [ha_eq, Finset.sum_range_succ, Finset.sum_range_succ]
        have hzero : ∑ i ∈ Finset.range (a - 1),
            (μ (p ^ (a - i)) : ℤ) * (μ (m / j) : ℤ) * (2 : ℤ) ^ ((p ^ i * j) ^ 2) = 0 := by
          refine Finset.sum_eq_zero (fun i hi => ?_)
          have hi_lt : i < a - 1 := Finset.mem_range.mp hi
          have hge2 : 2 ≤ a - i := by omega
          have hmu0 : μ (p ^ (a - i)) = 0 := by
            rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
            simp [show a - i ≠ 1 by omega]
          simp [hmu0]
        rw [hzero, zero_add]
        have h1 : a - (a - 1) = 1 := by omega
        have h2 : a - (a - 1 + 1) = 0 := by omega
        have h3 : a - 1 + 1 = a := by omega
        rw [h1, h2, h3, pow_one, pow_zero, ArithmeticFunction.moebius_apply_prime hp,
          ArithmeticFunction.moebius_apply_one]
        ring
      exact hinner
    rw [hsum_eq]
    refine Finset.dvd_sum (fun j hj => ?_)
    have hj1 : 1 ≤ j := Nat.pos_of_ne_zero (fun h => by subst h; simp at hj)
    exact dvd_mul_of_dvd_right (prime_pow_dvd_two_pow_sq_diff p a j hp ha hj1) _
  -- Combine pairwise coprime prime-power factors of `d`!
  have hd_prod : d = ∏ p ∈ d.primeFactors, p ^ d.factorization p :=
    (Nat.prod_factorization_pow_eq_self (by omega)).symm
  have hd_prod_z : (d : ℤ) = ∏ p ∈ d.primeFactors, ((p ^ d.factorization p : ℕ) : ℤ) := by
    conv_lhs => rw [hd_prod]
    rw [Nat.cast_prod]
  rw [hd_prod_z]
  refine Finset.prod_dvd_of_coprime ?_ (fun p hp => ?_)
  · intro p hp q hq hpq
    have hpp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hqp' : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hcop_nat : Nat.Coprime (p ^ d.factorization p) (q ^ d.factorization q) :=
      ((Nat.coprime_primes hpp' hqp').mpr hpq).pow _ _
    exact hcop_nat.isCoprime
  · exact hpp p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

/-- Cauchy product of two sequences `ℕ → ℤ`. -/
private def conv (u v : ℕ → ℤ) : ℕ → ℤ :=
  fun n => ∑ i ∈ Finset.range (n + 1), u i * v (n - i)

private lemma conv_zero (u v : ℕ → ℤ) : conv u v 0 = u 0 * v 0 := by
  simp [conv]

/-- Product rule for the logarithmic-derivative recurrence `n * u(n) = ∑_{k=1}^n f(k) * u(n - k)`. -/
private lemma conv_log_deriv {u v f g : ℕ → ℤ}
    (hu : ∀ n : ℕ, (n : ℤ) * u n = ∑ k ∈ Finset.Icc 1 n, f k * u (n - k))
    (hv : ∀ n : ℕ, (n : ℤ) * v n = ∑ k ∈ Finset.Icc 1 n, g k * v (n - k)) :
    ∀ n : ℕ, (n : ℤ) * conv u v n = ∑ k ∈ Finset.Icc 1 n, (f k + g k) * conv u v (n - k) := by
  intro n
  have hsplit : (n : ℤ) * conv u v n =
      (∑ i ∈ Finset.range (n + 1), ((i : ℤ) * u i) * v (n - i)) +
      (∑ i ∈ Finset.range (n + 1), u i * (((n - i : ℕ) : ℤ) * v (n - i))) := by
    rw [conv, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsub : ((n - i : ℕ) : ℤ) = (n : ℤ) - (i : ℤ) := Nat.cast_sub hin
    rw [hsub]; ring
  have hpart1 : ∑ i ∈ Finset.range (n + 1), ((i : ℤ) * u i) * v (n - i) =
      ∑ k ∈ Finset.Icc 1 n, f k * conv u v (n - k) := by
    have h1 : ∑ i ∈ Finset.range (n + 1), ((i : ℤ) * u i) * v (n - i) =
        ∑ i ∈ Finset.range (n + 1), ∑ k ∈ Finset.Icc 1 i, f k * (u (i - k) * v (n - i)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hu i, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => by ring)
    rw [h1]
    have h2 : ∑ i ∈ Finset.range (n + 1), ∑ k ∈ Finset.Icc 1 i, f k * (u (i - k) * v (n - i)) =
        ∑ i ∈ Finset.range (n + 1), ∑ k ∈ Finset.Icc 1 n,
          if k ≤ i then f k * (u (i - k) * v (n - i)) else 0 := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext k; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
    rw [h2, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
    rw [conv, Finset.mul_sum]
    have hbij : ∑ i ∈ Finset.range (n + 1), (if k ≤ i then f k * (u (i - k) * v (n - i)) else 0) =
        ∑ j ∈ Finset.range (n - k + 1), f k * (u j * v (n - k - j)) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun i _ => i - k) ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
      · intro i1 h1 i2 h2 heq
        simp only [Finset.mem_filter, Finset.mem_range] at h1 h2; omega
      · intro j hj
        refine ⟨j + k, ?_, by omega⟩
        simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢; omega
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        congr 2; congr 1; omega
    exact hbij
  have hpart2 : ∑ i ∈ Finset.range (n + 1), u i * (((n - i : ℕ) : ℤ) * v (n - i)) =
      ∑ k ∈ Finset.Icc 1 n, g k * conv u v (n - k) := by
    have h1 : ∑ i ∈ Finset.range (n + 1), u i * (((n - i : ℕ) : ℤ) * v (n - i)) =
        ∑ i ∈ Finset.range (n + 1), ∑ k ∈ Finset.Icc 1 (n - i), g k * (u i * v (n - i - k)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hv (n - i), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => by ring)
    rw [h1]
    have h2 : ∑ i ∈ Finset.range (n + 1), ∑ k ∈ Finset.Icc 1 (n - i), g k * (u i * v (n - i - k)) =
        ∑ i ∈ Finset.range (n + 1), ∑ k ∈ Finset.Icc 1 n,
          if i + k ≤ n then g k * (u i * v (n - i - k)) else 0 := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext k; simp only [Finset.mem_Icc, Finset.mem_filter]; omega
    rw [h2, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
    rw [conv, Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun i _ => ?_)
    · ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
    · congr 2; congr 1; omega
  rw [hsplit, hpart1, hpart2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => by ring)

private def invFactor (d : ℕ) : ℕ → ℤ := fun n => if d ∣ n then 1 else 0
private def posFactor (d : ℕ) : ℕ → ℤ := fun n => if n = 0 then 1 else if n = d then -1 else 0

private lemma invFactor_log_deriv (d : ℕ) (hd : 1 ≤ d) :
    ∀ n : ℕ, (n : ℤ) * invFactor d n =
      ∑ k ∈ Finset.Icc 1 n, (if d ∣ k then (d : ℤ) else 0) * invFactor d (n - k) := by
  intro n
  dsimp [invFactor]
  by_cases hdn : d ∣ n
  · rw [if_pos hdn, mul_one]
    obtain ⟨q, rfl⟩ := hdn
    have hfilt : ∑ k ∈ Finset.Icc 1 (d * q),
        (if d ∣ k then (d : ℤ) else 0) * (if d ∣ d * q - k then (1 : ℤ) else 0) =
        ∑ k ∈ (Finset.Icc 1 (d * q)).filter (fun k => d ∣ k), (d : ℤ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases hdk : d ∣ k
      · have hsub : d ∣ d * q - k := Nat.dvd_sub (dvd_mul_right d q) hdk
        simp [hdk, hsub]
      · simp [hdk]
    rw [hfilt, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.Icc 1 (d * q)).filter (fun k => d ∣ k)).card = q := by
      have heq : (Finset.Icc 1 (d * q)).filter (fun k => d ∣ k) =
          (Finset.Icc 1 q).image (fun j => d * j) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨hk1, hkq⟩, ⟨j, rfl⟩⟩
          refine ⟨j, ⟨?_, ?_⟩, rfl⟩
          · rcases Nat.eq_zero_or_pos j with rfl | hj
            · simp at hk1
            · exact hj
          · exact Nat.le_of_mul_le_mul_left hkq (by omega)
        · rintro ⟨j, ⟨hj1, hjq⟩, rfl⟩
          exact ⟨⟨by nlinarith, Nat.mul_le_mul_left d hjq⟩, dvd_mul_right d j⟩
      rw [heq, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left (by omega) h),
        Nat.card_Icc]
      omega
    rw [hcard]; push_cast; ring
  · rw [if_neg hdn, mul_zero]
    symm
    refine Finset.sum_eq_zero (fun k hk => ?_)
    have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
    by_cases hdk : d ∣ k
    · have hnd : ¬ d ∣ n - k := by
        intro hsub
        have := dvd_add hsub hdk
        rw [Nat.sub_add_cancel hkn] at this
        exact hdn this
      simp [hdk, hnd]
    · simp [hdk]

private lemma posFactor_log_deriv (d : ℕ) (hd : 1 ≤ d) :
    ∀ n : ℕ, (n : ℤ) * posFactor d n =
      ∑ k ∈ Finset.Icc 1 n, (if d ∣ k then -(d : ℤ) else 0) * posFactor d (n - k) := by
  intro n
  dsimp [posFactor]
  by_cases hn0 : n = 0
  · subst hn0; simp
  · rw [if_neg hn0]
    by_cases hnd : n = d
    · rw [hnd, if_pos rfl]
      have hterm : ∀ k ∈ Finset.Icc 1 d,
          (if d ∣ k then -(d : ℤ) else 0) * (if d - k = 0 then (1 : ℤ) else if d - k = d then -1 else 0) =
          if k = d then -(d : ℤ) else 0 := by
        intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hkd : k ≤ d := (Finset.mem_Icc.mp hk).2
        by_cases heq : k = d
        · rw [heq]; simp
        · have h1 : d - k ≠ 0 := by omega
          have h2 : d - k ≠ d := by omega
          simp [heq, h1, h2]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ d,
        if_pos (Finset.mem_Icc.mpr ⟨hd, le_rfl⟩)]
      ring
    · rw [if_neg hnd, mul_zero]
      symm
      by_cases hlt : n < d
      · refine Finset.sum_eq_zero (fun k hk => ?_)
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
        have hndvd : ¬ d ∣ k := fun h => by have := Nat.le_of_dvd (by omega) h; omega
        simp [hndvd]
      · have hgt : d < n := by omega
        have hterm : ∀ k ∈ Finset.Icc 1 n,
            (if d ∣ k then -(d : ℤ) else 0) *
              (if n - k = 0 then (1 : ℤ) else if n - k = d then -1 else 0) =
            (if k = n then (if d ∣ n then -(d : ℤ) else 0) else 0) +
            (if k = n - d then (if d ∣ n - d then (d : ℤ) else 0) else 0) := by
          intro k hk
          have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
          by_cases h1 : k = n
          · rw [h1]
            have hne : n ≠ n - d := by omega
            simp [hne]
          · by_cases h2 : k = n - d
            · rw [h2]
              have hne2 : n - (n - d) = d := by omega
              have hd0 : d ≠ 0 := by omega
              have hne3 : n - d ≠ n := by omega
              simp only [hne2, hd0, hne3, ↓reduceIte, mul_neg, mul_one, zero_add]
              split_ifs <;> ring
            · have hne1 : n - k ≠ 0 := by omega
              have hne2 : n - k ≠ d := by omega
              simp [h1, h2, hne1, hne2]
        rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
          Finset.sum_ite_eq' _ n, Finset.sum_ite_eq' _ (n - d),
          if_pos (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩),
          if_pos (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)]
        have hiff : d ∣ n - d ↔ d ∣ n :=
          ⟨fun h => by have := dvd_add h (dvd_refl d); rwa [Nat.sub_add_cancel (le_of_lt hgt)] at this,
           fun h => Nat.dvd_sub h (dvd_refl d)⟩
        by_cases hdn : d ∣ n
        · simp [hdn, hiff.mpr hdn]
        · simp [hdn, mt hiff.mp hdn]

/-- Existence of an integer sequence with `u 0 = 1` and given log-derivative `c * (if d | k then d else 0)`. -/
private lemma exists_int_seq_of_single (d : ℕ) (hd : 1 ≤ d) (e : ℤ) :
    ∃ u : ℕ → ℤ, u 0 = 1 ∧ ∀ n : ℕ, (n : ℤ) * u n =
      ∑ k ∈ Finset.Icc 1 n, (e * (if d ∣ k then (d : ℤ) else 0)) * u (n - k) := by
  have hnat : ∀ (m : ℕ) (base f : ℕ → ℤ), base 0 = 1 →
      (∀ n : ℕ, (n : ℤ) * base n = ∑ k ∈ Finset.Icc 1 n, f k * base (n - k)) →
      ∃ u : ℕ → ℤ, u 0 = 1 ∧ ∀ n : ℕ, (n : ℤ) * u n =
        ∑ k ∈ Finset.Icc 1 n, ((m : ℤ) * f k) * u (n - k) := by
    intro m base f hb0 hbf
    induction m with
    | zero =>
      refine ⟨fun n => if n = 0 then 1 else 0, by simp, fun n => ?_⟩
      cases n <;> simp
    | succ m ih =>
      obtain ⟨u, hu0, huf⟩ := ih
      refine ⟨conv u base, by rw [conv_zero, hu0, hb0, mul_one], fun n => ?_⟩
      have h := conv_log_deriv huf hbf n
      rw [h]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      push_cast; ring
  by_cases he : 0 ≤ e
  · obtain ⟨u, hu0, huf⟩ := hnat e.toNat (invFactor d) (fun k => if d ∣ k then (d : ℤ) else 0)
      (by simp [invFactor]) (invFactor_log_deriv d hd)
    refine ⟨u, hu0, fun n => ?_⟩
    rw [huf n, Int.toNat_of_nonneg he]
  · obtain ⟨u, hu0, huf⟩ := hnat (-e).toNat (posFactor d) (fun k => if d ∣ k then -(d : ℤ) else 0)
      (by simp [posFactor]) (posFactor_log_deriv d hd)
    refine ⟨u, hu0, fun n => ?_⟩
    rw [huf n, Int.toNat_of_nonneg (by omega)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hdk : d ∣ k <;> simp [hdk]

private lemma a_is_nat (N : ℕ) : ∃ t : ℕ, a N = (t : ℚ) := by
  let e : ℕ → ℤ := fun d => (∑ k ∈ d.divisors, (μ (d / k) : ℤ) * (2 : ℤ) ^ (k ^ 2)) / (d : ℤ)
  have he_mul : ∀ d : ℕ, 1 ≤ d → (d : ℤ) * e d = ∑ k ∈ d.divisors, (μ (d / k) : ℤ) * (2 : ℤ) ^ (k ^ 2) := by
    intro d hd
    exact Int.mul_ediv_cancel' (moebius_gauss_dvd d hd)
  -- Build integer sequence `U` with `U 0 = 1` and log-derivative `∑_{d=1}^N e(d) * (if d | k then d else 0)`.
  have hU : ∀ M : ℕ, ∃ U : ℕ → ℤ, U 0 = 1 ∧ ∀ n : ℕ, (n : ℤ) * U n =
      ∑ k ∈ Finset.Icc 1 n, (∑ d ∈ Finset.Icc 1 M, e d * (if d ∣ k then (d : ℤ) else 0)) * U (n - k) := by
    intro M
    induction M with
    | zero =>
      refine ⟨fun n => if n = 0 then 1 else 0, by simp, fun n => ?_⟩
      cases n <;> simp
    | succ M ih =>
      obtain ⟨U, hU0, hUrec⟩ := ih
      obtain ⟨V, hV0, hVrec⟩ := exists_int_seq_of_single (M + 1) (by omega) (e (M + 1))
      refine ⟨conv U V, by rw [conv_zero, hU0, hV0, mul_one], fun n => ?_⟩
      rw [conv_log_deriv hUrec hVrec n]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hIcc : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp)]
      ring
  obtain ⟨U, hU0, hUrec⟩ := hU N
  -- For `1 ≤ k ≤ N`, the log-derivative equals `2^(k^2)` by Möbius inversion!
  have hmob : ∀ k : ℕ, 1 ≤ k → k ≤ N →
      (∑ d ∈ Finset.Icc 1 N, e d * (if d ∣ k then (d : ℤ) else 0)) = (2 : ℤ) ^ (k ^ 2) := by
    intro k hk1 hkN
    have hfilt : ∑ d ∈ Finset.Icc 1 N, e d * (if d ∣ k then (d : ℤ) else 0) =
        ∑ d ∈ k.divisors, (d : ℤ) * e d := by
      have h1 : ∑ d ∈ Finset.Icc 1 N, e d * (if d ∣ k then (d : ℤ) else 0) =
          ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ k), (d : ℤ) * e d := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun d _ => by split_ifs <;> ring)
      rw [h1]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨_, _⟩, hdk⟩; exact ⟨hdk, by omega⟩
      · rintro ⟨hdk, _⟩
        have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (fun h => by subst h; simp at hdk; omega)
        have hdk_le : d ≤ k := Nat.le_of_dvd (by omega) hdk
        exact ⟨⟨hd1, le_trans hdk_le hkN⟩, hdk⟩
    rw [hfilt]
    have hsub : ∑ d ∈ k.divisors, (d : ℤ) * e d =
        ∑ d ∈ k.divisors, ∑ j ∈ d.divisors, (μ (d / j) : ℤ) * (2 : ℤ) ^ (j ^ 2) := by
      refine Finset.sum_congr rfl (fun d hd => ?_)
      have hd1 : 1 ≤ d := Nat.pos_of_ne_zero (fun h => by subst h; simp at hd)
      exact he_mul d hd1
    rw [hsub]
    have hswap : ∑ d ∈ k.divisors, ∑ j ∈ d.divisors, (μ (d / j) : ℤ) * (2 : ℤ) ^ (j ^ 2) =
        ∑ j ∈ k.divisors, (2 : ℤ) ^ (j ^ 2) * ∑ q ∈ (k / j).divisors, (μ q : ℤ) := by
      have h1 : ∀ d ∈ k.divisors, ∑ j ∈ d.divisors, (μ (d / j) : ℤ) * (2 : ℤ) ^ (j ^ 2) =
          ∑ j ∈ k.divisors, if j ∣ d then (μ (d / j) : ℤ) * (2 : ℤ) ^ (j ^ 2) else 0 := by
        intro d hd
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext j; simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨hjd, _⟩; exact ⟨⟨dvd_trans hjd (Nat.mem_divisors.mp hd).1, by omega⟩, hjd⟩
        · rintro ⟨⟨_, _⟩, hjd⟩; exact ⟨hjd, fun h => by subst h; simp at hd⟩
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hjk : j ∣ k := (Nat.mem_divisors.mp hj).1
      have hj0 : j ≠ 0 := fun h => by subst h; simp at hj
      rw [← Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_bij (fun d _ => d / j) ?_ ?_ ?_ ?_
      · intro d hd
        simp only [Finset.mem_filter, Nat.mem_divisors] at hd ⊢
        obtain ⟨q, rfl⟩ := hd.2
        obtain ⟨r, hr⟩ := hd.1.1
        refine ⟨⟨r, ?_⟩, ?_⟩
        · have : j * (q * r) = k := by linarith
          have hkjq : k / j = q * r := by rw [← this, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hj0)]
          rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hj0)]
          exact hkjq
        · intro hkj0
          have : k < j := Nat.div_eq_zero_iff.mp hkj0 |>.resolve_left hj0
          have := Nat.le_of_dvd (by omega) hjk; omega
      · intro d1 h1 d2 h2 heq
        simp only [Finset.mem_filter] at h1 h2
        rw [← Nat.div_mul_cancel h1.2, ← Nat.div_mul_cancel h2.2, heq]
      · intro q hq
        simp only [Nat.mem_divisors] at hq
        refine ⟨j * q, ?_, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hj0)⟩
        simp only [Finset.mem_filter, Nat.mem_divisors]
        refine ⟨⟨?_, by omega⟩, dvd_mul_right j q⟩
        have := mul_dvd_mul_left j hq.1
        rwa [Nat.mul_div_cancel' hjk] at this
      · intro d _
        ring
    rw [hswap]
    have hcollapse : ∀ j ∈ k.divisors,
        (2 : ℤ) ^ (j ^ 2) * (∑ q ∈ (k / j).divisors, (μ q : ℤ)) =
        if j = k then (2 : ℤ) ^ (k ^ 2) else 0 := by
      intro j hj
      have hjk : j ∣ k := (Nat.mem_divisors.mp hj).1
      have hj0 : j ≠ 0 := fun h => by subst h; simp at hj
      have hsum_mu : ∑ q ∈ (k / j).divisors, (μ q : ℤ) = if k / j = 1 then 1 else 0 := by
        have hm : ((ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) : ArithmeticFunction ℤ) (k / j) =
            (1 : ArithmeticFunction ℤ) (k / j) :=
          congr_fun (congr_arg DFunLike.coe ArithmeticFunction.moebius_mul_coe_zeta) (k / j)
        rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at hm
        rw [← hm, Nat.sum_divisorsAntidiagonal (f := fun a b => ArithmeticFunction.moebius a * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) b)]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        have hq0 : q ≠ 0 := by rintro rfl; simp at hq; omega
        have hq_le : q ≤ k / j := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (by omega) hjk) (Nat.pos_of_ne_zero hj0)) (Nat.mem_divisors.mp hq).1
        have hdiv_ne : k / j / q ≠ 0 := Nat.ne_of_gt (Nat.div_pos hq_le (Nat.pos_of_ne_zero hq0))
        simp [μ, ArithmeticFunction.zeta_apply, hdiv_ne]
      by_cases heq : j = k
      · subst heq
        rw [Nat.div_self (by omega)]
        simp [μ]
      · have hne1 : k / j ≠ 1 := by
          intro h1
          have := Nat.mul_div_cancel' hjk
          rw [h1, mul_one] at this
          exact heq this
        rw [if_neg heq, hsum_mu, if_neg hne1, mul_zero]
    rw [Finset.sum_congr rfl hcollapse, Finset.sum_ite_eq' _ k,
      if_pos (Nat.mem_divisors.mpr ⟨dvd_refl k, by omega⟩)]
  -- Show `a n = U n` for all `n ≤ N` by strong induction!
  have haU : ∀ n : ℕ, n ≤ N → a n = (U n : ℚ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hnN
      cases n with
      | zero => simp [a, hU0]
      | succ n =>
        rw [a]
        have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
        rw [div_eq_iff hn1]
        have hrec := congr_arg (Int.cast (R := ℚ)) (hUrec (n + 1))
        push_cast at hrec
        rw [mul_comm, show ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 by push_cast; rfl, hrec]
        have hIcc : Finset.Icc 1 (n + 1) = (Finset.range (n + 1)).image (· + 1) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
          constructor
          · intro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
          · rintro ⟨y, hy, rfl⟩; omega
        rw [hIcc, Finset.sum_image (fun _ _ _ _ h => by omega)]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hih := ih (n - k) (by omega) (by omega)
        have hm := congr_arg (Int.cast (R := ℚ)) (hmob (k + 1) (by omega) (by omega))
        push_cast at hm
        rw [hm, hih, show n + 1 - (k + 1) = n - k by omega]
  -- Also `a N ≥ 0` since `N! * a N = 2^N * c N ≥ 0`, so `U N ≥ 0`!
  have hU_nn : 0 ≤ U N := by
    have hfac := factorial_mul_a_eq N
    rw [haU N le_rfl] at hfac
    have hpos : (0 : ℚ) < (N.factorial : ℚ) := Nat.cast_pos.mpr (Nat.factorial_pos N)
    have hnn : (0 : ℚ) ≤ (N.factorial : ℚ) * (U N : ℚ) := by rw [hfac]; positivity
    have hU_q : (0 : ℚ) ≤ (U N : ℚ) := nonneg_of_mul_nonneg_right hnn hpos
    exact_mod_cast hU_q
  refine ⟨(U N).toNat, ?_⟩
  rw [haU N le_rfl]
  exact_mod_cast (Int.toNat_of_nonneg hU_nn).symm

private lemma prove_a155200 (n : ℕ) :
    ∃ m : ℕ, Odd m ∧ a n = ((2 ^ (Nat.digits 2 n).sum * m : ℕ) : ℚ) := by
  obtain ⟨t, ht⟩ := a_is_nat n
  obtain ⟨r, hr, hfac⟩ := legendre_two n
  have hrel_q := factorial_mul_a_eq n
  rw [ht, hfac] at hrel_q
  have hrel : 2 ^ (n - (Nat.digits 2 n).sum) * r * t = 2 ^ n * c n := by
    exact_mod_cast hrel_q
  have hle := digits_two_sum_le n
  have h2split : 2 ^ n = 2 ^ (n - (Nat.digits 2 n).sum) * 2 ^ (Nat.digits 2 n).sum := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [h2split, mul_assoc, mul_assoc] at hrel
  have hrt : r * t = 2 ^ (Nat.digits 2 n).sum * c n :=
    Nat.eq_of_mul_eq_mul_left (by positivity) hrel
  have hcop : Nat.Coprime r (2 ^ (Nat.digits 2 n).sum) := by
    have h2r : Nat.Coprime 2 r := Nat.prime_two.coprime_iff_not_dvd.mpr (fun h => by
      obtain ⟨s, hs⟩ := hr; obtain ⟨q, hq⟩ := h; omega)
    exact h2r.symm.pow_right _
  have hdvd : 2 ^ (Nat.digits 2 n).sum ∣ t :=
    hcop.symm.dvd_of_dvd_mul_left ⟨c n, hrt⟩
  obtain ⟨m, rfl⟩ := hdvd
  have hrm : r * m = c n := by
    have : 2 ^ (Nat.digits 2 n).sum * (r * m) = 2 ^ (Nat.digits 2 n).sum * c n := by
      linarith
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hm_odd : Odd m := by
    have hcodd : Odd (c n) := c_odd n
    rw [← hrm] at hcodd
    exact (Nat.odd_mul.mp hcodd).2
  exact ⟨m, hm_odd, ht⟩

end OMA.P_oeis_a155200

theorem OMA.solution : type_of% @OMA.S_oeis_a155200.main :=
  OMA.P_oeis_a155200.prove_a155200
