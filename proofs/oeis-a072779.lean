import OMAStatements.S_oeis_a072779
import Mathlib

/-!
The divisor-sum and totient factors are multiplicative. Track their excess over
twice the square of the index while adjoining prime powers. Repeated prime
factors force an excess of at least three. For a new prime to exponent one,
the recurrence identifies both equality cases exactly.
-/

open Finset OMA.S_oeis_a072779

private def sigU (n : ℕ) : ℤ := sigma 2 n
private def sigV (n : ℕ) : ℤ := (n.totient : ℤ) * sigma 1 n
private def sigD (n : ℕ) : ℤ := sigU n + sigV n - 2 * (n : ℤ)^2

private lemma sigma_mul {k n m : ℕ} (h : n.Coprime m) :
    sigma k (n*m) = sigma k n * sigma k m := by
  change ArithmeticFunction.sigma k (n*m) = ArithmeticFunction.sigma k n * ArithmeticFunction.sigma k m
  exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

private lemma sigU_mul {n m : ℕ} (h : n.Coprime m) : sigU (n*m) = sigU n * sigU m := by
  unfold sigU
  exact_mod_cast sigma_mul h

private lemma sigV_mul {n m : ℕ} (h : n.Coprime m) : sigV (n*m) = sigV n * sigV m := by
  unfold sigV
  rw [Nat.totient_mul h, sigma_mul h]
  push_cast
  ring

private lemma sigU_pos (n : ℕ) (hn : 0 < n) : 0 < sigU n := by
  change (0 : ℤ) < (ArithmeticFunction.sigma 2 n : ℕ)
  positivity

namespace A072779Power

lemma factor (p e : ℕ) (hp : p.Prime) (he : 0 < e) :
    ∃ b c : ℕ, sigma 2 (p^e) = (p^e)^2+b ∧
      (p^e).totient * sigma 1 (p^e) + c = (p^e)^2 ∧
      0 < c ∧ c ≤ b ∧ (e=1 → b=1 ∧ c=1) ∧ (2≤e → c+3≤b) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  let b := ∑ j ∈ range (k+1), p^(j*2)
  have sq : sigma 2 (p^(k+1)) = (p^(k+1))^2+b := by
    change ArithmeticFunction.sigma 2 (p^(k+1)) = _
    rw [ArithmeticFunction.sigma_apply_prime_pow hp, sum_range_succ, pow_mul]
    exact Nat.add_comm _ _
  have tot : (p^(k+1)).totient * sigma 1 (p^(k+1)) + p^k = (p^(k+1))^2 := by
    change (p^(k+1)).totient * ArithmeticFunction.sigma 1 (p^(k+1)) + p^k = _
    rw [Nat.totient_prime_pow_succ hp, ArithmeticFunction.sigma_one_apply_prime_pow hp]
    have geom := geom_sum_mul_add (p-1) (k+2)
    rw [Nat.sub_add_cancel hp.one_lt.le] at geom
    calc
      _ = p^k * ((∑ j ∈ range (k+2), p^j) * (p-1) + 1) := by ring
      _ = p^k * p^(k+2) := by rw [geom]
      _ = _ := by simp only [pow_succ]; ring
  have one (h : k + 1 = 1) : b = 1 ∧ p^k = 1 := by
    have hk : k = 0 := by omega
    simp [b, hk]
  have big (hk : 2 ≤ k+1) : p^k+3 ≤ b := by
    have low : 1 ≤ ∑ j ∈ range k, p^(j*2) := by
      have h := single_le_sum (f := fun j => p^(j*2)) (fun _ _ => Nat.zero_le _)
        (mem_range.mpr (by omega : 0 < k))
      simpa using h
    have hc : 2 ≤ p^k :=
      hp.two_le.trans (le_self_pow₀ hp.one_lt.le (by omega))
    have twice := Nat.mul_le_mul_right (p^k) hc
    dsimp only [b]
    rw [sum_range_succ, pow_mul]
    nlinarith
  refine ⟨b, p^k, sq, tot, pow_pos hp.pos _, ?_, one, big⟩
  by_cases h : k+1 = 1
  · simp [(one h).1, (one h).2]
  · have hbound := big (by omega)
    omega

end A072779Power

lemma oma_sigma_gap_step {U V W u b c : ℤ} (hU : 0 < U) (hV : 0 ≤ V)
    (hUV : V ≤ U) (hu : 0 < u) (hc : 1 ≤ c) (hb : c ≤ b) :
    (u-c)*V ≤ (u+b)*U ∧
    u*(U+V-2*W) + (b-c) + (U-V) ≤ (u+b)*U + (u-c)*V - 2*(u*W) := by
  constructor
  · nlinarith only [mul_nonneg hu.le (sub_nonneg.mpr hUV),
      mul_nonneg (show 0 ≤ b by omega) hU.le,
      mul_nonneg (show 0 ≤ c by omega) hV]
  · nlinarith only [mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ U-1 by omega),
      mul_nonneg (show 0 ≤ c-1 by omega) (sub_nonneg.mpr hUV)]

lemma oma_sigma_gap_one (U V W u : ℤ) :
    (u+1)*U + (u-1)*V - 2*(u*W) = u*(U+V-2*W) + (U-V) := by
  ring

lemma oma_sigma_prime_class {m p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    (m * p^e).Prime ↔ m = 1 ∧ e = 1 := by
  constructor
  · intro h
    rcases Nat.prime_mul_iff.mp h with ⟨_,hpow⟩ | ⟨hpow,hm⟩
    · have lt : 1 < p^e := one_lt_pow₀ hp.one_lt (by omega)
      omega
    · exact ⟨hm,(hpow.pow_eq_iff.mp (rfl : p^e = p^e)).2⟩
  · rintro ⟨rfl,rfl⟩
    simpa using hp

lemma oma_sigma_distinct_class {m p e : ℕ} (hp : p.Prime) (he : 0 < e) (hc : m.Coprime p) :
    IsProductOfTwoDistinctPrimes (m * p^e) ↔ m.Prime ∧ e = 1 := by
  constructor
  · rintro ⟨u,v,hu,hv,hne,heq⟩
    obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
    rw [pow_succ,←mul_assoc] at heq
    have hdiv : p ∣ u*v := heq ▸ dvd_mul_left p _
    have tail (q : ℕ) (hq : q.Prime) (hne' : p ≠ q) (h : m*p^d = q) :
        m.Prime ∧ d+1 = 1 := by
      cases d with
      | zero =>
        have hm : m = q := by simpa using h
        simpa [hm] using hq
      | succ d =>
        have hpq : p ∣ q := by
          rw [←h,pow_succ,←mul_assoc]
          exact dvd_mul_left p _
        exact False.elim (hne' ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpq))
    rcases hp.dvd_mul.mp hdiv with hpu | hpv
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hu).mp hpu
      exact tail v hv hne (Nat.eq_of_mul_eq_mul_right hp.pos (by simpa [mul_comm p v] using heq))
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hv).mp hpv
      exact tail u hu hne.symm (Nat.eq_of_mul_eq_mul_right hp.pos heq)
  · rintro ⟨hm,rfl⟩
    refine ⟨m,p,hm,hp,?_,by simp⟩
    rintro rfl
    exact hm.ne_one (by simpa using hc)

private def sigmaInvariant (n : ℕ) : Prop :=
  sigV n ≤ sigU n ∧ 0 ≤ sigD n ∧ (sigD n = 0 ↔ n = 1 ∨ n.Prime) ∧
    (sigD n = 2 ↔ IsProductOfTwoDistinctPrimes n)

private lemma sigma_induction
    (oneDiff : sigU 1 - sigV 1 = 0)
    (primeDiff : ∀ p : ℕ, p.Prime → sigU p - sigV p = 2) :
    ∀ n, 0 < n → sigmaInvariant n := by
  apply Nat.recOnPrimePow
  · omega
  · intro _
    have hnp : ¬ IsProductOfTwoDistinctPrimes 1 := by
      rintro ⟨p, q, hp, hq, hne, hprod⟩
      have hp2 := hp.two_le
      have hq2 := hq.two_le
      nlinarith
    norm_num [sigmaInvariant, sigD, sigU, sigV, sigma, hnp]
  intro m p e hp hpm he ih hpos
  have hm : 0 < m := Nat.pos_of_ne_zero (fun h => hpm (h ▸ dvd_zero _))
  obtain ⟨hUV,hD,hD0,_⟩ := ih hm
  have hcop : m.Coprime p := (hp.coprime_iff_not_dvd.mpr hpm).symm
  have hcpe : m.Coprime (p^e) := hcop.pow_right _
  rw [mul_comm] at hpos ⊢
  obtain ⟨b,c,hb,hc,hcpos,hbc,heone,hebig⟩ := A072779Power.factor p e hp he
  let u : ℤ := ((p^e : ℕ) : ℤ)^2
  have hUfac : sigU (p^e) = u + b := by
    dsimp [sigU, u]
    exact_mod_cast hb
  have hVfac : sigV (p^e) = u - c := by
    have h' : sigV (p^e) + c = u := by
      dsimp [sigV, u]
      exact_mod_cast hc
    omega
  have hUeq := (sigU_mul hcpe).trans (show sigU m * sigU (p^e) = (u+b)*sigU m by rw [hUfac, mul_comm])
  have hVeq := (sigV_mul hcpe).trans (show sigV m * sigV (p^e) = (u-c)*sigV m by rw [hVfac, mul_comm])
  have hDeq : sigD (m*p^e) = (u+b)*sigU m + (u-c)*sigV m - 2*(u*(m:ℤ)^2) := by
    unfold sigD
    rw [hUeq,hVeq]
    simp only [Nat.cast_mul, Nat.cast_pow, u]
    ring
  have hpow : 1 < p^e := one_lt_pow₀ hp.one_lt he.ne'
  have hu4 : (4:ℤ) ≤ u := by
    have hh : (2:ℤ) ≤ ((p^e:ℕ):ℤ) := by exact_mod_cast hpow
    dsimp [u]
    nlinarith
  have hVm : 0 ≤ sigV m := by unfold sigV; positivity
  obtain ⟨hUV',hD'⟩ := oma_sigma_gap_step (W:=(m:ℤ)^2) (b:=(b:ℤ)) (c:=(c:ℤ))
    (sigU_pos m hm) hVm hUV (by omega : 0 < u) (by exact_mod_cast hcpos) (by exact_mod_cast hbc)
  change u * sigD m + ((b:ℤ)-c) + (sigU m-sigV m) ≤ _ at hD'
  rw [← hDeq] at hD'
  have hprod := mul_nonneg (by omega : 0 ≤ u) hD
  have hn1 : m*p^e ≠ 1 := by
    have hle := Nat.le_mul_of_pos_left (p^e) hm
    omega
  refine ⟨by rwa [hUeq,hVeq], by omega, ?_⟩
  rw [oma_sigma_prime_class hp he, oma_sigma_distinct_class hp he hcop]
  simp only [hn1, false_or]
  by_cases he1 : e = 1
  · obtain ⟨rfl,rfl⟩ := heone he1
    have hrec : sigD (m*p^e) = u*sigD m + (sigU m - sigV m) := by
      simpa only [Nat.cast_one, sigD] using hDeq.trans (oma_sigma_gap_one _ _ _ _)
    simp only [he1, and_true] at hrec ⊢
    by_cases hm1 : m = 1
    · have hdz := hD0.mpr (Or.inl hm1)
      subst m
      rw [hdz,mul_zero,zero_add,oneDiff] at hrec
      rw [hrec]
      norm_num
    by_cases hprime : m.Prime
    · have hdz := hD0.mpr (Or.inr hprime)
      rw [hdz,mul_zero,zero_add,primeDiff m hprime] at hrec
      rw [hrec]
      simp [hm1,hprime]
    · have hne : sigD m ≠ 0 := fun h => (hD0.mp h).elim hm1 hprime
      have hmul := mul_le_mul_of_nonneg_left (show (1:ℤ) ≤ sigD m by omega) (show 0 ≤ u by omega)
      simp only [mul_one] at hmul
      simp only [hm1,hprime,iff_false]
      omega
  · have hb3 := hebig (by omega)
    have hb3z : (c:ℤ) + 3 ≤ b := by exact_mod_cast hb3
    simp only [he1, and_false, iff_false]
    omega

private lemma sig_diff_one : sigU 1 - sigV 1 = 0 := by
  simp [sigU, sigV, sigma]

private lemma sig_diff_prime {p : ℕ} (hp : p.Prime) : sigU p - sigV p = 2 := by
  have divs : p.divisors = {1,p} := by
    ext x
    simp [Nat.mem_divisors, hp.ne_zero, Nat.dvd_prime hp]
  simp [sigU, sigV, sigma, divs, hp.ne_one.symm, Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  ring

private lemma oma_sigma_finish
    (inv : ∀ n : ℕ, 0 < n → sigV n ≤ sigU n ∧ 0 ≤ sigD n ∧
      (sigD n = 0 ↔ n = 1 ∨ n.Prime) ∧
      (sigD n = 2 ↔ IsProductOfTwoDistinctPrimes n)) :
    type_of% @OMA.S_oeis_a072779.main := by
  have gap (n : ℕ) : sigD n = (a n : ℤ) - ((2*n^2 : ℕ) : ℤ) := by
    simp [sigD,sigU,sigV,a]
  constructor
  · intro n hn
    obtain ⟨_,hpos,hzero,_⟩ := inv n hn
    rw [gap] at hpos hzero
    refine ⟨by omega,?_⟩
    exact (show a n = 2*n^2 ↔ (a n : ℤ) - ((2*n^2 : ℕ) : ℤ) = 0 by omega).trans hzero
  · intro n hn
    have htwo := (inv n hn).2.2.2
    rw [gap] at htwo
    exact (show a n = 2+2*n^2 ↔ (a n : ℤ) - ((2*n^2 : ℕ) : ℤ) = 2 by omega).trans htwo

theorem OMA.solution : type_of% @OMA.S_oeis_a072779.main :=
  oma_sigma_finish (sigma_induction sig_diff_one (fun _ => sig_diff_prime))
