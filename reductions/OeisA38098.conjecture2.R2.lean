import FormalConjectures.OEIS.«38098»
import Mathlib.NumberTheory.Chebyshev

/-!
Zhi-Wei Sun's conjecture about the ratios π(n²)/n², https://oeis.org/A038098.

An exact separating ratio at 15648 means that strict decrease controls all
comparisons past the finite prefix. Among the finite pairs, a collision is
possible only at noncoprime indices. An explicit Chebyshev estimate further
confines collisions at each fixed index gap to a finite range. For the tail,
strict decrease is equivalent to a non-strict integer quota for primes
between the two consecutive squares.
-/

namespace A38098Gcd

/-- Equality of the prime-count ratios imposes divisibility by the square of
an index after removing the indices' common factor. -/
theorem denominator_dvd (m n : ℕ) (hm : 0 < m)
    (equal : (m^2).primeCounting*n^2 = (n^2).primeCounting*m^2) :
    (n/m.gcd n)^2 ∣ (n^2).primeCounting := by
  let g := m.gcd n
  have hg : 0 < g := Nat.gcd_pos_of_pos_left n hm
  have divided_m : (m/g)*g = m := Nat.div_mul_cancel (Nat.gcd_dvd_left m n)
  have divided_n : (n/g)*g = n := Nat.div_mul_cancel (Nat.gcd_dvd_right m n)
  have equal' : (m^2).primeCounting*(n/g)^2 = (n^2).primeCounting*(m/g)^2 := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hg 2)
    calc
      _ = (m^2).primeCounting*((n/g)*g)^2 := by ring
      _ = (m^2).primeCounting*n^2 := by rw [divided_n]
      _ = (n^2).primeCounting*m^2 := equal
      _ = (n^2).primeCounting*((m/g)*g)^2 := by rw [divided_m]
      _ = _ := by ring
  have cop : (n/g).Coprime (m/g) := (Nat.coprime_div_gcd_div_gcd hg).symm
  have cP : ((n/g)^2).Coprime ((m/g)^2) := cop.pow 2 2
  apply cP.dvd_of_dvd_mul_right
  simpa only [← equal'] using dvd_mul_left ((n/g)^2) (m^2).primeCounting

private theorem pi_lt (x : ℕ) (hx : 0 < x) : x.primeCounting < x := by
  rw [← Nat.primesLE_card_eq_primeCounting, Nat.primesLE_eq_filter_Ioc_one]
  exact (Finset.card_filter_le _ _).trans_lt (by simp; omega)

/-- Two distinct coprime indices have unequal ratios. -/
theorem coprime_ne (m n : ℕ) (hm : 0 < m) (hn : 2 ≤ n) (hc : m.Coprime n) :
    (m^2).primeCounting*n^2 ≠ (n^2).primeCounting*m^2 := by
  intro equal
  have hdiv := denominator_dvd m n hm equal
  rw [hc.gcd_eq_one, Nat.div_one] at hdiv
  have hpos : 0 < (n^2).primeCounting := by
    apply Nat.pos_of_ne_zero
    rw [ne_eq, Nat.primeCounting_eq_zero_iff]
    nlinarith
  exact (pi_lt _ (by positivity)).not_ge (Nat.le_of_dvd hpos hdiv)

open Real in
/-- An explicit Chebyshev bound with the integer base-two logarithm. -/
theorem pi_mul_natLog_le (x : ℕ) : x.primeCounting * Nat.log 2 x ≤ 8*x := by
  by_cases hx : 1 < x
  · have hxr : (1 : ℝ) < x := by exact_mod_cast hx
    have hpos := Real.log_pos hxr
    have htwo : (1/2 : ℝ) ≤ log 2 := by linarith [Real.log_two_gt_d9]
    have hlog4 : log 4 = 2*log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
      norm_num
    have hsqrt := Real.sqrt_nonneg (x:ℝ)
    have hspos := Real.sqrt_pos.2 (lt_trans zero_lt_one hxr)
    have hsq := Real.sq_sqrt (Nat.cast_nonneg x : (0:ℝ) ≤ x)
    have hl := Real.log_le_sub_one_of_pos hspos
    rw [Real.log_sqrt (Nat.cast_nonneg x)] at hl
    have hs : log x * √(x:ℝ) ≤ 2*x := by
      nlinarith [mul_le_mul_of_nonneg_right hl hsqrt]
    have h := Chebyshev.pi_le_log4_mul_div (x := (x:ℝ)) hxr
    rw [Nat.floor_natCast, Real.log_sqrt (Nat.cast_nonneg x), hlog4] at h
    have h' := (le_div_iff₀ (half_pos hpos)).mp
      (by linarith : (x.primeCounting : ℝ) - √(x:ℝ) ≤ 2*log 2*x/(log x/2))
    have hp : (x.primeCounting : ℝ) * log x ≤ (8*x) * log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg x : (0:ℝ) ≤ x)]
    have hlog := Real.natLog_le_logb x 2
    rw [Real.logb, Nat.cast_ofNat] at hlog
    have hlog' := (le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp hlog
    have hfinal : (x.primeCounting : ℝ) * (Nat.log 2 x : ℝ) ≤ 8*x := by
      apply le_of_mul_le_mul_right _ (Real.log_pos (by norm_num : (1:ℝ) < 2))
      calc
        (x.primeCounting : ℝ) * (Nat.log 2 x : ℝ) * log 2 =
            x.primeCounting * ((Nat.log 2 x : ℝ) * log 2) := by ring
        _ ≤ x.primeCounting * log x := mul_le_mul_of_nonneg_left hlog' (Nat.cast_nonneg _)
        _ ≤ _ := hp
    exact_mod_cast hfinal
  · interval_cases x <;> decide

/-- In a collision, the square of the greatest common divisor controls the
logarithm of the larger index. -/
theorem collision_log (m n : ℕ) (hm : 0 < m) (hn : 2 ≤ n)
    (equal : (m^2).primeCounting*n^2 = (n^2).primeCounting*m^2) :
    Nat.log 2 (n^2) ≤ 8*(m.gcd n)^2 := by
  let g := m.gcd n
  have hpos : 0 < (n^2).primeCounting := by
    apply Nat.pos_of_ne_zero
    rw [ne_eq,Nat.primeCounting_eq_zero_iff]
    nlinarith
  have hdiv : (n/g)^2 ≤ (n^2).primeCounting := Nat.le_of_dvd hpos (denominator_dvd m n hm equal)
  have hnSq : n^2 = (n/g)^2*g^2 := by
    rw [← mul_pow, Nat.div_mul_cancel (Nat.gcd_dvd_right m n)]
  have hc : n^2 ≤ (n^2).primeCounting*g^2 := by
    nth_rw 1 [hnSq]
    exact Nat.mul_le_mul_right _ hdiv
  have hlog := pi_mul_natLog_le (n^2)
  have hcancel : n^2 * Nat.log 2 (n^2) ≤ n^2 * (8*g^2) := by
    calc
      _ ≤ ((n^2).primeCounting*g^2)*Nat.log 2 (n^2) := Nat.mul_le_mul_right _ hc
      _ = ((n^2).primeCounting*Nat.log 2 (n^2))*g^2 := by ring
      _ ≤ (8*n^2)*g^2 := Nat.mul_le_mul_right _ hlog
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hcancel (by positivity)

/-- Each fixed index gap has only finitely many possible collisions. -/
theorem collision_gap (m n : ℕ) (hm : 0 < m) (hmn : m < n)
    (equal : (m^2).primeCounting*n^2 = (n^2).primeCounting*m^2) :
    n < 2^(4*(n-m)^2+1) := by
  have lg := collision_log m n hm (by omega) equal
  have hg : m.gcd n ≤ n-m := Nat.le_of_dvd (by omega)
    (Nat.dvd_sub (Nat.gcd_dvd_right m n) (Nat.gcd_dvd_left m n))
  have bound : n^2 < 2^(8*(n-m)^2+1) := by
    have hlog := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n^2)
    exact hlog.trans_le (Nat.pow_le_pow_right (by decide)
      (Nat.succ_le_succ (lg.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hg _)))))
  by_contra! h
  have hs := Nat.pow_le_pow_left h 2
  rw [← pow_mul] at hs
  have hh : (2:ℕ)^(8*(n-m)^2+1) ≤ 2^((4*(n-m)^2+1)*2) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact bound.not_ge (hh.trans hs)

end A38098Gcd

/- A finite initial certificate and strict tail decrease imply global injectivity
of Sun's prime-density ratios at squares.  The cross products in the certificate
are natural numbers. -/

namespace A038098Prefix

/-- Extend strict one-step decrease to every pair of indices after the cutoff. -/
theorem tail_compare {R : ℕ → ℚ} {T : ℕ} (tail : ∀ n, T < n → R (n+1) < R n)
    {m n : ℕ} (hm : T < m) (hmn : m < n) : R n < R m := by
  have step : StrictAnti (fun i : ℕ => R (T+1+i)) := strictAnti_nat_of_succ_lt
    (fun i => by simpa only [← Nat.add_assoc] using tail (T+1+i) (by omega))
  have h := step (show m-(T+1) < n-(T+1) by omega)
  simpa only [show T+1+(n-(T+1)) = n by omega, show T+1+(m-(T+1)) = m by omega] using h

/-- It suffices to separate the finitely many early pairs and place the anchor K
below every positive early ratio.  Index 1 has ratio zero and separates itself. -/
theorem injective_of_prefix (T K : ℕ) (hK : T < K)
    (finitePairs : ∀ m n : ℕ, 2 ≤ m → m ≤ T → m < n → n < K →
      (m^2).primeCounting * n^2 ≠ (n^2).primeCounting * m^2)
    (anchor : ∀ m : ℕ, 2 ≤ m → m ≤ T →
      (K^2).primeCounting * m^2 < (m^2).primeCounting * K^2)
    (tail : ∀ n : ℕ, T < n →
      ((n+1)^2).primeCounting / ((n+1 : ℚ)^2) < (n^2).primeCounting / (n : ℚ)^2) :
    ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (m^2).primeCounting / (m : ℚ)^2 = (n^2).primeCounting / (n : ℚ)^2 → m = n := by
  let R (a : ℕ) : ℚ := (a^2).primeCounting / (a : ℚ)^2
  have drop (a : ℕ) (ha : T < a) : R (a+1) < R a := by
    simpa only [R,Nat.cast_add,Nat.cast_one] using tail a ha
  have denom {a : ℕ} (ha : 0 < a) : (0 : ℚ) < (a:ℚ)^2 := by positivity
  have zero : R 1 = 0 := by norm_num [R]
  have positive (n : ℕ) (hn : 2 ≤ n) : 0 < R n := by
    have hp : 0 < (n^2).primeCounting := by
      apply Nat.pos_of_ne_zero
      intro hz
      have := Nat.primeCounting_eq_zero_iff.mp hz
      nlinarith
    exact div_pos (by exact_mod_cast hp) (denom (by omega))
  have sep {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) : R m ≠ R n := by
    by_cases h1 : m = 1
    · subst m
      rw [zero]
      exact (positive n (by omega)).ne
    by_cases hmt : T < m
    · exact (tail_compare drop hmt hmn).ne'
    have hm2 : 2 ≤ m := by omega
    by_cases hnK : n < K
    · intro eq
      have h := (div_eq_div_iff (denom (by omega : 0 < m)).ne' (denom (by omega : 0 < n)).ne').mp eq
      exact finitePairs m n hm2 (by omega) hmn hnK (by exact_mod_cast h)
    have ha : R K < R m := by
      apply (div_lt_div_iff₀ (denom (by omega : 0 < K)) (denom (by omega : 0 < m))).mpr
      exact_mod_cast anchor m hm2 (by omega)
    have hle : R n ≤ R K := by
      rcases eq_or_lt_of_le (le_of_not_gt hnK) with rfl | h
      · exact le_rfl
      · exact (tail_compare drop hK h).le
    exact (hle.trans_lt ha).ne'
  intro m n hm hn eq
  rcases lt_trichotomy m n with h | h | h
  · exact (sep hm h eq).elim
  · exact h
  · exact (sep hn h eq.symm).elim

end A038098Prefix

/- Distinctness for coprime indices, and an exact non-strict prime-count quota for
strict decrease over consecutive squares. -/

namespace A038098Prefix

open Finset

theorem square_gap_count (n : ℕ) :
    (n^2).primeCounting + ((Ioc (n^2) ((n+1)^2)).filter Nat.Prime).card =
      ((n+1)^2).primeCounting := by
  have hle : n^2 ≤ (n+1)^2 := Nat.pow_le_pow_left (by omega) _
  have hdiff : Nat.primesLE ((n+1)^2) \ Nat.primesLE (n^2) =
      (Ioc (n^2) ((n+1)^2)).filter Nat.Prime := by
    ext a
    simp only [mem_sdiff,Nat.mem_primesLE,mem_filter,mem_Ioc]
    grind
  rw [← Nat.primesLE_card_eq_primeCounting,← Nat.primesLE_card_eq_primeCounting,← hdiff,add_comm]
  exact card_sdiff_add_card_eq_card (Nat.primesLE_mono hle)

theorem local_nonincrease_iff (n : ℕ) (hn : 2 ≤ n) :
    (((n+1)^2).primeCounting / ((n+1 : ℚ)^2) < (n^2).primeCounting / (n : ℚ)^2) ↔
      ((Ioc (n^2) ((n+1)^2)).filter Nat.Prime).card * n^2 ≤
        (2*n+1) * (n^2).primeCounting := by
  have dn : 0 < (n:ℚ)^2 := by positivity
  have ds : 0 < (n+1:ℚ)^2 := by positivity
  rw [div_lt_div_iff₀ ds dn]
  have convert : ((((n+1)^2).primeCounting : ℚ) * (n:ℚ)^2 <
      ((n^2).primeCounting : ℚ) * (n+1:ℚ)^2) ↔
      ((n+1)^2).primeCounting * n^2 < (n^2).primeCounting * (n+1)^2 := by norm_cast
  rw [convert]
  have unequal := A38098Gcd.coprime_ne n (n+1) (by omega) (by omega) (by simp)
  have gap := square_gap_count n
  let d := ((Ioc (n^2) ((n+1)^2)).filter Nat.Prime).card
  change (n^2).primeCounting + d = ((n+1)^2).primeCounting at gap
  change _ ↔ d * n^2 ≤ _
  have identity : ((n+1)^2).primeCounting*n^2 + (2*n+1)*(n^2).primeCounting =
      (n^2).primeCounting*(n+1)^2 + d*n^2 := by
    rw [←gap]
    ring
  omega

end A038098Prefix

namespace OMA.R_OeisA38098_conjecture2_R2

/-- Check the remaining potentially equal ratios in the finite prefix. -/
def H1 : Prop :=
  ∀ m n : ℕ, 2 ≤ m → m ≤ 15646 → m < n → n < 15648 → ¬ m.Coprime n →
    (m^2).primeCounting*n^2 ≠ (n^2).primeCounting*m^2

/-- Separate all positive early ratios from the decreasing tail. -/
def H2 : Prop :=
  ∀ m : ℕ, 2 ≤ m → m ≤ 15646 →
    (15648^2 : ℕ).primeCounting*m^2 < (m^2).primeCounting*15648^2

/-- A non-strict integer quota for the primes between consecutive squares. -/
def H3 : Prop :=
  ∀ n : ℕ, 15646 < n →
    ((Finset.Ioc (n^2) ((n+1)^2)).filter Nat.Prime).card*n^2 ≤
      (2*n+1)*(n^2).primeCounting

theorem main : H1 → H2 → H3 → type_of% @OeisA38098.conjecture2 := by
  intro finite anchor quota
  have drop (n : ℕ) (hn : 15646 < n) :
      ((n+1)^2).primeCounting / ((n+1 : ℚ)^2) < (n^2).primeCounting / (n : ℚ)^2 :=
    (A038098Prefix.local_nonincrease_iff n (by omega)).mpr (quota n hn)
  refine ⟨A038098Prefix.injective_of_prefix 15646 15648 (by decide) ?_ anchor drop, drop⟩
  intro m n hm ht hmn hnk
  by_cases cop : m.Coprime n
  · exact A38098Gcd.coprime_ne m n (by omega) (by omega) cop
  · exact finite m n hm ht hmn hnk cop

end OMA.R_OeisA38098_conjecture2_R2
