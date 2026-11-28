import OMAReductions.R_Erdos820_erdos_820_variants_log_log_exponent_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A lower bound for the shifted prime divisor count in Erdős 820

This reduces the shifted-prime hypothesis of @Burntgogi's merged reduction
(#7680) to a residue-one prime count and a finite primorial construction.
The count is a lower-count consequence of Proposition 8 of Adleman,
Pomerance and Rumely, *On distinguishing prime numbers from composite numbers*,
Ann. of Math. 117 (1983), 173–206. The proof below uses totient-weighted
averaging and an elementary Chebyshev bound.
-/

open Finset Filter Nat
open scoped BigOperators

namespace OMA.R_Erdos820_erdos_820_variants_log_log_exponent_R1_H1_R1

private theorem weight_identity (x k : ℕ) (hk : k ≠ 0) :
    ∑ d ∈ k.divisors, d.totient * ((primesLE x).filter fun p => d ∣ p - 1).card =
      ∑ p ∈ primesLE x, (p-1).gcd k := by
  classical
  simp_rw [card_filter, Finset.mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  simp_rw [mul_ite, mul_one, mul_zero, ← sum_filter]
  have he : k.divisors.filter (fun d => d ∣ p-1) = ((p-1).gcd k).divisors := by
    ext d
    simp [Nat.mem_divisors, hk, Nat.gcd_ne_zero_right hk, Nat.dvd_gcd_iff, and_comm]
  rw [he, Nat.sum_totient]

/-- Each prime contributes at least `gcd (p-1) k` different indices j in [1,x]. -/
private theorem gcd_le_hits {x k p : ℕ} (hp : p ∈ primesLE x) :
    (p-1).gcd k ≤ ((Icc 1 x).filter fun j => p-1 ∣ k*j).card := by
  let g := (p-1).gcd k
  have hpred : 0 < p-1 := by have := (prime_of_mem_primesLE hp).two_le; omega
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hpred
  let q := (p-1) / g
  have he : q*g = p-1 := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hq : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hh
    rw [hh, Nat.zero_mul] at he
    omega
  have hk : g ∣ k := Nat.gcd_dvd_right _ _
  have hb := Finset.card_le_card_of_injOn (s := Icc 1 g)
    (t := (Icc 1 x).filter fun j => p-1 ∣ k*j) (fun i => q*i) (by
      intro i hi
      obtain ⟨h1, h2⟩ := mem_Icc.mp hi
      apply mem_filter.mpr
      constructor
      · exact mem_Icc.mpr ⟨Nat.mul_pos hq h1,
          (Nat.mul_le_mul_left q h2).trans (he.le.trans
            ((Nat.sub_le _ _).trans (le_of_mem_primesLE hp)))⟩
      · obtain ⟨b,hb⟩ := hk
        refine ⟨b*i, ?_⟩
        rw [← he, hb]
        dsimp only
        ac_rfl) (by
      intro i _ j _ heq
      exact Nat.eq_of_mul_eq_mul_left hq heq)
  simpa [Nat.card_Icc] using hb

/-- Average the counts over `x*k*j`. The extra factor `x` makes every
witness at least `x`, which simplifies the eventual comparison of scales. -/
private theorem ap_average {x k : ℕ} (hk : 0 < k) :
    ∑ d ∈ k.divisors, d.totient * ((primesLE x).filter fun p => d ∣ p - 1).card ≤
      ∑ j ∈ Icc 1 x, ((range (x*k*j + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ x*k*j)).card := by
  classical
  rw [weight_identity _ _ hk.ne']
  calc
    _ ≤ ∑ p ∈ primesLE x, ((Icc 1 x).filter fun j => p-1 ∣ k*j).card :=
      sum_le_sum fun _ hp => gcd_le_hits hp
    _ = ∑ j ∈ Icc 1 x, ((primesLE x).filter fun p => p-1 ∣ k*j).card := by
      simp_rw [card_filter]
      exact sum_comm
    _ ≤ _ := by
      apply sum_le_sum
      intro j hj
      apply card_le_card
      intro p hp
      obtain ⟨hp,hd⟩ := mem_filter.mp hp
      have hj' := (mem_Icc.mp hj).1
      have hn : x ≤ x*k*j := by
        calc x ≤ x*k := Nat.le_mul_of_pos_right _ hk
             _ ≤ _ := Nat.le_mul_of_pos_right _ hj'
      exact mem_filter.mpr ⟨mem_range.mpr (by have := le_of_mem_primesLE hp; omega),
        prime_of_mem_primesLE hp, by simpa [Nat.mul_assoc] using dvd_mul_of_dvd_right hd x⟩

/-- A witness in a short multiplicative window with only logarithmic loss. -/
private theorem finite_transfer {x k : ℕ} (hx : 1 < x) (hk : 0 < k) (hkx : k ≤ x)
    (hAP : ∀ d ∈ k.divisors, (x : ℝ) ≤ 2 * Real.log x * (d.totient * ((primesLE x).filter fun p => d ∣ p - 1).card : ℕ)) :
    ∃ n : ℕ, x ≤ n ∧ n ≤ x^3 ∧
      (k.divisors.card : ℝ) ≤ (2 * Real.log x) * ((range (n + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ n)).card := by
  have hlog : 0 ≤ 2 * Real.log x := by positivity
  have hsum := sum_le_sum hAP
  rw [sum_const, nsmul_eq_mul, ← mul_sum] at hsum
  have hav : (∑ d ∈ k.divisors, (↑(d.totient * ((primesLE x).filter fun p => d ∣ p - 1).card) : ℝ)) ≤
      ∑ j ∈ Icc 1 x, (((range (x*k*j + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ x*k*j)).card : ℝ) := by
    exact_mod_cast ap_average hk
  have htot := hsum.trans (mul_le_mul_of_nonneg_left hav hlog)
  let J := Icc 1 x
  have hjex : ∃ j ∈ J, (k.divisors.card : ℝ) ≤ 2 * Real.log x * ((range (x*k*j + 2)).filter (fun p => p.Prime ∧ p - 1 ∣ x*k*j)).card := by
    by_contra! hall
    have hs := sum_lt_sum_of_nonempty (s := J) ⟨x, mem_Icc.mpr ⟨by omega, le_rfl⟩⟩ hall
    rw [← mul_sum, sum_const, nsmul_eq_mul] at hs
    have hcard : J.card = x := by simp [J, Nat.card_Icc]
    rw [hcard, mul_comm (x:ℝ)] at hs
    exact (not_lt_of_ge htot) hs
  obtain ⟨j,hj,h⟩ := hjex
  obtain ⟨hj1,hjx⟩ := mem_Icc.mp hj
  exact ⟨_, (Nat.le_mul_of_pos_right _ hk).trans (Nat.le_mul_of_pos_right _ hj1), by
    calc x*k*j ≤ x*x*x := Nat.mul_le_mul (Nat.mul_le_mul_left _ hkx) hjx
         _ = _ := by ring, h⟩

/-- Elementary comparison between the primorial divisor count and the target
scale. The base-4 exponential sampling is chosen to use the primorial bound. -/
private theorem compare_scales {B : ℝ} (hB : 1 ≤ B) :
    ∀ᶠ t : ℕ in atTop, ∀ x n : ℕ, Real.log x = B*t → x ≤ n → n ≤ x^3 →
      (2 * Real.log x) * (4 * (n : ℝ) ^ ((1 / (96*B)) / Real.log (Real.log n))) <
        (2:ℝ) ^ (Nat.primeCounting t - 1) := by
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (show (0:ℝ) < 1/100 by norm_num)
  have hbig := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (8*B))
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall, hbig] with t hs ht
  intro x n hx hxn hnx
  have ht1 : (4:ℝ) ≤ t := by linarith
  have ht0 : (0:ℝ) < t := by linarith
  have htlog : 1 ≤ Real.log (t:ℝ) :=
    (Real.lt_log_iff_exp_lt ht0).mpr (by linarith [Real.exp_one_lt_three]) |>.le
  have hl : 0 < Real.log (t:ℝ) := by linarith
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg (sq_nonneg (Real.log (t:ℝ))), abs_of_nonneg ht0.le] at hs
  have htwo := Real.log_two_gt_d9
  have htadd : Real.log ((t:ℝ)+1) ≤ Real.log 2 + Real.log t := by
    rw [← Real.log_mul (by norm_num) ht0.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hpi := (div_le_iff₀ hl).mp (Chebyshev.pi_ge t)
  have hpred : (Nat.primeCounting t : ℝ) ≤ ((Nat.primeCounting t - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : Nat.primeCounting t ≤ (Nat.primeCounting t - 1) + 1)
  let r : ℝ := ((Nat.primeCounting t - 1 : ℕ) : ℝ)
  have hpig : (t:ℝ)/3 ≤ r * Real.log t := by
    change (↑(Nat.primeCounting t) : ℝ) ≤ r + 1 at hpred
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
    have htwo' : (1/2 : ℝ) < Real.log 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hpred hl.le, mul_le_mul_of_nonneg_left htwo'.le ht0.le,
      mul_nonneg (sub_nonneg.mpr htlog) hl.le]
  have hxlog : 0 < Real.log (x:ℝ) := by rw [hx]; positivity
  have hx0 : (0:ℝ) < x := by
    by_contra! h
    have hh : (x:ℝ) = 0 := le_antisymm h (Nat.cast_nonneg x)
    simp [hh] at hxlog
  have hnlo : (x:ℝ) ≤ n := by exact_mod_cast hxn
  have hn0 := hx0.trans_le hnlo
  have hlogn := Real.log_le_log hx0 hnlo
  have hnup : Real.log (n:ℝ) ≤ 3 * Real.log x := by
    have he := Real.log_le_log hn0 (show (n:ℝ) ≤ (x:ℝ)^3 by exact_mod_cast hnx)
    simpa only [Real.log_pow, Nat.cast_ofNat] using he
  have hll : Real.log (t:ℝ) ≤ Real.log (Real.log n) := by
    apply Real.log_le_log ht0
    linarith [mul_le_mul_of_nonneg_right hB ht0.le]
  have hf : Real.log (n:ℝ) * ((1/(96*B)) / Real.log (Real.log n)) * Real.log t ≤ t/32 := by
    have hLL := hl.trans_le hll
    have hb : 0 < B := by linarith
    have hdiv : Real.log t / Real.log (Real.log n) ≤ 1 := (div_le_one hLL).mpr hll
    calc
      _ = (Real.log n / (96*B)) * (Real.log t / Real.log (Real.log n)) := by ring
      _ ≤ (3 * (B*t) / (96*B)) * 1 := by
        apply mul_le_mul _ hdiv (by positivity) (by positivity)
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp; ring
  have hlog8 : Real.log (8 * Real.log x) ≤ 2 * Real.log t := by
    rw [two_mul, ← Real.log_mul ht0.ne' ht0.ne', hx]
    exact Real.log_le_log (by positivity) (by nlinarith [mul_le_mul_of_nonneg_right ht ht0.le])
  have hmain : Real.log (8 * Real.log x) +
      Real.log n * ((1/(96*B)) / Real.log (Real.log n)) < r * Real.log 2 := by
    apply (mul_lt_mul_iff_left₀ hl).mp
    have hrl : 0 ≤ r * Real.log t := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hlog8 hl.le,
      mul_le_mul_of_nonneg_right (show (1/2:ℝ) ≤ Real.log 2 by linarith) hrl]
  have h := Real.exp_lt_exp.mpr hmain
  rw [Real.exp_add, Real.exp_log (by positivity), ← Real.rpow_def_of_pos hn0,
    mul_comm r, ← Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)] at h
  dsimp only [r] at h
  rw [Real.rpow_natCast] at h
  linarith only [h]

/- The first hypothesis counts primes congruent to one with a fixed exponent
and an exceptional integer for each cutoff. The second supplies a positive
modulus with many divisors and excludes multiples of that exceptional integer. -/
def H1 : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ᶠ x : ℕ in atTop, ∃ E : ℕ, 1 < E ∧
    ∀ d : ℕ, 0 < d → d^C ≤ x → ¬ E ∣ d →
      (x : ℝ) ≤ (2 * Real.log x) * (d.totient * ((primesLE x).filter fun p => d ∣ p - 1).card : ℕ)

def H2 : Prop :=
  ∀ t E : ℕ, 1 < E →
    ∃ k : ℕ, 0 < k ∧ k ≤ 4 ^ t ∧ ¬ E ∣ k ∧
      2 ^ (Nat.primeCounting t - 1) ≤ k.divisors.card

theorem main : H1 → H2 → OMA.R_Erdos820_erdos_820_variants_log_log_exponent_R1.H1 := by
  intro hAP hMod
  obtain ⟨C,hC,hAP⟩ := hAP
  let B : ℝ := C * Real.log 4
  have h4 : 1 ≤ Real.log 4 :=
    (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 4)).mpr (by linarith [Real.exp_one_lt_three]) |>.le
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hC) h4
  refine ⟨1/(96*B), by positivity, ?_⟩
  rw [frequently_atTop]
  intro N
  obtain ⟨X,hX⟩ := eventually_atTop.mp hAP
  obtain ⟨T,hT⟩ := eventually_atTop.mp (compare_scales hB)
  let t := max (max (max N X) T) 2
  have ht : N ≤ t ∧ X ≤ t ∧ T ≤ t ∧ 2 ≤ t := by dsimp [t]; omega
  let x := (4^t)^C
  have hx1 : 4^t ≤ x := le_self_pow₀ (Nat.one_le_pow t 4 (by decide)) hC.ne'
  have htx : t ≤ x := (Nat.lt_pow_self (a := 4) (by decide)).le.trans hx1
  have hx : 1 < x := by omega
  obtain ⟨E,hE,hAP'⟩ := hX x (ht.2.1.trans htx)
  obtain ⟨k,hk,hkt,hex,hcard⟩ := hMod t E hE
  obtain ⟨n,hxn,hnx,hcount⟩ := finite_transfer hx hk (hkt.trans hx1) (by
    intro d hd
    obtain ⟨hdk,_⟩ := Nat.mem_divisors.mp hd
    exact hAP' d (Nat.pos_of_mem_divisors hd) (Nat.pow_le_pow_left ((Nat.le_of_dvd hk hdk).trans hkt) C)
      (fun he => hex (he.trans hdk)))
  have hlog : Real.log (x:ℝ) = B*t := by
    simp [x, Nat.cast_pow, Real.log_pow, B, mul_comm, mul_left_comm]
  have hscale := hT t ht.2.2.1 x n hlog hxn hnx
  have hc : (2:ℝ)^(Nat.primeCounting t - 1) ≤ k.divisors.card := by exact_mod_cast hcard
  have hlogpos : 0 < 2*Real.log (x:ℝ) :=
    mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hx))
  exact ⟨n, (ht.1.trans htx).trans hxn,
    (mul_lt_mul_iff_right₀ hlogpos).mp ((hscale.trans_le hc).trans_le hcount)⟩

end OMA.R_Erdos820_erdos_820_variants_log_log_exponent_R1_H1_R1
