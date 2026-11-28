import FormalConjectures.ErdosProblems.«377»
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Kummer's criterion and a two-frequency trigonometric test for the reciprocal weight of
primes dividing a central binomial coefficient. -/

namespace OMA.Carry377
open Finset Real
open scoped BigOperators

/-- A carry in the units digit forces divisibility of the central binomial coefficient. -/
theorem units_carry {n p : ℕ} (hp : p.Prime) (h : p ≤ n % p + n % p) :
    p ∣ n.centralBinom := by
  apply Nat.dvd_of_factorization_pos
  rw [Nat.centralBinom_eq_two_mul_choose, two_mul, Nat.factorization_choose' hp
    (show Nat.log p (n+n) < Nat.log p (n+n) + 2 by omega)]
  apply (Finset.card_pos.mpr ?_).ne'
  exact ⟨1, mem_filter.mpr ⟨mem_Ico.mpr ⟨by decide, by omega⟩, by simpa using h⟩⟩


/-- A degree-two trigonometric minorant for the event that the units digit carries. -/
theorem minorant (n : ℕ) {p : ℕ} (hp : p.Prime) :
    1 - cos (2 * (2 * π * ((n % p : ℕ) : ℝ) / p)) - 2 * sin ((2 * π * ((n % p : ℕ) : ℝ) / p))
      ≤ if p ∣ n.centralBinom then (4 : ℝ) else 0 := by
  have hs := sin_le_one ((2 * π * ((n % p : ℕ) : ℝ) / p))
  have ht := neg_one_le_sin ((2 * π * ((n % p : ℕ) : ℝ) / p))
  have he := sin_sq_add_cos_sq ((2 * π * ((n % p : ℕ) : ℝ) / p))
  rw [cos_two_mul]
  split_ifs with hd
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs) (by linarith : 0 ≤ 1 + sin ((2 * π * ((n % p : ℕ) : ℝ) / p)))]
  · have low : n % p + n % p < p := lt_of_not_ge (fun h => hd (units_carry hp h))
    have castlow : ((n % p : ℕ) : ℝ) + (n % p : ℕ) < (p : ℝ) := by exact_mod_cast low
    have pp : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have bound : (2 * π * ((n % p : ℕ) : ℝ) / p) ≤ π := by
      apply (div_le_iff₀ pp).2
      nlinarith [mul_nonneg pi_pos.le (sub_nonneg.mpr castlow.le)]
    have sn := sin_nonneg_of_nonneg_of_le_pi (by positivity) bound
    nlinarith [mul_nonneg sn (sub_nonneg.mpr hs)]

/-- If the two reciprocal-prime Fourier modes are small on a band, a positive fraction
of its reciprocal weight consists of divisors. No assumptions on other prime bands. -/
theorem harmonic_loss (n : ℕ) (band : Finset ℕ) (hsub : band ⊆ n.primesLE) :
    4 * Erdos377.sumInvPrimesNotDvdCentralBinom n ≤
    4 * (∑ p ∈ n.primesLE, (1 : ℝ) / p) - (∑ p ∈ band, (1 : ℝ) / p) +
      (∑ p ∈ band, cos (2 * (2 * π * ((n % p : ℕ) : ℝ) / p)) / p) + 2 * (∑ p ∈ band, sin ((2 * π * ((n % p : ℕ) : ℝ) / p)) / p) := by
  classical
  let d (p : ℕ) : ℝ := if p ∣ n.centralBinom then (1 : ℝ) / p else 0
  have bound (p : ℕ) (hp : p ∈ band) :
      (1 : ℝ)/p - cos (2 * (2 * π * ((n % p : ℕ) : ℝ) / p))/p - 2 * (sin ((2 * π * ((n % p : ℕ) : ℝ) / p))/p) ≤ 4 * d p := by
    have prime := (Nat.mem_primesLE.mp (hsub hp)).2
    have q := div_le_div_of_nonneg_right (minorant n prime) (Nat.cast_nonneg p)
    by_cases hv : p ∣ n.centralBinom <;> simp only [d, hv, if_true, if_false, zero_div,
      mul_zero, sub_div, mul_div_assoc] at q ⊢
    · calc
        _ ≤ 4 / (p : ℝ) := q
        _ = _ := by ring
    · exact q
  have summed := sum_le_sum bound
  have extd : (∑ p ∈ band, d p) ≤ ∑ p ∈ n.primesLE, d p :=
    sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by dsimp [d]; split <;> positivity)
  have ex : ((Icc 1 n).filter Nat.Prime) = n.primesLE := by
    ext p
    simp only [mem_filter, mem_Icc, Nat.mem_primesLE]
    exact ⟨fun h => ⟨h.1.2,h.2⟩, fun h => ⟨⟨h.2.one_le,h.1⟩,h.2⟩⟩
  have split : Erdos377.sumInvPrimesNotDvdCentralBinom n + ∑ p ∈ n.primesLE, d p =
      ∑ p ∈ n.primesLE, (1 : ℝ) / p := by
    unfold Erdos377.sumInvPrimesNotDvdCentralBinom
    rw [ex, ← sum_add_distrib]
    exact sum_congr rfl (fun p _ => by by_cases hv : p ∣ n.centralBinom <;> simp [d,hv])
  simp only [sum_sub_distrib, ← mul_sum] at summed
  linarith only [summed,extd,split]

end OMA.Carry377

namespace OMA.R_Erdos377_erdos_377_variants_ub_R1
open Finset Real Filter
open scoped BigOperators Classical

/-- Mertens' estimate for reciprocal primes. -/
def H1 : Prop := ∃ C : ℝ, ∀ n : ℕ,
  |(∑ p ∈ n.primesLE, (1 : ℝ)/p) - log (log n)| ≤ C

/-- Two Fourier modes on the primes above exp((log n)^(9/10)), with reciprocal weights.
Only a one-sided bound on the indicated linear combination is needed. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop,
  let B := n.primesLE.filter (fun (p : ℕ) => (9/10 : ℝ) * log (log n) < log (log p))
  let θ := fun (p : ℕ) => 2 * π * ((n % p : ℕ) : ℝ) / p
  (∑ p ∈ B, cos (2 * θ p) / p) + 2 * (∑ p ∈ B, sin (θ p) / p) ≤ log (log n) / 50

theorem main : H1 → H2 → type_of% @Erdos377.erdos_377.variants.ub := by
  classical
  rintro ⟨C,hC⟩ hOsc
  have C0 : 0 ≤ C := (abs_nonneg _).trans (hC 1)
  refine ⟨(99/100 : ℝ), by norm_num, ?_⟩
  have growth : Tendsto (fun n : ℕ => log (log (n : ℝ))) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hOsc,growth.eventually_ge_atTop (200*C)] with n hFourier hLarge
  let L := log (log n)
  let S := n.primesLE.filter (fun (p : ℕ) => log (log p) ≤ (9/10 : ℝ)*L)
  let B := n.primesLE.filter (fun (p : ℕ) => (9/10 : ℝ)*L < log (log p))
  have small : (∑ p ∈ S, (1 : ℝ)/p) ≤ (9/10 : ℝ)*L + C := by
    by_cases hne : S.Nonempty
    · let q := S.max' hne
      have hq : q ∈ S := S.max'_mem hne
      have sub : S ⊆ q.primesLE := by
        intro p hp
        exact Nat.mem_primesLE.mpr ⟨S.le_max' _ hp, (Nat.mem_primesLE.mp
          (mem_filter.mp hp).1).2⟩
      calc
        _ ≤ ∑ p ∈ q.primesLE, (1 : ℝ)/p :=
          sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
        _ ≤ log (log q) + C := by linarith only [(abs_le.mp (hC q)).2]
        _ ≤ _ := by linarith only [(mem_filter.mp hq).2]
    · rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]
      dsimp [L]; linarith
  have total : (∑ p ∈ S, (1 : ℝ)/p) + (∑ p ∈ B, (1 : ℝ)/p) =
      ∑ p ∈ n.primesLE, (1 : ℝ)/p := by
    simpa only [S,B,not_le] using sum_filter_add_sum_filter_not
      n.primesLE (fun p => log (log p) ≤ (9/10 : ℝ)*L) (fun p => (1 : ℝ)/p)
  have loss := OMA.Carry377.harmonic_loss n B (filter_subset ..)
  change (∑ p ∈ B, cos (2 * (2 * π * ((n % p : ℕ) : ℝ) / p)) / p) +
    2 * (∑ p ∈ B, sin ((2 * π * ((n % p : ℕ) : ℝ) / p)) / p) ≤ L / 50 at hFourier
  change 200*C ≤ L at hLarge
  change Erdos377.sumInvPrimesNotDvdCentralBinom n ≤ 99 / 100 * L
  have low := (abs_le.mp (hC n)).1
  have high := (abs_le.mp (hC n)).2
  change -C ≤ _ - L at low
  change _ - L ≤ C at high
  linarith only [loss,hFourier,small,total,low,high,hLarge,C0]

end OMA.R_Erdos377_erdos_377_variants_ub_R1
