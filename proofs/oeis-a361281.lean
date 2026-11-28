import OMAStatements.S_oeis_a361281
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Tactic

/-!
The congruences were conjectured by Peter Bala on March 12, 2023 in OEIS
A361281 (OEIS Foundation, CC BY-SA 4.0).
Source: https://oeis.org/A361281/internal
Proof credit: @grp06.

The term of index n-j in the exponential contributes the factor
x^(n-j) G^(n*(n-j))/(n-j)!. After multiplication by n!, this yields the
falling factorial n!/(n-j)! times the degree-j coefficient of F times
G^(n*(n-j)). After writing G = 1 + H, only powers
H^i with i ≤ j contribute to degree j. The outer falling factorial supplies
the factor i! needed to turn the binomial coefficient into a polynomial
in the exponent. The extra terms after shifting n by k have an outer
falling-factorial factor of k.
-/

section

open Finset PowerSeries OMA.S_oeis_a361281

private theorem int_descFactorial_product (n j : ℕ) :
    (n.descFactorial j : ℤ) = ∏ r ∈ range j, ((n : ℤ) - (r : ℤ)) := by
  by_cases h : j ≤ n
  · rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro r hr
    have hrj := Finset.mem_range.mp hr
    exact Nat.cast_sub (by omega)
  · have hn : n < j := lt_of_not_ge h
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hn, Nat.cast_zero]
    exact (Finset.prod_eq_zero (Finset.mem_range.mpr hn) (sub_self (n : ℤ))).symm

private theorem zmod_descFactorial_product (k n j : ℕ) :
    (n.descFactorial j : ZMod k) = ∏ r ∈ range j, ((n : ZMod k) - (r : ZMod k)) := by
  simpa only [Int.cast_prod, Int.cast_sub, Int.cast_natCast] using
    congrArg (fun z : ℤ => (z : ZMod k)) (int_descFactorial_product n j)

private theorem descFactorial_congr (k x y j : ℕ) (h : (x : ZMod k) = (y : ZMod k)) :
    (x.descFactorial j : ZMod k) = (y.descFactorial j : ZMod k) := by
  rw [zmod_descFactorial_product, zmod_descFactorial_product, h]

private theorem weighted_choose_congr (k n j i x y : ℕ) (hi : i ≤ j)
    (h : (x : ZMod k) = (y : ZMod k)) :
    (n.descFactorial j : ZMod k) * (x.choose i : ZMod k) =
      (n.descFactorial j : ZMod k) * (y.choose i : ZMod k) := by
  obtain ⟨q, hq⟩ :=
    (Nat.factorial_dvd_factorial hi).trans (Nat.factorial_dvd_descFactorial n j)
  have factor (t : ℕ) :
      (n.descFactorial j : ZMod k) * (t.choose i : ZMod k) =
        (q : ZMod k) * (t.descFactorial i : ZMod k) := by
    rw [hq, Nat.descFactorial_eq_factorial_mul_choose t i]
    push_cast
    ring
  rw [factor x, factor y, descFactorial_congr k x y i h]

private theorem coeff_mul_pow_eq_zero (F H : PowerSeries ℤ)
    (hH : constantCoeff H = 0) {i j : ℕ} (h : j < i) :
    coeff j (F * H ^ i) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le (show (j : ℕ∞) < (i : ℕ∞) from Nat.cast_lt.mpr h) ?_
  calc
    (i : ℕ∞) ≤ (H ^ i).order := le_order_pow_of_constantCoeff_eq_zero i hH
    _ ≤ F.order + (H ^ i).order := le_add_of_nonneg_left (zero_le : 0 ≤ F.order)
    _ ≤ (F * H ^ i).order := PowerSeries.le_order_mul _ _

private theorem coeff_binomial_truncate (F H : PowerSeries ℤ)
    (hH : constantCoeff H = 0) (M j : ℕ) :
    coeff j (F * (1 + H) ^ M) =
      ∑ i ∈ range (j + 1), (M.choose i : ℤ) * coeff j (F * H ^ i) := by
  let term : ℕ → ℤ := fun i => (M.choose i : ℤ) * coeff j (F * H ^ i)
  have hexpand : coeff j (F * (1 + H) ^ M) = ∑ i ∈ range (M + 1), term i := by
    rw [add_comm 1 H, add_pow]
    simp only [one_pow, mul_one, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change coeff j (F * (H ^ i * (M.choose i : PowerSeries ℤ))) = _
    rw [← map_natCast (PowerSeries.C (R := ℤ)) (M.choose i),
      ← mul_assoc, PowerSeries.coeff_mul_C]
    exact mul_comm _ _
  rw [hexpand]
  change (∑ i ∈ range (M + 1), term i) = ∑ i ∈ range (j + 1), term i
  rcases le_total j M with h | h
  · symm
    refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ h)) ?_
    intro i _ hi
    have hji : j < i := by
      have h' : ¬ i < j + 1 := fun h' => hi (Finset.mem_range.mpr h')
      omega
    simp [term, coeff_mul_pow_eq_zero F H hH hji]
  · refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ h)) ?_
    intro i _ hi
    have hMi : M < i := by
      have h' : ¬ i < M + 1 := fun h' => hi (Finset.mem_range.mpr h')
      omega
    simp [term, Nat.choose_eq_zero_of_lt hMi]

private theorem scaled_period (F G : PowerSeries ℤ) (hG : constantCoeff G = 1)
    (n k : ℕ) :
    ((scaledCoeff F G (n + k) : ℤ) : ZMod k) =
      ((scaledCoeff F G n : ℤ) : ZMod k) := by
  let H := G - 1
  have hH : constantCoeff H = 0 := by
    simp [H, hG, PowerSeries.constantCoeff_one]
  have hGH : G = 1 + H := by
    dsimp [H]
    abel
  have hn : ((n + k : ℕ) : ZMod k) = (n : ZMod k) := by
    rw [Nat.cast_add, ZMod.natCast_self, add_zero]
  let summand : ℕ → ℕ → ZMod k := fun x j =>
    (x.descFactorial j : ZMod k) * ((coeff j (F * G ^ (x * (x - j))) : ℤ) : ZMod k)
  have hreduction (x : ℕ) :
      ((scaledCoeff F G x : ℤ) : ZMod k) = ∑ j ∈ range (x + 1), summand x j := by
    simp only [scaledCoeff, Int.cast_sum, Int.cast_mul, Int.cast_natCast, summand]
  rw [hreduction, hreduction]
  calc
    (∑ j ∈ range (n + k + 1), summand (n + k) j) =
        ∑ j ∈ range (n + 1), summand (n + k) j := by
      symm
      refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
      intro j _ hj
      have hnj : n ∈ range j := by
        apply Finset.mem_range.mpr
        have h' : ¬ j < n + 1 := fun h' => hj (Finset.mem_range.mpr h')
        omega
      have hz : ((n + k : ℕ).descFactorial j : ZMod k) = 0 := by
        rw [zmod_descFactorial_product]
        exact Finset.prod_eq_zero hnj (by rw [hn, sub_self])
      simp only [summand, hz, zero_mul]
    _ = ∑ j ∈ range (n + 1), summand n j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hjnk : j ≤ n + k := by omega
      have hM : (((n + k) * (n + k - j) : ℕ) : ZMod k) =
          ((n * (n - j) : ℕ) : ZMod k) := by
        simp only [Nat.cast_mul, Nat.cast_sub hjn, Nat.cast_sub hjnk, hn]
      simp only [summand, descFactorial_congr k (n + k) n j hn, hGH,
        coeff_binomial_truncate F H hH, Int.cast_sum, Finset.mul_sum,
        Int.cast_mul, Int.cast_natCast, ← mul_assoc]
      apply Finset.sum_congr rfl
      intro i hi
      rw [weighted_choose_congr k n j i _ _
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hM]

private theorem scaled_specialization (n : ℕ) :
    scaledCoeff (1 : PowerSeries ℤ) (1 + PowerSeries.X) n = (a n : ℤ) := by
  have hcoeff (m j : ℕ) :
      coeff j ((1 + PowerSeries.X : PowerSeries ℤ) ^ m) = (m.choose j : ℤ) := by
    have hpoly : (1 + PowerSeries.X : PowerSeries ℤ) ^ m =
        ((((1 : Polynomial ℤ) + Polynomial.X) ^ m : Polynomial ℤ) : PowerSeries ℤ) := by
      simp only [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
    rw [hpoly, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
  simp only [scaledCoeff, a, Nat.cast_sum, Nat.cast_mul, one_mul, hcoeff]

private theorem a_period (n k : ℕ) : (a (n + k) : ZMod k) = (a n : ZMod k) := by
  have h := scaled_period 1 (1 + (PowerSeries.X : PowerSeries ℤ))
    (by simp [PowerSeries.constantCoeff_one, PowerSeries.constantCoeff_X]) n k
  simpa only [scaled_specialization, Int.cast_natCast] using h

private theorem a_period_multiple (r k t : ℕ) :
    (a (r + t * k) : ZMod k) = (a r : ZMod k) := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.succ_mul, ← Nat.add_assoc, a_period, ih]

theorem OMA.solution : type_of% @OMA.S_oeis_a361281.main := by
  refine ⟨scaled_period, a_period, ?_, ?_⟩
  · intro n
    have hsmall (r : ℕ) (hr : r < 4) : (a r : ZMod 4) = 1 := by
      interval_cases r <;> decide
    have hn : n % 4 + (n / 4) * 4 = n := by
      simpa only [Nat.mul_comm (n / 4) 4] using Nat.mod_add_div n 4
    calc
      (a n : ZMod 4) = (a (n % 4 + (n / 4) * 4) : ZMod 4) :=
        congrArg (fun t : ℕ => (a t : ZMod 4)) hn.symm
      _ = (a (n % 4) : ZMod 4) := a_period_multiple _ _ _
      _ = 1 := hsmall _ (Nat.mod_lt _ (by decide))
  · intro n
    have hn : 5 * n + 2 = 2 + n * 5 := by omega
    rw [hn, a_period_multiple]
    decide

end
