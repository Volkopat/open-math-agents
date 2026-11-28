import OMAStatements.S_oeis_a211438
import Mathlib

/-!
# A211438: triples (w,x,y) in {-n,...,n}^3 with w + 2x + 2y = 0

Write S(n) for {-n, ..., n} and m = floor(n/2). A solution is fixed by x, y and w = -2(x + y),
and w lies in S(n) exactly when |x + y| ≤ m. Sort the solutions by s = x + y. For 0 ≤ s ≤ m the
solutions with x + y = s are (-2s, x, s - x) with s - n ≤ x ≤ n, so there are 2n + 1 - s of
them; for -m ≤ s ≤ 0 they are those with -n ≤ x ≤ s + n, so there are 2n + 1 + s of them.
Summing, a(n) = (2m + 1)(2n + 1) - m(m + 1), which is the closed form for n = 2m and for
n = 2m + 1. The denominator (1 - x)^3 (1 + x)^2 expands to 1 - x - 2x^2 + 2x^3 + x^4 - x^5; the
coefficients of degree at most 4 are checked from a(0), ..., a(4), and from degree 5 on the
coefficient vanishes by the closed form.
-/

namespace OMA.P211438

open OMA.S_oeis_a211438 PowerSeries

/-- The interval {-n, ..., n}. -/
noncomputable abbrev S (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ)) n

/-- The solutions in S(n)^3. -/
noncomputable abbrev T (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (S n ×ˢ S n ×ˢ S n).filter (fun t : ℤ × ℤ × ℤ => t.1 + 2 * t.2.1 + 2 * t.2.2 = 0)

/-- The solutions with x + y = s. -/
noncomputable abbrev fib (n : ℕ) (s : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (T n).filter (fun t => t.2.1 + t.2.2 = s)

lemma fib_nonneg (n : ℕ) (s : ℤ) (h0 : 0 ≤ s) (h1 : 2 * s ≤ n) :
    ((fib n s).card : ℤ) = 2 * n + 1 - s := by
  have hc : (Finset.Icc (s - n) (n : ℤ)).card = (fib n s).card := by
    apply Finset.card_nbij' (fun x => (-2 * s, x, s - x)) (fun t => t.2.1)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_Icc, Finset.mem_filter, Finset.mem_product] at hx ⊢
      omega
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_Icc, Finset.mem_filter, Finset.mem_product] at ht ⊢
      omega
    · intro x hx
      simp
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_Icc, Finset.mem_filter, Finset.mem_product] at ht
      ext <;> simp <;> omega
  rw [← hc, Int.card_Icc]
  omega

lemma fib_nonpos (n : ℕ) (s : ℤ) (h0 : s ≤ 0) (h1 : -(n : ℤ) ≤ 2 * s) :
    ((fib n s).card : ℤ) = 2 * n + 1 + s := by
  have hc : (Finset.Icc (-(n : ℤ)) (s + n)).card = (fib n s).card := by
    apply Finset.card_nbij' (fun x => (-2 * s, x, s - x)) (fun t => t.2.1)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_Icc, Finset.mem_filter, Finset.mem_product] at hx ⊢
      omega
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_Icc, Finset.mem_filter, Finset.mem_product] at ht ⊢
      omega
    · intro x hx
      simp
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_Icc, Finset.mem_filter, Finset.mem_product] at ht
      ext <;> simp <;> omega
  rw [← hc, Int.card_Icc]
  omega

/-- Sorting the solutions by s = x + y, with |s| ≤ floor(n/2). -/
lemma a_eq_sum (n : ℕ) :
    a n = ∑ s ∈ Finset.Icc (-((n / 2 : ℕ) : ℤ)) ((n / 2 : ℕ) : ℤ), (fib n s).card := by
  unfold a
  apply Finset.card_eq_sum_card_fiberwise
  intro t ht
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ht ⊢
  omega

lemma sum_fib (n k : ℕ) (hk : 2 * k ≤ n) :
    (∑ s ∈ Finset.Icc (-(k : ℤ)) k, ((fib n s).card : ℤ)) =
      (2 * k + 1) * (2 * n + 1) - k * (k + 1) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton]
    rw [fib_nonneg n 0 le_rfl (by simp)]
    ring
  | succ k ih =>
    have hsplit : Finset.Icc (-((k + 1 : ℕ) : ℤ)) ((k + 1 : ℕ) : ℤ) =
        insert (-((k : ℤ) + 1)) (insert ((k : ℤ) + 1) (Finset.Icc (-(k : ℤ)) k)) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      push_cast
      omega
    rw [hsplit, Finset.sum_insert, Finset.sum_insert, ih (by omega),
      fib_nonneg n ((k : ℤ) + 1) (by omega) (by omega),
      fib_nonpos n (-((k : ℤ) + 1)) (by omega) (by omega)]
    · push_cast
      ring
    · simp only [Finset.mem_Icc]
      omega
    · simp only [Finset.mem_insert, Finset.mem_Icc]
      omega

/-- The closed form, multiplied by 8, in ℤ. -/
lemma closed (n : ℕ) :
    8 * (a n : ℤ) = 5 + 3 * (-1) ^ n + 2 * (7 + 3 * (-1) ^ n) * (n : ℤ) + 14 * (n : ℤ) ^ 2 := by
  have hs := sum_fib n (n / 2) (by omega)
  have h : (a n : ℤ) = ∑ s ∈ Finset.Icc (-((n / 2 : ℕ) : ℤ)) ((n / 2 : ℕ) : ℤ),
      ((fib n s).card : ℤ) := by
    rw [a_eq_sum n]
    push_cast
    rfl
  rw [h, hs]
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show (m + m) / 2 = m by omega, Even.neg_one_pow ⟨m, rfl⟩]
    push_cast
    ring
  · subst hm
    rw [show (2 * m + 1) / 2 = m by omega, Odd.neg_one_pow ⟨m, rfl⟩]
    push_cast
    ring

lemma gf : PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2 : PowerSeries ℤ) =
    1 + 2 * X + 8 * X ^ 2 + 2 * X ^ 3 + X ^ 4 := by
  have e : PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2 : PowerSeries ℤ) =
      PowerSeries.mk (fun n => (a n : ℤ)) - PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 1
      - (PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 2 + PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 2)
      + (PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 3 + PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 3)
      + PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 4
      - PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 5 := by
    ring
  have hN : (1 + 2 * X + 8 * X ^ 2 + 2 * X ^ 3 + X ^ 4 : PowerSeries ℤ) =
      C 1 + C 2 * X ^ 1 + C 8 * X ^ 2 + C 2 * X ^ 3 + C 1 * X ^ 4 := by
    simp
  rw [e, hN]
  ext m
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mk, coeff_C]
  have c0 := closed 0
  have c1 := closed 1
  have c2 := closed 2
  have c3 := closed 3
  have c4 := closed 4
  norm_num at c0 c1 c2 c3 c4
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m <;> simp <;> omega
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 5 := ⟨m - 5, by omega⟩
    have d0 := closed j
    have d1 := closed (j + 1)
    have d2 := closed (j + 2)
    have d3 := closed (j + 3)
    have d4 := closed (j + 4)
    have d5 := closed (j + 5)
    simp only [show 1 ≤ j + 5 by omega, show 2 ≤ j + 5 by omega, show 3 ≤ j + 5 by omega,
      show 4 ≤ j + 5 by omega, show 5 ≤ j + 5 by omega, if_true,
      show j + 5 ≠ 0 by omega, if_false,
      show j + 5 - 1 = j + 4 by omega, show j + 5 - 2 = j + 3 by omega,
      show j + 5 - 3 = j + 2 by omega, show j + 5 - 4 = j + 1 by omega,
      show j + 5 - 5 = j by omega]
    push_cast at d0 d1 d2 d3 d4 d5
    have : 8 * ((a (j + 5) : ℤ) - a (j + 4) - (a (j + 3) + a (j + 3)) + (a (j + 2) + a (j + 2))
        + a (j + 1) - a j) = 0 := by
      linear_combination d5 - d4 - 2 * d3 + 2 * d2 + d1 - d0
    omega

theorem sol : type_of% @OMA.S_oeis_a211438.main := by
  refine ⟨fun n => ?_, gf⟩
  have h := closed n
  rw [eq_div_iff (by norm_num : (8 : ℚ) ≠ 0)]
  have h' : ((8 * (a n : ℤ) : ℤ) : ℚ) =
      ((5 + 3 * (-1) ^ n + 2 * (7 + 3 * (-1) ^ n) * (n : ℤ) + 14 * (n : ℤ) ^ 2 : ℤ) : ℚ) := by
    rw [h]
  push_cast at h'
  linear_combination h'

end OMA.P211438

theorem OMA.solution : type_of% @OMA.S_oeis_a211438.main := OMA.P211438.sol
