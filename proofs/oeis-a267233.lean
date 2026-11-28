import OMAStatements.S_oeis_a267233

/-!
# A267233: four-letter arrays constrained after their first repeated letter

Sum over the second letter `b`, then the first letter `a`. If `a = b` both later letters lie
below `b`, giving `b^2` words; otherwise the count over `c, d` is `b + n (n + 1)` (`inner`, `mid`).
Summing over `b` with the sums of `b` and `b^2` gives the quartic (`count_eq`). It holds at every
index, so the fifth difference of `terms` vanishes (`recur`) and the coefficients of
`(1 - X)^5 * mk terms` are computed directly (`gf`).
-/

namespace A267233P
open OMA.S_oeis_a267233 Finset

theorem sum_lt (n b : ℕ) (hb : b ≤ n) :
    ∑ c ∈ range (n + 1), (if c < b then (1 : ℚ) else 0) = b := by
  rw [Finset.sum_boole]
  have : (range (n + 1)).filter (· < b) = range b := by
    ext x; simp only [mem_filter, mem_range]; omega
  rw [this, card_range]

theorem sum_eq_ne (n b : ℕ) (hb : b ≤ n) (f g : ℚ) :
    ∑ a ∈ range (n + 1), (if a = b then f else g) = f + n * g := by
  rw [Finset.sum_ite, sum_const, sum_const]
  have h1 : (range (n + 1)).filter (fun a => a = b) = {b} := by
    ext x; simp only [mem_filter, mem_range, mem_singleton]; omega
  have h2 : ((range (n + 1)).filter (fun a => ¬ a = b)).card = n := by
    have := Finset.card_filter_add_card_filter_not (s := range (n + 1)) (fun a => a = b)
    rw [h1, card_singleton, card_range] at this; omega
  rw [h1, h2, card_singleton]; simp

theorem inner (n a b : ℕ) (ha : a ≤ n) (hb : b ≤ n) :
    ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1), (if allowed a b c d then (1 : ℚ) else 0) =
      if a = b then (b : ℚ) ^ 2 else b + n * (n + 1) := by
  by_cases hab : a = b
  · subst hab
    simp only [allowed, if_true, ite_and]
    have : ∀ c ∈ range (n + 1), ∑ d ∈ range (n + 1), (if c < a then (if d < a then (1 : ℚ) else 0) else 0)
        = (if c < a then (1 : ℚ) else 0) * a := by
      intro c _
      by_cases hc : c < a
      · simp only [hc, if_true, one_mul]; exact sum_lt n a ha
      · simp [hc]
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, sum_lt n a ha]; ring
  · simp only [allowed, hab, if_false]
    have : ∀ c ∈ range (n + 1), ∑ d ∈ range (n + 1), (if (if b = c then d < b else True) then (1 : ℚ) else 0)
        = if c = b then (b : ℚ) else (n + 1) := by
      intro c _
      by_cases hc : c = b
      · subst hc; simp only [if_true]; exact sum_lt n c hb
      · have : ¬ b = c := fun h => hc h.symm
        simp [this, hc]
    rw [Finset.sum_congr rfl this, sum_eq_ne n b hb]

theorem mid (n b : ℕ) (hb : b ≤ n) :
    ∑ a ∈ range (n + 1), ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1),
      (if allowed a b c d then (1 : ℚ) else 0) = (b : ℚ) ^ 2 + n * (b + n * (n + 1)) := by
  have : ∀ a ∈ range (n + 1), ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1),
      (if allowed a b c d then (1 : ℚ) else 0) = if a = b then (b : ℚ) ^ 2 else b + n * (n + 1) :=
    fun a ha => inner n a b (by have := mem_range.1 ha; omega) hb
  rw [Finset.sum_congr rfl this, sum_eq_ne n b hb]

theorem sum_id (n : ℕ) : ∑ b ∈ range (n + 1), (b : ℚ) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

theorem sum_sq (n : ℕ) : ∑ b ∈ range (n + 1), (b : ℚ) ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

theorem count_eq (n : ℕ) : count n = (n:ℚ)^4 + 17/6*n^3 + 2*n^2 + 1/6*n := by
  unfold count
  have : ∀ b ∈ range (n + 1), ∑ a ∈ range (n + 1), ∑ c ∈ range (n + 1), ∑ d ∈ range (n + 1),
      (if allowed a b c d then (1 : ℚ) else 0) = (b : ℚ) ^ 2 + n * b + n * (n * (n + 1)) :=
    fun b hb => by rw [mid n b (by have := mem_range.1 hb; omega)]; ring
  rw [Finset.sum_congr rfl this, sum_add_distrib, sum_add_distrib, ← mul_sum, sum_sq, sum_id,
    sum_const, card_range]
  simp only [nsmul_eq_mul]; push_cast; ring

theorem terms_eq (j : ℕ) : terms j = (j:ℚ)^4 + 17/6*j^3 + 2*j^2 + 1/6*j := by
  cases j with
  | zero => simp [terms]
  | succ j => rw [terms, count_eq]

open PowerSeries in
theorem gf : ((1 : PowerSeries ℚ) - X)^5 * PowerSeries.mk terms = (X * (6 + 17*X + X^2) : PowerSeries ℚ) := by
  have e1 : ((1 - X) ^ 5 : PowerSeries ℚ) =
      1 - C 5 * X ^ 1 + C 10 * X ^ 2 - C 10 * X ^ 3 + C 5 * X ^ 4 - X ^ 5 := by
    simp only [map_ofNat, pow_one]; ring
  have e2 : (X * (6 + 17 * X + X ^ 2) : PowerSeries ℚ) = C 6 * X ^ 1 + C 17 * X ^ 2 + X ^ 3 := by
    simp only [map_ofNat, pow_one]; ring
  rw [e1, e2]
  ext k
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add, coeff_C_mul, coeff_X_pow_mul',
    coeff_mk, coeff_C_mul_X_pow, coeff_X_pow]
  rcases Nat.lt_or_ge k 5 with h | h
  · interval_cases k <;> simp [terms_eq] <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    simp only [show 1 ≤ j + 5 by omega, show 2 ≤ j + 5 by omega, show 3 ≤ j + 5 by omega,
      show 4 ≤ j + 5 by omega, le_refl, ↓reduceIte, show j + 5 ≠ 1 by omega,
      show j + 5 ≠ 2 by omega, show j + 5 ≠ 3 by omega,
      show j + 5 - 1 = j + 4 by omega, show j + 5 - 2 = j + 3 by omega,
      show j + 5 - 3 = j + 2 by omega, show j + 5 - 4 = j + 1 by omega, show j + 5 - 5 = j by omega,
      terms_eq]
    push_cast; ring

theorem recur (n : ℕ) : terms (n+6) = 5*terms (n+5) - 10*terms (n+4) +
    10*terms (n+3) - 5*terms (n+2) + terms (n+1) := by
  simp only [terms_eq]; push_cast; ring

end A267233P

theorem OMA.solution : type_of% @OMA.S_oeis_a267233.main :=
  ⟨A267233P.count_eq, A267233P.recur, A267233P.gf⟩
