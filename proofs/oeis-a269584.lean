import OMAStatements.S_oeis_a269584

/-!
# A269584: four-letter words with nearly equal successive repeated values

The recorded values of `(a, b, c, d)` violate the rule only when `b = a`, `d = c` and the two
values differ by at least two (`allowed_iff`), since two recorded values from overlapping pairs are
equal. So `count n` is `(n + 1)^4` minus the number of ordered pairs `(a, c)` with `|a - c| ≥ 2`,
which is `n^2 - n` (`viol`, by induction). This is the quartic (`count_eq`); the recurrence and the
generating function follow coefficientwise (`recur`, `gf`).
-/

namespace A269584P
open OMA.S_oeis_a269584 Finset

theorem allowed_iff (a b c d : ℕ) : allowed (repeats a b c d) = true ↔
    ¬ (b = a ∧ d = c ∧ (a + 2 ≤ c ∨ c + 2 ≤ a)) := by
  unfold repeats
  split_ifs with h1 h2 h3 h3 h2 h3 h3 <;>
    simp only [List.nil_append, List.append_nil, List.singleton_append, List.cons_append, allowed,
      Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, true_iff] <;>
    omega

theorem ind (a b c d : ℕ) : (if allowed (repeats a b c d) then (1 : ℚ) else 0) =
    1 - (if b = a ∧ d = c ∧ (a + 2 ≤ c ∨ c + 2 ≤ a) then 1 else 0) := by
  by_cases h : b = a ∧ d = c ∧ (a + 2 ≤ c ∨ c + 2 ≤ a)
  · have : ¬ allowed (repeats a b c d) = true := fun h' => (allowed_iff a b c d).1 h' h
    rw [if_neg this, if_pos h]; ring
  · have : allowed (repeats a b c d) = true := (allowed_iff a b c d).2 h
    rw [if_pos this, if_neg h]; ring

theorem viol (n : ℕ) : ∑ a ∈ range (n + 1), ∑ c ∈ range (n + 1),
    (if a + 2 ≤ c ∨ c + 2 ≤ a then (1 : ℚ) else 0) = n ^ 2 - n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have e1 : ∀ a ∈ range (k + 1), ∑ c ∈ range (k + 1 + 1),
        (if a + 2 ≤ c ∨ c + 2 ≤ a then (1 : ℚ) else 0) =
        ∑ c ∈ range (k + 1), (if a + 2 ≤ c ∨ c + 2 ≤ a then (1 : ℚ) else 0) +
          (if a + 2 ≤ k + 1 then 1 else 0) := by
      intro a ha
      rw [sum_range_succ]
      congr 1
      have := mem_range.1 ha
      by_cases h : a + 2 ≤ k + 1 <;> simp [h] <;> omega
    rw [sum_range_succ, Finset.sum_congr rfl e1, sum_add_distrib, ih]
    have e2 : ∑ a ∈ range (k + 1), (if a + 2 ≤ k + 1 then (1 : ℚ) else 0) = k := by
      rw [Finset.sum_boole]
      have : (range (k + 1)).filter (fun a => a + 2 ≤ k + 1) = range k := by
        ext x; simp only [mem_filter, mem_range]; omega
      rw [this, card_range]
    have e3 : ∑ c ∈ range (k + 1 + 1), (if k + 1 + 2 ≤ c ∨ c + 2 ≤ k + 1 then (1 : ℚ) else 0) = k := by
      rw [Finset.sum_boole]
      have : (range (k + 1 + 1)).filter (fun c => k + 1 + 2 ≤ c ∨ c + 2 ≤ k + 1) = range k := by
        ext x; simp only [mem_filter, mem_range]; omega
      rw [this, card_range]
    rw [e2, e3]; push_cast; ring

theorem sum_eq_and (n c : ℕ) (hc : c ≤ n) (P : Prop) [Decidable P] :
    ∑ x ∈ range (n + 1), (if x = c ∧ P then (1 : ℚ) else 0) = if P then 1 else 0 := by
  by_cases hP : P
  · simp only [hP, and_true, if_true]
    rw [Finset.sum_ite_eq' (range (n + 1)) c (fun _ => (1 : ℚ)), if_pos (mem_range.2 (by omega))]
  · simp [hP]

theorem count_eq (n : ℕ) : count n = (n:ℚ)^4 + 4*n^3 + 5*n^2 + 5*n + 1 := by
  unfold count
  simp only [ind, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
  have hv : ∀ a ∈ range (n + 1), ∀ c ∈ range (n + 1),
      ∑ b ∈ range (n + 1), ∑ d ∈ range (n + 1),
        (if b = a ∧ d = c ∧ (a + 2 ≤ c ∨ c + 2 ≤ a) then (1 : ℚ) else 0) =
      if a + 2 ≤ c ∨ c + 2 ≤ a then 1 else 0 := by
    intro a ha c hc
    have hc' : c ≤ n := by have := mem_range.1 hc; omega
    have ha' : a ≤ n := by have := mem_range.1 ha; omega
    have h1 : ∀ b ∈ range (n + 1), ∑ d ∈ range (n + 1),
        (if b = a ∧ d = c ∧ (a + 2 ≤ c ∨ c + 2 ≤ a) then (1 : ℚ) else 0) =
        if b = a ∧ (a + 2 ≤ c ∨ c + 2 ≤ a) then 1 else 0 := by
      intro b _
      simp only [and_left_comm (a := b = a)]
      exact sum_eq_and n c hc' _
    rw [Finset.sum_congr rfl h1, sum_eq_and n a ha']
  have hv2 : ∀ a ∈ range (n + 1), ∑ c ∈ range (n + 1), ∑ b ∈ range (n + 1), ∑ d ∈ range (n + 1),
        (if b = a ∧ d = c ∧ (a + 2 ≤ c ∨ c + 2 ≤ a) then (1 : ℚ) else 0) =
      ∑ c ∈ range (n + 1), (if a + 2 ≤ c ∨ c + 2 ≤ a then (1 : ℚ) else 0) :=
    fun a ha => Finset.sum_congr rfl (hv a ha)
  rw [Finset.sum_congr rfl hv2, viol]
  push_cast; ring

theorem terms_succ (j : ℕ) : terms (j + 1) = ((j + 1 : ℕ) : ℚ)^4 + 4*((j + 1 : ℕ) : ℚ)^3 +
    5*((j + 1 : ℕ) : ℚ)^2 + 5*((j + 1 : ℕ) : ℚ) + 1 := by
  rw [terms, count_eq]

theorem recur (n : ℕ) : terms (n+6) = 5*terms (n+5) - 10*terms (n+4) +
    10*terms (n+3) - 5*terms (n+2) + terms (n+1) := by
  simp only [show n + 6 = (n + 5) + 1 by rfl, show n + 5 = (n + 4) + 1 by rfl,
    show n + 4 = (n + 3) + 1 by rfl, show n + 3 = (n + 2) + 1 by rfl,
    show n + 2 = (n + 1) + 1 by rfl, terms_succ]
  push_cast; ring

open PowerSeries in
theorem gf : ((1 : PowerSeries ℚ) - X)^5 * PowerSeries.mk terms =
    (X * (16 - X + 15*X^2 - 7*X^3 + X^4) : PowerSeries ℚ) := by
  have e1 : ((1 - X) ^ 5 : PowerSeries ℚ) =
      1 - C 5 * X ^ 1 + C 10 * X ^ 2 - C 10 * X ^ 3 + C 5 * X ^ 4 - X ^ 5 := by
    simp only [map_ofNat, pow_one]; ring
  have e2 : (X * (16 - X + 15*X^2 - 7*X^3 + X^4) : PowerSeries ℚ) =
      C 16 * X ^ 1 - X ^ 2 + C 15 * X ^ 3 - C 7 * X ^ 4 + X ^ 5 := by
    simp only [map_ofNat, pow_one]; ring
  rw [e1, e2]
  ext k
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add, coeff_C_mul, coeff_X_pow_mul',
    coeff_mk, coeff_X_pow]
  rcases Nat.lt_or_ge k 6 with h | h
  · interval_cases k <;> simp [terms, count_eq] <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega, show 3 ≤ j + 6 by omega,
      show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega, ↓reduceIte, show j + 6 ≠ 1 by omega,
      show j + 6 ≠ 2 by omega, show j + 6 ≠ 3 by omega, show j + 6 ≠ 4 by omega,
      show j + 6 ≠ 5 by omega,
      show j + 6 - 1 = (j + 4) + 1 by omega, show j + 6 - 2 = (j + 3) + 1 by omega,
      show j + 6 - 3 = (j + 2) + 1 by omega, show j + 6 - 4 = (j + 1) + 1 by omega,
      show j + 6 - 5 = j + 1 by omega, show j + 6 = (j + 5) + 1 by rfl, terms_succ]
    push_cast; ring

end A269584P

theorem OMA.solution : type_of% @OMA.S_oeis_a269584.main :=
  ⟨A269584P.count_eq, A269584P.recur, A269584P.gf⟩
