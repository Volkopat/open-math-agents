import OMAStatements.S_oeis_a210374

-- Original proof and statement by @agchua in #19005.
-- Count all weak compositions and remove the four disjoint overflow classes.

namespace OMA.A210374

open Finset OMA.S_oeis_a210374

private abbrev tuples (k n : ℕ) := Finset.Nat.antidiagonalTuple k n

private theorem sum_choose (d n : ℕ) :
    ((List.Nat.antidiagonal n).map fun ij => (d + ij.2).choose d).sum =
      (d + n + 1).choose (d + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.Nat.antidiagonal_succ, List.map_cons, List.sum_cons, List.map_map]
    change (d + (n + 1)).choose d +
      ((List.Nat.antidiagonal n).map fun ij => (d + ij.2).choose d).sum = _
    rw [ih, Nat.choose_succ_succ (d + (n + 1)), ← Nat.add_assoc]

-- Stars and bars, by separating the first coordinate and applying the hockey-stick identity.
private theorem tuple_card (d n : ℕ) : (tuples (d + 1) n).card = (d + n).choose d := by
  induction d generalizing n with
  | zero => simp [Finset.Nat.antidiagonalTuple_one]
  | succ d ih =>
    change (List.Nat.antidiagonalTuple (d + 1 + 1) n).length = _
    rw [List.Nat.antidiagonalTuple, List.length_flatMap]
    simp only [List.length_map]
    change ((List.Nat.antidiagonal n).map fun ij => (tuples (d + 1) ij.2).card).sum = _
    simp_rw [ih]
    simpa [Nat.add_right_comm d 1 n] using sum_choose d n

private theorem sum_coordinate (f : Fin 4 → ℕ) (i : Fin 4) :
    (∑ k, f k) = f i + ∑ k ∈ (univ \ {i}), f k := by
  simpa using sum_update_of_mem (mem_univ i) f (f i)

private def overflow (n : ℕ) (i : Fin 4) := (tuples 4 (n + 2)).filter (fun f => n < f i)

-- Subtract n+1 at the overflowing coordinate, leaving a tuple of sum one.
private theorem overflow_card (n : ℕ) (i : Fin 4) : (overflow n i).card = 4 := by
  calc
    _ = (tuples 4 1).card := by
      refine card_nbij' (fun f => Function.update f i (f i - (n + 1)))
        (fun f => Function.update f i (f i + (n + 1))) ?_ ?_ ?_ ?_
      · intro f hf
        simp only [mem_coe] at hf ⊢
        rw [overflow, mem_filter, Finset.Nat.mem_antidiagonalTuple, sum_coordinate f i] at hf
        rw [Finset.Nat.mem_antidiagonalTuple, sum_update_of_mem (mem_univ i)]
        omega
      · intro f hf
        simp only [mem_coe] at hf ⊢
        rw [Finset.Nat.mem_antidiagonalTuple, sum_coordinate f i] at hf
        rw [overflow, mem_filter, Finset.Nat.mem_antidiagonalTuple, sum_update_of_mem (mem_univ i)]
        simp only [Function.update_self]
        omega
      · intro f hf
        have hi := (mem_filter.mp hf).2
        funext j
        by_cases h : j = i
        · subst j
          simp only [Function.update_self]
          omega
        · simp [Function.update_of_ne h]
      · intro f hf
        funext j
        by_cases h : j = i
        · subst j
          simp
        · simp [Function.update_of_ne h]
    _ = 4 := by rw [tuple_card 3 1]; decide

private theorem bounded_card (n : ℕ) :
    a n = ((tuples 4 (n + 2)).filter (fun f => ∀ i, f i ≤ n)).card := by
  unfold a
  refine card_nbij' (fun t => ![t.1, t.2.1, t.2.2.1, t.2.2.2])
    (fun f => (f 0, f 1, f 2, f 3)) ?_ ?_ ?_ ?_
  · rintro ⟨w, x, y, z⟩ ht
    simp only [mem_coe, mem_filter, mem_product, mem_Icc, Nat.zero_le, true_and] at ht
    simp only [mem_coe]
    rw [mem_filter, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_four]
    refine ⟨by simpa [Nat.add_assoc] using ht.2, ?_⟩
    intro i
    fin_cases i <;> simp [ht.1.1, ht.1.2.1, ht.1.2.2.1, ht.1.2.2.2]
  · intro f hf
    simp only [mem_coe, mem_filter, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_four] at hf
    simp only [mem_coe, mem_filter, mem_product, mem_Icc, Nat.zero_le, true_and]
    exact ⟨⟨hf.2 0, hf.2 1, hf.2 2, hf.2 3⟩, by omega⟩
  · intro t _
    rfl
  · intro f _
    funext i
    fin_cases i <;> rfl

private theorem count_plus (n : ℕ) (hn : 0 < n) : a n + 16 = (n + 5).choose 3 := by
  have hbad : ((tuples 4 (n + 2)).filter (fun f => ¬ ∀ i, f i ≤ n)) =
      univ.biUnion (overflow n) := by
    ext f
    simp only [mem_filter, mem_biUnion, mem_univ, true_and, overflow]
    constructor
    · rintro ⟨hs, hb⟩
      obtain ⟨i, hi⟩ := not_forall.mp hb
      exact ⟨i, hs, Nat.lt_of_not_ge hi⟩
    · rintro ⟨i, hs, hi⟩
      exact ⟨hs, fun h => (Nat.not_lt_of_ge (h i)) hi⟩
  have hd : ((univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint (overflow n) := by
    intro i _ j _ hij
    refine disjoint_left.mpr ?_
    intro f hi hj
    rw [overflow, mem_filter, Finset.Nat.mem_antidiagonalTuple] at hi hj
    have h := sum_le_sum_of_subset_of_nonneg (f := f)
      (subset_univ ({i, j} : Finset (Fin 4))) (fun k _ _ => Nat.zero_le (f k))
    simp [hij, hi.1] at h
    omega
  have h := card_filter_add_card_filter_not (s := tuples 4 (n + 2)) (fun f => ∀ i, f i ≤ n)
  rw [← bounded_card n, hbad, card_biUnion hd, tuple_card 3 (n + 2)] at h
  simpa [overflow_card, Nat.add_comm 3 (n + 2), ← Nat.add_assoc] using h

theorem closed (n : ℕ) (hn : 0 < n) :
    (a n : ℚ) = (-36 + 47 * (n : ℚ) + 12 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) / 6 := by
  have h := congrArg (fun x : ℕ => (x : ℚ)) (count_plus n hn)
  have hc := congrArg (fun x : ℕ => (x : ℚ)) (Nat.descFactorial_eq_factorial_mul_choose (n + 5) 3)
  norm_num [Nat.descFactorial_succ, Nat.factorial_succ,
    show n + 5 - 2 = n + 3 by omega, show n + 5 - 1 = n + 4 by omega] at h hc
  linear_combination (6 * h - hc) / 6

end OMA.A210374

namespace OMA.A210374

open PowerSeries OMA.S_oeis_a210374

theorem main_of_closed (hC : ∀ n : ℕ, 0 < n →
    (a n : ℚ) = (-36 + 47 * (n : ℚ) + 12 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) / 6) :
    type_of% @OMA.S_oeis_a210374.main := by
  have d (k : ℕ) : (a (k+5) : ℚ) - 4*a (k+4) + 6*a (k+3) - 4*a (k+2) + a (k+1) = 0 := by
    rw [hC (k+5) (by omega), hC (k+4) (by omega), hC (k+3) (by omega),
      hC (k+2) (by omega), hC (k+1) (by omega)]
    push_cast
    ring
  refine ⟨?_, hC, ?_⟩
  · let A := mk (fun n => (a n : ℚ))
    have hD : A * (1 - X) ^ 4 =
        A - C 4 * (X ^ 1 * A) + C 6 * (X ^ 2 * A) - C 4 * (X ^ 3 * A) + X ^ 4 * A := by
      simp only [map_ofNat]
      ring
    have hN : (X : ℚ⟦X⟧) * (4 + 3 * X - 12 * X ^ 2 + 6 * X ^ 3) =
        C 4 * X ^ 1 + C 3 * X ^ 2 - C 12 * X ^ 3 + C 6 * X ^ 4 := by
      simp only [map_ofNat]
      ring
    change A * (1 - X) ^ 4 = _
    rw [hD, hN]
    ext n
    simp only [A, map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_mk]
    by_cases hn : n < 5
    · have a0 : a 0 = 0 := by decide
      interval_cases n <;> norm_num [a0, hC]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k+5 := ⟨n-5, by omega⟩
      have e₁ : k+5-1 = k+4 := by omega
      have e₂ : k+5-2 = k+3 := by omega
      have e₃ : k+5-3 = k+2 := by omega
      have e₄ : k+5-4 = k+1 := by omega
      simpa (disch := omega) [e₁, e₂, e₃, e₄] using d k
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k+5 := ⟨n-5, by omega⟩
    rw [show k+5-1 = k+4 by omega, show k+5-2 = k+3 by omega,
      show k+5-3 = k+2 by omega, show k+5-4 = k+1 by omega]
    have hr : (a (k+5) : ℚ) = 4*a (k+4) - 6*a (k+3) + 4*a (k+2) - a (k+1) := by
      linarith only [d k]
    exact_mod_cast hr

end OMA.A210374

open OMA.A210374 in
theorem OMA.solution : type_of% @OMA.S_oeis_a210374.main := main_of_closed closed
