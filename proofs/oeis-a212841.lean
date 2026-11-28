import OMAStatements.S_oeis_a212841

/-!
Source: https://oeis.org/A212841 (OEIS Foundation, CC BY-SA 4.0).
R. H. Hardin supplied the sequence and Colin Barker stated both conjectures.
The counting and coefficient arguments adapt @grp06's proof of A212837.
-/

namespace OMA.S_oeis_a212841

open Finset PowerSeries
open scoped BigOperators

-- The tags 0, 1, and 2 denote the low endpoint, high endpoint, and interior.
private def tag (n : ℕ) (x : Fin (n + 1)) : Fin 3 :=
  if x.val = 0 then 0 else if x.val = n then 1 else 2

private theorem tag_low {n : ℕ} (x : Fin (n + 1)) :
    tag n x = 0 ↔ x.val = 0 := by
  by_cases h₀ : x.val = 0
  · simp [tag, h₀]
  · by_cases hₙ : x.val = n <;>
      simp [tag, h₀, hₙ, show (1 : Fin 3) ≠ 0 by decide,
        show (2 : Fin 3) ≠ 0 by decide]

private theorem tag_high {n : ℕ} (hn : 0 < n) (x : Fin (n + 1)) :
    tag n x = 1 ↔ x.val = n := by
  by_cases h₀ : x.val = 0
  · have hₙ : x.val ≠ n := by omega
    rw [tag, if_pos h₀]
    exact iff_of_false (by decide) hₙ
  · by_cases hₙ : x.val = n
    · rw [tag, if_neg h₀, if_pos hₙ]
      exact iff_of_true rfl hₙ
    · rw [tag, if_neg h₀, if_neg hₙ]
      exact iff_of_false (by decide) hₙ

private theorem tag_interior {n : ℕ} (x : Fin (n + 1)) :
    tag n x = 2 ↔ x.val ≠ 0 ∧ x.val ≠ n := by
  by_cases h₀ : x.val = 0
  · rw [tag, if_pos h₀]
    exact iff_of_false (by decide) (fun h => h.1 h₀)
  · by_cases hₙ : x.val = n
    · rw [tag, if_neg h₀, if_pos hₙ]
      exact iff_of_false (by decide) (fun h => h.2 hₙ)
    · rw [tag, if_neg h₀, if_neg hₙ]
      exact iff_of_true rfl ⟨h₀, hₙ⟩

private def letters (n : ℕ) (c : Fin 3) : Finset (Fin (n + 1)) :=
  univ.filter fun x => tag n x = c

private theorem card_letters {n : ℕ} (hn : 0 < n) (c : Fin 3) :
    (letters n c).card = if c = 2 then n - 1 else 1 := by
  have zero_iff (x : Fin (n + 1)) : x.val = 0 ↔ x = 0 := by
    constructor
    · intro h
      apply Fin.ext
      simpa only [Fin.val_zero] using h
    · rintro rfl
      simp only [Fin.val_zero]
  have last_iff (x : Fin (n + 1)) : x.val = n ↔ x = Fin.last n := by
    constructor
    · intro h
      apply Fin.ext
      simpa only [Fin.val_last] using h
    · rintro rfl
      simp only [Fin.val_last]
  have hlast : Fin.last n ≠ (0 : Fin (n + 1)) := by
    intro h
    have hv : n = 0 := by simpa only [Fin.val_last, Fin.val_zero] using congrArg Fin.val h
    omega
  have low : letters n 0 = {0} := by
    ext x
    simp [letters, tag_low, zero_iff]
  have high : letters n 1 = {Fin.last n} := by
    ext x
    simp [letters, tag_high hn, last_iff]
  have interior : letters n 2 =
      ((univ : Finset (Fin (n + 1))).erase 0).erase (Fin.last n) := by
    ext x
    simp [letters, tag_interior, zero_iff, last_iff, and_comm]
  fin_cases c
  · change (letters n 0).card = if (0 : Fin 3) = 2 then n - 1 else 1
    rw [low, if_neg (by decide), card_singleton]
  · change (letters n 1).card = if (1 : Fin 3) = 2 then n - 1 else 1
    rw [high, if_neg (by decide), card_singleton]
  · change (letters n 2).card = if (2 : Fin 3) = 2 then n - 1 else 1
    rw [interior, if_pos rfl,
      card_erase_of_mem (s := (univ : Finset (Fin (n + 1))).erase 0)
        (a := Fin.last n) (by simp [hlast]),
      card_erase_of_mem (s := (univ : Finset (Fin (n + 1)))) (a := 0) (mem_univ _),
      card_univ, Fintype.card_fin]
    omega

private def validTags {m : ℕ} (w : Fin m → Fin 3) : Prop :=
  ∀ i j : Fin m, j.val = i.val + 1 →
    ¬ ((w i = 0 ∧ w j = 1) ∨ (w i = 1 ∧ w j = 0))

private instance {m : ℕ} (w : Fin m → Fin 3) : Decidable (validTags w) := by
  unfold validTags
  infer_instance

private def validWords (m : ℕ) : Finset (Fin m → Fin 3) :=
  univ.filter validTags

private def interiorSlots {m : ℕ} (w : Fin m → Fin 3) : Finset (Fin m) :=
  univ.filter fun i => w i = 2

private theorem card_words (m n : ℕ) (hn : 0 < n) :
    ((univ : Finset (Fin m → Fin (n + 1))).filter
      (fun f => ∀ i j : Fin m, j.val = i.val + 1 → ¬ zn n (f i) (f j))).card =
      ∑ w ∈ validWords m, (n - 1) ^ (interiorSlots w).card := by
  let label : (Fin m → Fin (n + 1)) → (Fin m → Fin 3) := fun f i => tag n (f i)
  have valid_filter :
      (univ.filter fun f => label f ∈ validWords m) =
        (univ.filter fun f => ∀ i j : Fin m, j.val = i.val + 1 → ¬ zn n (f i) (f j)) := by
    ext f
    rw [mem_filter, mem_filter]
    simp only [validWords, mem_filter, mem_univ, true_and]
    simp only [validTags, label, tag_low, tag_high hn, zn]
  rw [← valid_filter, ← sum_card_fiberwise_eq_card_filter univ (validWords m) label]
  apply sum_congr rfl
  intro w _
  have fiber : (univ.filter fun f => label f = w) =
      Fintype.piFinset (fun i => letters n (w i)) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, letters, funext_iff, label]
  rw [fiber, Fintype.card_piFinset]
  simp_rw [card_letters hn]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const] <;> rfl

private def interiorNumber {m : ℕ} (w : Fin m → Fin 3) : Fin (m + 1) :=
  ⟨(interiorSlots w).card, by
    have h := Finset.card_le_univ (interiorSlots w)
    simpa only [Fintype.card_fin, Nat.lt_succ_iff] using h⟩

private def populations (j : Fin 9) : ℕ :=
  if j.val = 0 then 2 else if j.val = 1 then 28 else if j.val = 2 then 146 else if j.val = 3 then 360 else if j.val = 4 then 450 else if j.val = 5 then 292 else if j.val = 6 then 98 else if j.val = 7 then 16 else 1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tag_populations : ∀ j : Fin 9,
    ((validWords 8).filter fun w => interiorNumber w = j).card = populations j := by
  intro j
  fin_cases j <;> decide

private theorem count_shifted (n : ℕ) (hn : 0 < n) :
    a n = 2 + 28 * (n - 1) + 146 * (n - 1) ^ 2 + 360 * (n - 1) ^ 3 + 450 * (n - 1) ^ 4 + 292 * (n - 1) ^ 5 + 98 * (n - 1) ^ 6 + 16 * (n - 1) ^ 7 + (n - 1) ^ 8 := by
  unfold a
  rw [card_words 8 n hn]
  calc
    (∑ w ∈ validWords 8, (n - 1) ^ (interiorSlots w).card) =
        ∑ j : Fin 9, ∑ w ∈ (validWords 8).filter (fun w => interiorNumber w = j),
          (n - 1) ^ j.val := by
      symm
      exact Finset.sum_fiberwise_of_maps_to' (fun _ _ => mem_univ _)
        (fun j : Fin 9 => (n - 1) ^ j.val)
    _ = ∑ j : Fin 9, populations j * (n - 1) ^ j.val := by
      simp only [sum_const, Nat.nsmul_eq_mul, tag_populations]
    _ = _ := by
      norm_num [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, populations] <;> ring

private def sequencePolynomial {R : Type*} [Ring R] (x : R) : R :=
  1 - 8 * x + 8 * x ^ 2 + 24 * x ^ 3 - 30 * x ^ 4 - 16 * x ^ 5 + 14 * x ^ 6 + 8 * x ^ 7 + x ^ 8

private theorem cast_count {R : Type*} [CommRing R] (n : ℕ) (hn : 0 < n) :
    (a n : R) = sequencePolynomial (n : R) := by
  have h := congrArg (fun k : ℕ => (k : R)) (count_shifted n hn)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  rw [h, sequencePolynomial, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  ring

private theorem finite_difference {R : Type*} [CommRing R] (x : R) :
    sequencePolynomial x + (- 9 * sequencePolynomial (x - 1) + 36 * sequencePolynomial (x - 2) - 84 * sequencePolynomial (x - 3) + 126 * sequencePolynomial (x - 4) - 126 * sequencePolynomial (x - 5) + 84 * sequencePolynomial (x - 6) - 36 * sequencePolynomial (x - 7) + 9 * sequencePolynomial (x - 8) - sequencePolynomial (x - 9)) = 0 := by
  unfold sequencePolynomial
  ring

private theorem recurrence (n : ℕ) (hn : 9 < n) :
    (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  simp (disch := omega) only [cast_count, Nat.cast_sub, Nat.cast_one, Nat.cast_ofNat]
  linear_combination finite_difference (n : ℤ)

private def offsetCoeff (n : ℕ) : ℚ :=
  if n = 0 then 0 else sequencePolynomial (n : ℚ)

private theorem generating_function :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (2 + 1375 * X + 16177 * X ^ 2 + 23723 * X ^ 3 - 551 * X ^ 4 - 563 * X ^ 5 + 179 * X ^ 6 - 23 * X ^ 7 + X ^ 8) := by
  have hoffset : (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = offsetCoeff := by
    funext n
    by_cases hn : n = 0
    · simp [offsetCoeff, hn]
    · simp [offsetCoeff, hn, cast_count n (by omega : 0 < n)]
  rw [hoffset]
  let A : PowerSeries ℚ := PowerSeries.mk offsetCoeff
  have hleft : A * (1 - X) ^ 9 =
      A + (- A * X ^ 1 * C 9 + A * X ^ 2 * C 36 - A * X ^ 3 * C 84 + A * X ^ 4 * C 126 - A * X ^ 5 * C 126 + A * X ^ 6 * C 84 - A * X ^ 7 * C 36 + A * X ^ 8 * C 9 - A * X ^ 9) := by
    simp only [map_ofNat]
    ring
  have hright : (X : PowerSeries ℚ) * (2 + 1375 * X + 16177 * X ^ 2 + 23723 * X ^ 3 - 551 * X ^ 4 - 563 * X ^ 5 + 179 * X ^ 6 - 23 * X ^ 7 + X ^ 8) =
      C 2 * X ^ 1 + C 1375 * X ^ 2 + C 16177 * X ^ 3 + C 23723 * X ^ 4 - C 551 * X ^ 5 - C 563 * X ^ 6 + C 179 * X ^ 7 - C 23 * X ^ 8 + X ^ 9 := by
    simp only [map_ofNat]
    ring
  change A * (1 - X) ^ 9 = _
  rw [hleft, hright]
  apply PowerSeries.ext
  intro d
  simp only [map_add, map_sub, map_neg, coeff_mul_C, coeff_mul_X_pow',
    coeff_C, coeff_X_pow, A, coeff_mk]
  by_cases hd : d ≤ 9
  · interval_cases d <;> norm_num [offsetCoeff, sequencePolynomial]
  · simp (disch := omega) only [offsetCoeff, if_pos, if_neg, Nat.cast_sub,
      Nat.cast_one, Nat.cast_ofNat]
    linear_combination finite_difference (d : ℚ)

end OMA.S_oeis_a212841

theorem OMA.solution : type_of% @OMA.S_oeis_a212841.main := by
  exact ⟨OMA.S_oeis_a212841.generating_function, OMA.S_oeis_a212841.recurrence⟩
