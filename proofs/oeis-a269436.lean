import OMAStatements.S_oeis_a269436
import Mathlib

namespace A269436Aux

open OMA.S_oeis_a269436 in
lemma good_iff {n : ℕ} (w : Word n) :
    (repeats w).Pairwise (· ≥ ·) ↔ ¬ (w.1 = w.2.1 ∧ w.2.2.1 = w.2.2.2 ∧ w.1 < w.2.2.1) := by
  obtain ⟨a, b, c, d⟩ := w
  unfold repeats
  rcases eq_or_ne a b with rfl | h1
  · rcases eq_or_ne a c with rfl | h2
    · rcases eq_or_ne a d with rfl | h3
      · simp
      · simp [h3]
    · rcases eq_or_ne c d with rfl | h3
      · simp [h2]
      · simp [h2, h3]
  · rcases eq_or_ne b c with rfl | h2
    · rcases eq_or_ne b d with rfl | h3
      · simp [h1]
      · simp [h1, h3]
    · rcases eq_or_ne c d with rfl | h3
      · simp [h1, h2]
      · simp [h1, h2, h3]

lemma lt_card (m : ℕ) :
    2 * (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2)).card = m * (m - 1) := by
  have h : (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2)).card =
      ∑ i ∈ Finset.range m, i := by
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm,
      Finset.sum_range (fun i => i)]
    apply Finset.sum_congr rfl
    intro b _
    show (∑ x : Fin m, if x < b then 1 else 0) = (b : ℕ)
    rw [← Finset.card_filter]
    have e : Finset.univ.filter (fun x : Fin m => x < b) = Finset.Iio b := by
      ext x
      simp
    rw [e, Fin.card_Iio]
  have h2 := Finset.sum_range_id_mul_two m
  rw [h]
  linarith

lemma bad_card (m : ℕ) :
    (Finset.univ.filter (fun w : Fin m × Fin m × Fin m × Fin m =>
      w.1 = w.2.1 ∧ w.2.2.1 = w.2.2.2 ∧ w.1 < w.2.2.1)).card =
    (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2)).card := by
  refine Finset.card_bij' (fun w _ => (w.1, w.2.2.1)) (fun p _ => (p.1, p.1, p.2, p.2)) ?_ ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨Finset.mem_univ _, hw.2.2.2⟩
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨Finset.mem_univ _, rfl, rfl, hp.2⟩
  · rintro ⟨a, b, c, d⟩ hw
    rw [Finset.mem_filter] at hw
    obtain ⟨_, h1, h2, _⟩ := hw
    have h1' : a = b := h1
    have h2' : c = d := h2
    subst h1'
    subst h2'
    rfl
  · rintro ⟨a, c⟩ _
    rfl

open OMA.S_oeis_a269436 in
lemma count_eq (n : ℕ) : 2 * count n + (n + 1) * n = 2 * (n + 1) ^ 4 := by
  have hsplit : ((Finset.univ : Finset (Word n)).filter
        (fun w => w.1 = w.2.1 ∧ w.2.2.1 = w.2.2.2 ∧ w.1 < w.2.2.1)).card +
      ((Finset.univ : Finset (Word n)).filter
        (fun w => ¬ (w.1 = w.2.1 ∧ w.2.2.1 = w.2.2.2 ∧ w.1 < w.2.2.1))).card =
      (Finset.univ : Finset (Word n)).card :=
    Finset.card_filter_add_card_filter_not _
  have hgood : count n = ((Finset.univ : Finset (Word n)).filter
      (fun w => ¬ (w.1 = w.2.1 ∧ w.2.2.1 = w.2.2.2 ∧ w.1 < w.2.2.1))).card := by
    unfold count
    congr 1
    apply Finset.filter_congr
    intro w _
    exact good_iff w
  have hbad : ((Finset.univ : Finset (Word n)).filter
        (fun w => w.1 = w.2.1 ∧ w.2.2.1 = w.2.2.2 ∧ w.1 < w.2.2.1)).card =
      ((Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter (fun p => p.1 < p.2)).card :=
    bad_card (n + 1)
  have hlt : 2 * ((Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter
      (fun p => p.1 < p.2)).card = (n + 1) * (n + 1 - 1) := lt_card (n + 1)
  have hcard : (Finset.univ : Finset (Word n)).card = (n + 1) ^ 4 := by
    rw [Finset.card_univ]
    simp only [Word, Fintype.card_prod, Fintype.card_fin]
    ring
  have e : (n + 1) * (n + 1 - 1) = (n + 1) * n := by
    rw [Nat.add_sub_cancel]
  linarith

open OMA.S_oeis_a269436 in
lemma closed (n : ℕ) : terms (n + 1) = ((n : ℚ) + 2) ^ 4 - ((n : ℚ) + 2) * (n + 1) / 2 := by
  have h := count_eq (n + 1)
  have hq : (2 : ℚ) * (count (n + 1) : ℚ) + ((n : ℚ) + 1 + 1) * ((n : ℚ) + 1) =
      2 * ((n : ℚ) + 1 + 1) ^ 4 := by
    exact_mod_cast h
  show (count (n + 1) : ℚ) = ((n : ℚ) + 2) ^ 4 - ((n : ℚ) + 2) * (n + 1) / 2
  linarith

open OMA.S_oeis_a269436 in
lemma rec_gen (n : ℕ) : terms (n + 6) = 5 * terms (n + 5) - 10 * terms (n + 4) +
    10 * terms (n + 3) - 5 * terms (n + 2) + terms (n + 1) := by
  have e6 : terms (n + 6) = _ := closed (n + 5)
  have e5 : terms (n + 5) = _ := closed (n + 4)
  have e4 : terms (n + 4) = _ := closed (n + 3)
  have e3 : terms (n + 3) = _ := closed (n + 2)
  have e2 : terms (n + 2) = _ := closed (n + 1)
  rw [e6, e5, e4, e3, e2, closed n]
  push_cast
  ring

open OMA.S_oeis_a269436 in
lemma tv0 : terms 0 = 0 := rfl

open OMA.S_oeis_a269436 in
lemma tv1 : terms 1 = 15 := by
  have h := closed 0
  norm_num at h
  exact h

open OMA.S_oeis_a269436 in
lemma tv2 : terms 2 = 78 := by
  have h := closed 1
  norm_num at h
  exact h

open OMA.S_oeis_a269436 in
lemma tv3 : terms 3 = 250 := by
  have h := closed 2
  norm_num at h
  exact h

open OMA.S_oeis_a269436 in
lemma tv4 : terms 4 = 615 := by
  have h := closed 3
  norm_num at h
  exact h

open OMA.S_oeis_a269436 in
lemma tv5 : terms 5 = 1281 := by
  have h := closed 4
  norm_num at h
  exact h

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (C c * X ^ k * mk f) = if k ≤ n then c * f (n - k) else 0 := by
  rw [mul_comm (C c * X ^ k) (mk f), ← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul,
    coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A269436Aux

open OMA.S_oeis_a269436 A269436Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a269436.main := by
  refine ⟨closed, rec_gen, ?_⟩
  have hD : ((1 - X) ^ 5 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (-5 : ℚ) * X ^ 1 +
      C (10 : ℚ) * X ^ 2 + C (-10 : ℚ) * X ^ 3 + C (5 : ℚ) * X ^ 4 + C (-1 : ℚ) * X ^ 5 := by
    simp only [map_one, map_ofNat, map_neg]
    ring
  have hN : (X * (15 + 3 * X + 10 * X ^ 2 - 5 * X ^ 3 + X ^ 4) : PowerSeries ℚ) =
      C (15 : ℚ) * X ^ 1 + C (3 : ℚ) * X ^ 2 + C (10 : ℚ) * X ^ 3 + C (-5 : ℚ) * X ^ 4 +
        C (1 : ℚ) * X ^ 5 := by
    simp only [map_one, map_ofNat, map_neg]
    ring
  rw [hD, hN]
  ext n
  simp only [add_mul, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
  rcases Nat.lt_or_ge n 6 with hs | hs
  · interval_cases n <;> norm_num [tv0, tv1, tv2, tv3, tv4, tv5]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [if_pos (show 0 ≤ m + 6 by omega), if_pos (show 1 ≤ m + 6 by omega),
      if_pos (show 2 ≤ m + 6 by omega), if_pos (show 3 ≤ m + 6 by omega),
      if_pos (show 4 ≤ m + 6 by omega), if_pos (show 5 ≤ m + 6 by omega),
      if_neg (show ¬ (m + 6 = 1) by omega), if_neg (show ¬ (m + 6 = 2) by omega),
      if_neg (show ¬ (m + 6 = 3) by omega), if_neg (show ¬ (m + 6 = 4) by omega),
      if_neg (show ¬ (m + 6 = 5) by omega)]
    rw [show m + 6 - 0 = m + 6 from by omega, show m + 6 - 1 = m + 5 from by omega,
      show m + 6 - 2 = m + 4 from by omega, show m + 6 - 3 = m + 3 from by omega,
      show m + 6 - 4 = m + 2 from by omega, show m + 6 - 5 = m + 1 from by omega]
    have hrec := rec_gen m
    linarith
