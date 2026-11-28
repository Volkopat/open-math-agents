import OMAStatements.S_oeis_a266725
import Mathlib

namespace CAOEISA266725Aux

def F (t : ℕ) (i : ℤ) : Prop :=
  ((t : ℤ) = 0 ∧ i = 0) ∨ ((t : ℤ) % 2 = 1 ∧ ¬(2 * i = (t : ℤ) - 1)) ∨ ((t : ℤ) % 2 = 0 ∧ 2 ≤ (t : ℤ) ∧ (2 * i = (t : ℤ) - 2 ∨ 2 * i = (t : ℤ)))

open OMA.S_oeis_a266725 in
lemma rule_step (b1 b2 b3 : Bool) (P1 P2 P3 Q : Prop) (h1 : b1 = true ↔ P1) (h2 : b2 = true ↔ P2)
    (h3 : b3 = true ↔ P3)
    (H0 : ¬P1 → ¬P2 → ¬P3 → Q) (H1 : ¬P1 → ¬P2 → P3 → Q)
    (H2 : ¬P1 → P2 → ¬P3 → ¬Q) (H3 : ¬P1 → P2 → P3 → Q)
    (H4 : P1 → ¬P2 → ¬P3 → Q) (H5 : P1 → ¬P2 → P3 → Q)
    (H6 : P1 → P2 → ¬P3 → ¬Q) (H7 : P1 → P2 → P3 → ¬Q) :
    ruleOut 59 b1 b2 b3 = true ↔ Q := by
  cases b1 <;> cases b2 <;> cases b3
  · exact ⟨fun _ => H0 (fun h => Bool.false_ne_true (h1.mpr h)) (fun h => Bool.false_ne_true (h2.mpr h)) (fun h => Bool.false_ne_true (h3.mpr h)), fun _ => by decide⟩
  · exact ⟨fun _ => H1 (fun h => Bool.false_ne_true (h1.mpr h)) (fun h => Bool.false_ne_true (h2.mpr h)) (h3.mp rfl), fun _ => by decide⟩
  · exact ⟨fun h => absurd h (by decide), fun q => absurd q (H2 (fun h => Bool.false_ne_true (h1.mpr h)) (h2.mp rfl) (fun h => Bool.false_ne_true (h3.mpr h)))⟩
  · exact ⟨fun _ => H3 (fun h => Bool.false_ne_true (h1.mpr h)) (h2.mp rfl) (h3.mp rfl), fun _ => by decide⟩
  · exact ⟨fun _ => H4 (h1.mp rfl) (fun h => Bool.false_ne_true (h2.mpr h)) (fun h => Bool.false_ne_true (h3.mpr h)), fun _ => by decide⟩
  · exact ⟨fun _ => H5 (h1.mp rfl) (fun h => Bool.false_ne_true (h2.mpr h)) (h3.mp rfl), fun _ => by decide⟩
  · exact ⟨fun h => absurd h (by decide), fun q => absurd q (H6 (h1.mp rfl) (h2.mp rfl) (fun h => Bool.false_ne_true (h3.mpr h)))⟩
  · exact ⟨fun h => absurd h (by decide), fun q => absurd q (H7 (h1.mp rfl) (h2.mp rfl) (h3.mp rfl))⟩

set_option maxHeartbeats 4000000 in
open OMA.S_oeis_a266725 in
lemma cell_iff : ∀ (t : ℕ) (i : ℤ), cell 59 t i = true ↔ F t i := by
  intro t
  induction t with
  | zero =>
    intro i
    rw [cell]
    simp only [decide_eq_true_eq]
    unfold F
    omega
  | succ t ih =>
    intro i
    rw [cell]
    apply rule_step _ _ _ _ _ _ _ (ih (i - 1)) (ih i) (ih (i + 1)) <;> unfold F <;> omega

open OMA.S_oeis_a266725 in
def w (t j : ℕ) : ℕ := if cell 59 t ((j : ℤ) - t) = true then 1 else 0

open OMA.S_oeis_a266725 in
lemma onCount_w (t : ℕ) : onCount 59 t = ∑ j ∈ Finset.range (2 * t + 1), w t j := rfl

lemma w_one (t j : ℕ) (h : F t ((j : ℤ) - t)) : w t j = 1 := by
  unfold w
  rw [if_pos ((cell_iff _ _).mpr h)]

lemma w_zero (t j : ℕ) (h : ¬ F t ((j : ℤ) - t)) : w t j = 0 := by
  unfold w
  rw [if_neg (fun hc => h ((cell_iff _ _).mp hc))]

lemma w_congr (t t' j j' : ℕ) (h : F t ((j : ℤ) - t) ↔ F t' ((j' : ℤ) - t')) : w t j = w t' j' := by
  by_cases hf : F t ((j : ℤ) - t)
  · rw [w_one t j hf, w_one t' j' (h.mp hf)]
  · rw [w_zero t j hf, w_zero t' j' (fun h' => hf (h.mpr h'))]


lemma sum_cut (f g : ℕ → ℕ) (A N s1 s2 s3 : ℕ) (hA : A ≤ N)
    (h1 : ∀ j, j < A → f (s1 + j) = g j)
    (h2 : ∀ j, A ≤ j → j < N → f (s1 + s2 + j) = g j) :
    ∑ j ∈ Finset.range (s1 + N + s2 + s3), f j =
      ∑ j ∈ Finset.range N, g j + (∑ k ∈ Finset.range s1, f k + ∑ k ∈ Finset.range s2, f (s1 + A + k)
        + ∑ k ∈ Finset.range s3, f (s1 + N + s2 + k)) := by
  obtain ⟨B, rfl⟩ : ∃ B, N = A + B := ⟨N - A, by omega⟩
  have e : s1 + (A + B) + s2 + s3 = (((s1 + A) + s2) + B) + s3 := by ring
  rw [e, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add,
    Finset.sum_range_add (fun j => g j) A B]
  have e1 : ∑ x ∈ Finset.range A, f (s1 + x) = ∑ x ∈ Finset.range A, g x :=
    Finset.sum_congr rfl (fun x hx => h1 x (Finset.mem_range.mp hx))
  have e2 : ∑ x ∈ Finset.range B, f (s1 + A + s2 + x) = ∑ x ∈ Finset.range B, g (A + x) :=
    Finset.sum_congr rfl (fun x hx => by
      have := h2 (A + x) (by omega) (by have := Finset.mem_range.mp hx; omega)
      rw [← this]
      congr 1
      ring)
  have e3 : ∑ x ∈ Finset.range s3, f (s1 + A + s2 + B + x) = ∑ x ∈ Finset.range s3, f (s1 + (A + B) + s2 + x) :=
    Finset.sum_congr rfl (fun x _ => by congr 1; ring)
  rw [e1, e2, e3]
  ring

open OMA.S_oeis_a266725 in
lemma oc0 : onCount 59 0 = 1 := by
  rw [onCount_w, show 2 * 0 + 1 = 1 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : w 0 0 = 1 := w_one _ _ (by unfold F; omega)
  omega

open OMA.S_oeis_a266725 in
lemma oc1 : onCount 59 1 = 2 := by
  rw [onCount_w, show 2 * 1 + 1 = 3 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : w 1 0 = 1 := w_one _ _ (by unfold F; omega)
  have v1 : w 1 1 = 0 := w_zero _ _ (by unfold F; omega)
  have v2 : w 1 2 = 1 := w_one _ _ (by unfold F; omega)
  omega

open OMA.S_oeis_a266725 in
lemma oc2 : onCount 59 2 = 2 := by
  rw [onCount_w, show 2 * 2 + 1 = 5 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : w 2 0 = 0 := w_zero _ _ (by unfold F; omega)
  have v1 : w 2 1 = 0 := w_zero _ _ (by unfold F; omega)
  have v2 : w 2 2 = 1 := w_one _ _ (by unfold F; omega)
  have v3 : w 2 3 = 1 := w_one _ _ (by unfold F; omega)
  have v4 : w 2 4 = 0 := w_zero _ _ (by unfold F; omega)
  omega

open OMA.S_oeis_a266725 in
lemma oc3 : onCount 59 3 = 6 := by
  rw [onCount_w, show 2 * 3 + 1 = 7 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : w 3 0 = 1 := w_one _ _ (by unfold F; omega)
  have v1 : w 3 1 = 1 := w_one _ _ (by unfold F; omega)
  have v2 : w 3 2 = 1 := w_one _ _ (by unfold F; omega)
  have v3 : w 3 3 = 1 := w_one _ _ (by unfold F; omega)
  have v4 : w 3 4 = 0 := w_zero _ _ (by unfold F; omega)
  have v5 : w 3 5 = 1 := w_one _ _ (by unfold F; omega)
  have v6 : w 3 6 = 1 := w_one _ _ (by unfold F; omega)
  omega

set_option maxHeartbeats 4000000 in
open OMA.S_oeis_a266725 in
lemma ocstep0 (m : ℕ) : onCount 59 (2 + 2 * (m + 1)) = onCount 59 (2 + 2 * m) + 0 := by
  rw [onCount_w, onCount_w]
  rw [show 2 * (2 + 2 * (m + 1)) + 1 = 3 + (2 * (2 + 2 * m) + 1) + 0 + 1 from by ring]
  rw [sum_cut (w (2 + 2 * (m + 1))) (w (2 + 2 * m)) (2 * (2 + 2 * m) + 1) (2 * (2 + 2 * m) + 1) 3 0 1 (by omega)
    (fun j hj => w_congr _ _ _ _ (by unfold F; omega))
    (fun j hj1 hj2 => w_congr _ _ _ _ (by unfold F; omega))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v1 : w (2 + 2 * (m + 1)) (0) = 0 := w_zero _ _ (by unfold F; omega)
  have v2 : w (2 + 2 * (m + 1)) (1) = 0 := w_zero _ _ (by unfold F; omega)
  have v3 : w (2 + 2 * (m + 1)) (2) = 0 := w_zero _ _ (by unfold F; omega)
  have v4 : w (2 + 2 * (m + 1)) (3 + (2 * (2 + 2 * m) + 1) + 0 + 0) = 0 := w_zero _ _ (by unfold F; omega)
  omega

open OMA.S_oeis_a266725 in
lemma ocr0 (m : ℕ) : onCount 59 (2 + 2 * m) = 2 + 0 * m := by
  induction m with
  | zero => exact oc2
  | succ k ih =>
    rw [ocstep0, ih]
    ring

set_option maxHeartbeats 4000000 in
open OMA.S_oeis_a266725 in
lemma ocstep1 (m : ℕ) : onCount 59 (3 + 2 * (m + 1)) = onCount 59 (3 + 2 * m) + 4 := by
  rw [onCount_w, onCount_w]
  rw [show 2 * (3 + 2 * (m + 1)) + 1 = 3 + (2 * (3 + 2 * m) + 1) + 0 + 1 from by ring]
  rw [sum_cut (w (3 + 2 * (m + 1))) (w (3 + 2 * m)) (2 * (3 + 2 * m) + 1) (2 * (3 + 2 * m) + 1) 3 0 1 (by omega)
    (fun j hj => w_congr _ _ _ _ (by unfold F; omega))
    (fun j hj1 hj2 => w_congr _ _ _ _ (by unfold F; omega))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v1 : w (3 + 2 * (m + 1)) (0) = 1 := w_one _ _ (by unfold F; omega)
  have v2 : w (3 + 2 * (m + 1)) (1) = 1 := w_one _ _ (by unfold F; omega)
  have v3 : w (3 + 2 * (m + 1)) (2) = 1 := w_one _ _ (by unfold F; omega)
  have v4 : w (3 + 2 * (m + 1)) (3 + (2 * (3 + 2 * m) + 1) + 0 + 0) = 1 := w_one _ _ (by unfold F; omega)
  omega

open OMA.S_oeis_a266725 in
lemma ocr1 (m : ℕ) : onCount 59 (3 + 2 * m) = 6 + 4 * m := by
  induction m with
  | zero => exact oc3
  | succ k ih =>
    rw [ocstep1, ih]
    ring

open OMA.S_oeis_a266725 in
lemma ocE (m : ℕ) : (onCount 59 (2 + 2 * m) : ℤ) = 2 + 0 * (m : ℤ) := by
  rw [ocr0]
  push_cast
  ring

open OMA.S_oeis_a266725 in
lemma ocO (m : ℕ) : (onCount 59 (2 + 2 * m + 1) : ℤ) = 6 + 4 * (m : ℤ) := by
  rw [show 2 + 2 * m + 1 = 3 + 2 * m from by ring, ocr1]
  push_cast
  ring


open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

open OMA.S_oeis_a266725 in
lemma oc_eq (n : ℕ) (hn : 2 ≤ n) : (onCount 59 n : ℚ) = ((1 : ℚ) + (1 : ℚ) * (n : ℚ)) + (-1 : ℚ) ^ n * ((1 : ℚ) + (-1 : ℚ) * (n : ℚ)) := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 + 2 * m ∨ n = 2 + 2 * m + 1 := ⟨(n - 2) / 2, by omega⟩
  · have hs : (-1 : ℚ) ^ (2 + 2 * m) = 1 := Even.neg_one_pow ⟨1 + m, by ring⟩
    have h := ocE m
    have h' : ((onCount 59 (2 + 2 * m) : ℕ) : ℚ) = (((onCount 59 (2 + 2 * m) : ℕ) : ℤ) : ℚ) := by norm_cast
    rw [h', h, hs]
    push_cast
    ring
  · have hs : (-1 : ℚ) ^ (2 + 2 * m + 1) = -1 := Odd.neg_one_pow ⟨1 + m, by ring⟩
    have h := ocO m
    have h' : ((onCount 59 (2 + 2 * m + 1) : ℕ) : ℚ) = (((onCount 59 (2 + 2 * m + 1) : ℕ) : ℤ) : ℚ) := by norm_cast
    rw [h', h, hs]
    push_cast
    ring

open OMA.S_oeis_a266725 in
lemma a_eq (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = (((1 : ℚ) / 4) + ((1 : ℚ) / 2) * (n : ℚ) + ((1 : ℚ) / 2) * (n : ℚ) ^ 2) + (-1 : ℚ) ^ n * ((-(1 : ℚ) / 4) + ((1 : ℚ) / 2) * (n : ℚ)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3]
  | succ k hk ih =>
    have e : (a (k + 1) : ℚ) = (a k : ℚ) + ((2 * ((k : ℚ) + 1) + 1) - (onCount 59 (k + 1) : ℚ)) := by
      unfold a
      rw [Finset.sum_range_succ]
      push_cast
      ring
    rw [e, ih, oc_eq (k + 1) (by omega), pow_succ]
    push_cast
    ring

open OMA.S_oeis_a266725 in
lemma av0 : (a 0 : ℚ) = 0 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3]

open OMA.S_oeis_a266725 in
lemma av1 : (a 1 : ℚ) = 1 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3]

open OMA.S_oeis_a266725 in
lemma av2 : (a 2 : ℚ) = 4 := by
  rw [a_eq 2 (by norm_num)]
  norm_num

open OMA.S_oeis_a266725 in
lemma av3 : (a 3 : ℚ) = 5 := by
  rw [a_eq 3 (by norm_num)]
  norm_num

open OMA.S_oeis_a266725 in
lemma av4 : (a 4 : ℚ) = 12 := by
  rw [a_eq 4 (by norm_num)]
  norm_num

open OMA.S_oeis_a266725 in
lemma av5 : (a 5 : ℚ) = 13 := by
  rw [a_eq 5 (by norm_num)]
  norm_num

open OMA.S_oeis_a266725 in
lemma av6 : (a 6 : ℚ) = 24 := by
  rw [a_eq 6 (by norm_num)]
  norm_num

open OMA.S_oeis_a266725 in
lemma av7 : (a 7 : ℚ) = 25 := by
  rw [a_eq 7 (by norm_num)]
  norm_num

end CAOEISA266725Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a266725 CAOEISA266725Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a266725.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · rw [av0]
        norm_num
      · rw [av1]
        norm_num
    · rw [a_eq n h]
      ring
  · intro n hn
    rcases Nat.lt_or_ge n 7 with h | h
    · interval_cases n
      · norm_num [av0, av1, av2, av3, av4, av5]
      · norm_num [av1, av2, av3, av4, av5, av6]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
      rw [show m + 7 - 1 = m + 6 from by omega, show m + 7 - 2 = m + 5 from by omega, show m + 7 - 3 = m + 4 from by omega, show m + 7 - 4 = m + 3 from by omega, show m + 7 - 5 = m + 2 from by omega]
      rw [a_eq (m + 7) (by omega), a_eq (m + 6) (by omega), a_eq (m + 5) (by omega), a_eq (m + 4) (by omega), a_eq (m + 3) (by omega), a_eq (m + 2) (by omega)]
      push_cast
      ring
  · have hD : (((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-1) * PowerSeries.X ^ 1 + PowerSeries.C (-2) * PowerSeries.X ^ 2 + PowerSeries.C 2 * PowerSeries.X ^ 3 + PowerSeries.C 1 * PowerSeries.X ^ 4 + PowerSeries.C (-1) * PowerSeries.X ^ 5 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : ((PowerSeries.X * (1 + 3 * PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3)) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 1 + PowerSeries.C 3 * PowerSeries.X ^ 2 + PowerSeries.C (-1) * PowerSeries.X ^ 3 + PowerSeries.C 1 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 7 with h | h
    · interval_cases n
      · norm_num [av0]
      · norm_num [av0, av1]
      · norm_num [av0, av1, av2]
      · norm_num [av0, av1, av2, av3]
      · norm_num [av0, av1, av2, av3, av4]
      · norm_num [av0, av1, av2, av3, av4, av5]
      · norm_num [av1, av2, av3, av4, av5, av6]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
      rw [if_pos (show 0 ≤ m + 7 from by omega), if_pos (show 1 ≤ m + 7 from by omega), if_pos (show 2 ≤ m + 7 from by omega), if_pos (show 3 ≤ m + 7 from by omega), if_pos (show 4 ≤ m + 7 from by omega), if_pos (show 5 ≤ m + 7 from by omega)]
      rw [if_neg (show ¬ (m + 7 = 1) from by omega), if_neg (show ¬ (m + 7 = 2) from by omega), if_neg (show ¬ (m + 7 = 3) from by omega), if_neg (show ¬ (m + 7 = 4) from by omega)]
      rw [show m + 7 - 0 = m + 7 from by omega, show m + 7 - 1 = m + 6 from by omega, show m + 7 - 2 = m + 5 from by omega, show m + 7 - 3 = m + 4 from by omega, show m + 7 - 4 = m + 3 from by omega, show m + 7 - 5 = m + 2 from by omega]
      rw [a_eq (m + 7) (by omega), a_eq (m + 6) (by omega), a_eq (m + 5) (by omega), a_eq (m + 4) (by omega), a_eq (m + 3) (by omega), a_eq (m + 2) (by omega)]
      push_cast
      ring
