import OMAStatements.S_oeis_a104722
import Mathlib

namespace A104722Aux

lemma catalan_rec (k : ℕ) :
    ((k : ℤ) + 2) * (catalan (k + 1) : ℤ) = 2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ) := by
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  have h4 : (k + 1) * ((k + 2) * catalan (k + 1)) = (k + 1) * (2 * (2 * k + 1) * catalan k) := by
    calc (k + 1) * ((k + 2) * catalan (k + 1))
        = (k + 1) * ((k + 1 + 1) * catalan (k + 1)) := by ring
      _ = (k + 1) * Nat.centralBinom (k + 1) := by rw [h1]
      _ = 2 * (2 * k + 1) * Nat.centralBinom k := h3
      _ = 2 * (2 * k + 1) * ((k + 1) * catalan k) := by rw [h2]
      _ = (k + 1) * (2 * (2 * k + 1) * catalan k) := by ring
  have h5 := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) h4
  exact_mod_cast h5

lemma sum_even_odd (f : ℕ → ℤ) (m : ℕ) : ∑ k ∈ Finset.range (2 * m), f k =
    ∑ i ∈ Finset.range m, f (2 * i) + ∑ i ∈ Finset.range m, f (2 * i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring

lemma conv (j : ℕ) : ∑ i ∈ Finset.range (j + 1), (catalan i : ℤ) * (catalan (j - i) : ℤ) =
    (catalan (j + 1) : ℤ) := by
  rw [catalan_succ]
  push_cast
  rw [Fin.sum_univ_eq_sum_range (fun i => (catalan i : ℤ) * (catalan (j - i) : ℤ)) (j + 1)]

open OMA.S_oeis_a104722 in
lemma a_odd (j : ℕ) : a (2 * j + 1) = 2 * (catalan (j + 1) : ℤ) := by
  unfold a
  rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, sum_even_odd]
  have h1 : ∀ i ∈ Finset.range (j + 1), (b (2 * i) : ℤ) * (b (2 * j + 1 - 2 * i) : ℤ) =
      (catalan i : ℤ) * (catalan (j - i) : ℤ) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    unfold b
    rw [show 2 * i / 2 = i by omega, show (2 * j + 1 - 2 * i) / 2 = j - i by omega]
  have h2 : ∀ i ∈ Finset.range (j + 1), (b (2 * i + 1) : ℤ) * (b (2 * j + 1 - (2 * i + 1)) : ℤ) =
      (catalan i : ℤ) * (catalan (j - i) : ℤ) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    unfold b
    rw [show (2 * i + 1) / 2 = i by omega, show (2 * j + 1 - (2 * i + 1)) / 2 = j - i by omega]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, conv]
  ring

open OMA.S_oeis_a104722 in
lemma a_even (j : ℕ) : a (2 * (j + 1)) = (catalan (j + 2) : ℤ) + (catalan (j + 1) : ℤ) := by
  unfold a
  rw [Finset.sum_range_succ, sum_even_odd]
  have h1 : ∀ i ∈ Finset.range (j + 1), (b (2 * i) : ℤ) * (b (2 * (j + 1) - 2 * i) : ℤ) =
      (catalan i : ℤ) * (catalan (j + 1 - i) : ℤ) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    unfold b
    rw [show 2 * i / 2 = i by omega, show (2 * (j + 1) - 2 * i) / 2 = j + 1 - i by omega]
  have h2 : ∀ i ∈ Finset.range (j + 1), (b (2 * i + 1) : ℤ) * (b (2 * (j + 1) - (2 * i + 1)) : ℤ) =
      (catalan i : ℤ) * (catalan (j - i) : ℤ) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    unfold b
    rw [show (2 * i + 1) / 2 = i by omega, show (2 * (j + 1) - (2 * i + 1)) / 2 = j - i by omega]
  have h3 : (b (2 * (j + 1)) : ℤ) * (b (2 * (j + 1) - 2 * (j + 1)) : ℤ) =
      (catalan (j + 1) : ℤ) * (catalan (j + 1 - (j + 1)) : ℤ) := by
    unfold b
    rw [show 2 * (j + 1) / 2 = j + 1 by omega,
      show (2 * (j + 1) - 2 * (j + 1)) / 2 = j + 1 - (j + 1) by omega]
  have h4 := conv (j + 1)
  rw [Finset.sum_range_succ] at h4
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, h3, conv]
  rw [show j + 1 + 1 = j + 2 by ring] at h4
  linarith

end A104722Aux

open OMA.S_oeis_a104722 A104722Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a104722.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega]
  have r1 := catalan_rec
  obtain ⟨p, rfl | rfl⟩ := Nat.even_or_odd' m
  · have e4 : a (2 * p + 4) = (catalan (p + 3) : ℤ) + (catalan (p + 2) : ℤ) := a_even (p + 1)
    have e3 : a (2 * p + 3) = 2 * (catalan (p + 2) : ℤ) := a_odd (p + 1)
    have e2 : a (2 * p + 2) = (catalan (p + 2) : ℤ) + (catalan (p + 1) : ℤ) := a_even p
    have e1 : a (2 * p + 1) = 2 * (catalan (p + 1) : ℤ) := a_odd p
    rw [e4, e3, e2, e1]
    have q1 := catalan_rec (p + 2)
    have q2 := catalan_rec (p + 1)
    rw [show p + 2 + 1 = p + 3 by ring] at q1
    rw [show p + 1 + 1 = p + 2 by ring] at q2
    push_cast at q1 q2 ⊢
    linear_combination 2 * q1 + 6 * q2
  · have e5 : a (2 * p + 1 + 4) = 2 * (catalan (p + 3) : ℤ) := a_odd (p + 2)
    have e4 : a (2 * p + 1 + 3) = (catalan (p + 3) : ℤ) + (catalan (p + 2) : ℤ) := a_even (p + 1)
    have e3 : a (2 * p + 1 + 2) = 2 * (catalan (p + 2) : ℤ) := a_odd (p + 1)
    have e2 : a (2 * p + 1 + 1) = (catalan (p + 2) : ℤ) + (catalan (p + 1) : ℤ) := a_even p
    rw [e5, e4, e3, e2]
    have q1 := catalan_rec (p + 2)
    have q2 := catalan_rec (p + 1)
    rw [show p + 2 + 1 = p + 3 by ring] at q1
    rw [show p + 1 + 1 = p + 2 by ring] at q2
    push_cast at q1 q2 ⊢
    linear_combination 6 * q1 + 2 * q2
