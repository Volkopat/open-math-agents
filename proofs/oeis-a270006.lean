import OMAStatements.S_oeis_a270006
import Mathlib

namespace A270006Aux
open OMA.S_oeis_a270006 in
lemma step_gen (code t : ℕ) (f g : ℤ → ℤ → Bool)
    (hf : ∀ i j, cell code t i j = f i j)
    (h : ∀ (i j : ℤ), g i j = code.testBit ((f i j).toNat + 2 * ((f (i + 1) j).toNat +
      (f (i - 1) j).toNat + (f i (j + 1)).toNat + (f i (j - 1)).toNat))) :
    ∀ i j, cell code (t + 1) i j = g i j := by
  intro i j
  show code.testBit ((cell code t i j).toNat + 2 * ((cell code t (i + 1) j).toNat +
      (cell code t (i - 1) j).toNat + (cell code t i (j + 1)).toNat +
      (cell code t i (j - 1)).toNat)) = g i j
  rw [hf, hf, hf, hf, hf]
  exact (h i j).symm

lemma win (g : ℤ → ℕ) (r : ℕ) (hg : ∀ x : ℤ, (x < -(r : ℤ) ∨ (r : ℤ) < x) → g x = 0) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * (r + m) + 1), g ((i : ℤ) - ((r + m : ℕ) : ℤ)) =
      ∑ i ∈ Finset.range (2 * r + 1), g ((i : ℤ) - (r : ℤ)) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (r + (k + 1)) + 1 = (2 * (r + k) + 1) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ', ← ih]
    have e1 : g (((2 * (r + k) + 1 + 1 : ℕ) : ℤ) - ((r + (k + 1) : ℕ) : ℤ)) = 0 :=
      hg _ (by push_cast; omega)
    have e2 : g (((0 : ℕ) : ℤ) - ((r + (k + 1) : ℕ) : ℤ)) = 0 := hg _ (by push_cast; omega)
    rw [e1, e2, add_zero, add_zero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    push_cast
    ring

lemma win2 (F : ℤ → ℤ → ℕ) (r : ℕ)
    (hF : ∀ x y : ℤ, (x < -(r : ℤ) ∨ (r : ℤ) < x ∨ y < -(r : ℤ) ∨ (r : ℤ) < y) → F x y = 0)
    (m : ℕ) :
    ∑ i ∈ Finset.range (2 * (r + m) + 1), ∑ j ∈ Finset.range (2 * (r + m) + 1),
        F ((i : ℤ) - ((r + m : ℕ) : ℤ)) ((j : ℤ) - ((r + m : ℕ) : ℤ)) =
      ∑ i ∈ Finset.range (2 * r + 1), ∑ j ∈ Finset.range (2 * r + 1),
        F ((i : ℤ) - (r : ℤ)) ((j : ℤ) - (r : ℤ)) := by
  have h1 : ∀ x : ℤ, ∑ j ∈ Finset.range (2 * (r + m) + 1), F x ((j : ℤ) - ((r + m : ℕ) : ℤ)) =
      ∑ j ∈ Finset.range (2 * r + 1), F x ((j : ℤ) - (r : ℤ)) := fun x =>
    win (F x) r (fun y hy => hF x y (by omega)) m
  simp only [h1]
  exact win (fun x => ∑ j ∈ Finset.range (2 * r + 1), F x ((j : ℤ) - (r : ℤ))) r
    (fun x hx => Finset.sum_eq_zero (fun j _ => hF x _ (by omega))) m

lemma compl2 (p : ℤ → ℤ → Bool) (t : ℕ) :
    (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0)) +
      (∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 0 else 1)) =
      (2 * t + 1) * (2 * t + 1) := by
  rw [← Finset.sum_add_distrib]
  have h : ∀ i ∈ Finset.range (2 * t + 1),
      (∑ j ∈ Finset.range (2 * t + 1), (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0)) +
      (∑ j ∈ Finset.range (2 * t + 1), (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 0 else 1))
      = 2 * t + 1 := by
    intro i _
    rw [← Finset.sum_add_distrib]
    have h2 : ∀ j ∈ Finset.range (2 * t + 1),
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0) +
        (if p ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 0 else 1) = 1 := by
      intro j _
      split_ifs <;> rfl
    rw [Finset.sum_congr rfl h2]
    simp
  rw [Finset.sum_congr rfl h]
  simp
def p0 (i j : ℤ) : Bool :=
  decide ((i = 0 ∧ j = 0))
def p1 (i j : ℤ) : Bool :=
  decide (¬((i = 0 ∧ j = 0)))
def p2 (_ _ : ℤ) : Bool := false
def p3 (_ _ : ℤ) : Bool := true

lemma far0 (i j : ℤ) (h : i < -0 ∨ 0 < i ∨ j < -0 ∨ 0 < j) : p0 i j = false := by
  simp only [p0, decide_eq_false_iff_not]
  omega

lemma far1 (i j : ℤ) (h : i < -0 ∨ 0 < i ∨ j < -0 ∨ 0 < j) : p1 i j = true := by
  simp only [p1, decide_eq_true_eq]
  omega

lemma far2 (i j : ℤ) : p2 i j = false := rfl

lemma far3 (i j : ℤ) : p3 i j = true := rfl

def box1 : List ℤ := [-1, 0, 1]

lemma mem_box1 (x : ℤ) (h1 : -1 ≤ x) (h2 : x ≤ 1) : x ∈ box1 := by
  unfold box1
  simp
  omega

lemma trbox_0_1 : ∀ i ∈ box1, ∀ j ∈ box1, p1 i j =
    Nat.testBit 5 ((p0 i j).toNat + 2 * ((p0 (i + 1) j).toNat + (p0 (i - 1) j).toNat + (p0 i (j + 1)).toNat + (p0 i (j - 1)).toNat)) := by
  decide

lemma tr_0_1 (i j : ℤ) : p1 i j =
    Nat.testBit 5 ((p0 i j).toNat + 2 * ((p0 (i + 1) j).toNat + (p0 (i - 1) j).toNat + (p0 i (j + 1)).toNat + (p0 i (j - 1)).toNat)) := by
  by_cases h : (-1 ≤ i ∧ i ≤ 1) ∧ (-1 ≤ j ∧ j ≤ 1)
  · exact trbox_0_1 i (mem_box1 i h.1.1 h.1.2) j (mem_box1 j h.2.1 h.2.2)
  · rw [far1 i j (by omega), far0 i j (by omega), far0 (i + 1) j (by omega), far0 (i - 1) j (by omega),
      far0 i (j + 1) (by omega), far0 i (j - 1) (by omega)]
    decide

lemma trbox_1_2 : ∀ i ∈ box1, ∀ j ∈ box1, p2 i j =
    Nat.testBit 5 ((p1 i j).toNat + 2 * ((p1 (i + 1) j).toNat + (p1 (i - 1) j).toNat + (p1 i (j + 1)).toNat + (p1 i (j - 1)).toNat)) := by
  decide

lemma tr_1_2 (i j : ℤ) : p2 i j =
    Nat.testBit 5 ((p1 i j).toNat + 2 * ((p1 (i + 1) j).toNat + (p1 (i - 1) j).toNat + (p1 i (j + 1)).toNat + (p1 i (j - 1)).toNat)) := by
  by_cases h : (-1 ≤ i ∧ i ≤ 1) ∧ (-1 ≤ j ∧ j ≤ 1)
  · exact trbox_1_2 i (mem_box1 i h.1.1 h.1.2) j (mem_box1 j h.2.1 h.2.2)
  · rw [far2 i j, far1 i j (by omega), far1 (i + 1) j (by omega), far1 (i - 1) j (by omega),
      far1 i (j + 1) (by omega), far1 i (j - 1) (by omega)]
    decide

lemma trbox_2_3 : ∀ i ∈ box1, ∀ j ∈ box1, p3 i j =
    Nat.testBit 5 ((p2 i j).toNat + 2 * ((p2 (i + 1) j).toNat + (p2 (i - 1) j).toNat + (p2 i (j + 1)).toNat + (p2 i (j - 1)).toNat)) := by
  decide

lemma tr_2_3 (i j : ℤ) : p3 i j =
    Nat.testBit 5 ((p2 i j).toNat + 2 * ((p2 (i + 1) j).toNat + (p2 (i - 1) j).toNat + (p2 i (j + 1)).toNat + (p2 i (j - 1)).toNat)) := by
  by_cases h : (-1 ≤ i ∧ i ≤ 1) ∧ (-1 ≤ j ∧ j ≤ 1)
  · exact trbox_2_3 i (mem_box1 i h.1.1 h.1.2) j (mem_box1 j h.2.1 h.2.2)
  · rw [far3 i j, far2 i j, far2 (i + 1) j, far2 (i - 1) j,
      far2 i (j + 1), far2 i (j - 1)]
    decide

lemma trbox_3_2 : ∀ i ∈ box1, ∀ j ∈ box1, p2 i j =
    Nat.testBit 5 ((p3 i j).toNat + 2 * ((p3 (i + 1) j).toNat + (p3 (i - 1) j).toNat + (p3 i (j + 1)).toNat + (p3 i (j - 1)).toNat)) := by
  decide

lemma tr_3_2 (i j : ℤ) : p2 i j =
    Nat.testBit 5 ((p3 i j).toNat + 2 * ((p3 (i + 1) j).toNat + (p3 (i - 1) j).toNat + (p3 i (j + 1)).toNat + (p3 i (j - 1)).toNat)) := by
  by_cases h : (-1 ≤ i ∧ i ≤ 1) ∧ (-1 ≤ j ∧ j ≤ 1)
  · exact trbox_3_2 i (mem_box1 i h.1.1 h.1.2) j (mem_box1 j h.2.1 h.2.2)
  · rw [far2 i j, far3 i j, far3 (i + 1) j, far3 (i - 1) j,
      far3 i (j + 1), far3 i (j - 1)]
    decide

open OMA.S_oeis_a270006 in
lemma c0 : ∀ i j, cell 5 0 i j = p0 i j := by
  intro i j
  rfl

open OMA.S_oeis_a270006 in
lemma c1 : ∀ i j, cell 5 1 i j = p1 i j :=
  step_gen 5 0 p0 p1 c0 tr_0_1

open OMA.S_oeis_a270006 in
lemma c2 : ∀ i j, cell 5 2 i j = p2 i j :=
  step_gen 5 1 p1 p2 c1 tr_1_2

open OMA.S_oeis_a270006 in
lemma c3 : ∀ i j, cell 5 3 i j = p3 i j :=
  step_gen 5 2 p2 p3 c2 tr_2_3

open OMA.S_oeis_a270006 in
lemma cPer (n : ℕ) : (∀ i j, cell 5 (2 * n + 2) i j = p2 i j) ∧
    (∀ i j, cell 5 (2 * n + 2 + 1) i j = p3 i j) := by
  induction n with
  | zero => exact ⟨c2, c3⟩
  | succ k ih =>
    have h1 : ∀ i j, cell 5 (2 * (k + 1) + 2) i j = p2 i j :=
      step_gen 5 (2 * k + 2 + 1) p3 p2 ih.2 tr_3_2
    exact ⟨h1, step_gen 5 (2 * (k + 1) + 2) p2 p3 h1 tr_2_3⟩

open OMA.S_oeis_a270006 in
lemma cA (t : ℕ) (ht : 2 ≤ t) (hp : t % 2 = 0) : ∀ i j, cell 5 t i j = p2 i j := by
  obtain ⟨n, rfl⟩ : ∃ n, t = 2 * n + 2 := ⟨(t - 2) / 2, by omega⟩
  exact (cPer n).1

open OMA.S_oeis_a270006 in
lemma cB (t : ℕ) (ht : 2 ≤ t) (hp : t % 2 = 1) : ∀ i j, cell 5 t i j = p3 i j := by
  obtain ⟨n, rfl⟩ : ∃ n, t = 2 * n + 2 + 1 := ⟨(t - 2 - 1) / 2, by omega⟩
  exact (cPer n).2

open OMA.S_oeis_a270006 in
lemma on0 : onCount 5 0 = 1 := by
  unfold onCount
  simp only [c0]
  decide

open OMA.S_oeis_a270006 in
lemma on1 : onCount 5 1 = 8 := by
  unfold onCount
  simp only [c1]
  decide

lemma cnt2 (t : ℕ) : ((∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
    (if p2 ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0) : ℕ) : ℤ) = 0 := by
  simp [p2]

lemma cnt3 (t : ℕ) : ((∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
    (if p3 ((i : ℤ) - (t : ℤ)) ((j : ℤ) - (t : ℤ)) then 1 else 0) : ℕ) : ℤ) = (2 * (t : ℤ) + 1) ^ 2 := by
  simp [p3]
  ring

open OMA.S_oeis_a270006 in
lemma onA (t : ℕ) (ht : 2 ≤ t) (hp : t % 2 = 0) : (onCount 5 t : ℤ) = 0 := by
  unfold onCount
  simp only [cA t ht hp]
  exact cnt2 t

open OMA.S_oeis_a270006 in
lemma onB (t : ℕ) (ht : 2 ≤ t) (hp : t % 2 = 1) : (onCount 5 t : ℤ) = (2 * (t : ℤ) + 1) ^ 2 := by
  unfold onCount
  simp only [cB t ht hp]
  exact cnt3 t

open OMA.S_oeis_a270006 in
lemma onQ (t : ℕ) (ht : 2 ≤ t) : (onCount 5 t : ℚ) = (1 + (-1 : ℚ) ^ t) / 2 * (0) + (1 - (-1 : ℚ) ^ t) / 2 * ((2 * (t : ℚ) + 1) ^ 2) := by
  rcases Nat.even_or_odd t with h | h
  · have h1 := onA t ht (Nat.even_iff.mp h)
    have h2 : ((onCount 5 t : ℤ) : ℚ) = 0 := by rw [h1]; push_cast; ring
    rw [h.neg_one_pow]
    have h3 : (onCount 5 t : ℚ) = 0 := by exact_mod_cast h2
    rw [h3]; ring
  · have h1 := onB t ht (Nat.odd_iff.mp h)
    have h2 : ((onCount 5 t : ℤ) : ℚ) = (2 * (t : ℚ) + 1) ^ 2 := by rw [h1]; push_cast; ring
    rw [h.neg_one_pow]
    have h3 : (onCount 5 t : ℚ) = (2 * (t : ℚ) + 1) ^ 2 := by exact_mod_cast h2
    rw [h3]; ring

open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

open OMA.S_oeis_a270006 in
lemma oq0 : (onCount 5 0 : ℚ) = 1 := by
  rw [on0]; norm_num

open OMA.S_oeis_a270006 in
lemma oq1 : (onCount 5 1 : ℚ) = 8 := by
  rw [on1]; norm_num

open OMA.S_oeis_a270006 in
lemma oq2 : (onCount 5 2 : ℚ) = 0 := by
  rw [onQ 2 (by norm_num)]; norm_num

open OMA.S_oeis_a270006 in
lemma oq3 : (onCount 5 3 : ℚ) = 49 := by
  rw [onQ 3 (by norm_num)]; norm_num

open OMA.S_oeis_a270006 in
lemma oq4 : (onCount 5 4 : ℚ) = 0 := by
  rw [onQ 4 (by norm_num)]; norm_num

open OMA.S_oeis_a270006 in
lemma oq5 : (onCount 5 5 : ℚ) = 121 := by
  rw [onQ 5 (by norm_num)]; norm_num

open OMA.S_oeis_a270006 in
lemma oq6 : (onCount 5 6 : ℚ) = 0 := by
  rw [onQ 6 (by norm_num)]; norm_num

open OMA.S_oeis_a270006 in
lemma oq7 : (onCount 5 7 : ℚ) = 225 := by
  rw [onQ 7 (by norm_num)]; norm_num

open OMA.S_oeis_a270006 in
lemma oq8 : (onCount 5 8 : ℚ) = 0 := by
  rw [onQ 8 (by norm_num)]; norm_num

open OMA.S_oeis_a270006 in
lemma oq9 : (onCount 5 9 : ℚ) = 361 := by
  rw [onQ 9 (by norm_num)]; norm_num

open OMA.S_oeis_a270006 in
lemma oq10 : (onCount 5 10 : ℚ) = 0 := by
  rw [onQ 10 (by norm_num)]; norm_num

open OMA.S_oeis_a270006 in
lemma e0 : (a 0 : ℚ) = 1 := by
  unfold a; push_cast; rw [oq0]

open OMA.S_oeis_a270006 in
lemma e1 : (a 1 : ℚ) = 8 := by
  unfold a; push_cast; rw [oq1]

open OMA.S_oeis_a270006 in
lemma e2 : (a 2 : ℚ) = 0 := by
  unfold a; push_cast; rw [oq2]

open OMA.S_oeis_a270006 in
lemma e3 : (a 3 : ℚ) = 49 := by
  unfold a; push_cast; rw [oq3]

open OMA.S_oeis_a270006 in
lemma e4 : (a 4 : ℚ) = 0 := by
  unfold a; push_cast; rw [oq4]

open OMA.S_oeis_a270006 in
lemma e5 : (a 5 : ℚ) = 121 := by
  unfold a; push_cast; rw [oq5]

open OMA.S_oeis_a270006 in
lemma e6 : (a 6 : ℚ) = 0 := by
  unfold a; push_cast; rw [oq6]

open OMA.S_oeis_a270006 in
lemma e7 : (a 7 : ℚ) = 225 := by
  unfold a; push_cast; rw [oq7]

open OMA.S_oeis_a270006 in
lemma e8 : (a 8 : ℚ) = 0 := by
  unfold a; push_cast; rw [oq8]

open OMA.S_oeis_a270006 in
lemma aQ (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = (1 + (-1 : ℚ) ^ n) / 2 * (0) + (1 - (-1 : ℚ) ^ n) / 2 * ((2 * (n : ℚ) + 1) ^ 2) := by
  unfold a; push_cast; rw [onQ n (by omega)]

end A270006Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a270006 A270006Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a270006.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [aQ n (by omega)]
    ring
  · intro n hn hpar
    rw [aQ n (by omega)]
    rw [hpar.neg_one_pow]
    ring
  · intro n hn hpar
    rw [aQ n (by omega)]
    rw [hpar.neg_one_pow]
    ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simp only [show m + 8 - 2 = m + 6 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 6 = m + 2 by omega]
    rw [aQ (m + 8) (by omega), aQ (m + 6) (by omega), aQ (m + 4) (by omega), aQ (m + 2) (by omega)]
    push_cast
    ring
  · have hD : ((1 - X) ^ 3 * (1 + X) ^ 3 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-3) * PowerSeries.X ^ 2 + PowerSeries.C 3 * PowerSeries.X ^ 4 + PowerSeries.C (-1) * PowerSeries.X ^ 6 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + 8 * X - 3 * X ^ 2 + 25 * X ^ 3 + 3 * X ^ 4 - 2 * X ^ 5 - X ^ 6 + X ^ 7 : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 8 * PowerSeries.X ^ 1 + PowerSeries.C (-3) * PowerSeries.X ^ 2 + PowerSeries.C 25 * PowerSeries.X ^ 3 + PowerSeries.C 3 * PowerSeries.X ^ 4 + PowerSeries.C (-2) * PowerSeries.X ^ 5 + PowerSeries.C (-1) * PowerSeries.X ^ 6 + PowerSeries.C 1 * PowerSeries.X ^ 7 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e1]
    · norm_num [e0, e2]
    · norm_num [e1, e3]
    · norm_num [e0, e2, e4]
    · norm_num [e1, e3, e5]
    · norm_num [e0, e2, e4, e6]
    · norm_num [e1, e3, e5, e7]
    · have f2 := aQ (n + 2) (by omega)
      have f4 := aQ (n + 4) (by omega)
      have f6 := aQ (n + 6) (by omega)
      have f8 := aQ (n + 8) (by omega)
      simp [show n + 8 - 2 = n + 6 by omega, show n + 8 - 4 = n + 4 by omega, show n + 8 - 6 = n + 2 by omega, f2, f4, f6, f8]
      ring
