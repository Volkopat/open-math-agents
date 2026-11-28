import OMAStatements.S_oeis_a133308
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: Zeilberger certificate (found with sympy) for the Narayana-type sum, termwise identity by field_simp and ring, telescoping with Finset.sum_range_sub.

namespace OMA.S_oeis_a133308

lemma K1 (n k : ℕ) : ((n.choose (k+1) : ℕ) : ℚ) * ((k:ℚ)+1) = (n.choose k : ℚ) * ((n:ℚ) - k) := by
  rcases le_or_gt k n with h | h
  · have h2 := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_succ_right_eq n k)
    push_cast [Nat.cast_sub h] at h2
    linarith
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma K2 (n k : ℕ) : (((n+1).choose (k+1) : ℕ) : ℚ) * ((k:ℚ)+1) = (n.choose k : ℚ) * ((n:ℚ) + 1) := by
  have h2 := congrArg (Nat.cast : ℕ → ℚ) (Nat.add_one_mul_choose_eq n k)
  push_cast at h2
  linarith

def g (n i : ℕ) : ℚ := (n.choose i : ℚ) * (n.choose (i+1) : ℚ) * (7/8 : ℚ)^i * (8:ℚ)^n

def cc (m j : ℕ) : ℚ :=
  -(((j:ℚ)+1)^2 - 18*((j:ℚ)+1)*m - 19*((j:ℚ)+1) + 25*(m:ℚ)^2 + 67*m + 42) / (8*((m:ℚ)+1)^2)

def Gs (m j : ℕ) : ℚ :=
  cc m j * ((m+1).choose (j+1) : ℚ) * ((m+1).choose j : ℚ) * (7/8 : ℚ)^(j+1) * (8:ℚ)^(m+2)

def L (m i : ℕ) : ℚ :=
  ((m:ℚ)+3)/((m:ℚ)+2) * g (m+2) i - 15*(2*(m:ℚ)+3)/((m:ℚ)+1) * g (m+1) i + g m i

lemma extend (n : ℕ) : ∀ k, ∑ i ∈ Finset.range (n+k), g n i = ∑ i ∈ Finset.range n, g n i := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, Finset.sum_range_succ, ih]
    simp [g, Nat.choose_eq_zero_of_lt (show n < n + k + 1 by omega)]

lemma a_eq (n : ℕ) (hn : n ≠ 0) : a n = (∑ i ∈ Finset.range n, g n i) / n := by
  simp only [a, hn, if_false]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  simp only [g]
  rw [pow_sub₀ (8:ℚ) (by norm_num) hi.le, div_pow]
  field_simp

lemma term (j t : ℕ) : L (j+t) (j+1) = Gs (j+t) (j+1) - Gs (j+t) j := by
  set X : ℚ := ((j+t).choose j : ℚ) with hXd
  set Z : ℚ := X / (((j:ℚ)+1)*((j:ℚ)+2)*((t:ℚ)+1)) with hZd
  have hX : X = Z * (((j:ℚ)+1)*((j:ℚ)+2)*((t:ℚ)+1)) := by
    rw [hZd]; field_simp
  have hj1 : (j:ℚ)+1 ≠ 0 := by positivity
  have hj2 : (j:ℚ)+1+1 ≠ 0 := by positivity
  have ht1 : (t:ℚ)+1 ≠ 0 := by positivity
  have hB1 : (((j+t).choose (j+1) : ℕ) : ℚ) = Z*t*((j:ℚ)+2)*((t:ℚ)+1) := by
    have h := K1 (j+t) j
    push_cast at h
    rw [← hXd, hX] at h
    apply mul_right_cancel₀ hj1
    linear_combination h
  have hB2 : (((j+t).choose (j+1+1) : ℕ) : ℚ) = Z*t*((t:ℚ)-1)*((t:ℚ)+1) := by
    have h := K1 (j+t) (j+1)
    push_cast at h
    rw [hB1] at h
    apply mul_right_cancel₀ hj2
    linear_combination h
  have hB3 : (((j+t+1).choose (j+1) : ℕ) : ℚ) = Z*((j:ℚ)+t+1)*((j:ℚ)+2)*((t:ℚ)+1) := by
    have h := K2 (j+t) j
    push_cast at h
    rw [← hXd, hX] at h
    apply mul_right_cancel₀ hj1
    linear_combination h
  have hB4 : (((j+t+1).choose (j+1+1) : ℕ) : ℚ) = Z*t*((j:ℚ)+t+1)*((t:ℚ)+1) := by
    have h := K2 (j+t) (j+1)
    push_cast at h
    rw [hB1] at h
    apply mul_right_cancel₀ hj2
    linear_combination h
  have hB5 : (((j+t+1).choose j : ℕ) : ℚ) = Z*((j:ℚ)+t+1)*((j:ℚ)+1)*((j:ℚ)+2) := by
    have h := K1 (j+t+1) j
    push_cast at h
    rw [hB3] at h
    apply mul_right_cancel₀ ht1
    linear_combination -h
  have hB6 : (((j+t+2).choose (j+1) : ℕ) : ℚ) = Z*((j:ℚ)+t+1)*((j:ℚ)+t+2)*((j:ℚ)+2) := by
    have h := K2 (j+t+1) j
    push_cast at h
    rw [hB5] at h
    apply mul_right_cancel₀ hj1
    linear_combination h
  have hB7 : (((j+t+2).choose (j+1+1) : ℕ) : ℚ) = Z*((j:ℚ)+t+1)*((j:ℚ)+t+2)*((t:ℚ)+1) := by
    have h := K2 (j+t+1) (j+1)
    push_cast at h
    rw [hB3] at h
    apply mul_right_cancel₀ hj2
    linear_combination h
  simp only [L, g, Gs, cc]
  rw [hB1, hB2, hB3, hB4, hB5, hB6, hB7]
  push_cast
  field_simp
  ring

lemma key (m : ℕ) : ∑ i ∈ Finset.range (m+2), L m i = 0 := by
  rw [Finset.sum_range_succ']
  have h1 : ∑ j ∈ Finset.range (m+1), L m (j+1)
      = ∑ j ∈ Finset.range (m+1), (Gs m (j+1) - Gs m j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp hj)
    exact term j t
  rw [h1, Finset.sum_range_sub]
  have h2 : Gs m (m+1) = 0 := by
    simp [Gs]
  rw [h2]
  simp only [L, g, Gs, cc]
  simp
  field_simp
  ring

theorem main_proof : ∀ n : ℕ, 2 ≤ n →
    ((n : ℚ) + 1) * a n + 15 * (-2 * (n : ℚ) + 1) * a (n - 1) + ((n : ℚ) - 2) * a (n - 2) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    norm_num [a, Finset.sum_range_succ]
  · rw [a_eq (m+2) (by omega), a_eq (m+1) (by omega), a_eq m (by omega)]
    rw [← extend (m+1) 1, ← extend m 2]
    have hk := key m
    simp only [L, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hk
    have hm : (m:ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
    push_cast
    field_simp
    field_simp at hk
    linear_combination (m:ℚ) * hk


end OMA.S_oeis_a133308

theorem OMA.solution : type_of% @OMA.S_oeis_a133308.main := OMA.S_oeis_a133308.main_proof
