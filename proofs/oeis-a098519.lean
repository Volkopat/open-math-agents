import OMAStatements.S_oeis_a098519
import Mathlib

namespace A098519Aux

def E : ℤ → ℚ
  | Int.ofNat m => 1 / (m.factorial : ℚ)
  | Int.negSucc _ => 0

lemma E_nat (m : ℕ) : E (m : ℤ) = 1 / (m.factorial : ℚ) := rfl

lemma E_neg (j : ℤ) (h : j < 0) : E j = 0 := by
  obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero h
  rfl

lemma E_pred (j : ℤ) : E (j - 1) = (j : ℚ) * E j := by
  rcases lt_trichotomy j 0 with h | h | h
  · rw [E_neg j h, E_neg (j - 1) (by omega), mul_zero]
  · subst h
    rw [E_neg (0 - 1) (by omega)]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = (m : ℤ) + 1 := ⟨(j - 1).toNat, by omega⟩
    have e1 : ((m : ℤ) + 1 - 1) = (m : ℤ) := by ring
    have e2 : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    have hm : (m.factorial : ℚ) ≠ 0 := by positivity
    rw [e1, E_nat, e2, E_nat, Nat.factorial_succ]
    push_cast
    field_simp

def c (k : ℕ) : ℚ := (3 : ℚ) ^ k / ((k.factorial : ℚ) * ((k + 1).factorial : ℚ))

lemma c_succ (k : ℕ) : 4 * ((k : ℚ) + 1) * ((k : ℚ) + 2) * c (k + 1) = 12 * c k := by
  unfold c
  have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
  rw [Nat.factorial_succ (k + 1), Nat.factorial_succ k]
  push_cast
  field_simp
  ring

def b (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), c k * E ((n : ℤ) - 2 * (k : ℤ) - 1)

lemma b_ext (n N : ℕ) (h : n ≤ N) :
    b n = ∑ k ∈ Finset.range (N + 1), c k * E ((n : ℤ) - 2 * (k : ℤ) - 1) := by
  unfold b
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    rw [E_neg _ (by omega), mul_zero]

open OMA.S_oeis_a098519 in
lemma a_eq (n : ℕ) : a n = (n.factorial : ℚ) * b n := by
  unfold a b
  congr 1
  have h1 : ∀ k ∈ Finset.range (n / 2 + 1),
      (if 2 * k + 1 ≤ n then
        (3 : ℚ) ^ k / ((k.factorial : ℚ) * ((k + 1).factorial : ℚ) * ((n - 2 * k - 1).factorial : ℚ))
      else 0) = c k * E ((n : ℤ) - 2 * (k : ℤ) - 1) := by
    intro k _
    split_ifs with h
    · have e : ((n : ℤ) - 2 * (k : ℤ) - 1) = ((n - 2 * k - 1 : ℕ) : ℤ) := by omega
      rw [e, E_nat]
      unfold c
      have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
      have h2 : ((k + 1).factorial : ℚ) ≠ 0 := by positivity
      have h3 : ((n - 2 * k - 1).factorial : ℚ) ≠ 0 := by positivity
      field_simp
    · rw [E_neg _ (by omega), mul_zero]
  rw [Finset.sum_congr rfl h1]
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    rw [E_neg _ (by omega), mul_zero]

def g (m k : ℕ) : ℚ := 4 * (k : ℚ) * ((k : ℚ) + 1) * c k * E ((m : ℤ) + 2 - 2 * (k : ℤ) - 1)

lemma b_rec (m : ℕ) :
    (((m : ℚ) + 2) ^ 2 - 1) * b (m + 2) - (2 * ((m : ℚ) + 2) - 1) * b (m + 1) - 11 * b m = 0 := by
  have hb2 : b (m + 2) = ∑ k ∈ Finset.range (m + 2 + 1), c k * E ((m : ℤ) + 2 - 2 * (k : ℤ) - 1) := by
    rw [b_ext (m + 2) (m + 2) le_rfl]
    apply Finset.sum_congr rfl
    intro k _
    congr 2
  have hb1 : b (m + 1) = ∑ k ∈ Finset.range (m + 2 + 1), c k * E ((m : ℤ) + 1 - 2 * (k : ℤ) - 1) := by
    rw [b_ext (m + 1) (m + 2) (by omega)]
    apply Finset.sum_congr rfl
    intro k _
    congr 2
  have hb0 : b m = ∑ k ∈ Finset.range (m + 2 + 1), c k * E ((m : ℤ) - 2 * (k : ℤ) - 1) :=
    b_ext m (m + 2) (by omega)
  rw [hb2, hb1, hb0, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  have key : ∀ k ∈ Finset.range (m + 2 + 1),
      (((m : ℚ) + 2) ^ 2 - 1) * (c k * E ((m : ℤ) + 2 - 2 * (k : ℤ) - 1))
        - (2 * ((m : ℚ) + 2) - 1) * (c k * E ((m : ℤ) + 1 - 2 * (k : ℤ) - 1))
        - 11 * (c k * E ((m : ℤ) - 2 * (k : ℤ) - 1)) = g m k - g m (k + 1) := by
    intro k _
    have hE1 : E ((m : ℤ) + 1 - 2 * (k : ℤ) - 1) =
        (((m : ℤ) + 2 - 2 * (k : ℤ) - 1 : ℤ) : ℚ) * E ((m : ℤ) + 2 - 2 * (k : ℤ) - 1) := by
      have h := E_pred ((m : ℤ) + 2 - 2 * (k : ℤ) - 1)
      rw [show ((m : ℤ) + 2 - 2 * (k : ℤ) - 1 - 1) = (m : ℤ) + 1 - 2 * (k : ℤ) - 1 from by ring] at h
      exact h
    have hE0 : E ((m : ℤ) - 2 * (k : ℤ) - 1) =
        (((m : ℤ) + 1 - 2 * (k : ℤ) - 1 : ℤ) : ℚ) * E ((m : ℤ) + 1 - 2 * (k : ℤ) - 1) := by
      have h := E_pred ((m : ℤ) + 1 - 2 * (k : ℤ) - 1)
      rw [show ((m : ℤ) + 1 - 2 * (k : ℤ) - 1 - 1) = (m : ℤ) - 2 * (k : ℤ) - 1 from by ring] at h
      exact h
    have hE3 : E ((m : ℤ) + 2 - 2 * ((k + 1 : ℕ) : ℤ) - 1) = E ((m : ℤ) - 2 * (k : ℤ) - 1) := by
      congr 1
      push_cast
      ring
    have hc := c_succ k
    unfold g
    rw [hE3, hE0, hE1]
    push_cast
    linear_combination (((m : ℚ) + 1 - 2 * (k : ℚ) - 1) * ((m : ℚ) + 2 - 2 * (k : ℚ) - 1)
      * E ((m : ℤ) + 2 - 2 * (k : ℤ) - 1)) * hc
  rw [Finset.sum_congr rfl key, Finset.sum_range_sub']
  unfold g
  rw [E_neg ((m : ℤ) + 2 - 2 * ((m + 2 + 1 : ℕ) : ℤ) - 1) (by push_cast; omega)]
  simp

end A098519Aux

open OMA.S_oeis_a098519 A098519Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a098519.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega, a_eq, a_eq, a_eq]
  have f2 : ((m + 2).factorial : ℚ) = ((m : ℚ) + 2) * (((m : ℚ) + 1) * (m.factorial : ℚ)) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f1 : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [f2, f1]
  have h := b_rec m
  push_cast
  linear_combination (((m : ℚ) + 2) * ((m : ℚ) + 1) * (m.factorial : ℚ)) * h
