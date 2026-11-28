import OMAStatements.S_oeis_a130595
import Mathlib

open OMA.S_oeis_a130595

def Q (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
  fun i j => (-1 : ℚ) ^ ((i : ℕ) + j) * (Nat.choose i j : ℚ)

lemma sum_alt (N i j : ℕ) (hji : j ≤ i) (hiN : i ≤ N) :
    ∑ l ∈ Finset.range (N + 1), (Nat.choose i l : ℚ) * ((-1 : ℚ) ^ (l + j) * (Nat.choose l j : ℚ))
      = if i = j then 1 else 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, N = j + d + e := ⟨N - (j + d), by omega⟩
  rw [show j + d + e + 1 = j + ((d + 1) + e) by ring, Finset.sum_range_add, Finset.sum_range_add]
  have h0 : ∑ x ∈ Finset.range j,
      (Nat.choose (j + d) x : ℚ) * ((-1 : ℚ) ^ (x + j) * (Nat.choose x j : ℚ)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_range] at hx
    rw [Nat.choose_eq_zero_of_lt hx]; simp
  have h2 : ∑ x ∈ Finset.range e,
      (Nat.choose (j + d) (j + (d + 1 + x)) : ℚ) *
        ((-1 : ℚ) ^ (j + (d + 1 + x) + j) * (Nat.choose (j + (d + 1 + x)) j : ℚ)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [Nat.choose_eq_zero_of_lt (by omega : j + d < j + (d + 1 + x))]; simp
  rw [h0, h2, zero_add, add_zero]
  have h1 : ∀ m ∈ Finset.range (d + 1),
      (Nat.choose (j + d) (j + m) : ℚ) * ((-1 : ℚ) ^ (j + m + j) * (Nat.choose (j + m) j : ℚ))
      = (Nat.choose (j + d) j : ℚ) * ((-1 : ℚ) ^ m * (Nat.choose d m : ℚ)) := by
    intro m _
    have key : (Nat.choose (j + d) (j + m) : ℚ) * (Nat.choose (j + m) j : ℚ)
        = (Nat.choose (j + d) j : ℚ) * (Nat.choose d m : ℚ) := by
      have := Nat.choose_mul (n := j + d) (k := j + m) (s := j) (by omega)
      simp only [Nat.add_sub_cancel_left] at this
      exact_mod_cast this
    have hp : (-1 : ℚ) ^ (j + m + j) = (-1) ^ m := by
      rw [show j + m + j = m + 2 * j by ring, pow_add, pow_mul]; simp
    rw [hp]
    calc (Nat.choose (j + d) (j + m) : ℚ) * ((-1) ^ m * (Nat.choose (j + m) j : ℚ))
        = (-1) ^ m * ((Nat.choose (j + d) (j + m) : ℚ) * (Nat.choose (j + m) j : ℚ)) := by ring
      _ = _ := by rw [key]; ring
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have halt : ∑ m ∈ Finset.range (d + 1), ((-1 : ℚ) ^ m * (Nat.choose d m : ℚ)) =
      if d = 0 then 1 else 0 := by
    have := Int.alternating_sum_range_choose (n := d)
    rw [← Int.cast_inj (α := ℚ)] at this
    push_cast at this
    rw [this]
  rw [halt]
  by_cases hd : d = 0
  · subst hd; simp
  · rw [if_neg hd, if_neg (by omega)]; simp

lemma pascal_mul_Q (N : ℕ) : pascal N * Q N = 1 := by
  ext i j
  simp only [Matrix.mul_apply, pascal, Q, Matrix.one_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun l => (Nat.choose i l : ℚ) * ((-1 : ℚ) ^ (l + (j : ℕ)) * (Nat.choose l j : ℚ)))]
  by_cases hji : (j : ℕ) ≤ i
  · rw [sum_alt N i j hji (by omega)]
    by_cases h : i = j
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg (fun h' => h (Fin.ext h')), if_neg h]
  · rw [if_neg (fun h => hji (by rw [h]))]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l ≤ i
    · rw [Nat.choose_eq_zero_of_lt (by omega : l < j)]; simp
    · rw [Nat.choose_eq_zero_of_lt (by omega : i < l)]; simp

lemma T_eq (n k : ℕ) : T n k = if k ≤ n then (-1 : ℚ) ^ (n + k) * (Nat.choose n k : ℚ) else 0 := by
  unfold T
  split_ifs with h
  · rw [Matrix.inv_eq_right_inv (pascal_mul_Q n)]
    rfl
  · rfl

theorem OMA.solution : type_of% @OMA.S_oeis_a130595.main := by
  intro n k hk hkn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [T_eq, T_eq, T_eq, if_pos hkn, if_pos (by omega)]
  have hs : (m + 1) * Nat.choose m j = Nat.choose (m + 1) (j + 1) * (j + 1) :=
    Nat.add_one_mul_choose_eq m j
  have hp : Nat.choose (m + 1) (j + 1) = Nat.choose m j + Nat.choose m (j + 1) :=
    Nat.choose_succ_succ' m j
  have hs' : ((m : ℚ) + 1) * (Nat.choose m j : ℚ) = (Nat.choose (m + 1) (j + 1) : ℚ) * (j + 1) := by
    exact_mod_cast hs
  have hp' : (Nat.choose (m + 1) (j + 1) : ℚ) = (Nat.choose m j : ℚ) + (Nat.choose m (j + 1) : ℚ) := by
    exact_mod_cast hp
  have e1 : (-1 : ℚ) ^ (m + 1 + (j + 1)) = (-1) ^ (m + j) := by
    rw [show m + 1 + (j + 1) = m + j + 2 by ring, pow_add]; simp
  have e2 : (-1 : ℚ) ^ (m + (j + 1)) = -(-1) ^ (m + j) := by
    rw [show m + (j + 1) = m + j + 1 by ring, pow_succ]; ring
  rw [e1, e2]
  split_ifs with h
  · push_cast
    linear_combination (-(-1 : ℚ) ^ (m + j)) * hs' - ((-1 : ℚ) ^ (m + j) * (j:ℚ)) * hp'
  · have hz : Nat.choose m (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz] at hp'
    push_cast
    linear_combination (-(-1 : ℚ) ^ (m + j)) * hs' - ((-1 : ℚ) ^ (m + j) * (j:ℚ)) * hp'
