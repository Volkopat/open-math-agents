import OMAStatements.S_oeis_a143902

-- Problem: A143902: Rectangular array R by antidiagonals: R(m,n) = number of black squares.
-- Upstream: formal-conjectures statements/oeis-a143902.lean:0 (declaration OMA.S_oeis_a143902.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with S(k) the k-th antidiagonal sum and G(k) = 1 + ... + k, the terms of S(k+2)
-- with m <= k are floor(m(k+1-m)/2) + m, and the last two are k+1 and floor((k+2)/2). So
-- S(k+2) = S(k) + G(k) + (k+1) + floor((k+2)/2); induction gives 12 S(2j) = 2j(2j+1)(2j+2) and
-- 12 S(2j+1) = 2j(2j+2)(2j+4), which are 12 A006584(2j+1) and 12 A006584(2j+2).

namespace S02A143902

open OMA.S_oeis_a143902

def S (k : ℕ) : ℕ := ∑ m ∈ Finset.Icc 1 k, R m (k + 1 - m)

def G (k : ℕ) : ℕ := ∑ m ∈ Finset.Icc 1 k, m

theorem gauss (k : ℕ) : 2 * G k = k * (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h : G (k + 1) = G k + (k + 1) := by
      unfold G
      rw [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega)]
    have e : 2 * (G k + (k + 1)) = 2 * G k + 2 * (k + 1) := mul_add 2 (G k) (k + 1)
    rw [h, e, ih]
    ring

theorem step (k : ℕ) : S (k + 1 + 1) = S k + G k + (k + 1) + (k + 2) / 2 := by
  have hsum : ∑ m ∈ Finset.Icc 1 k, R m (k + 1 + 1 + 1 - m) = S k + G k := by
    unfold S G
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    have hmk : m ≤ k := (Finset.mem_Icc.mp hm).2
    have e : k + 1 + 1 + 1 - m = (k + 1 - m) + 2 := by omega
    rw [e]
    unfold R
    rw [mul_add, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
  have t1 : R (k + 1) (k + 1 + 1 + 1 - (k + 1)) = k + 1 := by
    have e : k + 1 + 1 + 1 - (k + 1) = 2 := by omega
    rw [e]
    unfold R
    omega
  have t2 : R (k + 1 + 1) (k + 1 + 1 + 1 - (k + 1 + 1)) = (k + 2) / 2 := by
    have e : k + 1 + 1 + 1 - (k + 1 + 1) = 1 := by omega
    rw [e]
    unfold R
    omega
  rw [show S (k + 1 + 1) = ∑ m ∈ Finset.Icc 1 (k + 1 + 1), R m (k + 1 + 1 + 1 - m) from rfl]
  rw [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 + 1 by omega)]
  rw [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega)]
  rw [hsum, t1, t2]

theorem even_case (j : ℕ) : 12 * S (2 * j) = 2 * j * (2 * j + 1) * (2 * j + 2) := by
  induction j with
  | zero => decide
  | succ j ih =>
    have h := step (2 * j)
    have hG := gauss (2 * j)
    have hd : (2 * j + 2) / 2 = j + 1 := by omega
    rw [hd] at h
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, h]
    zify at ih hG ⊢
    linear_combination ih + 6 * hG

theorem odd_case (j : ℕ) : 12 * S (2 * j + 1) = 2 * j * (2 * j + 2) * (2 * j + 4) := by
  induction j with
  | zero => decide
  | succ j ih =>
    have h := step (2 * j + 1)
    have hG := gauss (2 * j + 1)
    have hd : (2 * j + 1 + 2) / 2 = j + 1 := by omega
    rw [hd] at h
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring, h]
    zify at ih hG ⊢
    linear_combination ih + 6 * hG

theorem at_even (j : ℕ) : S (2 * j) = A006584 (2 * j + 1) := by
  have he := even_case j
  unfold A006584
  rw [if_neg (by omega : ¬ ((2 * j + 1) % 2 = 0))]
  have h1 : (2 * j + 1) ^ 2 = 2 * j * (2 * j + 2) + 1 := by ring
  have hsq : (2 * j + 1) ^ 2 - 1 = 2 * j * (2 * j + 2) := by omega
  rw [hsq]
  have h2 : (2 * j + 1) * (2 * j * (2 * j + 2)) = 12 * S (2 * j) := by
    rw [he]
    ring
  rw [h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 12)]

theorem at_odd (j : ℕ) : S (2 * j + 1) = A006584 (2 * j + 1 + 1) := by
  have ho := odd_case j
  unfold A006584
  rw [if_pos (by omega : (2 * j + 1 + 1) % 2 = 0)]
  have h1 : (2 * j + 1 + 1) ^ 2 = 2 * j * (2 * j + 4) + 4 := by ring
  have hsq : (2 * j + 1 + 1) ^ 2 - 4 = 2 * j * (2 * j + 4) := by omega
  rw [hsq]
  have h2 : (2 * j + 1 + 1) * (2 * j * (2 * j + 4)) = 12 * S (2 * j + 1) := by
    rw [ho]
    ring
  rw [h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 12)]

theorem main' (k : ℕ) : S k = A006584 (k + 1) := by
  obtain ⟨j, rfl | rfl⟩ : ∃ j, k = 2 * j ∨ k = 2 * j + 1 := ⟨k / 2, by omega⟩
  · exact at_even j
  · exact at_odd j

end S02A143902

open OMA.S_oeis_a143902 S02A143902 in
theorem OMA.solution : type_of% @OMA.S_oeis_a143902.main := by
  intro k _
  exact main' k
