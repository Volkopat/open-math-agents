import OMAStatements.S_oeis_a152601

-- Original Lean proof: @grp06.
/-! A telescoping certificate for Mathar's recurrence in https://oeis.org/A152601. -/

namespace OMA152601

open Finset
open OMA.S_oeis_a152601 (a)

private def w (n k : ℕ) : ℚ :=
  ((n + k).choose (2 * k) : ℚ) * (catalan k : ℚ) * (3 / 2) ^ k

private def u (n : ℕ) : ℚ := ∑ k ∈ range (n + 1), w n k

private def shifted (m : ℕ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => w (m + 1) k

private theorem w_zero {n k : ℕ} (h : n < k) : w n k = 0 := by
  simp [w, Nat.choose_eq_zero_of_lt (show n + k < 2 * k by omega)]

private theorem w_prev (m k : ℕ) :
    ((m : ℚ) + k + 1) * w m k = ((m : ℚ) + 1 - k) * w (m + 1) k := by
  by_cases hk : k ≤ m + 1
  · have h := Nat.choose_mul_succ_eq (m + k) (2 * k)
    rw [show m + k + 1 = m + 1 + k by omega,
      show m + 1 + k - 2 * k = m + 1 - k by omega] at h
    have hq := congrArg (fun n : ℕ => (n : ℚ)) h
    push_cast [Nat.cast_sub hk] at hq
    unfold w
    linear_combination ((catalan k : ℚ) * (3 / 2 : ℚ) ^ k) * hq
  · rw [w_zero (show m < k by omega), w_zero (show m + 1 < k by omega)]
    simp

private theorem padded_sum (m n : ℕ) (h : m ≤ n) :
    ∑ k ∈ range (n + 1), w m k = u m := by
  unfold u
  symm
  refine sum_subset (fun k hk => mem_range.mpr ?_) ?_
  · have hkm := mem_range.mp hk
    omega
  · intro k _ hkm
    rw [mem_range] at hkm
    exact w_zero (by omega)

private theorem scale (n : ℕ) : (a n : ℚ) = 2 ^ n * u n := by
  unfold a u
  push_cast
  rw [mul_sum]
  refine sum_congr rfl ?_
  intro k hk
  have hk' : k ≤ n := by rw [mem_range] at hk; omega
  have hpow : (2 : ℚ) ^ n = 2 ^ (n - k) * 2 ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  have hfactor : (2 : ℚ) ^ k * (3 / 2) ^ k = 3 ^ k := by
    rw [← mul_pow]
    norm_num
  unfold w
  rw [hpow]
  linear_combination -(((n + k).choose (2 * k) : ℚ) * catalan k * 2 ^ (n - k)) * hfactor

private theorem local_relation (n k x y z t : ℚ) (hn : 2 ≤ n) (hk : 0 ≤ k)
    (h₁ : (n + k) * y = (n - k) * x)
    (h₂ : (n + k - 1) * z = (n - k - 1) * y)
    (h₃ : k * (k + 1) * x = (3 / 2) * (n + k) * (n + k - 1) * t) :
    (n + 1) * x - (2 * n - 1) * y + (n - 2) * z = 3 * (2 * n - 1) * t := by
  have hp : 0 < (n + k) * (n + k - 1) :=
    mul_pos (by linarith) (by linarith)
  apply mul_left_cancel₀ (ne_of_gt hp)
  linear_combination
    (-(2 * n - 1) * (n + k - 1) + (n - 2) * (n - k - 1)) * h₁ +
    ((n - 2) * (n + k)) * h₂ + (2 * (2 * n - 1)) * h₃

/-- The factorial identity needed to turn the certificate into the source recurrence. -/
def ShiftIdentity : Prop := ∀ m k : ℕ,
    (k : ℚ) * (k + 1) * w (m + 2) k =
      (3 / 2) * ((m : ℚ) + 2 + k) * ((m : ℚ) + 2 + k - 1) * shifted m k

theorem recurrence_of_shift (hshift : ShiftIdentity) :
    type_of% @OMA.S_oeis_a152601.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hl (k : ℕ) :
      ((m : ℚ) + 3) * w (m + 2) k - (2 * (m : ℚ) + 3) * w (m + 1) k +
        (m : ℚ) * w m k = 3 * (2 * (m : ℚ) + 3) * shifted m k := by
    have h := local_relation ((m : ℚ) + 2) k
      (w (m + 2) k) (w (m + 1) k) (w m k) (shifted m k)
      (by
        have hm : (0 : ℚ) ≤ m := by positivity
        linarith) (by positivity) (by
        have h := w_prev (m + 1) k
        push_cast at h
        linear_combination h) (by
        have h := w_prev m k
        linear_combination h) (hshift m k)
    linear_combination h
  have heq := sum_congr (s₁ := range (m + 3)) rfl (fun k _ => hl k)
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum] at heq
  have hpad₁ := padded_sum (m + 1) (m + 2) (by omega)
  have hpad₂ := padded_sum m (m + 2) (by omega)
  have hsum_shift : ∑ k ∈ range (m + 3), shifted m k = u (m + 1) := by
    rw [sum_range_succ']
    simp [shifted, u]
  change ((m : ℚ) + 3) * u (m + 2) -
      (2 * (m : ℚ) + 3) * (∑ k ∈ range (m + 3), w (m + 1) k) +
      (m : ℚ) * (∑ k ∈ range (m + 3), w m k) =
      3 * (2 * (m : ℚ) + 3) * (∑ k ∈ range (m + 3), shifted m k) at heq
  rw [hpad₁, hpad₂, hsum_shift] at heq
  have hq : ((↑(m + 2) : ℚ) + 1) * (a (m + 2) : ℚ) +
      8 * (-2 * (↑(m + 2) : ℚ) + 1) * (a (m + 1) : ℚ) +
      4 * ((↑(m + 2) : ℚ) - 2) * (a m : ℚ) = 0 := by
    rw [scale, scale, scale]
    push_cast
    simp only [pow_add]
    norm_num
    linear_combination (4 * (2 : ℚ) ^ m) * heq
  exact_mod_cast hq

private theorem catalan_step (j : ℕ) :
    ((j : ℚ) + 2) * (catalan (j + 1) : ℚ) =
      2 * (2 * (j : ℚ) + 1) * (catalan j : ℚ) := by
  have hCat := congrArg (fun n : ℕ => (n : ℚ)) (succ_mul_catalan_eq_centralBinom j)
  have hCatSucc := congrArg (fun n : ℕ => (n : ℚ)) (succ_mul_catalan_eq_centralBinom (j + 1))
  have hCentral := congrArg (fun n : ℕ => (n : ℚ)) (Nat.succ_mul_centralBinom_succ j)
  push_cast at hCat hCatSucc hCentral
  apply mul_left_cancel₀ (show (j : ℚ) + 1 ≠ 0 by positivity)
  linear_combination ((j : ℚ) + 1) * hCatSucc + hCentral -
    2 * (2 * (j : ℚ) + 1) * hCat

private theorem shift_identity : ShiftIdentity := by
  intro m k
  cases k with
  | zero => simp [shifted]
  | succ j =>
    have hA := Nat.add_one_mul_choose_eq (m + 1 + j) (2 * j)
    have hB := Nat.add_one_mul_choose_eq (m + 2 + j) (2 * j + 1)
    rw [show m + 1 + j + 1 = m + 2 + j by omega] at hA
    rw [show m + 2 + j + 1 = m + 2 + (j + 1) by omega,
      show 2 * j + 1 + 1 = 2 * (j + 1) by omega] at hB
    have hAq := congrArg (fun n : ℕ => (n : ℚ)) hA
    have hBq := congrArg (fun n : ℕ => (n : ℚ)) hB
    push_cast at hAq hBq
    have hCore :
        ((j : ℚ) + 1) * ((j : ℚ) + 2) *
            ((m + 2 + (j + 1)).choose (2 * (j + 1)) : ℚ) * (catalan (j + 1) : ℚ) =
          ((m : ℚ) + j + 2) * ((m : ℚ) + j + 3) *
            ((m + 1 + j).choose (2 * j) : ℚ) * (catalan j : ℚ) := by
      linear_combination
        (((j : ℚ) + 1) * ((m + 2 + (j + 1)).choose (2 * (j + 1)) : ℚ)) * catalan_step j -
        (catalan j : ℚ) * (((m : ℚ) + j + 3) * hAq + (2 * (j : ℚ) + 1) * hBq)
    change ((↑(j + 1) : ℚ) * (↑(j + 1) + 1) * w (m + 2) (j + 1)) =
      (3 / 2) * ((m : ℚ) + 2 + ↑(j + 1)) * ((m : ℚ) + 2 + ↑(j + 1) - 1) * w (m + 1) j
    unfold w
    push_cast
    rw [pow_succ]
    linear_combination ((3 / 2 : ℚ) ^ j * (3 / 2)) * hCore

end OMA152601

theorem OMA.solution : type_of% @OMA.S_oeis_a152601.main :=
  OMA152601.recurrence_of_shift OMA152601.shift_identity
