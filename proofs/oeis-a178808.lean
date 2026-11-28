import OMAStatements.S_oeis_a178808

-- Problem: A178808: a(n) = (1/n^2) * Sum_{k = 0..n-1} (2*k+1)*(D_k)^2, where D_0, D_1, ... are central Delannoy numbers given by A001850.
-- Upstream: formal-conjectures statements/oeis-a178808.lean:0 (declaration OMA.S_oeis_a178808.main)
-- Credit: @mjsechrest2

open OMA.S_oeis_a178808

namespace OMA_a178808_proof

/-! ### Part 1: Delannoy 3-term recurrence and exact quadratic formula for `S n` -/

private lemma succ_mul_choose (n k : ℕ) :
    (n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1) := by
  by_cases hk : k ≤ n
  · have h1 := Nat.choose_mul_factorial_mul_factorial hk
    have h2 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ n + 1 by omega)
    rw [show n + 1 - (k + 1) = n - k by omega] at h2
    have hpos : k.factorial * (n - k).factorial ≠ 0 :=
      mul_ne_zero (Nat.factorial_ne_zero k) (Nat.factorial_ne_zero (n - k))
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos)
    calc (n + 1) * n.choose k * (k.factorial * (n - k).factorial)
        = (n + 1) * (n.choose k * k.factorial * (n - k).factorial) := by ring
      _ = (n + 1) * n.factorial := by rw [h1]
      _ = (n + 1).factorial := (Nat.factorial_succ n).symm
      _ = (n + 1).choose (k + 1) * (k + 1).factorial * (n - k).factorial := h2.symm
      _ = (n + 1).choose (k + 1) * ((k + 1) * k.factorial) * (n - k).factorial := by
          rw [Nat.factorial_succ k]
      _ = (n + 1).choose (k + 1) * (k + 1) * (k.factorial * (n - k).factorial) := by ring
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp

private lemma choose_sub_mul (n k : ℕ) :
    (n + 1 - k) * (n + 1).choose k = (n + 1) * n.choose k := by
  have h1 := succ_mul_choose n k
  have h2 := Nat.choose_succ_right_eq (n + 1) k
  linarith

private lemma choose_add_sub_mul (n k : ℕ) :
    (n + 1) * (n + 1 + k).choose k = (n + 1 + k) * (n + k).choose k := by
  have h := choose_sub_mul (n + k) k
  have heq : n + k + 1 - k = n + 1 := by omega
  have heq2 : n + k + 1 = n + 1 + k := by omega
  rw [heq, heq2] at h
  exact h

private def DF (n k : ℕ) : ℚ := (n.choose k : ℚ) * ((n + k).choose k : ℚ)
private def DH (n k : ℕ) : ℚ := ((n + 1).choose k : ℚ) * ((n + k).choose k : ℚ)

private lemma DF_eq_DH (n k : ℕ) (hk : k ≤ n + 1) :
    DF n k = (((n : ℚ) + 1 - k) / ((n : ℚ) + 1)) * DH n k := by
  unfold DF DH
  have h1 : ((n + 1 - k : ℕ) : ℚ) * ((n + 1).choose k : ℚ) = ((n + 1 : ℕ) : ℚ) * (n.choose k : ℚ) := by
    exact_mod_cast choose_sub_mul n k
  rw [Nat.cast_sub hk] at h1
  push_cast at h1
  have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hpos]
  calc (n.choose k : ℚ) * ((n + k).choose k : ℚ) * ((n : ℚ) + 1)
      = ((n + k).choose k : ℚ) * (((n : ℚ) + 1) * (n.choose k : ℚ)) := by ring
    _ = ((n + k).choose k : ℚ) * (((n : ℚ) + 1 - k) * ((n + 1).choose k : ℚ)) := by rw [← h1]
    _ = _ := by ring

private lemma DF_succ_eq_DH (n k : ℕ) :
    DF (n + 1) k = (((n : ℚ) + 1 + k) / ((n : ℚ) + 1)) * DH n k := by
  unfold DF DH
  have h1 : ((n + 1 : ℕ) : ℚ) * ((n + 1 + k).choose k : ℚ) = ((n + 1 + k : ℕ) : ℚ) * ((n + k).choose k : ℚ) := by
    exact_mod_cast choose_add_sub_mul n k
  push_cast at h1
  have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hpos]
  calc ((n + 1).choose k : ℚ) * ((n + 1 + k).choose k : ℚ) * ((n : ℚ) + 1)
      = ((n + 1).choose k : ℚ) * (((n : ℚ) + 1) * ((n + 1 + k).choose k : ℚ)) := by ring
    _ = ((n + 1).choose k : ℚ) * (((n : ℚ) + 1 + k) * ((n + k).choose k : ℚ)) := by rw [h1]
    _ = _ := by ring

private lemma DF_pred_eq_DH (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n + 1) :
    DF (n - 1) k = (((n : ℚ) - k) * ((n : ℚ) + 1 - k) / (((n : ℚ) + 1) * ((n : ℚ) + k))) * DH n k := by
  unfold DF DH
  have hpos1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hpos2 : ((n : ℚ) + k) ≠ 0 := by
    have : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
    linarith
  rcases lt_or_ge n k with hlt | hle
  · have hkn : k = n + 1 := by omega
    subst hkn
    rw [Nat.choose_eq_zero_of_lt (by omega : n - 1 < n + 1)]
    push_cast; ring
  · rcases eq_or_lt_of_le hle with rfl | hlt
    · rw [Nat.choose_eq_zero_of_lt (by omega : k - 1 < k)]
      push_cast; ring
    · have hch1 : ((n - k : ℕ) : ℚ) * (n.choose k : ℚ) = (n : ℚ) * ((n - 1).choose k : ℚ) := by
        have h := choose_sub_mul (n - 1) k
        rw [show n - 1 + 1 = n by omega] at h
        exact_mod_cast h
      have hch2 : ((n + 1 - k : ℕ) : ℚ) * ((n + 1).choose k : ℚ) = ((n + 1 : ℕ) : ℚ) * (n.choose k : ℚ) := by
        exact_mod_cast choose_sub_mul n k
      have hch3 : (n : ℚ) * ((n + k).choose k : ℚ) = ((n + k : ℕ) : ℚ) * ((n - 1 + k).choose k : ℚ) := by
        have h := choose_add_sub_mul (n - 1) k
        rw [show n - 1 + 1 = n by omega] at h
        exact_mod_cast h
      rw [Nat.cast_sub (by omega : k ≤ n)] at hch1
      rw [Nat.cast_sub hk] at hch2
      push_cast at hch2 hch3
      have hn0 : (n : ℚ) ≠ 0 := by
        have : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
        linarith
      have hkey : ((n : ℚ) + 1) * ((n : ℚ) + k) * (n : ℚ) *
          (((n - 1).choose k : ℚ) * ((n - 1 + k).choose k : ℚ)) =
          (n : ℚ) * ((n : ℚ) - k) * ((n : ℚ) + 1 - k) *
          (((n + 1).choose k : ℚ) * ((n + k).choose k : ℚ)) := by
        calc ((n : ℚ) + 1) * ((n : ℚ) + k) * (n : ℚ) *
              (((n - 1).choose k : ℚ) * ((n - 1 + k).choose k : ℚ))
            = ((n : ℚ) + 1) * ((n : ℚ) * ((n - 1).choose k : ℚ)) *
              (((n : ℚ) + k) * ((n - 1 + k).choose k : ℚ)) := by ring
          _ = ((n : ℚ) + 1) * (((n : ℚ) - k) * (n.choose k : ℚ)) *
              ((n : ℚ) * ((n + k).choose k : ℚ)) := by rw [← hch1, ← hch3]
          _ = (n : ℚ) * ((n : ℚ) - k) * (((n : ℚ) + 1) * (n.choose k : ℚ)) *
              ((n + k).choose k : ℚ) := by ring
          _ = (n : ℚ) * ((n : ℚ) - k) * (((n : ℚ) + 1 - k) * ((n + 1).choose k : ℚ)) *
              ((n + k).choose k : ℚ) := by rw [← hch2]
          _ = _ := by ring
      have hkey2 : ((n : ℚ) + 1) * ((n : ℚ) + k) *
          (((n - 1).choose k : ℚ) * ((n - 1 + k).choose k : ℚ)) =
          ((n : ℚ) - k) * ((n : ℚ) + 1 - k) *
          (((n + 1).choose k : ℚ) * ((n + k).choose k : ℚ)) := by
        apply mul_left_cancel₀ hn0
        linear_combination hkey
      rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hpos1 hpos2)]
      linear_combination hkey2

private lemma DH_succ_k (n k : ℕ) (hk : k ≤ n + 1) :
    DH n (k + 1) = (((n : ℚ) + 1 - k) * ((n : ℚ) + k + 1) / ((k : ℚ) + 1) ^ 2) * DH n k := by
  unfold DH
  have h1 : ((n + 1).choose (k + 1) : ℚ) * ((k + 1 : ℕ) : ℚ) =
      ((n + 1).choose k : ℚ) * ((n + 1 - k : ℕ) : ℚ) := by
    exact_mod_cast Nat.choose_succ_right_eq (n + 1) k
  have h2 : ((n + k + 1).choose (k + 1) : ℚ) * ((k + 1 : ℕ) : ℚ) =
      ((n + k + 1 : ℕ) : ℚ) * ((n + k).choose k : ℚ) := by
    exact_mod_cast (succ_mul_choose (n + k) k).symm
  rw [Nat.cast_sub hk] at h1
  push_cast at h1 h2
  have hpos : ((k : ℚ) + 1) ≠ 0 := by positivity
  rw [show n + (k + 1) = n + k + 1 by omega]
  rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hpos)]
  calc ((n + 1).choose (k + 1) : ℚ) * ((n + k + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) ^ 2
      = (((n + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1)) *
        (((n + k + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1)) := by ring
    _ = (((n + 1).choose k : ℚ) * ((n : ℚ) + 1 - k)) *
        (((n : ℚ) + k + 1) * ((n + k).choose k : ℚ)) := by rw [h1, h2]
    _ = _ := by ring

private lemma delannoy_rec (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℤ) + 1) * delannoy (n + 1) =
      3 * (2 * (n : ℤ) + 1) * delannoy n - (n : ℤ) * delannoy (n - 1) := by
  suffices h : ((n : ℚ) + 1) * (delannoy (n + 1) : ℚ) =
      3 * (2 * (n : ℚ) + 1) * (delannoy n : ℚ) - (n : ℚ) * (delannoy (n - 1) : ℚ) by
    exact_mod_cast h
  let G : ℕ → ℚ := fun k =>
    (-(2 * (k : ℚ) ^ 2 * (2 * (n : ℚ) + 1)) / (((k : ℚ) + n) * ((n : ℚ) + 1))) * DH n k
  have hstep : ∀ k ∈ Finset.range (n + 2),
      ((n : ℚ) + 1) * DF (n + 1) k - 3 * (2 * (n : ℚ) + 1) * DF n k + (n : ℚ) * DF (n - 1) k =
      G (k + 1) - G k := by
    intro k hk
    have hk' : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    dsimp only [G]
    rw [DF_succ_eq_DH, DF_eq_DH n k hk', DF_pred_eq_DH n k hn hk', DH_succ_k n k hk']
    have hpos1 : ((n : ℚ) + 1) ≠ 0 := by positivity
    have hpos2 : ((k : ℚ) + 1) ≠ 0 := by positivity
    have hpos3 : ((k : ℚ) + (n : ℚ)) ≠ 0 := by
      have : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
      linarith
    have hpos4 : ((k : ℚ) + 1 + (n : ℚ)) ≠ 0 := by positivity
    have hpos5 : ((n : ℚ) + (k : ℚ)) ≠ 0 := by
      have : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
      linarith
    push_cast
    field_simp [hpos1, hpos2, hpos3, hpos4, hpos5]
    ring
  have hsum := Finset.sum_congr rfl hstep
  rw [Finset.sum_range_sub G (n + 2)] at hsum
  have hG0 : G 0 = 0 := by simp [G]
  have hGend : G (n + 2) = 0 := by simp [G, DH]
  rw [hG0, hGend, sub_zero] at hsum
  have hs0 : ∑ k ∈ Finset.range (n + 2), DF n k = (delannoy n : ℚ) := by
    rw [Finset.sum_range_succ]
    have hl : DF n (n + 1) = 0 := by unfold DF; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    rw [hl, add_zero]; unfold delannoy DF; push_cast; rfl
  have hs1 : ∑ k ∈ Finset.range (n + 2), DF (n + 1) k = (delannoy (n + 1) : ℚ) := by
    unfold delannoy DF; push_cast; rfl
  have hsm : ∑ k ∈ Finset.range (n + 2), DF (n - 1) k = (delannoy (n - 1) : ℚ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hl1 : DF (n - 1) (n + 1) = 0 := by unfold DF; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    have hl2 : DF (n - 1) n = 0 := by unfold DF; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    rw [hl1, hl2, add_zero, add_zero]
    unfold delannoy DF; rw [show n - 1 + 1 = n by omega]; push_cast; rfl
  have hlin : ∑ k ∈ Finset.range (n + 2),
      (((n : ℚ) + 1) * DF (n + 1) k - 3 * (2 * (n : ℚ) + 1) * DF n k + (n : ℚ) * DF (n - 1) k) =
      ((n : ℚ) + 1) * (∑ k ∈ Finset.range (n + 2), DF (n + 1) k) -
      3 * (2 * (n : ℚ) + 1) * (∑ k ∈ Finset.range (n + 2), DF n k) +
      (n : ℚ) * (∑ k ∈ Finset.range (n + 2), DF (n - 1) k) := by
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [hlin, hs1, hs0, hsm] at hsum
  linarith

private lemma eight_mul_S (n : ℕ) (hn : 1 ≤ n) :
    8 * (S n : ℤ) = (n : ℤ) ^ 2 *
      (6 * (delannoy n : ℤ) * delannoy (n - 1) - (delannoy n : ℤ) ^ 2 - (delannoy (n - 1) : ℤ) ^ 2) := by
  induction n, hn using Nat.le_induction with
  | base =>
    decide
  | succ m hm ih =>
    have hS : (S (m + 1) : ℤ) = (S m : ℤ) + (2 * (m : ℤ) + 1) * (delannoy m : ℤ) ^ 2 := by
      unfold S
      rw [Finset.sum_range_succ]
      push_cast; ring
    have hrec := delannoy_rec m hm
    rw [hS, show m + 1 - 1 = m by omega]
    push_cast
    have hstep : ((m : ℤ) + 1) ^ 2 * (6 * (delannoy (m + 1) : ℤ) * delannoy m -
        (delannoy (m + 1) : ℤ) ^ 2 - (delannoy m : ℤ) ^ 2) =
        6 * ((m : ℤ) + 1) * (((m : ℤ) + 1) * delannoy (m + 1)) * delannoy m -
        (((m : ℤ) + 1) * delannoy (m + 1)) ^ 2 - ((m : ℤ) + 1) ^ 2 * (delannoy m : ℤ) ^ 2 := by ring
    rw [hstep, hrec]
    linear_combination ih

private lemma delannoy_eq_sum_pow_two (n : ℕ) :
    delannoy n = ∑ i ∈ Finset.range (n + 1), 2 ^ (n - i) * (n.choose i) ^ 2 := by
  unfold delannoy
  have hcv : ∀ j ∈ Finset.range (n + 1),
      (n + j).choose j = ∑ i ∈ Finset.range (n + 1), n.choose i * j.choose i := by
    intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.add_choose_eq]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => n.choose a * j.choose b) j]
    symm
    rw [← Finset.sum_subset (Finset.range_mono (show j + 1 ≤ n + 1 by omega))]
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [Nat.choose_symm hi']
    · intro i _ hin
      rw [Finset.mem_range] at hin
      rw [Nat.choose_eq_zero_of_lt (by omega : j < i), mul_zero]
  calc ∑ j ∈ Finset.range (n + 1), n.choose j * (n + j).choose j
      = ∑ j ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
          n.choose j * (n.choose i * j.choose i) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcv j hj, Finset.mul_sum]
    _ = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          n.choose j * (n.choose i * j.choose i) := Finset.sum_comm
    _ = ∑ i ∈ Finset.range (n + 1), 2 ^ (n - i) * (n.choose i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hstep : ∑ j ∈ Finset.range (n + 1), n.choose j * (n.choose i * j.choose i) =
            (n.choose i) ^ 2 * ∑ k ∈ Finset.range (n - i + 1), (n - i).choose k := by
          have hsub : ∑ j ∈ Finset.range (n + 1), n.choose j * (n.choose i * j.choose i) =
              ∑ j ∈ Finset.Icc i n, n.choose j * (n.choose i * j.choose i) := by
            symm
            apply Finset.sum_subset
            · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_range]; omega
            · intro j hj hjn
              rw [Finset.mem_range] at hj; rw [Finset.mem_Icc] at hjn
              rw [Nat.choose_eq_zero_of_lt (by omega : j < i), mul_zero, mul_zero]
          rw [hsub, Finset.mul_sum]
          symm
          apply Finset.sum_nbij' (fun k => k + i) (fun j => j - i)
          · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega
          · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_range]; omega
          · intro k _; omega
          · intro j hj; rw [Finset.mem_Icc] at hj; omega
          · intro k hk
            rw [Finset.mem_range] at hk
            have hmul := @Nat.choose_mul n (k + i) i (by omega)
            rw [show k + i - i = k by omega] at hmul
            calc (n.choose i) ^ 2 * (n - i).choose k
                = n.choose i * (n.choose i * (n - i).choose k) := by ring
              _ = n.choose i * (n.choose (k + i) * (k + i).choose i) := by rw [← hmul]
              _ = n.choose (k + i) * (n.choose i * (k + i).choose i) := by ring
        rw [Nat.sum_range_choose] at hstep
        linarith

private lemma delannoy_mod4 (n : ℕ) : delannoy n % 4 = (2 * n + 1) % 4 := by
  rw [delannoy_eq_sum_pow_two]
  have hsym : ∑ i ∈ Finset.range (n + 1), 2 ^ (n - i) * (n.choose i) ^ 2 =
      ∑ k ∈ Finset.range (n + 1), 2 ^ k * (n.choose k) ^ 2 := by
    apply Finset.sum_nbij' (fun i => n - i) (fun k => n - k)
    · intro i hi; rw [Finset.mem_range] at hi ⊢; omega
    · intro k hk; rw [Finset.mem_range] at hk ⊢; omega
    · intro i hi; rw [Finset.mem_range] at hi; omega
    · intro k hk; rw [Finset.mem_range] at hk; omega
    · intro i hi
      rw [Finset.mem_range] at hi
      rw [Nat.choose_symm (by omega : i ≤ n)]
  rw [hsym]
  rcases n with _ | _ | m
  · decide
  · decide
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have h4 : 4 ∣ ∑ k ∈ Finset.range (m + 1), 2 ^ (k + 1 + 1) * ((m + 2).choose (k + 1 + 1)) ^ 2 := by
      apply Finset.dvd_sum
      intro k _
      have : 2 ^ (k + 1 + 1) = 4 * 2 ^ k := by rw [pow_succ, pow_succ]; ring
      rw [this, mul_assoc]
      exact dvd_mul_right 4 _
    rcases h4 with ⟨t, ht⟩
    rw [ht]
    simp only [zero_add, pow_zero, pow_one, Nat.choose_zero_right, Nat.choose_one_right, one_pow, mul_one]
    have hsq : (m + 1 + 1) ^ 2 % 2 = (m + 1 + 1) % 2 := by
      have : (m + 1 + 1) % 2 = 0 ∨ (m + 1 + 1) % 2 = 1 := by omega
      rcases this with h | h <;> simp [Nat.pow_mod, h]
    omega

private lemma part1 (n : ℕ) (hn : 1 ≤ n) : n ^ 2 ∣ S n := by
  have h8 := eight_mul_S n hn
  have hmod1 := delannoy_mod4 n
  have hmod2 := delannoy_mod4 (n - 1)
  have hdvd8 : (8 : ℤ) ∣ 6 * (delannoy n : ℤ) * delannoy (n - 1) -
      (delannoy n : ℤ) ^ 2 - (delannoy (n - 1) : ℤ) ^ 2 := by
    have h1 : (delannoy n : ℤ) % 4 = (2 * (n : ℤ) + 1) % 4 := by exact_mod_cast hmod1
    have h2 : (delannoy (n - 1) : ℤ) % 4 = (2 * ((n - 1 : ℕ) : ℤ) + 1) % 4 := by exact_mod_cast hmod2
    have hsub : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    rw [hsub] at h2
    obtain ⟨q1, hq1⟩ : ∃ q1 : ℤ, (delannoy n : ℤ) = 4 * q1 + (delannoy n : ℤ) % 4 :=
      ⟨(delannoy n : ℤ) / 4, by omega⟩
    obtain ⟨q2, hq2⟩ : ∃ q2 : ℤ, (delannoy (n - 1) : ℤ) = 4 * q2 + (delannoy (n - 1) : ℤ) % 4 :=
      ⟨(delannoy (n - 1) : ℤ) / 4, by omega⟩
    have hpar : (n : ℤ) % 2 = 0 ∨ (n : ℤ) % 2 = 1 := by omega
    rcases hpar with hp | hp
    · have hr1 : (delannoy n : ℤ) % 4 = 1 := by omega
      have hr2 : (delannoy (n - 1) : ℤ) % 4 = 3 := by omega
      rw [hr1] at hq1; rw [hr2] at hq2
      refine ⟨3 * (4 * q1 * q2 + 3 * q1 + q2) - 2 * q1 ^ 2 - q1 - 2 * q2 ^ 2 - 3 * q2 + 1, ?_⟩
      rw [hq1, hq2]; ring
    · have hr1 : (delannoy n : ℤ) % 4 = 3 := by omega
      have hr2 : (delannoy (n - 1) : ℤ) % 4 = 1 := by omega
      rw [hr1] at hq1; rw [hr2] at hq2
      refine ⟨3 * (4 * q1 * q2 + q1 + 3 * q2) - 2 * q1 ^ 2 - 3 * q1 - 2 * q2 ^ 2 - q2 + 1, ?_⟩
      rw [hq1, hq2]; ring
  rcases hdvd8 with ⟨Q, hQ⟩
  rw [hQ] at h8
  have hS : (S n : ℤ) = (n : ℤ) ^ 2 * Q := by linarith
  have hQnn : 0 ≤ Q := by
    have hSn : (0 : ℤ) ≤ (S n : ℤ) := Int.natCast_nonneg _
    have hn2 : (0 : ℤ) < (n : ℤ) ^ 2 := by positivity
    nlinarith
  exact ⟨Q.toNat, by zify; rw [Int.toNat_of_nonneg hQnn]; exact hS⟩

/-! ### Part 2: Elementary congruences modulo `p`, `p^2`, `p^3` (Wolstenholme & Morley) -/

private lemma zmod_mul_inv (p r k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hkp : k < p) :
    (k : ZMod (p ^ r)) * (k : ZMod (p ^ r))⁻¹ = 1 := by
  have hcop : Nat.Coprime k (p ^ r) :=
    ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk1 hkp)).symm).pow_right r
  exact ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime k (p ^ r)).mpr hcop)

private lemma zmod_inv_mul (p r k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hkp : k < p) :
    (k : ZMod (p ^ r))⁻¹ * (k : ZMod (p ^ r)) = 1 := by
  rw [mul_comm]; exact zmod_mul_inv p r k hp hk1 hkp

private lemma zmod_two_mul_inv (p r : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    (2 : ZMod (p ^ r)) * (2 : ZMod (p ^ r))⁻¹ = 1 := by
  simpa using zmod_mul_inv p r 2 hp (by norm_num) (by omega)

private lemma zmod_inv_two_mul (p r : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    (2 : ZMod (p ^ r))⁻¹ * (2 : ZMod (p ^ r)) = 1 := by
  simpa using zmod_inv_mul p r 2 hp (by norm_num) (by omega)

private lemma prod_one_add_mul {ι R : Type*} [CommRing R] (s : Finset ι) (x : R) (hx : x ^ 3 = 0)
    (f : ι → R) :
    2 * (∏ i ∈ s, (1 + x * f i)) =
      2 + 2 * x * (∑ i ∈ s, f i) + x ^ 2 * ((∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, f i ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    have hmul : 2 * ((1 + x * f a) * ∏ i ∈ s, (1 + x * f i)) =
        (1 + x * f a) * (2 * ∏ i ∈ s, (1 + x * f i)) := by ring
    rw [hmul, ih]
    linear_combination (f a * ((∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, f i ^ 2)) * hx

private lemma sum_inv_sq_mod_p (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p) ^ 2)⁻¹ = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  let S : ZMod p := ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p) ^ 2)⁻¹
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h4ne : (2 : ZMod p) ^ 2 ≠ 1 := by
    intro h
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      have : (2 : ZMod p) ^ 2 - 1 = ((3 : ℕ) : ZMod p) := by norm_num
      rw [← this, h, sub_self]
    have := (ZMod.natCast_eq_zero_iff 3 p).mp h3
    have := Nat.le_of_dvd (by norm_num) this
    omega
  -- Compare S with ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ 2)⁻¹
  have hS_eq : S = ∑ x : ZMod p, if x ≠ 0 then (x ^ 2)⁻¹ else 0 := by
    dsimp [S]
    rw [← Finset.sum_filter]
    apply Finset.sum_nbij' (fun (k : ℕ) => (k : ZMod p)) (fun (x : ZMod p) => x.val)
    · intro k hk
      rw [Finset.mem_Icc] at hk
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro h0
      have := (ZMod.natCast_eq_zero_iff k p).mp h0
      have := Nat.le_of_dvd (by omega) this
      omega
    · intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_Icc]
      have hxpos : 0 < x.val := Nat.pos_of_ne_zero (fun h => hx.2 (by rw [← ZMod.natCast_zmod_val x, h]; simp))
      exact ⟨hxpos, Nat.le_pred_of_lt (ZMod.val_lt x)⟩
    · intro k hk
      rw [Finset.mem_Icc] at hk
      exact ZMod.val_natCast_of_lt (by omega)
    · intro x _
      exact ZMod.natCast_zmod_val x
    · intro k _; rfl
  have hscale : (2 : ZMod p) ^ 2 * S = S := by
    rw [hS_eq, Finset.mul_sum]
    let e : ZMod p ≃ ZMod p := Equiv.mulLeft₀ (2 : ZMod p) h2ne
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro x _
    change (2 : ZMod p) ^ 2 * (if (2 : ZMod p) * x ≠ 0 then (((2 : ZMod p) * x) ^ 2)⁻¹ else 0) =
      if x ≠ 0 then (x ^ 2)⁻¹ else 0
    by_cases hx : x = 0
    · simp [hx]
    · have h2x : (2 : ZMod p) * x ≠ 0 := mul_ne_zero h2ne hx
      rw [if_pos h2x, if_pos hx]
      have hsq : ((2 : ZMod p) * x) ^ 2 = (2 : ZMod p) ^ 2 * x ^ 2 := by ring
      rw [hsq, mul_inv]
      field_simp [h2ne, hx]
  have h0 : ((2 : ZMod p) ^ 2 - 1) * S = 0 := by linear_combination hscale
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr h4ne)

private lemma sum_alt_inv_sq_mod_p (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    ∑ k ∈ Finset.Icc 1 (p - 1), (-1 : ZMod p) ^ k * ((k : ZMod p) ^ 2)⁻¹ = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp_odd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with rfl | h <;> omega
  let S : ZMod p := ∑ k ∈ Finset.Icc 1 (p - 1), (-1 : ZMod p) ^ k * ((k : ZMod p) ^ 2)⁻¹
  have hrev : S = -S := by
    dsimp [S]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_nbij' (fun k => p - k) (fun k => p - k)
    · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
    · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
    · intro k hk; rw [Finset.mem_Icc] at hk; omega
    · intro k hk; rw [Finset.mem_Icc] at hk; omega
    · intro k hk
      rw [Finset.mem_Icc] at hk
      have hcast : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
        rw [Nat.cast_sub (by omega : k ≤ p), ZMod.natCast_self, zero_sub]
      rw [hcast, neg_sq]
      have hsign : (-1 : ZMod p) ^ (p - k) = -((-1 : ZMod p) ^ k) := by
        have h1 : (-1 : ZMod p) ^ (p - k) * (-1 : ZMod p) ^ k = (-1 : ZMod p) ^ p := by
          rw [← pow_add, Nat.sub_add_cancel (by omega : k ≤ p)]
        have h2 : (-1 : ZMod p) ^ p = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr hp_odd)
        have h3 : ((-1 : ZMod p) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        calc (-1 : ZMod p) ^ (p - k)
            = (-1 : ZMod p) ^ (p - k) * ((-1 : ZMod p) ^ k * (-1 : ZMod p) ^ k) := by
              rw [← sq, h3, mul_one]
          _ = ((-1 : ZMod p) ^ (p - k) * (-1 : ZMod p) ^ k) * (-1 : ZMod p) ^ k := by ring
          _ = -((-1 : ZMod p) ^ k) := by rw [h1, h2]; ring
      rw [hsign]; ring
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h0 : (2 : ZMod p) * S = 0 := by linear_combination hrev
  exact (mul_eq_zero.mp h0).resolve_left h2ne

private lemma sum_inv_mod_p2 (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹ = 0 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let S : ZMod (p ^ 2) := ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 2))⁻¹
  have hrev : S = ∑ k ∈ Finset.Icc 1 (p - 1), ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ := by
    dsimp [S]
    apply Finset.sum_nbij' (fun k => p - k) (fun k => p - k)
    · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
    · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
    · intro k hk; rw [Finset.mem_Icc] at hk; omega
    · intro k hk; rw [Finset.mem_Icc] at hk; omega
    · intro k hk; rw [Finset.mem_Icc] at hk; rw [show p - (p - k) = k by omega]
  have h2S : 2 * S = ∑ k ∈ Finset.Icc 1 (p - 1),
      ((k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹) := by
    rw [Finset.sum_add_distrib, ← hrev]; ring
  have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
      (k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ =
      -(p : ZMod (p ^ 2)) * ((k : ZMod (p ^ 2)) ^ 2)⁻¹ := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hki := zmod_mul_inv p 2 k hp hk.1 (by omega)
    have hpki := zmod_mul_inv p 2 (p - k) hp (by omega) (by omega)
    have hsub : ((p - k : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) - (k : ZMod (p ^ 2)) := by
      rw [Nat.cast_sub (by omega : k ≤ p)]
    have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    have hstep1 : (k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ =
        (p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ := by
      calc (k : ZMod (p ^ 2))⁻¹ + ((p - k : ℕ) : ZMod (p ^ 2))⁻¹
          = (k : ZMod (p ^ 2))⁻¹ * (((p - k : ℕ) : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹) +
            ((k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹) * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ := by
              rw [hki, hpki, mul_one, one_mul]
        _ = (((p - k : ℕ) : ZMod (p ^ 2)) + (k : ZMod (p ^ 2))) *
              (k : ZMod (p ^ 2))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ := by ring
        _ = (p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ := by
              rw [hsub]; ring
    have hstep2 : (p : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ =
        -(p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ := by
      have hmul : (p : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2)) =
          -(p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2)) := by
        rw [hsub]; linear_combination hp2
      calc (p : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹
          = (p : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ * ((k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹) := by
              rw [hki, mul_one]
        _ = (p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ * (k : ZMod (p ^ 2))⁻¹ := by ring
        _ = -(p : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ * (k : ZMod (p ^ 2))⁻¹ := by
              linear_combination ((p - k : ℕ) : ZMod (p ^ 2))⁻¹ * (k : ZMod (p ^ 2))⁻¹ * hmul
        _ = -(p : ZMod (p ^ 2)) * (((p - k : ℕ) : ZMod (p ^ 2)) * ((p - k : ℕ) : ZMod (p ^ 2))⁻¹) * (k : ZMod (p ^ 2))⁻¹ := by ring
        _ = -(p : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ := by rw [hpki, mul_one]
    have hsqinv : ((k : ZMod (p ^ 2)) ^ 2)⁻¹ = (k : ZMod (p ^ 2))⁻¹ * (k : ZMod (p ^ 2))⁻¹ := by
      have hcop : Nat.Coprime k (p ^ 2) :=
        ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 (by omega))).symm).pow_right 2
      have hu : IsUnit (k : ZMod (p ^ 2)) := (ZMod.isUnit_iff_coprime k (p ^ 2)).mpr hcop
      have hu2 : IsUnit ((k : ZMod (p ^ 2)) ^ 2) := hu.pow 2
      have hmul2 : (k : ZMod (p ^ 2)) ^ 2 * ((k : ZMod (p ^ 2))⁻¹ * (k : ZMod (p ^ 2))⁻¹) = 1 := by
        calc (k : ZMod (p ^ 2)) ^ 2 * ((k : ZMod (p ^ 2))⁻¹ * (k : ZMod (p ^ 2))⁻¹)
            = ((k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹) * ((k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹) := by ring
          _ = 1 := by rw [hki, mul_one]
      have hmul1 : (k : ZMod (p ^ 2)) ^ 2 * ((k : ZMod (p ^ 2)) ^ 2)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu2
      exact hu2.mul_left_cancel (hmul1.trans hmul2.symm)
    rw [hstep1, hsqinv]
    linear_combination (k : ZMod (p ^ 2))⁻¹ * hstep2
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum] at h2S
  -- Lift ∑ ((k : ZMod (p^2)) ^ 2)⁻¹ = 0 mod p via castHom
  have hmodp : (ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p))
      (∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2)) ^ 2)⁻¹) = 0 := by
    rw [map_sum]
    have heq : ∀ k ∈ Finset.Icc 1 (p - 1),
        (ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p)) (((k : ZMod (p ^ 2)) ^ 2)⁻¹) =
        ((k : ZMod p) ^ 2)⁻¹ := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hcop : Nat.Coprime k (p ^ 2) :=
        ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 (by omega))).symm).pow_right 2
      have hu2 : IsUnit ((k : ZMod (p ^ 2)) ^ 2) := ((ZMod.isUnit_iff_coprime k (p ^ 2)).mpr hcop).pow 2
      have hmul : (ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p)) ((k : ZMod (p ^ 2)) ^ 2) *
          (ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p)) (((k : ZMod (p ^ 2)) ^ 2)⁻¹) = 1 := by
        rw [← map_mul, ZMod.mul_inv_of_unit _ hu2, map_one]
      have hkn : (k : ZMod p) ≠ 0 := by
        intro h0
        have := (ZMod.natCast_eq_zero_iff k p).mp h0
        have := Nat.le_of_dvd hk.1 this
        omega
      have : Fact p.Prime := ⟨hp⟩
      rw [map_pow, map_natCast] at hmul
      calc (ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p)) (((k : ZMod (p ^ 2)) ^ 2)⁻¹)
          = ((k : ZMod p) ^ 2)⁻¹ * ((k : ZMod p) ^ 2 *
              (ZMod.castHom (dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p)) (((k : ZMod (p ^ 2)) ^ 2)⁻¹)) := by
            field_simp [hkn]
        _ = ((k : ZMod p) ^ 2)⁻¹ := by rw [hmul, mul_one]
    rw [Finset.sum_congr rfl heq]
    exact sum_inv_sq_mod_p p hp hp3
  have hp_mul_zero : (p : ZMod (p ^ 2)) * (∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2)) ^ 2)⁻¹) = 0 := by
    set T := ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2)) ^ 2)⁻¹
    have hTcast : (T.val : ZMod p) = 0 := by
      have := hmodp
      rw [← ZMod.natCast_zmod_val T] at this
      simpa using this
    have hdvd : p ∣ T.val := (ZMod.natCast_eq_zero_iff T.val p).mp hTcast
    rcases hdvd with ⟨c, hc⟩
    rw [← ZMod.natCast_zmod_val T, hc]
    push_cast
    have hp2 : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
      rw [← sq, ← Nat.cast_pow, ZMod.natCast_self]
    linear_combination (c : ZMod (p ^ 2)) * hp2
  have h2S0 : 2 * S = 0 := by
    rw [h2S]; linear_combination -hp_mul_zero
  have h2i := zmod_inv_two_mul p 2 hp hp3
  calc S = ((2 : ZMod (p ^ 2))⁻¹ * 2) * S := by rw [h2i, one_mul]
    _ = (2 : ZMod (p ^ 2))⁻¹ * (2 * S) := by ring
    _ = 0 := by rw [h2S0, mul_zero]

private lemma choose_two_p_mod_p3 (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    ((2 * p).choose p : ZMod (p ^ 3)) = 2 := by
  have : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  have hsum : (2 * p).choose p = ∑ k ∈ Finset.range (p + 1), (p.choose k) ^ 2 := by
    have h := Nat.add_choose_eq p p
    rw [← two_mul] at h
    rw [h, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => p.choose a * p.choose b) p]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Nat.choose_symm hk', sq]
  rw [hsum, Finset.sum_range_succ]
  rw [show p = (p - 1) + 1 by omega, Finset.sum_range_succ']
  rw [show p - 1 + 1 = p by omega]
  simp only [Nat.choose_self, Nat.choose_zero_right, one_pow]
  push_cast
  have hmid : ∑ k ∈ Finset.range (p - 1), ((p.choose (k + 1) : ZMod (p ^ 3)) ^ 2) = 0 := by
    -- Reindex to Icc 1 (p - 1)
    have hre : ∑ k ∈ Finset.range (p - 1), ((p.choose (k + 1) : ZMod (p ^ 3)) ^ 2) =
        ∑ k ∈ Finset.Icc 1 (p - 1), ((p.choose k : ZMod (p ^ 3)) ^ 2) := by
      apply Finset.sum_nbij' (fun k => k + 1) (fun k => k - 1)
      · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega
      · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
      · intro k _; omega
      · intro k hk; rw [Finset.mem_Icc] at hk; omega
      · intro k _; rfl
    rw [hre]
    have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
        (p.choose k : ZMod (p ^ 3)) ^ 2 = (p : ZMod (p ^ 3)) ^ 2 * ((k : ZMod (p ^ 3)) ^ 2)⁻¹ := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have h1 : k * p.choose k = p * (p - 1).choose (k - 1) := by
        have h := succ_mul_choose (p - 1) (k - 1)
        rw [show p - 1 + 1 = p by omega, show k - 1 + 1 = k by omega] at h
        linarith
      have h1z : (k : ZMod (p ^ 3)) * (p.choose k : ZMod (p ^ 3)) =
          (p : ZMod (p ^ 3)) * ((p - 1).choose (k - 1) : ZMod (p ^ 3)) := by
        simpa [Nat.cast_mul] using congrArg (Nat.cast (R := ZMod (p ^ 3))) h1
      have hki := zmod_mul_inv p 3 k hp hk.1 (by omega)
      have hch : (p.choose k : ZMod (p ^ 3)) =
          (p : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹ * ((p - 1).choose (k - 1) : ZMod (p ^ 3)) := by
        calc (p.choose k : ZMod (p ^ 3))
            = ((k : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹) * (p.choose k : ZMod (p ^ 3)) := by rw [hki, one_mul]
          _ = (k : ZMod (p ^ 3))⁻¹ * ((k : ZMod (p ^ 3)) * (p.choose k : ZMod (p ^ 3))) := by ring
          _ = (p : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹ * ((p - 1).choose (k - 1) : ZMod (p ^ 3)) := by
              rw [h1z]; ring
      -- Show ((p - 1).choose (k - 1)) ^ 2 ≡ 1 (mod p)
      have hmodp : (((p - 1).choose (k - 1) : ZMod p) ^ 2) = 1 := by
        have hfact : (p - 1).choose (k - 1) * (k - 1).factorial =
            ∏ i ∈ Finset.range (k - 1), (p - 1 - i) := by
          have := Nat.descFactorial_eq_factorial_mul_choose (p - 1) (k - 1)
          rw [mul_comm] at this
          rw [← this, Nat.descFactorial_eq_prod_range]
        have hfactz : ((p - 1).choose (k - 1) : ZMod p) * ((k - 1).factorial : ZMod p) =
            ∏ i ∈ Finset.range (k - 1), ((p - 1 - i : ℕ) : ZMod p) := by
          simpa [Nat.cast_mul, Nat.cast_prod] using congrArg (Nat.cast (R := ZMod p)) hfact
        have hprod : ∏ i ∈ Finset.range (k - 1), ((p - 1 - i : ℕ) : ZMod p) =
            (-1 : ZMod p) ^ (k - 1) * ((k - 1).factorial : ZMod p) := by
          have h1 : ∏ i ∈ Finset.range (k - 1), ((p - 1 - i : ℕ) : ZMod p) =
              ∏ i ∈ Finset.range (k - 1), (-1 : ZMod p) * ((i + 1 : ℕ) : ZMod p) := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [Finset.mem_range] at hi
            have hsub : ((p - 1 - i : ℕ) : ZMod p) = (p : ZMod p) - ((i + 1 : ℕ) : ZMod p) := by
              rw [show p - 1 - i = p - (i + 1) by omega, Nat.cast_sub (by omega)]
            rw [hsub, ZMod.natCast_self]; ring
          rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
          congr 1
          have hfac : ∀ m : ℕ, ∏ i ∈ Finset.range m, ((i + 1 : ℕ) : ZMod p) = (m.factorial : ZMod p) := by
            intro m; induction m with
            | zero => simp
            | succ m ihm => rw [Finset.prod_range_succ, ihm, Nat.factorial_succ]; push_cast; ring
          exact hfac (k - 1)
        rw [hprod] at hfactz
        have hfac_ne : ((k - 1).factorial : ZMod p) ≠ 0 := by
          intro h0
          have hd := (ZMod.natCast_eq_zero_iff _ p).mp h0
          have := hp.dvd_factorial.mp hd
          omega
        have : Fact p.Prime := ⟨hp⟩
        have hc : ((p - 1).choose (k - 1) : ZMod p) = (-1 : ZMod p) ^ (k - 1) :=
          mul_right_cancel₀ hfac_ne hfactz
        rw [hc, ← pow_mul, mul_comm, pow_mul]; norm_num
      have hdvd : p ∣ ((p - 1).choose (k - 1)) ^ 2 - 1 := by
        have hpos : 1 ≤ ((p - 1).choose (k - 1)) ^ 2 := by
          have : 0 < (p - 1).choose (k - 1) := Nat.choose_pos (by omega)
          nlinarith
        have hsub : ((((p - 1).choose (k - 1)) ^ 2 - 1 : ℕ) : ZMod p) = 0 := by
          rw [Nat.cast_sub hpos]; push_cast; rw [hmodp, sub_self]
        exact (ZMod.natCast_eq_zero_iff _ p).mp hsub
      rcases hdvd with ⟨c, hc⟩
      have hsq_eq : (((p - 1).choose (k - 1) : ZMod (p ^ 3)) ^ 2) = 1 + (p : ZMod (p ^ 3)) * c := by
        have hpos : 1 ≤ ((p - 1).choose (k - 1)) ^ 2 := by
          have : 0 < (p - 1).choose (k - 1) := Nat.choose_pos (by omega)
          nlinarith
        have hnat : ((p - 1).choose (k - 1)) ^ 2 = 1 + p * c := by omega
        simpa [Nat.cast_pow, Nat.cast_add, Nat.cast_mul] using congrArg (Nat.cast (R := ZMod (p ^ 3))) hnat
      have hp3z : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
      have hsqinv : ((k : ZMod (p ^ 3)) ^ 2)⁻¹ = (k : ZMod (p ^ 3))⁻¹ * (k : ZMod (p ^ 3))⁻¹ := by
        have hcop : Nat.Coprime k (p ^ 3) :=
          ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 (by omega))).symm).pow_right 3
        have hu2 : IsUnit ((k : ZMod (p ^ 3)) ^ 2) := ((ZMod.isUnit_iff_coprime k (p ^ 3)).mpr hcop).pow 2
        have hmul2 : (k : ZMod (p ^ 3)) ^ 2 * ((k : ZMod (p ^ 3))⁻¹ * (k : ZMod (p ^ 3))⁻¹) = 1 := by
          calc (k : ZMod (p ^ 3)) ^ 2 * ((k : ZMod (p ^ 3))⁻¹ * (k : ZMod (p ^ 3))⁻¹)
              = ((k : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹) * ((k : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹) := by ring
            _ = 1 := by rw [hki, mul_one]
        exact hu2.mul_left_cancel ((ZMod.mul_inv_of_unit _ hu2).trans hmul2.symm)
      rw [hch, mul_pow, mul_pow, hsq_eq, hsqinv]
      linear_combination ((k : ZMod (p ^ 3))⁻¹ ^ 2 * c) * hp3z
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    set T := ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 3)) ^ 2)⁻¹
    have hT0 : (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) T = 0 := by
      dsimp only [T]
      rw [map_sum]
      have heq : ∀ k ∈ Finset.Icc 1 (p - 1),
          (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) (((k : ZMod (p ^ 3)) ^ 2)⁻¹) =
          ((k : ZMod p) ^ 2)⁻¹ := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        have hcop : Nat.Coprime k (p ^ 3) :=
          ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk.1 (by omega))).symm).pow_right 3
        have hu2 : IsUnit ((k : ZMod (p ^ 3)) ^ 2) := ((ZMod.isUnit_iff_coprime k (p ^ 3)).mpr hcop).pow 2
        have hmul : (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) ((k : ZMod (p ^ 3)) ^ 2) *
            (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) (((k : ZMod (p ^ 3)) ^ 2)⁻¹) = 1 := by
          rw [← map_mul, ZMod.mul_inv_of_unit _ hu2, map_one]
        have : Fact p.Prime := ⟨hp⟩
        have hkn : (k : ZMod p) ≠ 0 := by
          intro h0
          have := (ZMod.natCast_eq_zero_iff k p).mp h0
          have := Nat.le_of_dvd hk.1 this
          omega
        rw [map_pow, map_natCast] at hmul
        calc (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) (((k : ZMod (p ^ 3)) ^ 2)⁻¹)
            = ((k : ZMod p) ^ 2)⁻¹ * ((k : ZMod p) ^ 2 *
                (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) (((k : ZMod (p ^ 3)) ^ 2)⁻¹)) := by
              field_simp [hkn]
          _ = ((k : ZMod p) ^ 2)⁻¹ := by rw [hmul, mul_one]
      rw [Finset.sum_congr rfl heq]
      exact sum_inv_sq_mod_p p hp hp3
    have hdvd : p ∣ T.val := by
      have hTcast : (T.val : ZMod p) = 0 := by
        have := hT0
        rw [← ZMod.natCast_zmod_val T] at this
        simpa using this
      exact (ZMod.natCast_eq_zero_iff T.val p).mp hTcast
    rcases hdvd with ⟨c, hc⟩
    rw [← ZMod.natCast_zmod_val T, hc]
    push_cast
    have hp3z : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    linear_combination (c : ZMod (p ^ 3)) * hp3z
  rw [hmid]; ring

private lemma morley_int_id (m : ℕ) :
    (-1 : ℤ) ^ m * ((2 * m).choose m : ℤ) * ((2 * m).factorial : ℤ) =
      (2 : ℤ) ^ (2 * m) * ∏ k ∈ Finset.Icc 1 (2 * m), (2 * (k : ℤ) - (2 * m + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hch : (m + 1) ^ 2 * ((2 * (m + 1)).choose (m + 1)) =
        (2 * m + 2) * (2 * m + 1) * ((2 * m).choose m) := by
      have h1 := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
      have h2 := Nat.choose_mul_factorial_mul_factorial (show m + 1 ≤ 2 * (m + 1) by omega)
      rw [show 2 * m - m = m by omega] at h1
      rw [show 2 * (m + 1) - (m + 1) = m + 1 by omega] at h2
      have hpos : m.factorial * m.factorial ≠ 0 :=
        mul_ne_zero (Nat.factorial_ne_zero m) (Nat.factorial_ne_zero m)
      apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos)
      calc (m + 1) ^ 2 * (2 * (m + 1)).choose (m + 1) * (m.factorial * m.factorial)
          = (2 * (m + 1)).choose (m + 1) * ((m + 1) * m.factorial) * ((m + 1) * m.factorial) := by ring
        _ = (2 * (m + 1)).choose (m + 1) * (m + 1).factorial * (m + 1).factorial := by
            rw [Nat.factorial_succ]
        _ = (2 * (m + 1)).factorial := h2
        _ = (2 * m + 2) * ((2 * m + 1) * (2 * m).factorial) := by
            rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
        _ = (2 * m + 2) * (2 * m + 1) * ((2 * m).choose m * m.factorial * m.factorial) := by
            rw [← h1]; ring
        _ = (2 * m + 2) * (2 * m + 1) * (2 * m).choose m * (m.factorial * m.factorial) := by ring
    have hfac : (2 * (m + 1)).factorial = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]; ring
    have hprod : ∏ k ∈ Finset.Icc 1 (2 * (m + 1)), (2 * (k : ℤ) - (2 * (m + 1 : ℕ) + 1)) =
        -(2 * (m : ℤ) + 1) ^ 2 * ∏ k ∈ Finset.Icc 1 (2 * m), (2 * (k : ℤ) - (2 * m + 1)) := by
      have hsplit : Finset.Icc 1 (2 * (m + 1)) =
          insert 1 (insert (2 * m + 2) (Finset.Icc 2 (2 * m + 1))) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsplit, Finset.prod_insert (by simp), Finset.prod_insert (by simp)]
      have hshift : ∏ k ∈ Finset.Icc 2 (2 * m + 1), (2 * (k : ℤ) - (2 * (m + 1 : ℕ) + 1)) =
          ∏ k ∈ Finset.Icc 1 (2 * m), (2 * (k : ℤ) - (2 * m + 1)) := by
        apply Finset.prod_nbij' (fun k => k - 1) (fun k => k + 1)
        · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
        · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
        · intro k hk; rw [Finset.mem_Icc] at hk; omega
        · intro k hk; rw [Finset.mem_Icc] at hk; omega
        · intro k hk
          rw [Finset.mem_Icc] at hk
          have : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
          rw [this]; push_cast; ring
      rw [hshift]
      push_cast; ring
    have hchz : ((m : ℤ) + 1) ^ 2 * ((2 * (m + 1)).choose (m + 1) : ℤ) =
        (2 * (m : ℤ) + 2) * (2 * (m : ℤ) + 1) * ((2 * m).choose m : ℤ) := by exact_mod_cast hch
    have hfacz : ((2 * (m + 1)).factorial : ℤ) =
        (2 * (m : ℤ) + 2) * (2 * (m : ℤ) + 1) * ((2 * m).factorial : ℤ) := by exact_mod_cast hfac
    have hm1 : ((m : ℤ) + 1) ^ 2 ≠ 0 := by positivity
    apply mul_left_cancel₀ hm1
    rw [hprod, hfacz]
    calc ((m : ℤ) + 1) ^ 2 * ((-1 : ℤ) ^ (m + 1) * ((2 * (m + 1)).choose (m + 1) : ℤ) *
            ((2 * (m : ℤ) + 2) * (2 * (m : ℤ) + 1) * ((2 * m).factorial : ℤ)))
        = (-1 : ℤ) ^ (m + 1) * (((m : ℤ) + 1) ^ 2 * ((2 * (m + 1)).choose (m + 1) : ℤ)) *
            ((2 * (m : ℤ) + 2) * (2 * (m : ℤ) + 1) * ((2 * m).factorial : ℤ)) := by ring
      _ = (-1 : ℤ) ^ (m + 1) * ((2 * (m : ℤ) + 2) * (2 * (m : ℤ) + 1) * ((2 * m).choose m : ℤ)) *
            ((2 * (m : ℤ) + 2) * (2 * (m : ℤ) + 1) * ((2 * m).factorial : ℤ)) := by rw [hchz]
      _ = -4 * ((m : ℤ) + 1) ^ 2 * (2 * (m : ℤ) + 1) ^ 2 *
            ((-1 : ℤ) ^ m * ((2 * m).choose m : ℤ) * ((2 * m).factorial : ℤ)) := by
            rw [pow_succ]; ring
      _ = -4 * ((m : ℤ) + 1) ^ 2 * (2 * (m : ℤ) + 1) ^ 2 *
            ((2 : ℤ) ^ (2 * m) * ∏ k ∈ Finset.Icc 1 (2 * m), (2 * (k : ℤ) - (2 * m + 1))) := by
            rw [ih]
      _ = ((m : ℤ) + 1) ^ 2 * ((2 : ℤ) ^ (2 * (m + 1)) *
            (-(2 * (m : ℤ) + 1) ^ 2 * ∏ k ∈ Finset.Icc 1 (2 * m), (2 * (k : ℤ) - (2 * m + 1)))) := by
            rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]; norm_num; ring

private lemma morley_congruence (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    (-1 : ZMod (p ^ 3)) ^ ((p - 1) / 2) * ((p - 1).choose ((p - 1) / 2) : ZMod (p ^ 3)) =
      (4 : ZMod (p ^ 3)) ^ (p - 1) := by
  have : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  have hp_odd : p % 2 = 1 := by rcases hp.eq_two_or_odd with rfl | h <;> omega
  set m := (p - 1) / 2
  have h2m : 2 * m = p - 1 := by omega
  have h2m1 : 2 * m + 1 = p := by omega
  have hid := congrArg (Int.cast (R := ZMod (p ^ 3))) (morley_int_id m)
  push_cast at hid
  rw [h2m] at hid
  -- Rewrite ∏ (2*k - p) = 2^(p-1) * (p-1)! * ∏ (1 + p * (-(2*k)⁻¹))
  have hprod : ∏ k ∈ Finset.Icc 1 (p - 1), (2 * (k : ZMod (p ^ 3)) - (2 * (m : ZMod (p ^ 3)) + 1)) =
      (2 : ZMod (p ^ 3)) ^ (p - 1) * ((p - 1).factorial : ZMod (p ^ 3)) *
        ∏ k ∈ Finset.Icc 1 (p - 1), (1 + (p : ZMod (p ^ 3)) * -((2 : ZMod (p ^ 3))⁻¹ * (k : ZMod (p ^ 3))⁻¹)) := by
    have h2m1z : (2 * (m : ZMod (p ^ 3)) + 1) = (p : ZMod (p ^ 3)) := by
      simpa [Nat.cast_add, Nat.cast_mul] using congrArg (Nat.cast (R := ZMod (p ^ 3))) h2m1
    have hfac : ∏ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 3)) = ((p - 1).factorial : ZMod (p ^ 3)) := by
      have h : ∀ n : ℕ, ∏ k ∈ Finset.Icc 1 n, (k : ZMod (p ^ 3)) = (n.factorial : ZMod (p ^ 3)) := by
        intro n; induction n with
        | zero => simp
        | succ n ihn =>
          have hI : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hI, Finset.prod_insert (by simp), ihn, Nat.factorial_succ]; push_cast; ring
      exact h (p - 1)
    have h2pow : (2 : ZMod (p ^ 3)) ^ (p - 1) = ∏ _k ∈ Finset.Icc 1 (p - 1), (2 : ZMod (p ^ 3)) := by
      rw [Finset.prod_const, show (Finset.Icc 1 (p - 1)).card = p - 1 by simp]
    rw [← hfac, h2pow]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    have h2i := zmod_two_mul_inv p 3 hp hp3
    have hki := zmod_mul_inv p 3 k hp hk.1 (by omega)
    rw [h2m1z]
    calc 2 * (k : ZMod (p ^ 3)) - (p : ZMod (p ^ 3))
        = 2 * (k : ZMod (p ^ 3)) - (p : ZMod (p ^ 3)) * ((2 * (2 : ZMod (p ^ 3))⁻¹) * ((k : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹)) := by
            rw [h2i, hki, mul_one, mul_one]
      _ = 2 * (k : ZMod (p ^ 3)) * (1 + (p : ZMod (p ^ 3)) * -((2 : ZMod (p ^ 3))⁻¹ * (k : ZMod (p ^ 3))⁻¹)) := by ring
  -- Evaluate ∏ (1 + p * (-(2k)⁻¹)) = 1 in ZMod (p^3)
  have hprod1 : ∏ k ∈ Finset.Icc 1 (p - 1),
      (1 + (p : ZMod (p ^ 3)) * -((2 : ZMod (p ^ 3))⁻¹ * (k : ZMod (p ^ 3))⁻¹)) = 1 := by
    have hp3z : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    have hexp := prod_one_add_mul (Finset.Icc 1 (p - 1)) (p : ZMod (p ^ 3)) hp3z
      (fun k => -((2 : ZMod (p ^ 3))⁻¹ * (k : ZMod (p ^ 3))⁻¹))
    set S1 : ZMod (p ^ 3) := ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 3))⁻¹
    set S2 : ZMod (p ^ 3) := ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 3))⁻¹) ^ 2
    have hsum1 : ∑ k ∈ Finset.Icc 1 (p - 1), -((2 : ZMod (p ^ 3))⁻¹ * (k : ZMod (p ^ 3))⁻¹) =
        -(2 : ZMod (p ^ 3))⁻¹ * S1 := by
      dsimp [S1]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    have hsum2 : ∑ k ∈ Finset.Icc 1 (p - 1), (-((2 : ZMod (p ^ 3))⁻¹ * (k : ZMod (p ^ 3))⁻¹)) ^ 2 =
        ((2 : ZMod (p ^ 3))⁻¹) ^ 2 * S2 := by
      dsimp [S2]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    rw [hsum1, hsum2] at hexp
    -- p * S1 = 0 in ZMod (p^3) because S1 = 0 in ZMod (p^2)
    have hpS1 : (p : ZMod (p ^ 3)) * S1 = 0 := by
      have hcast : (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2))) S1 = 0 := by
        dsimp only [S1]; rw [map_sum]
        have heq : ∀ k ∈ Finset.Icc 1 (p - 1),
            (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2))) ((k : ZMod (p ^ 3))⁻¹) =
            (k : ZMod (p ^ 2))⁻¹ := by
          intro k hk
          rw [Finset.mem_Icc] at hk
          have hki3 := zmod_mul_inv p 3 k hp hk.1 (by omega)
          have hki2 := zmod_inv_mul p 2 k hp hk.1 (by omega)
          have hmul : (k : ZMod (p ^ 2)) *
              (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2))) ((k : ZMod (p ^ 3))⁻¹) = 1 := by
            have := congrArg (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2))) hki3
            rw [map_mul, map_natCast, map_one] at this
            exact this
          calc (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2))) ((k : ZMod (p ^ 3))⁻¹)
              = ((k : ZMod (p ^ 2))⁻¹ * (k : ZMod (p ^ 2))) *
                  (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2))) ((k : ZMod (p ^ 3))⁻¹) := by
                rw [hki2, one_mul]
            _ = (k : ZMod (p ^ 2))⁻¹ * ((k : ZMod (p ^ 2)) *
                  (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2))) ((k : ZMod (p ^ 3))⁻¹)) := by ring
            _ = (k : ZMod (p ^ 2))⁻¹ := by rw [hmul, mul_one]
        rw [Finset.sum_congr rfl heq]
        exact sum_inv_mod_p2 p hp hp3
      have hdvd : p ^ 2 ∣ S1.val := by
        have hS1c : (S1.val : ZMod (p ^ 2)) = 0 := by
          have := hcast
          rw [← ZMod.natCast_zmod_val S1] at this
          simpa using this
        exact (ZMod.natCast_eq_zero_iff S1.val (p ^ 2)).mp hS1c
      rcases hdvd with ⟨c, hc⟩
      rw [← ZMod.natCast_zmod_val S1, hc]; push_cast
      linear_combination (c : ZMod (p ^ 3)) * hp3z
    -- p^2 * S2 = 0 in ZMod (p^3) because S2 = 0 in ZMod p
    have hp2S2 : (p : ZMod (p ^ 3)) ^ 2 * S2 = 0 := by
      have hcast : (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) S2 = 0 := by
        dsimp only [S2]; rw [map_sum]
        have heq : ∀ k ∈ Finset.Icc 1 (p - 1),
            (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) (((k : ZMod (p ^ 3))⁻¹) ^ 2) =
            ((k : ZMod p) ^ 2)⁻¹ := by
          intro k hk
          rw [Finset.mem_Icc] at hk
          have hki3 := zmod_mul_inv p 3 k hp hk.1 (by omega)
          have hmul : (k : ZMod p) *
              (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) ((k : ZMod (p ^ 3))⁻¹) = 1 := by
            have := congrArg (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) hki3
            simpa using this
          have : Fact p.Prime := ⟨hp⟩
          have hkn : (k : ZMod p) ≠ 0 := by
            intro h0
            have := (ZMod.natCast_eq_zero_iff k p).mp h0
            have := Nat.le_of_dvd hk.1 this
            omega
          have h1 : (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) ((k : ZMod (p ^ 3))⁻¹) =
              (k : ZMod p)⁻¹ := by
            calc _ = (k : ZMod p)⁻¹ * ((k : ZMod p) *
                  (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) ((k : ZMod (p ^ 3))⁻¹)) := by
                  field_simp [hkn]
              _ = (k : ZMod p)⁻¹ := by rw [hmul, mul_one]
          rw [map_pow, h1, inv_pow]
        rw [Finset.sum_congr rfl heq]
        exact sum_inv_sq_mod_p p hp hp3
      have hdvd : p ∣ S2.val := by
        have hS2c : (S2.val : ZMod p) = 0 := by
          have := hcast
          rw [← ZMod.natCast_zmod_val S2] at this
          simpa using this
        exact (ZMod.natCast_eq_zero_iff S2.val p).mp hS2c
      rcases hdvd with ⟨c, hc⟩
      rw [← ZMod.natCast_zmod_val S2, hc]; push_cast
      linear_combination (c : ZMod (p ^ 3)) * hp3z
    have h2prod : 2 * (∏ k ∈ Finset.Icc 1 (p - 1),
        (1 + (p : ZMod (p ^ 3)) * -((2 : ZMod (p ^ 3))⁻¹ * (k : ZMod (p ^ 3))⁻¹))) = 2 := by
      rw [hexp]
      linear_combination
        (-(2 * (2 : ZMod (p ^ 3))⁻¹) + (p : ZMod (p ^ 3)) * ((2 : ZMod (p ^ 3))⁻¹) ^ 2 * S1) * hpS1 -
        ((2 : ZMod (p ^ 3))⁻¹) ^ 2 * hp2S2
    have h2i := zmod_inv_two_mul p 3 hp hp3
    set P : ZMod (p ^ 3) := ∏ k ∈ Finset.Icc 1 (p - 1),
      (1 + (p : ZMod (p ^ 3)) * -((2 : ZMod (p ^ 3))⁻¹ * (k : ZMod (p ^ 3))⁻¹))
    calc P = ((2 : ZMod (p ^ 3))⁻¹ * 2) * P := by rw [h2i, one_mul]
      _ = (2 : ZMod (p ^ 3))⁻¹ * (2 * P) := by ring
      _ = (2 : ZMod (p ^ 3))⁻¹ * 2 := by rw [h2prod]
      _ = 1 := h2i
  rw [hprod, hprod1, mul_one] at hid
  have hfac_unit : IsUnit ((p - 1).factorial : ZMod (p ^ 3)) := by
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    have hnd : ¬ p ∣ (p - 1).factorial := fun hd => by
      have := hp.dvd_factorial.mp hd; omega
    exact ((hp.coprime_iff_not_dvd.mpr hnd).symm).pow_right 3
  have h4eq : (2 : ZMod (p ^ 3)) ^ (p - 1) * (2 : ZMod (p ^ 3)) ^ (p - 1) = (4 : ZMod (p ^ 3)) ^ (p - 1) := by
    rw [← mul_pow]; norm_num
  apply hfac_unit.mul_right_cancel
  calc (-1 : ZMod (p ^ 3)) ^ m * ((p - 1).choose m : ZMod (p ^ 3)) * ((p - 1).factorial : ZMod (p ^ 3))
      = (2 : ZMod (p ^ 3)) ^ (p - 1) * ((2 : ZMod (p ^ 3)) ^ (p - 1) * ((p - 1).factorial : ZMod (p ^ 3))) := hid
    _ = (4 : ZMod (p ^ 3)) ^ (p - 1) * ((p - 1).factorial : ZMod (p ^ 3)) := by rw [← mul_assoc, h4eq]

private lemma harmonic_half_mod_p2 (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    let q : ℤ := ((2 ^ (p - 1) - 1) / p : ℕ)
    (p : ZMod (p ^ 3)) * (∑ k ∈ Finset.Icc 1 ((p - 1) / 2), (k : ZMod (p ^ 3))⁻¹) =
      -2 * (p : ZMod (p ^ 3)) * (q : ZMod (p ^ 3)) + (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3)) ^ 2 := by
  intro q
  have : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  have hp_odd : p % 2 = 1 := by rcases hp.eq_two_or_odd with rfl | h <;> omega
  set m := (p - 1) / 2
  -- Expand (-1)^m * C(p-1, m) = ∏_{k=1}^m (1 + p * (-k⁻¹)) in ZMod (p^3)
  have hch_prod : (-1 : ZMod (p ^ 3)) ^ m * ((p - 1).choose m : ZMod (p ^ 3)) =
      ∏ k ∈ Finset.Icc 1 m, (1 + (p : ZMod (p ^ 3)) * -(k : ZMod (p ^ 3))⁻¹) := by
    have hdesc : (p - 1).choose m * m.factorial = ∏ i ∈ Finset.range m, (p - 1 - i) := by
      have := Nat.descFactorial_eq_factorial_mul_choose (p - 1) m
      rw [mul_comm] at this
      rw [← this, Nat.descFactorial_eq_prod_range]
    have hdescz : ((p - 1).choose m : ZMod (p ^ 3)) * (m.factorial : ZMod (p ^ 3)) =
        ∏ i ∈ Finset.range m, ((p - 1 - i : ℕ) : ZMod (p ^ 3)) := by
      simpa [Nat.cast_mul, Nat.cast_prod] using congrArg (Nat.cast (R := ZMod (p ^ 3))) hdesc
    have hfac_eq : (m.factorial : ZMod (p ^ 3)) = ∏ k ∈ Finset.Icc 1 m, (k : ZMod (p ^ 3)) := by
      have h : ∀ n : ℕ, (n.factorial : ZMod (p ^ 3)) = ∏ k ∈ Finset.Icc 1 n, (k : ZMod (p ^ 3)) := by
        intro n; induction n with
        | zero => simp
        | succ n ihn =>
          have hI : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hI, Finset.prod_insert (by simp), ← ihn, Nat.factorial_succ]; push_cast; ring
      exact h m
    have hunit : IsUnit (m.factorial : ZMod (p ^ 3)) := by
      apply (ZMod.isUnit_iff_coprime _ _).mpr
      have hnd : ¬ p ∣ m.factorial := fun hd => by
        have := hp.dvd_factorial.mp hd; omega
      exact ((hp.coprime_iff_not_dvd.mpr hnd).symm).pow_right 3
    apply hunit.mul_right_cancel
    have hshift : ∏ i ∈ Finset.range m, ((p - 1 - i : ℕ) : ZMod (p ^ 3)) =
        ∏ k ∈ Finset.Icc 1 m, ((p : ZMod (p ^ 3)) - (k : ZMod (p ^ 3))) := by
      apply Finset.prod_nbij' (fun i => i + 1) (fun k => k - 1)
      · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_Icc]; omega
      · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
      · intro i _; omega
      · intro k hk; rw [Finset.mem_Icc] at hk; omega
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [show p - 1 - i = p - (i + 1) by omega, Nat.cast_sub (by omega)]
    rw [mul_assoc, hdescz, hshift, hfac_eq, ← Finset.prod_mul_distrib]
    have hsign : (-1 : ZMod (p ^ 3)) ^ m = ∏ _k ∈ Finset.Icc 1 m, (-1 : ZMod (p ^ 3)) := by
      rw [Finset.prod_const, show (Finset.Icc 1 m).card = m by simp]
    rw [hsign, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hki := zmod_mul_inv p 3 k hp hk.1 (by omega)
    calc (-1 : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) - (k : ZMod (p ^ 3)))
        = (k : ZMod (p ^ 3)) - (p : ZMod (p ^ 3)) * ((k : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹) := by
          rw [hki, mul_one]; ring
      _ = (1 + (p : ZMod (p ^ 3)) * -(k : ZMod (p ^ 3))⁻¹) * (k : ZMod (p ^ 3)) := by ring
  -- Expand RHS using prod_one_add_mul
  have hp3z : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hexp := prod_one_add_mul (Finset.Icc 1 m) (p : ZMod (p ^ 3)) hp3z (fun k => -(k : ZMod (p ^ 3))⁻¹)
  set H : ZMod (p ^ 3) := ∑ k ∈ Finset.Icc 1 m, (k : ZMod (p ^ 3))⁻¹
  set H2 : ZMod (p ^ 3) := ∑ k ∈ Finset.Icc 1 m, ((k : ZMod (p ^ 3))⁻¹) ^ 2
  have hsum1 : ∑ k ∈ Finset.Icc 1 m, -(k : ZMod (p ^ 3))⁻¹ = -H := by
    dsimp [H]; rw [Finset.sum_neg_distrib]
  have hsum2 : ∑ k ∈ Finset.Icc 1 m, (-(k : ZMod (p ^ 3))⁻¹) ^ 2 = H2 := by
    dsimp [H2]; apply Finset.sum_congr rfl; intro k _; ring
  rw [hsum1, hsum2, ← hch_prod, morley_congruence p hp hp3] at hexp
  -- Show p^2 * H2 = 0 in ZMod (p^3)
  have hp2H2 : (p : ZMod (p ^ 3)) ^ 2 * H2 = 0 := by
    have hH2_modp : (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) H2 = 0 := by
      have : Fact p.Prime := ⟨hp⟩
      have h2sum : 2 * (∑ k ∈ Finset.Icc 1 m, ((k : ZMod p) ^ 2)⁻¹) =
          ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p) ^ 2)⁻¹ := by
        have hsplit : Finset.Icc 1 (p - 1) = Finset.Icc 1 m ∪ Finset.Icc (m + 1) (p - 1) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
        have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Icc (m + 1) (p - 1)) := by
          rw [Finset.disjoint_left]; intro x hx1 hx2; rw [Finset.mem_Icc] at hx1 hx2; omega
        rw [hsplit, Finset.sum_union hdisj]
        have hsym : ∑ k ∈ Finset.Icc (m + 1) (p - 1), ((k : ZMod p) ^ 2)⁻¹ =
            ∑ k ∈ Finset.Icc 1 m, ((k : ZMod p) ^ 2)⁻¹ := by
          apply Finset.sum_nbij' (fun k => p - k) (fun k => p - k)
          · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
          · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
          · intro k hk; rw [Finset.mem_Icc] at hk; omega
          · intro k hk; rw [Finset.mem_Icc] at hk; omega
          · intro k hk
            rw [Finset.mem_Icc] at hk
            rw [Nat.cast_sub (by omega : k ≤ p), ZMod.natCast_self, zero_sub, neg_sq]
        rw [hsym]; ring
      rw [sum_inv_sq_mod_p p hp hp3] at h2sum
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h; have := (ZMod.natCast_eq_zero_iff 2 p).mp h; have := Nat.le_of_dvd (by norm_num) this; omega
      have hzero : ∑ k ∈ Finset.Icc 1 m, ((k : ZMod p) ^ 2)⁻¹ = 0 :=
        (mul_eq_zero.mp h2sum).resolve_left h2ne
      dsimp only [H2]; rw [map_sum]
      have heq : ∀ k ∈ Finset.Icc 1 m,
          (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) (((k : ZMod (p ^ 3))⁻¹) ^ 2) =
          ((k : ZMod p) ^ 2)⁻¹ := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        have hki3 := zmod_mul_inv p 3 k hp hk.1 (by omega)
        have hmul : (k : ZMod p) *
            (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) ((k : ZMod (p ^ 3))⁻¹) = 1 := by
          have := congrArg (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) hki3
          simpa using this
        have hkn : (k : ZMod p) ≠ 0 := by
          intro h0; have := (ZMod.natCast_eq_zero_iff k p).mp h0; have := Nat.le_of_dvd hk.1 this; omega
        have h1 : (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) ((k : ZMod (p ^ 3))⁻¹) =
            (k : ZMod p)⁻¹ := by
          calc _ = (k : ZMod p)⁻¹ * ((k : ZMod p) *
                (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) ((k : ZMod (p ^ 3))⁻¹)) := by
                field_simp [hkn]
            _ = (k : ZMod p)⁻¹ := by rw [hmul, mul_one]
        rw [map_pow, h1, inv_pow]
      rw [Finset.sum_congr rfl heq, hzero]
    have hdvd : p ∣ H2.val := by
      have hH2c : (H2.val : ZMod p) = 0 := by
        have := hH2_modp; rw [← ZMod.natCast_zmod_val H2] at this; simpa using this
      exact (ZMod.natCast_eq_zero_iff H2.val p).mp hH2c
    rcases hdvd with ⟨c, hc⟩
    rw [← ZMod.natCast_zmod_val H2, hc]; push_cast
    linear_combination (c : ZMod (p ^ 3)) * hp3z
  -- Express 4^(p-1) = (1 + p*q)^2 = 1 + 2*p*q + p^2*q^2
  have hfermat : p ∣ 2 ^ (p - 1) - 1 := by
    have : Fact p.Prime := ⟨hp⟩
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h; have := (ZMod.natCast_eq_zero_iff 2 p).mp h; have := Nat.le_of_dvd (by norm_num) this; omega
    have h1 : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
    have hpos : 1 ≤ 2 ^ (p - 1) := Nat.one_le_pow _ _ (by norm_num)
    have h0 : ((2 ^ (p - 1) - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub hpos]; push_cast; rw [h1, sub_self]
    exact (ZMod.natCast_eq_zero_iff _ p).mp h0
  have h2pow : (2 : ZMod (p ^ 3)) ^ (p - 1) = 1 + (p : ZMod (p ^ 3)) * (q : ZMod (p ^ 3)) := by
    have hpos : 1 ≤ 2 ^ (p - 1) := Nat.one_le_pow _ _ (by norm_num)
    have hnat : 2 ^ (p - 1) = 1 + p * ((2 ^ (p - 1) - 1) / p) := by
      have hdiv := Nat.mul_div_cancel' hfermat
      omega
    have hcast : ((2 ^ (p - 1) : ℕ) : ZMod (p ^ 3)) =
        ((1 + p * ((2 ^ (p - 1) - 1) / p) : ℕ) : ZMod (p ^ 3)) := congrArg Nat.cast hnat
    push_cast at hcast
    have hq : (q : ZMod (p ^ 3)) = (((2 ^ (p - 1) - 1) / p : ℕ) : ZMod (p ^ 3)) := by
      dsimp only [q]; exact Int.cast_natCast _
    rw [hq]; exact hcast
  have h4pow : (4 : ZMod (p ^ 3)) ^ (p - 1) =
      1 + 2 * (p : ZMod (p ^ 3)) * (q : ZMod (p ^ 3)) + (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3)) ^ 2 := by
    have : (4 : ZMod (p ^ 3)) ^ (p - 1) = ((2 : ZMod (p ^ 3)) ^ (p - 1)) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this, h2pow]; ring
  rw [h4pow] at hexp
  -- hexp : 2 + 4pq + 2p^2 q^2 = 2 - 2pH + p^2 H^2 - p^2 H2
  have hrel : 2 * (p : ZMod (p ^ 3)) * H =
      -4 * (p : ZMod (p ^ 3)) * (q : ZMod (p ^ 3)) - 2 * (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3)) ^ 2 +
      (p : ZMod (p ^ 3)) ^ 2 * H ^ 2 := by
    linear_combination hexp - hp2H2
  -- Multiply hrel by p to get p^2 * H = -2 * p^2 * q
  have hp2H : (p : ZMod (p ^ 3)) ^ 2 * H = -2 * (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3)) := by
    have h2 : 2 * ((p : ZMod (p ^ 3)) ^ 2 * H) = 2 * (-2 * (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3))) := by
      linear_combination (p : ZMod (p ^ 3)) * hrel - (2 * (q : ZMod (p ^ 3)) ^ 2 - H ^ 2) * hp3z
    have h2i := zmod_inv_two_mul p 3 hp hp3
    calc (p : ZMod (p ^ 3)) ^ 2 * H
        = ((2 : ZMod (p ^ 3))⁻¹ * 2) * ((p : ZMod (p ^ 3)) ^ 2 * H) := by rw [h2i, one_mul]
      _ = (2 : ZMod (p ^ 3))⁻¹ * (2 * ((p : ZMod (p ^ 3)) ^ 2 * H)) := by ring
      _ = (2 : ZMod (p ^ 3))⁻¹ * (2 * (-2 * (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3)))) := by rw [h2]
      _ = ((2 : ZMod (p ^ 3))⁻¹ * 2) * (-2 * (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3))) := by ring
      _ = -2 * (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3)) := by rw [h2i, one_mul]
  -- Hence p^2 * H^2 = 4 * p^2 * q^2
  have hp2Hsq : (p : ZMod (p ^ 3)) ^ 2 * H ^ 2 = 4 * (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3)) ^ 2 := by
    calc (p : ZMod (p ^ 3)) ^ 2 * H ^ 2
        = ((p : ZMod (p ^ 3)) ^ 2 * H) * H := by ring
      _ = (-2 * (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3))) * H := by rw [hp2H]
      _ = -2 * (q : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) ^ 2 * H) := by ring
      _ = -2 * (q : ZMod (p ^ 3)) * (-2 * (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3))) := by rw [hp2H]
      _ = 4 * (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3)) ^ 2 := by ring
  rw [hp2Hsq] at hrel
  have h2i := zmod_inv_two_mul p 3 hp hp3
  have h2goal : 2 * ((p : ZMod (p ^ 3)) * H) =
      2 * (-2 * (p : ZMod (p ^ 3)) * (q : ZMod (p ^ 3)) + (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3)) ^ 2) := by
    linear_combination hrel
  calc (p : ZMod (p ^ 3)) * H
      = ((2 : ZMod (p ^ 3))⁻¹ * 2) * ((p : ZMod (p ^ 3)) * H) := by rw [h2i, one_mul]
    _ = (2 : ZMod (p ^ 3))⁻¹ * (2 * ((p : ZMod (p ^ 3)) * H)) := by ring
    _ = (2 : ZMod (p ^ 3))⁻¹ * (2 * (-2 * (p : ZMod (p ^ 3)) * (q : ZMod (p ^ 3)) +
          (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3)) ^ 2)) := by rw [h2goal]
    _ = ((2 : ZMod (p ^ 3))⁻¹ * 2) * (-2 * (p : ZMod (p ^ 3)) * (q : ZMod (p ^ 3)) +
          (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3)) ^ 2) := by ring
    _ = _ := by rw [h2i, one_mul]

private lemma alt_harmonic_mod_p2 (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    let q : ℤ := ((2 ^ (p - 1) - 1) / p : ℕ)
    (p : ZMod (p ^ 3)) * (∑ k ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ k * (k : ZMod (p ^ 3))⁻¹) =
      -2 * (p : ZMod (p ^ 3)) * (q : ZMod (p ^ 3)) + (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3)) ^ 2 := by
  intro q
  have : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  have hp_odd : p % 2 = 1 := by rcases hp.eq_two_or_odd with rfl | h <;> omega
  set m := (p - 1) / 2
  have h2m : 2 * m = p - 1 := by omega
  -- ∑_{k=1}^{p-1} (-1)^k / k = 2 * ∑_{j=1}^m 1/(2j) - ∑_{k=1}^{p-1} 1/k = ∑_{j=1}^m 1/j - ∑_{k=1}^{p-1} 1/k
  have hsplit : ∑ k ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ k * (k : ZMod (p ^ 3))⁻¹ +
      ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 3))⁻¹ =
      ∑ j ∈ Finset.Icc 1 m, (j : ZMod (p ^ 3))⁻¹ := by
    rw [← Finset.sum_add_distrib]
    have hfilter : ∑ k ∈ Finset.Icc 1 (p - 1),
        ((-1 : ZMod (p ^ 3)) ^ k * (k : ZMod (p ^ 3))⁻¹ + (k : ZMod (p ^ 3))⁻¹) =
        ∑ k ∈ (Finset.Icc 1 (p - 1)).filter (fun k => k % 2 = 0),
          (2 * (k : ZMod (p ^ 3))⁻¹) := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (p - 1)) (fun k => k % 2 = 0)]
      have hodd0 : ∑ k ∈ (Finset.Icc 1 (p - 1)).filter (fun k => ¬ k % 2 = 0),
          ((-1 : ZMod (p ^ 3)) ^ k * (k : ZMod (p ^ 3))⁻¹ + (k : ZMod (p ^ 3))⁻¹) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_filter] at hk
        have h1 : (-1 : ZMod (p ^ 3)) ^ k = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))
        rw [h1]; ring
      rw [hodd0, add_zero]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_filter] at hk
      have h1 : (-1 : ZMod (p ^ 3)) ^ k = 1 := Even.neg_one_pow (Nat.even_iff.mpr hk.2)
      rw [h1]; ring
    rw [hfilter]
    apply Finset.sum_nbij' (fun k => k / 2) (fun j => 2 * j)
    · intro k hk; rw [Finset.mem_filter, Finset.mem_Icc] at hk; rw [Finset.mem_Icc]; omega
    · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_filter, Finset.mem_Icc]; omega
    · intro k hk; rw [Finset.mem_filter] at hk; omega
    · intro j _; omega
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      have hk2 : k = 2 * (k / 2) := by omega
      have h2i := zmod_two_mul_inv p 3 hp hp3
      have hki := zmod_mul_inv p 3 k hp hk.1.1 (by omega)
      have hji := zmod_mul_inv p 3 (k / 2) hp (by omega) (by omega)
      have hmul : (2 : ZMod (p ^ 3)) * ((k / 2 : ℕ) : ZMod (p ^ 3)) = (k : ZMod (p ^ 3)) := by
        simpa [Nat.cast_mul] using congrArg (Nat.cast (R := ZMod (p ^ 3))) hk2.symm
      calc 2 * (k : ZMod (p ^ 3))⁻¹
          = 2 * (k : ZMod (p ^ 3))⁻¹ * (((k / 2 : ℕ) : ZMod (p ^ 3)) * ((k / 2 : ℕ) : ZMod (p ^ 3))⁻¹) := by
              rw [hji, mul_one]
        _ = (2 * ((k / 2 : ℕ) : ZMod (p ^ 3))) * (k : ZMod (p ^ 3))⁻¹ * ((k / 2 : ℕ) : ZMod (p ^ 3))⁻¹ := by ring
        _ = ((k : ZMod (p ^ 3)) * (k : ZMod (p ^ 3))⁻¹) * ((k / 2 : ℕ) : ZMod (p ^ 3))⁻¹ := by rw [hmul]
        _ = ((k / 2 : ℕ) : ZMod (p ^ 3))⁻¹ := by rw [hki, one_mul]
  -- And p * ∑_{k=1}^{p-1} k⁻¹ = 0 in ZMod (p^3)
  set S1 : ZMod (p ^ 3) := ∑ k ∈ Finset.Icc 1 (p - 1), (k : ZMod (p ^ 3))⁻¹
  have hpS1 : (p : ZMod (p ^ 3)) * S1 = 0 := by
    have hp3z : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    have hcast : (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2))) S1 = 0 := by
      dsimp only [S1]; rw [map_sum]
      have heq : ∀ k ∈ Finset.Icc 1 (p - 1),
          (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2))) ((k : ZMod (p ^ 3))⁻¹) =
          (k : ZMod (p ^ 2))⁻¹ := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        have hki3 := zmod_mul_inv p 3 k hp hk.1 (by omega)
        have hki2 := zmod_inv_mul p 2 k hp hk.1 (by omega)
        have hmul : (k : ZMod (p ^ 2)) *
            (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2))) ((k : ZMod (p ^ 3))⁻¹) = 1 := by
          have := congrArg (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2))) hki3
          rw [map_mul, map_natCast, map_one] at this
          exact this
        calc (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2))) ((k : ZMod (p ^ 3))⁻¹)
            = ((k : ZMod (p ^ 2))⁻¹ * (k : ZMod (p ^ 2))) *
                (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2))) ((k : ZMod (p ^ 3))⁻¹) := by
              rw [hki2, one_mul]
          _ = (k : ZMod (p ^ 2))⁻¹ * ((k : ZMod (p ^ 2)) *
                (ZMod.castHom (pow_dvd_pow p (by norm_num : 2 ≤ 3)) (ZMod (p ^ 2))) ((k : ZMod (p ^ 3))⁻¹)) := by ring
          _ = (k : ZMod (p ^ 2))⁻¹ := by rw [hmul, mul_one]
      rw [Finset.sum_congr rfl heq]
      exact sum_inv_mod_p2 p hp hp3
    have hdvd : p ^ 2 ∣ S1.val := by
      have hS1c : (S1.val : ZMod (p ^ 2)) = 0 := by
        have := hcast; rw [← ZMod.natCast_zmod_val S1] at this; simpa using this
      exact (ZMod.natCast_eq_zero_iff S1.val (p ^ 2)).mp hS1c
    rcases hdvd with ⟨c, hc⟩
    rw [← ZMod.natCast_zmod_val S1, hc]; push_cast
    linear_combination (c : ZMod (p ^ 3)) * hp3z
  have hharm := harmonic_half_mod_p2 p hp hp3
  dsimp only at hharm
  calc (p : ZMod (p ^ 3)) * (∑ k ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ k * (k : ZMod (p ^ 3))⁻¹)
      = (p : ZMod (p ^ 3)) * (∑ k ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ k * (k : ZMod (p ^ 3))⁻¹ + S1) -
          (p : ZMod (p ^ 3)) * S1 := by ring
    _ = (p : ZMod (p ^ 3)) * (∑ j ∈ Finset.Icc 1 m, (j : ZMod (p ^ 3))⁻¹) := by rw [hsplit, hpS1, sub_zero]
    _ = _ := hharm

/-! ### Part 3: Delannoy numbers `D_{p-1}` and `D_p` modulo `p^3` -/

private lemma prod_p2_sub_sq (p j : ℕ) :
    (p : ZMod (p ^ 3)) * ∏ i ∈ Finset.Icc 1 (j - 1), ((p : ZMod (p ^ 3)) ^ 2 - (i : ZMod (p ^ 3)) ^ 2) =
      (p : ZMod (p ^ 3)) * (-1 : ZMod (p ^ 3)) ^ (j - 1) * (((j - 1).factorial : ZMod (p ^ 3)) ^ 2) := by
  have hp3z : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hgen : ∀ n : ℕ,
      (p : ZMod (p ^ 3)) * ∏ i ∈ Finset.Icc 1 n, ((p : ZMod (p ^ 3)) ^ 2 - (i : ZMod (p ^ 3)) ^ 2) =
        (p : ZMod (p ^ 3)) * (-1 : ZMod (p ^ 3)) ^ n * ((n.factorial : ZMod (p ^ 3)) ^ 2) := by
    intro n; induction n with
    | zero => simp
    | succ n ihn =>
      have hI : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hI, Finset.prod_insert (by simp)]
      calc (p : ZMod (p ^ 3)) * (((p : ZMod (p ^ 3)) ^ 2 - ((n + 1 : ℕ) : ZMod (p ^ 3)) ^ 2) *
              ∏ i ∈ Finset.Icc 1 n, ((p : ZMod (p ^ 3)) ^ 2 - (i : ZMod (p ^ 3)) ^ 2))
          = ((p : ZMod (p ^ 3)) ^ 2 - ((n + 1 : ℕ) : ZMod (p ^ 3)) ^ 2) *
              ((p : ZMod (p ^ 3)) * ∏ i ∈ Finset.Icc 1 n, ((p : ZMod (p ^ 3)) ^ 2 - (i : ZMod (p ^ 3)) ^ 2)) := by ring
        _ = ((p : ZMod (p ^ 3)) ^ 2 - ((n + 1 : ℕ) : ZMod (p ^ 3)) ^ 2) *
              ((p : ZMod (p ^ 3)) * (-1 : ZMod (p ^ 3)) ^ n * ((n.factorial : ZMod (p ^ 3)) ^ 2)) := by rw [ihn]
        _ = (p : ZMod (p ^ 3)) * (-1 : ZMod (p ^ 3)) ^ (n + 1) * (((n + 1).factorial : ZMod (p ^ 3)) ^ 2) := by
              rw [Nat.factorial_succ, pow_succ (-1 : ZMod (p ^ 3))]; push_cast
              linear_combination ((-1 : ZMod (p ^ 3)) ^ n * ((n.factorial : ZMod (p ^ 3)) ^ 2)) * hp3z
  exact hgen (j - 1)

private lemma delannoy_pred_mod_p3 (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    let q : ℤ := ((2 ^ (p - 1) - 1) / p : ℕ)
    (delannoy (p - 1) : ZMod (p ^ 3)) =
      1 - 2 * (p : ZMod (p ^ 3)) * (q : ZMod (p ^ 3)) + (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3)) ^ 2 := by
  intro q
  have : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  unfold delannoy
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, add_zero, mul_one]
  push_cast
  have hre : ∑ k ∈ Finset.range (p - 1),
      (((p - 1).choose (k + 1) : ZMod (p ^ 3)) * ((p - 1 + (k + 1)).choose (k + 1) : ZMod (p ^ 3))) =
      ∑ j ∈ Finset.Icc 1 (p - 1),
        (((p - 1).choose j : ZMod (p ^ 3)) * ((p - 1 + j).choose j : ZMod (p ^ 3))) := by
    apply Finset.sum_nbij' (fun k => k + 1) (fun j => j - 1)
    · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega
    · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_range]; omega
    · intro k _; omega
    · intro j hj; rw [Finset.mem_Icc] at hj; omega
    · intro k _; rfl
  rw [hre]
  have hterm : ∀ j ∈ Finset.Icc 1 (p - 1),
      ((p - 1).choose j : ZMod (p ^ 3)) * ((p - 1 + j).choose j : ZMod (p ^ 3)) =
      (-1 : ZMod (p ^ 3)) ^ j * (p : ZMod (p ^ 3)) * (j : ZMod (p ^ 3))⁻¹ -
      (-1 : ZMod (p ^ 3)) ^ j * (p : ZMod (p ^ 3)) ^ 2 * ((j : ZMod (p ^ 3)) ^ 2)⁻¹ := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hd1 : (p - 1).choose j * j.factorial = ∏ i ∈ Finset.range j, (p - 1 - i) := by
      have := Nat.descFactorial_eq_factorial_mul_choose (p - 1) j
      rw [mul_comm] at this; rw [← this, Nat.descFactorial_eq_prod_range]
    have hd2 : (p - 1 + j).choose j * j.factorial = ∏ i ∈ Finset.range j, (p - 1 + j - i) := by
      have := Nat.descFactorial_eq_factorial_mul_choose (p - 1 + j) j
      rw [mul_comm] at this; rw [← this, Nat.descFactorial_eq_prod_range]
    have hprod1 : ∏ i ∈ Finset.range j, ((p - 1 - i : ℕ) : ZMod (p ^ 3)) =
        ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3))) *
          ∏ i ∈ Finset.Icc 1 (j - 1), ((p : ZMod (p ^ 3)) - (i : ZMod (p ^ 3))) := by
      rw [show j = (j - 1) + 1 by omega, Finset.prod_range_succ, mul_comm]
      congr 1
      · rw [show p - 1 - (j - 1) = p - j by omega, Nat.cast_sub (by omega), show j - 1 + 1 = j by omega]
      · apply Finset.prod_nbij' (fun i => i + 1) (fun i => i - 1)
        · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_Icc]; omega
        · intro i hi; rw [Finset.mem_Icc] at hi; rw [Finset.mem_range]; omega
        · intro i _; omega
        · intro i hi; rw [Finset.mem_Icc] at hi; omega
        · intro i hi
          rw [Finset.mem_range] at hi
          rw [show p - 1 - i = p - (i + 1) by omega, Nat.cast_sub (by omega)]
    have hprod2 : ∏ i ∈ Finset.range j, ((p - 1 + j - i : ℕ) : ZMod (p ^ 3)) =
        (p : ZMod (p ^ 3)) * ∏ i ∈ Finset.Icc 1 (j - 1), ((p : ZMod (p ^ 3)) + (i : ZMod (p ^ 3))) := by
      rw [show j = (j - 1) + 1 by omega, Finset.prod_range_succ, mul_comm]
      congr 1
      · rw [show p - 1 + (j - 1 + 1) - (j - 1) = p by omega]
      · apply Finset.prod_nbij' (fun i => j - 1 - i) (fun i => j - 1 - i)
        · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_Icc]; omega
        · intro i hi; rw [Finset.mem_Icc] at hi; rw [Finset.mem_range]; omega
        · intro i hi; rw [Finset.mem_range] at hi; omega
        · intro i hi; rw [Finset.mem_Icc] at hi; omega
        · intro i hi
          rw [Finset.mem_range] at hi
          rw [show p - 1 + (j - 1 + 1) - i = p + (j - 1 - i) by omega]; push_cast; rfl
    have hmul : ((p - 1).choose j : ZMod (p ^ 3)) * ((p - 1 + j).choose j : ZMod (p ^ 3)) *
        ((j.factorial : ZMod (p ^ 3)) ^ 2) =
        ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3))) *
          ((p : ZMod (p ^ 3)) * (-1 : ZMod (p ^ 3)) ^ (j - 1) * (((j - 1).factorial : ZMod (p ^ 3)) ^ 2)) := by
      have hd1z : ((p - 1).choose j : ZMod (p ^ 3)) * (j.factorial : ZMod (p ^ 3)) =
          ∏ i ∈ Finset.range j, ((p - 1 - i : ℕ) : ZMod (p ^ 3)) := by
        simpa [Nat.cast_mul, Nat.cast_prod] using congrArg (Nat.cast (R := ZMod (p ^ 3))) hd1
      have hd2z : ((p - 1 + j).choose j : ZMod (p ^ 3)) * (j.factorial : ZMod (p ^ 3)) =
          ∏ i ∈ Finset.range j, ((p - 1 + j - i : ℕ) : ZMod (p ^ 3)) := by
        simpa [Nat.cast_mul, Nat.cast_prod] using congrArg (Nat.cast (R := ZMod (p ^ 3))) hd2
      calc ((p - 1).choose j : ZMod (p ^ 3)) * ((p - 1 + j).choose j : ZMod (p ^ 3)) *
            ((j.factorial : ZMod (p ^ 3)) ^ 2)
          = (((p - 1).choose j : ZMod (p ^ 3)) * (j.factorial : ZMod (p ^ 3))) *
            (((p - 1 + j).choose j : ZMod (p ^ 3)) * (j.factorial : ZMod (p ^ 3))) := by ring
        _ = ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3))) *
            ((p : ZMod (p ^ 3)) * ((∏ i ∈ Finset.Icc 1 (j - 1), ((p : ZMod (p ^ 3)) - (i : ZMod (p ^ 3)))) *
              (∏ i ∈ Finset.Icc 1 (j - 1), ((p : ZMod (p ^ 3)) + (i : ZMod (p ^ 3)))))) := by
            rw [hd1z, hd2z, hprod1, hprod2]; ring
        _ = ((p : ZMod (p ^ 3)) - (j : ZMod (p ^ 3))) *
            ((p : ZMod (p ^ 3)) * ∏ i ∈ Finset.Icc 1 (j - 1), ((p : ZMod (p ^ 3)) ^ 2 - (i : ZMod (p ^ 3)) ^ 2)) := by
            rw [← Finset.prod_mul_distrib]
            congr 2; apply Finset.prod_congr rfl; intro i _; ring
        _ = _ := by rw [prod_p2_sub_sq p j]
    have hunit : IsUnit ((j.factorial : ZMod (p ^ 3)) ^ 2) := by
      apply IsUnit.pow
      apply (ZMod.isUnit_iff_coprime _ _).mpr
      have hnd : ¬ p ∣ j.factorial := fun hd => by have := hp.dvd_factorial.mp hd; omega
      exact ((hp.coprime_iff_not_dvd.mpr hnd).symm).pow_right 3
    have hji := zmod_mul_inv p 3 j hp hj.1 (by omega)
    have hjsqi : (j : ZMod (p ^ 3)) ^ 2 * ((j : ZMod (p ^ 3)) ^ 2)⁻¹ = 1 := by
      have hcop : Nat.Coprime j (p ^ 3) :=
        ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hj.1 (by omega))).symm).pow_right 3
      exact ZMod.mul_inv_of_unit _ (((ZMod.isUnit_iff_coprime j (p ^ 3)).mpr hcop).pow 2)
    have hfacj : (j.factorial : ZMod (p ^ 3)) = (j : ZMod (p ^ 3)) * ((j - 1).factorial : ZMod (p ^ 3)) := by
      have : j.factorial = j * (j - 1).factorial := by
        conv_lhs => rw [show j = (j - 1) + 1 by omega, Nat.factorial_succ, show j - 1 + 1 = j by omega]
      simpa [Nat.cast_mul] using congrArg (Nat.cast (R := ZMod (p ^ 3))) this
    have hsign : (-1 : ZMod (p ^ 3)) ^ j = -((-1 : ZMod (p ^ 3)) ^ (j - 1)) := by
      conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]; ring
    apply hunit.mul_right_cancel
    rw [hmul, hfacj, mul_pow, hsign]
    linear_combination
      ((-1 : ZMod (p ^ 3)) ^ (j - 1) * (p : ZMod (p ^ 3)) * (j : ZMod (p ^ 3)) *
        ((j - 1).factorial : ZMod (p ^ 3)) ^ 2) * hji -
      ((-1 : ZMod (p ^ 3)) ^ (j - 1) * (p : ZMod (p ^ 3)) ^ 2 *
        ((j - 1).factorial : ZMod (p ^ 3)) ^ 2) * hjsqi
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  have h1 : ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ j * (p : ZMod (p ^ 3)) * (j : ZMod (p ^ 3))⁻¹ =
      (p : ZMod (p ^ 3)) * ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ j * (j : ZMod (p ^ 3))⁻¹ := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have h2 : ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ j * (p : ZMod (p ^ 3)) ^ 2 * ((j : ZMod (p ^ 3)) ^ 2)⁻¹ = 0 := by
    have hfac : ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ j * (p : ZMod (p ^ 3)) ^ 2 * ((j : ZMod (p ^ 3)) ^ 2)⁻¹ =
        (p : ZMod (p ^ 3)) ^ 2 * ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ j * ((j : ZMod (p ^ 3)) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    rw [hfac]
    set T := ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ j * ((j : ZMod (p ^ 3)) ^ 2)⁻¹
    have hT0 : (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) T = 0 := by
      dsimp only [T]; rw [map_sum]
      have heq : ∀ j ∈ Finset.Icc 1 (p - 1),
          (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p))
            ((-1 : ZMod (p ^ 3)) ^ j * ((j : ZMod (p ^ 3)) ^ 2)⁻¹) =
          (-1 : ZMod p) ^ j * ((j : ZMod p) ^ 2)⁻¹ := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        rw [map_mul, map_pow, map_neg, map_one]
        congr 1
        have hcop : Nat.Coprime j (p ^ 3) :=
          ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hj.1 (by omega))).symm).pow_right 3
        have hu2 : IsUnit ((j : ZMod (p ^ 3)) ^ 2) := ((ZMod.isUnit_iff_coprime j (p ^ 3)).mpr hcop).pow 2
        have hmul : (j : ZMod p) ^ 2 *
            (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) (((j : ZMod (p ^ 3)) ^ 2)⁻¹) = 1 := by
          have := congrArg (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) (ZMod.mul_inv_of_unit _ hu2)
          simpa using this
        have : Fact p.Prime := ⟨hp⟩
        have hjn : (j : ZMod p) ≠ 0 := by
          intro h0; have := (ZMod.natCast_eq_zero_iff j p).mp h0; have := Nat.le_of_dvd hj.1 this; omega
        calc _ = ((j : ZMod p) ^ 2)⁻¹ * ((j : ZMod p) ^ 2 * _) := by field_simp [hjn]
          _ = ((j : ZMod p) ^ 2)⁻¹ := by rw [hmul, mul_one]
      rw [Finset.sum_congr rfl heq]
      exact sum_alt_inv_sq_mod_p p hp hp3
    have hdvd : p ∣ T.val := by
      have hTc : (T.val : ZMod p) = 0 := by
        have := hT0; rw [← ZMod.natCast_zmod_val T] at this; simpa using this
      exact (ZMod.natCast_eq_zero_iff T.val p).mp hTc
    rcases hdvd with ⟨c, hc⟩
    rw [← ZMod.natCast_zmod_val T, hc]; push_cast
    have hp3z : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    linear_combination (c : ZMod (p ^ 3)) * hp3z
  rw [h1, h2, sub_zero, alt_harmonic_mod_p2 p hp hp3]
  ring

private lemma delannoy_prime_mod_p3 (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    let q : ℤ := ((2 ^ (p - 1) - 1) / p : ℕ)
    (delannoy p : ZMod (p ^ 3)) =
      3 + 2 * (p : ZMod (p ^ 3)) * (q : ZMod (p ^ 3)) - (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3)) ^ 2 := by
  intro q
  have : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  unfold delannoy
  rw [Finset.sum_range_succ]
  rw [show p = (p - 1) + 1 by omega, Finset.sum_range_succ', show p - 1 + 1 = p by omega]
  simp only [Nat.choose_self, Nat.choose_zero_right, one_mul, add_zero, mul_one]
  push_cast
  rw [show p + p = 2 * p by omega, choose_two_p_mod_p3 p hp hp3]
  -- Reindex middle sum over range (p - 1) to Icc 1 (p - 1)
  have hre : ∑ k ∈ Finset.range (p - 1),
      ((p.choose (k + 1) : ZMod (p ^ 3)) * ((p + (k + 1)).choose (k + 1) : ZMod (p ^ 3))) =
      ∑ j ∈ Finset.Icc 1 (p - 1),
        ((p.choose j : ZMod (p ^ 3)) * ((p + j).choose j : ZMod (p ^ 3))) := by
    apply Finset.sum_nbij' (fun k => k + 1) (fun j => j - 1)
    · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]; omega
    · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_range]; omega
    · intro k _; omega
    · intro j hj; rw [Finset.mem_Icc] at hj; omega
    · intro k _; rfl
  have hterm : ∀ j ∈ Finset.Icc 1 (p - 1),
      (p.choose j : ZMod (p ^ 3)) * ((p + j).choose j : ZMod (p ^ 3)) =
      -((-1 : ZMod (p ^ 3)) ^ j * (p : ZMod (p ^ 3)) * (j : ZMod (p ^ 3))⁻¹) -
      (-1 : ZMod (p ^ 3)) ^ j * (p : ZMod (p ^ 3)) ^ 2 * ((j : ZMod (p ^ 3)) ^ 2)⁻¹ := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hd1 : p.choose j * j.factorial = ∏ i ∈ Finset.range j, (p - i) := by
      have := Nat.descFactorial_eq_factorial_mul_choose p j
      rw [mul_comm] at this; rw [← this, Nat.descFactorial_eq_prod_range]
    have hd2 : (p + j).choose j * j.factorial = ∏ i ∈ Finset.range j, (p + j - i) := by
      have := Nat.descFactorial_eq_factorial_mul_choose (p + j) j
      rw [mul_comm] at this; rw [← this, Nat.descFactorial_eq_prod_range]
    have hprod1 : ∏ i ∈ Finset.range j, ((p - i : ℕ) : ZMod (p ^ 3)) =
        (p : ZMod (p ^ 3)) * ∏ i ∈ Finset.Icc 1 (j - 1), ((p : ZMod (p ^ 3)) - (i : ZMod (p ^ 3))) := by
      rw [show j = (j - 1) + 1 by omega, Finset.prod_range_succ', Nat.sub_zero, mul_comm]
      congr 1
      apply Finset.prod_nbij' (fun i => i + 1) (fun i => i - 1)
      · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_Icc]; omega
      · intro i hi; rw [Finset.mem_Icc] at hi; rw [Finset.mem_range]; omega
      · intro i _; omega
      · intro i hi; rw [Finset.mem_Icc] at hi; omega
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [Nat.cast_sub (by omega : i + 1 ≤ p)]
    have hprod2 : ∏ i ∈ Finset.range j, ((p + j - i : ℕ) : ZMod (p ^ 3)) =
        ((p : ZMod (p ^ 3)) + (j : ZMod (p ^ 3))) *
          ∏ i ∈ Finset.Icc 1 (j - 1), ((p : ZMod (p ^ 3)) + (i : ZMod (p ^ 3))) := by
      rw [show j = (j - 1) + 1 by omega, Finset.prod_range_succ', mul_comm]
      congr 1
      · simp [show j - 1 + 1 = j by omega]
      · apply Finset.prod_nbij' (fun i => j - 1 - i) (fun i => j - 1 - i)
        · intro i hi; rw [Finset.mem_range] at hi; rw [Finset.mem_Icc]; omega
        · intro i hi; rw [Finset.mem_Icc] at hi; rw [Finset.mem_range]; omega
        · intro i hi; rw [Finset.mem_range] at hi; omega
        · intro i hi; rw [Finset.mem_Icc] at hi; omega
        · intro i hi
          rw [Finset.mem_range] at hi
          rw [show p + (j - 1 + 1) - (i + 1) = p + (j - 1 - i) by omega]; push_cast; rfl
    have hmul : (p.choose j : ZMod (p ^ 3)) * ((p + j).choose j : ZMod (p ^ 3)) *
        ((j.factorial : ZMod (p ^ 3)) ^ 2) =
        ((p : ZMod (p ^ 3)) + (j : ZMod (p ^ 3))) *
          ((p : ZMod (p ^ 3)) * (-1 : ZMod (p ^ 3)) ^ (j - 1) * (((j - 1).factorial : ZMod (p ^ 3)) ^ 2)) := by
      have hd1z : (p.choose j : ZMod (p ^ 3)) * (j.factorial : ZMod (p ^ 3)) =
          ∏ i ∈ Finset.range j, ((p - i : ℕ) : ZMod (p ^ 3)) := by
        simpa [Nat.cast_mul, Nat.cast_prod] using congrArg (Nat.cast (R := ZMod (p ^ 3))) hd1
      have hd2z : ((p + j).choose j : ZMod (p ^ 3)) * (j.factorial : ZMod (p ^ 3)) =
          ∏ i ∈ Finset.range j, ((p + j - i : ℕ) : ZMod (p ^ 3)) := by
        simpa [Nat.cast_mul, Nat.cast_prod] using congrArg (Nat.cast (R := ZMod (p ^ 3))) hd2
      calc (p.choose j : ZMod (p ^ 3)) * ((p + j).choose j : ZMod (p ^ 3)) *
            ((j.factorial : ZMod (p ^ 3)) ^ 2)
          = ((p.choose j : ZMod (p ^ 3)) * (j.factorial : ZMod (p ^ 3))) *
            (((p + j).choose j : ZMod (p ^ 3)) * (j.factorial : ZMod (p ^ 3))) := by ring
        _ = ((p : ZMod (p ^ 3)) + (j : ZMod (p ^ 3))) *
            ((p : ZMod (p ^ 3)) * ((∏ i ∈ Finset.Icc 1 (j - 1), ((p : ZMod (p ^ 3)) - (i : ZMod (p ^ 3)))) *
              (∏ i ∈ Finset.Icc 1 (j - 1), ((p : ZMod (p ^ 3)) + (i : ZMod (p ^ 3)))))) := by
            rw [hd1z, hd2z, hprod1, hprod2]; ring
        _ = ((p : ZMod (p ^ 3)) + (j : ZMod (p ^ 3))) *
            ((p : ZMod (p ^ 3)) * ∏ i ∈ Finset.Icc 1 (j - 1), ((p : ZMod (p ^ 3)) ^ 2 - (i : ZMod (p ^ 3)) ^ 2)) := by
            rw [← Finset.prod_mul_distrib]
            congr 2; apply Finset.prod_congr rfl; intro i _; ring
        _ = _ := by rw [prod_p2_sub_sq p j]
    have hunit : IsUnit ((j.factorial : ZMod (p ^ 3)) ^ 2) := by
      apply IsUnit.pow
      apply (ZMod.isUnit_iff_coprime _ _).mpr
      have hnd : ¬ p ∣ j.factorial := fun hd => by have := hp.dvd_factorial.mp hd; omega
      exact ((hp.coprime_iff_not_dvd.mpr hnd).symm).pow_right 3
    have hji := zmod_mul_inv p 3 j hp hj.1 (by omega)
    have hjsqi : (j : ZMod (p ^ 3)) ^ 2 * ((j : ZMod (p ^ 3)) ^ 2)⁻¹ = 1 := by
      have hcop : Nat.Coprime j (p ^ 3) :=
        ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hj.1 (by omega))).symm).pow_right 3
      exact ZMod.mul_inv_of_unit _ (((ZMod.isUnit_iff_coprime j (p ^ 3)).mpr hcop).pow 2)
    have hfacj : (j.factorial : ZMod (p ^ 3)) = (j : ZMod (p ^ 3)) * ((j - 1).factorial : ZMod (p ^ 3)) := by
      have : j.factorial = j * (j - 1).factorial := by
        conv_lhs => rw [show j = (j - 1) + 1 by omega, Nat.factorial_succ, show j - 1 + 1 = j by omega]
      simpa [Nat.cast_mul] using congrArg (Nat.cast (R := ZMod (p ^ 3))) this
    have hsign : (-1 : ZMod (p ^ 3)) ^ j = -((-1 : ZMod (p ^ 3)) ^ (j - 1)) := by
      conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]; ring
    apply hunit.mul_right_cancel
    rw [hmul, hfacj, mul_pow, hsign]
    linear_combination
      (-(-1 : ZMod (p ^ 3)) ^ (j - 1) * (p : ZMod (p ^ 3)) * (j : ZMod (p ^ 3)) *
        ((j - 1).factorial : ZMod (p ^ 3)) ^ 2) * hji -
      ((-1 : ZMod (p ^ 3)) ^ (j - 1) * (p : ZMod (p ^ 3)) ^ 2 *
        ((j - 1).factorial : ZMod (p ^ 3)) ^ 2) * hjsqi
  have hmid : ∑ j ∈ Finset.Icc 1 (p - 1),
      ((p.choose j : ZMod (p ^ 3)) * ((p + j).choose j : ZMod (p ^ 3))) =
      2 * (p : ZMod (p ^ 3)) * (q : ZMod (p ^ 3)) - (p : ZMod (p ^ 3)) ^ 2 * (q : ZMod (p ^ 3)) ^ 2 := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    have h1 : ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ j * (p : ZMod (p ^ 3)) * (j : ZMod (p ^ 3))⁻¹ =
        (p : ZMod (p ^ 3)) * ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ j * (j : ZMod (p ^ 3))⁻¹ := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    have h2 : ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ j * (p : ZMod (p ^ 3)) ^ 2 * ((j : ZMod (p ^ 3)) ^ 2)⁻¹ = 0 := by
      have hfac : ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ j * (p : ZMod (p ^ 3)) ^ 2 * ((j : ZMod (p ^ 3)) ^ 2)⁻¹ =
          (p : ZMod (p ^ 3)) ^ 2 * ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ j * ((j : ZMod (p ^ 3)) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      rw [hfac]
      set T := ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod (p ^ 3)) ^ j * ((j : ZMod (p ^ 3)) ^ 2)⁻¹
      have hT0 : (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) T = 0 := by
        dsimp only [T]; rw [map_sum]
        have heq : ∀ j ∈ Finset.Icc 1 (p - 1),
            (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p))
              ((-1 : ZMod (p ^ 3)) ^ j * ((j : ZMod (p ^ 3)) ^ 2)⁻¹) =
            (-1 : ZMod p) ^ j * ((j : ZMod p) ^ 2)⁻¹ := by
          intro j hj
          rw [Finset.mem_Icc] at hj
          rw [map_mul, map_pow, map_neg, map_one]
          congr 1
          have hcop : Nat.Coprime j (p ^ 3) :=
            ((hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hj.1 (by omega))).symm).pow_right 3
          have hu2 : IsUnit ((j : ZMod (p ^ 3)) ^ 2) := ((ZMod.isUnit_iff_coprime j (p ^ 3)).mpr hcop).pow 2
          have hmul : (j : ZMod p) ^ 2 *
              (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) (((j : ZMod (p ^ 3)) ^ 2)⁻¹) = 1 := by
            have := congrArg (ZMod.castHom (dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)) (ZMod.mul_inv_of_unit _ hu2)
            simpa using this
          have : Fact p.Prime := ⟨hp⟩
          have hjn : (j : ZMod p) ≠ 0 := by
            intro h0; have := (ZMod.natCast_eq_zero_iff j p).mp h0; have := Nat.le_of_dvd hj.1 this; omega
          calc _ = ((j : ZMod p) ^ 2)⁻¹ * ((j : ZMod p) ^ 2 * _) := by field_simp [hjn]
            _ = ((j : ZMod p) ^ 2)⁻¹ := by rw [hmul, mul_one]
        rw [Finset.sum_congr rfl heq]
        exact sum_alt_inv_sq_mod_p p hp hp3
      have hdvd : p ∣ T.val := by
        have hTc : (T.val : ZMod p) = 0 := by
          have := hT0; rw [← ZMod.natCast_zmod_val T] at this; simpa using this
        exact (ZMod.natCast_eq_zero_iff T.val p).mp hTc
      rcases hdvd with ⟨c, hc⟩
      rw [← ZMod.natCast_zmod_val T, hc]; push_cast
      have hp3z : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
      linear_combination (c : ZMod (p ^ 3)) * hp3z
    rw [h1, h2, sub_zero, alt_harmonic_mod_p2 p hp hp3]
    ring
  rw [hre, hmid]; ring

private lemma part2 (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    let q : ℤ := ((2 ^ (p - 1) - 1) / p : ℕ)
    (p : ℤ) ^ 5 ∣ (S p : ℤ) - ((p : ℤ) ^ 2 - 4 * (p : ℤ) ^ 3 * q - 2 * (p : ℤ) ^ 4 * q ^ 2) := by
  intro q
  have h8 := eight_mul_S p (by omega)
  have hD1 := delannoy_pred_mod_p3 p hp hp3
  have hD2 := delannoy_prime_mod_p3 p hp hp3
  dsimp only at hD1 hD2
  have hquad : ((6 * (delannoy p : ℤ) * (delannoy (p - 1) : ℤ) -
      (delannoy p : ℤ) ^ 2 - (delannoy (p - 1) : ℤ) ^ 2 -
      8 * (1 - 4 * (p : ℤ) * q - 2 * (p : ℤ) ^ 2 * q ^ 2) : ℤ) : ZMod (p ^ 3)) = 0 := by
    push_cast
    rw [hD1, hD2]
    have hp3z : (p : ZMod (p ^ 3)) ^ 3 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
    linear_combination
      (32 * (q : ZMod (p ^ 3)) ^ 3 - 8 * (p : ZMod (p ^ 3)) * (q : ZMod (p ^ 3)) ^ 4) * hp3z
  have hdvd3 : ((p ^ 3 : ℕ) : ℤ) ∣ 6 * (delannoy p : ℤ) * (delannoy (p - 1) : ℤ) -
      (delannoy p : ℤ) ^ 2 - (delannoy (p - 1) : ℤ) ^ 2 -
      8 * (1 - 4 * (p : ℤ) * q - 2 * (p : ℤ) ^ 2 * q ^ 2) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hquad
  rcases hdvd3 with ⟨k, hk⟩
  push_cast at hk
  have h8diff : 8 * ((S p : ℤ) - ((p : ℤ) ^ 2 - 4 * (p : ℤ) ^ 3 * q - 2 * (p : ℤ) ^ 4 * q ^ 2)) =
      (p : ℤ) ^ 5 * k := by
    linear_combination h8 + (p : ℤ) ^ 2 * hk
  have hcop : IsCoprime ((p : ℤ) ^ 5) 8 := by
    have hp2 : ¬ (2 : ℤ) ∣ (p : ℤ) := by
      have hodd : p % 2 = 1 := by rcases hp.eq_two_or_odd with rfl | h <;> omega
      omega
    have hc2 : IsCoprime (2 : ℤ) (p : ℤ) :=
      (Int.prime_iff_natAbs_prime.mpr (by decide)).coprime_iff_not_dvd.mpr hp2
    have h8eq : (8 : ℤ) = 2 ^ 3 := by norm_num
    rw [h8eq]
    exact (hc2.symm.pow_left).pow_right
  apply hcop.dvd_of_dvd_mul_left
  exact ⟨k, h8diff⟩

end OMA_a178808_proof

open OMA_a178808_proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a178808.main :=
  ⟨part1, part2⟩
