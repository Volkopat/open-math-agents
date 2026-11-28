import OMAStatements.S_oeis_a357559

-- Problem: A357559: a(n) = Sum_{k = 0..n} (-1)^(n+k)*k^3*binomial(n,k)*binomial(n+k,k)^2.
-- Upstream: formal-conjectures statements/oeis-a357559.lean:0 (declaration OMA.S_oeis_a357559.main)
-- Credit: @mjsechrest2

open OMA.S_oeis_a357559

namespace OMA_a357559_proof

private def F (n k : ℕ) : ℚ :=
  (-1 : ℚ) ^ (n + k) * (n.choose k : ℚ) * ((n + k).choose k : ℚ) ^ 2

private def H (n k : ℕ) : ℚ :=
  (-1 : ℚ) ^ (n + k) * ((n + 1).choose k : ℚ) * ((n + k).choose k : ℚ) ^ 2

private def A (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + k) * (n.choose k * ((n + k).choose k) ^ 2 : ℕ)

private def a1 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + k) * (k * n.choose k * ((n + k).choose k) ^ 2 : ℕ)

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

private lemma F_eq_H (n k : ℕ) (hk : k ≤ n + 1) :
    F n k = (((n : ℚ) + 1 - k) / ((n : ℚ) + 1)) * H n k := by
  unfold F H
  have h1 : ((n + 1 - k : ℕ) : ℚ) * ((n + 1).choose k : ℚ) = ((n + 1 : ℕ) : ℚ) * (n.choose k : ℚ) := by
    exact_mod_cast choose_sub_mul n k
  have hsub : ((n + 1 - k : ℕ) : ℚ) = (n : ℚ) + 1 - k := by
    rw [Nat.cast_sub hk]; push_cast; ring
  have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [hsub] at h1
  push_cast at h1
  rw [div_mul_eq_mul_div, eq_div_iff hpos]
  calc (-1 : ℚ) ^ (n + k) * (n.choose k : ℚ) * ((n + k).choose k : ℚ) ^ 2 * ((n : ℚ) + 1)
      = (-1 : ℚ) ^ (n + k) * ((n + k).choose k : ℚ) ^ 2 * (((n : ℚ) + 1) * (n.choose k : ℚ)) := by ring
    _ = (-1 : ℚ) ^ (n + k) * ((n + k).choose k : ℚ) ^ 2 * (((n : ℚ) + 1 - k) * ((n + 1).choose k : ℚ)) := by rw [← h1]
    _ = _ := by ring

private lemma F_succ_eq_H (n k : ℕ) :
    F (n + 1) k = -(((n : ℚ) + 1 + k) ^ 2 / ((n : ℚ) + 1) ^ 2) * H n k := by
  unfold F H
  have h1 : ((n + 1 : ℕ) : ℚ) * ((n + 1 + k).choose k : ℚ) = ((n + 1 + k : ℕ) : ℚ) * ((n + k).choose k : ℚ) := by
    exact_mod_cast choose_add_sub_mul n k
  push_cast at h1
  have hpos : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hsign : (-1 : ℚ) ^ (n + 1 + k) = -((-1 : ℚ) ^ (n + k)) := by
    rw [show n + 1 + k = (n + k) + 1 by omega, pow_succ]; ring
  rw [hsign]
  have hsq : ((n : ℚ) + 1) ^ 2 * ((n + 1 + k).choose k : ℚ) ^ 2 =
      ((n : ℚ) + 1 + k) ^ 2 * ((n + k).choose k : ℚ) ^ 2 := by
    calc ((n : ℚ) + 1) ^ 2 * ((n + 1 + k).choose k : ℚ) ^ 2
        = (((n : ℚ) + 1) * ((n + 1 + k).choose k : ℚ)) ^ 2 := by ring
      _ = (((n : ℚ) + 1 + k) * ((n + k).choose k : ℚ)) ^ 2 := by rw [h1]
      _ = ((n : ℚ) + 1 + k) ^ 2 * ((n + k).choose k : ℚ) ^ 2 := by ring
  rw [← neg_div, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hpos)]
  calc -((-1 : ℚ) ^ (n + k)) * ((n + 1).choose k : ℚ) * ((n + 1 + k).choose k : ℚ) ^ 2 * ((n : ℚ) + 1) ^ 2
      = -((-1 : ℚ) ^ (n + k)) * ((n + 1).choose k : ℚ) * (((n : ℚ) + 1) ^ 2 * ((n + 1 + k).choose k : ℚ) ^ 2) := by ring
    _ = -((-1 : ℚ) ^ (n + k)) * ((n + 1).choose k : ℚ) * (((n : ℚ) + 1 + k) ^ 2 * ((n + k).choose k : ℚ) ^ 2) := by rw [hsq]
    _ = _ := by ring

private lemma F_pred_eq_H (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n + 1) :
    F (n - 1) k = -((n : ℚ) * ((n : ℚ) - k) * ((n : ℚ) + 1 - k) / (((n : ℚ) + 1) * ((n : ℚ) + k) ^ 2)) * H n k := by
  unfold F H
  have hpos1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hpos2 : ((n : ℚ) + k) ≠ 0 := by
    have : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
    linarith
  rcases lt_or_ge n k with hlt | hle
  · have hkn : k = n + 1 := by omega
    subst hkn
    have hch : (n - 1).choose (n + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hch]
    push_cast
    ring
  · rcases eq_or_lt_of_le hle with rfl | hlt
    · have hch : (k - 1).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hch]
      push_cast
      ring
    · have hsign : (-1 : ℚ) ^ (n - 1 + k) = -((-1 : ℚ) ^ (n + k)) := by
        have : n + k = (n - 1 + k) + 1 := by omega
        rw [this, pow_succ]; ring
      rw [hsign]
      have hch1 : ((n - k : ℕ) : ℚ) * (n.choose k : ℚ) = (n : ℚ) * ((n - 1).choose k : ℚ) := by
        have h := choose_sub_mul (n - 1) k
        have h1 : n - 1 + 1 = n := by omega
        rw [h1] at h
        exact_mod_cast h
      have hch2 : ((n + 1 - k : ℕ) : ℚ) * ((n + 1).choose k : ℚ) = ((n + 1 : ℕ) : ℚ) * (n.choose k : ℚ) := by
        exact_mod_cast choose_sub_mul n k
      have hch3 : (n : ℚ) * ((n + k).choose k : ℚ) = ((n + k : ℕ) : ℚ) * ((n - 1 + k).choose k : ℚ) := by
        have h := choose_add_sub_mul (n - 1) k
        have h1 : n - 1 + 1 = n := by omega
        rw [h1] at h
        exact_mod_cast h
      rw [Nat.cast_sub (by omega : k ≤ n)] at hch1
      rw [Nat.cast_sub hk] at hch2
      push_cast at hch2 hch3
      have hcomb : ((n : ℚ) - k) * ((n : ℚ) + 1 - k) * ((n + 1).choose k : ℚ) =
          (n : ℚ) * ((n : ℚ) + 1) * ((n - 1).choose k : ℚ) := by
        calc ((n : ℚ) - k) * ((n : ℚ) + 1 - k) * ((n + 1).choose k : ℚ)
            = ((n : ℚ) - k) * (((n : ℚ) + 1 - k) * ((n + 1).choose k : ℚ)) := by ring
          _ = ((n : ℚ) - k) * (((n : ℚ) + 1) * (n.choose k : ℚ)) := by rw [hch2]
          _ = ((n : ℚ) + 1) * (((n : ℚ) - k) * (n.choose k : ℚ)) := by ring
          _ = ((n : ℚ) + 1) * ((n : ℚ) * ((n - 1).choose k : ℚ)) := by rw [hch1]
          _ = (n : ℚ) * ((n : ℚ) + 1) * ((n - 1).choose k : ℚ) := by ring
      have hsq : (n : ℚ) ^ 2 * ((n + k).choose k : ℚ) ^ 2 =
          ((n : ℚ) + k) ^ 2 * ((n - 1 + k).choose k : ℚ) ^ 2 := by
        calc (n : ℚ) ^ 2 * ((n + k).choose k : ℚ) ^ 2
            = ((n : ℚ) * ((n + k).choose k : ℚ)) ^ 2 := by ring
          _ = (((n : ℚ) + k) * ((n - 1 + k).choose k : ℚ)) ^ 2 := by rw [hch3]
          _ = ((n : ℚ) + k) ^ 2 * ((n - 1 + k).choose k : ℚ) ^ 2 := by ring
      have hn0 : (n : ℚ) ≠ 0 := by
        have : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
        linarith
      have hkey : ((n : ℚ) + 1) * ((n : ℚ) + k) ^ 2 * (n : ℚ) *
          (((n - 1).choose k : ℚ) * ((n - 1 + k).choose k : ℚ) ^ 2) =
          (n : ℚ) ^ 2 * ((n : ℚ) - k) * ((n : ℚ) + 1 - k) *
          (((n + 1).choose k : ℚ) * ((n + k).choose k : ℚ) ^ 2) := by
        calc ((n : ℚ) + 1) * ((n : ℚ) + k) ^ 2 * (n : ℚ) *
              (((n - 1).choose k : ℚ) * ((n - 1 + k).choose k : ℚ) ^ 2)
            = ((n : ℚ) * ((n : ℚ) + 1) * ((n - 1).choose k : ℚ)) *
              (((n : ℚ) + k) ^ 2 * ((n - 1 + k).choose k : ℚ) ^ 2) := by ring
          _ = (((n : ℚ) - k) * ((n : ℚ) + 1 - k) * ((n + 1).choose k : ℚ)) *
              ((n : ℚ) ^ 2 * ((n + k).choose k : ℚ) ^ 2) := by rw [← hcomb, ← hsq]
          _ = (n : ℚ) ^ 2 * ((n : ℚ) - k) * ((n : ℚ) + 1 - k) *
              (((n + 1).choose k : ℚ) * ((n + k).choose k : ℚ) ^ 2) := by ring
      have hkey2 : ((n : ℚ) + 1) * ((n : ℚ) + k) ^ 2 *
          (((n - 1).choose k : ℚ) * ((n - 1 + k).choose k : ℚ) ^ 2) =
          (n : ℚ) * ((n : ℚ) - k) * ((n : ℚ) + 1 - k) *
          (((n + 1).choose k : ℚ) * ((n + k).choose k : ℚ) ^ 2) := by
        apply mul_left_cancel₀ hn0
        linear_combination hkey
      have hden : ((n : ℚ) + 1) * ((n : ℚ) + k) ^ 2 ≠ 0 := mul_ne_zero hpos1 (pow_ne_zero 2 hpos2)
      rw [← neg_div, div_mul_eq_mul_div, eq_div_iff hden]
      calc -((-1 : ℚ) ^ (n + k)) * ((n - 1).choose k : ℚ) * ((n - 1 + k).choose k : ℚ) ^ 2 *
            (((n : ℚ) + 1) * ((n : ℚ) + k) ^ 2)
          = -((-1 : ℚ) ^ (n + k)) * (((n : ℚ) + 1) * ((n : ℚ) + k) ^ 2 *
              (((n - 1).choose k : ℚ) * ((n - 1 + k).choose k : ℚ) ^ 2)) := by ring
        _ = -((-1 : ℚ) ^ (n + k)) * ((n : ℚ) * ((n : ℚ) - k) * ((n : ℚ) + 1 - k) *
              (((n + 1).choose k : ℚ) * ((n + k).choose k : ℚ) ^ 2)) := by rw [hkey2]
        _ = _ := by ring

private lemma H_succ_k (n k : ℕ) (hk : k ≤ n + 1) :
    H n (k + 1) = -(((n : ℚ) + 1 - k) * ((n : ℚ) + k + 1) ^ 2 / ((k : ℚ) + 1) ^ 3) * H n k := by
  unfold H
  have h1 : ((n + 1).choose (k + 1) : ℚ) * ((k + 1 : ℕ) : ℚ) =
      ((n + 1).choose k : ℚ) * ((n + 1 - k : ℕ) : ℚ) := by
    exact_mod_cast Nat.choose_succ_right_eq (n + 1) k
  have h2 : ((n + k + 1).choose (k + 1) : ℚ) * ((k + 1 : ℕ) : ℚ) =
      ((n + k + 1 : ℕ) : ℚ) * ((n + k).choose k : ℚ) := by
    have h := succ_mul_choose (n + k) k
    exact_mod_cast h.symm
  rw [Nat.cast_sub hk] at h1
  push_cast at h1 h2
  have hpos : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hsign : (-1 : ℚ) ^ (n + (k + 1)) = -((-1 : ℚ) ^ (n + k)) := by
    rw [show n + (k + 1) = (n + k) + 1 by omega, pow_succ]; ring
  rw [show n + (k + 1) = n + k + 1 by omega]
  rw [show (-1 : ℚ) ^ (n + k + 1) = -((-1 : ℚ) ^ (n + k)) by rw [pow_succ]; ring]
  have hcomb : ((n + 1).choose (k + 1) : ℚ) * ((n + k + 1).choose (k + 1) : ℚ) ^ 2 * ((k : ℚ) + 1) ^ 3 =
      ((n : ℚ) + 1 - k) * ((n : ℚ) + k + 1) ^ 2 * ((n + 1).choose k : ℚ) * ((n + k).choose k : ℚ) ^ 2 := by
    calc ((n + 1).choose (k + 1) : ℚ) * ((n + k + 1).choose (k + 1) : ℚ) ^ 2 * ((k : ℚ) + 1) ^ 3
        = (((n + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1)) *
          (((n + k + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1)) ^ 2 := by ring
      _ = (((n + 1).choose k : ℚ) * ((n : ℚ) + 1 - k)) *
          (((n : ℚ) + k + 1) * ((n + k).choose k : ℚ)) ^ 2 := by rw [h1, h2]
      _ = ((n : ℚ) + 1 - k) * ((n : ℚ) + k + 1) ^ 2 * ((n + 1).choose k : ℚ) * ((n + k).choose k : ℚ) ^ 2 := by ring
  rw [← neg_div, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 3 hpos)]
  calc -((-1 : ℚ) ^ (n + k)) * ((n + 1).choose (k + 1) : ℚ) * ((n + k + 1).choose (k + 1) : ℚ) ^ 2 *
        ((k : ℚ) + 1) ^ 3
      = -((-1 : ℚ) ^ (n + k)) * (((n + 1).choose (k + 1) : ℚ) *
          ((n + k + 1).choose (k + 1) : ℚ) ^ 2 * ((k : ℚ) + 1) ^ 3) := by ring
    _ = -((-1 : ℚ) ^ (n + k)) * (((n : ℚ) + 1 - k) * ((n : ℚ) + k + 1) ^ 2 *
          ((n + 1).choose k : ℚ) * ((n + k).choose k : ℚ) ^ 2) := by rw [hcomb]
    _ = _ := by ring

private lemma sum_F_eq_A (n : ℕ) :
    ∑ k ∈ Finset.range (n + 2), F n k = (A n : ℚ) := by
  rw [Finset.sum_range_succ]
  have hlast : F n (n + 1) = 0 := by
    unfold F; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [hlast, add_zero]
  unfold A F
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma sum_F_succ_eq_A (n : ℕ) :
    ∑ k ∈ Finset.range (n + 2), F (n + 1) k = (A (n + 1) : ℚ) := by
  unfold A F
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma sum_F_pred_eq_A (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 2), F (n - 1) k = (A (n - 1) : ℚ) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have h1 : F (n - 1) (n + 1) = 0 := by
    unfold F; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have h2 : F (n - 1) n = 0 := by
    unfold F; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [h1, h2, add_zero, add_zero]
  have hlen : n - 1 + 1 = n := by omega
  unfold A F
  rw [hlen]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma sum_k_F_eq_a1 (n : ℕ) :
    ∑ k ∈ Finset.range (n + 2), (k : ℚ) * F n k = (a1 n : ℚ) := by
  rw [Finset.sum_range_succ]
  have hlast : (n + 1 : ℚ) * F n (n + 1) = 0 := by
    unfold F; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [show ((n + 1 : ℕ) : ℚ) * F n (n + 1) = 0 by exact_mod_cast hlast, add_zero]
  unfold a1 F
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma sum_k3_F_eq_a (n : ℕ) :
    ∑ k ∈ Finset.range (n + 2), (k : ℚ) ^ 3 * F n k = (a n : ℚ) := by
  rw [Finset.sum_range_succ]
  have hlast : ((n + 1 : ℕ) : ℚ) ^ 3 * F n (n + 1) = 0 := by
    unfold F; rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  rw [hlast, add_zero]
  unfold a F
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma idA (n : ℕ) :
    5 * a1 n = ((n : ℤ) + 1) * (A (n + 1) - 3 * A n) := by
  suffices h : (5 : ℚ) * (a1 n : ℚ) = ((n : ℚ) + 1) * ((A (n + 1) : ℚ) - 3 * (A n : ℚ)) by
    exact_mod_cast h
  let G : ℕ → ℚ := fun k => (4 * (k : ℚ) ^ 3 / ((n : ℚ) + 1) ^ 2) * H n k
  have hstep : ∀ k ∈ Finset.range (n + 2),
      ((n : ℚ) + 1) * F (n + 1) k - (3 * ((n : ℚ) + 1) + 5 * (k : ℚ)) * F n k =
      G (k + 1) - G k := by
    intro k hk
    have hk' : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    dsimp only [G]
    rw [F_succ_eq_H, F_eq_H n k hk', H_succ_k n k hk']
    have hpos1 : ((n : ℚ) + 1) ≠ 0 := by positivity
    have hpos2 : ((k : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp [hpos1, hpos2]
    ring
  have hsum := Finset.sum_congr rfl hstep
  rw [Finset.sum_range_sub G (n + 2)] at hsum
  have hG0 : G 0 = 0 := by simp [G]
  have hGend : G (n + 2) = 0 := by
    simp [G, H, Nat.choose_eq_zero_of_lt (show n + 1 < n + 2 by omega)]
  rw [hG0, hGend, sub_zero] at hsum
  have hlin : ∑ k ∈ Finset.range (n + 2),
      (((n : ℚ) + 1) * F (n + 1) k - (3 * ((n : ℚ) + 1) + 5 * (k : ℚ)) * F n k) =
      ((n : ℚ) + 1) * (∑ k ∈ Finset.range (n + 2), F (n + 1) k) -
      3 * ((n : ℚ) + 1) * (∑ k ∈ Finset.range (n + 2), F n k) -
      5 * (∑ k ∈ Finset.range (n + 2), (k : ℚ) * F n k) := by
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hlin, sum_F_succ_eq_A, sum_F_eq_A, sum_k_F_eq_a1] at hsum
  linarith

private lemma idB (n : ℕ) :
    5 * ((n : ℤ) + 2) * ((n : ℤ) + 3) * a n =
      ((n : ℤ) + 1) ^ 3 * ((2 * (n : ℤ) ^ 2 + 1) * A (n + 1) - ((n : ℤ) ^ 2 + 5 * n + 3) * A n) := by
  suffices h : (5 : ℚ) * ((n : ℚ) + 2) * ((n : ℚ) + 3) * (a n : ℚ) =
      ((n : ℚ) + 1) ^ 3 * ((2 * (n : ℚ) ^ 2 + 1) * (A (n + 1) : ℚ) -
        ((n : ℚ) ^ 2 + 5 * (n : ℚ) + 3) * (A n : ℚ)) by
    exact_mod_cast h
  let G : ℕ → ℚ := fun k =>
    ((k : ℚ) ^ 3 * (5 * (k : ℚ) ^ 2 * n + 10 * (k : ℚ) ^ 2 - 20 * (k : ℚ) * n - 25 * (k : ℚ) +
      3 * (n : ℚ) ^ 3 + 8 * (n : ℚ) ^ 2 + 24 * (n : ℚ) + 19) / ((n : ℚ) + 1)) * H n k
  have hstep : ∀ k ∈ Finset.range (n + 2),
      ((n : ℚ) + 1) ^ 3 * ((2 * (n : ℚ) ^ 2 + 1) * F (n + 1) k -
        ((n : ℚ) ^ 2 + 5 * (n : ℚ) + 3) * F n k) -
      5 * ((n : ℚ) + 2) * ((n : ℚ) + 3) * (k : ℚ) ^ 3 * F n k =
      G (k + 1) - G k := by
    intro k hk
    have hk' : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    dsimp only [G]
    rw [F_succ_eq_H, F_eq_H n k hk', H_succ_k n k hk']
    have hpos1 : ((n : ℚ) + 1) ≠ 0 := by positivity
    have hpos2 : ((k : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp [hpos1, hpos2]
    ring
  have hsum := Finset.sum_congr rfl hstep
  rw [Finset.sum_range_sub G (n + 2)] at hsum
  have hG0 : G 0 = 0 := by simp [G]
  have hGend : G (n + 2) = 0 := by
    simp [G, H, Nat.choose_eq_zero_of_lt (show n + 1 < n + 2 by omega)]
  rw [hG0, hGend, sub_zero] at hsum
  have hlin : ∑ k ∈ Finset.range (n + 2),
      (((n : ℚ) + 1) ^ 3 * ((2 * (n : ℚ) ^ 2 + 1) * F (n + 1) k -
        ((n : ℚ) ^ 2 + 5 * (n : ℚ) + 3) * F n k) -
      5 * ((n : ℚ) + 2) * ((n : ℚ) + 3) * (k : ℚ) ^ 3 * F n k) =
      ((n : ℚ) + 1) ^ 3 * (2 * (n : ℚ) ^ 2 + 1) * (∑ k ∈ Finset.range (n + 2), F (n + 1) k) -
      ((n : ℚ) + 1) ^ 3 * ((n : ℚ) ^ 2 + 5 * (n : ℚ) + 3) * (∑ k ∈ Finset.range (n + 2), F n k) -
      5 * ((n : ℚ) + 2) * ((n : ℚ) + 3) * (∑ k ∈ Finset.range (n + 2), (k : ℚ) ^ 3 * F n k) := by
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hlin, sum_F_succ_eq_A, sum_F_eq_A, sum_k3_F_eq_a] at hsum
  linarith

private lemma idC (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℤ) + 1) ^ 2 * A (n + 1) =
      (11 * (n : ℤ) ^ 2 + 11 * n + 3) * A n + (n : ℤ) ^ 2 * A (n - 1) := by
  suffices h : ((n : ℚ) + 1) ^ 2 * (A (n + 1) : ℚ) =
      (11 * (n : ℚ) ^ 2 + 11 * (n : ℚ) + 3) * (A n : ℚ) + (n : ℚ) ^ 2 * (A (n - 1) : ℚ) by
    exact_mod_cast h
  let G : ℕ → ℚ := fun k =>
    (-(k : ℚ) ^ 3 * ((k : ℚ) ^ 2 - 6 * (k : ℚ) * n - 5 * (k : ℚ) - 11 * (n : ℚ) ^ 2 - 7 * (n : ℚ)) /
      (((n : ℚ) + 1) * ((k : ℚ) + n) ^ 2)) * H n k
  have hstep : ∀ k ∈ Finset.range (n + 2),
      ((n : ℚ) + 1) ^ 2 * F (n + 1) k -
      (11 * (n : ℚ) ^ 2 + 11 * (n : ℚ) + 3) * F n k -
      (n : ℚ) ^ 2 * F (n - 1) k =
      G (k + 1) - G k := by
    intro k hk
    have hk' : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    dsimp only [G]
    rw [F_succ_eq_H, F_eq_H n k hk', F_pred_eq_H n k hn hk', H_succ_k n k hk']
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
  have hGend : G (n + 2) = 0 := by
    simp [G, H, Nat.choose_eq_zero_of_lt (show n + 1 < n + 2 by omega)]
  rw [hG0, hGend, sub_zero] at hsum
  have hlin : ∑ k ∈ Finset.range (n + 2),
      (((n : ℚ) + 1) ^ 2 * F (n + 1) k -
      (11 * (n : ℚ) ^ 2 + 11 * (n : ℚ) + 3) * F n k -
      (n : ℚ) ^ 2 * F (n - 1) k) =
      ((n : ℚ) + 1) ^ 2 * (∑ k ∈ Finset.range (n + 2), F (n + 1) k) -
      (11 * (n : ℚ) ^ 2 + 11 * (n : ℚ) + 3) * (∑ k ∈ Finset.range (n + 2), F n k) -
      (n : ℚ) ^ 2 * (∑ k ∈ Finset.range (n + 2), F (n - 1) k) := by
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hlin, sum_F_succ_eq_A, sum_F_eq_A, sum_F_pred_eq_A n hn] at hsum
  linarith

private lemma idD (n : ℕ) (hn : 1 ≤ n) :
    5 * ((n : ℤ) + 2) * ((n : ℤ) + 3) * a n =
      (n : ℤ) ^ 2 * ((n : ℤ) + 1) *
        (3 * (7 * (n : ℤ) ^ 2 + 5 * n + 1) * A n + (2 * (n : ℤ) ^ 2 + 1) * A (n - 1)) := by
  have hB := idB n
  have hC := idC n hn
  have hpos : ((n : ℤ) + 1) ^ 2 ≠ 0 := by positivity
  apply mul_left_cancel₀ hpos
  calc ((n : ℤ) + 1) ^ 2 * (5 * ((n : ℤ) + 2) * ((n : ℤ) + 3) * a n)
      = ((n : ℤ) + 1) ^ 3 * ((2 * (n : ℤ) ^ 2 + 1) * (((n : ℤ) + 1) ^ 2 * A (n + 1)) -
          ((n : ℤ) + 1) ^ 2 * ((n : ℤ) ^ 2 + 5 * n + 3) * A n) := by
        linear_combination ((n : ℤ) + 1) ^ 2 * hB
    _ = ((n : ℤ) + 1) ^ 3 * ((2 * (n : ℤ) ^ 2 + 1) *
          ((11 * (n : ℤ) ^ 2 + 11 * n + 3) * A n + (n : ℤ) ^ 2 * A (n - 1)) -
          ((n : ℤ) + 1) ^ 2 * ((n : ℤ) ^ 2 + 5 * n + 3) * A n) := by rw [hC]
    _ = ((n : ℤ) + 1) ^ 2 * ((n : ℤ) ^ 2 * ((n : ℤ) + 1) *
          (3 * (7 * (n : ℤ) ^ 2 + 5 * n + 1) * A n + (2 * (n : ℤ) ^ 2 + 1) * A (n - 1))) := by
        ring

private lemma choose_mod_prime (p : ℕ) [Fact p.Prime] (q r s t : ℕ) (hr : r < p) (ht : t < p) :
    ((p * q + r).choose (p * s + t) : ZMod p) = (q.choose s : ZMod p) * (r.choose t : ZMod p) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := p * q + r) (k := p * s + t)
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h1 : (p * q + r) % p = r := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  have h2 : (p * s + t) % p = t := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt ht]
  have h3 : (p * q + r) / p = q := by
    rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hr, add_zero]
  have h4 : (p * s + t) / p = s := by
    rw [Nat.mul_add_div hp, Nat.div_eq_of_lt ht, add_zero]
  rw [h1, h2, h3, h4] at h
  have hzm := (ZMod.natCast_eq_natCast_iff _ _ p).mpr h
  push_cast at hzm
  rw [hzm, mul_comm]

private lemma choose_add_mod_prime (p : ℕ) [Fact p.Prime] (q r s t : ℕ)
    (hr : r < p) (ht : t ≤ r) :
    (((p * q + r) + (p * s + t)).choose (p * s + t) : ZMod p) =
      ((q + s).choose s : ZMod p) * ((r + t).choose t : ZMod p) := by
  have hp : p.Prime := Fact.out
  by_cases hrt : r + t < p
  · have heq : (p * q + r) + (p * s + t) = p * (q + s) + (r + t) := by ring
    rw [heq]
    exact choose_mod_prime p (q + s) (r + t) s t hrt (by omega)
  · have hrt2 : r + t - p < p := by omega
    have hrt_eq : r + t = p + (r + t - p) := by omega
    have heq : (p * q + r) + (p * s + t) = p * (q + s + 1) + (r + t - p) := by linarith
    rw [heq, choose_mod_prime p (q + s + 1) (r + t - p) s t hrt2 (by omega)]
    have hzero1 : (r + t - p).choose t = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hzero2 : ((r + t).choose t : ZMod p) = 0 := by
      have hdiv : p ∣ (r + t).choose t := by
        have hfac := Nat.choose_mul_factorial_mul_factorial (show t ≤ r + t by omega)
        rw [show r + t - t = r by omega] at hfac
        have hpdvd : p ∣ (r + t).factorial := hp.dvd_factorial.mpr (by omega)
        rw [← hfac] at hpdvd
        have hnd1 : ¬ p ∣ t.factorial := fun hd => by
          have := hp.dvd_factorial.mp hd; omega
        have hnd2 : ¬ p ∣ r.factorial := fun hd => by
          have := hp.dvd_factorial.mp hd; omega
        rcases hp.dvd_mul.mp hpdvd with h1 | h2
        · rcases hp.dvd_mul.mp h1 with hc | ht'
          · exact hc
          · exact absurd ht' hnd1
        · exact absurd h2 hnd2
      exact (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
    rw [hzero1, hzero2]
    simp

private lemma A_lucas (p : ℕ) [Fact p.Prime] (hp_odd : p % 2 = 1) (q r : ℕ) (hr : r < p) :
    (A (p * q + r) : ZMod p) = (A q : ZMod p) * (A r : ZMod p) := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  unfold A
  push_cast
  have hrange : ∀ n : ℕ,
      ∑ k ∈ Finset.range (n + 1), (-1 : ZMod p) ^ (n + k) *
        ((n.choose k : ZMod p) * (((n + k).choose k : ZMod p) ^ 2)) =
      ∑ k ∈ Finset.range (n + 1), (-1 : ZMod p) ^ (n + k) *
        ((n.choose k : ZMod p) * ((n + k).choose k : ZMod p) ^ 2) := fun _ => rfl
  -- Extend sum over k to range (p * (q + 1)) since choose = 0 for k > p*q + r
  have hext : ∑ k ∈ Finset.range (p * q + r + 1),
        (-1 : ZMod p) ^ (p * q + r + k) *
          (((p * q + r).choose k : ZMod p) * (((p * q + r + k).choose k : ZMod p) ^ 2)) =
      ∑ k ∈ Finset.range (p * (q + 1)),
        (-1 : ZMod p) ^ (p * q + r + k) *
          (((p * q + r).choose k : ZMod p) * (((p * q + r + k).choose k : ZMod p) ^ 2)) := by
    apply Finset.sum_subset
    · intro k hk
      rw [Finset.mem_range] at hk ⊢
      nlinarith
    · intro k _ hk
      rw [Finset.mem_range] at hk
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [hext]
  -- Split k ∈ range (p * (q + 1)) into s ∈ range (q + 1), t ∈ range p via k = p * s + t
  have hsplit : ∑ k ∈ Finset.range (p * (q + 1)),
        (-1 : ZMod p) ^ (p * q + r + k) *
          (((p * q + r).choose k : ZMod p) * (((p * q + r + k).choose k : ZMod p) ^ 2)) =
      ∑ s ∈ Finset.range (q + 1), ∑ t ∈ Finset.range p,
        (-1 : ZMod p) ^ (p * q + r + (p * s + t)) *
          (((p * q + r).choose (p * s + t) : ZMod p) *
            (((p * q + r + (p * s + t)).choose (p * s + t) : ZMod p) ^ 2)) := by
    rw [← Finset.sum_product']
    apply Finset.sum_nbij' (fun k => (k / p, k % p)) (fun st => p * st.1 + st.2)
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨Nat.div_lt_of_lt_mul (by linarith), Nat.mod_lt k hp_pos⟩
    · intro st hst
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hst
      rw [Finset.mem_range]
      nlinarith
    · intro k _
      exact Nat.div_add_mod k p
    · intro st hst
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hst
      ext
      · dsimp; rw [Nat.mul_add_div hp_pos, Nat.div_eq_of_lt hst.2, add_zero]
      · dsimp; rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hst.2]
    · intro k _
      dsimp only
      rw [Nat.div_add_mod k p]
  rw [hsplit]
  -- Shrink inner sum from range p to range (r + 1)
  have hinner : ∀ s ∈ Finset.range (q + 1),
      ∑ t ∈ Finset.range p,
        (-1 : ZMod p) ^ (p * q + r + (p * s + t)) *
          (((p * q + r).choose (p * s + t) : ZMod p) *
            (((p * q + r + (p * s + t)).choose (p * s + t) : ZMod p) ^ 2)) =
      ((-1 : ZMod p) ^ (q + s) * ((q.choose s : ZMod p) * ((q + s).choose s : ZMod p) ^ 2)) *
      ∑ t ∈ Finset.range (r + 1),
        (-1 : ZMod p) ^ (r + t) * ((r.choose t : ZMod p) * ((r + t).choose t : ZMod p) ^ 2) := by
    intro s _
    rw [Finset.mul_sum]
    rw [← Finset.sum_subset (Finset.range_mono (show r + 1 ≤ p by omega))]
    · apply Finset.sum_congr rfl
      intro t ht
      have ht_le : t ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
      have ht_lt : t < p := by omega
      rw [choose_mod_prime p q r s t hr ht_lt, choose_add_mod_prime p q r s t hr ht_le]
      have hsign : (-1 : ZMod p) ^ (p * q + r + (p * s + t)) =
          (-1 : ZMod p) ^ (q + s) * (-1 : ZMod p) ^ (r + t) := by
        rw [show p * q + r + (p * s + t) = p * (q + s) + (r + t) by ring, pow_add, pow_mul]
        have hp1 : (-1 : ZMod p) ^ p = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr hp_odd)
        rw [hp1]
      rw [hsign]
      ring
    · intro t ht htn
      have ht_lt : t < p := Finset.mem_range.mp ht
      have ht_gt : r < t := by rw [Finset.mem_range] at htn; omega
      rw [choose_mod_prime p q r s t hr ht_lt, Nat.choose_eq_zero_of_lt ht_gt]
      simp
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]

private lemma three_pow_five : (3 : ZMod 5) ^ 5 = 3 := by decide
private lemma A_one_mod3 : (A 1 : ZMod 3) = 0 := by decide

private lemma A_mod5 (n : ℕ) : (A n : ZMod 5) = (3 : ZMod 5) ^ n := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hlt : n < 5
    · interval_cases n <;> decide
    · have hdiv : n / 5 < n := Nat.div_lt_self (by omega) (by omega)
      have hmod : n % 5 < 5 := Nat.mod_lt n (by omega)
      have hne : n = 5 * (n / 5) + n % 5 := (Nat.div_add_mod n 5).symm
      conv_lhs => rw [hne]
      rw [A_lucas 5 (by decide) (n / 5) (n % 5) hmod]
      rw [ih (n / 5) hdiv, ih (n % 5) (by omega)]
      conv_rhs => rw [hne]
      rw [pow_add, pow_mul]
      rw [three_pow_five]

private lemma A_odd_mod3 (n : ℕ) (hodd : n % 2 = 1) : (A n : ZMod 3) = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hdiv : n / 3 < n := Nat.div_lt_self (by omega) (by omega)
    have hmod : n % 3 < 3 := Nat.mod_lt n (by omega)
    have hne : n = 3 * (n / 3) + n % 3 := (Nat.div_add_mod n 3).symm
    conv_lhs => rw [hne]
    rw [A_lucas 3 (by decide) (n / 3) (n % 3) hmod]
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcases with hr | hr | hr
    · have hqodd : (n / 3) % 2 = 1 := by omega
      rw [ih (n / 3) hdiv hqodd, zero_mul]
    · rw [hr]
      rw [A_one_mod3, mul_zero]
    · have hqodd : (n / 3) % 2 = 1 := by omega
      rw [ih (n / 3) hdiv hqodd, zero_mul]

private lemma five_dvd_X (n : ℕ) :
    (5 : ℤ) ∣ (2 * (n : ℤ) ^ 2 + 1) * A (n + 1) - ((n : ℤ) ^ 2 + 5 * n + 3) * A n := by
  change ((5 : ℕ) : ℤ) ∣ _
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [A_mod5 (n + 1), A_mod5 n]
  have h3p : (3 : ZMod 5) ^ (n + 1) = (3 : ZMod 5) ^ n * 3 := pow_succ _ _
  rw [h3p]
  have h5 : (5 : ZMod 5) = 0 := by decide
  have h : ((2 * (n : ZMod 5) ^ 2 + 1) * ((3 : ZMod 5) ^ n * 3) -
      ((n : ZMod 5) ^ 2 + 5 * (n : ZMod 5) + 3) * (3 : ZMod 5) ^ n) =
      (5 : ZMod 5) * ((n : ZMod 5) ^ 2 - (n : ZMod 5)) * (3 : ZMod 5) ^ n := by ring
  rw [h, h5, zero_mul, zero_mul]

private lemma five_dvd_Y (n : ℕ) (hn : 1 ≤ n) :
    (5 : ℤ) ∣ 3 * (7 * (n : ℤ) ^ 2 + 5 * n + 1) * A n + (2 * (n : ℤ) ^ 2 + 1) * A (n - 1) := by
  change ((5 : ℕ) : ℤ) ∣ _
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [A_mod5 n, A_mod5 (n - 1)]
  have h3p : (3 : ZMod 5) ^ n = (3 : ZMod 5) ^ (n - 1) * 3 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    exact pow_succ _ _
  rw [h3p]
  have h5 : (5 : ZMod 5) = 0 := by decide
  have h : 3 * (7 * (n : ZMod 5) ^ 2 + 5 * (n : ZMod 5) + 1) * ((3 : ZMod 5) ^ (n - 1) * 3) +
      (2 * (n : ZMod 5) ^ 2 + 1) * (3 : ZMod 5) ^ (n - 1) =
      (5 : ZMod 5) * (13 * (n : ZMod 5) ^ 2 + 9 * (n : ZMod 5) + 2) * (3 : ZMod 5) ^ (n - 1) := by ring
  rw [h, h5, zero_mul, zero_mul]

private lemma three_dvd_Y_even (m : ℕ) (hm : 1 ≤ m) :
    (3 : ℤ) ∣ 3 * (7 * (2 * m : ℤ) ^ 2 + 5 * (2 * m) + 1) * A (2 * m) +
      (2 * (2 * m : ℤ) ^ 2 + 1) * A (2 * m - 1) := by
  change ((3 : ℕ) : ℤ) ∣ _
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [A_odd_mod3 (2 * m - 1) (by omega)]
  have h3 : (3 : ZMod 3) = 0 := by decide
  rw [h3]
  ring

private lemma three_dvd_a_even (m : ℕ) : (3 : ℤ) ∣ a (2 * m) := by
  have hmod : (a (2 * m) : ZMod 3) = (a1 (2 * m) : ZMod 3) := by
    unfold a a1
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    have hk3 : (k : ZMod 3) ^ 3 = (k : ZMod 3) := by
      haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
      exact ZMod.pow_card (k : ZMod 3)
    linear_combination (-1 : ZMod 3) ^ (2 * m + k) *
      ((2 * m).choose k : ZMod 3) * ((2 * m + k).choose k : ZMod 3) ^ 2 * hk3
  have h5a1 : (5 : ZMod 3) * (a1 (2 * m) : ZMod 3) = 0 := by
    have h := congrArg (Int.cast (R := ZMod 3)) (idA (2 * m))
    push_cast at h
    rw [A_odd_mod3 (2 * m + 1) (by omega)] at h
    have h3 : (3 : ZMod 3) = 0 := by decide
    rw [h3] at h
    simpa using h
  have ha1 : (a1 (2 * m) : ZMod 3) = 0 := by
    have hinv : (2 : ZMod 3) * (5 : ZMod 3) = 1 := by decide
    calc (a1 (2 * m) : ZMod 3) = ((2 : ZMod 3) * 5) * (a1 (2 * m) : ZMod 3) := by rw [hinv, one_mul]
      _ = 2 * (5 * (a1 (2 * m) : ZMod 3)) := by ring
      _ = 0 := by rw [h5a1, mul_zero]
  change ((3 : ℕ) : ℤ) ∣ _
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hmod, ha1]

end OMA_a357559_proof

open OMA_a357559_proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a357559.main := by
  intro m hm
  have hcop_main : IsCoprime ((m : ℤ) ^ 2) ((2 * (m : ℤ) + 1) ^ 3) := by
    have hc : IsCoprime (m : ℤ) (2 * (m : ℤ) + 1) := ⟨-2, 1, by ring⟩
    exact (hc.pow_left).pow_right
  apply hcop_main.mul_dvd
  · -- Part 1: (m : ℤ) ^ 2 ∣ 3 * a (2 * m)
    have hD := idD (2 * m) (by omega)
    have h5Y := five_dvd_Y (2 * m) (by omega)
    have h3Y := three_dvd_Y_even m hm
    have h15Y : (15 : ℤ) ∣ 3 * (7 * (2 * m : ℤ) ^ 2 + 5 * (2 * m) + 1) * A (2 * m) +
        (2 * (2 * m : ℤ) ^ 2 + 1) * A (2 * m - 1) := by
      have hcop35 : IsCoprime (3 : ℤ) 5 := ⟨2, -1, by ring⟩
      simpa using hcop35.mul_dvd h3Y h5Y
    rcases h15Y with ⟨Y', hY'⟩
    push_cast at hD
    rw [hY'] at hD
    have heq : ((m : ℤ) + 1) * (2 * (m : ℤ) + 3) * a (2 * m) =
        6 * (m : ℤ) ^ 2 * (2 * (m : ℤ) + 1) * Y' := by
      linarith
    by_cases h3m : (3 : ℤ) ∣ (m : ℤ)
    · rcases h3m with ⟨j, hj⟩
      have heq2 : ((m : ℤ) + 1) * (2 * j + 1) * a (2 * m) =
          2 * (m : ℤ) ^ 2 * (2 * (m : ℤ) + 1) * Y' := by
        have h3eq : 2 * (m : ℤ) + 3 = 3 * (2 * j + 1) := by rw [hj]; ring
        rw [h3eq] at heq
        linarith
      by_cases h3j : (3 : ℤ) ∣ j
      · -- 9 ∣ m: m^2 is coprime to (m + 1) * (2 * j + 1)
        rcases h3j with ⟨k, hk⟩
        have hc1 : IsCoprime (m : ℤ) ((m : ℤ) + 1) := ⟨-1, 1, by ring⟩
        have hc2 : IsCoprime (m : ℤ) (2 * j + 1) := by
          rw [hj]
          have hcj : IsCoprime j (2 * j + 1) := ⟨-2, 1, by ring⟩
          have hc3 : IsCoprime (3 : ℤ) (2 * j + 1) := ⟨-2 * k, 1, by rw [hk]; ring⟩
          exact hc3.mul_left hcj
        have hcop : IsCoprime ((m : ℤ) ^ 2) (((m : ℤ) + 1) * (2 * j + 1)) :=
          (hc1.mul_right hc2).pow_left
        have hdvd : (m : ℤ) ^ 2 ∣ a (2 * m) := by
          apply hcop.dvd_of_dvd_mul_left
          exact ⟨2 * (2 * (m : ℤ) + 1) * Y', by linarith⟩
        exact dvd_mul_of_dvd_right hdvd 3
      · -- 3 ∥ m: m^2 = 9 * j^2 with IsCoprime 9 (j^2)
        have hm2 : (m : ℤ) ^ 2 = 9 * j ^ 2 := by rw [hj]; ring
        rw [hm2]
        have hcop3j : IsCoprime (3 : ℤ) j := by
          have hp3 : Prime (3 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)
          exact hp3.coprime_iff_not_dvd.mpr h3j
        have hcop9j2 : IsCoprime (9 : ℤ) (j ^ 2) := by
          have : (9 : ℤ) = 3 ^ 2 := by norm_num
          rw [this]
          exact hcop3j.pow_left.pow_right
        apply hcop9j2.mul_dvd
        · rcases three_dvd_a_even m with ⟨c, hc⟩
          exact ⟨c, by linarith⟩
        · have hc1 : IsCoprime j ((m : ℤ) + 1) := ⟨-3, 1, by rw [hj]; ring⟩
          have hc2 : IsCoprime j (2 * j + 1) := ⟨-2, 1, by ring⟩
          have hcop : IsCoprime (j ^ 2) (((m : ℤ) + 1) * (2 * j + 1)) :=
            (hc1.mul_right hc2).pow_left
          have hdvd : j ^ 2 ∣ a (2 * m) := by
            apply hcop.dvd_of_dvd_mul_left
            exact ⟨18 * (2 * (m : ℤ) + 1) * Y', by rw [hm2] at heq2; linarith⟩
          exact dvd_mul_of_dvd_right hdvd 3
    · -- 3 ∤ m: m^2 is coprime to (m + 1) * (2 * m + 3)
      have hc1 : IsCoprime (m : ℤ) ((m : ℤ) + 1) := ⟨-1, 1, by ring⟩
      have hcop3m : IsCoprime (3 : ℤ) (m : ℤ) := by
        have hp3 : Prime (3 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)
        exact hp3.coprime_iff_not_dvd.mpr h3m
      have hc2 : IsCoprime (m : ℤ) (2 * (m : ℤ) + 3) := by
        rcases hcop3m with ⟨u, v, huv⟩
        exact ⟨v - 2 * u, u, by linear_combination huv⟩
      have hcop : IsCoprime ((m : ℤ) ^ 2) (((m : ℤ) + 1) * (2 * (m : ℤ) + 3)) :=
        (hc1.mul_right hc2).pow_left
      have hdvd : (m : ℤ) ^ 2 ∣ a (2 * m) := by
        apply hcop.dvd_of_dvd_mul_left
        exact ⟨6 * (2 * (m : ℤ) + 1) * Y', by linarith⟩
      exact dvd_mul_of_dvd_right hdvd 3
  · -- Part 2: (2 * m + 1) ^ 3 ∣ 3 * a (2 * m)
    have hB := idB (2 * m)
    rcases five_dvd_X (2 * m) with ⟨X', hX'⟩
    push_cast at hB hX'
    rw [hX'] at hB
    have heq : (2 * (m : ℤ) + 2) * (2 * (m : ℤ) + 3) * a (2 * m) =
        (2 * (m : ℤ) + 1) ^ 3 * X' := by
      linarith
    have hc1 : IsCoprime (2 * (m : ℤ) + 1) (2 * (m : ℤ) + 2) := ⟨-1, 1, by ring⟩
    have hc2 : IsCoprime (2 * (m : ℤ) + 1) (2 * (m : ℤ) + 3) := ⟨(m : ℤ) + 1, -(m : ℤ), by ring⟩
    have hcop : IsCoprime ((2 * (m : ℤ) + 1) ^ 3) ((2 * (m : ℤ) + 2) * (2 * (m : ℤ) + 3)) :=
      (hc1.mul_right hc2).pow_left
    have hdvd : (2 * (m : ℤ) + 1) ^ 3 ∣ a (2 * m) := by
      apply hcop.dvd_of_dvd_mul_left
      exact ⟨X', heq⟩
    exact dvd_mul_of_dvd_right hdvd 3
