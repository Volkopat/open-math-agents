import OMAStatements.S_oeis_a221466

-- Problem: A221466: Number of 0..n arrays of length 7 with each element unequal to at least one neighbor, starting with 0.
-- Upstream: formal-conjectures statements/oeis-a221466.lean:0 (declaration OMA.S_oeis_a221466.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: write a(n) as the iterated sum over x1, ..., x6 in 0..n and sum out x6, x5, ..., x1
-- in turn. At each step the summand depends on the new entry x only through whether x equals the
-- previous entry y, and the sum over x of (if y = x then A else B) is A + n B. This gives
-- a(n) = n^6 + 4 n^5 + 3 n^4, whose seventh difference vanishes (the recurrence), and the g.f.
-- follows by comparing coefficients.

namespace R06A221466

open OMA.S_oeis_a221466

theorem bnd {n x : ℕ} (h : x ∈ Finset.range (n + 1)) : x ≤ n := by
  rw [Finset.mem_range] at h
  omega

theorem G1 (n y A B : ℕ) (hy : y ≤ n) :
    ∑ x ∈ Finset.range (n + 1), (if y = x then A else B) = A + n * B := by
  have hmem : y ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase (Finset.range (n + 1)) _ hmem, if_pos (rfl : y = y)]
  have h2 : ∑ x ∈ (Finset.range (n + 1)).erase y, (if y = x then A else B) =
      ∑ _x ∈ (Finset.range (n + 1)).erase y, B :=
    Finset.sum_congr rfl (fun x hx => if_neg (fun h => Finset.ne_of_mem_erase hx h.symm))
  rw [h2, Finset.sum_const, Finset.card_erase_of_mem hmem, Finset.card_range, smul_eq_mul,
    Nat.add_sub_cancel]

theorem L6 (n x1 x2 x3 x4 x5 : ℕ) (h5 : x5 ≤ n) :
    ∑ x6 ∈ Finset.range (n + 1), (if ok 0 x1 x2 x3 x4 x5 x6 then 1 else 0) =
      if x1 ≠ 0 ∧ (x1 ≠ x2 ∨ x2 ≠ x3) ∧ (x2 ≠ x3 ∨ x3 ≠ x4) ∧ (x3 ≠ x4 ∨ x4 ≠ x5) then n
      else 0 := by
  by_cases hP : x1 ≠ 0 ∧ (x1 ≠ x2 ∨ x2 ≠ x3) ∧ (x2 ≠ x3 ∨ x3 ≠ x4) ∧ (x3 ≠ x4 ∨ x4 ≠ x5)
  · rw [if_pos hP]
    have h := G1 n x5 0 1 h5
    rw [Nat.mul_one, Nat.zero_add] at h
    refine Eq.trans (Finset.sum_congr rfl (fun x6 _ => ?_)) h
    split_ifs <;> omega
  · rw [if_neg hP]
    refine Finset.sum_eq_zero (fun x6 _ => ?_)
    split_ifs <;> omega

theorem L5 (n x1 x2 x3 x4 : ℕ) (h4 : x4 ≤ n) :
    ∑ x5 ∈ Finset.range (n + 1),
        (if x1 ≠ 0 ∧ (x1 ≠ x2 ∨ x2 ≠ x3) ∧ (x2 ≠ x3 ∨ x3 ≠ x4) ∧ (x3 ≠ x4 ∨ x4 ≠ x5) then n
          else 0) =
      if x1 ≠ 0 ∧ (x1 ≠ x2 ∨ x2 ≠ x3) ∧ (x2 ≠ x3 ∨ x3 ≠ x4) then
        (if x3 = x4 then 0 else n) + n * n else 0 := by
  by_cases hP : x1 ≠ 0 ∧ (x1 ≠ x2 ∨ x2 ≠ x3) ∧ (x2 ≠ x3 ∨ x3 ≠ x4)
  · rw [if_pos hP]
    refine Eq.trans (Finset.sum_congr rfl (fun x5 _ => ?_))
      (G1 n x4 (if x3 = x4 then 0 else n) n h4)
    split_ifs <;> omega
  · rw [if_neg hP]
    refine Finset.sum_eq_zero (fun x5 _ => ?_)
    split_ifs <;> omega

theorem L4 (n x1 x2 x3 : ℕ) (h3 : x3 ≤ n) :
    ∑ x4 ∈ Finset.range (n + 1),
        (if x1 ≠ 0 ∧ (x1 ≠ x2 ∨ x2 ≠ x3) ∧ (x2 ≠ x3 ∨ x3 ≠ x4) then
          (if x3 = x4 then 0 else n) + n * n else 0) =
      if x1 ≠ 0 ∧ (x1 ≠ x2 ∨ x2 ≠ x3) then
        (if x2 = x3 then 0 else n * n) + n * (n + n * n) else 0 := by
  by_cases hP : x1 ≠ 0 ∧ (x1 ≠ x2 ∨ x2 ≠ x3)
  · rw [if_pos hP]
    refine Eq.trans (Finset.sum_congr rfl (fun x4 _ => ?_))
      (G1 n x3 (if x2 = x3 then 0 else n * n) (n + n * n) h3)
    split_ifs <;> omega
  · rw [if_neg hP]
    refine Finset.sum_eq_zero (fun x4 _ => ?_)
    split_ifs <;> omega

theorem L3 (n x1 x2 : ℕ) (h2 : x2 ≤ n) :
    ∑ x3 ∈ Finset.range (n + 1),
        (if x1 ≠ 0 ∧ (x1 ≠ x2 ∨ x2 ≠ x3) then
          (if x2 = x3 then 0 else n * n) + n * (n + n * n) else 0) =
      if x1 ≠ 0 then
        (if x1 = x2 then 0 else n * (n + n * n)) + n * (n * n + n * (n + n * n)) else 0 := by
  by_cases hP : x1 ≠ 0
  · rw [if_pos hP]
    refine Eq.trans (Finset.sum_congr rfl (fun x3 _ => ?_))
      (G1 n x2 (if x1 = x2 then 0 else n * (n + n * n)) (n * n + n * (n + n * n)) h2)
    split_ifs <;> omega
  · rw [if_neg hP]
    refine Finset.sum_eq_zero (fun x3 _ => ?_)
    split_ifs <;> omega

theorem L2 (n x1 : ℕ) (h1 : x1 ≤ n) :
    ∑ x2 ∈ Finset.range (n + 1),
        (if x1 ≠ 0 then
          (if x1 = x2 then 0 else n * (n + n * n)) + n * (n * n + n * (n + n * n)) else 0) =
      if x1 ≠ 0 then
        (0 + n * (n * n + n * (n + n * n))) +
          n * (n * (n + n * n) + n * (n * n + n * (n + n * n))) else 0 := by
  by_cases hP : x1 ≠ 0
  · rw [if_pos hP]
    refine Eq.trans (Finset.sum_congr rfl (fun x2 _ => ?_))
      (G1 n x1 (0 + n * (n * n + n * (n + n * n)))
        (n * (n + n * n) + n * (n * n + n * (n + n * n))) h1)
    split_ifs <;> omega
  · rw [if_neg hP]
    exact Finset.sum_eq_zero (fun x2 _ => if_neg hP)

theorem L1 (n K : ℕ) :
    ∑ x1 ∈ Finset.range (n + 1), (if x1 ≠ 0 then K else 0) = n * K := by
  have h := G1 n 0 0 K (Nat.zero_le n)
  rw [Nat.zero_add] at h
  refine Eq.trans (Finset.sum_congr rfl (fun x1 _ => ?_)) h
  split_ifs <;> omega

theorem a_sum (n : ℕ) : a n = ∑ x1 ∈ Finset.range (n + 1), ∑ x2 ∈ Finset.range (n + 1),
    ∑ x3 ∈ Finset.range (n + 1), ∑ x4 ∈ Finset.range (n + 1), ∑ x5 ∈ Finset.range (n + 1),
      ∑ x6 ∈ Finset.range (n + 1), (if ok 0 x1 x2 x3 x4 x5 x6 then 1 else 0) := by
  unfold a
  rw [Finset.card_filter]
  simp only [Finset.sum_product]

theorem a_cf (n : ℕ) : a n = n * ((0 + n * (n * n + n * (n + n * n))) +
    n * (n * (n + n * n) + n * (n * n + n * (n + n * n)))) := by
  rw [a_sum n]
  refine Eq.trans (Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ =>
    Finset.sum_congr rfl (fun x3 _ => Finset.sum_congr rfl (fun x4 _ =>
      Finset.sum_congr rfl (fun x5 h5 => L6 n x1 x2 x3 x4 x5 (bnd h5))))))) ?_
  refine Eq.trans (Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ =>
    Finset.sum_congr rfl (fun x3 _ => Finset.sum_congr rfl (fun x4 h4 =>
      L5 n x1 x2 x3 x4 (bnd h4)))))) ?_
  refine Eq.trans (Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 _ =>
    Finset.sum_congr rfl (fun x3 h3 => L4 n x1 x2 x3 (bnd h3))))) ?_
  refine Eq.trans (Finset.sum_congr rfl (fun x1 _ => Finset.sum_congr rfl (fun x2 h2 =>
    L3 n x1 x2 (bnd h2)))) ?_
  refine Eq.trans (Finset.sum_congr rfl (fun x1 h1 => L2 n x1 (bnd h1))) ?_
  exact L1 n _

theorem a_q (n : ℕ) : (a n : ℚ) = (n : ℚ) ^ 6 + 4 * (n : ℚ) ^ 5 + 3 * (n : ℚ) ^ 4 := by
  rw [a_cf n]
  push_cast
  ring

theorem a_z (n : ℕ) : (a n : ℤ) = (n : ℤ) ^ 6 + 4 * (n : ℤ) ^ 5 + 3 * (n : ℤ) ^ 4 := by
  rw [a_cf n]
  push_cast
  ring

end R06A221466

open OMA.S_oeis_a221466 R06A221466 in
theorem OMA.solution : type_of% @OMA.S_oeis_a221466.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    rw [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega,
      show k + 8 - 3 = k + 5 by omega, show k + 8 - 4 = k + 4 by omega,
      show k + 8 - 5 = k + 3 by omega, show k + 8 - 6 = k + 2 by omega,
      show k + 8 - 7 = k + 1 by omega,
      a_z (k + 8), a_z (k + 7), a_z (k + 6), a_z (k + 5), a_z (k + 4), a_z (k + 3),
      a_z (k + 2), a_z (k + 1)]
    push_cast
    ring
  · obtain ⟨A, hA⟩ : ∃ A : PowerSeries ℚ, A = PowerSeries.mk (fun n => (a n : ℚ)) :=
      ⟨_, rfl⟩
    rw [← hA]
    have cA : ∀ n, PowerSeries.coeff n A =
        (n : ℚ) ^ 6 + 4 * (n : ℚ) ^ 5 + 3 * (n : ℚ) ^ 4 := by
      intro n
      rw [hA, PowerSeries.coeff_mk, a_q n]
    have k7 : (PowerSeries.C (7 : ℚ) : PowerSeries ℚ) = 7 := map_ofNat _ 7
    have k8 : (PowerSeries.C (8 : ℚ) : PowerSeries ℚ) = 8 := map_ofNat _ 8
    have k16 : (PowerSeries.C (16 : ℚ) : PowerSeries ℚ) = 16 := map_ofNat _ 16
    have k21 : (PowerSeries.C (21 : ℚ) : PowerSeries ℚ) = 21 := map_ofNat _ 21
    have k35 : (PowerSeries.C (35 : ℚ) : PowerSeries ℚ) = 35 := map_ofNat _ 35
    have k112 : (PowerSeries.C (112 : ℚ) : PowerSeries ℚ) = 112 := map_ofNat _ 112
    have k184 : (PowerSeries.C (184 : ℚ) : PowerSeries ℚ) = 184 := map_ofNat _ 184
    have k432 : (PowerSeries.C (432 : ℚ) : PowerSeries ℚ) = 432 := map_ofNat _ 432
    have e : A * (1 - PowerSeries.X) ^ 7 =
        A - A * PowerSeries.X ^ 1 * PowerSeries.C (7 : ℚ) +
          A * PowerSeries.X ^ 2 * PowerSeries.C (21 : ℚ) -
          A * PowerSeries.X ^ 3 * PowerSeries.C (35 : ℚ) +
          A * PowerSeries.X ^ 4 * PowerSeries.C (35 : ℚ) -
          A * PowerSeries.X ^ 5 * PowerSeries.C (21 : ℚ) +
          A * PowerSeries.X ^ 6 * PowerSeries.C (7 : ℚ) - A * PowerSeries.X ^ 7 := by
      rw [k7, k21, k35]
      ring
    have e2 : (8 * PowerSeries.X * (1 + 23 * PowerSeries.X + 54 * PowerSeries.X ^ 2 +
        14 * PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 4) : PowerSeries ℚ) =
        PowerSeries.X ^ 1 * PowerSeries.C (8 : ℚ) + PowerSeries.X ^ 2 * PowerSeries.C (184 : ℚ) +
          PowerSeries.X ^ 3 * PowerSeries.C (432 : ℚ) +
          PowerSeries.X ^ 4 * PowerSeries.C (112 : ℚ) -
          PowerSeries.X ^ 5 * PowerSeries.C (16 : ℚ) := by
      rw [k8, k184, k432, k112, k16]
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 8 with hm | hm
    · interval_cases m <;> norm_num [cA]
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 8 := ⟨m - 8, by omega⟩
      rw [if_pos (show 1 ≤ j + 8 by omega), if_pos (show 2 ≤ j + 8 by omega),
        if_pos (show 3 ≤ j + 8 by omega), if_pos (show 4 ≤ j + 8 by omega),
        if_pos (show 5 ≤ j + 8 by omega), if_pos (show 6 ≤ j + 8 by omega),
        if_pos (show 7 ≤ j + 8 by omega),
        if_neg (show ¬ (j + 8 = 1) by omega), if_neg (show ¬ (j + 8 = 2) by omega),
        if_neg (show ¬ (j + 8 = 3) by omega), if_neg (show ¬ (j + 8 = 4) by omega),
        if_neg (show ¬ (j + 8 = 5) by omega),
        show j + 8 - 1 = j + 7 by omega, show j + 8 - 2 = j + 6 by omega,
        show j + 8 - 3 = j + 5 by omega, show j + 8 - 4 = j + 4 by omega,
        show j + 8 - 5 = j + 3 by omega, show j + 8 - 6 = j + 2 by omega,
        show j + 8 - 7 = j + 1 by omega,
        cA (j + 8), cA (j + 7), cA (j + 6), cA (j + 5), cA (j + 4), cA (j + 3), cA (j + 2),
        cA (j + 1)]
      push_cast
      ring
