import OMAStatements.S_oeis_a132089

-- Problem: A132089: Triangle T, read by rows, equal to the matrix square of Losanitsch's triangle (A034851).
-- Upstream: formal-conjectures statements/oeis-a132089.lean:0 (declaration OMA.S_oeis_a132089.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: L(k, 0) = (1 + 1) / 2 = 1 for every k, so (A * L)(i, 0) is the i-th row sum of A
-- for A = L and A = L^m. The row sum of L is (2^n + S(n)) / 2 with S(n) the sum of
-- C(n mod 2, j mod 2) * C(n/2, j/2) over j = 0..n; grouping j = 2i, 2i+1 gives S(n) = 2^ceil(n/2),
-- and (2^n + 2^ceil(n/2)) / 2 = 2^(n-1) + 2^(floor((n+1)/2) - 1) = A005418(n+1).

namespace K04A132089

open OMA.S_oeis_a132089

theorem L_col0 (k : ℕ) : L k 0 = 1 := by
  rw [L, Nat.choose_zero_right, Nat.zero_mod, Nat.choose_zero_right, Nat.zero_div,
    Nat.choose_zero_right]
  norm_num

theorem Lpow_succ (m i j : ℕ) :
    Lpow (m + 1) i j = ∑ k ∈ Finset.range (i + 1), Lpow m i k * L k j := rfl

theorem part_col (n : ℕ) : T n 0 = ∑ j ∈ Finset.range (n + 1), L n j := by
  unfold T
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [L_col0, mul_one]

theorem part_pow (m i : ℕ) :
    Lpow (m + 1) i 0 = ∑ j ∈ Finset.range (i + 1), Lpow m i j := by
  rw [Lpow_succ]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [L_col0, mul_one]

theorem sum_pairs (f : ℕ → ℕ) (m : ℕ) :
    ∑ j ∈ Finset.range (2 * m + 1 + 1), f j =
      ∑ i ∈ Finset.range (m + 1), (f (2 * i) + f (2 * i + 1)) := by
  induction m with
  | zero => simp [Finset.sum_range_succ]
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 + 1 = 2 * k + 1 + 1 + 1 + 1 by ring,
      Finset.sum_range_succ f (2 * k + 1 + 1 + 1), Finset.sum_range_succ f (2 * k + 1 + 1), ih,
      Finset.sum_range_succ _ (k + 1)]
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    ring

theorem B_sum (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), Nat.choose (n % 2) (j % 2) * Nat.choose (n / 2) (j / 2) =
      2 ^ ((n + 1) / 2) := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
  · have e1 : 2 * m % 2 = 0 := by omega
    have e2 : 2 * m / 2 = m := by omega
    have e3 : (2 * m + 1) / 2 = m := by omega
    rw [e1, e2, e3]
    have hp : ∑ j ∈ Finset.range (2 * m + 1 + 1), Nat.choose 0 (j % 2) * Nat.choose m (j / 2) =
        ∑ i ∈ Finset.range (m + 1), (Nat.choose 0 (2 * i % 2) * Nat.choose m (2 * i / 2) +
          Nat.choose 0 ((2 * i + 1) % 2) * Nat.choose m ((2 * i + 1) / 2)) :=
      sum_pairs (fun j => Nat.choose 0 (j % 2) * Nat.choose m (j / 2)) m
    have hs : ∑ j ∈ Finset.range (2 * m + 1 + 1), Nat.choose 0 (j % 2) * Nat.choose m (j / 2) =
        ∑ j ∈ Finset.range (2 * m + 1), Nat.choose 0 (j % 2) * Nat.choose m (j / 2) +
          Nat.choose 0 ((2 * m + 1) % 2) * Nat.choose m ((2 * m + 1) / 2) :=
      Finset.sum_range_succ _ _
    have hl : Nat.choose 0 ((2 * m + 1) % 2) * Nat.choose m ((2 * m + 1) / 2) = 0 := by
      rw [show (2 * m + 1) % 2 = 1 by omega, Nat.choose_eq_zero_of_lt (show 0 < 1 by norm_num),
        zero_mul]
    rw [hl, add_zero] at hs
    rw [← hs, hp, ← Nat.sum_range_choose m]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [show 2 * i % 2 = 0 by omega, show 2 * i / 2 = i by omega,
      show (2 * i + 1) % 2 = 1 by omega, Nat.choose_zero_right,
      Nat.choose_eq_zero_of_lt (show 0 < 1 by norm_num)]
    ring
  · have e1 : (2 * m + 1) % 2 = 1 := by omega
    have e2 : (2 * m + 1) / 2 = m := by omega
    have e3 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    rw [e1, e2, e3]
    have hp : ∑ j ∈ Finset.range (2 * m + 1 + 1), Nat.choose 1 (j % 2) * Nat.choose m (j / 2) =
        ∑ i ∈ Finset.range (m + 1), (Nat.choose 1 (2 * i % 2) * Nat.choose m (2 * i / 2) +
          Nat.choose 1 ((2 * i + 1) % 2) * Nat.choose m ((2 * i + 1) / 2)) :=
      sum_pairs (fun j => Nat.choose 1 (j % 2) * Nat.choose m (j / 2)) m
    rw [hp, pow_succ, ← Nat.sum_range_choose m, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [show 2 * i % 2 = 0 by omega, show 2 * i / 2 = i by omega,
      show (2 * i + 1) % 2 = 1 by omega, show (2 * i + 1) / 2 = i by omega,
      Nat.choose_zero_right, Nat.choose_one_right]
    ring

theorem rowsum_nat (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
        (Nat.choose n j + Nat.choose (n % 2) (j % 2) * Nat.choose (n / 2) (j / 2)) =
      2 ^ n + 2 ^ ((n + 1) / 2) := by
  rw [Finset.sum_add_distrib, Nat.sum_range_choose, B_sum n]

theorem rowsum (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), L n j = ((2 ^ n + 2 ^ ((n + 1) / 2) : ℕ) : ℚ) / 2 := by
  unfold L
  rw [← Finset.sum_div, ← Nat.cast_sum, rowsum_nat n]

theorem zpow_aux (c : ℕ) : (2 : ℚ) ^ ((c : ℤ) - 1) = (2 : ℚ) ^ c / 2 := by
  rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast, zpow_one]

theorem part_a005418 (n : ℕ) : ∑ j ∈ Finset.range (n + 1), L n j = A005418 (n + 1) := by
  rw [rowsum n, A005418]
  have h1 : ((n + 1 : ℕ) : ℤ) - 2 = (n : ℤ) - 1 := by omega
  rw [h1, zpow_aux n, zpow_aux ((n + 1) / 2)]
  push_cast
  ring

end K04A132089

open OMA.S_oeis_a132089 K04A132089 in
theorem OMA.solution : type_of% @OMA.S_oeis_a132089.main := by
  exact ⟨part_col, part_a005418, part_pow⟩
