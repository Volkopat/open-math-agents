import OMAStatements.S_mo_293821
import Mathlib

-- Problem: mo-293821, the recursion a(n) = a(2^k - n) + k (n - 2^(k-1)) for 2^(k-1) < n <= 2^k
-- with a(0) = a(1) = 0 counts the 1's in the binary expansions of 0, ..., n - 1.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Write s(i) for the binary digit sum and S(n) for the sum of s(i) over i < n. Complementing
-- the k lowest bits gives s(i) + s(2^k - 1 - i) = k for i < 2^k. Summing over i < 2^k gives
-- 2 S(2^k) = k 2^k, and summing over i < m = 2^k - n gives
-- S(2^k) - S(n) = k m - S(m). Hence S(n) = S(2^k - n) + k (n - 2^(k-1)), the same recursion,
-- and a = S by strong induction.

theorem OMA.solution : type_of% @OMA.S_mo_293821.main := by
  intro a ha0 ha1 _ hrec
  have L1 : ∀ i : ℕ, (Nat.digits 2 i).sum = i % 2 + (Nat.digits 2 (i / 2)).sum := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · rw [Nat.digits_def' (by norm_num) hi, List.sum_cons]
  have L2 : ∀ k : ℕ, ∀ i : ℕ, i < 2 ^ k →
      (Nat.digits 2 i).sum + (Nat.digits 2 (2 ^ k - 1 - i)).sum = k := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      simp
    | succ k ih =>
      intro i hi
      have hP : 0 < 2 ^ k := pow_pos (by norm_num) k
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [hpow] at hi ⊢
      have h1 := L1 i
      have h2 := L1 (2 * 2 ^ k - 1 - i)
      have h3 : (2 * 2 ^ k - 1 - i) % 2 = 1 - i % 2 := by omega
      have h4 : (2 * 2 ^ k - 1 - i) / 2 = 2 ^ k - 1 - i / 2 := by omega
      have h5 := ih (i / 2) (by omega)
      rw [h3, h4] at h2
      have h6 : i % 2 ≤ 1 := by omega
      omega
  have L3 : ∀ k m : ℕ, m ≤ 2 ^ k →
      ∑ i ∈ Finset.range m, (Nat.digits 2 i).sum +
        ∑ i ∈ Finset.range m, (Nat.digits 2 (2 ^ k - 1 - i)).sum = k * m := by
    intro k m hm
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl
        (fun i hi => L2 k i (lt_of_lt_of_le (Finset.mem_range.mp hi) hm))]
    simp [mul_comm]
  have hpow2 : ∀ k : ℕ, 1 ≤ k → 2 ^ k = 2 * 2 ^ (k - 1) := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp [pow_succ, mul_comm]
  have hS : ∀ k n : ℕ, 1 ≤ k → 2 ^ (k - 1) < n → n ≤ 2 ^ k →
      ∑ i ∈ Finset.range n, (Nat.digits 2 i).sum =
        ∑ i ∈ Finset.range (2 ^ k - n), (Nat.digits 2 i).sum + k * (n - 2 ^ (k - 1)) := by
    intro k n hk hlt hle
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ k = n + m := ⟨2 ^ k - n, by omega⟩
    have hsub : 2 ^ k - n = m := by omega
    rw [hsub]
    have hpow := hpow2 k hk
    have hrefl : ∑ j ∈ Finset.range (2 ^ k), (Nat.digits 2 (2 ^ k - 1 - j)).sum =
        ∑ j ∈ Finset.range (2 ^ k), (Nat.digits 2 j).sum :=
      Finset.sum_range_reflect (fun i => (Nat.digits 2 i).sum) (2 ^ k)
    have htot := L3 k (2 ^ k) le_rfl
    rw [hrefl] at htot
    have hC : ∑ i ∈ Finset.range (2 ^ k), (Nat.digits 2 i).sum =
        ∑ i ∈ Finset.range n, (Nat.digits 2 i).sum +
          ∑ j ∈ Finset.range m, (Nat.digits 2 (n + j)).sum := by
      rw [hm]
      exact Finset.sum_range_add (fun i => (Nat.digits 2 i).sum) n m
    have hrefl2 : ∑ j ∈ Finset.range m, (Nat.digits 2 (n + (m - 1 - j))).sum =
        ∑ j ∈ Finset.range m, (Nat.digits 2 (n + j)).sum :=
      Finset.sum_range_reflect (fun j => (Nat.digits 2 (n + j)).sum) m
    have hT : ∑ j ∈ Finset.range m, (Nat.digits 2 (n + j)).sum =
        ∑ j ∈ Finset.range m, (Nat.digits 2 (2 ^ k - 1 - j)).sum := by
      rw [← hrefl2]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hidx : n + (m - 1 - j) = 2 ^ k - 1 - j := by omega
      rw [hidx]
    have hB := L3 k m (by omega)
    obtain ⟨d, hd⟩ : ∃ d, n = 2 ^ (k - 1) + d := ⟨n - 2 ^ (k - 1), by omega⟩
    have hQ : 2 ^ (k - 1) = m + d := by omega
    have hnd : n - 2 ^ (k - 1) = d := by omega
    have hk2 : k * 2 ^ k = 2 * (k * m) + 2 * (k * d) := by
      rw [hpow, hQ]
      ring
    rw [hnd]
    linarith
  have key : ∀ n : ℕ, a n = ∑ i ∈ Finset.range n, (Nat.digits 2 i).sum := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.lt_or_ge n 2 with hn | hn
      · interval_cases n
        · simpa using ha0
        · simpa using ha1
      · have hex : ∃ k, n ≤ 2 ^ k := ⟨n, (Nat.lt_two_pow_self).le⟩
        obtain ⟨k, hk1, hk2⟩ : ∃ k, n ≤ 2 ^ k ∧ ∀ j < k, ¬ n ≤ 2 ^ j :=
          ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
        have hk0 : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with rfl | hpos
          · have h1 : n ≤ 1 := by simpa using hk1
            omega
          · exact hpos
        have hlt : 2 ^ (k - 1) < n := not_le.mp (hk2 (k - 1) (by omega))
        have hpow := hpow2 k hk0
        rw [hrec k n hk0 hlt hk1, ih (2 ^ k - n) (by omega), hS k n hk0 hlt hk1]
  intro n
  exact key (n + 1)
