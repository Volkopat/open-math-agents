import OMAStatements.S_oeis_a255437

-- Problem: A255437: In positive integers: replace k^2 with the first k odd numbers.
-- Upstream: formal-conjectures statements/oeis-a255437.lean:0 (declaration OMA.S_oeis_a255437.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let K = 2n^2+2n, so that (2n+1)^2 = 2K+1. The blocks of 1, ..., (K+1)^2 have total
-- length L with 2L + (K+1) = 3(K+1)^2 (induction over k: between k^2 and (k+1)^2 there are 2k
-- blocks of length 1, and the block of (k+1)^2 has length k+1), and 2*A068722(n) + (K+1) is the
-- same number, so L = A068722(n). The last entry of the block of (K+1)^2 is 2K+1. Every earlier
-- entry is a non-square m (so m is not (2n+1)^2) or an odd number 2j+1 with j < K.

namespace S08A255437

open OMA.S_oeis_a255437

theorem pre_succ (M : ℕ) : pre (M + 1) = pre M ++ blk (M + 1) := by
  unfold pre
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem blk_sq (k : ℕ) : blk (k * k) = (List.range k).map (fun j => 2 * j + 1) := by
  unfold blk
  rw [Nat.sqrt_eq]
  exact if_pos rfl

theorem blk_ns (k j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ k + k) : blk (k * k + j) = [k * k + j] := by
  unfold blk
  rw [Nat.sqrt_add_eq k hj2]
  exact if_neg (by omega)

theorem blk_len_pos (m : ℕ) (hm : 1 ≤ m) : 1 ≤ (blk m).length := by
  unfold blk
  split_ifs
  · rw [List.length_map, List.length_range]
    have := Nat.sqrt_pos.mpr (show 0 < m by omega)
    omega
  · simp

theorem len_ge (M : ℕ) : M ≤ (pre M).length := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [pre_succ, List.length_append]
    have := blk_len_pos (M + 1) (by omega)
    omega

theorem len_le (M j : ℕ) : (pre M).length ≤ (pre (M + j)).length := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show M + (j + 1) = M + j + 1 by ring, pre_succ, List.length_append]
    omega

theorem getD_pre_add (M j t : ℕ) (ht : t < (pre M).length) :
    (pre (M + j)).getD t 0 = (pre M).getD t 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show M + (j + 1) = M + j + 1 by ring, pre_succ,
      List.getD_append _ _ _ _ (lt_of_lt_of_le ht (len_le M j)), ih]

theorem a_eq (i M : ℕ) (hi : 1 ≤ i) (hiM : i ≤ (pre M).length) :
    a i = (pre M).getD (i - 1) 0 := by
  unfold a
  rcases le_total i M with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    have := len_ge i
    rw [getD_pre_add i j (i - 1) (by omega)]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [getD_pre_add M j (M + j - 1) (by omega)]

theorem getD_mem (l : List ℕ) (t : ℕ) (ht : t < l.length) : l.getD t 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ ht]
  exact List.getElem_mem ht

theorem getD_single (x t : ℕ) (ht : t = 0) : [x].getD t 0 = x := by
  subst ht
  exact List.getD_cons_zero

theorem len_ns (k j : ℕ) (hj : j ≤ k + k) :
    (pre (k * k + j)).length = (pre (k * k)).length + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e1 : k * k + (j + 1) = k * k + j + 1 := by ring
    have h1 : (pre (k * k + (j + 1))).length = (pre (k * k + j)).length + 1 := by
      rw [e1, pre_succ, List.length_append, ← e1, blk_ns k (j + 1) (by omega) hj,
        List.length_singleton]
    have h3 := ih (by omega)
    omega

theorem len_sq (k : ℕ) : 2 * (pre (k * k)).length + k = 3 * (k * k) := by
  induction k with
  | zero => simp [pre]
  | succ k ih =>
    have e : (k + 1) * (k + 1) = k * k + (k + k) + 1 := by ring
    have h1 : (pre (k * k + (k + k) + 1)).length = (pre (k * k + (k + k))).length + (k + 1) := by
      rw [pre_succ, List.length_append, ← e, blk_sq, List.length_map, List.length_range]
    have h2 := len_ns k (k + k) le_rfl
    rw [e]
    omega

theorem mem_pre (M x : ℕ) (h : x ∈ pre M) : ∃ m, 1 ≤ m ∧ m ≤ M ∧ x ∈ blk m := by
  unfold pre at h
  rw [List.mem_flatMap] at h
  obtain ⟨i, hi, hx⟩ := h
  have hiM := List.mem_range.mp hi
  exact ⟨i + 1, by omega, by omega, hx⟩

theorem mem_blk (m x : ℕ) (h : x ∈ blk m) :
    (Nat.sqrt m * Nat.sqrt m = m ∧ ∃ j, j < Nat.sqrt m ∧ x = 2 * j + 1) ∨
    (Nat.sqrt m * Nat.sqrt m ≠ m ∧ x = m) := by
  unfold blk at h
  by_cases hs : Nat.sqrt m * Nat.sqrt m = m
  · rw [if_pos hs] at h
    left
    refine ⟨hs, ?_⟩
    simp only [List.mem_map, List.mem_range] at h
    obtain ⟨j, hj, hjx⟩ := h
    exact ⟨j, hj, hjx.symm⟩
  · rw [if_neg hs, List.mem_singleton] at h
    exact Or.inr ⟨hs, h⟩

theorem decomp (K : ℕ) : pre ((K + 1) * (K + 1)) =
    (pre (K * K + (K + K)) ++ (List.range K).map (fun j => 2 * j + 1)) ++ [2 * K + 1] := by
  rw [show (K + 1) * (K + 1) = K * K + (K + K) + 1 by ring, pre_succ,
    show K * K + (K + K) + 1 = (K + 1) * (K + 1) by ring, blk_sq, List.range_succ,
    List.map_append, List.map_singleton, List.append_assoc]

theorem noq (K r x : ℕ) (hr : r * r = 2 * K + 1)
    (hx : x ∈ pre (K * K + (K + K)) ++ (List.range K).map (fun j => 2 * j + 1)) :
    x ≠ 2 * K + 1 := by
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · obtain ⟨m, -, hm2, hxm⟩ := mem_pre _ x hx
    rcases mem_blk m x hxm with ⟨-, j, hj, hxj⟩ | ⟨hns, hxm'⟩
    · have hlt : Nat.sqrt m < K + 1 := Nat.sqrt_lt.mpr (by
        rw [show (K + 1) * (K + 1) = K * K + (K + K) + 1 by ring]
        omega)
      omega
    · intro hq
      apply hns
      rw [← hxm', hq, ← hr, Nat.sqrt_eq]
  · simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, hjx⟩ := hx
    omega

end S08A255437

open OMA.S_oeis_a255437 S08A255437 in
theorem OMA.solution : type_of% @OMA.S_oeis_a255437.main := by
  intro n
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * n * n + 2 * n := ⟨_, rfl⟩
  have hr : (2 * n + 1) * (2 * n + 1) = 2 * K + 1 := by
    rw [hK]
    ring
  have hq : (2 * n + 1) ^ 2 = 2 * K + 1 := by
    rw [hK]
    ring
  have hP : 2 * A068722 n + (K + 1) = 3 * ((K + 1) * (K + 1)) := by
    unfold A068722
    rw [hK]
    ring
  have hL := len_sq (K + 1)
  obtain ⟨X, hX⟩ : ∃ X : List ℕ,
      X = pre (K * K + (K + K)) ++ (List.range K).map (fun j => 2 * j + 1) := ⟨_, rfl⟩
  have hD : pre ((K + 1) * (K + 1)) = X ++ [2 * K + 1] := by
    rw [hX]
    exact decomp K
  have hXq : ∀ x ∈ X, x ≠ 2 * K + 1 := by
    intro x hx
    rw [hX] at hx
    exact noq K (2 * n + 1) x hr hx
  have hlen : (pre ((K + 1) * (K + 1))).length = X.length + 1 := by
    rw [hD, List.length_append, List.length_singleton]
  have hA : A068722 n = X.length + 1 := by omega
  rw [hq]
  refine ⟨?_, ?_⟩
  · rw [a_eq (A068722 n) ((K + 1) * (K + 1)) (by omega) (by omega), hD,
      List.getD_append_right X [2 * K + 1] 0 (A068722 n - 1) (by omega)]
    exact getD_single (2 * K + 1) (A068722 n - 1 - X.length) (by omega)
  · intro i hi1 hi2
    rw [a_eq i ((K + 1) * (K + 1)) hi1 (by omega), hD,
      List.getD_append X [2 * K + 1] 0 (i - 1) (by omega)]
    exact hXq _ (getD_mem X (i - 1) (by omega))
