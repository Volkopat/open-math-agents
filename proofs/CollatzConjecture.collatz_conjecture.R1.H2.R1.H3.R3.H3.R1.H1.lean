import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3_H3_R1

namespace BoundedCollatzDescent

open CollatzConjecture

private def next (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

private theorem next_iterate (n : ℕ) : ∃ k : ℕ, collatzStep^[k] n = next n := by
  by_cases hn : n % 2 = 0
  · exact ⟨1, by simp [next, hn, collatzStep, Nat.even_iff]⟩
  · have he : (3 * n + 1) % 2 = 0 := by omega
    exact ⟨2, by
      simp [next, hn, he, collatzStep, Nat.even_iff, Function.iterate_succ_apply]⟩

private def drops : ℕ → ℕ → ℕ → Bool
  | 0, x, n => decide (x < n)
  | k + 1, x, n => decide (x < n) || drops k (next x) n

private theorem drops_certifies (k x n : ℕ) (h : drops k x n = true) :
    ∃ i : ℕ, collatzStep^[i] x < n := by
  induction k generalizing x with
  | zero => exact ⟨0, of_decide_eq_true h⟩
  | succ k ih =>
    simp only [drops, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨j, hj⟩ := next_iterate x
      obtain ⟨i, hi⟩ := ih (next x) h
      exact ⟨i + j, by rwa [Function.iterate_add_apply, hj]⟩

private def residues : List ℕ :=
  [27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
    239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
    511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
    767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023]

private def checked (b q i : ℕ) : Bool :=
  let n := 1024 * (16 * b + q) + residues.getD i 0
  drops 164 n n

private def checkedBatch (b : ℕ) : Bool :=
  (List.range 16).all fun q => (List.range 64).all fun i => checked b q i

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check6 : checkedBatch 6 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check7 : checkedBatch 7 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check8 : checkedBatch 8 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check9 : checkedBatch 9 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check10 : checkedBatch 10 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check11 : checkedBatch 11 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check12 : checkedBatch 12 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check13 : checkedBatch 13 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check14 : checkedBatch 14 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check15 : checkedBatch 15 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check16 : checkedBatch 16 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check17 : checkedBatch 17 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check18 : checkedBatch 18 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check19 : checkedBatch 19 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check20 : checkedBatch 20 = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem check21 : checkedBatch 21 = true := by
  decide +kernel

private theorem checked_range (b : ℕ) (hb₁ : 6 ≤ b) (hb₂ : b ≤ 21)
    (q : Fin 16) (i : Fin 64) : checked b q.val i.val = true := by
  have h : checkedBatch b = true := by
    interval_cases b
    · exact check6
    · exact check7
    · exact check8
    · exact check9
    · exact check10
    · exact check11
    · exact check12
    · exact check13
    · exact check14
    · exact check15
    · exact check16
    · exact check17
    · exact check18
    · exact check19
    · exact check20
    · exact check21
  have hq := List.all_eq_true.mp h q.val (List.mem_range.mpr q.isLt)
  exact List.all_eq_true.mp hq i.val (List.mem_range.mpr i.isLt)

theorem descent (n : ℕ) (hn : 100000 ≤ n) (hN : n < 350000)
    (hr : n % 1024 ∈ residues) : ∃ i : ℕ, collatzStep^[i] n < n := by
  obtain ⟨i, hi, hval⟩ := List.getElem_of_mem hr
  have hi' : i < 64 := hi
  let q : Fin 16 := ⟨n / 1024 % 16, Nat.mod_lt _ (by decide)⟩
  have hq : 16 * (n / 1024 / 16) + q.val = n / 1024 := Nat.div_add_mod _ _
  have hsplit := Nat.div_add_mod n 1024
  have h := checked_range (n / 1024 / 16) (by omega) (by omega) q ⟨i, hi'⟩
  unfold checked at h
  change drops 164 (1024 * (16 * (n / 1024 / 16) + q.val) + residues.getD i 0)
    (1024 * (16 * (n / 1024 / 16) + q.val) + residues.getD i 0) = true at h
  rw [hq, List.getD_eq_getElem residues 0 hi, hval, hsplit] at h
  exact drops_certifies 164 n n h

end BoundedCollatzDescent

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R3_H3_R1.H1 :=
  BoundedCollatzDescent.descent