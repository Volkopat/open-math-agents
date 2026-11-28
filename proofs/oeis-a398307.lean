import OMAStatements.S_oeis_a398307
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Dedup

open OMA.S_oeis_a398307

private def observed : List ℕ :=
  [541, 577, 528, 593, 583, 609, 591, 578, 603, 594, 589, 575, 590, 597, 606, 605, 600, 608, 602, 611, 362, 276, 612, 633, 634, 620, 266, 619, 592, 623, 622, 596, 467, 414, 629, 268, 646, 152, 617, 631, 599, 645, 621, 649, 571, 308, 637, 651, 643, 640, 506, 630, 647, 657, 658, 653, 182, 664, 439, 435, 323, 161, 404, 642, 659, 671, 441, 673, 663, 676, 660, 677, 667, 668, 678, 681, 674, 675, 0, 669, 656, 688]

private def fixed (s : ℕ) : ℕ := observed[s]?.getD 0
private def frozenStep (n v : ℕ) : ℕ :=
  let m := fixed (digitSum v)
  if m = 0 then 0 else n-m

private def start : ℕ := 699999900
private def layers : ℕ → List ℕ
  | 0 => List.range' (start-689) 688
  | t+1 => ((layers t).map (frozenStep (start+t))).eraseDups

private def suppliedPrefix : List ℕ :=
  [0, 1, 0, 2, 0, 2, 2, 1, 6, 0, 5, 0, 2, 6, 5, 4, 0, 5, 3, 0, 3, 2, 9, 0, 4, 9, 3, 6, 14, 11, 8, 0, 8, 2, 12, 8, 3, 10, 30, 2, 6, 13, 17, 7, 0, 13, 21, 10, 40, 24, 9, 25, 8, 17, 1, 47, 26, 4, 33, 18, 9, 10, 7, 19, 2, 25, 3, 30, 1, 14, 52, 8, 19, 11, 9, 14, 58, 31, 20, 14, 62, 9, 7, 20, 19, 23, 68, 7, 5, 71, 18, 9, 10, 24, 53, 23, 7, 9, 6, 58, 54, 3, 35, 31, 46, 12, 4, 49, 62, 37, 17, 39, 6, 14, 25, 18, 18, 19, 25, 22, 13, 14, 33, 10, 55, 1, 57, 21, 26, 57, 24, 18, 34, 36, 36, 37, 12, 35, 66, 2, 75, 4, 35, 71, 72, 47, 72, 49, 27, 51, 37, 27, 54, 55, 30, 53, 84, 20, 18, 61, 63, 63, 64, 39, 27, 67, 45, 69, 0, 124, 73, 47, 98, 62, 102, 73, 52, 80, 106, 82, 56, 107, 110, 43, 87, 0, 17, 115, 91, 65, 116, 119, 118, 69, 0, 9, 98, 10, 72, 3, 98, 14, 113, 114, 91, 7, 109, 9, 12, 9, 2, 71, 140, 124, 8, 143, 1, 91, 20, 8, 5, 132, 109, 25, 18, 15, 113, 6, 115, 23, 9, 21, 32, 12, 34, 29, 162, 6, 10, 22, 98, 54, 11, 32, 23, 24, 8, 27, 17, 2, 39, 17, 5, 32, 1, 38, 13, 115, 52, 53, 13, 119, 19, 24, 26, 18, 35, 20, 18, 38, 27, 40, 130, 131, 21, 75, 42, 39, 44, 32, 27, 50, 29, 40, 142, 79, 0, 92, 45, 58, 29, 48, 58, 32, 41, 42, 58, 36, 67, 38, 57, 67, 41, 50, 51, 67, 45, 76, 47, 66, 76, 50, 59, 111, 114, 77, 114, 79, 0, 32, 67, 60, 84, 89, 72, 94, 65, 84, 94, 68, 128, 88, 0, 14, 81, 104, 83, 94, 77, 5, 87, 115, 136, 104, 4, 203, 6, 109, 109, 110, 100, 96, 126, 122, 14, 15, 9, 126, 1, 104, 20, 111, 162, 6, 17, 118, 127, 128, 125, 122, 30, 171, 15, 9, 17, 128, 133, 171, 4, 34, 174, 147, 148, 122, 44, 138, 152, 140, 48, 155, 147, 157, 131, 53, 147, 161, 149, 42, 34, 193, 139, 140, 62, 156, 170, 158, 51, 43, 202, 30, 210, 211, 33, 49, 153, 41, 76, 156, 184, 158, 65, 178, 0, 90, 50, 85, 165, 193, 167, 74, 187, 0, 9, 59, 79, 0, 4, 58, 177, 66, 206, 194, 87, 70, 238, 184, 185, 92, 205, 243, 17, 204, 88, 0, 18, 22, 19, 218, 215, 212, 120, 261, 29, 220, 27, 32, 126, 34, 262, 230, 130, 34, 266, 118, 235, 236, 233, 230, 138, 245, 237, 247, 221, 143, 237, 251, 239, 132, 124, 283, 229, 230, 152, 246, 260, 248, 141, 133, 292, 238, 239, 146, 259, 0, 50, 165, 272, 264, 274, 248, 155, 268, 0, 9, 81, 1, 157, 256, 257, 164, 277, 0, 9, 9, 1, 9, 2, 277, 0, 7, 324, 5, 192, 299, 173, 292, 275, 182, 295, 0, 11, 14, 10, 18, 18, 19, 3, 347, 6, 185, 8, 304, 22, 116, 3, 8, 5, 25, 28, 16, 30, 6, 13, 126, 38, 24, 4, 130, 1, 44, 14, 14, 15, 11, 47, 1, 7, 47, 4, 12, 25, 4, 3, 28, 41, 28, 43, 10, 12, 6, 28, 3, 9, 67, 31, 13, 14, 40, 16, 22, 18, 8, 46, 15, 14, 48, 17, 5, 51, 19, 22, 29, 38, 39, 25, 38, 42, 27, 25, 42, 30, 29, 48, 34, 47, 51, 36, 34, 51, 39, 41, 23, 24, 43, 57, 46, 48, 48, 49, 43, 63, 48, 53, 41, 36, 52, 69, 43, 71, 47, 76, 55, 64, 65, 80, 53, 54, 64, 70, 82, 72, 68, 57, 74, 90, 72, 73, 79, 69, 65, 96, 67, 76, 77, 69, 71, 74, 103, 96, 75, 91, 93, 93, 94, 88, 86, 81, 94, 92, 115, 113, 83, 118, 105, 104, 87, 92, 123, 108, 106, 123, 111, 110, 176, 99, 104, 98, 100, 132, 119, 136, 123, 122, 105, 124, 138, 127, 129, 129, 130, 138, 132, 132, 133, 147, 136, 138, 138, 139, 133, 153, 138, 143, 131, 126, 142, 159, 133, 161, 137, 166, 145, 154, 155, 170, 143, 144, 154, 160, 172, 162, 158, 147, 164, 180, 162, 163, 169, 159, 155, 186, 157, 166, 167, 159, 161, 164, 193, 172, 181, 182, 197, 165, 184, 178, 176, 171, 184, 182, 205, 203, 173, 208, 195, 180, 192, 197, 180, 195, 185, 185, 186, 188, 186, 190, 207, 203, 189, 197, 192, 211, 219, 213, 213, 214, 228, 217, 219, 219, 220, 228, 222, 222, 223, 237, 226, 228, 228, 229, 223, 243, 228, 233, 221, 216, 232, 249, 223, 251, 227, 256, 235, 244, 245, 260, 233, 234, 244, 250, 262, 252, 248, 237, 254, 270, 252, 253, 259, 249, 245, 276, 247, 256, 257, 249, 251, 254, 283, 262, 271, 272, 287, 255, 274, 268, 266, 261, 274, 272, 295, 271, 283, 276, 269, 267, 271, 288, 276, 274, 283, 284, 276, 278, 276, 280, 297, 285, 283, 292, 293, 285, 287, 285, 289, 284, 290, 322, 320, 290, 325, 312, 311, 294, 299, 543, 316, 318, 318, 319, 313, 333, 318, 323, 311, 306, 322, 339, 313, 341, 317, 346, 325, 334, 335, 350, 323, 324, 334, 340, 352, 342, 338, 327, 344, 360, 342, 343, 349, 339, 335, 366, 337, 346, 347, 339, 341, 344, 373, 352, 361, 362, 377, 345, 364, 358, 356, 351, 364, 362, 385, 361, 373, 366, 359, 357, 361, 378, 366, 364, 373, 374, 366, 368, 366, 370, 387, 375, 373, 382, 383, 375, 377, 375, 379, 374, 380, 412, 410, 380, 415, 402, 401, 384, 389, 633, 406, 408, 408, 409]

/-- Check each proposed next term against the complete preceding history. -/
private def prefixCheck : List ℕ → ℕ → ℕ → List (ℕ × ℕ) → Bool
  | [], _, v, h =>
    (v == 409) && (List.range 82).all (fun s => lookup s h == fixed s)
  | w::ws, n, v, h =>
    (w == (step n ⟨v,h⟩).value) && prefixCheck ws (n+1) w ((v,n)::h)

private theorem prefix_sound (xs : List ℕ) (n v : ℕ) (h : List (ℕ × ℕ))
    (hn : n ≠ 0) (hs : state n = ⟨v,h⟩) (hc : prefixCheck xs n v h = true) :
    (state (n+xs.length)).value = 409 ∧
    ∀ s : Fin 82, lookup s.val (state (n+xs.length)).history = fixed s.val := by
  induction xs generalizing n v h with
  | nil =>
    simp only [prefixCheck,Bool.and_eq_true,beq_iff_eq] at hc
    simp only [List.length_nil,Nat.add_zero,hs]
    exact ⟨hc.1, fun s => beq_iff_eq.mp (List.all_eq_true.mp hc.2 s.val (List.mem_range.mpr s.isLt))⟩
  | cons w ws ih =>
    simp only [prefixCheck,Bool.and_eq_true,beq_iff_eq] at hc
    have hnext : state (n+1) = ⟨w,(v,n)::h⟩ := by
      rw [state, if_neg hn, hs, hc.1]
      rfl
    have hres := ih (n+1) w ((v,n)::h) (by omega) hnext hc.2
    rwa [show n + (w::ws).length = (n+1)+ws.length by simp; omega]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 14000000 in
private theorem prefix_checked : prefixCheck suppliedPrefix 1 0 [] = true := by decide +kernel

set_option maxRecDepth 32000 in
private theorem at_prefix : (state 1000).value = 409 ∧
    ∀ s : Fin 82, lookup s.val (state 1000).history = fixed s.val := by
  have h := prefix_sound suppliedPrefix 1 0 [] (by decide) (by rfl) prefix_checked
  have hlen : suppliedPrefix.length = 999 := by decide +kernel
  simpa only [hlen] using h

private theorem largest_lookup : ∀ s : Fin 82, fixed s.val ≤ 688 := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
private theorem terminal : layers 542 = [0] := by decide +kernel
private theorem digits_correct (fuel v : ℕ) (hv : v ≤ fuel) :
    sumAux fuel v = (Nat.digits 10 v).sum := by
  induction fuel generalizing v with
  | zero =>
    have hz : v = 0 := by omega
    simp [hz,sumAux]
  | succ i ih =>
    by_cases h : v = 0
    · simp [h,sumAux]
    · rw [sumAux, if_neg h, Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 10) (Nat.pos_of_ne_zero h)]
      simp only [List.sum_cons, Nat.add_left_cancel_iff]
      exact ih _ (by have := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide : 1 < 10); omega)

/-- The executable digit sum in the source statement agrees with Mathlib's decimal expansion. -/
theorem A398307_digitSum_correct (v : ℕ) : digitSum v = (Nat.digits 10 v).sum :=
  digits_correct v v le_rfl

private theorem list_sum_bound (l : List ℕ) (h : ∀ d ∈ l, d ≤ 9) : l.sum ≤ 9*l.length := by
  induction l with
  | nil => simp
  | cons d l ih =>
    have hd := h d (by simp)
    have ht := ih (fun e he => h e (by simp [he]))
    simp only [List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

private theorem key_small {v : ℕ} (hv : v < 1000000000) : digitSum v ≤ 81 := by
  rw [A398307_digitSum_correct]
  have hd := list_sum_bound (Nat.digits 10 v) (fun d hd => by
    have := Nat.digits_lt_base (by decide : 1 < 10) hd
    omega)
  have hl : (Nat.digits 10 v).length ≤ 9 := (Nat.digits_length_le_iff (by decide : 1 < 10) v).mpr hv
  omega

private theorem state_succ {n : ℕ} (hn : n ≠ 0) : state (n+1) = step n (state n) := by
  rw [state, if_neg hn]

private theorem bound {n : ℕ} (h : 2 ≤ n) : (state n).value ≤ n-2 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [state_succ (by omega : j ≠ 0)]
  simp only [step]
  split <;> omega

private def Stable (n : ℕ) : Prop :=
  81 < (state n).value ∧ n-689 ≤ (state n).value ∧
  ∀ s : Fin 82, lookup s.val (state n).history = fixed s.val

private theorem at_start : Stable 1000 := by
  obtain ⟨hv,hm⟩ := at_prefix
  exact ⟨by omega,by omega,hm⟩

private theorem next_frozen {n : ℕ} (hlo : 1000 ≤ n) (hhi : n ≤ 700000442) (hs : Stable n) :
    (state (n+1)).value = frozenStep n (state n).value := by
  have hbound := bound (n := n) (by omega)
  have hkey := key_small (v := (state n).value) (by omega)
  have hmem := hs.2.2 ⟨digitSum (state n).value,by omega⟩
  rw [state_succ (by omega)]
  simp only [step,frozenStep]
  exact congrArg (fun m => if m = 0 then 0 else n-m) hmem

private theorem advance {n : ℕ} (hlo : 1000 ≤ n) (hhi : n ≤ 700000442)
    (hs : Stable n) (hnz : (state (n+1)).value ≠ 0) : Stable (n+1) := by
  have ht := next_frozen hlo hhi hs
  have hbound := bound (n := n) (by omega)
  have hkey := key_small (v := (state n).value) (by omega)
  have hm := largest_lookup ⟨digitSum (state n).value,by omega⟩
  change fixed (digitSum (state n).value) ≤ 688 at hm
  change (state (n+1)).value = (if fixed (digitSum (state n).value) = 0 then 0 else n-fixed (digitSum (state n).value)) at ht
  split at ht
  · contradiction
  · refine ⟨by omega, by omega, ?_⟩
    intro s
    rw [state_succ (by omega)]
    simp only [step,lookup]
    rw [if_neg (by have := hs.1; have := s.isLt; omega : s.val ≠ (state n).value)]
    exact hs.2.2 s

private theorem propagate (val : ℕ → ℕ)
    (hlow : start-689 ≤ val start) (hupp : val start ≤ start-2)
    (htrans : ∀ t : ℕ, t < 542 → val (start+t+1) = frozenStep (start+t) (val (start+t))) :
    val (start+542) = 0 := by
  have stay : ∀ t : ℕ, t ≤ 542 → val (start+t) ∈ layers t := by
    intro t
    induction t with
    | zero =>
      intro _
      change val start ∈ List.range' (start-689) 688
      apply List.mem_range'.mpr
      exact ⟨val start - (start-689),by unfold start at *; omega, by unfold start at *; omega⟩
    | succ t ih =>
      intro ht
      rw [show start+(t+1) = (start+t)+1 by omega, htrans t (by omega)]
      apply List.mem_eraseDups.mpr
      exact List.mem_map_of_mem (ih (by omega))
  have hfinal := stay 542 (by decide)
  rw [terminal, List.mem_singleton] at hfinal
  exact hfinal

/-- The finite certificate implies a zero after the last index in the proposed list. -/
theorem A398307_additional_zero : ∃ n : ℕ, 541 < n ∧ n ≤ 700000442 ∧ (state n).value = 0 := by
  by_contra! hnz
  have stable_all : ∀ n : ℕ, 1000 ≤ n → n ≤ 700000442 → Stable n := by
    intro n hlo
    induction n, hlo using Nat.le_induction with
    | base => intro _; exact at_start
    | succ j hj ih =>
      intro hhi
      exact advance hj (by omega) (ih (by omega)) (hnz _ (by omega) hhi)
  have hs0 := stable_all start (by decide) (by decide)
  have hfinal := propagate (fun n => (state n).value) hs0.2.1
    (bound (n := start) (by decide)) (by
      intro t ht
      have hlo : 1000 ≤ start+t := by unfold start; omega
      have hhi : start+t ≤ 700000442 := by unfold start; omega
      exact next_frozen hlo hhi (stable_all _ hlo hhi))
  exact (hnz (start+542) (by decide) (by decide)) hfinal

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a398307.main) := by
  intro h
  obtain ⟨n,hn,_,hv⟩ := A398307_additional_zero
  have hm : n ∈ claimed := h ▸ (show n ∈ {j : ℕ | 0 < j ∧ (state j).value = 0} from ⟨by omega,hv⟩)
  simp only [claimed, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  omega
