import OMAReductions.R_Erdos436_erdos_436_variants_five_two_R1
import Mathlib

namespace OMA436

def P : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101]

def M : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

def G : List (List ℕ) := [[1], [], [5, 9, 24, 80], [6, 14, 20, 27, 35, 48, 49, 125, 224, 2400, 4374], [10, 11, 21, 32, 44, 54, 55, 98, 99, 120, 175, 242, 384, 440, 539, 3024], [12, 13, 25, 26, 39, 65, 77, 90, 104, 143, 168, 195, 324, 350, 351, 363, 624, 675, 728, 1000, 1715, 2079, 4224, 6655], [17, 34, 50, 51, 84, 119, 135, 153, 169, 220, 272, 288, 374, 441, 560, 594, 714, 832, 935, 1155, 1224, 1274, 1700, 2057, 2430, 2499, 2600, 4913, 5831], [18, 19, 38, 56, 75, 76, 95, 132, 152, 170, 189, 208, 209, 285, 323, 342, 360, 399, 455, 475, 494, 968, 1215, 1330, 1444, 1520, 1539, 1728, 2375, 2431, 2925, 3135, 3249, 4199, 5775, 5928, 5984, 6174, 6859], [22, 23, 45, 68, 69, 91, 114, 160, 161, 207, 230, 252, 275, 299, 322, 390, 391, 459, 483, 506, 528, 575, 735, 759, 874, 896, 1104, 1196, 1287, 1495, 1862, 2023, 2024, 2184, 2299, 2645, 2736, 3059, 3380, 3519, 4692, 4760, 5082, 7865], [28, 29, 57, 115, 116, 144, 174, 203, 231, 260, 289, 319, 377, 405, 493, 550, 551, 608, 637, 725, 782, 783, 840, 1014, 1044, 1275, 1449, 1595, 1624, 1682, 2000, 2001, 2175, 2204, 2261, 2464, 2639, 2754, 2783, 3248, 3450, 3509, 4640, 4784, 4900, 5103, 5887, 5915, 6669, 7105, 7424, 7888], [30, 31, 62, 92, 124, 154, 155, 186, 216, 247, 279, 340, 341, 434, 464, 495, 527, 588, 620, 650, 713, 805, 836, 867, 899, 930, 1023, 1053, 1209, 1364, 1425, 1518, 1519, 1767, 1859, 2015, 2232, 3564, 3875, 4185, 4991, 5642, 5796, 6075, 6137, 6292, 6324, 6727, 7656], [36, 37, 110, 111, 147, 184, 185, 221, 259, 296, 406, 407, 629, 665, 666, 702, 740, 850, 924, 999, 1035, 1368, 1443, 1479, 1664, 1665, 1701, 1924, 2145, 2294, 2552, 2737, 2849, 3219, 3255, 3773, 4255, 5290, 6992], [40, 81, 123, 164, 204, 245, 286, 287, 368, 369, 450, 492, 532, 574, 615, 696, 779, 1024, 1147, 1189, 1352, 1517, 1804, 2295, 2541, 2583, 2624, 2664, 2870, 3689, 4059, 4920, 6068, 6272, 6600, 7175, 7749], [43, 86, 129, 215, 300, 558, 644, 816, 860, 945, 989, 1247, 1332, 1375, 1376, 1547, 1935, 2106, 2365, 3267, 4773, 7568], [46, 47, 94, 140, 187, 188, 375, 376, 798, 1127, 1175, 2303, 2349, 3807, 6579], [105, 264, 529, 689, 2808, 3444], [59, 118, 413, 472, 884, 1652, 1887], [60, 243, 304, 609, 1403, 2379, 3599], [133, 402, 670, 736, 1407, 3015], [70, 141, 212, 284, 354, 567, 923, 1206, 3195, 3549], [145, 583, 1824, 2336, 3869], [237, 473, 868], [83, 414, 663, 4399], [712, 2135, 2491, 3293, 3649, 6141, 7475], [291, 387, 582, 969, 1551, 2231, 4558, 7080], [100, 201, 303, 403, 909]]

def fac : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | k + 1, n, p => if n < p * p then (if n < 2 then [] else [n]) else
      if n % p = 0 then p :: fac k (n / p) p else fac k n (p + 1)

def sv (vs : List (ZMod 5)) (l : List ℕ) : ZMod 5 := (l.map fun p => vs.getD (P.idxOf p) 0).sum

def ok (vs : List (ZMod 5)) (g : List ℕ) : Bool :=
  g.any fun n => sv vs (fac 200 n 2) == 0 && sv vs (fac 200 (n + 1) 2) == 0

set_option maxRecDepth 100000 in
lemma check : ∀ m ∈ M, ∀ n ∈ G.getD m [], 1 ≤ n ∧ n ≤ 7888 ∧ (fac 200 n 2).prod = n ∧
    (fac 200 (n + 1) 2).prod = n + 1 ∧ ∀ p ∈ fac 200 n 2 ++ fac 200 (n + 1) 2,
      p.Prime ∧ p ∈ P ∧ P.idxOf p ≤ m := by
  decide +kernel

lemma sv_eq (w : ℕ → ZMod 5) (m : ℕ) (l : List ℕ) (h : ∀ p ∈ l, p ∈ P ∧ P.idxOf p ≤ m) :
    sv ((P.map w).take (m + 1)) l = (l.map w).sum := by
  unfold sv
  congr 1
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨h1, h2⟩ := h p hp
  simp [List.getD_eq_getElem?_getD, Nat.lt_succ_of_le h2,
    List.idxOf_lt_length_iff.2 h1, List.getElem_idxOf]

end OMA436

open OMA436 in
set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_five_two_R1.H1 := by
  intro w
  suffices h : ∃ m ∈ M, ok ((P.map w).take (m + 1)) (G.getD m []) by
    obtain ⟨m, hm, h⟩ := h
    obtain ⟨n, hn, h⟩ := List.any_eq_true.1 h
    obtain ⟨h0, hN, h1, h2, h3⟩ := check m hm n hn
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨n, Finset.mem_Icc.2 ⟨h0, hN⟩, ?_, ?_⟩
    · rw [← ((Nat.primeFactorsList_unique h1 fun p hp => (h3 p (by simp [hp])).1).map w).sum_eq,
        ← sv_eq w m _ fun p hp => (h3 p (by simp [hp])).2]
      exact h.1
    · rw [← ((Nat.primeFactorsList_unique h2 fun p hp => (h3 p (by simp [hp])).1).map w).sum_eq,
        ← sv_eq w m _ fun p hp => (h3 p (by simp [hp])).2]
      exact h.2
  simp only [M, P, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp, exists_eq_left,
    List.map_cons, List.map_nil, List.take_succ_cons, List.take_zero]
  generalize w 2 = v0, w 3 = v1, w 5 = v2, w 7 = v3, w 11 = v4, w 13 = v5, w 17 = v6, w 19 = v7, w 23 = v8, w 29 = v9, w 31 = v10, w 37 = v11, w 41 = v12, w 43 = v13, w 47 = v14, w 53 = v15, w 59 = v16, w 61 = v17, w 67 = v18, w 71 = v19, w 73 = v20, w 79 = v21, w 83 = v22, w 89 = v23, w 97 = v24, w 101 = v25
  revert v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25
  simp only [forall_or_left]
  intro v0
  obtain rfl | rfl | rfl | rfl | rfl : v0 = 0 ∨ v0 = 1 ∨ v0 = 2 ∨ v0 = 3 ∨ v0 = 4 := by revert v0; decide
  all_goals first | exact Or.inl (by decide +kernel) | refine Or.inr fun v1 => ?_
  all_goals obtain rfl | rfl | rfl | rfl | rfl : v1 = 0 ∨ v1 = 1 ∨ v1 = 2 ∨ v1 = 3 ∨ v1 = 4 := by revert v1; decide
  all_goals decide +kernel

