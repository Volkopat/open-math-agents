import FormalConjectures.GreensOpenProblems.«72»

/-! # Checked no-three-in-line configurations for sizes 3 through 60 -/
-- Credit: @steveDOTdigital

namespace OMA.GridProof

-- For a fixed anchor, collinear points give the same slope key. A collision
-- between unrelated slopes would only cause the checker to reject a witness.
abbrev Pt := ℕ × ℕ

def key (a b : Pt) : ℕ :=
  if b.1 = a.1 then 0 else
    let r : ℚ := ((b.2 : ℚ) - a.2) / ((b.1 : ℚ) - a.1)
    1 + r.den + 64 * (r.num + 60).toNat

def fresh : ℕ → List ℕ → Bool
  | _, [] => true
  | seen, k :: ks => !seen.testBit k && fresh (seen ||| 2^k) ks

def keysOK (a : Pt) (xs : List Pt) : Bool :=
  fresh 0 (xs.map (key a))

def good : List Pt → Bool
  | [] => true
  | a :: xs => keysOK a xs && good xs

private theorem fresh_sound {l : List ℕ} {seen : ℕ} (h : fresh seen l = true) :
    l.Nodup ∧ ∀ k ∈ l, seen.testBit k = false := by
  induction l generalizing seen with
  | nil => simp
  | cons k ks ih =>
    obtain ⟨hk, ht⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨nd, bits⟩ := ih ht
    refine ⟨List.nodup_cons.2 ⟨?_, nd⟩, ?_⟩
    · intro hm
      have := bits k hm
      simp at this
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · simpa using hk
      · have := bits i hi
        rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
        exact this.1

private theorem good_sound {xs : List Pt} (ok : good xs = true)
    {a b c : Pt} (sub : [a,b,c].Sublist xs) : key a b ≠ key a c := by
  induction xs with
  | nil => simp at sub
  | cons x xs ih =>
    obtain ⟨hr, ht⟩ := Bool.and_eq_true_iff.mp ok
    cases sub with
    | cons _ h => exact ih ht h
    | cons_cons _ h =>
      have nodup := (fresh_sound hr).1
      have two := nodup.sublist (h.map (key a))
      simpa using two

private def realPt (a : Pt) : ℝ × ℝ := (a.1, a.2)

private theorem onLine {S : Set (ℝ × ℝ)} (h : Collinear ℝ S)
    {a b c : Pt} (ha : realPt a ∈ S) (hb : realPt b ∈ S) (hc : realPt c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) : key a b = key a c := by
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h
  obtain ⟨o, v, line⟩ := h
  obtain ⟨i, hi⟩ := line _ ha
  obtain ⟨j, hj⟩ := line _ hb
  obtain ⟨k, hk⟩ := line _ hc
  have coord (p : Pt) (t : ℝ) (e : realPt p = t • v +ᵥ o) :
      (p.1 : ℝ) = t * v.1 + o.1 ∧ (p.2 : ℝ) = t * v.2 + o.2 := by
    exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
  have eqReal : (a.1 : ℝ) * b.2 + b.1 * (c.2 : ℝ) + c.1 * (a.2 : ℝ) =
      (b.1 : ℝ) * a.2 + c.1 * (b.2 : ℝ) + a.1 * (c.2 : ℝ) := by
    rw [(coord _ _ hi).1, (coord _ _ hi).2, (coord _ _ hj).1,
      (coord _ _ hj).2, (coord _ _ hk).1, (coord _ _ hk).2]
    ring
  have eqQ : (a.1 : ℚ) * b.2 + b.1 * (c.2 : ℚ) + c.1 * (a.2 : ℚ) =
      (b.1 : ℚ) * a.2 + c.1 * (b.2 : ℚ) + a.1 * (c.2 : ℚ) := by exact_mod_cast eqReal
  have cross : ((b.2 : ℚ) - a.2) * ((c.1 : ℚ) - a.1) =
      ((c.2 : ℚ) - a.2) * ((b.1 : ℚ) - a.1) := by linarith only [eqQ]
  by_cases hb' : b.1 = a.1
  · have by' : (b.2 : ℚ) ≠ a.2 := by
      intro e
      exact hab (Prod.ext hb'.symm (by exact_mod_cast e.symm))
    rw [hb', sub_self, mul_zero] at cross
    have hc' : c.1 = a.1 := by exact_mod_cast sub_eq_zero.mp ((mul_eq_zero.mp cross).resolve_left (sub_ne_zero.mpr by'))
    simp [key, hb', hc']
  · have bx : (b.1 : ℚ) - a.1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hb')
    have hc' : c.1 ≠ a.1 := by
      intro e
      rw [e, sub_self, mul_zero] at cross
      have cy := sub_eq_zero.mp ((mul_eq_zero.mp cross.symm).resolve_right bx)
      exact hac (Prod.ext e.symm (by exact_mod_cast cy.symm))
    have cx : (c.1 : ℚ) - a.1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hc')
    simp only [key, if_neg hb', if_neg hc', (div_eq_div_iff bx cx).2 cross]

private theorem witness {n : ℕ} {xs : List Pt}
    (nd : xs.Nodup) (len : xs.length = 2*n)
    (bounds : ∀ p ∈ xs, p.1 < n ∧ p.2 < n) (ok : good xs = true) :
    Green72.NoKInLineFor 3 n := by
  classical
  have allowed : Green72.AllowedSet 3 n xs.toFinset := by
    refine ⟨fun p hp => bounds p (List.mem_toFinset.1 hp), ?_⟩
    intro t ht hcard line
    let ys := xs.filter (fun p => decide (p ∈ t))
    have feq : ys.toFinset = t := by
      ext p
      simp [ys, and_iff_right_of_imp (fun hp => List.mem_toFinset.1 (ht hp))]
    have ylen : ys.length = 3 := by
      rw [← List.toFinset_card_of_nodup (nd.filter _), feq, hcard]
    obtain ⟨a,b,c,h3⟩ := List.length_eq_three.mp ylen
    have sub : [a,b,c].Sublist xs := h3 ▸ List.filter_sublist ..
    have inside {p : Pt} (hp : p ∈ [a,b,c]) : realPt p ∈
        {r | ∃ i ∈ t, r = ((i.1 : ℝ), (i.2 : ℝ))} := by
      exact ⟨p, feq ▸ List.mem_toFinset.2 (h3 ▸ hp), rfl⟩
    have bad := onLine line (inside (p := a) (by simp)) (inside (p := b) (by simp))
      (inside (p := c) (by simp))
    have three : [a,b,c].Nodup := nd.sublist sub
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at three
    exact good_sound ok sub (bad (fun e => three.1 (Or.inl e)) (fun e => three.1 (Or.inr e)))
  apply le_antisymm Green72.allowedSetSize_le
  change (3-1) * n ≤ sSup {r | ∃ s, r = s.card ∧ Green72.AllowedSet 3 n s}
  have member : (3-1)*n ∈ {r : ℕ | ∃ s, r = s.card ∧ Green72.AllowedSet 3 n s} :=
    ⟨xs.toFinset, by rw [List.toFinset_card_of_nodup nd, len], allowed⟩
  apply le_csSup _ member
  refine ⟨n*n, ?_⟩
  rintro r ⟨s, rfl, hs⟩
  calc s.card ≤ ((Finset.range n) ×ˢ (Finset.range n)).card := by
        apply Finset.card_le_card
        intro p hp
        exact Finset.mem_product.2 ⟨Finset.mem_range.2 (hs.is_bounded p hp).1,
          Finset.mem_range.2 (hs.is_bounded p hp).2⟩
       _ = _ := by simp

-- One witness for each grid size from Achim Flammenkamp's database.
-- https://wwwhomes.uni-bielefeld.de/~achim/no3in/download/configurations/
-- Each entry packs the two columns in a row as 64 * first + second.
private def packed : ℕ → List ℕ
  | 3 => [1, 2, 66]
  | 4 => [66, 3, 3, 66]
  | 5 => [2, 132, 1, 196, 67]
  | 6 => [2, 132, 1, 261, 67, 197]
  | 7 => [67, 5, 197, 2, 262, 66, 262]
  | 8 => [132, 131, 391, 6, 71, 1, 261, 197]
  | 9 => [196, 70, 67, 392, 8, 2, 327, 135, 261]
  | 10 => [261, 135, 72, 198, 9, 9, 198, 72, 135, 261]
  | 11 => [66, 6, 2, 391, 263, 586, 67, 196, 586, 328, 328]
  | 12 => [457, 261, 139, 328, 75, 67, 522, 10, 198, 9, 391, 132]
  | 13 => [262, 73, 329, 651, 5, 132, 12, 522, 460, 66, 199, 203, 392]
  | 14 => [261, 458, 261, 652, 2, 2, 396, 71, 717, 717, 67, 521, 198, 521]
  | 15 => [201, 460, 269, 8, 136, 334, 651, 77, 196, 9, 396, 398, 74, 135, 331]
  | 16 => [331, 136, 72, 331, 783, 3, 393, 846, 66, 393, 783, 3, 266, 462, 461, 266]
  | 17 => [653, 71, 327, 12, 197, 782, 8, 911, 394, 66, 528, 132, 717, 272, 587, 591, 198]
  | 18 => [651, 397, 202, 133, 848, 200, 81, 977, 328, 588, 2, 16, 590, 68, 783, 462, 267, 391]
  | 19 => [328, 718, 136, 262, 79, 402, 847, 73, 1042, 459, 2, 593, 197, 12, 209, 782, 656, 263, 653]
  | 20 => [458, 847, 205, 133, 530, 200, 1106, 12, 261, 595, 10, 911, 467, 66, 720, 75, 913, 400, 262, 588]
  | 21 => [1, 587, 980, 652, 394, 270, 913, 147, 196, 137, 1044, 197, 525, 402, 1107, 13, 82, 719, 327, 528, 460]
  | 22 => [526, 654, 466, 655, 203, 131, 1109, 1045, 133, 589, 18, 400, 4, 589, 1108, 70, 69, 1236, 723, 460, 271, 524]
  | 23 => [587, 978, 329, 915, 198, 328, 140, 86, 655, 4, 134, 85, 1044, 1174, 460, 21, 660, 913, 1043, 196, 849, 456, 717]
  | 24 => [718, 265, 134, 785, 148, 849, 327, 215, 19, 723, 912, 1175, 341, 8, 528, 788, 86, 86, 469, 978, 198, 266, 655, 589]
  | 25 => [789, 471, 335, 398, 200, 270, 271, 727, 136, 721, 1176, 1368, 150, 3, 6, 461, 1046, 77, 596, 660, 336, 658, 595, 81, 787]
  | 26 => [783, 724, 399, 274, 406, 588, 17, 1367, 69, 729, 80, 200, 471, 146, 1110, 600, 14, 1304, 132, 537, 848, 211, 469, 330, 915, 653]
  | 27 => [538, 658, 261, 786, 654, 1112, 1238, 593, 851, 215, 73, 331, 1497, 1369, 4, 2, 916, 1048, 150, 396, 1050, 198, 72, 719, 461, 1301, 463]
  | 28 => [977, 1109, 471, 332, 526, 402, 1561, 87, 1241, 71, 592, 24, 5, 848, 718, 1435, 219, 722, 1306, 136, 282, 131, 597, 851, 655, 276, 394, 790]
  | 29 => [653, 788, 593, 261, 1626, 393, 412, 1042, 913, 67, 1306, 461, 1564, 69, 469, 1499, 4, 981, 136, 1627, 718, 524, 22, 1238, 131, 1496, 723, 656, 978]
  | 30 => [12, 719, 1107, 464, 663, 1432, 261, 662, 1176, 132, 784, 157, 329, 1115, 73, 219, 1373, 205, 1369, 92, 914, 1692, 6, 532, 1626, 392, 468, 919, 717, 979]
  | 31 => [657, 1366, 468, 461, 793, 216, 133, 398, 211, 783, 1433, 275, 1886, 68, 14, 597, 1054, 1693, 1, 730, 328, 978, 731, 1048, 156, 411, 1180, 1111, 663, 521, 852]
  | 32 => [5, 980, 653, 1499, 921, 595, 602, 272, 1245, 71, 203, 1175, 398, 1, 1565, 668, 213, 135, 1951, 1113, 525, 1308, 1566, 140, 987, 342, 790, 401, 264, 1173, 720, 1695]
  | 33 => [219, 263, 787, 784, 1112, 1695, 1175, 535, 14, 75, 207, 1371, 653, 1628, 10, 1694, 158, 134, 1440, 263, 1238, 331, 1117, 1375, 1184, 600, 590, 70, 527, 1044, 852, 1628, 349]
  | 34 => [527, 655, 605, 1046, 141, 1562, 1045, 330, 1633, 351, 1696, 204, 406, 925, 916, 2081, 1758, 198, 1, 851, 275, 731, 1374, 71, 156, 8, 1500, 785, 457, 1311, 721, 280, 1175, 1177]
  | 35 => [781, 786, 1627, 858, 1565, 275, 394, 139, 212, 145, 284, 1307, 2146, 2018, 523, 336, 1249, 601, 79, 1181, 1498, 3, 1, 462, 414, 1120, 927, 1504, 1564, 990, 330, 533, 457, 1046, 1366]
  | 36 => [800, 1173, 468, 4, 1312, 670, 405, 1569, 588, 1115, 1246, 470, 1763, 720, 70, 132, 662, 90, 610, 857, 2017, 1890, 1240, 8, 860, 336, 530, 1498, 139, 925, 345, 207, 2019, 988, 913, 215]
  | 37 => [1108, 1761, 726, 349, 854, 87, 593, 200, 733, 94, 1368, 1826, 658, 352, 132, 656, 21, 1956, 792, 6, 996, 1306, 2082, 287, 1178, 136, 783, 419, 473, 1825, 1243, 867, 919, 479, 921, 201, 1043]
  | 38 => [852, 100, 410, 399, 721, 663, 354, 1436, 787, 471, 1056, 161, 1245, 1061, 137, 482, 1563, 33, 524, 1629, 293, 653, 222, 1827, 21, 530, 291, 341, 926, 1177, 591, 224, 923, 1306, 1439, 735, 100, 1112]
  | 39 => [1434, 412, 529, 1055, 1694, 988, 1509, 205, 1188, 605, 69, 846, 4, 1759, 1115, 417, 35, 1572, 1250, 1172, 275, 142, 230, 352, 725, 459, 2214, 1561, 2149, 605, 148, 1635, 79, 663, 524, 470, 1374, 672, 784]
  | 40 => [146, 924, 15, 730, 1048, 1241, 797, 541, 1312, 1050, 391, 100, 1185, 201, 358, 293, 1955, 1110, 1767, 546, 351, 12, 1110, 265, 163, 98, 1956, 405, 230, 2081, 855, 467, 671, 667, 916, 983, 860, 1575, 729, 1381]
  | 41 => [1115, 1241, 159, 726, 930, 919, 264, 651, 1570, 156, 993, 2149, 600, 18, 2276, 94, 524, 360, 219, 1319, 1237, 84, 869, 35, 1824, 679, 261, 1448, 1055, 199, 473, 806, 400, 1886, 2084, 1114, 410, 1181, 614, 981, 855]
  | 42 => [1111, 1173, 730, 609, 415, 601, 869, 726, 218, 2342, 277, 162, 1756, 803, 787, 136, 337, 1641, 40, 475, 74, 2024, 930, 105, 16, 1572, 2151, 1437, 413, 846, 487, 1317, 197, 998, 1246, 284, 1056, 675, 544, 990, 1303, 1176]
  | 43 => [395, 1241, 335, 1696, 662, 936, 1834, 611, 1437, 466, 230, 1386, 1691, 529, 421, 808, 204, 93, 1249, 1577, 264, 735, 2214, 82, 599, 873, 1959, 158, 356, 1634, 976, 21, 295, 1571, 852, 481, 14, 156, 1312, 656, 1765, 1111, 2020]
  | 44 => [1372, 655, 1239, 1061, 354, 871, 221, 717, 1305, 278, 78, 1188, 799, 2342, 417, 42, 1704, 1043, 544, 1705, 163, 619, 34, 553, 145, 739, 1563, 209, 107, 677, 327, 799, 473, 1898, 1383, 1175, 1952, 936, 286, 614, 411, 1304, 1825, 982]
  | 45 => [1174, 1632, 990, 456, 1564, 416, 1383, 937, 681, 664, 2276, 859, 69, 1121, 165, 1002, 275, 735, 1388, 92, 265, 1702, 44, 402, 2280, 1067, 23, 865, 1640, 157, 490, 731, 2539, 1119, 521, 1314, 226, 222, 343, 806, 1044, 2341, 925, 787, 1434]
  | 46 => [791, 144, 1580, 1436, 2019, 719, 1246, 1574, 1056, 1763, 265, 1256, 1133, 532, 270, 424, 2412, 225, 596, 2215, 1760, 135, 42, 237, 2475, 850, 395, 1636, 810, 72, 359, 2025, 1637, 28, 346, 2345, 658, 861, 469, 986, 1954, 654, 1111, 85, 1899, 1441]
  | 47 => [1316, 800, 873, 981, 1756, 150, 1955, 729, 524, 1119, 27, 423, 2477, 1324, 81, 619, 402, 2085, 286, 266, 2158, 491, 1513, 1432, 343, 231, 13, 2346, 1066, 590, 1832, 229, 1901, 154, 72, 488, 1262, 989, 2214, 1379, 720, 1580, 1171, 1631, 353, 930, 666]
  | 48 => [1249, 854, 1171, 1565, 804, 465, 1699, 2346, 1702, 526, 1303, 263, 427, 143, 38, 2018, 985, 1322, 237, 2991, 1957, 392, 1070, 229, 684, 95, 2537, 657, 1, 172, 347, 1440, 848, 623, 2093, 297, 2603, 1563, 2151, 597, 331, 789, 1960, 739, 1175, 1821, 1634, 924]
  | 49 => [790, 1180, 989, 868, 1500, 1127, 2213, 1504, 658, 344, 2280, 416, 240, 685, 411, 1710, 459, 1131, 2607, 149, 68, 925, 1008, 2668, 615, 263, 33, 1250, 2863, 1774, 72, 351, 2409, 150, 1386, 230, 45, 1066, 525, 1579, 1958, 1049, 718, 607, 1305, 803, 1249, 1310, 1700]
  | 50 => [732, 1761, 980, 1316, 1002, 2342, 1564, 264, 1450, 2149, 679, 197, 593, 5, 1503, 2927, 73, 2021, 913, 1562, 2991, 6, 105, 1251, 1963, 403, 926, 560, 2801, 131, 1497, 2083, 786, 2608, 132, 1178, 2865, 2088, 2862, 679, 784, 475, 2669, 1369, 717, 482, 861, 1890, 1046, 1382]
  | 51 => [1757, 652, 476, 1633, 929, 1306, 781, 2032, 727, 1189, 1841, 746, 2865, 2668, 1070, 1181, 1700, 196, 2281, 468, 2029, 15, 138, 42, 336, 239, 2221, 562, 2608, 2290, 339, 1963, 591, 2991, 920, 1376, 290, 393, 70, 551, 86, 864, 1767, 147, 2406, 1566, 1124, 1113, 1451, 2472, 1367]
  | 52 => [1239, 803, 785, 2219, 218, 728, 2155, 856, 397, 1697, 1317, 2350, 3186, 300, 670, 739, 79, 241, 393, 1971, 1513, 915, 1437, 2035, 2862, 265, 2735, 327, 20, 1437, 2085, 668, 21, 2733, 176, 2354, 1064, 1385, 495, 66, 335, 927, 1177, 2477, 1766, 530, 1768, 1648, 529, 2215, 1063, 1824]
  | 53 => [1044, 2213, 1305, 1577, 2017, 328, 920, 533, 2927, 679, 1899, 222, 2211, 595, 1134, 86, 1716, 806, 76, 295, 3252, 301, 741, 665, 2993, 1906, 1060, 151, 198, 1770, 1001, 496, 2, 880, 2611, 936, 26, 1971, 419, 2155, 1106, 1457, 599, 874, 327, 2028, 1830, 2863, 1237, 732, 1760, 978, 2084]
  | 54 => [1829, 1183, 2545, 1386, 154, 1252, 984, 678, 1961, 1898, 1966, 201, 529, 915, 168, 495, 2152, 361, 1652, 3125, 1050, 1458, 96, 522, 623, 35, 2161, 276, 1205, 428, 2797, 1396, 223, 1765, 5, 92, 816, 852, 430, 883, 2215, 2349, 2866, 471, 728, 791, 1003, 1894, 1122, 1779, 736, 270, 1443, 1049]
  | 55 => [870, 1311, 1326, 1448, 1962, 1241, 1563, 480, 2356, 745, 1107, 2541, 281, 630, 220, 721, 33, 2540, 545, 2865, 3381, 1042, 499, 90, 304, 2737, 927, 432, 1512, 332, 434, 1845, 239, 2342, 66, 330, 1390, 655, 1398, 2411, 1715, 45, 1906, 591, 2277, 875, 146, 1455, 1758, 1891, 792, 928, 546, 1506, 1065]
  | 56 => [736, 1757, 1193, 1632, 2220, 852, 528, 1956, 2801, 1569, 1770, 132, 529, 690, 35, 1255, 1009, 2155, 1909, 488, 946, 280, 593, 3, 2222, 500, 82, 2934, 74, 2422, 240, 597, 3383, 2478, 2035, 361, 1008, 154, 790, 424, 1060, 1335, 365, 2479, 3317, 860, 1439, 396, 1241, 2543, 2282, 725, 1502, 933, 1692, 1516]
  | 57 => [2098, 1693, 1192, 866, 1385, 737, 28, 1957, 1644, 615, 857, 2867, 523, 2997, 1382, 1076, 169, 600, 950, 475, 1431, 2740, 228, 356, 39, 2992, 503, 101, 434, 1271, 113, 522, 1144, 1331, 1333, 270, 2146, 1905, 170, 2095, 1014, 296, 1187, 202, 2928, 332, 2027, 1135, 799, 1242, 1848, 1517, 995, 1451, 1062, 1758, 408]
  | 58 => [1371, 2475, 1126, 1951, 523, 426, 1332, 679, 1141, 1628, 1650, 885, 1834, 2542, 99, 332, 1444, 3191, 461, 66, 2163, 1081, 937, 1506, 1306, 3056, 225, 249, 2928, 588, 54, 1590, 586, 2021, 1506, 1067, 41, 408, 3576, 2866, 136, 1379, 2932, 1464, 722, 989, 300, 480, 1888, 296, 1199, 357, 1011, 2993, 1691, 1256, 915, 1956]
  | 59 => [1582, 1312, 1887, 1515, 691, 2149, 851, 300, 2090, 623, 2038, 597, 42, 1588, 488, 225, 524, 1174, 937, 1844, 1529, 367, 1833, 2487, 2938, 335, 72, 138, 2343, 184, 1238, 3128, 3257, 2805, 13, 212, 1118, 757, 99, 414, 1132, 2344, 2994, 1655, 1203, 418, 1082, 2417, 283, 753, 1050, 950, 2541, 1369, 496, 995, 1757, 1702, 802]
  | 60 => [1326, 2279, 2026, 979, 1705, 625, 535, 1902, 1205, 2422, 351, 1386, 815, 7, 1960, 1784, 1497, 139, 307, 952, 123, 1584, 609, 2805, 102, 1771, 1463, 2220, 138, 948, 493, 3193, 985, 293, 1056, 1402, 400, 1714, 739, 58, 237, 567, 3129, 2212, 224, 1245, 3387, 815, 1126, 1846, 342, 425, 862, 2355, 690, 1185, 2604, 1116, 1304, 871]
  | _ => []

private def grid (n : ℕ) : List Pt :=
  (packed n).zipIdx.flatMap fun (v, i) => [(i, v / 64), (i, v % 64)]

private def valid (n : ℕ) : Bool :=
  let xs := grid n
  decide (xs.Nodup) && decide (xs.length = 2*n) &&
    xs.all (fun p => decide (p.1 < n ∧ p.2 < n)) && good xs

private theorem from_valid (n : ℕ) (h : valid n = true) : Green72.NoKInLineFor 3 n := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact witness h.1.1.1 h.1.1.2 h.1.2 h.2

private lemma of_all {l k n : ℕ} (h : (List.range' l k).all valid = true) (h1 : l ≤ n) (h2 : n < l + k) :
    valid n = true := List.all_eq_true.mp h n (List.mem_range'_1.mpr ⟨h1, h2⟩)
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem c0 : (List.range' 3 27).all valid = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem c1 : (List.range' 30 8).all valid = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem c2 : (List.range' 38 6).all valid = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem c3 : (List.range' 44 5).all valid = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem c4 : (List.range' 49 4).all valid = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem c5 : (List.range' 53 3).all valid = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem c6 : (List.range' 56 3).all valid = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem c7 : (List.range' 59 2).all valid = true := by decide +kernel

theorem all_sizes {n : ℕ} (lo : 3 ≤ n) (hi : n ≤ 60) : Green72.NoKInLineFor 3 n :=
  from_valid n <|
  if h0 : n < 30 then of_all c0 (by omega) h0 else
  if h1 : n < 38 then of_all c1 (by omega) h1 else
  if h2 : n < 44 then of_all c2 (by omega) h2 else
  if h3 : n < 49 then of_all c3 (by omega) h3 else
  if h4 : n < 53 then of_all c4 (by omega) h4 else
  if h5 : n < 56 then of_all c5 (by omega) h5 else
  if h6 : n < 59 then of_all c6 (by omega) h6 else
  of_all c7 (by omega) (by omega)

end OMA.GridProof

theorem OMA.solution : type_of% @Green72.no_three_in_line_le := by
  exact OMA.GridProof.all_sizes
