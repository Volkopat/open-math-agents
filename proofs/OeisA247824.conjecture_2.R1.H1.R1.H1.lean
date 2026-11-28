import OMAReductions.R_OeisA247824_conjecture_2_R1_H1_R1
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

/- Credit: @connoranderson. Certifies H1 of physbuzz's Legendre and Meissel
reduction by evaluating the Legendre recurrence against a checked list of primes. -/

/- Split certificates for the primes below the sieve cutoff. -/
namespace A247824Checked

def quick (n : ℕ) := if n ≤ 67 then decide n.Prime else (n.gcd 36471110918188685288249859096605464427167635314049524593701628500267962436943872000000000000000 == 1)
theorem quick_spec {n : ℕ} (h : n ≤ 4568) : quick n = true ↔ n.Prime := by
  unfold quick
  split_ifs with small
  · simp
  · have fac : Nat.factorial 67 = 36471110918188685288249859096605464427167635314049524593701628500267962436943872000000000000000 := by rfl
    rw [← fac, beq_iff_eq]
    constructor
    · intro hg
      by_contra hnp
      have hp := Nat.minFac_prime (n := n) (by omega)
      have hs := Nat.minFac_sq_le_self (n := n) (by omega) hnp
      have hm : n.minFac ≤ 67 := by
        by_contra! hi
        have z := Nat.mul_le_mul hi hi
        rw [pow_two] at hs
        omega
      have hd := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) hm)
      rw [hg] at hd
      exact hp.not_dvd_one hd
    · intro hp
      exact hp.coprime_factorial_of_lt (by omega)
def Lb0_142 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b0_142 : ((List.range' 0 142).filter quick) = Lb0_142 := by rfl
def Lb142_143 : List ℕ := [149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b142_143 : ((List.range' 142 143).filter quick) = Lb142_143 := by rfl
def Lb0_285 := Lb0_142 ++ Lb142_143
theorem b0_285 : ((List.range' 0 285).filter quick) = Lb0_285 := by
  rw [show List.range' 0 285 = List.range' 0 142 ++ List.range' 142 143 from (List.range'_append_1 (s := 0) (m := 142) (n := 143)).symm, List.filter_append, b0_142, b142_143] <;> rfl
def Lb285_143 : List ℕ := [293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b285_143 : ((List.range' 285 143).filter quick) = Lb285_143 := by rfl
def Lb428_143 : List ℕ := [431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b428_143 : ((List.range' 428 143).filter quick) = Lb428_143 := by rfl
def Lb285_286 := Lb285_143 ++ Lb428_143
theorem b285_286 : ((List.range' 285 286).filter quick) = Lb285_286 := by
  rw [show List.range' 285 286 = List.range' 285 143 ++ List.range' 428 143 from (List.range'_append_1 (s := 285) (m := 143) (n := 143)).symm, List.filter_append, b285_143, b428_143] <;> rfl
def Lb0_571 := Lb0_285 ++ Lb285_286
theorem b0_571 : ((List.range' 0 571).filter quick) = Lb0_571 := by
  rw [show List.range' 0 571 = List.range' 0 285 ++ List.range' 285 286 from (List.range'_append_1 (s := 0) (m := 285) (n := 286)).symm, List.filter_append, b0_285, b285_286] <;> rfl
def Lb571_142 : List ℕ := [571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b571_142 : ((List.range' 571 142).filter quick) = Lb571_142 := by rfl
def Lb713_143 : List ℕ := [719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b713_143 : ((List.range' 713 143).filter quick) = Lb713_143 := by rfl
def Lb571_285 := Lb571_142 ++ Lb713_143
theorem b571_285 : ((List.range' 571 285).filter quick) = Lb571_285 := by
  rw [show List.range' 571 285 = List.range' 571 142 ++ List.range' 713 143 from (List.range'_append_1 (s := 571) (m := 142) (n := 143)).symm, List.filter_append, b571_142, b713_143] <;> rfl
def Lb856_143 : List ℕ := [857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b856_143 : ((List.range' 856 143).filter quick) = Lb856_143 := by rfl
def Lb999_143 : List ℕ := [1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b999_143 : ((List.range' 999 143).filter quick) = Lb999_143 := by rfl
def Lb856_286 := Lb856_143 ++ Lb999_143
theorem b856_286 : ((List.range' 856 286).filter quick) = Lb856_286 := by
  rw [show List.range' 856 286 = List.range' 856 143 ++ List.range' 999 143 from (List.range'_append_1 (s := 856) (m := 143) (n := 143)).symm, List.filter_append, b856_143, b999_143] <;> rfl
def Lb571_571 := Lb571_285 ++ Lb856_286
theorem b571_571 : ((List.range' 571 571).filter quick) = Lb571_571 := by
  rw [show List.range' 571 571 = List.range' 571 285 ++ List.range' 856 286 from (List.range'_append_1 (s := 571) (m := 285) (n := 286)).symm, List.filter_append, b571_285, b856_286] <;> rfl
def Lb0_1142 := Lb0_571 ++ Lb571_571
theorem b0_1142 : ((List.range' 0 1142).filter quick) = Lb0_1142 := by
  rw [show List.range' 0 1142 = List.range' 0 571 ++ List.range' 571 571 from (List.range'_append_1 (s := 0) (m := 571) (n := 571)).symm, List.filter_append, b0_571, b571_571] <;> rfl
def Lb1142_142 : List ℕ := [1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b1142_142 : ((List.range' 1142 142).filter quick) = Lb1142_142 := by rfl
def Lb1284_143 : List ℕ := [1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b1284_143 : ((List.range' 1284 143).filter quick) = Lb1284_143 := by rfl
def Lb1142_285 := Lb1142_142 ++ Lb1284_143
theorem b1142_285 : ((List.range' 1142 285).filter quick) = Lb1142_285 := by
  rw [show List.range' 1142 285 = List.range' 1142 142 ++ List.range' 1284 143 from (List.range'_append_1 (s := 1142) (m := 142) (n := 143)).symm, List.filter_append, b1142_142, b1284_143] <;> rfl
def Lb1427_143 : List ℕ := [1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b1427_143 : ((List.range' 1427 143).filter quick) = Lb1427_143 := by rfl
def Lb1570_143 : List ℕ := [1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b1570_143 : ((List.range' 1570 143).filter quick) = Lb1570_143 := by rfl
def Lb1427_286 := Lb1427_143 ++ Lb1570_143
theorem b1427_286 : ((List.range' 1427 286).filter quick) = Lb1427_286 := by
  rw [show List.range' 1427 286 = List.range' 1427 143 ++ List.range' 1570 143 from (List.range'_append_1 (s := 1427) (m := 143) (n := 143)).symm, List.filter_append, b1427_143, b1570_143] <;> rfl
def Lb1142_571 := Lb1142_285 ++ Lb1427_286
theorem b1142_571 : ((List.range' 1142 571).filter quick) = Lb1142_571 := by
  rw [show List.range' 1142 571 = List.range' 1142 285 ++ List.range' 1427 286 from (List.range'_append_1 (s := 1142) (m := 285) (n := 286)).symm, List.filter_append, b1142_285, b1427_286] <;> rfl
def Lb1713_142 : List ℕ := [1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b1713_142 : ((List.range' 1713 142).filter quick) = Lb1713_142 := by rfl
def Lb1855_143 : List ℕ := [1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b1855_143 : ((List.range' 1855 143).filter quick) = Lb1855_143 := by rfl
def Lb1713_285 := Lb1713_142 ++ Lb1855_143
theorem b1713_285 : ((List.range' 1713 285).filter quick) = Lb1713_285 := by
  rw [show List.range' 1713 285 = List.range' 1713 142 ++ List.range' 1855 143 from (List.range'_append_1 (s := 1713) (m := 142) (n := 143)).symm, List.filter_append, b1713_142, b1855_143] <;> rfl
def Lb1998_143 : List ℕ := [1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b1998_143 : ((List.range' 1998 143).filter quick) = Lb1998_143 := by rfl
def Lb2141_143 : List ℕ := [2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b2141_143 : ((List.range' 2141 143).filter quick) = Lb2141_143 := by rfl
def Lb1998_286 := Lb1998_143 ++ Lb2141_143
theorem b1998_286 : ((List.range' 1998 286).filter quick) = Lb1998_286 := by
  rw [show List.range' 1998 286 = List.range' 1998 143 ++ List.range' 2141 143 from (List.range'_append_1 (s := 1998) (m := 143) (n := 143)).symm, List.filter_append, b1998_143, b2141_143] <;> rfl
def Lb1713_571 := Lb1713_285 ++ Lb1998_286
theorem b1713_571 : ((List.range' 1713 571).filter quick) = Lb1713_571 := by
  rw [show List.range' 1713 571 = List.range' 1713 285 ++ List.range' 1998 286 from (List.range'_append_1 (s := 1713) (m := 285) (n := 286)).symm, List.filter_append, b1713_285, b1998_286] <;> rfl
def Lb1142_1142 := Lb1142_571 ++ Lb1713_571
theorem b1142_1142 : ((List.range' 1142 1142).filter quick) = Lb1142_1142 := by
  rw [show List.range' 1142 1142 = List.range' 1142 571 ++ List.range' 1713 571 from (List.range'_append_1 (s := 1142) (m := 571) (n := 571)).symm, List.filter_append, b1142_571, b1713_571] <;> rfl
def Lb0_2284 := Lb0_1142 ++ Lb1142_1142
theorem b0_2284 : ((List.range' 0 2284).filter quick) = Lb0_2284 := by
  rw [show List.range' 0 2284 = List.range' 0 1142 ++ List.range' 1142 1142 from (List.range'_append_1 (s := 0) (m := 1142) (n := 1142)).symm, List.filter_append, b0_1142, b1142_1142] <;> rfl
def Lb2284_142 : List ℕ := [2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b2284_142 : ((List.range' 2284 142).filter quick) = Lb2284_142 := by rfl
def Lb2426_143 : List ℕ := [2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b2426_143 : ((List.range' 2426 143).filter quick) = Lb2426_143 := by rfl
def Lb2284_285 := Lb2284_142 ++ Lb2426_143
theorem b2284_285 : ((List.range' 2284 285).filter quick) = Lb2284_285 := by
  rw [show List.range' 2284 285 = List.range' 2284 142 ++ List.range' 2426 143 from (List.range'_append_1 (s := 2284) (m := 142) (n := 143)).symm, List.filter_append, b2284_142, b2426_143] <;> rfl
def Lb2569_143 : List ℕ := [2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b2569_143 : ((List.range' 2569 143).filter quick) = Lb2569_143 := by rfl
def Lb2712_143 : List ℕ := [2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b2712_143 : ((List.range' 2712 143).filter quick) = Lb2712_143 := by rfl
def Lb2569_286 := Lb2569_143 ++ Lb2712_143
theorem b2569_286 : ((List.range' 2569 286).filter quick) = Lb2569_286 := by
  rw [show List.range' 2569 286 = List.range' 2569 143 ++ List.range' 2712 143 from (List.range'_append_1 (s := 2569) (m := 143) (n := 143)).symm, List.filter_append, b2569_143, b2712_143] <;> rfl
def Lb2284_571 := Lb2284_285 ++ Lb2569_286
theorem b2284_571 : ((List.range' 2284 571).filter quick) = Lb2284_571 := by
  rw [show List.range' 2284 571 = List.range' 2284 285 ++ List.range' 2569 286 from (List.range'_append_1 (s := 2284) (m := 285) (n := 286)).symm, List.filter_append, b2284_285, b2569_286] <;> rfl
def Lb2855_142 : List ℕ := [2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b2855_142 : ((List.range' 2855 142).filter quick) = Lb2855_142 := by rfl
def Lb2997_143 : List ℕ := [2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b2997_143 : ((List.range' 2997 143).filter quick) = Lb2997_143 := by rfl
def Lb2855_285 := Lb2855_142 ++ Lb2997_143
theorem b2855_285 : ((List.range' 2855 285).filter quick) = Lb2855_285 := by
  rw [show List.range' 2855 285 = List.range' 2855 142 ++ List.range' 2997 143 from (List.range'_append_1 (s := 2855) (m := 142) (n := 143)).symm, List.filter_append, b2855_142, b2997_143] <;> rfl
def Lb3140_143 : List ℕ := [3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b3140_143 : ((List.range' 3140 143).filter quick) = Lb3140_143 := by rfl
def Lb3283_143 : List ℕ := [3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b3283_143 : ((List.range' 3283 143).filter quick) = Lb3283_143 := by rfl
def Lb3140_286 := Lb3140_143 ++ Lb3283_143
theorem b3140_286 : ((List.range' 3140 286).filter quick) = Lb3140_286 := by
  rw [show List.range' 3140 286 = List.range' 3140 143 ++ List.range' 3283 143 from (List.range'_append_1 (s := 3140) (m := 143) (n := 143)).symm, List.filter_append, b3140_143, b3283_143] <;> rfl
def Lb2855_571 := Lb2855_285 ++ Lb3140_286
theorem b2855_571 : ((List.range' 2855 571).filter quick) = Lb2855_571 := by
  rw [show List.range' 2855 571 = List.range' 2855 285 ++ List.range' 3140 286 from (List.range'_append_1 (s := 2855) (m := 285) (n := 286)).symm, List.filter_append, b2855_285, b3140_286] <;> rfl
def Lb2284_1142 := Lb2284_571 ++ Lb2855_571
theorem b2284_1142 : ((List.range' 2284 1142).filter quick) = Lb2284_1142 := by
  rw [show List.range' 2284 1142 = List.range' 2284 571 ++ List.range' 2855 571 from (List.range'_append_1 (s := 2284) (m := 571) (n := 571)).symm, List.filter_append, b2284_571, b2855_571] <;> rfl
def Lb3426_142 : List ℕ := [3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b3426_142 : ((List.range' 3426 142).filter quick) = Lb3426_142 := by rfl
def Lb3568_143 : List ℕ := [3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b3568_143 : ((List.range' 3568 143).filter quick) = Lb3568_143 := by rfl
def Lb3426_285 := Lb3426_142 ++ Lb3568_143
theorem b3426_285 : ((List.range' 3426 285).filter quick) = Lb3426_285 := by
  rw [show List.range' 3426 285 = List.range' 3426 142 ++ List.range' 3568 143 from (List.range'_append_1 (s := 3426) (m := 142) (n := 143)).symm, List.filter_append, b3426_142, b3568_143] <;> rfl
def Lb3711_143 : List ℕ := [3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b3711_143 : ((List.range' 3711 143).filter quick) = Lb3711_143 := by rfl
def Lb3854_143 : List ℕ := [3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b3854_143 : ((List.range' 3854 143).filter quick) = Lb3854_143 := by rfl
def Lb3711_286 := Lb3711_143 ++ Lb3854_143
theorem b3711_286 : ((List.range' 3711 286).filter quick) = Lb3711_286 := by
  rw [show List.range' 3711 286 = List.range' 3711 143 ++ List.range' 3854 143 from (List.range'_append_1 (s := 3711) (m := 143) (n := 143)).symm, List.filter_append, b3711_143, b3854_143] <;> rfl
def Lb3426_571 := Lb3426_285 ++ Lb3711_286
theorem b3426_571 : ((List.range' 3426 571).filter quick) = Lb3426_571 := by
  rw [show List.range' 3426 571 = List.range' 3426 285 ++ List.range' 3711 286 from (List.range'_append_1 (s := 3426) (m := 285) (n := 286)).symm, List.filter_append, b3426_285, b3711_286] <;> rfl
def Lb3997_143 : List ℕ := [4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b3997_143 : ((List.range' 3997 143).filter quick) = Lb3997_143 := by rfl
def Lb4140_143 : List ℕ := [4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b4140_143 : ((List.range' 4140 143).filter quick) = Lb4140_143 := by rfl
def Lb3997_286 := Lb3997_143 ++ Lb4140_143
theorem b3997_286 : ((List.range' 3997 286).filter quick) = Lb3997_286 := by
  rw [show List.range' 3997 286 = List.range' 3997 143 ++ List.range' 4140 143 from (List.range'_append_1 (s := 3997) (m := 143) (n := 143)).symm, List.filter_append, b3997_143, b4140_143] <;> rfl
def Lb4283_143 : List ℕ := [4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b4283_143 : ((List.range' 4283 143).filter quick) = Lb4283_143 := by rfl
def Lb4426_143 : List ℕ := [4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567]
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem b4426_143 : ((List.range' 4426 143).filter quick) = Lb4426_143 := by rfl
def Lb4283_286 := Lb4283_143 ++ Lb4426_143
theorem b4283_286 : ((List.range' 4283 286).filter quick) = Lb4283_286 := by
  rw [show List.range' 4283 286 = List.range' 4283 143 ++ List.range' 4426 143 from (List.range'_append_1 (s := 4283) (m := 143) (n := 143)).symm, List.filter_append, b4283_143, b4426_143] <;> rfl
def Lb3997_572 := Lb3997_286 ++ Lb4283_286
theorem b3997_572 : ((List.range' 3997 572).filter quick) = Lb3997_572 := by
  rw [show List.range' 3997 572 = List.range' 3997 286 ++ List.range' 4283 286 from (List.range'_append_1 (s := 3997) (m := 286) (n := 286)).symm, List.filter_append, b3997_286, b4283_286] <;> rfl
def Lb3426_1143 := Lb3426_571 ++ Lb3997_572
theorem b3426_1143 : ((List.range' 3426 1143).filter quick) = Lb3426_1143 := by
  rw [show List.range' 3426 1143 = List.range' 3426 571 ++ List.range' 3997 572 from (List.range'_append_1 (s := 3426) (m := 571) (n := 572)).symm, List.filter_append, b3426_571, b3997_572] <;> rfl
def Lb2284_2285 := Lb2284_1142 ++ Lb3426_1143
theorem b2284_2285 : ((List.range' 2284 2285).filter quick) = Lb2284_2285 := by
  rw [show List.range' 2284 2285 = List.range' 2284 1142 ++ List.range' 3426 1143 from (List.range'_append_1 (s := 2284) (m := 1142) (n := 1143)).symm, List.filter_append, b2284_1142, b3426_1143] <;> rfl
def Lb0_4569 := Lb0_2284 ++ Lb2284_2285
theorem b0_4569 : ((List.range' 0 4569).filter quick) = Lb0_4569 := by
  rw [show List.range' 0 4569 = List.range' 0 2284 ++ List.range' 2284 2285 from (List.range'_append_1 (s := 0) (m := 2284) (n := 2285)).symm, List.filter_append, b0_2284, b2284_2285] <;> rfl
def primes := Lb0_4569.reverse
theorem list_cert : ((List.range (4568+1)).filter (fun p => decide p.Prime)).reverse = primes := by
  have eq : (List.range 4569).filter (fun p => decide p.Prime) = (List.range 4569).filter quick := by
    apply List.filter_congr
    intro t ht
    have h : t < 4569 := List.mem_range.mp ht
    exact Bool.eq_iff_iff.mpr (by simpa using (quick_spec (n := t) (by omega)).symm)
  rw [eq, List.range_eq_range', b0_4569] <;> rfl
theorem small_card : (Nat.primesLE 4568).card = 619 := by
  let l := ((List.range (4568+1)).filter (fun p => decide p.Prime)).reverse
  have hn : l.Nodup := List.nodup_reverse.mpr ((List.nodup_range).filter _)
  have heq : Nat.primesLE 4568 = l.toFinset := by
    ext n
    simp [l, Nat.mem_primesLE] <;> omega
  rw [heq, List.toFinset_card_of_nodup hn]
  change ((List.range (4568+1)).filter (fun p => decide p.Prime)).reverse.length = 619
  rw [list_cert]
  decide +kernel
end A247824Checked

/- Legendre sieve certificates for the first rank. -/
namespace A247824Checked
def s0 (t : Nat) := t
def s1 (t : Nat) := if t < 2 then (if t = 0 then 0 else 1) else s0 t - s0 (t / 2)
def s2 (t : Nat) := if t < 3 then (if t = 0 then 0 else 1) else s1 t - s1 (t / 3)
def s3 (t : Nat) := if t < 5 then (if t = 0 then 0 else 1) else s2 t - s2 (t / 5)
def s4 (t : Nat) := if t < 7 then (if t = 0 then 0 else 1) else s3 t - s3 (t / 7)
def s5 (t : Nat) := if t < 11 then (if t = 0 then 0 else 1) else s4 t - s4 (t / 11)
def s6 (t : Nat) := if t < 13 then (if t = 0 then 0 else 1) else s5 t - s5 (t / 13)
def s7 (t : Nat) := if t < 17 then (if t = 0 then 0 else 1) else s6 t - s6 (t / 17)
def s8 (t : Nat) := if t < 19 then (if t = 0 then 0 else 1) else s7 t - s7 (t / 19)
def s9 (t : Nat) := if t < 23 then (if t = 0 then 0 else 1) else s8 t - s8 (t / 23)
def s10 (t : Nat) := if t < 29 then (if t = 0 then 0 else 1) else s9 t - s9 (t / 29)
def s11 (t : Nat) := if t < 31 then (if t = 0 then 0 else 1) else s10 t - s10 (t / 31)
def s12 (t : Nat) := if t < 37 then (if t = 0 then 0 else 1) else s11 t - s11 (t / 37)
def s13 (t : Nat) := if t < 41 then (if t = 0 then 0 else 1) else s12 t - s12 (t / 41)
def s14 (t : Nat) := if t < 43 then (if t = 0 then 0 else 1) else s13 t - s13 (t / 43)
def s15 (t : Nat) := if t < 47 then (if t = 0 then 0 else 1) else s14 t - s14 (t / 47)
def s16 (t : Nat) := if t < 53 then (if t = 0 then 0 else 1) else s15 t - s15 (t / 53)
def s17 (t : Nat) := if t < 59 then (if t = 0 then 0 else 1) else s16 t - s16 (t / 59)
def s18 (t : Nat) := if t < 61 then (if t = 0 then 0 else 1) else s17 t - s17 (t / 61)
def s19 (t : Nat) := if t < 67 then (if t = 0 then 0 else 1) else s18 t - s18 (t / 67)
def s20 (t : Nat) := if t < 71 then (if t = 0 then 0 else 1) else s19 t - s19 (t / 71)
def s21 (t : Nat) := if t < 73 then (if t = 0 then 0 else 1) else s20 t - s20 (t / 73)
def s22 (t : Nat) := if t < 79 then (if t = 0 then 0 else 1) else s21 t - s21 (t / 79)
def s23 (t : Nat) := if t < 83 then (if t = 0 then 0 else 1) else s22 t - s22 (t / 83)
def s24 (t : Nat) := if t < 89 then (if t = 0 then 0 else 1) else s23 t - s23 (t / 89)
def s25 (t : Nat) := if t < 97 then (if t = 0 then 0 else 1) else s24 t - s24 (t / 97)
def s26 (t : Nat) := if t < 101 then (if t = 0 then 0 else 1) else s25 t - s25 (t / 101)
def s27 (t : Nat) := if t < 103 then (if t = 0 then 0 else 1) else s26 t - s26 (t / 103)
def s28 (t : Nat) := if t < 107 then (if t = 0 then 0 else 1) else s27 t - s27 (t / 107)
def s29 (t : Nat) := if t < 109 then (if t = 0 then 0 else 1) else s28 t - s28 (t / 109)
def s30 (t : Nat) := if t < 113 then (if t = 0 then 0 else 1) else s29 t - s29 (t / 113)
def s31 (t : Nat) := if t < 127 then (if t = 0 then 0 else 1) else s30 t - s30 (t / 127)
def s32 (t : Nat) := if t < 131 then (if t = 0 then 0 else 1) else s31 t - s31 (t / 131)
def s33 (t : Nat) := if t < 137 then (if t = 0 then 0 else 1) else s32 t - s32 (t / 137)
def s34 (t : Nat) := if t < 139 then (if t = 0 then 0 else 1) else s33 t - s33 (t / 139)
def s35 (t : Nat) := if t < 149 then (if t = 0 then 0 else 1) else s34 t - s34 (t / 149)
def s36 (t : Nat) := if t < 151 then (if t = 0 then 0 else 1) else s35 t - s35 (t / 151)
def s37 (t : Nat) := if t < 157 then (if t = 0 then 0 else 1) else s36 t - s36 (t / 157)
def s38 (t : Nat) := if t < 163 then (if t = 0 then 0 else 1) else s37 t - s37 (t / 163)
def s39 (t : Nat) := if t < 167 then (if t = 0 then 0 else 1) else s38 t - s38 (t / 167)
def s40 (t : Nat) := if t < 173 then (if t = 0 then 0 else 1) else s39 t - s39 (t / 173)
def s41 (t : Nat) := if t < 179 then (if t = 0 then 0 else 1) else s40 t - s40 (t / 179)
def s42 (t : Nat) := if t < 181 then (if t = 0 then 0 else 1) else s41 t - s41 (t / 181)
def s43 (t : Nat) := if t < 191 then (if t = 0 then 0 else 1) else s42 t - s42 (t / 191)
def s44 (t : Nat) := if t < 193 then (if t = 0 then 0 else 1) else s43 t - s43 (t / 193)
def s45 (t : Nat) := if t < 197 then (if t = 0 then 0 else 1) else s44 t - s44 (t / 197)
def s46 (t : Nat) := if t < 199 then (if t = 0 then 0 else 1) else s45 t - s45 (t / 199)
def s47 (t : Nat) := if t < 211 then (if t = 0 then 0 else 1) else s46 t - s46 (t / 211)
def s48 (t : Nat) := if t < 223 then (if t = 0 then 0 else 1) else s47 t - s47 (t / 223)
def s49 (t : Nat) := if t < 227 then (if t = 0 then 0 else 1) else s48 t - s48 (t / 227)
def s50 (t : Nat) := if t < 229 then (if t = 0 then 0 else 1) else s49 t - s49 (t / 229)
def s51 (t : Nat) := if t < 233 then (if t = 0 then 0 else 1) else s50 t - s50 (t / 233)
def s52 (t : Nat) := if t < 239 then (if t = 0 then 0 else 1) else s51 t - s51 (t / 239)
def s53 (t : Nat) := if t < 241 then (if t = 0 then 0 else 1) else s52 t - s52 (t / 241)
def s54 (t : Nat) := if t < 251 then (if t = 0 then 0 else 1) else s53 t - s53 (t / 251)
def s55 (t : Nat) := if t < 257 then (if t = 0 then 0 else 1) else s54 t - s54 (t / 257)
def s56 (t : Nat) := if t < 263 then (if t = 0 then 0 else 1) else s55 t - s55 (t / 263)
def s57 (t : Nat) := if t < 269 then (if t = 0 then 0 else 1) else s56 t - s56 (t / 269)
def s58 (t : Nat) := if t < 271 then (if t = 0 then 0 else 1) else s57 t - s57 (t / 271)
def s59 (t : Nat) := if t < 277 then (if t = 0 then 0 else 1) else s58 t - s58 (t / 277)
def s60 (t : Nat) := if t < 281 then (if t = 0 then 0 else 1) else s59 t - s59 (t / 281)
def s61 (t : Nat) := if t < 283 then (if t = 0 then 0 else 1) else s60 t - s60 (t / 283)
def s62 (t : Nat) := if t < 293 then (if t = 0 then 0 else 1) else s61 t - s61 (t / 293)
def s63 (t : Nat) := if t < 307 then (if t = 0 then 0 else 1) else s62 t - s62 (t / 307)
def s64 (t : Nat) := if t < 311 then (if t = 0 then 0 else 1) else s63 t - s63 (t / 311)
def s65 (t : Nat) := if t < 313 then (if t = 0 then 0 else 1) else s64 t - s64 (t / 313)
def s66 (t : Nat) := if t < 317 then (if t = 0 then 0 else 1) else s65 t - s65 (t / 317)
def s67 (t : Nat) := if t < 331 then (if t = 0 then 0 else 1) else s66 t - s66 (t / 331)
def s68 (t : Nat) := if t < 337 then (if t = 0 then 0 else 1) else s67 t - s67 (t / 337)
def s69 (t : Nat) := if t < 347 then (if t = 0 then 0 else 1) else s68 t - s68 (t / 347)
def s70 (t : Nat) := if t < 349 then (if t = 0 then 0 else 1) else s69 t - s69 (t / 349)
def s71 (t : Nat) := if t < 353 then (if t = 0 then 0 else 1) else s70 t - s70 (t / 353)
def s72 (t : Nat) := if t < 359 then (if t = 0 then 0 else 1) else s71 t - s71 (t / 359)
def s73 (t : Nat) := if t < 367 then (if t = 0 then 0 else 1) else s72 t - s72 (t / 367)
def s74 (t : Nat) := if t < 373 then (if t = 0 then 0 else 1) else s73 t - s73 (t / 373)
def s75 (t : Nat) := if t < 379 then (if t = 0 then 0 else 1) else s74 t - s74 (t / 379)
def s76 (t : Nat) := if t < 383 then (if t = 0 then 0 else 1) else s75 t - s75 (t / 383)
def s77 (t : Nat) := if t < 389 then (if t = 0 then 0 else 1) else s76 t - s76 (t / 389)
def s78 (t : Nat) := if t < 397 then (if t = 0 then 0 else 1) else s77 t - s77 (t / 397)
def s79 (t : Nat) := if t < 401 then (if t = 0 then 0 else 1) else s78 t - s78 (t / 401)
def s80 (t : Nat) := if t < 409 then (if t = 0 then 0 else 1) else s79 t - s79 (t / 409)
def s81 (t : Nat) := if t < 419 then (if t = 0 then 0 else 1) else s80 t - s80 (t / 419)
def s82 (t : Nat) := if t < 421 then (if t = 0 then 0 else 1) else s81 t - s81 (t / 421)
def s83 (t : Nat) := if t < 431 then (if t = 0 then 0 else 1) else s82 t - s82 (t / 431)
def s84 (t : Nat) := if t < 433 then (if t = 0 then 0 else 1) else s83 t - s83 (t / 433)
def s85 (t : Nat) := if t < 439 then (if t = 0 then 0 else 1) else s84 t - s84 (t / 439)
def s86 (t : Nat) := if t < 443 then (if t = 0 then 0 else 1) else s85 t - s85 (t / 443)
def s87 (t : Nat) := if t < 449 then (if t = 0 then 0 else 1) else s86 t - s86 (t / 449)
def s88 (t : Nat) := if t < 457 then (if t = 0 then 0 else 1) else s87 t - s87 (t / 457)
def s89 (t : Nat) := if t < 461 then (if t = 0 then 0 else 1) else s88 t - s88 (t / 461)
def s90 (t : Nat) := if t < 463 then (if t = 0 then 0 else 1) else s89 t - s89 (t / 463)
def s91 (t : Nat) := if t < 467 then (if t = 0 then 0 else 1) else s90 t - s90 (t / 467)
def s92 (t : Nat) := if t < 479 then (if t = 0 then 0 else 1) else s91 t - s91 (t / 479)
def s93 (t : Nat) := if t < 487 then (if t = 0 then 0 else 1) else s92 t - s92 (t / 487)
def s94 (t : Nat) := if t < 491 then (if t = 0 then 0 else 1) else s93 t - s93 (t / 491)
def s95 (t : Nat) := if t < 499 then (if t = 0 then 0 else 1) else s94 t - s94 (t / 499)
def s96 (t : Nat) := if t < 503 then (if t = 0 then 0 else 1) else s95 t - s95 (t / 503)
def s97 (t : Nat) := if t < 509 then (if t = 0 then 0 else 1) else s96 t - s96 (t / 509)
def s98 (t : Nat) := if t < 521 then (if t = 0 then 0 else 1) else s97 t - s97 (t / 521)
def s99 (t : Nat) := if t < 523 then (if t = 0 then 0 else 1) else s98 t - s98 (t / 523)
def s100 (t : Nat) := if t < 541 then (if t = 0 then 0 else 1) else s99 t - s99 (t / 541)
def s101 (t : Nat) := if t < 547 then (if t = 0 then 0 else 1) else s100 t - s100 (t / 547)
def s102 (t : Nat) := if t < 557 then (if t = 0 then 0 else 1) else s101 t - s101 (t / 557)
def s103 (t : Nat) := if t < 563 then (if t = 0 then 0 else 1) else s102 t - s102 (t / 563)
def s104 (t : Nat) := if t < 569 then (if t = 0 then 0 else 1) else s103 t - s103 (t / 569)
def s105 (t : Nat) := if t < 571 then (if t = 0 then 0 else 1) else s104 t - s104 (t / 571)
def s106 (t : Nat) := if t < 577 then (if t = 0 then 0 else 1) else s105 t - s105 (t / 577)
def s107 (t : Nat) := if t < 587 then (if t = 0 then 0 else 1) else s106 t - s106 (t / 587)
def s108 (t : Nat) := if t < 593 then (if t = 0 then 0 else 1) else s107 t - s107 (t / 593)
def s109 (t : Nat) := if t < 599 then (if t = 0 then 0 else 1) else s108 t - s108 (t / 599)
def s110 (t : Nat) := if t < 601 then (if t = 0 then 0 else 1) else s109 t - s109 (t / 601)
def s111 (t : Nat) := if t < 607 then (if t = 0 then 0 else 1) else s110 t - s110 (t / 607)
def s112 (t : Nat) := if t < 613 then (if t = 0 then 0 else 1) else s111 t - s111 (t / 613)
def s113 (t : Nat) := if t < 617 then (if t = 0 then 0 else 1) else s112 t - s112 (t / 617)
def s114 (t : Nat) := if t < 619 then (if t = 0 then 0 else 1) else s113 t - s113 (t / 619)
def s115 (t : Nat) := if t < 631 then (if t = 0 then 0 else 1) else s114 t - s114 (t / 631)
def s116 (t : Nat) := if t < 641 then (if t = 0 then 0 else 1) else s115 t - s115 (t / 641)
def s117 (t : Nat) := if t < 643 then (if t = 0 then 0 else 1) else s116 t - s116 (t / 643)
def s118 (t : Nat) := if t < 647 then (if t = 0 then 0 else 1) else s117 t - s117 (t / 647)
def s119 (t : Nat) := if t < 653 then (if t = 0 then 0 else 1) else s118 t - s118 (t / 653)
def s120 (t : Nat) := if t < 659 then (if t = 0 then 0 else 1) else s119 t - s119 (t / 659)
def s121 (t : Nat) := if t < 661 then (if t = 0 then 0 else 1) else s120 t - s120 (t / 661)
def s122 (t : Nat) := if t < 673 then (if t = 0 then 0 else 1) else s121 t - s121 (t / 673)
def s123 (t : Nat) := if t < 677 then (if t = 0 then 0 else 1) else s122 t - s122 (t / 677)
def s124 (t : Nat) := if t < 683 then (if t = 0 then 0 else 1) else s123 t - s123 (t / 683)
def s125 (t : Nat) := if t < 691 then (if t = 0 then 0 else 1) else s124 t - s124 (t / 691)
def s126 (t : Nat) := if t < 701 then (if t = 0 then 0 else 1) else s125 t - s125 (t / 701)
def s127 (t : Nat) := if t < 709 then (if t = 0 then 0 else 1) else s126 t - s126 (t / 709)
def s128 (t : Nat) := if t < 719 then (if t = 0 then 0 else 1) else s127 t - s127 (t / 719)
def s129 (t : Nat) := if t < 727 then (if t = 0 then 0 else 1) else s128 t - s128 (t / 727)
def s130 (t : Nat) := if t < 733 then (if t = 0 then 0 else 1) else s129 t - s129 (t / 733)
def s131 (t : Nat) := if t < 739 then (if t = 0 then 0 else 1) else s130 t - s130 (t / 739)
def s132 (t : Nat) := if t < 743 then (if t = 0 then 0 else 1) else s131 t - s131 (t / 743)
def s133 (t : Nat) := if t < 751 then (if t = 0 then 0 else 1) else s132 t - s132 (t / 751)
def s134 (t : Nat) := if t < 757 then (if t = 0 then 0 else 1) else s133 t - s133 (t / 757)
def s135 (t : Nat) := if t < 761 then (if t = 0 then 0 else 1) else s134 t - s134 (t / 761)
def s136 (t : Nat) := if t < 769 then (if t = 0 then 0 else 1) else s135 t - s135 (t / 769)
def s137 (t : Nat) := if t < 773 then (if t = 0 then 0 else 1) else s136 t - s136 (t / 773)
def s138 (t : Nat) := if t < 787 then (if t = 0 then 0 else 1) else s137 t - s137 (t / 787)
def s139 (t : Nat) := if t < 797 then (if t = 0 then 0 else 1) else s138 t - s138 (t / 797)
def s140 (t : Nat) := if t < 809 then (if t = 0 then 0 else 1) else s139 t - s139 (t / 809)
def s141 (t : Nat) := if t < 811 then (if t = 0 then 0 else 1) else s140 t - s140 (t / 811)
def s142 (t : Nat) := if t < 821 then (if t = 0 then 0 else 1) else s141 t - s141 (t / 821)
def s143 (t : Nat) := if t < 823 then (if t = 0 then 0 else 1) else s142 t - s142 (t / 823)
def s144 (t : Nat) := if t < 827 then (if t = 0 then 0 else 1) else s143 t - s143 (t / 827)
def s145 (t : Nat) := if t < 829 then (if t = 0 then 0 else 1) else s144 t - s144 (t / 829)
def s146 (t : Nat) := if t < 839 then (if t = 0 then 0 else 1) else s145 t - s145 (t / 839)
def s147 (t : Nat) := if t < 853 then (if t = 0 then 0 else 1) else s146 t - s146 (t / 853)
def s148 (t : Nat) := if t < 857 then (if t = 0 then 0 else 1) else s147 t - s147 (t / 857)
def s149 (t : Nat) := if t < 859 then (if t = 0 then 0 else 1) else s148 t - s148 (t / 859)
def s150 (t : Nat) := if t < 863 then (if t = 0 then 0 else 1) else s149 t - s149 (t / 863)
def s151 (t : Nat) := if t < 877 then (if t = 0 then 0 else 1) else s150 t - s150 (t / 877)
def s152 (t : Nat) := if t < 881 then (if t = 0 then 0 else 1) else s151 t - s151 (t / 881)
def s153 (t : Nat) := if t < 883 then (if t = 0 then 0 else 1) else s152 t - s152 (t / 883)
def s154 (t : Nat) := if t < 887 then (if t = 0 then 0 else 1) else s153 t - s153 (t / 887)
def s155 (t : Nat) := if t < 907 then (if t = 0 then 0 else 1) else s154 t - s154 (t / 907)
def s156 (t : Nat) := if t < 911 then (if t = 0 then 0 else 1) else s155 t - s155 (t / 911)
def s157 (t : Nat) := if t < 919 then (if t = 0 then 0 else 1) else s156 t - s156 (t / 919)
def s158 (t : Nat) := if t < 929 then (if t = 0 then 0 else 1) else s157 t - s157 (t / 929)
def s159 (t : Nat) := if t < 937 then (if t = 0 then 0 else 1) else s158 t - s158 (t / 937)
def s160 (t : Nat) := if t < 941 then (if t = 0 then 0 else 1) else s159 t - s159 (t / 941)
def s161 (t : Nat) := if t < 947 then (if t = 0 then 0 else 1) else s160 t - s160 (t / 947)
def s162 (t : Nat) := if t < 953 then (if t = 0 then 0 else 1) else s161 t - s161 (t / 953)
def s163 (t : Nat) := if t < 967 then (if t = 0 then 0 else 1) else s162 t - s162 (t / 967)
def s164 (t : Nat) := if t < 971 then (if t = 0 then 0 else 1) else s163 t - s163 (t / 971)
def s165 (t : Nat) := if t < 977 then (if t = 0 then 0 else 1) else s164 t - s164 (t / 977)
def s166 (t : Nat) := if t < 983 then (if t = 0 then 0 else 1) else s165 t - s165 (t / 983)
def s167 (t : Nat) := if t < 991 then (if t = 0 then 0 else 1) else s166 t - s166 (t / 991)
def s168 (t : Nat) := if t < 997 then (if t = 0 then 0 else 1) else s167 t - s167 (t / 997)
def s169 (t : Nat) := if t < 1009 then (if t = 0 then 0 else 1) else s168 t - s168 (t / 1009)
def s170 (t : Nat) := if t < 1013 then (if t = 0 then 0 else 1) else s169 t - s169 (t / 1013)
def s171 (t : Nat) := if t < 1019 then (if t = 0 then 0 else 1) else s170 t - s170 (t / 1019)
def s172 (t : Nat) := if t < 1021 then (if t = 0 then 0 else 1) else s171 t - s171 (t / 1021)
def s173 (t : Nat) := if t < 1031 then (if t = 0 then 0 else 1) else s172 t - s172 (t / 1031)
def s174 (t : Nat) := if t < 1033 then (if t = 0 then 0 else 1) else s173 t - s173 (t / 1033)
def s175 (t : Nat) := if t < 1039 then (if t = 0 then 0 else 1) else s174 t - s174 (t / 1039)
def s176 (t : Nat) := if t < 1049 then (if t = 0 then 0 else 1) else s175 t - s175 (t / 1049)
def s177 (t : Nat) := if t < 1051 then (if t = 0 then 0 else 1) else s176 t - s176 (t / 1051)
def s178 (t : Nat) := if t < 1061 then (if t = 0 then 0 else 1) else s177 t - s177 (t / 1061)
def s179 (t : Nat) := if t < 1063 then (if t = 0 then 0 else 1) else s178 t - s178 (t / 1063)
def s180 (t : Nat) := if t < 1069 then (if t = 0 then 0 else 1) else s179 t - s179 (t / 1069)
def s181 (t : Nat) := if t < 1087 then (if t = 0 then 0 else 1) else s180 t - s180 (t / 1087)
def s182 (t : Nat) := if t < 1091 then (if t = 0 then 0 else 1) else s181 t - s181 (t / 1091)
def s183 (t : Nat) := if t < 1093 then (if t = 0 then 0 else 1) else s182 t - s182 (t / 1093)
def s184 (t : Nat) := if t < 1097 then (if t = 0 then 0 else 1) else s183 t - s183 (t / 1097)
def s185 (t : Nat) := if t < 1103 then (if t = 0 then 0 else 1) else s184 t - s184 (t / 1103)
def s186 (t : Nat) := if t < 1109 then (if t = 0 then 0 else 1) else s185 t - s185 (t / 1109)
def s187 (t : Nat) := if t < 1117 then (if t = 0 then 0 else 1) else s186 t - s186 (t / 1117)
def s188 (t : Nat) := if t < 1123 then (if t = 0 then 0 else 1) else s187 t - s187 (t / 1123)
def s189 (t : Nat) := if t < 1129 then (if t = 0 then 0 else 1) else s188 t - s188 (t / 1129)
def s190 (t : Nat) := if t < 1151 then (if t = 0 then 0 else 1) else s189 t - s189 (t / 1151)
def s191 (t : Nat) := if t < 1153 then (if t = 0 then 0 else 1) else s190 t - s190 (t / 1153)
def s192 (t : Nat) := if t < 1163 then (if t = 0 then 0 else 1) else s191 t - s191 (t / 1163)
def s193 (t : Nat) := if t < 1171 then (if t = 0 then 0 else 1) else s192 t - s192 (t / 1171)
def s194 (t : Nat) := if t < 1181 then (if t = 0 then 0 else 1) else s193 t - s193 (t / 1181)
def s195 (t : Nat) := if t < 1187 then (if t = 0 then 0 else 1) else s194 t - s194 (t / 1187)
def s196 (t : Nat) := if t < 1193 then (if t = 0 then 0 else 1) else s195 t - s195 (t / 1193)
def s197 (t : Nat) := if t < 1201 then (if t = 0 then 0 else 1) else s196 t - s196 (t / 1201)
def s198 (t : Nat) := if t < 1213 then (if t = 0 then 0 else 1) else s197 t - s197 (t / 1213)
def s199 (t : Nat) := if t < 1217 then (if t = 0 then 0 else 1) else s198 t - s198 (t / 1217)
def s200 (t : Nat) := if t < 1223 then (if t = 0 then 0 else 1) else s199 t - s199 (t / 1223)
def s201 (t : Nat) := if t < 1229 then (if t = 0 then 0 else 1) else s200 t - s200 (t / 1229)
def s202 (t : Nat) := if t < 1231 then (if t = 0 then 0 else 1) else s201 t - s201 (t / 1231)
def s203 (t : Nat) := if t < 1237 then (if t = 0 then 0 else 1) else s202 t - s202 (t / 1237)
def s204 (t : Nat) := if t < 1249 then (if t = 0 then 0 else 1) else s203 t - s203 (t / 1249)
def s205 (t : Nat) := if t < 1259 then (if t = 0 then 0 else 1) else s204 t - s204 (t / 1259)
def s206 (t : Nat) := if t < 1277 then (if t = 0 then 0 else 1) else s205 t - s205 (t / 1277)
def s207 (t : Nat) := if t < 1279 then (if t = 0 then 0 else 1) else s206 t - s206 (t / 1279)
def s208 (t : Nat) := if t < 1283 then (if t = 0 then 0 else 1) else s207 t - s207 (t / 1283)
def s209 (t : Nat) := if t < 1289 then (if t = 0 then 0 else 1) else s208 t - s208 (t / 1289)
def s210 (t : Nat) := if t < 1291 then (if t = 0 then 0 else 1) else s209 t - s209 (t / 1291)
def s211 (t : Nat) := if t < 1297 then (if t = 0 then 0 else 1) else s210 t - s210 (t / 1297)
def s212 (t : Nat) := if t < 1301 then (if t = 0 then 0 else 1) else s211 t - s211 (t / 1301)
def s213 (t : Nat) := if t < 1303 then (if t = 0 then 0 else 1) else s212 t - s212 (t / 1303)
def s214 (t : Nat) := if t < 1307 then (if t = 0 then 0 else 1) else s213 t - s213 (t / 1307)
def s215 (t : Nat) := if t < 1319 then (if t = 0 then 0 else 1) else s214 t - s214 (t / 1319)
def s216 (t : Nat) := if t < 1321 then (if t = 0 then 0 else 1) else s215 t - s215 (t / 1321)
def s217 (t : Nat) := if t < 1327 then (if t = 0 then 0 else 1) else s216 t - s216 (t / 1327)
def s218 (t : Nat) := if t < 1361 then (if t = 0 then 0 else 1) else s217 t - s217 (t / 1361)
def s219 (t : Nat) := if t < 1367 then (if t = 0 then 0 else 1) else s218 t - s218 (t / 1367)
def s220 (t : Nat) := if t < 1373 then (if t = 0 then 0 else 1) else s219 t - s219 (t / 1373)
def s221 (t : Nat) := if t < 1381 then (if t = 0 then 0 else 1) else s220 t - s220 (t / 1381)
def s222 (t : Nat) := if t < 1399 then (if t = 0 then 0 else 1) else s221 t - s221 (t / 1399)
def s223 (t : Nat) := if t < 1409 then (if t = 0 then 0 else 1) else s222 t - s222 (t / 1409)
def s224 (t : Nat) := if t < 1423 then (if t = 0 then 0 else 1) else s223 t - s223 (t / 1423)
def s225 (t : Nat) := if t < 1427 then (if t = 0 then 0 else 1) else s224 t - s224 (t / 1427)
def s226 (t : Nat) := if t < 1429 then (if t = 0 then 0 else 1) else s225 t - s225 (t / 1429)
def s227 (t : Nat) := if t < 1433 then (if t = 0 then 0 else 1) else s226 t - s226 (t / 1433)
def s228 (t : Nat) := if t < 1439 then (if t = 0 then 0 else 1) else s227 t - s227 (t / 1439)
def s229 (t : Nat) := if t < 1447 then (if t = 0 then 0 else 1) else s228 t - s228 (t / 1447)
def s230 (t : Nat) := if t < 1451 then (if t = 0 then 0 else 1) else s229 t - s229 (t / 1451)
def s231 (t : Nat) := if t < 1453 then (if t = 0 then 0 else 1) else s230 t - s230 (t / 1453)
def s232 (t : Nat) := if t < 1459 then (if t = 0 then 0 else 1) else s231 t - s231 (t / 1459)
def s233 (t : Nat) := if t < 1471 then (if t = 0 then 0 else 1) else s232 t - s232 (t / 1471)
def s234 (t : Nat) := if t < 1481 then (if t = 0 then 0 else 1) else s233 t - s233 (t / 1481)
def s235 (t : Nat) := if t < 1483 then (if t = 0 then 0 else 1) else s234 t - s234 (t / 1483)
def s236 (t : Nat) := if t < 1487 then (if t = 0 then 0 else 1) else s235 t - s235 (t / 1487)
def s237 (t : Nat) := if t < 1489 then (if t = 0 then 0 else 1) else s236 t - s236 (t / 1489)
def s238 (t : Nat) := if t < 1493 then (if t = 0 then 0 else 1) else s237 t - s237 (t / 1493)
def s239 (t : Nat) := if t < 1499 then (if t = 0 then 0 else 1) else s238 t - s238 (t / 1499)
def s240 (t : Nat) := if t < 1511 then (if t = 0 then 0 else 1) else s239 t - s239 (t / 1511)
def s241 (t : Nat) := if t < 1523 then (if t = 0 then 0 else 1) else s240 t - s240 (t / 1523)
def s242 (t : Nat) := if t < 1531 then (if t = 0 then 0 else 1) else s241 t - s241 (t / 1531)
def s243 (t : Nat) := if t < 1543 then (if t = 0 then 0 else 1) else s242 t - s242 (t / 1543)
def s244 (t : Nat) := if t < 1549 then (if t = 0 then 0 else 1) else s243 t - s243 (t / 1549)
def s245 (t : Nat) := if t < 1553 then (if t = 0 then 0 else 1) else s244 t - s244 (t / 1553)
def s246 (t : Nat) := if t < 1559 then (if t = 0 then 0 else 1) else s245 t - s245 (t / 1559)
def s247 (t : Nat) := if t < 1567 then (if t = 0 then 0 else 1) else s246 t - s246 (t / 1567)
def s248 (t : Nat) := if t < 1571 then (if t = 0 then 0 else 1) else s247 t - s247 (t / 1571)
def s249 (t : Nat) := if t < 1579 then (if t = 0 then 0 else 1) else s248 t - s248 (t / 1579)
def s250 (t : Nat) := if t < 1583 then (if t = 0 then 0 else 1) else s249 t - s249 (t / 1583)
def s251 (t : Nat) := if t < 1597 then (if t = 0 then 0 else 1) else s250 t - s250 (t / 1597)
def s252 (t : Nat) := if t < 1601 then (if t = 0 then 0 else 1) else s251 t - s251 (t / 1601)
def s253 (t : Nat) := if t < 1607 then (if t = 0 then 0 else 1) else s252 t - s252 (t / 1607)
def s254 (t : Nat) := if t < 1609 then (if t = 0 then 0 else 1) else s253 t - s253 (t / 1609)
def s255 (t : Nat) := if t < 1613 then (if t = 0 then 0 else 1) else s254 t - s254 (t / 1613)
def s256 (t : Nat) := if t < 1619 then (if t = 0 then 0 else 1) else s255 t - s255 (t / 1619)
def s257 (t : Nat) := if t < 1621 then (if t = 0 then 0 else 1) else s256 t - s256 (t / 1621)
def s258 (t : Nat) := if t < 1627 then (if t = 0 then 0 else 1) else s257 t - s257 (t / 1627)
def s259 (t : Nat) := if t < 1637 then (if t = 0 then 0 else 1) else s258 t - s258 (t / 1637)
def s260 (t : Nat) := if t < 1657 then (if t = 0 then 0 else 1) else s259 t - s259 (t / 1657)
def s261 (t : Nat) := if t < 1663 then (if t = 0 then 0 else 1) else s260 t - s260 (t / 1663)
def s262 (t : Nat) := if t < 1667 then (if t = 0 then 0 else 1) else s261 t - s261 (t / 1667)
def s263 (t : Nat) := if t < 1669 then (if t = 0 then 0 else 1) else s262 t - s262 (t / 1669)
def s264 (t : Nat) := if t < 1693 then (if t = 0 then 0 else 1) else s263 t - s263 (t / 1693)
def s265 (t : Nat) := if t < 1697 then (if t = 0 then 0 else 1) else s264 t - s264 (t / 1697)
def s266 (t : Nat) := if t < 1699 then (if t = 0 then 0 else 1) else s265 t - s265 (t / 1699)
def s267 (t : Nat) := if t < 1709 then (if t = 0 then 0 else 1) else s266 t - s266 (t / 1709)
def s268 (t : Nat) := if t < 1721 then (if t = 0 then 0 else 1) else s267 t - s267 (t / 1721)
def s269 (t : Nat) := if t < 1723 then (if t = 0 then 0 else 1) else s268 t - s268 (t / 1723)
def s270 (t : Nat) := if t < 1733 then (if t = 0 then 0 else 1) else s269 t - s269 (t / 1733)
def s271 (t : Nat) := if t < 1741 then (if t = 0 then 0 else 1) else s270 t - s270 (t / 1741)
def s272 (t : Nat) := if t < 1747 then (if t = 0 then 0 else 1) else s271 t - s271 (t / 1747)
def s273 (t : Nat) := if t < 1753 then (if t = 0 then 0 else 1) else s272 t - s272 (t / 1753)
def s274 (t : Nat) := if t < 1759 then (if t = 0 then 0 else 1) else s273 t - s273 (t / 1759)
def s275 (t : Nat) := if t < 1777 then (if t = 0 then 0 else 1) else s274 t - s274 (t / 1777)
def s276 (t : Nat) := if t < 1783 then (if t = 0 then 0 else 1) else s275 t - s275 (t / 1783)
def s277 (t : Nat) := if t < 1787 then (if t = 0 then 0 else 1) else s276 t - s276 (t / 1787)
def s278 (t : Nat) := if t < 1789 then (if t = 0 then 0 else 1) else s277 t - s277 (t / 1789)
def s279 (t : Nat) := if t < 1801 then (if t = 0 then 0 else 1) else s278 t - s278 (t / 1801)
def s280 (t : Nat) := if t < 1811 then (if t = 0 then 0 else 1) else s279 t - s279 (t / 1811)
def s281 (t : Nat) := if t < 1823 then (if t = 0 then 0 else 1) else s280 t - s280 (t / 1823)
def s282 (t : Nat) := if t < 1831 then (if t = 0 then 0 else 1) else s281 t - s281 (t / 1831)
def s283 (t : Nat) := if t < 1847 then (if t = 0 then 0 else 1) else s282 t - s282 (t / 1847)
def s284 (t : Nat) := if t < 1861 then (if t = 0 then 0 else 1) else s283 t - s283 (t / 1861)
def s285 (t : Nat) := if t < 1867 then (if t = 0 then 0 else 1) else s284 t - s284 (t / 1867)
def s286 (t : Nat) := if t < 1871 then (if t = 0 then 0 else 1) else s285 t - s285 (t / 1871)
def s287 (t : Nat) := if t < 1873 then (if t = 0 then 0 else 1) else s286 t - s286 (t / 1873)
def s288 (t : Nat) := if t < 1877 then (if t = 0 then 0 else 1) else s287 t - s287 (t / 1877)
def s289 (t : Nat) := if t < 1879 then (if t = 0 then 0 else 1) else s288 t - s288 (t / 1879)
def s290 (t : Nat) := if t < 1889 then (if t = 0 then 0 else 1) else s289 t - s289 (t / 1889)
def s291 (t : Nat) := if t < 1901 then (if t = 0 then 0 else 1) else s290 t - s290 (t / 1901)
def s292 (t : Nat) := if t < 1907 then (if t = 0 then 0 else 1) else s291 t - s291 (t / 1907)
def s293 (t : Nat) := if t < 1913 then (if t = 0 then 0 else 1) else s292 t - s292 (t / 1913)
def s294 (t : Nat) := if t < 1931 then (if t = 0 then 0 else 1) else s293 t - s293 (t / 1931)
def s295 (t : Nat) := if t < 1933 then (if t = 0 then 0 else 1) else s294 t - s294 (t / 1933)
def s296 (t : Nat) := if t < 1949 then (if t = 0 then 0 else 1) else s295 t - s295 (t / 1949)
def s297 (t : Nat) := if t < 1951 then (if t = 0 then 0 else 1) else s296 t - s296 (t / 1951)
def s298 (t : Nat) := if t < 1973 then (if t = 0 then 0 else 1) else s297 t - s297 (t / 1973)
def s299 (t : Nat) := if t < 1979 then (if t = 0 then 0 else 1) else s298 t - s298 (t / 1979)
def s300 (t : Nat) := if t < 1987 then (if t = 0 then 0 else 1) else s299 t - s299 (t / 1987)
def s301 (t : Nat) := if t < 1993 then (if t = 0 then 0 else 1) else s300 t - s300 (t / 1993)
def s302 (t : Nat) := if t < 1997 then (if t = 0 then 0 else 1) else s301 t - s301 (t / 1997)
def s303 (t : Nat) := if t < 1999 then (if t = 0 then 0 else 1) else s302 t - s302 (t / 1999)
def s304 (t : Nat) := if t < 2003 then (if t = 0 then 0 else 1) else s303 t - s303 (t / 2003)
def s305 (t : Nat) := if t < 2011 then (if t = 0 then 0 else 1) else s304 t - s304 (t / 2011)
def s306 (t : Nat) := if t < 2017 then (if t = 0 then 0 else 1) else s305 t - s305 (t / 2017)
def s307 (t : Nat) := if t < 2027 then (if t = 0 then 0 else 1) else s306 t - s306 (t / 2027)
def s308 (t : Nat) := if t < 2029 then (if t = 0 then 0 else 1) else s307 t - s307 (t / 2029)
def s309 (t : Nat) := if t < 2039 then (if t = 0 then 0 else 1) else s308 t - s308 (t / 2039)
def s310 (t : Nat) := if t < 2053 then (if t = 0 then 0 else 1) else s309 t - s309 (t / 2053)
def s311 (t : Nat) := if t < 2063 then (if t = 0 then 0 else 1) else s310 t - s310 (t / 2063)
def s312 (t : Nat) := if t < 2069 then (if t = 0 then 0 else 1) else s311 t - s311 (t / 2069)
def s313 (t : Nat) := if t < 2081 then (if t = 0 then 0 else 1) else s312 t - s312 (t / 2081)
def s314 (t : Nat) := if t < 2083 then (if t = 0 then 0 else 1) else s313 t - s313 (t / 2083)
def s315 (t : Nat) := if t < 2087 then (if t = 0 then 0 else 1) else s314 t - s314 (t / 2087)
def s316 (t : Nat) := if t < 2089 then (if t = 0 then 0 else 1) else s315 t - s315 (t / 2089)
def s317 (t : Nat) := if t < 2099 then (if t = 0 then 0 else 1) else s316 t - s316 (t / 2099)
def s318 (t : Nat) := if t < 2111 then (if t = 0 then 0 else 1) else s317 t - s317 (t / 2111)
def s319 (t : Nat) := if t < 2113 then (if t = 0 then 0 else 1) else s318 t - s318 (t / 2113)
def s320 (t : Nat) := if t < 2129 then (if t = 0 then 0 else 1) else s319 t - s319 (t / 2129)
def s321 (t : Nat) := if t < 2131 then (if t = 0 then 0 else 1) else s320 t - s320 (t / 2131)
def s322 (t : Nat) := if t < 2137 then (if t = 0 then 0 else 1) else s321 t - s321 (t / 2137)
def s323 (t : Nat) := if t < 2141 then (if t = 0 then 0 else 1) else s322 t - s322 (t / 2141)
def s324 (t : Nat) := if t < 2143 then (if t = 0 then 0 else 1) else s323 t - s323 (t / 2143)
def s325 (t : Nat) := if t < 2153 then (if t = 0 then 0 else 1) else s324 t - s324 (t / 2153)
def s326 (t : Nat) := if t < 2161 then (if t = 0 then 0 else 1) else s325 t - s325 (t / 2161)
def s327 (t : Nat) := if t < 2179 then (if t = 0 then 0 else 1) else s326 t - s326 (t / 2179)
def s328 (t : Nat) := if t < 2203 then (if t = 0 then 0 else 1) else s327 t - s327 (t / 2203)
def s329 (t : Nat) := if t < 2207 then (if t = 0 then 0 else 1) else s328 t - s328 (t / 2207)
def s330 (t : Nat) := if t < 2213 then (if t = 0 then 0 else 1) else s329 t - s329 (t / 2213)
def s331 (t : Nat) := if t < 2221 then (if t = 0 then 0 else 1) else s330 t - s330 (t / 2221)
def s332 (t : Nat) := if t < 2237 then (if t = 0 then 0 else 1) else s331 t - s331 (t / 2237)
def s333 (t : Nat) := if t < 2239 then (if t = 0 then 0 else 1) else s332 t - s332 (t / 2239)
def s334 (t : Nat) := if t < 2243 then (if t = 0 then 0 else 1) else s333 t - s333 (t / 2243)
def s335 (t : Nat) := if t < 2251 then (if t = 0 then 0 else 1) else s334 t - s334 (t / 2251)
def s336 (t : Nat) := if t < 2267 then (if t = 0 then 0 else 1) else s335 t - s335 (t / 2267)
def s337 (t : Nat) := if t < 2269 then (if t = 0 then 0 else 1) else s336 t - s336 (t / 2269)
def s338 (t : Nat) := if t < 2273 then (if t = 0 then 0 else 1) else s337 t - s337 (t / 2273)
def s339 (t : Nat) := if t < 2281 then (if t = 0 then 0 else 1) else s338 t - s338 (t / 2281)
def s340 (t : Nat) := if t < 2287 then (if t = 0 then 0 else 1) else s339 t - s339 (t / 2287)
def s341 (t : Nat) := if t < 2293 then (if t = 0 then 0 else 1) else s340 t - s340 (t / 2293)
def s342 (t : Nat) := if t < 2297 then (if t = 0 then 0 else 1) else s341 t - s341 (t / 2297)
def s343 (t : Nat) := if t < 2309 then (if t = 0 then 0 else 1) else s342 t - s342 (t / 2309)
def s344 (t : Nat) := if t < 2311 then (if t = 0 then 0 else 1) else s343 t - s343 (t / 2311)
def s345 (t : Nat) := if t < 2333 then (if t = 0 then 0 else 1) else s344 t - s344 (t / 2333)
def s346 (t : Nat) := if t < 2339 then (if t = 0 then 0 else 1) else s345 t - s345 (t / 2339)
def s347 (t : Nat) := if t < 2341 then (if t = 0 then 0 else 1) else s346 t - s346 (t / 2341)
def s348 (t : Nat) := if t < 2347 then (if t = 0 then 0 else 1) else s347 t - s347 (t / 2347)
def s349 (t : Nat) := if t < 2351 then (if t = 0 then 0 else 1) else s348 t - s348 (t / 2351)
def s350 (t : Nat) := if t < 2357 then (if t = 0 then 0 else 1) else s349 t - s349 (t / 2357)
def s351 (t : Nat) := if t < 2371 then (if t = 0 then 0 else 1) else s350 t - s350 (t / 2371)
def s352 (t : Nat) := if t < 2377 then (if t = 0 then 0 else 1) else s351 t - s351 (t / 2377)
def s353 (t : Nat) := if t < 2381 then (if t = 0 then 0 else 1) else s352 t - s352 (t / 2381)
def s354 (t : Nat) := if t < 2383 then (if t = 0 then 0 else 1) else s353 t - s353 (t / 2383)
def s355 (t : Nat) := if t < 2389 then (if t = 0 then 0 else 1) else s354 t - s354 (t / 2389)
def s356 (t : Nat) := if t < 2393 then (if t = 0 then 0 else 1) else s355 t - s355 (t / 2393)
def s357 (t : Nat) := if t < 2399 then (if t = 0 then 0 else 1) else s356 t - s356 (t / 2399)
def s358 (t : Nat) := if t < 2411 then (if t = 0 then 0 else 1) else s357 t - s357 (t / 2411)
def s359 (t : Nat) := if t < 2417 then (if t = 0 then 0 else 1) else s358 t - s358 (t / 2417)
def s360 (t : Nat) := if t < 2423 then (if t = 0 then 0 else 1) else s359 t - s359 (t / 2423)
def s361 (t : Nat) := if t < 2437 then (if t = 0 then 0 else 1) else s360 t - s360 (t / 2437)
def s362 (t : Nat) := if t < 2441 then (if t = 0 then 0 else 1) else s361 t - s361 (t / 2441)
def s363 (t : Nat) := if t < 2447 then (if t = 0 then 0 else 1) else s362 t - s362 (t / 2447)
def s364 (t : Nat) := if t < 2459 then (if t = 0 then 0 else 1) else s363 t - s363 (t / 2459)
def s365 (t : Nat) := if t < 2467 then (if t = 0 then 0 else 1) else s364 t - s364 (t / 2467)
def s366 (t : Nat) := if t < 2473 then (if t = 0 then 0 else 1) else s365 t - s365 (t / 2473)
def s367 (t : Nat) := if t < 2477 then (if t = 0 then 0 else 1) else s366 t - s366 (t / 2477)
def s368 (t : Nat) := if t < 2503 then (if t = 0 then 0 else 1) else s367 t - s367 (t / 2503)
def s369 (t : Nat) := if t < 2521 then (if t = 0 then 0 else 1) else s368 t - s368 (t / 2521)
def s370 (t : Nat) := if t < 2531 then (if t = 0 then 0 else 1) else s369 t - s369 (t / 2531)
def s371 (t : Nat) := if t < 2539 then (if t = 0 then 0 else 1) else s370 t - s370 (t / 2539)
def s372 (t : Nat) := if t < 2543 then (if t = 0 then 0 else 1) else s371 t - s371 (t / 2543)
def s373 (t : Nat) := if t < 2549 then (if t = 0 then 0 else 1) else s372 t - s372 (t / 2549)
def s374 (t : Nat) := if t < 2551 then (if t = 0 then 0 else 1) else s373 t - s373 (t / 2551)
def s375 (t : Nat) := if t < 2557 then (if t = 0 then 0 else 1) else s374 t - s374 (t / 2557)
def s376 (t : Nat) := if t < 2579 then (if t = 0 then 0 else 1) else s375 t - s375 (t / 2579)
def s377 (t : Nat) := if t < 2591 then (if t = 0 then 0 else 1) else s376 t - s376 (t / 2591)
def s378 (t : Nat) := if t < 2593 then (if t = 0 then 0 else 1) else s377 t - s377 (t / 2593)
def s379 (t : Nat) := if t < 2609 then (if t = 0 then 0 else 1) else s378 t - s378 (t / 2609)
def s380 (t : Nat) := if t < 2617 then (if t = 0 then 0 else 1) else s379 t - s379 (t / 2617)
def s381 (t : Nat) := if t < 2621 then (if t = 0 then 0 else 1) else s380 t - s380 (t / 2621)
def s382 (t : Nat) := if t < 2633 then (if t = 0 then 0 else 1) else s381 t - s381 (t / 2633)
def s383 (t : Nat) := if t < 2647 then (if t = 0 then 0 else 1) else s382 t - s382 (t / 2647)
def s384 (t : Nat) := if t < 2657 then (if t = 0 then 0 else 1) else s383 t - s383 (t / 2657)
def s385 (t : Nat) := if t < 2659 then (if t = 0 then 0 else 1) else s384 t - s384 (t / 2659)
def s386 (t : Nat) := if t < 2663 then (if t = 0 then 0 else 1) else s385 t - s385 (t / 2663)
def s387 (t : Nat) := if t < 2671 then (if t = 0 then 0 else 1) else s386 t - s386 (t / 2671)
def s388 (t : Nat) := if t < 2677 then (if t = 0 then 0 else 1) else s387 t - s387 (t / 2677)
def s389 (t : Nat) := if t < 2683 then (if t = 0 then 0 else 1) else s388 t - s388 (t / 2683)
def s390 (t : Nat) := if t < 2687 then (if t = 0 then 0 else 1) else s389 t - s389 (t / 2687)
def s391 (t : Nat) := if t < 2689 then (if t = 0 then 0 else 1) else s390 t - s390 (t / 2689)
def s392 (t : Nat) := if t < 2693 then (if t = 0 then 0 else 1) else s391 t - s391 (t / 2693)
def s393 (t : Nat) := if t < 2699 then (if t = 0 then 0 else 1) else s392 t - s392 (t / 2699)
def s394 (t : Nat) := if t < 2707 then (if t = 0 then 0 else 1) else s393 t - s393 (t / 2707)
def s395 (t : Nat) := if t < 2711 then (if t = 0 then 0 else 1) else s394 t - s394 (t / 2711)
def s396 (t : Nat) := if t < 2713 then (if t = 0 then 0 else 1) else s395 t - s395 (t / 2713)
def s397 (t : Nat) := if t < 2719 then (if t = 0 then 0 else 1) else s396 t - s396 (t / 2719)
def s398 (t : Nat) := if t < 2729 then (if t = 0 then 0 else 1) else s397 t - s397 (t / 2729)
def s399 (t : Nat) := if t < 2731 then (if t = 0 then 0 else 1) else s398 t - s398 (t / 2731)
def s400 (t : Nat) := if t < 2741 then (if t = 0 then 0 else 1) else s399 t - s399 (t / 2741)
def s401 (t : Nat) := if t < 2749 then (if t = 0 then 0 else 1) else s400 t - s400 (t / 2749)
def s402 (t : Nat) := if t < 2753 then (if t = 0 then 0 else 1) else s401 t - s401 (t / 2753)
def s403 (t : Nat) := if t < 2767 then (if t = 0 then 0 else 1) else s402 t - s402 (t / 2767)
def s404 (t : Nat) := if t < 2777 then (if t = 0 then 0 else 1) else s403 t - s403 (t / 2777)
def s405 (t : Nat) := if t < 2789 then (if t = 0 then 0 else 1) else s404 t - s404 (t / 2789)
def s406 (t : Nat) := if t < 2791 then (if t = 0 then 0 else 1) else s405 t - s405 (t / 2791)
def s407 (t : Nat) := if t < 2797 then (if t = 0 then 0 else 1) else s406 t - s406 (t / 2797)
def s408 (t : Nat) := if t < 2801 then (if t = 0 then 0 else 1) else s407 t - s407 (t / 2801)
def s409 (t : Nat) := if t < 2803 then (if t = 0 then 0 else 1) else s408 t - s408 (t / 2803)
def s410 (t : Nat) := if t < 2819 then (if t = 0 then 0 else 1) else s409 t - s409 (t / 2819)
def s411 (t : Nat) := if t < 2833 then (if t = 0 then 0 else 1) else s410 t - s410 (t / 2833)
def s412 (t : Nat) := if t < 2837 then (if t = 0 then 0 else 1) else s411 t - s411 (t / 2837)
def s413 (t : Nat) := if t < 2843 then (if t = 0 then 0 else 1) else s412 t - s412 (t / 2843)
def s414 (t : Nat) := if t < 2851 then (if t = 0 then 0 else 1) else s413 t - s413 (t / 2851)
def s415 (t : Nat) := if t < 2857 then (if t = 0 then 0 else 1) else s414 t - s414 (t / 2857)
def s416 (t : Nat) := if t < 2861 then (if t = 0 then 0 else 1) else s415 t - s415 (t / 2861)
def s417 (t : Nat) := if t < 2879 then (if t = 0 then 0 else 1) else s416 t - s416 (t / 2879)
def s418 (t : Nat) := if t < 2887 then (if t = 0 then 0 else 1) else s417 t - s417 (t / 2887)
def s419 (t : Nat) := if t < 2897 then (if t = 0 then 0 else 1) else s418 t - s418 (t / 2897)
def s420 (t : Nat) := if t < 2903 then (if t = 0 then 0 else 1) else s419 t - s419 (t / 2903)
def s421 (t : Nat) := if t < 2909 then (if t = 0 then 0 else 1) else s420 t - s420 (t / 2909)
def s422 (t : Nat) := if t < 2917 then (if t = 0 then 0 else 1) else s421 t - s421 (t / 2917)
def s423 (t : Nat) := if t < 2927 then (if t = 0 then 0 else 1) else s422 t - s422 (t / 2927)
def s424 (t : Nat) := if t < 2939 then (if t = 0 then 0 else 1) else s423 t - s423 (t / 2939)
def s425 (t : Nat) := if t < 2953 then (if t = 0 then 0 else 1) else s424 t - s424 (t / 2953)
def s426 (t : Nat) := if t < 2957 then (if t = 0 then 0 else 1) else s425 t - s425 (t / 2957)
def s427 (t : Nat) := if t < 2963 then (if t = 0 then 0 else 1) else s426 t - s426 (t / 2963)
def s428 (t : Nat) := if t < 2969 then (if t = 0 then 0 else 1) else s427 t - s427 (t / 2969)
def s429 (t : Nat) := if t < 2971 then (if t = 0 then 0 else 1) else s428 t - s428 (t / 2971)
def s430 (t : Nat) := if t < 2999 then (if t = 0 then 0 else 1) else s429 t - s429 (t / 2999)
def s431 (t : Nat) := if t < 3001 then (if t = 0 then 0 else 1) else s430 t - s430 (t / 3001)
def s432 (t : Nat) := if t < 3011 then (if t = 0 then 0 else 1) else s431 t - s431 (t / 3011)
def s433 (t : Nat) := if t < 3019 then (if t = 0 then 0 else 1) else s432 t - s432 (t / 3019)
def s434 (t : Nat) := if t < 3023 then (if t = 0 then 0 else 1) else s433 t - s433 (t / 3023)
def s435 (t : Nat) := if t < 3037 then (if t = 0 then 0 else 1) else s434 t - s434 (t / 3037)
def s436 (t : Nat) := if t < 3041 then (if t = 0 then 0 else 1) else s435 t - s435 (t / 3041)
def s437 (t : Nat) := if t < 3049 then (if t = 0 then 0 else 1) else s436 t - s436 (t / 3049)
def s438 (t : Nat) := if t < 3061 then (if t = 0 then 0 else 1) else s437 t - s437 (t / 3061)
def s439 (t : Nat) := if t < 3067 then (if t = 0 then 0 else 1) else s438 t - s438 (t / 3067)
def s440 (t : Nat) := if t < 3079 then (if t = 0 then 0 else 1) else s439 t - s439 (t / 3079)
def s441 (t : Nat) := if t < 3083 then (if t = 0 then 0 else 1) else s440 t - s440 (t / 3083)
def s442 (t : Nat) := if t < 3089 then (if t = 0 then 0 else 1) else s441 t - s441 (t / 3089)
def s443 (t : Nat) := if t < 3109 then (if t = 0 then 0 else 1) else s442 t - s442 (t / 3109)
def s444 (t : Nat) := if t < 3119 then (if t = 0 then 0 else 1) else s443 t - s443 (t / 3119)
def s445 (t : Nat) := if t < 3121 then (if t = 0 then 0 else 1) else s444 t - s444 (t / 3121)
def s446 (t : Nat) := if t < 3137 then (if t = 0 then 0 else 1) else s445 t - s445 (t / 3137)
def s447 (t : Nat) := if t < 3163 then (if t = 0 then 0 else 1) else s446 t - s446 (t / 3163)
def s448 (t : Nat) := if t < 3167 then (if t = 0 then 0 else 1) else s447 t - s447 (t / 3167)
def s449 (t : Nat) := if t < 3169 then (if t = 0 then 0 else 1) else s448 t - s448 (t / 3169)
def s450 (t : Nat) := if t < 3181 then (if t = 0 then 0 else 1) else s449 t - s449 (t / 3181)
def s451 (t : Nat) := if t < 3187 then (if t = 0 then 0 else 1) else s450 t - s450 (t / 3187)
def s452 (t : Nat) := if t < 3191 then (if t = 0 then 0 else 1) else s451 t - s451 (t / 3191)
def s453 (t : Nat) := if t < 3203 then (if t = 0 then 0 else 1) else s452 t - s452 (t / 3203)
def s454 (t : Nat) := if t < 3209 then (if t = 0 then 0 else 1) else s453 t - s453 (t / 3209)
def s455 (t : Nat) := if t < 3217 then (if t = 0 then 0 else 1) else s454 t - s454 (t / 3217)
def s456 (t : Nat) := if t < 3221 then (if t = 0 then 0 else 1) else s455 t - s455 (t / 3221)
def s457 (t : Nat) := if t < 3229 then (if t = 0 then 0 else 1) else s456 t - s456 (t / 3229)
def s458 (t : Nat) := if t < 3251 then (if t = 0 then 0 else 1) else s457 t - s457 (t / 3251)
def s459 (t : Nat) := if t < 3253 then (if t = 0 then 0 else 1) else s458 t - s458 (t / 3253)
def s460 (t : Nat) := if t < 3257 then (if t = 0 then 0 else 1) else s459 t - s459 (t / 3257)
def s461 (t : Nat) := if t < 3259 then (if t = 0 then 0 else 1) else s460 t - s460 (t / 3259)
def s462 (t : Nat) := if t < 3271 then (if t = 0 then 0 else 1) else s461 t - s461 (t / 3271)
def s463 (t : Nat) := if t < 3299 then (if t = 0 then 0 else 1) else s462 t - s462 (t / 3299)
def s464 (t : Nat) := if t < 3301 then (if t = 0 then 0 else 1) else s463 t - s463 (t / 3301)
def s465 (t : Nat) := if t < 3307 then (if t = 0 then 0 else 1) else s464 t - s464 (t / 3307)
def s466 (t : Nat) := if t < 3313 then (if t = 0 then 0 else 1) else s465 t - s465 (t / 3313)
def s467 (t : Nat) := if t < 3319 then (if t = 0 then 0 else 1) else s466 t - s466 (t / 3319)
def s468 (t : Nat) := if t < 3323 then (if t = 0 then 0 else 1) else s467 t - s467 (t / 3323)
def s469 (t : Nat) := if t < 3329 then (if t = 0 then 0 else 1) else s468 t - s468 (t / 3329)
def s470 (t : Nat) := if t < 3331 then (if t = 0 then 0 else 1) else s469 t - s469 (t / 3331)
def s471 (t : Nat) := if t < 3343 then (if t = 0 then 0 else 1) else s470 t - s470 (t / 3343)
def s472 (t : Nat) := if t < 3347 then (if t = 0 then 0 else 1) else s471 t - s471 (t / 3347)
def s473 (t : Nat) := if t < 3359 then (if t = 0 then 0 else 1) else s472 t - s472 (t / 3359)
def s474 (t : Nat) := if t < 3361 then (if t = 0 then 0 else 1) else s473 t - s473 (t / 3361)
def s475 (t : Nat) := if t < 3371 then (if t = 0 then 0 else 1) else s474 t - s474 (t / 3371)
def s476 (t : Nat) := if t < 3373 then (if t = 0 then 0 else 1) else s475 t - s475 (t / 3373)
def s477 (t : Nat) := if t < 3389 then (if t = 0 then 0 else 1) else s476 t - s476 (t / 3389)
def s478 (t : Nat) := if t < 3391 then (if t = 0 then 0 else 1) else s477 t - s477 (t / 3391)
def s479 (t : Nat) := if t < 3407 then (if t = 0 then 0 else 1) else s478 t - s478 (t / 3407)
def s480 (t : Nat) := if t < 3413 then (if t = 0 then 0 else 1) else s479 t - s479 (t / 3413)
def s481 (t : Nat) := if t < 3433 then (if t = 0 then 0 else 1) else s480 t - s480 (t / 3433)
def s482 (t : Nat) := if t < 3449 then (if t = 0 then 0 else 1) else s481 t - s481 (t / 3449)
def s483 (t : Nat) := if t < 3457 then (if t = 0 then 0 else 1) else s482 t - s482 (t / 3457)
def s484 (t : Nat) := if t < 3461 then (if t = 0 then 0 else 1) else s483 t - s483 (t / 3461)
def s485 (t : Nat) := if t < 3463 then (if t = 0 then 0 else 1) else s484 t - s484 (t / 3463)
def s486 (t : Nat) := if t < 3467 then (if t = 0 then 0 else 1) else s485 t - s485 (t / 3467)
def s487 (t : Nat) := if t < 3469 then (if t = 0 then 0 else 1) else s486 t - s486 (t / 3469)
def s488 (t : Nat) := if t < 3491 then (if t = 0 then 0 else 1) else s487 t - s487 (t / 3491)
def s489 (t : Nat) := if t < 3499 then (if t = 0 then 0 else 1) else s488 t - s488 (t / 3499)
def s490 (t : Nat) := if t < 3511 then (if t = 0 then 0 else 1) else s489 t - s489 (t / 3511)
def s491 (t : Nat) := if t < 3517 then (if t = 0 then 0 else 1) else s490 t - s490 (t / 3517)
def s492 (t : Nat) := if t < 3527 then (if t = 0 then 0 else 1) else s491 t - s491 (t / 3527)
def s493 (t : Nat) := if t < 3529 then (if t = 0 then 0 else 1) else s492 t - s492 (t / 3529)
def s494 (t : Nat) := if t < 3533 then (if t = 0 then 0 else 1) else s493 t - s493 (t / 3533)
def s495 (t : Nat) := if t < 3539 then (if t = 0 then 0 else 1) else s494 t - s494 (t / 3539)
def s496 (t : Nat) := if t < 3541 then (if t = 0 then 0 else 1) else s495 t - s495 (t / 3541)
def s497 (t : Nat) := if t < 3547 then (if t = 0 then 0 else 1) else s496 t - s496 (t / 3547)
def s498 (t : Nat) := if t < 3557 then (if t = 0 then 0 else 1) else s497 t - s497 (t / 3557)
def s499 (t : Nat) := if t < 3559 then (if t = 0 then 0 else 1) else s498 t - s498 (t / 3559)
def s500 (t : Nat) := if t < 3571 then (if t = 0 then 0 else 1) else s499 t - s499 (t / 3571)
def s501 (t : Nat) := if t < 3581 then (if t = 0 then 0 else 1) else s500 t - s500 (t / 3581)
def s502 (t : Nat) := if t < 3583 then (if t = 0 then 0 else 1) else s501 t - s501 (t / 3583)
def s503 (t : Nat) := if t < 3593 then (if t = 0 then 0 else 1) else s502 t - s502 (t / 3593)
def s504 (t : Nat) := if t < 3607 then (if t = 0 then 0 else 1) else s503 t - s503 (t / 3607)
def s505 (t : Nat) := if t < 3613 then (if t = 0 then 0 else 1) else s504 t - s504 (t / 3613)
def s506 (t : Nat) := if t < 3617 then (if t = 0 then 0 else 1) else s505 t - s505 (t / 3617)
def s507 (t : Nat) := if t < 3623 then (if t = 0 then 0 else 1) else s506 t - s506 (t / 3623)
def s508 (t : Nat) := if t < 3631 then (if t = 0 then 0 else 1) else s507 t - s507 (t / 3631)
def s509 (t : Nat) := if t < 3637 then (if t = 0 then 0 else 1) else s508 t - s508 (t / 3637)
def s510 (t : Nat) := if t < 3643 then (if t = 0 then 0 else 1) else s509 t - s509 (t / 3643)
def s511 (t : Nat) := if t < 3659 then (if t = 0 then 0 else 1) else s510 t - s510 (t / 3659)
def s512 (t : Nat) := if t < 3671 then (if t = 0 then 0 else 1) else s511 t - s511 (t / 3671)
def s513 (t : Nat) := if t < 3673 then (if t = 0 then 0 else 1) else s512 t - s512 (t / 3673)
def s514 (t : Nat) := if t < 3677 then (if t = 0 then 0 else 1) else s513 t - s513 (t / 3677)
def s515 (t : Nat) := if t < 3691 then (if t = 0 then 0 else 1) else s514 t - s514 (t / 3691)
def s516 (t : Nat) := if t < 3697 then (if t = 0 then 0 else 1) else s515 t - s515 (t / 3697)
def s517 (t : Nat) := if t < 3701 then (if t = 0 then 0 else 1) else s516 t - s516 (t / 3701)
def s518 (t : Nat) := if t < 3709 then (if t = 0 then 0 else 1) else s517 t - s517 (t / 3709)
def s519 (t : Nat) := if t < 3719 then (if t = 0 then 0 else 1) else s518 t - s518 (t / 3719)
def s520 (t : Nat) := if t < 3727 then (if t = 0 then 0 else 1) else s519 t - s519 (t / 3727)
def s521 (t : Nat) := if t < 3733 then (if t = 0 then 0 else 1) else s520 t - s520 (t / 3733)
def s522 (t : Nat) := if t < 3739 then (if t = 0 then 0 else 1) else s521 t - s521 (t / 3739)
def s523 (t : Nat) := if t < 3761 then (if t = 0 then 0 else 1) else s522 t - s522 (t / 3761)
def s524 (t : Nat) := if t < 3767 then (if t = 0 then 0 else 1) else s523 t - s523 (t / 3767)
def s525 (t : Nat) := if t < 3769 then (if t = 0 then 0 else 1) else s524 t - s524 (t / 3769)
def s526 (t : Nat) := if t < 3779 then (if t = 0 then 0 else 1) else s525 t - s525 (t / 3779)
def s527 (t : Nat) := if t < 3793 then (if t = 0 then 0 else 1) else s526 t - s526 (t / 3793)
def s528 (t : Nat) := if t < 3797 then (if t = 0 then 0 else 1) else s527 t - s527 (t / 3797)
def s529 (t : Nat) := if t < 3803 then (if t = 0 then 0 else 1) else s528 t - s528 (t / 3803)
def s530 (t : Nat) := if t < 3821 then (if t = 0 then 0 else 1) else s529 t - s529 (t / 3821)
def s531 (t : Nat) := if t < 3823 then (if t = 0 then 0 else 1) else s530 t - s530 (t / 3823)
def s532 (t : Nat) := if t < 3833 then (if t = 0 then 0 else 1) else s531 t - s531 (t / 3833)
def s533 (t : Nat) := if t < 3847 then (if t = 0 then 0 else 1) else s532 t - s532 (t / 3847)
def s534 (t : Nat) := if t < 3851 then (if t = 0 then 0 else 1) else s533 t - s533 (t / 3851)
def s535 (t : Nat) := if t < 3853 then (if t = 0 then 0 else 1) else s534 t - s534 (t / 3853)
def s536 (t : Nat) := if t < 3863 then (if t = 0 then 0 else 1) else s535 t - s535 (t / 3863)
def s537 (t : Nat) := if t < 3877 then (if t = 0 then 0 else 1) else s536 t - s536 (t / 3877)
def s538 (t : Nat) := if t < 3881 then (if t = 0 then 0 else 1) else s537 t - s537 (t / 3881)
def s539 (t : Nat) := if t < 3889 then (if t = 0 then 0 else 1) else s538 t - s538 (t / 3889)
def s540 (t : Nat) := if t < 3907 then (if t = 0 then 0 else 1) else s539 t - s539 (t / 3907)
def s541 (t : Nat) := if t < 3911 then (if t = 0 then 0 else 1) else s540 t - s540 (t / 3911)
def s542 (t : Nat) := if t < 3917 then (if t = 0 then 0 else 1) else s541 t - s541 (t / 3917)
def s543 (t : Nat) := if t < 3919 then (if t = 0 then 0 else 1) else s542 t - s542 (t / 3919)
def s544 (t : Nat) := if t < 3923 then (if t = 0 then 0 else 1) else s543 t - s543 (t / 3923)
def s545 (t : Nat) := if t < 3929 then (if t = 0 then 0 else 1) else s544 t - s544 (t / 3929)
def s546 (t : Nat) := if t < 3931 then (if t = 0 then 0 else 1) else s545 t - s545 (t / 3931)
def s547 (t : Nat) := if t < 3943 then (if t = 0 then 0 else 1) else s546 t - s546 (t / 3943)
def s548 (t : Nat) := if t < 3947 then (if t = 0 then 0 else 1) else s547 t - s547 (t / 3947)
def s549 (t : Nat) := if t < 3967 then (if t = 0 then 0 else 1) else s548 t - s548 (t / 3967)
def s550 (t : Nat) := if t < 3989 then (if t = 0 then 0 else 1) else s549 t - s549 (t / 3989)
def s551 (t : Nat) := if t < 4001 then (if t = 0 then 0 else 1) else s550 t - s550 (t / 4001)
def s552 (t : Nat) := if t < 4003 then (if t = 0 then 0 else 1) else s551 t - s551 (t / 4003)
def s553 (t : Nat) := if t < 4007 then (if t = 0 then 0 else 1) else s552 t - s552 (t / 4007)
def s554 (t : Nat) := if t < 4013 then (if t = 0 then 0 else 1) else s553 t - s553 (t / 4013)
def s555 (t : Nat) := if t < 4019 then (if t = 0 then 0 else 1) else s554 t - s554 (t / 4019)
def s556 (t : Nat) := if t < 4021 then (if t = 0 then 0 else 1) else s555 t - s555 (t / 4021)
def s557 (t : Nat) := if t < 4027 then (if t = 0 then 0 else 1) else s556 t - s556 (t / 4027)
def s558 (t : Nat) := if t < 4049 then (if t = 0 then 0 else 1) else s557 t - s557 (t / 4049)
def s559 (t : Nat) := if t < 4051 then (if t = 0 then 0 else 1) else s558 t - s558 (t / 4051)
def s560 (t : Nat) := if t < 4057 then (if t = 0 then 0 else 1) else s559 t - s559 (t / 4057)
def s561 (t : Nat) := if t < 4073 then (if t = 0 then 0 else 1) else s560 t - s560 (t / 4073)
def s562 (t : Nat) := if t < 4079 then (if t = 0 then 0 else 1) else s561 t - s561 (t / 4079)
def s563 (t : Nat) := if t < 4091 then (if t = 0 then 0 else 1) else s562 t - s562 (t / 4091)
def s564 (t : Nat) := if t < 4093 then (if t = 0 then 0 else 1) else s563 t - s563 (t / 4093)
def s565 (t : Nat) := if t < 4099 then (if t = 0 then 0 else 1) else s564 t - s564 (t / 4099)
def s566 (t : Nat) := if t < 4111 then (if t = 0 then 0 else 1) else s565 t - s565 (t / 4111)
def s567 (t : Nat) := if t < 4127 then (if t = 0 then 0 else 1) else s566 t - s566 (t / 4127)
def s568 (t : Nat) := if t < 4129 then (if t = 0 then 0 else 1) else s567 t - s567 (t / 4129)
def s569 (t : Nat) := if t < 4133 then (if t = 0 then 0 else 1) else s568 t - s568 (t / 4133)
def s570 (t : Nat) := if t < 4139 then (if t = 0 then 0 else 1) else s569 t - s569 (t / 4139)
def s571 (t : Nat) := if t < 4153 then (if t = 0 then 0 else 1) else s570 t - s570 (t / 4153)
def s572 (t : Nat) := if t < 4157 then (if t = 0 then 0 else 1) else s571 t - s571 (t / 4157)
def s573 (t : Nat) := if t < 4159 then (if t = 0 then 0 else 1) else s572 t - s572 (t / 4159)
def s574 (t : Nat) := if t < 4177 then (if t = 0 then 0 else 1) else s573 t - s573 (t / 4177)
def s575 (t : Nat) := if t < 4201 then (if t = 0 then 0 else 1) else s574 t - s574 (t / 4201)
def s576 (t : Nat) := if t < 4211 then (if t = 0 then 0 else 1) else s575 t - s575 (t / 4211)
def s577 (t : Nat) := if t < 4217 then (if t = 0 then 0 else 1) else s576 t - s576 (t / 4217)
def s578 (t : Nat) := if t < 4219 then (if t = 0 then 0 else 1) else s577 t - s577 (t / 4219)
def s579 (t : Nat) := if t < 4229 then (if t = 0 then 0 else 1) else s578 t - s578 (t / 4229)
def s580 (t : Nat) := if t < 4231 then (if t = 0 then 0 else 1) else s579 t - s579 (t / 4231)
def s581 (t : Nat) := if t < 4241 then (if t = 0 then 0 else 1) else s580 t - s580 (t / 4241)
def s582 (t : Nat) := if t < 4243 then (if t = 0 then 0 else 1) else s581 t - s581 (t / 4243)
def s583 (t : Nat) := if t < 4253 then (if t = 0 then 0 else 1) else s582 t - s582 (t / 4253)
def s584 (t : Nat) := if t < 4259 then (if t = 0 then 0 else 1) else s583 t - s583 (t / 4259)
def s585 (t : Nat) := if t < 4261 then (if t = 0 then 0 else 1) else s584 t - s584 (t / 4261)
def s586 (t : Nat) := if t < 4271 then (if t = 0 then 0 else 1) else s585 t - s585 (t / 4271)
def s587 (t : Nat) := if t < 4273 then (if t = 0 then 0 else 1) else s586 t - s586 (t / 4273)
def s588 (t : Nat) := if t < 4283 then (if t = 0 then 0 else 1) else s587 t - s587 (t / 4283)
def s589 (t : Nat) := if t < 4289 then (if t = 0 then 0 else 1) else s588 t - s588 (t / 4289)
def s590 (t : Nat) := if t < 4297 then (if t = 0 then 0 else 1) else s589 t - s589 (t / 4297)
def s591 (t : Nat) := if t < 4327 then (if t = 0 then 0 else 1) else s590 t - s590 (t / 4327)
def s592 (t : Nat) := if t < 4337 then (if t = 0 then 0 else 1) else s591 t - s591 (t / 4337)
def s593 (t : Nat) := if t < 4339 then (if t = 0 then 0 else 1) else s592 t - s592 (t / 4339)
def s594 (t : Nat) := if t < 4349 then (if t = 0 then 0 else 1) else s593 t - s593 (t / 4349)
def s595 (t : Nat) := if t < 4357 then (if t = 0 then 0 else 1) else s594 t - s594 (t / 4357)
def s596 (t : Nat) := if t < 4363 then (if t = 0 then 0 else 1) else s595 t - s595 (t / 4363)
def s597 (t : Nat) := if t < 4373 then (if t = 0 then 0 else 1) else s596 t - s596 (t / 4373)
def s598 (t : Nat) := if t < 4391 then (if t = 0 then 0 else 1) else s597 t - s597 (t / 4391)
def s599 (t : Nat) := if t < 4397 then (if t = 0 then 0 else 1) else s598 t - s598 (t / 4397)
def s600 (t : Nat) := if t < 4409 then (if t = 0 then 0 else 1) else s599 t - s599 (t / 4409)
def s601 (t : Nat) := if t < 4421 then (if t = 0 then 0 else 1) else s600 t - s600 (t / 4421)
def s602 (t : Nat) := if t < 4423 then (if t = 0 then 0 else 1) else s601 t - s601 (t / 4423)
def s603 (t : Nat) := if t < 4441 then (if t = 0 then 0 else 1) else s602 t - s602 (t / 4441)
def s604 (t : Nat) := if t < 4447 then (if t = 0 then 0 else 1) else s603 t - s603 (t / 4447)
def s605 (t : Nat) := if t < 4451 then (if t = 0 then 0 else 1) else s604 t - s604 (t / 4451)
def s606 (t : Nat) := if t < 4457 then (if t = 0 then 0 else 1) else s605 t - s605 (t / 4457)
def s607 (t : Nat) := if t < 4463 then (if t = 0 then 0 else 1) else s606 t - s606 (t / 4463)
def s608 (t : Nat) := if t < 4481 then (if t = 0 then 0 else 1) else s607 t - s607 (t / 4481)
def s609 (t : Nat) := if t < 4483 then (if t = 0 then 0 else 1) else s608 t - s608 (t / 4483)
def s610 (t : Nat) := if t < 4493 then (if t = 0 then 0 else 1) else s609 t - s609 (t / 4493)
def s611 (t : Nat) := if t < 4507 then (if t = 0 then 0 else 1) else s610 t - s610 (t / 4507)
def s612 (t : Nat) := if t < 4513 then (if t = 0 then 0 else 1) else s611 t - s611 (t / 4513)
def s613 (t : Nat) := if t < 4517 then (if t = 0 then 0 else 1) else s612 t - s612 (t / 4517)
def s614 (t : Nat) := if t < 4519 then (if t = 0 then 0 else 1) else s613 t - s613 (t / 4519)
def s615 (t : Nat) := if t < 4523 then (if t = 0 then 0 else 1) else s614 t - s614 (t / 4523)
def s616 (t : Nat) := if t < 4547 then (if t = 0 then 0 else 1) else s615 t - s615 (t / 4547)
def s617 (t : Nat) := if t < 4549 then (if t = 0 then 0 else 1) else s616 t - s616 (t / 4549)
def s618 (t : Nat) := if t < 4561 then (if t = 0 then 0 else 1) else s617 t - s617 (t / 4561)
def s619 (t : Nat) := if t < 4567 then (if t = 0 then 0 else 1) else s618 t - s618 (t / 4567)
end A247824Checked

namespace A247824Checked
theorem stepCert (f : Nat → Nat) (p x q l r v : Nat) (h : ¬ x < p) (hq : x/p = q) (hl : f x = l) (hr : f q = r) (hv : l-r=v) : (if x<p then (if x=0 then 0 else 1) else f x-f (x/p)) = v := by rw [if_neg h,hq,hl,hr,hv]
theorem u1 (x q l r v : Nat) (h : ¬x<2) (d : x/2=q) (a : s0 x=l) (b : s0 q=r) (c : l-r=v) : s1 x=v := stepCert s0 2 x q l r v h d a b c
theorem u2 (x q l r v : Nat) (h : ¬x<3) (d : x/3=q) (a : s1 x=l) (b : s1 q=r) (c : l-r=v) : s2 x=v := stepCert s1 3 x q l r v h d a b c
theorem u3 (x q l r v : Nat) (h : ¬x<5) (d : x/5=q) (a : s2 x=l) (b : s2 q=r) (c : l-r=v) : s3 x=v := stepCert s2 5 x q l r v h d a b c
theorem u4 (x q l r v : Nat) (h : ¬x<7) (d : x/7=q) (a : s3 x=l) (b : s3 q=r) (c : l-r=v) : s4 x=v := stepCert s3 7 x q l r v h d a b c
theorem u5 (x q l r v : Nat) (h : ¬x<11) (d : x/11=q) (a : s4 x=l) (b : s4 q=r) (c : l-r=v) : s5 x=v := stepCert s4 11 x q l r v h d a b c
theorem u6 (x q l r v : Nat) (h : ¬x<13) (d : x/13=q) (a : s5 x=l) (b : s5 q=r) (c : l-r=v) : s6 x=v := stepCert s5 13 x q l r v h d a b c
theorem u7 (x q l r v : Nat) (h : ¬x<17) (d : x/17=q) (a : s6 x=l) (b : s6 q=r) (c : l-r=v) : s7 x=v := stepCert s6 17 x q l r v h d a b c
theorem u8 (x q l r v : Nat) (h : ¬x<19) (d : x/19=q) (a : s7 x=l) (b : s7 q=r) (c : l-r=v) : s8 x=v := stepCert s7 19 x q l r v h d a b c
theorem u9 (x q l r v : Nat) (h : ¬x<23) (d : x/23=q) (a : s8 x=l) (b : s8 q=r) (c : l-r=v) : s9 x=v := stepCert s8 23 x q l r v h d a b c
theorem u10 (x q l r v : Nat) (h : ¬x<29) (d : x/29=q) (a : s9 x=l) (b : s9 q=r) (c : l-r=v) : s10 x=v := stepCert s9 29 x q l r v h d a b c
theorem u11 (x q l r v : Nat) (h : ¬x<31) (d : x/31=q) (a : s10 x=l) (b : s10 q=r) (c : l-r=v) : s11 x=v := stepCert s10 31 x q l r v h d a b c
theorem u12 (x q l r v : Nat) (h : ¬x<37) (d : x/37=q) (a : s11 x=l) (b : s11 q=r) (c : l-r=v) : s12 x=v := stepCert s11 37 x q l r v h d a b c
theorem u13 (x q l r v : Nat) (h : ¬x<41) (d : x/41=q) (a : s12 x=l) (b : s12 q=r) (c : l-r=v) : s13 x=v := stepCert s12 41 x q l r v h d a b c
theorem u14 (x q l r v : Nat) (h : ¬x<43) (d : x/43=q) (a : s13 x=l) (b : s13 q=r) (c : l-r=v) : s14 x=v := stepCert s13 43 x q l r v h d a b c
theorem u15 (x q l r v : Nat) (h : ¬x<47) (d : x/47=q) (a : s14 x=l) (b : s14 q=r) (c : l-r=v) : s15 x=v := stepCert s14 47 x q l r v h d a b c
theorem u16 (x q l r v : Nat) (h : ¬x<53) (d : x/53=q) (a : s15 x=l) (b : s15 q=r) (c : l-r=v) : s16 x=v := stepCert s15 53 x q l r v h d a b c
theorem u17 (x q l r v : Nat) (h : ¬x<59) (d : x/59=q) (a : s16 x=l) (b : s16 q=r) (c : l-r=v) : s17 x=v := stepCert s16 59 x q l r v h d a b c
theorem u18 (x q l r v : Nat) (h : ¬x<61) (d : x/61=q) (a : s17 x=l) (b : s17 q=r) (c : l-r=v) : s18 x=v := stepCert s17 61 x q l r v h d a b c
theorem u19 (x q l r v : Nat) (h : ¬x<67) (d : x/67=q) (a : s18 x=l) (b : s18 q=r) (c : l-r=v) : s19 x=v := stepCert s18 67 x q l r v h d a b c
theorem u20 (x q l r v : Nat) (h : ¬x<71) (d : x/71=q) (a : s19 x=l) (b : s19 q=r) (c : l-r=v) : s20 x=v := stepCert s19 71 x q l r v h d a b c
theorem u21 (x q l r v : Nat) (h : ¬x<73) (d : x/73=q) (a : s20 x=l) (b : s20 q=r) (c : l-r=v) : s21 x=v := stepCert s20 73 x q l r v h d a b c
theorem u22 (x q l r v : Nat) (h : ¬x<79) (d : x/79=q) (a : s21 x=l) (b : s21 q=r) (c : l-r=v) : s22 x=v := stepCert s21 79 x q l r v h d a b c
theorem u23 (x q l r v : Nat) (h : ¬x<83) (d : x/83=q) (a : s22 x=l) (b : s22 q=r) (c : l-r=v) : s23 x=v := stepCert s22 83 x q l r v h d a b c
theorem u24 (x q l r v : Nat) (h : ¬x<89) (d : x/89=q) (a : s23 x=l) (b : s23 q=r) (c : l-r=v) : s24 x=v := stepCert s23 89 x q l r v h d a b c
theorem u25 (x q l r v : Nat) (h : ¬x<97) (d : x/97=q) (a : s24 x=l) (b : s24 q=r) (c : l-r=v) : s25 x=v := stepCert s24 97 x q l r v h d a b c
theorem u26 (x q l r v : Nat) (h : ¬x<101) (d : x/101=q) (a : s25 x=l) (b : s25 q=r) (c : l-r=v) : s26 x=v := stepCert s25 101 x q l r v h d a b c
theorem u27 (x q l r v : Nat) (h : ¬x<103) (d : x/103=q) (a : s26 x=l) (b : s26 q=r) (c : l-r=v) : s27 x=v := stepCert s26 103 x q l r v h d a b c
theorem u28 (x q l r v : Nat) (h : ¬x<107) (d : x/107=q) (a : s27 x=l) (b : s27 q=r) (c : l-r=v) : s28 x=v := stepCert s27 107 x q l r v h d a b c
theorem u29 (x q l r v : Nat) (h : ¬x<109) (d : x/109=q) (a : s28 x=l) (b : s28 q=r) (c : l-r=v) : s29 x=v := stepCert s28 109 x q l r v h d a b c
theorem u30 (x q l r v : Nat) (h : ¬x<113) (d : x/113=q) (a : s29 x=l) (b : s29 q=r) (c : l-r=v) : s30 x=v := stepCert s29 113 x q l r v h d a b c
theorem u31 (x q l r v : Nat) (h : ¬x<127) (d : x/127=q) (a : s30 x=l) (b : s30 q=r) (c : l-r=v) : s31 x=v := stepCert s30 127 x q l r v h d a b c
theorem u32 (x q l r v : Nat) (h : ¬x<131) (d : x/131=q) (a : s31 x=l) (b : s31 q=r) (c : l-r=v) : s32 x=v := stepCert s31 131 x q l r v h d a b c
theorem u33 (x q l r v : Nat) (h : ¬x<137) (d : x/137=q) (a : s32 x=l) (b : s32 q=r) (c : l-r=v) : s33 x=v := stepCert s32 137 x q l r v h d a b c
theorem u34 (x q l r v : Nat) (h : ¬x<139) (d : x/139=q) (a : s33 x=l) (b : s33 q=r) (c : l-r=v) : s34 x=v := stepCert s33 139 x q l r v h d a b c
theorem u35 (x q l r v : Nat) (h : ¬x<149) (d : x/149=q) (a : s34 x=l) (b : s34 q=r) (c : l-r=v) : s35 x=v := stepCert s34 149 x q l r v h d a b c
theorem u36 (x q l r v : Nat) (h : ¬x<151) (d : x/151=q) (a : s35 x=l) (b : s35 q=r) (c : l-r=v) : s36 x=v := stepCert s35 151 x q l r v h d a b c
theorem u37 (x q l r v : Nat) (h : ¬x<157) (d : x/157=q) (a : s36 x=l) (b : s36 q=r) (c : l-r=v) : s37 x=v := stepCert s36 157 x q l r v h d a b c
theorem u38 (x q l r v : Nat) (h : ¬x<163) (d : x/163=q) (a : s37 x=l) (b : s37 q=r) (c : l-r=v) : s38 x=v := stepCert s37 163 x q l r v h d a b c
theorem u39 (x q l r v : Nat) (h : ¬x<167) (d : x/167=q) (a : s38 x=l) (b : s38 q=r) (c : l-r=v) : s39 x=v := stepCert s38 167 x q l r v h d a b c
theorem u40 (x q l r v : Nat) (h : ¬x<173) (d : x/173=q) (a : s39 x=l) (b : s39 q=r) (c : l-r=v) : s40 x=v := stepCert s39 173 x q l r v h d a b c
theorem u41 (x q l r v : Nat) (h : ¬x<179) (d : x/179=q) (a : s40 x=l) (b : s40 q=r) (c : l-r=v) : s41 x=v := stepCert s40 179 x q l r v h d a b c
theorem u42 (x q l r v : Nat) (h : ¬x<181) (d : x/181=q) (a : s41 x=l) (b : s41 q=r) (c : l-r=v) : s42 x=v := stepCert s41 181 x q l r v h d a b c
theorem u43 (x q l r v : Nat) (h : ¬x<191) (d : x/191=q) (a : s42 x=l) (b : s42 q=r) (c : l-r=v) : s43 x=v := stepCert s42 191 x q l r v h d a b c
theorem u44 (x q l r v : Nat) (h : ¬x<193) (d : x/193=q) (a : s43 x=l) (b : s43 q=r) (c : l-r=v) : s44 x=v := stepCert s43 193 x q l r v h d a b c
theorem u45 (x q l r v : Nat) (h : ¬x<197) (d : x/197=q) (a : s44 x=l) (b : s44 q=r) (c : l-r=v) : s45 x=v := stepCert s44 197 x q l r v h d a b c
theorem u46 (x q l r v : Nat) (h : ¬x<199) (d : x/199=q) (a : s45 x=l) (b : s45 q=r) (c : l-r=v) : s46 x=v := stepCert s45 199 x q l r v h d a b c
theorem u47 (x q l r v : Nat) (h : ¬x<211) (d : x/211=q) (a : s46 x=l) (b : s46 q=r) (c : l-r=v) : s47 x=v := stepCert s46 211 x q l r v h d a b c
theorem u48 (x q l r v : Nat) (h : ¬x<223) (d : x/223=q) (a : s47 x=l) (b : s47 q=r) (c : l-r=v) : s48 x=v := stepCert s47 223 x q l r v h d a b c
theorem u49 (x q l r v : Nat) (h : ¬x<227) (d : x/227=q) (a : s48 x=l) (b : s48 q=r) (c : l-r=v) : s49 x=v := stepCert s48 227 x q l r v h d a b c
theorem u50 (x q l r v : Nat) (h : ¬x<229) (d : x/229=q) (a : s49 x=l) (b : s49 q=r) (c : l-r=v) : s50 x=v := stepCert s49 229 x q l r v h d a b c
theorem u51 (x q l r v : Nat) (h : ¬x<233) (d : x/233=q) (a : s50 x=l) (b : s50 q=r) (c : l-r=v) : s51 x=v := stepCert s50 233 x q l r v h d a b c
theorem u52 (x q l r v : Nat) (h : ¬x<239) (d : x/239=q) (a : s51 x=l) (b : s51 q=r) (c : l-r=v) : s52 x=v := stepCert s51 239 x q l r v h d a b c
theorem u53 (x q l r v : Nat) (h : ¬x<241) (d : x/241=q) (a : s52 x=l) (b : s52 q=r) (c : l-r=v) : s53 x=v := stepCert s52 241 x q l r v h d a b c
theorem u54 (x q l r v : Nat) (h : ¬x<251) (d : x/251=q) (a : s53 x=l) (b : s53 q=r) (c : l-r=v) : s54 x=v := stepCert s53 251 x q l r v h d a b c
theorem u55 (x q l r v : Nat) (h : ¬x<257) (d : x/257=q) (a : s54 x=l) (b : s54 q=r) (c : l-r=v) : s55 x=v := stepCert s54 257 x q l r v h d a b c
theorem u56 (x q l r v : Nat) (h : ¬x<263) (d : x/263=q) (a : s55 x=l) (b : s55 q=r) (c : l-r=v) : s56 x=v := stepCert s55 263 x q l r v h d a b c
theorem u57 (x q l r v : Nat) (h : ¬x<269) (d : x/269=q) (a : s56 x=l) (b : s56 q=r) (c : l-r=v) : s57 x=v := stepCert s56 269 x q l r v h d a b c
theorem u58 (x q l r v : Nat) (h : ¬x<271) (d : x/271=q) (a : s57 x=l) (b : s57 q=r) (c : l-r=v) : s58 x=v := stepCert s57 271 x q l r v h d a b c
theorem u59 (x q l r v : Nat) (h : ¬x<277) (d : x/277=q) (a : s58 x=l) (b : s58 q=r) (c : l-r=v) : s59 x=v := stepCert s58 277 x q l r v h d a b c
theorem u60 (x q l r v : Nat) (h : ¬x<281) (d : x/281=q) (a : s59 x=l) (b : s59 q=r) (c : l-r=v) : s60 x=v := stepCert s59 281 x q l r v h d a b c
theorem u61 (x q l r v : Nat) (h : ¬x<283) (d : x/283=q) (a : s60 x=l) (b : s60 q=r) (c : l-r=v) : s61 x=v := stepCert s60 283 x q l r v h d a b c
theorem u62 (x q l r v : Nat) (h : ¬x<293) (d : x/293=q) (a : s61 x=l) (b : s61 q=r) (c : l-r=v) : s62 x=v := stepCert s61 293 x q l r v h d a b c
theorem u63 (x q l r v : Nat) (h : ¬x<307) (d : x/307=q) (a : s62 x=l) (b : s62 q=r) (c : l-r=v) : s63 x=v := stepCert s62 307 x q l r v h d a b c
theorem u64 (x q l r v : Nat) (h : ¬x<311) (d : x/311=q) (a : s63 x=l) (b : s63 q=r) (c : l-r=v) : s64 x=v := stepCert s63 311 x q l r v h d a b c
theorem u65 (x q l r v : Nat) (h : ¬x<313) (d : x/313=q) (a : s64 x=l) (b : s64 q=r) (c : l-r=v) : s65 x=v := stepCert s64 313 x q l r v h d a b c
theorem u66 (x q l r v : Nat) (h : ¬x<317) (d : x/317=q) (a : s65 x=l) (b : s65 q=r) (c : l-r=v) : s66 x=v := stepCert s65 317 x q l r v h d a b c
theorem u67 (x q l r v : Nat) (h : ¬x<331) (d : x/331=q) (a : s66 x=l) (b : s66 q=r) (c : l-r=v) : s67 x=v := stepCert s66 331 x q l r v h d a b c
theorem u68 (x q l r v : Nat) (h : ¬x<337) (d : x/337=q) (a : s67 x=l) (b : s67 q=r) (c : l-r=v) : s68 x=v := stepCert s67 337 x q l r v h d a b c
theorem u69 (x q l r v : Nat) (h : ¬x<347) (d : x/347=q) (a : s68 x=l) (b : s68 q=r) (c : l-r=v) : s69 x=v := stepCert s68 347 x q l r v h d a b c
theorem u70 (x q l r v : Nat) (h : ¬x<349) (d : x/349=q) (a : s69 x=l) (b : s69 q=r) (c : l-r=v) : s70 x=v := stepCert s69 349 x q l r v h d a b c
theorem u71 (x q l r v : Nat) (h : ¬x<353) (d : x/353=q) (a : s70 x=l) (b : s70 q=r) (c : l-r=v) : s71 x=v := stepCert s70 353 x q l r v h d a b c
theorem u72 (x q l r v : Nat) (h : ¬x<359) (d : x/359=q) (a : s71 x=l) (b : s71 q=r) (c : l-r=v) : s72 x=v := stepCert s71 359 x q l r v h d a b c
theorem u73 (x q l r v : Nat) (h : ¬x<367) (d : x/367=q) (a : s72 x=l) (b : s72 q=r) (c : l-r=v) : s73 x=v := stepCert s72 367 x q l r v h d a b c
theorem u74 (x q l r v : Nat) (h : ¬x<373) (d : x/373=q) (a : s73 x=l) (b : s73 q=r) (c : l-r=v) : s74 x=v := stepCert s73 373 x q l r v h d a b c
theorem u75 (x q l r v : Nat) (h : ¬x<379) (d : x/379=q) (a : s74 x=l) (b : s74 q=r) (c : l-r=v) : s75 x=v := stepCert s74 379 x q l r v h d a b c
theorem u76 (x q l r v : Nat) (h : ¬x<383) (d : x/383=q) (a : s75 x=l) (b : s75 q=r) (c : l-r=v) : s76 x=v := stepCert s75 383 x q l r v h d a b c
theorem u77 (x q l r v : Nat) (h : ¬x<389) (d : x/389=q) (a : s76 x=l) (b : s76 q=r) (c : l-r=v) : s77 x=v := stepCert s76 389 x q l r v h d a b c
theorem u78 (x q l r v : Nat) (h : ¬x<397) (d : x/397=q) (a : s77 x=l) (b : s77 q=r) (c : l-r=v) : s78 x=v := stepCert s77 397 x q l r v h d a b c
theorem u79 (x q l r v : Nat) (h : ¬x<401) (d : x/401=q) (a : s78 x=l) (b : s78 q=r) (c : l-r=v) : s79 x=v := stepCert s78 401 x q l r v h d a b c
theorem u80 (x q l r v : Nat) (h : ¬x<409) (d : x/409=q) (a : s79 x=l) (b : s79 q=r) (c : l-r=v) : s80 x=v := stepCert s79 409 x q l r v h d a b c
theorem u81 (x q l r v : Nat) (h : ¬x<419) (d : x/419=q) (a : s80 x=l) (b : s80 q=r) (c : l-r=v) : s81 x=v := stepCert s80 419 x q l r v h d a b c
theorem u82 (x q l r v : Nat) (h : ¬x<421) (d : x/421=q) (a : s81 x=l) (b : s81 q=r) (c : l-r=v) : s82 x=v := stepCert s81 421 x q l r v h d a b c
theorem u83 (x q l r v : Nat) (h : ¬x<431) (d : x/431=q) (a : s82 x=l) (b : s82 q=r) (c : l-r=v) : s83 x=v := stepCert s82 431 x q l r v h d a b c
theorem u84 (x q l r v : Nat) (h : ¬x<433) (d : x/433=q) (a : s83 x=l) (b : s83 q=r) (c : l-r=v) : s84 x=v := stepCert s83 433 x q l r v h d a b c
theorem u85 (x q l r v : Nat) (h : ¬x<439) (d : x/439=q) (a : s84 x=l) (b : s84 q=r) (c : l-r=v) : s85 x=v := stepCert s84 439 x q l r v h d a b c
theorem u86 (x q l r v : Nat) (h : ¬x<443) (d : x/443=q) (a : s85 x=l) (b : s85 q=r) (c : l-r=v) : s86 x=v := stepCert s85 443 x q l r v h d a b c
theorem u87 (x q l r v : Nat) (h : ¬x<449) (d : x/449=q) (a : s86 x=l) (b : s86 q=r) (c : l-r=v) : s87 x=v := stepCert s86 449 x q l r v h d a b c
theorem u88 (x q l r v : Nat) (h : ¬x<457) (d : x/457=q) (a : s87 x=l) (b : s87 q=r) (c : l-r=v) : s88 x=v := stepCert s87 457 x q l r v h d a b c
theorem u89 (x q l r v : Nat) (h : ¬x<461) (d : x/461=q) (a : s88 x=l) (b : s88 q=r) (c : l-r=v) : s89 x=v := stepCert s88 461 x q l r v h d a b c
theorem u90 (x q l r v : Nat) (h : ¬x<463) (d : x/463=q) (a : s89 x=l) (b : s89 q=r) (c : l-r=v) : s90 x=v := stepCert s89 463 x q l r v h d a b c
theorem u91 (x q l r v : Nat) (h : ¬x<467) (d : x/467=q) (a : s90 x=l) (b : s90 q=r) (c : l-r=v) : s91 x=v := stepCert s90 467 x q l r v h d a b c
theorem u92 (x q l r v : Nat) (h : ¬x<479) (d : x/479=q) (a : s91 x=l) (b : s91 q=r) (c : l-r=v) : s92 x=v := stepCert s91 479 x q l r v h d a b c
theorem u93 (x q l r v : Nat) (h : ¬x<487) (d : x/487=q) (a : s92 x=l) (b : s92 q=r) (c : l-r=v) : s93 x=v := stepCert s92 487 x q l r v h d a b c
theorem u94 (x q l r v : Nat) (h : ¬x<491) (d : x/491=q) (a : s93 x=l) (b : s93 q=r) (c : l-r=v) : s94 x=v := stepCert s93 491 x q l r v h d a b c
theorem u95 (x q l r v : Nat) (h : ¬x<499) (d : x/499=q) (a : s94 x=l) (b : s94 q=r) (c : l-r=v) : s95 x=v := stepCert s94 499 x q l r v h d a b c
theorem u96 (x q l r v : Nat) (h : ¬x<503) (d : x/503=q) (a : s95 x=l) (b : s95 q=r) (c : l-r=v) : s96 x=v := stepCert s95 503 x q l r v h d a b c
theorem u97 (x q l r v : Nat) (h : ¬x<509) (d : x/509=q) (a : s96 x=l) (b : s96 q=r) (c : l-r=v) : s97 x=v := stepCert s96 509 x q l r v h d a b c
theorem u98 (x q l r v : Nat) (h : ¬x<521) (d : x/521=q) (a : s97 x=l) (b : s97 q=r) (c : l-r=v) : s98 x=v := stepCert s97 521 x q l r v h d a b c
theorem u99 (x q l r v : Nat) (h : ¬x<523) (d : x/523=q) (a : s98 x=l) (b : s98 q=r) (c : l-r=v) : s99 x=v := stepCert s98 523 x q l r v h d a b c
theorem u100 (x q l r v : Nat) (h : ¬x<541) (d : x/541=q) (a : s99 x=l) (b : s99 q=r) (c : l-r=v) : s100 x=v := stepCert s99 541 x q l r v h d a b c
theorem u101 (x q l r v : Nat) (h : ¬x<547) (d : x/547=q) (a : s100 x=l) (b : s100 q=r) (c : l-r=v) : s101 x=v := stepCert s100 547 x q l r v h d a b c
theorem u102 (x q l r v : Nat) (h : ¬x<557) (d : x/557=q) (a : s101 x=l) (b : s101 q=r) (c : l-r=v) : s102 x=v := stepCert s101 557 x q l r v h d a b c
theorem u103 (x q l r v : Nat) (h : ¬x<563) (d : x/563=q) (a : s102 x=l) (b : s102 q=r) (c : l-r=v) : s103 x=v := stepCert s102 563 x q l r v h d a b c
theorem u104 (x q l r v : Nat) (h : ¬x<569) (d : x/569=q) (a : s103 x=l) (b : s103 q=r) (c : l-r=v) : s104 x=v := stepCert s103 569 x q l r v h d a b c
theorem u105 (x q l r v : Nat) (h : ¬x<571) (d : x/571=q) (a : s104 x=l) (b : s104 q=r) (c : l-r=v) : s105 x=v := stepCert s104 571 x q l r v h d a b c
theorem u106 (x q l r v : Nat) (h : ¬x<577) (d : x/577=q) (a : s105 x=l) (b : s105 q=r) (c : l-r=v) : s106 x=v := stepCert s105 577 x q l r v h d a b c
theorem u107 (x q l r v : Nat) (h : ¬x<587) (d : x/587=q) (a : s106 x=l) (b : s106 q=r) (c : l-r=v) : s107 x=v := stepCert s106 587 x q l r v h d a b c
theorem u108 (x q l r v : Nat) (h : ¬x<593) (d : x/593=q) (a : s107 x=l) (b : s107 q=r) (c : l-r=v) : s108 x=v := stepCert s107 593 x q l r v h d a b c
theorem u109 (x q l r v : Nat) (h : ¬x<599) (d : x/599=q) (a : s108 x=l) (b : s108 q=r) (c : l-r=v) : s109 x=v := stepCert s108 599 x q l r v h d a b c
theorem u110 (x q l r v : Nat) (h : ¬x<601) (d : x/601=q) (a : s109 x=l) (b : s109 q=r) (c : l-r=v) : s110 x=v := stepCert s109 601 x q l r v h d a b c
theorem u111 (x q l r v : Nat) (h : ¬x<607) (d : x/607=q) (a : s110 x=l) (b : s110 q=r) (c : l-r=v) : s111 x=v := stepCert s110 607 x q l r v h d a b c
theorem u112 (x q l r v : Nat) (h : ¬x<613) (d : x/613=q) (a : s111 x=l) (b : s111 q=r) (c : l-r=v) : s112 x=v := stepCert s111 613 x q l r v h d a b c
theorem u113 (x q l r v : Nat) (h : ¬x<617) (d : x/617=q) (a : s112 x=l) (b : s112 q=r) (c : l-r=v) : s113 x=v := stepCert s112 617 x q l r v h d a b c
theorem u114 (x q l r v : Nat) (h : ¬x<619) (d : x/619=q) (a : s113 x=l) (b : s113 q=r) (c : l-r=v) : s114 x=v := stepCert s113 619 x q l r v h d a b c
theorem u115 (x q l r v : Nat) (h : ¬x<631) (d : x/631=q) (a : s114 x=l) (b : s114 q=r) (c : l-r=v) : s115 x=v := stepCert s114 631 x q l r v h d a b c
theorem u116 (x q l r v : Nat) (h : ¬x<641) (d : x/641=q) (a : s115 x=l) (b : s115 q=r) (c : l-r=v) : s116 x=v := stepCert s115 641 x q l r v h d a b c
theorem u117 (x q l r v : Nat) (h : ¬x<643) (d : x/643=q) (a : s116 x=l) (b : s116 q=r) (c : l-r=v) : s117 x=v := stepCert s116 643 x q l r v h d a b c
theorem u118 (x q l r v : Nat) (h : ¬x<647) (d : x/647=q) (a : s117 x=l) (b : s117 q=r) (c : l-r=v) : s118 x=v := stepCert s117 647 x q l r v h d a b c
theorem u119 (x q l r v : Nat) (h : ¬x<653) (d : x/653=q) (a : s118 x=l) (b : s118 q=r) (c : l-r=v) : s119 x=v := stepCert s118 653 x q l r v h d a b c
theorem u120 (x q l r v : Nat) (h : ¬x<659) (d : x/659=q) (a : s119 x=l) (b : s119 q=r) (c : l-r=v) : s120 x=v := stepCert s119 659 x q l r v h d a b c
theorem u121 (x q l r v : Nat) (h : ¬x<661) (d : x/661=q) (a : s120 x=l) (b : s120 q=r) (c : l-r=v) : s121 x=v := stepCert s120 661 x q l r v h d a b c
theorem u122 (x q l r v : Nat) (h : ¬x<673) (d : x/673=q) (a : s121 x=l) (b : s121 q=r) (c : l-r=v) : s122 x=v := stepCert s121 673 x q l r v h d a b c
theorem u123 (x q l r v : Nat) (h : ¬x<677) (d : x/677=q) (a : s122 x=l) (b : s122 q=r) (c : l-r=v) : s123 x=v := stepCert s122 677 x q l r v h d a b c
theorem u124 (x q l r v : Nat) (h : ¬x<683) (d : x/683=q) (a : s123 x=l) (b : s123 q=r) (c : l-r=v) : s124 x=v := stepCert s123 683 x q l r v h d a b c
theorem u125 (x q l r v : Nat) (h : ¬x<691) (d : x/691=q) (a : s124 x=l) (b : s124 q=r) (c : l-r=v) : s125 x=v := stepCert s124 691 x q l r v h d a b c
theorem u126 (x q l r v : Nat) (h : ¬x<701) (d : x/701=q) (a : s125 x=l) (b : s125 q=r) (c : l-r=v) : s126 x=v := stepCert s125 701 x q l r v h d a b c
theorem u127 (x q l r v : Nat) (h : ¬x<709) (d : x/709=q) (a : s126 x=l) (b : s126 q=r) (c : l-r=v) : s127 x=v := stepCert s126 709 x q l r v h d a b c
theorem u128 (x q l r v : Nat) (h : ¬x<719) (d : x/719=q) (a : s127 x=l) (b : s127 q=r) (c : l-r=v) : s128 x=v := stepCert s127 719 x q l r v h d a b c
theorem u129 (x q l r v : Nat) (h : ¬x<727) (d : x/727=q) (a : s128 x=l) (b : s128 q=r) (c : l-r=v) : s129 x=v := stepCert s128 727 x q l r v h d a b c
theorem u130 (x q l r v : Nat) (h : ¬x<733) (d : x/733=q) (a : s129 x=l) (b : s129 q=r) (c : l-r=v) : s130 x=v := stepCert s129 733 x q l r v h d a b c
theorem u131 (x q l r v : Nat) (h : ¬x<739) (d : x/739=q) (a : s130 x=l) (b : s130 q=r) (c : l-r=v) : s131 x=v := stepCert s130 739 x q l r v h d a b c
theorem u132 (x q l r v : Nat) (h : ¬x<743) (d : x/743=q) (a : s131 x=l) (b : s131 q=r) (c : l-r=v) : s132 x=v := stepCert s131 743 x q l r v h d a b c
theorem u133 (x q l r v : Nat) (h : ¬x<751) (d : x/751=q) (a : s132 x=l) (b : s132 q=r) (c : l-r=v) : s133 x=v := stepCert s132 751 x q l r v h d a b c
theorem u134 (x q l r v : Nat) (h : ¬x<757) (d : x/757=q) (a : s133 x=l) (b : s133 q=r) (c : l-r=v) : s134 x=v := stepCert s133 757 x q l r v h d a b c
theorem u135 (x q l r v : Nat) (h : ¬x<761) (d : x/761=q) (a : s134 x=l) (b : s134 q=r) (c : l-r=v) : s135 x=v := stepCert s134 761 x q l r v h d a b c
theorem u136 (x q l r v : Nat) (h : ¬x<769) (d : x/769=q) (a : s135 x=l) (b : s135 q=r) (c : l-r=v) : s136 x=v := stepCert s135 769 x q l r v h d a b c
theorem u137 (x q l r v : Nat) (h : ¬x<773) (d : x/773=q) (a : s136 x=l) (b : s136 q=r) (c : l-r=v) : s137 x=v := stepCert s136 773 x q l r v h d a b c
theorem u138 (x q l r v : Nat) (h : ¬x<787) (d : x/787=q) (a : s137 x=l) (b : s137 q=r) (c : l-r=v) : s138 x=v := stepCert s137 787 x q l r v h d a b c
theorem u139 (x q l r v : Nat) (h : ¬x<797) (d : x/797=q) (a : s138 x=l) (b : s138 q=r) (c : l-r=v) : s139 x=v := stepCert s138 797 x q l r v h d a b c
theorem u140 (x q l r v : Nat) (h : ¬x<809) (d : x/809=q) (a : s139 x=l) (b : s139 q=r) (c : l-r=v) : s140 x=v := stepCert s139 809 x q l r v h d a b c
theorem u141 (x q l r v : Nat) (h : ¬x<811) (d : x/811=q) (a : s140 x=l) (b : s140 q=r) (c : l-r=v) : s141 x=v := stepCert s140 811 x q l r v h d a b c
theorem u142 (x q l r v : Nat) (h : ¬x<821) (d : x/821=q) (a : s141 x=l) (b : s141 q=r) (c : l-r=v) : s142 x=v := stepCert s141 821 x q l r v h d a b c
theorem u143 (x q l r v : Nat) (h : ¬x<823) (d : x/823=q) (a : s142 x=l) (b : s142 q=r) (c : l-r=v) : s143 x=v := stepCert s142 823 x q l r v h d a b c
theorem u144 (x q l r v : Nat) (h : ¬x<827) (d : x/827=q) (a : s143 x=l) (b : s143 q=r) (c : l-r=v) : s144 x=v := stepCert s143 827 x q l r v h d a b c
theorem u145 (x q l r v : Nat) (h : ¬x<829) (d : x/829=q) (a : s144 x=l) (b : s144 q=r) (c : l-r=v) : s145 x=v := stepCert s144 829 x q l r v h d a b c
theorem u146 (x q l r v : Nat) (h : ¬x<839) (d : x/839=q) (a : s145 x=l) (b : s145 q=r) (c : l-r=v) : s146 x=v := stepCert s145 839 x q l r v h d a b c
theorem u147 (x q l r v : Nat) (h : ¬x<853) (d : x/853=q) (a : s146 x=l) (b : s146 q=r) (c : l-r=v) : s147 x=v := stepCert s146 853 x q l r v h d a b c
theorem u148 (x q l r v : Nat) (h : ¬x<857) (d : x/857=q) (a : s147 x=l) (b : s147 q=r) (c : l-r=v) : s148 x=v := stepCert s147 857 x q l r v h d a b c
theorem u149 (x q l r v : Nat) (h : ¬x<859) (d : x/859=q) (a : s148 x=l) (b : s148 q=r) (c : l-r=v) : s149 x=v := stepCert s148 859 x q l r v h d a b c
theorem u150 (x q l r v : Nat) (h : ¬x<863) (d : x/863=q) (a : s149 x=l) (b : s149 q=r) (c : l-r=v) : s150 x=v := stepCert s149 863 x q l r v h d a b c
theorem u151 (x q l r v : Nat) (h : ¬x<877) (d : x/877=q) (a : s150 x=l) (b : s150 q=r) (c : l-r=v) : s151 x=v := stepCert s150 877 x q l r v h d a b c
theorem u152 (x q l r v : Nat) (h : ¬x<881) (d : x/881=q) (a : s151 x=l) (b : s151 q=r) (c : l-r=v) : s152 x=v := stepCert s151 881 x q l r v h d a b c
theorem u153 (x q l r v : Nat) (h : ¬x<883) (d : x/883=q) (a : s152 x=l) (b : s152 q=r) (c : l-r=v) : s153 x=v := stepCert s152 883 x q l r v h d a b c
theorem u154 (x q l r v : Nat) (h : ¬x<887) (d : x/887=q) (a : s153 x=l) (b : s153 q=r) (c : l-r=v) : s154 x=v := stepCert s153 887 x q l r v h d a b c
theorem u155 (x q l r v : Nat) (h : ¬x<907) (d : x/907=q) (a : s154 x=l) (b : s154 q=r) (c : l-r=v) : s155 x=v := stepCert s154 907 x q l r v h d a b c
theorem u156 (x q l r v : Nat) (h : ¬x<911) (d : x/911=q) (a : s155 x=l) (b : s155 q=r) (c : l-r=v) : s156 x=v := stepCert s155 911 x q l r v h d a b c
theorem u157 (x q l r v : Nat) (h : ¬x<919) (d : x/919=q) (a : s156 x=l) (b : s156 q=r) (c : l-r=v) : s157 x=v := stepCert s156 919 x q l r v h d a b c
theorem u158 (x q l r v : Nat) (h : ¬x<929) (d : x/929=q) (a : s157 x=l) (b : s157 q=r) (c : l-r=v) : s158 x=v := stepCert s157 929 x q l r v h d a b c
theorem u159 (x q l r v : Nat) (h : ¬x<937) (d : x/937=q) (a : s158 x=l) (b : s158 q=r) (c : l-r=v) : s159 x=v := stepCert s158 937 x q l r v h d a b c
theorem u160 (x q l r v : Nat) (h : ¬x<941) (d : x/941=q) (a : s159 x=l) (b : s159 q=r) (c : l-r=v) : s160 x=v := stepCert s159 941 x q l r v h d a b c
theorem u161 (x q l r v : Nat) (h : ¬x<947) (d : x/947=q) (a : s160 x=l) (b : s160 q=r) (c : l-r=v) : s161 x=v := stepCert s160 947 x q l r v h d a b c
theorem u162 (x q l r v : Nat) (h : ¬x<953) (d : x/953=q) (a : s161 x=l) (b : s161 q=r) (c : l-r=v) : s162 x=v := stepCert s161 953 x q l r v h d a b c
theorem u163 (x q l r v : Nat) (h : ¬x<967) (d : x/967=q) (a : s162 x=l) (b : s162 q=r) (c : l-r=v) : s163 x=v := stepCert s162 967 x q l r v h d a b c
theorem u164 (x q l r v : Nat) (h : ¬x<971) (d : x/971=q) (a : s163 x=l) (b : s163 q=r) (c : l-r=v) : s164 x=v := stepCert s163 971 x q l r v h d a b c
theorem u165 (x q l r v : Nat) (h : ¬x<977) (d : x/977=q) (a : s164 x=l) (b : s164 q=r) (c : l-r=v) : s165 x=v := stepCert s164 977 x q l r v h d a b c
theorem u166 (x q l r v : Nat) (h : ¬x<983) (d : x/983=q) (a : s165 x=l) (b : s165 q=r) (c : l-r=v) : s166 x=v := stepCert s165 983 x q l r v h d a b c
theorem u167 (x q l r v : Nat) (h : ¬x<991) (d : x/991=q) (a : s166 x=l) (b : s166 q=r) (c : l-r=v) : s167 x=v := stepCert s166 991 x q l r v h d a b c
theorem u168 (x q l r v : Nat) (h : ¬x<997) (d : x/997=q) (a : s167 x=l) (b : s167 q=r) (c : l-r=v) : s168 x=v := stepCert s167 997 x q l r v h d a b c
theorem u169 (x q l r v : Nat) (h : ¬x<1009) (d : x/1009=q) (a : s168 x=l) (b : s168 q=r) (c : l-r=v) : s169 x=v := stepCert s168 1009 x q l r v h d a b c
theorem u170 (x q l r v : Nat) (h : ¬x<1013) (d : x/1013=q) (a : s169 x=l) (b : s169 q=r) (c : l-r=v) : s170 x=v := stepCert s169 1013 x q l r v h d a b c
theorem u171 (x q l r v : Nat) (h : ¬x<1019) (d : x/1019=q) (a : s170 x=l) (b : s170 q=r) (c : l-r=v) : s171 x=v := stepCert s170 1019 x q l r v h d a b c
theorem u172 (x q l r v : Nat) (h : ¬x<1021) (d : x/1021=q) (a : s171 x=l) (b : s171 q=r) (c : l-r=v) : s172 x=v := stepCert s171 1021 x q l r v h d a b c
theorem u173 (x q l r v : Nat) (h : ¬x<1031) (d : x/1031=q) (a : s172 x=l) (b : s172 q=r) (c : l-r=v) : s173 x=v := stepCert s172 1031 x q l r v h d a b c
theorem u174 (x q l r v : Nat) (h : ¬x<1033) (d : x/1033=q) (a : s173 x=l) (b : s173 q=r) (c : l-r=v) : s174 x=v := stepCert s173 1033 x q l r v h d a b c
theorem u175 (x q l r v : Nat) (h : ¬x<1039) (d : x/1039=q) (a : s174 x=l) (b : s174 q=r) (c : l-r=v) : s175 x=v := stepCert s174 1039 x q l r v h d a b c
theorem u176 (x q l r v : Nat) (h : ¬x<1049) (d : x/1049=q) (a : s175 x=l) (b : s175 q=r) (c : l-r=v) : s176 x=v := stepCert s175 1049 x q l r v h d a b c
theorem u177 (x q l r v : Nat) (h : ¬x<1051) (d : x/1051=q) (a : s176 x=l) (b : s176 q=r) (c : l-r=v) : s177 x=v := stepCert s176 1051 x q l r v h d a b c
theorem u178 (x q l r v : Nat) (h : ¬x<1061) (d : x/1061=q) (a : s177 x=l) (b : s177 q=r) (c : l-r=v) : s178 x=v := stepCert s177 1061 x q l r v h d a b c
theorem u179 (x q l r v : Nat) (h : ¬x<1063) (d : x/1063=q) (a : s178 x=l) (b : s178 q=r) (c : l-r=v) : s179 x=v := stepCert s178 1063 x q l r v h d a b c
theorem u180 (x q l r v : Nat) (h : ¬x<1069) (d : x/1069=q) (a : s179 x=l) (b : s179 q=r) (c : l-r=v) : s180 x=v := stepCert s179 1069 x q l r v h d a b c
theorem u181 (x q l r v : Nat) (h : ¬x<1087) (d : x/1087=q) (a : s180 x=l) (b : s180 q=r) (c : l-r=v) : s181 x=v := stepCert s180 1087 x q l r v h d a b c
theorem u182 (x q l r v : Nat) (h : ¬x<1091) (d : x/1091=q) (a : s181 x=l) (b : s181 q=r) (c : l-r=v) : s182 x=v := stepCert s181 1091 x q l r v h d a b c
theorem u183 (x q l r v : Nat) (h : ¬x<1093) (d : x/1093=q) (a : s182 x=l) (b : s182 q=r) (c : l-r=v) : s183 x=v := stepCert s182 1093 x q l r v h d a b c
theorem u184 (x q l r v : Nat) (h : ¬x<1097) (d : x/1097=q) (a : s183 x=l) (b : s183 q=r) (c : l-r=v) : s184 x=v := stepCert s183 1097 x q l r v h d a b c
theorem u185 (x q l r v : Nat) (h : ¬x<1103) (d : x/1103=q) (a : s184 x=l) (b : s184 q=r) (c : l-r=v) : s185 x=v := stepCert s184 1103 x q l r v h d a b c
theorem u186 (x q l r v : Nat) (h : ¬x<1109) (d : x/1109=q) (a : s185 x=l) (b : s185 q=r) (c : l-r=v) : s186 x=v := stepCert s185 1109 x q l r v h d a b c
theorem u187 (x q l r v : Nat) (h : ¬x<1117) (d : x/1117=q) (a : s186 x=l) (b : s186 q=r) (c : l-r=v) : s187 x=v := stepCert s186 1117 x q l r v h d a b c
theorem u188 (x q l r v : Nat) (h : ¬x<1123) (d : x/1123=q) (a : s187 x=l) (b : s187 q=r) (c : l-r=v) : s188 x=v := stepCert s187 1123 x q l r v h d a b c
theorem u189 (x q l r v : Nat) (h : ¬x<1129) (d : x/1129=q) (a : s188 x=l) (b : s188 q=r) (c : l-r=v) : s189 x=v := stepCert s188 1129 x q l r v h d a b c
theorem u190 (x q l r v : Nat) (h : ¬x<1151) (d : x/1151=q) (a : s189 x=l) (b : s189 q=r) (c : l-r=v) : s190 x=v := stepCert s189 1151 x q l r v h d a b c
theorem u191 (x q l r v : Nat) (h : ¬x<1153) (d : x/1153=q) (a : s190 x=l) (b : s190 q=r) (c : l-r=v) : s191 x=v := stepCert s190 1153 x q l r v h d a b c
theorem u192 (x q l r v : Nat) (h : ¬x<1163) (d : x/1163=q) (a : s191 x=l) (b : s191 q=r) (c : l-r=v) : s192 x=v := stepCert s191 1163 x q l r v h d a b c
theorem u193 (x q l r v : Nat) (h : ¬x<1171) (d : x/1171=q) (a : s192 x=l) (b : s192 q=r) (c : l-r=v) : s193 x=v := stepCert s192 1171 x q l r v h d a b c
theorem u194 (x q l r v : Nat) (h : ¬x<1181) (d : x/1181=q) (a : s193 x=l) (b : s193 q=r) (c : l-r=v) : s194 x=v := stepCert s193 1181 x q l r v h d a b c
theorem u195 (x q l r v : Nat) (h : ¬x<1187) (d : x/1187=q) (a : s194 x=l) (b : s194 q=r) (c : l-r=v) : s195 x=v := stepCert s194 1187 x q l r v h d a b c
theorem u196 (x q l r v : Nat) (h : ¬x<1193) (d : x/1193=q) (a : s195 x=l) (b : s195 q=r) (c : l-r=v) : s196 x=v := stepCert s195 1193 x q l r v h d a b c
theorem u197 (x q l r v : Nat) (h : ¬x<1201) (d : x/1201=q) (a : s196 x=l) (b : s196 q=r) (c : l-r=v) : s197 x=v := stepCert s196 1201 x q l r v h d a b c
theorem u198 (x q l r v : Nat) (h : ¬x<1213) (d : x/1213=q) (a : s197 x=l) (b : s197 q=r) (c : l-r=v) : s198 x=v := stepCert s197 1213 x q l r v h d a b c
theorem u199 (x q l r v : Nat) (h : ¬x<1217) (d : x/1217=q) (a : s198 x=l) (b : s198 q=r) (c : l-r=v) : s199 x=v := stepCert s198 1217 x q l r v h d a b c
theorem u200 (x q l r v : Nat) (h : ¬x<1223) (d : x/1223=q) (a : s199 x=l) (b : s199 q=r) (c : l-r=v) : s200 x=v := stepCert s199 1223 x q l r v h d a b c
theorem u201 (x q l r v : Nat) (h : ¬x<1229) (d : x/1229=q) (a : s200 x=l) (b : s200 q=r) (c : l-r=v) : s201 x=v := stepCert s200 1229 x q l r v h d a b c
theorem u202 (x q l r v : Nat) (h : ¬x<1231) (d : x/1231=q) (a : s201 x=l) (b : s201 q=r) (c : l-r=v) : s202 x=v := stepCert s201 1231 x q l r v h d a b c
theorem u203 (x q l r v : Nat) (h : ¬x<1237) (d : x/1237=q) (a : s202 x=l) (b : s202 q=r) (c : l-r=v) : s203 x=v := stepCert s202 1237 x q l r v h d a b c
theorem u204 (x q l r v : Nat) (h : ¬x<1249) (d : x/1249=q) (a : s203 x=l) (b : s203 q=r) (c : l-r=v) : s204 x=v := stepCert s203 1249 x q l r v h d a b c
theorem u205 (x q l r v : Nat) (h : ¬x<1259) (d : x/1259=q) (a : s204 x=l) (b : s204 q=r) (c : l-r=v) : s205 x=v := stepCert s204 1259 x q l r v h d a b c
theorem u206 (x q l r v : Nat) (h : ¬x<1277) (d : x/1277=q) (a : s205 x=l) (b : s205 q=r) (c : l-r=v) : s206 x=v := stepCert s205 1277 x q l r v h d a b c
theorem u207 (x q l r v : Nat) (h : ¬x<1279) (d : x/1279=q) (a : s206 x=l) (b : s206 q=r) (c : l-r=v) : s207 x=v := stepCert s206 1279 x q l r v h d a b c
theorem u208 (x q l r v : Nat) (h : ¬x<1283) (d : x/1283=q) (a : s207 x=l) (b : s207 q=r) (c : l-r=v) : s208 x=v := stepCert s207 1283 x q l r v h d a b c
theorem u209 (x q l r v : Nat) (h : ¬x<1289) (d : x/1289=q) (a : s208 x=l) (b : s208 q=r) (c : l-r=v) : s209 x=v := stepCert s208 1289 x q l r v h d a b c
theorem u210 (x q l r v : Nat) (h : ¬x<1291) (d : x/1291=q) (a : s209 x=l) (b : s209 q=r) (c : l-r=v) : s210 x=v := stepCert s209 1291 x q l r v h d a b c
theorem u211 (x q l r v : Nat) (h : ¬x<1297) (d : x/1297=q) (a : s210 x=l) (b : s210 q=r) (c : l-r=v) : s211 x=v := stepCert s210 1297 x q l r v h d a b c
theorem u212 (x q l r v : Nat) (h : ¬x<1301) (d : x/1301=q) (a : s211 x=l) (b : s211 q=r) (c : l-r=v) : s212 x=v := stepCert s211 1301 x q l r v h d a b c
theorem u213 (x q l r v : Nat) (h : ¬x<1303) (d : x/1303=q) (a : s212 x=l) (b : s212 q=r) (c : l-r=v) : s213 x=v := stepCert s212 1303 x q l r v h d a b c
theorem u214 (x q l r v : Nat) (h : ¬x<1307) (d : x/1307=q) (a : s213 x=l) (b : s213 q=r) (c : l-r=v) : s214 x=v := stepCert s213 1307 x q l r v h d a b c
theorem u215 (x q l r v : Nat) (h : ¬x<1319) (d : x/1319=q) (a : s214 x=l) (b : s214 q=r) (c : l-r=v) : s215 x=v := stepCert s214 1319 x q l r v h d a b c
theorem u216 (x q l r v : Nat) (h : ¬x<1321) (d : x/1321=q) (a : s215 x=l) (b : s215 q=r) (c : l-r=v) : s216 x=v := stepCert s215 1321 x q l r v h d a b c
theorem u217 (x q l r v : Nat) (h : ¬x<1327) (d : x/1327=q) (a : s216 x=l) (b : s216 q=r) (c : l-r=v) : s217 x=v := stepCert s216 1327 x q l r v h d a b c
theorem u218 (x q l r v : Nat) (h : ¬x<1361) (d : x/1361=q) (a : s217 x=l) (b : s217 q=r) (c : l-r=v) : s218 x=v := stepCert s217 1361 x q l r v h d a b c
theorem u219 (x q l r v : Nat) (h : ¬x<1367) (d : x/1367=q) (a : s218 x=l) (b : s218 q=r) (c : l-r=v) : s219 x=v := stepCert s218 1367 x q l r v h d a b c
theorem u220 (x q l r v : Nat) (h : ¬x<1373) (d : x/1373=q) (a : s219 x=l) (b : s219 q=r) (c : l-r=v) : s220 x=v := stepCert s219 1373 x q l r v h d a b c
theorem u221 (x q l r v : Nat) (h : ¬x<1381) (d : x/1381=q) (a : s220 x=l) (b : s220 q=r) (c : l-r=v) : s221 x=v := stepCert s220 1381 x q l r v h d a b c
theorem u222 (x q l r v : Nat) (h : ¬x<1399) (d : x/1399=q) (a : s221 x=l) (b : s221 q=r) (c : l-r=v) : s222 x=v := stepCert s221 1399 x q l r v h d a b c
theorem u223 (x q l r v : Nat) (h : ¬x<1409) (d : x/1409=q) (a : s222 x=l) (b : s222 q=r) (c : l-r=v) : s223 x=v := stepCert s222 1409 x q l r v h d a b c
theorem u224 (x q l r v : Nat) (h : ¬x<1423) (d : x/1423=q) (a : s223 x=l) (b : s223 q=r) (c : l-r=v) : s224 x=v := stepCert s223 1423 x q l r v h d a b c
theorem u225 (x q l r v : Nat) (h : ¬x<1427) (d : x/1427=q) (a : s224 x=l) (b : s224 q=r) (c : l-r=v) : s225 x=v := stepCert s224 1427 x q l r v h d a b c
theorem u226 (x q l r v : Nat) (h : ¬x<1429) (d : x/1429=q) (a : s225 x=l) (b : s225 q=r) (c : l-r=v) : s226 x=v := stepCert s225 1429 x q l r v h d a b c
theorem u227 (x q l r v : Nat) (h : ¬x<1433) (d : x/1433=q) (a : s226 x=l) (b : s226 q=r) (c : l-r=v) : s227 x=v := stepCert s226 1433 x q l r v h d a b c
theorem u228 (x q l r v : Nat) (h : ¬x<1439) (d : x/1439=q) (a : s227 x=l) (b : s227 q=r) (c : l-r=v) : s228 x=v := stepCert s227 1439 x q l r v h d a b c
theorem u229 (x q l r v : Nat) (h : ¬x<1447) (d : x/1447=q) (a : s228 x=l) (b : s228 q=r) (c : l-r=v) : s229 x=v := stepCert s228 1447 x q l r v h d a b c
theorem u230 (x q l r v : Nat) (h : ¬x<1451) (d : x/1451=q) (a : s229 x=l) (b : s229 q=r) (c : l-r=v) : s230 x=v := stepCert s229 1451 x q l r v h d a b c
theorem u231 (x q l r v : Nat) (h : ¬x<1453) (d : x/1453=q) (a : s230 x=l) (b : s230 q=r) (c : l-r=v) : s231 x=v := stepCert s230 1453 x q l r v h d a b c
theorem u232 (x q l r v : Nat) (h : ¬x<1459) (d : x/1459=q) (a : s231 x=l) (b : s231 q=r) (c : l-r=v) : s232 x=v := stepCert s231 1459 x q l r v h d a b c
theorem u233 (x q l r v : Nat) (h : ¬x<1471) (d : x/1471=q) (a : s232 x=l) (b : s232 q=r) (c : l-r=v) : s233 x=v := stepCert s232 1471 x q l r v h d a b c
theorem u234 (x q l r v : Nat) (h : ¬x<1481) (d : x/1481=q) (a : s233 x=l) (b : s233 q=r) (c : l-r=v) : s234 x=v := stepCert s233 1481 x q l r v h d a b c
theorem u235 (x q l r v : Nat) (h : ¬x<1483) (d : x/1483=q) (a : s234 x=l) (b : s234 q=r) (c : l-r=v) : s235 x=v := stepCert s234 1483 x q l r v h d a b c
theorem u236 (x q l r v : Nat) (h : ¬x<1487) (d : x/1487=q) (a : s235 x=l) (b : s235 q=r) (c : l-r=v) : s236 x=v := stepCert s235 1487 x q l r v h d a b c
theorem u237 (x q l r v : Nat) (h : ¬x<1489) (d : x/1489=q) (a : s236 x=l) (b : s236 q=r) (c : l-r=v) : s237 x=v := stepCert s236 1489 x q l r v h d a b c
theorem u238 (x q l r v : Nat) (h : ¬x<1493) (d : x/1493=q) (a : s237 x=l) (b : s237 q=r) (c : l-r=v) : s238 x=v := stepCert s237 1493 x q l r v h d a b c
theorem u239 (x q l r v : Nat) (h : ¬x<1499) (d : x/1499=q) (a : s238 x=l) (b : s238 q=r) (c : l-r=v) : s239 x=v := stepCert s238 1499 x q l r v h d a b c
theorem u240 (x q l r v : Nat) (h : ¬x<1511) (d : x/1511=q) (a : s239 x=l) (b : s239 q=r) (c : l-r=v) : s240 x=v := stepCert s239 1511 x q l r v h d a b c
theorem u241 (x q l r v : Nat) (h : ¬x<1523) (d : x/1523=q) (a : s240 x=l) (b : s240 q=r) (c : l-r=v) : s241 x=v := stepCert s240 1523 x q l r v h d a b c
theorem u242 (x q l r v : Nat) (h : ¬x<1531) (d : x/1531=q) (a : s241 x=l) (b : s241 q=r) (c : l-r=v) : s242 x=v := stepCert s241 1531 x q l r v h d a b c
theorem u243 (x q l r v : Nat) (h : ¬x<1543) (d : x/1543=q) (a : s242 x=l) (b : s242 q=r) (c : l-r=v) : s243 x=v := stepCert s242 1543 x q l r v h d a b c
theorem u244 (x q l r v : Nat) (h : ¬x<1549) (d : x/1549=q) (a : s243 x=l) (b : s243 q=r) (c : l-r=v) : s244 x=v := stepCert s243 1549 x q l r v h d a b c
theorem u245 (x q l r v : Nat) (h : ¬x<1553) (d : x/1553=q) (a : s244 x=l) (b : s244 q=r) (c : l-r=v) : s245 x=v := stepCert s244 1553 x q l r v h d a b c
theorem u246 (x q l r v : Nat) (h : ¬x<1559) (d : x/1559=q) (a : s245 x=l) (b : s245 q=r) (c : l-r=v) : s246 x=v := stepCert s245 1559 x q l r v h d a b c
theorem u247 (x q l r v : Nat) (h : ¬x<1567) (d : x/1567=q) (a : s246 x=l) (b : s246 q=r) (c : l-r=v) : s247 x=v := stepCert s246 1567 x q l r v h d a b c
theorem u248 (x q l r v : Nat) (h : ¬x<1571) (d : x/1571=q) (a : s247 x=l) (b : s247 q=r) (c : l-r=v) : s248 x=v := stepCert s247 1571 x q l r v h d a b c
theorem u249 (x q l r v : Nat) (h : ¬x<1579) (d : x/1579=q) (a : s248 x=l) (b : s248 q=r) (c : l-r=v) : s249 x=v := stepCert s248 1579 x q l r v h d a b c
theorem u250 (x q l r v : Nat) (h : ¬x<1583) (d : x/1583=q) (a : s249 x=l) (b : s249 q=r) (c : l-r=v) : s250 x=v := stepCert s249 1583 x q l r v h d a b c
theorem u251 (x q l r v : Nat) (h : ¬x<1597) (d : x/1597=q) (a : s250 x=l) (b : s250 q=r) (c : l-r=v) : s251 x=v := stepCert s250 1597 x q l r v h d a b c
theorem u252 (x q l r v : Nat) (h : ¬x<1601) (d : x/1601=q) (a : s251 x=l) (b : s251 q=r) (c : l-r=v) : s252 x=v := stepCert s251 1601 x q l r v h d a b c
theorem u253 (x q l r v : Nat) (h : ¬x<1607) (d : x/1607=q) (a : s252 x=l) (b : s252 q=r) (c : l-r=v) : s253 x=v := stepCert s252 1607 x q l r v h d a b c
theorem u254 (x q l r v : Nat) (h : ¬x<1609) (d : x/1609=q) (a : s253 x=l) (b : s253 q=r) (c : l-r=v) : s254 x=v := stepCert s253 1609 x q l r v h d a b c
theorem u255 (x q l r v : Nat) (h : ¬x<1613) (d : x/1613=q) (a : s254 x=l) (b : s254 q=r) (c : l-r=v) : s255 x=v := stepCert s254 1613 x q l r v h d a b c
theorem u256 (x q l r v : Nat) (h : ¬x<1619) (d : x/1619=q) (a : s255 x=l) (b : s255 q=r) (c : l-r=v) : s256 x=v := stepCert s255 1619 x q l r v h d a b c
theorem u257 (x q l r v : Nat) (h : ¬x<1621) (d : x/1621=q) (a : s256 x=l) (b : s256 q=r) (c : l-r=v) : s257 x=v := stepCert s256 1621 x q l r v h d a b c
theorem u258 (x q l r v : Nat) (h : ¬x<1627) (d : x/1627=q) (a : s257 x=l) (b : s257 q=r) (c : l-r=v) : s258 x=v := stepCert s257 1627 x q l r v h d a b c
theorem u259 (x q l r v : Nat) (h : ¬x<1637) (d : x/1637=q) (a : s258 x=l) (b : s258 q=r) (c : l-r=v) : s259 x=v := stepCert s258 1637 x q l r v h d a b c
theorem u260 (x q l r v : Nat) (h : ¬x<1657) (d : x/1657=q) (a : s259 x=l) (b : s259 q=r) (c : l-r=v) : s260 x=v := stepCert s259 1657 x q l r v h d a b c
theorem u261 (x q l r v : Nat) (h : ¬x<1663) (d : x/1663=q) (a : s260 x=l) (b : s260 q=r) (c : l-r=v) : s261 x=v := stepCert s260 1663 x q l r v h d a b c
theorem u262 (x q l r v : Nat) (h : ¬x<1667) (d : x/1667=q) (a : s261 x=l) (b : s261 q=r) (c : l-r=v) : s262 x=v := stepCert s261 1667 x q l r v h d a b c
theorem u263 (x q l r v : Nat) (h : ¬x<1669) (d : x/1669=q) (a : s262 x=l) (b : s262 q=r) (c : l-r=v) : s263 x=v := stepCert s262 1669 x q l r v h d a b c
theorem u264 (x q l r v : Nat) (h : ¬x<1693) (d : x/1693=q) (a : s263 x=l) (b : s263 q=r) (c : l-r=v) : s264 x=v := stepCert s263 1693 x q l r v h d a b c
theorem u265 (x q l r v : Nat) (h : ¬x<1697) (d : x/1697=q) (a : s264 x=l) (b : s264 q=r) (c : l-r=v) : s265 x=v := stepCert s264 1697 x q l r v h d a b c
theorem u266 (x q l r v : Nat) (h : ¬x<1699) (d : x/1699=q) (a : s265 x=l) (b : s265 q=r) (c : l-r=v) : s266 x=v := stepCert s265 1699 x q l r v h d a b c
theorem u267 (x q l r v : Nat) (h : ¬x<1709) (d : x/1709=q) (a : s266 x=l) (b : s266 q=r) (c : l-r=v) : s267 x=v := stepCert s266 1709 x q l r v h d a b c
theorem u268 (x q l r v : Nat) (h : ¬x<1721) (d : x/1721=q) (a : s267 x=l) (b : s267 q=r) (c : l-r=v) : s268 x=v := stepCert s267 1721 x q l r v h d a b c
theorem u269 (x q l r v : Nat) (h : ¬x<1723) (d : x/1723=q) (a : s268 x=l) (b : s268 q=r) (c : l-r=v) : s269 x=v := stepCert s268 1723 x q l r v h d a b c
theorem u270 (x q l r v : Nat) (h : ¬x<1733) (d : x/1733=q) (a : s269 x=l) (b : s269 q=r) (c : l-r=v) : s270 x=v := stepCert s269 1733 x q l r v h d a b c
theorem u271 (x q l r v : Nat) (h : ¬x<1741) (d : x/1741=q) (a : s270 x=l) (b : s270 q=r) (c : l-r=v) : s271 x=v := stepCert s270 1741 x q l r v h d a b c
theorem u272 (x q l r v : Nat) (h : ¬x<1747) (d : x/1747=q) (a : s271 x=l) (b : s271 q=r) (c : l-r=v) : s272 x=v := stepCert s271 1747 x q l r v h d a b c
theorem u273 (x q l r v : Nat) (h : ¬x<1753) (d : x/1753=q) (a : s272 x=l) (b : s272 q=r) (c : l-r=v) : s273 x=v := stepCert s272 1753 x q l r v h d a b c
theorem u274 (x q l r v : Nat) (h : ¬x<1759) (d : x/1759=q) (a : s273 x=l) (b : s273 q=r) (c : l-r=v) : s274 x=v := stepCert s273 1759 x q l r v h d a b c
theorem u275 (x q l r v : Nat) (h : ¬x<1777) (d : x/1777=q) (a : s274 x=l) (b : s274 q=r) (c : l-r=v) : s275 x=v := stepCert s274 1777 x q l r v h d a b c
theorem u276 (x q l r v : Nat) (h : ¬x<1783) (d : x/1783=q) (a : s275 x=l) (b : s275 q=r) (c : l-r=v) : s276 x=v := stepCert s275 1783 x q l r v h d a b c
theorem u277 (x q l r v : Nat) (h : ¬x<1787) (d : x/1787=q) (a : s276 x=l) (b : s276 q=r) (c : l-r=v) : s277 x=v := stepCert s276 1787 x q l r v h d a b c
theorem u278 (x q l r v : Nat) (h : ¬x<1789) (d : x/1789=q) (a : s277 x=l) (b : s277 q=r) (c : l-r=v) : s278 x=v := stepCert s277 1789 x q l r v h d a b c
theorem u279 (x q l r v : Nat) (h : ¬x<1801) (d : x/1801=q) (a : s278 x=l) (b : s278 q=r) (c : l-r=v) : s279 x=v := stepCert s278 1801 x q l r v h d a b c
theorem u280 (x q l r v : Nat) (h : ¬x<1811) (d : x/1811=q) (a : s279 x=l) (b : s279 q=r) (c : l-r=v) : s280 x=v := stepCert s279 1811 x q l r v h d a b c
theorem u281 (x q l r v : Nat) (h : ¬x<1823) (d : x/1823=q) (a : s280 x=l) (b : s280 q=r) (c : l-r=v) : s281 x=v := stepCert s280 1823 x q l r v h d a b c
theorem u282 (x q l r v : Nat) (h : ¬x<1831) (d : x/1831=q) (a : s281 x=l) (b : s281 q=r) (c : l-r=v) : s282 x=v := stepCert s281 1831 x q l r v h d a b c
theorem u283 (x q l r v : Nat) (h : ¬x<1847) (d : x/1847=q) (a : s282 x=l) (b : s282 q=r) (c : l-r=v) : s283 x=v := stepCert s282 1847 x q l r v h d a b c
theorem u284 (x q l r v : Nat) (h : ¬x<1861) (d : x/1861=q) (a : s283 x=l) (b : s283 q=r) (c : l-r=v) : s284 x=v := stepCert s283 1861 x q l r v h d a b c
theorem u285 (x q l r v : Nat) (h : ¬x<1867) (d : x/1867=q) (a : s284 x=l) (b : s284 q=r) (c : l-r=v) : s285 x=v := stepCert s284 1867 x q l r v h d a b c
theorem u286 (x q l r v : Nat) (h : ¬x<1871) (d : x/1871=q) (a : s285 x=l) (b : s285 q=r) (c : l-r=v) : s286 x=v := stepCert s285 1871 x q l r v h d a b c
theorem u287 (x q l r v : Nat) (h : ¬x<1873) (d : x/1873=q) (a : s286 x=l) (b : s286 q=r) (c : l-r=v) : s287 x=v := stepCert s286 1873 x q l r v h d a b c
theorem u288 (x q l r v : Nat) (h : ¬x<1877) (d : x/1877=q) (a : s287 x=l) (b : s287 q=r) (c : l-r=v) : s288 x=v := stepCert s287 1877 x q l r v h d a b c
theorem u289 (x q l r v : Nat) (h : ¬x<1879) (d : x/1879=q) (a : s288 x=l) (b : s288 q=r) (c : l-r=v) : s289 x=v := stepCert s288 1879 x q l r v h d a b c
theorem u290 (x q l r v : Nat) (h : ¬x<1889) (d : x/1889=q) (a : s289 x=l) (b : s289 q=r) (c : l-r=v) : s290 x=v := stepCert s289 1889 x q l r v h d a b c
theorem u291 (x q l r v : Nat) (h : ¬x<1901) (d : x/1901=q) (a : s290 x=l) (b : s290 q=r) (c : l-r=v) : s291 x=v := stepCert s290 1901 x q l r v h d a b c
theorem u292 (x q l r v : Nat) (h : ¬x<1907) (d : x/1907=q) (a : s291 x=l) (b : s291 q=r) (c : l-r=v) : s292 x=v := stepCert s291 1907 x q l r v h d a b c
theorem u293 (x q l r v : Nat) (h : ¬x<1913) (d : x/1913=q) (a : s292 x=l) (b : s292 q=r) (c : l-r=v) : s293 x=v := stepCert s292 1913 x q l r v h d a b c
theorem u294 (x q l r v : Nat) (h : ¬x<1931) (d : x/1931=q) (a : s293 x=l) (b : s293 q=r) (c : l-r=v) : s294 x=v := stepCert s293 1931 x q l r v h d a b c
theorem u295 (x q l r v : Nat) (h : ¬x<1933) (d : x/1933=q) (a : s294 x=l) (b : s294 q=r) (c : l-r=v) : s295 x=v := stepCert s294 1933 x q l r v h d a b c
theorem u296 (x q l r v : Nat) (h : ¬x<1949) (d : x/1949=q) (a : s295 x=l) (b : s295 q=r) (c : l-r=v) : s296 x=v := stepCert s295 1949 x q l r v h d a b c
theorem u297 (x q l r v : Nat) (h : ¬x<1951) (d : x/1951=q) (a : s296 x=l) (b : s296 q=r) (c : l-r=v) : s297 x=v := stepCert s296 1951 x q l r v h d a b c
theorem u298 (x q l r v : Nat) (h : ¬x<1973) (d : x/1973=q) (a : s297 x=l) (b : s297 q=r) (c : l-r=v) : s298 x=v := stepCert s297 1973 x q l r v h d a b c
theorem u299 (x q l r v : Nat) (h : ¬x<1979) (d : x/1979=q) (a : s298 x=l) (b : s298 q=r) (c : l-r=v) : s299 x=v := stepCert s298 1979 x q l r v h d a b c
theorem u300 (x q l r v : Nat) (h : ¬x<1987) (d : x/1987=q) (a : s299 x=l) (b : s299 q=r) (c : l-r=v) : s300 x=v := stepCert s299 1987 x q l r v h d a b c
theorem u301 (x q l r v : Nat) (h : ¬x<1993) (d : x/1993=q) (a : s300 x=l) (b : s300 q=r) (c : l-r=v) : s301 x=v := stepCert s300 1993 x q l r v h d a b c
theorem u302 (x q l r v : Nat) (h : ¬x<1997) (d : x/1997=q) (a : s301 x=l) (b : s301 q=r) (c : l-r=v) : s302 x=v := stepCert s301 1997 x q l r v h d a b c
theorem u303 (x q l r v : Nat) (h : ¬x<1999) (d : x/1999=q) (a : s302 x=l) (b : s302 q=r) (c : l-r=v) : s303 x=v := stepCert s302 1999 x q l r v h d a b c
theorem u304 (x q l r v : Nat) (h : ¬x<2003) (d : x/2003=q) (a : s303 x=l) (b : s303 q=r) (c : l-r=v) : s304 x=v := stepCert s303 2003 x q l r v h d a b c
theorem u305 (x q l r v : Nat) (h : ¬x<2011) (d : x/2011=q) (a : s304 x=l) (b : s304 q=r) (c : l-r=v) : s305 x=v := stepCert s304 2011 x q l r v h d a b c
theorem u306 (x q l r v : Nat) (h : ¬x<2017) (d : x/2017=q) (a : s305 x=l) (b : s305 q=r) (c : l-r=v) : s306 x=v := stepCert s305 2017 x q l r v h d a b c
theorem u307 (x q l r v : Nat) (h : ¬x<2027) (d : x/2027=q) (a : s306 x=l) (b : s306 q=r) (c : l-r=v) : s307 x=v := stepCert s306 2027 x q l r v h d a b c
theorem u308 (x q l r v : Nat) (h : ¬x<2029) (d : x/2029=q) (a : s307 x=l) (b : s307 q=r) (c : l-r=v) : s308 x=v := stepCert s307 2029 x q l r v h d a b c
theorem u309 (x q l r v : Nat) (h : ¬x<2039) (d : x/2039=q) (a : s308 x=l) (b : s308 q=r) (c : l-r=v) : s309 x=v := stepCert s308 2039 x q l r v h d a b c
theorem u310 (x q l r v : Nat) (h : ¬x<2053) (d : x/2053=q) (a : s309 x=l) (b : s309 q=r) (c : l-r=v) : s310 x=v := stepCert s309 2053 x q l r v h d a b c
theorem u311 (x q l r v : Nat) (h : ¬x<2063) (d : x/2063=q) (a : s310 x=l) (b : s310 q=r) (c : l-r=v) : s311 x=v := stepCert s310 2063 x q l r v h d a b c
theorem u312 (x q l r v : Nat) (h : ¬x<2069) (d : x/2069=q) (a : s311 x=l) (b : s311 q=r) (c : l-r=v) : s312 x=v := stepCert s311 2069 x q l r v h d a b c
theorem u313 (x q l r v : Nat) (h : ¬x<2081) (d : x/2081=q) (a : s312 x=l) (b : s312 q=r) (c : l-r=v) : s313 x=v := stepCert s312 2081 x q l r v h d a b c
theorem u314 (x q l r v : Nat) (h : ¬x<2083) (d : x/2083=q) (a : s313 x=l) (b : s313 q=r) (c : l-r=v) : s314 x=v := stepCert s313 2083 x q l r v h d a b c
theorem u315 (x q l r v : Nat) (h : ¬x<2087) (d : x/2087=q) (a : s314 x=l) (b : s314 q=r) (c : l-r=v) : s315 x=v := stepCert s314 2087 x q l r v h d a b c
theorem u316 (x q l r v : Nat) (h : ¬x<2089) (d : x/2089=q) (a : s315 x=l) (b : s315 q=r) (c : l-r=v) : s316 x=v := stepCert s315 2089 x q l r v h d a b c
theorem u317 (x q l r v : Nat) (h : ¬x<2099) (d : x/2099=q) (a : s316 x=l) (b : s316 q=r) (c : l-r=v) : s317 x=v := stepCert s316 2099 x q l r v h d a b c
theorem u318 (x q l r v : Nat) (h : ¬x<2111) (d : x/2111=q) (a : s317 x=l) (b : s317 q=r) (c : l-r=v) : s318 x=v := stepCert s317 2111 x q l r v h d a b c
theorem u319 (x q l r v : Nat) (h : ¬x<2113) (d : x/2113=q) (a : s318 x=l) (b : s318 q=r) (c : l-r=v) : s319 x=v := stepCert s318 2113 x q l r v h d a b c
theorem u320 (x q l r v : Nat) (h : ¬x<2129) (d : x/2129=q) (a : s319 x=l) (b : s319 q=r) (c : l-r=v) : s320 x=v := stepCert s319 2129 x q l r v h d a b c
theorem u321 (x q l r v : Nat) (h : ¬x<2131) (d : x/2131=q) (a : s320 x=l) (b : s320 q=r) (c : l-r=v) : s321 x=v := stepCert s320 2131 x q l r v h d a b c
theorem u322 (x q l r v : Nat) (h : ¬x<2137) (d : x/2137=q) (a : s321 x=l) (b : s321 q=r) (c : l-r=v) : s322 x=v := stepCert s321 2137 x q l r v h d a b c
theorem u323 (x q l r v : Nat) (h : ¬x<2141) (d : x/2141=q) (a : s322 x=l) (b : s322 q=r) (c : l-r=v) : s323 x=v := stepCert s322 2141 x q l r v h d a b c
theorem u324 (x q l r v : Nat) (h : ¬x<2143) (d : x/2143=q) (a : s323 x=l) (b : s323 q=r) (c : l-r=v) : s324 x=v := stepCert s323 2143 x q l r v h d a b c
theorem u325 (x q l r v : Nat) (h : ¬x<2153) (d : x/2153=q) (a : s324 x=l) (b : s324 q=r) (c : l-r=v) : s325 x=v := stepCert s324 2153 x q l r v h d a b c
theorem u326 (x q l r v : Nat) (h : ¬x<2161) (d : x/2161=q) (a : s325 x=l) (b : s325 q=r) (c : l-r=v) : s326 x=v := stepCert s325 2161 x q l r v h d a b c
theorem u327 (x q l r v : Nat) (h : ¬x<2179) (d : x/2179=q) (a : s326 x=l) (b : s326 q=r) (c : l-r=v) : s327 x=v := stepCert s326 2179 x q l r v h d a b c
theorem u328 (x q l r v : Nat) (h : ¬x<2203) (d : x/2203=q) (a : s327 x=l) (b : s327 q=r) (c : l-r=v) : s328 x=v := stepCert s327 2203 x q l r v h d a b c
theorem u329 (x q l r v : Nat) (h : ¬x<2207) (d : x/2207=q) (a : s328 x=l) (b : s328 q=r) (c : l-r=v) : s329 x=v := stepCert s328 2207 x q l r v h d a b c
theorem u330 (x q l r v : Nat) (h : ¬x<2213) (d : x/2213=q) (a : s329 x=l) (b : s329 q=r) (c : l-r=v) : s330 x=v := stepCert s329 2213 x q l r v h d a b c
theorem u331 (x q l r v : Nat) (h : ¬x<2221) (d : x/2221=q) (a : s330 x=l) (b : s330 q=r) (c : l-r=v) : s331 x=v := stepCert s330 2221 x q l r v h d a b c
theorem u332 (x q l r v : Nat) (h : ¬x<2237) (d : x/2237=q) (a : s331 x=l) (b : s331 q=r) (c : l-r=v) : s332 x=v := stepCert s331 2237 x q l r v h d a b c
theorem u333 (x q l r v : Nat) (h : ¬x<2239) (d : x/2239=q) (a : s332 x=l) (b : s332 q=r) (c : l-r=v) : s333 x=v := stepCert s332 2239 x q l r v h d a b c
theorem u334 (x q l r v : Nat) (h : ¬x<2243) (d : x/2243=q) (a : s333 x=l) (b : s333 q=r) (c : l-r=v) : s334 x=v := stepCert s333 2243 x q l r v h d a b c
theorem u335 (x q l r v : Nat) (h : ¬x<2251) (d : x/2251=q) (a : s334 x=l) (b : s334 q=r) (c : l-r=v) : s335 x=v := stepCert s334 2251 x q l r v h d a b c
theorem u336 (x q l r v : Nat) (h : ¬x<2267) (d : x/2267=q) (a : s335 x=l) (b : s335 q=r) (c : l-r=v) : s336 x=v := stepCert s335 2267 x q l r v h d a b c
theorem u337 (x q l r v : Nat) (h : ¬x<2269) (d : x/2269=q) (a : s336 x=l) (b : s336 q=r) (c : l-r=v) : s337 x=v := stepCert s336 2269 x q l r v h d a b c
theorem u338 (x q l r v : Nat) (h : ¬x<2273) (d : x/2273=q) (a : s337 x=l) (b : s337 q=r) (c : l-r=v) : s338 x=v := stepCert s337 2273 x q l r v h d a b c
theorem u339 (x q l r v : Nat) (h : ¬x<2281) (d : x/2281=q) (a : s338 x=l) (b : s338 q=r) (c : l-r=v) : s339 x=v := stepCert s338 2281 x q l r v h d a b c
theorem u340 (x q l r v : Nat) (h : ¬x<2287) (d : x/2287=q) (a : s339 x=l) (b : s339 q=r) (c : l-r=v) : s340 x=v := stepCert s339 2287 x q l r v h d a b c
theorem u341 (x q l r v : Nat) (h : ¬x<2293) (d : x/2293=q) (a : s340 x=l) (b : s340 q=r) (c : l-r=v) : s341 x=v := stepCert s340 2293 x q l r v h d a b c
theorem u342 (x q l r v : Nat) (h : ¬x<2297) (d : x/2297=q) (a : s341 x=l) (b : s341 q=r) (c : l-r=v) : s342 x=v := stepCert s341 2297 x q l r v h d a b c
theorem u343 (x q l r v : Nat) (h : ¬x<2309) (d : x/2309=q) (a : s342 x=l) (b : s342 q=r) (c : l-r=v) : s343 x=v := stepCert s342 2309 x q l r v h d a b c
theorem u344 (x q l r v : Nat) (h : ¬x<2311) (d : x/2311=q) (a : s343 x=l) (b : s343 q=r) (c : l-r=v) : s344 x=v := stepCert s343 2311 x q l r v h d a b c
theorem u345 (x q l r v : Nat) (h : ¬x<2333) (d : x/2333=q) (a : s344 x=l) (b : s344 q=r) (c : l-r=v) : s345 x=v := stepCert s344 2333 x q l r v h d a b c
theorem u346 (x q l r v : Nat) (h : ¬x<2339) (d : x/2339=q) (a : s345 x=l) (b : s345 q=r) (c : l-r=v) : s346 x=v := stepCert s345 2339 x q l r v h d a b c
theorem u347 (x q l r v : Nat) (h : ¬x<2341) (d : x/2341=q) (a : s346 x=l) (b : s346 q=r) (c : l-r=v) : s347 x=v := stepCert s346 2341 x q l r v h d a b c
theorem u348 (x q l r v : Nat) (h : ¬x<2347) (d : x/2347=q) (a : s347 x=l) (b : s347 q=r) (c : l-r=v) : s348 x=v := stepCert s347 2347 x q l r v h d a b c
theorem u349 (x q l r v : Nat) (h : ¬x<2351) (d : x/2351=q) (a : s348 x=l) (b : s348 q=r) (c : l-r=v) : s349 x=v := stepCert s348 2351 x q l r v h d a b c
theorem u350 (x q l r v : Nat) (h : ¬x<2357) (d : x/2357=q) (a : s349 x=l) (b : s349 q=r) (c : l-r=v) : s350 x=v := stepCert s349 2357 x q l r v h d a b c
theorem u351 (x q l r v : Nat) (h : ¬x<2371) (d : x/2371=q) (a : s350 x=l) (b : s350 q=r) (c : l-r=v) : s351 x=v := stepCert s350 2371 x q l r v h d a b c
theorem u352 (x q l r v : Nat) (h : ¬x<2377) (d : x/2377=q) (a : s351 x=l) (b : s351 q=r) (c : l-r=v) : s352 x=v := stepCert s351 2377 x q l r v h d a b c
theorem u353 (x q l r v : Nat) (h : ¬x<2381) (d : x/2381=q) (a : s352 x=l) (b : s352 q=r) (c : l-r=v) : s353 x=v := stepCert s352 2381 x q l r v h d a b c
theorem u354 (x q l r v : Nat) (h : ¬x<2383) (d : x/2383=q) (a : s353 x=l) (b : s353 q=r) (c : l-r=v) : s354 x=v := stepCert s353 2383 x q l r v h d a b c
theorem u355 (x q l r v : Nat) (h : ¬x<2389) (d : x/2389=q) (a : s354 x=l) (b : s354 q=r) (c : l-r=v) : s355 x=v := stepCert s354 2389 x q l r v h d a b c
theorem u356 (x q l r v : Nat) (h : ¬x<2393) (d : x/2393=q) (a : s355 x=l) (b : s355 q=r) (c : l-r=v) : s356 x=v := stepCert s355 2393 x q l r v h d a b c
theorem u357 (x q l r v : Nat) (h : ¬x<2399) (d : x/2399=q) (a : s356 x=l) (b : s356 q=r) (c : l-r=v) : s357 x=v := stepCert s356 2399 x q l r v h d a b c
theorem u358 (x q l r v : Nat) (h : ¬x<2411) (d : x/2411=q) (a : s357 x=l) (b : s357 q=r) (c : l-r=v) : s358 x=v := stepCert s357 2411 x q l r v h d a b c
theorem u359 (x q l r v : Nat) (h : ¬x<2417) (d : x/2417=q) (a : s358 x=l) (b : s358 q=r) (c : l-r=v) : s359 x=v := stepCert s358 2417 x q l r v h d a b c
theorem u360 (x q l r v : Nat) (h : ¬x<2423) (d : x/2423=q) (a : s359 x=l) (b : s359 q=r) (c : l-r=v) : s360 x=v := stepCert s359 2423 x q l r v h d a b c
theorem u361 (x q l r v : Nat) (h : ¬x<2437) (d : x/2437=q) (a : s360 x=l) (b : s360 q=r) (c : l-r=v) : s361 x=v := stepCert s360 2437 x q l r v h d a b c
theorem u362 (x q l r v : Nat) (h : ¬x<2441) (d : x/2441=q) (a : s361 x=l) (b : s361 q=r) (c : l-r=v) : s362 x=v := stepCert s361 2441 x q l r v h d a b c
theorem u363 (x q l r v : Nat) (h : ¬x<2447) (d : x/2447=q) (a : s362 x=l) (b : s362 q=r) (c : l-r=v) : s363 x=v := stepCert s362 2447 x q l r v h d a b c
theorem u364 (x q l r v : Nat) (h : ¬x<2459) (d : x/2459=q) (a : s363 x=l) (b : s363 q=r) (c : l-r=v) : s364 x=v := stepCert s363 2459 x q l r v h d a b c
theorem u365 (x q l r v : Nat) (h : ¬x<2467) (d : x/2467=q) (a : s364 x=l) (b : s364 q=r) (c : l-r=v) : s365 x=v := stepCert s364 2467 x q l r v h d a b c
theorem u366 (x q l r v : Nat) (h : ¬x<2473) (d : x/2473=q) (a : s365 x=l) (b : s365 q=r) (c : l-r=v) : s366 x=v := stepCert s365 2473 x q l r v h d a b c
theorem u367 (x q l r v : Nat) (h : ¬x<2477) (d : x/2477=q) (a : s366 x=l) (b : s366 q=r) (c : l-r=v) : s367 x=v := stepCert s366 2477 x q l r v h d a b c
theorem u368 (x q l r v : Nat) (h : ¬x<2503) (d : x/2503=q) (a : s367 x=l) (b : s367 q=r) (c : l-r=v) : s368 x=v := stepCert s367 2503 x q l r v h d a b c
theorem u369 (x q l r v : Nat) (h : ¬x<2521) (d : x/2521=q) (a : s368 x=l) (b : s368 q=r) (c : l-r=v) : s369 x=v := stepCert s368 2521 x q l r v h d a b c
theorem u370 (x q l r v : Nat) (h : ¬x<2531) (d : x/2531=q) (a : s369 x=l) (b : s369 q=r) (c : l-r=v) : s370 x=v := stepCert s369 2531 x q l r v h d a b c
theorem u371 (x q l r v : Nat) (h : ¬x<2539) (d : x/2539=q) (a : s370 x=l) (b : s370 q=r) (c : l-r=v) : s371 x=v := stepCert s370 2539 x q l r v h d a b c
theorem u372 (x q l r v : Nat) (h : ¬x<2543) (d : x/2543=q) (a : s371 x=l) (b : s371 q=r) (c : l-r=v) : s372 x=v := stepCert s371 2543 x q l r v h d a b c
theorem u373 (x q l r v : Nat) (h : ¬x<2549) (d : x/2549=q) (a : s372 x=l) (b : s372 q=r) (c : l-r=v) : s373 x=v := stepCert s372 2549 x q l r v h d a b c
theorem u374 (x q l r v : Nat) (h : ¬x<2551) (d : x/2551=q) (a : s373 x=l) (b : s373 q=r) (c : l-r=v) : s374 x=v := stepCert s373 2551 x q l r v h d a b c
theorem u375 (x q l r v : Nat) (h : ¬x<2557) (d : x/2557=q) (a : s374 x=l) (b : s374 q=r) (c : l-r=v) : s375 x=v := stepCert s374 2557 x q l r v h d a b c
theorem u376 (x q l r v : Nat) (h : ¬x<2579) (d : x/2579=q) (a : s375 x=l) (b : s375 q=r) (c : l-r=v) : s376 x=v := stepCert s375 2579 x q l r v h d a b c
theorem u377 (x q l r v : Nat) (h : ¬x<2591) (d : x/2591=q) (a : s376 x=l) (b : s376 q=r) (c : l-r=v) : s377 x=v := stepCert s376 2591 x q l r v h d a b c
theorem u378 (x q l r v : Nat) (h : ¬x<2593) (d : x/2593=q) (a : s377 x=l) (b : s377 q=r) (c : l-r=v) : s378 x=v := stepCert s377 2593 x q l r v h d a b c
theorem u379 (x q l r v : Nat) (h : ¬x<2609) (d : x/2609=q) (a : s378 x=l) (b : s378 q=r) (c : l-r=v) : s379 x=v := stepCert s378 2609 x q l r v h d a b c
theorem u380 (x q l r v : Nat) (h : ¬x<2617) (d : x/2617=q) (a : s379 x=l) (b : s379 q=r) (c : l-r=v) : s380 x=v := stepCert s379 2617 x q l r v h d a b c
theorem u381 (x q l r v : Nat) (h : ¬x<2621) (d : x/2621=q) (a : s380 x=l) (b : s380 q=r) (c : l-r=v) : s381 x=v := stepCert s380 2621 x q l r v h d a b c
theorem u382 (x q l r v : Nat) (h : ¬x<2633) (d : x/2633=q) (a : s381 x=l) (b : s381 q=r) (c : l-r=v) : s382 x=v := stepCert s381 2633 x q l r v h d a b c
theorem u383 (x q l r v : Nat) (h : ¬x<2647) (d : x/2647=q) (a : s382 x=l) (b : s382 q=r) (c : l-r=v) : s383 x=v := stepCert s382 2647 x q l r v h d a b c
theorem u384 (x q l r v : Nat) (h : ¬x<2657) (d : x/2657=q) (a : s383 x=l) (b : s383 q=r) (c : l-r=v) : s384 x=v := stepCert s383 2657 x q l r v h d a b c
theorem u385 (x q l r v : Nat) (h : ¬x<2659) (d : x/2659=q) (a : s384 x=l) (b : s384 q=r) (c : l-r=v) : s385 x=v := stepCert s384 2659 x q l r v h d a b c
theorem u386 (x q l r v : Nat) (h : ¬x<2663) (d : x/2663=q) (a : s385 x=l) (b : s385 q=r) (c : l-r=v) : s386 x=v := stepCert s385 2663 x q l r v h d a b c
theorem u387 (x q l r v : Nat) (h : ¬x<2671) (d : x/2671=q) (a : s386 x=l) (b : s386 q=r) (c : l-r=v) : s387 x=v := stepCert s386 2671 x q l r v h d a b c
theorem u388 (x q l r v : Nat) (h : ¬x<2677) (d : x/2677=q) (a : s387 x=l) (b : s387 q=r) (c : l-r=v) : s388 x=v := stepCert s387 2677 x q l r v h d a b c
theorem u389 (x q l r v : Nat) (h : ¬x<2683) (d : x/2683=q) (a : s388 x=l) (b : s388 q=r) (c : l-r=v) : s389 x=v := stepCert s388 2683 x q l r v h d a b c
theorem u390 (x q l r v : Nat) (h : ¬x<2687) (d : x/2687=q) (a : s389 x=l) (b : s389 q=r) (c : l-r=v) : s390 x=v := stepCert s389 2687 x q l r v h d a b c
theorem u391 (x q l r v : Nat) (h : ¬x<2689) (d : x/2689=q) (a : s390 x=l) (b : s390 q=r) (c : l-r=v) : s391 x=v := stepCert s390 2689 x q l r v h d a b c
theorem u392 (x q l r v : Nat) (h : ¬x<2693) (d : x/2693=q) (a : s391 x=l) (b : s391 q=r) (c : l-r=v) : s392 x=v := stepCert s391 2693 x q l r v h d a b c
theorem u393 (x q l r v : Nat) (h : ¬x<2699) (d : x/2699=q) (a : s392 x=l) (b : s392 q=r) (c : l-r=v) : s393 x=v := stepCert s392 2699 x q l r v h d a b c
theorem u394 (x q l r v : Nat) (h : ¬x<2707) (d : x/2707=q) (a : s393 x=l) (b : s393 q=r) (c : l-r=v) : s394 x=v := stepCert s393 2707 x q l r v h d a b c
theorem u395 (x q l r v : Nat) (h : ¬x<2711) (d : x/2711=q) (a : s394 x=l) (b : s394 q=r) (c : l-r=v) : s395 x=v := stepCert s394 2711 x q l r v h d a b c
theorem u396 (x q l r v : Nat) (h : ¬x<2713) (d : x/2713=q) (a : s395 x=l) (b : s395 q=r) (c : l-r=v) : s396 x=v := stepCert s395 2713 x q l r v h d a b c
theorem u397 (x q l r v : Nat) (h : ¬x<2719) (d : x/2719=q) (a : s396 x=l) (b : s396 q=r) (c : l-r=v) : s397 x=v := stepCert s396 2719 x q l r v h d a b c
theorem u398 (x q l r v : Nat) (h : ¬x<2729) (d : x/2729=q) (a : s397 x=l) (b : s397 q=r) (c : l-r=v) : s398 x=v := stepCert s397 2729 x q l r v h d a b c
theorem u399 (x q l r v : Nat) (h : ¬x<2731) (d : x/2731=q) (a : s398 x=l) (b : s398 q=r) (c : l-r=v) : s399 x=v := stepCert s398 2731 x q l r v h d a b c
theorem u400 (x q l r v : Nat) (h : ¬x<2741) (d : x/2741=q) (a : s399 x=l) (b : s399 q=r) (c : l-r=v) : s400 x=v := stepCert s399 2741 x q l r v h d a b c
theorem u401 (x q l r v : Nat) (h : ¬x<2749) (d : x/2749=q) (a : s400 x=l) (b : s400 q=r) (c : l-r=v) : s401 x=v := stepCert s400 2749 x q l r v h d a b c
theorem u402 (x q l r v : Nat) (h : ¬x<2753) (d : x/2753=q) (a : s401 x=l) (b : s401 q=r) (c : l-r=v) : s402 x=v := stepCert s401 2753 x q l r v h d a b c
theorem u403 (x q l r v : Nat) (h : ¬x<2767) (d : x/2767=q) (a : s402 x=l) (b : s402 q=r) (c : l-r=v) : s403 x=v := stepCert s402 2767 x q l r v h d a b c
theorem u404 (x q l r v : Nat) (h : ¬x<2777) (d : x/2777=q) (a : s403 x=l) (b : s403 q=r) (c : l-r=v) : s404 x=v := stepCert s403 2777 x q l r v h d a b c
theorem u405 (x q l r v : Nat) (h : ¬x<2789) (d : x/2789=q) (a : s404 x=l) (b : s404 q=r) (c : l-r=v) : s405 x=v := stepCert s404 2789 x q l r v h d a b c
theorem u406 (x q l r v : Nat) (h : ¬x<2791) (d : x/2791=q) (a : s405 x=l) (b : s405 q=r) (c : l-r=v) : s406 x=v := stepCert s405 2791 x q l r v h d a b c
theorem u407 (x q l r v : Nat) (h : ¬x<2797) (d : x/2797=q) (a : s406 x=l) (b : s406 q=r) (c : l-r=v) : s407 x=v := stepCert s406 2797 x q l r v h d a b c
theorem u408 (x q l r v : Nat) (h : ¬x<2801) (d : x/2801=q) (a : s407 x=l) (b : s407 q=r) (c : l-r=v) : s408 x=v := stepCert s407 2801 x q l r v h d a b c
theorem u409 (x q l r v : Nat) (h : ¬x<2803) (d : x/2803=q) (a : s408 x=l) (b : s408 q=r) (c : l-r=v) : s409 x=v := stepCert s408 2803 x q l r v h d a b c
theorem u410 (x q l r v : Nat) (h : ¬x<2819) (d : x/2819=q) (a : s409 x=l) (b : s409 q=r) (c : l-r=v) : s410 x=v := stepCert s409 2819 x q l r v h d a b c
theorem u411 (x q l r v : Nat) (h : ¬x<2833) (d : x/2833=q) (a : s410 x=l) (b : s410 q=r) (c : l-r=v) : s411 x=v := stepCert s410 2833 x q l r v h d a b c
theorem u412 (x q l r v : Nat) (h : ¬x<2837) (d : x/2837=q) (a : s411 x=l) (b : s411 q=r) (c : l-r=v) : s412 x=v := stepCert s411 2837 x q l r v h d a b c
theorem u413 (x q l r v : Nat) (h : ¬x<2843) (d : x/2843=q) (a : s412 x=l) (b : s412 q=r) (c : l-r=v) : s413 x=v := stepCert s412 2843 x q l r v h d a b c
theorem u414 (x q l r v : Nat) (h : ¬x<2851) (d : x/2851=q) (a : s413 x=l) (b : s413 q=r) (c : l-r=v) : s414 x=v := stepCert s413 2851 x q l r v h d a b c
theorem u415 (x q l r v : Nat) (h : ¬x<2857) (d : x/2857=q) (a : s414 x=l) (b : s414 q=r) (c : l-r=v) : s415 x=v := stepCert s414 2857 x q l r v h d a b c
theorem u416 (x q l r v : Nat) (h : ¬x<2861) (d : x/2861=q) (a : s415 x=l) (b : s415 q=r) (c : l-r=v) : s416 x=v := stepCert s415 2861 x q l r v h d a b c
theorem u417 (x q l r v : Nat) (h : ¬x<2879) (d : x/2879=q) (a : s416 x=l) (b : s416 q=r) (c : l-r=v) : s417 x=v := stepCert s416 2879 x q l r v h d a b c
theorem u418 (x q l r v : Nat) (h : ¬x<2887) (d : x/2887=q) (a : s417 x=l) (b : s417 q=r) (c : l-r=v) : s418 x=v := stepCert s417 2887 x q l r v h d a b c
theorem u419 (x q l r v : Nat) (h : ¬x<2897) (d : x/2897=q) (a : s418 x=l) (b : s418 q=r) (c : l-r=v) : s419 x=v := stepCert s418 2897 x q l r v h d a b c
theorem u420 (x q l r v : Nat) (h : ¬x<2903) (d : x/2903=q) (a : s419 x=l) (b : s419 q=r) (c : l-r=v) : s420 x=v := stepCert s419 2903 x q l r v h d a b c
theorem u421 (x q l r v : Nat) (h : ¬x<2909) (d : x/2909=q) (a : s420 x=l) (b : s420 q=r) (c : l-r=v) : s421 x=v := stepCert s420 2909 x q l r v h d a b c
theorem u422 (x q l r v : Nat) (h : ¬x<2917) (d : x/2917=q) (a : s421 x=l) (b : s421 q=r) (c : l-r=v) : s422 x=v := stepCert s421 2917 x q l r v h d a b c
theorem u423 (x q l r v : Nat) (h : ¬x<2927) (d : x/2927=q) (a : s422 x=l) (b : s422 q=r) (c : l-r=v) : s423 x=v := stepCert s422 2927 x q l r v h d a b c
theorem u424 (x q l r v : Nat) (h : ¬x<2939) (d : x/2939=q) (a : s423 x=l) (b : s423 q=r) (c : l-r=v) : s424 x=v := stepCert s423 2939 x q l r v h d a b c
theorem u425 (x q l r v : Nat) (h : ¬x<2953) (d : x/2953=q) (a : s424 x=l) (b : s424 q=r) (c : l-r=v) : s425 x=v := stepCert s424 2953 x q l r v h d a b c
theorem u426 (x q l r v : Nat) (h : ¬x<2957) (d : x/2957=q) (a : s425 x=l) (b : s425 q=r) (c : l-r=v) : s426 x=v := stepCert s425 2957 x q l r v h d a b c
theorem u427 (x q l r v : Nat) (h : ¬x<2963) (d : x/2963=q) (a : s426 x=l) (b : s426 q=r) (c : l-r=v) : s427 x=v := stepCert s426 2963 x q l r v h d a b c
theorem u428 (x q l r v : Nat) (h : ¬x<2969) (d : x/2969=q) (a : s427 x=l) (b : s427 q=r) (c : l-r=v) : s428 x=v := stepCert s427 2969 x q l r v h d a b c
theorem u429 (x q l r v : Nat) (h : ¬x<2971) (d : x/2971=q) (a : s428 x=l) (b : s428 q=r) (c : l-r=v) : s429 x=v := stepCert s428 2971 x q l r v h d a b c
theorem u430 (x q l r v : Nat) (h : ¬x<2999) (d : x/2999=q) (a : s429 x=l) (b : s429 q=r) (c : l-r=v) : s430 x=v := stepCert s429 2999 x q l r v h d a b c
theorem u431 (x q l r v : Nat) (h : ¬x<3001) (d : x/3001=q) (a : s430 x=l) (b : s430 q=r) (c : l-r=v) : s431 x=v := stepCert s430 3001 x q l r v h d a b c
theorem u432 (x q l r v : Nat) (h : ¬x<3011) (d : x/3011=q) (a : s431 x=l) (b : s431 q=r) (c : l-r=v) : s432 x=v := stepCert s431 3011 x q l r v h d a b c
theorem u433 (x q l r v : Nat) (h : ¬x<3019) (d : x/3019=q) (a : s432 x=l) (b : s432 q=r) (c : l-r=v) : s433 x=v := stepCert s432 3019 x q l r v h d a b c
theorem u434 (x q l r v : Nat) (h : ¬x<3023) (d : x/3023=q) (a : s433 x=l) (b : s433 q=r) (c : l-r=v) : s434 x=v := stepCert s433 3023 x q l r v h d a b c
theorem u435 (x q l r v : Nat) (h : ¬x<3037) (d : x/3037=q) (a : s434 x=l) (b : s434 q=r) (c : l-r=v) : s435 x=v := stepCert s434 3037 x q l r v h d a b c
theorem u436 (x q l r v : Nat) (h : ¬x<3041) (d : x/3041=q) (a : s435 x=l) (b : s435 q=r) (c : l-r=v) : s436 x=v := stepCert s435 3041 x q l r v h d a b c
theorem u437 (x q l r v : Nat) (h : ¬x<3049) (d : x/3049=q) (a : s436 x=l) (b : s436 q=r) (c : l-r=v) : s437 x=v := stepCert s436 3049 x q l r v h d a b c
theorem u438 (x q l r v : Nat) (h : ¬x<3061) (d : x/3061=q) (a : s437 x=l) (b : s437 q=r) (c : l-r=v) : s438 x=v := stepCert s437 3061 x q l r v h d a b c
theorem u439 (x q l r v : Nat) (h : ¬x<3067) (d : x/3067=q) (a : s438 x=l) (b : s438 q=r) (c : l-r=v) : s439 x=v := stepCert s438 3067 x q l r v h d a b c
theorem u440 (x q l r v : Nat) (h : ¬x<3079) (d : x/3079=q) (a : s439 x=l) (b : s439 q=r) (c : l-r=v) : s440 x=v := stepCert s439 3079 x q l r v h d a b c
theorem u441 (x q l r v : Nat) (h : ¬x<3083) (d : x/3083=q) (a : s440 x=l) (b : s440 q=r) (c : l-r=v) : s441 x=v := stepCert s440 3083 x q l r v h d a b c
theorem u442 (x q l r v : Nat) (h : ¬x<3089) (d : x/3089=q) (a : s441 x=l) (b : s441 q=r) (c : l-r=v) : s442 x=v := stepCert s441 3089 x q l r v h d a b c
theorem u443 (x q l r v : Nat) (h : ¬x<3109) (d : x/3109=q) (a : s442 x=l) (b : s442 q=r) (c : l-r=v) : s443 x=v := stepCert s442 3109 x q l r v h d a b c
theorem u444 (x q l r v : Nat) (h : ¬x<3119) (d : x/3119=q) (a : s443 x=l) (b : s443 q=r) (c : l-r=v) : s444 x=v := stepCert s443 3119 x q l r v h d a b c
theorem u445 (x q l r v : Nat) (h : ¬x<3121) (d : x/3121=q) (a : s444 x=l) (b : s444 q=r) (c : l-r=v) : s445 x=v := stepCert s444 3121 x q l r v h d a b c
theorem u446 (x q l r v : Nat) (h : ¬x<3137) (d : x/3137=q) (a : s445 x=l) (b : s445 q=r) (c : l-r=v) : s446 x=v := stepCert s445 3137 x q l r v h d a b c
theorem u447 (x q l r v : Nat) (h : ¬x<3163) (d : x/3163=q) (a : s446 x=l) (b : s446 q=r) (c : l-r=v) : s447 x=v := stepCert s446 3163 x q l r v h d a b c
theorem u448 (x q l r v : Nat) (h : ¬x<3167) (d : x/3167=q) (a : s447 x=l) (b : s447 q=r) (c : l-r=v) : s448 x=v := stepCert s447 3167 x q l r v h d a b c
theorem u449 (x q l r v : Nat) (h : ¬x<3169) (d : x/3169=q) (a : s448 x=l) (b : s448 q=r) (c : l-r=v) : s449 x=v := stepCert s448 3169 x q l r v h d a b c
theorem u450 (x q l r v : Nat) (h : ¬x<3181) (d : x/3181=q) (a : s449 x=l) (b : s449 q=r) (c : l-r=v) : s450 x=v := stepCert s449 3181 x q l r v h d a b c
theorem u451 (x q l r v : Nat) (h : ¬x<3187) (d : x/3187=q) (a : s450 x=l) (b : s450 q=r) (c : l-r=v) : s451 x=v := stepCert s450 3187 x q l r v h d a b c
theorem u452 (x q l r v : Nat) (h : ¬x<3191) (d : x/3191=q) (a : s451 x=l) (b : s451 q=r) (c : l-r=v) : s452 x=v := stepCert s451 3191 x q l r v h d a b c
theorem u453 (x q l r v : Nat) (h : ¬x<3203) (d : x/3203=q) (a : s452 x=l) (b : s452 q=r) (c : l-r=v) : s453 x=v := stepCert s452 3203 x q l r v h d a b c
theorem u454 (x q l r v : Nat) (h : ¬x<3209) (d : x/3209=q) (a : s453 x=l) (b : s453 q=r) (c : l-r=v) : s454 x=v := stepCert s453 3209 x q l r v h d a b c
theorem u455 (x q l r v : Nat) (h : ¬x<3217) (d : x/3217=q) (a : s454 x=l) (b : s454 q=r) (c : l-r=v) : s455 x=v := stepCert s454 3217 x q l r v h d a b c
theorem u456 (x q l r v : Nat) (h : ¬x<3221) (d : x/3221=q) (a : s455 x=l) (b : s455 q=r) (c : l-r=v) : s456 x=v := stepCert s455 3221 x q l r v h d a b c
theorem u457 (x q l r v : Nat) (h : ¬x<3229) (d : x/3229=q) (a : s456 x=l) (b : s456 q=r) (c : l-r=v) : s457 x=v := stepCert s456 3229 x q l r v h d a b c
theorem u458 (x q l r v : Nat) (h : ¬x<3251) (d : x/3251=q) (a : s457 x=l) (b : s457 q=r) (c : l-r=v) : s458 x=v := stepCert s457 3251 x q l r v h d a b c
theorem u459 (x q l r v : Nat) (h : ¬x<3253) (d : x/3253=q) (a : s458 x=l) (b : s458 q=r) (c : l-r=v) : s459 x=v := stepCert s458 3253 x q l r v h d a b c
theorem u460 (x q l r v : Nat) (h : ¬x<3257) (d : x/3257=q) (a : s459 x=l) (b : s459 q=r) (c : l-r=v) : s460 x=v := stepCert s459 3257 x q l r v h d a b c
theorem u461 (x q l r v : Nat) (h : ¬x<3259) (d : x/3259=q) (a : s460 x=l) (b : s460 q=r) (c : l-r=v) : s461 x=v := stepCert s460 3259 x q l r v h d a b c
theorem u462 (x q l r v : Nat) (h : ¬x<3271) (d : x/3271=q) (a : s461 x=l) (b : s461 q=r) (c : l-r=v) : s462 x=v := stepCert s461 3271 x q l r v h d a b c
theorem u463 (x q l r v : Nat) (h : ¬x<3299) (d : x/3299=q) (a : s462 x=l) (b : s462 q=r) (c : l-r=v) : s463 x=v := stepCert s462 3299 x q l r v h d a b c
theorem u464 (x q l r v : Nat) (h : ¬x<3301) (d : x/3301=q) (a : s463 x=l) (b : s463 q=r) (c : l-r=v) : s464 x=v := stepCert s463 3301 x q l r v h d a b c
theorem u465 (x q l r v : Nat) (h : ¬x<3307) (d : x/3307=q) (a : s464 x=l) (b : s464 q=r) (c : l-r=v) : s465 x=v := stepCert s464 3307 x q l r v h d a b c
theorem u466 (x q l r v : Nat) (h : ¬x<3313) (d : x/3313=q) (a : s465 x=l) (b : s465 q=r) (c : l-r=v) : s466 x=v := stepCert s465 3313 x q l r v h d a b c
theorem u467 (x q l r v : Nat) (h : ¬x<3319) (d : x/3319=q) (a : s466 x=l) (b : s466 q=r) (c : l-r=v) : s467 x=v := stepCert s466 3319 x q l r v h d a b c
theorem u468 (x q l r v : Nat) (h : ¬x<3323) (d : x/3323=q) (a : s467 x=l) (b : s467 q=r) (c : l-r=v) : s468 x=v := stepCert s467 3323 x q l r v h d a b c
theorem u469 (x q l r v : Nat) (h : ¬x<3329) (d : x/3329=q) (a : s468 x=l) (b : s468 q=r) (c : l-r=v) : s469 x=v := stepCert s468 3329 x q l r v h d a b c
theorem u470 (x q l r v : Nat) (h : ¬x<3331) (d : x/3331=q) (a : s469 x=l) (b : s469 q=r) (c : l-r=v) : s470 x=v := stepCert s469 3331 x q l r v h d a b c
theorem u471 (x q l r v : Nat) (h : ¬x<3343) (d : x/3343=q) (a : s470 x=l) (b : s470 q=r) (c : l-r=v) : s471 x=v := stepCert s470 3343 x q l r v h d a b c
theorem u472 (x q l r v : Nat) (h : ¬x<3347) (d : x/3347=q) (a : s471 x=l) (b : s471 q=r) (c : l-r=v) : s472 x=v := stepCert s471 3347 x q l r v h d a b c
theorem u473 (x q l r v : Nat) (h : ¬x<3359) (d : x/3359=q) (a : s472 x=l) (b : s472 q=r) (c : l-r=v) : s473 x=v := stepCert s472 3359 x q l r v h d a b c
theorem u474 (x q l r v : Nat) (h : ¬x<3361) (d : x/3361=q) (a : s473 x=l) (b : s473 q=r) (c : l-r=v) : s474 x=v := stepCert s473 3361 x q l r v h d a b c
theorem u475 (x q l r v : Nat) (h : ¬x<3371) (d : x/3371=q) (a : s474 x=l) (b : s474 q=r) (c : l-r=v) : s475 x=v := stepCert s474 3371 x q l r v h d a b c
theorem u476 (x q l r v : Nat) (h : ¬x<3373) (d : x/3373=q) (a : s475 x=l) (b : s475 q=r) (c : l-r=v) : s476 x=v := stepCert s475 3373 x q l r v h d a b c
theorem u477 (x q l r v : Nat) (h : ¬x<3389) (d : x/3389=q) (a : s476 x=l) (b : s476 q=r) (c : l-r=v) : s477 x=v := stepCert s476 3389 x q l r v h d a b c
theorem u478 (x q l r v : Nat) (h : ¬x<3391) (d : x/3391=q) (a : s477 x=l) (b : s477 q=r) (c : l-r=v) : s478 x=v := stepCert s477 3391 x q l r v h d a b c
theorem u479 (x q l r v : Nat) (h : ¬x<3407) (d : x/3407=q) (a : s478 x=l) (b : s478 q=r) (c : l-r=v) : s479 x=v := stepCert s478 3407 x q l r v h d a b c
theorem u480 (x q l r v : Nat) (h : ¬x<3413) (d : x/3413=q) (a : s479 x=l) (b : s479 q=r) (c : l-r=v) : s480 x=v := stepCert s479 3413 x q l r v h d a b c
theorem u481 (x q l r v : Nat) (h : ¬x<3433) (d : x/3433=q) (a : s480 x=l) (b : s480 q=r) (c : l-r=v) : s481 x=v := stepCert s480 3433 x q l r v h d a b c
theorem u482 (x q l r v : Nat) (h : ¬x<3449) (d : x/3449=q) (a : s481 x=l) (b : s481 q=r) (c : l-r=v) : s482 x=v := stepCert s481 3449 x q l r v h d a b c
theorem u483 (x q l r v : Nat) (h : ¬x<3457) (d : x/3457=q) (a : s482 x=l) (b : s482 q=r) (c : l-r=v) : s483 x=v := stepCert s482 3457 x q l r v h d a b c
theorem u484 (x q l r v : Nat) (h : ¬x<3461) (d : x/3461=q) (a : s483 x=l) (b : s483 q=r) (c : l-r=v) : s484 x=v := stepCert s483 3461 x q l r v h d a b c
theorem u485 (x q l r v : Nat) (h : ¬x<3463) (d : x/3463=q) (a : s484 x=l) (b : s484 q=r) (c : l-r=v) : s485 x=v := stepCert s484 3463 x q l r v h d a b c
theorem u486 (x q l r v : Nat) (h : ¬x<3467) (d : x/3467=q) (a : s485 x=l) (b : s485 q=r) (c : l-r=v) : s486 x=v := stepCert s485 3467 x q l r v h d a b c
theorem u487 (x q l r v : Nat) (h : ¬x<3469) (d : x/3469=q) (a : s486 x=l) (b : s486 q=r) (c : l-r=v) : s487 x=v := stepCert s486 3469 x q l r v h d a b c
theorem u488 (x q l r v : Nat) (h : ¬x<3491) (d : x/3491=q) (a : s487 x=l) (b : s487 q=r) (c : l-r=v) : s488 x=v := stepCert s487 3491 x q l r v h d a b c
theorem u489 (x q l r v : Nat) (h : ¬x<3499) (d : x/3499=q) (a : s488 x=l) (b : s488 q=r) (c : l-r=v) : s489 x=v := stepCert s488 3499 x q l r v h d a b c
theorem u490 (x q l r v : Nat) (h : ¬x<3511) (d : x/3511=q) (a : s489 x=l) (b : s489 q=r) (c : l-r=v) : s490 x=v := stepCert s489 3511 x q l r v h d a b c
theorem u491 (x q l r v : Nat) (h : ¬x<3517) (d : x/3517=q) (a : s490 x=l) (b : s490 q=r) (c : l-r=v) : s491 x=v := stepCert s490 3517 x q l r v h d a b c
theorem u492 (x q l r v : Nat) (h : ¬x<3527) (d : x/3527=q) (a : s491 x=l) (b : s491 q=r) (c : l-r=v) : s492 x=v := stepCert s491 3527 x q l r v h d a b c
theorem u493 (x q l r v : Nat) (h : ¬x<3529) (d : x/3529=q) (a : s492 x=l) (b : s492 q=r) (c : l-r=v) : s493 x=v := stepCert s492 3529 x q l r v h d a b c
theorem u494 (x q l r v : Nat) (h : ¬x<3533) (d : x/3533=q) (a : s493 x=l) (b : s493 q=r) (c : l-r=v) : s494 x=v := stepCert s493 3533 x q l r v h d a b c
theorem u495 (x q l r v : Nat) (h : ¬x<3539) (d : x/3539=q) (a : s494 x=l) (b : s494 q=r) (c : l-r=v) : s495 x=v := stepCert s494 3539 x q l r v h d a b c
theorem u496 (x q l r v : Nat) (h : ¬x<3541) (d : x/3541=q) (a : s495 x=l) (b : s495 q=r) (c : l-r=v) : s496 x=v := stepCert s495 3541 x q l r v h d a b c
theorem u497 (x q l r v : Nat) (h : ¬x<3547) (d : x/3547=q) (a : s496 x=l) (b : s496 q=r) (c : l-r=v) : s497 x=v := stepCert s496 3547 x q l r v h d a b c
theorem u498 (x q l r v : Nat) (h : ¬x<3557) (d : x/3557=q) (a : s497 x=l) (b : s497 q=r) (c : l-r=v) : s498 x=v := stepCert s497 3557 x q l r v h d a b c
theorem u499 (x q l r v : Nat) (h : ¬x<3559) (d : x/3559=q) (a : s498 x=l) (b : s498 q=r) (c : l-r=v) : s499 x=v := stepCert s498 3559 x q l r v h d a b c
theorem u500 (x q l r v : Nat) (h : ¬x<3571) (d : x/3571=q) (a : s499 x=l) (b : s499 q=r) (c : l-r=v) : s500 x=v := stepCert s499 3571 x q l r v h d a b c
theorem u501 (x q l r v : Nat) (h : ¬x<3581) (d : x/3581=q) (a : s500 x=l) (b : s500 q=r) (c : l-r=v) : s501 x=v := stepCert s500 3581 x q l r v h d a b c
theorem u502 (x q l r v : Nat) (h : ¬x<3583) (d : x/3583=q) (a : s501 x=l) (b : s501 q=r) (c : l-r=v) : s502 x=v := stepCert s501 3583 x q l r v h d a b c
theorem u503 (x q l r v : Nat) (h : ¬x<3593) (d : x/3593=q) (a : s502 x=l) (b : s502 q=r) (c : l-r=v) : s503 x=v := stepCert s502 3593 x q l r v h d a b c
theorem u504 (x q l r v : Nat) (h : ¬x<3607) (d : x/3607=q) (a : s503 x=l) (b : s503 q=r) (c : l-r=v) : s504 x=v := stepCert s503 3607 x q l r v h d a b c
theorem u505 (x q l r v : Nat) (h : ¬x<3613) (d : x/3613=q) (a : s504 x=l) (b : s504 q=r) (c : l-r=v) : s505 x=v := stepCert s504 3613 x q l r v h d a b c
theorem u506 (x q l r v : Nat) (h : ¬x<3617) (d : x/3617=q) (a : s505 x=l) (b : s505 q=r) (c : l-r=v) : s506 x=v := stepCert s505 3617 x q l r v h d a b c
theorem u507 (x q l r v : Nat) (h : ¬x<3623) (d : x/3623=q) (a : s506 x=l) (b : s506 q=r) (c : l-r=v) : s507 x=v := stepCert s506 3623 x q l r v h d a b c
theorem u508 (x q l r v : Nat) (h : ¬x<3631) (d : x/3631=q) (a : s507 x=l) (b : s507 q=r) (c : l-r=v) : s508 x=v := stepCert s507 3631 x q l r v h d a b c
theorem u509 (x q l r v : Nat) (h : ¬x<3637) (d : x/3637=q) (a : s508 x=l) (b : s508 q=r) (c : l-r=v) : s509 x=v := stepCert s508 3637 x q l r v h d a b c
theorem u510 (x q l r v : Nat) (h : ¬x<3643) (d : x/3643=q) (a : s509 x=l) (b : s509 q=r) (c : l-r=v) : s510 x=v := stepCert s509 3643 x q l r v h d a b c
theorem u511 (x q l r v : Nat) (h : ¬x<3659) (d : x/3659=q) (a : s510 x=l) (b : s510 q=r) (c : l-r=v) : s511 x=v := stepCert s510 3659 x q l r v h d a b c
theorem u512 (x q l r v : Nat) (h : ¬x<3671) (d : x/3671=q) (a : s511 x=l) (b : s511 q=r) (c : l-r=v) : s512 x=v := stepCert s511 3671 x q l r v h d a b c
theorem u513 (x q l r v : Nat) (h : ¬x<3673) (d : x/3673=q) (a : s512 x=l) (b : s512 q=r) (c : l-r=v) : s513 x=v := stepCert s512 3673 x q l r v h d a b c
theorem u514 (x q l r v : Nat) (h : ¬x<3677) (d : x/3677=q) (a : s513 x=l) (b : s513 q=r) (c : l-r=v) : s514 x=v := stepCert s513 3677 x q l r v h d a b c
theorem u515 (x q l r v : Nat) (h : ¬x<3691) (d : x/3691=q) (a : s514 x=l) (b : s514 q=r) (c : l-r=v) : s515 x=v := stepCert s514 3691 x q l r v h d a b c
theorem u516 (x q l r v : Nat) (h : ¬x<3697) (d : x/3697=q) (a : s515 x=l) (b : s515 q=r) (c : l-r=v) : s516 x=v := stepCert s515 3697 x q l r v h d a b c
theorem u517 (x q l r v : Nat) (h : ¬x<3701) (d : x/3701=q) (a : s516 x=l) (b : s516 q=r) (c : l-r=v) : s517 x=v := stepCert s516 3701 x q l r v h d a b c
theorem u518 (x q l r v : Nat) (h : ¬x<3709) (d : x/3709=q) (a : s517 x=l) (b : s517 q=r) (c : l-r=v) : s518 x=v := stepCert s517 3709 x q l r v h d a b c
theorem u519 (x q l r v : Nat) (h : ¬x<3719) (d : x/3719=q) (a : s518 x=l) (b : s518 q=r) (c : l-r=v) : s519 x=v := stepCert s518 3719 x q l r v h d a b c
theorem u520 (x q l r v : Nat) (h : ¬x<3727) (d : x/3727=q) (a : s519 x=l) (b : s519 q=r) (c : l-r=v) : s520 x=v := stepCert s519 3727 x q l r v h d a b c
theorem u521 (x q l r v : Nat) (h : ¬x<3733) (d : x/3733=q) (a : s520 x=l) (b : s520 q=r) (c : l-r=v) : s521 x=v := stepCert s520 3733 x q l r v h d a b c
theorem u522 (x q l r v : Nat) (h : ¬x<3739) (d : x/3739=q) (a : s521 x=l) (b : s521 q=r) (c : l-r=v) : s522 x=v := stepCert s521 3739 x q l r v h d a b c
theorem u523 (x q l r v : Nat) (h : ¬x<3761) (d : x/3761=q) (a : s522 x=l) (b : s522 q=r) (c : l-r=v) : s523 x=v := stepCert s522 3761 x q l r v h d a b c
theorem u524 (x q l r v : Nat) (h : ¬x<3767) (d : x/3767=q) (a : s523 x=l) (b : s523 q=r) (c : l-r=v) : s524 x=v := stepCert s523 3767 x q l r v h d a b c
theorem u525 (x q l r v : Nat) (h : ¬x<3769) (d : x/3769=q) (a : s524 x=l) (b : s524 q=r) (c : l-r=v) : s525 x=v := stepCert s524 3769 x q l r v h d a b c
theorem u526 (x q l r v : Nat) (h : ¬x<3779) (d : x/3779=q) (a : s525 x=l) (b : s525 q=r) (c : l-r=v) : s526 x=v := stepCert s525 3779 x q l r v h d a b c
theorem u527 (x q l r v : Nat) (h : ¬x<3793) (d : x/3793=q) (a : s526 x=l) (b : s526 q=r) (c : l-r=v) : s527 x=v := stepCert s526 3793 x q l r v h d a b c
theorem u528 (x q l r v : Nat) (h : ¬x<3797) (d : x/3797=q) (a : s527 x=l) (b : s527 q=r) (c : l-r=v) : s528 x=v := stepCert s527 3797 x q l r v h d a b c
theorem u529 (x q l r v : Nat) (h : ¬x<3803) (d : x/3803=q) (a : s528 x=l) (b : s528 q=r) (c : l-r=v) : s529 x=v := stepCert s528 3803 x q l r v h d a b c
theorem u530 (x q l r v : Nat) (h : ¬x<3821) (d : x/3821=q) (a : s529 x=l) (b : s529 q=r) (c : l-r=v) : s530 x=v := stepCert s529 3821 x q l r v h d a b c
theorem u531 (x q l r v : Nat) (h : ¬x<3823) (d : x/3823=q) (a : s530 x=l) (b : s530 q=r) (c : l-r=v) : s531 x=v := stepCert s530 3823 x q l r v h d a b c
theorem u532 (x q l r v : Nat) (h : ¬x<3833) (d : x/3833=q) (a : s531 x=l) (b : s531 q=r) (c : l-r=v) : s532 x=v := stepCert s531 3833 x q l r v h d a b c
theorem u533 (x q l r v : Nat) (h : ¬x<3847) (d : x/3847=q) (a : s532 x=l) (b : s532 q=r) (c : l-r=v) : s533 x=v := stepCert s532 3847 x q l r v h d a b c
theorem u534 (x q l r v : Nat) (h : ¬x<3851) (d : x/3851=q) (a : s533 x=l) (b : s533 q=r) (c : l-r=v) : s534 x=v := stepCert s533 3851 x q l r v h d a b c
theorem u535 (x q l r v : Nat) (h : ¬x<3853) (d : x/3853=q) (a : s534 x=l) (b : s534 q=r) (c : l-r=v) : s535 x=v := stepCert s534 3853 x q l r v h d a b c
theorem u536 (x q l r v : Nat) (h : ¬x<3863) (d : x/3863=q) (a : s535 x=l) (b : s535 q=r) (c : l-r=v) : s536 x=v := stepCert s535 3863 x q l r v h d a b c
theorem u537 (x q l r v : Nat) (h : ¬x<3877) (d : x/3877=q) (a : s536 x=l) (b : s536 q=r) (c : l-r=v) : s537 x=v := stepCert s536 3877 x q l r v h d a b c
theorem u538 (x q l r v : Nat) (h : ¬x<3881) (d : x/3881=q) (a : s537 x=l) (b : s537 q=r) (c : l-r=v) : s538 x=v := stepCert s537 3881 x q l r v h d a b c
theorem u539 (x q l r v : Nat) (h : ¬x<3889) (d : x/3889=q) (a : s538 x=l) (b : s538 q=r) (c : l-r=v) : s539 x=v := stepCert s538 3889 x q l r v h d a b c
theorem u540 (x q l r v : Nat) (h : ¬x<3907) (d : x/3907=q) (a : s539 x=l) (b : s539 q=r) (c : l-r=v) : s540 x=v := stepCert s539 3907 x q l r v h d a b c
theorem u541 (x q l r v : Nat) (h : ¬x<3911) (d : x/3911=q) (a : s540 x=l) (b : s540 q=r) (c : l-r=v) : s541 x=v := stepCert s540 3911 x q l r v h d a b c
theorem u542 (x q l r v : Nat) (h : ¬x<3917) (d : x/3917=q) (a : s541 x=l) (b : s541 q=r) (c : l-r=v) : s542 x=v := stepCert s541 3917 x q l r v h d a b c
theorem u543 (x q l r v : Nat) (h : ¬x<3919) (d : x/3919=q) (a : s542 x=l) (b : s542 q=r) (c : l-r=v) : s543 x=v := stepCert s542 3919 x q l r v h d a b c
theorem u544 (x q l r v : Nat) (h : ¬x<3923) (d : x/3923=q) (a : s543 x=l) (b : s543 q=r) (c : l-r=v) : s544 x=v := stepCert s543 3923 x q l r v h d a b c
theorem u545 (x q l r v : Nat) (h : ¬x<3929) (d : x/3929=q) (a : s544 x=l) (b : s544 q=r) (c : l-r=v) : s545 x=v := stepCert s544 3929 x q l r v h d a b c
theorem u546 (x q l r v : Nat) (h : ¬x<3931) (d : x/3931=q) (a : s545 x=l) (b : s545 q=r) (c : l-r=v) : s546 x=v := stepCert s545 3931 x q l r v h d a b c
theorem u547 (x q l r v : Nat) (h : ¬x<3943) (d : x/3943=q) (a : s546 x=l) (b : s546 q=r) (c : l-r=v) : s547 x=v := stepCert s546 3943 x q l r v h d a b c
theorem u548 (x q l r v : Nat) (h : ¬x<3947) (d : x/3947=q) (a : s547 x=l) (b : s547 q=r) (c : l-r=v) : s548 x=v := stepCert s547 3947 x q l r v h d a b c
theorem u549 (x q l r v : Nat) (h : ¬x<3967) (d : x/3967=q) (a : s548 x=l) (b : s548 q=r) (c : l-r=v) : s549 x=v := stepCert s548 3967 x q l r v h d a b c
theorem u550 (x q l r v : Nat) (h : ¬x<3989) (d : x/3989=q) (a : s549 x=l) (b : s549 q=r) (c : l-r=v) : s550 x=v := stepCert s549 3989 x q l r v h d a b c
theorem u551 (x q l r v : Nat) (h : ¬x<4001) (d : x/4001=q) (a : s550 x=l) (b : s550 q=r) (c : l-r=v) : s551 x=v := stepCert s550 4001 x q l r v h d a b c
theorem u552 (x q l r v : Nat) (h : ¬x<4003) (d : x/4003=q) (a : s551 x=l) (b : s551 q=r) (c : l-r=v) : s552 x=v := stepCert s551 4003 x q l r v h d a b c
theorem u553 (x q l r v : Nat) (h : ¬x<4007) (d : x/4007=q) (a : s552 x=l) (b : s552 q=r) (c : l-r=v) : s553 x=v := stepCert s552 4007 x q l r v h d a b c
theorem u554 (x q l r v : Nat) (h : ¬x<4013) (d : x/4013=q) (a : s553 x=l) (b : s553 q=r) (c : l-r=v) : s554 x=v := stepCert s553 4013 x q l r v h d a b c
theorem u555 (x q l r v : Nat) (h : ¬x<4019) (d : x/4019=q) (a : s554 x=l) (b : s554 q=r) (c : l-r=v) : s555 x=v := stepCert s554 4019 x q l r v h d a b c
theorem u556 (x q l r v : Nat) (h : ¬x<4021) (d : x/4021=q) (a : s555 x=l) (b : s555 q=r) (c : l-r=v) : s556 x=v := stepCert s555 4021 x q l r v h d a b c
theorem u557 (x q l r v : Nat) (h : ¬x<4027) (d : x/4027=q) (a : s556 x=l) (b : s556 q=r) (c : l-r=v) : s557 x=v := stepCert s556 4027 x q l r v h d a b c
theorem u558 (x q l r v : Nat) (h : ¬x<4049) (d : x/4049=q) (a : s557 x=l) (b : s557 q=r) (c : l-r=v) : s558 x=v := stepCert s557 4049 x q l r v h d a b c
theorem u559 (x q l r v : Nat) (h : ¬x<4051) (d : x/4051=q) (a : s558 x=l) (b : s558 q=r) (c : l-r=v) : s559 x=v := stepCert s558 4051 x q l r v h d a b c
theorem u560 (x q l r v : Nat) (h : ¬x<4057) (d : x/4057=q) (a : s559 x=l) (b : s559 q=r) (c : l-r=v) : s560 x=v := stepCert s559 4057 x q l r v h d a b c
theorem u561 (x q l r v : Nat) (h : ¬x<4073) (d : x/4073=q) (a : s560 x=l) (b : s560 q=r) (c : l-r=v) : s561 x=v := stepCert s560 4073 x q l r v h d a b c
theorem u562 (x q l r v : Nat) (h : ¬x<4079) (d : x/4079=q) (a : s561 x=l) (b : s561 q=r) (c : l-r=v) : s562 x=v := stepCert s561 4079 x q l r v h d a b c
theorem u563 (x q l r v : Nat) (h : ¬x<4091) (d : x/4091=q) (a : s562 x=l) (b : s562 q=r) (c : l-r=v) : s563 x=v := stepCert s562 4091 x q l r v h d a b c
theorem u564 (x q l r v : Nat) (h : ¬x<4093) (d : x/4093=q) (a : s563 x=l) (b : s563 q=r) (c : l-r=v) : s564 x=v := stepCert s563 4093 x q l r v h d a b c
theorem u565 (x q l r v : Nat) (h : ¬x<4099) (d : x/4099=q) (a : s564 x=l) (b : s564 q=r) (c : l-r=v) : s565 x=v := stepCert s564 4099 x q l r v h d a b c
theorem u566 (x q l r v : Nat) (h : ¬x<4111) (d : x/4111=q) (a : s565 x=l) (b : s565 q=r) (c : l-r=v) : s566 x=v := stepCert s565 4111 x q l r v h d a b c
theorem u567 (x q l r v : Nat) (h : ¬x<4127) (d : x/4127=q) (a : s566 x=l) (b : s566 q=r) (c : l-r=v) : s567 x=v := stepCert s566 4127 x q l r v h d a b c
theorem u568 (x q l r v : Nat) (h : ¬x<4129) (d : x/4129=q) (a : s567 x=l) (b : s567 q=r) (c : l-r=v) : s568 x=v := stepCert s567 4129 x q l r v h d a b c
theorem u569 (x q l r v : Nat) (h : ¬x<4133) (d : x/4133=q) (a : s568 x=l) (b : s568 q=r) (c : l-r=v) : s569 x=v := stepCert s568 4133 x q l r v h d a b c
theorem u570 (x q l r v : Nat) (h : ¬x<4139) (d : x/4139=q) (a : s569 x=l) (b : s569 q=r) (c : l-r=v) : s570 x=v := stepCert s569 4139 x q l r v h d a b c
theorem u571 (x q l r v : Nat) (h : ¬x<4153) (d : x/4153=q) (a : s570 x=l) (b : s570 q=r) (c : l-r=v) : s571 x=v := stepCert s570 4153 x q l r v h d a b c
theorem u572 (x q l r v : Nat) (h : ¬x<4157) (d : x/4157=q) (a : s571 x=l) (b : s571 q=r) (c : l-r=v) : s572 x=v := stepCert s571 4157 x q l r v h d a b c
theorem u573 (x q l r v : Nat) (h : ¬x<4159) (d : x/4159=q) (a : s572 x=l) (b : s572 q=r) (c : l-r=v) : s573 x=v := stepCert s572 4159 x q l r v h d a b c
theorem u574 (x q l r v : Nat) (h : ¬x<4177) (d : x/4177=q) (a : s573 x=l) (b : s573 q=r) (c : l-r=v) : s574 x=v := stepCert s573 4177 x q l r v h d a b c
theorem u575 (x q l r v : Nat) (h : ¬x<4201) (d : x/4201=q) (a : s574 x=l) (b : s574 q=r) (c : l-r=v) : s575 x=v := stepCert s574 4201 x q l r v h d a b c
theorem u576 (x q l r v : Nat) (h : ¬x<4211) (d : x/4211=q) (a : s575 x=l) (b : s575 q=r) (c : l-r=v) : s576 x=v := stepCert s575 4211 x q l r v h d a b c
theorem u577 (x q l r v : Nat) (h : ¬x<4217) (d : x/4217=q) (a : s576 x=l) (b : s576 q=r) (c : l-r=v) : s577 x=v := stepCert s576 4217 x q l r v h d a b c
theorem u578 (x q l r v : Nat) (h : ¬x<4219) (d : x/4219=q) (a : s577 x=l) (b : s577 q=r) (c : l-r=v) : s578 x=v := stepCert s577 4219 x q l r v h d a b c
theorem u579 (x q l r v : Nat) (h : ¬x<4229) (d : x/4229=q) (a : s578 x=l) (b : s578 q=r) (c : l-r=v) : s579 x=v := stepCert s578 4229 x q l r v h d a b c
theorem u580 (x q l r v : Nat) (h : ¬x<4231) (d : x/4231=q) (a : s579 x=l) (b : s579 q=r) (c : l-r=v) : s580 x=v := stepCert s579 4231 x q l r v h d a b c
theorem u581 (x q l r v : Nat) (h : ¬x<4241) (d : x/4241=q) (a : s580 x=l) (b : s580 q=r) (c : l-r=v) : s581 x=v := stepCert s580 4241 x q l r v h d a b c
theorem u582 (x q l r v : Nat) (h : ¬x<4243) (d : x/4243=q) (a : s581 x=l) (b : s581 q=r) (c : l-r=v) : s582 x=v := stepCert s581 4243 x q l r v h d a b c
theorem u583 (x q l r v : Nat) (h : ¬x<4253) (d : x/4253=q) (a : s582 x=l) (b : s582 q=r) (c : l-r=v) : s583 x=v := stepCert s582 4253 x q l r v h d a b c
theorem u584 (x q l r v : Nat) (h : ¬x<4259) (d : x/4259=q) (a : s583 x=l) (b : s583 q=r) (c : l-r=v) : s584 x=v := stepCert s583 4259 x q l r v h d a b c
theorem u585 (x q l r v : Nat) (h : ¬x<4261) (d : x/4261=q) (a : s584 x=l) (b : s584 q=r) (c : l-r=v) : s585 x=v := stepCert s584 4261 x q l r v h d a b c
theorem u586 (x q l r v : Nat) (h : ¬x<4271) (d : x/4271=q) (a : s585 x=l) (b : s585 q=r) (c : l-r=v) : s586 x=v := stepCert s585 4271 x q l r v h d a b c
theorem u587 (x q l r v : Nat) (h : ¬x<4273) (d : x/4273=q) (a : s586 x=l) (b : s586 q=r) (c : l-r=v) : s587 x=v := stepCert s586 4273 x q l r v h d a b c
theorem u588 (x q l r v : Nat) (h : ¬x<4283) (d : x/4283=q) (a : s587 x=l) (b : s587 q=r) (c : l-r=v) : s588 x=v := stepCert s587 4283 x q l r v h d a b c
theorem u589 (x q l r v : Nat) (h : ¬x<4289) (d : x/4289=q) (a : s588 x=l) (b : s588 q=r) (c : l-r=v) : s589 x=v := stepCert s588 4289 x q l r v h d a b c
theorem u590 (x q l r v : Nat) (h : ¬x<4297) (d : x/4297=q) (a : s589 x=l) (b : s589 q=r) (c : l-r=v) : s590 x=v := stepCert s589 4297 x q l r v h d a b c
theorem u591 (x q l r v : Nat) (h : ¬x<4327) (d : x/4327=q) (a : s590 x=l) (b : s590 q=r) (c : l-r=v) : s591 x=v := stepCert s590 4327 x q l r v h d a b c
theorem u592 (x q l r v : Nat) (h : ¬x<4337) (d : x/4337=q) (a : s591 x=l) (b : s591 q=r) (c : l-r=v) : s592 x=v := stepCert s591 4337 x q l r v h d a b c
theorem u593 (x q l r v : Nat) (h : ¬x<4339) (d : x/4339=q) (a : s592 x=l) (b : s592 q=r) (c : l-r=v) : s593 x=v := stepCert s592 4339 x q l r v h d a b c
theorem u594 (x q l r v : Nat) (h : ¬x<4349) (d : x/4349=q) (a : s593 x=l) (b : s593 q=r) (c : l-r=v) : s594 x=v := stepCert s593 4349 x q l r v h d a b c
theorem u595 (x q l r v : Nat) (h : ¬x<4357) (d : x/4357=q) (a : s594 x=l) (b : s594 q=r) (c : l-r=v) : s595 x=v := stepCert s594 4357 x q l r v h d a b c
theorem u596 (x q l r v : Nat) (h : ¬x<4363) (d : x/4363=q) (a : s595 x=l) (b : s595 q=r) (c : l-r=v) : s596 x=v := stepCert s595 4363 x q l r v h d a b c
theorem u597 (x q l r v : Nat) (h : ¬x<4373) (d : x/4373=q) (a : s596 x=l) (b : s596 q=r) (c : l-r=v) : s597 x=v := stepCert s596 4373 x q l r v h d a b c
theorem u598 (x q l r v : Nat) (h : ¬x<4391) (d : x/4391=q) (a : s597 x=l) (b : s597 q=r) (c : l-r=v) : s598 x=v := stepCert s597 4391 x q l r v h d a b c
theorem u599 (x q l r v : Nat) (h : ¬x<4397) (d : x/4397=q) (a : s598 x=l) (b : s598 q=r) (c : l-r=v) : s599 x=v := stepCert s598 4397 x q l r v h d a b c
theorem u600 (x q l r v : Nat) (h : ¬x<4409) (d : x/4409=q) (a : s599 x=l) (b : s599 q=r) (c : l-r=v) : s600 x=v := stepCert s599 4409 x q l r v h d a b c
theorem u601 (x q l r v : Nat) (h : ¬x<4421) (d : x/4421=q) (a : s600 x=l) (b : s600 q=r) (c : l-r=v) : s601 x=v := stepCert s600 4421 x q l r v h d a b c
theorem u602 (x q l r v : Nat) (h : ¬x<4423) (d : x/4423=q) (a : s601 x=l) (b : s601 q=r) (c : l-r=v) : s602 x=v := stepCert s601 4423 x q l r v h d a b c
theorem u603 (x q l r v : Nat) (h : ¬x<4441) (d : x/4441=q) (a : s602 x=l) (b : s602 q=r) (c : l-r=v) : s603 x=v := stepCert s602 4441 x q l r v h d a b c
theorem u604 (x q l r v : Nat) (h : ¬x<4447) (d : x/4447=q) (a : s603 x=l) (b : s603 q=r) (c : l-r=v) : s604 x=v := stepCert s603 4447 x q l r v h d a b c
theorem u605 (x q l r v : Nat) (h : ¬x<4451) (d : x/4451=q) (a : s604 x=l) (b : s604 q=r) (c : l-r=v) : s605 x=v := stepCert s604 4451 x q l r v h d a b c
theorem u606 (x q l r v : Nat) (h : ¬x<4457) (d : x/4457=q) (a : s605 x=l) (b : s605 q=r) (c : l-r=v) : s606 x=v := stepCert s605 4457 x q l r v h d a b c
theorem u607 (x q l r v : Nat) (h : ¬x<4463) (d : x/4463=q) (a : s606 x=l) (b : s606 q=r) (c : l-r=v) : s607 x=v := stepCert s606 4463 x q l r v h d a b c
theorem u608 (x q l r v : Nat) (h : ¬x<4481) (d : x/4481=q) (a : s607 x=l) (b : s607 q=r) (c : l-r=v) : s608 x=v := stepCert s607 4481 x q l r v h d a b c
theorem u609 (x q l r v : Nat) (h : ¬x<4483) (d : x/4483=q) (a : s608 x=l) (b : s608 q=r) (c : l-r=v) : s609 x=v := stepCert s608 4483 x q l r v h d a b c
theorem u610 (x q l r v : Nat) (h : ¬x<4493) (d : x/4493=q) (a : s609 x=l) (b : s609 q=r) (c : l-r=v) : s610 x=v := stepCert s609 4493 x q l r v h d a b c
theorem u611 (x q l r v : Nat) (h : ¬x<4507) (d : x/4507=q) (a : s610 x=l) (b : s610 q=r) (c : l-r=v) : s611 x=v := stepCert s610 4507 x q l r v h d a b c
theorem u612 (x q l r v : Nat) (h : ¬x<4513) (d : x/4513=q) (a : s611 x=l) (b : s611 q=r) (c : l-r=v) : s612 x=v := stepCert s611 4513 x q l r v h d a b c
theorem u613 (x q l r v : Nat) (h : ¬x<4517) (d : x/4517=q) (a : s612 x=l) (b : s612 q=r) (c : l-r=v) : s613 x=v := stepCert s612 4517 x q l r v h d a b c
theorem u614 (x q l r v : Nat) (h : ¬x<4519) (d : x/4519=q) (a : s613 x=l) (b : s613 q=r) (c : l-r=v) : s614 x=v := stepCert s613 4519 x q l r v h d a b c
theorem u615 (x q l r v : Nat) (h : ¬x<4523) (d : x/4523=q) (a : s614 x=l) (b : s614 q=r) (c : l-r=v) : s615 x=v := stepCert s614 4523 x q l r v h d a b c
theorem u616 (x q l r v : Nat) (h : ¬x<4547) (d : x/4547=q) (a : s615 x=l) (b : s615 q=r) (c : l-r=v) : s616 x=v := stepCert s615 4547 x q l r v h d a b c
theorem u617 (x q l r v : Nat) (h : ¬x<4549) (d : x/4549=q) (a : s616 x=l) (b : s616 q=r) (c : l-r=v) : s617 x=v := stepCert s616 4549 x q l r v h d a b c
theorem u618 (x q l r v : Nat) (h : ¬x<4561) (d : x/4561=q) (a : s617 x=l) (b : s617 q=r) (c : l-r=v) : s618 x=v := stepCert s617 4561 x q l r v h d a b c
theorem u619 (x q l r v : Nat) (h : ¬x<4567) (d : x/4567=q) (a : s618 x=l) (b : s618 q=r) (c : l-r=v) : s619 x=v := stepCert s618 4567 x q l r v h d a b c
end A247824Checked

namespace A247824Checked
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c15_20868472 : s15 20868472 = 2894471 := by
  rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c15_393744 : s15 393744 = 54692 := by
  rfl
theorem c16_20868472 : s16 20868472 = 2839779 := u16 20868472 393744 2894471 54692 2839779 (by decide) rfl c15_20868472 c15_393744 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c16_353702 : s16 353702 = 48236 := by
  rfl
theorem c17_20868472 : s17 20868472 = 2791543 := u17 20868472 353702 2839779 48236 2791543 (by decide) rfl c16_20868472 c16_353702 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c17_342106 : s17 342106 = 45880 := by
  rfl
theorem c18_20868472 : s18 20868472 = 2745663 := u18 20868472 342106 2791543 45880 2745663 (by decide) rfl c17_20868472 c17_342106 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c18_311469 : s18 311469 = 41097 := by
  rfl
theorem c19_20868472 : s19 20868472 = 2704566 := u19 20868472 311469 2745663 41097 2704566 (by decide) rfl c18_20868472 c18_311469 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c19_293922 : s19 293922 = 38204 := by
  rfl
theorem c20_20868472 : s20 20868472 = 2666362 := u20 20868472 293922 2704566 38204 2666362 (by decide) rfl c19_20868472 c19_293922 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c20_285869 : s20 285869 = 36623 := by
  rfl
theorem c21_20868472 : s21 20868472 = 2629739 := u21 20868472 285869 2666362 36623 2629739 (by decide) rfl c20_20868472 c20_285869 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c21_264157 : s21 264157 = 33342 := by
  rfl
theorem c22_20868472 : s22 20868472 = 2596397 := u22 20868472 264157 2629739 33342 2596397 (by decide) rfl c21_20868472 c21_264157 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c22_251427 : s22 251427 = 31297 := by
  rfl
theorem c23_20868472 : s23 20868472 = 2565100 := u23 20868472 251427 2596397 31297 2565100 (by decide) rfl c22_20868472 c22_251427 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c23_234477 : s23 234477 = 28783 := by
  rfl
theorem c24_20868472 : s24 20868472 = 2536317 := u24 20868472 234477 2565100 28783 2536317 (by decide) rfl c23_20868472 c23_234477 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c24_215138 : s24 215138 = 26049 := by
  rfl
theorem c25_20868472 : s25 20868472 = 2510268 := u25 20868472 215138 2536317 26049 2510268 (by decide) rfl c24_20868472 c24_215138 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c25_206618 : s25 206618 = 24710 := by
  rfl
theorem c26_20868472 : s26 20868472 = 2485558 := u26 20868472 206618 2510268 24710 2485558 (by decide) rfl c25_20868472 c25_206618 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c26_202606 : s26 202606 = 23941 := by
  rfl
theorem c27_20868472 : s27 20868472 = 2461617 := u27 20868472 202606 2485558 23941 2461617 (by decide) rfl c26_20868472 c26_202606 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c27_195032 : s27 195032 = 22775 := by
  rfl
theorem c28_20868472 : s28 20868472 = 2438842 := u28 20868472 195032 2461617 22775 2438842 (by decide) rfl c27_20868472 c27_195032 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c28_191453 : s28 191453 = 22096 := by
  rfl
theorem c29_20868472 : s29 20868472 = 2416746 := u29 20868472 191453 2438842 22096 2416746 (by decide) rfl c28_20868472 c28_191453 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c29_184676 : s29 184676 = 21068 := by
  rfl
theorem c30_20868472 : s30 20868472 = 2395678 := u30 20868472 184676 2416746 21068 2395678 (by decide) rfl c29_20868472 c29_184676 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c30_164318 : s30 164318 = 18507 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c31_20868472 : s31 20868472 = 2377171 := u31 20868472 164318 2395678 18507 2377171 (by decide) rfl c30_20868472 c30_164318 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c31_159301 : s31 159301 = 17755 := by
  rfl
theorem c32_20868472 : s32 20868472 = 2359416 := u32 20868472 159301 2377171 17755 2359416 (by decide) rfl c31_20868472 c31_159301 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c32_152324 : s32 152324 = 16808 := by
  rfl
theorem c33_20868472 : s33 20868472 = 2342608 := u33 20868472 152324 2359416 16808 2342608 (by decide) rfl c32_20868472 c32_152324 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c33_150132 : s33 150132 = 16408 := by
  rfl
theorem c34_20868472 : s34 20868472 = 2326200 := u34 20868472 150132 2342608 16408 2326200 (by decide) rfl c33_20868472 c33_150132 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c34_140056 : s34 140056 = 15146 := by
  rfl
theorem c35_20868472 : s35 20868472 = 2311054 := u35 20868472 140056 2326200 15146 2311054 (by decide) rfl c34_20868472 c34_140056 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c35_138201 : s35 138201 = 14827 := by
  rfl
theorem c36_20868472 : s36 20868472 = 2296227 := u36 20868472 138201 2311054 14827 2296227 (by decide) rfl c35_20868472 c35_138201 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c36_132920 : s36 132920 = 14120 := by
  rfl
theorem c37_20868472 : s37 20868472 = 2282107 := u37 20868472 132920 2296227 14120 2282107 (by decide) rfl c36_20868472 c36_132920 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c37_128027 : s37 128027 = 13484 := by
  rfl
theorem c38_20868472 : s38 20868472 = 2268623 := u38 20868472 128027 2282107 13484 2268623 (by decide) rfl c37_20868472 c37_128027 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c38_124960 : s38 124960 = 13060 := by
  rfl
theorem c39_20868472 : s39 20868472 = 2255563 := u39 20868472 124960 2268623 13060 2255563 (by decide) rfl c38_20868472 c38_124960 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c39_120627 : s39 120627 = 12503 := by
  rfl
theorem c40_20868472 : s40 20868472 = 2243060 := u40 20868472 120627 2255563 12503 2243060 (by decide) rfl c39_20868472 c39_120627 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c40_116583 : s40 116583 = 11997 := by
  rfl
theorem c41_20868472 : s41 20868472 = 2231063 := u41 20868472 116583 2243060 11997 2231063 (by decide) rfl c40_20868472 c40_116583 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c41_115295 : s41 115295 = 11775 := by
  rfl
theorem c42_20868472 : s42 20868472 = 2219288 := u42 20868472 115295 2231063 11775 2219288 (by decide) rfl c41_20868472 c41_115295 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c42_109259 : s42 109259 = 11096 := by
  rfl
theorem c43_20868472 : s43 20868472 = 2208192 := u43 20868472 109259 2219288 11096 2208192 (by decide) rfl c42_20868472 c42_109259 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c43_108126 : s43 108126 = 10914 := by
  rfl
theorem c44_20868472 : s44 20868472 = 2197278 := u44 20868472 108126 2208192 10914 2197278 (by decide) rfl c43_20868472 c43_108126 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c44_105931 : s44 105931 = 10639 := by
  rfl
theorem c45_20868472 : s45 20868472 = 2186639 := u45 20868472 105931 2197278 10639 2186639 (by decide) rfl c44_20868472 c44_105931 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c45_104866 : s45 104866 = 10480 := by
  rfl
theorem c46_20868472 : s46 20868472 = 2176159 := u46 20868472 104866 2186639 10480 2176159 (by decide) rfl c45_20868472 c45_104866 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c46_98902 : s46 98902 = 9838 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c47_20868472 : s47 20868472 = 2166321 := u47 20868472 98902 2176159 9838 2166321 (by decide) rfl c46_20868472 c46_98902 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c47_93580 : s47 93580 = 9273 := by
  rfl
theorem c48_20868472 : s48 20868472 = 2157048 := u48 20868472 93580 2166321 9273 2157048 (by decide) rfl c47_20868472 c47_93580 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c48_91931 : s48 91931 = 9068 := by
  rfl
theorem c49_20868472 : s49 20868472 = 2147980 := u49 20868472 91931 2157048 9068 2147980 (by decide) rfl c48_20868472 c48_91931 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c49_91128 : s49 91128 = 8960 := by
  rfl
theorem c50_20868472 : s50 20868472 = 2139020 := u50 20868472 91128 2147980 8960 2139020 (by decide) rfl c49_20868472 c49_91128 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c50_89564 : s50 89564 = 8781 := by
  rfl
theorem c51_20868472 : s51 20868472 = 2130239 := u51 20868472 89564 2139020 8781 2130239 (by decide) rfl c50_20868472 c50_89564 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c51_87315 : s51 87315 = 8545 := by
  rfl
theorem c52_20868472 : s52 20868472 = 2121694 := u52 20868472 87315 2130239 8545 2121694 (by decide) rfl c51_20868472 c51_87315 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c52_86591 : s52 86591 = 8460 := by
  rfl
theorem c53_20868472 : s53 20868472 = 2113234 := u53 20868472 86591 2121694 8460 2113234 (by decide) rfl c52_20868472 c52_86591 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c53_83141 : s53 83141 = 8124 := by
  rfl
theorem c54_20868472 : s54 20868472 = 2105110 := u54 20868472 83141 2113234 8124 2105110 (by decide) rfl c53_20868472 c53_83141 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c54_81200 : s54 81200 = 7932 := by
  rfl
theorem c55_20868472 : s55 20868472 = 2097178 := u55 20868472 81200 2105110 7932 2097178 (by decide) rfl c54_20868472 c54_81200 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c55_79347 : s55 79347 = 7742 := by
  rfl
theorem c56_20868472 : s56 20868472 = 2089436 := u56 20868472 79347 2097178 7742 2089436 (by decide) rfl c55_20868472 c55_79347 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c56_77577 : s56 77577 = 7579 := by
  rfl
theorem c57_20868472 : s57 20868472 = 2081857 := u57 20868472 77577 2089436 7579 2081857 (by decide) rfl c56_20868472 c56_77577 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c57_77005 : s57 77005 = 7517 := by
  rfl
theorem c58_20868472 : s58 20868472 = 2074340 := u58 20868472 77005 2081857 7517 2074340 (by decide) rfl c57_20868472 c57_77005 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c58_75337 : s58 75337 = 7366 := by
  rfl
theorem c59_20868472 : s59 20868472 = 2066974 := u59 20868472 75337 2074340 7366 2066974 (by decide) rfl c58_20868472 c58_75337 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c59_74265 : s59 74265 = 7268 := by
  rfl
theorem c60_20868472 : s60 20868472 = 2059706 := u60 20868472 74265 2066974 7268 2059706 (by decide) rfl c59_20868472 c59_74265 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c60_73740 : s60 73740 = 7222 := by
  rfl
theorem c61_20868472 : s61 20868472 = 2052484 := u61 20868472 73740 2059706 7222 2052484 (by decide) rfl c60_20868472 c60_73740 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c61_71223 : s61 71223 = 6990 := by
  rfl
theorem c62_20868472 : s62 20868472 = 2045494 := u62 20868472 71223 2052484 6990 2045494 (by decide) rfl c61_20868472 c61_71223 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c62_67975 : s62 67975 = 6710 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c63_20868472 : s63 20868472 = 2038784 := u63 20868472 67975 2045494 6710 2038784 (by decide) rfl c62_20868472 c62_67975 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c63_67101 : s63 67101 = 6622 := by
  rfl
theorem c64_20868472 : s64 20868472 = 2032162 := u64 20868472 67101 2038784 6622 2032162 (by decide) rfl c63_20868472 c63_67101 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c64_66672 : s64 66672 = 6582 := by
  rfl
theorem c65_20868472 : s65 20868472 = 2025580 := u65 20868472 66672 2032162 6582 2025580 (by decide) rfl c64_20868472 c64_66672 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c65_65831 : s65 65831 = 6511 := by
  rfl
theorem c66_20868472 : s66 20868472 = 2019069 := u66 20868472 65831 2025580 6511 2019069 (by decide) rfl c65_20868472 c65_65831 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c66_63046 : s66 63046 = 6257 := by
  rfl
theorem c67_20868472 : s67 20868472 = 2012812 := u67 20868472 63046 2019069 6257 2012812 (by decide) rfl c66_20868472 c66_63046 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c67_61924 : s67 61924 = 6157 := by
  rfl
theorem c68_20868472 : s68 20868472 = 2006655 := u68 20868472 61924 2012812 6157 2006655 (by decide) rfl c67_20868472 c67_61924 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c68_60139 : s68 60139 = 6005 := by
  rfl
theorem c69_20868472 : s69 20868472 = 2000650 := u69 20868472 60139 2006655 6005 2000650 (by decide) rfl c68_20868472 c68_60139 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c69_59795 : s69 59795 = 5976 := by
  rfl
theorem c70_20868472 : s70 20868472 = 1994674 := u70 20868472 59795 2000650 5976 1994674 (by decide) rfl c69_20868472 c69_59795 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c70_59117 : s70 59117 = 5908 := by
  rfl
theorem c71_20868472 : s71 20868472 = 1988766 := u71 20868472 59117 1994674 5908 1988766 (by decide) rfl c70_20868472 c70_59117 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c71_58129 : s71 58129 = 5816 := by
  rfl
theorem c72_20868472 : s72 20868472 = 1982950 := u72 20868472 58129 1988766 5816 1982950 (by decide) rfl c71_20868472 c71_58129 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c72_56862 : s72 56862 = 5694 := by
  rfl
theorem c73_20868472 : s73 20868472 = 1977256 := u73 20868472 56862 1982950 5694 1977256 (by decide) rfl c72_20868472 c72_56862 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c73_55947 : s73 55947 = 5607 := by
  rfl
theorem c74_20868472 : s74 20868472 = 1971649 := u74 20868472 55947 1977256 5607 1971649 (by decide) rfl c73_20868472 c73_55947 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c74_55061 : s74 55061 = 5524 := by
  rfl
theorem c75_20868472 : s75 20868472 = 1966125 := u75 20868472 55061 1971649 5524 1966125 (by decide) rfl c74_20868472 c74_55061 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c75_54486 : s75 54486 = 5468 := by
  rfl
theorem c76_20868472 : s76 20868472 = 1960657 := u76 20868472 54486 1966125 5468 1960657 (by decide) rfl c75_20868472 c75_54486 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c76_53646 : s76 53646 = 5393 := by
  rfl
theorem c77_20868472 : s77 20868472 = 1955264 := u77 20868472 53646 1960657 5393 1955264 (by decide) rfl c76_20868472 c76_53646 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c77_52565 : s77 52565 = 5291 := by
  rfl
theorem c78_20868472 : s78 20868472 = 1949973 := u78 20868472 52565 1955264 5291 1949973 (by decide) rfl c77_20868472 c77_52565 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c78_52041 : s78 52041 = 5245 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c79_20868472 : s79 20868472 = 1944728 := u79 20868472 52041 1949973 5245 1944728 (by decide) rfl c78_20868472 c78_52041 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c79_51023 : s79 51023 = 5145 := by
  rfl
theorem c80_20868472 : s80 20868472 = 1939583 := u80 20868472 51023 1944728 5145 1939583 (by decide) rfl c79_20868472 c79_51023 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c80_49805 : s80 49805 = 5035 := by
  rfl
theorem c81_20868472 : s81 20868472 = 1934548 := u81 20868472 49805 1939583 5035 1934548 (by decide) rfl c80_20868472 c80_49805 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c81_49568 : s81 49568 = 5013 := by
  rfl
theorem c82_20868472 : s82 20868472 = 1929535 := u82 20868472 49568 1934548 5013 1929535 (by decide) rfl c81_20868472 c81_49568 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c82_48418 : s82 48418 = 4900 := by
  rfl
theorem c83_20868472 : s83 20868472 = 1924635 := u83 20868472 48418 1929535 4900 1924635 (by decide) rfl c82_20868472 c82_48418 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c83_48195 : s83 48195 = 4880 := by
  rfl
theorem c84_20868472 : s84 20868472 = 1919755 := u84 20868472 48195 1924635 4880 1919755 (by decide) rfl c83_20868472 c83_48195 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c84_47536 : s84 47536 = 4818 := by
  rfl
theorem c85_20868472 : s85 20868472 = 1914937 := u85 20868472 47536 1919755 4818 1914937 (by decide) rfl c84_20868472 c84_47536 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c85_47107 : s85 47107 = 4774 := by
  rfl
theorem c86_20868472 : s86 20868472 = 1910163 := u86 20868472 47107 1914937 4774 1910163 (by decide) rfl c85_20868472 c85_47107 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c86_46477 : s86 46477 = 4719 := by
  rfl
theorem c87_20868472 : s87 20868472 = 1905444 := u87 20868472 46477 1910163 4719 1905444 (by decide) rfl c86_20868472 c86_46477 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c87_45664 : s87 45664 = 4645 := by
  rfl
theorem c88_20868472 : s88 20868472 = 1900799 := u88 20868472 45664 1905444 4645 1900799 (by decide) rfl c87_20868472 c87_45664 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c88_45267 : s88 45267 = 4609 := by
  rfl
theorem c89_20868472 : s89 20868472 = 1896190 := u89 20868472 45267 1900799 4609 1896190 (by decide) rfl c88_20868472 c88_45267 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c89_45072 : s89 45072 = 4591 := by
  rfl
theorem c90_20868472 : s90 20868472 = 1891599 := u90 20868472 45072 1896190 4591 1891599 (by decide) rfl c89_20868472 c89_45072 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c90_44686 : s90 44686 = 4555 := by
  rfl
theorem c91_20868472 : s91 20868472 = 1887044 := u91 20868472 44686 1891599 4555 1887044 (by decide) rfl c90_20868472 c90_44686 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c91_43566 : s91 43566 = 4447 := by
  rfl
theorem c92_20868472 : s92 20868472 = 1882597 := u92 20868472 43566 1887044 4447 1882597 (by decide) rfl c91_20868472 c91_43566 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c92_42851 : s92 42851 = 4389 := by
  rfl
theorem c93_20868472 : s93 20868472 = 1878208 := u93 20868472 42851 1882597 4389 1878208 (by decide) rfl c92_20868472 c92_42851 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c93_42501 : s93 42501 = 4355 := by
  rfl
theorem c94_20868472 : s94 20868472 = 1873853 := u94 20868472 42501 1878208 4355 1873853 (by decide) rfl c93_20868472 c93_42501 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c94_41820 : s94 41820 = 4279 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c95_20868472 : s95 20868472 = 1869574 := u95 20868472 41820 1873853 4279 1869574 (by decide) rfl c94_20868472 c94_41820 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c95_41488 : s95 41488 = 4244 := by
  rfl
theorem c96_20868472 : s96 20868472 = 1865330 := u96 20868472 41488 1869574 4244 1865330 (by decide) rfl c95_20868472 c95_41488 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c96_40998 : s96 40998 = 4196 := by
  rfl
theorem c97_20868472 : s97 20868472 = 1861134 := u97 20868472 40998 1865330 4196 1861134 (by decide) rfl c96_20868472 c96_40998 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c97_40054 : s97 40054 = 4112 := by
  rfl
theorem c98_20868472 : s98 20868472 = 1857022 := u98 20868472 40054 1861134 4112 1857022 (by decide) rfl c97_20868472 c97_40054 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c98_39901 : s98 39901 = 4099 := by
  rfl
theorem c99_20868472 : s99 20868472 = 1852923 := u99 20868472 39901 1857022 4099 1852923 (by decide) rfl c98_20868472 c98_39901 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c99_38573 : s99 38573 = 3966 := by
  rfl
theorem c100_20868472 : s100 20868472 = 1848957 := u100 20868472 38573 1852923 3966 1848957 (by decide) rfl c99_20868472 c99_38573 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c100_38150 : s100 38150 = 3927 := by
  rfl
theorem c101_20868472 : s101 20868472 = 1845030 := u101 20868472 38150 1848957 3927 1845030 (by decide) rfl c100_20868472 c100_38150 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c101_37465 : s101 37465 = 3865 := by
  rfl
theorem c102_20868472 : s102 20868472 = 1841165 := u102 20868472 37465 1845030 3865 1841165 (by decide) rfl c101_20868472 c101_37465 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c102_37066 : s102 37066 = 3830 := by
  rfl
theorem c103_20868472 : s103 20868472 = 1837335 := u103 20868472 37066 1841165 3830 1837335 (by decide) rfl c102_20868472 c102_37066 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c103_36675 : s103 36675 = 3785 := by
  rfl
theorem c104_20868472 : s104 20868472 = 1833550 := u104 20868472 36675 1837335 3785 1833550 (by decide) rfl c103_20868472 c103_36675 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c104_36547 : s104 36547 = 3771 := by
  rfl
theorem c105_20868472 : s105 20868472 = 1829779 := u105 20868472 36547 1833550 3771 1829779 (by decide) rfl c104_20868472 c104_36547 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c105_36167 : s105 36167 = 3736 := by
  rfl
theorem c106_20868472 : s106 20868472 = 1826043 := u106 20868472 36167 1829779 3736 1826043 (by decide) rfl c105_20868472 c105_36167 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c106_35551 : s106 35551 = 3681 := by
  rfl
theorem c107_20868472 : s107 20868472 = 1822362 := u107 20868472 35551 1826043 3681 1822362 (by decide) rfl c106_20868472 c106_35551 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c107_35191 : s107 35191 = 3645 := by
  rfl
theorem c108_20868472 : s108 20868472 = 1818717 := u108 20868472 35191 1822362 3645 1818717 (by decide) rfl c107_20868472 c107_35191 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c108_34838 : s108 34838 = 3610 := by
  rfl
theorem c109_20868472 : s109 20868472 = 1815107 := u109 20868472 34838 1818717 3610 1815107 (by decide) rfl c108_20868472 c108_34838 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c109_34722 : s109 34722 = 3600 := by
  rfl
theorem c110_20868472 : s110 20868472 = 1811507 := u110 20868472 34722 1815107 3600 1811507 (by decide) rfl c109_20868472 c109_34722 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c110_34379 : s110 34379 = 3565 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c111_20868472 : s111 20868472 = 1807942 := u111 20868472 34379 1811507 3565 1807942 (by decide) rfl c110_20868472 c110_34379 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c111_34043 : s111 34043 = 3532 := by
  rfl
theorem c112_20868472 : s112 20868472 = 1804410 := u112 20868472 34043 1807942 3532 1804410 (by decide) rfl c111_20868472 c111_34043 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c112_33822 : s112 33822 = 3511 := by
  rfl
theorem c113_20868472 : s113 20868472 = 1800899 := u113 20868472 33822 1804410 3511 1800899 (by decide) rfl c112_20868472 c112_33822 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c113_33713 : s113 33713 = 3498 := by
  rfl
theorem c114_20868472 : s114 20868472 = 1797401 := u114 20868472 33713 1800899 3498 1797401 (by decide) rfl c113_20868472 c113_33713 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c114_33072 : s114 33072 = 3432 := by
  rfl
theorem c115_20868472 : s115 20868472 = 1793969 := u115 20868472 33072 1797401 3432 1793969 (by decide) rfl c114_20868472 c114_33072 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c115_32556 : s115 32556 = 3378 := by
  rfl
theorem c116_20868472 : s116 20868472 = 1790591 := u116 20868472 32556 1793969 3378 1790591 (by decide) rfl c115_20868472 c115_32556 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c116_32454 : s116 32454 = 3368 := by
  rfl
theorem c117_20868472 : s117 20868472 = 1787223 := u117 20868472 32454 1790591 3368 1787223 (by decide) rfl c116_20868472 c116_32454 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c117_32254 : s117 32254 = 3343 := by
  rfl
theorem c118_20868472 : s118 20868472 = 1783880 := u118 20868472 32254 1787223 3343 1783880 (by decide) rfl c117_20868472 c117_32254 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c118_31957 : s118 31957 = 3311 := by
  rfl
theorem c119_20868472 : s119 20868472 = 1780569 := u119 20868472 31957 1783880 3311 1780569 (by decide) rfl c118_20868472 c118_31957 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c119_31666 : s119 31666 = 3288 := by
  rfl
theorem c120_20868472 : s120 20868472 = 1777281 := u120 20868472 31666 1780569 3288 1777281 (by decide) rfl c119_20868472 c119_31666 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c120_31571 : s120 31571 = 3278 := by
  rfl
theorem c121_20868472 : s121 20868472 = 1774003 := u121 20868472 31571 1777281 3278 1774003 (by decide) rfl c120_20868472 c120_31571 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c121_31008 : s121 31008 = 3220 := by
  rfl
theorem c122_20868472 : s122 20868472 = 1770783 := u122 20868472 31008 1774003 3220 1770783 (by decide) rfl c121_20868472 c121_31008 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c122_30824 : s122 30824 = 3201 := by
  rfl
theorem c123_20868472 : s123 20868472 = 1767582 := u123 20868472 30824 1770783 3201 1767582 (by decide) rfl c122_20868472 c122_30824 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c123_30554 : s123 30554 = 3176 := by
  rfl
theorem c124_20868472 : s124 20868472 = 1764406 := u124 20868472 30554 1767582 3176 1764406 (by decide) rfl c123_20868472 c123_30554 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c124_30200 : s124 30200 = 3143 := by
  rfl
theorem c125_20868472 : s125 20868472 = 1761263 := u125 20868472 30200 1764406 3143 1761263 (by decide) rfl c124_20868472 c124_30200 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c125_29769 : s125 29769 = 3103 := by
  rfl
theorem c126_20868472 : s126 20868472 = 1758160 := u126 20868472 29769 1761263 3103 1758160 (by decide) rfl c125_20868472 c125_29769 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c126_29433 : s126 29433 = 3073 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c127_20868472 : s127 20868472 = 1755087 := u127 20868472 29433 1758160 3073 1755087 (by decide) rfl c126_20868472 c126_29433 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c127_29024 : s127 29024 = 3031 := by
  rfl
theorem c128_20868472 : s128 20868472 = 1752056 := u128 20868472 29024 1755087 3031 1752056 (by decide) rfl c127_20868472 c127_29024 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c128_28704 : s128 28704 = 3000 := by
  rfl
theorem c129_20868472 : s129 20868472 = 1749056 := u129 20868472 28704 1752056 3000 1749056 (by decide) rfl c128_20868472 c128_28704 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c129_28469 : s129 28469 = 2969 := by
  rfl
theorem c130_20868472 : s130 20868472 = 1746087 := u130 20868472 28469 1749056 2969 1746087 (by decide) rfl c129_20868472 c129_28469 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c130_28238 : s130 28238 = 2948 := by
  rfl
theorem c131_20868472 : s131 20868472 = 1743139 := u131 20868472 28238 1746087 2948 1743139 (by decide) rfl c130_20868472 c130_28238 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c131_28086 : s131 28086 = 2933 := by
  rfl
theorem c132_20868472 : s132 20868472 = 1740206 := u132 20868472 28086 1743139 2933 1740206 (by decide) rfl c131_20868472 c131_28086 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c132_27787 : s132 27787 = 2901 := by
  rfl
theorem c133_20868472 : s133 20868472 = 1737305 := u133 20868472 27787 1740206 2901 1737305 (by decide) rfl c132_20868472 c132_27787 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c133_27567 : s133 27567 = 2878 := by
  rfl
theorem c134_20868472 : s134 20868472 = 1734427 := u134 20868472 27567 1737305 2878 1734427 (by decide) rfl c133_20868472 c133_27567 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c134_27422 : s134 27422 = 2863 := by
  rfl
theorem c135_20868472 : s135 20868472 = 1731564 := u135 20868472 27422 1734427 2863 1731564 (by decide) rfl c134_20868472 c134_27422 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c135_27137 : s135 27137 = 2841 := by
  rfl
theorem c136_20868472 : s136 20868472 = 1728723 := u136 20868472 27137 1731564 2841 1728723 (by decide) rfl c135_20868472 c135_27137 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c136_26996 : s136 26996 = 2826 := by
  rfl
theorem c137_20868472 : s137 20868472 = 1725897 := u137 20868472 26996 1728723 2826 1725897 (by decide) rfl c136_20868472 c136_26996 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c137_26516 : s137 26516 = 2776 := by
  rfl
theorem c138_20868472 : s138 20868472 = 1723121 := u138 20868472 26516 1725897 2776 1723121 (by decide) rfl c137_20868472 c137_26516 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c138_26183 : s138 26183 = 2741 := by
  rfl
theorem c139_20868472 : s139 20868472 = 1720380 := u139 20868472 26183 1723121 2741 1720380 (by decide) rfl c138_20868472 c138_26183 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c139_25795 : s139 25795 = 2701 := by
  rfl
theorem c140_20868472 : s140 20868472 = 1717679 := u140 20868472 25795 1720380 2701 1717679 (by decide) rfl c139_20868472 c139_25795 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c140_25731 : s140 25731 = 2693 := by
  rfl
theorem c141_20868472 : s141 20868472 = 1714986 := u141 20868472 25731 1717679 2693 1714986 (by decide) rfl c140_20868472 c140_25731 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c141_25418 : s141 25418 = 2662 := by
  rfl
theorem c142_20868472 : s142 20868472 = 1712324 := u142 20868472 25418 1714986 2662 1712324 (by decide) rfl c141_20868472 c141_25418 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c142_25356 : s142 25356 = 2655 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c143_20868472 : s143 20868472 = 1709669 := u143 20868472 25356 1712324 2655 1709669 (by decide) rfl c142_20868472 c142_25356 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c143_25233 : s143 25233 = 2641 := by
  rfl
theorem c144_20868472 : s144 20868472 = 1707028 := u144 20868472 25233 1709669 2641 1707028 (by decide) rfl c143_20868472 c143_25233 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c144_25173 : s144 25173 = 2636 := by
  rfl
theorem c145_20868472 : s145 20868472 = 1704392 := u145 20868472 25173 1707028 2636 1704392 (by decide) rfl c144_20868472 c144_25173 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c145_24873 : s145 24873 = 2605 := by
  rfl
theorem c146_20868472 : s146 20868472 = 1701787 := u146 20868472 24873 1704392 2605 1701787 (by decide) rfl c145_20868472 c145_24873 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c146_24464 : s146 24464 = 2569 := by
  rfl
theorem c147_20868472 : s147 20868472 = 1699218 := u147 20868472 24464 1701787 2569 1699218 (by decide) rfl c146_20868472 c146_24464 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c147_24350 : s147 24350 = 2557 := by
  rfl
theorem c148_20868472 : s148 20868472 = 1696661 := u148 20868472 24350 1699218 2557 1696661 (by decide) rfl c147_20868472 c147_24350 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c148_24293 : s148 24293 = 2553 := by
  rfl
theorem c149_20868472 : s149 20868472 = 1694108 := u149 20868472 24293 1696661 2553 1694108 (by decide) rfl c148_20868472 c148_24293 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c149_24181 : s149 24181 = 2544 := by
  rfl
theorem c150_20868472 : s150 20868472 = 1691564 := u150 20868472 24181 1694108 2544 1691564 (by decide) rfl c149_20868472 c149_24181 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c150_23795 : s150 23795 = 2497 := by
  rfl
theorem c151_20868472 : s151 20868472 = 1689067 := u151 20868472 23795 1691564 2497 1689067 (by decide) rfl c150_20868472 c150_23795 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c151_23687 : s151 23687 = 2486 := by
  rfl
theorem c152_20868472 : s152 20868472 = 1686581 := u152 20868472 23687 1689067 2486 1686581 (by decide) rfl c151_20868472 c151_23687 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c152_23633 : s152 23633 = 2480 := by
  rfl
theorem c153_20868472 : s153 20868472 = 1684101 := u153 20868472 23633 1686581 2480 1684101 (by decide) rfl c152_20868472 c152_23633 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c153_23527 : s153 23527 = 2462 := by
  rfl
theorem c154_20868472 : s154 20868472 = 1681639 := u154 20868472 23527 1684101 2462 1681639 (by decide) rfl c153_20868472 c153_23527 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c154_23008 : s154 23008 = 2412 := by
  rfl
theorem c155_20868472 : s155 20868472 = 1679227 := u155 20868472 23008 1681639 2412 1679227 (by decide) rfl c154_20868472 c154_23008 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c155_22907 : s155 22907 = 2403 := by
  rfl
theorem c156_20868472 : s156 20868472 = 1676824 := u156 20868472 22907 1679227 2403 1676824 (by decide) rfl c155_20868472 c155_22907 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c156_22707 : s156 22707 = 2381 := by
  rfl
theorem c157_20868472 : s157 20868472 = 1674443 := u157 20868472 22707 1676824 2381 1674443 (by decide) rfl c156_20868472 c156_22707 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c157_22463 : s157 22463 = 2356 := by
  rfl
theorem c158_20868472 : s158 20868472 = 1672087 := u158 20868472 22463 1674443 2356 1672087 (by decide) rfl c157_20868472 c157_22463 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c158_22271 : s158 22271 = 2336 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c159_20868472 : s159 20868472 = 1669751 := u159 20868472 22271 1672087 2336 1669751 (by decide) rfl c158_20868472 c158_22271 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c159_22176 : s159 22176 = 2329 := by
  rfl
theorem c160_20868472 : s160 20868472 = 1667422 := u160 20868472 22176 1669751 2329 1667422 (by decide) rfl c159_20868472 c159_22176 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c160_22036 : s160 22036 = 2309 := by
  rfl
theorem c161_20868472 : s161 20868472 = 1665113 := u161 20868472 22036 1667422 2309 1665113 (by decide) rfl c160_20868472 c160_22036 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c161_21897 : s161 21897 = 2296 := by
  rfl
theorem c162_20868472 : s162 20868472 = 1662817 := u162 20868472 21897 1665113 2296 1662817 (by decide) rfl c161_20868472 c161_21897 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c162_21580 : s162 21580 = 2261 := by
  rfl
theorem c163_20868472 : s163 20868472 = 1660556 := u163 20868472 21580 1662817 2261 1660556 (by decide) rfl c162_20868472 c162_21580 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c163_21491 : s163 21491 = 2248 := by
  rfl
theorem c164_20868472 : s164 20868472 = 1658308 := u164 20868472 21491 1660556 2248 1658308 (by decide) rfl c163_20868472 c163_21491 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c164_21359 : s164 21359 = 2234 := by
  rfl
theorem c165_20868472 : s165 20868472 = 1656074 := u165 20868472 21359 1658308 2234 1656074 (by decide) rfl c164_20868472 c164_21359 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c165_21229 : s165 21229 = 2223 := by
  rfl
theorem c166_20868472 : s166 20868472 = 1653851 := u166 20868472 21229 1656074 2223 1653851 (by decide) rfl c165_20868472 c165_21229 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c166_21057 : s166 21057 = 2202 := by
  rfl
theorem c167_20868472 : s167 20868472 = 1651649 := u167 20868472 21057 1653851 2202 1651649 (by decide) rfl c166_20868472 c166_21057 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c167_20931 : s167 20931 = 2188 := by
  rfl
theorem c168_20868472 : s168 20868472 = 1649461 := u168 20868472 20931 1651649 2188 1649461 (by decide) rfl c167_20868472 c167_20931 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c168_20682 : s168 20682 = 2162 := by
  rfl
theorem c169_20868472 : s169 20868472 = 1647299 := u169 20868472 20682 1649461 2162 1647299 (by decide) rfl c168_20868472 c168_20682 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c169_20600 : s169 20600 = 2155 := by
  rfl
theorem c170_20868472 : s170 20868472 = 1645144 := u170 20868472 20600 1647299 2155 1645144 (by decide) rfl c169_20868472 c169_20600 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c170_20479 : s170 20479 = 2143 := by
  rfl
theorem c171_20868472 : s171 20868472 = 1643001 := u171 20868472 20479 1645144 2143 1643001 (by decide) rfl c170_20868472 c170_20479 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c171_20439 : s171 20439 = 2138 := by
  rfl
theorem c172_20868472 : s172 20868472 = 1640863 := u172 20868472 20439 1643001 2138 1640863 (by decide) rfl c171_20868472 c171_20439 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c172_20241 : s172 20241 = 2117 := by
  rfl
theorem c173_20868472 : s173 20868472 = 1638746 := u173 20868472 20241 1640863 2117 1638746 (by decide) rfl c172_20868472 c172_20241 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c173_20201 : s173 20201 = 2113 := by
  rfl
theorem c174_20868472 : s174 20868472 = 1636633 := u174 20868472 20201 1638746 2113 1636633 (by decide) rfl c173_20868472 c173_20201 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c174_20085 : s174 20085 = 2097 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c175_20868472 : s175 20868472 = 1634536 := u175 20868472 20085 1636633 2097 1634536 (by decide) rfl c174_20868472 c174_20085 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c175_19893 : s175 19893 = 2076 := by
  rfl
theorem c176_20868472 : s176 20868472 = 1632460 := u176 20868472 19893 1634536 2076 1632460 (by decide) rfl c175_20868472 c175_19893 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c176_19855 : s176 19855 = 2071 := by
  rfl
theorem c177_20868472 : s177 20868472 = 1630389 := u177 20868472 19855 1632460 2071 1630389 (by decide) rfl c176_20868472 c176_19855 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c177_19668 : s177 19668 = 2050 := by
  rfl
theorem c178_20868472 : s178 20868472 = 1628339 := u178 20868472 19668 1630389 2050 1628339 (by decide) rfl c177_20868472 c177_19668 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c178_19631 : s178 19631 = 2048 := by
  rfl
theorem c179_20868472 : s179 20868472 = 1626291 := u179 20868472 19631 1628339 2048 1626291 (by decide) rfl c178_20868472 c178_19631 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c179_19521 : s179 19521 = 2036 := by
  rfl
theorem c180_20868472 : s180 20868472 = 1624255 := u180 20868472 19521 1626291 2036 1624255 (by decide) rfl c179_20868472 c179_19521 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c180_19198 : s180 19198 = 1997 := by
  rfl
theorem c181_20868472 : s181 20868472 = 1622258 := u181 20868472 19198 1624255 1997 1622258 (by decide) rfl c180_20868472 c180_19198 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c181_19127 : s181 19127 = 1990 := by
  rfl
theorem c182_20868472 : s182 20868472 = 1620268 := u182 20868472 19127 1622258 1990 1620268 (by decide) rfl c181_20868472 c181_19127 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c182_19092 : s182 19092 = 1988 := by
  rfl
theorem c183_20868472 : s183 20868472 = 1618280 := u183 20868472 19092 1620268 1988 1618280 (by decide) rfl c182_20868472 c182_19092 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c183_19023 : s183 19023 = 1979 := by
  rfl
theorem c184_20868472 : s184 20868472 = 1616301 := u184 20868472 19023 1618280 1979 1616301 (by decide) rfl c183_20868472 c183_19023 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c184_18919 : s184 18919 = 1971 := by
  rfl
theorem c185_20868472 : s185 20868472 = 1614330 := u185 20868472 18919 1616301 1971 1614330 (by decide) rfl c184_20868472 c184_18919 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c185_18817 : s185 18817 = 1962 := by
  rfl
theorem c186_20868472 : s186 20868472 = 1612368 := u186 20868472 18817 1614330 1962 1612368 (by decide) rfl c185_20868472 c185_18817 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c186_18682 : s186 18682 = 1948 := by
  rfl
theorem c187_20868472 : s187 20868472 = 1610420 := u187 20868472 18682 1612368 1948 1610420 (by decide) rfl c186_20868472 c186_18682 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c187_18582 : s187 18582 = 1939 := by
  rfl
theorem c188_20868472 : s188 20868472 = 1608481 := u188 20868472 18582 1610420 1939 1608481 (by decide) rfl c187_20868472 c187_18582 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c188_18484 : s188 18484 = 1930 := by
  rfl
theorem c189_20868472 : s189 20868472 = 1606551 := u189 20868472 18484 1608481 1930 1606551 (by decide) rfl c188_20868472 c188_18484 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c189_18130 : s189 18130 = 1889 := by
  rfl
theorem c190_20868472 : s190 20868472 = 1604662 := u190 20868472 18130 1606551 1889 1604662 (by decide) rfl c189_20868472 c189_18130 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c190_18099 : s190 18099 = 1885 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c191_20868472 : s191 20868472 = 1602777 := u191 20868472 18099 1604662 1885 1602777 (by decide) rfl c190_20868472 c190_18099 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c191_17943 : s191 17943 = 1867 := by
  rfl
theorem c192_20868472 : s192 20868472 = 1600910 := u192 20868472 17943 1602777 1867 1600910 (by decide) rfl c191_20868472 c191_17943 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c192_17821 : s192 17821 = 1852 := by
  rfl
theorem c193_20868472 : s193 20868472 = 1599058 := u193 20868472 17821 1600910 1852 1599058 (by decide) rfl c192_20868472 c192_17821 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c193_17670 : s193 17670 = 1838 := by
  rfl
theorem c194_20868472 : s194 20868472 = 1597220 := u194 20868472 17670 1599058 1838 1597220 (by decide) rfl c193_20868472 c193_17670 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c194_17580 : s194 17580 = 1828 := by
  rfl
theorem c195_20868472 : s195 20868472 = 1595392 := u195 20868472 17580 1597220 1828 1595392 (by decide) rfl c194_20868472 c194_17580 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c195_17492 : s195 17492 = 1819 := by
  rfl
theorem c196_20868472 : s196 20868472 = 1593573 := u196 20868472 17492 1595392 1819 1593573 (by decide) rfl c195_20868472 c195_17492 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c196_17375 : s196 17375 = 1801 := by
  rfl
theorem c197_20868472 : s197 20868472 = 1591772 := u197 20868472 17375 1593573 1801 1591772 (by decide) rfl c196_20868472 c196_17375 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c197_17204 : s197 17204 = 1785 := by
  rfl
theorem c198_20868472 : s198 20868472 = 1589987 := u198 20868472 17204 1591772 1785 1589987 (by decide) rfl c197_20868472 c197_17204 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c198_17147 : s198 17147 = 1778 := by
  rfl
theorem c199_20868472 : s199 20868472 = 1588209 := u199 20868472 17147 1589987 1778 1588209 (by decide) rfl c198_20868472 c198_17147 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c199_17063 : s199 17063 = 1770 := by
  rfl
theorem c200_20868472 : s200 20868472 = 1586439 := u200 20868472 17063 1588209 1770 1586439 (by decide) rfl c199_20868472 c199_17063 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c200_16980 : s200 16980 = 1758 := by
  rfl
theorem c201_20868472 : s201 20868472 = 1584681 := u201 20868472 16980 1586439 1758 1584681 (by decide) rfl c200_20868472 c200_16980 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c201_16952 : s201 16952 = 1755 := by
  rfl
theorem c202_20868472 : s202 20868472 = 1582926 := u202 20868472 16952 1584681 1755 1582926 (by decide) rfl c201_20868472 c201_16952 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c202_16870 : s202 16870 = 1743 := by
  rfl
theorem c203_20868472 : s203 20868472 = 1581183 := u203 20868472 16870 1582926 1743 1581183 (by decide) rfl c202_20868472 c202_16870 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c203_16708 : s203 16708 = 1731 := by
  rfl
theorem c204_20868472 : s204 20868472 = 1579452 := u204 20868472 16708 1581183 1731 1579452 (by decide) rfl c203_20868472 c203_16708 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c204_16575 : s204 16575 = 1716 := by
  rfl
theorem c205_20868472 : s205 20868472 = 1577736 := u205 20868472 16575 1579452 1716 1577736 (by decide) rfl c204_20868472 c204_16575 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c205_16341 : s205 16341 = 1691 := by
  rfl
theorem c206_20868472 : s206 20868472 = 1576045 := u206 20868472 16341 1577736 1691 1576045 (by decide) rfl c205_20868472 c205_16341 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c206_16316 : s206 16316 = 1687 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c207_20868472 : s207 20868472 = 1574358 := u207 20868472 16316 1576045 1687 1574358 (by decide) rfl c206_20868472 c206_16316 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c207_16265 : s207 16265 = 1683 := by
  rfl
theorem c208_20868472 : s208 20868472 = 1572675 := u208 20868472 16265 1574358 1683 1572675 (by decide) rfl c207_20868472 c207_16265 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c208_16189 : s208 16189 = 1675 := by
  rfl
theorem c209_20868472 : s209 20868472 = 1571000 := u209 20868472 16189 1572675 1675 1571000 (by decide) rfl c208_20868472 c208_16189 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c209_16164 : s209 16164 = 1671 := by
  rfl
theorem c210_20868472 : s210 20868472 = 1569329 := u210 20868472 16164 1571000 1671 1569329 (by decide) rfl c209_20868472 c209_16164 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c210_16089 : s210 16089 = 1663 := by
  rfl
theorem c211_20868472 : s211 20868472 = 1567666 := u211 20868472 16089 1569329 1663 1567666 (by decide) rfl c210_20868472 c210_16089 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c211_16040 : s211 16040 = 1655 := by
  rfl
theorem c212_20868472 : s212 20868472 = 1566011 := u212 20868472 16040 1567666 1655 1566011 (by decide) rfl c211_20868472 c211_16040 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c212_16015 : s212 16015 = 1653 := by
  rfl
theorem c213_20868472 : s213 20868472 = 1564358 := u213 20868472 16015 1566011 1653 1564358 (by decide) rfl c212_20868472 c212_16015 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c213_15966 : s213 15966 = 1647 := by
  rfl
theorem c214_20868472 : s214 20868472 = 1562711 := u214 20868472 15966 1564358 1647 1562711 (by decide) rfl c213_20868472 c213_15966 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c214_15821 : s214 15821 = 1633 := by
  rfl
theorem c215_20868472 : s215 20868472 = 1561078 := u215 20868472 15821 1562711 1633 1561078 (by decide) rfl c214_20868472 c214_15821 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c215_15797 : s215 15797 = 1629 := by
  rfl
theorem c216_20868472 : s216 20868472 = 1559449 := u216 20868472 15797 1561078 1629 1559449 (by decide) rfl c215_20868472 c215_15797 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c216_15726 : s216 15726 = 1616 := by
  rfl
theorem c217_20868472 : s217 20868472 = 1557833 := u217 20868472 15726 1559449 1616 1557833 (by decide) rfl c216_20868472 c216_15726 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c217_15333 : s217 15333 = 1576 := by
  rfl
theorem c218_20868472 : s218 20868472 = 1556257 := u218 20868472 15333 1557833 1576 1556257 (by decide) rfl c217_20868472 c217_15333 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c218_15265 : s218 15265 = 1564 := by
  rfl
theorem c219_20868472 : s219 20868472 = 1554693 := u219 20868472 15265 1556257 1564 1554693 (by decide) rfl c218_20868472 c218_15265 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c219_15199 : s219 15199 = 1557 := by
  rfl
theorem c220_20868472 : s220 20868472 = 1553136 := u220 20868472 15199 1554693 1557 1553136 (by decide) rfl c219_20868472 c219_15199 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c220_15111 : s220 15111 = 1546 := by
  rfl
theorem c221_20868472 : s221 20868472 = 1551590 := u221 20868472 15111 1553136 1546 1551590 (by decide) rfl c220_20868472 c220_15111 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c221_14916 : s221 14916 = 1526 := by
  rfl
theorem c222_20868472 : s222 20868472 = 1550064 := u222 20868472 14916 1551590 1526 1550064 (by decide) rfl c221_20868472 c221_14916 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c222_14810 : s222 14810 = 1513 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c223_20868472 : s223 20868472 = 1548551 := u223 20868472 14810 1550064 1513 1548551 (by decide) rfl c222_20868472 c222_14810 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c223_14665 : s223 14665 = 1495 := by
  rfl
theorem c224_20868472 : s224 20868472 = 1547056 := u224 20868472 14665 1548551 1495 1547056 (by decide) rfl c223_20868472 c223_14665 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c224_14624 : s224 14624 = 1488 := by
  rfl
theorem c225_20868472 : s225 20868472 = 1545568 := u225 20868472 14624 1547056 1488 1545568 (by decide) rfl c224_20868472 c224_14624 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c225_14603 : s225 14603 = 1486 := by
  rfl
theorem c226_20868472 : s226 20868472 = 1544082 := u226 20868472 14603 1545568 1486 1544082 (by decide) rfl c225_20868472 c225_14603 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c226_14562 : s226 14562 = 1482 := by
  rfl
theorem c227_20868472 : s227 20868472 = 1542600 := u227 20868472 14562 1544082 1482 1542600 (by decide) rfl c226_20868472 c226_14562 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c227_14502 : s227 14502 = 1472 := by
  rfl
theorem c228_20868472 : s228 20868472 = 1541128 := u228 20868472 14502 1542600 1472 1541128 (by decide) rfl c227_20868472 c227_14502 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c228_14421 : s228 14421 = 1463 := by
  rfl
theorem c229_20868472 : s229 20868472 = 1539665 := u229 20868472 14421 1541128 1463 1539665 (by decide) rfl c228_20868472 c228_14421 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c229_14382 : s229 14382 = 1456 := by
  rfl
theorem c230_20868472 : s230 20868472 = 1538209 := u230 20868472 14382 1539665 1456 1538209 (by decide) rfl c229_20868472 c229_14382 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c230_14362 : s230 14362 = 1454 := by
  rfl
theorem c231_20868472 : s231 20868472 = 1536755 := u231 20868472 14362 1538209 1454 1536755 (by decide) rfl c230_20868472 c230_14362 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c231_14303 : s231 14303 = 1448 := by
  rfl
theorem c232_20868472 : s232 20868472 = 1535307 := u232 20868472 14303 1536755 1448 1535307 (by decide) rfl c231_20868472 c231_14303 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c232_14186 : s232 14186 = 1438 := by
  rfl
theorem c233_20868472 : s233 20868472 = 1533869 := u233 20868472 14186 1535307 1438 1533869 (by decide) rfl c232_20868472 c232_14186 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c233_14090 : s233 14090 = 1430 := by
  rfl
theorem c234_20868472 : s234 20868472 = 1532439 := u234 20868472 14090 1533869 1430 1532439 (by decide) rfl c233_20868472 c233_14090 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c234_14071 : s234 14071 = 1426 := by
  rfl
theorem c235_20868472 : s235 20868472 = 1531013 := u235 20868472 14071 1532439 1426 1531013 (by decide) rfl c234_20868472 c234_14071 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c235_14033 : s235 14033 = 1422 := by
  rfl
theorem c236_20868472 : s236 20868472 = 1529591 := u236 20868472 14033 1531013 1422 1529591 (by decide) rfl c235_20868472 c235_14033 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c236_14015 : s236 14015 = 1419 := by
  rfl
theorem c237_20868472 : s237 20868472 = 1528172 := u237 20868472 14015 1529591 1419 1528172 (by decide) rfl c236_20868472 c236_14015 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c237_13977 : s237 13977 = 1414 := by
  rfl
theorem c238_20868472 : s238 20868472 = 1526758 := u238 20868472 13977 1528172 1414 1526758 (by decide) rfl c237_20868472 c237_13977 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c238_13921 : s238 13921 = 1409 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c239_20868472 : s239 20868472 = 1525349 := u239 20868472 13921 1526758 1409 1525349 (by decide) rfl c238_20868472 c238_13921 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c239_13811 : s239 13811 = 1395 := by
  rfl
theorem c240_20868472 : s240 20868472 = 1523954 := u240 20868472 13811 1525349 1395 1523954 (by decide) rfl c239_20868472 c239_13811 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c240_13702 : s240 13702 = 1381 := by
  rfl
theorem c241_20868472 : s241 20868472 = 1522573 := u241 20868472 13702 1523954 1381 1522573 (by decide) rfl c240_20868472 c240_13702 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c241_13630 : s241 13630 = 1371 := by
  rfl
theorem c242_20868472 : s242 20868472 = 1521202 := u242 20868472 13630 1522573 1371 1521202 (by decide) rfl c241_20868472 c241_13630 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c242_13524 : s242 13524 = 1361 := by
  rfl
theorem c243_20868472 : s243 20868472 = 1519841 := u243 20868472 13524 1521202 1361 1519841 (by decide) rfl c242_20868472 c242_13524 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c243_13472 : s243 13472 = 1355 := by
  rfl
theorem c244_20868472 : s244 20868472 = 1518486 := u244 20868472 13472 1519841 1355 1518486 (by decide) rfl c243_20868472 c243_13472 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c244_13437 : s244 13437 = 1349 := by
  rfl
theorem c245_20868472 : s245 20868472 = 1517137 := u245 20868472 13437 1518486 1349 1517137 (by decide) rfl c244_20868472 c244_13437 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c245_13385 : s245 13385 = 1343 := by
  rfl
theorem c246_20868472 : s246 20868472 = 1515794 := u246 20868472 13385 1517137 1343 1515794 (by decide) rfl c245_20868472 c245_13385 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c246_13317 : s246 13317 = 1336 := by
  rfl
theorem c247_20868472 : s247 20868472 = 1514458 := u247 20868472 13317 1515794 1336 1514458 (by decide) rfl c246_20868472 c246_13317 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c247_13283 : s247 13283 = 1331 := by
  rfl
theorem c248_20868472 : s248 20868472 = 1513127 := u248 20868472 13283 1514458 1331 1513127 (by decide) rfl c247_20868472 c247_13283 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c248_13216 : s248 13216 = 1323 := by
  rfl
theorem c249_20868472 : s249 20868472 = 1511804 := u249 20868472 13216 1513127 1323 1511804 (by decide) rfl c248_20868472 c248_13216 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c249_13182 : s249 13182 = 1320 := by
  rfl
theorem c250_20868472 : s250 20868472 = 1510484 := u250 20868472 13182 1511804 1320 1510484 (by decide) rfl c249_20868472 c249_13182 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c250_13067 : s250 13067 = 1307 := by
  rfl
theorem c251_20868472 : s251 20868472 = 1509177 := u251 20868472 13067 1510484 1307 1509177 (by decide) rfl c250_20868472 c250_13067 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c251_13034 : s251 13034 = 1302 := by
  rfl
theorem c252_20868472 : s252 20868472 = 1507875 := u252 20868472 13034 1509177 1302 1507875 (by decide) rfl c251_20868472 c251_13034 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c252_12985 : s252 12985 = 1296 := by
  rfl
theorem c253_20868472 : s253 20868472 = 1506579 := u253 20868472 12985 1507875 1296 1506579 (by decide) rfl c252_20868472 c252_12985 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c253_12969 : s253 12969 = 1292 := by
  rfl
theorem c254_20868472 : s254 20868472 = 1505287 := u254 20868472 12969 1506579 1292 1505287 (by decide) rfl c253_20868472 c253_12969 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c254_12937 : s254 12937 = 1287 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c255_20868472 : s255 20868472 = 1504000 := u255 20868472 12937 1505287 1287 1504000 (by decide) rfl c254_20868472 c254_12937 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c255_12889 : s255 12889 = 1279 := by
  rfl
theorem c256_20868472 : s256 20868472 = 1502721 := u256 20868472 12889 1504000 1279 1502721 (by decide) rfl c255_20868472 c255_12889 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c256_12873 : s256 12873 = 1277 := by
  rfl
theorem c257_20868472 : s257 20868472 = 1501444 := u257 20868472 12873 1502721 1277 1501444 (by decide) rfl c256_20868472 c256_12873 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c257_12826 : s257 12826 = 1273 := by
  rfl
theorem c258_20868472 : s258 20868472 = 1500171 := u258 20868472 12826 1501444 1273 1500171 (by decide) rfl c257_20868472 c257_12826 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c258_12747 : s258 12747 = 1264 := by
  rfl
theorem c259_20868472 : s259 20868472 = 1498907 := u259 20868472 12747 1500171 1264 1498907 (by decide) rfl c258_20868472 c258_12747 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c259_12594 : s259 12594 = 1246 := by
  rfl
theorem c260_20868472 : s260 20868472 = 1497661 := u260 20868472 12594 1498907 1246 1497661 (by decide) rfl c259_20868472 c259_12594 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c260_12548 : s260 12548 = 1240 := by
  rfl
theorem c261_20868472 : s261 20868472 = 1496421 := u261 20868472 12548 1497661 1240 1496421 (by decide) rfl c260_20868472 c260_12548 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c261_12518 : s261 12518 = 1235 := by
  rfl
theorem c262_20868472 : s262 20868472 = 1495186 := u262 20868472 12518 1496421 1235 1495186 (by decide) rfl c261_20868472 c261_12518 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c262_12503 : s262 12503 = 1232 := by
  rfl
theorem c263_20868472 : s263 20868472 = 1493954 := u263 20868472 12503 1495186 1232 1493954 (by decide) rfl c262_20868472 c262_12503 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c263_12326 : s263 12326 = 1210 := by
  rfl
theorem c264_20868472 : s264 20868472 = 1492744 := u264 20868472 12326 1493954 1210 1492744 (by decide) rfl c263_20868472 c263_12326 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c264_12297 : s264 12297 = 1207 := by
  rfl
theorem c265_20868472 : s265 20868472 = 1491537 := u265 20868472 12297 1492744 1207 1491537 (by decide) rfl c264_20868472 c264_12297 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c265_12282 : s265 12282 = 1205 := by
  rfl
theorem c266_20868472 : s266 20868472 = 1490332 := u266 20868472 12282 1491537 1205 1490332 (by decide) rfl c265_20868472 c265_12282 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c266_12210 : s266 12210 = 1194 := by
  rfl
theorem c267_20868472 : s267 20868472 = 1489138 := u267 20868472 12210 1490332 1194 1489138 (by decide) rfl c266_20868472 c266_12210 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c267_12125 : s267 12125 = 1186 := by
  rfl
theorem c268_20868472 : s268 20868472 = 1487952 := u268 20868472 12125 1489138 1186 1487952 (by decide) rfl c267_20868472 c267_12125 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c268_12111 : s268 12111 = 1183 := by
  rfl
theorem c269_20868472 : s269 20868472 = 1486769 := u269 20868472 12111 1487952 1183 1486769 (by decide) rfl c268_20868472 c268_12111 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c269_12041 : s269 12041 = 1174 := by
  rfl
theorem c270_20868472 : s270 20868472 = 1485595 := u270 20868472 12041 1486769 1174 1485595 (by decide) rfl c269_20868472 c269_12041 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c270_11986 : s270 11986 = 1168 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c271_20868472 : s271 20868472 = 1484427 := u271 20868472 11986 1485595 1168 1484427 (by decide) rfl c270_20868472 c270_11986 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c271_11945 : s271 11945 = 1162 := by
  rfl
theorem c272_20868472 : s272 20868472 = 1483265 := u272 20868472 11945 1484427 1162 1483265 (by decide) rfl c271_20868472 c271_11945 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c272_11904 : s272 11904 = 1155 := by
  rfl
theorem c273_20868472 : s273 20868472 = 1482110 := u273 20868472 11904 1483265 1155 1482110 (by decide) rfl c272_20868472 c272_11904 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c273_11863 : s273 11863 = 1150 := by
  rfl
theorem c274_20868472 : s274 20868472 = 1480960 := u274 20868472 11863 1482110 1150 1480960 (by decide) rfl c273_20868472 c273_11863 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c274_11743 : s274 11743 = 1136 := by
  rfl
theorem c275_20868472 : s275 20868472 = 1479824 := u275 20868472 11743 1480960 1136 1479824 (by decide) rfl c274_20868472 c274_11743 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c275_11704 : s275 11704 = 1131 := by
  rfl
theorem c276_20868472 : s276 20868472 = 1478693 := u276 20868472 11704 1479824 1131 1478693 (by decide) rfl c275_20868472 c275_11704 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c276_11677 : s276 11677 = 1126 := by
  rfl
theorem c277_20868472 : s277 20868472 = 1477567 := u277 20868472 11677 1478693 1126 1477567 (by decide) rfl c276_20868472 c276_11677 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c277_11664 : s277 11664 = 1124 := by
  rfl
theorem c278_20868472 : s278 20868472 = 1476443 := u278 20868472 11664 1477567 1124 1476443 (by decide) rfl c277_20868472 c277_11664 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c278_11587 : s278 11587 = 1117 := by
  rfl
theorem c279_20868472 : s279 20868472 = 1475326 := u279 20868472 11587 1476443 1117 1475326 (by decide) rfl c278_20868472 c278_11587 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c279_11523 : s279 11523 = 1111 := by
  rfl
theorem c280_20868472 : s280 20868472 = 1474215 := u280 20868472 11523 1475326 1111 1474215 (by decide) rfl c279_20868472 c279_11523 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c280_11447 : s280 11447 = 1102 := by
  rfl
theorem c281_20868472 : s281 20868472 = 1473113 := u281 20868472 11447 1474215 1102 1473113 (by decide) rfl c280_20868472 c280_11447 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c281_11397 : s281 11397 = 1095 := by
  rfl
theorem c282_20868472 : s282 20868472 = 1472018 := u282 20868472 11397 1473113 1095 1472018 (by decide) rfl c281_20868472 c281_11397 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c282_11298 : s282 11298 = 1084 := by
  rfl
theorem c283_20868472 : s283 20868472 = 1470934 := u283 20868472 11298 1472018 1084 1470934 (by decide) rfl c282_20868472 c282_11298 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c283_11213 : s283 11213 = 1075 := by
  rfl
theorem c284_20868472 : s284 20868472 = 1469859 := u284 20868472 11213 1470934 1075 1469859 (by decide) rfl c283_20868472 c283_11213 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c284_11177 : s284 11177 = 1072 := by
  rfl
theorem c285_20868472 : s285 20868472 = 1468787 := u285 20868472 11177 1469859 1072 1468787 (by decide) rfl c284_20868472 c284_11177 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c285_11153 : s285 11153 = 1066 := by
  rfl
theorem c286_20868472 : s286 20868472 = 1467721 := u286 20868472 11153 1468787 1066 1467721 (by decide) rfl c285_20868472 c285_11153 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c286_11141 : s286 11141 = 1064 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c287_20868472 : s287 20868472 = 1466657 := u287 20868472 11141 1467721 1064 1466657 (by decide) rfl c286_20868472 c286_11141 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c287_11117 : s287 11117 = 1061 := by
  rfl
theorem c288_20868472 : s288 20868472 = 1465596 := u288 20868472 11117 1466657 1061 1465596 (by decide) rfl c287_20868472 c287_11117 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c288_11106 : s288 11106 = 1058 := by
  rfl
theorem c289_20868472 : s289 20868472 = 1464538 := u289 20868472 11106 1465596 1058 1464538 (by decide) rfl c288_20868472 c288_11106 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c289_11047 : s289 11047 = 1050 := by
  rfl
theorem c290_20868472 : s290 20868472 = 1463488 := u290 20868472 11047 1464538 1050 1463488 (by decide) rfl c289_20868472 c289_11047 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c290_10977 : s290 10977 = 1043 := by
  rfl
theorem c291_20868472 : s291 20868472 = 1462445 := u291 20868472 10977 1463488 1043 1462445 (by decide) rfl c290_20868472 c290_10977 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c291_10943 : s291 10943 = 1039 := by
  rfl
theorem c292_20868472 : s292 20868472 = 1461406 := u292 20868472 10943 1462445 1039 1461406 (by decide) rfl c291_20868472 c291_10943 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c292_10908 : s292 10908 = 1035 := by
  rfl
theorem c293_20868472 : s293 20868472 = 1460371 := u293 20868472 10908 1461406 1035 1460371 (by decide) rfl c292_20868472 c292_10908 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c293_10807 : s293 10807 = 1023 := by
  rfl
theorem c294_20868472 : s294 20868472 = 1459348 := u294 20868472 10807 1460371 1023 1459348 (by decide) rfl c293_20868472 c293_10807 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c294_10795 : s294 10795 = 1021 := by
  rfl
theorem c295_20868472 : s295 20868472 = 1458327 := u295 20868472 10795 1459348 1021 1458327 (by decide) rfl c294_20868472 c294_10795 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c295_10707 : s295 10707 = 1010 := by
  rfl
theorem c296_20868472 : s296 20868472 = 1457317 := u296 20868472 10707 1458327 1010 1457317 (by decide) rfl c295_20868472 c295_10707 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c296_10696 : s296 10696 = 1009 := by
  rfl
theorem c297_20868472 : s297 20868472 = 1456308 := u297 20868472 10696 1457317 1009 1456308 (by decide) rfl c296_20868472 c296_10696 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c297_10577 : s297 10577 = 994 := by
  rfl
theorem c298_20868472 : s298 20868472 = 1455314 := u298 20868472 10577 1456308 994 1455314 (by decide) rfl c297_20868472 c297_10577 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c298_10544 : s298 10544 = 991 := by
  rfl
theorem c299_20868472 : s299 20868472 = 1454323 := u299 20868472 10544 1455314 991 1454323 (by decide) rfl c298_20868472 c298_10544 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c299_10502 : s299 10502 = 987 := by
  rfl
theorem c300_20868472 : s300 20868472 = 1453336 := u300 20868472 10502 1454323 987 1453336 (by decide) rfl c299_20868472 c299_10502 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c300_10470 : s300 10470 = 982 := by
  rfl
theorem c301_20868472 : s301 20868472 = 1452354 := u301 20868472 10470 1453336 982 1452354 (by decide) rfl c300_20868472 c300_10470 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c301_10449 : s301 10449 = 977 := by
  rfl
theorem c302_20868472 : s302 20868472 = 1451377 := u302 20868472 10449 1452354 977 1451377 (by decide) rfl c301_20868472 c301_10449 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c302_10439 : s302 10439 = 976 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c303_20868472 : s303 20868472 = 1450401 := u303 20868472 10439 1451377 976 1450401 (by decide) rfl c302_20868472 c302_10439 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c303_10418 : s303 10418 = 972 := by
  rfl
theorem c304_20868472 : s304 20868472 = 1449429 := u304 20868472 10418 1450401 972 1449429 (by decide) rfl c303_20868472 c303_10418 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c304_10377 : s304 10377 = 969 := by
  rfl
theorem c305_20868472 : s305 20868472 = 1448460 := u305 20868472 10377 1449429 969 1448460 (by decide) rfl c304_20868472 c304_10377 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c305_10346 : s305 10346 = 966 := by
  rfl
theorem c306_20868472 : s306 20868472 = 1447494 := u306 20868472 10346 1448460 966 1447494 (by decide) rfl c305_20868472 c305_10346 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c306_10295 : s306 10295 = 957 := by
  rfl
theorem c307_20868472 : s307 20868472 = 1446537 := u307 20868472 10295 1447494 957 1446537 (by decide) rfl c306_20868472 c306_10295 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c307_10285 : s307 10285 = 955 := by
  rfl
theorem c308_20868472 : s308 20868472 = 1445582 := u308 20868472 10285 1446537 955 1445582 (by decide) rfl c307_20868472 c307_10285 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c308_10234 : s308 10234 = 947 := by
  rfl
theorem c309_20868472 : s309 20868472 = 1444635 := u309 20868472 10234 1445582 947 1444635 (by decide) rfl c308_20868472 c308_10234 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c309_10164 : s309 10164 = 940 := by
  rfl
theorem c310_20868472 : s310 20868472 = 1443695 := u310 20868472 10164 1444635 940 1443695 (by decide) rfl c309_20868472 c309_10164 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c310_10115 : s310 10115 = 933 := by
  rfl
theorem c311_20868472 : s311 20868472 = 1442762 := u311 20868472 10115 1443695 933 1442762 (by decide) rfl c310_20868472 c310_10115 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c311_10086 : s311 10086 = 927 := by
  rfl
theorem c312_20868472 : s312 20868472 = 1441835 := u312 20868472 10086 1442762 927 1441835 (by decide) rfl c311_20868472 c311_10086 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c312_10028 : s312 10028 = 920 := by
  rfl
theorem c313_20868472 : s313 20868472 = 1440915 := u313 20868472 10028 1441835 920 1440915 (by decide) rfl c312_20868472 c312_10028 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c313_10018 : s313 10018 = 919 := by
  rfl
theorem c314_20868472 : s314 20868472 = 1439996 := u314 20868472 10018 1440915 919 1439996 (by decide) rfl c313_20868472 c313_10018 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c314_9999 : s314 9999 = 916 := by
  rfl
theorem c315_20868472 : s315 20868472 = 1439080 := u315 20868472 9999 1439996 916 1439080 (by decide) rfl c314_20868472 c314_9999 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c315_9989 : s315 9989 = 915 := by
  rfl
theorem c316_20868472 : s316 20868472 = 1438165 := u316 20868472 9989 1439080 915 1438165 (by decide) rfl c315_20868472 c315_9989 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c316_9942 : s316 9942 = 911 := by
  rfl
theorem c317_20868472 : s317 20868472 = 1437254 := u317 20868472 9942 1438165 911 1437254 (by decide) rfl c316_20868472 c316_9942 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c317_9885 : s317 9885 = 903 := by
  rfl
theorem c318_20868472 : s318 20868472 = 1436351 := u318 20868472 9885 1437254 903 1436351 (by decide) rfl c317_20868472 c317_9885 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c318_9876 : s318 9876 = 901 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c319_20868472 : s319 20868472 = 1435450 := u319 20868472 9876 1436351 901 1435450 (by decide) rfl c318_20868472 c318_9876 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c319_9802 : s319 9802 = 890 := by
  rfl
theorem c320_20868472 : s320 20868472 = 1434560 := u320 20868472 9802 1435450 890 1434560 (by decide) rfl c319_20868472 c319_9802 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c320_9792 : s320 9792 = 889 := by
  rfl
theorem c321_20868472 : s321 20868472 = 1433671 := u321 20868472 9792 1434560 889 1433671 (by decide) rfl c320_20868472 c320_9792 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c321_9765 : s321 9765 = 883 := by
  rfl
theorem c322_20868472 : s322 20868472 = 1432788 := u322 20868472 9765 1433671 883 1432788 (by decide) rfl c321_20868472 c321_9765 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c322_9747 : s322 9747 = 881 := by
  rfl
theorem c323_20868472 : s323 20868472 = 1431907 := u323 20868472 9747 1432788 881 1431907 (by decide) rfl c322_20868472 c322_9747 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c323_9737 : s323 9737 = 878 := by
  rfl
theorem c324_20868472 : s324 20868472 = 1431029 := u324 20868472 9737 1431907 878 1431029 (by decide) rfl c323_20868472 c323_9737 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c324_9692 : s324 9692 = 873 := by
  rfl
theorem c325_20868472 : s325 20868472 = 1430156 := u325 20868472 9692 1431029 873 1430156 (by decide) rfl c324_20868472 c324_9692 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c325_9656 : s325 9656 = 868 := by
  rfl
theorem c326_20868472 : s326 20868472 = 1429288 := u326 20868472 9656 1430156 868 1429288 (by decide) rfl c325_20868472 c325_9656 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c326_9577 : s326 9577 = 858 := by
  rfl
theorem c327_20868472 : s327 20868472 = 1428430 := u327 20868472 9577 1429288 858 1428430 (by decide) rfl c326_20868472 c326_9577 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c327_9472 : s327 9472 = 847 := by
  rfl
theorem c328_20868472 : s328 20868472 = 1427583 := u328 20868472 9472 1428430 847 1427583 (by decide) rfl c327_20868472 c327_9472 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c328_9455 : s328 9455 = 843 := by
  rfl
theorem c329_20868472 : s329 20868472 = 1426740 := u329 20868472 9455 1427583 843 1426740 (by decide) rfl c328_20868472 c328_9455 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c329_9429 : s329 9429 = 838 := by
  rfl
theorem c330_20868472 : s330 20868472 = 1425902 := u330 20868472 9429 1426740 838 1425902 (by decide) rfl c329_20868472 c329_9429 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c330_9395 : s330 9395 = 832 := by
  rfl
theorem c331_20868472 : s331 20868472 = 1425070 := u331 20868472 9395 1425902 832 1425070 (by decide) rfl c330_20868472 c330_9395 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c331_9328 : s331 9328 = 824 := by
  rfl
theorem c332_20868472 : s332 20868472 = 1424246 := u332 20868472 9328 1425070 824 1424246 (by decide) rfl c331_20868472 c331_9328 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c332_9320 : s332 9320 = 822 := by
  rfl
theorem c333_20868472 : s333 20868472 = 1423424 := u333 20868472 9320 1424246 822 1423424 (by decide) rfl c332_20868472 c332_9320 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c333_9303 : s333 9303 = 819 := by
  rfl
theorem c334_20868472 : s334 20868472 = 1422605 := u334 20868472 9303 1423424 819 1422605 (by decide) rfl c333_20868472 c333_9303 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c334_9270 : s334 9270 = 814 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c335_20868472 : s335 20868472 = 1421791 := u335 20868472 9270 1422605 814 1421791 (by decide) rfl c334_20868472 c334_9270 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c335_9205 : s335 9205 = 807 := by
  rfl
theorem c336_20868472 : s336 20868472 = 1420984 := u336 20868472 9205 1421791 807 1420984 (by decide) rfl c335_20868472 c335_9205 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c336_9197 : s336 9197 = 804 := by
  rfl
theorem c337_20868472 : s337 20868472 = 1420180 := u337 20868472 9197 1420984 804 1420180 (by decide) rfl c336_20868472 c336_9197 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c337_9181 : s337 9181 = 802 := by
  rfl
theorem c338_20868472 : s338 20868472 = 1419378 := u338 20868472 9181 1420180 802 1419378 (by decide) rfl c337_20868472 c337_9181 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c338_9148 : s338 9148 = 796 := by
  rfl
theorem c339_20868472 : s339 20868472 = 1418582 := u339 20868472 9148 1419378 796 1418582 (by decide) rfl c338_20868472 c338_9148 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c339_9124 : s339 9124 = 792 := by
  rfl
theorem c340_20868472 : s340 20868472 = 1417790 := u340 20868472 9124 1418582 792 1417790 (by decide) rfl c339_20868472 c339_9124 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c340_9100 : s340 9100 = 789 := by
  rfl
theorem c341_20868472 : s341 20868472 = 1417001 := u341 20868472 9100 1417790 789 1417001 (by decide) rfl c340_20868472 c340_9100 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c341_9085 : s341 9085 = 787 := by
  rfl
theorem c342_20868472 : s342 20868472 = 1416214 := u342 20868472 9085 1417001 787 1416214 (by decide) rfl c341_20868472 c341_9085 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c342_9037 : s342 9037 = 781 := by
  rfl
theorem c343_20868472 : s343 20868472 = 1415433 := u343 20868472 9037 1416214 781 1415433 (by decide) rfl c342_20868472 c342_9037 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c343_9030 : s343 9030 = 780 := by
  rfl
theorem c344_20868472 : s344 20868472 = 1414653 := u344 20868472 9030 1415433 780 1414653 (by decide) rfl c343_20868472 c343_9030 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c344_8944 : s344 8944 = 769 := by
  rfl
theorem c345_20868472 : s345 20868472 = 1413884 := u345 20868472 8944 1414653 769 1413884 (by decide) rfl c344_20868472 c344_8944 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c345_8921 : s345 8921 = 764 := by
  rfl
theorem c346_20868472 : s346 20868472 = 1413120 := u346 20868472 8921 1413884 764 1413120 (by decide) rfl c345_20868472 c345_8921 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c346_8914 : s346 8914 = 763 := by
  rfl
theorem c347_20868472 : s347 20868472 = 1412357 := u347 20868472 8914 1413120 763 1412357 (by decide) rfl c346_20868472 c346_8914 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c347_8891 : s347 8891 = 761 := by
  rfl
theorem c348_20868472 : s348 20868472 = 1411596 := u348 20868472 8891 1412357 761 1411596 (by decide) rfl c347_20868472 c347_8891 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c348_8876 : s348 8876 = 759 := by
  rfl
theorem c349_20868472 : s349 20868472 = 1410837 := u349 20868472 8876 1411596 759 1410837 (by decide) rfl c348_20868472 c348_8876 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c349_8853 : s349 8853 = 755 := by
  rfl
theorem c350_20868472 : s350 20868472 = 1410082 := u350 20868472 8853 1410837 755 1410082 (by decide) rfl c349_20868472 c349_8853 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c350_8801 : s350 8801 = 746 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c351_20868472 : s351 20868472 = 1409336 := u351 20868472 8801 1410082 746 1409336 (by decide) rfl c350_20868472 c350_8801 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c351_8779 : s351 8779 = 744 := by
  rfl
theorem c352_20868472 : s352 20868472 = 1408592 := u352 20868472 8779 1409336 744 1408592 (by decide) rfl c351_20868472 c351_8779 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c352_8764 : s352 8764 = 742 := by
  rfl
theorem c353_20868472 : s353 20868472 = 1407850 := u353 20868472 8764 1408592 742 1407850 (by decide) rfl c352_20868472 c352_8764 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c353_8757 : s353 8757 = 740 := by
  rfl
theorem c354_20868472 : s354 20868472 = 1407110 := u354 20868472 8757 1407850 740 1407110 (by decide) rfl c353_20868472 c353_8757 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c354_8735 : s354 8735 = 735 := by
  rfl
theorem c355_20868472 : s355 20868472 = 1406375 := u355 20868472 8735 1407110 735 1406375 (by decide) rfl c354_20868472 c354_8735 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c355_8720 : s355 8720 = 733 := by
  rfl
theorem c356_20868472 : s356 20868472 = 1405642 := u356 20868472 8720 1406375 733 1405642 (by decide) rfl c355_20868472 c355_8720 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c356_8698 : s356 8698 = 728 := by
  rfl
theorem c357_20868472 : s357 20868472 = 1404914 := u357 20868472 8698 1405642 728 1404914 (by decide) rfl c356_20868472 c356_8698 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c357_8655 : s357 8655 = 721 := by
  rfl
theorem c358_20868472 : s358 20868472 = 1404193 := u358 20868472 8655 1404914 721 1404193 (by decide) rfl c357_20868472 c357_8655 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c358_8634 : s358 8634 = 718 := by
  rfl
theorem c359_20868472 : s359 20868472 = 1403475 := u359 20868472 8634 1404193 718 1403475 (by decide) rfl c358_20868472 c358_8634 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c359_8612 : s359 8612 = 714 := by
  rfl
theorem c360_20868472 : s360 20868472 = 1402761 := u360 20868472 8612 1403475 714 1402761 (by decide) rfl c359_20868472 c359_8612 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c360_8563 : s360 8563 = 708 := by
  rfl
theorem c361_20868472 : s361 20868472 = 1402053 := u361 20868472 8563 1402761 708 1402053 (by decide) rfl c360_20868472 c360_8563 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c361_8549 : s361 8549 = 706 := by
  rfl
theorem c362_20868472 : s362 20868472 = 1401347 := u362 20868472 8549 1402053 706 1401347 (by decide) rfl c361_20868472 c361_8549 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c362_8528 : s362 8528 = 702 := by
  rfl
theorem c363_20868472 : s363 20868472 = 1400645 := u363 20868472 8528 1401347 702 1400645 (by decide) rfl c362_20868472 c362_8528 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c363_8486 : s363 8486 = 697 := by
  rfl
theorem c364_20868472 : s364 20868472 = 1399948 := u364 20868472 8486 1400645 697 1399948 (by decide) rfl c363_20868472 c363_8486 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c364_8459 : s364 8459 = 694 := by
  rfl
theorem c365_20868472 : s365 20868472 = 1399254 := u365 20868472 8459 1399948 694 1399254 (by decide) rfl c364_20868472 c364_8459 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c365_8438 : s365 8438 = 691 := by
  rfl
theorem c366_20868472 : s366 20868472 = 1398563 := u366 20868472 8438 1399254 691 1398563 (by decide) rfl c365_20868472 c365_8438 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c366_8424 : s366 8424 = 688 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c367_20868472 : s367 20868472 = 1397875 := u367 20868472 8424 1398563 688 1397875 (by decide) rfl c366_20868472 c366_8424 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c367_8337 : s367 8337 = 679 := by
  rfl
theorem c368_20868472 : s368 20868472 = 1397196 := u368 20868472 8337 1397875 679 1397196 (by decide) rfl c367_20868472 c367_8337 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c368_8277 : s368 8277 = 671 := by
  rfl
theorem c369_20868472 : s369 20868472 = 1396525 := u369 20868472 8277 1397196 671 1396525 (by decide) rfl c368_20868472 c368_8277 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c369_8245 : s369 8245 = 667 := by
  rfl
theorem c370_20868472 : s370 20868472 = 1395858 := u370 20868472 8245 1396525 667 1395858 (by decide) rfl c369_20868472 c369_8245 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c370_8219 : s370 8219 = 661 := by
  rfl
theorem c371_20868472 : s371 20868472 = 1395197 := u371 20868472 8219 1395858 661 1395197 (by decide) rfl c370_20868472 c370_8219 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c371_8206 : s371 8206 = 658 := by
  rfl
theorem c372_20868472 : s372 20868472 = 1394539 := u372 20868472 8206 1395197 658 1394539 (by decide) rfl c371_20868472 c371_8206 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c372_8186 : s372 8186 = 656 := by
  rfl
theorem c373_20868472 : s373 20868472 = 1393883 := u373 20868472 8186 1394539 656 1393883 (by decide) rfl c372_20868472 c372_8186 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c373_8180 : s373 8180 = 655 := by
  rfl
theorem c374_20868472 : s374 20868472 = 1393228 := u374 20868472 8180 1393883 655 1393228 (by decide) rfl c373_20868472 c373_8180 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c374_8161 : s374 8161 = 651 := by
  rfl
theorem c375_20868472 : s375 20868472 = 1392577 := u375 20868472 8161 1393228 651 1392577 (by decide) rfl c374_20868472 c374_8161 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c375_8091 : s375 8091 = 643 := by
  rfl
theorem c376_20868472 : s376 20868472 = 1391934 := u376 20868472 8091 1392577 643 1391934 (by decide) rfl c375_20868472 c375_8091 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c376_8054 : s376 8054 = 637 := by
  rfl
theorem c377_20868472 : s377 20868472 = 1391297 := u377 20868472 8054 1391934 637 1391297 (by decide) rfl c376_20868472 c376_8054 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c377_8048 : s377 8048 = 635 := by
  rfl
theorem c378_20868472 : s378 20868472 = 1390662 := u378 20868472 8048 1391297 635 1390662 (by decide) rfl c377_20868472 c377_8048 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c378_7998 : s378 7998 = 630 := by
  rfl
theorem c379_20868472 : s379 20868472 = 1390032 := u379 20868472 7998 1390662 630 1390032 (by decide) rfl c378_20868472 c378_7998 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c379_7974 : s379 7974 = 628 := by
  rfl
theorem c380_20868472 : s380 20868472 = 1389404 := u380 20868472 7974 1390032 628 1389404 (by decide) rfl c379_20868472 c379_7974 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c380_7962 : s380 7962 = 626 := by
  rfl
theorem c381_20868472 : s381 20868472 = 1388778 := u381 20868472 7962 1389404 626 1388778 (by decide) rfl c380_20868472 c380_7962 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c381_7925 : s381 7925 = 620 := by
  rfl
theorem c382_20868472 : s382 20868472 = 1388158 := u382 20868472 7925 1388778 620 1388158 (by decide) rfl c381_20868472 c381_7925 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c382_7883 : s382 7883 = 616 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c383_20868472 : s383 20868472 = 1387542 := u383 20868472 7883 1388158 616 1387542 (by decide) rfl c382_20868472 c382_7883 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c383_7854 : s383 7854 = 610 := by
  rfl
theorem c384_20868472 : s384 20868472 = 1386932 := u384 20868472 7854 1387542 610 1386932 (by decide) rfl c383_20868472 c383_7854 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c384_7848 : s384 7848 = 608 := by
  rfl
theorem c385_20868472 : s385 20868472 = 1386324 := u385 20868472 7848 1386932 608 1386324 (by decide) rfl c384_20868472 c384_7848 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c385_7836 : s385 7836 = 606 := by
  rfl
theorem c386_20868472 : s386 20868472 = 1385718 := u386 20868472 7836 1386324 606 1385718 (by decide) rfl c385_20868472 c385_7836 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c386_7812 : s386 7812 = 602 := by
  rfl
theorem c387_20868472 : s387 20868472 = 1385116 := u387 20868472 7812 1385718 602 1385116 (by decide) rfl c386_20868472 c386_7812 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c387_7795 : s387 7795 = 601 := by
  rfl
theorem c388_20868472 : s388 20868472 = 1384515 := u388 20868472 7795 1385116 601 1384515 (by decide) rfl c387_20868472 c387_7795 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c388_7778 : s388 7778 = 598 := by
  rfl
theorem c389_20868472 : s389 20868472 = 1383917 := u389 20868472 7778 1384515 598 1383917 (by decide) rfl c388_20868472 c388_7778 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c389_7766 : s389 7766 = 597 := by
  rfl
theorem c390_20868472 : s390 20868472 = 1383320 := u390 20868472 7766 1383917 597 1383320 (by decide) rfl c389_20868472 c389_7766 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c390_7760 : s390 7760 = 596 := by
  rfl
theorem c391_20868472 : s391 20868472 = 1382724 := u391 20868472 7760 1383320 596 1382724 (by decide) rfl c390_20868472 c390_7760 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c391_7749 : s391 7749 = 592 := by
  rfl
theorem c392_20868472 : s392 20868472 = 1382132 := u392 20868472 7749 1382724 592 1382132 (by decide) rfl c391_20868472 c391_7749 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c392_7731 : s392 7731 = 590 := by
  rfl
theorem c393_20868472 : s393 20868472 = 1381542 := u393 20868472 7731 1382132 590 1381542 (by decide) rfl c392_20868472 c392_7731 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c393_7709 : s393 7709 = 586 := by
  rfl
theorem c394_20868472 : s394 20868472 = 1380956 := u394 20868472 7709 1381542 586 1380956 (by decide) rfl c393_20868472 c393_7709 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c394_7697 : s394 7697 = 583 := by
  rfl
theorem c395_20868472 : s395 20868472 = 1380373 := u395 20868472 7697 1380956 583 1380373 (by decide) rfl c394_20868472 c394_7697 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c395_7692 : s395 7692 = 582 := by
  rfl
theorem c396_20868472 : s396 20868472 = 1379791 := u396 20868472 7692 1380373 582 1379791 (by decide) rfl c395_20868472 c395_7692 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c396_7675 : s396 7675 = 578 := by
  rfl
theorem c397_20868472 : s397 20868472 = 1379213 := u397 20868472 7675 1379791 578 1379213 (by decide) rfl c396_20868472 c396_7675 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c397_7646 : s397 7646 = 574 := by
  rfl
theorem c398_20868472 : s398 20868472 = 1378639 := u398 20868472 7646 1379213 574 1378639 (by decide) rfl c397_20868472 c397_7646 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c398_7641 : s398 7641 = 572 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c399_20868472 : s399 20868472 = 1378067 := u399 20868472 7641 1378639 572 1378067 (by decide) rfl c398_20868472 c398_7641 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c399_7613 : s399 7613 = 569 := by
  rfl
theorem c400_20868472 : s400 20868472 = 1377498 := u400 20868472 7613 1378067 569 1377498 (by decide) rfl c399_20868472 c399_7613 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c400_7591 : s400 7591 = 566 := by
  rfl
theorem c401_20868472 : s401 20868472 = 1376932 := u401 20868472 7591 1377498 566 1376932 (by decide) rfl c400_20868472 c400_7591 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c401_7580 : s401 7580 = 562 := by
  rfl
theorem c402_20868472 : s402 20868472 = 1376370 := u402 20868472 7580 1376932 562 1376370 (by decide) rfl c401_20868472 c401_7580 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c402_7541 : s402 7541 = 555 := by
  rfl
theorem c403_20868472 : s403 20868472 = 1375815 := u403 20868472 7541 1376370 555 1375815 (by decide) rfl c402_20868472 c402_7541 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c403_7514 : s403 7514 = 549 := by
  rfl
theorem c404_20868472 : s404 20868472 = 1375266 := u404 20868472 7514 1375815 549 1375266 (by decide) rfl c403_20868472 c403_7514 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c404_7482 : s404 7482 = 544 := by
  rfl
theorem c405_20868472 : s405 20868472 = 1374722 := u405 20868472 7482 1375266 544 1374722 (by decide) rfl c404_20868472 c404_7482 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c405_7477 : s405 7477 = 542 := by
  rfl
theorem c406_20868472 : s406 20868472 = 1374180 := u406 20868472 7477 1374722 542 1374180 (by decide) rfl c405_20868472 c405_7477 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c406_7461 : s406 7461 = 540 := by
  rfl
theorem c407_20868472 : s407 20868472 = 1373640 := u407 20868472 7461 1374180 540 1373640 (by decide) rfl c406_20868472 c406_7461 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c407_7450 : s407 7450 = 536 := by
  rfl
theorem c408_20868472 : s408 20868472 = 1373104 := u408 20868472 7450 1373640 536 1373104 (by decide) rfl c407_20868472 c407_7450 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c408_7445 : s408 7445 = 535 := by
  rfl
theorem c409_20868472 : s409 20868472 = 1372569 := u409 20868472 7445 1373104 535 1372569 (by decide) rfl c408_20868472 c408_7445 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c409_7402 : s409 7402 = 531 := by
  rfl
theorem c410_20868472 : s410 20868472 = 1372038 := u410 20868472 7402 1372569 531 1372038 (by decide) rfl c409_20868472 c409_7402 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c410_7366 : s410 7366 = 528 := by
  rfl
theorem c411_20868472 : s411 20868472 = 1371510 := u411 20868472 7366 1372038 528 1371510 (by decide) rfl c410_20868472 c410_7366 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c411_7355 : s411 7355 = 527 := by
  rfl
theorem c412_20868472 : s412 20868472 = 1370983 := u412 20868472 7355 1371510 527 1370983 (by decide) rfl c411_20868472 c411_7355 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c412_7340 : s412 7340 = 524 := by
  rfl
theorem c413_20868472 : s413 20868472 = 1370459 := u413 20868472 7340 1370983 524 1370459 (by decide) rfl c412_20868472 c412_7340 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c413_7319 : s413 7319 = 520 := by
  rfl
theorem c414_20868472 : s414 20868472 = 1369939 := u414 20868472 7319 1370459 520 1369939 (by decide) rfl c413_20868472 c413_7319 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c414_7304 : s414 7304 = 517 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c415_20868472 : s415 20868472 = 1369422 := u415 20868472 7304 1369939 517 1369422 (by decide) rfl c414_20868472 c414_7304 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c415_7294 : s415 7294 = 515 := by
  rfl
theorem c416_20868472 : s416 20868472 = 1368907 := u416 20868472 7294 1369422 515 1368907 (by decide) rfl c415_20868472 c415_7294 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c416_7248 : s416 7248 = 512 := by
  rfl
theorem c417_20868472 : s417 20868472 = 1368395 := u417 20868472 7248 1368907 512 1368395 (by decide) rfl c416_20868472 c416_7248 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c417_7228 : s417 7228 = 507 := by
  rfl
theorem c418_20868472 : s418 20868472 = 1367888 := u418 20868472 7228 1368395 507 1367888 (by decide) rfl c417_20868472 c417_7228 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c418_7203 : s418 7203 = 502 := by
  rfl
theorem c419_20868472 : s419 20868472 = 1367386 := u419 20868472 7203 1367888 502 1367386 (by decide) rfl c418_20868472 c418_7203 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c419_7188 : s419 7188 = 500 := by
  rfl
theorem c420_20868472 : s420 20868472 = 1366886 := u420 20868472 7188 1367386 500 1366886 (by decide) rfl c419_20868472 c419_7188 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c420_7173 : s420 7173 = 497 := by
  rfl
theorem c421_20868472 : s421 20868472 = 1366389 := u421 20868472 7173 1366886 497 1366389 (by decide) rfl c420_20868472 c420_7173 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c421_7154 : s421 7154 = 495 := by
  rfl
theorem c422_20868472 : s422 20868472 = 1365894 := u422 20868472 7154 1366389 495 1365894 (by decide) rfl c421_20868472 c421_7154 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c422_7129 : s422 7129 = 493 := by
  rfl
theorem c423_20868472 : s423 20868472 = 1365401 := u423 20868472 7129 1365894 493 1365401 (by decide) rfl c422_20868472 c422_7129 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c423_7100 : s423 7100 = 487 := by
  rfl
theorem c424_20868472 : s424 20868472 = 1364914 := u424 20868472 7100 1365401 487 1364914 (by decide) rfl c423_20868472 c423_7100 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c424_7066 : s424 7066 = 484 := by
  rfl
theorem c425_20868472 : s425 20868472 = 1364430 := u425 20868472 7066 1364914 484 1364430 (by decide) rfl c424_20868472 c424_7066 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c425_7057 : s425 7057 = 483 := by
  rfl
theorem c426_20868472 : s426 20868472 = 1363947 := u426 20868472 7057 1364430 483 1363947 (by decide) rfl c425_20868472 c425_7057 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c426_7043 : s426 7043 = 481 := by
  rfl
theorem c427_20868472 : s427 20868472 = 1363466 := u427 20868472 7043 1363947 481 1363466 (by decide) rfl c426_20868472 c426_7043 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c427_7028 : s427 7028 = 478 := by
  rfl
theorem c428_20868472 : s428 20868472 = 1362988 := u428 20868472 7028 1363466 478 1362988 (by decide) rfl c427_20868472 c427_7028 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c428_7024 : s428 7024 = 476 := by
  rfl
theorem c429_20868472 : s429 20868472 = 1362512 := u429 20868472 7024 1362988 476 1362512 (by decide) rfl c428_20868472 c428_7024 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c429_6958 : s429 6958 = 464 := by
  rfl
theorem c430_20868472 : s430 20868472 = 1362048 := u430 20868472 6958 1362512 464 1362048 (by decide) rfl c429_20868472 c429_6958 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c430_6953 : s430 6953 = 463 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c431_20868472 : s431 20868472 = 1361585 := u431 20868472 6953 1362048 463 1361585 (by decide) rfl c430_20868472 c430_6953 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c431_6930 : s431 6930 = 460 := by
  rfl
theorem c432_20868472 : s432 20868472 = 1361125 := u432 20868472 6930 1361585 460 1361125 (by decide) rfl c431_20868472 c431_6930 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c432_6912 : s432 6912 = 458 := by
  rfl
theorem c433_20868472 : s433 20868472 = 1360667 := u433 20868472 6912 1361125 458 1360667 (by decide) rfl c432_20868472 c432_6912 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c433_6903 : s433 6903 = 455 := by
  rfl
theorem c434_20868472 : s434 20868472 = 1360212 := u434 20868472 6903 1360667 455 1360212 (by decide) rfl c433_20868472 c433_6903 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c434_6871 : s434 6871 = 452 := by
  rfl
theorem c435_20868472 : s435 20868472 = 1359760 := u435 20868472 6871 1360212 452 1359760 (by decide) rfl c434_20868472 c434_6871 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c435_6862 : s435 6862 = 448 := by
  rfl
theorem c436_20868472 : s436 20868472 = 1359312 := u436 20868472 6862 1359760 448 1359312 (by decide) rfl c435_20868472 c435_6862 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c436_6844 : s436 6844 = 446 := by
  rfl
theorem c437_20868472 : s437 20868472 = 1358866 := u437 20868472 6844 1359312 446 1358866 (by decide) rfl c436_20868472 c436_6844 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c437_6817 : s437 6817 = 440 := by
  rfl
theorem c438_20868472 : s438 20868472 = 1358426 := u438 20868472 6817 1358866 440 1358426 (by decide) rfl c437_20868472 c437_6817 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c438_6804 : s438 6804 = 439 := by
  rfl
theorem c439_20868472 : s439 20868472 = 1357987 := u439 20868472 6804 1358426 439 1357987 (by decide) rfl c438_20868472 c438_6804 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c439_6777 : s439 6777 = 433 := by
  rfl
theorem c440_20868472 : s440 20868472 = 1357554 := u440 20868472 6777 1357987 433 1357554 (by decide) rfl c439_20868472 c439_6777 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c440_6768 : s440 6768 = 432 := by
  rfl
theorem c441_20868472 : s441 20868472 = 1357122 := u441 20868472 6768 1357554 432 1357122 (by decide) rfl c440_20868472 c440_6768 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c441_6755 : s441 6755 = 429 := by
  rfl
theorem c442_20868472 : s442 20868472 = 1356693 := u442 20868472 6755 1357122 429 1356693 (by decide) rfl c441_20868472 c441_6755 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c442_6712 : s442 6712 = 425 := by
  rfl
theorem c443_20868472 : s443 20868472 = 1356268 := u443 20868472 6712 1356693 425 1356268 (by decide) rfl c442_20868472 c442_6712 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c443_6690 : s443 6690 = 420 := by
  rfl
theorem c444_20868472 : s444 20868472 = 1355848 := u444 20868472 6690 1356268 420 1355848 (by decide) rfl c443_20868472 c443_6690 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c444_6686 : s444 6686 = 418 := by
  rfl
theorem c445_20868472 : s445 20868472 = 1355430 := u445 20868472 6686 1355848 418 1355430 (by decide) rfl c444_20868472 c444_6686 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c445_6652 : s445 6652 = 412 := by
  rfl
theorem c446_20868472 : s446 20868472 = 1355018 := u446 20868472 6652 1355430 412 1355018 (by decide) rfl c445_20868472 c445_6652 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c446_6597 : s446 6597 = 407 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c447_20868472 : s447 20868472 = 1354611 := u447 20868472 6597 1355018 407 1354611 (by decide) rfl c446_20868472 c446_6597 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c447_6589 : s447 6589 = 406 := by
  rfl
theorem c448_20868472 : s448 20868472 = 1354205 := u448 20868472 6589 1354611 406 1354205 (by decide) rfl c447_20868472 c447_6589 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c448_6585 : s448 6585 = 405 := by
  rfl
theorem c449_20868472 : s449 20868472 = 1353800 := u449 20868472 6585 1354205 405 1353800 (by decide) rfl c448_20868472 c448_6585 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c449_6560 : s449 6560 = 399 := by
  rfl
theorem c450_20868472 : s450 20868472 = 1353401 := u450 20868472 6560 1353800 399 1353401 (by decide) rfl c449_20868472 c449_6560 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c450_6547 : s450 6547 = 396 := by
  rfl
theorem c451_20868472 : s451 20868472 = 1353005 := u451 20868472 6547 1353401 396 1353005 (by decide) rfl c450_20868472 c450_6547 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c451_6539 : s451 6539 = 394 := by
  rfl
theorem c452_20868472 : s452 20868472 = 1352611 := u452 20868472 6539 1353005 394 1352611 (by decide) rfl c451_20868472 c451_6539 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c452_6515 : s452 6515 = 391 := by
  rfl
theorem c453_20868472 : s453 20868472 = 1352220 := u453 20868472 6515 1352611 391 1352220 (by decide) rfl c452_20868472 c452_6515 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c453_6503 : s453 6503 = 390 := by
  rfl
theorem c454_20868472 : s454 20868472 = 1351830 := u454 20868472 6503 1352220 390 1351830 (by decide) rfl c453_20868472 c453_6503 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c454_6486 : s454 6486 = 388 := by
  rfl
theorem c455_20868472 : s455 20868472 = 1351442 := u455 20868472 6486 1351830 388 1351442 (by decide) rfl c454_20868472 c454_6486 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c455_6478 : s455 6478 = 386 := by
  rfl
theorem c456_20868472 : s456 20868472 = 1351056 := u456 20868472 6478 1351442 386 1351056 (by decide) rfl c455_20868472 c455_6478 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c456_6462 : s456 6462 = 383 := by
  rfl
theorem c457_20868472 : s457 20868472 = 1350673 := u457 20868472 6462 1351056 383 1350673 (by decide) rfl c456_20868472 c456_6462 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c457_6419 : s457 6419 = 378 := by
  rfl
theorem c458_20868472 : s458 20868472 = 1350295 := u458 20868472 6419 1350673 378 1350295 (by decide) rfl c457_20868472 c457_6419 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c458_6415 : s458 6415 = 377 := by
  rfl
theorem c459_20868472 : s459 20868472 = 1349918 := u459 20868472 6415 1350295 377 1349918 (by decide) rfl c458_20868472 c458_6415 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c459_6407 : s459 6407 = 376 := by
  rfl
theorem c460_20868472 : s460 20868472 = 1349542 := u460 20868472 6407 1349918 376 1349542 (by decide) rfl c459_20868472 c459_6407 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c460_6403 : s460 6403 = 375 := by
  rfl
theorem c461_20868472 : s461 20868472 = 1349167 := u461 20868472 6403 1349542 375 1349167 (by decide) rfl c460_20868472 c460_6403 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c461_6379 : s461 6379 = 372 := by
  rfl
theorem c462_20868472 : s462 20868472 = 1348795 := u462 20868472 6379 1349167 372 1348795 (by decide) rfl c461_20868472 c461_6379 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c462_6325 : s462 6325 = 362 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c463_20868472 : s463 20868472 = 1348433 := u463 20868472 6325 1348795 362 1348433 (by decide) rfl c462_20868472 c462_6325 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c463_6321 : s463 6321 = 360 := by
  rfl
theorem c464_20868472 : s464 20868472 = 1348073 := u464 20868472 6321 1348433 360 1348073 (by decide) rfl c463_20868472 c463_6321 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c464_6310 : s464 6310 = 357 := by
  rfl
theorem c465_20868472 : s465 20868472 = 1347716 := u465 20868472 6310 1348073 357 1347716 (by decide) rfl c464_20868472 c464_6310 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c465_6298 : s465 6298 = 354 := by
  rfl
theorem c466_20868472 : s466 20868472 = 1347362 := u466 20868472 6298 1347716 354 1347362 (by decide) rfl c465_20868472 c465_6298 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c466_6287 : s466 6287 = 353 := by
  rfl
theorem c467_20868472 : s467 20868472 = 1347009 := u467 20868472 6287 1347362 353 1347009 (by decide) rfl c466_20868472 c466_6287 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c467_6280 : s467 6280 = 351 := by
  rfl
theorem c468_20868472 : s468 20868472 = 1346658 := u468 20868472 6280 1347009 351 1346658 (by decide) rfl c467_20868472 c467_6280 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c468_6268 : s468 6268 = 347 := by
  rfl
theorem c469_20868472 : s469 20868472 = 1346311 := u469 20868472 6268 1346658 347 1346311 (by decide) rfl c468_20868472 c468_6268 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c469_6264 : s469 6264 = 346 := by
  rfl
theorem c470_20868472 : s470 20868472 = 1345965 := u470 20868472 6264 1346311 346 1345965 (by decide) rfl c469_20868472 c469_6264 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c470_6242 : s470 6242 = 342 := by
  rfl
theorem c471_20868472 : s471 20868472 = 1345623 := u471 20868472 6242 1345965 342 1345623 (by decide) rfl c470_20868472 c470_6242 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c471_6234 : s471 6234 = 341 := by
  rfl
theorem c472_20868472 : s472 20868472 = 1345282 := u472 20868472 6234 1345623 341 1345282 (by decide) rfl c471_20868472 c471_6234 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c472_6212 : s472 6212 = 337 := by
  rfl
theorem c473_20868472 : s473 20868472 = 1344945 := u473 20868472 6212 1345282 337 1344945 (by decide) rfl c472_20868472 c472_6212 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c473_6209 : s473 6209 = 335 := by
  rfl
theorem c474_20868472 : s474 20868472 = 1344610 := u474 20868472 6209 1344945 335 1344610 (by decide) rfl c473_20868472 c473_6209 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c474_6190 : s474 6190 = 331 := by
  rfl
theorem c475_20868472 : s475 20868472 = 1344279 := u475 20868472 6190 1344610 331 1344279 (by decide) rfl c474_20868472 c474_6190 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c475_6186 : s475 6186 = 330 := by
  rfl
theorem c476_20868472 : s476 20868472 = 1343949 := u476 20868472 6186 1344279 330 1343949 (by decide) rfl c475_20868472 c475_6186 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c476_6157 : s476 6157 = 327 := by
  rfl
theorem c477_20868472 : s477 20868472 = 1343622 := u477 20868472 6157 1343949 327 1343622 (by decide) rfl c476_20868472 c476_6157 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c477_6154 : s477 6154 = 326 := by
  rfl
theorem c478_20868472 : s478 20868472 = 1343296 := u478 20868472 6154 1343622 326 1343296 (by decide) rfl c477_20868472 c477_6154 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c478_6125 : s478 6125 = 321 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c479_20868472 : s479 20868472 = 1342975 := u479 20868472 6125 1343296 321 1342975 (by decide) rfl c478_20868472 c478_6125 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c479_6114 : s479 6114 = 319 := by
  rfl
theorem c480_20868472 : s480 20868472 = 1342656 := u480 20868472 6114 1342975 319 1342656 (by decide) rfl c479_20868472 c479_6114 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c480_6078 : s480 6078 = 313 := by
  rfl
theorem c481_20868472 : s481 20868472 = 1342343 := u481 20868472 6078 1342656 313 1342343 (by decide) rfl c480_20868472 c480_6078 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c481_6050 : s481 6050 = 309 := by
  rfl
theorem c482_20868472 : s482 20868472 = 1342034 := u482 20868472 6050 1342343 309 1342034 (by decide) rfl c481_20868472 c481_6050 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c482_6036 : s482 6036 = 305 := by
  rfl
theorem c483_20868472 : s483 20868472 = 1341729 := u483 20868472 6036 1342034 305 1341729 (by decide) rfl c482_20868472 c482_6036 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c483_6029 : s483 6029 = 304 := by
  rfl
theorem c484_20868472 : s484 20868472 = 1341425 := u484 20868472 6029 1341729 304 1341425 (by decide) rfl c483_20868472 c483_6029 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c484_6026 : s484 6026 = 302 := by
  rfl
theorem c485_20868472 : s485 20868472 = 1341123 := u485 20868472 6026 1341425 302 1341123 (by decide) rfl c484_20868472 c484_6026 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c485_6019 : s485 6019 = 301 := by
  rfl
theorem c486_20868472 : s486 20868472 = 1340822 := u486 20868472 6019 1341123 301 1340822 (by decide) rfl c485_20868472 c485_6019 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c486_6015 : s486 6015 = 300 := by
  rfl
theorem c487_20868472 : s487 20868472 = 1340522 := u487 20868472 6015 1340822 300 1340522 (by decide) rfl c486_20868472 c486_6015 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c487_5977 : s487 5977 = 295 := by
  rfl
theorem c488_20868472 : s488 20868472 = 1340227 := u488 20868472 5977 1340522 295 1340227 (by decide) rfl c487_20868472 c487_5977 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c488_5964 : s488 5964 = 294 := by
  rfl
theorem c489_20868472 : s489 20868472 = 1339933 := u489 20868472 5964 1340227 294 1339933 (by decide) rfl c488_20868472 c488_5964 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c489_5943 : s489 5943 = 292 := by
  rfl
theorem c490_20868472 : s490 20868472 = 1339641 := u490 20868472 5943 1339933 292 1339641 (by decide) rfl c489_20868472 c489_5943 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c490_5933 : s490 5933 = 290 := by
  rfl
theorem c491_20868472 : s491 20868472 = 1339351 := u491 20868472 5933 1339641 290 1339351 (by decide) rfl c490_20868472 c490_5933 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c491_5916 : s491 5916 = 287 := by
  rfl
theorem c492_20868472 : s492 20868472 = 1339064 := u492 20868472 5916 1339351 287 1339064 (by decide) rfl c491_20868472 c491_5916 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c492_5913 : s492 5913 = 286 := by
  rfl
theorem c493_20868472 : s493 20868472 = 1338778 := u493 20868472 5913 1339064 286 1338778 (by decide) rfl c492_20868472 c492_5913 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c493_5906 : s493 5906 = 285 := by
  rfl
theorem c494_20868472 : s494 20868472 = 1338493 := u494 20868472 5906 1338778 285 1338493 (by decide) rfl c493_20868472 c493_5906 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c494_5896 : s494 5896 = 282 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c495_20868472 : s495 20868472 = 1338211 := u495 20868472 5896 1338493 282 1338211 (by decide) rfl c494_20868472 c494_5896 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c495_5893 : s495 5893 = 281 := by
  rfl
theorem c496_20868472 : s496 20868472 = 1337930 := u496 20868472 5893 1338211 281 1337930 (by decide) rfl c495_20868472 c495_5893 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c496_5883 : s496 5883 = 280 := by
  rfl
theorem c497_20868472 : s497 20868472 = 1337650 := u497 20868472 5883 1337930 280 1337650 (by decide) rfl c496_20868472 c496_5883 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c497_5866 : s497 5866 = 275 := by
  rfl
theorem c498_20868472 : s498 20868472 = 1337375 := u498 20868472 5866 1337650 275 1337375 (by decide) rfl c497_20868472 c497_5866 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c498_5863 : s498 5863 = 274 := by
  rfl
theorem c499_20868472 : s499 20868472 = 1337101 := u499 20868472 5863 1337375 274 1337101 (by decide) rfl c498_20868472 c498_5863 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c499_5843 : s499 5843 = 269 := by
  rfl
theorem c500_20868472 : s500 20868472 = 1336832 := u500 20868472 5843 1337101 269 1336832 (by decide) rfl c499_20868472 c499_5843 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c500_5827 : s500 5827 = 266 := by
  rfl
theorem c501_20868472 : s501 20868472 = 1336566 := u501 20868472 5827 1336832 266 1336566 (by decide) rfl c500_20868472 c500_5827 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c501_5824 : s501 5824 = 264 := by
  rfl
theorem c502_20868472 : s502 20868472 = 1336302 := u502 20868472 5824 1336566 264 1336302 (by decide) rfl c501_20868472 c501_5824 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c502_5808 : s502 5808 = 261 := by
  rfl
theorem c503_20868472 : s503 20868472 = 1336041 := u503 20868472 5808 1336302 261 1336041 (by decide) rfl c502_20868472 c502_5808 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c503_5785 : s503 5785 = 257 := by
  rfl
theorem c504_20868472 : s504 20868472 = 1335784 := u504 20868472 5785 1336041 257 1335784 (by decide) rfl c503_20868472 c503_5785 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c504_5775 : s504 5775 = 254 := by
  rfl
theorem c505_20868472 : s505 20868472 = 1335530 := u505 20868472 5775 1335784 254 1335530 (by decide) rfl c504_20868472 c504_5775 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c505_5769 : s505 5769 = 253 := by
  rfl
theorem c506_20868472 : s506 20868472 = 1335277 := u506 20868472 5769 1335530 253 1335277 (by decide) rfl c505_20868472 c505_5769 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c506_5759 : s506 5759 = 252 := by
  rfl
theorem c507_20868472 : s507 20868472 = 1335025 := u507 20868472 5759 1335277 252 1335025 (by decide) rfl c506_20868472 c506_5759 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c507_5747 : s507 5747 = 250 := by
  rfl
theorem c508_20868472 : s508 20868472 = 1334775 := u508 20868472 5747 1335025 250 1334775 (by decide) rfl c507_20868472 c507_5747 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c508_5737 : s508 5737 = 247 := by
  rfl
theorem c509_20868472 : s509 20868472 = 1334528 := u509 20868472 5737 1334775 247 1334528 (by decide) rfl c508_20868472 c508_5737 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c509_5728 : s509 5728 = 245 := by
  rfl
theorem c510_20868472 : s510 20868472 = 1334283 := u510 20868472 5728 1334528 245 1334283 (by decide) rfl c509_20868472 c509_5728 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c510_5703 : s510 5703 = 242 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c511_20868472 : s511 20868472 = 1334041 := u511 20868472 5703 1334283 242 1334041 (by decide) rfl c510_20868472 c510_5703 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c511_5684 : s511 5684 = 238 := by
  rfl
theorem c512_20868472 : s512 20868472 = 1333803 := u512 20868472 5684 1334041 238 1333803 (by decide) rfl c511_20868472 c511_5684 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c512_5681 : s512 5681 = 236 := by
  rfl
theorem c513_20868472 : s513 20868472 = 1333567 := u513 20868472 5681 1333803 236 1333567 (by decide) rfl c512_20868472 c512_5681 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c513_5675 : s513 5675 = 235 := by
  rfl
theorem c514_20868472 : s514 20868472 = 1333332 := u514 20868472 5675 1333567 235 1333332 (by decide) rfl c513_20868472 c513_5675 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c514_5653 : s514 5653 = 231 := by
  rfl
theorem c515_20868472 : s515 20868472 = 1333101 := u515 20868472 5653 1333332 231 1333101 (by decide) rfl c514_20868472 c514_5653 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c515_5644 : s515 5644 = 227 := by
  rfl
theorem c516_20868472 : s516 20868472 = 1332874 := u516 20868472 5644 1333101 227 1332874 (by decide) rfl c515_20868472 c515_5644 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c516_5638 : s516 5638 = 224 := by
  rfl
theorem c517_20868472 : s517 20868472 = 1332650 := u517 20868472 5638 1332874 224 1332650 (by decide) rfl c516_20868472 c516_5638 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c517_5626 : s517 5626 = 223 := by
  rfl
theorem c518_20868472 : s518 20868472 = 1332427 := u518 20868472 5626 1332650 223 1332427 (by decide) rfl c517_20868472 c517_5626 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c518_5611 : s518 5611 = 221 := by
  rfl
theorem c519_20868472 : s519 20868472 = 1332206 := u519 20868472 5611 1332427 221 1332206 (by decide) rfl c518_20868472 c518_5611 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c519_5599 : s519 5599 = 220 := by
  rfl
theorem c520_20868472 : s520 20868472 = 1331986 := u520 20868472 5599 1332206 220 1331986 (by decide) rfl c519_20868472 c519_5599 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c520_5590 : s520 5590 = 218 := by
  rfl
theorem c521_20868472 : s521 20868472 = 1331768 := u521 20868472 5590 1331986 218 1331768 (by decide) rfl c520_20868472 c520_5590 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c521_5581 : s521 5581 = 217 := by
  rfl
theorem c522_20868472 : s522 20868472 = 1331551 := u522 20868472 5581 1331768 217 1331551 (by decide) rfl c521_20868472 c521_5581 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c522_5548 : s522 5548 = 211 := by
  rfl
theorem c523_20868472 : s523 20868472 = 1331340 := u523 20868472 5548 1331551 211 1331340 (by decide) rfl c522_20868472 c522_5548 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c523_5539 : s523 5539 = 210 := by
  rfl
theorem c524_20868472 : s524 20868472 = 1331130 := u524 20868472 5539 1331340 210 1331130 (by decide) rfl c523_20868472 c523_5539 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c524_5536 : s524 5536 = 209 := by
  rfl
theorem c525_20868472 : s525 20868472 = 1330921 := u525 20868472 5536 1331130 209 1330921 (by decide) rfl c524_20868472 c524_5536 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c525_5522 : s525 5522 = 206 := by
  rfl
theorem c526_20868472 : s526 20868472 = 1330715 := u526 20868472 5522 1330921 206 1330715 (by decide) rfl c525_20868472 c525_5522 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c526_5501 : s526 5501 = 201 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c527_20868472 : s527 20868472 = 1330514 := u527 20868472 5501 1330715 201 1330514 (by decide) rfl c526_20868472 c526_5501 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c527_5496 : s527 5496 = 199 := by
  rfl
theorem c528_20868472 : s528 20868472 = 1330315 := u528 20868472 5496 1330514 199 1330315 (by decide) rfl c527_20868472 c527_5496 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c528_5487 : s528 5487 = 198 := by
  rfl
theorem c529_20868472 : s529 20868472 = 1330117 := u529 20868472 5487 1330315 198 1330117 (by decide) rfl c528_20868472 c528_5487 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c529_5461 : s529 5461 = 193 := by
  rfl
theorem c530_20868472 : s530 20868472 = 1329924 := u530 20868472 5461 1330117 193 1329924 (by decide) rfl c529_20868472 c529_5461 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c530_5458 : s530 5458 = 192 := by
  rfl
theorem c531_20868472 : s531 20868472 = 1329732 := u531 20868472 5458 1329924 192 1329732 (by decide) rfl c530_20868472 c530_5458 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c531_5444 : s531 5444 = 190 := by
  rfl
theorem c532_20868472 : s532 20868472 = 1329542 := u532 20868472 5444 1329732 190 1329542 (by decide) rfl c531_20868472 c531_5444 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c532_5424 : s532 5424 = 185 := by
  rfl
theorem c533_20868472 : s533 20868472 = 1329357 := u533 20868472 5424 1329542 185 1329357 (by decide) rfl c532_20868472 c532_5424 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c533_5418 : s533 5418 = 183 := by
  rfl
theorem c534_20868472 : s534 20868472 = 1329174 := u534 20868472 5418 1329357 183 1329174 (by decide) rfl c533_20868472 c533_5418 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c534_5416 : s534 5416 = 181 := by
  rfl
theorem c535_20868472 : s535 20868472 = 1328993 := u535 20868472 5416 1329174 181 1328993 (by decide) rfl c534_20868472 c534_5416 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c535_5402 : s535 5402 = 178 := by
  rfl
theorem c536_20868472 : s536 20868472 = 1328815 := u536 20868472 5402 1328993 178 1328815 (by decide) rfl c535_20868472 c535_5402 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c536_5382 : s536 5382 = 174 := by
  rfl
theorem c537_20868472 : s537 20868472 = 1328641 := u537 20868472 5382 1328815 174 1328641 (by decide) rfl c536_20868472 c536_5382 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c537_5377 : s537 5377 = 172 := by
  rfl
theorem c538_20868472 : s538 20868472 = 1328469 := u538 20868472 5377 1328641 172 1328469 (by decide) rfl c537_20868472 c537_5377 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c538_5366 : s538 5366 = 171 := by
  rfl
theorem c539_20868472 : s539 20868472 = 1328298 := u539 20868472 5366 1328469 171 1328298 (by decide) rfl c538_20868472 c538_5366 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c539_5341 : s539 5341 = 168 := by
  rfl
theorem c540_20868472 : s540 20868472 = 1328130 := u540 20868472 5341 1328298 168 1328130 (by decide) rfl c539_20868472 c539_5341 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c540_5335 : s540 5335 = 167 := by
  rfl
theorem c541_20868472 : s541 20868472 = 1327963 := u541 20868472 5335 1328130 167 1327963 (by decide) rfl c540_20868472 c540_5335 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c541_5327 : s541 5327 = 165 := by
  rfl
theorem c542_20868472 : s542 20868472 = 1327798 := u542 20868472 5327 1327963 165 1327798 (by decide) rfl c541_20868472 c541_5327 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c542_5324 : s542 5324 = 164 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c543_20868472 : s543 20868472 = 1327634 := u543 20868472 5324 1327798 164 1327634 (by decide) rfl c542_20868472 c542_5324 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c543_5319 : s543 5319 = 162 := by
  rfl
theorem c544_20868472 : s544 20868472 = 1327472 := u544 20868472 5319 1327634 162 1327472 (by decide) rfl c543_20868472 c543_5319 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c544_5311 : s544 5311 = 161 := by
  rfl
theorem c545_20868472 : s545 20868472 = 1327311 := u545 20868472 5311 1327472 161 1327311 (by decide) rfl c544_20868472 c544_5311 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c545_5308 : s545 5308 = 159 := by
  rfl
theorem c546_20868472 : s546 20868472 = 1327152 := u546 20868472 5308 1327311 159 1327152 (by decide) rfl c545_20868472 c545_5308 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c546_5292 : s546 5292 = 156 := by
  rfl
theorem c547_20868472 : s547 20868472 = 1326996 := u547 20868472 5292 1327152 156 1326996 (by decide) rfl c546_20868472 c546_5292 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c547_5287 : s547 5287 = 155 := by
  rfl
theorem c548_20868472 : s548 20868472 = 1326841 := u548 20868472 5287 1326996 155 1326841 (by decide) rfl c547_20868472 c547_5287 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c548_5260 : s548 5260 = 150 := by
  rfl
theorem c549_20868472 : s549 20868472 = 1326691 := u549 20868472 5260 1326841 150 1326691 (by decide) rfl c548_20868472 c548_5260 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c549_5231 : s549 5231 = 147 := by
  rfl
theorem c550_20868472 : s550 20868472 = 1326544 := u550 20868472 5231 1326691 147 1326544 (by decide) rfl c549_20868472 c549_5231 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c550_5215 : s550 5215 = 144 := by
  rfl
theorem c551_20868472 : s551 20868472 = 1326400 := u551 20868472 5215 1326544 144 1326400 (by decide) rfl c550_20868472 c550_5215 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c551_5213 : s551 5213 = 143 := by
  rfl
theorem c552_20868472 : s552 20868472 = 1326257 := u552 20868472 5213 1326400 143 1326257 (by decide) rfl c551_20868472 c551_5213 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c552_5208 : s552 5208 = 141 := by
  rfl
theorem c553_20868472 : s553 20868472 = 1326116 := u553 20868472 5208 1326257 141 1326116 (by decide) rfl c552_20868472 c552_5208 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c553_5200 : s553 5200 = 140 := by
  rfl
theorem c554_20868472 : s554 20868472 = 1325976 := u554 20868472 5200 1326116 140 1325976 (by decide) rfl c553_20868472 c553_5200 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c554_5192 : s554 5192 = 138 := by
  rfl
theorem c555_20868472 : s555 20868472 = 1325838 := u555 20868472 5192 1325976 138 1325838 (by decide) rfl c554_20868472 c554_5192 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c555_5189 : s555 5189 = 137 := by
  rfl
theorem c556_20868472 : s556 20868472 = 1325701 := u556 20868472 5189 1325838 137 1325701 (by decide) rfl c555_20868472 c555_5189 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c556_5182 : s556 5182 = 135 := by
  rfl
theorem c557_20868472 : s557 20868472 = 1325566 := u557 20868472 5182 1325701 135 1325566 (by decide) rfl c556_20868472 c556_5182 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c557_5153 : s557 5153 = 131 := by
  rfl
theorem c558_20868472 : s558 20868472 = 1325435 := u558 20868472 5153 1325566 131 1325435 (by decide) rfl c557_20868472 c557_5153 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c558_5151 : s558 5151 = 129 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c559_20868472 : s559 20868472 = 1325306 := u559 20868472 5151 1325435 129 1325306 (by decide) rfl c558_20868472 c558_5151 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c559_5143 : s559 5143 = 127 := by
  rfl
theorem c560_20868472 : s560 20868472 = 1325179 := u560 20868472 5143 1325306 127 1325179 (by decide) rfl c559_20868472 c559_5143 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c560_5123 : s560 5123 = 126 := by
  rfl
theorem c561_20868472 : s561 20868472 = 1325053 := u561 20868472 5123 1325179 126 1325053 (by decide) rfl c560_20868472 c560_5123 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c561_5116 : s561 5116 = 124 := by
  rfl
theorem c562_20868472 : s562 20868472 = 1324929 := u562 20868472 5116 1325053 124 1324929 (by decide) rfl c561_20868472 c561_5116 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c562_5101 : s562 5101 = 121 := by
  rfl
theorem c563_20868472 : s563 20868472 = 1324808 := u563 20868472 5101 1324929 121 1324808 (by decide) rfl c562_20868472 c562_5101 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c563_5098 : s563 5098 = 118 := by
  rfl
theorem c564_20868472 : s564 20868472 = 1324690 := u564 20868472 5098 1324808 118 1324690 (by decide) rfl c563_20868472 c563_5098 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c564_5091 : s564 5091 = 117 := by
  rfl
theorem c565_20868472 : s565 20868472 = 1324573 := u565 20868472 5091 1324690 117 1324573 (by decide) rfl c564_20868472 c564_5091 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c565_5076 : s565 5076 = 113 := by
  rfl
theorem c566_20868472 : s566 20868472 = 1324460 := u566 20868472 5076 1324573 113 1324460 (by decide) rfl c565_20868472 c565_5076 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c566_5056 : s566 5056 = 111 := by
  rfl
theorem c567_20868472 : s567 20868472 = 1324349 := u567 20868472 5056 1324460 111 1324349 (by decide) rfl c566_20868472 c566_5056 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c567_5054 : s567 5054 = 110 := by
  rfl
theorem c568_20868472 : s568 20868472 = 1324239 := u568 20868472 5054 1324349 110 1324239 (by decide) rfl c567_20868472 c567_5054 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c568_5049 : s568 5049 = 108 := by
  rfl
theorem c569_20868472 : s569 20868472 = 1324131 := u569 20868472 5049 1324239 108 1324131 (by decide) rfl c568_20868472 c568_5049 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c569_5041 : s569 5041 = 107 := by
  rfl
theorem c570_20868472 : s570 20868472 = 1324024 := u570 20868472 5041 1324131 107 1324024 (by decide) rfl c569_20868472 c569_5041 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c570_5024 : s570 5024 = 105 := by
  rfl
theorem c571_20868472 : s571 20868472 = 1323919 := u571 20868472 5024 1324024 105 1323919 (by decide) rfl c570_20868472 c570_5024 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c571_5020 : s571 5020 = 102 := by
  rfl
theorem c572_20868472 : s572 20868472 = 1323817 := u572 20868472 5020 1323919 102 1323817 (by decide) rfl c571_20868472 c571_5020 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c572_5017 : s572 5017 = 101 := by
  rfl
theorem c573_20868472 : s573 20868472 = 1323716 := u573 20868472 5017 1323817 101 1323716 (by decide) rfl c572_20868472 c572_5017 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c573_4996 : s573 4996 = 96 := by
  rfl
theorem c574_20868472 : s574 20868472 = 1323620 := u574 20868472 4996 1323716 96 1323620 (by decide) rfl c573_20868472 c573_4996 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c574_4967 : s574 4967 = 91 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c575_20868472 : s575 20868472 = 1323529 := u575 20868472 4967 1323620 91 1323529 (by decide) rfl c574_20868472 c574_4967 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c575_4955 : s575 4955 = 88 := by
  rfl
theorem c576_20868472 : s576 20868472 = 1323441 := u576 20868472 4955 1323529 88 1323441 (by decide) rfl c575_20868472 c575_4955 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c576_4948 : s576 4948 = 86 := by
  rfl
theorem c577_20868472 : s577 20868472 = 1323355 := u577 20868472 4948 1323441 86 1323355 (by decide) rfl c576_20868472 c576_4948 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c577_4946 : s577 4946 = 85 := by
  rfl
theorem c578_20868472 : s578 20868472 = 1323270 := u578 20868472 4946 1323355 85 1323270 (by decide) rfl c577_20868472 c577_4946 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c578_4934 : s578 4934 = 82 := by
  rfl
theorem c579_20868472 : s579 20868472 = 1323188 := u579 20868472 4934 1323270 82 1323188 (by decide) rfl c578_20868472 c578_4934 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c579_4932 : s579 4932 = 80 := by
  rfl
theorem c580_20868472 : s580 20868472 = 1323108 := u580 20868472 4932 1323188 80 1323108 (by decide) rfl c579_20868472 c579_4932 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c580_4920 : s580 4920 = 78 := by
  rfl
theorem c581_20868472 : s581 20868472 = 1323030 := u581 20868472 4920 1323108 78 1323030 (by decide) rfl c580_20868472 c580_4920 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c581_4918 : s581 4918 = 76 := by
  rfl
theorem c582_20868472 : s582 20868472 = 1322954 := u582 20868472 4918 1323030 76 1322954 (by decide) rfl c581_20868472 c581_4918 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c582_4906 : s582 4906 = 74 := by
  rfl
theorem c583_20868472 : s583 20868472 = 1322880 := u583 20868472 4906 1322954 74 1322880 (by decide) rfl c582_20868472 c582_4906 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c583_4899 : s583 4899 = 72 := by
  rfl
theorem c584_20868472 : s584 20868472 = 1322808 := u584 20868472 4899 1322880 72 1322808 (by decide) rfl c583_20868472 c583_4899 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c584_4897 : s584 4897 = 71 := by
  rfl
theorem c585_20868472 : s585 20868472 = 1322737 := u585 20868472 4897 1322808 71 1322737 (by decide) rfl c584_20868472 c584_4897 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c585_4886 : s585 4886 = 69 := by
  rfl
theorem c586_20868472 : s586 20868472 = 1322668 := u586 20868472 4886 1322737 69 1322668 (by decide) rfl c585_20868472 c585_4886 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c586_4883 : s586 4883 = 68 := by
  rfl
theorem c587_20868472 : s587 20868472 = 1322600 := u587 20868472 4883 1322668 68 1322600 (by decide) rfl c586_20868472 c586_4883 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c587_4872 : s587 4872 = 66 := by
  rfl
theorem c588_20868472 : s588 20868472 = 1322534 := u588 20868472 4872 1322600 66 1322534 (by decide) rfl c587_20868472 c587_4872 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c588_4865 : s588 4865 = 64 := by
  rfl
theorem c589_20868472 : s589 20868472 = 1322470 := u589 20868472 4865 1322534 64 1322470 (by decide) rfl c588_20868472 c588_4865 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c589_4856 : s589 4856 = 62 := by
  rfl
theorem c590_20868472 : s590 20868472 = 1322408 := u590 20868472 4856 1322470 62 1322408 (by decide) rfl c589_20868472 c589_4856 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c590_4822 : s590 4822 = 60 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c591_20868472 : s591 20868472 = 1322348 := u591 20868472 4822 1322408 60 1322348 (by decide) rfl c590_20868472 c590_4822 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c591_4811 : s591 4811 = 57 := by
  rfl
theorem c592_20868472 : s592 20868472 = 1322291 := u592 20868472 4811 1322348 57 1322291 (by decide) rfl c591_20868472 c591_4811 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c592_4809 : s592 4809 = 56 := by
  rfl
theorem c593_20868472 : s593 20868472 = 1322235 := u593 20868472 4809 1322291 56 1322235 (by decide) rfl c592_20868472 c592_4809 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c593_4798 : s593 4798 = 53 := by
  rfl
theorem c594_20868472 : s594 20868472 = 1322182 := u594 20868472 4798 1322235 53 1322182 (by decide) rfl c593_20868472 c593_4798 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c594_4789 : s594 4789 = 51 := by
  rfl
theorem c595_20868472 : s595 20868472 = 1322131 := u595 20868472 4789 1322182 51 1322131 (by decide) rfl c594_20868472 c594_4789 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c595_4783 : s595 4783 = 48 := by
  rfl
theorem c596_20868472 : s596 20868472 = 1322083 := u596 20868472 4783 1322131 48 1322083 (by decide) rfl c595_20868472 c595_4783 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c596_4772 : s596 4772 = 46 := by
  rfl
theorem c597_20868472 : s597 20868472 = 1322037 := u597 20868472 4772 1322083 46 1322037 (by decide) rfl c596_20868472 c596_4772 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c597_4752 : s597 4752 = 44 := by
  rfl
theorem c598_20868472 : s598 20868472 = 1321993 := u598 20868472 4752 1322037 44 1321993 (by decide) rfl c597_20868472 c597_4752 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c598_4746 : s598 4746 = 42 := by
  rfl
theorem c599_20868472 : s599 20868472 = 1321951 := u599 20868472 4746 1321993 42 1321951 (by decide) rfl c598_20868472 c598_4746 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c599_4733 : s599 4733 = 41 := by
  rfl
theorem c600_20868472 : s600 20868472 = 1321910 := u600 20868472 4733 1321951 41 1321910 (by decide) rfl c599_20868472 c599_4733 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c600_4720 : s600 4720 = 36 := by
  rfl
theorem c601_20868472 : s601 20868472 = 1321874 := u601 20868472 4720 1321910 36 1321874 (by decide) rfl c600_20868472 c600_4720 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c601_4718 : s601 4718 = 35 := by
  rfl
theorem c602_20868472 : s602 20868472 = 1321839 := u602 20868472 4718 1321874 35 1321839 (by decide) rfl c601_20868472 c601_4718 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c602_4699 : s602 4699 = 33 := by
  rfl
theorem c603_20868472 : s603 20868472 = 1321806 := u603 20868472 4699 1321839 33 1321806 (by decide) rfl c602_20868472 c602_4699 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c603_4692 : s603 4692 = 32 := by
  rfl
theorem c604_20868472 : s604 20868472 = 1321774 := u604 20868472 4692 1321806 32 1321774 (by decide) rfl c603_20868472 c603_4692 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c604_4688 : s604 4688 = 30 := by
  rfl
theorem c605_20868472 : s605 20868472 = 1321744 := u605 20868472 4688 1321774 30 1321744 (by decide) rfl c604_20868472 c604_4688 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c605_4682 : s605 4682 = 29 := by
  rfl
theorem c606_20868472 : s606 20868472 = 1321715 := u606 20868472 4682 1321744 29 1321715 (by decide) rfl c605_20868472 c605_4682 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c606_4675 : s606 4675 = 27 := by
  rfl
end A247824Checked

namespace A247824Checked
theorem c607_20868472 : s607 20868472 = 1321688 := u607 20868472 4675 1321715 27 1321688 (by decide) rfl c606_20868472 c606_4675 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c607_4657 : s607 4657 = 24 := by
  rfl
theorem c608_20868472 : s608 20868472 = 1321664 := u608 20868472 4657 1321688 24 1321664 (by decide) rfl c607_20868472 c607_4657 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c608_4655 : s608 4655 = 22 := by
  rfl
theorem c609_20868472 : s609 20868472 = 1321642 := u609 20868472 4655 1321664 22 1321642 (by decide) rfl c608_20868472 c608_4655 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c609_4644 : s609 4644 = 19 := by
  rfl
theorem c610_20868472 : s610 20868472 = 1321623 := u610 20868472 4644 1321642 19 1321623 (by decide) rfl c609_20868472 c609_4644 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c610_4630 : s610 4630 = 15 := by
  rfl
theorem c611_20868472 : s611 20868472 = 1321608 := u611 20868472 4630 1321623 15 1321608 (by decide) rfl c610_20868472 c610_4630 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c611_4624 : s611 4624 = 14 := by
  rfl
theorem c612_20868472 : s612 20868472 = 1321594 := u612 20868472 4624 1321608 14 1321594 (by decide) rfl c611_20868472 c611_4624 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c612_4619 : s612 4619 = 12 := by
  rfl
theorem c613_20868472 : s613 20868472 = 1321582 := u613 20868472 4619 1321594 12 1321582 (by decide) rfl c612_20868472 c612_4619 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c613_4617 : s613 4617 = 11 := by
  rfl
theorem c614_20868472 : s614 20868472 = 1321571 := u614 20868472 4617 1321582 11 1321571 (by decide) rfl c613_20868472 c613_4617 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c614_4613 : s614 4613 = 10 := by
  rfl
theorem c615_20868472 : s615 20868472 = 1321561 := u615 20868472 4613 1321571 10 1321561 (by decide) rfl c614_20868472 c614_4613 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c615_4589 : s615 4589 = 6 := by
  rfl
theorem c616_20868472 : s616 20868472 = 1321555 := u616 20868472 4589 1321561 6 1321555 (by decide) rfl c615_20868472 c615_4589 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c616_4587 : s616 4587 = 5 := by
  rfl
theorem c617_20868472 : s617 20868472 = 1321550 := u617 20868472 4587 1321555 5 1321550 (by decide) rfl c616_20868472 c616_4587 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c617_4575 : s617 4575 = 3 := by
  rfl
theorem c618_20868472 : s618 20868472 = 1321547 := u618 20868472 4575 1321550 3 1321547 (by decide) rfl c617_20868472 c617_4575 rfl
set_option maxHeartbeats 2200000 in
set_option maxRecDepth 4096 in
theorem c618_4569 : s618 4569 = 2 := by
  rfl
theorem c619_20868472 : s619 20868472 = 1321545 := u619 20868472 4569 1321547 2 1321545 (by decide) rfl c618_20868472 c618_4569 rfl
end A247824Checked

namespace A247824Checked
def advance (p : Nat) (f : Nat → Nat) (x : Nat) := if x < p then (if x = 0 then 0 else 1) else f x - f (x / p)
theorem pushFold (p : Nat) (ps : List Nat) (f : Nat → Nat) (e : ps.foldr advance id = f) :
    (p::ps).foldr advance id = advance p f :=
  congrArg (advance p) e
def ps0 : List Nat := []
theorem z0 : ps0.foldr advance id = s0 := rfl
def ps1 := 2 :: ps0
theorem z1 : ps1.foldr advance id = s1 := pushFold 2 ps0 s0 z0
def ps2 := 3 :: ps1
theorem z2 : ps2.foldr advance id = s2 := pushFold 3 ps1 s1 z1
def ps3 := 5 :: ps2
theorem z3 : ps3.foldr advance id = s3 := pushFold 5 ps2 s2 z2
def ps4 := 7 :: ps3
theorem z4 : ps4.foldr advance id = s4 := pushFold 7 ps3 s3 z3
def ps5 := 11 :: ps4
theorem z5 : ps5.foldr advance id = s5 := pushFold 11 ps4 s4 z4
def ps6 := 13 :: ps5
theorem z6 : ps6.foldr advance id = s6 := pushFold 13 ps5 s5 z5
def ps7 := 17 :: ps6
theorem z7 : ps7.foldr advance id = s7 := pushFold 17 ps6 s6 z6
def ps8 := 19 :: ps7
theorem z8 : ps8.foldr advance id = s8 := pushFold 19 ps7 s7 z7
def ps9 := 23 :: ps8
theorem z9 : ps9.foldr advance id = s9 := pushFold 23 ps8 s8 z8
def ps10 := 29 :: ps9
theorem z10 : ps10.foldr advance id = s10 := pushFold 29 ps9 s9 z9
def ps11 := 31 :: ps10
theorem z11 : ps11.foldr advance id = s11 := pushFold 31 ps10 s10 z10
def ps12 := 37 :: ps11
theorem z12 : ps12.foldr advance id = s12 := pushFold 37 ps11 s11 z11
def ps13 := 41 :: ps12
theorem z13 : ps13.foldr advance id = s13 := pushFold 41 ps12 s12 z12
def ps14 := 43 :: ps13
theorem z14 : ps14.foldr advance id = s14 := pushFold 43 ps13 s13 z13
def ps15 := 47 :: ps14
theorem z15 : ps15.foldr advance id = s15 := pushFold 47 ps14 s14 z14
def ps16 := 53 :: ps15
theorem z16 : ps16.foldr advance id = s16 := pushFold 53 ps15 s15 z15
def ps17 := 59 :: ps16
theorem z17 : ps17.foldr advance id = s17 := pushFold 59 ps16 s16 z16
def ps18 := 61 :: ps17
theorem z18 : ps18.foldr advance id = s18 := pushFold 61 ps17 s17 z17
def ps19 := 67 :: ps18
theorem z19 : ps19.foldr advance id = s19 := pushFold 67 ps18 s18 z18
def ps20 := 71 :: ps19
theorem z20 : ps20.foldr advance id = s20 := pushFold 71 ps19 s19 z19
def ps21 := 73 :: ps20
theorem z21 : ps21.foldr advance id = s21 := pushFold 73 ps20 s20 z20
def ps22 := 79 :: ps21
theorem z22 : ps22.foldr advance id = s22 := pushFold 79 ps21 s21 z21
def ps23 := 83 :: ps22
theorem z23 : ps23.foldr advance id = s23 := pushFold 83 ps22 s22 z22
def ps24 := 89 :: ps23
theorem z24 : ps24.foldr advance id = s24 := pushFold 89 ps23 s23 z23
def ps25 := 97 :: ps24
theorem z25 : ps25.foldr advance id = s25 := pushFold 97 ps24 s24 z24
def ps26 := 101 :: ps25
theorem z26 : ps26.foldr advance id = s26 := pushFold 101 ps25 s25 z25
def ps27 := 103 :: ps26
theorem z27 : ps27.foldr advance id = s27 := pushFold 103 ps26 s26 z26
def ps28 := 107 :: ps27
theorem z28 : ps28.foldr advance id = s28 := pushFold 107 ps27 s27 z27
def ps29 := 109 :: ps28
theorem z29 : ps29.foldr advance id = s29 := pushFold 109 ps28 s28 z28
def ps30 := 113 :: ps29
theorem z30 : ps30.foldr advance id = s30 := pushFold 113 ps29 s29 z29
def ps31 := 127 :: ps30
theorem z31 : ps31.foldr advance id = s31 := pushFold 127 ps30 s30 z30
def ps32 := 131 :: ps31
theorem z32 : ps32.foldr advance id = s32 := pushFold 131 ps31 s31 z31
def ps33 := 137 :: ps32
theorem z33 : ps33.foldr advance id = s33 := pushFold 137 ps32 s32 z32
def ps34 := 139 :: ps33
theorem z34 : ps34.foldr advance id = s34 := pushFold 139 ps33 s33 z33
def ps35 := 149 :: ps34
theorem z35 : ps35.foldr advance id = s35 := pushFold 149 ps34 s34 z34
def ps36 := 151 :: ps35
theorem z36 : ps36.foldr advance id = s36 := pushFold 151 ps35 s35 z35
def ps37 := 157 :: ps36
theorem z37 : ps37.foldr advance id = s37 := pushFold 157 ps36 s36 z36
def ps38 := 163 :: ps37
theorem z38 : ps38.foldr advance id = s38 := pushFold 163 ps37 s37 z37
def ps39 := 167 :: ps38
theorem z39 : ps39.foldr advance id = s39 := pushFold 167 ps38 s38 z38
def ps40 := 173 :: ps39
theorem z40 : ps40.foldr advance id = s40 := pushFold 173 ps39 s39 z39
def ps41 := 179 :: ps40
theorem z41 : ps41.foldr advance id = s41 := pushFold 179 ps40 s40 z40
def ps42 := 181 :: ps41
theorem z42 : ps42.foldr advance id = s42 := pushFold 181 ps41 s41 z41
def ps43 := 191 :: ps42
theorem z43 : ps43.foldr advance id = s43 := pushFold 191 ps42 s42 z42
def ps44 := 193 :: ps43
theorem z44 : ps44.foldr advance id = s44 := pushFold 193 ps43 s43 z43
def ps45 := 197 :: ps44
theorem z45 : ps45.foldr advance id = s45 := pushFold 197 ps44 s44 z44
def ps46 := 199 :: ps45
theorem z46 : ps46.foldr advance id = s46 := pushFold 199 ps45 s45 z45
def ps47 := 211 :: ps46
theorem z47 : ps47.foldr advance id = s47 := pushFold 211 ps46 s46 z46
def ps48 := 223 :: ps47
theorem z48 : ps48.foldr advance id = s48 := pushFold 223 ps47 s47 z47
def ps49 := 227 :: ps48
theorem z49 : ps49.foldr advance id = s49 := pushFold 227 ps48 s48 z48
def ps50 := 229 :: ps49
theorem z50 : ps50.foldr advance id = s50 := pushFold 229 ps49 s49 z49
def ps51 := 233 :: ps50
theorem z51 : ps51.foldr advance id = s51 := pushFold 233 ps50 s50 z50
def ps52 := 239 :: ps51
theorem z52 : ps52.foldr advance id = s52 := pushFold 239 ps51 s51 z51
def ps53 := 241 :: ps52
theorem z53 : ps53.foldr advance id = s53 := pushFold 241 ps52 s52 z52
def ps54 := 251 :: ps53
theorem z54 : ps54.foldr advance id = s54 := pushFold 251 ps53 s53 z53
def ps55 := 257 :: ps54
theorem z55 : ps55.foldr advance id = s55 := pushFold 257 ps54 s54 z54
def ps56 := 263 :: ps55
theorem z56 : ps56.foldr advance id = s56 := pushFold 263 ps55 s55 z55
def ps57 := 269 :: ps56
theorem z57 : ps57.foldr advance id = s57 := pushFold 269 ps56 s56 z56
def ps58 := 271 :: ps57
theorem z58 : ps58.foldr advance id = s58 := pushFold 271 ps57 s57 z57
def ps59 := 277 :: ps58
theorem z59 : ps59.foldr advance id = s59 := pushFold 277 ps58 s58 z58
def ps60 := 281 :: ps59
theorem z60 : ps60.foldr advance id = s60 := pushFold 281 ps59 s59 z59
def ps61 := 283 :: ps60
theorem z61 : ps61.foldr advance id = s61 := pushFold 283 ps60 s60 z60
def ps62 := 293 :: ps61
theorem z62 : ps62.foldr advance id = s62 := pushFold 293 ps61 s61 z61
def ps63 := 307 :: ps62
theorem z63 : ps63.foldr advance id = s63 := pushFold 307 ps62 s62 z62
def ps64 := 311 :: ps63
theorem z64 : ps64.foldr advance id = s64 := pushFold 311 ps63 s63 z63
def ps65 := 313 :: ps64
theorem z65 : ps65.foldr advance id = s65 := pushFold 313 ps64 s64 z64
def ps66 := 317 :: ps65
theorem z66 : ps66.foldr advance id = s66 := pushFold 317 ps65 s65 z65
def ps67 := 331 :: ps66
theorem z67 : ps67.foldr advance id = s67 := pushFold 331 ps66 s66 z66
def ps68 := 337 :: ps67
theorem z68 : ps68.foldr advance id = s68 := pushFold 337 ps67 s67 z67
def ps69 := 347 :: ps68
theorem z69 : ps69.foldr advance id = s69 := pushFold 347 ps68 s68 z68
def ps70 := 349 :: ps69
theorem z70 : ps70.foldr advance id = s70 := pushFold 349 ps69 s69 z69
def ps71 := 353 :: ps70
theorem z71 : ps71.foldr advance id = s71 := pushFold 353 ps70 s70 z70
def ps72 := 359 :: ps71
theorem z72 : ps72.foldr advance id = s72 := pushFold 359 ps71 s71 z71
def ps73 := 367 :: ps72
theorem z73 : ps73.foldr advance id = s73 := pushFold 367 ps72 s72 z72
def ps74 := 373 :: ps73
theorem z74 : ps74.foldr advance id = s74 := pushFold 373 ps73 s73 z73
def ps75 := 379 :: ps74
theorem z75 : ps75.foldr advance id = s75 := pushFold 379 ps74 s74 z74
def ps76 := 383 :: ps75
theorem z76 : ps76.foldr advance id = s76 := pushFold 383 ps75 s75 z75
def ps77 := 389 :: ps76
theorem z77 : ps77.foldr advance id = s77 := pushFold 389 ps76 s76 z76
def ps78 := 397 :: ps77
theorem z78 : ps78.foldr advance id = s78 := pushFold 397 ps77 s77 z77
def ps79 := 401 :: ps78
theorem z79 : ps79.foldr advance id = s79 := pushFold 401 ps78 s78 z78
def ps80 := 409 :: ps79
theorem z80 : ps80.foldr advance id = s80 := pushFold 409 ps79 s79 z79
def ps81 := 419 :: ps80
theorem z81 : ps81.foldr advance id = s81 := pushFold 419 ps80 s80 z80
def ps82 := 421 :: ps81
theorem z82 : ps82.foldr advance id = s82 := pushFold 421 ps81 s81 z81
def ps83 := 431 :: ps82
theorem z83 : ps83.foldr advance id = s83 := pushFold 431 ps82 s82 z82
def ps84 := 433 :: ps83
theorem z84 : ps84.foldr advance id = s84 := pushFold 433 ps83 s83 z83
def ps85 := 439 :: ps84
theorem z85 : ps85.foldr advance id = s85 := pushFold 439 ps84 s84 z84
def ps86 := 443 :: ps85
theorem z86 : ps86.foldr advance id = s86 := pushFold 443 ps85 s85 z85
def ps87 := 449 :: ps86
theorem z87 : ps87.foldr advance id = s87 := pushFold 449 ps86 s86 z86
def ps88 := 457 :: ps87
theorem z88 : ps88.foldr advance id = s88 := pushFold 457 ps87 s87 z87
def ps89 := 461 :: ps88
theorem z89 : ps89.foldr advance id = s89 := pushFold 461 ps88 s88 z88
def ps90 := 463 :: ps89
theorem z90 : ps90.foldr advance id = s90 := pushFold 463 ps89 s89 z89
def ps91 := 467 :: ps90
theorem z91 : ps91.foldr advance id = s91 := pushFold 467 ps90 s90 z90
def ps92 := 479 :: ps91
theorem z92 : ps92.foldr advance id = s92 := pushFold 479 ps91 s91 z91
def ps93 := 487 :: ps92
theorem z93 : ps93.foldr advance id = s93 := pushFold 487 ps92 s92 z92
def ps94 := 491 :: ps93
theorem z94 : ps94.foldr advance id = s94 := pushFold 491 ps93 s93 z93
def ps95 := 499 :: ps94
theorem z95 : ps95.foldr advance id = s95 := pushFold 499 ps94 s94 z94
def ps96 := 503 :: ps95
theorem z96 : ps96.foldr advance id = s96 := pushFold 503 ps95 s95 z95
def ps97 := 509 :: ps96
theorem z97 : ps97.foldr advance id = s97 := pushFold 509 ps96 s96 z96
def ps98 := 521 :: ps97
theorem z98 : ps98.foldr advance id = s98 := pushFold 521 ps97 s97 z97
def ps99 := 523 :: ps98
theorem z99 : ps99.foldr advance id = s99 := pushFold 523 ps98 s98 z98
def ps100 := 541 :: ps99
theorem z100 : ps100.foldr advance id = s100 := pushFold 541 ps99 s99 z99
def ps101 := 547 :: ps100
theorem z101 : ps101.foldr advance id = s101 := pushFold 547 ps100 s100 z100
def ps102 := 557 :: ps101
theorem z102 : ps102.foldr advance id = s102 := pushFold 557 ps101 s101 z101
def ps103 := 563 :: ps102
theorem z103 : ps103.foldr advance id = s103 := pushFold 563 ps102 s102 z102
def ps104 := 569 :: ps103
theorem z104 : ps104.foldr advance id = s104 := pushFold 569 ps103 s103 z103
def ps105 := 571 :: ps104
theorem z105 : ps105.foldr advance id = s105 := pushFold 571 ps104 s104 z104
def ps106 := 577 :: ps105
theorem z106 : ps106.foldr advance id = s106 := pushFold 577 ps105 s105 z105
def ps107 := 587 :: ps106
theorem z107 : ps107.foldr advance id = s107 := pushFold 587 ps106 s106 z106
def ps108 := 593 :: ps107
theorem z108 : ps108.foldr advance id = s108 := pushFold 593 ps107 s107 z107
def ps109 := 599 :: ps108
theorem z109 : ps109.foldr advance id = s109 := pushFold 599 ps108 s108 z108
def ps110 := 601 :: ps109
theorem z110 : ps110.foldr advance id = s110 := pushFold 601 ps109 s109 z109
def ps111 := 607 :: ps110
theorem z111 : ps111.foldr advance id = s111 := pushFold 607 ps110 s110 z110
def ps112 := 613 :: ps111
theorem z112 : ps112.foldr advance id = s112 := pushFold 613 ps111 s111 z111
def ps113 := 617 :: ps112
theorem z113 : ps113.foldr advance id = s113 := pushFold 617 ps112 s112 z112
def ps114 := 619 :: ps113
theorem z114 : ps114.foldr advance id = s114 := pushFold 619 ps113 s113 z113
def ps115 := 631 :: ps114
theorem z115 : ps115.foldr advance id = s115 := pushFold 631 ps114 s114 z114
def ps116 := 641 :: ps115
theorem z116 : ps116.foldr advance id = s116 := pushFold 641 ps115 s115 z115
def ps117 := 643 :: ps116
theorem z117 : ps117.foldr advance id = s117 := pushFold 643 ps116 s116 z116
def ps118 := 647 :: ps117
theorem z118 : ps118.foldr advance id = s118 := pushFold 647 ps117 s117 z117
def ps119 := 653 :: ps118
theorem z119 : ps119.foldr advance id = s119 := pushFold 653 ps118 s118 z118
def ps120 := 659 :: ps119
theorem z120 : ps120.foldr advance id = s120 := pushFold 659 ps119 s119 z119
def ps121 := 661 :: ps120
theorem z121 : ps121.foldr advance id = s121 := pushFold 661 ps120 s120 z120
def ps122 := 673 :: ps121
theorem z122 : ps122.foldr advance id = s122 := pushFold 673 ps121 s121 z121
def ps123 := 677 :: ps122
theorem z123 : ps123.foldr advance id = s123 := pushFold 677 ps122 s122 z122
def ps124 := 683 :: ps123
theorem z124 : ps124.foldr advance id = s124 := pushFold 683 ps123 s123 z123
def ps125 := 691 :: ps124
theorem z125 : ps125.foldr advance id = s125 := pushFold 691 ps124 s124 z124
def ps126 := 701 :: ps125
theorem z126 : ps126.foldr advance id = s126 := pushFold 701 ps125 s125 z125
def ps127 := 709 :: ps126
theorem z127 : ps127.foldr advance id = s127 := pushFold 709 ps126 s126 z126
def ps128 := 719 :: ps127
theorem z128 : ps128.foldr advance id = s128 := pushFold 719 ps127 s127 z127
def ps129 := 727 :: ps128
theorem z129 : ps129.foldr advance id = s129 := pushFold 727 ps128 s128 z128
def ps130 := 733 :: ps129
theorem z130 : ps130.foldr advance id = s130 := pushFold 733 ps129 s129 z129
def ps131 := 739 :: ps130
theorem z131 : ps131.foldr advance id = s131 := pushFold 739 ps130 s130 z130
def ps132 := 743 :: ps131
theorem z132 : ps132.foldr advance id = s132 := pushFold 743 ps131 s131 z131
def ps133 := 751 :: ps132
theorem z133 : ps133.foldr advance id = s133 := pushFold 751 ps132 s132 z132
def ps134 := 757 :: ps133
theorem z134 : ps134.foldr advance id = s134 := pushFold 757 ps133 s133 z133
def ps135 := 761 :: ps134
theorem z135 : ps135.foldr advance id = s135 := pushFold 761 ps134 s134 z134
def ps136 := 769 :: ps135
theorem z136 : ps136.foldr advance id = s136 := pushFold 769 ps135 s135 z135
def ps137 := 773 :: ps136
theorem z137 : ps137.foldr advance id = s137 := pushFold 773 ps136 s136 z136
def ps138 := 787 :: ps137
theorem z138 : ps138.foldr advance id = s138 := pushFold 787 ps137 s137 z137
def ps139 := 797 :: ps138
theorem z139 : ps139.foldr advance id = s139 := pushFold 797 ps138 s138 z138
def ps140 := 809 :: ps139
theorem z140 : ps140.foldr advance id = s140 := pushFold 809 ps139 s139 z139
def ps141 := 811 :: ps140
theorem z141 : ps141.foldr advance id = s141 := pushFold 811 ps140 s140 z140
def ps142 := 821 :: ps141
theorem z142 : ps142.foldr advance id = s142 := pushFold 821 ps141 s141 z141
def ps143 := 823 :: ps142
theorem z143 : ps143.foldr advance id = s143 := pushFold 823 ps142 s142 z142
def ps144 := 827 :: ps143
theorem z144 : ps144.foldr advance id = s144 := pushFold 827 ps143 s143 z143
def ps145 := 829 :: ps144
theorem z145 : ps145.foldr advance id = s145 := pushFold 829 ps144 s144 z144
def ps146 := 839 :: ps145
theorem z146 : ps146.foldr advance id = s146 := pushFold 839 ps145 s145 z145
def ps147 := 853 :: ps146
theorem z147 : ps147.foldr advance id = s147 := pushFold 853 ps146 s146 z146
def ps148 := 857 :: ps147
theorem z148 : ps148.foldr advance id = s148 := pushFold 857 ps147 s147 z147
def ps149 := 859 :: ps148
theorem z149 : ps149.foldr advance id = s149 := pushFold 859 ps148 s148 z148
def ps150 := 863 :: ps149
theorem z150 : ps150.foldr advance id = s150 := pushFold 863 ps149 s149 z149
def ps151 := 877 :: ps150
theorem z151 : ps151.foldr advance id = s151 := pushFold 877 ps150 s150 z150
def ps152 := 881 :: ps151
theorem z152 : ps152.foldr advance id = s152 := pushFold 881 ps151 s151 z151
def ps153 := 883 :: ps152
theorem z153 : ps153.foldr advance id = s153 := pushFold 883 ps152 s152 z152
def ps154 := 887 :: ps153
theorem z154 : ps154.foldr advance id = s154 := pushFold 887 ps153 s153 z153
def ps155 := 907 :: ps154
theorem z155 : ps155.foldr advance id = s155 := pushFold 907 ps154 s154 z154
def ps156 := 911 :: ps155
theorem z156 : ps156.foldr advance id = s156 := pushFold 911 ps155 s155 z155
def ps157 := 919 :: ps156
theorem z157 : ps157.foldr advance id = s157 := pushFold 919 ps156 s156 z156
def ps158 := 929 :: ps157
theorem z158 : ps158.foldr advance id = s158 := pushFold 929 ps157 s157 z157
def ps159 := 937 :: ps158
theorem z159 : ps159.foldr advance id = s159 := pushFold 937 ps158 s158 z158
def ps160 := 941 :: ps159
theorem z160 : ps160.foldr advance id = s160 := pushFold 941 ps159 s159 z159
def ps161 := 947 :: ps160
theorem z161 : ps161.foldr advance id = s161 := pushFold 947 ps160 s160 z160
def ps162 := 953 :: ps161
theorem z162 : ps162.foldr advance id = s162 := pushFold 953 ps161 s161 z161
def ps163 := 967 :: ps162
theorem z163 : ps163.foldr advance id = s163 := pushFold 967 ps162 s162 z162
def ps164 := 971 :: ps163
theorem z164 : ps164.foldr advance id = s164 := pushFold 971 ps163 s163 z163
def ps165 := 977 :: ps164
theorem z165 : ps165.foldr advance id = s165 := pushFold 977 ps164 s164 z164
def ps166 := 983 :: ps165
theorem z166 : ps166.foldr advance id = s166 := pushFold 983 ps165 s165 z165
def ps167 := 991 :: ps166
theorem z167 : ps167.foldr advance id = s167 := pushFold 991 ps166 s166 z166
def ps168 := 997 :: ps167
theorem z168 : ps168.foldr advance id = s168 := pushFold 997 ps167 s167 z167
def ps169 := 1009 :: ps168
theorem z169 : ps169.foldr advance id = s169 := pushFold 1009 ps168 s168 z168
def ps170 := 1013 :: ps169
theorem z170 : ps170.foldr advance id = s170 := pushFold 1013 ps169 s169 z169
def ps171 := 1019 :: ps170
theorem z171 : ps171.foldr advance id = s171 := pushFold 1019 ps170 s170 z170
def ps172 := 1021 :: ps171
theorem z172 : ps172.foldr advance id = s172 := pushFold 1021 ps171 s171 z171
def ps173 := 1031 :: ps172
theorem z173 : ps173.foldr advance id = s173 := pushFold 1031 ps172 s172 z172
def ps174 := 1033 :: ps173
theorem z174 : ps174.foldr advance id = s174 := pushFold 1033 ps173 s173 z173
def ps175 := 1039 :: ps174
theorem z175 : ps175.foldr advance id = s175 := pushFold 1039 ps174 s174 z174
def ps176 := 1049 :: ps175
theorem z176 : ps176.foldr advance id = s176 := pushFold 1049 ps175 s175 z175
def ps177 := 1051 :: ps176
theorem z177 : ps177.foldr advance id = s177 := pushFold 1051 ps176 s176 z176
def ps178 := 1061 :: ps177
theorem z178 : ps178.foldr advance id = s178 := pushFold 1061 ps177 s177 z177
def ps179 := 1063 :: ps178
theorem z179 : ps179.foldr advance id = s179 := pushFold 1063 ps178 s178 z178
def ps180 := 1069 :: ps179
theorem z180 : ps180.foldr advance id = s180 := pushFold 1069 ps179 s179 z179
def ps181 := 1087 :: ps180
theorem z181 : ps181.foldr advance id = s181 := pushFold 1087 ps180 s180 z180
def ps182 := 1091 :: ps181
theorem z182 : ps182.foldr advance id = s182 := pushFold 1091 ps181 s181 z181
def ps183 := 1093 :: ps182
theorem z183 : ps183.foldr advance id = s183 := pushFold 1093 ps182 s182 z182
def ps184 := 1097 :: ps183
theorem z184 : ps184.foldr advance id = s184 := pushFold 1097 ps183 s183 z183
def ps185 := 1103 :: ps184
theorem z185 : ps185.foldr advance id = s185 := pushFold 1103 ps184 s184 z184
def ps186 := 1109 :: ps185
theorem z186 : ps186.foldr advance id = s186 := pushFold 1109 ps185 s185 z185
def ps187 := 1117 :: ps186
theorem z187 : ps187.foldr advance id = s187 := pushFold 1117 ps186 s186 z186
def ps188 := 1123 :: ps187
theorem z188 : ps188.foldr advance id = s188 := pushFold 1123 ps187 s187 z187
def ps189 := 1129 :: ps188
theorem z189 : ps189.foldr advance id = s189 := pushFold 1129 ps188 s188 z188
def ps190 := 1151 :: ps189
theorem z190 : ps190.foldr advance id = s190 := pushFold 1151 ps189 s189 z189
def ps191 := 1153 :: ps190
theorem z191 : ps191.foldr advance id = s191 := pushFold 1153 ps190 s190 z190
def ps192 := 1163 :: ps191
theorem z192 : ps192.foldr advance id = s192 := pushFold 1163 ps191 s191 z191
def ps193 := 1171 :: ps192
theorem z193 : ps193.foldr advance id = s193 := pushFold 1171 ps192 s192 z192
def ps194 := 1181 :: ps193
theorem z194 : ps194.foldr advance id = s194 := pushFold 1181 ps193 s193 z193
def ps195 := 1187 :: ps194
theorem z195 : ps195.foldr advance id = s195 := pushFold 1187 ps194 s194 z194
def ps196 := 1193 :: ps195
theorem z196 : ps196.foldr advance id = s196 := pushFold 1193 ps195 s195 z195
def ps197 := 1201 :: ps196
theorem z197 : ps197.foldr advance id = s197 := pushFold 1201 ps196 s196 z196
def ps198 := 1213 :: ps197
theorem z198 : ps198.foldr advance id = s198 := pushFold 1213 ps197 s197 z197
def ps199 := 1217 :: ps198
theorem z199 : ps199.foldr advance id = s199 := pushFold 1217 ps198 s198 z198
def ps200 := 1223 :: ps199
theorem z200 : ps200.foldr advance id = s200 := pushFold 1223 ps199 s199 z199
def ps201 := 1229 :: ps200
theorem z201 : ps201.foldr advance id = s201 := pushFold 1229 ps200 s200 z200
def ps202 := 1231 :: ps201
theorem z202 : ps202.foldr advance id = s202 := pushFold 1231 ps201 s201 z201
def ps203 := 1237 :: ps202
theorem z203 : ps203.foldr advance id = s203 := pushFold 1237 ps202 s202 z202
def ps204 := 1249 :: ps203
theorem z204 : ps204.foldr advance id = s204 := pushFold 1249 ps203 s203 z203
def ps205 := 1259 :: ps204
theorem z205 : ps205.foldr advance id = s205 := pushFold 1259 ps204 s204 z204
def ps206 := 1277 :: ps205
theorem z206 : ps206.foldr advance id = s206 := pushFold 1277 ps205 s205 z205
def ps207 := 1279 :: ps206
theorem z207 : ps207.foldr advance id = s207 := pushFold 1279 ps206 s206 z206
def ps208 := 1283 :: ps207
theorem z208 : ps208.foldr advance id = s208 := pushFold 1283 ps207 s207 z207
def ps209 := 1289 :: ps208
theorem z209 : ps209.foldr advance id = s209 := pushFold 1289 ps208 s208 z208
def ps210 := 1291 :: ps209
theorem z210 : ps210.foldr advance id = s210 := pushFold 1291 ps209 s209 z209
def ps211 := 1297 :: ps210
theorem z211 : ps211.foldr advance id = s211 := pushFold 1297 ps210 s210 z210
def ps212 := 1301 :: ps211
theorem z212 : ps212.foldr advance id = s212 := pushFold 1301 ps211 s211 z211
def ps213 := 1303 :: ps212
theorem z213 : ps213.foldr advance id = s213 := pushFold 1303 ps212 s212 z212
def ps214 := 1307 :: ps213
theorem z214 : ps214.foldr advance id = s214 := pushFold 1307 ps213 s213 z213
def ps215 := 1319 :: ps214
theorem z215 : ps215.foldr advance id = s215 := pushFold 1319 ps214 s214 z214
def ps216 := 1321 :: ps215
theorem z216 : ps216.foldr advance id = s216 := pushFold 1321 ps215 s215 z215
def ps217 := 1327 :: ps216
theorem z217 : ps217.foldr advance id = s217 := pushFold 1327 ps216 s216 z216
def ps218 := 1361 :: ps217
theorem z218 : ps218.foldr advance id = s218 := pushFold 1361 ps217 s217 z217
def ps219 := 1367 :: ps218
theorem z219 : ps219.foldr advance id = s219 := pushFold 1367 ps218 s218 z218
def ps220 := 1373 :: ps219
theorem z220 : ps220.foldr advance id = s220 := pushFold 1373 ps219 s219 z219
def ps221 := 1381 :: ps220
theorem z221 : ps221.foldr advance id = s221 := pushFold 1381 ps220 s220 z220
def ps222 := 1399 :: ps221
theorem z222 : ps222.foldr advance id = s222 := pushFold 1399 ps221 s221 z221
def ps223 := 1409 :: ps222
theorem z223 : ps223.foldr advance id = s223 := pushFold 1409 ps222 s222 z222
def ps224 := 1423 :: ps223
theorem z224 : ps224.foldr advance id = s224 := pushFold 1423 ps223 s223 z223
def ps225 := 1427 :: ps224
theorem z225 : ps225.foldr advance id = s225 := pushFold 1427 ps224 s224 z224
def ps226 := 1429 :: ps225
theorem z226 : ps226.foldr advance id = s226 := pushFold 1429 ps225 s225 z225
def ps227 := 1433 :: ps226
theorem z227 : ps227.foldr advance id = s227 := pushFold 1433 ps226 s226 z226
def ps228 := 1439 :: ps227
theorem z228 : ps228.foldr advance id = s228 := pushFold 1439 ps227 s227 z227
def ps229 := 1447 :: ps228
theorem z229 : ps229.foldr advance id = s229 := pushFold 1447 ps228 s228 z228
def ps230 := 1451 :: ps229
theorem z230 : ps230.foldr advance id = s230 := pushFold 1451 ps229 s229 z229
def ps231 := 1453 :: ps230
theorem z231 : ps231.foldr advance id = s231 := pushFold 1453 ps230 s230 z230
def ps232 := 1459 :: ps231
theorem z232 : ps232.foldr advance id = s232 := pushFold 1459 ps231 s231 z231
def ps233 := 1471 :: ps232
theorem z233 : ps233.foldr advance id = s233 := pushFold 1471 ps232 s232 z232
def ps234 := 1481 :: ps233
theorem z234 : ps234.foldr advance id = s234 := pushFold 1481 ps233 s233 z233
def ps235 := 1483 :: ps234
theorem z235 : ps235.foldr advance id = s235 := pushFold 1483 ps234 s234 z234
def ps236 := 1487 :: ps235
theorem z236 : ps236.foldr advance id = s236 := pushFold 1487 ps235 s235 z235
def ps237 := 1489 :: ps236
theorem z237 : ps237.foldr advance id = s237 := pushFold 1489 ps236 s236 z236
def ps238 := 1493 :: ps237
theorem z238 : ps238.foldr advance id = s238 := pushFold 1493 ps237 s237 z237
def ps239 := 1499 :: ps238
theorem z239 : ps239.foldr advance id = s239 := pushFold 1499 ps238 s238 z238
def ps240 := 1511 :: ps239
theorem z240 : ps240.foldr advance id = s240 := pushFold 1511 ps239 s239 z239
def ps241 := 1523 :: ps240
theorem z241 : ps241.foldr advance id = s241 := pushFold 1523 ps240 s240 z240
def ps242 := 1531 :: ps241
theorem z242 : ps242.foldr advance id = s242 := pushFold 1531 ps241 s241 z241
def ps243 := 1543 :: ps242
theorem z243 : ps243.foldr advance id = s243 := pushFold 1543 ps242 s242 z242
def ps244 := 1549 :: ps243
theorem z244 : ps244.foldr advance id = s244 := pushFold 1549 ps243 s243 z243
def ps245 := 1553 :: ps244
theorem z245 : ps245.foldr advance id = s245 := pushFold 1553 ps244 s244 z244
def ps246 := 1559 :: ps245
theorem z246 : ps246.foldr advance id = s246 := pushFold 1559 ps245 s245 z245
def ps247 := 1567 :: ps246
theorem z247 : ps247.foldr advance id = s247 := pushFold 1567 ps246 s246 z246
def ps248 := 1571 :: ps247
theorem z248 : ps248.foldr advance id = s248 := pushFold 1571 ps247 s247 z247
def ps249 := 1579 :: ps248
theorem z249 : ps249.foldr advance id = s249 := pushFold 1579 ps248 s248 z248
def ps250 := 1583 :: ps249
theorem z250 : ps250.foldr advance id = s250 := pushFold 1583 ps249 s249 z249
def ps251 := 1597 :: ps250
theorem z251 : ps251.foldr advance id = s251 := pushFold 1597 ps250 s250 z250
def ps252 := 1601 :: ps251
theorem z252 : ps252.foldr advance id = s252 := pushFold 1601 ps251 s251 z251
def ps253 := 1607 :: ps252
theorem z253 : ps253.foldr advance id = s253 := pushFold 1607 ps252 s252 z252
def ps254 := 1609 :: ps253
theorem z254 : ps254.foldr advance id = s254 := pushFold 1609 ps253 s253 z253
def ps255 := 1613 :: ps254
theorem z255 : ps255.foldr advance id = s255 := pushFold 1613 ps254 s254 z254
def ps256 := 1619 :: ps255
theorem z256 : ps256.foldr advance id = s256 := pushFold 1619 ps255 s255 z255
def ps257 := 1621 :: ps256
theorem z257 : ps257.foldr advance id = s257 := pushFold 1621 ps256 s256 z256
def ps258 := 1627 :: ps257
theorem z258 : ps258.foldr advance id = s258 := pushFold 1627 ps257 s257 z257
def ps259 := 1637 :: ps258
theorem z259 : ps259.foldr advance id = s259 := pushFold 1637 ps258 s258 z258
def ps260 := 1657 :: ps259
theorem z260 : ps260.foldr advance id = s260 := pushFold 1657 ps259 s259 z259
def ps261 := 1663 :: ps260
theorem z261 : ps261.foldr advance id = s261 := pushFold 1663 ps260 s260 z260
def ps262 := 1667 :: ps261
theorem z262 : ps262.foldr advance id = s262 := pushFold 1667 ps261 s261 z261
def ps263 := 1669 :: ps262
theorem z263 : ps263.foldr advance id = s263 := pushFold 1669 ps262 s262 z262
def ps264 := 1693 :: ps263
theorem z264 : ps264.foldr advance id = s264 := pushFold 1693 ps263 s263 z263
def ps265 := 1697 :: ps264
theorem z265 : ps265.foldr advance id = s265 := pushFold 1697 ps264 s264 z264
def ps266 := 1699 :: ps265
theorem z266 : ps266.foldr advance id = s266 := pushFold 1699 ps265 s265 z265
def ps267 := 1709 :: ps266
theorem z267 : ps267.foldr advance id = s267 := pushFold 1709 ps266 s266 z266
def ps268 := 1721 :: ps267
theorem z268 : ps268.foldr advance id = s268 := pushFold 1721 ps267 s267 z267
def ps269 := 1723 :: ps268
theorem z269 : ps269.foldr advance id = s269 := pushFold 1723 ps268 s268 z268
def ps270 := 1733 :: ps269
theorem z270 : ps270.foldr advance id = s270 := pushFold 1733 ps269 s269 z269
def ps271 := 1741 :: ps270
theorem z271 : ps271.foldr advance id = s271 := pushFold 1741 ps270 s270 z270
def ps272 := 1747 :: ps271
theorem z272 : ps272.foldr advance id = s272 := pushFold 1747 ps271 s271 z271
def ps273 := 1753 :: ps272
theorem z273 : ps273.foldr advance id = s273 := pushFold 1753 ps272 s272 z272
def ps274 := 1759 :: ps273
theorem z274 : ps274.foldr advance id = s274 := pushFold 1759 ps273 s273 z273
def ps275 := 1777 :: ps274
theorem z275 : ps275.foldr advance id = s275 := pushFold 1777 ps274 s274 z274
def ps276 := 1783 :: ps275
theorem z276 : ps276.foldr advance id = s276 := pushFold 1783 ps275 s275 z275
def ps277 := 1787 :: ps276
theorem z277 : ps277.foldr advance id = s277 := pushFold 1787 ps276 s276 z276
def ps278 := 1789 :: ps277
theorem z278 : ps278.foldr advance id = s278 := pushFold 1789 ps277 s277 z277
def ps279 := 1801 :: ps278
theorem z279 : ps279.foldr advance id = s279 := pushFold 1801 ps278 s278 z278
def ps280 := 1811 :: ps279
theorem z280 : ps280.foldr advance id = s280 := pushFold 1811 ps279 s279 z279
def ps281 := 1823 :: ps280
theorem z281 : ps281.foldr advance id = s281 := pushFold 1823 ps280 s280 z280
def ps282 := 1831 :: ps281
theorem z282 : ps282.foldr advance id = s282 := pushFold 1831 ps281 s281 z281
def ps283 := 1847 :: ps282
theorem z283 : ps283.foldr advance id = s283 := pushFold 1847 ps282 s282 z282
def ps284 := 1861 :: ps283
theorem z284 : ps284.foldr advance id = s284 := pushFold 1861 ps283 s283 z283
def ps285 := 1867 :: ps284
theorem z285 : ps285.foldr advance id = s285 := pushFold 1867 ps284 s284 z284
def ps286 := 1871 :: ps285
theorem z286 : ps286.foldr advance id = s286 := pushFold 1871 ps285 s285 z285
def ps287 := 1873 :: ps286
theorem z287 : ps287.foldr advance id = s287 := pushFold 1873 ps286 s286 z286
def ps288 := 1877 :: ps287
theorem z288 : ps288.foldr advance id = s288 := pushFold 1877 ps287 s287 z287
def ps289 := 1879 :: ps288
theorem z289 : ps289.foldr advance id = s289 := pushFold 1879 ps288 s288 z288
def ps290 := 1889 :: ps289
theorem z290 : ps290.foldr advance id = s290 := pushFold 1889 ps289 s289 z289
def ps291 := 1901 :: ps290
theorem z291 : ps291.foldr advance id = s291 := pushFold 1901 ps290 s290 z290
def ps292 := 1907 :: ps291
theorem z292 : ps292.foldr advance id = s292 := pushFold 1907 ps291 s291 z291
def ps293 := 1913 :: ps292
theorem z293 : ps293.foldr advance id = s293 := pushFold 1913 ps292 s292 z292
def ps294 := 1931 :: ps293
theorem z294 : ps294.foldr advance id = s294 := pushFold 1931 ps293 s293 z293
def ps295 := 1933 :: ps294
theorem z295 : ps295.foldr advance id = s295 := pushFold 1933 ps294 s294 z294
def ps296 := 1949 :: ps295
theorem z296 : ps296.foldr advance id = s296 := pushFold 1949 ps295 s295 z295
def ps297 := 1951 :: ps296
theorem z297 : ps297.foldr advance id = s297 := pushFold 1951 ps296 s296 z296
def ps298 := 1973 :: ps297
theorem z298 : ps298.foldr advance id = s298 := pushFold 1973 ps297 s297 z297
def ps299 := 1979 :: ps298
theorem z299 : ps299.foldr advance id = s299 := pushFold 1979 ps298 s298 z298
def ps300 := 1987 :: ps299
theorem z300 : ps300.foldr advance id = s300 := pushFold 1987 ps299 s299 z299
def ps301 := 1993 :: ps300
theorem z301 : ps301.foldr advance id = s301 := pushFold 1993 ps300 s300 z300
def ps302 := 1997 :: ps301
theorem z302 : ps302.foldr advance id = s302 := pushFold 1997 ps301 s301 z301
def ps303 := 1999 :: ps302
theorem z303 : ps303.foldr advance id = s303 := pushFold 1999 ps302 s302 z302
def ps304 := 2003 :: ps303
theorem z304 : ps304.foldr advance id = s304 := pushFold 2003 ps303 s303 z303
def ps305 := 2011 :: ps304
theorem z305 : ps305.foldr advance id = s305 := pushFold 2011 ps304 s304 z304
def ps306 := 2017 :: ps305
theorem z306 : ps306.foldr advance id = s306 := pushFold 2017 ps305 s305 z305
def ps307 := 2027 :: ps306
theorem z307 : ps307.foldr advance id = s307 := pushFold 2027 ps306 s306 z306
def ps308 := 2029 :: ps307
theorem z308 : ps308.foldr advance id = s308 := pushFold 2029 ps307 s307 z307
def ps309 := 2039 :: ps308
theorem z309 : ps309.foldr advance id = s309 := pushFold 2039 ps308 s308 z308
def ps310 := 2053 :: ps309
theorem z310 : ps310.foldr advance id = s310 := pushFold 2053 ps309 s309 z309
def ps311 := 2063 :: ps310
theorem z311 : ps311.foldr advance id = s311 := pushFold 2063 ps310 s310 z310
def ps312 := 2069 :: ps311
theorem z312 : ps312.foldr advance id = s312 := pushFold 2069 ps311 s311 z311
def ps313 := 2081 :: ps312
theorem z313 : ps313.foldr advance id = s313 := pushFold 2081 ps312 s312 z312
def ps314 := 2083 :: ps313
theorem z314 : ps314.foldr advance id = s314 := pushFold 2083 ps313 s313 z313
def ps315 := 2087 :: ps314
theorem z315 : ps315.foldr advance id = s315 := pushFold 2087 ps314 s314 z314
def ps316 := 2089 :: ps315
theorem z316 : ps316.foldr advance id = s316 := pushFold 2089 ps315 s315 z315
def ps317 := 2099 :: ps316
theorem z317 : ps317.foldr advance id = s317 := pushFold 2099 ps316 s316 z316
def ps318 := 2111 :: ps317
theorem z318 : ps318.foldr advance id = s318 := pushFold 2111 ps317 s317 z317
def ps319 := 2113 :: ps318
theorem z319 : ps319.foldr advance id = s319 := pushFold 2113 ps318 s318 z318
def ps320 := 2129 :: ps319
theorem z320 : ps320.foldr advance id = s320 := pushFold 2129 ps319 s319 z319
def ps321 := 2131 :: ps320
theorem z321 : ps321.foldr advance id = s321 := pushFold 2131 ps320 s320 z320
def ps322 := 2137 :: ps321
theorem z322 : ps322.foldr advance id = s322 := pushFold 2137 ps321 s321 z321
def ps323 := 2141 :: ps322
theorem z323 : ps323.foldr advance id = s323 := pushFold 2141 ps322 s322 z322
def ps324 := 2143 :: ps323
theorem z324 : ps324.foldr advance id = s324 := pushFold 2143 ps323 s323 z323
def ps325 := 2153 :: ps324
theorem z325 : ps325.foldr advance id = s325 := pushFold 2153 ps324 s324 z324
def ps326 := 2161 :: ps325
theorem z326 : ps326.foldr advance id = s326 := pushFold 2161 ps325 s325 z325
def ps327 := 2179 :: ps326
theorem z327 : ps327.foldr advance id = s327 := pushFold 2179 ps326 s326 z326
def ps328 := 2203 :: ps327
theorem z328 : ps328.foldr advance id = s328 := pushFold 2203 ps327 s327 z327
def ps329 := 2207 :: ps328
theorem z329 : ps329.foldr advance id = s329 := pushFold 2207 ps328 s328 z328
def ps330 := 2213 :: ps329
theorem z330 : ps330.foldr advance id = s330 := pushFold 2213 ps329 s329 z329
def ps331 := 2221 :: ps330
theorem z331 : ps331.foldr advance id = s331 := pushFold 2221 ps330 s330 z330
def ps332 := 2237 :: ps331
theorem z332 : ps332.foldr advance id = s332 := pushFold 2237 ps331 s331 z331
def ps333 := 2239 :: ps332
theorem z333 : ps333.foldr advance id = s333 := pushFold 2239 ps332 s332 z332
def ps334 := 2243 :: ps333
theorem z334 : ps334.foldr advance id = s334 := pushFold 2243 ps333 s333 z333
def ps335 := 2251 :: ps334
theorem z335 : ps335.foldr advance id = s335 := pushFold 2251 ps334 s334 z334
def ps336 := 2267 :: ps335
theorem z336 : ps336.foldr advance id = s336 := pushFold 2267 ps335 s335 z335
def ps337 := 2269 :: ps336
theorem z337 : ps337.foldr advance id = s337 := pushFold 2269 ps336 s336 z336
def ps338 := 2273 :: ps337
theorem z338 : ps338.foldr advance id = s338 := pushFold 2273 ps337 s337 z337
def ps339 := 2281 :: ps338
theorem z339 : ps339.foldr advance id = s339 := pushFold 2281 ps338 s338 z338
def ps340 := 2287 :: ps339
theorem z340 : ps340.foldr advance id = s340 := pushFold 2287 ps339 s339 z339
def ps341 := 2293 :: ps340
theorem z341 : ps341.foldr advance id = s341 := pushFold 2293 ps340 s340 z340
def ps342 := 2297 :: ps341
theorem z342 : ps342.foldr advance id = s342 := pushFold 2297 ps341 s341 z341
def ps343 := 2309 :: ps342
theorem z343 : ps343.foldr advance id = s343 := pushFold 2309 ps342 s342 z342
def ps344 := 2311 :: ps343
theorem z344 : ps344.foldr advance id = s344 := pushFold 2311 ps343 s343 z343
def ps345 := 2333 :: ps344
theorem z345 : ps345.foldr advance id = s345 := pushFold 2333 ps344 s344 z344
def ps346 := 2339 :: ps345
theorem z346 : ps346.foldr advance id = s346 := pushFold 2339 ps345 s345 z345
def ps347 := 2341 :: ps346
theorem z347 : ps347.foldr advance id = s347 := pushFold 2341 ps346 s346 z346
def ps348 := 2347 :: ps347
theorem z348 : ps348.foldr advance id = s348 := pushFold 2347 ps347 s347 z347
def ps349 := 2351 :: ps348
theorem z349 : ps349.foldr advance id = s349 := pushFold 2351 ps348 s348 z348
def ps350 := 2357 :: ps349
theorem z350 : ps350.foldr advance id = s350 := pushFold 2357 ps349 s349 z349
def ps351 := 2371 :: ps350
theorem z351 : ps351.foldr advance id = s351 := pushFold 2371 ps350 s350 z350
def ps352 := 2377 :: ps351
theorem z352 : ps352.foldr advance id = s352 := pushFold 2377 ps351 s351 z351
def ps353 := 2381 :: ps352
theorem z353 : ps353.foldr advance id = s353 := pushFold 2381 ps352 s352 z352
def ps354 := 2383 :: ps353
theorem z354 : ps354.foldr advance id = s354 := pushFold 2383 ps353 s353 z353
def ps355 := 2389 :: ps354
theorem z355 : ps355.foldr advance id = s355 := pushFold 2389 ps354 s354 z354
def ps356 := 2393 :: ps355
theorem z356 : ps356.foldr advance id = s356 := pushFold 2393 ps355 s355 z355
def ps357 := 2399 :: ps356
theorem z357 : ps357.foldr advance id = s357 := pushFold 2399 ps356 s356 z356
def ps358 := 2411 :: ps357
theorem z358 : ps358.foldr advance id = s358 := pushFold 2411 ps357 s357 z357
def ps359 := 2417 :: ps358
theorem z359 : ps359.foldr advance id = s359 := pushFold 2417 ps358 s358 z358
def ps360 := 2423 :: ps359
theorem z360 : ps360.foldr advance id = s360 := pushFold 2423 ps359 s359 z359
def ps361 := 2437 :: ps360
theorem z361 : ps361.foldr advance id = s361 := pushFold 2437 ps360 s360 z360
def ps362 := 2441 :: ps361
theorem z362 : ps362.foldr advance id = s362 := pushFold 2441 ps361 s361 z361
def ps363 := 2447 :: ps362
theorem z363 : ps363.foldr advance id = s363 := pushFold 2447 ps362 s362 z362
def ps364 := 2459 :: ps363
theorem z364 : ps364.foldr advance id = s364 := pushFold 2459 ps363 s363 z363
def ps365 := 2467 :: ps364
theorem z365 : ps365.foldr advance id = s365 := pushFold 2467 ps364 s364 z364
def ps366 := 2473 :: ps365
theorem z366 : ps366.foldr advance id = s366 := pushFold 2473 ps365 s365 z365
def ps367 := 2477 :: ps366
theorem z367 : ps367.foldr advance id = s367 := pushFold 2477 ps366 s366 z366
def ps368 := 2503 :: ps367
theorem z368 : ps368.foldr advance id = s368 := pushFold 2503 ps367 s367 z367
def ps369 := 2521 :: ps368
theorem z369 : ps369.foldr advance id = s369 := pushFold 2521 ps368 s368 z368
def ps370 := 2531 :: ps369
theorem z370 : ps370.foldr advance id = s370 := pushFold 2531 ps369 s369 z369
def ps371 := 2539 :: ps370
theorem z371 : ps371.foldr advance id = s371 := pushFold 2539 ps370 s370 z370
def ps372 := 2543 :: ps371
theorem z372 : ps372.foldr advance id = s372 := pushFold 2543 ps371 s371 z371
def ps373 := 2549 :: ps372
theorem z373 : ps373.foldr advance id = s373 := pushFold 2549 ps372 s372 z372
def ps374 := 2551 :: ps373
theorem z374 : ps374.foldr advance id = s374 := pushFold 2551 ps373 s373 z373
def ps375 := 2557 :: ps374
theorem z375 : ps375.foldr advance id = s375 := pushFold 2557 ps374 s374 z374
def ps376 := 2579 :: ps375
theorem z376 : ps376.foldr advance id = s376 := pushFold 2579 ps375 s375 z375
def ps377 := 2591 :: ps376
theorem z377 : ps377.foldr advance id = s377 := pushFold 2591 ps376 s376 z376
def ps378 := 2593 :: ps377
theorem z378 : ps378.foldr advance id = s378 := pushFold 2593 ps377 s377 z377
def ps379 := 2609 :: ps378
theorem z379 : ps379.foldr advance id = s379 := pushFold 2609 ps378 s378 z378
def ps380 := 2617 :: ps379
theorem z380 : ps380.foldr advance id = s380 := pushFold 2617 ps379 s379 z379
def ps381 := 2621 :: ps380
theorem z381 : ps381.foldr advance id = s381 := pushFold 2621 ps380 s380 z380
def ps382 := 2633 :: ps381
theorem z382 : ps382.foldr advance id = s382 := pushFold 2633 ps381 s381 z381
def ps383 := 2647 :: ps382
theorem z383 : ps383.foldr advance id = s383 := pushFold 2647 ps382 s382 z382
def ps384 := 2657 :: ps383
theorem z384 : ps384.foldr advance id = s384 := pushFold 2657 ps383 s383 z383
def ps385 := 2659 :: ps384
theorem z385 : ps385.foldr advance id = s385 := pushFold 2659 ps384 s384 z384
def ps386 := 2663 :: ps385
theorem z386 : ps386.foldr advance id = s386 := pushFold 2663 ps385 s385 z385
def ps387 := 2671 :: ps386
theorem z387 : ps387.foldr advance id = s387 := pushFold 2671 ps386 s386 z386
def ps388 := 2677 :: ps387
theorem z388 : ps388.foldr advance id = s388 := pushFold 2677 ps387 s387 z387
def ps389 := 2683 :: ps388
theorem z389 : ps389.foldr advance id = s389 := pushFold 2683 ps388 s388 z388
def ps390 := 2687 :: ps389
theorem z390 : ps390.foldr advance id = s390 := pushFold 2687 ps389 s389 z389
def ps391 := 2689 :: ps390
theorem z391 : ps391.foldr advance id = s391 := pushFold 2689 ps390 s390 z390
def ps392 := 2693 :: ps391
theorem z392 : ps392.foldr advance id = s392 := pushFold 2693 ps391 s391 z391
def ps393 := 2699 :: ps392
theorem z393 : ps393.foldr advance id = s393 := pushFold 2699 ps392 s392 z392
def ps394 := 2707 :: ps393
theorem z394 : ps394.foldr advance id = s394 := pushFold 2707 ps393 s393 z393
def ps395 := 2711 :: ps394
theorem z395 : ps395.foldr advance id = s395 := pushFold 2711 ps394 s394 z394
def ps396 := 2713 :: ps395
theorem z396 : ps396.foldr advance id = s396 := pushFold 2713 ps395 s395 z395
def ps397 := 2719 :: ps396
theorem z397 : ps397.foldr advance id = s397 := pushFold 2719 ps396 s396 z396
def ps398 := 2729 :: ps397
theorem z398 : ps398.foldr advance id = s398 := pushFold 2729 ps397 s397 z397
def ps399 := 2731 :: ps398
theorem z399 : ps399.foldr advance id = s399 := pushFold 2731 ps398 s398 z398
def ps400 := 2741 :: ps399
theorem z400 : ps400.foldr advance id = s400 := pushFold 2741 ps399 s399 z399
def ps401 := 2749 :: ps400
theorem z401 : ps401.foldr advance id = s401 := pushFold 2749 ps400 s400 z400
def ps402 := 2753 :: ps401
theorem z402 : ps402.foldr advance id = s402 := pushFold 2753 ps401 s401 z401
def ps403 := 2767 :: ps402
theorem z403 : ps403.foldr advance id = s403 := pushFold 2767 ps402 s402 z402
def ps404 := 2777 :: ps403
theorem z404 : ps404.foldr advance id = s404 := pushFold 2777 ps403 s403 z403
def ps405 := 2789 :: ps404
theorem z405 : ps405.foldr advance id = s405 := pushFold 2789 ps404 s404 z404
def ps406 := 2791 :: ps405
theorem z406 : ps406.foldr advance id = s406 := pushFold 2791 ps405 s405 z405
def ps407 := 2797 :: ps406
theorem z407 : ps407.foldr advance id = s407 := pushFold 2797 ps406 s406 z406
def ps408 := 2801 :: ps407
theorem z408 : ps408.foldr advance id = s408 := pushFold 2801 ps407 s407 z407
def ps409 := 2803 :: ps408
theorem z409 : ps409.foldr advance id = s409 := pushFold 2803 ps408 s408 z408
def ps410 := 2819 :: ps409
theorem z410 : ps410.foldr advance id = s410 := pushFold 2819 ps409 s409 z409
def ps411 := 2833 :: ps410
theorem z411 : ps411.foldr advance id = s411 := pushFold 2833 ps410 s410 z410
def ps412 := 2837 :: ps411
theorem z412 : ps412.foldr advance id = s412 := pushFold 2837 ps411 s411 z411
def ps413 := 2843 :: ps412
theorem z413 : ps413.foldr advance id = s413 := pushFold 2843 ps412 s412 z412
def ps414 := 2851 :: ps413
theorem z414 : ps414.foldr advance id = s414 := pushFold 2851 ps413 s413 z413
def ps415 := 2857 :: ps414
theorem z415 : ps415.foldr advance id = s415 := pushFold 2857 ps414 s414 z414
def ps416 := 2861 :: ps415
theorem z416 : ps416.foldr advance id = s416 := pushFold 2861 ps415 s415 z415
def ps417 := 2879 :: ps416
theorem z417 : ps417.foldr advance id = s417 := pushFold 2879 ps416 s416 z416
def ps418 := 2887 :: ps417
theorem z418 : ps418.foldr advance id = s418 := pushFold 2887 ps417 s417 z417
def ps419 := 2897 :: ps418
theorem z419 : ps419.foldr advance id = s419 := pushFold 2897 ps418 s418 z418
def ps420 := 2903 :: ps419
theorem z420 : ps420.foldr advance id = s420 := pushFold 2903 ps419 s419 z419
def ps421 := 2909 :: ps420
theorem z421 : ps421.foldr advance id = s421 := pushFold 2909 ps420 s420 z420
def ps422 := 2917 :: ps421
theorem z422 : ps422.foldr advance id = s422 := pushFold 2917 ps421 s421 z421
def ps423 := 2927 :: ps422
theorem z423 : ps423.foldr advance id = s423 := pushFold 2927 ps422 s422 z422
def ps424 := 2939 :: ps423
theorem z424 : ps424.foldr advance id = s424 := pushFold 2939 ps423 s423 z423
def ps425 := 2953 :: ps424
theorem z425 : ps425.foldr advance id = s425 := pushFold 2953 ps424 s424 z424
def ps426 := 2957 :: ps425
theorem z426 : ps426.foldr advance id = s426 := pushFold 2957 ps425 s425 z425
def ps427 := 2963 :: ps426
theorem z427 : ps427.foldr advance id = s427 := pushFold 2963 ps426 s426 z426
def ps428 := 2969 :: ps427
theorem z428 : ps428.foldr advance id = s428 := pushFold 2969 ps427 s427 z427
def ps429 := 2971 :: ps428
theorem z429 : ps429.foldr advance id = s429 := pushFold 2971 ps428 s428 z428
def ps430 := 2999 :: ps429
theorem z430 : ps430.foldr advance id = s430 := pushFold 2999 ps429 s429 z429
def ps431 := 3001 :: ps430
theorem z431 : ps431.foldr advance id = s431 := pushFold 3001 ps430 s430 z430
def ps432 := 3011 :: ps431
theorem z432 : ps432.foldr advance id = s432 := pushFold 3011 ps431 s431 z431
def ps433 := 3019 :: ps432
theorem z433 : ps433.foldr advance id = s433 := pushFold 3019 ps432 s432 z432
def ps434 := 3023 :: ps433
theorem z434 : ps434.foldr advance id = s434 := pushFold 3023 ps433 s433 z433
def ps435 := 3037 :: ps434
theorem z435 : ps435.foldr advance id = s435 := pushFold 3037 ps434 s434 z434
def ps436 := 3041 :: ps435
theorem z436 : ps436.foldr advance id = s436 := pushFold 3041 ps435 s435 z435
def ps437 := 3049 :: ps436
theorem z437 : ps437.foldr advance id = s437 := pushFold 3049 ps436 s436 z436
def ps438 := 3061 :: ps437
theorem z438 : ps438.foldr advance id = s438 := pushFold 3061 ps437 s437 z437
def ps439 := 3067 :: ps438
theorem z439 : ps439.foldr advance id = s439 := pushFold 3067 ps438 s438 z438
def ps440 := 3079 :: ps439
theorem z440 : ps440.foldr advance id = s440 := pushFold 3079 ps439 s439 z439
def ps441 := 3083 :: ps440
theorem z441 : ps441.foldr advance id = s441 := pushFold 3083 ps440 s440 z440
def ps442 := 3089 :: ps441
theorem z442 : ps442.foldr advance id = s442 := pushFold 3089 ps441 s441 z441
def ps443 := 3109 :: ps442
theorem z443 : ps443.foldr advance id = s443 := pushFold 3109 ps442 s442 z442
def ps444 := 3119 :: ps443
theorem z444 : ps444.foldr advance id = s444 := pushFold 3119 ps443 s443 z443
def ps445 := 3121 :: ps444
theorem z445 : ps445.foldr advance id = s445 := pushFold 3121 ps444 s444 z444
def ps446 := 3137 :: ps445
theorem z446 : ps446.foldr advance id = s446 := pushFold 3137 ps445 s445 z445
def ps447 := 3163 :: ps446
theorem z447 : ps447.foldr advance id = s447 := pushFold 3163 ps446 s446 z446
def ps448 := 3167 :: ps447
theorem z448 : ps448.foldr advance id = s448 := pushFold 3167 ps447 s447 z447
def ps449 := 3169 :: ps448
theorem z449 : ps449.foldr advance id = s449 := pushFold 3169 ps448 s448 z448
def ps450 := 3181 :: ps449
theorem z450 : ps450.foldr advance id = s450 := pushFold 3181 ps449 s449 z449
def ps451 := 3187 :: ps450
theorem z451 : ps451.foldr advance id = s451 := pushFold 3187 ps450 s450 z450
def ps452 := 3191 :: ps451
theorem z452 : ps452.foldr advance id = s452 := pushFold 3191 ps451 s451 z451
def ps453 := 3203 :: ps452
theorem z453 : ps453.foldr advance id = s453 := pushFold 3203 ps452 s452 z452
def ps454 := 3209 :: ps453
theorem z454 : ps454.foldr advance id = s454 := pushFold 3209 ps453 s453 z453
def ps455 := 3217 :: ps454
theorem z455 : ps455.foldr advance id = s455 := pushFold 3217 ps454 s454 z454
def ps456 := 3221 :: ps455
theorem z456 : ps456.foldr advance id = s456 := pushFold 3221 ps455 s455 z455
def ps457 := 3229 :: ps456
theorem z457 : ps457.foldr advance id = s457 := pushFold 3229 ps456 s456 z456
def ps458 := 3251 :: ps457
theorem z458 : ps458.foldr advance id = s458 := pushFold 3251 ps457 s457 z457
def ps459 := 3253 :: ps458
theorem z459 : ps459.foldr advance id = s459 := pushFold 3253 ps458 s458 z458
def ps460 := 3257 :: ps459
theorem z460 : ps460.foldr advance id = s460 := pushFold 3257 ps459 s459 z459
def ps461 := 3259 :: ps460
theorem z461 : ps461.foldr advance id = s461 := pushFold 3259 ps460 s460 z460
def ps462 := 3271 :: ps461
theorem z462 : ps462.foldr advance id = s462 := pushFold 3271 ps461 s461 z461
def ps463 := 3299 :: ps462
theorem z463 : ps463.foldr advance id = s463 := pushFold 3299 ps462 s462 z462
def ps464 := 3301 :: ps463
theorem z464 : ps464.foldr advance id = s464 := pushFold 3301 ps463 s463 z463
def ps465 := 3307 :: ps464
theorem z465 : ps465.foldr advance id = s465 := pushFold 3307 ps464 s464 z464
def ps466 := 3313 :: ps465
theorem z466 : ps466.foldr advance id = s466 := pushFold 3313 ps465 s465 z465
def ps467 := 3319 :: ps466
theorem z467 : ps467.foldr advance id = s467 := pushFold 3319 ps466 s466 z466
def ps468 := 3323 :: ps467
theorem z468 : ps468.foldr advance id = s468 := pushFold 3323 ps467 s467 z467
def ps469 := 3329 :: ps468
theorem z469 : ps469.foldr advance id = s469 := pushFold 3329 ps468 s468 z468
def ps470 := 3331 :: ps469
theorem z470 : ps470.foldr advance id = s470 := pushFold 3331 ps469 s469 z469
def ps471 := 3343 :: ps470
theorem z471 : ps471.foldr advance id = s471 := pushFold 3343 ps470 s470 z470
def ps472 := 3347 :: ps471
theorem z472 : ps472.foldr advance id = s472 := pushFold 3347 ps471 s471 z471
def ps473 := 3359 :: ps472
theorem z473 : ps473.foldr advance id = s473 := pushFold 3359 ps472 s472 z472
def ps474 := 3361 :: ps473
theorem z474 : ps474.foldr advance id = s474 := pushFold 3361 ps473 s473 z473
def ps475 := 3371 :: ps474
theorem z475 : ps475.foldr advance id = s475 := pushFold 3371 ps474 s474 z474
def ps476 := 3373 :: ps475
theorem z476 : ps476.foldr advance id = s476 := pushFold 3373 ps475 s475 z475
def ps477 := 3389 :: ps476
theorem z477 : ps477.foldr advance id = s477 := pushFold 3389 ps476 s476 z476
def ps478 := 3391 :: ps477
theorem z478 : ps478.foldr advance id = s478 := pushFold 3391 ps477 s477 z477
def ps479 := 3407 :: ps478
theorem z479 : ps479.foldr advance id = s479 := pushFold 3407 ps478 s478 z478
def ps480 := 3413 :: ps479
theorem z480 : ps480.foldr advance id = s480 := pushFold 3413 ps479 s479 z479
def ps481 := 3433 :: ps480
theorem z481 : ps481.foldr advance id = s481 := pushFold 3433 ps480 s480 z480
def ps482 := 3449 :: ps481
theorem z482 : ps482.foldr advance id = s482 := pushFold 3449 ps481 s481 z481
def ps483 := 3457 :: ps482
theorem z483 : ps483.foldr advance id = s483 := pushFold 3457 ps482 s482 z482
def ps484 := 3461 :: ps483
theorem z484 : ps484.foldr advance id = s484 := pushFold 3461 ps483 s483 z483
def ps485 := 3463 :: ps484
theorem z485 : ps485.foldr advance id = s485 := pushFold 3463 ps484 s484 z484
def ps486 := 3467 :: ps485
theorem z486 : ps486.foldr advance id = s486 := pushFold 3467 ps485 s485 z485
def ps487 := 3469 :: ps486
theorem z487 : ps487.foldr advance id = s487 := pushFold 3469 ps486 s486 z486
def ps488 := 3491 :: ps487
theorem z488 : ps488.foldr advance id = s488 := pushFold 3491 ps487 s487 z487
def ps489 := 3499 :: ps488
theorem z489 : ps489.foldr advance id = s489 := pushFold 3499 ps488 s488 z488
def ps490 := 3511 :: ps489
theorem z490 : ps490.foldr advance id = s490 := pushFold 3511 ps489 s489 z489
def ps491 := 3517 :: ps490
theorem z491 : ps491.foldr advance id = s491 := pushFold 3517 ps490 s490 z490
def ps492 := 3527 :: ps491
theorem z492 : ps492.foldr advance id = s492 := pushFold 3527 ps491 s491 z491
def ps493 := 3529 :: ps492
theorem z493 : ps493.foldr advance id = s493 := pushFold 3529 ps492 s492 z492
def ps494 := 3533 :: ps493
theorem z494 : ps494.foldr advance id = s494 := pushFold 3533 ps493 s493 z493
def ps495 := 3539 :: ps494
theorem z495 : ps495.foldr advance id = s495 := pushFold 3539 ps494 s494 z494
def ps496 := 3541 :: ps495
theorem z496 : ps496.foldr advance id = s496 := pushFold 3541 ps495 s495 z495
def ps497 := 3547 :: ps496
theorem z497 : ps497.foldr advance id = s497 := pushFold 3547 ps496 s496 z496
def ps498 := 3557 :: ps497
theorem z498 : ps498.foldr advance id = s498 := pushFold 3557 ps497 s497 z497
def ps499 := 3559 :: ps498
theorem z499 : ps499.foldr advance id = s499 := pushFold 3559 ps498 s498 z498
def ps500 := 3571 :: ps499
theorem z500 : ps500.foldr advance id = s500 := pushFold 3571 ps499 s499 z499
def ps501 := 3581 :: ps500
theorem z501 : ps501.foldr advance id = s501 := pushFold 3581 ps500 s500 z500
def ps502 := 3583 :: ps501
theorem z502 : ps502.foldr advance id = s502 := pushFold 3583 ps501 s501 z501
def ps503 := 3593 :: ps502
theorem z503 : ps503.foldr advance id = s503 := pushFold 3593 ps502 s502 z502
def ps504 := 3607 :: ps503
theorem z504 : ps504.foldr advance id = s504 := pushFold 3607 ps503 s503 z503
def ps505 := 3613 :: ps504
theorem z505 : ps505.foldr advance id = s505 := pushFold 3613 ps504 s504 z504
def ps506 := 3617 :: ps505
theorem z506 : ps506.foldr advance id = s506 := pushFold 3617 ps505 s505 z505
def ps507 := 3623 :: ps506
theorem z507 : ps507.foldr advance id = s507 := pushFold 3623 ps506 s506 z506
def ps508 := 3631 :: ps507
theorem z508 : ps508.foldr advance id = s508 := pushFold 3631 ps507 s507 z507
def ps509 := 3637 :: ps508
theorem z509 : ps509.foldr advance id = s509 := pushFold 3637 ps508 s508 z508
def ps510 := 3643 :: ps509
theorem z510 : ps510.foldr advance id = s510 := pushFold 3643 ps509 s509 z509
def ps511 := 3659 :: ps510
theorem z511 : ps511.foldr advance id = s511 := pushFold 3659 ps510 s510 z510
def ps512 := 3671 :: ps511
theorem z512 : ps512.foldr advance id = s512 := pushFold 3671 ps511 s511 z511
def ps513 := 3673 :: ps512
theorem z513 : ps513.foldr advance id = s513 := pushFold 3673 ps512 s512 z512
def ps514 := 3677 :: ps513
theorem z514 : ps514.foldr advance id = s514 := pushFold 3677 ps513 s513 z513
def ps515 := 3691 :: ps514
theorem z515 : ps515.foldr advance id = s515 := pushFold 3691 ps514 s514 z514
def ps516 := 3697 :: ps515
theorem z516 : ps516.foldr advance id = s516 := pushFold 3697 ps515 s515 z515
def ps517 := 3701 :: ps516
theorem z517 : ps517.foldr advance id = s517 := pushFold 3701 ps516 s516 z516
def ps518 := 3709 :: ps517
theorem z518 : ps518.foldr advance id = s518 := pushFold 3709 ps517 s517 z517
def ps519 := 3719 :: ps518
theorem z519 : ps519.foldr advance id = s519 := pushFold 3719 ps518 s518 z518
def ps520 := 3727 :: ps519
theorem z520 : ps520.foldr advance id = s520 := pushFold 3727 ps519 s519 z519
def ps521 := 3733 :: ps520
theorem z521 : ps521.foldr advance id = s521 := pushFold 3733 ps520 s520 z520
def ps522 := 3739 :: ps521
theorem z522 : ps522.foldr advance id = s522 := pushFold 3739 ps521 s521 z521
def ps523 := 3761 :: ps522
theorem z523 : ps523.foldr advance id = s523 := pushFold 3761 ps522 s522 z522
def ps524 := 3767 :: ps523
theorem z524 : ps524.foldr advance id = s524 := pushFold 3767 ps523 s523 z523
def ps525 := 3769 :: ps524
theorem z525 : ps525.foldr advance id = s525 := pushFold 3769 ps524 s524 z524
def ps526 := 3779 :: ps525
theorem z526 : ps526.foldr advance id = s526 := pushFold 3779 ps525 s525 z525
def ps527 := 3793 :: ps526
theorem z527 : ps527.foldr advance id = s527 := pushFold 3793 ps526 s526 z526
def ps528 := 3797 :: ps527
theorem z528 : ps528.foldr advance id = s528 := pushFold 3797 ps527 s527 z527
def ps529 := 3803 :: ps528
theorem z529 : ps529.foldr advance id = s529 := pushFold 3803 ps528 s528 z528
def ps530 := 3821 :: ps529
theorem z530 : ps530.foldr advance id = s530 := pushFold 3821 ps529 s529 z529
def ps531 := 3823 :: ps530
theorem z531 : ps531.foldr advance id = s531 := pushFold 3823 ps530 s530 z530
def ps532 := 3833 :: ps531
theorem z532 : ps532.foldr advance id = s532 := pushFold 3833 ps531 s531 z531
def ps533 := 3847 :: ps532
theorem z533 : ps533.foldr advance id = s533 := pushFold 3847 ps532 s532 z532
def ps534 := 3851 :: ps533
theorem z534 : ps534.foldr advance id = s534 := pushFold 3851 ps533 s533 z533
def ps535 := 3853 :: ps534
theorem z535 : ps535.foldr advance id = s535 := pushFold 3853 ps534 s534 z534
def ps536 := 3863 :: ps535
theorem z536 : ps536.foldr advance id = s536 := pushFold 3863 ps535 s535 z535
def ps537 := 3877 :: ps536
theorem z537 : ps537.foldr advance id = s537 := pushFold 3877 ps536 s536 z536
def ps538 := 3881 :: ps537
theorem z538 : ps538.foldr advance id = s538 := pushFold 3881 ps537 s537 z537
def ps539 := 3889 :: ps538
theorem z539 : ps539.foldr advance id = s539 := pushFold 3889 ps538 s538 z538
def ps540 := 3907 :: ps539
theorem z540 : ps540.foldr advance id = s540 := pushFold 3907 ps539 s539 z539
def ps541 := 3911 :: ps540
theorem z541 : ps541.foldr advance id = s541 := pushFold 3911 ps540 s540 z540
def ps542 := 3917 :: ps541
theorem z542 : ps542.foldr advance id = s542 := pushFold 3917 ps541 s541 z541
def ps543 := 3919 :: ps542
theorem z543 : ps543.foldr advance id = s543 := pushFold 3919 ps542 s542 z542
def ps544 := 3923 :: ps543
theorem z544 : ps544.foldr advance id = s544 := pushFold 3923 ps543 s543 z543
def ps545 := 3929 :: ps544
theorem z545 : ps545.foldr advance id = s545 := pushFold 3929 ps544 s544 z544
def ps546 := 3931 :: ps545
theorem z546 : ps546.foldr advance id = s546 := pushFold 3931 ps545 s545 z545
def ps547 := 3943 :: ps546
theorem z547 : ps547.foldr advance id = s547 := pushFold 3943 ps546 s546 z546
def ps548 := 3947 :: ps547
theorem z548 : ps548.foldr advance id = s548 := pushFold 3947 ps547 s547 z547
def ps549 := 3967 :: ps548
theorem z549 : ps549.foldr advance id = s549 := pushFold 3967 ps548 s548 z548
def ps550 := 3989 :: ps549
theorem z550 : ps550.foldr advance id = s550 := pushFold 3989 ps549 s549 z549
def ps551 := 4001 :: ps550
theorem z551 : ps551.foldr advance id = s551 := pushFold 4001 ps550 s550 z550
def ps552 := 4003 :: ps551
theorem z552 : ps552.foldr advance id = s552 := pushFold 4003 ps551 s551 z551
def ps553 := 4007 :: ps552
theorem z553 : ps553.foldr advance id = s553 := pushFold 4007 ps552 s552 z552
def ps554 := 4013 :: ps553
theorem z554 : ps554.foldr advance id = s554 := pushFold 4013 ps553 s553 z553
def ps555 := 4019 :: ps554
theorem z555 : ps555.foldr advance id = s555 := pushFold 4019 ps554 s554 z554
def ps556 := 4021 :: ps555
theorem z556 : ps556.foldr advance id = s556 := pushFold 4021 ps555 s555 z555
def ps557 := 4027 :: ps556
theorem z557 : ps557.foldr advance id = s557 := pushFold 4027 ps556 s556 z556
def ps558 := 4049 :: ps557
theorem z558 : ps558.foldr advance id = s558 := pushFold 4049 ps557 s557 z557
def ps559 := 4051 :: ps558
theorem z559 : ps559.foldr advance id = s559 := pushFold 4051 ps558 s558 z558
def ps560 := 4057 :: ps559
theorem z560 : ps560.foldr advance id = s560 := pushFold 4057 ps559 s559 z559
def ps561 := 4073 :: ps560
theorem z561 : ps561.foldr advance id = s561 := pushFold 4073 ps560 s560 z560
def ps562 := 4079 :: ps561
theorem z562 : ps562.foldr advance id = s562 := pushFold 4079 ps561 s561 z561
def ps563 := 4091 :: ps562
theorem z563 : ps563.foldr advance id = s563 := pushFold 4091 ps562 s562 z562
def ps564 := 4093 :: ps563
theorem z564 : ps564.foldr advance id = s564 := pushFold 4093 ps563 s563 z563
def ps565 := 4099 :: ps564
theorem z565 : ps565.foldr advance id = s565 := pushFold 4099 ps564 s564 z564
def ps566 := 4111 :: ps565
theorem z566 : ps566.foldr advance id = s566 := pushFold 4111 ps565 s565 z565
def ps567 := 4127 :: ps566
theorem z567 : ps567.foldr advance id = s567 := pushFold 4127 ps566 s566 z566
def ps568 := 4129 :: ps567
theorem z568 : ps568.foldr advance id = s568 := pushFold 4129 ps567 s567 z567
def ps569 := 4133 :: ps568
theorem z569 : ps569.foldr advance id = s569 := pushFold 4133 ps568 s568 z568
def ps570 := 4139 :: ps569
theorem z570 : ps570.foldr advance id = s570 := pushFold 4139 ps569 s569 z569
def ps571 := 4153 :: ps570
theorem z571 : ps571.foldr advance id = s571 := pushFold 4153 ps570 s570 z570
def ps572 := 4157 :: ps571
theorem z572 : ps572.foldr advance id = s572 := pushFold 4157 ps571 s571 z571
def ps573 := 4159 :: ps572
theorem z573 : ps573.foldr advance id = s573 := pushFold 4159 ps572 s572 z572
def ps574 := 4177 :: ps573
theorem z574 : ps574.foldr advance id = s574 := pushFold 4177 ps573 s573 z573
def ps575 := 4201 :: ps574
theorem z575 : ps575.foldr advance id = s575 := pushFold 4201 ps574 s574 z574
def ps576 := 4211 :: ps575
theorem z576 : ps576.foldr advance id = s576 := pushFold 4211 ps575 s575 z575
def ps577 := 4217 :: ps576
theorem z577 : ps577.foldr advance id = s577 := pushFold 4217 ps576 s576 z576
def ps578 := 4219 :: ps577
theorem z578 : ps578.foldr advance id = s578 := pushFold 4219 ps577 s577 z577
def ps579 := 4229 :: ps578
theorem z579 : ps579.foldr advance id = s579 := pushFold 4229 ps578 s578 z578
def ps580 := 4231 :: ps579
theorem z580 : ps580.foldr advance id = s580 := pushFold 4231 ps579 s579 z579
def ps581 := 4241 :: ps580
theorem z581 : ps581.foldr advance id = s581 := pushFold 4241 ps580 s580 z580
def ps582 := 4243 :: ps581
theorem z582 : ps582.foldr advance id = s582 := pushFold 4243 ps581 s581 z581
def ps583 := 4253 :: ps582
theorem z583 : ps583.foldr advance id = s583 := pushFold 4253 ps582 s582 z582
def ps584 := 4259 :: ps583
theorem z584 : ps584.foldr advance id = s584 := pushFold 4259 ps583 s583 z583
def ps585 := 4261 :: ps584
theorem z585 : ps585.foldr advance id = s585 := pushFold 4261 ps584 s584 z584
def ps586 := 4271 :: ps585
theorem z586 : ps586.foldr advance id = s586 := pushFold 4271 ps585 s585 z585
def ps587 := 4273 :: ps586
theorem z587 : ps587.foldr advance id = s587 := pushFold 4273 ps586 s586 z586
def ps588 := 4283 :: ps587
theorem z588 : ps588.foldr advance id = s588 := pushFold 4283 ps587 s587 z587
def ps589 := 4289 :: ps588
theorem z589 : ps589.foldr advance id = s589 := pushFold 4289 ps588 s588 z588
def ps590 := 4297 :: ps589
theorem z590 : ps590.foldr advance id = s590 := pushFold 4297 ps589 s589 z589
def ps591 := 4327 :: ps590
theorem z591 : ps591.foldr advance id = s591 := pushFold 4327 ps590 s590 z590
def ps592 := 4337 :: ps591
theorem z592 : ps592.foldr advance id = s592 := pushFold 4337 ps591 s591 z591
def ps593 := 4339 :: ps592
theorem z593 : ps593.foldr advance id = s593 := pushFold 4339 ps592 s592 z592
def ps594 := 4349 :: ps593
theorem z594 : ps594.foldr advance id = s594 := pushFold 4349 ps593 s593 z593
def ps595 := 4357 :: ps594
theorem z595 : ps595.foldr advance id = s595 := pushFold 4357 ps594 s594 z594
def ps596 := 4363 :: ps595
theorem z596 : ps596.foldr advance id = s596 := pushFold 4363 ps595 s595 z595
def ps597 := 4373 :: ps596
theorem z597 : ps597.foldr advance id = s597 := pushFold 4373 ps596 s596 z596
def ps598 := 4391 :: ps597
theorem z598 : ps598.foldr advance id = s598 := pushFold 4391 ps597 s597 z597
def ps599 := 4397 :: ps598
theorem z599 : ps599.foldr advance id = s599 := pushFold 4397 ps598 s598 z598
def ps600 := 4409 :: ps599
theorem z600 : ps600.foldr advance id = s600 := pushFold 4409 ps599 s599 z599
def ps601 := 4421 :: ps600
theorem z601 : ps601.foldr advance id = s601 := pushFold 4421 ps600 s600 z600
def ps602 := 4423 :: ps601
theorem z602 : ps602.foldr advance id = s602 := pushFold 4423 ps601 s601 z601
def ps603 := 4441 :: ps602
theorem z603 : ps603.foldr advance id = s603 := pushFold 4441 ps602 s602 z602
def ps604 := 4447 :: ps603
theorem z604 : ps604.foldr advance id = s604 := pushFold 4447 ps603 s603 z603
def ps605 := 4451 :: ps604
theorem z605 : ps605.foldr advance id = s605 := pushFold 4451 ps604 s604 z604
def ps606 := 4457 :: ps605
theorem z606 : ps606.foldr advance id = s606 := pushFold 4457 ps605 s605 z605
def ps607 := 4463 :: ps606
theorem z607 : ps607.foldr advance id = s607 := pushFold 4463 ps606 s606 z606
def ps608 := 4481 :: ps607
theorem z608 : ps608.foldr advance id = s608 := pushFold 4481 ps607 s607 z607
def ps609 := 4483 :: ps608
theorem z609 : ps609.foldr advance id = s609 := pushFold 4483 ps608 s608 z608
def ps610 := 4493 :: ps609
theorem z610 : ps610.foldr advance id = s610 := pushFold 4493 ps609 s609 z609
def ps611 := 4507 :: ps610
theorem z611 : ps611.foldr advance id = s611 := pushFold 4507 ps610 s610 z610
def ps612 := 4513 :: ps611
theorem z612 : ps612.foldr advance id = s612 := pushFold 4513 ps611 s611 z611
def ps613 := 4517 :: ps612
theorem z613 : ps613.foldr advance id = s613 := pushFold 4517 ps612 s612 z612
def ps614 := 4519 :: ps613
theorem z614 : ps614.foldr advance id = s614 := pushFold 4519 ps613 s613 z613
def ps615 := 4523 :: ps614
theorem z615 : ps615.foldr advance id = s615 := pushFold 4523 ps614 s614 z614
def ps616 := 4547 :: ps615
theorem z616 : ps616.foldr advance id = s616 := pushFold 4547 ps615 s615 z615
def ps617 := 4549 :: ps616
theorem z617 : ps617.foldr advance id = s617 := pushFold 4549 ps616 s616 z616
def ps618 := 4561 :: ps617
theorem z618 : ps618.foldr advance id = s618 := pushFold 4561 ps617 s617 z617
def ps619 := 4567 :: ps618
theorem z619 : ps619.foldr advance id = s619 := pushFold 4567 ps618 s618 z618
end A247824Checked
namespace A247824Checked
private theorem finish_numbers {v c : ℕ} (hv : v=1321545) (hc : c=619) : v+c=1322164 := by omega
private theorem finish_list (ps : List ℕ) (hf : ps.foldr advance id 20868472 = 1321545) :
    ps.foldr (fun (p : ℕ) (f : ℕ → ℕ) (t : ℕ) =>
      if t < p then (if t = 0 then 0 else 1) else f t - f (t / p)) id 20868472 +
      (Nat.primesLE 4568).card = 1322164 :=
  finish_numbers (v:=ps.foldr advance id 20868472) (c:=(Nat.primesLE 4568).card) hf small_card
set_option maxRecDepth 5000 in
private theorem child_list : primes = ps619 := by rfl
private theorem transfer (ps : List ℕ) (f : ℕ → ℕ) (eq : ps.foldr advance id = f)
    (value : f 20868472 = 1321545) : ps.foldr advance id 20868472 = 1321545 :=
  (congrFun eq 20868472).trans value
set_option maxRecDepth 10000 in
theorem child_value : OMA.R_OeisA247824_conjecture_2_R1_H1_R1.H1 := by
  unfold OMA.R_OeisA247824_conjecture_2_R1_H1_R1.H1
  apply finish_list
  exact transfer _ s619 ((congrArg (fun ps : List ℕ => ps.foldr advance id) (list_cert.trans child_list)).trans z619) c619_20868472
end A247824Checked

theorem OMA.solution : OMA.R_OeisA247824_conjecture_2_R1_H1_R1.H1 :=
  A247824Checked.child_value
