import OMAReductions.R_oeis_a366274_R1
import Mathlib

/-! Verify the small prime-counting range by rational intervals, and use
Dusart's successively stronger bounds for the remaining two ranges. -/

open Finset Real
namespace ExplicitPrimeIntervals

theorem rational_le_log {y : ℝ} (hy : 1 ≤ y) : 2*(y-1)/(y+1) ≤ Real.log y := by
  let f (x : ℝ) := Real.log x - 2*(x-1)/(x+1)
  have df (x : ℝ) (hx : 1 ≤ x) :
      HasDerivAt f ((x-1)^2 / (x*(x+1)^2)) x := by
    have hp : 0 < x := by linarith
    have hs : 0 < x+1 := by linarith
    have dx := Real.hasDerivAt_log hp.ne'
    have dn := ((hasDerivAt_id x).sub_const 1).const_mul (2 : ℝ)
    have dd := (hasDerivAt_id x).add_const 1
    convert dx.sub (dn.div dd hs.ne') using 1 <;>
      first
      | rfl
      | (simp only [id_eq,mul_one]; field_simp [hp.ne',hs.ne'] <;> ring)
  have hm : MonotoneOn f (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro x hx
      exact (df x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (df x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : 1 ≤ x := interior_subset hx
      rw [(df x hx').deriv]
      positivity
  have h := hm (show (1:ℝ) ∈ Set.Ici (1:ℝ) by simp)
    (Set.mem_Ici.mpr hy) hy
  simpa [f,sub_nonneg] using h

theorem dyadic_log_bound {a k : ℕ} (ha : 0 < a) (hq : 2^k ≤ a) :
    let q := (2:ℕ)^k
    let D := 10000000000*(a+q)
    let N := k*6931471803*(a+q) + 2*(a-q)*10000000000
    (N : ℝ) / (D : ℝ) ≤ Real.log a := by
  let q := (2:ℕ)^k
  let D := 10000000000*(a+q)
  let N := k*6931471803*(a+q) + 2*(a-q)*10000000000
  change (N:ℝ)/(D:ℝ) ≤ Real.log a
  have hle : q ≤ a := hq
  have qp : (0:ℝ) < (q:ℝ) := by
    dsimp [q]
    positivity
  have ap : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have aq : (0:ℝ) < (a:ℝ)+(q:ℝ) := by positivity
  have rp : 1 ≤ (a:ℝ)/(q:ℝ) :=
    (le_div_iff₀ qp).mpr (by simpa only [one_mul] using (show (q:ℝ) ≤ (a:ℝ) by exact_mod_cast hle))
  have rat := rational_le_log rp
  have ratio : 2*((a:ℝ)/(q:ℝ)-1)/((a:ℝ)/(q:ℝ)+1) =
      2*((a:ℝ)-(q:ℝ))/((a:ℝ)+(q:ℝ)) := by
    have pc : (a:ℝ)/(q:ℝ)+1 ≠ 0 := by linarith
    field_simp [qp.ne',aq.ne',pc] <;> ring
  rw [ratio,Real.log_div ap.ne' qp.ne'] at rat
  have logs : Real.log (q:ℝ) = (k:ℝ)*Real.log 2 := by
    rw [show (q:ℝ) = (2:ℝ)^k by simp [q], Real.log_pow]
  rw [logs] at rat
  have approx : (6931471803/10000000000 : ℝ) ≤ Real.log 2 := by
    have eq : (6931471803/10000000000 : ℝ) = (0.6931471803 : ℝ) := by norm_num
    rw [eq]
    exact Real.log_two_gt_d9.le
  have mul := mul_le_mul_of_nonneg_left approx (Nat.cast_nonneg k : 0 ≤ (k:ℝ))
  have num : (N:ℝ) = (k:ℝ)*6931471803*((a:ℝ)+(q:ℝ)) +
      2*((a:ℝ)-(q:ℝ))*10000000000 := by
    dsimp [N]
    push_cast [Nat.cast_sub hle]
    rfl
  have den : (D:ℝ) = 10000000000*((a:ℝ)+(q:ℝ)) := by
    dsimp [D]
    push_cast
    rfl
  rw [num,den]
  have split :
      ((k:ℝ)*6931471803*((a:ℝ)+(q:ℝ)) + 2*((a:ℝ)-(q:ℝ))*10000000000) /
        (10000000000*((a:ℝ)+(q:ℝ))) =
      (k:ℝ)*(6931471803/10000000000) + 2*((a:ℝ)-(q:ℝ))/((a:ℝ)+(q:ℝ)) := by
    field_simp [aq.ne'] <;> ring
  rw [split]
  linarith

theorem interval_estimate {a b k c x : ℕ} (ha : 0 < a) (hpower : 2^k ≤ a)
    (many : c ≤ Nat.primeCounting a)
    (certificate :
      let q := (2:ℕ)^k
      let D := 10000000000*(a+q)
      let N := k*6931471803*(a+q) + 2*(a-q)*10000000000
      0 < N ∧ b*D*(N+D) ≤ c*N^2)
    (left : a ≤ x) (right : x ≤ b) :
    (x:ℝ)/Real.log x*(1+1/Real.log x) ≤ (Nat.primeCounting x : ℝ) := by
  let q := (2:ℕ)^k
  let D := 10000000000*(a+q)
  let N := k*6931471803*(a+q) + 2*(a-q)*10000000000
  let L := (N:ℝ)/(D:ℝ)
  change 0 < N ∧ b*D*(N+D) ≤ c*N^2 at certificate
  obtain ⟨hn,arithmetic⟩ := certificate
  have np : 0 < (N:ℝ) := by exact_mod_cast hn
  have dp : 0 < (D:ℝ) := by
    have dpos : 0 < D := by dsimp [D]; positivity
    exact_mod_cast dpos
  have lp : 0 < L := div_pos np dp
  have lm : L ≤ Real.log x := by
    exact (dyadic_log_bound ha hpower).trans
      (Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast left))
  have lpos : 0 < Real.log x := lp.trans_le lm
  have z1 : (x:ℝ)/Real.log x ≤ (b:ℝ)/L :=
    (div_le_div_of_nonneg_left (Nat.cast_nonneg x) lp lm).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast right) lp.le)
  have z2 : (1:ℝ)+1/Real.log x ≤ 1+1/L := by
    linarith [div_le_div_of_nonneg_left (zero_le_one : (0:ℝ) ≤ 1) lp lm]
  have cmp : (b:ℝ)/L*(1+1/L) ≤ (c:ℝ) := by
    have iden : (b:ℝ)/L*(1+1/L) =
        (b:ℝ)*(D:ℝ)*((N:ℝ)+(D:ℝ))/(N:ℝ)^2 := by
      dsimp [L]
      field_simp [np.ne',dp.ne'] <;> ring
    rw [iden,div_le_iff₀ (sq_pos_of_pos np)]
    exact_mod_cast arithmetic
  have up : (c:ℝ) ≤ (Nat.primeCounting x:ℝ) := by
    exact_mod_cast many.trans (Nat.monotone_primeCounting left)
  exact (mul_le_mul z1 z2 (by positivity) (by positivity)).trans (cmp.trans up)

theorem cover_table (P : ℕ → Prop) (rows : List (ℕ × ℕ × ℕ × ℕ)) (lo hi : ℕ)
    (each : ∀ r ∈ rows, ∀ x, r.1 ≤ x → x ≤ r.2.1 → P x)
    (whole : rows.foldr (fun r next ↦ if next = some (r.2.1+1) then some r.1 else none)
      (some (hi+1)) = some lo) :
    ∀ x, lo ≤ x → x ≤ hi → P x := by
  induction rows generalizing lo with
  | nil =>
    have eq : hi+1 = lo := Option.some.inj whole
    intro x hx hy
    omega
  | cons r rs ih =>
    rw [List.foldr_cons] at whole
    split at whole
    · rename_i next
      have start : r.1 = lo := Option.some.inj whole
      intro x hx hy
      by_cases h : x ≤ r.2.1
      · exact each r (by simp) x (by omega) h
      · exact ih (r.2.1+1) (fun s hs ↦ each s (List.mem_cons_of_mem _ hs)) next x (by omega) hy
    · contradiction

end ExplicitPrimeIntervals

open Finset Real
namespace ExplicitPrimeIntervals

theorem prime_from_small_factor_gcd {p : ℕ} (h2 : 2 ≤ p) (bound : p ≤ 5393)
    (hg : Nat.gcd p 4470115461512684340891257138125051110076800700282905015819080092370422104067183317016903680000000000000000 = 1) : p.Prime := by
  by_contra hp
  have fac := Nat.minFac_prime (show p ≠ 1 by omega)
  have sq := Nat.minFac_sq_le_self (by omega : 0 < p) hp
  have limit : p.minFac ≤ 73 := by
    by_contra! h
    have big := Nat.pow_le_pow_left (show 74 ≤ p.minFac by omega) 2
    omega
  have factorial : (73:ℕ).factorial = 4470115461512684340891257138125051110076800700282905015819080092370422104067183317016903680000000000000000 := by decide
  have div := Nat.dvd_gcd (Nat.minFac_dvd p) (Nat.dvd_factorial fac.pos limit)
  rw [factorial,hg] at div
  exact fac.ne_one (Nat.dvd_one.mp div)


set_option maxRecDepth 12000 in
set_option maxHeartbeats 3500000 in
theorem small_range (x : ℕ) (hlo : 599 ≤ x) (hhi : x ≤ 5393) :
    (x:ℝ)/Real.log x*(1+1/Real.log x) ≤ (Nat.primeCounting x:ℝ) := by
  let ps : List ℕ := [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
    53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
    127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197,
    199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
    283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
    383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
    467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571,
    577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
    661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761,
    769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
    877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977,
    983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069,
    1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187,
    1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291,
    1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427,
    1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511,
    1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613,
    1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733,
    1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867,
    1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987,
    1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087,
    2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213,
    2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333,
    2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423,
    2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557,
    2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687,
    2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789,
    2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903,
    2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037,
    3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181,
    3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307,
    3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413,
    3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539,
    3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643,
    3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769,
    3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907,
    3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019,
    4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139,
    4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261,
    4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409,
    4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523,
    4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657,
    4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793,
    4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937,
    4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039,
    5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179,
    5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323,
    5333
  ]
  let verified (p : ℕ) : Bool :=
    if p ≤ 73 then decide p.Prime
    else decide (2 ≤ p ∧ p ≤ 5393 ∧ Nat.gcd p 4470115461512684340891257138125051110076800700282905015819080092370422104067183317016903680000000000000000 = 1)
  have verifiedPrimes : ps.all verified = true := by
    dsimp +zetaDelta only
    decide +kernel
  have primal (p : ℕ) (hp : p ∈ ps) : p.Prime := by
    have cert := List.all_eq_true.mp verifiedPrimes p hp
    by_cases small : p ≤ 73
    · exact of_decide_eq_true (by simpa only [verified,if_pos small] using cert)
    · have good : 2 ≤ p ∧ p ≤ 5393 ∧ Nat.gcd p 4470115461512684340891257138125051110076800700282905015819080092370422104067183317016903680000000000000000 = 1 :=
        of_decide_eq_true (by simpa only [verified,if_neg small] using cert)
      exact prime_from_small_factor_gcd good.1 good.2.1 good.2.2
  have increasing : ps.IsChain (· < ·) := by
    dsimp +zetaDelta only
    decide +kernel
  have monotone : StrictMono ps.get :=
    ((List.sortedLT_iff_pairwise).mpr (List.isChain_iff_pairwise.mp increasing)).strictMono_get
  have nd : ps.Nodup := monotone.injective.nodup
  have total : ps.length = 706 := by
    dsimp +zetaDelta only
    decide +kernel
  let rows : List (ℕ × ℕ × ℕ × ℕ) := [
    (599, 602, 9, 109), (603, 609, 9, 110), (610, 615, 9, 111), (616, 622, 9, 112),
    (623, 634, 9, 114), (635, 642, 9, 115), (643, 655, 9, 117), (656, 668, 9, 119),
    (669, 682, 9, 121), (683, 701, 9, 124), (702, 716, 9, 126), (717, 724, 9, 127),
    (725, 731, 9, 128), (732, 738, 9, 129), (739, 750, 9, 131), (751, 764, 9, 133),
    (765, 778, 9, 135), (779, 792, 9, 137), (793, 800, 9, 138), (801, 807, 9, 139),
    (808, 808, 9, 139), (809, 814, 9, 140), (815, 821, 9, 141), (822, 828, 9, 142),
    (829, 846, 9, 145), (847, 855, 9, 146), (856, 862, 9, 147), (863, 881, 9, 150),
    (882, 896, 9, 152), (897, 910, 9, 154), (911, 924, 9, 156), (925, 932, 9, 157),
    (933, 939, 9, 158), (940, 946, 9, 159), (947, 959, 9, 161), (960, 967, 9, 162),
    (968, 975, 9, 163), (976, 982, 9, 164), (983, 995, 9, 166), (996, 1003, 9, 167),
    (1004, 1010, 9, 168), (1011, 1017, 9, 169), (1018, 1024, 9, 170), (1025, 1042, 10, 172),
    (1043, 1063, 10, 175), (1064, 1091, 10, 179), (1092, 1113, 10, 182), (1114, 1142, 10, 186),
    (1143, 1165, 10, 189), (1166, 1187, 10, 192), (1188, 1209, 10, 195), (1210, 1225, 10, 197),
    (1226, 1246, 10, 200), (1247, 1268, 10, 203), (1269, 1284, 10, 205), (1285, 1306, 10, 208),
    (1307, 1347, 10, 214), (1348, 1372, 10, 217), (1373, 1395, 10, 220), (1396, 1405, 10, 221),
    (1406, 1413, 10, 222), (1414, 1421, 10, 223), (1422, 1422, 10, 223), (1423, 1428, 10, 224),
    (1429, 1442, 10, 226), (1443, 1457, 10, 228), (1458, 1478, 10, 231), (1479, 1494, 10, 233),
    (1495, 1529, 10, 238), (1530, 1553, 10, 241), (1554, 1583, 10, 245), (1584, 1620, 10, 250),
    (1621, 1671, 10, 257), (1672, 1717, 10, 263), (1718, 1750, 10, 267), (1751, 1788, 10, 272),
    (1789, 1832, 10, 278), (1833, 1865, 10, 282), (1866, 1883, 10, 284), (1884, 1919, 10, 289),
    (1920, 1950, 10, 293), (1951, 1981, 10, 297), (1982, 1998, 10, 299), (1999, 2028, 10, 303),
    (2029, 2065, 10, 308), (2066, 2099, 11, 311), (2100, 2144, 11, 317), (2145, 2198, 11, 324),
    (2199, 2227, 11, 327), (2228, 2258, 11, 331), (2259, 2290, 11, 335), (2291, 2329, 11, 340),
    (2330, 2362, 11, 344), (2363, 2408, 11, 350), (2409, 2463, 11, 357), (2464, 2519, 11, 364),
    (2520, 2555, 11, 368), (2556, 2602, 11, 374), (2603, 2636, 11, 378), (2637, 2669, 11, 382),
    (2670, 2702, 11, 386), (2703, 2755, 11, 393), (2756, 2826, 11, 402), (2827, 2892, 11, 410),
    (2893, 2958, 11, 418), (2959, 3024, 11, 426), (3025, 3090, 11, 434), (3091, 3156, 11, 442),
    (3157, 3193, 11, 446), (3194, 3241, 11, 452), (3242, 3284, 11, 457), (3285, 3325, 11, 462),
    (3326, 3374, 11, 468), (3375, 3438, 11, 476), (3439, 3482, 11, 481), (3483, 3532, 11, 487),
    (3533, 3589, 11, 494), (3590, 3654, 11, 502), (3655, 3721, 11, 510), (3722, 3795, 11, 519),
    (3796, 3863, 11, 527), (3864, 3938, 11, 536), (3939, 4020, 11, 546), (4021, 4104, 11, 556),
    (4105, 4196, 12, 565), (4197, 4275, 12, 574), (4276, 4383, 12, 587), (4384, 4472, 12, 597),
    (4473, 4559, 12, 607), (4560, 4646, 12, 617), (4647, 4733, 12, 627), (4734, 4835, 12, 639),
    (4836, 4932, 12, 650), (4933, 5013, 12, 659), (5014, 5123, 12, 672), (5124, 5237, 12, 685),
    (5238, 5343, 12, 697), (5344, 5393, 12, 706)
  ]
  let rowOK (r : ℕ × ℕ × ℕ × ℕ) : Prop :=
    let a := r.1
    let b := r.2.1
    let k := r.2.2.1
    let c := r.2.2.2
    let q := (2:ℕ)^k
    let D := 10000000000*(a+q)
    let N := k*6931471803*(a+q) + 2*(a-q)*10000000000
    0 < a ∧ q ≤ a ∧ 0 < c ∧ c ≤ 706 ∧ ps[c-1]?.getD (a+1) ≤ a ∧
      0 < N ∧ b*D*(N+D) ≤ c*N^2
  have checked : (rows.all fun r ↦ decide (rowOK r)) = true := by
    dsimp +zetaDelta only
    decide +kernel
  have coverage : rows.foldr
      (fun r next ↦ if next = some (r.2.1+1) then some r.1 else none) (some 5394) =
      some 599 := by
    dsimp +zetaDelta only
    decide +kernel
  have counting (a c : ℕ) (hc : 0 < c) (len : c ≤ ps.length)
      (last : ps[c-1]?.getD (a+1) ≤ a) : c ≤ Nat.primeCounting a := by
    let idx : Fin ps.length := ⟨c-1,by omega⟩
    have opt : ps[c-1]? = some (ps.get idx) :=
      List.getElem?_eq_getElem idx.isLt
    rw [opt,Option.getD_some] at last
    have small (i : Fin c) : ps.get (Fin.castLE len i) ≤ a := by
      have h : Fin.castLE len i ≤ idx := by
        change i.val ≤ c-1
        have := i.isLt
        omega
      exact (monotone.monotone h).trans last
    let f : Fin c ↪ (Nat.primesLE a) := ⟨fun i ↦
      ⟨ps.get (Fin.castLE len i),Nat.mem_primesLE.mpr
        ⟨small i,primal _ (List.get_mem _ _)⟩⟩,
      fun _ _ h ↦ Fin.castLE_injective len (nd.get_inj_iff.mp (congrArg Subtype.val h))⟩
    simpa only [Fintype.card_fin,Fintype.card_coe,Nat.primesLE_card_eq_primeCounting] using
      Fintype.card_le_of_embedding f
  apply cover_table _ rows 599 5393 ?_ coverage x hlo hhi
  intro r hr y left right
  have good : rowOK r := of_decide_eq_true (List.all_eq_true.mp checked r hr)
  obtain ⟨ha,hpow,cpos,hlen,hlast,cert⟩ := good
  exact interval_estimate ha hpow (counting r.1 r.2.2.2 cpos (by simpa only [total] using hlen) hlast) cert left right

end ExplicitPrimeIntervals

open Real
namespace OMA.R_oeis_a366274_R1_H1_R1

/-- The intermediate range of Dusart's bound with denominator log x minus one. -/
def H1 : Prop := ∀ x : ℕ, 5394 ≤ x → x ≤ 88783 →
  (x:ℝ)/(Real.log x-1) ≤ (Nat.primeCounting x:ℝ)

/-- The three-term lower bound in the asymptotic range. -/
def H2 : Prop := ∀ x : ℕ, 88784 ≤ x →
  (x:ℝ)/Real.log x*(1+1/Real.log x+2/(Real.log x)^2) ≤ (Nat.primeCounting x:ℝ)

theorem main : H1 → H2 → OMA.R_oeis_a366274_R1.H1 := by
  intro mid large x hx
  by_cases small : x ≤ 5393
  · exact ExplicitPrimeIntervals.small_range x hx small
  have logFour : 1 < Real.log 4 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]
    norm_num <;> linarith [Real.log_two_gt_d9]
  have hx4 : (4:ℝ) ≤ x := by exact_mod_cast (show 4 ≤ x by omega)
  have hl : 1 < Real.log x := logFour.trans_le (Real.log_le_log (by norm_num) hx4)
  have hp : 0 < Real.log x := by linarith
  by_cases middle : x ≤ 88783
  · have denom : 0 < Real.log x-1 := by linarith
    have diff : (x:ℝ)/(Real.log x-1) -
        (x:ℝ)/Real.log x*(1+1/Real.log x) =
        (x:ℝ)/((Real.log x)^2*(Real.log x-1)) := by
      field_simp [hp.ne',denom.ne'] <;> ring
    have refineBound : (x:ℝ)/Real.log x*(1+1/Real.log x) ≤ (x:ℝ)/(Real.log x-1) := by
      apply sub_nonneg.mp
      rw [diff]
      positivity
    exact refineBound.trans (mid x (by omega) middle)
  · have addBound : (1:ℝ)+1/Real.log x ≤ 1+1/Real.log x+2/(Real.log x)^2 :=
      le_add_of_nonneg_right (by positivity)
    exact (mul_le_mul_of_nonneg_left addBound (by positivity)).trans (large x (by omega))

end OMA.R_oeis_a366274_R1_H1_R1
