import OMAReductions.R_oeis_a366274_R1_H1_R1
import Mathlib

namespace ExplicitPrimeCount

private def trial (n d : ℕ) : ℕ → Bool
  | 0 => true
  | len + 1 => (n % d != 0) && trial n (d + 1) len

private theorem trial_spec (n d len : ℕ) :
    trial n d len = true ↔ ∀ k : ℕ, d ≤ k → k < d + len → ¬ k ∣ n := by
  induction len generalizing d with
  | zero => simp only [trial, add_zero, true_iff]; omega
  | succ len ih =>
    simp only [trial, Bool.and_eq_true, bne_iff_ne, ih, Nat.dvd_iff_mod_eq_zero]
    constructor
    · rintro ⟨h, hs⟩ k lo hi
      by_cases eq : k = d
      · simpa [eq] using h
      · exact hs k (by omega) (by omega)
    · intro h
      exact ⟨h d (by omega) (by omega), fun k lo hi => h k (by omega) (by omega)⟩

private def sieve (n : ℕ) : Bool :=
  decide (2 ≤ n) && trial n 2 (n.sqrt - 1)

private theorem sieve_spec (n : ℕ) : sieve n = true ↔ n.Prime := by
  simp only [sieve, Bool.and_eq_true, decide_eq_true_eq, trial_spec]
  constructor
  · rintro ⟨hn, h⟩
    by_contra notPrime
    have fac := Nat.minFac_prime (show n ≠ 1 by omega)
    have hs := Nat.le_sqrt'.mpr (Nat.minFac_sq_le_self (by omega) notPrime)
    exact h n.minFac fac.two_le (by omega) (Nat.minFac_dvd n)
  · intro hp
    refine ⟨hp.two_le, fun k lo hi => ?_⟩
    have sk := Nat.sqrt_lt_self hp.one_lt
    have : k < n := by omega
    exact (Nat.prime_def_lt'.mp hp).2 k lo this

private def basis : ℕ := 2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210

private theorem basis_eq : primorial 300 = basis := by decide +kernel

private def validPrime (n : ℕ) : Bool :=
  if n ≤ 300 then sieve n else Nat.gcd n basis == 1

private theorem validPrime_spec {n : ℕ} (bound : n ≤ 88783) (h : validPrime n = true) :
    n.Prime := by
  by_cases low : n ≤ 300
  · exact (sieve_spec _).mp (by simpa [validPrime, low] using h)
  · have cop : Nat.gcd n basis = 1 := by simpa [validPrime, low] using h
    by_contra bad
    have fac := Nat.minFac_prime (show n ≠ 1 by omega)
    have small := Nat.minFac_sq_le_self (show 0 < n by omega) bad
    have fd : n.minFac ≤ 300 := by
      by_contra! h
      have sq := Nat.pow_le_pow_left (show 301 ≤ n.minFac by omega) 2
      omega
    have div : n.minFac ∣ Nat.gcd n basis := Nat.dvd_gcd (Nat.minFac_dvd n)
      (basis_eq ▸ fac.dvd_primorial_iff.mpr fd)
    rw [cop] at div
    exact fac.ne_one (Nat.dvd_one.mp div)

private def blockCount (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (if validPrime a then 1 else 0) + blockCount (a + 1) n

private theorem count_ge (a n : ℕ) (h : a + n ≤ 88784) :
    Nat.count Nat.Prime a + blockCount a n ≤ Nat.count Nat.Prime (a + n) := by
  induction n generalizing a with
  | zero => simp [blockCount]
  | succ n ih =>
    have hs := ih (a + 1) (by omega)
    rw [Nat.count_succ] at hs
    rw [show a + (n + 1) = a + 1 + n by omega]
    refine le_trans ?_ hs
    by_cases ha : validPrime a = true
    · simp [blockCount, ha, validPrime_spec (by omega) ha, Nat.add_assoc]
    · rw [blockCount, if_neg ha, zero_add]
      omega

private def denominator (a k : ℕ) : ℕ :=
  3 * 10000000000 * (a + 2 ^ k) ^ 3

private def numerator (a k : ℕ) : ℕ :=
  3 * k * 6931471803 * (a + 2 ^ k) ^ 3 +
    6 * 10000000000 * (a - 2 ^ k) * (a + 2 ^ k) ^ 2 +
    2 * 10000000000 * (a - 2 ^ k) ^ 3

private theorem lower_log {a k : ℕ} (hk : 2 ^ k ≤ a) :
    (numerator a k : ℝ) / (denominator a k : ℝ) ≤ Real.log a := by
  let q : ℝ := (2 : ℝ) ^ k
  let A : ℝ := a
  have hq : 0 < q := by dsimp [q]; positivity
  have hle : q ≤ A := by dsimp [q, A]; exact_mod_cast hk
  have ha : 0 < A := hq.trans_le hle
  have pos : 0 < A + q := by positivity
  let t := (A - q) / (A + q)
  have h0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hle) pos.le
  have h1 : t < 1 := (div_lt_one pos).2 (by linarith)
  have h := Real.sum_range_le_log_div h0 h1 2
  norm_num [Finset.sum_range_succ] at h
  have eq : (1 + t) / (1 - t) = A / q := by
    have den : 1 - t ≠ 0 := by linarith
    dsimp [t] at den ⊢
    field_simp [hq.ne', pos.ne', den]
    <;> ring
  rw [eq, Real.log_div ha.ne' hq.ne'] at h
  have lg : Real.log q = k * Real.log 2 := by dsimp [q]; rw [Real.log_pow]
  rw [lg] at h
  have log2 : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by
    have h' := Real.log_two_gt_d9.le
    norm_num at h' ⊢
    exact h'
  have scaled := mul_le_mul_of_nonneg_left log2 (Nat.cast_nonneg k : 0 ≤ (k : ℝ))
  have identity :
      (numerator a k : ℝ) / (denominator a k : ℝ) =
        (k : ℝ) * (6931471803 / 10000000000) + 2 * (t + t ^ 3 / 3) := by
    unfold numerator denominator
    push_cast [Nat.cast_sub hk]
    have nz : (a : ℝ) + (2 : ℝ) ^ k ≠ 0 := pos.ne'
    dsimp [t, A, q]
    field_simp [nz]
    <;> ring
  rw [identity]
  change _ ≤ Real.log A
  linarith only [h, scaled]

private def table : List (ℕ × ℕ × ℕ × ℕ) := [
  (0, 0, 0, 0), (600, 600, 0, 109), (1200, 1200, 0, 196), (1800, 1800, 0, 278),
  (2400, 2400, 0, 357), (3000, 3000, 0, 430), (3600, 3600, 0, 503), (4200, 4200, 0, 574),
  (4800, 4800, 0, 646), (5394, 5398, 12, 711), (5399, 5406, 12, 712), (5407, 5415, 12, 713),
  (5416, 5424, 12, 714), (5425, 5440, 12, 716), (5441, 5465, 12, 719), (5466, 5484, 12, 721),
  (5485, 5517, 12, 725), (5518, 5544, 12, 728), (5545, 5578, 12, 732), (5579, 5613, 12, 736),
  (5614, 5633, 12, 738), (5634, 5643, 12, 739), (5644, 5659, 12, 741), (5660, 5700, 12, 746),
  (5701, 5743, 12, 751), (5744, 5787, 12, 756), (5788, 5816, 12, 759), (5817, 5851, 12, 763),
  (5852, 5901, 12, 769), (5902, 5961, 12, 776), (5962, 6008, 12, 781), (6009, 6037, 12, 784),
  (6038, 6064, 12, 787), (6065, 6091, 12, 790), (6092, 6133, 12, 795), (6134, 6177, 12, 800),
  (6178, 6213, 12, 804), (6214, 6249, 12, 808), (6250, 6285, 12, 812), (6286, 6328, 12, 817),
  (6329, 6388, 12, 824), (6389, 6465, 12, 833), (6466, 6514, 12, 838), (6515, 6552, 12, 842),
  (6553, 6595, 12, 847), (6596, 6640, 12, 852), (6641, 6677, 12, 856), (6678, 6713, 12, 860),
  (6714, 6764, 12, 866), (6765, 6810, 12, 871), (6811, 6855, 12, 876), (6856, 6900, 12, 881),
  (6901, 6953, 12, 887), (6954, 6999, 12, 892), (7000, 7067, 12, 900), (7068, 7131, 12, 907),
  (7132, 7194, 12, 914), (7195, 7242, 12, 919), (7243, 7303, 12, 926), (7304, 7342, 12, 930),
  (7343, 7387, 12, 935), (7388, 7416, 12, 938), (7417, 7443, 12, 941), (7444, 7455, 12, 942),
  (7456, 7464, 12, 943), (7465, 7481, 12, 945), (7482, 7499, 12, 947), (7500, 7525, 12, 950),
  (7526, 7552, 12, 953), (7553, 7595, 12, 958), (7596, 7656, 12, 965), (7657, 7711, 12, 971),
  (7712, 7774, 12, 978), (7775, 7838, 12, 985), (7839, 7885, 12, 990), (7886, 7947, 12, 997),
  (7948, 8003, 12, 1003), (8004, 8042, 12, 1007), (8043, 8078, 12, 1011), (8079, 8107, 12, 1014),
  (8108, 8150, 12, 1019), (8151, 8188, 12, 1023), (8189, 8224, 12, 1027), (8225, 8263, 13, 1031),
  (8264, 8308, 13, 1036), (8309, 8362, 13, 1042), (8363, 8409, 13, 1047), (8410, 8447, 13, 1051),
  (8448, 8500, 13, 1057), (8501, 8530, 13, 1060), (8531, 8558, 13, 1063), (8559, 8586, 13, 1066),
  (8587, 8614, 13, 1069), (8615, 8641, 13, 1072), (8642, 8677, 13, 1076), (8678, 8714, 13, 1080),
  (8715, 8767, 13, 1086), (8768, 8830, 13, 1093), (8831, 8894, 13, 1100), (8895, 8967, 13, 1108),
  (8968, 9024, 13, 1114), (9025, 9088, 13, 1121), (9089, 9145, 13, 1127), (9146, 9201, 13, 1133),
  (9202, 9264, 13, 1140), (9265, 9329, 13, 1147), (9330, 9394, 13, 1154), (9395, 9459, 13, 1161),
  (9460, 9541, 13, 1170), (9542, 9641, 13, 1181), (9642, 9726, 13, 1190), (9727, 9811, 13, 1199),
  (9812, 9911, 13, 1210), (9912, 10022, 13, 1222), (10023, 10109, 13, 1231), (10110, 10202, 13, 1241),
  (10203, 10304, 13, 1252), (10305, 10415, 13, 1264), (10416, 10511, 13, 1274), (10512, 10614, 13, 1285),
  (10615, 10709, 13, 1295), (10710, 10803, 13, 1305), (10804, 10898, 13, 1315), (10899, 10992, 13, 1325),
  (10993, 11087, 13, 1335), (11088, 11173, 13, 1344), (11174, 11267, 13, 1354), (11268, 11345, 13, 1362),
  (11346, 11421, 13, 1370), (11422, 11488, 13, 1377), (11489, 11563, 13, 1385), (11564, 11630, 13, 1392),
  (11631, 11689, 13, 1398), (11690, 11738, 13, 1403), (11739, 11785, 13, 1408), (11786, 11824, 13, 1412),
  (11825, 11871, 13, 1417), (11872, 11927, 13, 1423), (11928, 11984, 13, 1429), (11985, 12058, 13, 1437),
  (12059, 12125, 13, 1444), (12126, 12201, 13, 1452), (12202, 12260, 13, 1458), (12261, 12326, 13, 1465),
  (12327, 12393, 13, 1472), (12394, 12460, 13, 1479), (12461, 12535, 13, 1487), (12536, 12620, 13, 1496),
  (12621, 12731, 13, 1508), (12732, 12838, 13, 1519), (12839, 12943, 13, 1530), (12944, 13049, 13, 1541),
  (13050, 13180, 13, 1555), (13181, 13306, 13, 1568), (13307, 13414, 13, 1579), (13415, 13521, 13, 1590),
  (13522, 13627, 13, 1601), (13628, 13724, 13, 1611), (13725, 13847, 13, 1624), (13848, 13963, 13, 1636),
  (13964, 14088, 13, 1649), (14089, 14214, 13, 1662), (14215, 14306, 13, 1671), (14307, 14376, 13, 1678),
  (14377, 14436, 13, 1684), (14437, 14520, 13, 1693), (14521, 14590, 13, 1700), (14591, 14675, 13, 1709),
  (14676, 14763, 13, 1718), (14764, 14867, 13, 1729), (14868, 14983, 13, 1741), (14984, 15108, 13, 1754),
  (15109, 15217, 13, 1765), (15218, 15325, 13, 1776), (15326, 15458, 13, 1790), (15459, 15603, 13, 1805),
  (15604, 15741, 13, 1819), (15742, 15904, 13, 1836), (15905, 16070, 13, 1853), (16071, 16237, 13, 1870),
  (16238, 16404, 13, 1887), (16405, 16540, 14, 1900), (16541, 16677, 14, 1914), (16678, 16824, 14, 1929),
  (16825, 16946, 14, 1941), (16947, 17082, 14, 1955), (17083, 17220, 14, 1969), (17221, 17358, 14, 1983),
  (17359, 17488, 14, 1996), (17489, 17643, 14, 2012), (17644, 17793, 14, 2027), (17794, 17942, 14, 2042),
  (17943, 18091, 14, 2057), (18092, 18249, 14, 2073), (18250, 18416, 14, 2090), (18417, 18603, 14, 2109),
  (18604, 18792, 14, 2128), (18793, 18955, 14, 2144), (18956, 19071, 14, 2155), (19072, 19173, 14, 2165),
  (19174, 19264, 14, 2174), (19265, 19363, 14, 2184), (19364, 19436, 14, 2191), (19437, 19551, 14, 2203),
  (19552, 19688, 14, 2217), (19689, 19802, 14, 2228), (19803, 19930, 14, 2241), (19931, 20051, 14, 2253),
  (20052, 20198, 14, 2268), (20199, 20358, 14, 2284), (20359, 20527, 14, 2301), (20528, 20680, 14, 2316),
  (20681, 20814, 14, 2329), (20815, 20963, 14, 2344), (20964, 21105, 14, 2358), (21106, 21246, 14, 2372),
  (21247, 21405, 14, 2388), (21406, 21558, 14, 2403), (21559, 21719, 14, 2419), (21720, 21889, 14, 2436),
  (21890, 22079, 14, 2455), (22080, 22280, 14, 2475), (22281, 22492, 14, 2496), (22493, 22687, 14, 2515),
  (22688, 22871, 14, 2533), (22872, 23082, 14, 2554), (23083, 23322, 14, 2578), (23323, 23548, 14, 2600),
  (23549, 23736, 14, 2618), (23737, 23939, 14, 2638), (23940, 24188, 14, 2663), (24189, 24479, 14, 2692),
  (24480, 24730, 14, 2716), (24731, 24940, 14, 2736), (24941, 25136, 14, 2755), (25137, 25331, 14, 2774),
  (25332, 25527, 14, 2793), (25528, 25713, 14, 2811), (25714, 25916, 14, 2831), (25917, 26112, 14, 2850),
  (26113, 26326, 14, 2871), (26327, 26552, 14, 2893), (26553, 26760, 14, 2913), (26761, 27003, 14, 2937),
  (27004, 27251, 14, 2961), (27252, 27471, 14, 2982), (27472, 27670, 14, 3001), (27671, 27839, 14, 3017),
  (27840, 28070, 14, 3040), (28071, 28298, 14, 3062), (28299, 28508, 14, 3082), (28509, 28697, 14, 3100),
  (28698, 28959, 14, 3126), (28960, 29219, 14, 3151), (29220, 29479, 14, 3176), (29480, 29748, 14, 3202),
  (29749, 29982, 14, 3224), (29983, 30193, 14, 3244), (30194, 30411, 14, 3265), (30412, 30621, 14, 3285),
  (30622, 30802, 14, 3302), (30803, 30989, 14, 3320), (30990, 31196, 14, 3340), (31197, 31424, 14, 3362),
  (31425, 31663, 14, 3385), (31664, 31885, 14, 3406), (31886, 32086, 14, 3425), (32087, 32276, 14, 3443),
  (32277, 32465, 14, 3461), (32466, 32692, 14, 3483), (32693, 32941, 14, 3507), (32942, 33200, 15, 3531),
  (33201, 33481, 15, 3558), (33482, 33756, 15, 3584), (33757, 34078, 15, 3615), (34079, 34386, 15, 3644),
  (34387, 34711, 15, 3675), (34712, 35049, 15, 3707), (35050, 35340, 15, 3734), (35341, 35665, 15, 3765),
  (35666, 35965, 15, 3793), (35966, 36243, 15, 3819), (36244, 36529, 15, 3846), (36530, 36816, 15, 3873),
  (36817, 37141, 15, 3904), (37142, 37480, 15, 3936), (37481, 37792, 15, 3965), (37793, 38130, 15, 3997),
  (38131, 38433, 15, 4025), (38434, 38733, 15, 4053), (38734, 39042, 15, 4082), (39043, 39352, 15, 4111),
  (39353, 39681, 15, 4142), (39682, 40003, 15, 4172), (40004, 40335, 15, 4203), (40336, 40638, 15, 4231),
  (40639, 40949, 15, 4260), (40950, 41250, 15, 4288), (41251, 41580, 15, 4319), (41581, 41885, 15, 4347),
  (41886, 42206, 15, 4377), (42207, 42577, 15, 4412), (42578, 43011, 15, 4453), (43012, 43463, 15, 4495),
  (43464, 43858, 15, 4531), (43859, 44228, 15, 4565), (44229, 44635, 15, 4603), (44636, 45027, 15, 4639),
  (45028, 45437, 15, 4677), (45438, 45829, 15, 4713), (45830, 46200, 15, 4747), (46201, 46560, 15, 4780),
  (46561, 46899, 15, 4811), (46900, 47266, 15, 4845), (47267, 47567, 15, 4872), (47568, 47901, 15, 4903),
  (47902, 48248, 15, 4935), (48249, 48587, 15, 4966), (48588, 48925, 15, 4997), (48926, 49283, 15, 5030),
  (49284, 49663, 15, 5065), (49664, 50045, 15, 5100), (50046, 50438, 15, 5136), (50439, 50861, 15, 5175),
  (50862, 51239, 15, 5209), (51240, 51612, 15, 5243), (51613, 52044, 15, 5283), (52045, 52472, 15, 5322),
  (52473, 52871, 15, 5358), (52872, 53267, 15, 5394), (53268, 53693, 15, 5433), (53694, 54121, 15, 5472),
  (54122, 54541, 15, 5510), (54542, 54980, 15, 5550), (54981, 55411, 15, 5589), (55412, 55831, 15, 5627),
  (55832, 56271, 15, 5667), (56272, 56732, 15, 5709), (56733, 57206, 15, 5752), (57207, 57751, 15, 5802),
  (57752, 58294, 15, 5851), (58295, 58857, 15, 5902), (58858, 59383, 15, 5949), (59384, 59965, 15, 6002),
  (59966, 60543, 15, 6054), (60544, 61101, 15, 6104), (61102, 61658, 15, 6154), (61659, 62215, 15, 6204),
  (62216, 62772, 15, 6254), (62773, 63289, 15, 6300), (63290, 63742, 15, 6340), (63743, 64320, 15, 6393),
  (64321, 64851, 15, 6440), (64852, 65306, 15, 6480), (65307, 65785, 15, 6523), (65786, 66328, 16, 6571),
  (66329, 66807, 16, 6613), (66808, 67299, 16, 6657), (67300, 67833, 16, 6705), (67834, 68413, 16, 6757),
  (68414, 68926, 16, 6802), (68927, 69474, 16, 6851), (69475, 69995, 16, 6897), (69996, 70423, 16, 6934),
  (70424, 70902, 16, 6977), (70903, 71386, 16, 7020), (71387, 71933, 16, 7069), (71934, 72506, 16, 7120),
  (72507, 73103, 16, 7173), (73104, 73722, 16, 7228), (73723, 74314, 16, 7280), (74315, 74893, 16, 7331),
  (74894, 75513, 16, 7386), (75514, 76095, 16, 7437), (76096, 76705, 16, 7491), (76706, 77298, 16, 7543),
  (77299, 77890, 16, 7595), (77891, 78543, 16, 7653), (78544, 79161, 16, 7707), (79162, 79756, 16, 7759),
  (79757, 80349, 16, 7811), (80350, 80994, 16, 7868), (80995, 81644, 16, 7925), (81645, 82316, 16, 7984),
  (82317, 83052, 16, 8049), (83053, 83753, 16, 8110), (83754, 84452, 16, 8171), (84453, 85151, 16, 8232),
  (85152, 85840, 16, 8292), (85841, 86528, 16, 8352), (86529, 87227, 16, 8413), (87228, 87886, 16, 8470),
  (87887, 88615, 16, 8534), (88616, 88783, 16, 8584)]

private def row (i : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  table.getD i (0, 0, 0, 0)

private def countAt (i : ℕ) : ℕ := (row i).2.2.2

private def check (i : ℕ) : Prop :=
  let a := (row i).1
  let b := (row i).2.1
  let k := (row i).2.2.1
  let c := countAt i
  let next := (row (i + 1)).1
  (i + 1 < 394 → a ≤ next ∧ next ≤ 88783 ∧
      countAt (i + 1) ≤ c + blockCount (a + 1) (next - a)) ∧
  (9 ≤ i → 2 ^ k ≤ a ∧ 0 < c ∧ denominator a k < numerator a k ∧
    b * denominator a k ≤ c * (numerator a k - denominator a k))

private instance (i : ℕ) : Decidable (check i) := by
  unfold check
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem table_checked (g : Fin 25) :
    ∀ r : Fin 16, 16 * g.val + r.val < 394 → check (16 * g.val + r.val) := by
  fin_cases g <;> decide +kernel

private theorem checked (i : ℕ) (hi : i < 394) : check i := by
  let g : Fin 25 := ⟨i / 16, by omega⟩
  let r : Fin 16 := ⟨i % 16, by omega⟩
  have eq : 16 * g.val + r.val = i := by dsimp [g, r]; omega
  have h := table_checked g r (eq.symm ▸ hi)
  rwa [eq] at h

private theorem count_certified (i : ℕ) (hi : i < 394) :
    countAt i ≤ Nat.primeCounting (row i).1 := by
  induction i with
  | zero => change 0 ≤ _; exact Nat.zero_le _
  | succ i ih =>
    obtain ⟨le, upper, sum⟩ := (checked i (by omega)).1 hi
    let a := (row i).1
    let b := (row (i + 1)).1
    have eq : a + 1 + (b - a) = b + 1 := by dsimp [a, b]; omega
    have h := count_ge (a + 1) (b - a) (by rw [eq]; dsimp [b]; omega)
    rw [eq] at h
    have lower := ih (by omega)
    change countAt i ≤ Nat.count Nat.Prime (a + 1) at lower
    exact sum.trans ((Nat.add_le_add_right lower _).trans h)

private theorem estimate {a b k c x : ℕ} (hk : 2 ^ k ≤ a) (c0 : 0 < c)
    (logs : denominator a k < numerator a k)
    (cert : b * denominator a k ≤ c * (numerator a k - denominator a k))
    (πbound : c ≤ Nat.primeCounting a) (al : a ≤ x) (xu : x ≤ b) :
    (x : ℝ) / (Real.log x - 1) ≤ (Nat.primeCounting x : ℝ) := by
  let D : ℝ := denominator a k
  let N : ℝ := numerator a k
  have D0 : 0 < D := by dsimp [D, denominator]; positivity
  have HN : D < N := by dsimp [D, N]; exact_mod_cast logs
  have low : N / D ≤ Real.log a := lower_log hk
  have a0 : 0 < (a : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos Nat.zero_lt_two k) hk)
  have alR : (a : ℝ) ≤ x := by exact_mod_cast al
  have lowX := low.trans (Real.log_le_log a0 alR)
  have logpos : 0 < Real.log x - 1 := by
    have h : 1 < N / D := (lt_div_iff₀ D0).2 (by simpa using HN)
    linarith
  have hcert : (b : ℝ) * D ≤ (c : ℝ) * (N - D) := by
    have hh : (((b * denominator a k : ℕ)) : ℝ) ≤
        (((c * (numerator a k - denominator a k) : ℕ)) : ℝ) := by exact_mod_cast cert
    simpa only [Nat.cast_mul, Nat.cast_sub logs.le, D, N] using hh
  have hb : (b : ℝ) ≤ (c : ℝ) * (N / D - 1) := by
    apply le_of_mul_le_mul_right _ D0
    have fact : (c : ℝ) * (N / D - 1) * D = (c : ℝ) * (N - D) := by
      field_simp
      <;> ring
    rwa [fact]
  have cπ : (c : ℝ) ≤ Nat.primeCounting x := by
    exact_mod_cast πbound.trans (Nat.monotone_primeCounting al)
  apply (div_le_iff₀ logpos).2
  calc (x : ℝ) ≤ b := by exact_mod_cast xu
    _ ≤ (c : ℝ) * (N / D - 1) := hb
    _ ≤ (c : ℝ) * (Real.log x - 1) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right lowX _) (Nat.cast_nonneg c)
    _ ≤ _ := mul_le_mul_of_nonneg_right cπ logpos.le

private def intervals : List (ℕ × ℕ × ℕ × ℕ) :=
  List.ofFn (fun i : Fin 385 => row (i.val + 9))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem covers :
    intervals.foldr (fun r next => if next = some (r.2.1 + 1) then some r.1 else none)
      (some (88783 + 1)) = some 5394 := by decide +kernel

theorem result : OMA.R_oeis_a366274_R1_H1_R1.H1 := by
  refine ExplicitPrimeIntervals.cover_table _ intervals 5394 88783 ?_ covers
  intro r hr x al xu
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  let j := i.val + 9
  have hj : j < 394 := by dsimp [j]; omega
  obtain ⟨hk, c0, logs, cert⟩ := (checked j hj).2 (by dsimp [j]; omega)
  exact estimate hk c0 logs cert (count_certified j hj) al xu

end ExplicitPrimeCount

theorem OMA.solution : OMA.R_oeis_a366274_R1_H1_R1.H1 :=
  ExplicitPrimeCount.result