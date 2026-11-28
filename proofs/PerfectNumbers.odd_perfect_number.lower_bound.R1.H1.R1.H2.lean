import OMAReductions.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-!
For each allowed prime p the table gives a lower bound a on its exponent
and a nonnegative weight w. The kernel checks that all smaller positive
exponents violate a divisor-sum constraint, and that
p^29500 ≤ 2^w * p^a * (p-1)^29500. Beyond the table a single monotonicity
argument gives the same estimate with weight zero. Multiplication over the
distinct prime factors bounds the divisor sum using the total weight 23783.
-/

open Nat ArithmeticFunction Finset

namespace OddPerfectEndgame


lemma component_bound {p e k w : ℕ} (hp : p.Prime)
    (h : p ^ k ≤ 2 ^ w * p ^ e * (p - 1) ^ k) :
    (sigma 1 (p ^ e)) ^ k ≤ 2 ^ w * p ^ e * (p ^ e) ^ k := by
  have hs : sigma 1 (p ^ e) * (p - 1) ≤ p ^ e * p := by
    rw [sigma_one_apply_prime_pow hp, geom_sum_mul_of_one_le hp.one_le, pow_succ]
    omega
  refine Nat.le_of_mul_le_mul_right (c := (p - 1) ^ k) ?_ (pow_pos (by have := hp.two_le; omega) _)
  calc
    _ = (sigma 1 (p ^ e) * (p - 1)) ^ k := (mul_pow ..).symm
    _ ≤ (p ^ e * p) ^ k := Nat.pow_le_pow_left hs _
    _ = (p ^ e) ^ k * p ^ k := mul_pow ..
    _ ≤ (p ^ e) ^ k * (2 ^ w * p ^ e * (p - 1) ^ k) := Nat.mul_le_mul_left _ h
    _ = _ := by ac_rfl

lemma combine {n k : ℕ} (hn : n ≠ 0) (weight : ℕ → ℕ)
    (h : ∀ p ∈ n.primeFactors, p ^ k ≤
      2 ^ weight p * p ^ n.factorization p * (p - 1) ^ k) :
    (sigma 1 n) ^ k ≤ 2 ^ (∑ p ∈ n.primeFactors, weight p) * n * n ^ k := by
  have factorSize : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n :=
    prod_factorization_pow_eq_self hn
  have factorSigma : sigma 1 n =
      ∏ p ∈ n.primeFactors, sigma 1 (p ^ n.factorization p) :=
    isMultiplicative_sigma.multiplicative_factorization _ hn
  calc
    _ = ∏ p ∈ n.primeFactors, (sigma 1 (p ^ n.factorization p)) ^ k := by
      rw [factorSigma, Finset.prod_pow]
    _ ≤ ∏ p ∈ n.primeFactors, (2 ^ weight p * p ^ n.factorization p *
          (p ^ n.factorization p) ^ k) :=
      Finset.prod_le_prod' fun p hp => component_bound (prime_of_mem_primeFactors hp) (h p hp)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow,
        factorSize, Finset.prod_pow_eq_pow_sum]

lemma tail_bound {p t k : ℕ} (ht : 2 ≤ t) (hp : t ≤ p)
    (h : t ^ k ≤ t * (t - 1) ^ k) : p ^ k ≤ p * (p - 1) ^ k := by
  have hcross : p * (t - 1) ≤ t * (p - 1) := by
    have ht' : t - 1 + 1 = t := by omega
    have hp' : p - 1 + 1 = p := by omega
    nlinarith only [congrArg (p * ·) ht', congrArg (t * ·) hp', hp]
  refine Nat.le_of_mul_le_mul_right (c := (t - 1) ^ k) ?_ (pow_pos (by omega) _)
  calc
    _ = (p * (t - 1)) ^ k := (mul_pow ..).symm
    _ ≤ (t * (p - 1)) ^ k := Nat.pow_le_pow_left hcross _
    _ = t ^ k * (p - 1) ^ k := mul_pow ..
    _ ≤ (t * (t - 1) ^ k) * (p - 1) ^ k := Nat.mul_le_mul_right _ h
    _ ≤ (p * (t - 1) ^ k) * (p - 1) ^ k := by gcongr
    _ = _ := by ac_rfl

lemma binary_power (k p : ℕ) : npowBinRec k p = p ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [npowBinRec_succ, ih, pow_succ]

lemma tail_certificate : (3607 : ℕ) ^ 29500 ≤ 3607 * (3607-1) ^ 29500 := by
  rw [← binary_power 29500 3607, ← binary_power 29500 (3607-1)]
  decide

def pages : Array (Array (ℕ × ℕ × ℕ)) := #[
  #[(23, 4, 1874), (29, 4, 1475), (37, 6, 1135), (41, 2, 1041), (43, 4, 980),
    (47, 6, 882), (53, 6, 777), (59, 2, 716)],
  #[(67, 4, 616), (71, 2, 592), (73, 1, 581), (79, 4, 517), (83, 4, 491),
    (89, 2, 468), (101, 2, 411), (103, 6, 376), (107, 4, 373), (109, 6, 352),
    (113, 10, 311)],
  #[(131, 2, 313), (137, 6, 270), (139, 4, 279), (149, 4, 258), (151, 6, 240),
    (157, 1, 265), (163, 6, 218), (167, 2, 241), (173, 2, 232), (179, 6, 194),
    (181, 6, 191), (191, 10, 148)],
  #[(193, 4, 191), (197, 4, 187), (199, 4, 184), (211, 10, 125), (223, 6, 145),
    (227, 2, 173), (229, 6, 140), (233, 6, 136), (239, 4, 147), (241, 6, 130),
    (251, 2, 154)],
  #[(257, 6, 118), (263, 4, 130), (269, 6, 111), (271, 6, 109), (277, 1, 146),
    (281, 2, 136), (283, 6, 102), (293, 2, 130), (311, 6, 88), (313, 1, 128),
    (317, 6, 85)],
  #[(337, 4, 93), (347, 4, 90), (349, 6, 72), (353, 4, 87), (359, 4, 85),
    (367, 6, 66), (373, 4, 81), (379, 10, 27), (383, 2, 95)],
  #[(389, 10, 24), (397, 1, 99), (401, 6, 55), (409, 4, 70), (419, 6, 50),
    (421, 1, 93), (431, 6, 47), (433, 6, 46), (439, 4, 62), (443, 6, 44)],
  #[(449, 10, 7), (457, 1, 85), (461, 2, 75), (463, 4, 57), (467, 6, 39),
    (479, 2, 72), (487, 6, 34), (491, 2, 69), (499, 6, 32), (503, 4, 49),
    (509, 2, 66)],
  #[(521, 6, 28), (523, 4, 46), (541, 1, 70), (547, 4, 42), (557, 4, 40),
    (563, 4, 40), (569, 6, 20), (571, 6, 20)],
  #[(577, 6, 19), (587, 2, 55), (593, 2, 54), (599, 6, 16), (601, 6, 16),
    (607, 6, 15), (613, 4, 33), (617, 4, 32), (619, 6, 14), (631, 10, 0)],
  #[(641, 6, 11), (643, 10, 0), (647, 2, 48), (653, 6, 10), (659, 10, 0),
    (661, 6, 9), (673, 1, 54), (677, 2, 45), (683, 4, 25), (691, 6, 6),
    (701, 2, 42)],
  #[(709, 6, 4), (719, 2, 41), (727, 4, 21), (733, 1, 49), (739, 4, 20),
    (743, 2, 39), (751, 6, 0), (757, 1, 47), (761, 2, 37)],
  #[(769, 4, 18), (773, 2, 36), (787, 4, 16), (797, 2, 35), (809, 4, 15),
    (811, 6, 0), (821, 6, 0), (823, 6, 0), (827, 2, 33), (829, 6, 0)],
  #[(839, 2, 32), (853, 6, 0), (857, 2, 31), (859, 4, 11), (863, 6, 0),
    (877, 1, 39), (881, 6, 0), (883, 10, 0), (887, 4, 9)],
  #[(907, 6, 0), (911, 2, 28), (919, 4, 7), (929, 2, 27), (937, 4, 6),
    (941, 6, 0), (947, 4, 6), (953, 2, 25)],
  #[(967, 4, 5), (971, 6, 0), (977, 6, 0), (983, 2, 24), (991, 6, 0),
    (997, 1, 33), (1009, 4, 3), (1013, 2, 23), (1019, 4, 2), (1021, 6, 0)],
  #[(1031, 6, 0), (1033, 4, 2), (1039, 6, 0), (1049, 6, 0), (1051, 10, 0),
    (1061, 6, 0), (1063, 4, 0), (1069, 4, 0), (1087, 6, 0)],
  #[(1091, 2, 19), (1097, 2, 19), (1103, 6, 0), (1109, 6, 0), (1117, 6, 0),
    (1123, 4, 0), (1129, 4, 0), (1151, 10, 0)],
  #[(1153, 1, 27), (1163, 2, 17), (1171, 6, 0), (1181, 2, 16), (1187, 4, 0),
    (1193, 2, 16), (1201, 1, 26), (1213, 1, 25)],
  #[(1217, 2, 15), (1223, 4, 0), (1229, 6, 0), (1231, 6, 0), (1237, 1, 25),
    (1249, 4, 0), (1259, 2, 14), (1277, 4, 0), (1279, 6, 0)],
  #[(1283, 4, 0), (1289, 4, 0), (1291, 6, 0), (1297, 4, 0), (1301, 2, 13),
    (1303, 10, 0), (1307, 6, 0), (1319, 2, 12), (1321, 1, 22), (1327, 4, 0)],
  #[(1361, 6, 0), (1367, 6, 0), (1373, 2, 11), (1381, 1, 21), (1399, 10, 0)],
  #[(1409, 4, 0), (1423, 6, 0), (1427, 2, 9), (1429, 4, 0), (1433, 6, 0),
    (1439, 6, 0), (1447, 4, 0), (1451, 6, 0), (1453, 1, 19), (1459, 6, 0),
    (1471, 10, 0)],
  #[(1481, 6, 0), (1483, 6, 0), (1487, 2, 8), (1489, 6, 0), (1493, 4, 0),
    (1499, 2, 8), (1511, 6, 0), (1523, 6, 0), (1531, 6, 0)],
  #[(1543, 6, 0), (1549, 6, 0), (1553, 2, 7), (1559, 2, 7), (1567, 6, 0),
    (1571, 2, 6), (1579, 4, 0), (1583, 2, 6), (1597, 10, 0)],
  #[(1601, 2, 6), (1607, 4, 0), (1609, 6, 0), (1613, 4, 0), (1619, 4, 0),
    (1621, 1, 16), (1627, 4, 0), (1637, 6, 0), (1657, 1, 15), (1663, 4, 0)],
  #[(1667, 10, 0), (1669, 4, 0), (1693, 4, 0), (1697, 2, 4), (1699, 6, 0),
    (1709, 2, 4), (1721, 6, 0), (1723, 4, 0)],
  #[(1733, 4, 0), (1741, 6, 0), (1747, 6, 0), (1753, 1, 14), (1759, 4, 0),
    (1777, 4, 0), (1783, 6, 0), (1787, 6, 0), (1789, 6, 0)],
  #[(1801, 6, 0), (1811, 2, 2), (1823, 4, 0), (1831, 6, 0), (1847, 2, 2)],
  #[(1861, 6, 0), (1867, 4, 0), (1871, 6, 0), (1873, 1, 12), (1877, 4, 0),
    (1879, 6, 0), (1889, 2, 1), (1901, 6, 0), (1907, 10, 0), (1913, 4, 0)],
  #[(1931, 2, 1), (1933, 1, 12), (1949, 6, 0), (1951, 6, 0), (1973, 2, 0),
    (1979, 4, 0)],
  #[(1987, 4, 0), (1993, 1, 11), (1997, 4, 0), (1999, 4, 0), (2003, 2, 0),
    (2011, 6, 0), (2017, 1, 11), (2027, 6, 0), (2029, 6, 0), (2039, 6, 0)],
  #[(2053, 4, 0), (2063, 4, 0), (2069, 4, 0), (2081, 6, 0), (2083, 6, 0),
    (2087, 4, 0), (2089, 4, 0), (2099, 2, 0), (2111, 6, 0)],
  #[(2113, 4, 0), (2129, 2, 0), (2131, 6, 0), (2137, 1, 9), (2141, 6, 0),
    (2143, 10, 0), (2153, 4, 0), (2161, 1, 9)],
  #[(2179, 4, 0), (2203, 6, 0), (2207, 4, 0), (2213, 4, 0), (2221, 6, 0),
    (2237, 6, 0), (2239, 4, 0)],
  #[(2243, 4, 0), (2251, 6, 0), (2267, 2, 0), (2269, 10, 0), (2273, 2, 0),
    (2281, 6, 0), (2287, 4, 0), (2293, 6, 0), (2297, 10, 0)],
  #[(2309, 2, 0), (2311, 12, 0), (2333, 6, 0), (2339, 2, 0), (2341, 1, 7),
    (2347, 6, 0), (2351, 2, 0), (2357, 2, 0)],
  #[(2371, 6, 0), (2377, 1, 7), (2381, 10, 0), (2383, 4, 0), (2389, 6, 0),
    (2393, 4, 0), (2399, 2, 0), (2411, 2, 0), (2417, 4, 0), (2423, 10, 0)],
  #[(2437, 1, 7), (2441, 2, 0), (2447, 6, 0), (2459, 4, 0), (2467, 6, 0),
    (2473, 1, 6), (2477, 4, 0)],
  #[(2503, 4, 0), (2521, 10, 0), (2531, 6, 0), (2539, 6, 0), (2543, 4, 0),
    (2549, 2, 0), (2551, 6, 0), (2557, 1, 6)],
  #[(2579, 2, 0), (2591, 12, 0), (2593, 1, 6), (2609, 4, 0), (2617, 4, 0),
    (2621, 2, 0)],
  #[(2633, 10, 0), (2647, 4, 0), (2657, 6, 0), (2659, 4, 0), (2663, 2, 0),
    (2671, 10, 0), (2677, 6, 0), (2683, 4, 0), (2687, 6, 0)],
  #[(2689, 10, 0), (2693, 2, 0), (2699, 10, 0), (2707, 4, 0), (2711, 6, 0),
    (2713, 1, 5), (2719, 4, 0), (2729, 2, 0), (2731, 10, 0), (2741, 6, 0),
    (2749, 4, 0)],
  #[(2753, 6, 0), (2767, 6, 0), (2777, 6, 0), (2789, 2, 0), (2791, 6, 0),
    (2797, 1, 4), (2801, 2, 0), (2803, 6, 0)],
  #[(2819, 6, 0), (2833, 4, 0), (2837, 6, 0), (2843, 10, 0), (2851, 6, 0),
    (2857, 1, 4), (2861, 6, 0), (2879, 4, 0)],
  #[(2887, 6, 0), (2897, 2, 0), (2903, 2, 0), (2909, 6, 0), (2917, 1, 4),
    (2927, 2, 0), (2939, 4, 0)],
  #[(2953, 10, 0), (2957, 2, 0), (2963, 6, 0), (2969, 2, 0), (2971, 6, 0),
    (2999, 4, 0), (3001, 6, 0)],
  #[(3011, 2, 0), (3019, 6, 0), (3023, 2, 0), (3037, 4, 0), (3041, 2, 0),
    (3049, 4, 0), (3061, 1, 3), (3067, 10, 0)],
  #[(3079, 4, 0), (3083, 2, 0), (3089, 6, 0), (3109, 4, 0), (3119, 4, 0),
    (3121, 6, 0)],
  #[(3137, 2, 0), (3163, 4, 0), (3167, 4, 0), (3169, 6, 0), (3181, 1, 2),
    (3187, 4, 0), (3191, 2, 0)],
  #[(3203, 4, 0), (3209, 2, 0), (3217, 1, 2), (3221, 2, 0), (3229, 4, 0),
    (3251, 2, 0), (3253, 1, 2), (3257, 6, 0), (3259, 6, 0)],
  #[(3271, 6, 0), (3299, 4, 0), (3301, 6, 0), (3307, 4, 0), (3313, 1, 2),
    (3319, 10, 0), (3323, 2, 0)],
  #[(3329, 4, 0), (3331, 6, 0), (3343, 4, 0), (3347, 2, 0), (3359, 6, 0),
    (3361, 1, 1), (3371, 6, 0), (3373, 4, 0), (3389, 12, 0), (3391, 6, 0)],
  #[(3407, 2, 0), (3413, 6, 0), (3433, 4, 0), (3449, 2, 0)],
  #[(3457, 6, 0), (3461, 10, 0), (3463, 6, 0), (3467, 4, 0), (3469, 6, 0),
    (3491, 2, 0), (3499, 4, 0), (3511, 6, 0), (3517, 1, 1)],
  #[(3527, 4, 0), (3529, 10, 0), (3533, 2, 0), (3539, 4, 0), (3541, 6, 0),
    (3547, 6, 0), (3557, 2, 0), (3559, 4, 0), (3571, 10, 0), (3581, 6, 0),
    (3583, 4, 0)],
  #[(3593, 4, 0)]]

def entry (p : ℕ) : ℕ × ℕ :=
  let page := pages[p / 64]?.getD #[]
  ((page.find? (fun r => r.1 == p)).map Prod.snd).getD (1, 0)

def forbidden : ℕ := 5001473436652898064596041305

def geometric (p e : ℕ) : ℕ := ∑ j ∈ Finset.range (e+1), p ^ j

def admissible (p e : ℕ) : Prop :=
  (geometric p e).Coprime forbidden ∧ ¬ 4 ∣ geometric p e

instance (p e : ℕ) : Decidable (admissible p e) := by unfold admissible; infer_instance

def sieve (p : ℕ) : Bool :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59].all
    (fun d => decide (d ≤ 1 ∨ p ≤ d ∨ ¬ d ∣ p))

lemma sieve_prime {p : ℕ} (hp : p.Prime) : sieve p = true := by
  apply List.all_eq_true.mpr
  intro d _
  apply decide_eq_true
  by_cases hd : d ∣ p
  · rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
  · exact Or.inr (Or.inr hd)

def rowOK (p : ℕ) : Bool :=
  if 2 < p ∧ sieve p = true ∧ p.Coprime forbidden then
    decide (npowBinRec 29500 p ≤ npowBinRec (entry p).2 2 *
      p ^ (entry p).1 * npowBinRec 29500 (p - 1)) &&
      (List.range (entry p).1).all (fun e => decide (e = 0 ∨ ¬ admissible p e))
  else true

def pageOK (q : ℕ) : Bool := (List.range 64).all (fun j => rowOK (64*q+j))

lemma nonzero_weight_small {p : ℕ} (h : 3648 ≤ p) : (entry p).2 = 0 := by
  have hs : pages.size = 57 := by decide
  have hidx : pages.size ≤ p / 64 := by rw [hs]; omega
  simp [entry, Array.getElem?_eq_none hidx]

lemma sum_pages (w : ℕ → ℕ) (b : ℕ) :
    ∑ j ∈ Finset.range (64*b), w j =
      ∑ q ∈ Finset.range b, ∑ j ∈ Finset.range 64, w (64*q+j) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ (fun q => ∑ j ∈ Finset.range 64, w (64*q+j)) b,
      Nat.mul_succ, Finset.sum_range_add, ih]

lemma factor_divisor_sum {n p : ℕ} (hn : n ≠ 0) (hp : Nat.Prime p) :
    sigma 1 (p ^ n.factorization p) ∣ sigma 1 n := by
  have hc := (coprime_ordCompl hp hn).pow_left (n.factorization p)
  have hm := isMultiplicative_sigma (k := 1) |>.map_mul_of_coprime hc
  rw [ordProj_mul_ordCompl_eq_self n p] at hm
  rw [hm]
  exact Nat.dvd_mul_right _ _

lemma local_certificate (coverage : ∀ q < 57, pageOK q = true)
    {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hc : p.Coprime forbidden)
    (he : 0 < e) (ha : admissible p e) :
    p ^ 29500 ≤ 2 ^ (entry p).2 * p ^ e * (p-1) ^ 29500 := by
  by_cases hsmall : p < 3648
  · have hall := coverage (p/64) (by omega)
    have hr := List.all_eq_true.mp hall (p%64) (List.mem_range.mpr (by omega))
    rw [Nat.div_add_mod] at hr
    have h3 : 2 < p := by have := hp.two_le; omega
    rw [rowOK, if_pos ⟨h3, sieve_prime hp, hc⟩, Bool.and_eq_true, decide_eq_true_eq] at hr
    have hmin : (entry p).1 ≤ e := by
      by_contra! hlt
      have hv := List.all_eq_true.mp hr.2 e (List.mem_range.mpr hlt)
      exact ((of_decide_eq_true hv).resolve_left he.ne') ha
    have hb := hr.1
    simp only [binary_power] at hb
    exact hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hp.pos hmin)))
  · have ht := tail_bound (t := 3607) (k := 29500) (by decide) (p := p) (by omega) tail_certificate
    rw [nonzero_weight_small (by omega), pow_zero, one_mul]
    exact ht.trans (Nat.mul_le_mul_right _ (by simpa using Nat.pow_le_pow_right hp.pos (show 1 ≤ e from he)))

lemma endgame_of_certificate (coverage : ∀ q < 57, pageOK q = true)
    (budget : (∑ q ∈ Finset.range 57, ∑ j ∈ Finset.range 64, (entry (64*q+j)).2) = 23783) :
    OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1.H2 := by
  intro n ho hsize hc hs hc4
  have hn : n ≠ 0 := by obtain ⟨a, ha⟩ := ho; omega
  have component (p : ℕ) (hm : p ∈ n.primeFactors) :
      p ^ 29500 ≤ 2 ^ (entry p).2 * p ^ n.factorization p * (p-1) ^ 29500 := by
    have hp := Nat.prime_of_mem_primeFactors hm
    have hd := Nat.dvd_of_mem_primeFactors hm
    have hdσ := factor_divisor_sum hn hp
    have hp2 : p ≠ 2 := by rintro rfl; obtain ⟨a, ha⟩ := ho; omega
    apply local_certificate coverage hp hp2 (hc.coprime_dvd_left hd)
      (hp.factorization_pos_of_dvd hn hd)
    unfold admissible geometric
    rw [← sigma_one_apply_prime_pow hp]
    exact ⟨hs.coprime_dvd_left hdσ, fun h => hc4 (h.trans hdσ)⟩
  have hsum : (∑ p ∈ n.primeFactors, (entry p).2) ≤ 23783 := by
    calc
      _ = ∑ p ∈ n.primeFactors.filter (· < 3648), (entry p).2 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p _
        split_ifs with h
        · rfl
        · exact nonzero_weight_small (by omega)
      _ ≤ ∑ p ∈ Finset.range (64*57), (entry p).2 := by
        apply Finset.sum_le_sum_of_subset
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      _ = 23783 := (sum_pages (fun p => (entry p).2) 57).trans budget
  have hbudget : 2^23783 * 10^1500 < (2 : ℕ)^29500 := by
    rw [← binary_power 23783 2, ← binary_power 1500 10, ← binary_power 29500 2]
    decide
  have hcand := combine hn (fun p => (entry p).2) component
  have hlt : (sigma 1 n)^29500 < (2*n)^29500 := by
    rw [mul_pow]
    apply lt_of_le_of_lt hcand
    apply Nat.mul_lt_mul_of_pos_right _ (pow_pos (Nat.pos_of_ne_zero hn) _)
    have hw : (2 : ℕ) ^ (∑ p ∈ n.primeFactors, (entry p).2) ≤ 2^23783 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hsum
    exact (Nat.mul_le_mul hw hsize).trans_lt hbudget
  exact lt_of_not_ge (fun h => (not_le_of_gt hlt) (Nat.pow_le_pow_left h 29500))

lemma verified_rows : (List.range 57).all pageOK = true := by decide

lemma verified_budget :
    (∑ q ∈ Finset.range 57, ∑ j ∈ Finset.range 64, (entry (64*q+j)).2) = 23783 := by
  have sum_list (n : ℕ) (f : ℕ → ℕ) :
      (∑ i ∈ Finset.range n, f i) = ((List.range n).map f).sum := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]
  simp_rw [sum_list]
  decide +kernel

end OddPerfectEndgame

theorem OMA.solution : OMA.R_PerfectNumbers_odd_perfect_number_lower_bound_R1_H1_R1.H2 :=
  OddPerfectEndgame.endgame_of_certificate
    (fun q hq => List.all_eq_true.mp OddPerfectEndgame.verified_rows q (List.mem_range.mpr hq))
    OddPerfectEndgame.verified_budget
