import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H1_R1
import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
For the leaf of Erdős problem 470 with fixed prime powers \(3^2,5,7\),
use the two residual primes to write the input as `315 * p^a * q^b`.
Capping the exponents at three gives nine boxes for each prime pair.
Whenever a box can contain an abundant input, the checked table supplies
an abundant divisor core and a subset of its proper divisors whose sum
is the excess over twice the core. Taking the remaining proper divisors
and scaling gives a pseudoperfectness witness for the input.
-/

namespace OMA.Erdos470MinimalCores

open Finset ArithmeticFunction

/-- The exact hypotheses force (3^2\cdot5\cdot7\) and precisely two distinct residual primes. -/
theorem support_shape {n p : ℕ} (ho : Odd n) (hn : n ≠ 0) (hc : n.primeFactors.card = 5)
    (h3 : n.factorization 3 = 2) (h5 : n.factorization 5 = 1) (h7 : n.factorization 7 = 1)
    (hp : p.Prime) (hpd : p ∣ n) (hpmin : 107 ≤ p)
    (hbound : ∀ q ∈ n.primeFactors, q < 5565) :
    ∃ q a b : ℕ, q.Prime ∧ 11 ≤ q ∧ q < 5565 ∧ p ≠ q ∧ 0 < a ∧ 0 < b ∧
      n = 315 * p ^ a * q ^ b := by
  have h3m : 3 ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, h3]
    decide
  have h5m : 5 ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, h5]
    decide
  have h7m : 7 ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, h7]
    decide
  have hpm : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hn⟩
  have h4 : ({p, 3, 5, 7} : Finset ℕ).card = 4 := by
    simp [show p ≠ 3 by omega, show p ≠ 5 by omega, show p ≠ 7 by omega]
  obtain ⟨q, hqm, hqnot⟩ := Finset.exists_mem_notMem_of_card_lt_card (by
    rw [h4, hc]
    decide : ({p, 3, 5, 7} : Finset ℕ).card < n.primeFactors.card)
  have hqp := Nat.prime_of_mem_primeFactors hqm
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqnot
  have hq2 : q ≠ 2 := by
    intro he
    have hd := Nat.dvd_of_mem_primeFactors hqm
    rw [he] at hd
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hd)
  have hql : 11 ≤ q := by
    have htwo := hqp.two_le
    by_contra! hh
    interval_cases q <;> simp_all <;> exact False.elim ((of_decide_eq_false rfl) hqp)
  have hs : ({q, p, 3, 5, 7} : Finset ℕ) = n.primeFactors := by
    apply Finset.eq_of_subset_of_card_le
    · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hqm, hpm, h3m, h5m, h7m⟩
    · have hqn : q ∉ ({p, 3, 5, 7} : Finset ℕ) := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hqnot
      rw [Finset.card_insert_of_notMem hqn, h4, hc]
  refine ⟨q, n.factorization p, n.factorization q, hqp, hql, hbound q hqm, Ne.symm hqnot.1, ?_, ?_, ?_⟩
  · rwa [← Nat.support_factorization, Finsupp.mem_support_iff, ← Nat.pos_iff_ne_zero] at hpm
  · rwa [← Nat.support_factorization, Finsupp.mem_support_iff, ← Nat.pos_iff_ne_zero] at hqm
  nth_rw 1 [Nat.prod_primeFactors_pow_factorization hn, ← hs]
  simp [Finset.prod_insert, hqnot, h3, h5, h7, show p ≠ 3 by omega,
    show p ≠ 5 by omega, show p ≠ 7 by omega]
  ring

/-- Pseudoperfect witnesses can be scaled along divisibility. -/
theorem pseudoperfect_of_dvd {core n : ℕ} (hn : 0 < n) (hd : core ∣ n)
    (hc : core.Pseudoperfect) : n.Pseudoperfect := by
  obtain ⟨z, rfl⟩ := hd
  have hz : 0 < z := Nat.pos_of_mul_pos_left hn
  obtain ⟨_, s, hs, hsum⟩ := hc
  refine ⟨hn, s.image (· * z), ?_, ?_⟩
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hdiv, hlt⟩ := Nat.mem_properDivisors.mp (hs hd)
    exact Nat.mem_properDivisors.mpr
      ⟨Nat.mul_dvd_mul_right hdiv z, Nat.mul_lt_mul_of_pos_right hlt hz⟩
  · rw [Finset.sum_image (fun x _ y _ h => (Nat.mul_right_cancel_iff hz).mp h),
      ← Finset.sum_mul, hsum]

/-- Deleting proper divisors whose sum is the abundance excess leaves the required witness. -/
theorem pseudoperfect_of_excess {n : ℕ} (hn : 0 < n) (D : Finset ℕ)
    (hD : ∀ d ∈ D, d ∣ n ∧ d < n)
    (hSum : (∑ d ∈ D, d) + 2 * n = ArithmeticFunction.sigma 1 n) : n.Pseudoperfect := by
  have hsub : D ⊆ n.properDivisors := fun d hd => Nat.mem_properDivisors.mpr (hD d hd)
  refine ⟨hn, n.properDivisors \ D, Finset.sdiff_subset, ?_⟩
  have he := Finset.sum_sdiff (f := id) hsub
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self] at hSum
  simp only [id_eq] at he
  omega

/-- The geometric sum used for the divisor ratios of residual prime powers. -/
def geom (p a : ℕ) : ℕ := ∑ i ∈ Finset.range (a + 1), p ^ i

theorem sigma_core {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp315 : p.Coprime 315) (hq315 : q.Coprime 315) (hpq : p.Coprime q) :
    ArithmeticFunction.sigma 1 (315 * p^a * q^b) = 624 * geom p a * geom q b := by
  have h1 : (315 * p ^ a).Coprime (q ^ b) :=
    ((Nat.coprime_mul_iff_left).mpr ⟨hq315.symm, hpq.pow_left a⟩).pow_right b
  rw [isMultiplicative_sigma.map_mul_of_coprime h1,
    isMultiplicative_sigma.map_mul_of_coprime (hp315.symm.pow_right a),
    sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hq]
  have h315 : ArithmeticFunction.sigma 1 315 = 624 := by decide +kernel
  rw [h315]
  rfl

end OMA.Erdos470MinimalCores

namespace OMA.Erdos470MinimalCores

open Finset

/-- Numerator of the upper abundancy bound for an exponent capped at three. -/
def upperNumerator (p a : ℕ) : ℕ := if a < 3 then geom p a else p

/-- Denominator of the upper abundancy bound for an exponent capped at three. -/
def upperDenominator (p a : ℕ) : ℕ := if a < 3 then p ^ a else p - 1

/-- A capped exponent box can contain an abundant core only if this strict
cross-multiplied inequality holds. -/
def upperAllows (p q a b : ℕ) : Prop :=
  630 * upperDenominator p a * upperDenominator q b <
    624 * upperNumerator p a * upperNumerator q b

instance (p q a b : ℕ) : Decidable (upperAllows p q a b) := by
  unfold upperAllows
  infer_instance

theorem ratio_le_cap {p a : ℕ} (hp : 2 ≤ p) :
    geom p a * upperDenominator p (min a 3) ≤ p ^ a * upperNumerator p (min a 3) := by
  by_cases ha : a < 3
  · rw [min_eq_left ha.le]
    simp [upperNumerator, upperDenominator, ha, mul_comm]
  · have hm : min a 3 = 3 := min_eq_right (Nat.le_of_not_gt ha)
    rw [hm, upperDenominator, upperNumerator, if_neg (by decide), if_neg (by decide), geom,
      geom_sum_mul_of_one_le (by omega : 1 ≤ p), pow_succ]
    exact Nat.sub_le _ _

theorem upperDenominator_pos {p a : ℕ} (hp : 2 ≤ p) : 0 < upperDenominator p a := by
  unfold upperDenominator
  split
  · positivity
  · omega

theorem upperAllows_of_abundant {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp315 : p.Coprime 315) (hq315 : q.Coprime 315) (hpq : p.Coprime q)
    (h : (315 * p ^ a * q ^ b).Abundant) : upperAllows p q (min a 3) (min b 3) := by
  rw [Nat.abundant_iff_sum_divisors, ← ArithmeticFunction.sigma_one_apply,
    sigma_core hp hq hp315 hq315 hpq] at h
  have hpos := Nat.mul_pos (upperDenominator_pos (a := min a 3) hp.two_le)
    (upperDenominator_pos (a := min b 3) hq.two_le)
  have hlt := Nat.mul_lt_mul_of_pos_right h hpos
  have hmul := Nat.mul_le_mul (ratio_le_cap (a := a) hp.two_le) (ratio_le_cap (a := b) hq.two_le)
  have hcomp := Nat.mul_le_mul_left 624 hmul
  have hlhs : (2 * (315 * p^a * q^b)) *
      (upperDenominator p (min a 3) * upperDenominator q (min b 3)) =
      (630 * upperDenominator p (min a 3) * upperDenominator q (min b 3)) * (p^a * q^b) := by ring
  have hmid : (624 * geom p a * geom q b) *
      (upperDenominator p (min a 3) * upperDenominator q (min b 3)) =
      624 * ((geom p a * upperDenominator p (min a 3)) * (geom q b * upperDenominator q (min b 3))) := by ring
  have hrhs : 624 * ((p^a * upperNumerator p (min a 3)) * (q^b * upperNumerator q (min b 3))) =
      (624 * upperNumerator p (min a 3) * upperNumerator q (min b 3)) * (p^a * q^b) := by ring
  rw [hlhs,hmid] at hlt
  rw [hrhs] at hcomp
  exact Nat.lt_of_mul_lt_mul_right (hlt.trans_le hcomp)

end OMA.Erdos470MinimalCores

namespace OMA.Erdos470MinimalCores

/-- Exponents of a certified divisor core and its omitted proper divisors. -/
structure Witness where
  a : ℕ
  b : ℕ
  omitted : List ℕ

/-- Each entry supplies the (at most two) relevant cores for one residual prime. -/
abbrev Row := ℕ × List Witness

def verifyWitness (p q : ℕ) (w : Witness) : Bool :=
  let n := 315 * p ^ w.a * q ^ w.b
  decide w.omitted.Nodup && w.omitted.all (fun d => decide (d ∣ n ∧ d < n)) &&
    decide (w.omitted.sum + 2 * n = 624 * geom p w.a * geom q w.b)

theorem verifyWitness_sound {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp315 : p.Coprime 315) (hq315 : q.Coprime 315) (hpq : p.Coprime q)
    (w : Witness) (hw : verifyWitness p q w = true) : (315 * p ^ w.a * q ^ w.b).Pseudoperfect := by
  unfold verifyWitness at hw
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hw
  obtain ⟨⟨hnodup, hproper⟩, hsum⟩ := hw
  have hpos := Nat.mul_pos (Nat.mul_pos (by decide : 0 < 315) (pow_pos hp.pos w.a))
    (pow_pos hq.pos w.b)
  refine pseudoperfect_of_excess hpos w.omitted.toFinset ?_ ?_
  · intro d hd
    exact hproper d (List.mem_toFinset.mp hd)
  · rw [List.sum_toFinset _ hnodup, sigma_core hp hq hp315 hq315 hpq]
    simpa using hsum

/-- Check every exponent box and every certificate for a fixed pair of primes. -/
def verifyPair (p q : ℕ) (ws : List Witness) : Bool :=
  if p = q then true else
  ws.all (verifyWitness p q) && [1, 2, 3].all (fun a => [1, 2, 3].all (fun b =>
    !decide (upperAllows p q a b) || ws.any (fun w => decide (w.a ≤ a ∧ w.b ≤ b))))

/-- A verified pair yields a pseudoperfect divisor of every abundant core in the box. -/
theorem verifyPair_sound {p q a b : ℕ} {ws : List Witness} (hpq : p ≠ q)
    (ha : a ∈ ([1, 2, 3] : List ℕ)) (hb : b ∈ ([1, 2, 3] : List ℕ))
    (hu : upperAllows p q a b) (h : verifyPair p q ws = true) :
    ∃ w ∈ ws, w.a ≤ a ∧ w.b ≤ b ∧ verifyWitness p q w = true := by
  simp only [verifyPair, if_neg hpq, Bool.and_eq_true, List.all_eq_true] at h
  have hw := h.2 a ha b hb
  simp only [hu, decide_true, Bool.not_true, Bool.false_or, List.any_eq_true,
    decide_eq_true_eq] at hw
  obtain ⟨w, hw, hle⟩ := hw
  exact ⟨w, hw, hle.1, hle.2, h.1 w hw⟩

/-- Merge an increasing list of primes with the list of nonempty certificate rows. -/
def verifyBatch (p : ℕ) : List ℕ → List Row → Bool
  | [], rows => rows.isEmpty
  | q :: qs, [] => verifyPair p q [] && verifyBatch p qs []
  | q :: qs, (r, ws) :: rows =>
    if q = r then verifyPair p q ws && verifyBatch p qs rows
    else verifyPair p q [] && verifyBatch p qs ((r, ws) :: rows)

theorem verifyBatch_sound {p : ℕ} {qs : List ℕ} {rows : List Row}
    (h : verifyBatch p qs rows = true) {q : ℕ} (hq : q ∈ qs) :
    ∃ ws, verifyPair p q ws = true := by
  induction qs generalizing rows with
  | nil => simp at hq
  | cons r rs ih =>
    rw [List.mem_cons] at hq
    cases rows with
    | nil =>
      simp only [verifyBatch, Bool.and_eq_true] at h
      rcases hq with rfl | hq
      · exact ⟨[], h.1⟩
      · exact ih h.2 hq
    | cons row rows =>
      obtain ⟨s,ws⟩ := row
      by_cases hrs : r = s
      · simp only [verifyBatch, hrs, if_true, Bool.and_eq_true] at h
        rcases hq with rfl | hq
        · exact ⟨ws, by simpa [hrs] using h.1⟩
        · exact ih h.2 hq
      · simp only [verifyBatch, if_neg hrs, Bool.and_eq_true] at h
        rcases hq with rfl | hq
        · exact ⟨[], h.1⟩
        · exact ih h.2 hq

end OMA.Erdos470MinimalCores

namespace OMA.Erdos470MinimalCores

/-- The small-divisor sieve used to enumerate the finite support candidates. -/
def smallPrimeDivisors : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
  37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

def primeCandidate (q : ℕ) : Bool :=
  smallPrimeDivisors.all fun p => decide (p < 2 ∨ q ≤ p ∨ q % p ≠ 0)

theorem primeCandidate_of_prime {q : ℕ} (hq : q.Prime) : primeCandidate q = true := by
  apply List.all_eq_true.mpr
  intro p _
  apply decide_eq_true
  by_cases hp : 2 ≤ p
  · by_cases hqp : q ≤ p
    · exact Or.inr (Or.inl hqp)
    · refine Or.inr (Or.inr fun hm => hqp ?_)
      exact le_of_eq ((Nat.dvd_prime_two_le hq hp).mp (Nat.dvd_of_mod_eq_zero hm)).symm
  · exact Or.inl (by omega)

end OMA.Erdos470MinimalCores

namespace OMA.Erdos470MinimalCores

def qPrimes : List ℕ := [
  11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
  67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
  137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199,
  211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
  283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373,
  379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457,
  461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
  563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641,
  643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733,
  739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827,
  829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929,
  937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021,
  1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109,
  1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223,
  1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307,
  1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439,
  1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531,
  1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619,
  1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733,
  1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861,
  1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973,
  1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069,
  2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161,
  2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287,
  2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383,
  2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503,
  2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633,
  2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713,
  2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819,
  2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939,
  2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061,
  3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191,
  3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313,
  3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413,
  3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533,
  3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631,
  3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739,
  3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863,
  3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989,
  4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093,
  4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219,
  4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337,
  4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457,
  4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583,
  4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691,
  4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813,
  4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951,
  4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051,
  5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179,
  5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309,
  5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437,
  5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531,
  5557, 5563]

def pPrimes : List ℕ := [
  107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
  181, 191, 193, 197, 199]

def qPrimesFrom11 : List ℕ := [
  11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
  67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
  137]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom11_eq : qPrimesFrom11 = (List.range' 11 128).filter primeCandidate := by rfl

def qPrimesFrom139 : List ℕ := [
  139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211,
  223, 227, 229, 233, 239, 241, 251, 257, 263]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom139_eq : qPrimesFrom139 = (List.range' 139 128).filter primeCandidate := by rfl

def qPrimesFrom267 : List ℕ := [
  269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349,
  353, 359, 367, 373, 379, 383, 389]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom267_eq : qPrimesFrom267 = (List.range' 267 128).filter primeCandidate := by rfl

def qPrimesFrom395 : List ℕ := [
  397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467,
  479, 487, 491, 499, 503, 509, 521]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom395_eq : qPrimesFrom395 = (List.range' 395 128).filter primeCandidate := by rfl

def qPrimesFrom523 : List ℕ := [
  523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613,
  617, 619, 631, 641, 643, 647]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom523_eq : qPrimesFrom523 = (List.range' 523 128).filter primeCandidate := by rfl

def qPrimesFrom651 : List ℕ := [
  653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743,
  751, 757, 761, 769, 773]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom651_eq : qPrimesFrom651 = (List.range' 651 128).filter primeCandidate := by rfl

def qPrimesFrom779 : List ℕ := [
  787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877,
  881, 883, 887]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom779_eq : qPrimesFrom779 = (List.range' 779 128).filter primeCandidate := by rfl

def qPrimesFrom907 : List ℕ := [
  907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997,
  1009, 1013, 1019, 1021, 1031, 1033]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom907_eq : qPrimesFrom907 = (List.range' 907 128).filter primeCandidate := by rfl

def qPrimesFrom1035 : List ℕ := [
  1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123,
  1129, 1151, 1153]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom1035_eq : qPrimesFrom1035 = (List.range' 1035 128).filter primeCandidate := by rfl

def qPrimesFrom1163 : List ℕ := [
  1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259,
  1277, 1279, 1283, 1289]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom1163_eq : qPrimesFrom1163 = (List.range' 1163 128).filter primeCandidate := by rfl

def qPrimesFrom1291 : List ℕ := [
  1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom1291_eq : qPrimesFrom1291 = (List.range' 1291 128).filter primeCandidate := by rfl

def qPrimesFrom1419 : List ℕ := [
  1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489,
  1493, 1499, 1511, 1523, 1531, 1543]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom1419_eq : qPrimesFrom1419 = (List.range' 1419 128).filter primeCandidate := by rfl

def qPrimesFrom1547 : List ℕ := [
  1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621,
  1627, 1637, 1657, 1663, 1667, 1669]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom1547_eq : qPrimesFrom1547 = (List.range' 1547 128).filter primeCandidate := by rfl

def qPrimesFrom1675 : List ℕ := [
  1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787,
  1789, 1801]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom1675_eq : qPrimesFrom1675 = (List.range' 1675 128).filter primeCandidate := by rfl

def qPrimesFrom1803 : List ℕ := [
  1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom1803_eq : qPrimesFrom1803 = (List.range' 1803 128).filter primeCandidate := by rfl

def qPrimesFrom1931 : List ℕ := [
  1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027,
  2029, 2039, 2053]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom1931_eq : qPrimesFrom1931 = (List.range' 1931 128).filter primeCandidate := by rfl

def qPrimesFrom2059 : List ℕ := [
  2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143,
  2153, 2161, 2179]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom2059_eq : qPrimesFrom2059 = (List.range' 2059 128).filter primeCandidate := by rfl

def qPrimesFrom2187 : List ℕ := [
  2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293,
  2297, 2309, 2311]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom2187_eq : qPrimesFrom2187 = (List.range' 2187 128).filter primeCandidate := by rfl

def qPrimesFrom2315 : List ℕ := [
  2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411,
  2417, 2423, 2437, 2441]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom2315_eq : qPrimesFrom2315 = (List.range' 2315 128).filter primeCandidate := by rfl

def qPrimesFrom2443 : List ℕ := [
  2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom2443_eq : qPrimesFrom2443 = (List.range' 2443 128).filter primeCandidate := by rfl

def qPrimesFrom2571 : List ℕ := [
  2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683,
  2687, 2689, 2693]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom2571_eq : qPrimesFrom2571 = (List.range' 2571 128).filter primeCandidate := by rfl

def qPrimesFrom2699 : List ℕ := [
  2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791,
  2797, 2801, 2803, 2819]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom2699_eq : qPrimesFrom2699 = (List.range' 2699 128).filter primeCandidate := by rfl

def qPrimesFrom2827 : List ℕ := [
  2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939,
  2953]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom2827_eq : qPrimesFrom2827 = (List.range' 2827 128).filter primeCandidate := by rfl

def qPrimesFrom2955 : List ℕ := [
  2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067,
  3079]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom2955_eq : qPrimesFrom2955 = (List.range' 2955 128).filter primeCandidate := by rfl

def qPrimesFrom3083 : List ℕ := [
  3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom3083_eq : qPrimesFrom3083 = (List.range' 3083 128).filter primeCandidate := by rfl

def qPrimesFrom3211 : List ℕ := [
  3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323,
  3329, 3331]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom3211_eq : qPrimesFrom3211 = (List.range' 3211 128).filter primeCandidate := by rfl

def qPrimesFrom3339 : List ℕ := [
  3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461,
  3463]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom3339_eq : qPrimesFrom3339 = (List.range' 3339 128).filter primeCandidate := by rfl

def qPrimesFrom3467 : List ℕ := [
  3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559,
  3571, 3581, 3583, 3593]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom3467_eq : qPrimesFrom3467 = (List.range' 3467 128).filter primeCandidate := by rfl

def qPrimesFrom3595 : List ℕ := [
  3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701,
  3709, 3719]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom3595_eq : qPrimesFrom3595 = (List.range' 3595 128).filter primeCandidate := by rfl

def qPrimesFrom3723 : List ℕ := [
  3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom3723_eq : qPrimesFrom3723 = (List.range' 3723 128).filter primeCandidate := by rfl

def qPrimesFrom3851 : List ℕ := [
  3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943,
  3947, 3967]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom3851_eq : qPrimesFrom3851 = (List.range' 3851 128).filter primeCandidate := by rfl

def qPrimesFrom3979 : List ℕ := [
  3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091,
  4093, 4099]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom3979_eq : qPrimesFrom3979 = (List.range' 3979 128).filter primeCandidate := by rfl

def qPrimesFrom4107 : List ℕ := [
  4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229,
  4231]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom4107_eq : qPrimesFrom4107 = (List.range' 4107 128).filter primeCandidate := by rfl

def qPrimesFrom4235 : List ℕ := [
  4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349,
  4357]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom4235_eq : qPrimesFrom4235 = (List.range' 4235 128).filter primeCandidate := by rfl

def qPrimesFrom4363 : List ℕ := [
  4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom4363_eq : qPrimesFrom4363 = (List.range' 4363 128).filter primeCandidate := by rfl

def qPrimesFrom4491 : List ℕ := [
  4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom4491_eq : qPrimesFrom4491 = (List.range' 4491 128).filter primeCandidate := by rfl

def qPrimesFrom4619 : List ℕ := [
  4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723,
  4729, 4733]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom4619_eq : qPrimesFrom4619 = (List.range' 4619 128).filter primeCandidate := by rfl

def qPrimesFrom4747 : List ℕ := [
  4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom4747_eq : qPrimesFrom4747 = (List.range' 4747 128).filter primeCandidate := by rfl

def qPrimesFrom4875 : List ℕ := [
  4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973,
  4987, 4993, 4999]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom4875_eq : qPrimesFrom4875 = (List.range' 4875 128).filter primeCandidate := by rfl

def qPrimesFrom5003 : List ℕ := [
  5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107,
  5113, 5119]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom5003_eq : qPrimesFrom5003 = (List.range' 5003 128).filter primeCandidate := by rfl

def qPrimesFrom5131 : List ℕ := [
  5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom5131_eq : qPrimesFrom5131 = (List.range' 5131 128).filter primeCandidate := by rfl

def qPrimesFrom5259 : List ℕ := [
  5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom5259_eq : qPrimesFrom5259 = (List.range' 5259 128).filter primeCandidate := by rfl

def qPrimesFrom5387 : List ℕ := [
  5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477,
  5479, 5483, 5501, 5503, 5507]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom5387_eq : qPrimesFrom5387 = (List.range' 5387 128).filter primeCandidate := by rfl

def qPrimesFrom5515 : List ℕ := [
  5519, 5521, 5527, 5531, 5557, 5563]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimesFrom5515_eq : qPrimesFrom5515 = (List.range' 5515 50).filter primeCandidate := by rfl

def qChunk : ℕ → List ℕ
  | 0 => qPrimesFrom11
  | 1 => qPrimesFrom139
  | 2 => qPrimesFrom267
  | 3 => qPrimesFrom395
  | 4 => qPrimesFrom523
  | 5 => qPrimesFrom651
  | 6 => qPrimesFrom779
  | 7 => qPrimesFrom907
  | 8 => qPrimesFrom1035
  | 9 => qPrimesFrom1163
  | 10 => qPrimesFrom1291
  | 11 => qPrimesFrom1419
  | 12 => qPrimesFrom1547
  | 13 => qPrimesFrom1675
  | 14 => qPrimesFrom1803
  | 15 => qPrimesFrom1931
  | 16 => qPrimesFrom2059
  | 17 => qPrimesFrom2187
  | 18 => qPrimesFrom2315
  | 19 => qPrimesFrom2443
  | 20 => qPrimesFrom2571
  | 21 => qPrimesFrom2699
  | 22 => qPrimesFrom2827
  | 23 => qPrimesFrom2955
  | 24 => qPrimesFrom3083
  | 25 => qPrimesFrom3211
  | 26 => qPrimesFrom3339
  | 27 => qPrimesFrom3467
  | 28 => qPrimesFrom3595
  | 29 => qPrimesFrom3723
  | 30 => qPrimesFrom3851
  | 31 => qPrimesFrom3979
  | 32 => qPrimesFrom4107
  | 33 => qPrimesFrom4235
  | 34 => qPrimesFrom4363
  | 35 => qPrimesFrom4491
  | 36 => qPrimesFrom4619
  | 37 => qPrimesFrom4747
  | 38 => qPrimesFrom4875
  | 39 => qPrimesFrom5003
  | 40 => qPrimesFrom5131
  | 41 => qPrimesFrom5259
  | 42 => qPrimesFrom5387
  | 43 => qPrimesFrom5515
  | _ => []

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimes_grouped : qPrimes = ((List.range 44).map qChunk).flatten := by rfl

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem qPrimes_complete (r : ℕ) (hr : r.Prime) (hlo : 11 ≤ r) (hhi : r < 5565) : r ∈ qPrimes := by
  rw [qPrimes_grouped]
  apply List.mem_flatten.mpr
  have hCand := primeCandidate_of_prime hr
  by_cases h0 : r < 139
  · refine ⟨qPrimesFrom11, List.mem_map.mpr ⟨0, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom11_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨hlo, h0⟩, hCand⟩
  by_cases h1 : r < 267
  · refine ⟨qPrimesFrom139, List.mem_map.mpr ⟨1, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom139_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h0, h1⟩, hCand⟩
  by_cases h2 : r < 395
  · refine ⟨qPrimesFrom267, List.mem_map.mpr ⟨2, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom267_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h1, h2⟩, hCand⟩
  by_cases h3 : r < 523
  · refine ⟨qPrimesFrom395, List.mem_map.mpr ⟨3, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom395_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h2, h3⟩, hCand⟩
  by_cases h4 : r < 651
  · refine ⟨qPrimesFrom523, List.mem_map.mpr ⟨4, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom523_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h3, h4⟩, hCand⟩
  by_cases h5 : r < 779
  · refine ⟨qPrimesFrom651, List.mem_map.mpr ⟨5, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom651_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h4, h5⟩, hCand⟩
  by_cases h6 : r < 907
  · refine ⟨qPrimesFrom779, List.mem_map.mpr ⟨6, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom779_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h5, h6⟩, hCand⟩
  by_cases h7 : r < 1035
  · refine ⟨qPrimesFrom907, List.mem_map.mpr ⟨7, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom907_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h6, h7⟩, hCand⟩
  by_cases h8 : r < 1163
  · refine ⟨qPrimesFrom1035, List.mem_map.mpr ⟨8, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom1035_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h7, h8⟩, hCand⟩
  by_cases h9 : r < 1291
  · refine ⟨qPrimesFrom1163, List.mem_map.mpr ⟨9, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom1163_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h8, h9⟩, hCand⟩
  by_cases h10 : r < 1419
  · refine ⟨qPrimesFrom1291, List.mem_map.mpr ⟨10, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom1291_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h9, h10⟩, hCand⟩
  by_cases h11 : r < 1547
  · refine ⟨qPrimesFrom1419, List.mem_map.mpr ⟨11, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom1419_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h10, h11⟩, hCand⟩
  by_cases h12 : r < 1675
  · refine ⟨qPrimesFrom1547, List.mem_map.mpr ⟨12, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom1547_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h11, h12⟩, hCand⟩
  by_cases h13 : r < 1803
  · refine ⟨qPrimesFrom1675, List.mem_map.mpr ⟨13, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom1675_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h12, h13⟩, hCand⟩
  by_cases h14 : r < 1931
  · refine ⟨qPrimesFrom1803, List.mem_map.mpr ⟨14, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom1803_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h13, h14⟩, hCand⟩
  by_cases h15 : r < 2059
  · refine ⟨qPrimesFrom1931, List.mem_map.mpr ⟨15, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom1931_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h14, h15⟩, hCand⟩
  by_cases h16 : r < 2187
  · refine ⟨qPrimesFrom2059, List.mem_map.mpr ⟨16, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom2059_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h15, h16⟩, hCand⟩
  by_cases h17 : r < 2315
  · refine ⟨qPrimesFrom2187, List.mem_map.mpr ⟨17, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom2187_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h16, h17⟩, hCand⟩
  by_cases h18 : r < 2443
  · refine ⟨qPrimesFrom2315, List.mem_map.mpr ⟨18, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom2315_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h17, h18⟩, hCand⟩
  by_cases h19 : r < 2571
  · refine ⟨qPrimesFrom2443, List.mem_map.mpr ⟨19, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom2443_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h18, h19⟩, hCand⟩
  by_cases h20 : r < 2699
  · refine ⟨qPrimesFrom2571, List.mem_map.mpr ⟨20, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom2571_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h19, h20⟩, hCand⟩
  by_cases h21 : r < 2827
  · refine ⟨qPrimesFrom2699, List.mem_map.mpr ⟨21, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom2699_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h20, h21⟩, hCand⟩
  by_cases h22 : r < 2955
  · refine ⟨qPrimesFrom2827, List.mem_map.mpr ⟨22, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom2827_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h21, h22⟩, hCand⟩
  by_cases h23 : r < 3083
  · refine ⟨qPrimesFrom2955, List.mem_map.mpr ⟨23, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom2955_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h22, h23⟩, hCand⟩
  by_cases h24 : r < 3211
  · refine ⟨qPrimesFrom3083, List.mem_map.mpr ⟨24, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom3083_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h23, h24⟩, hCand⟩
  by_cases h25 : r < 3339
  · refine ⟨qPrimesFrom3211, List.mem_map.mpr ⟨25, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom3211_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h24, h25⟩, hCand⟩
  by_cases h26 : r < 3467
  · refine ⟨qPrimesFrom3339, List.mem_map.mpr ⟨26, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom3339_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h25, h26⟩, hCand⟩
  by_cases h27 : r < 3595
  · refine ⟨qPrimesFrom3467, List.mem_map.mpr ⟨27, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom3467_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h26, h27⟩, hCand⟩
  by_cases h28 : r < 3723
  · refine ⟨qPrimesFrom3595, List.mem_map.mpr ⟨28, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom3595_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h27, h28⟩, hCand⟩
  by_cases h29 : r < 3851
  · refine ⟨qPrimesFrom3723, List.mem_map.mpr ⟨29, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom3723_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h28, h29⟩, hCand⟩
  by_cases h30 : r < 3979
  · refine ⟨qPrimesFrom3851, List.mem_map.mpr ⟨30, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom3851_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h29, h30⟩, hCand⟩
  by_cases h31 : r < 4107
  · refine ⟨qPrimesFrom3979, List.mem_map.mpr ⟨31, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom3979_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h30, h31⟩, hCand⟩
  by_cases h32 : r < 4235
  · refine ⟨qPrimesFrom4107, List.mem_map.mpr ⟨32, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom4107_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h31, h32⟩, hCand⟩
  by_cases h33 : r < 4363
  · refine ⟨qPrimesFrom4235, List.mem_map.mpr ⟨33, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom4235_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h32, h33⟩, hCand⟩
  by_cases h34 : r < 4491
  · refine ⟨qPrimesFrom4363, List.mem_map.mpr ⟨34, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom4363_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h33, h34⟩, hCand⟩
  by_cases h35 : r < 4619
  · refine ⟨qPrimesFrom4491, List.mem_map.mpr ⟨35, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom4491_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h34, h35⟩, hCand⟩
  by_cases h36 : r < 4747
  · refine ⟨qPrimesFrom4619, List.mem_map.mpr ⟨36, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom4619_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h35, h36⟩, hCand⟩
  by_cases h37 : r < 4875
  · refine ⟨qPrimesFrom4747, List.mem_map.mpr ⟨37, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom4747_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h36, h37⟩, hCand⟩
  by_cases h38 : r < 5003
  · refine ⟨qPrimesFrom4875, List.mem_map.mpr ⟨38, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom4875_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h37, h38⟩, hCand⟩
  by_cases h39 : r < 5131
  · refine ⟨qPrimesFrom5003, List.mem_map.mpr ⟨39, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom5003_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h38, h39⟩, hCand⟩
  by_cases h40 : r < 5259
  · refine ⟨qPrimesFrom5131, List.mem_map.mpr ⟨40, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom5131_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h39, h40⟩, hCand⟩
  by_cases h41 : r < 5387
  · refine ⟨qPrimesFrom5259, List.mem_map.mpr ⟨41, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom5259_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h40, h41⟩, hCand⟩
  by_cases h42 : r < 5515
  · refine ⟨qPrimesFrom5387, List.mem_map.mpr ⟨42, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
    rw [qPrimesFrom5387_eq, List.mem_filter]
    exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h41, h42⟩, hCand⟩
  refine ⟨qPrimesFrom5515, List.mem_map.mpr ⟨43, List.mem_range.mpr (by decide), rfl⟩, ?_⟩
  rw [qPrimesFrom5515_eq, List.mem_filter]
  exact ⟨List.mem_range'_1.mpr ⟨Nat.le_of_not_gt h42, hhi⟩, hCand⟩


set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem pPrimes_eq : pPrimes = (List.range' 107 103).filter primeCandidate := by rfl

theorem pPrimes_complete (r : ℕ) (hr : r.Prime) (hlo : 107 ≤ r) (hhi : r < 210) : r ∈ pPrimes := by
  rw [pPrimes_eq, List.mem_filter]
  exact ⟨List.mem_range'_1.mpr ⟨hlo, hhi⟩, primeCandidate_of_prime hr⟩

set_option maxRecDepth 16000 in
def rows107 : List Row := [
  (11, [⟨1, 1, [1, 7, 33, 107, 321, 385, 535, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (13, [⟨1, 1, [107, 117, 273, 321, 535, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (17, [⟨1, 1, [3, 9, 51, 107, 255, 321, 535, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (19, [⟨1, 1, [1, 15, 95, 107, 171, 321, 535, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (23, [⟨1, 1, [3, 107, 207, 321, 535, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (29, [⟨1, 1, [15, 87, 107, 321, 535, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (31, [⟨1, 1, [31, 35, 107, 321, 535, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (37, [⟨1, 1, [7, 21, 37, 321, 535, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (41, [⟨1, 1, [1, 7, 35, 41, 107, 123, 535, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (43, [⟨1, 1, [7, 35, 107, 129, 535, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (47, [⟨1, 1, [7, 45, 47, 107, 535, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (53, [⟨1, 1, [45, 53, 535, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (59, [⟨1, 1, [3, 35, 59, 107, 321, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (61, [⟨1, 1, [61, 107, 321, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (67, [⟨1, 1, [15, 45, 321, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (71, [⟨1, 1, [3, 21, 71, 107, 321, 535, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (73, [⟨1, 1, [5, 9, 45, 107, 321, 535, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (79, [⟨1, 1, [1, 3, 9, 45, 107, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (83, [⟨1, 1, [1, 9, 83, 749, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (89, [⟨1, 1, [3, 89, 107, 535, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (97, [⟨1, 1, [1, 9, 45, 535, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (101, [⟨1, 1, [1, 5, 21, 63, 107, 321, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (103, [⟨1, 1, [9, 45, 107, 321, 963, 1605, 2247, 3745, 4815, 6741, 11235, 33705]⟩]),
  (109, [⟨1, 1, [9, 21, 109, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (113, [⟨1, 1, [9, 35, 1695, 3955, 5085, 7119, 11865, 35595]⟩]),
  (127, [⟨1, 1, [1, 3, 15, 63, 127, 889, 2667, 8001, 13335, 40005]⟩]),
  (131, [⟨1, 1, [1, 3, 9, 45, 131, 393, 1179, 8253, 13755, 41265]⟩]),
  (137, [⟨1, 1, [3, 15, 107, 137, 959, 6165, 14385, 43155]⟩]),
  (139, [⟨1, 1, [9, 107, 139, 6255, 14595, 43785]⟩]),
  (149, [⟨1, 1, [9, 35, 745, 1341, 15645, 46935]⟩]),
  (151, [⟨1, 1, [1, 45, 151, 1057, 15855, 47565]⟩]),
  (157, [⟨1, 1, [1, 3, 35, 471, 1413, 3297, 9891, 49455]⟩]),
  (163, [⟨1, 1, [1, 9, 63, 163, 1141, 1467, 10269, 51345]⟩]),
  (167, [⟨1, 1, [7, 21, 63, 1169, 10521, 52605]⟩]),
  (173, [⟨1, 1, [1, 3, 7, 21, 63, 173, 519, 1211, 7785, 54495]⟩]),
  (179, [⟨1, 1, [1, 3, 21, 63, 179, 1253, 6265, 56385]⟩]),
  (181, [⟨1, 1, [15, 45, 181, 543, 6335, 57015]⟩]),
  (191, [⟨1, 1, [1, 7, 45, 107, 191, 573, 2865, 60165]⟩]),
  (193, [⟨1, 1, [35, 193, 2895, 60795]⟩]),
  (197, [⟨1, 1, [3, 15, 1773, 62055]⟩]),
  (199, [⟨1, 1, [1, 7, 15, 107, 995, 62685]⟩]),
  (211, [⟨1, 1, [5, 15, 63, 211, 1477, 1899, 3165, 4431, 7385, 9495, 13293, 22155]⟩]),
  (223, [⟨1, 1, [1, 45, 3345, 4683, 7805, 10035, 14049, 23415]⟩]),
  (227, [⟨1, 1, [9, 21, 63, 107, 2043, 4767, 7945, 10215, 14301, 23835]⟩]),
  (229, [⟨1, 1, [3, 63, 1603, 4809, 8015, 10305, 14427, 24045]⟩]),
  (233, [⟨1, 1, [1, 9, 45, 233, 1631, 3495, 8155, 10485, 14679, 24465]⟩]),
  (239, [⟨1, 1, [21, 105, 107, 3585, 8365, 10755, 15057, 25095]⟩]),
  (241, [⟨1, 1, [1, 45, 107, 241, 723, 2169, 8435, 10845, 15183, 25305]⟩]),
  (251, [⟨1, 1, [1, 7, 9, 107, 251, 3765, 5271, 11295, 15813, 26355]⟩]),
  (257, [⟨1, 1, [1, 3, 9, 45, 257, 2313, 5397, 11565, 16191, 26985]⟩]),
  (263, [⟨1, 1, [1, 63, 263, 789, 5523, 11835, 16569, 27615]⟩]),
  (269, [⟨1, 1, [35, 107, 269, 807, 4035, 12105, 16947, 28245]⟩]),
  (271, [⟨1, 1, [5, 9, 63, 107, 271, 1897, 2439, 12195, 17073, 28455]⟩]),
  (277, [⟨1, 1, [3, 15, 63, 831, 2493, 12465, 17451, 29085]⟩]),
  (281, [⟨1, 1, [21, 105, 107, 281, 1967, 12645, 17703, 29505]⟩]),
  (283, [⟨1, 1, [3, 35, 1981, 12735, 17829, 29715]⟩]),
  (293, [⟨1, 1, [5, 15, 63, 105, 107, 293, 2051, 10255, 18459, 30765]⟩]),
  (307, [⟨1, 1, [7, 45, 107, 921, 2763, 6447, 19341, 32235]⟩]),
  (311, [⟨1, 1, [1, 3, 105, 107, 2799, 6531, 19593, 32655]⟩]),
  (313, [⟨1, 1, [1, 3, 9, 21, 63, 313, 2191, 6573, 19719, 32865]⟩]),
  (317, [⟨1, 1, [3, 15, 63, 107, 1585, 6657, 19971, 33285]⟩]),
  (331, [⟨1, 1, [1, 7, 21, 63, 107, 331, 2317, 2979, 20853, 34755]⟩]),
  (337, [⟨1, 1, [1, 7, 321, 337, 1011, 3033, 21231, 35385]⟩]),
  (347, [⟨1, 1, [1, 3, 7, 63, 347, 2429, 21861, 36435]⟩]),
  (349, [⟨1, 1, [35, 2443, 21987, 36645]⟩]),
  (353, [⟨1, 1, [1, 321, 353, 1059, 22239, 37065]⟩]),
  (359, [⟨1, 1, [3, 9, 35, 105, 107, 359, 22617, 37695]⟩]),
  (367, [⟨1, 1, [1, 3, 15, 105, 107, 5505, 16515, 38535]⟩]),
  (373, [⟨1, 1, [5, 35, 105, 107, 1119, 3357, 16785, 39165]⟩]),
  (379, [⟨1, 1, [1, 3, 9, 21, 63, 105, 107, 3411, 17055, 39795]⟩]),
  (383, [⟨1, 1, [1, 45, 321, 2681, 17235, 40215]⟩]),
  (389, [⟨1, 1, [1, 3, 7, 21, 63, 1945, 17505, 40845]⟩]),
  (397, [⟨1, 1, [3, 21, 63, 105, 107, 397, 17865, 41685]⟩]),
  (401, [⟨1, 1, [3, 21, 18045, 42105]⟩]),
  (409, [⟨1, 1, [1, 5, 35, 63, 105, 107, 409, 2045, 14315, 42945]⟩]),
  (419, [⟨1, 1, [1, 9, 21, 321, 419, 6285, 8799, 43995]⟩]),
  (421, [⟨1, 1, [1, 3, 7, 21, 421, 6315, 8841, 44205]⟩]),
  (431, [⟨1, 1, [1, 3, 45, 107, 1293, 3879, 9051, 45255]⟩]),
  (433, [⟨1, 1, [5, 15, 45, 105, 107, 433, 1299, 3031, 9093, 45465]⟩]),
  (439, [⟨1, 1, [1, 3, 9, 105, 107, 3951, 9219, 46095]⟩]),
  (443, [⟨1, 1, [1, 3, 7, 45, 443, 3101, 9303, 46515]⟩]),
  (449, [⟨1, 1, [7, 35, 449, 2245, 9429, 47145]⟩]),
  (457, [⟨1, 1, [1, 105, 107, 1371, 9597, 47985]⟩]),
  (461, [⟨1, 1, [1, 7, 15, 63, 461, 3227, 6915, 48405]⟩]),
  (463, [⟨1, 1, [45, 105, 107, 463, 9723, 48615]⟩]),
  (467, [⟨1, 1, [1, 15, 21, 107, 9807, 49035]⟩]),
  (479, [⟨1, 1, [1, 3, 7, 321, 479, 3353, 4311, 50295]⟩]),
  (487, [⟨1, 1, [1, 15, 63, 107, 7305, 51135]⟩]),
  (491, [⟨1, 1, [3, 15, 107, 2455, 4419, 51555]⟩]),
  (499, [⟨1, 1, [1, 5, 21, 1497, 4491, 52395]⟩]),
  (503, [⟨1, 1, [5, 15, 45, 107, 321, 503, 4527, 52815]⟩]),
  (509, [⟨1, 1, [1, 3, 9, 21, 63, 107, 4581, 53445]⟩]),
  (521, [⟨1, 1, [1, 3, 9, 63, 107, 521, 2605, 54705]⟩]),
  (523, [⟨1, 1, [5, 15, 107, 321, 2615, 54915]⟩]),
  (541, [⟨1, 1, [3, 9, 21, 63, 105, 107, 541, 56805]⟩]),
  (547, [⟨1, 1, [1, 3, 107, 57435]⟩]),
  (557, [⟨1, 1, [1, 7, 9, 535, 557, 1671, 19495, 35091]⟩]),
  (563, [⟨1, 1, [1, 3, 7, 63, 321, 1689, 19705, 35469]⟩]),
  (569, [⟨1, 1, [3, 35, 105, 107, 569, 8535, 11949, 35847]⟩]),
  (571, [⟨1, 1, [5, 9, 571, 8565, 11991, 35973]⟩]),
  (577, [⟨1, 1, [1, 3, 7, 21, 107, 321, 20195, 36351]⟩]),
  (587, [⟨1, 1, [1, 45, 107, 321, 1761, 5283, 12327, 36981]⟩]),
  (593, [⟨1, 1, [1, 7, 9, 45, 321, 593, 1779, 4151, 12453, 37359]⟩]),
  (599, [⟨1, 1, [1, 7, 21, 63, 105, 107, 599, 5391, 12579, 37737]⟩]),
  (601, [⟨1, 1, [1, 7, 9, 63, 601, 5409, 12621, 37863]⟩]),
  (607, [⟨1, 1, [15, 5463, 12747, 38241]⟩]),
  (613, [⟨1, 1, [5, 35, 535, 4291, 12873, 38619]⟩]),
  (617, [⟨1, 1, [1, 3, 7, 21, 107, 4319, 12957, 38871]⟩]),
  (619, [⟨1, 1, [5, 535, 619, 3095, 12999, 38997]⟩]),
  (631, [⟨1, 1, [15, 63, 107, 321, 631, 1893, 13251, 39753]⟩]),
  (641, [⟨1, 1, [3, 21, 63, 1923, 13461, 40383]⟩]),
  (643, [⟨1, 1, [1, 7, 21, 63, 107, 321, 643, 4501, 9645, 40509]⟩]),
  (647, [⟨1, 1, [1, 5, 35, 63, 647, 4529, 9705, 40761]⟩]),
  (653, [⟨1, 1, [5, 21, 107, 653, 13713, 41139]⟩]),
  (659, [⟨1, 1, [1, 3, 63, 107, 13839, 41517]⟩]),
  (661, [⟨1, 1, [3, 9, 21, 63, 535, 3305, 9915, 41643]⟩]),
  (673, [⟨1, 1, [1, 7, 21, 63, 673, 2019, 10095, 42399]⟩]),
  (677, [⟨1, 1, [3, 45, 321, 2031, 10155, 42651]⟩]),
  (683, [⟨1, 1, [9, 21, 107, 321, 683, 4781, 6147, 43029]⟩]),
  (691, [⟨1, 1, [9, 35, 321, 691, 10365, 43533]⟩]),
  (701, [⟨1, 1, [3, 9, 21, 63, 10515, 44163]⟩]),
  (709, [⟨1, 1, [1, 15, 21, 3545, 6381, 44667]⟩]),
  (719, [⟨1, 1, [1, 3, 9, 21, 63, 107, 321, 2157, 6471, 45297]⟩]),
  (727, [⟨1, 1, [1, 7, 9, 63, 107, 321, 727, 2181, 5089, 45801]⟩]),
  (733, [⟨1, 1, [3, 9, 35, 107, 535, 733, 6597, 46179]⟩]),
  (739, [⟨1, 1, [1, 35, 107, 739, 6651, 46557]⟩]),
  (743, [⟨1, 1, [1, 9, 21, 63, 107, 321, 6687, 46809]⟩]),
  (751, [⟨1, 1, [3, 15, 535, 751, 5257, 47313]⟩]),
  (757, [⟨1, 1, [1, 3, 15, 757, 5299, 47691]⟩]),
  (761, [⟨1, 1, [5, 35, 63, 321, 5327, 47943]⟩]),
  (769, [⟨1, 1, [1, 15, 45, 107, 321, 769, 3845, 48447]⟩]),
  (773, [⟨1, 1, [1, 3, 9, 21, 107, 773, 3865, 48699]⟩]),
  (787, [⟨1, 1, [1, 5, 63, 107, 321, 787, 2361, 49581]⟩]),
  (797, [⟨1, 1, [1, 15, 107, 321, 2391, 50211]⟩]),
  (809, [⟨1, 1, [3, 9, 21, 105, 107, 4045, 12135, 36405]⟩]),
  (811, [⟨1, 1, [1, 15, 63, 4055, 12165, 36495]⟩]),
  (821, [⟨1, 1, [7, 63, 821, 51723]⟩]),
  (823, [⟨1, 1, [3, 21, 63, 107, 535, 51849]⟩]),
  (827, [⟨1, 1, [21, 63, 321, 52101]⟩]),
  (829, [⟨1, 1, [1, 9, 21, 105, 107, 52227]⟩]),
  (839, [⟨1, 1, [15, 45, 105, 107, 839, 5873, 7551, 37755]⟩]),
  (853, [⟨1, 1, [5, 853, 12795, 38385]⟩]),
  (857, [⟨1, 1, [1, 3, 7, 535, 12855, 38565]⟩]),
  (859, [⟨1, 1, [1, 5, 63, 321, 12885, 38655]⟩]),
  (863, [⟨1, 1, [15, 63, 12945, 38835]⟩]),
  (877, [⟨1, 1, [35, 63, 107, 535, 877, 2631, 7893, 39465]⟩]),
  (881, [⟨1, 1, [1, 7, 107, 321, 881, 2643, 7929, 39645]⟩]),
  (883, [⟨1, 1, [9, 63, 105, 107, 883, 2649, 7947, 39735]⟩]),
  (887, [⟨1, 1, [1, 3, 7, 107, 749, 2661, 7983, 39915]⟩]),
  (907, [⟨1, 1, [1, 7, 9, 45, 105, 107, 907, 2721, 6349, 40815]⟩]),
  (911, [⟨1, 1, [3, 9, 21, 107, 749, 911, 8199, 40995]⟩]),
  (919, [⟨1, 1, [9, 21, 63, 105, 107, 919, 8271, 41355]⟩]),
  (929, [⟨1, 1, [1, 3, 9, 63, 107, 321, 8361, 41805]⟩]),
  (937, [⟨1, 1, [9, 107, 749, 937, 6559, 42165]⟩]),
  (941, [⟨1, 1, [1, 45, 535, 941, 6587, 42345]⟩]),
  (947, [⟨1, 1, [3, 45, 107, 947, 6629, 42615]⟩]),
  (953, [⟨1, 1, [5, 35, 107, 535, 6671, 42885]⟩]),
  (967, [⟨1, 1, [1, 5, 21, 107, 535, 967, 4835, 43515]⟩]),
  (971, [⟨1, 1, [9, 63, 321, 971, 4855, 43695]⟩]),
  (977, [⟨1, 1, [1, 15, 21, 63, 107, 749, 4885, 43965]⟩]),
  (983, [⟨1, 1, [1, 3, 9, 535, 4915, 44235]⟩]),
  (991, [⟨1, 1, [1, 3, 4955, 44595]⟩]),
  (997, [⟨1, 1, [1, 3, 9, 45, 535, 997, 2991, 44865]⟩]),
  (1009, [⟨1, 1, [1, 3, 45, 749, 3027, 45405]⟩]),
  (1013, [⟨1, 1, [1, 105, 107, 321, 3039, 45585]⟩]),
  (1019, [⟨1, 1, [1, 9, 21, 107, 3057, 45855]⟩]),
  (1021, [⟨1, 1, [1, 5, 3063, 45945]⟩]),
  (1031, [⟨1, 1, [1, 3, 7, 45, 321, 3093, 9279, 36085]⟩]),
  (1033, [⟨1, 1, [35, 105, 107, 3099, 9297, 36155]⟩]),
  (1039, [⟨1, 1, [5, 35, 107, 749, 1039, 46755]⟩]),
  (1049, [⟨1, 1, [9, 35, 105, 107, 1049, 47205]⟩]),
  (1051, [⟨1, 1, [21, 107, 1051, 47295]⟩]),
  (1061, [⟨1, 1, [5, 9, 535, 47745]⟩]),
  (1063, [⟨1, 1, [1, 3, 35, 63, 321, 47835]⟩]),
  (1069, [⟨1, 1, [45, 48105]⟩]),
  (1087, [⟨1, 1, [15, 107, 963, 1087, 7609, 38045]⟩]),
  (1091, [⟨1, 1, [1, 7, 21, 63, 749, 1091, 7637, 38185]⟩]),
  (1093, [⟨1, 1, [5, 9, 63, 107, 535, 1093, 7651, 38255]⟩]),
  (1097, [⟨1, 1, [3, 9, 35, 107, 321, 1097, 7679, 38395]⟩]),
  (1103, [⟨1, 1, [1, 3, 105, 1103, 7721, 38605]⟩]),
  (1109, [⟨1, 1, [5, 35, 63, 749, 7763, 38815]⟩]),
  (1117, [⟨1, 1, [1, 5, 45, 321, 7819, 39095]⟩]),
  (1123, [⟨1, 1, [3, 9, 7861, 39305]⟩]),
  (1129, [⟨1, 1, [1, 3, 7, 21, 749, 1129, 5645, 39515]⟩]),
  (1151, [⟨1, 1, [1, 35, 63, 535, 5755, 40285]⟩]),
  (1153, [⟨1, 1, [1, 5, 21, 63, 107, 321, 5765, 40355]⟩]),
  (1163, [⟨1, 1, [1, 9, 21, 107, 963, 1163, 3489, 40705]⟩]),
  (1171, [⟨1, 1, [3, 107, 535, 1171, 3513, 40985]⟩]),
  (1181, [⟨1, 1, [3, 9, 63, 1181, 3543, 41335]⟩]),
  (1187, [⟨1, 1, [1, 63, 107, 749, 3561, 41545]⟩]),
  (1193, [⟨1, 1, [1, 3, 45, 535, 3579, 41755]⟩]),
  (1201, [⟨1, 1, [1, 7, 21, 107, 3603, 42035]⟩]),
  (1213, [⟨1, 1, [35, 107, 535, 1213, 18195, 25473]⟩]),
  (1217, [⟨1, 1, [1, 7, 21, 107, 321, 1217, 18255, 25557]⟩]),
  (1223, [⟨1, 1, [5, 15, 107, 1223, 18345, 25683]⟩]),
  (1229, [⟨1, 1, [63, 963, 1229, 43015]⟩]),
  (1231, [⟨1, 1, [1, 7, 9, 45, 107, 749, 1231, 43085]⟩]),
  (1237, [⟨1, 1, [5, 9, 45, 535, 1237, 43295]⟩]),
  (1249, [⟨1, 1, [3, 15, 107, 321, 749, 43715]⟩]),
  (1259, [⟨1, 1, [1, 7, 15, 107, 535, 44065]⟩]),
  (1277, [⟨1, 1, [1, 3, 21, 963, 1277, 3831, 11493, 26817]⟩]),
  (1279, [⟨1, 1, [7, 21, 107, 749, 1279, 3837, 11511, 26859]⟩]),
  (1283, [⟨1, 1, [1, 3, 9, 21, 107, 535, 1283, 3849, 11547, 26943]⟩]),
  (1289, [⟨1, 1, [1, 7, 35, 321, 1289, 3867, 11601, 27069]⟩]),
  (1291, [⟨1, 1, [3, 45, 105, 107, 1291, 3873, 11619, 27111]⟩]),
  (1297, [⟨1, 1, [5, 63, 107, 321, 749, 3891, 11673, 27237]⟩]),
  (1301, [⟨1, 1, [15, 63, 963, 3903, 11709, 27321]⟩]),
  (1303, [⟨1, 1, [5, 15, 63, 107, 749, 3909, 11727, 27363]⟩]),
  (1307, [⟨1, 1, [9, 21, 63, 107, 535, 3921, 11763, 27447]⟩]),
  (1319, [⟨1, 1, [1, 15, 107, 3957, 11871, 27699]⟩]),
  (1321, [⟨1, 1, [21, 3963, 11889, 27741]⟩]),
  (1327, [⟨1, 1, [1, 15, 63, 963, 1327, 3981, 9289, 27867]⟩]),
  (1361, [⟨1, 1, [1, 15, 45, 107, 535, 1361, 12249, 28581]⟩]),
  (1367, [⟨1, 1, [1, 3, 21, 63, 321, 1367, 12303, 28707]⟩]),
  (1373, [⟨1, 1, [1, 7, 107, 1373, 12357, 28833]⟩]),
  (1381, [⟨1, 1, [1, 3, 9, 21, 107, 963, 12429, 29001]⟩]),
  (1399, [⟨1, 1, [7, 21, 105, 107, 12591, 29379]⟩]),
  (1409, [⟨1, 1, [1, 35, 63, 107, 963, 1409, 9863, 29589]⟩]),
  (1423, [⟨1, 1, [5, 15, 63, 107, 321, 1423, 9961, 29883]⟩]),
  (1427, [⟨1, 1, [3, 45, 63, 105, 107, 1427, 9989, 29967]⟩]),
  (1429, [⟨1, 1, [1, 7, 9, 105, 107, 1429, 10003, 30009]⟩]),
  (1433, [⟨1, 1, [1, 5, 35, 1433, 10031, 30093]⟩]),
  (1439, [⟨1, 1, [21, 107, 321, 749, 10073, 30219]⟩]),
  (1447, [⟨1, 1, [3, 15, 63, 749, 10129, 30387]⟩]),
  (1451, [⟨1, 1, [1, 3, 107, 535, 10157, 30471]⟩]),
  (1453, [⟨1, 1, [1, 3, 15, 535, 10171, 30513]⟩]),
  (1459, [⟨1, 1, [3, 63, 105, 107, 10213, 30639]⟩]),
  (1471, [⟨1, 1, [5, 15, 107, 321, 749, 1471, 7355, 30891]⟩]),
  (1481, [⟨1, 1, [105, 107, 535, 1481, 7405, 31101]⟩]),
  (1483, [⟨1, 1, [15, 107, 535, 1483, 7415, 31143]⟩]),
  (1487, [⟨1, 1, [1, 3, 45, 107, 321, 1487, 7435, 31227]⟩]),
  (1489, [⟨1, 1, [3, 63, 321, 1489, 7445, 31269]⟩]),
  (1493, [⟨1, 1, [1, 15, 21, 63, 107, 1493, 7465, 31353]⟩]),
  (1499, [⟨1, 1, [45, 107, 321, 963, 7495, 31479]⟩]),
  (1511, [⟨1, 1, [7, 45, 107, 749, 7555, 31731]⟩]),
  (1523, [⟨1, 1, [5, 9, 45, 321, 7615, 31983]⟩]),
  (1531, [⟨1, 1, [7, 21, 7655, 32151]⟩]),
  (1543, [⟨1, 1, [1, 7, 9, 63, 963, 1543, 4629, 32403]⟩]),
  (1549, [⟨1, 1, [1, 35, 749, 1549, 4647, 32529]⟩]),
  (1553, [⟨1, 1, [15, 63, 535, 1553, 4659, 32613]⟩]),
  (1559, [⟨1, 1, [1, 3, 9, 21, 321, 1559, 4677, 32739]⟩]),
  (1567, [⟨1, 1, [1, 3, 7, 1567, 4701, 32907]⟩]),
  (1571, [⟨1, 1, [1, 3, 15, 107, 321, 963, 4713, 32991]⟩]),
  (1579, [⟨1, 1, [1, 3, 107, 963, 4737, 33159]⟩]),
  (1583, [⟨1, 1, [5, 45, 107, 749, 4749, 33243]⟩]),
  (1597, [⟨1, 1, [1, 7, 35, 63, 105, 107, 4791, 33537]⟩]),
  (1601, [⟨1, 1, [1, 7, 35, 107, 4803, 33621]⟩]),
  (1607, [⟨1, 1, [7, 535, 963, 1607, 11249, 24105]⟩]),
  (1609, [⟨1, 1, [1, 3, 7, 21, 107, 321, 963, 1609, 11263, 24135]⟩]),
  (1613, [⟨1, 1, [1, 3, 15, 63, 107, 321, 749, 1613, 11291, 24195]⟩]),
  (1619, [⟨1, 1, [5, 45, 963, 1619, 11333, 24285]⟩]),
  (1621, [⟨1, 1, [3, 9, 63, 107, 749, 1621, 11347, 24315]⟩]),
  (1627, [⟨1, 1, [1, 7, 35, 107, 535, 1627, 11389, 24405]⟩]),
  (1637, [⟨1, 1, [63, 105, 107, 1637, 11459, 24555]⟩]),
  (1657, [⟨1, 1, [7, 35, 107, 963, 1657, 34797]⟩]),
  (1663, [⟨1, 1, [1, 15, 107, 749, 1663, 34923]⟩]),
  (1667, [⟨1, 1, [7, 63, 107, 535, 1667, 35007]⟩]),
  (1669, [⟨1, 1, [1, 3, 9, 21, 63, 535, 1669, 35049]⟩]),
  (1693, [⟨1, 1, [3, 15, 63, 321, 963, 35553]⟩]),
  (1697, [⟨1, 1, [1, 3, 7, 21, 107, 321, 749, 35637]⟩]),
  (1699, [⟨1, 1, [1, 15, 45, 107, 963, 35679]⟩]),
  (1709, [⟨1, 1, [1, 35, 63, 107, 535, 35889]⟩]),
  (1721, [⟨1, 1, [1, 15, 45, 105, 107, 36141]⟩]),
  (1723, [⟨1, 1, [1, 3, 21, 63, 107, 36183]⟩]),
  (1733, [⟨1, 1, [5, 35, 535, 963, 8665, 25995]⟩]),
  (1741, [⟨1, 1, [3, 9, 45, 107, 321, 749, 8705, 26115]⟩]),
  (1747, [⟨1, 1, [1, 7, 35, 963, 8735, 26205]⟩]),
  (1753, [⟨1, 1, [1, 7, 21, 749, 8765, 26295]⟩]),
  (1759, [⟨1, 1, [15, 535, 8795, 26385]⟩]),
  (1777, [⟨1, 1, [3, 35, 1605, 1777, 5331, 26655]⟩]),
  (1783, [⟨1, 1, [9, 21, 107, 321, 963, 1783, 5349, 26745]⟩]),
  (1787, [⟨1, 1, [3, 9, 21, 63, 107, 321, 749, 1787, 5361, 26805]⟩]),
  (1789, [⟨1, 1, [1, 21, 107, 321, 749, 1789, 5367, 26835]⟩]),
  (1801, [⟨1, 1, [1, 5, 749, 1801, 5403, 27015]⟩]),
  (1811, [⟨1, 1, [1, 63, 321, 1811, 5433, 27165]⟩]),
  (1823, [⟨1, 1, [7, 45, 107, 1605, 5469, 27345]⟩]),
  (1831, [⟨1, 1, [1, 21, 63, 107, 321, 963, 5493, 27465]⟩]),
  (1847, [⟨1, 1, [9, 35, 107, 749, 5541, 27705]⟩]),
  (1861, [⟨1, 1, [3, 9, 63, 321, 5583, 27915]⟩]),
  (1867, [⟨1, 1, [1, 9, 63, 107, 5601, 28005]⟩]),
  (1871, [⟨1, 1, [1, 35, 5613, 28065]⟩]),
  (1873, [⟨1, 1, [3, 15, 107, 749, 963, 1873, 13111, 16857]⟩]),
  (1877, [⟨1, 1, [1, 7, 21, 63, 1605, 1877, 13139, 16893]⟩]),
  (1879, [⟨1, 1, [1, 21, 1605, 1879, 13153, 16911]⟩]),
  (1889, [⟨1, 1, [1, 15, 21, 63, 107, 321, 749, 1889, 13223, 17001]⟩]),
  (1901, [⟨1, 1, [1, 107, 749, 1901, 13307, 17109]⟩]),
  (1907, [⟨1, 1, [5, 107, 535, 1907, 13349, 17163]⟩]),
  (1913, [⟨1, 1, [9, 107, 321, 1913, 13391, 17217]⟩]),
  (1931, [⟨1, 1, [5, 21, 107, 1605, 1931, 28965]⟩]),
  (1933, [⟨1, 1, [5, 15, 45, 1605, 1933, 28995]⟩]),
  (1949, [⟨1, 1, [1, 3, 7, 45, 107, 963, 1949, 29235]⟩]),
  (1951, [⟨1, 1, [1, 3, 7, 21, 63, 963, 1951, 29265]⟩]),
  (1973, [⟨1, 1, [35, 63, 105, 107, 1973, 29595]⟩]),
  (1979, [⟨1, 1, [1, 105, 1979, 29685]⟩]),
  (1987, [⟨1, 1, [1, 3, 105, 107, 1605, 29805]⟩]),
  (1993, [⟨1, 1, [3, 15, 1605, 29895]⟩]),
  (1997, [⟨1, 1, [1, 15, 21, 63, 107, 321, 963, 29955]⟩]),
  (1999, [⟨1, 1, [1, 3, 9, 21, 107, 321, 963, 29985]⟩]),
  (2003, [⟨1, 1, [9, 321, 963, 30045]⟩]),
  (2011, [⟨1, 1, [3, 63, 963, 30165]⟩]),
  (2017, [⟨1, 1, [1, 3, 15, 63, 749, 30255]⟩]),
  (2027, [⟨1, 1, [1, 9, 63, 107, 321, 30405]⟩]),
  (2029, [⟨1, 1, [7, 107, 321, 30435]⟩]),
  (2039, [⟨1, 1, [105, 30585]⟩]),
  (2053, [⟨1, 1, [7, 21, 63, 1605, 10265, 18477]⟩]),
  (2063, [⟨1, 1, [1, 7, 21, 63, 321, 963, 10315, 18567]⟩]),
  (2069, [⟨1, 1, [7, 107, 321, 749, 10345, 18621]⟩]),
  (2081, [⟨1, 1, [1, 5, 45, 749, 10405, 18729]⟩]),
  (2083, [⟨1, 1, [1, 9, 21, 63, 107, 535, 10415, 18747]⟩]),
  (2087, [⟨1, 1, [1, 9, 63, 535, 10435, 18783]⟩]),
  (2089, [⟨1, 1, [9, 535, 10445, 18801]⟩]),
  (2099, [⟨1, 1, [3, 9, 105, 107, 10495, 18891]⟩]),
  (2111, [⟨1, 1, [1, 3, 21, 321, 1605, 2111, 6333, 18999]⟩]),
  (2113, [⟨1, 1, [7, 63, 107, 749, 963, 2113, 6339, 19017]⟩]),
  (2129, [⟨1, 1, [1, 3, 105, 321, 963, 2129, 6387, 19161]⟩]),
  (2131, [⟨1, 1, [3, 9, 35, 321, 963, 2131, 6393, 19179]⟩]),
  (2137, [⟨1, 1, [3, 9, 63, 107, 963, 2137, 6411, 19233]⟩]),
  (2141, [⟨1, 1, [1, 3, 9, 45, 963, 2141, 6423, 19269]⟩]),
  (2143, [⟨1, 1, [5, 35, 63, 107, 749, 2143, 6429, 19287]⟩]),
  (2153, [⟨1, 1, [7, 107, 535, 2153, 6459, 19377]⟩]),
  (2161, [⟨1, 1, [1, 7, 9, 63, 321, 2161, 6483, 19449]⟩]),
  (2179, [⟨1, 1, [3, 9, 21, 63, 321, 1605, 6537, 19611]⟩]),
  (2203, [⟨1, 1, [3, 15, 321, 963, 6609, 19827]⟩]),
  (2207, [⟨1, 1, [5, 107, 321, 749, 6621, 19863]⟩]),
  (2213, [⟨1, 1, [1, 3, 35, 963, 6639, 19917]⟩]),
  (2221, [⟨1, 1, [1, 3, 9, 749, 6663, 19989]⟩]),
  (2237, [⟨1, 1, [7, 63, 105, 107, 6711, 20133]⟩]),
  (2239, [⟨1, 1, [1, 9, 105, 107, 6717, 20151]⟩]),
  (2243, [⟨1, 1, [1, 3, 35, 63, 6729, 20187]⟩]),
  (2251, [⟨1, 1, [1, 7, 9, 63, 107, 321, 1605, 2251, 6753, 15757]⟩]),
  (2267, [⟨1, 1, [9, 35, 1605, 2267, 6801, 15869]⟩]),
  (2269, [⟨1, 1, [9, 21, 63, 535, 963, 2269, 6807, 15883]⟩]),
  (2273, [⟨1, 1, [21, 63, 107, 321, 963, 2273, 6819, 15911]⟩]),
  (2281, [⟨1, 1, [3, 63, 107, 321, 749, 2281, 6843, 15967]⟩]),
  (2287, [⟨1, 1, [1, 105, 963, 2287, 6861, 16009]⟩]),
  (2293, [⟨1, 1, [1, 3, 35, 107, 749, 2293, 6879, 16051]⟩]),
  (2297, [⟨1, 1, [9, 21, 749, 2297, 6891, 16079]⟩]),
  (2309, [⟨1, 1, [3, 107, 321, 2309, 6927, 16163]⟩]),
  (2311, [⟨1, 1, [7, 45, 321, 2311, 6933, 16177]⟩]),
  (2333, [⟨1, 1, [35, 107, 321, 1605, 2333, 20997]⟩]),
  (2339, [⟨1, 1, [3, 15, 63, 107, 749, 963, 2339, 21051]⟩]),
  (2341, [⟨1, 1, [1, 3, 21, 107, 749, 963, 2341, 21069]⟩]),
  (2347, [⟨1, 1, [1, 7, 63, 1605, 2347, 21123]⟩]),
  (2351, [⟨1, 1, [3, 63, 535, 963, 2351, 21159]⟩]),
  (2357, [⟨1, 1, [5, 107, 321, 963, 2357, 21213]⟩]),
  (2371, [⟨1, 1, [1, 5, 35, 963, 2371, 21339]⟩]),
  (2377, [⟨1, 1, [3, 21, 63, 749, 2377, 21393]⟩]),
  (2381, [⟨1, 1, [1, 3, 15, 63, 107, 535, 2381, 21429]⟩]),
  (2383, [⟨1, 1, [5, 21, 107, 535, 2383, 21447]⟩]),
  (2389, [⟨1, 1, [9, 63, 107, 321, 2389, 21501]⟩]),
  (2393, [⟨1, 1, [1, 3, 63, 321, 2393, 21537]⟩]),
  (2399, [⟨1, 1, [1, 7, 105, 107, 2399, 21591]⟩]),
  (2411, [⟨1, 1, [3, 45, 2247, 21699]⟩]),
  (2417, [⟨1, 1, [1, 15, 21, 63, 107, 321, 1605, 21753]⟩]),
  (2423, [⟨1, 1, [45, 321, 1605, 21807]⟩]),
  (2437, [⟨1, 1, [1, 3, 7, 21, 63, 535, 963, 21933]⟩]),
  (2441, [⟨1, 1, [1, 9, 21, 63, 107, 321, 963, 21969]⟩]),
  (2447, [⟨1, 1, [1, 3, 35, 321, 963, 22023]⟩]),
  (2459, [⟨1, 1, [1, 35, 963, 22131]⟩]),
  (2467, [⟨1, 1, [1, 3, 9, 21, 749, 22203]⟩]),
  (2473, [⟨1, 1, [1, 7, 15, 63, 535, 22257]⟩]),
  (2477, [⟨1, 1, [1, 21, 63, 107, 321, 22293]⟩]),
  (2503, [⟨1, 1, [1, 3, 63, 2247, 2503, 17521]⟩]),
  (2521, [⟨1, 1, [1, 5, 21, 107, 749, 963, 2521, 17647]⟩]),
  (2531, [⟨1, 1, [1, 3, 21, 63, 535, 963, 2531, 17717]⟩]),
  (2539, [⟨1, 1, [1, 9, 21, 63, 321, 963, 2539, 17773]⟩]),
  (2543, [⟨1, 1, [1, 3, 9, 21, 63, 107, 321, 749, 2543, 17801]⟩]),
  (2549, [⟨1, 1, [3, 45, 107, 963, 2549, 17843]⟩]),
  (2551, [⟨1, 1, [5, 35, 63, 963, 2551, 17857]⟩]),
  (2557, [⟨1, 1, [9, 45, 107, 749, 2557, 17899]⟩]),
  (2579, [⟨1, 1, [1, 7, 9, 321, 2579, 18053]⟩]),
  (2591, [⟨1, 1, [5, 21, 2591, 18137]⟩]),
  (2593, [⟨1, 1, [1, 105, 107, 749, 1605, 18151]⟩]),
  (2609, [⟨1, 1, [1, 5, 21, 535, 1605, 18263]⟩]),
  (2617, [⟨1, 1, [1, 5, 35, 321, 1605, 18319]⟩]),
  (2621, [⟨1, 1, [3, 45, 107, 749, 963, 18347]⟩]),
  (2633, [⟨1, 1, [1, 5, 63, 535, 963, 18431]⟩]),
  (2647, [⟨1, 1, [5, 35, 107, 321, 749, 18529]⟩]),
  (2657, [⟨1, 1, [1, 3, 963, 18599]⟩]),
  (2659, [⟨1, 1, [1, 15, 45, 107, 749, 18613]⟩]),
  (2663, [⟨1, 1, [5, 63, 749, 18641]⟩]),
  (2671, [⟨1, 1, [1, 3, 15, 63, 535, 18697]⟩]),
  (2677, [⟨1, 1, [1, 3, 35, 107, 321, 18739]⟩]),
  (2683, [⟨1, 1, [7, 35, 63, 105, 107, 18781]⟩]),
  (2687, [⟨1, 1, [5, 105, 107, 18809]⟩]),
  (2689, [⟨1, 1, [15, 45, 107, 18823]⟩]),
  (2693, [⟨1, 1, [1, 3, 63, 18851]⟩]),
  (2699, [⟨1, 1, [3, 45, 321, 2247, 2699, 13495]⟩]),
  (2707, [⟨1, 1, [7, 63, 107, 2247, 2707, 13535]⟩]),
  (2711, [⟨1, 1, [3, 15, 63, 2247, 2711, 13555]⟩]),
  (2713, [⟨1, 1, [3, 9, 21, 2247, 2713, 13565]⟩]),
  (2719, [⟨1, 1, [5, 35, 63, 107, 321, 1605, 2719, 13595]⟩]),
  (2729, [⟨1, 1, [5, 9, 63, 107, 749, 963, 2729, 13645]⟩]),
  (2731, [⟨1, 1, [1, 7, 21, 107, 749, 963, 2731, 13655]⟩]),
  (2741, [⟨1, 1, [3, 1605, 2741, 13705]⟩]),
  (2749, [⟨1, 1, [1, 3, 21, 107, 321, 963, 2749, 13745]⟩]),
  (2753, [⟨1, 1, [1, 35, 321, 963, 2753, 13765]⟩]),
  (2767, [⟨1, 1, [21, 963, 2767, 13835]⟩]),
  (2777, [⟨1, 1, [1, 3, 35, 63, 107, 535, 2777, 13885]⟩]),
  (2789, [⟨1, 1, [7, 21, 107, 321, 2789, 13945]⟩]),
  (2791, [⟨1, 1, [3, 21, 63, 321, 2791, 13955]⟩]),
  (2797, [⟨1, 1, [7, 45, 105, 107, 2797, 13985]⟩]),
  (2801, [⟨1, 1, [1, 15, 45, 107, 2801, 14005]⟩]),
  (2803, [⟨1, 1, [1, 3, 9, 107, 2803, 14015]⟩]),
  (2819, [⟨1, 1, [1, 9, 21, 63, 107, 749, 1605, 14095]⟩]),
  (2833, [⟨1, 1, [9, 21, 63, 535, 1605, 14165]⟩]),
  (2837, [⟨1, 1, [1, 535, 1605, 14185]⟩]),
  (2843, [⟨1, 1, [5, 9, 63, 321, 1605, 14215]⟩]),
  (2851, [⟨1, 1, [107, 749, 963, 14255]⟩]),
  (2857, [⟨1, 1, [1, 3, 9, 63, 1605, 14285]⟩]),
  (2861, [⟨1, 1, [7, 21, 63, 535, 963, 14305]⟩]),
  (2879, [⟨1, 1, [105, 107, 963, 14395]⟩]),
  (2887, [⟨1, 1, [7, 21, 963, 14435]⟩]),
  (2897, [⟨1, 1, [3, 9, 749, 14485]⟩]),
  (2903, [⟨1, 1, [1, 3, 21, 63, 535, 14515]⟩]),
  (2909, [⟨1, 1, [3, 9, 45, 107, 321, 14545]⟩]),
  (2917, [⟨1, 1, [5, 21, 63, 105, 107, 14585]⟩]),
  (2927, [⟨1, 1, [1, 7, 63, 14635]⟩]),
  (2939, [⟨1, 1, [5, 9, 45, 107, 321, 2247, 2939, 8817]⟩]),
  (2953, [⟨1, 1, [9, 63, 107, 2247, 2953, 8859]⟩]),
  (2957, [⟨1, 1, [7, 21, 63, 2247, 2957, 8871]⟩]),
  (2963, [⟨1, 1, [3, 63, 535, 1605, 2963, 8889]⟩]),
  (2969, [⟨1, 1, [1, 5, 35, 107, 321, 1605, 2969, 8907]⟩]),
  (2971, [⟨1, 1, [1, 5, 35, 63, 321, 1605, 2971, 8913]⟩]),
  (2999, [⟨1, 1, [1, 7, 15, 107, 321, 963, 2999, 8997]⟩]),
  (3001, [⟨1, 1, [1, 7, 15, 63, 321, 963, 3001, 9003]⟩]),
  (3011, [⟨1, 1, [1, 7, 9, 63, 107, 963, 3011, 9033]⟩]),
  (3019, [⟨1, 1, [1, 3, 7, 963, 3019, 9057]⟩]),
  (3023, [⟨1, 1, [9, 21, 107, 749, 3023, 9069]⟩]),
  (3037, [⟨1, 1, [1, 7, 35, 535, 3037, 9111]⟩]),
  (3041, [⟨1, 1, [1, 7, 9, 45, 107, 321, 3041, 9123]⟩]),
  (3049, [⟨1, 1, [1, 3, 35, 63, 105, 107, 3049, 9147]⟩]),
  (3061, [⟨1, 1, [5, 45, 3061, 9183]⟩]),
  (3067, [⟨1, 1, [3, 9, 21, 63, 107, 535, 2247, 9201]⟩]),
  (3079, [⟨1, 1, [1, 3, 9, 45, 107, 321, 2247, 9237]⟩]),
  (3083, [⟨1, 1, [3, 15, 63, 321, 2247, 9249]⟩]),
  (3089, [⟨1, 1, [1, 7, 9, 45, 107, 749, 1605, 9267]⟩]),
  (3109, [⟨1, 1, [7, 63, 107, 321, 1605, 9327]⟩]),
  (3119, [⟨1, 1, [1, 3, 7, 63, 107, 749, 963, 9357]⟩]),
  (3121, [⟨1, 1, [1, 3, 7, 21, 107, 749, 963, 9363]⟩]),
  (3137, [⟨1, 1, [1, 7, 9, 535, 963, 9411]⟩]),
  (3163, [⟨1, 1, [1, 5, 963, 9489]⟩]),
  (3167, [⟨1, 1, [1, 7, 21, 107, 749, 9501]⟩]),
  (3169, [⟨1, 1, [1, 9, 21, 63, 749, 9507]⟩]),
  (3181, [⟨1, 1, [1, 3, 7, 45, 535, 9543]⟩]),
  (3187, [⟨1, 1, [1, 15, 21, 107, 321, 9561]⟩]),
  (3191, [⟨1, 1, [15, 45, 321, 9573]⟩]),
  (3203, [⟨1, 1, [1, 21, 107, 9609]⟩]),
  (3209, [⟨1, 1, [3, 9627]⟩]),
  (3217, [⟨1, 1, [63, 107, 321, 963, 3217, 4815]⟩]),
  (3221, [⟨1, 1, [1, 9, 21, 63, 321, 963, 3221, 4815]⟩]),
  (3229, [⟨1, 1, [1, 3, 45, 107, 321, 749, 3229, 4815]⟩]),
  (3251, [⟨1, 1, [5, 9, 45, 749, 3251, 4815]⟩]),
  (3253, [⟨1, 1, [21, 749, 3253, 4815]⟩]),
  (3257, [⟨1, 1, [7, 45, 107, 535, 3257, 4815]⟩]),
  (3259, [⟨1, 1, [5, 9, 107, 535, 3259, 4815]⟩]),
  (3271, [⟨1, 1, [107, 321, 3271, 4815]⟩]),
  (3299, [⟨1, 1, [3, 963, 3299, 3745]⟩]),
  (3301, [⟨1, 1, [9, 63, 107, 749, 3301, 3745]⟩]),
  (3307, [⟨1, 1, [5, 15, 45, 749, 3307, 3745]⟩]),
  (3313, [⟨1, 1, [1, 3, 9, 45, 107, 535, 3313, 3745]⟩]),
  (3319, [⟨1, 1, [1, 5, 45, 535, 3319, 3745]⟩]),
  (3323, [⟨1, 1, [1, 3, 15, 63, 107, 321, 3323, 3745]⟩]),
  (3329, [⟨1, 1, [3, 9, 63, 321, 3329, 3745]⟩]),
  (3331, [⟨1, 1, [1, 15, 21, 321, 3331, 3745]⟩]),
  (3343, [⟨1, 1, [1, 7, 15, 107, 3343, 3745]⟩]),
  (3347, [⟨1, 1, [9, 45, 3347, 3745]⟩]),
  (3359, [⟨1, 1, [5, 35, 321, 963, 2247, 3359]⟩]),
  (3361, [⟨1, 1, [1, 3, 105, 107, 321, 749, 2247, 3361]⟩]),
  (3371, [⟨1, 1, [5, 21, 107, 963, 2247, 3371]⟩]),
  (3373, [⟨1, 1, [1, 3, 7, 21, 63, 963, 2247, 3373]⟩]),
  (3389, [⟨1, 1, [5, 749, 2247, 3389]⟩]),
  (3391, [⟨1, 1, [1, 3, 7, 63, 107, 535, 2247, 3391]⟩]),
  (3407, [⟨1, 1, [7, 21, 63, 321, 2247, 3407]⟩]),
  (3413, [⟨1, 1, [21, 63, 107, 749, 1605, 3413]⟩]),
  (3433, [⟨1, 1, [1, 3, 21, 535, 1605, 3433]⟩]),
  (3449, [⟨1, 1, [7, 35, 107, 749, 963, 3449]⟩]),
  (3457, [⟨1, 1, [1, 5, 35, 63, 1605, 3457]⟩]),
  (3461, [⟨1, 1, [7, 21, 1605, 3461]⟩]),
  (3463, [⟨1, 1, [1, 3, 9, 21, 63, 535, 963, 3463]⟩]),
  (3467, [⟨1, 1, [21, 535, 963, 3467]⟩]),
  (3469, [⟨1, 1, [1, 5, 21, 63, 107, 321, 963, 3469]⟩]),
  (3491, [⟨1, 1, [1, 15, 21, 63, 963, 3491]⟩]),
  (3499, [⟨1, 1, [1, 9, 45, 107, 749, 3499]⟩]),
  (3511, [⟨1, 1, [1, 5, 35, 107, 535, 3511]⟩]),
  (3517, [⟨1, 1, [1, 3, 9, 21, 535, 3517]⟩]),
  (3527, [⟨1, 1, [1, 3, 9, 45, 321, 3527]⟩]),
  (3529, [⟨1, 1, [5, 15, 321, 3529]⟩]),
  (3533, [⟨1, 1, [1, 7, 45, 105, 107, 3533]⟩]),
  (3539, [⟨1, 1, [9, 35, 107, 3539]⟩]),
  (3541, [⟨1, 1, [1, 5, 107, 3541]⟩]),
  (3547, [⟨1, 1, [15, 321, 963, 2247]⟩]),
  (3557, [⟨1, 1, [1, 3, 45, 107, 963, 2247]⟩]),
  (3559, [⟨1, 1, [1, 3, 9, 107, 963, 2247]⟩]),
  (3571, [⟨1, 1, [1, 3, 7, 107, 749, 2247]⟩]),
  (3581, [⟨1, 1, [45, 107, 535, 2247]⟩]),
  (3583, [⟨1, 1, [9, 107, 535, 2247]⟩]),
  (3593, [⟨1, 1, [1, 7, 35, 107, 321, 2247]⟩]),
  (3607, [⟨1, 1, [5, 107, 749, 1605]⟩]),
  (3613, [⟨1, 1, [1, 3, 107, 2247]⟩]),
  (3617, [⟨1, 1, [1, 3, 35, 2247]⟩]),
  (3623, [⟨1, 1, [3, 35, 535, 1605]⟩]),
  (3631, [⟨1, 1, [1, 107, 321, 1605]⟩]),
  (3637, [⟨1, 1, [321, 1605]⟩]),
  (3643, [⟨1, 1, [1, 105, 107, 1605]⟩]),
  (3659, [⟨1, 1, [1, 3, 7, 21, 535, 963]⟩]),
  (3671, [⟨1, 1, [9, 21, 321, 963]⟩]),
  (3673, [⟨1, 1, [3, 35, 63, 107, 321, 749]⟩]),
  (3677, [⟨1, 1, [1, 7, 21, 107, 321, 749]⟩]),
  (3691, [⟨1, 1, [35, 63, 107, 749]⟩]),
  (3697, [⟨1, 1, [1, 3, 9, 21, 63, 749]⟩]),
  (3701, [⟨1, 1, [1, 3, 21, 749]⟩]),
  (3709, [⟨1, 1, [1, 3, 7, 21, 63, 535]⟩]),
  (3719, [⟨1, 1, [1, 21, 107, 321]⟩]),
  (3727, [⟨1, 1, [1, 9, 21, 63, 105, 107]⟩]),
  (3733, [⟨1, 1, [7, 21, 63, 107]⟩]),
  (3739, [⟨1, 1, [1, 5, 21, 63]⟩]),
  (3761, [⟨2, 1, [1, 105, 107, 963, 3761, 57245, 240429, 2012135]⟩]),
  (3767, [⟨2, 1, [1, 35, 63, 535, 963, 3767, 11449, 34347, 240429, 2015345]⟩]),
  (3769, [⟨2, 1, [1, 21, 63, 1605, 11449, 34347, 240429, 2016415]⟩]),
  (3779, [⟨2, 1, [1, 21, 63, 107, 2247, 3779, 11449, 80143, 171735, 2021765]⟩]),
  (3793, [⟨2, 1, [3, 15, 63, 107, 963, 2247, 240429, 2029255]⟩]),
  (3797, [⟨2, 1, [1, 63, 107, 321, 963, 2247, 3797, 57245, 171735, 2031395]⟩]),
  (3803, [⟨2, 1, [3, 9, 45, 321, 3745, 3803, 11449, 34347, 171735, 2034605]⟩]),
  (3821, [⟨2, 1, [1, 35, 535, 3821, 4815, 11449, 171735, 2044235]⟩]),
  (3823, [⟨2, 1, [105, 1605, 3823, 11449, 171735, 2045305]⟩]),
  (3833, [⟨2, 1, [1, 21, 107, 321, 963, 3833, 4815, 57245, 103041, 2050655]⟩]),
  (3847, [⟨2, 1, [5, 9, 63, 107, 963, 2247, 3847, 34347, 103041, 2058145]⟩]),
  (3851, [⟨2, 1, [1, 749, 3851, 6741, 11449, 34347, 80143, 2060285]⟩]),
  (3853, [⟨2, 1, [7, 63, 3745, 3853, 11449, 34347, 80143, 2061355]⟩]),
  (3863, [⟨2, 1, [105, 107, 535, 11449, 103041, 2066705]⟩]),
  (3877, [⟨2, 1, [7, 35, 107, 535, 3877, 4815, 80143, 2074195]⟩]),
  (3881, [⟨2, 1, [1, 3, 35, 63, 321, 1605, 80143, 2076335]⟩]),
  (3889, [⟨2, 1, [7, 21, 535, 963, 3889, 4815, 57245, 2080615]⟩]),
  (3907, [⟨2, 1, [1, 7, 9, 45, 34347, 2090245]⟩]),
  (3911, [⟨2, 1, [1, 5, 21, 107, 3745, 11449, 11733, 2092385]⟩]),
  (3917, [⟨2, 1, [1, 9, 21, 107, 535, 3917, 11449, 2095595]⟩]),
  (3919, [⟨2, 1, [15, 45, 107, 749, 11449, 2096665]⟩]),
  (3923, [⟨2, 1, [3, 21, 107, 963, 3923, 2098805]⟩]),
  (3929, [⟨2, 1, [1, 9, 21, 63, 535, 1605, 11449, 400715, 420403, 1261209]⟩]),
  (3931, [⟨2, 1, [1, 7, 15, 63, 107, 321, 963, 3931, 4815, 400715, 420617, 1261851]⟩]),
  (3943, [⟨2, 1, [1, 3, 7, 45, 107, 749, 11449, 34347, 103041, 240429, 421901, 1265703]⟩]),
  (3947, [⟨2, 1, [5, 35, 63, 107, 321, 963, 3947, 34347, 103041, 240429, 422329, 1266987]⟩]),
  (3967, [⟨2, 1, [9, 35, 107, 321, 749, 3967, 103041, 240429, 424469, 1273407]⟩]),
  (3989, [⟨2, 1, [21, 63, 107, 321, 963, 11449, 57245, 240429, 426823, 1280469]⟩]),
  (4001, [⟨2, 1, [1, 3, 15, 63, 321, 963, 2247, 11449, 34347, 240429, 428107, 1284321]⟩]),
  (4003, [⟨2, 1, [1, 45, 107, 11449, 34347, 240429, 428321, 1284963]⟩]),
  (4007, [⟨2, 1, [3, 9, 21, 107, 535, 4007, 34347, 240429, 428749, 1286247]⟩]),
  (4013, [⟨2, 1, [5, 21, 107, 1605, 4013, 11449, 80143, 171735, 429391, 1288173]⟩]),
  (4019, [⟨2, 1, [1, 3, 15, 535, 2247, 4019, 11449, 240429, 430033, 1290099]⟩]),
  (4021, [⟨2, 1, [1, 7, 35, 107, 963, 2247, 11449, 240429, 430247, 1290741]⟩]),
  (4027, [⟨2, 1, [3, 15, 63, 321, 4027, 240429, 430889, 1292667]⟩]),
  (4049, [⟨2, 1, [1, 3, 7, 63, 107, 535, 34347, 171735, 433243, 1299729]⟩]),
  (4051, [⟨2, 1, [1, 7, 45, 107, 749, 3745, 4051, 11449, 80143, 103041, 433457, 1300371]⟩]),
  (4057, [⟨2, 1, [1, 45, 107, 749, 4057, 4815, 11449, 171735, 434099, 1302297]⟩]),
  (4073, [⟨2, 1, [63, 107, 749, 4073, 57245, 103041, 435811, 1307433]⟩]),
  (4079, [⟨2, 1, [1, 3, 7, 45, 321, 1605, 4079, 11449, 34347, 103041, 436453, 1309359]⟩]),
  (4091, [⟨2, 1, [7, 35, 321, 3745, 4091, 11449, 34347, 80143, 437737, 1313211]⟩]),
  (4093, [⟨2, 1, [1, 3, 107, 535, 4093, 11449, 34347, 80143, 437951, 1313853]⟩]),
  (4099, [⟨2, 1, [1, 5, 35, 63, 1605, 4099, 11449, 103041, 438593, 1315779]⟩]),
  (4111, [⟨2, 1, [1, 5, 21, 63, 3745, 4111, 11449, 80143, 439877, 1319631]⟩]),
  (4127, [⟨2, 1, [1, 15, 45, 107, 749, 2247, 11449, 57245, 441589, 1324767]⟩]),
  (4129, [⟨2, 1, [1, 5, 63, 535, 1605, 4129, 4815, 57245, 441803, 1325409]⟩]),
  (4133, [⟨2, 1, [1, 15, 21, 63, 4133, 57245, 442231, 1326693]⟩]),
  (4139, [⟨2, 1, [9, 21, 63, 107, 963, 4139, 11449, 34347, 442873, 1328619]⟩]),
  (4153, [⟨2, 1, [3, 15, 63, 107, 535, 2247, 11449, 12459, 444371, 1333113]⟩]),
  (4157, [⟨2, 1, [9, 63, 535, 3745, 4157, 11449, 444799, 1334397]⟩]),
  (4159, [⟨2, 1, [1, 3, 9, 21, 107, 749, 4159, 11449, 445013, 1335039]⟩]),
  (4177, [⟨2, 1, [1, 3, 9, 749, 3745, 4177, 11449, 171735, 240429, 1340817]⟩]),
  (4201, [⟨2, 1, [1, 3, 9, 321, 3745, 11449, 34347, 103041, 240429, 1348521]⟩]),
  (4211, [⟨2, 1, [9, 107, 1605, 4211, 4815, 11449, 34347, 80143, 240429, 1351731]⟩]),
  (4217, [⟨2, 1, [1, 45, 963, 11449, 34347, 80143, 240429, 1353657]⟩]),
  (4219, [⟨2, 1, [1, 7, 63, 107, 4219, 4815, 11449, 103041, 240429, 1354299]⟩]),
  (4229, [⟨2, 1, [1, 3, 7, 21, 63, 107, 4229, 103041, 240429, 1357509]⟩]),
  (4231, [⟨2, 1, [1, 7, 107, 321, 749, 103041, 240429, 1358151]⟩]),
  (4241, [⟨2, 1, [3, 15, 63, 321, 963, 2247, 4241, 80143, 240429, 1361361]⟩]),
  (4243, [⟨2, 1, [1, 7, 35, 321, 4243, 80143, 240429, 1362003]⟩]),
  (4253, [⟨2, 1, [1, 3, 63, 535, 1605, 4253, 4815, 57245, 240429, 1365213]⟩]),
  (4259, [⟨2, 1, [1, 3, 35, 535, 963, 57245, 240429, 1367139]⟩]),
  (4261, [⟨2, 1, [1, 21, 107, 535, 4261, 4815, 11449, 34347, 240429, 1367781]⟩]),
  (4271, [⟨2, 1, [1, 45, 107, 535, 4271, 34347, 240429, 1370991]⟩]),
  (4273, [⟨2, 1, [1, 107, 1605, 34347, 240429, 1371633]⟩]),
  (4283, [⟨2, 1, [1, 3, 7, 21, 321, 3745, 4283, 11449, 240429, 1374843]⟩]),
  (4289, [⟨2, 1, [1, 3, 21, 963, 4289, 4815, 240429, 1376769]⟩]),
  (4297, [⟨2, 1, [3, 21, 63, 107, 321, 3745, 4297, 57245, 171735, 1379337]⟩]),
  (4327, [⟨2, 1, [7, 45, 321, 963, 4327, 11449, 171735, 1388967]⟩]),
  (4337, [⟨2, 1, [5, 21, 107, 749, 171735, 1392177]⟩]),
  (4339, [⟨2, 1, [3, 35, 963, 3745, 4339, 57245, 103041, 1392819]⟩]),
  (4349, [⟨2, 1, [3, 21, 535, 3745, 11449, 34347, 103041, 1396029]⟩]),
  (4357, [⟨2, 1, [1, 9, 21, 63, 107, 321, 2247, 34347, 103041, 1398597]⟩]),
  (4363, [⟨2, 1, [1, 9, 107, 4363, 11449, 34347, 80143, 1400523]⟩]),
  (4373, [⟨2, 1, [1, 3, 9, 21, 4373, 6741, 103041, 1403733]⟩]),
  (4391, [⟨2, 1, [1, 3, 9, 107, 321, 4391, 80143, 1409511]⟩]),
  (4397, [⟨2, 1, [1, 5, 535, 1605, 4397, 11449, 57245, 1411437]⟩]),
  (4409, [⟨2, 1, [1, 35, 63, 107, 535, 4409, 4815, 11449, 34347, 1415289]⟩]),
  (4421, [⟨2, 1, [3, 9, 321, 1605, 34347, 1419141]⟩]),
  (4423, [⟨2, 1, [1, 45, 107, 3745, 4423, 11449, 13269, 1419783]⟩]),
  (4441, [⟨2, 1, [1, 7, 9, 63, 3745, 1425561]⟩]),
  (4447, [⟨2, 1, [1, 3, 15, 107, 749, 1605, 4447, 11449, 34347, 171735, 475829, 721287]⟩]),
  (4451, [⟨2, 1, [7, 321, 963, 11449, 34347, 171735, 476257, 721287]⟩]),
  (4457, [⟨2, 1, [1, 5, 535, 3745, 34347, 171735, 476899, 721287]⟩]),
  (4463, [⟨2, 1, [1, 35, 535, 2247, 4463, 11449, 80143, 103041, 477541, 721287]⟩]),
  (4481, [⟨2, 1, [15, 321, 4481, 171735, 479467, 721287]⟩]),
  (4483, [⟨2, 1, [1, 9, 63, 321, 1605, 171735, 479681, 721287]⟩]),
  (4493, [⟨2, 1, [1, 535, 963, 4493, 4815, 11449, 34347, 103041, 480751, 721287]⟩]),
  (4507, [⟨2, 1, [1, 5, 63, 107, 749, 1605, 34347, 103041, 482249, 721287]⟩]),
  (4513, [⟨2, 1, [1, 3, 45, 963, 4513, 11449, 34347, 80143, 482891, 721287]⟩]),
  (4517, [⟨2, 1, [1, 7, 9, 63, 4517, 6741, 11449, 103041, 483319, 721287]⟩]),
  (4519, [⟨2, 1, [7, 35, 107, 1605, 2247, 4519, 11449, 103041, 483533, 721287]⟩]),
  (4523, [⟨2, 1, [1, 3, 35, 63, 535, 2247, 11449, 103041, 483961, 721287]⟩]),
  (4547, [⟨2, 1, [35, 63, 107, 963, 2247, 80143, 486529, 721287]⟩]),
  (4549, [⟨2, 1, [1, 7, 9, 45, 535, 80143, 486743, 721287]⟩]),
  (4561, [⟨2, 1, [1, 15, 21, 63, 321, 1605, 4561, 57245, 488027, 721287]⟩]),
  (4567, [⟨2, 1, [9, 21, 63, 107, 4567, 4815, 11449, 34347, 488669, 721287]⟩]),
  (4583, [⟨2, 1, [3, 535, 4583, 4815, 57245, 171735, 490381, 515205]⟩]),
  (4591, [⟨2, 1, [5, 15, 45, 107, 535, 4591, 4815, 11449, 491237, 721287]⟩]),
  (4597, [⟨2, 1, [9, 45, 1605, 11449, 491879, 721287]⟩]),
  (4603, [⟨2, 1, [1, 5, 45, 4603, 492521, 721287]⟩]),
  (4621, [⟨2, 1, [5, 45, 535, 1605, 11449, 171735, 494447, 515205]⟩]),
  (4637, [⟨2, 1, [5, 15, 63, 107, 749, 1605, 57245, 103041, 496159, 515205]⟩]),
  (4639, [⟨2, 1, [9, 107, 1605, 4639, 4815, 11449, 34347, 103041, 496373, 515205]⟩]),
  (4643, [⟨2, 1, [5, 35, 107, 749, 4643, 11449, 34347, 103041, 496801, 515205]⟩]),
  (4649, [⟨2, 1, [3, 9, 21, 107, 3745, 4649, 34347, 103041, 497443, 515205]⟩]),
  (4651, [⟨2, 1, [1, 3, 35, 63, 963, 4651, 34347, 103041, 497657, 515205]⟩]),
  (4657, [⟨2, 1, [1, 3, 7, 21, 63, 107, 1605, 2247, 4657, 11449, 34347, 80143, 498299, 515205]⟩]),
  (4663, [⟨2, 1, [45, 105, 107, 11449, 34347, 80143, 498941, 515205]⟩]),
  (4673, [⟨2, 1, [5, 107, 535, 3745, 4673, 103041, 500011, 515205]⟩]),
  (4679, [⟨2, 1, [1, 3, 9, 63, 535, 103041, 500653, 515205]⟩]),
  (4691, [⟨2, 1, [7, 21, 63, 107, 749, 963, 4691, 80143, 501937, 515205]⟩]),
  (4703, [⟨2, 1, [9, 63, 107, 963, 11449, 57245, 503221, 515205]⟩]),
  (4721, [⟨2, 1, [1, 3, 7, 45, 535, 4721, 4815, 34347, 505147, 515205]⟩]),
  (4723, [⟨2, 1, [3, 15, 321, 2247, 4723, 34347, 505361, 515205]⟩]),
  (4729, [⟨2, 1, [1, 3, 7, 749, 4729, 4815, 34347, 103041, 400715, 506003]⟩]),
  (4733, [⟨2, 1, [1, 3, 63, 107, 749, 3745, 34347, 103041, 400715, 506431]⟩]),
  (4751, [⟨2, 1, [1, 63, 535, 1605, 508357, 515205]⟩]),
  (4759, [⟨2, 1, [1, 5, 21, 107, 2247, 103041, 400715, 509213]⟩]),
  (4783, [⟨2, 1, [1, 7, 15, 107, 535, 2247, 11449, 57245, 400715, 511781]⟩]),
  (4787, [⟨2, 1, [1, 7, 15, 63, 107, 3745, 4787, 57245, 400715, 512209]⟩]),
  (4789, [⟨2, 1, [3, 45, 107, 963, 4789, 57245, 400715, 512423]⟩]),
  (4793, [⟨2, 1, [5, 9, 45, 105, 107, 57245, 400715, 512851]⟩]),
  (4799, [⟨2, 1, [1, 3, 7, 45, 963, 2247, 11449, 34347, 400715, 513493]⟩]),
  (4801, [⟨2, 1, [5, 15, 107, 321, 11449, 34347, 400715, 513707]⟩]),
  (4813, [⟨2, 1, [5, 15, 1605, 4813, 11449, 171735, 240429, 514991]⟩]),
  (4817, [⟨2, 1, [1, 7, 45, 749, 11449, 171735, 240429, 515419]⟩]),
  (4831, [⟨2, 1, [15, 107, 1605, 2247, 400715, 516917]⟩]),
  (4861, [⟨2, 1, [1, 7, 63, 321, 2247, 4861, 11449, 103041, 240429, 520127]⟩]),
  (4871, [⟨2, 1, [9, 35, 4815, 103041, 240429, 521197]⟩]),
  (4877, [⟨2, 1, [1, 3, 21, 63, 107, 535, 2247, 4877, 11449, 80143, 240429, 521839]⟩]),
  (4889, [⟨2, 1, [1, 5, 35, 107, 2247, 80143, 240429, 523123]⟩]),
  (4903, [⟨2, 1, [1, 21, 107, 535, 4903, 57245, 240429, 524621]⟩]),
  (4909, [⟨2, 1, [15, 107, 321, 963, 2247, 4909, 11449, 34347, 240429, 525263]⟩]),
  (4919, [⟨2, 1, [1, 3, 35, 963, 4919, 34347, 240429, 526333]⟩]),
  (4931, [⟨2, 1, [1, 3, 9, 21, 107, 321, 11449, 80143, 171735, 527617]⟩]),
  (4933, [⟨2, 1, [1, 9, 21, 63, 321, 3745, 4933, 11449, 240429, 527831]⟩]),
  (4937, [⟨2, 1, [3, 9, 21, 107, 321, 749, 2247, 11449, 240429, 528259]⟩]),
  (4943, [⟨2, 1, [1, 3, 7, 535, 963, 4943, 240429, 528901]⟩]),
  (4951, [⟨2, 1, [1, 9, 63, 1605, 4951, 57245, 171735, 529757]⟩]),
  (4957, [⟨2, 1, [3, 63, 107, 749, 3745, 4957, 11449, 34347, 171735, 530399]⟩]),
  (4967, [⟨2, 1, [1, 5, 21, 63, 321, 1605, 4967, 34347, 171735, 531469]⟩]),
  (4969, [⟨2, 1, [1, 35, 63, 321, 3745, 34347, 171735, 531683]⟩]),
  (4973, [⟨2, 1, [5, 15, 63, 107, 4815, 4973, 11449, 80143, 103041, 532111]⟩]),
  (4987, [⟨2, 1, [3, 9, 21, 63, 1605, 11449, 171735, 533609]⟩]),
  (4993, [⟨2, 1, [1, 3, 7, 21, 63, 107, 749, 3745, 171735, 534251]⟩]),
  (4999, [⟨2, 1, [1, 7, 9, 107, 321, 2247, 4999, 57245, 103041, 534893]⟩]),
  (5003, [⟨2, 1, [1, 21, 107, 321, 1605, 57245, 103041, 535321]⟩]),
  (5009, [⟨2, 1, [1, 5, 35, 5009, 11449, 34347, 103041, 535963]⟩]),
  (5011, [⟨2, 1, [1, 7, 21, 63, 535, 1605, 11449, 34347, 103041, 536177]⟩]),
  (5021, [⟨2, 1, [1, 5, 21, 107, 321, 749, 4815, 5021, 11449, 34347, 80143, 537247]⟩]),
  (5023, [⟨2, 1, [3, 9, 21, 63, 107, 749, 2247, 5023, 11449, 34347, 80143, 537461]⟩]),
  (5039, [⟨2, 1, [1, 5, 321, 963, 2247, 5039, 103041, 539173]⟩]),
  (5051, [⟨2, 1, [5, 9, 107, 749, 2247, 11449, 80143, 540457]⟩]),
  (5059, [⟨2, 1, [21, 63, 963, 2247, 80143, 541313]⟩]),
  (5077, [⟨2, 1, [3, 15, 63, 749, 57245, 543239]⟩]),
  (5081, [⟨2, 1, [1, 63, 535, 963, 5081, 11449, 34347, 543667]⟩]),
  (5087, [⟨2, 1, [3, 9, 45, 749, 3745, 5087, 34347, 544309]⟩]),
  (5099, [⟨2, 1, [1, 9, 321, 11449, 15297, 545593]⟩]),
  (5101, [⟨2, 1, [5, 963, 5101, 6741, 11449, 545807]⟩]),
  (5107, [⟨2, 1, [1, 3, 9, 63, 535, 3745, 11449, 546449]⟩]),
  (5113, [⟨2, 1, [35, 63, 535, 1605, 5113, 547091]⟩]),
  (5119, [⟨2, 1, [7, 21, 63, 107, 963, 2247, 5119, 34347, 103041, 400715]⟩]),
  (5147, [⟨2, 1, [1, 9, 21, 63, 107, 321, 749, 5147, 103041, 400715]⟩]),
  (5153, [⟨2, 1, [3, 21, 63, 4815, 5153, 11449, 80143, 400715]⟩]),
  (5167, [⟨2, 1, [3, 63, 963, 2247, 80143, 400715]⟩]),
  (5171, [⟨2, 1, [3, 63, 535, 3745, 5171, 11449, 57245, 400715]⟩]),
  (5179, [⟨2, 1, [21, 535, 4815, 5179, 57245, 400715]⟩]),
  (5189, [⟨2, 1, [45, 3745, 5189, 11449, 34347, 400715]⟩]),
  (5197, [⟨2, 1, [4815, 5197, 34347, 400715]⟩]),
  (5209, [⟨2, 1, [9, 21, 63, 535, 5209, 11449, 171735, 240429]⟩]),
  (5227, [⟨2, 1, [9, 63, 5227, 400715]⟩]),
  (5231, [⟨2, 1, [7, 21, 63, 400715]⟩]),
  (5233, [⟨2, 1, [5, 15, 45, 107, 321, 963, 2247, 5233, 11449, 34347, 103041, 240429]⟩]),
  (5237, [⟨2, 1, [1, 5, 21, 63, 107, 321, 963, 2247, 11449, 34347, 103041, 240429]⟩]),
  (5261, [⟨2, 1, [5, 63, 535, 963, 5261, 11449, 103041, 240429]⟩]),
  (5273, [⟨2, 1, [21, 63, 321, 2247, 103041, 240429]⟩]),
  (5279, [⟨2, 1, [3, 9, 35, 963, 5279, 11449, 80143, 240429]⟩]),
  (5281, [⟨2, 1, [3, 9, 35, 107, 321, 963, 2247, 11449, 80143, 240429]⟩]),
  (5297, [⟨2, 1, [5, 21, 107, 321, 5297, 11449, 57245, 240429]⟩]),
  (5303, [⟨2, 1, [1, 3, 15, 321, 3745, 5303, 57245, 240429]⟩]),
  (5309, [⟨2, 1, [15, 63, 535, 963, 57245, 240429]⟩]),
  (5323, [⟨2, 1, [1, 3, 63, 107, 749, 5323, 34347, 240429]⟩]),
  (5333, [⟨2, 1, [1, 3, 7, 63, 107, 749, 3745, 11449, 80143, 171735]⟩]),
  (5347, [⟨2, 1, [1, 3, 35, 107, 1605, 2247, 5347, 240429]⟩]),
  (5351, [⟨2, 1, [1, 7, 63, 321, 3745, 240429]⟩]),
  (5381, [⟨2, 1, [35, 107, 535, 4815, 5381, 11449, 80143, 103041]⟩]),
  (5387, [⟨2, 1, [5, 15, 45, 749, 2247, 11449, 80143, 103041]⟩]),
  (5393, [⟨2, 1, [21, 321, 963, 5393, 11449, 171735]⟩]),
  (5399, [⟨2, 1, [5, 9, 107, 4815, 5399, 171735]⟩]),
  (5407, [⟨2, 1, [1, 3, 9, 63, 107, 963, 4815, 5407, 57245, 103041]⟩]),
  (5413, [⟨2, 1, [1, 3, 21, 321, 963, 2247, 57245, 103041]⟩]),
  (5417, [⟨2, 1, [1, 15, 21, 63, 535, 3745, 5417, 11449, 34347, 103041]⟩]),
  (5419, [⟨2, 1, [1, 7, 9, 45, 107, 1605, 5419, 11449, 34347, 103041]⟩]),
  (5431, [⟨2, 1, [1, 21, 749, 2247, 34347, 103041]⟩]),
  (5437, [⟨2, 1, [1, 5, 35, 107, 321, 749, 5437, 11449, 34347, 80143]⟩]),
  (5441, [⟨2, 1, [1, 3, 7, 45, 107, 321, 963, 11449, 34347, 80143]⟩]),
  (5443, [⟨2, 1, [1, 3, 9, 21, 4815, 5443, 11449, 103041]⟩]),
  (5449, [⟨2, 1, [1, 3, 15, 107, 749, 1605, 11449, 103041]⟩]),
  (5471, [⟨2, 1, [1, 15, 21, 107, 321, 2247, 5471, 80143]⟩]),
  (5477, [⟨2, 1, [5, 45, 321, 80143]⟩]),
  (5479, [⟨2, 1, [1, 35, 63, 107, 321, 963, 2247, 5479, 11449, 57245]⟩]),
  (5483, [⟨2, 1, [1, 3, 45, 107, 1605, 2247, 11449, 57245]⟩]),
  (5501, [⟨2, 1, [1, 45, 107, 321, 749, 2247, 11449, 34347]⟩]),
  (5503, [⟨2, 1, [1, 9, 107, 749, 11449, 34347]⟩]),
  (5507, [⟨2, 1, [1, 3, 35, 63, 535, 963, 5507, 34347]⟩]),
  (5519, [⟨2, 1, [1, 3, 21, 63, 107, 321, 1605, 5519, 6741, 11449]⟩]),
  (5521, [⟨2, 1, [5, 45, 107, 321, 963, 4815, 5521, 11449]⟩]),
  (5527, [⟨2, 1, [1, 5, 107, 1605, 2247, 11449]⟩]),
  (5531, [⟨2, 1, [1, 3, 7, 63, 107, 749, 3745, 5531]⟩]),
  (5557, [⟨3, 1, [1, 103041, 240429, 594599]⟩]),
  (5563, [⟨3, 1, [107, 535, 2247, 103041]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified107 : verifyBatch 107 qPrimes rows107 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows109 : List Row := [
  (11, [⟨1, 1, [1, 7, 55, 109, 231, 327, 545, 763, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (13, [⟨1, 1, [39, 109, 195, 327, 545, 763, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (17, [⟨1, 1, [3, 9, 17, 85, 109, 327, 545, 763, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (19, [⟨1, 1, [19, 35, 109, 327, 545, 763, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (23, [⟨1, 1, [5, 15, 23, 327, 545, 763, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (29, [⟨1, 1, [7, 29, 45, 109, 545, 763, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (31, [⟨1, 1, [21, 109, 545, 763, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (37, [⟨1, 1, [1, 21, 37, 109, 327, 763, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (41, [⟨1, 1, [7, 41, 327, 763, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (43, [⟨1, 1, [9, 43, 45, 109, 327, 545, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (47, [⟨1, 1, [1, 3, 35, 47, 109, 763, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (53, [⟨1, 1, [15, 763, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (59, [⟨1, 1, [1, 7, 45, 545, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (61, [⟨1, 1, [1, 5, 35, 61, 109, 327, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (67, [⟨1, 1, [1, 9, 21, 327, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (71, [⟨1, 1, [5, 15, 109, 327, 763, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (73, [⟨1, 1, [1, 5, 63, 109, 981, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (79, [⟨1, 1, [7, 21, 79, 109, 763, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (83, [⟨1, 1, [1, 3, 9, 83, 763, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (89, [⟨1, 1, [1, 3, 21, 109, 545, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (97, [⟨1, 1, [3, 109, 327, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (101, [⟨1, 1, [101, 109, 763, 981, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (103, [⟨1, 1, [1, 5, 35, 109, 763, 981, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (107, [⟨1, 1, [9, 21, 109, 1635, 2289, 3815, 4905, 6867, 11445, 34335]⟩]),
  (113, [⟨1, 1, [1, 3, 45, 565, 1017, 3955, 5085, 7119, 11865, 35595]⟩]),
  (127, [⟨1, 1, [15, 45, 127, 635, 2667, 8001, 13335, 40005]⟩]),
  (131, [⟨1, 1, [3, 15, 109, 131, 1179, 8253, 13755, 41265]⟩]),
  (137, [⟨1, 1, [3, 137, 685, 6165, 14385, 43155]⟩]),
  (139, [⟨1, 1, [1, 3, 109, 139, 973, 4865, 14595, 43785]⟩]),
  (149, [⟨1, 1, [1, 15, 21, 63, 149, 1341, 15645, 46935]⟩]),
  (151, [⟨1, 1, [1, 7, 15, 63, 151, 453, 15855, 47565]⟩]),
  (157, [⟨1, 1, [1, 9, 21, 157, 1099, 3297, 9891, 49455]⟩]),
  (163, [⟨1, 1, [1, 7, 9, 163, 489, 1467, 10269, 51345]⟩]),
  (167, [⟨1, 1, [3, 501, 10521, 52605]⟩]),
  (173, [⟨1, 1, [1, 7, 15, 109, 173, 865, 7785, 54495]⟩]),
  (179, [⟨1, 1, [5, 15, 63, 537, 6265, 56385]⟩]),
  (181, [⟨1, 1, [1, 5, 35, 181, 543, 1629, 3801, 57015]⟩]),
  (191, [⟨1, 1, [1, 7, 63, 955, 1719, 60165]⟩]),
  (193, [⟨1, 1, [1, 15, 109, 193, 1737, 60795]⟩]),
  (197, [⟨1, 1, [21, 63, 591, 62055]⟩]),
  (199, [⟨1, 1, [5, 21, 63, 109, 199, 597, 981, 995, 1393, 1791, 2985, 4179, 6965, 8955, 12537, 20895]⟩]),
  (211, [⟨1, 1, [5, 15, 45, 211, 633, 1477, 3165, 4431, 7385, 9495, 13293, 22155]⟩]),
  (223, [⟨1, 1, [7, 63, 109, 223, 1561, 4683, 7805, 10035, 14049, 23415]⟩]),
  (227, [⟨1, 1, [1, 7, 15, 63, 681, 4767, 7945, 10215, 14301, 23835]⟩]),
  (229, [⟨1, 1, [15, 45, 109, 4809, 8015, 10305, 14427, 24045]⟩]),
  (233, [⟨1, 1, [1, 7, 21, 109, 233, 3495, 8155, 10485, 14679, 24465]⟩]),
  (239, [⟨1, 1, [3, 9, 35, 2151, 8365, 10755, 15057, 25095]⟩]),
  (241, [⟨1, 1, [3, 21, 63, 109, 241, 1205, 8435, 10845, 15183, 25305]⟩]),
  (251, [⟨1, 1, [1, 7, 109, 2259, 5271, 11295, 15813, 26355]⟩]),
  (257, [⟨1, 1, [21, 771, 5397, 11565, 16191, 26985]⟩]),
  (263, [⟨1, 1, [1, 45, 105, 109, 263, 1841, 2367, 11835, 16569, 27615]⟩]),
  (269, [⟨1, 1, [45, 807, 2421, 12105, 16947, 28245]⟩]),
  (271, [⟨1, 1, [5, 9, 63, 271, 2439, 12195, 17073, 28455]⟩]),
  (277, [⟨1, 1, [7, 105, 109, 277, 831, 12465, 17451, 29085]⟩]),
  (281, [⟨1, 1, [1, 3, 9, 63, 281, 12645, 17703, 29505]⟩]),
  (283, [⟨1, 1, [45, 109, 2547, 9905, 17829, 29715]⟩]),
  (293, [⟨1, 1, [15, 63, 293, 10255, 18459, 30765]⟩]),
  (307, [⟨1, 1, [7, 63, 109, 307, 921, 6447, 19341, 32235]⟩]),
  (311, [⟨1, 1, [1, 5, 105, 109, 311, 6531, 19593, 32655]⟩]),
  (313, [⟨1, 1, [9, 21, 63, 6573, 19719, 32865]⟩]),
  (317, [⟨1, 1, [5, 9, 45, 109, 951, 4755, 19971, 33285]⟩]),
  (331, [⟨1, 1, [5, 9, 109, 2979, 20853, 34755]⟩]),
  (337, [⟨1, 1, [15, 105, 109, 1685, 21231, 35385]⟩]),
  (347, [⟨1, 1, [1, 3, 63, 105, 109, 347, 2429, 3123, 15615, 36435]⟩]),
  (349, [⟨1, 1, [1, 21, 105, 109, 349, 5235, 15705, 36645]⟩]),
  (353, [⟨1, 1, [1, 3, 45, 109, 1765, 3177, 15885, 37065]⟩]),
  (359, [⟨1, 1, [1, 7, 63, 359, 1077, 2513, 16155, 37695]⟩]),
  (367, [⟨1, 1, [1, 3, 7, 2569, 16515, 38535]⟩]),
  (373, [⟨1, 1, [1, 7, 373, 1119, 16785, 39165]⟩]),
  (379, [⟨1, 1, [1, 5, 35, 379, 17055, 39795]⟩]),
  (383, [⟨1, 1, [5, 15, 63, 3447, 13405, 40215]⟩]),
  (389, [⟨1, 1, [1, 3, 63, 109, 389, 1945, 13615, 40845]⟩]),
  (397, [⟨1, 1, [1, 7, 21, 327, 397, 5955, 8337, 41685]⟩]),
  (401, [⟨1, 1, [1, 5, 63, 401, 14035, 42105]⟩]),
  (409, [⟨1, 1, [1, 9, 327, 409, 1227, 2863, 8589, 42945]⟩]),
  (419, [⟨1, 1, [1, 15, 327, 2933, 8799, 43995]⟩]),
  (421, [⟨1, 1, [1, 7, 9, 2947, 8841, 44205]⟩]),
  (431, [⟨1, 1, [1, 5, 105, 1293, 9051, 45255]⟩]),
  (433, [⟨1, 1, [3, 9, 105, 109, 433, 3031, 6495, 45465]⟩]),
  (439, [⟨1, 1, [3, 9, 35, 109, 9219, 46095]⟩]),
  (443, [⟨1, 1, [7, 21, 63, 327, 443, 1329, 6645, 46515]⟩]),
  (449, [⟨1, 1, [5, 15, 45, 327, 449, 3143, 4041, 47145]⟩]),
  (457, [⟨1, 1, [1, 5, 21, 63, 6855, 47985]⟩]),
  (461, [⟨1, 1, [1, 21, 63, 327, 461, 1383, 4149, 48405]⟩]),
  (463, [⟨1, 1, [7, 109, 463, 1389, 4167, 48615]⟩]),
  (467, [⟨1, 1, [1, 21, 109, 327, 467, 1401, 3269, 49035]⟩]),
  (479, [⟨1, 1, [1, 3, 9, 21, 109, 479, 3353, 50295]⟩]),
  (487, [⟨1, 1, [3, 21, 109, 327, 2435, 51135]⟩]),
  (491, [⟨1, 1, [1, 63, 327, 491, 1473, 51555]⟩]),
  (499, [⟨1, 1, [63, 105, 109, 4491, 17465, 31437]⟩]),
  (503, [⟨1, 1, [3, 15, 105, 109, 503, 52815]⟩]),
  (509, [⟨1, 1, [9, 35, 63, 327, 509, 2545, 17815, 32067]⟩]),
  (521, [⟨1, 1, [1, 7, 9, 45, 327, 1563, 18235, 32823]⟩]),
  (523, [⟨1, 1, [3, 15, 109, 1569, 18305, 32949]⟩]),
  (541, [⟨1, 1, [3, 35, 109, 327, 1623, 4869, 11361, 34083]⟩]),
  (547, [⟨1, 1, [1, 5, 45, 105, 109, 547, 1641, 3829, 11487, 34461]⟩]),
  (557, [⟨1, 1, [5, 15, 109, 5013, 11697, 35091]⟩]),
  (563, [⟨1, 1, [3, 15, 63, 109, 327, 3941, 11823, 35469]⟩]),
  (569, [⟨1, 1, [3, 9, 21, 327, 569, 2845, 11949, 35847]⟩]),
  (571, [⟨1, 1, [1, 3, 7, 109, 571, 2855, 11991, 35973]⟩]),
  (577, [⟨1, 1, [9, 545, 577, 1731, 12117, 36351]⟩]),
  (587, [⟨1, 1, [3, 545, 587, 4109, 8805, 36981]⟩]),
  (593, [⟨1, 1, [9, 109, 327, 593, 12453, 37359]⟩]),
  (599, [⟨1, 1, [1, 5, 21, 327, 12579, 37737]⟩]),
  (601, [⟨1, 1, [1, 7, 9, 109, 12621, 37863]⟩]),
  (607, [⟨1, 1, [1, 3, 45, 3035, 9105, 38241]⟩]),
  (613, [⟨1, 1, [7, 45, 545, 1839, 9195, 38619]⟩]),
  (617, [⟨1, 1, [9, 35, 109, 1851, 9255, 38871]⟩]),
  (619, [⟨1, 1, [5, 545, 619, 4333, 5571, 38997]⟩]),
  (631, [⟨1, 1, [1, 3, 7, 45, 109, 327, 9465, 39753]⟩]),
  (641, [⟨1, 1, [1, 7, 45, 3205, 5769, 40383]⟩]),
  (643, [⟨1, 1, [1, 45, 109, 327, 643, 1929, 5787, 40509]⟩]),
  (647, [⟨1, 1, [1, 3, 9, 45, 647, 1941, 5823, 40761]⟩]),
  (653, [⟨1, 1, [3, 9, 63, 1959, 5877, 41139]⟩]),
  (659, [⟨1, 1, [1, 5, 35, 63, 659, 1977, 4613, 41517]⟩]),
  (661, [⟨1, 1, [3, 9, 545, 661, 5949, 41643]⟩]),
  (673, [⟨1, 1, [1, 3, 9, 109, 545, 673, 4711, 42399]⟩]),
  (677, [⟨1, 1, [1, 3, 45, 105, 109, 677, 4739, 42651]⟩]),
  (683, [⟨1, 1, [1, 3, 9, 327, 4781, 43029]⟩]),
  (691, [⟨1, 1, [1, 7, 9, 105, 109, 691, 3455, 43533]⟩]),
  (701, [⟨1, 1, [35, 63, 545, 701, 2103, 44163]⟩]),
  (709, [⟨1, 1, [1, 9, 21, 545, 2127, 44667]⟩]),
  (719, [⟨1, 1, [1, 7, 327, 3595, 10785, 32355]⟩]),
  (727, [⟨1, 1, [1, 3, 21, 63, 105, 109, 727, 45801]⟩]),
  (733, [⟨1, 1, [35, 109, 327, 46179]⟩]),
  (739, [⟨1, 1, [9, 35, 63, 545, 739, 5173, 6651, 33255]⟩]),
  (743, [⟨1, 1, [7, 63, 105, 109, 743, 5201, 6687, 33435]⟩]),
  (751, [⟨1, 1, [1, 21, 63, 105, 109, 751, 11265, 33795]⟩]),
  (757, [⟨1, 1, [1, 3, 7, 63, 109, 327, 11355, 34065]⟩]),
  (761, [⟨1, 1, [1, 5, 35, 109, 11415, 34245]⟩]),
  (769, [⟨1, 1, [1, 5, 21, 63, 109, 3845, 6921, 34605]⟩]),
  (773, [⟨1, 1, [1, 7, 63, 545, 773, 2319, 6957, 34785]⟩]),
  (787, [⟨1, 1, [1, 7, 9, 45, 109, 2361, 7083, 35415]⟩]),
  (797, [⟨1, 1, [35, 63, 797, 2391, 5579, 35865]⟩]),
  (809, [⟨1, 1, [9, 21, 109, 545, 7281, 36405]⟩]),
  (811, [⟨1, 1, [1, 7, 9, 63, 109, 327, 7299, 36495]⟩]),
  (821, [⟨1, 1, [1, 15, 45, 109, 327, 821, 5747, 36945]⟩]),
  (823, [⟨1, 1, [1, 3, 327, 823, 5761, 37035]⟩]),
  (827, [⟨1, 1, [63, 763, 5789, 37215]⟩]),
  (829, [⟨1, 1, [1, 7, 109, 545, 5803, 37305]⟩]),
  (839, [⟨1, 1, [1, 5, 21, 109, 545, 839, 4195, 37755]⟩]),
  (853, [⟨1, 1, [1, 9, 63, 327, 4265, 38385]⟩]),
  (857, [⟨1, 1, [1, 7, 9, 63, 4285, 38565]⟩]),
  (859, [⟨1, 1, [1, 15, 763, 859, 2577, 38655]⟩]),
  (863, [⟨1, 1, [1, 5, 21, 109, 327, 863, 2589, 38835]⟩]),
  (877, [⟨1, 1, [5, 15, 105, 109, 2631, 39465]⟩]),
  (881, [⟨1, 1, [5, 35, 763, 2643, 7929, 30835]⟩]),
  (883, [⟨1, 1, [1, 5, 35, 63, 545, 2649, 7947, 30905]⟩]),
  (887, [⟨1, 1, [5, 9, 327, 2661, 7983, 31045]⟩]),
  (907, [⟨1, 1, [7, 63, 545, 40815]⟩]),
  (911, [⟨1, 1, [3, 35, 63, 105, 109, 40995]⟩]),
  (919, [⟨1, 1, [5, 21, 63, 545, 8271, 32165]⟩]),
  (929, [⟨1, 1, [15, 45, 763, 929, 6503, 32515]⟩]),
  (937, [⟨1, 1, [1, 3, 21, 105, 109, 937, 6559, 32795]⟩]),
  (941, [⟨1, 1, [1, 15, 109, 763, 6587, 32935]⟩]),
  (947, [⟨1, 1, [5, 15, 109, 327, 6629, 33145]⟩]),
  (953, [⟨1, 1, [3, 21, 6671, 33355]⟩]),
  (967, [⟨1, 1, [15, 63, 109, 763, 4835, 33845]⟩]),
  (971, [⟨1, 1, [1, 15, 109, 545, 4855, 33985]⟩]),
  (977, [⟨1, 1, [1, 35, 105, 109, 4885, 34195]⟩]),
  (983, [⟨1, 1, [5, 45, 763, 983, 2949, 34405]⟩]),
  (991, [⟨1, 1, [3, 9, 35, 105, 109, 991, 2973, 34685]⟩]),
  (997, [⟨1, 1, [3, 15, 63, 763, 2991, 34895]⟩]),
  (1009, [⟨1, 1, [7, 21, 3027, 35315]⟩]),
  (1013, [⟨1, 1, [1, 5, 763, 1013, 15195, 21273]⟩]),
  (1019, [⟨1, 1, [5, 35, 327, 1019, 15285, 21399]⟩]),
  (1021, [⟨1, 1, [1, 3, 15, 105, 109, 1021, 15315, 21441]⟩]),
  (1031, [⟨1, 1, [1, 3, 45, 545, 1031, 36085]⟩]),
  (1033, [⟨1, 1, [5, 21, 109, 327, 1033, 36155]⟩]),
  (1039, [⟨1, 1, [3, 63, 1039, 36365]⟩]),
  (1049, [⟨1, 1, [1, 3, 15, 109, 327, 36715]⟩]),
  (1051, [⟨1, 1, [3, 45, 63, 105, 109, 36785]⟩]),
  (1061, [⟨1, 1, [1, 3, 15, 63, 109, 545, 1061, 3183, 9549, 22281]⟩]),
  (1063, [⟨1, 1, [63, 545, 1063, 3189, 9567, 22323]⟩]),
  (1069, [⟨1, 1, [1, 9, 105, 109, 1069, 3207, 9621, 22449]⟩]),
  (1087, [⟨1, 1, [5, 45, 109, 3261, 9783, 22827]⟩]),
  (1091, [⟨1, 1, [1, 7, 9, 981, 1091, 3273, 7637, 22911]⟩]),
  (1093, [⟨1, 1, [1, 5, 105, 763, 1093, 3279, 7651, 22953]⟩]),
  (1097, [⟨1, 1, [3, 15, 63, 545, 1097, 3291, 7679, 23037]⟩]),
  (1103, [⟨1, 1, [5, 35, 105, 109, 1103, 3309, 7721, 23163]⟩]),
  (1109, [⟨1, 1, [1, 9, 981, 1109, 9981, 23289]⟩]),
  (1117, [⟨1, 1, [1, 3, 63, 109, 327, 1117, 10053, 23457]⟩]),
  (1123, [⟨1, 1, [7, 21, 109, 1123, 10107, 23583]⟩]),
  (1129, [⟨1, 1, [7, 21, 109, 763, 10161, 23709]⟩]),
  (1151, [⟨1, 1, [5, 9, 63, 109, 545, 1151, 8057, 24171]⟩]),
  (1153, [⟨1, 1, [5, 63, 545, 1153, 8071, 24213]⟩]),
  (1163, [⟨1, 1, [1, 7, 15, 1163, 8141, 24423]⟩]),
  (1171, [⟨1, 1, [5, 63, 109, 545, 8197, 24591]⟩]),
  (1181, [⟨1, 1, [3, 9, 21, 109, 8267, 24801]⟩]),
  (1187, [⟨1, 1, [981, 1187, 5935, 24927]⟩]),
  (1193, [⟨1, 1, [1, 9, 21, 63, 545, 1193, 5965, 25053]⟩]),
  (1201, [⟨1, 1, [1, 3, 7, 63, 109, 1201, 6005, 25221]⟩]),
  (1213, [⟨1, 1, [1, 3, 9, 45, 109, 545, 6065, 25473]⟩]),
  (1217, [⟨1, 1, [7, 45, 109, 327, 6085, 25557]⟩]),
  (1223, [⟨1, 1, [1, 7, 35, 109, 6115, 25683]⟩]),
  (1229, [⟨1, 1, [1, 63, 981, 1229, 3687, 25809]⟩]),
  (1231, [⟨1, 1, [63, 109, 763, 1231, 3693, 25851]⟩]),
  (1237, [⟨1, 1, [15, 45, 545, 1237, 3711, 25977]⟩]),
  (1249, [⟨1, 1, [1, 5, 35, 63, 109, 981, 3747, 26229]⟩]),
  (1259, [⟨1, 1, [109, 545, 3777, 26439]⟩]),
  (1277, [⟨1, 1, [3, 21, 63, 109, 763, 1277, 8939, 19155]⟩]),
  (1279, [⟨1, 1, [1, 5, 21, 63, 763, 1279, 8953, 19185]⟩]),
  (1283, [⟨1, 1, [3, 9, 21, 63, 545, 1283, 8981, 19245]⟩]),
  (1289, [⟨1, 1, [1, 45, 63, 105, 109, 1289, 9023, 19335]⟩]),
  (1291, [⟨1, 1, [3, 105, 109, 1291, 9037, 19365]⟩]),
  (1297, [⟨1, 1, [1, 105, 109, 981, 1297, 27237]⟩]),
  (1301, [⟨1, 1, [7, 981, 1301, 27321]⟩]),
  (1303, [⟨1, 1, [3, 9, 109, 763, 1303, 27363]⟩]),
  (1307, [⟨1, 1, [1, 21, 109, 545, 1307, 27447]⟩]),
  (1319, [⟨1, 1, [7, 45, 1319, 27699]⟩]),
  (1321, [⟨1, 1, [7, 63, 109, 327, 763, 27741]⟩]),
  (1327, [⟨1, 1, [7, 21, 63, 109, 763, 27867]⟩]),
  (1361, [⟨1, 1, [45, 545, 6805, 20415]⟩]),
  (1367, [⟨1, 1, [1, 3, 9, 63, 105, 109, 6835, 20505]⟩]),
  (1373, [⟨1, 1, [1, 9, 45, 327, 981, 1373, 4119, 20595]⟩]),
  (1381, [⟨1, 1, [1, 35, 63, 109, 763, 1381, 4143, 20715]⟩]),
  (1399, [⟨1, 1, [5, 21, 63, 1399, 4197, 20985]⟩]),
  (1409, [⟨1, 1, [1, 5, 21, 981, 4227, 21135]⟩]),
  (1423, [⟨1, 1, [9, 327, 4269, 21345]⟩]),
  (1427, [⟨1, 1, [35, 109, 4281, 21405]⟩]),
  (1429, [⟨1, 1, [3, 45, 4287, 21435]⟩]),
  (1433, [⟨1, 1, [1, 5, 21, 63, 109, 327, 763, 1433, 10031, 12897]⟩]),
  (1439, [⟨1, 1, [5, 21, 981, 1439, 10073, 12951]⟩]),
  (1447, [⟨1, 1, [1, 7, 15, 63, 545, 1447, 10129, 13023]⟩]),
  (1451, [⟨1, 1, [7, 109, 327, 1451, 10157, 13059]⟩]),
  (1453, [⟨1, 1, [1, 21, 327, 1453, 10171, 13077]⟩]),
  (1459, [⟨1, 1, [1, 3, 63, 1459, 10213, 13131]⟩]),
  (1471, [⟨1, 1, [1, 3, 35, 63, 109, 763, 1471, 22065]⟩]),
  (1481, [⟨1, 1, [15, 63, 109, 327, 1481, 22215]⟩]),
  (1483, [⟨1, 1, [1, 3, 7, 21, 63, 327, 1483, 22245]⟩]),
  (1487, [⟨1, 1, [3, 21, 105, 109, 1487, 22305]⟩]),
  (1489, [⟨1, 1, [1, 15, 21, 109, 1489, 22335]⟩]),
  (1493, [⟨1, 1, [3, 35, 109, 327, 981, 22395]⟩]),
  (1499, [⟨1, 1, [1, 3, 7, 21, 63, 109, 981, 22485]⟩]),
  (1511, [⟨1, 1, [1, 15, 21, 63, 545, 22665]⟩]),
  (1523, [⟨1, 1, [105, 22845]⟩]),
  (1531, [⟨1, 1, [5, 9, 63, 109, 327, 763, 7655, 13779]⟩]),
  (1543, [⟨1, 1, [1, 9, 21, 63, 109, 545, 7715, 13887]⟩]),
  (1549, [⟨1, 1, [3, 45, 109, 327, 7745, 13941]⟩]),
  (1553, [⟨1, 1, [1, 9, 21, 63, 105, 109, 7765, 13977]⟩]),
  (1559, [⟨1, 1, [9, 35, 7795, 14031]⟩]),
  (1567, [⟨1, 1, [15, 45, 109, 327, 763, 1567, 4701, 14103]⟩]),
  (1571, [⟨1, 1, [1, 105, 981, 1571, 4713, 14139]⟩]),
  (1579, [⟨1, 1, [5, 21, 63, 109, 545, 1579, 4737, 14211]⟩]),
  (1583, [⟨1, 1, [5, 21, 545, 1583, 4749, 14247]⟩]),
  (1597, [⟨1, 1, [5, 35, 545, 981, 4791, 14373]⟩]),
  (1601, [⟨1, 1, [1, 5, 21, 63, 327, 981, 4803, 14409]⟩]),
  (1607, [⟨1, 1, [1, 3, 7, 45, 109, 981, 4821, 14463]⟩]),
  (1609, [⟨1, 1, [3, 15, 63, 981, 4827, 14481]⟩]),
  (1613, [⟨1, 1, [1, 21, 109, 763, 4839, 14517]⟩]),
  (1619, [⟨1, 1, [1, 3, 9, 21, 63, 545, 4857, 14571]⟩]),
  (1621, [⟨1, 1, [1, 3, 9, 545, 4863, 14589]⟩]),
  (1627, [⟨1, 1, [1, 7, 21, 63, 105, 109, 4881, 14643]⟩]),
  (1637, [⟨1, 1, [1, 105, 109, 327, 981, 1637, 4911, 11459]⟩]),
  (1657, [⟨1, 1, [1, 3, 45, 109, 545, 1657, 4971, 11599]⟩]),
  (1663, [⟨1, 1, [21, 109, 327, 1663, 4989, 11641]⟩]),
  (1667, [⟨1, 1, [1, 15, 63, 105, 109, 1667, 5001, 11669]⟩]),
  (1669, [⟨1, 1, [1, 3, 35, 63, 109, 1669, 5007, 11683]⟩]),
  (1693, [⟨1, 1, [3, 45, 109, 763, 1693, 15237]⟩]),
  (1697, [⟨1, 1, [1, 105, 109, 545, 1697, 15273]⟩]),
  (1699, [⟨1, 1, [5, 21, 109, 545, 1699, 15291]⟩]),
  (1709, [⟨1, 1, [3, 63, 105, 109, 1709, 15381]⟩]),
  (1721, [⟨1, 1, [1, 5, 35, 63, 109, 327, 981, 15489]⟩]),
  (1723, [⟨1, 1, [5, 21, 109, 327, 981, 15507]⟩]),
  (1733, [⟨1, 1, [9, 63, 981, 15597]⟩]),
  (1741, [⟨1, 1, [3, 21, 63, 109, 545, 15669]⟩]),
  (1747, [⟨1, 1, [1, 7, 63, 109, 327, 15723]⟩]),
  (1753, [⟨1, 1, [5, 9, 45, 105, 109, 15777]⟩]),
  (1759, [⟨1, 1, [1, 3, 35, 15831]⟩]),
  (1777, [⟨1, 1, [3, 21, 109, 981, 1777, 12439]⟩]),
  (1783, [⟨1, 1, [5, 9, 109, 763, 1783, 12481]⟩]),
  (1787, [⟨1, 1, [1, 7, 9, 63, 109, 545, 1787, 12509]⟩]),
  (1789, [⟨1, 1, [1, 3, 109, 545, 1789, 12523]⟩]),
  (1801, [⟨1, 1, [9, 21, 63, 109, 1801, 12607]⟩]),
  (1811, [⟨1, 1, [9, 35, 63, 545, 981, 12677]⟩]),
  (1823, [⟨1, 1, [1, 35, 63, 109, 981, 12761]⟩]),
  (1831, [⟨1, 1, [21, 109, 763, 12817]⟩]),
  (1847, [⟨1, 1, [3, 21, 63, 105, 109, 12929]⟩]),
  (1861, [⟨1, 1, [9, 1635, 1861, 9305]⟩]),
  (1867, [⟨1, 1, [1, 3, 7, 109, 327, 981, 1867, 9335]⟩]),
  (1871, [⟨1, 1, [1, 21, 63, 109, 327, 763, 1871, 9355]⟩]),
  (1873, [⟨1, 1, [1, 3, 9, 109, 327, 763, 1873, 9365]⟩]),
  (1877, [⟨1, 1, [3, 21, 63, 981, 1877, 9385]⟩]),
  (1879, [⟨1, 1, [15, 981, 1879, 9395]⟩]),
  (1889, [⟨1, 1, [7, 21, 63, 545, 1889, 9445]⟩]),
  (1901, [⟨1, 1, [1, 3, 7, 21, 63, 109, 1901, 9505]⟩]),
  (1907, [⟨1, 1, [7, 35, 109, 763, 981, 9535]⟩]),
  (1913, [⟨1, 1, [5, 45, 1635, 9565]⟩]),
  (1931, [⟨1, 1, [1, 3, 7, 63, 981, 9655]⟩]),
  (1933, [⟨1, 1, [1, 3, 981, 9665]⟩]),
  (1949, [⟨1, 1, [35, 63, 327, 9745]⟩]),
  (1951, [⟨1, 1, [7, 21, 327, 9755]⟩]),
  (1973, [⟨1, 1, [1, 3, 7, 21, 545, 981, 1973, 5919]⟩]),
  (1979, [⟨1, 1, [1, 45, 327, 981, 1979, 5937]⟩]),
  (1987, [⟨1, 1, [3, 35, 63, 981, 1987, 5961]⟩]),
  (1993, [⟨1, 1, [1, 5, 109, 763, 1993, 5979]⟩]),
  (1997, [⟨1, 1, [1, 3, 21, 63, 109, 545, 1997, 5991]⟩]),
  (1999, [⟨1, 1, [5, 15, 109, 545, 1999, 5997]⟩]),
  (2003, [⟨1, 1, [1, 3, 35, 63, 109, 327, 2003, 6009]⟩]),
  (2011, [⟨1, 1, [7, 45, 105, 109, 2011, 6033]⟩]),
  (2017, [⟨1, 1, [1, 7, 9, 45, 2017, 6051]⟩]),
  (2027, [⟨1, 1, [5, 109, 1635, 6081]⟩]),
  (2029, [⟨1, 1, [3, 45, 1635, 6087]⟩]),
  (2039, [⟨1, 1, [45, 327, 981, 6117]⟩]),
  (2053, [⟨1, 1, [1, 3, 15, 109, 763, 6159]⟩]),
  (2063, [⟨1, 1, [1, 15, 545, 6189]⟩]),
  (2069, [⟨1, 1, [1, 35, 327, 6207]⟩]),
  (2081, [⟨1, 1, [3, 9, 21, 63, 109, 1635, 2081, 2289]⟩]),
  (2083, [⟨1, 1, [1, 3, 9, 21, 109, 1635, 2083, 2289]⟩]),
  (2087, [⟨1, 1, [1, 3, 15, 109, 2087, 3815]⟩]),
  (2089, [⟨1, 1, [3, 63, 2089, 3815]⟩]),
  (2099, [⟨1, 1, [5, 15, 63, 109, 327, 763, 2099, 2289]⟩]),
  (2111, [⟨1, 1, [3, 35, 109, 763, 2111, 2289]⟩]),
  (2113, [⟨1, 1, [1, 21, 63, 763, 2113, 2289]⟩]),
  (2129, [⟨1, 1, [1, 3, 21, 327, 2129, 2289]⟩]),
  (2131, [⟨1, 1, [9, 63, 109, 763, 1635, 2131]⟩]),
  (2137, [⟨1, 1, [1, 5, 35, 63, 2137, 2289]⟩]),
  (2141, [⟨1, 1, [5, 21, 63, 545, 1635, 2141]⟩]),
  (2143, [⟨1, 1, [1, 5, 21, 545, 1635, 2143]⟩]),
  (2153, [⟨1, 1, [9, 35, 109, 763, 981, 2153]⟩]),
  (2161, [⟨1, 1, [5, 9, 1635, 2161]⟩]),
  (2179, [⟨1, 1, [1, 109, 981, 2179]⟩]),
  (2203, [⟨1, 1, [5, 15, 327, 2203]⟩]),
  (2207, [⟨1, 1, [9, 105, 109, 2207]⟩]),
  (2213, [⟨1, 1, [1, 15, 21, 2213]⟩]),
  (2221, [⟨1, 1, [3, 45, 327, 1635]⟩]),
  (2237, [⟨1, 1, [1, 3, 545, 981]⟩]),
  (2239, [⟨1, 1, [1, 7, 45, 109, 327, 981]⟩]),
  (2243, [⟨1, 1, [7, 35, 327, 981]⟩]),
  (2251, [⟨1, 1, [5, 15, 109, 981]⟩]),
  (2267, [⟨1, 1, [1, 21, 63, 545]⟩]),
  (2269, [⟨1, 1, [1, 3, 21, 545]⟩]),
  (2273, [⟨1, 1, [5, 9, 109, 327]⟩]),
  (2281, [⟨1, 1, [3, 35, 63, 109]⟩]),
  (2287, [⟨1, 1, [9, 21]⟩]),
  (2293, [⟨2, 1, [7, 45, 109, 1635, 2293, 6879, 11881, 35643, 106929, 1249685]⟩]),
  (2297, [⟨2, 1, [1, 3, 21, 109, 763, 2297, 6891, 35643, 106929, 1251865]⟩]),
  (2309, [⟨2, 1, [1, 9, 63, 109, 327, 6927, 106929, 1258405]⟩]),
  (2311, [⟨2, 1, [1, 9, 63, 981, 106929, 1259495]⟩]),
  (2333, [⟨2, 1, [1, 3, 63, 109, 327, 1635, 35643, 1271485]⟩]),
  (2339, [⟨2, 1, [1, 9, 45, 545, 2339, 3815, 11881, 1274755]⟩]),
  (2341, [⟨2, 1, [45, 327, 11881, 1275845]⟩]),
  (2347, [⟨2, 1, [1, 5, 63, 109, 763, 981, 2347, 7041, 59405, 178215, 255823, 767469]⟩]),
  (2351, [⟨2, 1, [7, 35, 109, 327, 981, 2351, 7053, 11881, 35643, 178215, 256259, 768777]⟩]),
  (2357, [⟨2, 1, [7, 35, 109, 763, 981, 2357, 35643, 178215, 256913, 770739]⟩]),
  (2371, [⟨2, 1, [35, 63, 109, 327, 981, 7113, 59405, 106929, 258439, 775317]⟩]),
  (2377, [⟨2, 1, [1, 9, 45, 327, 1635, 11881, 35643, 106929, 259093, 777279]⟩]),
  (2381, [⟨2, 1, [9, 35, 545, 981, 35643, 106929, 259529, 778587]⟩]),
  (2383, [⟨2, 1, [1, 7, 21, 109, 7149, 11881, 35643, 83167, 259747, 779241]⟩]),
  (2389, [⟨2, 1, [1, 21, 109, 545, 11881, 106929, 260401, 781203]⟩]),
  (2393, [⟨2, 1, [15, 105, 109, 106929, 260837, 782511]⟩]),
  (2399, [⟨2, 1, [3, 45, 763, 2289, 2399, 83167, 261491, 784473]⟩]),
  (2411, [⟨2, 1, [3, 109, 1635, 2411, 11881, 35643, 262799, 788397]⟩]),
  (2417, [⟨2, 1, [1, 3, 7, 327, 1635, 2417, 11881, 16919, 263453, 790359]⟩]),
  (2423, [⟨2, 1, [1, 3, 63, 327, 2423, 11881, 264107, 792321]⟩]),
  (2437, [⟨2, 1, [1, 15, 45, 1635, 2437, 7311, 11881, 35643, 178215, 796899]⟩]),
  (2441, [⟨2, 1, [1, 3, 9, 21, 1635, 2441, 7323, 35643, 178215, 798207]⟩]),
  (2447, [⟨2, 1, [1, 7, 15, 63, 109, 545, 2289, 2447, 11881, 83167, 106929, 800169]⟩]),
  (2459, [⟨2, 1, [1, 5, 35, 109, 545, 2289, 2459, 59405, 106929, 804093]⟩]),
  (2467, [⟨2, 1, [1, 3, 7, 109, 545, 2289, 2467, 35643, 106929, 806709]⟩]),
  (2473, [⟨2, 1, [1, 35, 109, 327, 981, 2473, 7419, 11881, 106929, 808671]⟩]),
  (2477, [⟨2, 1, [9, 109, 327, 981, 2477, 7431, 106929, 809979]⟩]),
  (2503, [⟨2, 1, [1, 9, 21, 63, 109, 327, 2289, 2503, 35643, 818481]⟩]),
  (2521, [⟨2, 1, [1, 3, 7, 21, 63, 2289, 274789, 534645]⟩]),
  (2531, [⟨2, 1, [5, 21, 327, 2531, 7593, 83167, 275879, 415835]⟩]),
  (2539, [⟨2, 1, [1, 5, 35, 63, 105, 109, 11881, 59405, 276751, 415835]⟩]),
  (2543, [⟨2, 1, [5, 21, 63, 109, 981, 59405, 277187, 415835]⟩]),
  (2549, [⟨2, 1, [1, 763, 7647, 35643, 277841, 415835]⟩]),
  (2551, [⟨2, 1, [1, 7, 15, 327, 2551, 35643, 278059, 415835]⟩]),
  (2557, [⟨2, 1, [1, 63, 109, 2289, 7671, 11881, 278713, 415835]⟩]),
  (2579, [⟨2, 1, [3, 35, 63, 109, 981, 7737, 11881, 106929, 249501, 281111]⟩]),
  (2591, [⟨2, 1, [3, 9, 45, 109, 981, 2591, 7773, 83167, 249501, 282419]⟩]),
  (2593, [⟨2, 1, [1, 7, 21, 109, 981, 2289, 2593, 83167, 249501, 282637]⟩]),
  (2609, [⟨2, 1, [1, 7, 21, 63, 545, 981, 7827, 35643, 249501, 284381]⟩]),
  (2617, [⟨2, 1, [45, 109, 545, 2617, 7851, 11881, 249501, 285253]⟩]),
  (2621, [⟨2, 1, [3, 35, 109, 11881, 249501, 285689]⟩]),
  (2633, [⟨2, 1, [1, 3, 9, 21, 63, 2633, 11881, 35643, 178215, 286997]⟩]),
  (2647, [⟨2, 1, [1, 5, 109, 981, 2647, 7941, 178215, 288523]⟩]),
  (2657, [⟨2, 1, [7, 327, 2657, 4905, 11881, 35643, 106929, 289613]⟩]),
  (2659, [⟨2, 1, [1, 3, 9, 21, 63, 2289, 11881, 35643, 106929, 289831]⟩]),
  (2663, [⟨2, 1, [1, 3, 35, 545, 2663, 35643, 106929, 290267]⟩]),
  (2671, [⟨2, 1, [9, 2289, 2671, 11881, 106929, 291139]⟩]),
  (2677, [⟨2, 1, [1, 7, 35, 63, 105, 109, 106929, 291793]⟩]),
  (2683, [⟨2, 1, [1, 9, 63, 981, 2683, 3815, 83167, 292447]⟩]),
  (2687, [⟨2, 1, [1, 3, 21, 327, 8061, 11881, 59405, 292883]⟩]),
  (2689, [⟨2, 1, [105, 109, 2689, 11881, 59405, 293101]⟩]),
  (2693, [⟨2, 1, [1, 5, 21, 63, 981, 2693, 59405, 293537]⟩]),
  (2699, [⟨2, 1, [7, 21, 63, 109, 2699, 8097, 35643, 294191]⟩]),
  (2707, [⟨2, 1, [1, 15, 21, 109, 763, 981, 2707, 8121, 11881, 295063]⟩]),
  (2711, [⟨2, 1, [63, 1635, 11881, 295499]⟩]),
  (2713, [⟨2, 1, [15, 109, 327, 2713, 4905, 295717]⟩]),
  (2719, [⟨2, 1, [3, 9, 35, 2719, 35643, 249501]⟩]),
  (2729, [⟨2, 1, [5, 63, 11881, 249501]⟩]),
  (2731, [⟨2, 1, [1, 5, 105, 2731, 3815, 249501]⟩]),
  (2741, [⟨2, 1, [1, 3, 15, 109, 327, 763, 2741, 11881, 35643, 178215]⟩]),
  (2749, [⟨2, 1, [35, 63, 109, 327, 981, 2289, 2749, 11881, 83167, 106929]⟩]),
  (2753, [⟨2, 1, [5, 15, 63, 109, 2753, 4905, 11881, 178215]⟩]),
  (2767, [⟨2, 1, [1, 21, 63, 327, 981, 2289, 2767, 11881, 35643, 106929]⟩]),
  (2777, [⟨2, 1, [1, 3, 35, 63, 109, 763, 2777, 11881, 35643, 83167]⟩]),
  (2789, [⟨2, 1, [3, 9, 45, 981, 2789, 3815, 11881, 83167]⟩]),
  (2791, [⟨2, 1, [1, 15, 45, 2289, 11881, 83167]⟩]),
  (2797, [⟨2, 1, [3, 35, 63, 109, 1635, 8391, 11881, 59405]⟩]),
  (2801, [⟨2, 1, [7, 45, 63, 105, 109, 2801, 8403, 59405]⟩]),
  (2803, [⟨2, 1, [5, 9, 45, 109, 981, 2289, 2803, 59405]⟩]),
  (2819, [⟨2, 1, [9, 35, 109, 2819, 8457, 11881]⟩]),
  (2833, [⟨3, 1, [3, 545, 981, 8499, 11881, 249501]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified109 : verifyBatch 109 qPrimes rows109 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows113 : List Row := [
  (11, [⟨1, 1, [1, 3, 11, 15, 113, 339, 565, 791, 1017, 1695, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (13, [⟨1, 1, [1, 13, 21, 339, 565, 791, 1017, 1695, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (17, [⟨1, 1, [7, 17, 21, 113, 565, 791, 1017, 1695, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (19, [⟨1, 1, [1, 9, 19, 21, 565, 791, 1017, 1695, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (23, [⟨1, 1, [1, 15, 21, 23, 339, 791, 1017, 1695, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (29, [⟨1, 1, [1, 29, 45, 791, 1017, 1695, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (31, [⟨1, 1, [1, 3, 31, 45, 113, 565, 1017, 1695, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (37, [⟨1, 1, [1, 3, 9, 37, 45, 339, 1017, 1695, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (41, [⟨1, 1, [1, 41, 63, 113, 1017, 1695, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (43, [⟨1, 1, [1, 3, 43, 63, 1017, 1695, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (47, [⟨1, 1, [7, 113, 791, 1695, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (53, [⟨1, 1, [1, 21, 565, 1695, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (59, [⟨1, 1, [1, 15, 21, 113, 791, 1017, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (61, [⟨1, 1, [7, 35, 113, 1695, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (67, [⟨1, 1, [3, 9, 45, 113, 339, 1017, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (71, [⟨1, 1, [1, 3, 63, 113, 339, 791, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (73, [⟨1, 1, [9, 63, 113, 1017, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (79, [⟨1, 1, [1, 7, 79, 791, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (83, [⟨1, 1, [5, 9, 83, 565, 2373, 3955, 5085, 7119, 11865, 35595]⟩]),
  (89, [⟨1, 1, [1, 7, 15, 89, 113, 791, 1695, 3955, 5085, 7119, 11865, 35595]⟩]),
  (97, [⟨1, 1, [1, 3, 15, 565, 1695, 3955, 5085, 7119, 11865, 35595]⟩]),
  (101, [⟨1, 1, [1, 7, 21, 339, 1695, 3955, 5085, 7119, 11865, 35595]⟩]),
  (103, [⟨1, 1, [1, 3, 9, 21, 113, 791, 1017, 3955, 5085, 7119, 11865, 35595]⟩]),
  (107, [⟨1, 1, [9, 35, 1695, 3955, 5085, 7119, 11865, 35595]⟩]),
  (109, [⟨1, 1, [1, 3, 45, 565, 1017, 3955, 5085, 7119, 11865, 35595]⟩]),
  (127, [⟨1, 1, [1, 15, 127, 889, 1905, 8001, 13335, 40005]⟩]),
  (131, [⟨1, 1, [3, 131, 655, 8253, 13755, 41265]⟩]),
  (137, [⟨1, 1, [3, 9, 21, 6165, 14385, 43155]⟩]),
  (139, [⟨1, 1, [9, 35, 63, 139, 2085, 2919, 14595, 43785]⟩]),
  (149, [⟨1, 1, [63, 447, 15645, 46935]⟩]),
  (151, [⟨1, 1, [15, 151, 453, 5285, 9513, 47565]⟩]),
  (157, [⟨1, 1, [15, 3297, 9891, 49455]⟩]),
  (163, [⟨1, 1, [5, 63, 163, 489, 10269, 51345]⟩]),
  (167, [⟨1, 1, [3, 45, 113, 167, 501, 1169, 7515, 52605]⟩]),
  (173, [⟨1, 1, [3, 9, 21, 1211, 6055, 54495]⟩]),
  (179, [⟨1, 1, [1, 9, 63, 1253, 3759, 56385]⟩]),
  (181, [⟨1, 1, [3, 543, 3801, 57015]⟩]),
  (191, [⟨1, 1, [21, 63, 573, 60165]⟩]),
  (193, [⟨1, 1, [15, 45, 193, 579, 965, 1017, 1351, 1737, 2895, 4053, 6755, 8685, 12159, 20265]⟩]),
  (197, [⟨1, 1, [5, 35, 63, 113, 197, 985, 1379, 1773, 2955, 4137, 6895, 8865, 12411, 20685]⟩]),
  (199, [⟨1, 1, [9, 21, 63, 597, 1393, 1791, 2985, 4179, 6965, 8955, 12537, 20895]⟩]),
  (211, [⟨1, 1, [1, 7, 21, 1055, 1899, 4431, 7385, 9495, 13293, 22155]⟩]),
  (223, [⟨1, 1, [1, 3, 105, 113, 223, 3345, 7805, 10035, 14049, 23415]⟩]),
  (227, [⟨1, 1, [1, 21, 63, 227, 681, 1589, 7945, 10215, 14301, 23835]⟩]),
  (229, [⟨1, 1, [3, 9, 21, 113, 229, 1603, 8015, 10305, 14427, 24045]⟩]),
  (233, [⟨1, 1, [1, 7, 63, 699, 8155, 10485, 14679, 24465]⟩]),
  (239, [⟨1, 1, [5, 35, 113, 2151, 5019, 10755, 15057, 25095]⟩]),
  (241, [⟨1, 1, [1, 5, 35, 1687, 5061, 10845, 15183, 25305]⟩]),
  (251, [⟨1, 1, [5, 35, 63, 251, 3765, 11295, 15813, 26355]⟩]),
  (257, [⟨1, 1, [7, 21, 63, 113, 2313, 11565, 16191, 26985]⟩]),
  (263, [⟨1, 1, [1, 3, 9, 113, 789, 11835, 16569, 27615]⟩]),
  (269, [⟨1, 1, [7, 113, 1883, 9415, 16947, 28245]⟩]),
  (271, [⟨1, 1, [21, 113, 1355, 9485, 17073, 28455]⟩]),
  (277, [⟨1, 1, [1, 5, 105, 113, 277, 831, 2493, 5817, 17451, 29085]⟩]),
  (281, [⟨1, 1, [1, 7, 35, 281, 2529, 5901, 17703, 29505]⟩]),
  (283, [⟨1, 1, [5, 35, 63, 283, 1981, 5943, 17829, 29715]⟩]),
  (293, [⟨1, 1, [3, 9, 105, 113, 1465, 4395, 18459, 30765]⟩]),
  (307, [⟨1, 1, [1, 105, 113, 2763, 19341, 32235]⟩]),
  (311, [⟨1, 1, [1, 9, 105, 113, 311, 1555, 19593, 32655]⟩]),
  (313, [⟨1, 1, [1, 21, 63, 1565, 19719, 32865]⟩]),
  (317, [⟨1, 1, [15, 113, 1585, 4755, 14265, 33285]⟩]),
  (331, [⟨1, 1, [21, 63, 105, 113, 331, 2979, 14895, 34755]⟩]),
  (337, [⟨1, 1, [1, 7, 21, 2359, 15165, 35385]⟩]),
  (347, [⟨1, 1, [1, 347, 15615, 36435]⟩]),
  (349, [⟨1, 1, [1, 7, 63, 105, 113, 3141, 12215, 36645]⟩]),
  (353, [⟨1, 1, [7, 63, 113, 2471, 12355, 37065]⟩]),
  (359, [⟨1, 1, [9, 45, 359, 1077, 12565, 37695]⟩]),
  (367, [⟨1, 1, [3, 21, 63, 105, 113, 367, 1101, 3303, 7707, 38535]⟩]),
  (373, [⟨1, 1, [3, 45, 105, 113, 373, 3357, 7833, 39165]⟩]),
  (379, [⟨1, 1, [45, 105, 113, 2653, 7959, 39795]⟩]),
  (383, [⟨1, 1, [63, 105, 113, 1915, 8043, 40215]⟩]),
  (389, [⟨1, 1, [3, 9, 45, 63, 105, 113, 389, 2723, 5835, 40845]⟩]),
  (397, [⟨1, 1, [1, 9, 63, 1985, 5955, 41685]⟩]),
  (401, [⟨1, 1, [1, 45, 113, 1203, 6015, 42105]⟩]),
  (409, [⟨1, 1, [5, 35, 339, 2045, 3681, 42945]⟩]),
  (419, [⟨1, 1, [9, 35, 63, 105, 113, 419, 3771, 43995]⟩]),
  (421, [⟨1, 1, [1, 5, 63, 339, 3789, 44205]⟩]),
  (431, [⟨1, 1, [21, 431, 2155, 45255]⟩]),
  (433, [⟨1, 1, [1, 3, 7, 113, 2165, 45465]⟩]),
  (439, [⟨1, 1, [3, 15, 1317, 46095]⟩]),
  (443, [⟨1, 1, [3, 35, 105, 113, 443, 46515]⟩]),
  (449, [⟨1, 1, [3, 15, 63, 113, 449, 2245, 15715, 28287]⟩]),
  (457, [⟨1, 1, [5, 15, 63, 105, 113, 1371, 15995, 28791]⟩]),
  (461, [⟨1, 1, [1, 7, 21, 113, 461, 6915, 9681, 29043]⟩]),
  (463, [⟨1, 1, [1, 15, 63, 105, 113, 463, 16205, 29169]⟩]),
  (467, [⟨1, 1, [1, 3, 35, 113, 16345, 29421]⟩]),
  (479, [⟨1, 1, [5, 21, 105, 113, 479, 4311, 10059, 30177]⟩]),
  (487, [⟨1, 1, [1, 3, 9, 21, 487, 3409, 10227, 30681]⟩]),
  (491, [⟨1, 1, [9, 21, 63, 339, 491, 2455, 10311, 30933]⟩]),
  (499, [⟨1, 1, [15, 45, 105, 113, 499, 1497, 10479, 31437]⟩]),
  (503, [⟨1, 1, [1, 15, 21, 63, 113, 1509, 10563, 31689]⟩]),
  (509, [⟨1, 1, [1, 45, 339, 509, 10689, 32067]⟩]),
  (521, [⟨1, 1, [1, 7, 9, 45, 105, 113, 521, 1563, 7815, 32823]⟩]),
  (523, [⟨1, 1, [1, 7, 523, 1569, 7845, 32949]⟩]),
  (541, [⟨1, 1, [3, 9, 35, 105, 113, 2705, 4869, 34083]⟩]),
  (547, [⟨1, 1, [5, 21, 547, 1641, 4923, 34461]⟩]),
  (557, [⟨1, 1, [1, 3, 9, 45, 339, 557, 5013, 35091]⟩]),
  (563, [⟨1, 1, [1, 21, 63, 113, 5067, 35469]⟩]),
  (569, [⟨1, 1, [1, 3, 7, 569, 3983, 35847]⟩]),
  (571, [⟨1, 1, [1, 5, 45, 63, 105, 113, 3997, 35973]⟩]),
  (577, [⟨1, 1, [7, 45, 113, 577, 2885, 36351]⟩]),
  (587, [⟨1, 1, [1, 3, 105, 587, 1761, 36981]⟩]),
  (593, [⟨1, 1, [1, 3, 565, 2965, 8895, 26685]⟩]),
  (599, [⟨1, 1, [1, 9, 105, 339, 599, 37737]⟩]),
  (601, [⟨1, 1, [105, 113, 601, 37863]⟩]),
  (607, [⟨1, 1, [1, 3, 113, 38241]⟩]),
  (613, [⟨1, 1, [7, 21, 613, 4291, 5517, 27585]⟩]),
  (617, [⟨1, 1, [5, 63, 113, 617, 9255, 27765]⟩]),
  (619, [⟨1, 1, [5, 565, 9285, 27855]⟩]),
  (631, [⟨1, 1, [3, 9, 113, 339, 631, 1893, 5679, 28395]⟩]),
  (641, [⟨1, 1, [1, 15, 45, 565, 641, 1923, 4487, 28845]⟩]),
  (643, [⟨1, 1, [1, 3, 63, 339, 643, 1929, 4501, 28935]⟩]),
  (647, [⟨1, 1, [3, 45, 565, 647, 5823, 29115]⟩]),
  (653, [⟨1, 1, [3, 9, 35, 565, 5877, 29385]⟩]),
  (659, [⟨1, 1, [1, 3, 9, 45, 565, 659, 4613, 29655]⟩]),
  (661, [⟨1, 1, [7, 63, 339, 661, 4627, 29745]⟩]),
  (673, [⟨1, 1, [1, 3, 15, 113, 339, 673, 3365, 30285]⟩]),
  (677, [⟨1, 1, [1, 5, 45, 677, 3385, 30465]⟩]),
  (683, [⟨1, 1, [1, 5, 35, 63, 3415, 30735]⟩]),
  (691, [⟨1, 1, [5, 21, 63, 565, 2073, 31095]⟩]),
  (701, [⟨1, 1, [9, 45, 63, 105, 113, 2103, 6309, 24535]⟩]),
  (709, [⟨1, 1, [3, 15, 105, 113, 709, 31905]⟩]),
  (719, [⟨1, 1, [1, 3, 105, 565, 6471, 25165]⟩]),
  (727, [⟨1, 1, [7, 45, 565, 727, 5089, 25445]⟩]),
  (733, [⟨1, 1, [35, 733, 5131, 25655]⟩]),
  (739, [⟨1, 1, [1, 15, 63, 113, 5173, 25865]⟩]),
  (743, [⟨1, 1, [1, 35, 63, 113, 339, 743, 3715, 26005]⟩]),
  (751, [⟨1, 1, [1, 5, 21, 63, 113, 339, 3755, 26285]⟩]),
  (757, [⟨1, 1, [3, 9, 45, 113, 565, 757, 2271, 26495]⟩]),
  (761, [⟨1, 1, [3, 21, 339, 761, 2283, 26635]⟩]),
  (769, [⟨1, 1, [1, 3, 45, 339, 2307, 26915]⟩]),
  (773, [⟨1, 1, [5, 15, 2319, 27055]⟩]),
  (787, [⟨1, 1, [1, 3, 21, 63, 105, 113, 787, 27545]⟩]),
  (797, [⟨1, 1, [1, 5, 21, 63, 113, 27895]⟩]),
  (809, [⟨1, 1, [3, 9, 63, 113, 565, 2427, 7281, 16989]⟩]),
  (811, [⟨1, 1, [5, 9, 565, 2433, 7299, 17031]⟩]),
  (821, [⟨1, 1, [15, 63, 113, 339, 821, 2463, 5747, 17241]⟩]),
  (823, [⟨1, 1, [1, 3, 15, 339, 823, 2469, 5761, 17283]⟩]),
  (827, [⟨1, 1, [5, 9, 827, 2481, 5789, 17367]⟩]),
  (829, [⟨1, 1, [1, 105, 565, 829, 7461, 17409]⟩]),
  (839, [⟨1, 1, [1, 3, 7, 21, 63, 565, 7551, 17619]⟩]),
  (853, [⟨1, 1, [1, 3, 7, 45, 63, 105, 113, 853, 5971, 17913]⟩]),
  (857, [⟨1, 1, [5, 857, 5999, 17997]⟩]),
  (859, [⟨1, 1, [5, 15, 113, 565, 6013, 18039]⟩]),
  (863, [⟨1, 1, [1, 9, 21, 339, 6041, 18123]⟩]),
  (877, [⟨1, 1, [1, 35, 63, 877, 4385, 18417]⟩]),
  (881, [⟨1, 1, [7, 21, 63, 565, 4405, 18501]⟩]),
  (883, [⟨1, 1, [9, 35, 113, 339, 4415, 18543]⟩]),
  (887, [⟨1, 1, [63, 113, 4435, 18627]⟩]),
  (907, [⟨1, 1, [1, 5, 45, 339, 2721, 19047]⟩]),
  (911, [⟨1, 1, [15, 63, 2733, 19131]⟩]),
  (919, [⟨1, 1, [1, 3, 9, 21, 339, 919, 6433, 13785]⟩]),
  (929, [⟨1, 1, [1, 7, 9, 63, 113, 339, 929, 19509]⟩]),
  (937, [⟨1, 1, [7, 63, 791, 19677]⟩]),
  (941, [⟨1, 1, [1, 3, 105, 113, 339, 19761]⟩]),
  (947, [⟨1, 1, [1, 5, 105, 19887]⟩]),
  (953, [⟨1, 1, [1, 3, 45, 565, 4765, 14295]⟩]),
  (967, [⟨1, 1, [9, 21, 63, 113, 339, 967, 2901, 14505]⟩]),
  (971, [⟨1, 1, [35, 105, 113, 971, 2913, 14565]⟩]),
  (977, [⟨1, 1, [1, 791, 2931, 14655]⟩]),
  (983, [⟨1, 1, [21, 339, 2949, 14745]⟩]),
  (991, [⟨1, 1, [1, 3, 9, 21, 63, 113, 565, 991, 6937, 8919]⟩]),
  (997, [⟨1, 1, [1, 9, 339, 997, 6979, 8973]⟩]),
  (1009, [⟨1, 1, [9, 45, 113, 339, 1009, 15135]⟩]),
  (1013, [⟨1, 1, [1, 7, 105, 113, 1013, 15195]⟩]),
  (1019, [⟨1, 1, [1, 3, 9, 21, 791, 15285]⟩]),
  (1021, [⟨1, 1, [9, 113, 565, 15315]⟩]),
  (1031, [⟨1, 1, [1, 3, 7, 1017, 5155, 9279]⟩]),
  (1033, [⟨1, 1, [3, 35, 63, 791, 5165, 9297]⟩]),
  (1039, [⟨1, 1, [1, 3, 7, 21, 113, 339, 5195, 9351]⟩]),
  (1049, [⟨1, 1, [1, 7, 9, 45, 791, 1049, 3147, 9441]⟩]),
  (1051, [⟨1, 1, [1, 5, 35, 113, 565, 1051, 3153, 9459]⟩]),
  (1061, [⟨1, 1, [1, 3, 45, 1061, 3183, 9549]⟩]),
  (1063, [⟨1, 1, [1, 3, 7, 63, 113, 791, 3189, 9567]⟩]),
  (1069, [⟨1, 1, [1, 7, 9, 565, 3207, 9621]⟩]),
  (1087, [⟨1, 1, [1, 7, 21, 113, 339, 1087, 3261, 7609]⟩]),
  (1091, [⟨1, 1, [3, 105, 113, 1091, 3273, 7637]⟩]),
  (1093, [⟨1, 1, [7, 21, 63, 1093, 3279, 7651]⟩]),
  (1097, [⟨1, 1, [3, 21, 113, 791, 1097, 9873]⟩]),
  (1103, [⟨1, 1, [1, 7, 21, 63, 113, 339, 1103, 9927]⟩]),
  (1109, [⟨1, 1, [3, 9, 35, 113, 1109, 9981]⟩]),
  (1117, [⟨1, 1, [3, 21, 63, 113, 565, 10053]⟩]),
  (1123, [⟨1, 1, [3, 45, 339, 10107]⟩]),
  (1129, [⟨1, 1, [9, 10161]⟩]),
  (1151, [⟨1, 1, [21, 113, 791, 8057]⟩]),
  (1153, [⟨1, 1, [3, 9, 791, 8071]⟩]),
  (1163, [⟨1, 1, [1, 7, 9, 63, 113, 8141]⟩]),
  (1171, [⟨1, 1, [1, 21, 63, 791, 1171, 5855]⟩]),
  (1181, [⟨1, 1, [1, 3, 9, 45, 105, 113, 1181, 5905]⟩]),
  (1187, [⟨1, 1, [1, 7, 15, 63, 1017, 5935]⟩]),
  (1193, [⟨1, 1, [1, 7, 63, 113, 565, 5965]⟩]),
  (1201, [⟨1, 1, [5, 9, 45, 105, 113, 6005]⟩]),
  (1213, [⟨1, 1, [1, 5, 35, 63, 113, 565, 1213, 3639]⟩]),
  (1217, [⟨1, 1, [35, 63, 113, 339, 1217, 3651]⟩]),
  (1223, [⟨1, 1, [5, 21, 63, 113, 1223, 3669]⟩]),
  (1229, [⟨1, 1, [3, 63, 1017, 3687]⟩]),
  (1231, [⟨1, 1, [5, 15, 45, 113, 791, 3693]⟩]),
  (1237, [⟨1, 1, [1, 7, 9, 45, 565, 3711]⟩]),
  (1249, [⟨1, 1, [5, 63, 1249, 2373]⟩]),
  (1259, [⟨1, 1, [5, 15, 63, 113, 1259, 1695]⟩]),
  (1277, [⟨1, 1, [5, 105, 791, 1277]⟩]),
  (1279, [⟨1, 1, [791, 1279]⟩]),
  (1283, [⟨1, 1, [1, 5, 565, 1283]⟩]),
  (1289, [⟨1, 1, [1, 7, 15, 105, 113, 1289]⟩]),
  (1291, [⟨1, 1, [3, 15, 113, 1291]⟩]),
  (1297, [⟨1, 1, [3, 15, 63, 1017]⟩]),
  (1301, [⟨1, 1, [7, 21, 63, 791]⟩]),
  (1303, [⟨1, 1, [3, 9, 21, 63, 113, 565]⟩]),
  (1307, [⟨1, 1, [1, 105, 113, 339]⟩]),
  (1319, [⟨2, 1, [21, 113, 339, 3957, 63845, 745235]⟩]),
  (1321, [⟨2, 1, [5, 15, 113, 1017, 3963, 12769, 38307, 746365]⟩]),
  (1327, [⟨2, 1, [3, 9, 63, 113, 339, 6635, 12769, 749755]⟩]),
  (1361, [⟨2, 1, [3, 45, 63, 105, 113, 6805, 114921, 461379]⟩]),
  (1367, [⟨2, 1, [3, 63, 113, 791, 9569, 12769, 63845, 463413]⟩]),
  (1373, [⟨2, 1, [45, 113, 1017, 12769, 38307, 465447]⟩]),
  (1381, [⟨2, 1, [15, 63, 113, 1381, 4143, 468159]⟩]),
  (1399, [⟨2, 1, [5, 105, 12769, 89383, 114921, 158087]⟩]),
  (1409, [⟨2, 1, [3, 9, 21, 63, 113, 791, 7045, 38307, 114921, 159217]⟩]),
  (1423, [⟨2, 1, [15, 113, 565, 1423, 4269, 12769, 63845, 160799]⟩]),
  (1427, [⟨2, 1, [9, 21, 63, 113, 791, 1427, 7135, 12769, 38307, 161251]⟩]),
  (1429, [⟨2, 1, [1, 3, 9, 113, 1017, 10003, 38307, 161477]⟩]),
  (1433, [⟨2, 1, [1, 3, 63, 339, 1017, 12769, 12897, 161929]⟩]),
  (1439, [⟨2, 1, [5, 9, 113, 339, 1017, 1439, 38307, 114921]⟩]),
  (1447, [⟨2, 1, [45, 10129, 12769, 89383]⟩]),
  (1451, [⟨2, 1, [5, 9, 1017, 89383]⟩]),
  (1453, [⟨2, 1, [35, 339, 1017, 1453, 12769, 63845]⟩]),
  (1459, [⟨2, 1, [21, 63, 113, 791, 7295, 38307]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified113 : verifyBatch 113 qPrimes rows113 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows127 : List Row := [
  (11, [⟨1, 1, [1, 11, 33, 77, 127, 889, 1143, 1905, 2667, 4445, 5715, 8001, 13335, 40005]⟩]),
  (13, [⟨1, 1, [9, 91, 127, 635, 1143, 1905, 2667, 4445, 5715, 8001, 13335, 40005]⟩]),
  (17, [⟨1, 1, [5, 51, 127, 381, 889, 1905, 2667, 4445, 5715, 8001, 13335, 40005]⟩]),
  (19, [⟨1, 1, [15, 19, 1143, 1905, 2667, 4445, 5715, 8001, 13335, 40005]⟩]),
  (23, [⟨1, 1, [1, 3, 21, 23, 69, 127, 381, 1905, 2667, 4445, 5715, 8001, 13335, 40005]⟩]),
  (29, [⟨1, 1, [1, 21, 29, 127, 381, 1143, 2667, 4445, 5715, 8001, 13335, 40005]⟩]),
  (31, [⟨1, 1, [1, 7, 21, 127, 381, 889, 2667, 4445, 5715, 8001, 13335, 40005]⟩]),
  (37, [⟨1, 1, [1, 7, 37, 45, 127, 381, 2667, 4445, 5715, 8001, 13335, 40005]⟩]),
  (41, [⟨1, 1, [5, 41, 2667, 4445, 5715, 8001, 13335, 40005]⟩]),
  (43, [⟨1, 1, [3, 21, 127, 381, 1905, 4445, 5715, 8001, 13335, 40005]⟩]),
  (47, [⟨1, 1, [15, 45, 47, 635, 1143, 4445, 5715, 8001, 13335, 40005]⟩]),
  (53, [⟨1, 1, [1, 5, 35, 127, 889, 4445, 5715, 8001, 13335, 40005]⟩]),
  (59, [⟨1, 1, [1, 7, 35, 59, 127, 4445, 5715, 8001, 13335, 40005]⟩]),
  (61, [⟨1, 1, [1, 3, 15, 61, 127, 381, 1143, 2667, 5715, 8001, 13335, 40005]⟩]),
  (67, [⟨1, 1, [5, 9, 889, 2667, 5715, 8001, 13335, 40005]⟩]),
  (71, [⟨1, 1, [5, 21, 71, 127, 889, 1905, 5715, 8001, 13335, 40005]⟩]),
  (73, [⟨1, 1, [3, 9, 63, 2667, 5715, 8001, 13335, 40005]⟩]),
  (79, [⟨1, 1, [9, 1905, 5715, 8001, 13335, 40005]⟩]),
  (83, [⟨1, 1, [9, 83, 127, 1143, 5715, 8001, 13335, 40005]⟩]),
  (89, [⟨1, 1, [5, 21, 127, 381, 5715, 8001, 13335, 40005]⟩]),
  (97, [⟨1, 1, [5, 15, 45, 635, 4445, 8001, 13335, 40005]⟩]),
  (101, [⟨1, 1, [21, 127, 4445, 8001, 13335, 40005]⟩]),
  (103, [⟨1, 1, [1, 7, 15, 103, 381, 1143, 2667, 8001, 13335, 40005]⟩]),
  (107, [⟨1, 1, [1, 3, 15, 63, 127, 889, 2667, 8001, 13335, 40005]⟩]),
  (109, [⟨1, 1, [15, 45, 127, 635, 2667, 8001, 13335, 40005]⟩]),
  (113, [⟨1, 1, [1, 15, 127, 889, 1905, 8001, 13335, 40005]⟩]),
  (131, [⟨1, 1, [9, 21, 63, 131, 655, 5895, 13755, 41265]⟩]),
  (137, [⟨1, 1, [1, 137, 411, 2877, 14385, 43155]⟩]),
  (139, [⟨1, 1, [1, 7, 15, 63, 139, 2085, 14595, 43785]⟩]),
  (149, [⟨1, 1, [1, 7, 745, 2235, 9387, 46935]⟩]),
  (151, [⟨1, 1, [1, 7, 9, 127, 453, 1359, 9513, 47565]⟩]),
  (157, [⟨1, 1, [1, 3, 7, 105, 157, 1413, 7065, 49455]⟩]),
  (163, [⟨1, 1, [3, 35, 127, 163, 5705, 51345]⟩]),
  (167, [⟨1, 1, [1, 45, 167, 501, 3507, 52605]⟩]),
  (173, [⟨1, 1, [5, 9, 105, 173, 1211, 54495]⟩]),
  (179, [⟨1, 1, [3, 35, 537, 895, 1253, 1611, 2685, 3759, 6265, 8055, 11277, 18795]⟩]),
  (181, [⟨1, 1, [1, 5, 45, 543, 1267, 1629, 2715, 3801, 6335, 8145, 11403, 19005]⟩]),
  (191, [⟨1, 1, [1, 3, 9, 21, 191, 573, 1337, 4011, 6685, 8595, 12033, 20055]⟩]),
  (193, [⟨1, 1, [1, 35, 127, 193, 965, 4053, 6755, 8685, 12159, 20265]⟩]),
  (197, [⟨1, 1, [3, 21, 63, 197, 591, 2955, 6895, 8865, 12411, 20685]⟩]),
  (199, [⟨1, 1, [1, 9, 63, 2985, 6965, 8955, 12537, 20895]⟩]),
  (211, [⟨1, 1, [9, 105, 211, 1055, 4431, 9495, 13293, 22155]⟩]),
  (223, [⟨1, 1, [3, 35, 1561, 10035, 14049, 23415]⟩]),
  (227, [⟨1, 1, [5, 63, 127, 10215, 14301, 23835]⟩]),
  (229, [⟨1, 1, [1, 7, 45, 127, 1603, 8015, 14427, 24045]⟩]),
  (233, [⟨1, 1, [5, 9, 45, 127, 233, 8155, 14679, 24465]⟩]),
  (239, [⟨1, 1, [1, 45, 1673, 5019, 15057, 25095]⟩]),
  (241, [⟨1, 1, [3, 35, 63, 241, 723, 5061, 15183, 25305]⟩]),
  (251, [⟨1, 1, [9, 45, 753, 2259, 15813, 26355]⟩]),
  (257, [⟨1, 1, [3, 9, 63, 127, 257, 771, 16191, 26985]⟩]),
  (263, [⟨1, 1, [1, 3, 7, 45, 127, 3945, 11835, 27615]⟩]),
  (269, [⟨1, 1, [1, 15, 105, 127, 269, 1883, 12105, 28245]⟩]),
  (271, [⟨1, 1, [1, 7, 63, 127, 271, 1355, 12195, 28455]⟩]),
  (277, [⟨1, 1, [3, 9, 21, 63, 12465, 29085]⟩]),
  (281, [⟨1, 1, [5, 63, 281, 1405, 9835, 29505]⟩]),
  (283, [⟨1, 1, [3, 63, 283, 849, 9905, 29715]⟩]),
  (293, [⟨1, 1, [1, 3, 45, 127, 293, 2051, 6153, 30765]⟩]),
  (307, [⟨1, 1, [7, 45, 307, 2149, 2763, 32235]⟩]),
  (311, [⟨1, 1, [3, 21, 105, 127, 311, 933, 2799, 32655]⟩]),
  (313, [⟨1, 1, [3, 9, 45, 939, 2817, 32865]⟩]),
  (317, [⟨1, 1, [1, 9, 63, 105, 127, 317, 2219, 33285]⟩]),
  (331, [⟨1, 1, [3, 35, 63, 1655, 11585, 20853]⟩]),
  (337, [⟨1, 1, [3, 337, 11795, 21231]⟩]),
  (347, [⟨1, 1, [1, 7, 9, 45, 347, 2429, 7287, 21861]⟩]),
  (349, [⟨1, 1, [5, 63, 105, 127, 349, 1745, 7329, 21987]⟩]),
  (353, [⟨1, 1, [1, 9, 21, 63, 353, 1059, 7413, 22239]⟩]),
  (359, [⟨1, 1, [3, 9, 35, 127, 7539, 22617]⟩]),
  (367, [⟨1, 1, [1, 105, 127, 367, 5505, 23121]⟩]),
  (373, [⟨1, 1, [5, 45, 373, 1119, 3357, 23499]⟩]),
  (379, [⟨1, 1, [5, 45, 105, 127, 3411, 23877]⟩]),
  (383, [⟨1, 1, [3, 15, 63, 127, 2681, 24129]⟩]),
  (389, [⟨1, 1, [127, 389, 1167, 24507]⟩]),
  (397, [⟨1, 1, [3, 9, 63, 25011]⟩]),
  (401, [⟨1, 1, [1, 9, 63, 401, 6015, 18045]⟩]),
  (409, [⟨1, 1, [3, 9, 105, 1227, 3681, 18405]⟩]),
  (419, [⟨1, 1, [9, 21, 105, 127, 2933, 18855]⟩]),
  (421, [⟨1, 1, [1, 7, 63, 105, 127, 421, 2105, 18945]⟩]),
  (431, [⟨1, 1, [1, 9, 127, 1293, 3879, 15085]⟩]),
  (433, [⟨1, 1, [1, 9, 63, 127, 433, 19485]⟩]),
  (439, [⟨1, 1, [1, 3, 7, 21, 381, 439, 3073, 15365]⟩]),
  (443, [⟨1, 1, [5, 127, 3101, 15505]⟩]),
  (449, [⟨1, 1, [3, 15, 381, 449, 1347, 15715]⟩]),
  (457, [⟨1, 1, [5, 9, 45, 63, 105, 127, 457, 15995]⟩]),
  (461, [⟨1, 1, [5, 9, 105, 16135]⟩]),
  (463, [⟨1, 1, [1, 3, 105, 127, 463, 1389, 4167, 9723]⟩]),
  (467, [⟨1, 1, [15, 1401, 4203, 9807]⟩]),
  (479, [⟨1, 1, [3, 15, 45, 63, 105, 127, 3353, 10059]⟩]),
  (487, [⟨1, 1, [1, 3, 2435, 10227]⟩]),
  (491, [⟨1, 1, [35, 63, 105, 127, 1473, 10311]⟩]),
  (499, [⟨1, 1, [1, 3, 7, 21, 499, 10479]⟩]),
  (503, [⟨1, 1, [1, 7, 9, 381, 2515, 7545]⟩]),
  (509, [⟨1, 1, [3, 21, 63, 381, 1527, 7635]⟩]),
  (521, [⟨1, 1, [1, 3, 7, 21, 127, 7815]⟩]),
  (523, [⟨1, 1, [1, 35, 45, 63, 105, 127, 2615, 4707]⟩]),
  (541, [⟨1, 1, [5, 45, 63, 105, 127, 4869]⟩]),
  (547, [⟨1, 1, [1, 9, 547, 3829]⟩]),
  (557, [⟨1, 1, [1, 9, 21, 63, 127, 2785]⟩]),
  (563, [⟨1, 1, [3, 105, 381, 1689]⟩]),
  (569, [⟨1, 1, [1, 3, 15, 127, 569, 635]⟩]),
  (571, [⟨1, 1, [1, 7, 9, 105, 381, 571]⟩]),
  (577, [⟨1, 1, [5, 9, 105, 127]⟩]),
  (587, [⟨2, 1, [1, 7, 9, 105, 127, 2935, 74549, 145161]⟩]),
  (593, [⟨2, 1, [1, 3, 7, 381, 2965, 16129, 26685, 75311]⟩]),
  (599, [⟨2, 1, [7, 45, 63, 105, 127, 599, 2995, 16129]⟩]),
  (601, [⟨2, 2, [5, 21, 63, 601, 1803, 5409, 76327, 1806005]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified127 : verifyBatch 127 qPrimes rows127 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows131 : List Row := [
  (11, [⟨1, 1, [1, 9, 11, 917, 1179, 1965, 2751, 4585, 5895, 8253, 13755, 41265]⟩]),
  (13, [⟨1, 1, [3, 9, 13, 65, 131, 393, 1179, 1965, 2751, 4585, 5895, 8253, 13755, 41265]⟩]),
  (17, [⟨1, 1, [3, 9, 85, 131, 917, 1965, 2751, 4585, 5895, 8253, 13755, 41265]⟩]),
  (19, [⟨1, 1, [1, 15, 19, 131, 655, 1965, 2751, 4585, 5895, 8253, 13755, 41265]⟩]),
  (23, [⟨1, 1, [1, 3, 15, 23, 131, 1965, 2751, 4585, 5895, 8253, 13755, 41265]⟩]),
  (29, [⟨1, 1, [1, 9, 21, 87, 131, 917, 2751, 4585, 5895, 8253, 13755, 41265]⟩]),
  (31, [⟨1, 1, [1, 3, 21, 31, 131, 655, 2751, 4585, 5895, 8253, 13755, 41265]⟩]),
  (37, [⟨1, 1, [1, 655, 1965, 4585, 5895, 8253, 13755, 41265]⟩]),
  (41, [⟨1, 1, [1, 7, 1965, 4585, 5895, 8253, 13755, 41265]⟩]),
  (43, [⟨1, 1, [1, 3, 9, 21, 43, 393, 1179, 4585, 5895, 8253, 13755, 41265]⟩]),
  (47, [⟨1, 1, [1, 15, 21, 47, 917, 4585, 5895, 8253, 13755, 41265]⟩]),
  (53, [⟨1, 1, [1, 7, 21, 4585, 5895, 8253, 13755, 41265]⟩]),
  (59, [⟨1, 1, [1, 45, 59, 131, 655, 2751, 5895, 8253, 13755, 41265]⟩]),
  (61, [⟨1, 1, [1, 7, 35, 131, 393, 2751, 5895, 8253, 13755, 41265]⟩]),
  (67, [⟨1, 1, [7, 45, 67, 131, 917, 1179, 5895, 8253, 13755, 41265]⟩]),
  (71, [⟨1, 1, [1, 9, 45, 71, 393, 1179, 5895, 8253, 13755, 41265]⟩]),
  (73, [⟨1, 1, [1, 63, 131, 1179, 5895, 8253, 13755, 41265]⟩]),
  (79, [⟨1, 1, [9, 393, 5895, 8253, 13755, 41265]⟩]),
  (83, [⟨1, 1, [1, 15, 131, 917, 4585, 8253, 13755, 41265]⟩]),
  (89, [⟨1, 1, [3, 89, 4585, 8253, 13755, 41265]⟩]),
  (97, [⟨1, 1, [9, 97, 131, 393, 2751, 8253, 13755, 41265]⟩]),
  (101, [⟨1, 1, [3, 9, 101, 655, 1965, 8253, 13755, 41265]⟩]),
  (103, [⟨1, 1, [1, 5, 45, 393, 1965, 8253, 13755, 41265]⟩]),
  (107, [⟨1, 1, [1, 3, 9, 45, 131, 393, 1179, 8253, 13755, 41265]⟩]),
  (109, [⟨1, 1, [3, 15, 109, 131, 1179, 8253, 13755, 41265]⟩]),
  (113, [⟨1, 1, [3, 131, 655, 8253, 13755, 41265]⟩]),
  (127, [⟨1, 1, [9, 21, 63, 131, 655, 5895, 13755, 41265]⟩]),
  (137, [⟨1, 1, [1, 9, 21, 137, 411, 2055, 14385, 43155]⟩]),
  (139, [⟨1, 1, [1, 7, 9, 63, 139, 1251, 14595, 43785]⟩]),
  (149, [⟨1, 1, [15, 105, 447, 1341, 9387, 46935]⟩]),
  (151, [⟨1, 1, [1, 9, 63, 755, 9513, 47565]⟩]),
  (157, [⟨1, 1, [1, 15, 21, 63, 471, 1413, 5495, 49455]⟩]),
  (163, [⟨1, 1, [1, 7, 45, 1141, 3423, 51345]⟩]),
  (167, [⟨1, 1, [1, 15, 21, 167, 2505, 52605]⟩]),
  (173, [⟨1, 1, [1, 35, 63, 131, 173, 519, 655, 865, 1211, 1557, 2595, 3633, 6055, 7785, 10899, 18165]⟩]),
  (179, [⟨1, 1, [7, 21, 895, 1611, 2685, 3759, 6265, 8055, 11277, 18795]⟩]),
  (181, [⟨1, 1, [1, 3, 9, 1629, 2715, 3801, 6335, 8145, 11403, 19005]⟩]),
  (191, [⟨1, 1, [3, 9, 35, 4011, 6685, 8595, 12033, 20055]⟩]),
  (193, [⟨1, 1, [1, 3, 15, 131, 193, 2895, 6755, 8685, 12159, 20265]⟩]),
  (197, [⟨1, 1, [1, 21, 197, 1379, 6895, 8865, 12411, 20685]⟩]),
  (199, [⟨1, 1, [5, 45, 131, 597, 6965, 8955, 12537, 20895]⟩]),
  (211, [⟨1, 1, [15, 63, 3165, 9495, 13293, 22155]⟩]),
  (223, [⟨1, 1, [3, 15, 63, 223, 669, 7805, 14049, 23415]⟩]),
  (227, [⟨1, 1, [63, 131, 227, 681, 1589, 4767, 14301, 23835]⟩]),
  (229, [⟨1, 1, [5, 21, 131, 229, 1603, 4809, 14427, 24045]⟩]),
  (233, [⟨1, 1, [5, 9, 105, 233, 1631, 3495, 14679, 24465]⟩]),
  (239, [⟨1, 1, [21, 131, 1195, 2151, 15057, 25095]⟩]),
  (241, [⟨1, 1, [1, 3, 7, 45, 131, 241, 723, 1687, 15183, 25305]⟩]),
  (251, [⟨1, 1, [5, 35, 251, 3765, 11295, 26355]⟩]),
  (257, [⟨1, 1, [1, 7, 15, 105, 257, 1799, 11565, 26985]⟩]),
  (263, [⟨1, 1, [1, 3, 45, 263, 11835, 27615]⟩]),
  (269, [⟨1, 1, [9, 45, 269, 807, 9415, 28245]⟩]),
  (271, [⟨1, 1, [1, 3, 15, 105, 131, 271, 9485, 28455]⟩]),
  (277, [⟨1, 1, [1, 35, 63, 2493, 5817, 29085]⟩]),
  (281, [⟨1, 1, [35, 1405, 5901, 29505]⟩]),
  (283, [⟨1, 1, [15, 849, 5943, 29715]⟩]),
  (293, [⟨1, 1, [35, 1465, 2637, 30765]⟩]),
  (307, [⟨1, 1, [1, 7, 21, 63, 307, 32235]⟩]),
  (311, [⟨1, 1, [7, 21, 105, 131, 311, 933, 10885, 19593]⟩]),
  (313, [⟨1, 1, [1, 3, 45, 939, 10955, 19719]⟩]),
  (317, [⟨1, 1, [1, 7, 21, 105, 131, 317, 951, 2853, 6657, 19971]⟩]),
  (331, [⟨1, 1, [9, 35, 105, 131, 331, 2317, 4965, 20853]⟩]),
  (337, [⟨1, 1, [9, 131, 337, 1011, 5055, 21231]⟩]),
  (347, [⟨1, 1, [3, 21, 105, 1041, 3123, 21861]⟩]),
  (349, [⟨1, 1, [1, 3, 349, 1047, 2443, 21987]⟩]),
  (353, [⟨1, 1, [5, 9, 105, 353, 2471, 22239]⟩]),
  (359, [⟨1, 1, [5, 21, 131, 359, 1077, 22617]⟩]),
  (367, [⟨1, 1, [1, 7, 21, 131, 367, 2569, 3303, 16515]⟩]),
  (373, [⟨1, 1, [9, 63, 105, 131, 373, 1119, 3357, 16785]⟩]),
  (379, [⟨1, 1, [5, 15, 105, 379, 3411, 17055]⟩]),
  (383, [⟨1, 1, [1, 7, 15, 383, 2681, 17235]⟩]),
  (389, [⟨1, 1, [1, 7, 45, 105, 131, 389, 1167, 17505]⟩]),
  (397, [⟨1, 1, [1, 3, 9, 45, 131, 17865]⟩]),
  (401, [⟨1, 1, [1, 3, 7, 21, 131, 401, 2807, 14035]⟩]),
  (409, [⟨1, 1, [7, 21, 131, 409, 1227, 14315]⟩]),
  (419, [⟨1, 1, [1, 7, 105, 131, 419, 1257, 3771, 8799]⟩]),
  (421, [⟨1, 1, [1, 15, 21, 105, 131, 1263, 3789, 8841]⟩]),
  (431, [⟨1, 1, [3, 9, 35, 431, 3017, 9051]⟩]),
  (433, [⟨1, 1, [35, 63, 3031, 9093]⟩]),
  (439, [⟨1, 1, [1, 3, 35, 105, 131, 439, 1317, 9219]⟩]),
  (443, [⟨1, 1, [5, 15, 393, 443, 3101, 6645]⟩]),
  (449, [⟨1, 1, [7, 63, 131, 9429]⟩]),
  (457, [⟨1, 1, [3, 105, 1371, 6855]⟩]),
  (461, [⟨1, 1, [1, 3, 7, 63, 105, 131, 461, 6915]⟩]),
  (463, [⟨1, 1, [3, 21, 393, 6945]⟩]),
  (467, [⟨1, 1, [45, 131, 2335, 4203]⟩]),
  (479, [⟨1, 1, [3, 63, 393, 4311]⟩]),
  (487, [⟨1, 1, [5, 15, 45, 3409]⟩]),
  (491, [⟨1, 1, [1, 5, 21, 45, 63, 105, 131, 2455]⟩]),
  (499, [⟨1, 1, [3, 9, 21, 1497]⟩]),
  (503, [⟨1, 1, [35, 45, 63, 105, 131, 503]⟩]),
  (509, [⟨1, 2, [5, 21, 393, 509, 3563, 32067]⟩, ⟨2, 1, [1, 45, 131, 4581, 17161, 17815, 66679, 200037]⟩]),
  (521, [⟨2, 1, [1, 5, 35, 63, 393, 2605, 4689, 51483]⟩]),
  (523, [⟨2, 1, [1, 393, 523, 17161]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified131 : verifyBatch 131 qPrimes rows131 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows137 : List Row := [
  (11, [⟨1, 1, [1, 3, 9, 77, 137, 411, 1233, 2055, 2877, 4795, 6165, 8631, 14385, 43155]⟩]),
  (13, [⟨1, 1, [1, 13, 91, 137, 1233, 2055, 2877, 4795, 6165, 8631, 14385, 43155]⟩]),
  (17, [⟨1, 1, [1, 15, 119, 137, 411, 2055, 2877, 4795, 6165, 8631, 14385, 43155]⟩]),
  (19, [⟨1, 1, [1, 3, 9, 137, 959, 1233, 2877, 4795, 6165, 8631, 14385, 43155]⟩]),
  (23, [⟨1, 1, [5, 15, 23, 137, 411, 959, 2877, 4795, 6165, 8631, 14385, 43155]⟩]),
  (29, [⟨1, 1, [1, 87, 137, 959, 2055, 4795, 6165, 8631, 14385, 43155]⟩]),
  (31, [⟨1, 1, [1, 9, 93, 685, 2055, 4795, 6165, 8631, 14385, 43155]⟩]),
  (37, [⟨1, 1, [1, 3, 7, 411, 1233, 4795, 6165, 8631, 14385, 43155]⟩]),
  (41, [⟨1, 1, [41, 137, 685, 4795, 6165, 8631, 14385, 43155]⟩]),
  (43, [⟨1, 1, [1, 3, 9, 43, 411, 4795, 6165, 8631, 14385, 43155]⟩]),
  (47, [⟨1, 1, [1, 3, 35, 47, 137, 411, 959, 2877, 6165, 8631, 14385, 43155]⟩]),
  (53, [⟨1, 1, [15, 53, 63, 137, 959, 2055, 6165, 8631, 14385, 43155]⟩]),
  (59, [⟨1, 1, [1, 3, 35, 2055, 6165, 8631, 14385, 43155]⟩]),
  (61, [⟨1, 1, [9, 45, 411, 1233, 6165, 8631, 14385, 43155]⟩]),
  (67, [⟨1, 1, [1, 3, 7, 21, 67, 411, 6165, 8631, 14385, 43155]⟩]),
  (71, [⟨1, 1, [1, 3, 9, 45, 71, 959, 4795, 8631, 14385, 43155]⟩]),
  (73, [⟨1, 1, [7, 685, 4795, 8631, 14385, 43155]⟩]),
  (79, [⟨1, 1, [7, 45, 137, 1233, 2877, 8631, 14385, 43155]⟩]),
  (83, [⟨1, 1, [1, 3, 15, 63, 137, 411, 2877, 8631, 14385, 43155]⟩]),
  (89, [⟨1, 1, [3, 35, 89, 137, 2055, 8631, 14385, 43155]⟩]),
  (97, [⟨1, 1, [5, 45, 685, 8631, 14385, 43155]⟩]),
  (101, [⟨1, 1, [1, 7, 9, 63, 137, 959, 1233, 6165, 14385, 43155]⟩]),
  (103, [⟨1, 1, [1, 3, 7, 21, 63, 685, 1233, 6165, 14385, 43155]⟩]),
  (107, [⟨1, 1, [3, 15, 107, 137, 959, 6165, 14385, 43155]⟩]),
  (109, [⟨1, 1, [3, 137, 685, 6165, 14385, 43155]⟩]),
  (113, [⟨1, 1, [3, 9, 21, 6165, 14385, 43155]⟩]),
  (127, [⟨1, 1, [1, 137, 411, 2877, 14385, 43155]⟩]),
  (131, [⟨1, 1, [1, 9, 21, 137, 411, 2055, 14385, 43155]⟩]),
  (139, [⟨1, 1, [1, 7, 63, 139, 14595, 43785]⟩]),
  (149, [⟨1, 1, [1, 3, 9, 21, 105, 149, 9387, 46935]⟩]),
  (151, [⟨1, 1, [7, 35, 453, 1359, 6795, 47565]⟩]),
  (157, [⟨1, 1, [1, 3, 9, 63, 5495, 49455]⟩]),
  (163, [⟨1, 1, [3, 45, 2445, 51345]⟩]),
  (167, [⟨1, 1, [1, 3, 7, 21, 105, 137, 167, 52605]⟩]),
  (173, [⟨1, 1, [5, 21, 105, 173, 865, 1557, 2595, 3633, 6055, 7785, 10899, 18165]⟩]),
  (179, [⟨1, 1, [1, 3, 9, 895, 1611, 3759, 6265, 8055, 11277, 18795]⟩]),
  (181, [⟨1, 1, [137, 181, 1267, 3801, 6335, 8145, 11403, 19005]⟩]),
  (191, [⟨1, 1, [1, 3, 21, 137, 191, 573, 6685, 8595, 12033, 20055]⟩]),
  (193, [⟨1, 1, [1, 3, 9, 21, 6755, 8685, 12159, 20265]⟩]),
  (197, [⟨1, 1, [1, 7, 15, 985, 4137, 8865, 12411, 20685]⟩]),
  (199, [⟨1, 1, [7, 137, 4179, 8955, 12537, 20895]⟩]),
  (211, [⟨1, 1, [3, 21, 1477, 7385, 13293, 22155]⟩]),
  (223, [⟨1, 1, [1, 3, 9, 21, 1115, 3345, 14049, 23415]⟩]),
  (227, [⟨1, 1, [1, 15, 63, 227, 681, 2043, 14301, 23835]⟩]),
  (229, [⟨1, 1, [1, 7, 229, 2061, 14427, 24045]⟩]),
  (233, [⟨1, 1, [9, 21, 105, 699, 14679, 24465]⟩]),
  (239, [⟨1, 1, [9, 63, 717, 2151, 10755, 25095]⟩]),
  (241, [⟨1, 1, [3, 9, 63, 2169, 10845, 25305]⟩]),
  (251, [⟨1, 1, [1, 3, 15, 1255, 8785, 26355]⟩]),
  (257, [⟨1, 1, [1, 7, 9, 257, 771, 1799, 5397, 26985]⟩]),
  (263, [⟨1, 1, [1, 5, 105, 789, 5523, 27615]⟩]),
  (269, [⟨1, 1, [1, 3, 7, 21, 269, 1883, 2421, 28245]⟩]),
  (271, [⟨1, 1, [5, 63, 137, 1355, 2439, 28455]⟩]),
  (277, [⟨1, 1, [105, 137, 1939, 29085]⟩]),
  (281, [⟨1, 1, [21, 105, 843, 29505]⟩]),
  (283, [⟨1, 1, [1, 7, 9, 63, 283, 29715]⟩]),
  (293, [⟨1, 1, [21, 105, 137, 293, 879, 2051, 6153, 18459]⟩]),
  (307, [⟨1, 1, [15, 137, 307, 921, 4605, 19341]⟩]),
  (311, [⟨1, 1, [1, 3, 9, 21, 105, 137, 4665, 19593]⟩]),
  (313, [⟨1, 1, [1, 15, 21, 1565, 2817, 19719]⟩]),
  (317, [⟨1, 1, [5, 63, 137, 317, 2853, 19971]⟩]),
  (331, [⟨1, 1, [7, 45, 331, 2317, 2979, 14895]⟩]),
  (337, [⟨1, 1, [5, 35, 137, 1011, 3033, 15165]⟩]),
  (347, [⟨1, 1, [1, 3, 7, 45, 1735, 15615]⟩]),
  (349, [⟨1, 1, [1, 15, 105, 137, 1047, 15705]⟩]),
  (353, [⟨1, 1, [7, 21, 63, 105, 137, 15885]⟩]),
  (359, [⟨1, 1, [1, 5, 63, 105, 137, 359, 1795, 12565]⟩]),
  (367, [⟨1, 1, [1, 3, 9, 21, 63, 137, 367, 12845]⟩]),
  (373, [⟨1, 1, [1, 7, 9, 63, 105, 137, 373, 1119, 2611, 7833]⟩]),
  (379, [⟨1, 1, [1, 15, 63, 379, 2653, 7959]⟩]),
  (383, [⟨1, 1, [15, 63, 105, 137, 1915, 8043]⟩]),
  (389, [⟨1, 1, [1, 5, 137, 389, 2723, 5835]⟩]),
  (397, [⟨1, 1, [1, 9, 45, 63, 105, 137, 1191, 5955]⟩]),
  (401, [⟨1, 1, [1, 3, 7, 45, 105, 137, 401, 6015]⟩]),
  (409, [⟨1, 1, [1, 21, 63, 137, 1227, 3681]⟩]),
  (419, [⟨1, 1, [1, 7, 9, 63, 137, 2933]⟩]),
  (421, [⟨1, 1, [7, 21, 63, 137, 421, 2105]⟩]),
  (431, [⟨1, 1, [3, 35, 63, 105, 137, 431]⟩]),
  (433, [⟨1, 1, [7, 21, 45, 63, 105, 137]⟩]),
  (439, [⟨2, 1, [3, 9, 21, 45, 63, 105, 137, 9219, 60143, 93845]⟩]),
  (443, [⟨2, 1, [1, 9, 137, 443, 685, 56307]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified137 : verifyBatch 137 qPrimes rows137 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows139 : List Row := [
  (11, [⟨1, 1, [11, 33, 77, 417, 1251, 2085, 2919, 4865, 6255, 8757, 14595, 43785]⟩]),
  (13, [⟨1, 1, [1, 117, 1251, 2085, 2919, 4865, 6255, 8757, 14595, 43785]⟩]),
  (17, [⟨1, 1, [1, 9, 17, 85, 417, 2085, 2919, 4865, 6255, 8757, 14595, 43785]⟩]),
  (19, [⟨1, 1, [5, 9, 95, 2085, 2919, 4865, 6255, 8757, 14595, 43785]⟩]),
  (23, [⟨1, 1, [1, 3, 7, 23, 69, 1251, 2919, 4865, 6255, 8757, 14595, 43785]⟩]),
  (29, [⟨1, 1, [7, 87, 2919, 4865, 6255, 8757, 14595, 43785]⟩]),
  (31, [⟨1, 1, [15, 31, 45, 417, 2085, 4865, 6255, 8757, 14595, 43785]⟩]),
  (37, [⟨1, 1, [37, 45, 1251, 4865, 6255, 8757, 14595, 43785]⟩]),
  (41, [⟨1, 1, [35, 41, 417, 4865, 6255, 8757, 14595, 43785]⟩]),
  (43, [⟨1, 1, [9, 21, 43, 4865, 6255, 8757, 14595, 43785]⟩]),
  (47, [⟨1, 1, [5, 15, 47, 139, 973, 2919, 6255, 8757, 14595, 43785]⟩]),
  (53, [⟨1, 1, [5, 53, 695, 2085, 6255, 8757, 14595, 43785]⟩]),
  (59, [⟨1, 1, [1, 3, 45, 139, 417, 973, 6255, 8757, 14595, 43785]⟩]),
  (61, [⟨1, 1, [1, 45, 139, 973, 6255, 8757, 14595, 43785]⟩]),
  (67, [⟨1, 1, [1, 15, 21, 1251, 4865, 8757, 14595, 43785]⟩]),
  (71, [⟨1, 1, [1, 9, 21, 417, 4865, 8757, 14595, 43785]⟩]),
  (73, [⟨1, 1, [7, 21, 4865, 8757, 14595, 43785]⟩]),
  (79, [⟨1, 1, [1, 3, 15, 695, 2919, 8757, 14595, 43785]⟩]),
  (83, [⟨1, 1, [1, 3, 9, 695, 2085, 8757, 14595, 43785]⟩]),
  (89, [⟨1, 1, [1, 3, 139, 417, 973, 8757, 14595, 43785]⟩]),
  (97, [⟨1, 1, [1, 3, 9, 21, 97, 139, 2085, 6255, 14595, 43785]⟩]),
  (101, [⟨1, 1, [3, 21, 101, 139, 1251, 6255, 14595, 43785]⟩]),
  (103, [⟨1, 1, [1, 3, 15, 103, 973, 6255, 14595, 43785]⟩]),
  (107, [⟨1, 1, [9, 107, 139, 6255, 14595, 43785]⟩]),
  (109, [⟨1, 1, [1, 3, 109, 139, 973, 4865, 14595, 43785]⟩]),
  (113, [⟨1, 1, [9, 35, 63, 139, 2085, 2919, 14595, 43785]⟩]),
  (127, [⟨1, 1, [1, 7, 15, 63, 139, 2085, 14595, 43785]⟩]),
  (131, [⟨1, 1, [1, 7, 9, 63, 139, 1251, 14595, 43785]⟩]),
  (137, [⟨1, 1, [1, 7, 63, 139, 14595, 43785]⟩]),
  (149, [⟨1, 1, [1, 45, 149, 2235, 6705, 46935]⟩]),
  (151, [⟨1, 1, [1, 3, 15, 63, 151, 1057, 6795, 47565]⟩]),
  (157, [⟨1, 1, [5, 63, 157, 1413, 3297, 49455]⟩]),
  (163, [⟨1, 1, [1, 15, 139, 163, 1467, 51345]⟩]),
  (167, [⟨1, 1, [5, 21, 105, 139, 167, 417, 501, 835, 1169, 1503, 2505, 3507, 5845, 7515, 10521, 17535]⟩]),
  (173, [⟨1, 1, [1, 7, 21, 139, 173, 1557, 2595, 3633, 6055, 7785, 10899, 18165]⟩]),
  (179, [⟨1, 1, [1, 7, 1611, 3759, 6265, 8055, 11277, 18795]⟩]),
  (181, [⟨1, 1, [1, 3, 9, 105, 543, 3801, 6335, 8145, 11403, 19005]⟩]),
  (191, [⟨1, 1, [1, 9, 63, 191, 573, 1719, 4011, 8595, 12033, 20055]⟩]),
  (193, [⟨1, 1, [1, 3, 15, 105, 193, 1351, 4053, 8685, 12159, 20265]⟩]),
  (197, [⟨1, 1, [5, 21, 63, 985, 2955, 8865, 12411, 20685]⟩]),
  (199, [⟨1, 1, [5, 9, 45, 139, 2985, 8955, 12537, 20895]⟩]),
  (211, [⟨1, 1, [1, 5, 211, 7385, 13293, 22155]⟩]),
  (223, [⟨1, 1, [7, 21, 139, 223, 669, 2007, 14049, 23415]⟩]),
  (227, [⟨1, 1, [1, 7, 45, 139, 227, 1135, 14301, 23835]⟩]),
  (229, [⟨1, 1, [1, 5, 105, 687, 14427, 24045]⟩]),
  (233, [⟨1, 1, [1, 15, 63, 139, 1165, 2097, 10485, 24465]⟩]),
  (239, [⟨1, 1, [5, 15, 105, 1195, 10755, 25095]⟩]),
  (241, [⟨1, 1, [1, 3, 9, 105, 723, 2169, 8435, 25305]⟩]),
  (251, [⟨1, 1, [3, 9, 753, 2259, 5271, 26355]⟩]),
  (257, [⟨1, 1, [35, 63, 139, 771, 5397, 26985]⟩]),
  (263, [⟨1, 1, [9, 35, 263, 1841, 2367, 27615]⟩]),
  (269, [⟨1, 1, [5, 15, 45, 139, 2421, 28245]⟩]),
  (271, [⟨1, 1, [35, 63, 1897, 28455]⟩]),
  (277, [⟨1, 1, [105, 29085]⟩]),
  (281, [⟨1, 1, [1, 5, 105, 139, 281, 4215, 5901, 17703]⟩]),
  (283, [⟨1, 1, [3, 9, 45, 139, 9905, 17829]⟩]),
  (293, [⟨1, 1, [1, 45, 293, 879, 6153, 18459]⟩]),
  (307, [⟨1, 1, [3, 9, 21, 139, 307, 921, 2149, 19341]⟩]),
  (311, [⟨1, 1, [1, 35, 105, 139, 2177, 19593]⟩]),
  (313, [⟨1, 1, [3, 9, 21, 313, 1565, 19719]⟩]),
  (317, [⟨1, 1, [1, 45, 139, 1585, 4755, 14265]⟩]),
  (331, [⟨1, 1, [63, 105, 139, 331, 2317, 14895]⟩]),
  (337, [⟨1, 1, [5, 9, 63, 337, 1011, 15165]⟩]),
  (347, [⟨1, 1, [1, 3, 15, 105, 139, 347, 1735, 12145]⟩]),
  (349, [⟨1, 1, [5, 105, 1745, 12215]⟩]),
  (353, [⟨1, 1, [9, 21, 139, 353, 5295, 7413]⟩]),
  (359, [⟨1, 1, [3, 15, 105, 1077, 3231, 7539]⟩]),
  (367, [⟨1, 1, [5, 9, 2569, 7707]⟩]),
  (373, [⟨1, 1, [15, 63, 1119, 7833]⟩]),
  (379, [⟨1, 1, [1, 5, 45, 139, 1895, 5685]⟩]),
  (383, [⟨1, 1, [1, 35, 1149, 5745]⟩]),
  (389, [⟨1, 1, [1, 21, 63, 139, 1945, 3501]⟩]),
  (397, [⟨1, 1, [5, 15, 397, 3573]⟩]),
  (401, [⟨1, 1, [1, 35, 63, 105, 139, 2807]⟩]),
  (409, [⟨1, 1, [1, 5, 35, 63, 139, 1227]⟩]),
  (419, [⟨2, 1, [1, 35, 63, 105, 139, 19321, 58241, 96605]⟩]),
  (421, [⟨2, 1, [1, 3, 9, 45, 417, 421, 57963, 58519]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified139 : verifyBatch 139 qPrimes rows139 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows149 : List Row := [
  (11, [⟨1, 1, [5, 33, 1341, 2235, 3129, 5215, 6705, 9387, 15645, 46935]⟩]),
  (13, [⟨1, 1, [3, 91, 745, 2235, 3129, 5215, 6705, 9387, 15645, 46935]⟩]),
  (17, [⟨1, 1, [1, 5, 51, 149, 447, 1341, 3129, 5215, 6705, 9387, 15645, 46935]⟩]),
  (19, [⟨1, 1, [3, 15, 95, 1341, 3129, 5215, 6705, 9387, 15645, 46935]⟩]),
  (23, [⟨1, 1, [7, 69, 149, 1043, 2235, 5215, 6705, 9387, 15645, 46935]⟩]),
  (29, [⟨1, 1, [1, 7, 87, 447, 1341, 5215, 6705, 9387, 15645, 46935]⟩]),
  (31, [⟨1, 1, [1, 5, 21, 31, 93, 149, 1043, 5215, 6705, 9387, 15645, 46935]⟩]),
  (37, [⟨1, 1, [21, 447, 1341, 3129, 6705, 9387, 15645, 46935]⟩]),
  (41, [⟨1, 1, [1, 9, 123, 149, 447, 3129, 6705, 9387, 15645, 46935]⟩]),
  (43, [⟨1, 1, [5, 35, 149, 3129, 6705, 9387, 15645, 46935]⟩]),
  (47, [⟨1, 1, [3, 2235, 6705, 9387, 15645, 46935]⟩]),
  (53, [⟨1, 1, [1, 21, 149, 447, 6705, 9387, 15645, 46935]⟩]),
  (59, [⟨1, 1, [1, 5, 35, 447, 5215, 9387, 15645, 46935]⟩]),
  (61, [⟨1, 1, [1, 35, 61, 149, 447, 1341, 3129, 9387, 15645, 46935]⟩]),
  (67, [⟨1, 1, [1, 3, 45, 67, 149, 1043, 2235, 9387, 15645, 46935]⟩]),
  (71, [⟨1, 1, [1, 7, 71, 149, 2235, 9387, 15645, 46935]⟩]),
  (73, [⟨1, 1, [1, 7, 9, 45, 73, 447, 1341, 9387, 15645, 46935]⟩]),
  (79, [⟨1, 1, [5, 745, 2235, 6705, 15645, 46935]⟩]),
  (83, [⟨1, 1, [1, 3, 9, 21, 83, 447, 1341, 6705, 15645, 46935]⟩]),
  (89, [⟨1, 1, [3, 9, 35, 89, 149, 6705, 15645, 46935]⟩]),
  (97, [⟨1, 1, [1, 7, 9, 45, 149, 447, 1043, 3129, 15645, 46935]⟩]),
  (101, [⟨1, 1, [1, 3, 21, 149, 447, 3129, 15645, 46935]⟩]),
  (103, [⟨1, 1, [3, 15, 63, 3129, 15645, 46935]⟩]),
  (107, [⟨1, 1, [9, 35, 745, 1341, 15645, 46935]⟩]),
  (109, [⟨1, 1, [1, 15, 21, 63, 149, 1341, 15645, 46935]⟩]),
  (113, [⟨1, 1, [63, 447, 15645, 46935]⟩]),
  (127, [⟨1, 1, [1, 7, 745, 2235, 9387, 46935]⟩]),
  (131, [⟨1, 1, [15, 105, 447, 1341, 9387, 46935]⟩]),
  (137, [⟨1, 1, [1, 3, 9, 21, 105, 149, 9387, 46935]⟩]),
  (139, [⟨1, 1, [1, 45, 149, 2235, 6705, 46935]⟩]),
  (151, [⟨1, 1, [5, 21, 105, 151, 453, 1359, 3171, 47565]⟩]),
  (157, [⟨1, 1, [7, 21, 157, 471, 1099, 49455]⟩]),
  (163, [⟨1, 1, [3, 35, 163, 489, 1141, 1467, 2445, 3423, 5705, 7335, 10269, 17115]⟩]),
  (167, [⟨1, 1, [1, 7, 9, 63, 167, 835, 2505, 3507, 5845, 7515, 10521, 17535]⟩]),
  (173, [⟨1, 1, [7, 173, 1211, 2595, 6055, 7785, 10899, 18165]⟩]),
  (179, [⟨1, 1, [1, 3, 9, 149, 179, 537, 6265, 8055, 11277, 18795]⟩]),
  (181, [⟨1, 1, [1, 7, 15, 181, 543, 1629, 3801, 8145, 11403, 19005]⟩]),
  (191, [⟨1, 1, [1, 9, 1337, 8595, 12033, 20055]⟩]),
  (193, [⟨1, 1, [1, 3, 35, 149, 193, 8685, 12159, 20265]⟩]),
  (197, [⟨1, 1, [1, 3, 21, 197, 2955, 4137, 12411, 20685]⟩]),
  (199, [⟨1, 1, [7, 63, 199, 597, 1393, 4179, 12537, 20895]⟩]),
  (211, [⟨1, 1, [1, 21, 105, 1055, 13293, 22155]⟩]),
  (223, [⟨1, 1, [5, 9, 149, 2007, 7805, 23415]⟩]),
  (227, [⟨1, 1, [1, 3, 9, 63, 227, 3405, 4767, 23835]⟩]),
  (229, [⟨1, 1, [1, 3, 15, 149, 687, 2061, 4809, 24045]⟩]),
  (233, [⟨1, 1, [3, 15, 149, 1165, 4893, 24465]⟩]),
  (239, [⟨1, 1, [1, 45, 105, 239, 3585, 25095]⟩]),
  (241, [⟨1, 1, [1, 7, 21, 63, 241, 723, 2169, 25305]⟩]),
  (251, [⟨1, 1, [1, 15, 63, 149, 251, 753, 8785, 15813]⟩]),
  (257, [⟨1, 1, [7, 45, 257, 2313, 5397, 16191]⟩]),
  (263, [⟨1, 1, [1, 7, 15, 63, 149, 263, 5523, 16569]⟩]),
  (269, [⟨1, 1, [3, 105, 149, 1345, 2421, 16947]⟩]),
  (271, [⟨1, 1, [105, 813, 2439, 17073]⟩]),
  (277, [⟨1, 1, [1, 3, 35, 63, 149, 277, 831, 17451]⟩]),
  (281, [⟨1, 1, [1, 5, 21, 17703]⟩]),
  (283, [⟨1, 1, [1, 15, 45, 149, 4245, 12735]⟩]),
  (293, [⟨1, 1, [7, 21, 105, 293, 879, 13185]⟩]),
  (307, [⟨1, 1, [3, 15, 105, 149, 307, 921, 2763, 6447]⟩]),
  (311, [⟨1, 1, [1, 45, 105, 149, 2799, 6531]⟩]),
  (313, [⟨1, 1, [1, 3, 9, 313, 2191, 6573]⟩]),
  (317, [⟨1, 1, [1, 21, 63, 317, 951, 6657]⟩]),
  (331, [⟨1, 1, [1, 3, 105, 149, 993, 2979]⟩]),
  (337, [⟨1, 1, [1, 3, 35, 63, 149, 2359]⟩]),
  (347, [⟨1, 2, [3, 105, 149, 3123, 7287, 51703]⟩, ⟨2, 1, [15, 45, 347, 1041, 3123, 21861, 22201, 155109]⟩]),
  (349, [⟨2, 1, [1, 3, 21, 63, 105, 149, 349, 5235, 52001, 66603]⟩]),
  (353, [⟨2, 2, [1, 3, 7, 21, 353, 1059, 22201, 37065, 52597, 1869135]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified149 : verifyBatch 149 qPrimes rows149 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows151 : List Row := [
  (11, [⟨1, 1, [1, 11, 77, 151, 1057, 2265, 3171, 5285, 6795, 9513, 15855, 47565]⟩]),
  (13, [⟨1, 1, [3, 9, 117, 151, 453, 2265, 3171, 5285, 6795, 9513, 15855, 47565]⟩]),
  (17, [⟨1, 1, [7, 51, 453, 1359, 3171, 5285, 6795, 9513, 15855, 47565]⟩]),
  (19, [⟨1, 1, [3, 95, 151, 1057, 3171, 5285, 6795, 9513, 15855, 47565]⟩]),
  (23, [⟨1, 1, [1, 3, 23, 151, 3171, 5285, 6795, 9513, 15855, 47565]⟩]),
  (29, [⟨1, 1, [1, 9, 21, 29, 87, 151, 1359, 5285, 6795, 9513, 15855, 47565]⟩]),
  (31, [⟨1, 1, [5, 31, 1057, 5285, 6795, 9513, 15855, 47565]⟩]),
  (37, [⟨1, 1, [5, 151, 1359, 3171, 6795, 9513, 15855, 47565]⟩]),
  (41, [⟨1, 1, [9, 35, 41, 151, 1057, 2265, 6795, 9513, 15855, 47565]⟩]),
  (43, [⟨1, 1, [1, 3, 15, 43, 63, 151, 453, 2265, 6795, 9513, 15855, 47565]⟩]),
  (47, [⟨1, 1, [7, 47, 453, 1359, 6795, 9513, 15855, 47565]⟩]),
  (53, [⟨1, 1, [1, 7, 15, 151, 6795, 9513, 15855, 47565]⟩]),
  (59, [⟨1, 1, [21, 59, 63, 151, 453, 1359, 3171, 9513, 15855, 47565]⟩]),
  (61, [⟨1, 1, [1, 3, 7, 21, 151, 1359, 3171, 9513, 15855, 47565]⟩]),
  (67, [⟨1, 1, [1, 755, 2265, 9513, 15855, 47565]⟩]),
  (71, [⟨1, 1, [1, 9, 71, 453, 1359, 9513, 15855, 47565]⟩]),
  (73, [⟨1, 1, [3, 45, 73, 151, 1057, 9513, 15855, 47565]⟩]),
  (79, [⟨1, 1, [1, 3, 7, 79, 2265, 6795, 15855, 47565]⟩]),
  (83, [⟨1, 1, [1, 3, 15, 151, 1057, 6795, 15855, 47565]⟩]),
  (89, [⟨1, 1, [5, 45, 89, 151, 755, 5285, 15855, 47565]⟩]),
  (97, [⟨1, 1, [1, 5, 45, 97, 755, 3171, 15855, 47565]⟩]),
  (101, [⟨1, 1, [5, 9, 63, 151, 453, 2265, 15855, 47565]⟩]),
  (103, [⟨1, 1, [5, 9, 103, 2265, 15855, 47565]⟩]),
  (107, [⟨1, 1, [1, 45, 151, 1057, 15855, 47565]⟩]),
  (109, [⟨1, 1, [1, 7, 15, 63, 151, 453, 15855, 47565]⟩]),
  (113, [⟨1, 1, [15, 151, 453, 5285, 9513, 47565]⟩]),
  (127, [⟨1, 1, [1, 7, 9, 127, 453, 1359, 9513, 47565]⟩]),
  (131, [⟨1, 1, [1, 9, 63, 755, 9513, 47565]⟩]),
  (137, [⟨1, 1, [7, 35, 453, 1359, 6795, 47565]⟩]),
  (139, [⟨1, 1, [1, 3, 15, 63, 151, 1057, 6795, 47565]⟩]),
  (149, [⟨1, 1, [5, 21, 105, 151, 453, 1359, 3171, 47565]⟩]),
  (157, [⟨1, 1, [5, 15, 1099, 49455]⟩]),
  (163, [⟨1, 1, [5, 35, 105, 163, 815, 1467, 2445, 3423, 5705, 7335, 10269, 17115]⟩]),
  (167, [⟨1, 1, [1, 7, 151, 167, 2505, 3507, 5845, 7515, 10521, 17535]⟩]),
  (173, [⟨1, 1, [9, 35, 519, 2595, 6055, 7785, 10899, 18165]⟩]),
  (179, [⟨1, 1, [1, 5, 151, 179, 537, 1611, 3759, 8055, 11277, 18795]⟩]),
  (181, [⟨1, 1, [1, 3, 181, 1267, 3801, 8145, 11403, 19005]⟩]),
  (191, [⟨1, 1, [7, 105, 191, 8595, 12033, 20055]⟩]),
  (193, [⟨1, 1, [1, 21, 63, 193, 965, 6755, 12159, 20265]⟩]),
  (197, [⟨1, 1, [7, 21, 63, 197, 1773, 4137, 12411, 20685]⟩]),
  (199, [⟨1, 1, [1, 3, 15, 105, 995, 4179, 12537, 20895]⟩]),
  (211, [⟨1, 1, [1, 3, 105, 211, 1477, 1899, 9495, 22155]⟩]),
  (223, [⟨1, 1, [1, 9, 63, 669, 7805, 23415]⟩]),
  (227, [⟨1, 1, [3, 35, 151, 2043, 4767, 23835]⟩]),
  (229, [⟨1, 1, [7, 35, 229, 1145, 4809, 24045]⟩]),
  (233, [⟨1, 1, [1, 7, 9, 1165, 3495, 24465]⟩]),
  (239, [⟨1, 1, [1, 7, 45, 151, 2151, 25095]⟩]),
  (241, [⟨1, 1, [9, 21, 105, 241, 1205, 25305]⟩]),
  (251, [⟨1, 1, [7, 63, 151, 251, 753, 1757, 5271, 15813]⟩]),
  (257, [⟨1, 1, [15, 771, 5397, 16191]⟩]),
  (263, [⟨1, 1, [1, 7, 9, 151, 3945, 16569]⟩]),
  (269, [⟨1, 1, [9, 151, 1883, 16947]⟩]),
  (271, [⟨1, 1, [1, 3, 9, 105, 151, 271, 813, 17073]⟩]),
  (277, [⟨1, 1, [9, 105, 4155, 12465]⟩]),
  (281, [⟨1, 1, [151, 281, 2529, 12645]⟩]),
  (283, [⟨1, 1, [1, 7, 35, 283, 1981, 12735]⟩]),
  (293, [⟨1, 1, [1, 3, 9, 45, 151, 293, 1465, 10255]⟩]),
  (307, [⟨1, 1, [1, 35, 105, 151, 1535, 6447]⟩]),
  (311, [⟨1, 1, [3, 45, 105, 151, 311, 6531]⟩]),
  (313, [⟨1, 1, [9, 6573]⟩]),
  (317, [⟨1, 1, [5, 15, 45, 317, 2219, 2853]⟩]),
  (331, [⟨1, 1, [1, 9, 21, 151, 331, 993]⟩]),
  (337, [⟨1, 2, [151, 337, 1011, 2359, 7077, 21231]⟩, ⟨2, 1, [1, 9, 21, 105, 151, 7077, 22801, 152661]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified151 : verifyBatch 151 qPrimes rows151 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows157 : List Row := [
  (11, [⟨1, 1, [1, 9, 99, 157, 785, 2355, 3297, 5495, 7065, 9891, 16485, 49455]⟩]),
  (13, [⟨1, 1, [1, 9, 91, 157, 1099, 1413, 3297, 5495, 7065, 9891, 16485, 49455]⟩]),
  (17, [⟨1, 1, [85, 1413, 3297, 5495, 7065, 9891, 16485, 49455]⟩]),
  (19, [⟨1, 1, [1, 19, 57, 785, 3297, 5495, 7065, 9891, 16485, 49455]⟩]),
  (23, [⟨1, 1, [3, 23, 35, 471, 2355, 5495, 7065, 9891, 16485, 49455]⟩]),
  (29, [⟨1, 1, [1, 7, 29, 157, 785, 5495, 7065, 9891, 16485, 49455]⟩]),
  (31, [⟨1, 1, [1, 7, 21, 157, 2355, 3297, 7065, 9891, 16485, 49455]⟩]),
  (37, [⟨1, 1, [5, 157, 471, 3297, 7065, 9891, 16485, 49455]⟩]),
  (41, [⟨1, 1, [1, 7, 15, 123, 157, 2355, 7065, 9891, 16485, 49455]⟩]),
  (43, [⟨1, 1, [9, 129, 471, 1413, 7065, 9891, 16485, 49455]⟩]),
  (47, [⟨1, 1, [3, 9, 47, 63, 157, 471, 7065, 9891, 16485, 49455]⟩]),
  (53, [⟨1, 1, [45, 53, 157, 2355, 3297, 9891, 16485, 49455]⟩]),
  (59, [⟨1, 1, [15, 59, 157, 471, 3297, 9891, 16485, 49455]⟩]),
  (61, [⟨1, 1, [5, 61, 3297, 9891, 16485, 49455]⟩]),
  (67, [⟨1, 1, [7, 35, 1413, 9891, 16485, 49455]⟩]),
  (71, [⟨1, 1, [5, 21, 157, 9891, 16485, 49455]⟩]),
  (73, [⟨1, 1, [3, 15, 2355, 7065, 16485, 49455]⟩]),
  (79, [⟨1, 1, [9, 63, 79, 471, 1413, 5495, 16485, 49455]⟩]),
  (83, [⟨1, 1, [7, 45, 83, 157, 471, 5495, 16485, 49455]⟩]),
  (89, [⟨1, 1, [1, 21, 89, 157, 785, 3297, 16485, 49455]⟩]),
  (97, [⟨1, 1, [1, 15, 63, 157, 471, 1099, 16485, 49455]⟩]),
  (101, [⟨1, 1, [63, 471, 16485, 49455]⟩]),
  (103, [⟨1, 1, [1, 9, 45, 157, 785, 5495, 9891, 49455]⟩]),
  (107, [⟨1, 1, [1, 3, 35, 471, 1413, 3297, 9891, 49455]⟩]),
  (109, [⟨1, 1, [1, 9, 21, 157, 1099, 3297, 9891, 49455]⟩]),
  (113, [⟨1, 1, [15, 3297, 9891, 49455]⟩]),
  (127, [⟨1, 1, [1, 3, 7, 105, 157, 1413, 7065, 49455]⟩]),
  (131, [⟨1, 1, [1, 15, 21, 63, 471, 1413, 5495, 49455]⟩]),
  (137, [⟨1, 1, [1, 3, 9, 63, 5495, 49455]⟩]),
  (139, [⟨1, 1, [5, 63, 157, 1413, 3297, 49455]⟩]),
  (149, [⟨1, 1, [7, 21, 157, 471, 1099, 49455]⟩]),
  (151, [⟨1, 1, [5, 15, 1099, 49455]⟩]),
  (163, [⟨1, 1, [35, 105, 163, 1141, 1467, 3423, 5705, 7335, 10269, 17115]⟩]),
  (167, [⟨1, 1, [1, 7, 9, 45, 501, 3507, 5845, 7515, 10521, 17535]⟩]),
  (173, [⟨1, 1, [5, 45, 105, 519, 6055, 7785, 10899, 18165]⟩]),
  (179, [⟨1, 1, [1, 15, 21, 105, 179, 537, 2685, 8055, 11277, 18795]⟩]),
  (181, [⟨1, 1, [1, 7, 15, 105, 181, 543, 1629, 8145, 11403, 19005]⟩]),
  (191, [⟨1, 1, [1, 35, 1719, 4011, 12033, 20055]⟩]),
  (193, [⟨1, 1, [5, 157, 579, 4053, 12159, 20265]⟩]),
  (197, [⟨1, 1, [1, 7, 21, 63, 985, 1773, 12411, 20685]⟩]),
  (199, [⟨1, 1, [3, 21, 63, 1791, 12537, 20895]⟩]),
  (211, [⟨1, 1, [1, 9, 45, 1899, 7385, 22155]⟩]),
  (223, [⟨1, 1, [5, 21, 223, 669, 3345, 23415]⟩]),
  (227, [⟨1, 1, [1, 3, 7, 63, 227, 681, 1589, 23835]⟩]),
  (229, [⟨1, 1, [1, 7, 9, 105, 1603, 24045]⟩]),
  (233, [⟨1, 1, [3, 9, 21, 24465]⟩]),
  (239, [⟨1, 1, [1, 3, 15, 105, 239, 2151, 5019, 15057]⟩]),
  (241, [⟨1, 1, [1, 7, 15, 1687, 5061, 15183]⟩]),
  (251, [⟨1, 1, [1, 7, 35, 157, 251, 753, 1757, 15813]⟩]),
  (257, [⟨1, 1, [1, 3, 157, 1285, 3855, 11565]⟩]),
  (263, [⟨1, 1, [1, 9, 63, 157, 263, 789, 1841, 11835]⟩]),
  (269, [⟨1, 1, [3, 9, 21, 105, 807, 12105]⟩]),
  (271, [⟨1, 1, [1, 7, 9, 45, 157, 12195]⟩]),
  (277, [⟨1, 1, [1, 15, 21, 63, 157, 277, 4155, 5817]⟩]),
  (281, [⟨1, 1, [1, 21, 63, 157, 281, 843, 1967, 5901]⟩]),
  (283, [⟨1, 1, [3, 105, 2547, 5943]⟩]),
  (293, [⟨1, 1, [1, 3, 35, 105, 879, 4395]⟩]),
  (307, [⟨1, 1, [45, 921]⟩]),
  (311, [⟨1, 2, [5, 311, 933, 2177]⟩, ⟨2, 1, [1, 7, 157, 146481]⟩]),
  (313, [⟨2, 1, [1, 3, 7, 63, 157, 313, 939, 2191, 19719, 24649]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified157 : verifyBatch 157 qPrimes rows157 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows163 : List Row := [
  (11, [⟨1, 1, [1, 9, 11, 33, 99, 163, 489, 2445, 3423, 5705, 7335, 10269, 17115, 51345]⟩]),
  (13, [⟨1, 1, [1, 5, 91, 2445, 3423, 5705, 7335, 10269, 17115, 51345]⟩]),
  (17, [⟨1, 1, [3, 9, 17, 119, 163, 815, 3423, 5705, 7335, 10269, 17115, 51345]⟩]),
  (19, [⟨1, 1, [1, 15, 19, 57, 163, 1141, 2445, 5705, 7335, 10269, 17115, 51345]⟩]),
  (23, [⟨1, 1, [5, 23, 115, 815, 1467, 5705, 7335, 10269, 17115, 51345]⟩]),
  (29, [⟨1, 1, [1, 21, 29, 87, 163, 5705, 7335, 10269, 17115, 51345]⟩]),
  (31, [⟨1, 1, [1, 5, 31, 45, 163, 489, 1141, 3423, 7335, 10269, 17115, 51345]⟩]),
  (37, [⟨1, 1, [5, 35, 37, 163, 489, 2445, 7335, 10269, 17115, 51345]⟩]),
  (41, [⟨1, 1, [5, 123, 163, 1467, 7335, 10269, 17115, 51345]⟩]),
  (43, [⟨1, 1, [1, 7, 21, 43, 163, 815, 7335, 10269, 17115, 51345]⟩]),
  (47, [⟨1, 1, [1, 3, 9, 47, 63, 1141, 5705, 10269, 17115, 51345]⟩]),
  (53, [⟨1, 1, [5, 15, 45, 53, 163, 1141, 3423, 10269, 17115, 51345]⟩]),
  (59, [⟨1, 1, [9, 45, 59, 163, 2445, 10269, 17115, 51345]⟩]),
  (61, [⟨1, 1, [3, 9, 45, 489, 1467, 10269, 17115, 51345]⟩]),
  (67, [⟨1, 1, [7, 45, 163, 1141, 1467, 7335, 17115, 51345]⟩]),
  (71, [⟨1, 1, [1, 3, 7, 21, 71, 163, 1141, 7335, 17115, 51345]⟩]),
  (73, [⟨1, 1, [3, 9, 35, 163, 489, 7335, 17115, 51345]⟩]),
  (79, [⟨1, 1, [7, 35, 163, 5705, 17115, 51345]⟩]),
  (83, [⟨1, 1, [1, 9, 83, 163, 815, 3423, 17115, 51345]⟩]),
  (89, [⟨1, 1, [1, 3, 21, 63, 815, 1467, 17115, 51345]⟩]),
  (97, [⟨1, 1, [1, 5, 21, 163, 489, 5705, 10269, 51345]⟩]),
  (101, [⟨1, 1, [15, 63, 1467, 3423, 10269, 51345]⟩]),
  (103, [⟨1, 1, [1, 21, 815, 3423, 10269, 51345]⟩]),
  (107, [⟨1, 1, [1, 9, 63, 163, 1141, 1467, 10269, 51345]⟩]),
  (109, [⟨1, 1, [1, 7, 9, 163, 489, 1467, 10269, 51345]⟩]),
  (113, [⟨1, 1, [5, 63, 163, 489, 10269, 51345]⟩]),
  (127, [⟨1, 1, [3, 35, 127, 163, 5705, 51345]⟩]),
  (131, [⟨1, 1, [1, 7, 45, 1141, 3423, 51345]⟩]),
  (137, [⟨1, 1, [3, 45, 2445, 51345]⟩]),
  (139, [⟨1, 1, [1, 15, 139, 163, 1467, 51345]⟩]),
  (149, [⟨1, 1, [3, 35, 163, 489, 1141, 1467, 2445, 3423, 5705, 7335, 10269, 17115]⟩]),
  (151, [⟨1, 1, [5, 35, 105, 163, 815, 1467, 2445, 3423, 5705, 7335, 10269, 17115]⟩]),
  (157, [⟨1, 1, [35, 105, 163, 1141, 1467, 3423, 5705, 7335, 10269, 17115]⟩]),
  (167, [⟨1, 1, [1, 5, 21, 105, 167, 1503, 5845, 7515, 10521, 17535]⟩]),
  (173, [⟨1, 1, [9, 21, 63, 519, 3633, 7785, 10899, 18165]⟩]),
  (179, [⟨1, 1, [1, 21, 105, 179, 537, 8055, 11277, 18795]⟩]),
  (181, [⟨1, 1, [1, 7, 63, 181, 1267, 6335, 11403, 19005]⟩]),
  (191, [⟨1, 1, [1, 45, 105, 191, 573, 1719, 12033, 20055]⟩]),
  (193, [⟨1, 1, [1, 45, 193, 1351, 12159, 20265]⟩]),
  (197, [⟨1, 1, [9, 21, 63, 2955, 8865, 20685]⟩]),
  (199, [⟨1, 1, [5, 45, 199, 1791, 8955, 20895]⟩]),
  (211, [⟨1, 1, [1, 1055, 4431, 22155]⟩]),
  (223, [⟨1, 1, [1, 3, 35, 163, 223, 1115, 7805, 14049]⟩]),
  (227, [⟨1, 1, [1, 7, 15, 163, 681, 2043, 4767, 14301]⟩]),
  (229, [⟨1, 1, [1, 3, 35, 163, 229, 1603, 4809, 14427]⟩]),
  (233, [⟨1, 1, [1, 3, 45, 233, 4893, 14679]⟩]),
  (239, [⟨1, 1, [9, 35, 239, 717, 1673, 15057]⟩]),
  (241, [⟨1, 1, [3, 9, 35, 105, 1687, 15183]⟩]),
  (251, [⟨1, 1, [1, 15, 163, 251, 1757, 11295]⟩]),
  (257, [⟨1, 1, [5, 45, 2313, 8995]⟩]),
  (263, [⟨1, 1, [1, 7, 21, 9205]⟩]),
  (269, [⟨1, 1, [1, 3, 7, 105, 1345, 5649]⟩]),
  (271, [⟨1, 1, [1, 5, 163, 271, 1897, 4065]⟩]),
  (277, [⟨1, 1, [3, 15, 105, 4155]⟩]),
  (281, [⟨1, 1, [7, 45, 281, 2529]⟩]),
  (283, [⟨1, 1, [1, 9, 163, 1981]⟩]),
  (293, [⟨2, 2, [3, 9, 105, 293, 2051, 4395, 26569, 85849, 257547, 3863205]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified163 : verifyBatch 163 qPrimes rows163 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows167 : List Row := [
  (11, [⟨1, 1, [1, 7, 33, 99, 501, 2505, 3507, 5845, 7515, 10521, 17535, 52605]⟩]),
  (13, [⟨1, 1, [13, 39, 835, 1503, 3507, 5845, 7515, 10521, 17535, 52605]⟩]),
  (17, [⟨1, 1, [5, 17, 21, 835, 3507, 5845, 7515, 10521, 17535, 52605]⟩]),
  (19, [⟨1, 1, [1, 7, 19, 95, 3507, 5845, 7515, 10521, 17535, 52605]⟩]),
  (23, [⟨1, 1, [21, 23, 69, 501, 1503, 5845, 7515, 10521, 17535, 52605]⟩]),
  (29, [⟨1, 1, [1, 15, 167, 501, 1503, 3507, 7515, 10521, 17535, 52605]⟩]),
  (31, [⟨1, 1, [1, 31, 63, 167, 1169, 3507, 7515, 10521, 17535, 52605]⟩]),
  (37, [⟨1, 1, [1, 7, 9, 37, 111, 2505, 7515, 10521, 17535, 52605]⟩]),
  (41, [⟨1, 1, [3, 9, 21, 123, 167, 835, 7515, 10521, 17535, 52605]⟩]),
  (43, [⟨1, 1, [1, 3, 21, 43, 501, 1503, 5845, 10521, 17535, 52605]⟩]),
  (47, [⟨1, 1, [3, 9, 47, 501, 5845, 10521, 17535, 52605]⟩]),
  (53, [⟨1, 1, [1, 3, 9, 53, 63, 501, 3507, 10521, 17535, 52605]⟩]),
  (59, [⟨1, 1, [1, 3, 7, 21, 167, 501, 1169, 10521, 17535, 52605]⟩]),
  (61, [⟨1, 1, [5, 45, 61, 167, 835, 10521, 17535, 52605]⟩]),
  (67, [⟨1, 1, [5, 9, 167, 501, 1169, 7515, 17535, 52605]⟩]),
  (71, [⟨1, 1, [5, 501, 1503, 5845, 17535, 52605]⟩]),
  (73, [⟨1, 1, [1, 3, 7, 73, 1169, 5845, 17535, 52605]⟩]),
  (79, [⟨1, 1, [3, 9, 63, 79, 1169, 3507, 17535, 52605]⟩]),
  (83, [⟨1, 1, [1, 7, 9, 45, 83, 167, 501, 2505, 17535, 52605]⟩]),
  (89, [⟨1, 1, [3, 45, 167, 835, 17535, 52605]⟩]),
  (97, [⟨1, 1, [9, 21, 1503, 3507, 10521, 52605]⟩]),
  (101, [⟨1, 1, [21, 3507, 10521, 52605]⟩]),
  (103, [⟨1, 1, [1, 15, 21, 63, 167, 2505, 10521, 52605]⟩]),
  (107, [⟨1, 1, [7, 21, 63, 1169, 10521, 52605]⟩]),
  (109, [⟨1, 1, [3, 501, 10521, 52605]⟩]),
  (113, [⟨1, 1, [3, 45, 113, 167, 501, 1169, 7515, 52605]⟩]),
  (127, [⟨1, 1, [1, 45, 167, 501, 3507, 52605]⟩]),
  (131, [⟨1, 1, [1, 15, 21, 167, 2505, 52605]⟩]),
  (137, [⟨1, 1, [1, 3, 7, 21, 105, 137, 167, 52605]⟩]),
  (139, [⟨1, 1, [5, 21, 105, 139, 167, 417, 501, 835, 1169, 1503, 2505, 3507, 5845, 7515, 10521, 17535]⟩]),
  (149, [⟨1, 1, [1, 7, 9, 63, 167, 835, 2505, 3507, 5845, 7515, 10521, 17535]⟩]),
  (151, [⟨1, 1, [1, 7, 151, 167, 2505, 3507, 5845, 7515, 10521, 17535]⟩]),
  (157, [⟨1, 1, [1, 7, 9, 45, 501, 3507, 5845, 7515, 10521, 17535]⟩]),
  (163, [⟨1, 1, [1, 5, 21, 105, 167, 1503, 5845, 7515, 10521, 17535]⟩]),
  (173, [⟨1, 1, [167, 865, 1557, 7785, 10899, 18165]⟩]),
  (179, [⟨1, 1, [3, 9, 105, 179, 537, 6265, 11277, 18795]⟩]),
  (181, [⟨1, 1, [3, 9, 21, 543, 1629, 3801, 11403, 19005]⟩]),
  (191, [⟨1, 1, [5, 9, 45, 105, 955, 2865, 8595, 20055]⟩]),
  (193, [⟨1, 1, [3, 9, 21, 2895, 8685, 20265]⟩]),
  (197, [⟨1, 1, [7, 21, 197, 591, 8865, 20685]⟩]),
  (199, [⟨1, 1, [1, 7, 45, 105, 199, 1393, 6965, 20895]⟩]),
  (211, [⟨1, 1, [9, 167, 211, 633, 1899, 22155]⟩]),
  (223, [⟨1, 1, [1, 21, 223, 1561, 4683, 14049]⟩]),
  (227, [⟨1, 1, [3, 15, 167, 1135, 3405, 14301]⟩]),
  (229, [⟨1, 1, [3, 9, 167, 229, 3435, 14427]⟩]),
  (233, [⟨1, 1, [3, 45, 167, 233, 1631, 14679]⟩]),
  (239, [⟨1, 1, [45, 105, 3585, 10755]⟩]),
  (241, [⟨1, 1, [1, 7, 63, 167, 241, 723, 1687, 10845]⟩]),
  (251, [⟨1, 1, [15, 45, 105, 251, 753, 8785]⟩]),
  (257, [⟨1, 1, [3, 63, 167, 257, 1799, 5397]⟩]),
  (263, [⟨1, 1, [1, 7, 45, 105, 1315, 3945]⟩]),
  (269, [⟨1, 1, [3, 21, 167, 269, 807, 1883]⟩]),
  (271, [⟨1, 1, [5, 9, 45, 167, 271, 1897]⟩]),
  (277, [⟨1, 1, [21, 105]⟩]),
  (281, [⟨2, 2, [1, 3, 35, 105, 843, 17703, 236883, 1658181]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified167 : verifyBatch 167 qPrimes rows167 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows173 : List Row := [
  (11, [⟨1, 1, [5, 11, 33, 173, 1211, 1557, 3633, 6055, 7785, 10899, 18165, 54495]⟩]),
  (13, [⟨1, 1, [1, 7, 13, 65, 519, 1557, 3633, 6055, 7785, 10899, 18165, 54495]⟩]),
  (17, [⟨1, 1, [7, 153, 173, 1211, 2595, 6055, 7785, 10899, 18165, 54495]⟩]),
  (19, [⟨1, 1, [5, 19, 173, 519, 2595, 6055, 7785, 10899, 18165, 54495]⟩]),
  (23, [⟨1, 1, [1, 5, 23, 69, 1557, 6055, 7785, 10899, 18165, 54495]⟩]),
  (29, [⟨1, 1, [7, 29, 1557, 3633, 7785, 10899, 18165, 54495]⟩]),
  (31, [⟨1, 1, [7, 31, 35, 173, 519, 3633, 7785, 10899, 18165, 54495]⟩]),
  (37, [⟨1, 1, [1, 3, 7, 173, 519, 1211, 7785, 10899, 18165, 54495]⟩]),
  (41, [⟨1, 1, [9, 35, 41, 173, 7785, 10899, 18165, 54495]⟩]),
  (43, [⟨1, 1, [1, 15, 43, 63, 173, 865, 6055, 10899, 18165, 54495]⟩]),
  (47, [⟨1, 1, [1, 7, 15, 173, 519, 1211, 3633, 10899, 18165, 54495]⟩]),
  (53, [⟨1, 1, [3, 15, 53, 63, 173, 1211, 1557, 10899, 18165, 54495]⟩]),
  (59, [⟨1, 1, [1, 3, 9, 59, 519, 10899, 18165, 54495]⟩]),
  (61, [⟨1, 1, [3, 45, 61, 173, 2595, 7785, 18165, 54495]⟩]),
  (67, [⟨1, 1, [3, 9, 35, 519, 1557, 6055, 18165, 54495]⟩]),
  (71, [⟨1, 1, [5, 45, 71, 173, 2595, 3633, 18165, 54495]⟩]),
  (73, [⟨1, 1, [1, 21, 63, 73, 173, 519, 1211, 3633, 18165, 54495]⟩]),
  (79, [⟨1, 1, [1, 7, 9, 79, 519, 2595, 18165, 54495]⟩]),
  (83, [⟨1, 1, [3, 21, 63, 83, 173, 1211, 18165, 54495]⟩]),
  (89, [⟨1, 1, [1, 3, 15, 89, 173, 6055, 10899, 54495]⟩]),
  (97, [⟨1, 1, [5, 15, 63, 173, 1211, 1557, 10899, 54495]⟩]),
  (101, [⟨1, 1, [1, 3, 7, 45, 101, 1211, 10899, 54495]⟩]),
  (103, [⟨1, 1, [21, 519, 10899, 54495]⟩]),
  (107, [⟨1, 1, [1, 3, 7, 21, 63, 173, 519, 1211, 7785, 54495]⟩]),
  (109, [⟨1, 1, [1, 7, 15, 109, 173, 865, 7785, 54495]⟩]),
  (113, [⟨1, 1, [3, 9, 21, 1211, 6055, 54495]⟩]),
  (127, [⟨1, 1, [5, 9, 105, 173, 1211, 54495]⟩]),
  (131, [⟨1, 1, [1, 35, 63, 131, 173, 519, 655, 865, 1211, 1557, 2595, 3633, 6055, 7785, 10899, 18165]⟩]),
  (137, [⟨1, 1, [5, 21, 105, 173, 865, 1557, 2595, 3633, 6055, 7785, 10899, 18165]⟩]),
  (139, [⟨1, 1, [1, 7, 21, 139, 173, 1557, 2595, 3633, 6055, 7785, 10899, 18165]⟩]),
  (149, [⟨1, 1, [7, 173, 1211, 2595, 6055, 7785, 10899, 18165]⟩]),
  (151, [⟨1, 1, [9, 35, 519, 2595, 6055, 7785, 10899, 18165]⟩]),
  (157, [⟨1, 1, [5, 45, 105, 519, 6055, 7785, 10899, 18165]⟩]),
  (163, [⟨1, 1, [9, 21, 63, 519, 3633, 7785, 10899, 18165]⟩]),
  (167, [⟨1, 1, [167, 865, 1557, 7785, 10899, 18165]⟩]),
  (179, [⟨1, 1, [1, 3, 35, 63, 537, 3759, 11277, 18795]⟩]),
  (181, [⟨1, 1, [7, 45, 105, 181, 1267, 1629, 11403, 19005]⟩]),
  (191, [⟨1, 1, [1, 3, 21, 63, 191, 573, 8595, 20055]⟩]),
  (193, [⟨1, 1, [5, 105, 193, 1351, 6755, 20265]⟩]),
  (197, [⟨1, 1, [1, 7, 21, 197, 591, 1379, 4137, 20685]⟩]),
  (199, [⟨1, 1, [1, 15, 105, 995, 4179, 20895]⟩]),
  (211, [⟨1, 1, [1, 7, 9, 105, 211, 3165, 4431, 13293]⟩]),
  (223, [⟨1, 1, [1, 3, 21, 173, 2007, 14049]⟩]),
  (227, [⟨1, 1, [7, 63, 227, 14301]⟩]),
  (229, [⟨1, 1, [9, 21, 3435, 10305]⟩]),
  (233, [⟨1, 1, [1, 3, 9, 45, 173, 233, 1165, 10485]⟩]),
  (239, [⟨1, 1, [7, 63, 1195, 8365]⟩]),
  (241, [⟨1, 1, [21, 105, 241, 8435]⟩]),
  (251, [⟨1, 1, [1, 3, 35, 105, 753, 3765]⟩]),
  (257, [⟨1, 1, [1, 7, 9, 105, 257, 1799]⟩]),
  (263, [⟨1, 2, [3, 9, 35, 173, 263, 27615]⟩, ⟨2, 1, [1, 3, 9, 63, 789, 2367, 5523, 27615, 29929, 45499]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified173 : verifyBatch 173 qPrimes rows173 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows179 : List Row := [
  (11, [⟨1, 1, [1, 5, 11, 33, 99, 2685, 3759, 6265, 8055, 11277, 18795, 56385]⟩]),
  (13, [⟨1, 1, [1, 13, 39, 91, 179, 1611, 3759, 6265, 8055, 11277, 18795, 56385]⟩]),
  (17, [⟨1, 1, [15, 119, 3759, 6265, 8055, 11277, 18795, 56385]⟩]),
  (19, [⟨1, 1, [15, 19, 95, 179, 2685, 6265, 8055, 11277, 18795, 56385]⟩]),
  (23, [⟨1, 1, [1, 3, 115, 179, 895, 6265, 8055, 11277, 18795, 56385]⟩]),
  (29, [⟨1, 1, [1, 7, 9, 87, 895, 3759, 8055, 11277, 18795, 56385]⟩]),
  (31, [⟨1, 1, [1, 5, 93, 3759, 8055, 11277, 18795, 56385]⟩]),
  (37, [⟨1, 1, [3, 9, 35, 37, 179, 895, 8055, 11277, 18795, 56385]⟩]),
  (41, [⟨1, 1, [3, 9, 21, 41, 179, 895, 6265, 11277, 18795, 56385]⟩]),
  (43, [⟨1, 1, [5, 21, 43, 179, 6265, 11277, 18795, 56385]⟩]),
  (47, [⟨1, 1, [3, 9, 47, 895, 3759, 11277, 18795, 56385]⟩]),
  (53, [⟨1, 1, [9, 35, 179, 537, 1253, 11277, 18795, 56385]⟩]),
  (59, [⟨1, 1, [1, 7, 21, 895, 1611, 8055, 18795, 56385]⟩]),
  (61, [⟨1, 1, [3, 21, 1611, 8055, 18795, 56385]⟩]),
  (67, [⟨1, 1, [9, 179, 537, 6265, 18795, 56385]⟩]),
  (71, [⟨1, 1, [9, 35, 63, 71, 1253, 3759, 18795, 56385]⟩]),
  (73, [⟨1, 1, [1, 15, 21, 63, 73, 179, 1253, 2685, 18795, 56385]⟩]),
  (79, [⟨1, 1, [1, 15, 63, 79, 179, 1253, 18795, 56385]⟩]),
  (83, [⟨1, 1, [5, 15, 45, 83, 895, 6265, 11277, 56385]⟩]),
  (89, [⟨1, 1, [9, 35, 89, 179, 537, 3759, 11277, 56385]⟩]),
  (97, [⟨1, 1, [1, 15, 97, 895, 11277, 56385]⟩]),
  (101, [⟨1, 1, [5, 35, 63, 179, 537, 1611, 8055, 56385]⟩]),
  (103, [⟨1, 1, [35, 63, 179, 1253, 8055, 56385]⟩]),
  (107, [⟨1, 1, [1, 3, 21, 63, 179, 1253, 6265, 56385]⟩]),
  (109, [⟨1, 1, [5, 15, 63, 537, 6265, 56385]⟩]),
  (113, [⟨1, 1, [1, 9, 63, 1253, 3759, 56385]⟩]),
  (127, [⟨1, 1, [3, 35, 537, 895, 1253, 1611, 2685, 3759, 6265, 8055, 11277, 18795]⟩]),
  (131, [⟨1, 1, [7, 21, 895, 1611, 2685, 3759, 6265, 8055, 11277, 18795]⟩]),
  (137, [⟨1, 1, [1, 3, 9, 895, 1611, 3759, 6265, 8055, 11277, 18795]⟩]),
  (139, [⟨1, 1, [1, 7, 1611, 3759, 6265, 8055, 11277, 18795]⟩]),
  (149, [⟨1, 1, [1, 3, 9, 149, 179, 537, 6265, 8055, 11277, 18795]⟩]),
  (151, [⟨1, 1, [1, 5, 151, 179, 537, 1611, 3759, 8055, 11277, 18795]⟩]),
  (157, [⟨1, 1, [1, 15, 21, 105, 179, 537, 2685, 8055, 11277, 18795]⟩]),
  (163, [⟨1, 1, [1, 21, 105, 179, 537, 8055, 11277, 18795]⟩]),
  (167, [⟨1, 1, [3, 9, 105, 179, 537, 6265, 11277, 18795]⟩]),
  (173, [⟨1, 1, [1, 3, 35, 63, 537, 3759, 11277, 18795]⟩]),
  (181, [⟨1, 1, [1, 15, 21, 63, 905, 2715, 8145, 19005]⟩]),
  (191, [⟨1, 1, [3, 9, 573, 1719, 4011, 20055]⟩]),
  (193, [⟨1, 1, [1, 7, 179, 965, 4053, 20265]⟩]),
  (197, [⟨1, 1, [9, 21, 2955, 20685]⟩]),
  (199, [⟨1, 1, [21, 63, 1791, 20895]⟩]),
  (211, [⟨1, 1, [5, 63, 211, 633, 3165, 13293]⟩]),
  (223, [⟨1, 1, [1, 45, 105, 223, 1561, 10035]⟩]),
  (227, [⟨1, 1, [3, 179, 2043, 7945]⟩]),
  (229, [⟨1, 1, [5, 105, 1145, 8015]⟩]),
  (233, [⟨1, 1, [5, 9, 233, 699, 1631, 4893]⟩]),
  (239, [⟨1, 1, [5, 45, 179, 239, 717, 3585]⟩]),
  (241, [⟨1, 1, [5, 9, 241, 3615]⟩]),
  (251, [⟨2, 1, [3, 9, 21, 105, 251, 753, 11295, 32041]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified179 : verifyBatch 179 qPrimes rows179 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows181 : List Row := [
  (11, [⟨1, 1, [1, 11, 55, 2715, 3801, 6335, 8145, 11403, 19005, 57015]⟩]),
  (13, [⟨1, 1, [9, 39, 181, 1629, 3801, 6335, 8145, 11403, 19005, 57015]⟩]),
  (17, [⟨1, 1, [1, 9, 3801, 6335, 8145, 11403, 19005, 57015]⟩]),
  (19, [⟨1, 1, [1, 171, 2715, 6335, 8145, 11403, 19005, 57015]⟩]),
  (23, [⟨1, 1, [1, 3, 15, 115, 905, 6335, 8145, 11403, 19005, 57015]⟩]),
  (29, [⟨1, 1, [3, 29, 45, 181, 543, 3801, 8145, 11403, 19005, 57015]⟩]),
  (31, [⟨1, 1, [1, 5, 21, 31, 905, 2715, 8145, 11403, 19005, 57015]⟩]),
  (37, [⟨1, 1, [1, 905, 8145, 11403, 19005, 57015]⟩]),
  (41, [⟨1, 1, [21, 123, 181, 543, 6335, 11403, 19005, 57015]⟩]),
  (43, [⟨1, 1, [1, 3, 15, 43, 63, 181, 543, 1629, 3801, 11403, 19005, 57015]⟩]),
  (47, [⟨1, 1, [5, 35, 47, 543, 3801, 11403, 19005, 57015]⟩]),
  (53, [⟨1, 1, [9, 21, 1629, 11403, 19005, 57015]⟩]),
  (59, [⟨1, 1, [1, 3, 7, 21, 59, 63, 181, 543, 1267, 8145, 19005, 57015]⟩]),
  (61, [⟨1, 1, [1, 3, 7, 61, 63, 181, 905, 8145, 19005, 57015]⟩]),
  (67, [⟨1, 1, [1, 3, 7, 67, 181, 6335, 19005, 57015]⟩]),
  (71, [⟨1, 1, [5, 35, 905, 3801, 19005, 57015]⟩]),
  (73, [⟨1, 1, [21, 3801, 19005, 57015]⟩]),
  (79, [⟨1, 1, [3, 63, 79, 905, 19005, 57015]⟩]),
  (83, [⟨1, 1, [3, 21, 83, 181, 2715, 3801, 11403, 57015]⟩]),
  (89, [⟨1, 1, [5, 45, 181, 3801, 11403, 57015]⟩]),
  (97, [⟨1, 1, [1, 3, 9, 45, 97, 181, 11403, 57015]⟩]),
  (101, [⟨1, 1, [1, 15, 101, 1629, 8145, 57015]⟩]),
  (103, [⟨1, 1, [35, 63, 181, 543, 8145, 57015]⟩]),
  (107, [⟨1, 1, [15, 45, 181, 543, 6335, 57015]⟩]),
  (109, [⟨1, 1, [1, 5, 35, 181, 543, 1629, 3801, 57015]⟩]),
  (113, [⟨1, 1, [3, 543, 3801, 57015]⟩]),
  (127, [⟨1, 1, [1, 5, 45, 543, 1267, 1629, 2715, 3801, 6335, 8145, 11403, 19005]⟩]),
  (131, [⟨1, 1, [1, 3, 9, 1629, 2715, 3801, 6335, 8145, 11403, 19005]⟩]),
  (137, [⟨1, 1, [137, 181, 1267, 3801, 6335, 8145, 11403, 19005]⟩]),
  (139, [⟨1, 1, [1, 3, 9, 105, 543, 3801, 6335, 8145, 11403, 19005]⟩]),
  (149, [⟨1, 1, [1, 7, 15, 181, 543, 1629, 3801, 8145, 11403, 19005]⟩]),
  (151, [⟨1, 1, [1, 3, 181, 1267, 3801, 8145, 11403, 19005]⟩]),
  (157, [⟨1, 1, [1, 7, 15, 105, 181, 543, 1629, 8145, 11403, 19005]⟩]),
  (163, [⟨1, 1, [1, 7, 63, 181, 1267, 6335, 11403, 19005]⟩]),
  (167, [⟨1, 1, [3, 9, 21, 543, 1629, 3801, 11403, 19005]⟩]),
  (173, [⟨1, 1, [7, 45, 105, 181, 1267, 1629, 11403, 19005]⟩]),
  (179, [⟨1, 1, [1, 15, 21, 63, 905, 2715, 8145, 19005]⟩]),
  (191, [⟨1, 1, [9, 105, 191, 955, 4011, 20055]⟩]),
  (193, [⟨1, 1, [21, 63, 4053, 20265]⟩]),
  (197, [⟨1, 1, [3, 9, 21, 63, 1773, 20685]⟩]),
  (199, [⟨1, 1, [3, 9, 21, 105, 597, 20895]⟩]),
  (211, [⟨1, 1, [5, 45, 211, 633, 1899, 13293]⟩]),
  (223, [⟨1, 1, [1, 15, 45, 669, 2007, 7805]⟩]),
  (227, [⟨1, 1, [5, 63, 681, 7945]⟩]),
  (229, [⟨1, 1, [1, 3, 7, 21, 181, 687, 2061, 4809]⟩]),
  (233, [⟨1, 1, [1, 3, 9, 21, 63, 233, 699, 4893]⟩]),
  (239, [⟨1, 1, [1, 7, 35, 239, 717, 2151]⟩]),
  (241, [⟨1, 1, [3, 9, 45, 2169]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified181 : verifyBatch 181 qPrimes rows181 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows191 : List Row := [
  (11, [⟨1, 1, [1, 5, 33, 191, 573, 1719, 4011, 6685, 8595, 12033, 20055, 60165]⟩]),
  (13, [⟨1, 1, [1, 3, 7, 13, 117, 1337, 4011, 6685, 8595, 12033, 20055, 60165]⟩]),
  (17, [⟨1, 1, [1, 153, 191, 1337, 1719, 6685, 8595, 12033, 20055, 60165]⟩]),
  (19, [⟨1, 1, [1, 7, 57, 573, 1719, 6685, 8595, 12033, 20055, 60165]⟩]),
  (23, [⟨1, 1, [9, 69, 191, 6685, 8595, 12033, 20055, 60165]⟩]),
  (29, [⟨1, 1, [1, 3, 15, 29, 145, 191, 573, 2865, 8595, 12033, 20055, 60165]⟩]),
  (31, [⟨1, 1, [1, 3, 7, 93, 955, 1719, 8595, 12033, 20055, 60165]⟩]),
  (37, [⟨1, 1, [7, 21, 191, 1337, 6685, 12033, 20055, 60165]⟩]),
  (41, [⟨1, 1, [41, 191, 573, 1337, 4011, 12033, 20055, 60165]⟩]),
  (43, [⟨1, 1, [5, 9, 129, 955, 4011, 12033, 20055, 60165]⟩]),
  (47, [⟨1, 1, [15, 141, 2865, 12033, 20055, 60165]⟩]),
  (53, [⟨1, 1, [1, 5, 21, 53, 191, 1337, 1719, 8595, 20055, 60165]⟩]),
  (59, [⟨1, 1, [1, 3, 191, 8595, 20055, 60165]⟩]),
  (61, [⟨1, 1, [45, 61, 955, 6685, 20055, 60165]⟩]),
  (67, [⟨1, 1, [9, 21, 573, 4011, 20055, 60165]⟩]),
  (71, [⟨1, 1, [1, 7, 35, 191, 573, 1719, 20055, 60165]⟩]),
  (73, [⟨1, 1, [9, 63, 73, 1337, 20055, 60165]⟩]),
  (79, [⟨1, 1, [1, 5, 63, 573, 1719, 4011, 12033, 60165]⟩]),
  (83, [⟨1, 1, [1, 3, 15, 63, 191, 4011, 12033, 60165]⟩]),
  (89, [⟨1, 1, [1, 5, 191, 955, 12033, 60165]⟩]),
  (97, [⟨1, 1, [1, 3, 7, 21, 573, 1719, 6685, 60165]⟩]),
  (101, [⟨1, 1, [45, 191, 6685, 60165]⟩]),
  (103, [⟨1, 1, [9, 35, 103, 1719, 4011, 60165]⟩]),
  (107, [⟨1, 1, [1, 7, 45, 107, 191, 573, 2865, 60165]⟩]),
  (109, [⟨1, 1, [1, 7, 63, 955, 1719, 60165]⟩]),
  (113, [⟨1, 1, [21, 63, 573, 60165]⟩]),
  (127, [⟨1, 1, [1, 3, 9, 21, 191, 573, 1337, 4011, 6685, 8595, 12033, 20055]⟩]),
  (131, [⟨1, 1, [3, 9, 35, 4011, 6685, 8595, 12033, 20055]⟩]),
  (137, [⟨1, 1, [1, 3, 21, 137, 191, 573, 6685, 8595, 12033, 20055]⟩]),
  (139, [⟨1, 1, [1, 9, 63, 191, 573, 1719, 4011, 8595, 12033, 20055]⟩]),
  (149, [⟨1, 1, [1, 9, 1337, 8595, 12033, 20055]⟩]),
  (151, [⟨1, 1, [7, 105, 191, 8595, 12033, 20055]⟩]),
  (157, [⟨1, 1, [1, 35, 1719, 4011, 12033, 20055]⟩]),
  (163, [⟨1, 1, [1, 45, 105, 191, 573, 1719, 12033, 20055]⟩]),
  (167, [⟨1, 1, [5, 9, 45, 105, 955, 2865, 8595, 20055]⟩]),
  (173, [⟨1, 1, [1, 3, 21, 63, 191, 573, 8595, 20055]⟩]),
  (179, [⟨1, 1, [3, 9, 573, 1719, 4011, 20055]⟩]),
  (181, [⟨1, 1, [9, 105, 191, 955, 4011, 20055]⟩]),
  (193, [⟨1, 1, [1, 7, 35, 105, 6755, 12159]⟩]),
  (197, [⟨1, 1, [1, 3, 7, 21, 197, 1379, 2955, 12411]⟩]),
  (199, [⟨1, 1, [1, 9, 199, 1393, 1791, 12537]⟩]),
  (211, [⟨1, 1, [3, 63, 105, 9495]⟩]),
  (223, [⟨1, 1, [3, 9, 45, 3345]⟩]),
  (227, [⟨1, 1, [1, 3, 7, 63, 105, 1135]⟩]),
  (229, [⟨1, 1, [1, 5, 35, 229]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified191 : verifyBatch 191 qPrimes rows191 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows193 : List Row := [
  (11, [⟨1, 1, [55, 99, 579, 1737, 4053, 6755, 8685, 12159, 20265, 60795]⟩]),
  (13, [⟨1, 1, [3, 9, 39, 1351, 4053, 6755, 8685, 12159, 20265, 60795]⟩]),
  (17, [⟨1, 1, [17, 21, 193, 1351, 1737, 6755, 8685, 12159, 20265, 60795]⟩]),
  (19, [⟨1, 1, [5, 9, 19, 95, 193, 579, 1351, 6755, 8685, 12159, 20265, 60795]⟩]),
  (23, [⟨1, 1, [115, 6755, 8685, 12159, 20265, 60795]⟩]),
  (29, [⟨1, 1, [3, 15, 29, 145, 579, 2895, 8685, 12159, 20265, 60795]⟩]),
  (31, [⟨1, 1, [1, 3, 9, 31, 45, 193, 579, 1737, 8685, 12159, 20265, 60795]⟩]),
  (37, [⟨1, 1, [3, 15, 37, 111, 193, 965, 6755, 12159, 20265, 60795]⟩]),
  (41, [⟨1, 1, [9, 21, 123, 1737, 4053, 12159, 20265, 60795]⟩]),
  (43, [⟨1, 1, [7, 43, 193, 579, 4053, 12159, 20265, 60795]⟩]),
  (47, [⟨1, 1, [1, 15, 21, 965, 1737, 12159, 20265, 60795]⟩]),
  (53, [⟨1, 1, [1, 15, 45, 53, 2895, 8685, 20265, 60795]⟩]),
  (59, [⟨1, 1, [5, 9, 177, 193, 1351, 6755, 20265, 60795]⟩]),
  (61, [⟨1, 1, [1, 5, 21, 61, 579, 6755, 20265, 60795]⟩]),
  (67, [⟨1, 1, [35, 63, 67, 4053, 20265, 60795]⟩]),
  (71, [⟨1, 1, [3, 15, 63, 71, 193, 1737, 20265, 60795]⟩]),
  (73, [⟨1, 1, [1, 3, 45, 965, 20265, 60795]⟩]),
  (79, [⟨1, 1, [3, 9, 35, 79, 1737, 4053, 12159, 60795]⟩]),
  (83, [⟨1, 1, [9, 21, 83, 193, 579, 2895, 12159, 60795]⟩]),
  (89, [⟨1, 1, [3, 35, 63, 89, 965, 2895, 8685, 60795]⟩]),
  (97, [⟨1, 1, [1, 3, 63, 97, 193, 1351, 6755, 60795]⟩]),
  (101, [⟨1, 1, [5, 45, 101, 193, 579, 1351, 4053, 60795]⟩]),
  (103, [⟨1, 1, [3, 45, 193, 965, 4053, 60795]⟩]),
  (107, [⟨1, 1, [35, 193, 2895, 60795]⟩]),
  (109, [⟨1, 1, [1, 15, 109, 193, 1737, 60795]⟩]),
  (113, [⟨1, 1, [15, 45, 193, 579, 965, 1017, 1351, 1737, 2895, 4053, 6755, 8685, 12159, 20265]⟩]),
  (127, [⟨1, 1, [1, 35, 127, 193, 965, 4053, 6755, 8685, 12159, 20265]⟩]),
  (131, [⟨1, 1, [1, 3, 15, 131, 193, 2895, 6755, 8685, 12159, 20265]⟩]),
  (137, [⟨1, 1, [1, 3, 9, 21, 6755, 8685, 12159, 20265]⟩]),
  (139, [⟨1, 1, [1, 3, 15, 105, 193, 1351, 4053, 8685, 12159, 20265]⟩]),
  (149, [⟨1, 1, [1, 3, 35, 149, 193, 8685, 12159, 20265]⟩]),
  (151, [⟨1, 1, [1, 21, 63, 193, 965, 6755, 12159, 20265]⟩]),
  (157, [⟨1, 1, [5, 157, 579, 4053, 12159, 20265]⟩]),
  (163, [⟨1, 1, [1, 45, 193, 1351, 12159, 20265]⟩]),
  (167, [⟨1, 1, [3, 9, 21, 2895, 8685, 20265]⟩]),
  (173, [⟨1, 1, [5, 105, 193, 1351, 6755, 20265]⟩]),
  (179, [⟨1, 1, [1, 7, 179, 965, 4053, 20265]⟩]),
  (181, [⟨1, 1, [21, 63, 4053, 20265]⟩]),
  (191, [⟨1, 1, [1, 7, 35, 105, 6755, 12159]⟩]),
  (197, [⟨1, 1, [35, 63, 197, 1379, 1773, 12411]⟩]),
  (199, [⟨1, 1, [1, 63, 199, 597, 1393, 12537]⟩]),
  (211, [⟨1, 1, [3, 45, 105, 211, 633, 7385]⟩]),
  (223, [⟨1, 1, [1, 21, 63, 105, 223, 1561]⟩]),
  (227, [⟨1, 2, [5, 15, 45, 227, 681, 7945, 23835, 51529]⟩, ⟨2, 1, [1, 15, 193, 1135, 4767, 23835, 37249, 43811]⟩]),
  (229, [⟨2, 2, [5, 15, 687, 8015, 24045, 1835435]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified193 : verifyBatch 193 qPrimes rows193 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows197 : List Row := [
  (11, [⟨1, 1, [1, 33, 165, 197, 591, 1379, 4137, 6895, 8865, 12411, 20685, 62055]⟩]),
  (13, [⟨1, 1, [3, 65, 197, 985, 4137, 6895, 8865, 12411, 20685, 62055]⟩]),
  (17, [⟨1, 1, [3, 197, 2955, 6895, 8865, 12411, 20685, 62055]⟩]),
  (19, [⟨1, 1, [3, 9, 57, 197, 1773, 6895, 8865, 12411, 20685, 62055]⟩]),
  (23, [⟨1, 1, [1, 3, 197, 591, 1773, 4137, 8865, 12411, 20685, 62055]⟩]),
  (29, [⟨1, 1, [5, 197, 1379, 1773, 8865, 12411, 20685, 62055]⟩]),
  (31, [⟨1, 1, [5, 31, 35, 197, 591, 1379, 8865, 12411, 20685, 62055]⟩]),
  (37, [⟨1, 1, [35, 37, 197, 591, 6895, 12411, 20685, 62055]⟩]),
  (41, [⟨1, 1, [7, 1379, 4137, 12411, 20685, 62055]⟩]),
  (43, [⟨1, 1, [9, 21, 43, 197, 4137, 12411, 20685, 62055]⟩]),
  (47, [⟨1, 1, [1, 7, 197, 591, 1379, 12411, 20685, 62055]⟩]),
  (53, [⟨1, 1, [9, 591, 1773, 8865, 20685, 62055]⟩]),
  (59, [⟨1, 1, [1, 9, 985, 6895, 20685, 62055]⟩]),
  (61, [⟨1, 1, [15, 61, 197, 591, 1773, 4137, 20685, 62055]⟩]),
  (67, [⟨1, 1, [1, 9, 67, 197, 1379, 1773, 20685, 62055]⟩]),
  (71, [⟨1, 1, [3, 9, 197, 985, 20685, 62055]⟩]),
  (73, [⟨1, 1, [5, 73, 20685, 62055]⟩]),
  (79, [⟨1, 1, [79, 197, 591, 4137, 12411, 62055]⟩]),
  (83, [⟨1, 1, [5, 9, 985, 1773, 12411, 62055]⟩]),
  (89, [⟨1, 1, [15, 2955, 8865, 62055]⟩]),
  (97, [⟨1, 1, [1, 3, 15, 63, 197, 2955, 4137, 62055]⟩]),
  (101, [⟨1, 1, [1, 7, 9, 985, 4137, 62055]⟩]),
  (103, [⟨1, 1, [5, 15, 63, 985, 2955, 62055]⟩]),
  (107, [⟨1, 1, [3, 15, 1773, 62055]⟩]),
  (109, [⟨1, 1, [21, 63, 591, 62055]⟩]),
  (113, [⟨1, 1, [5, 35, 63, 113, 197, 985, 1379, 1773, 2955, 4137, 6895, 8865, 12411, 20685]⟩]),
  (127, [⟨1, 1, [3, 21, 63, 197, 591, 2955, 6895, 8865, 12411, 20685]⟩]),
  (131, [⟨1, 1, [1, 21, 197, 1379, 6895, 8865, 12411, 20685]⟩]),
  (137, [⟨1, 1, [1, 7, 15, 985, 4137, 8865, 12411, 20685]⟩]),
  (139, [⟨1, 1, [5, 21, 63, 985, 2955, 8865, 12411, 20685]⟩]),
  (149, [⟨1, 1, [1, 3, 21, 197, 2955, 4137, 12411, 20685]⟩]),
  (151, [⟨1, 1, [7, 21, 63, 197, 1773, 4137, 12411, 20685]⟩]),
  (157, [⟨1, 1, [1, 7, 21, 63, 985, 1773, 12411, 20685]⟩]),
  (163, [⟨1, 1, [9, 21, 63, 2955, 8865, 20685]⟩]),
  (167, [⟨1, 1, [7, 21, 197, 591, 8865, 20685]⟩]),
  (173, [⟨1, 1, [1, 7, 21, 197, 591, 1379, 4137, 20685]⟩]),
  (179, [⟨1, 1, [9, 21, 2955, 20685]⟩]),
  (181, [⟨1, 1, [3, 9, 21, 63, 1773, 20685]⟩]),
  (191, [⟨1, 1, [1, 3, 7, 21, 197, 1379, 2955, 12411]⟩]),
  (193, [⟨1, 1, [35, 63, 197, 1379, 1773, 12411]⟩]),
  (199, [⟨1, 1, [1, 3, 63, 105, 199, 1393, 1791, 8955]⟩]),
  (211, [⟨1, 1, [3, 9, 105, 211, 1055, 4431]⟩]),
  (223, [⟨2, 2, [1, 35, 105, 1115, 3345, 1740515, 5221545, 9796613]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified197 : verifyBatch 197 qPrimes rows197 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
def rows199 : List Row := [
  (11, [⟨1, 1, [1, 3, 11, 33, 77, 199, 597, 1393, 4179, 6965, 8955, 12537, 20895, 62685]⟩]),
  (13, [⟨1, 1, [1, 9, 13, 39, 117, 995, 4179, 6965, 8955, 12537, 20895, 62685]⟩]),
  (17, [⟨1, 1, [3, 85, 2985, 6965, 8955, 12537, 20895, 62685]⟩]),
  (19, [⟨1, 1, [9, 133, 1791, 6965, 8955, 12537, 20895, 62685]⟩]),
  (23, [⟨1, 1, [7, 21, 23, 597, 1791, 4179, 8955, 12537, 20895, 62685]⟩]),
  (29, [⟨1, 1, [5, 9, 199, 2985, 8955, 12537, 20895, 62685]⟩]),
  (31, [⟨1, 1, [1, 15, 21, 31, 199, 1791, 8955, 12537, 20895, 62685]⟩]),
  (37, [⟨1, 1, [1, 9, 21, 597, 6965, 12537, 20895, 62685]⟩]),
  (41, [⟨1, 1, [1, 15, 123, 995, 4179, 12537, 20895, 62685]⟩]),
  (43, [⟨1, 1, [21, 43, 129, 995, 2985, 12537, 20895, 62685]⟩]),
  (47, [⟨1, 1, [1, 9, 45, 47, 1791, 12537, 20895, 62685]⟩]),
  (53, [⟨1, 1, [3, 9, 53, 199, 1791, 8955, 20895, 62685]⟩]),
  (59, [⟨1, 1, [7, 21, 597, 6965, 20895, 62685]⟩]),
  (61, [⟨1, 1, [21, 61, 199, 597, 1393, 4179, 20895, 62685]⟩]),
  (67, [⟨1, 1, [45, 2985, 20895, 62685]⟩]),
  (71, [⟨1, 1, [1, 3, 15, 63, 71, 597, 20895, 62685]⟩]),
  (73, [⟨1, 1, [1, 7, 995, 6965, 12537, 62685]⟩]),
  (79, [⟨1, 1, [7, 21, 63, 79, 199, 4179, 12537, 62685]⟩]),
  (83, [⟨1, 1, [1, 15, 63, 199, 597, 1393, 12537, 62685]⟩]),
  (89, [⟨1, 1, [7, 35, 597, 1791, 8955, 62685]⟩]),
  (97, [⟨1, 1, [5, 9, 45, 199, 597, 1791, 4179, 62685]⟩]),
  (101, [⟨1, 1, [3, 63, 101, 199, 4179, 62685]⟩]),
  (103, [⟨1, 1, [1, 21, 199, 1393, 1791, 62685]⟩]),
  (107, [⟨1, 1, [1, 7, 15, 107, 995, 62685]⟩]),
  (109, [⟨1, 1, [5, 21, 63, 109, 199, 597, 981, 995, 1393, 1791, 2985, 4179, 6965, 8955, 12537, 20895]⟩]),
  (113, [⟨1, 1, [9, 21, 63, 597, 1393, 1791, 2985, 4179, 6965, 8955, 12537, 20895]⟩]),
  (127, [⟨1, 1, [1, 9, 63, 2985, 6965, 8955, 12537, 20895]⟩]),
  (131, [⟨1, 1, [5, 45, 131, 597, 6965, 8955, 12537, 20895]⟩]),
  (137, [⟨1, 1, [7, 137, 4179, 8955, 12537, 20895]⟩]),
  (139, [⟨1, 1, [5, 9, 45, 139, 2985, 8955, 12537, 20895]⟩]),
  (149, [⟨1, 1, [7, 63, 199, 597, 1393, 4179, 12537, 20895]⟩]),
  (151, [⟨1, 1, [1, 3, 15, 105, 995, 4179, 12537, 20895]⟩]),
  (157, [⟨1, 1, [3, 21, 63, 1791, 12537, 20895]⟩]),
  (163, [⟨1, 1, [5, 45, 199, 1791, 8955, 20895]⟩]),
  (167, [⟨1, 1, [1, 7, 45, 105, 199, 1393, 6965, 20895]⟩]),
  (173, [⟨1, 1, [1, 15, 105, 995, 4179, 20895]⟩]),
  (179, [⟨1, 1, [21, 63, 1791, 20895]⟩]),
  (181, [⟨1, 1, [3, 9, 21, 105, 597, 20895]⟩]),
  (191, [⟨1, 1, [1, 9, 199, 1393, 1791, 12537]⟩]),
  (193, [⟨1, 1, [1, 63, 199, 597, 1393, 12537]⟩]),
  (197, [⟨1, 1, [1, 3, 63, 105, 199, 1393, 1791, 8955]⟩]),
  (211, [⟨1, 1, [1, 35, 63, 4431]⟩])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem verified199 : verifyBatch 199 qPrimes rows199 = true := by
  decide +kernel


set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem batch_exists {p : ℕ} (hp : p ∈ pPrimes) : ∃ rows, verifyBatch p qPrimes rows = true := by
  simp only [pPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨rows107, verified107⟩
  · exact ⟨rows109, verified109⟩
  · exact ⟨rows113, verified113⟩
  · exact ⟨rows127, verified127⟩
  · exact ⟨rows131, verified131⟩
  · exact ⟨rows137, verified137⟩
  · exact ⟨rows139, verified139⟩
  · exact ⟨rows149, verified149⟩
  · exact ⟨rows151, verified151⟩
  · exact ⟨rows157, verified157⟩
  · exact ⟨rows163, verified163⟩
  · exact ⟨rows167, verified167⟩
  · exact ⟨rows173, verified173⟩
  · exact ⟨rows179, verified179⟩
  · exact ⟨rows181, verified181⟩
  · exact ⟨rows191, verified191⟩
  · exact ⟨rows193, verified193⟩
  · exact ⟨rows197, verified197⟩
  · exact ⟨rows199, verified199⟩

end OMA.Erdos470MinimalCores

/-! Connect the checked exponent boxes and proper-divisor certificates to the target. -/

namespace OMA.Erdos470MinimalCores

private theorem coprime_base {p : ℕ} (hp : p.Prime) (hmin : 11 ≤ p) : p.Coprime 315 := by
  have h3 : p.Coprime 3 := (Nat.coprime_primes hp (by decide)).mpr (by omega)
  have h5 : p.Coprime 5 := (Nat.coprime_primes hp (by decide)).mpr (by omega)
  have h7 : p.Coprime 7 := (Nat.coprime_primes hp (by decide)).mpr (by omega)
  rw [show 315 = (3^2*5*7 : ℕ) by decide, Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
  exact ⟨⟨h3.pow_right 2, h5⟩, h7⟩

private theorem mem_cap (a : ℕ) (ha : 0 < a) : min a 3 ∈ ([1, 2, 3] : List ℕ) := by
  have hmin : 1 ≤ min a 3 := le_min ha (by decide)
  have hmax : min a 3 ≤ 3 := min_le_right _ _
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem finish_census (ps qs : List ℕ)
    (hps : ∀ p, p.Prime → 107 ≤ p → p < 210 → p ∈ ps)
    (hqs : ∀ q, q.Prime → 11 ≤ q → q < 5565 → q ∈ qs)
    (hbatch : ∀ p ∈ ps, ∃ rows, verifyBatch p qs rows = true)
    {n : ℕ} (ho : Odd n) (ha : n.Abundant) (hc : n.primeFactors.card = 5)
    (h3 : n.factorization 3 = 2) (h5 : n.factorization 5 = 1) (h7 : n.factorization 7 = 1)
    (hpExists : ∃ p : ℕ, p.Prime ∧ 107 ≤ p ∧ p < 210 ∧ p ∣ n)
    (hbound : ∀ r ∈ n.primeFactors, r < 5565) : n.Pseudoperfect := by
  obtain ⟨p, hp, hplo, hphi, hpd⟩ := hpExists
  obtain ⟨q, a, b, hq, hqlo, hqhi, hpq, ha0, hb0, hn⟩ :=
    support_shape ho ho.pos.ne' hc h3 h5 h7 hp hpd hplo hbound
  have hpMem := hps p hp hplo hphi
  have hqMem := hqs q hq hqlo hqhi
  have hp315 := coprime_base hp (by omega)
  have hq315 := coprime_base hq hqlo
  have hpqC := (Nat.coprime_primes hp hq).mpr hpq
  have hAb : (315 * p^a * q^b).Abundant := hn ▸ ha
  have hu := upperAllows_of_abundant hp hq hp315 hq315 hpqC hAb
  obtain ⟨rows, hrows⟩ := hbatch p hpMem
  obtain ⟨ws, hws⟩ := verifyBatch_sound hrows hqMem
  obtain ⟨w, _, hwA, hwB, hw⟩ := verifyPair_sound hpq (mem_cap a ha0) (mem_cap b hb0) hu hws
  have hcore := verifyWitness_sound hp hq hp315 hq315 hpqC w hw
  refine pseudoperfect_of_dvd ho.pos ?_ hcore
  rw [hn]
  exact Nat.mul_dvd_mul (Nat.mul_dvd_mul (dvd_refl 315)
    (Nat.pow_dvd_pow p (hwA.trans (min_le_left _ _))))
    (Nat.pow_dvd_pow q (hwB.trans (min_le_left _ _)))

end OMA.Erdos470MinimalCores

open OMA.Erdos470MinimalCores

theorem OMA.solution :
    OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H1_R1.H1 := by
  intro n ho ha hc h3 h5 h7 hp hbound _
  exact finish_census pPrimes qPrimes pPrimes_complete qPrimes_complete
    (fun _ hm => batch_exists hm) ho ha hc h3 h5 h7 hp hbound
