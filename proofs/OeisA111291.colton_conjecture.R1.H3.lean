import OMAReductions.R_OeisA111291_colton_conjecture_R1
import Mathlib

/-! Grouped generator bounds for the finite Colton tail.

The reciprocal estimate uses verified smooth generators and disjoint prime
extensions. A checked table of cofactor ranks bounds the excluded prime sum.
-/

-- Credit: @Genbox

/- A kernel-reducible segmented bitset sieve for exact prime counting. -/

namespace ColtonSieve

open Finset

/-- The first entries of a periodic mask have no gaps in units of its stride. -/
def pulses (step len : Nat) : Nat :=
  ((2 ^ step) ^ len - 1) / (2 ^ step - 1)

lemma pulses_succ {step : Nat} (hs : 0 < step) (len : Nat) :
    pulses step (len+1) = (pulses step len <<< step) ||| 1 := by
  have hbase : 2 ≤ (2 : Nat)^step := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (show 1 ≤ step by omega)
  unfold pulses
  rw [← Nat.geomSum_eq hbase, ← Nat.geomSum_eq hbase, geom_sum_succ]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (show 1 < (2 : Nat)^step by omega)]
  rw [Nat.shiftLeft_eq, Nat.mul_comm]

theorem pulses_bit {step : Nat} (hs : 0 < step) (len i : Nat) :
    (pulses step len).testBit i = true ↔ ∃ j < len, i = step * j := by
  induction len generalizing i with
  | zero => simp [pulses]
  | succ len ih =>
    rw [pulses_succ hs, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, ih, Nat.testBit_one_eq_true_iff_self_eq_zero]
    constructor
    · rintro (⟨hi, j, hj, h⟩ | rfl)
      · refine ⟨j+1, by omega, ?_⟩
        rw [Nat.mul_succ]
        omega
      · exact ⟨0, by omega, by simp⟩
    · rintro ⟨j, hj, h⟩
      cases j with
      | zero => exact Or.inr (by simpa using h)
      | succ j =>
        rw [Nat.mul_succ] at h
        exact Or.inl ⟨by omega, j, by omega, by omega⟩

/-- Offset from the segment start to the first multiple of p. -/
def phase (lo p : Nat) : Nat := p * ((lo+p-1)/p) - lo

lemma phase_bounds {p : Nat} (hp : 0 < p) (lo : Nat) :
    phase lo p < p ∧ p ∣ lo + phase lo p := by
  have hmod := Nat.mod_lt (lo+p-1) hp
  have hdiv := Nat.mod_add_div (lo+p-1) p
  unfold phase
  constructor
  · omega
  · refine ⟨(lo+p-1)/p, ?_⟩
    omega

lemma divides_phase {p : Nat} (hp : 0 < p) (lo i : Nat) :
    p ∣ lo+i ↔ ∃ j, i = phase lo p + p*j := by
  have ⟨hbound, q, hq⟩ := phase_bounds hp lo
  constructor
  · rintro ⟨r, hr⟩
    have hqr : q ≤ r := by
      by_contra! h
      have hm := Nat.mul_le_mul_left p (show r+1 ≤ q by omega)
      rw [Nat.mul_succ] at hm
      omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hqr
    rw [Nat.mul_add] at hr
    exact ⟨j, by omega⟩
  · rintro ⟨j, rfl⟩
    refine ⟨q+j, ?_⟩
    rw [Nat.mul_add]
    omega

/-- Bit zero describes lo. Wider bit positions reserve unused bits for digit sums. -/
def progressionMask (width lo len p : Nat) : Nat :=
  pulses (width*p) (len/p+1) <<< (width * phase lo p)

lemma progression_bit {width p : Nat} (hw : 0 < width) (hp : 0 < p)
    (lo len i : Nat) (hi : i < len) :
    (progressionMask width lo len p).testBit (width*i) = true ↔ p ∣ lo+i := by
  rw [progressionMask, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq,
    pulses_bit (Nat.mul_pos hw hp), divides_phase hp]
  constructor
  · rintro ⟨hle, j, _, he⟩
    have hle' : phase lo p ≤ i := Nat.le_of_mul_le_mul_left hle hw
    have he' : width * (i-phase lo p) = width * (p*j) := by
      simpa only [Nat.mul_sub, Nat.mul_assoc] using he
    exact ⟨j, by have := Nat.eq_of_mul_eq_mul_left hw he'; omega⟩
  · rintro ⟨j, rfl⟩
    have hj : j < len/p+1 := by
      have h : p*j ≤ len := by omega
      exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hp).mpr (by simpa [Nat.mul_comm] using h))
    refine ⟨Nat.mul_le_mul_left _ (Nat.le_add_right _ _), j, hj, ?_⟩
    simp [Nat.mul_add, Nat.mul_assoc]

private lemma pulses_lt (step len : Nat) : pulses step len < 2^(step*len) := by
  unfold pulses
  rw [Nat.pow_mul]
  have hp : 0 < (2^step : Nat)^len := by positivity
  exact (Nat.div_le_self _ _).trans_lt (by omega)

private def encoded (width len : Nat) (f : Nat → Bool) : Nat :=
  ∑ i ∈ range len, if f i then 2^(width*i) else 0

private lemma encoded_bound {width len : Nat} (hw : 0 < width) (f : Nat → Bool) :
    encoded width len f < 2^(width*len) := by
  have h2 : 2 ≤ (2 : Nat)^width := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (show 1 ≤ width by omega)
  refine lt_of_le_of_lt ?_ (pulses_lt width len)
  unfold pulses encoded
  rw [← Nat.geomSum_eq h2]
  refine sum_le_sum fun i hi => ?_
  rw [← Nat.pow_mul]
  split <;> simp

private lemma encoded_bit {width : Nat} (hw : 0 < width) (len i : Nat) (f : Nat → Bool) :
    (encoded width len f).testBit i = true ↔ ∃ j < len, i = width*j ∧ f j = true := by
  induction len generalizing i with
  | zero => simp [encoded]
  | succ len ih =>
    have hsplit : encoded width (len+1) f =
        (((f len).toNat <<< (width*len)) ||| encoded width len f) := by
      rw [← Nat.shiftLeft_add_eq_or_of_lt (encoded_bound hw f)]
      unfold encoded
      rw [sum_range_succ, Nat.add_comm]
      cases h : f len <;> simp [Nat.shiftLeft_eq]
    rw [hsplit, Nat.testBit_or, Nat.testBit_shiftLeft,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro (⟨hi,hbit⟩ | ⟨j,hj,he,hf⟩)
      · have h : f len = true := by
          cases h : f len <;> simp [h] at hbit ⊢
        have he : i = width*len := by
          rw [h] at hbit
          change (1 : Nat).testBit (i-width*len) = true at hbit
          have hz := Nat.testBit_one_eq_true_iff_self_eq_zero.mp hbit
          omega
        exact ⟨len, by omega, he, h⟩
      · exact ⟨j, by omega, he, hf⟩
    · rintro ⟨j,hj,he,hf⟩
      by_cases h : j = len
      · subst j
        rw [he, hf]
        simp
      · exact Or.inr ⟨j, by omega, he, hf⟩

private lemma encoded_mod {width len : Nat} (hw : 2 ≤ width)
    (hlen : len < 2^width-1) (f : Nat → Bool) :
    encoded width len f % (2^width-1) = ∑ i ∈ range len, (f i).toNat := by
  let b : Nat := 2^width
  have hb : 4 ≤ b := by
    simpa [b] using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hw
  have hm : b ≡ 1 [MOD b-1] := by
    have he : b-1+1 = b := by omega
    calc
      b = b-1+1 := he.symm
      _ ≡ 0+1 [MOD b-1] := (Nat.modEq_zero_iff_dvd.mpr (dvd_refl (b-1))).add_right 1
  have hrel : encoded width len f ≡ (∑ i ∈ range len, (f i).toNat) [MOD b-1] := by
    induction len with
    | zero => simp [encoded, Nat.ModEq]
    | succ len ih =>
      have hi : encoded width len f ≡ (∑ i ∈ range len, (f i).toNat) [MOD b-1] :=
        ih (by omega)
      unfold encoded at *
      rw [sum_range_succ, sum_range_succ]
      apply hi.add
      cases hf : f len
      · simp [Nat.ModEq]
      · simp only [if_true, Bool.toNat_true]
        rw [Nat.pow_mul]
        have hp := hm.pow len
        simpa [b] using hp
  have hs : (∑ i ∈ range len, (f i).toNat) ≤ len := by
    calc
      _ ≤ ∑ i ∈ range len, (1:Nat) := sum_le_sum <| fun i hi => by cases f i <;> decide
      _ = len := by simp
  unfold Nat.ModEq at hrel
  exact hrel.trans (Nat.mod_eq_of_lt (hs.trans_lt hlen))

private def eligibleDivisors : List Nat :=
  (List.range 3201).filter (fun p => decide (2 ≤ p ∧ (p ≤ 64 ∨ Nat.Coprime p (Nat.factorial 64))))

private def smallDivisors : List Nat := [
  2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
  20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37,
  38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55,
  56, 57, 58, 59, 60, 61, 62, 63, 64, 67, 71, 73, 79, 83, 89, 97, 101, 103,
  107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197,
  199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
  311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
  421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523,
  541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643,
  647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761,
  769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883,
  887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019,
  1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129,
  1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279,
  1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427,
  1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543,
  1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663,
  1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801,
  1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951,
  1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087,
  2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239,
  2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371,
  2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521,
  2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671,
  2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789,
  2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927,
  2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083,
  3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191]

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private theorem smallDivisors_eq : smallDivisors = eligibleDivisors := by decide +kernel

private lemma mem_smallDivisors {p : Nat} :
    p ∈ smallDivisors ↔ p < 3201 ∧ 2 ≤ p ∧ (p ≤ 64 ∨ Nat.Coprime p (Nat.factorial 64)) := by
  rw [smallDivisors_eq, eligibleDivisors, List.mem_filter, List.mem_range, decide_eq_true_eq]

private lemma prime_mem_smallDivisors {p : Nat} (hp : p.Prime) (hb : p < 3201) :
    p ∈ smallDivisors := by
  refine mem_smallDivisors.mpr ⟨hb,hp.two_le,?_⟩
  by_cases h : p ≤ 64
  · exact Or.inl h
  · exact Or.inr (hp.coprime_factorial_of_lt (by omega))

private def properMask (width lo len p : Nat) : Nat :=
  progressionMask width lo len p ^^^
    (if lo ≤ p ∧ p < lo+len then (1 : Nat) <<< (width*(p-lo)) else 0)

private lemma properMask_bit {width lo len p i : Nat} (hw : 0 < width) (hp : 0 < p)
    (hi : i < len) :
    (properMask width lo len p).testBit (width*i) = true ↔ p ∣ lo+i ∧ p ≠ lo+i := by
  have singleton :
      (if lo ≤ p ∧ p < lo+len then (1 : Nat) <<< (width*(p-lo)) else 0).testBit
        (width*i) = true ↔ p = lo+i := by
    split
    · next h =>
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq,
        Nat.testBit_one_eq_true_iff_self_eq_zero]
      constructor
      · rintro ⟨hle,hzero⟩
        have he : width*i = width*(p-lo) := by omega
        have hi := Nat.eq_of_mul_eq_mul_left hw he
        omega
      · intro he
        have hi : p-lo = i := by omega
        simp [hi]
    · next h =>
      simp only [Nat.zero_testBit, Bool.false_eq_true, false_iff]
      omega
  unfold properMask
  rw [Nat.testBit_xor]
  by_cases h : p = lo+i
  · have hm := (progression_bit hw hp lo len i hi).mpr (h ▸ (dvd_rfl : p ∣ p))
    rw [hm, singleton.mpr h]
    simp [h]
  · have hs : (if lo ≤ p ∧ p < lo+len then (1 : Nat) <<< (width*(p-lo)) else 0).testBit
          (width*i) = false := Bool.eq_false_iff.mpr (h ∘ singleton.mp)
    rw [hs, Bool.xor_false, progression_bit hw hp lo len i hi]
    simp [h]

private def rejectMask (width lo len : Nat) : List Nat → Nat
  | [] => 0
  | p :: ps => (properMask width lo len p) ||| rejectMask width lo len ps

private lemma rejectMask_bit {width lo len i : Nat} (hw : 0 < width) (hi : i < len)
    (ps : List Nat) (hps : ∀ p ∈ ps, 0 < p) :
    (rejectMask width lo len ps).testBit (width*i) = true ↔ ∃ p ∈ ps, p ∣ lo+i ∧ p ≠ lo+i := by
  induction ps with
  | nil => simp [rejectMask]
  | cons p ps ih =>
    rw [rejectMask, Nat.testBit_or, Bool.or_eq_true, properMask_bit hw (hps p (by simp)) hi,
      ih (fun q hq => hps q (List.mem_cons_of_mem _ hq))]
    simp only [List.mem_cons]
    constructor
    · rintro (hp | ⟨q,hq,hd⟩)
      · exact ⟨p, Or.inl rfl, hp⟩
      · exact ⟨q, Or.inr hq, hd⟩
    · rintro ⟨q,rfl | hq, hd⟩
      · exact Or.inl hd
      · exact Or.inr ⟨q,hq,hd⟩

private def intervalDivisors (limit : Nat) : List Nat :=
  smallDivisors.filter (fun p => decide (p^2 < limit))

private lemma mem_intervalDivisors {limit p : Nat} :
    p ∈ intervalDivisors limit ↔ p ∈ smallDivisors ∧ p^2 < limit := by
  rw [intervalDivisors, List.mem_filter, decide_eq_true_eq]

private lemma no_small_factor {n limit : Nat} (hlo : 2 ≤ n) (hn : n < limit) (hhi : limit ≤ 10240000) :
    (¬ ∃ p ∈ intervalDivisors limit, p ∣ n ∧ p ≠ n) ↔ n.Prime := by
  constructor
  · intro h
    by_contra hnot
    have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hs := Nat.minFac_sq_le_self (by omega : 0 < n) hnot
    have hmin : n.minFac < 3201 := by
      by_contra! h
      have := Nat.pow_le_pow_left h 2
      norm_num at this
      omega
    exact h ⟨n.minFac, mem_intervalDivisors.mpr ⟨prime_mem_smallDivisors hp hmin, hs.trans_lt hn⟩, n.minFac_dvd,
      ne_of_lt ((Nat.not_prime_iff_minFac_lt hlo).mp hnot)⟩
  · intro h hn
    obtain ⟨p, hp, hd, hne⟩ := hn
    obtain ⟨hbound,hp,_⟩ := mem_smallDivisors.mp (mem_intervalDivisors.mp hp).1
    exact hne ((Nat.dvd_prime_two_le h hp).mp hd)

private def liveMask (width lo len : Nat) : Nat :=
  let box := pulses width len
  box ^^^ (box &&& rejectMask width lo len (intervalDivisors (lo+len)))

private lemma liveMask_eq {width lo len : Nat} (hw : 0 < width)
    (hlo : 2 ≤ lo) (hhi : lo+len ≤ 10240000) :
    liveMask width lo len = encoded width len (fun i => decide ((lo+i).Prime)) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have he :
      (liveMask width lo len).testBit j = true ↔
        ∃ i < len, j = width*i ∧ (lo+i).Prime := by
    unfold liveMask
    rw [Nat.testBit_xor, Nat.testBit_and]
    cases h : (pulses width len).testBit j
    · simp only [Bool.false_and, Bool.false_xor, Bool.false_eq_true, false_iff]
      rintro ⟨i, hi, hj, _⟩
      have htrue := (pulses_bit hw len j).mpr ⟨i,hi,hj⟩
      rw [h] at htrue
      cases htrue
    · simp only [Bool.true_and, Bool.true_xor]
      obtain ⟨i,hi,rfl⟩ := (pulses_bit hw len j).mp h
      have hit := rejectMask_bit (lo := lo) hw hi (intervalDivisors (lo+len))
          (fun p hp => Nat.lt_of_lt_of_le (by decide : 0 < 2) (mem_smallDivisors.mp (mem_intervalDivisors.mp hp).1).2.1)
      have hbool :
          (!(rejectMask width lo len (intervalDivisors (lo+len))).testBit (width*i)) = true ↔
          (rejectMask width lo len (intervalDivisors (lo+len))).testBit (width*i) = false := by
        cases (rejectMask width lo len (intervalDivisors (lo+len))).testBit (width*i) <;> decide
      have hnn : (rejectMask width lo len (intervalDivisors (lo+len))).testBit (width*i) = false
          ↔ ¬ ∃ p ∈ intervalDivisors (lo+len), p ∣ lo+i ∧ p ≠ lo+i := by
        rw [← Bool.not_eq_true, hit]
      rw [hbool, hnn, no_small_factor (by omega) (by omega) hhi]
      constructor
      · intro hp
        exact ⟨i,hi,rfl,hp⟩
      · rintro ⟨k,hk,hik,hp⟩
        have heq := Nat.eq_of_mul_eq_mul_left hw hik
        simpa only [heq] using hp
  apply Bool.eq_iff_iff.mpr
  rw [he, encoded_bit hw]
  simp only [decide_eq_true_eq]

/-- Unwidened packed prime flags for a segment starting at two or later. -/
def primeMask (lo len : Nat) : Nat := liveMask 1 lo len

theorem primeMask_bit {lo len i : Nat} (hlo : 2 ≤ lo) (hhi : lo+len ≤ 10240000)
    (hi : i < len) : (primeMask lo len).testBit i = true ↔ (lo+i).Prime := by
  unfold primeMask
  rw [liveMask_eq (by decide) hlo hhi, encoded_bit (by decide : 0 < 1)]
  simp only [one_mul, decide_eq_true_eq]
  constructor
  · rintro ⟨j,hj,rfl,hp⟩
    exact hp
  · intro h
    exact ⟨i,hi,rfl,h⟩

/-- A rank difference for a segment shorter than 16383 integers. -/
def blockCount (lo len : Nat) : Nat := liveMask 14 lo len % (2^14-1)

private theorem count_add_range (lo len : Nat) :
    Nat.primeCounting' (lo+len) = Nat.primeCounting' lo +
      ∑ i ∈ range len, (decide ((lo+i).Prime)).toNat := by
  induction len with
  | zero => simp
  | succ len ih =>
    rw [← Nat.add_assoc, Nat.primeCounting', Nat.count_succ, ← Nat.primeCounting', ih,
      sum_range_succ, Nat.add_assoc]
    congr 1
    by_cases hp : (lo+len).Prime <;> simp [hp]

theorem blockCount_correct {lo len : Nat} (hlen : len < 16383)
    (hlo : 2 ≤ lo) (hhi : lo+len ≤ 10240000) :
    Nat.primeCounting' (lo+len) = Nat.primeCounting' lo + blockCount lo len := by
  rw [blockCount, liveMask_eq (by decide) hlo hhi,
    encoded_mod (by decide) hlen, count_add_range]

end ColtonSieve



namespace ColtonHarmonic

open Finset

def generators (limit : ℕ) : Finset ℕ :=
  (Icc 1 limit).filter (fun k => 0 < k ∧ 2*k.divisors.card ∣ k)

def primes (n : ℕ) : Finset ℕ := (range (n+1)).filter Nat.Prime

def primeInterval (lo hi : ℕ) : Finset ℕ := primes hi \ primes lo

def weightedPrefix (scale n : ℕ) : ℕ := ∑ p ∈ primes n, scale / p

theorem mem_primeInterval {lo hi p : ℕ} : p ∈ primeInterval lo hi ↔ p.Prime ∧ lo < p ∧ p ≤ hi := by
  simp only [primeInterval, primes, mem_sdiff, mem_filter, mem_range]
  constructor
  · rintro ⟨⟨hi',hp⟩,outside⟩
    have h : ¬ p < lo+1 := fun in' => outside ⟨in',hp⟩
    exact ⟨hp,by omega,by omega⟩
  · rintro ⟨hp,lo',hi'⟩
    exact ⟨⟨by omega,hp⟩,fun h => by have := h.1; omega⟩

private theorem primes_mono : Monotone primes := by
  intro a b hab p hp
  obtain ⟨hr,hp⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hr; omega), hp⟩

theorem weighted_difference (scale : ℕ) {lo hi : ℕ} (h : lo ≤ hi) :
    weightedPrefix scale hi - weightedPrefix scale lo = ∑ p ∈ primeInterval lo hi, scale / p := by
  have same := sum_sdiff (f := fun p => scale / p) (primes_mono h)
  change (∑ p ∈ primeInterval lo hi, scale / p) + weightedPrefix scale lo = weightedPrefix scale hi at same
  omega

private theorem cast_div_le {a b : ℕ} (hb : 0 < b) :
    ((a/b : ℕ) : ℚ) ≤ (a : ℚ) / b := by
  apply (le_div_iff₀ (by exact_mod_cast hb)).2
  exact_mod_cast Nat.div_mul_le_self a b

private theorem divided_weight_le (scale m : ℕ) (hs : 0 < scale) (hm : 0 < m)
    (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) :
    (((∑ p ∈ P, scale / p)/m : ℕ) : ℚ) / scale ≤ ∑ p ∈ P, 1 / ((m*p : ℕ) : ℚ) := by
  have hscale : (0 : ℚ) < scale := by exact_mod_cast hs
  have hmass : (0 : ℚ) < m := by exact_mod_cast hm
  have step : ((∑ p ∈ P, scale / p : ℕ) : ℚ) ≤ ∑ p ∈ P, (scale : ℚ) / p := by
    push_cast
    exact sum_le_sum (fun p hp => cast_div_le (hP p hp))
  calc
    _ ≤ ((∑ p ∈ P, scale / p : ℕ) : ℚ) / m / scale :=
      div_le_div_of_nonneg_right (cast_div_le hm) hscale.le
    _ ≤ (∑ p ∈ P, (scale : ℚ) / p) / m / scale :=
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_right step hmass.le) hscale.le
    _ = _ := by
      rw [sum_div, sum_div]
      apply sum_congr rfl
      intro p hp
      have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast (hP p hp).ne'
      push_cast
      field_simp

private theorem largest_product {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (htop : m.primeFactors.sup id < p) : (m*p).primeFactors.sup id = p := by
  have hn : m*p ≠ 0 := (Nat.mul_pos hm hp.pos).ne'
  apply le_antisymm
  · apply Finset.sup_le
    intro q hq
    obtain ⟨hqprime,hqdvd,_⟩ := Nat.mem_primeFactors.mp hq
    rcases hqprime.dvd_mul.mp hqdvd with hd | hd
    · exact ((Finset.le_sup (f := id) (hqprime.mem_primeFactors hd hm.ne')).trans htop.le)
    · exact Nat.le_of_dvd hp.pos hd
  · exact Finset.le_sup (f := id) (hp.mem_primeFactors (dvd_mul_left p m) hn)

private theorem product_generator {limit m p : ℕ} (hm : 0 < m)
    (hgen : 4*m.divisors.card ∣ m) (hp : p.Prime)
    (htop : m.primeFactors.sup id < p) (hbound : m*p ≤ limit) : m*p ∈ generators limit := by
  have hpos : 0 < m*p := Nat.mul_pos hm hp.pos
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hpos,hbound⟩, hpos, ?_⟩
  have hnd : ¬ p ∣ m := fun hd => htop.not_ge (Finset.le_sup (f := id) (hp.mem_primeFactors hd hm.ne'))
  have hc : m.Coprime p := (hp.coprime_iff_not_dvd.mpr hnd).symm
  have hsize : p.divisors.card = 2 := by simp [hp.divisors, Ne.symm hp.ne_one]
  rw [Nat.Coprime.card_divisors_mul hc, hsize]
  have hs : 2*(m.divisors.card*2) = 4*m.divisors.card := by omega
  exact hs ▸ dvd_mul_of_dvd_left hgen p

/-- Weighted scaled integer lower bound for a collection of smooth terms and
cofactor times largest-prime products. -/
theorem lower_bound {ι : Type} [DecidableEq ι]
    (limit cut cap scale : ℕ) (hs : 0 < scale)
    (S : Finset ℕ) (M : Finset ι) (value lower lowWeight highWeight : ι → ℕ)
    (small : S ⊆ generators limit)
    (small_top : ∀ k ∈ S, k.primeFactors.sup id ≤ cut)
    (distinct : Set.InjOn value ↑M)
    (good : ∀ i ∈ M, 0 < value i ∧ 4*(value i).divisors.card ∣ value i)
    (lo : ∀ i ∈ M, max cut ((value i).primeFactors.sup id) ≤ lower i)
    (nonempty_range : ∀ i ∈ M, lower i ≤ min cap (limit/value i))
    (prefix_correct : ∀ i ∈ M,
      highWeight i = weightedPrefix scale (min cap (limit/value i)) ∧
      lowWeight i = weightedPrefix scale (lower i)) :
    (((∑ k ∈ S, scale/k) + ∑ i ∈ M, (highWeight i - lowWeight i) / value i : ℕ) : ℚ) / scale ≤
      ∑ k ∈ generators limit, 1 / (k : ℚ) := by
  classical
  let P (i : ι) := primeInterval (lower i) (min cap (limit/value i))
  let terms := M.sigma P
  let product (x : Σ _ : ι, ℕ) := value x.1*x.2
  let T := terms.image product
  have properties {x : Σ _ : ι, ℕ} (hx : x ∈ terms) :
      x.1 ∈ M ∧ x.2.Prime ∧ cut < x.2 ∧ (value x.1).primeFactors.sup id < x.2 ∧
        value x.1*x.2 ≤ limit := by
    obtain ⟨hm,hp⟩ := mem_sigma.mp hx
    obtain ⟨hprime,hlo,hhi⟩ := mem_primeInterval.mp hp
    have hcut := (le_max_left cut _).trans (lo x.1 hm)
    have htop := (le_max_right cut _).trans (lo x.1 hm)
    have hh := (Nat.le_div_iff_mul_le (good _ hm).1).mp (hhi.trans (min_le_right ..))
    exact ⟨hm,hprime,hcut.trans_lt hlo,htop.trans_lt hlo,by simpa only [Nat.mul_comm] using hh⟩
  have size_top {x : Σ _ : ι, ℕ} (hx : x ∈ terms) : (product x).primeFactors.sup id = x.2 := by
    obtain ⟨hm,hprime,_,htop,_⟩ := properties hx
    exact largest_product (good _ hm).1 hprime htop
  have injective : Set.InjOn product ↑terms := by
    rintro ⟨m,p⟩ hx ⟨n,q⟩ hy he
    have hp : (product ⟨m,p⟩).primeFactors.sup id = p := size_top hx
    have hq : (product ⟨n,q⟩).primeFactors.sup id = q := size_top hy
    rw [he,hq] at hp
    subst q
    have hprime := (properties hx).2.1
    have hm : value m = value n := Nat.eq_of_mul_eq_mul_right hprime.pos he
    have same : m = n := distinct (properties hx).1 (properties hy).1 hm
    subst n
    rfl
  have all_good : T ⊆ generators limit := by
    intro k hk
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hk
    obtain ⟨hm,hprime,_,htop,hprod⟩ := properties hx
    exact product_generator (good _ hm).1 (good _ hm).2 hprime htop hprod
  have apart : Disjoint S T := by
    apply disjoint_left.mpr
    intro k hk hkt
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hkt
    have hcap := small_top _ hk
    rw [size_top hx] at hcap
    exact (properties hx).2.2.1.not_ge hcap
  have hscale : (0 : ℚ) < scale := by exact_mod_cast hs
  have smooth_bound : ((∑ k ∈ S, scale/k : ℕ) : ℚ) / scale ≤ ∑ k ∈ S, 1/(k : ℚ) := by
    push_cast
    rw [sum_div]
    apply sum_le_sum
    intro k hk
    have hk0 : 0 < k := (mem_filter.mp (small hk)).2.1
    have t := div_le_div_of_nonneg_right (cast_div_le (a := scale) hk0) hscale.le
    have hne : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
    convert t using 1
    field_simp
  have group_bound :
      ((∑ i ∈ M, (highWeight i - lowWeight i) / value i : ℕ) : ℚ) / scale ≤
        ∑ i ∈ M, ∑ p ∈ P i, 1/((value i*p : ℕ) : ℚ) := by
    push_cast
    rw [sum_div]
    apply sum_le_sum
    intro i hi
    obtain ⟨whi,wlo⟩ := prefix_correct i hi
    rw [whi, wlo, weighted_difference scale (nonempty_range i hi)]
    simpa only [P, Nat.cast_mul] using
      divided_weight_le scale (value i) hs (good _ hi).1 (P i) (fun p hp => (mem_primeInterval.mp hp).1.pos)
  calc
    _ = ((∑ k ∈ S, scale/k : ℕ) : ℚ) / scale +
        ((∑ i ∈ M, (highWeight i - lowWeight i) / value i : ℕ) : ℚ) / scale := by
      push_cast
      rw [add_div]
    _ ≤ (∑ k ∈ S, 1/(k : ℚ)) + ∑ i ∈ M, ∑ p ∈ P i, 1/((value i*p : ℕ) : ℚ) :=
      add_le_add smooth_bound group_bound
    _ = ∑ k ∈ S ∪ T, 1/(k : ℚ) := by
      rw [sum_union apart, sum_image injective, sum_sigma']
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (union_subset small all_good) (by intros; positivity)

end ColtonHarmonic


namespace ColtonHarmonic

open Finset

/-- Decode prime offsets stored by differences, one byte per prime. -/
def decodeOffsets : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | count+1, word, previous =>
    let offset := previous + word % 256
    offset :: decodeOffsets count (word / 256) offset

def offsetsMask : List Nat → Nat
  | [] => 0
  | i :: rest => (1 <<< i) ||| offsetsMask rest

private theorem offsetsMask_bit (xs : List Nat) (i : Nat) :
    (offsetsMask xs).testBit i = true ↔ i ∈ xs := by
  induction xs with
  | nil => simp [offsetsMask]
  | cons x xs ih =>
    rw [offsetsMask, Nat.testBit_or, Bool.or_eq_true, ih,
      Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, decide_eq_true_eq]
    simp only [List.mem_cons]
    rw [eq_comm (a := x)]

private theorem sum_offsets (f : Nat → Nat) {xs : List Nat} (h : xs.Nodup) :
    ∑ i ∈ xs.toFinset, f i = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx,hn⟩ := List.nodup_cons.mp h
    simp only [List.toFinset_cons,List.map_cons,List.sum_cons]
    rw [sum_insert (by simpa using hx), ih hn]

private theorem have_interval {lo len : Nat} (hlo : 2 ≤ lo) (hhi : lo+len ≤ 10240000)
    {offsets : List Nat} (in_range : ∀ i ∈ offsets, i < len)
    (same : offsetsMask offsets = ColtonSieve.primeMask lo len) :
    primeInterval (lo-1) (lo+len-1) = offsets.toFinset.image (lo+·) := by
  ext p
  rw [mem_primeInterval,mem_image]
  constructor
  · rintro ⟨hprime,hl,hu⟩
    have i_lt : p-lo < len := by omega
    have hgoal := (ColtonSieve.primeMask_bit hlo hhi i_lt).mpr (by
      rw [show lo+(p-lo) = p by omega]
      exact hprime)
    rw [← same, offsetsMask_bit] at hgoal
    exact ⟨p-lo,List.mem_toFinset.mpr hgoal,by omega⟩
  · rintro ⟨i,hi,rfl⟩
    have hi' := List.mem_toFinset.mp hi
    have ilt := in_range i hi'
    have bit : (ColtonSieve.primeMask lo len).testBit i = true := by
      rw [← same,offsetsMask_bit]
      exact hi'
    exact ⟨(ColtonSieve.primeMask_bit hlo hhi ilt).mp bit,by omega,by omega⟩

/-- A verified gap list gives the exact change in both the prime count and its
scaled reciprocal prefix. Positivity of the mask covers every listed prime,
and equality of the masks establishes that the list misses no prime. -/
theorem weighted_segment (scale : Nat) {lo len : Nat} (hlo : 2 ≤ lo) (hhi : lo+len ≤ 10240000)
    {offsets : List Nat} (in_range : ∀ i ∈ offsets, i < len) (unique : offsets.Nodup)
    (same : offsetsMask offsets = ColtonSieve.primeMask lo len) :
    (lo+len-1).primeCounting = (lo-1).primeCounting + offsets.length ∧
      weightedPrefix scale (lo+len-1) = weightedPrefix scale (lo-1) +
        (offsets.map (fun i => scale/(lo+i))).sum := by
  have int := have_interval hlo hhi in_range same
  have hspan : lo-1 ≤ lo+len-1 := by omega
  have hinj : Function.Injective (lo+·) := fun _ _ h => Nat.add_left_cancel h
  constructor
  · have h := card_sdiff_of_subset (primes_mono hspan)
    change (primeInterval (lo-1) (lo+len-1)).card =
      (primes (lo+len-1)).card - (primes (lo-1)).card at h
    rw [int,card_image_of_injective _ hinj, List.toFinset_card_of_nodup unique] at h
    have cnt (n : Nat) : (primes n).card = n.primeCounting := Nat.primesLE_card_eq_primeCounting n
    have mono := Nat.monotone_primeCounting hspan
    rw [cnt,cnt] at h
    omega
  · have h := weighted_difference scale hspan
    rw [int, sum_image (fun _ _ _ _ he => hinj he), sum_offsets _ unique] at h
    have mono : weightedPrefix scale (lo-1) ≤ weightedPrefix scale (lo+len-1) :=
      sum_le_sum_of_subset_of_nonneg (f := fun p => scale/p) (primes_mono hspan) (fun _ _ _ => Nat.zero_le _)
    omega

end ColtonHarmonic


namespace ColtonH3Data


def smoothWords : Array Nat := #[
  0x840700000004650000100027004000042400000080460002000045000000084400000100430000000067000000842500001000450002000424000000802700001004240000000409080000000700000084060040000007000000046400000080450000000c040000000427080000002500000008430000008424000200000700400000250000000482080000040400000004450000100007004000040400000080260002000025000000082400000000470000100025000200040400000000a20000008007000010040400000000650000000444080000004200000080250000000407004000004200000084040000000425000200004200000080060000100042000000002700000000450000008042000000042400000004420000000007000000002500000004040000000043000000004200000000220000000003,
  0x8000004440000008427000010082400000004850800008025000010004700400004440004000043080000040700000080660000000c250000010424000200800700021004040040008025000010000a000200006500400004070000000864080000840400000084450000001004000010800700000008270040008404000010006500000100260002000444080000042500020080250000200043080000800600000088240002000407004000042500000008820000008047000010044400000000a5000000042900400080060000001022000010802508000000270002008404000010040700000000680000008426004000002700020004250000108404000000002b00000080650000000c240002008006000000044708000000450000100425000000844400000010030002000027000010800600400000450800000424,
  0x847004200000700000100460000100409000001840408000004450800100007000000010200020080450002000c04100000004308400004040800008026000000884400020004270000108406004000044500000008a2000000806700401000070802000025000000044900400080260800000824000000104200001080450000100c0400000180060800000047000000086500420000250000100427008000004300000080c20040000824000000844608001000250802000404004000004700000004a400000100270002000445000000004b00021000070000000c440040100025000000840900420004040002008026000000046708000080070800100404080000006500000008830000000c0700001004450002000824004000800700020000470040100404000010802600400000650000008c040002100025,
  0x10047000010040a0000008c060000108444000000006b000210002700000080a500401000450000008429000200000c00000001030002008046000000048708000080270000108407080000040900000080680000000c2700000100a2000001042600020008440000200027004000802700000010430002000067000010804600000180070040000409000000802b080000840600000100650840000007000210004500040004240000008447000010084400000004a500000008290800008045004000840600001000670800000c0408000004270000000c4500000104440002008027000000046800400080450040000c04000010002a000000882600020004090000018025000000000f00400004270000000884080200000700000000a70840000025000000042b0000001024000010802700020084060000200424,
  0x8a4080000844408020000270000010427080010800608400000450000108824000000044b0002100407000000848500000010440002000068000010088200001080470002008426000020044410000004240000000867004000844400001000a50800008407004200002700000100660000100429004010800608001000270000001007000200002b0000010482000010800a08000080460040008407000010006800000088640002000447000010842600401000270802000045000000900400000000e50080000424000000046900400080460800000844000010002b00000088270000018026080000006700020084440004000027000000088500021080060000000c090042000045000010044700000000a8004000084400000084660800100045000000102500400000670002008407000000800d0000008882,
  0x400088240000100485004200040700000104460002000864000020004710000000270040000882004000804700000084a400401004440800100407000010806600400000a50000018027080000006800000005020002008445004000042900020010040000110424000000804b0002108007000030002508000084260000008c4400020008270840000027000201002600040004440040100407000010086400002000a20040000068080000002b000000084900400084260000008c07008000002700001084450802008006000010100400000184060800000447000200882400000080a6000030040400000104640000100827000200088200020080470000200065004000002b000000048800001100260002100444000010004a00020000a50000008846000200042900420080060000018045000000002f0040000447,
  0x8847004001042400420080070000100c44000001804600001084090000200482000400004700000008a500021080260000000c290800008445004010000a0800001004080010800700000081020040000864080000082700000084860000001045080001002608020004440000100c0700060004040000000868000000802d00021008240040008445000030000700400010040000010067000010042a00020004850000008c260040108007000210004700040000a2000000040f00000080c5004000082700002080260000000c8400000084490040010026000200002c0800008824004200044408020004070000009042000200806600000004a708000008820800008047000201042400000088650800100444000000142408000000a5000210000a0004000065080000042908400080060000000c4700000100c2,
  0x400048200000084a50040000c07000000106400401004450000008829000200040c004200082400020084460000200464100000044400000008870042000047000010044900020004a40000008c45004010802608001008240080000065000010104200000184440800000485000000042e00020100270000008468000011800608001000470000001027000200004b0000100865000010802a0002000c440002008409084000044400002004270800008066000000800f0004008026000000888400401008240800010424000010844608020080070040000485000001840700000080a70040100047000000842b080010000a00001004a4000001046500060000250000009024000000010500800004440002000c07000011002708400004070002100445004000806608000008640000208424000010004b0000001082,
  0x8487000010000f08000100270000100884080200044510000000a2080000004b08021000070000000869004000844600001000a70800000c44000200010208000084090000010068000010042b0080000047080200802600400004a4000010102400000184260002008844000020802700040004270000000c8500021084060000001009004001002700420004450000100847004000004b1000000065004210000700000004a800001100460040000c440040008409000010006a0800000c0700000088660800100445000200044900420080260802000824000000004f0000010c240002001042084000800700001001020002108045000000840d00000100c30002018006080200004700040084240000010447000600000700800000a208001080260002000865000000900600000000e70000108844000000046b,
  0x40080270000008885000000144400020004680000008c090004100424004000010200420080450000108447000210002a0800000449000200882600000080a808400080260000020442004000884400001004a50800001042000200000f0000010466000010082908001080450002000884000000902500401084060000200067080001800610000000470000018824080000086500000084c4000000108300020000a7000200042b00000108820000100c450000018047000010840a00c000040400400004490002001024008000802600001104440840000824000000806b00003000450800008446004000104200000100a5000010046800022004240040108045000001042900020008470040018006000200800c0840000047000020002a000010882608000004a40040000865000201004600021004090004000464,
  0x10048708000010240042000409000000900700000000e8000200802b004000000f008000042708020084060800200424004000088400020100651800000404080000084700000084a600000010650842000007080001004608001004090000108068000001086400400000a7000000050400020084470000200465004000042b00000008880000110426000000804d0002100844000030002700000088c20040001024000010044a00020004a50000008c4600020008290800000102080200804500000000ab004200840600000184450040200424000000042f004000084700002080460000000ca400800084241000008026000000846900001180070040010046000200004c08000088440040100409000010802b00c0000025008000048208001084060002000c450000110065084000044500020104440840100007,
  0x100c0900421000450002008429000020044710000004270044000424000000802f004000844700001000a80800000c45000400804600000088a4000200048700401008440800010444000010846600400004a5000010102518000000250800000468000000090200000080c700400008290840008045000000844b080010002a0800008826000001048500060000450802000409000010800d0000009044000200806800c00000070080000464080000000f00000004a900001100470000108c0608000008840040000c4500020104260000208444000010006b00000010a2100000842400000088670002200027004001044400001080a500003080060000018066000010842908000000a70040000468000210000c10000004820004000067080000042b00021080460000000c49004010002a00400088260002018007,
  0x60000270800108046000200088500000090260000000107000020006808000180070002000c09000000048b084000040900021004470040008068080000802b00000084c50000208426000000108400020000a8000000884908000100650040010426000200042c004200084400000108830040200027000200846608021000450002001025100000046400000008a700800080270804000424000010900400000204060000000c2b0800008447008010042400000100a60000100469004010804608001008440040018007000200800d000010882708000004a5000000044e0002010047000210040a0000208065004000802b000400046508000008290002008c060000200c2400000084880000118026084000840600000010470040010065000200006b00000104c200041000270000100885000010804a00020080a5,
  0x80000842900400010250004000c24000010044b0000001482080200000c0000008c4700800000670000108485080200804600001010440002100068000001844608000004870006008006000020088200000080e60000208047004000800d00040004470000000ca510000080270002108426000000102900400100470000300444004010040a100010042400000104a40040008c060000100867000003000300002000a5004000006b0000110066000020042900400080a50800008068004000842900020090040000008886004200000c00820004240002000469080001042600420080460802000844000000006f08002000270000010c4400400004870000101007000210002b0000018409180000000700000008e400020088270000000c68000000842d0002018026000030040700040084440000010467000010082a,
  0x1427000200044b00001080a6000030800700000108a20040009004000010842a08000000a800020084850000010c2600400004690002001044000400006800800080460840000844000210804700000204250800008466004010002b000000840f00000100c500400088270000100488080000102500040084260000008c8400022004440000010449100200042400020008670040018026000200802c000020004a004000001000021000a500001088460044000027004000088500020100660002100429080000800d004210800600000084a70040000c090000118045000010002f00401004470800010047080010040a00001008a40800008c06000001086500400000a8080000006b0000009424000000050500020010070000000889000011042708000080a50040008466000210800a08401000450004008065,
  0x802000447000010804b000000908200020080a600c000004500000300220000100c0a00060004070800108426000000086b00021008270004000882000030000a000400804700000088a500400010070002200065004200002b0000001464000200048800021100260000008c29004010800a00041004440800009004000210004a088000042400040000a5080000046900000009030002008846000020086400000080c8084000804600040004290000000c87004010006800000101020002018045080010002b000200002f080000882700420004470000010486000010084900020008a40000009045004010842608000180260000001c04008000046510000000670000018844080400002708000008850002010427008010002708021080060800000c09000000886808420000450000118406000001002d0800100447,
  0x902700000001080040018045000200804b004000002f00800004470802008426000011002a080020044400400008a4000010142400000188260800000867000020842708001000a5000000108508000100660004100065080010042900400104270000300824084010800600000108840000100c47000600044400001100c20000200485004000044b100000046500000008a80000110446000000806d00400084850000020407000030004700400010440042000068100010002700000100a7000010046a0800001007080200002b0000008c660040108047080010800a000200084900420084260040200444000000044f104000042400000110240000008105004000086700002080660080008444100000804600401000a5080010006800820000270040010066000200006c004010042900021010040002018406,
  0x20014240080008426000000846b080010004a08020000a50000300445080000884600000104a500001008680802000429000010802d000000906400c0000027084200800608000180450002000c470040101004080000002f0040018406000200840c00001100670840000447000020042a00020100c2000210048500400080a60000108c2608000008a400020104460004000864100000844400000088870002200047000010040f100200002700001080c500401008270000308026080001042700420080470000100c840040200065000010844900400004880040110026000210002c080000044b000000980400000008e500800080650080000c2400021080660000000c690800008485004010004a000000842e00420000a5004000884600001004a708000010440802000068004200042900000104680800108047,
  0x9009000200802d08400000680000101082008000042900001088470002300007000000046e00420010040000011043000201006700c0008006000210042a004000804b000400048508000008490002008c2610000080650000200c4400000084a8000011804608400084261000000c240000001067000410004700001008a5000200040f000010806a00020080c50042000827000001086600022080260000100c290880000027000001802b0002000c84000200844900002004670800101004080001840610000004470042010026000400002c004400044408000080a6000000804f000400806600000088c400020004a708001008270080000068000010848608020080470800200065084000002b000010104500000184471800000045080000048800060080070000000922080011002600002008830040000849,
  0x2008650840008047000020802a00001001420000000c88000000844d00000101030002018046000210840900400014240000010487000010084a0006000047080010806600020008a5000010800f000000904608400000a500041080260002000c2910000000680000108884004210000a00000004ab00440000650840000429080200100400002080c2000000082f080000804b0040000c47000020844600000010a400400100c21000008426004010048500000088690040010446000200044c00001080a7080200082700000180680040200047000010842b0002008486104000002700002004a40000010c27008000088200020010450080008047080201002608040004440000109024000010010500000204260000000c4b008010044400000100c600040084270000008c85004010806600800000a50002000868,
  0x4000802d10000008820004000467100000804700403000070002108446000002082400000010490040010067004010042a0042000485100010044400000104c40040008c260000100887080000142400020080a7000001800d10000000a5004210004700000004e8000200842b0000200449004000040f080210000a00400080c50804000065100000042900402080260040000c8400801000650000018c060040008449000400088300001000aa0800000c470002009024000200010500000088a6004200002c08000100c2000001006b08001004850082000444000010042e0000001465000211002700003080450800010446004200806600000180a50000108468080020004700400004a700001010270006000824000210004b0000400442000001842918000000270002001082000000090400000004130002008847,
  0x2100449000001882700040004a40800000868080000802d004210802600000084c70040000c290082000065000010004f0800300007084000100400000280260800010067080010042a0802000485000200042e0800008c26000020010200000108850006000445000010840d00000094440000000525000200846800c00004070002118006080210004700800008640002001027080000040f00000008a9000011044708000080c5084000082700061000070800208026004000848600001090060800000c84000210802a18000080060800008449004000104500000100a80004000c44000010046b0840010026080200002c00022004270802008066000200800f000030840600001010640000018466000010882908000004a70006008026000200888400002008a200000081060040000868000210040c0000208067,
  0x80001804600800004850800108409000200840d000011006800400080a7080400004708000008a5000000850400020104470080100047004000842b080210802600040008650800000c290002009006084010000a000020102400000088880000118426000001004d00021088440000001447000200046b00000108c20040009024000410042700400001050000100c85000010844a000000007100c00004440000010c460000101009004011002700020010640080008066000200882900000080ab000002044500040080c20800008486004010004b0040001082000000842f1000100065000001900400000100e5004000884700001004a80800001045000030040900040084460000010469100200044400020008870040018046000200804c0040108409000020006a00400000300000108866004400004700400008a5,
  0x2000c850000009426000000050700001100a508400004850000200468004000042e00020010090042010027000000088b000011042908000080a70002100847004000846800040008a20040118006000210800c0000000c0f0840100047000030002a0004008067080000842b00000088c50040001027004200004b1002000065000000148400020004a8000211004600000284240000008c49004010802a000200082c0000108487080000902408000001050042008409000210006a08800004440040200427000000984208001100270002008866000020088400000080e80840008066004000800f100000086400040004490000000ca70080008427000011800a00440080260040008884080010004b0800001082000000102b000200004f080000884700000104a600001008690000009065004010844600002000a7,
  0x4010884400002004a5004000046b000210000f00800008831000000485080000042e000011046608020100270002100884000010902500000204270800008468000000890200400010640800118006100010004700000100c70040008829000010048a0800001027080200004b0000008c86004200040c080010802a000200086900001084c400000000eb004200844600021000a70000018485000400010200060080450802008409000000046f1040000444080020042700000110440040000887000201006800c0008007000210042b180000040710000080660000110882080000800f00000084a90000118047008200004700000208430000001068080400802608000088840040100449000000882d000210102400020184260080108026000010806b0000030042000001086700022080270000100c2a0800108446,
  0x80010884400040000a7080000046b000000982400000009050080000c440000000c89004010006a000000844e00020108820008000442004000886600020180470800001064000210840a00002100650800008829004200044900000104880004001024080200040c008200802600021104440000009047000200806b004000004f000410802700800004670000108885000230004508000000120802008446000011004a00020100a500001014440002100468000001884618000004440000108c090800000887000600840600000084e600020104290000208447004000840d00000010a5100000842700420180060842000047000220002a000001002f080010044900021088260000020c0400000014290040010447000030084400001080a80046000007084010802600000108a4004000900608800000650002008487,
  0x2008c09000011086400401000a70000200c27000000848b0840008409080010006a000010050400002100a200400100680800008866004010042b00000104c5000410002a00001008880802000449000010804d0000009084000000016500020080a800c00000470842008026000600040900800004a40040101024080000004f00000004e90040018426000200842c000020044a004000041000420088440000108c46004020802700440004270040000c8500020104660002100829000400088400001000ab0002009025080000840d0042108406000020104300000088a7004000100900022000670802018006000010042f100200004700401008470000008c2b000030804608000104470806000007100010802600000180a60000108469080000900600020084c4104000006500400004a80040110046000210004c,
  0x28027080001006800000105020004100067080010042b0040010429000200042f0042000847000020010300000108860002208046004200800c0000100c490880000047000001804b004020002a100200802600020084690040108826000020048708001010240800018426008000086510000004670042010046000400004c08020088440042100409000000806f080020802700400084870804000427000010900700001000e80800000c85000210802b18000080070000000c2e004010000f008010042708021084060800001009084001002700401008840000008c68000001042d080010084700001084a6084000004b0000101065000010882a08000004a800800080c20800110046000200888500c000082400000110260000008107004000086900002080680002001444100000088300040004680080008446,
  0xc00004451040000047080020002a0000010c47000010100a000040042500800008a20800108826000200106510000004a400000008e70080008067000011048508020100460006100045080210040900400084c40000109044000210806800c010000700000204460000000c6b0800008487000201086400420000a7000020888200000100e6080010000f00001004a90002000504000030040a0004008447004200042b080010088400400108820002000888000211042600000090290040018047000200804d004010840a000020006b00800004490002000c0c004200102400c00080260040110444000210044a00002080a5004000806b00040004a508000008690002008c4600000084c8000011806600403000450840008446000020842908001000a71000000c44000000108700400100a500020000ab0040100468,
  0x4400802700400088850002018066000210842908020000a7000030044700400014440042000468100010042700000104a70040008c090004001043000010086a080200042b0080000102000010802f00000090660800010882000003000600002000a808000180470004108046080010840a0002000c4900001088a4004210002a084000044900420088260002100487080200102400400080a808800080260800110444000000084f10000080c2080000806b000000850500002084660800300045000200900700020000e810000084460000008889004200000f08000100a50800100468000010090200820004270040010466000200046c00001080c700401008290000008c0d00420008840004010065080001042900000108c3004000902508020008470040200067000010844b0840018006080200800c00020084a6,
  0x100c2b000001802d00000094270000000508000200844b00001100a60000200469004000042f080210002a100000044908020088260040208046000011042a08000080a8000201048510400080260000018c2618000008240040008469000210800d0002009044000030002b000400806800c2000007004200004c08400088440004000c27000010044e0000001485080200000f00020004a9000211004700040100a20800010466004010802b08001008290002108c06080200088400000180c500001084880800009025000021802600000000af084010840608002000670000010c84000220844400001010470006000844000210006b00000184491800000047000000092400000004330000200885000201002c000020804a0040008010100000086500420104440000000ca808000084c40002308006000000846d,
  0x1090260000100107000210804a1800008026000030006800040080a5080000846900400010650002100c09000020886400000100c8000010048b0840010046080200004c084010040900040084290000008c87000220044700401080681002000427000600000c004001086400800000a7080010802b00001084c5000200802f00003084260040000504000010108400021000a8000001848600040001030000108849000600804600020088a400400008880040110426000210042c004000804d10000008a2000400048700421008441000008067080201044400800010240000020844000000106908040080270800008885004010044a00021010250040008c4600001008a708000014440080108027080200046800020009020800008c0900020080c70042000829000003004300002000e500400000ab0000120406,
  0x8400000a7004000005000021090040000001c07000202040600800004680002000c2b00001088860800000504004210000c0044000067084000042b000001108200020100a600c00080450002100469000001884718000004450000108c0a08000008880800110426080000804d00421080460040000c490802100844008010002a000010006f0000110c44004010048708400010240000028046000000886b00001184091800100007080010044a0000210482000200044e00040088820800008c46000030800a00000108a5004000900700400000e8004200802b0000100c6808020008291000000102000010842d08000000ab0002008488000211802600000304040000010c2908420084060000400407000410844400800008840002001047000400006b080000042f08400008470800208046000210088500400084a6,
  0x840008826000001006d08001004871000001024000610800600000014670040010485000200048b00001080e6004600004508420004090000308047004010800d004000904400041004470042008068100010802700000180a7000010846a080000900708000000e8080200802b00020084c5084000000f0000010c6600400004a90002208426000010102900401100470880000427000001842b000200108400040000a80000009825000200884900001104a40040108c060840000884000020086700000080cb0042010426000400042c0000020465004020844400003000a508000084a6004010006b000000844f00000190240000010105004220002708000010650000210066000030042900040084660000008cc40040308006080010806800020008a700820080270040018066000200806c08000108640040108429,
  0x2008a4000001102700000081080800108c06004000802f100000088400040004690080008447000011086500401000a80802010426000011802a0800208444004400804600400088a4080010006b00001005050000020826000000104b000200006f08022000270002010c440042000487000210100700000104c6000201840918020000070000100889084001044400000090850800308006000003002508000180660000001c44000001800f00800004a508001084290002000c6810000000a70040101025000200842d084000046800400009020004018026080210000c000001888400400080c70804000067000000086e00c00084060080100067000210082a0000208485004000844b080210804600040008850800000c4900020090260002000107084010002a000020104400000088a800022000680000118446,
  0x120425004200800d0000100c4a0006000447000010840f10020080270000009446000000052700c000040900001100c500002004880800101025004000044e000031002600041084260002001029100000046800420100470800000902004210040a00000008ab000011044908000080c7084000082900020104a40042008c0600400084880040118026000210802c0000000c2f000030004a080000844b00401000100040001047008001006500022000a5004200006b100010002a00000014a400441000270040100885000211006600000284440000008c6900022004290800010485004010804a08060000450000021003080010800d000200084c08000090440040100c09080200806808c0000007000020002f00420084290000018468004020044700040000e508000004a9080011004700020088861040000427,
  0x100e70008000425004000884900001004aa0800001047080200006b00020005050000008ca60000118844004200042c0804100027000001046b0800100885000600002b080010804a0002000889000000010b00040104820800100c09000030100400001088680802008429000000048f0042001025000011002d0800200447000001106400400008a70000101427000210044b00002080a600000188290000000d040040109004080000802f00000084c900400204060040000c2b000020842a008000104308001000a80082000067000000108800400100a6080400804600020000ac0000110c2608000088a40040100469000000884d00021010440004100068000201844600801080460000210464080200048708401008440000300827000400886400000090c2000220088200020080e600000108870002208047,
  0x20104490800109004004000842d000400086708000204060800000c2b10000084470042018026000400802c0000028065000220004a0042000010004400844408000100a600041000a5000001004f080010046900021088460000020c24000000144900001080c8004010082a08401080460042000885000401006600000108c40040009026000410042900400001070000100c8700402000680000000564080200800d00001101020042000c09004000048b000210002f000001840d10000004a5080000044e000000980700000008e800800080680000110486080201004700000080ad080210040a00021008a4084000802b00400084c50080000c2700001090450802008c060000020447180000804500402084260800008488004000108400800100a20800118026000201086500420000a810001000670000019006,
  0x9844000000092500800080a500020088680002118406000201002d0840008068000200142700021080a600c01000450000000ca9008000842908000084c5000000846e0042009004080020842600400088860800001084000210842a08020000a81800008406000400848508000088490002010c26100001006500420004690000208c4400000104a80004001044000010086b08400104260006000068080200042c008000010300820080460000009067084200084400000300070004100882004000006f010000044208402000270040010c4400041080470002020425008000048700001088a500401010070800000032004210002b00400184091840000007000200840f000011006a00020100c50002100488080200102500000188660000108c2908000008a70006008426088000802700000085060040000c68,
  0x40101044080000006f004210006800000005090040018446000200844c00001100a70800010c4408400004870046008006000020046a080010100700020101020040000430080210002b0800018409004020088200400080e6000400002f0040208047004400044700020104861040008027000210084900002084a400040008a40800000c68000000110200800088820002009045080000842d00000088c7004000102908020180261000001043000010044f100200006700400104a408040084440000111024000010810500000284260000008c4b00003080660002018844080010082a00801084441000108046080200088500000180c600402000a5008000006b080000902608000001070000218027080020006800002005020000010c8500821000270040110066000210006c0802000c090040200429080000048b,
  0x8000010290840010047084010040a00401008a40000008c88000011882608000104a40840008c06000001044d0000021022004001086500800000a8000200086b000401046408002000a5084000006b004000050500001010850000018487000010884a000230000a00060080470800110066000000047100020088a500c00008440042001007000420006508002004290000011046004000088900004008241800000409000400048800800084660002008c2910000080680000110884004210800a0000200c4700000084ab08400084291000000c27080200900400002100c200003004850800008886004010044b000000882f084200000c10000100a2000410004a00001008a800060000a50802000469000010806d00000090a4000220086400020080c800000108690842008046000012040700060004290002000c87,
  0x4000840f080210800a000002088200000010a700400100c51000008429004010048808400010250000028047000220002c000011840a0044008426080010044b004220044400001098040000020c060040010449000200044f00001080aa0002011024000200810500000108a600800180260002208066004200802c0000100c690880000067000001806b004020004a10000001030082008444000010842e1002008046004010884600002004a70800101044080210006808000184460080000885100000048700420100660806008006000400006c00421004290000110468080020088208000080e60800208047084000800d080400044700001090270000100108000210804b0000000c4e00040080a600c2000045004010002f0000008904000000841300801004470002100c0a00002088650008000407000201800c,
  0x40010c26000202040700800004690002000c2c100000006b00001088870800000505000230004700000004ae004200104400042000a200440000680000011083100210002700020100a700c0008046000210046a080200100700002080c5080000088910000080a50000200c8400000084e800400204250000208449
]

def smoothSize : Nat := 2713
def smoothWord (i : Nat) : Nat := (smoothWords[i/64]! >>> (40*(i%64))) % 2^40

set_option maxRecDepth 6000 in
private def groupRowsBlocks : Array (Array (List Nat × Nat × Nat)) := #[
  #[
    ([2, 2, 3, 3], 1, 783),
    ([2, 2, 2, 2, 5], 1, 745),
    ([2, 2, 2, 2, 2, 3], 1, 739),
    ([2, 2, 2, 2, 2, 2, 2], 1, 732),
    ([2, 2, 2, 2, 3, 5], 1, 723),
    ([2, 2, 2, 2, 2, 3, 3], 1, 721),
    ([2, 2, 2, 2, 2, 2, 2, 3], 1, 718),
    ([2, 2, 2, 2, 2, 2, 7], 1, 717),
    ([2, 2, 2, 2, 2, 3, 5], 1, 716),
    ([2, 2, 2, 2, 5, 7], 1, 715),
    ([2, 2, 2, 2, 2, 2, 2, 5], 1, 714),
    ([2, 2, 2, 2, 2, 3, 7], 1, 713),
    ([2, 2, 2, 2, 3, 3, 5], 1, 712),
    ([2, 2, 2, 2, 2, 3, 3, 3], 1, 711),
    ([2, 2, 2, 2, 5, 11], 1, 710),
    ([2, 2, 2, 2, 2, 2, 2, 7], 1, 709),
    ([2, 2, 2, 2, 5, 13], 1, 708),
    ([2, 2, 2, 2, 2, 3, 11], 1, 707),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3], 1, 706),
    ([2, 2, 2, 2, 3, 5, 5], 1, 705),
    ([2, 2, 2, 2, 2, 3, 13], 1, 704),
    ([2, 2, 2, 2, 2, 2, 3, 7], 1, 703),
    ([2, 2, 2, 2, 5, 17], 1, 702),
    ([2, 2, 2, 2, 2, 2, 2, 11], 1, 701),
    ([2, 2, 2, 2, 2, 3, 3, 5], 1, 700),
    ([2, 2, 2, 2, 5, 19], 1, 699),
    ([2, 2, 2, 2, 2, 3, 17], 1, 698),
    ([2, 2, 2, 2, 2, 2, 2, 13], 1, 697),
    ([2, 2, 2, 2, 2, 3, 19], 1, 696),
    ([2, 2, 2, 2, 5, 23], 2, 695),
    ([2, 2, 2, 2, 2, 2, 2, 3, 5], 1, 694),
    ([2, 2, 2, 2, 5, 5, 5], 1, 693)
  ],
  #[
    ([2, 2, 2, 2, 2, 3, 3, 7], 1, 692),
    ([2, 2, 2, 2, 2, 2, 2, 17], 1, 691),
    ([2, 2, 2, 2, 2, 3, 23], 2, 690),
    ([2, 2, 2, 2, 2, 2, 5, 7], 1, 689),
    ([2, 2, 2, 2, 5, 29], 3, 688),
    ([2, 2, 2, 2, 2, 2, 2, 19], 1, 687),
    ([2, 2, 2, 2, 5, 31], 4, 686),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 5], 1, 685),
    ([2, 2, 2, 2, 2, 2, 2, 3, 7], 1, 684),
    ([2, 2, 2, 2, 2, 3, 29], 3, 683),
    ([2, 2, 2, 2, 2, 2, 2, 23], 2, 682),
    ([2, 2, 2, 2, 5, 37], 5, 681),
    ([2, 2, 2, 2, 2, 3, 31], 4, 680),
    ([2, 2, 2, 2, 2, 3, 3, 11], 1, 679),
    ([2, 2, 2, 2, 5, 41], 6, 678),
    ([2, 2, 2, 2, 5, 43], 7, 677),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 3], 1, 676),
    ([2, 2, 2, 2, 2, 3, 37], 5, 675),
    ([2, 2, 2, 2, 3, 3, 5, 5], 1, 674),
    ([2, 2, 2, 2, 2, 2, 2, 29], 3, 673),
    ([2, 2, 2, 2, 2, 3, 3, 13], 1, 672),
    ([2, 2, 2, 2, 5, 47], 8, 671),
    ([2, 2, 2, 2, 2, 3, 41], 6, 670),
    ([2, 2, 2, 2, 2, 2, 2, 31], 4, 669),
    ([2, 2, 2, 2, 2, 2, 3, 3, 7], 1, 668),
    ([2, 2, 2, 2, 2, 3, 43], 7, 667),
    ([2, 2, 2, 2, 2, 2, 2, 3, 11], 1, 666),
    ([2, 2, 2, 2, 5, 53], 9, 665),
    ([2, 2, 2, 2, 2, 2, 2, 5, 7], 1, 664),
    ([2, 2, 2, 2, 2, 3, 47], 8, 663),
    ([2, 2, 2, 2, 5, 59], 10, 662),
    ([2, 2, 2, 2, 2, 2, 2, 37], 5, 661)
  ],
  #[
    ([2, 2, 2, 2, 5, 61], 11, 660),
    ([2, 2, 2, 2, 2, 3, 3, 17], 1, 659),
    ([2, 2, 2, 2, 2, 2, 7, 11], 1, 658),
    ([2, 2, 2, 2, 2, 2, 2, 3, 13], 1, 657),
    ([2, 2, 2, 2, 3, 3, 5, 7], 1, 656),
    ([2, 2, 2, 2, 2, 3, 53], 9, 655),
    ([2, 2, 2, 2, 2, 2, 2, 41], 6, 654),
    ([2, 2, 2, 2, 5, 67], 12, 653),
    ([2, 2, 2, 2, 2, 3, 3, 19], 1, 652),
    ([2, 2, 2, 2, 2, 2, 2, 43], 7, 651),
    ([2, 2, 2, 2, 2, 3, 59], 10, 650),
    ([2, 2, 2, 2, 5, 71], 13, 649),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 5], 1, 648),
    ([2, 2, 2, 2, 2, 2, 7, 13], 1, 647),
    ([2, 2, 2, 2, 5, 73], 14, 646),
    ([2, 2, 2, 2, 2, 3, 61], 11, 645),
    ([2, 2, 2, 2, 2, 2, 2, 47], 8, 644),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], 1, 643),
    ([2, 2, 2, 2, 5, 79], 15, 642),
    ([2, 2, 2, 2, 2, 3, 67], 12, 641),
    ([2, 2, 2, 2, 2, 2, 2, 3, 17], 1, 640),
    ([2, 2, 2, 2, 2, 3, 3, 23], 2, 639),
    ([2, 2, 2, 2, 5, 83], 16, 638),
    ([2, 2, 2, 2, 2, 2, 3, 5, 7], 1, 637),
    ([2, 2, 2, 2, 2, 2, 2, 53], 9, 636),
    ([2, 2, 2, 2, 2, 3, 71], 13, 635),
    ([2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], 1, 634),
    ([2, 2, 2, 2, 2, 3, 73], 14, 633),
    ([2, 2, 2, 2, 2, 2, 2, 5, 11], 1, 632),
    ([2, 2, 2, 2, 5, 89], 17, 631),
    ([2, 2, 2, 2, 2, 2, 2, 3, 19], 1, 630),
    ([2, 2, 2, 2, 2, 2, 2, 59], 10, 629)
  ],
  #[
    ([2, 2, 2, 2, 2, 3, 79], 15, 628),
    ([2, 2, 2, 2, 2, 2, 7, 17], 1, 627),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5], 1, 626),
    ([2, 2, 2, 2, 5, 97], 18, 625),
    ([2, 2, 2, 2, 2, 3, 3, 3, 3, 3], 1, 624),
    ([2, 2, 2, 2, 2, 2, 2, 61], 11, 623),
    ([2, 2, 2, 2, 3, 3, 5, 11], 1, 622),
    ([2, 2, 2, 2, 2, 3, 83], 16, 621),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 7], 1, 620),
    ([2, 2, 2, 2, 5, 101], 19, 619),
    ([2, 2, 3, 3, 3, 3, 5, 5], 1, 618),
    ([2, 2, 2, 2, 5, 103], 20, 617),
    ([2, 2, 2, 2, 2, 2, 2, 5, 13], 1, 616),
    ([2, 2, 2, 2, 2, 3, 3, 29], 3, 615),
    ([2, 2, 2, 2, 3, 5, 5, 7], 1, 614),
    ([2, 2, 2, 2, 2, 2, 7, 19], 1, 613),
    ([2, 2, 2, 2, 2, 3, 89], 17, 612),
    ([2, 2, 2, 2, 5, 107], 21, 611),
    ([2, 2, 2, 2, 2, 2, 2, 67], 12, 610),
    ([2, 2, 2, 2, 5, 109], 22, 609),
    ([2, 2, 2, 2, 2, 2, 2, 3, 23], 2, 608),
    ([2, 2, 2, 2, 2, 3, 3, 31], 4, 607),
    ([2, 2, 2, 2, 5, 113], 23, 606),
    ([2, 2, 2, 2, 2, 2, 2, 71], 13, 605),
    ([2, 2, 2, 2, 2, 3, 97], 18, 604),
    ([2, 2, 2, 2, 2, 2, 2, 73], 14, 603),
    ([2, 2, 2, 2, 3, 3, 5, 13], 1, 602),
    ([2, 2, 2, 2, 2, 2, 3, 7, 7], 1, 601),
    ([2, 2, 2, 2, 2, 2, 2, 3, 5, 5], 1, 600),
    ([2, 2, 2, 2, 2, 3, 101], 19, 599),
    ([2, 2, 2, 2, 2, 2, 2, 7, 11], 1, 598),
    ([2, 2, 2, 2, 2, 3, 103], 20, 597)
  ],
  #[
    ([2, 2, 2, 2, 5, 5, 5, 5], 1, 596),
    ([2, 2, 2, 2, 2, 3, 3, 5, 7], 1, 595),
    ([2, 2, 2, 2, 2, 2, 2, 79], 15, 594),
    ([2, 2, 2, 2, 5, 127], 24, 593),
    ([2, 2, 2, 2, 2, 3, 107], 21, 592),
    ([2, 2, 2, 2, 2, 2, 7, 23], 2, 591),
    ([2, 2, 2, 2, 2, 3, 109], 22, 590),
    ([2, 2, 2, 2, 5, 131], 25, 589),
    ([2, 2, 2, 2, 2, 2, 2, 83], 16, 588),
    ([2, 2, 2, 2, 2, 3, 3, 37], 5, 587),
    ([2, 2, 2, 2, 3, 3, 3, 5, 5], 1, 586),
    ([2, 2, 2, 2, 2, 3, 113], 23, 585),
    ([2, 2, 2, 2, 2, 2, 2, 5, 17], 1, 584),
    ([2, 2, 2, 2, 5, 137], 29, 583),
    ([2, 2, 2, 2, 5, 139], 31, 582),
    ([2, 2, 2, 2, 2, 2, 2, 3, 29], 3, 581),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 11], 1, 580),
    ([2, 2, 2, 2, 2, 2, 2, 89], 17, 579),
    ([2, 2, 2, 2, 2, 2, 2, 7, 13], 1, 578),
    ([2, 2, 2, 2, 3, 5, 7, 7], 1, 577),
    ([2, 2, 2, 2, 2, 3, 3, 41], 6, 576),
    ([2, 2, 2, 2, 2, 2, 2, 3, 31], 4, 575),
    ([2, 2, 2, 2, 5, 149], 37, 574),
    ([2, 2, 2, 2, 5, 151], 39, 573),
    ([2, 2, 2, 2, 2, 2, 3, 3, 3, 7], 1, 572),
    ([2, 2, 2, 2, 2, 2, 2, 5, 19], 1, 571),
    ([2, 2, 2, 2, 2, 3, 127], 24, 570),
    ([2, 2, 2, 2, 3, 3, 5, 17], 1, 569),
    ([2, 2, 2, 2, 2, 3, 3, 43], 7, 568),
    ([2, 2, 2, 2, 2, 2, 2, 97], 18, 567),
    ([2, 2, 2, 2, 5, 157], 44, 566),
    ([2, 2, 2, 2, 2, 3, 131], 25, 565)
  ],
  #[
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 11], 1, 564),
    ([2, 2, 2, 2, 2, 2, 2, 101], 19, 563),
    ([2, 2, 2, 2, 2, 3, 3, 3, 3, 5], 1, 562),
    ([2, 2, 2, 2, 2, 2, 7, 29], 3, 561),
    ([2, 2, 2, 2, 5, 163], 47, 560),
    ([2, 2, 2, 2, 2, 3, 137], 29, 559),
    ([2, 2, 2, 2, 2, 2, 2, 103], 20, 558),
    ([2, 2, 2, 2, 3, 5, 5, 11], 1, 557),
    ([2, 2, 2, 2, 2, 3, 139], 31, 556),
    ([2, 2, 2, 2, 5, 167], 49, 555),
    ([2, 2, 2, 2, 2, 3, 3, 47], 8, 554),
    ([2, 2, 2, 2, 3, 3, 5, 19], 1, 553),
    ([2, 2, 2, 2, 2, 2, 2, 107], 21, 552),
    ([2, 2, 2, 2, 5, 173], 53, 551),
    ([2, 2, 2, 2, 2, 2, 7, 31], 4, 550),
    ([2, 2, 2, 2, 2, 2, 2, 109], 22, 549),
    ([2, 2, 2, 2, 2, 2, 2, 3, 37], 5, 548),
    ([2, 2, 2, 2, 2, 3, 149], 37, 547),
    ([2, 2, 2, 2, 5, 179], 57, 546),
    ([2, 2, 2, 2, 2, 2, 2, 113], 23, 545),
    ([2, 2, 2, 2, 5, 181], 59, 544),
    ([2, 2, 2, 2, 2, 3, 151], 39, 543),
    ([2, 2, 2, 2, 2, 2, 2, 5, 23], 2, 542),
    ([2, 2, 2, 2, 2, 2, 3, 7, 11], 1, 541),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 13], 1, 540),
    ([2, 2, 2, 2, 2, 3, 157], 44, 539),
    ([2, 2, 2, 2, 2, 2, 2, 7, 17], 1, 538),
    ([2, 2, 2, 2, 2, 3, 3, 53], 9, 537),
    ([2, 2, 2, 2, 5, 191], 65, 536),
    ([2, 2, 2, 2, 5, 193], 67, 535),
    ([2, 2, 2, 2, 3, 5, 5, 13], 1, 534),
    ([2, 2, 2, 2, 2, 3, 163], 47, 533)
  ],
  #[
    ([2, 2, 2, 2, 2, 2, 2, 3, 41], 6, 532),
    ([2, 2, 2, 2, 5, 197], 69, 531),
    ([2, 2, 2, 2, 2, 3, 3, 5, 11], 1, 530),
    ([2, 2, 2, 2, 5, 199], 71, 529),
    ([2, 2, 2, 2, 2, 2, 2, 5, 5, 5], 1, 528),
    ([2, 2, 2, 2, 2, 3, 167], 49, 527),
    ([2, 2, 2, 2, 2, 2, 2, 127], 24, 526),
    ([2, 2, 2, 2, 2, 2, 2, 3, 43], 7, 525),
    ([2, 2, 2, 2, 3, 3, 5, 23], 2, 524),
    ([2, 2, 2, 2, 2, 2, 7, 37], 5, 523),
    ([2, 2, 2, 2, 2, 3, 173], 53, 522),
    ([2, 2, 2, 2, 2, 2, 2, 131], 25, 521),
    ([2, 2, 2, 2, 5, 211], 78, 520),
    ([2, 2, 2, 2, 2, 3, 3, 59], 10, 519),
    ([2, 2, 2, 2, 2, 2, 2, 7, 19], 1, 518),
    ([2, 2, 2, 2, 2, 3, 179], 57, 517),
    ([2, 2, 2, 2, 2, 3, 181], 59, 516),
    ([2, 2, 2, 2, 2, 2, 3, 7, 13], 1, 515),
    ([2, 2, 2, 2, 2, 2, 2, 137], 29, 514),
    ([2, 2, 2, 2, 2, 3, 3, 61], 11, 513),
    ([2, 2, 2, 2, 2, 2, 2, 139], 31, 512),
    ([2, 2, 2, 2, 5, 223], 87, 511),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 7], 1, 510),
    ([2, 2, 2, 2, 3, 3, 5, 5, 5], 1, 509),
    ([2, 2, 2, 2, 2, 2, 2, 3, 47], 8, 508),
    ([2, 2, 2, 2, 5, 227], 91, 507),
    ([2, 2, 2, 2, 2, 2, 2, 11, 13], 1, 506),
    ([2, 2, 2, 2, 5, 229], 93, 505),
    ([2, 2, 2, 2, 2, 3, 191], 65, 504),
    ([2, 2, 2, 2, 2, 2, 7, 41], 6, 503),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3], 1, 502),
    ([2, 2, 2, 2, 2, 3, 193], 67, 501)
  ],
  #[
    ([2, 2, 2, 2, 2, 2, 2, 5, 29], 3, 500),
    ([2, 2, 2, 2, 5, 233], 97, 499),
    ([2, 2, 2, 2, 2, 3, 3, 5, 13], 1, 498),
    ([2, 2, 2, 2, 2, 2, 2, 3, 7, 7], 1, 497),
    ([2, 2, 2, 2, 2, 3, 197], 69, 496),
    ([2, 2, 2, 2, 2, 2, 2, 149], 37, 495),
    ([2, 2, 2, 2, 2, 3, 199], 71, 494),
    ([2, 2, 2, 2, 5, 239], 102, 494),
    ([2, 2, 2, 2, 2, 2, 7, 43], 7, 493),
    ([2, 2, 2, 2, 5, 241], 104, 492),
    ([2, 2, 2, 2, 2, 3, 3, 67], 12, 491),
    ([2, 2, 2, 2, 2, 2, 2, 151], 39, 490),
    ([2, 2, 2, 2, 3, 3, 3, 3, 3, 5], 1, 489),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 17], 1, 488),
    ([2, 2, 2, 2, 2, 2, 2, 5, 31], 4, 487),
    ([2, 2, 2, 2, 5, 251], 109, 486),
    ([2, 2, 2, 2, 2, 2, 2, 157], 44, 485),
    ([2, 2, 2, 2, 2, 2, 3, 3, 5, 7], 1, 484),
    ([2, 2, 2, 2, 2, 3, 211], 78, 483),
    ([2, 2, 2, 2, 2, 2, 2, 3, 53], 9, 482),
    ([2, 2, 2, 2, 3, 5, 5, 17], 1, 481),
    ([2, 2, 2, 2, 2, 3, 3, 71], 13, 480),
    ([2, 2, 2, 2, 5, 257], 113, 479),
    ([2, 2, 2, 2, 2, 2, 2, 7, 23], 2, 478),
    ([2, 2, 2, 2, 2, 2, 2, 163], 47, 477),
    ([2, 2, 2, 2, 3, 3, 5, 29], 3, 476),
    ([2, 2, 2, 2, 2, 3, 3, 73], 14, 475),
    ([2, 2, 2, 2, 5, 263], 117, 474),
    ([2, 2, 2, 2, 2, 2, 7, 47], 8, 473),
    ([2, 2, 2, 2, 2, 2, 2, 167], 49, 472),
    ([2, 2, 2, 2, 2, 3, 223], 87, 471),
    ([2, 2, 2, 2, 5, 269], 121, 470)
  ],
  #[
    ([2, 2, 2, 2, 2, 3, 3, 3, 5, 5], 1, 469),
    ([2, 2, 2, 2, 5, 271], 123, 468),
    ([2, 2, 2, 2, 2, 3, 227], 91, 467),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 19], 1, 466),
    ([2, 2, 2, 2, 2, 2, 7, 7, 7], 1, 465),
    ([2, 2, 2, 2, 2, 3, 229], 93, 464),
    ([2, 2, 2, 2, 2, 2, 2, 173], 53, 463),
    ([2, 2, 2, 2, 5, 277], 126, 462),
    ([2, 2, 2, 2, 2, 3, 3, 7, 11], 1, 461),
    ([2, 2, 2, 2, 3, 3, 5, 31], 4, 460),
    ([2, 2, 2, 2, 2, 3, 233], 97, 459),
    ([2, 2, 2, 2, 5, 281], 129, 458),
    ([2, 2, 3, 3, 5, 5, 5, 5], 1, 457),
    ([2, 2, 2, 2, 5, 283], 131, 456),
    ([2, 2, 2, 2, 2, 2, 2, 3, 59], 10, 455),
    ([2, 2, 2, 2, 2, 3, 3, 79], 15, 454),
    ([2, 2, 2, 2, 3, 5, 5, 19], 1, 453),
    ([2, 2, 2, 2, 2, 2, 3, 7, 17], 1, 452),
    ([2, 2, 2, 2, 2, 2, 2, 179], 57, 451),
    ([2, 2, 2, 2, 2, 3, 239], 102, 450),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5], 1, 449),
    ([2, 2, 2, 2, 2, 3, 241], 104, 448),
    ([2, 2, 2, 2, 2, 2, 2, 181], 59, 447),
    ([2, 2, 2, 2, 2, 2, 2, 3, 61], 11, 446),
    ([2, 2, 2, 2, 5, 293], 139, 446),
    ([2, 2, 2, 2, 2, 2, 2, 5, 37], 5, 445),
    ([2, 2, 2, 2, 2, 2, 7, 53], 9, 444),
    ([2, 2, 2, 2, 2, 3, 3, 83], 16, 443),
    ([2, 2, 2, 2, 2, 2, 2, 11, 17], 1, 442),
    ([2, 2, 2, 2, 2, 3, 251], 109, 441),
    ([2, 2, 2, 2, 2, 2, 2, 191], 65, 440),
    ([2, 2, 2, 2, 2, 3, 3, 5, 17], 1, 439)
  ],
  #[
    ([2, 2, 2, 2, 5, 307], 151, 438),
    ([2, 2, 2, 2, 2, 2, 5, 7, 11], 1, 437),
    ([2, 2, 2, 2, 2, 3, 257], 113, 436),
    ([2, 2, 2, 2, 2, 2, 2, 193], 67, 435),
    ([2, 2, 2, 2, 5, 311], 155, 434),
    ([2, 2, 2, 2, 5, 313], 157, 433),
    ([2, 2, 2, 2, 3, 3, 5, 5, 7], 1, 432),
    ([2, 2, 2, 2, 2, 2, 2, 197], 69, 432),
    ([2, 2, 2, 2, 2, 3, 263], 117, 431),
    ([2, 2, 2, 2, 5, 317], 161, 430),
    ([2, 2, 2, 2, 2, 2, 2, 199], 71, 429),
    ([2, 2, 2, 2, 2, 2, 3, 7, 19], 1, 428),
    ([2, 2, 2, 2, 2, 3, 3, 89], 17, 427),
    ([2, 2, 2, 2, 2, 2, 2, 3, 67], 12, 426),
    ([2, 2, 2, 2, 2, 3, 269], 121, 425),
    ([2, 2, 2, 2, 2, 2, 2, 7, 29], 3, 424),
    ([2, 2, 2, 2, 2, 3, 271], 123, 423),
    ([2, 2, 2, 2, 2, 3, 3, 7, 13], 1, 422),
    ([2, 2, 2, 2, 2, 2, 2, 5, 41], 6, 421),
    ([2, 2, 3, 3, 3, 3, 3, 3, 3, 3], 1, 421),
    ([2, 2, 2, 2, 2, 2, 7, 59], 10, 420),
    ([2, 2, 2, 2, 5, 331], 175, 419),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 23], 2, 418),
    ([2, 2, 2, 2, 2, 3, 277], 126, 417),
    ([2, 2, 2, 2, 3, 3, 5, 37], 5, 416),
    ([2, 2, 2, 2, 2, 2, 2, 11, 19], 1, 415),
    ([2, 2, 2, 2, 5, 337], 180, 414),
    ([2, 2, 2, 2, 2, 3, 281], 129, 414),
    ([2, 2, 2, 2, 2, 2, 2, 211], 78, 413),
    ([2, 2, 2, 2, 2, 3, 283], 131, 412),
    ([2, 2, 2, 2, 2, 2, 2, 3, 71], 13, 411),
    ([2, 2, 2, 2, 2, 2, 7, 61], 11, 410)
  ],
  #[
    ([2, 2, 2, 2, 2, 3, 3, 5, 19], 1, 409),
    ([2, 2, 2, 2, 2, 2, 2, 5, 43], 7, 408),
    ([2, 2, 2, 2, 3, 5, 5, 23], 2, 407),
    ([2, 2, 2, 2, 5, 347], 189, 406),
    ([2, 2, 2, 2, 2, 2, 2, 7, 31], 4, 406),
    ([2, 2, 2, 2, 5, 349], 191, 405),
    ([2, 2, 2, 2, 2, 3, 3, 97], 18, 404),
    ([2, 2, 2, 2, 2, 2, 2, 3, 73], 14, 403),
    ([2, 2, 2, 2, 2, 3, 293], 139, 402),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 11], 1, 401),
    ([2, 2, 2, 2, 2, 2, 3, 3, 7, 7], 1, 400),
    ([2, 2, 2, 2, 5, 353], 194, 400),
    ([2, 2, 2, 2, 2, 2, 2, 13, 17], 1, 399),
    ([2, 2, 2, 2, 2, 2, 2, 223], 87, 398),
    ([2, 2, 2, 2, 5, 359], 199, 397),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 5], 1, 396),
    ([2, 2, 2, 2, 3, 5, 11, 11], 1, 395),
    ([2, 2, 2, 2, 2, 2, 2, 227], 91, 395),
    ([2, 2, 2, 2, 2, 3, 3, 101], 19, 394),
    ([2, 2, 2, 2, 2, 2, 5, 7, 13], 1, 393),
    ([2, 2, 2, 2, 2, 2, 2, 229], 93, 392),
    ([2, 2, 2, 2, 5, 367], 207, 391),
    ([2, 2, 2, 2, 2, 3, 307], 151, 390),
    ([2, 2, 2, 2, 3, 3, 5, 41], 6, 389),
    ([2, 2, 2, 2, 2, 3, 3, 103], 20, 388),
    ([2, 2, 2, 2, 2, 2, 2, 233], 97, 387),
    ([2, 2, 2, 2, 5, 373], 212, 387),
    ([2, 2, 2, 2, 2, 3, 311], 155, 386),
    ([2, 2, 2, 2, 3, 5, 5, 5, 5], 1, 385),
    ([2, 2, 2, 2, 2, 2, 7, 67], 12, 385),
    ([2, 2, 2, 2, 2, 3, 313], 157, 384),
    ([2, 2, 2, 2, 2, 2, 2, 5, 47], 8, 383)
  ],
  #[
    ([2, 2, 2, 2, 5, 379], 217, 382),
    ([2, 2, 2, 2, 2, 2, 2, 3, 79], 15, 382),
    ([2, 2, 2, 2, 2, 3, 317], 161, 381),
    ([2, 2, 2, 2, 2, 2, 2, 239], 102, 380),
    ([2, 2, 2, 2, 5, 383], 221, 379),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5], 1, 378),
    ([2, 2, 2, 2, 2, 3, 3, 107], 21, 377),
    ([2, 2, 2, 2, 2, 2, 2, 241], 104, 376),
    ([2, 2, 2, 2, 2, 2, 3, 7, 23], 2, 375),
    ([2, 2, 2, 2, 3, 3, 5, 43], 7, 374),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3], 1, 373),
    ([2, 2, 2, 2, 2, 3, 3, 109], 22, 371),
    ([2, 2, 2, 2, 2, 2, 2, 13, 19], 1, 370),
    ([2, 2, 2, 2, 2, 3, 331], 175, 369),
    ([2, 2, 2, 2, 2, 2, 7, 71], 13, 368),
    ([2, 2, 2, 2, 2, 2, 2, 3, 83], 16, 367),
    ([2, 2, 2, 2, 2, 2, 2, 251], 109, 365),
    ([2, 2, 2, 2, 2, 3, 337], 180, 364),
    ([2, 2, 2, 2, 2, 2, 2, 11, 23], 2, 363),
    ([2, 2, 2, 2, 3, 3, 3, 3, 5, 5], 1, 363),
    ([2, 2, 2, 2, 2, 3, 3, 113], 23, 362),
    ([2, 2, 2, 2, 2, 2, 7, 73], 14, 361),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], 1, 360),
    ([2, 2, 2, 2, 2, 2, 2, 257], 113, 359),
    ([2, 2, 2, 2, 2, 3, 3, 5, 23], 2, 358),
    ([2, 2, 2, 2, 2, 2, 2, 7, 37], 5, 358),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 13], 1, 357),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 29], 3, 356),
    ([2, 2, 2, 2, 2, 2, 3, 5, 5, 7], 1, 354),
    ([2, 2, 2, 2, 2, 2, 2, 263], 117, 353),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 11], 1, 351),
    ([2, 2, 2, 2, 3, 3, 5, 47], 8, 351)
  ],
  #[
    ([2, 2, 2, 2, 2, 2, 2, 5, 53], 9, 349),
    ([2, 2, 2, 2, 2, 2, 2, 3, 89], 17, 348),
    ([2, 2, 2, 2, 2, 3, 3, 7, 17], 1, 347),
    ([2, 2, 2, 2, 2, 2, 2, 269], 121, 346),
    ([2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5], 1, 345),
    ([2, 2, 2, 2, 2, 2, 2, 271], 123, 343),
    ([2, 2, 2, 2, 3, 5, 5, 29], 3, 342),
    ([2, 2, 2, 2, 3, 3, 5, 7, 7], 1, 339),
    ([2, 2, 2, 2, 2, 2, 7, 79], 15, 338),
    ([2, 2, 2, 2, 2, 2, 2, 277], 126, 337),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 31], 4, 336),
    ([2, 2, 2, 2, 2, 2, 2, 281], 129, 334),
    ([2, 2, 2, 2, 2, 3, 3, 5, 5, 5], 1, 333),
    ([2, 2, 2, 2, 2, 2, 2, 283], 131, 332),
    ([2, 2, 2, 2, 2, 3, 3, 127], 24, 329),
    ([2, 2, 2, 2, 2, 2, 2, 7, 41], 6, 328),
    ([2, 2, 2, 2, 2, 2, 7, 83], 16, 324),
    ([2, 2, 2, 2, 3, 5, 5, 31], 4, 324),
    ([2, 2, 2, 2, 2, 2, 2, 3, 97], 18, 323),
    ([2, 2, 2, 2, 2, 3, 3, 131], 25, 320),
    ([2, 2, 2, 2, 2, 2, 2, 5, 59], 10, 319),
    ([2, 2, 2, 2, 2, 2, 5, 7, 17], 1, 317),
    ([2, 2, 2, 2, 3, 3, 5, 53], 9, 316),
    ([2, 2, 2, 2, 2, 2, 2, 13, 23], 2, 315),
    ([2, 2, 2, 2, 2, 3, 3, 7, 19], 1, 315),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5], 1, 313),
    ([2, 2, 2, 2, 2, 2, 2, 7, 43], 7, 312),
    ([2, 2, 2, 2, 2, 2, 2, 3, 101], 19, 311),
    ([2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5], 1, 310),
    ([2, 2, 2, 2, 2, 2, 3, 7, 29], 3, 309),
    ([2, 2, 2, 2, 2, 2, 2, 5, 61], 11, 308),
    ([2, 2, 2, 2, 2, 3, 3, 137], 29, 305)
  ],
  #[
    ([2, 2, 2, 2, 2, 2, 2, 3, 103], 20, 304),
    ([2, 2, 2, 2, 3, 3, 5, 5, 11], 1, 304),
    ([2, 2, 2, 2, 2, 2, 7, 89], 17, 302),
    ([2, 2, 2, 2, 2, 3, 3, 139], 31, 301),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 7], 1, 299),
    ([2, 2, 2, 2, 3, 5, 13, 13], 1, 297),
    ([2, 2, 2, 2, 2, 2, 2, 11, 29], 3, 294),
    ([2, 2, 2, 2, 2, 2, 2, 3, 107], 21, 293),
    ([2, 2, 2, 2, 2, 3, 3, 11, 13], 1, 292),
    ([2, 2, 2, 2, 2, 2, 2, 17, 19], 1, 291),
    ([2, 2, 2, 2, 2, 2, 3, 7, 31], 4, 289),
    ([2, 2, 2, 2, 2, 3, 3, 5, 29], 3, 287),
    ([2, 2, 2, 2, 2, 2, 2, 3, 109], 22, 286),
    ([2, 2, 2, 2, 2, 2, 2, 7, 47], 8, 285),
    ([2, 2, 2, 2, 2, 3, 3, 3, 7, 7], 1, 284),
    ([2, 2, 2, 2, 3, 3, 5, 59], 10, 283),
    ([2, 2, 2, 2, 2, 2, 5, 7, 19], 1, 282),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 37], 5, 282),
    ([2, 2, 2, 2, 2, 2, 2, 5, 67], 12, 281),
    ([2, 2, 2, 2, 2, 3, 3, 149], 37, 281),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 7], 1, 280),
    ([2, 2, 2, 2, 2, 2, 2, 3, 113], 23, 277),
    ([2, 2, 2, 2, 2, 2, 7, 97], 18, 277),
    ([2, 2, 2, 2, 2, 3, 3, 151], 39, 276),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 17], 1, 276),
    ([2, 2, 2, 2, 2, 2, 2, 11, 31], 4, 275),
    ([2, 2, 2, 2, 2, 2, 2, 7, 7, 7], 1, 273),
    ([2, 2, 2, 2, 3, 3, 5, 61], 11, 273),
    ([2, 2, 2, 2, 2, 2, 3, 3, 7, 11], 1, 271),
    ([2, 2, 2, 2, 3, 5, 5, 37], 5, 271),
    ([2, 2, 2, 2, 2, 3, 3, 5, 31], 4, 269),
    ([2, 2, 2, 2, 2, 3, 3, 157], 44, 265)
  ],
  #[
    ([2, 2, 2, 2, 2, 2, 7, 101], 19, 265),
    ([2, 2, 2, 2, 2, 2, 2, 5, 71], 13, 264),
    ([2, 2, 2, 2, 2, 2, 7, 103], 20, 259),
    ([2, 2, 2, 2, 2, 3, 3, 7, 23], 2, 258),
    ([2, 2, 2, 2, 2, 2, 2, 3, 11, 11], 1, 257),
    ([2, 2, 2, 2, 2, 2, 2, 5, 73], 14, 256),
    ([2, 2, 2, 2, 3, 3, 5, 5, 13], 1, 255),
    ([2, 2, 2, 2, 2, 3, 3, 163], 47, 254),
    ([2, 2, 2, 2, 2, 2, 3, 5, 7, 7], 1, 253),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 41], 6, 251),
    ([2, 2, 2, 2, 2, 2, 2, 7, 53], 9, 250),
    ([2, 2, 2, 2, 2, 2, 7, 107], 21, 248),
    ([2, 2, 2, 2, 2, 3, 3, 167], 49, 247),
    ([2, 2, 2, 2, 3, 3, 5, 67], 12, 246),
    ([2, 2, 2, 2, 2, 2, 2, 13, 29], 3, 246),
    ([2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 7], 1, 245),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 19], 1, 243),
    ([2, 2, 2, 2, 2, 2, 2, 3, 127], 24, 242),
    ([2, 2, 2, 2, 2, 2, 7, 109], 22, 241),
    ([2, 2, 2, 2, 3, 5, 5, 41], 6, 239),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 43], 7, 237),
    ([2, 2, 2, 2, 2, 2, 3, 7, 37], 5, 236),
    ([2, 2, 2, 2, 2, 3, 3, 173], 53, 235),
    ([2, 2, 2, 2, 2, 2, 2, 17, 23], 2, 234),
    ([2, 2, 2, 2, 2, 2, 2, 3, 131], 25, 232),
    ([2, 2, 2, 2, 2, 2, 2, 5, 79], 15, 230),
    ([2, 2, 2, 2, 2, 2, 7, 113], 23, 230),
    ([2, 2, 2, 2, 3, 3, 5, 71], 13, 228),
    ([2, 2, 2, 2, 2, 2, 5, 7, 23], 2, 225),
    ([2, 2, 2, 2, 2, 2, 2, 13, 31], 4, 224),
    ([2, 2, 2, 2, 3, 5, 5, 43], 7, 224),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5], 1, 222)
  ],
  #[
    ([2, 2, 2, 2, 2, 2, 2, 11, 37], 5, 221),
    ([2, 2, 2, 2, 2, 2, 3, 3, 7, 13], 1, 219),
    ([2, 2, 2, 2, 3, 3, 5, 73], 14, 218),
    ([2, 2, 2, 2, 2, 2, 2, 3, 137], 29, 218),
    ([2, 2, 2, 2, 2, 2, 2, 7, 59], 10, 216),
    ([2, 2, 2, 2, 2, 2, 2, 5, 83], 16, 215),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 13], 1, 214),
    ([2, 2, 2, 2, 2, 3, 3, 5, 37], 5, 214),
    ([2, 2, 2, 2, 2, 2, 2, 3, 139], 31, 213),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 7], 1, 211),
    ([2, 2, 2, 2, 2, 3, 3, 11, 17], 1, 210),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 47], 8, 208),
    ([2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 7], 1, 207),
    ([2, 2, 2, 2, 2, 2, 2, 7, 61], 11, 205),
    ([2, 2, 2, 2, 2, 2, 3, 7, 41], 6, 202),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3], 1, 201),
    ([2, 2, 2, 2, 2, 2, 2, 19, 23], 2, 198),
    ([2, 2, 2, 2, 2, 2, 5, 5, 5, 7], 1, 198),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 11], 1, 196),
    ([2, 2, 2, 2, 3, 5, 5, 47], 8, 195),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 7], 1, 195),
    ([2, 2, 2, 2, 3, 3, 5, 79], 15, 192),
    ([2, 2, 2, 2, 2, 2, 7, 127], 24, 192),
    ([2, 2, 2, 2, 2, 2, 2, 5, 89], 17, 192),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7], 1, 190),
    ([2, 2, 2, 2, 2, 2, 2, 11, 41], 6, 188),
    ([2, 2, 2, 2, 2, 2, 3, 7, 43], 7, 188),
    ([2, 2, 2, 2, 2, 3, 3, 7, 29], 3, 185),
    ([2, 2, 2, 2, 2, 2, 7, 131], 25, 183),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 23], 2, 182),
    ([2, 2, 2, 2, 2, 3, 3, 5, 41], 6, 181),
    ([2, 2, 2, 2, 3, 3, 5, 83], 16, 178)
  ],
  #[
    ([2, 2, 2, 2, 2, 3, 5, 5, 5, 5], 1, 177),
    ([2, 2, 2, 2, 2, 2, 2, 7, 67], 12, 177),
    ([2, 2, 2, 2, 2, 3, 3, 11, 19], 1, 176),
    ([2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 7], 1, 174),
    ([2, 2, 2, 2, 2, 2, 2, 11, 43], 7, 174),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 53], 9, 171),
    ([2, 2, 2, 2, 3, 3, 5, 5, 17], 1, 170),
    ([2, 2, 2, 2, 2, 2, 2, 13, 37], 5, 168),
    ([2, 2, 2, 2, 2, 3, 3, 5, 43], 7, 166),
    ([2, 2, 2, 2, 2, 2, 2, 5, 97], 18, 166),
    ([2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3], 1, 165),
    ([2, 2, 2, 2, 2, 3, 3, 7, 31], 4, 164),
    ([2, 2, 2, 2, 2, 2, 2, 17, 29], 3, 160),
    ([2, 2, 2, 2, 2, 2, 3, 7, 47], 8, 160),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 11], 1, 159),
    ([2, 2, 2, 2, 3, 5, 5, 53], 9, 158),
    ([2, 2, 2, 2, 2, 2, 2, 7, 71], 13, 158),
    ([2, 2, 2, 2, 2, 3, 3, 13, 17], 1, 158),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 5, 5], 1, 156),
    ([2, 2, 2, 2, 2, 2, 7, 11, 13], 1, 156),
    ([2, 2, 2, 2, 3, 3, 5, 89], 17, 156),
    ([2, 2, 2, 2, 2, 2, 2, 5, 101], 19, 153),
    ([2, 2, 2, 2, 2, 3, 3, 3, 3, 5, 5], 1, 152),
    ([2, 2, 2, 2, 2, 2, 2, 3, 13, 13], 1, 152),
    ([2, 2, 2, 2, 2, 2, 5, 7, 29], 3, 151),
    ([2, 2, 2, 2, 2, 2, 2, 7, 73], 14, 149),
    ([2, 2, 2, 2, 2, 2, 3, 7, 7, 7], 1, 147),
    ([2, 2, 2, 2, 2, 2, 2, 5, 103], 20, 147),
    ([2, 2, 2, 2, 2, 2, 2, 11, 47], 8, 146),
    ([2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 7], 1, 143),
    ([2, 2, 2, 2, 2, 2, 2, 17, 31], 4, 142),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 11], 1, 141)
  ],
  #[
    ([2, 2, 2, 2, 2, 3, 3, 5, 47], 8, 141),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 59], 10, 140),
    ([2, 2, 2, 2, 2, 2, 2, 13, 41], 6, 139),
    ([2, 2, 2, 2, 3, 3, 5, 5, 19], 1, 138),
    ([2, 2, 2, 2, 2, 2, 3, 3, 7, 17], 1, 137),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5], 1, 136),
    ([2, 2, 2, 2, 3, 5, 17, 17], 1, 135),
    ([2, 2, 2, 2, 2, 2, 5, 7, 31], 4, 135),
    ([2, 2, 2, 2, 3, 3, 5, 97], 18, 134),
    ([2, 2, 2, 2, 5, 5, 5, 5, 7], 1, 133),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 61], 11, 132),
    ([2, 2, 2, 2, 2, 2, 2, 19, 29], 3, 131),
    ([2, 2, 2, 2, 2, 2, 2, 7, 79], 15, 130),
    ([2, 2, 2, 2, 3, 5, 5, 59], 10, 130),
    ([2, 2, 2, 2, 2, 3, 3, 13, 19], 1, 129),
    ([2, 2, 2, 2, 2, 2, 3, 7, 53], 9, 128),
    ([2, 2, 2, 2, 2, 2, 2, 13, 43], 7, 127),
    ([2, 2, 2, 2, 2, 3, 3, 11, 23], 2, 125),
    ([2, 2, 2, 2, 3, 5, 5, 61], 11, 124),
    ([2, 2, 2, 2, 2, 2, 3, 5, 7, 11], 1, 122),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 29], 3, 121),
    ([2, 2, 2, 2, 2, 2, 2, 7, 83], 16, 120),
    ([2, 2, 2, 2, 2, 3, 3, 7, 37], 5, 120),
    ([2, 2, 2, 2, 2, 2, 2, 11, 53], 9, 120),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 13], 1, 119),
    ([2, 2, 2, 2, 2, 2, 2, 19, 31], 4, 118),
    ([2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 11], 1, 117),
    ([2, 2, 2, 2, 2, 3, 3, 5, 53], 9, 116),
    ([2, 2, 2, 2, 2, 2, 3, 3, 7, 19], 1, 115),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 67], 12, 114),
    ([2, 2, 2, 2, 2, 2, 2, 13, 47], 8, 112),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 7, 11], 1, 111)
  ],
  #[
    ([2, 2, 2, 2, 2, 2, 3, 7, 59], 10, 110),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 31], 4, 110),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 13], 1, 108),
    ([2, 2, 2, 2, 2, 2, 2, 5, 5, 5, 5], 1, 108),
    ([2, 2, 2, 2, 3, 5, 5, 67], 12, 107),
    ([2, 2, 2, 2, 2, 2, 2, 17, 37], 5, 107),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 71], 13, 106),
    ([2, 2, 2, 2, 2, 2, 3, 7, 61], 11, 105),
    ([2, 2, 2, 2, 2, 3, 3, 7, 41], 6, 104),
    ([2, 2, 2, 2, 3, 3, 5, 5, 23], 2, 104),
    ([2, 2, 2, 2, 2, 2, 5, 7, 37], 5, 104),
    ([2, 2, 2, 2, 2, 2, 2, 11, 59], 10, 103),
    ([2, 2, 2, 2, 2, 2, 7, 11, 17], 1, 101),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 11], 1, 100),
    ([2, 2, 2, 2, 2, 2, 3, 3, 3, 7, 7], 1, 100),
    ([2, 2, 2, 2, 2, 3, 3, 5, 59], 10, 99),
    ([2, 2, 2, 2, 3, 5, 5, 71], 13, 98),
    ([2, 2, 2, 2, 2, 2, 2, 23, 29], 3, 98),
    ([2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 11], 1, 97),
    ([2, 2, 2, 2, 2, 2, 2, 11, 61], 11, 96),
    ([2, 2, 2, 2, 2, 3, 3, 13, 23], 2, 96),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 5, 5], 1, 95),
    ([2, 2, 2, 2, 3, 5, 19, 19], 1, 94),
    ([2, 2, 2, 2, 2, 3, 3, 7, 43], 7, 94),
    ([2, 2, 2, 2, 3, 3, 5, 11, 11], 1, 93),
    ([2, 2, 2, 2, 2, 2, 3, 5, 7, 13], 1, 92),
    ([2, 2, 2, 2, 2, 3, 3, 5, 61], 11, 91),
    ([2, 2, 2, 2, 2, 2, 2, 13, 53], 9, 90),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 11], 1, 89),
    ([2, 2, 2, 2, 2, 2, 2, 17, 41], 6, 88),
    ([2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 13], 1, 86),
    ([2, 2, 2, 2, 2, 2, 2, 19, 37], 5, 86)
  ],
  #[
    ([2, 2, 2, 2, 3, 3, 5, 5, 5, 5], 1, 86),
    ([2, 2, 2, 2, 2, 3, 3, 3, 3, 5, 7], 1, 85),
    ([2, 2, 2, 2, 2, 2, 2, 23, 31], 4, 84),
    ([2, 2, 2, 2, 2, 2, 5, 7, 41], 6, 83),
    ([2, 2, 2, 2, 2, 3, 3, 11, 29], 3, 83),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5], 1, 83),
    ([2, 2, 2, 2, 2, 2, 3, 3, 7, 23], 2, 82),
    ([2, 2, 2, 2, 2, 3, 3, 17, 19], 1, 81),
    ([2, 2, 2, 2, 2, 2, 2, 17, 43], 7, 80),
    ([2, 2, 2, 2, 2, 2, 7, 11, 19], 1, 80),
    ([2, 2, 2, 2, 2, 2, 2, 3, 5, 7, 7], 1, 79),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 37], 5, 78),
    ([2, 2, 2, 2, 2, 3, 3, 7, 47], 8, 78),
    ([2, 2, 2, 2, 2, 2, 5, 7, 43], 7, 77),
    ([2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 5], 1, 76),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 17], 1, 75),
    ([2, 2, 2, 2, 2, 3, 3, 11, 31], 4, 74),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3], 1, 74),
    ([2, 2, 2, 2, 2, 3, 3, 7, 7, 7], 1, 73),
    ([2, 2, 2, 2, 2, 2, 7, 13, 17], 1, 73),
    ([2, 2, 2, 2, 2, 2, 2, 19, 41], 6, 72),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 13], 1, 72),
    ([2, 2, 2, 2, 2, 2, 3, 3, 5, 5, 7], 1, 70),
    ([2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 13], 1, 69),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 11], 1, 69),
    ([2, 2, 2, 2, 2, 2, 2, 17, 47], 8, 68),
    ([2, 2, 2, 2, 2, 2, 3, 7, 7, 11], 1, 67),
    ([2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 5], 1, 66),
    ([2, 2, 2, 2, 3, 3, 5, 5, 29], 3, 65),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 17], 1, 65),
    ([2, 2, 2, 2, 2, 3, 3, 3, 11, 11], 1, 65),
    ([2, 2, 2, 2, 2, 2, 2, 19, 43], 7, 65)
  ],
  #[
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 13], 1, 64),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 5, 41], 6, 64),
    ([2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 11], 1, 63),
    ([2, 2, 2, 2, 2, 3, 3, 13, 29], 3, 62),
    ([2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 7], 1, 61),
    ([2, 2, 2, 2, 2, 2, 2, 23, 37], 5, 61),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 19], 1, 60),
    ([2, 2, 2, 2, 2, 2, 5, 7, 7, 7], 1, 60),
    ([2, 2, 2, 2, 5, 5, 5, 5, 11], 1, 59),
    ([2, 2, 2, 2, 2, 2, 7, 13, 19], 1, 58),
    ([2, 2, 2, 2, 2, 2, 2, 3, 17, 17], 1, 58),
    ([2, 2, 2, 2, 3, 3, 5, 5, 31], 4, 57),
    ([2, 2, 2, 2, 2, 3, 3, 17, 23], 2, 56),
    ([2, 2, 2, 2, 2, 2, 7, 11, 23], 2, 55),
    ([2, 2, 2, 2, 2, 2, 3, 5, 7, 17], 1, 54),
    ([2, 2, 2, 2, 2, 2, 2, 29, 31], 4, 53),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 5], 1, 53),
    ([2, 2, 2, 2, 2, 3, 3, 13, 31], 4, 52),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 19], 1, 51),
    ([2, 2, 2, 2, 2, 2, 3, 3, 7, 29], 3, 51),
    ([2, 2, 2, 2, 2, 3, 3, 11, 37], 5, 50),
    ([2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 17], 1, 50),
    ([2, 2, 2, 2, 3, 3, 5, 13, 13], 1, 48),
    ([2, 2, 2, 2, 2, 2, 3, 7, 7, 13], 1, 47),
    ([2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 13], 1, 46),
    ([2, 2, 2, 2, 2, 3, 3, 19, 23], 2, 45),
    ([2, 2, 2, 2, 3, 5, 23, 23], 2, 44),
    ([2, 2, 2, 2, 2, 2, 3, 5, 7, 19], 1, 43),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7], 1, 42),
    ([2, 2, 2, 2, 5, 5, 5, 5, 13], 1, 41),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 17], 1, 41),
    ([2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 19], 1, 40)
  ],
  #[
    ([2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 17], 1, 39),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 23], 2, 38),
    ([2, 2, 2, 2, 2, 2, 3, 3, 3, 7, 11], 1, 38),
    ([2, 2, 2, 2, 2, 2, 7, 13, 23], 2, 37),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 17], 1, 36),
    ([2, 2, 2, 2, 2, 2, 2, 3, 19, 19], 1, 35),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 11, 11], 1, 34),
    ([2, 2, 2, 2, 2, 2, 3, 3, 5, 7, 7], 1, 33),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 23], 2, 33),
    ([2, 2, 2, 2, 2, 3, 3, 3, 3, 5, 11], 1, 32),
    ([2, 2, 3, 3, 3, 3, 3, 3, 7, 7], 1, 31),
    ([2, 2, 2, 2, 2, 2, 2, 3, 3, 5, 5, 5], 1, 30),
    ([2, 2, 2, 2, 2, 2, 7, 17, 19], 1, 30),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 19], 1, 29),
    ([2, 2, 2, 2, 2, 3, 3, 3, 13, 13], 1, 28),
    ([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 11, 13], 1, 28),
    ([2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 19], 1, 27),
    ([2, 2, 2, 2, 3, 5, 5, 5, 5, 5], 1, 26)
  ]
]

private def groupRowsSize : Nat := 690

private def groupRowsAt (i : Nat) : (List Nat × Nat × Nat) :=
  (groupRowsBlocks[i/32]!)[i%32]!

set_option maxRecDepth 6000 in
private def upperRowsBlocks : Array (Array (Nat × Nat)) := #[
  #[
    (36, 783),
    (80, 745),
    (96, 739),
    (128, 732),
    (240, 723),
    (288, 721),
    (384, 718),
    (448, 717),
    (480, 716),
    (560, 715),
    (640, 714),
    (672, 713),
    (720, 712),
    (864, 711),
    (880, 710),
    (896, 709),
    (1040, 708),
    (1056, 707),
    (1152, 706),
    (1200, 705),
    (1248, 704),
    (1344, 703),
    (1360, 702),
    (1408, 701),
    (1440, 700),
    (1520, 699),
    (1632, 698),
    (1664, 697),
    (1824, 696),
    (1840, 695),
    (1920, 694),
    (2000, 693)
  ],
  #[
    (2016, 692),
    (2176, 691),
    (2208, 690),
    (2240, 689),
    (2320, 688),
    (2432, 687),
    (2480, 686),
    (2560, 685),
    (2688, 684),
    (2784, 683),
    (2944, 682),
    (2960, 681),
    (2976, 680),
    (3168, 679),
    (3280, 678),
    (3440, 677),
    (3456, 676),
    (3552, 675),
    (3600, 674),
    (3712, 673),
    (3744, 672),
    (3760, 671),
    (3936, 670),
    (3968, 669),
    (4032, 668),
    (4128, 667),
    (4224, 666),
    (4240, 665),
    (4480, 664),
    (4512, 663),
    (4720, 662),
    (4736, 661)
  ],
  #[
    (4880, 660),
    (4896, 659),
    (4928, 658),
    (4992, 657),
    (5040, 656),
    (5088, 655),
    (5248, 654),
    (5360, 653),
    (5472, 652),
    (5504, 651),
    (5664, 650),
    (5680, 649),
    (5760, 648),
    (5824, 647),
    (5840, 646),
    (5856, 645),
    (6016, 644),
    (6144, 643),
    (6320, 642),
    (6432, 641),
    (6528, 640),
    (6624, 639),
    (6640, 638),
    (6720, 637),
    (6784, 636),
    (6816, 635),
    (6912, 634),
    (7008, 633),
    (7040, 632),
    (7120, 631),
    (7296, 630),
    (7552, 629)
  ],
  #[
    (7584, 628),
    (7616, 627),
    (7680, 626),
    (7760, 625),
    (7776, 624),
    (7808, 623),
    (7920, 622),
    (7968, 621),
    (8064, 620),
    (8080, 619),
    (8100, 618),
    (8240, 617),
    (8320, 616),
    (8352, 615),
    (8400, 614),
    (8512, 613),
    (8544, 612),
    (8560, 611),
    (8576, 610),
    (8720, 609),
    (8832, 608),
    (8928, 607),
    (9040, 606),
    (9088, 605),
    (9312, 604),
    (9344, 603),
    (9360, 602),
    (9408, 601),
    (9600, 600),
    (9696, 599),
    (9856, 598),
    (9888, 597)
  ],
  #[
    (10000, 596),
    (10080, 595),
    (10112, 594),
    (10160, 593),
    (10272, 592),
    (10304, 591),
    (10464, 590),
    (10480, 589),
    (10624, 588),
    (10656, 587),
    (10800, 586),
    (10848, 585),
    (10880, 584),
    (10960, 583),
    (11120, 582),
    (11136, 581),
    (11264, 580),
    (11392, 579),
    (11648, 578),
    (11760, 577),
    (11808, 576),
    (11904, 575),
    (11920, 574),
    (12080, 573),
    (12096, 572),
    (12160, 571),
    (12192, 570),
    (12240, 569),
    (12384, 568),
    (12416, 567),
    (12560, 566),
    (12576, 565)
  ],
  #[
    (12672, 564),
    (12928, 563),
    (12960, 562),
    (12992, 561),
    (13040, 560),
    (13152, 559),
    (13184, 558),
    (13200, 557),
    (13344, 556),
    (13360, 555),
    (13536, 554),
    (13680, 553),
    (13696, 552),
    (13840, 551),
    (13888, 550),
    (13952, 549),
    (14208, 548),
    (14304, 547),
    (14320, 546),
    (14464, 545),
    (14480, 544),
    (14496, 543),
    (14720, 542),
    (14784, 541),
    (14976, 540),
    (15072, 539),
    (15232, 538),
    (15264, 537),
    (15280, 536),
    (15440, 535),
    (15600, 534),
    (15648, 533)
  ],
  #[
    (15744, 532),
    (15760, 531),
    (15840, 530),
    (15920, 529),
    (16000, 528),
    (16032, 527),
    (16256, 526),
    (16512, 525),
    (16560, 524),
    (16576, 523),
    (16608, 522),
    (16768, 521),
    (16880, 520),
    (16992, 519),
    (17024, 518),
    (17184, 517),
    (17376, 516),
    (17472, 515),
    (17536, 514),
    (17568, 513),
    (17792, 512),
    (17840, 511),
    (17920, 510),
    (18000, 509),
    (18048, 508),
    (18160, 507),
    (18304, 506),
    (18320, 505),
    (18336, 504),
    (18368, 503),
    (18432, 502),
    (18528, 501)
  ],
  #[
    (18560, 500),
    (18640, 499),
    (18720, 498),
    (18816, 497),
    (18912, 496),
    (19072, 495),
    (19104, 494),
    (19120, 494),
    (19264, 493),
    (19280, 492),
    (19296, 491),
    (19328, 490),
    (19440, 489),
    (19584, 488),
    (19840, 487),
    (20080, 486),
    (20096, 485),
    (20160, 484),
    (20256, 483),
    (20352, 482),
    (20400, 481),
    (20448, 480),
    (20560, 479),
    (20608, 478),
    (20864, 477),
    (20880, 476),
    (21024, 475),
    (21040, 474),
    (21056, 473),
    (21376, 472),
    (21408, 471),
    (21520, 470)
  ],
  #[
    (21600, 469),
    (21680, 468),
    (21792, 467),
    (21888, 466),
    (21952, 465),
    (21984, 464),
    (22144, 463),
    (22160, 462),
    (22176, 461),
    (22320, 460),
    (22368, 459),
    (22480, 458),
    (22500, 457),
    (22640, 456),
    (22656, 455),
    (22752, 454),
    (22800, 453),
    (22848, 452),
    (22912, 451),
    (22944, 450),
    (23040, 449),
    (23136, 448),
    (23168, 447),
    (23424, 446),
    (23440, 446),
    (23680, 445),
    (23744, 444),
    (23904, 443),
    (23936, 442),
    (24096, 441),
    (24448, 440),
    (24480, 439)
  ],
  #[
    (24560, 438),
    (24640, 437),
    (24672, 436),
    (24704, 435),
    (24880, 434),
    (25040, 433),
    (25200, 432),
    (25216, 432),
    (25248, 431),
    (25360, 430),
    (25472, 429),
    (25536, 428),
    (25632, 427),
    (25728, 426),
    (25824, 425),
    (25984, 424),
    (26016, 423),
    (26208, 422),
    (26240, 421),
    (26244, 421),
    (26432, 420),
    (26480, 419),
    (26496, 418),
    (26592, 417),
    (26640, 416),
    (26752, 415),
    (26960, 414),
    (26976, 414),
    (27008, 413),
    (27168, 412),
    (27264, 411),
    (27328, 410)
  ],
  #[
    (27360, 409),
    (27520, 408),
    (27600, 407),
    (27760, 406),
    (27776, 406),
    (27920, 405),
    (27936, 404),
    (28032, 403),
    (28128, 402),
    (28160, 401),
    (28224, 400),
    (28240, 400),
    (28288, 399),
    (28544, 398),
    (28720, 397),
    (28800, 396),
    (29040, 395),
    (29056, 395),
    (29088, 394),
    (29120, 393),
    (29312, 392),
    (29360, 391),
    (29472, 390),
    (29520, 389),
    (29664, 388),
    (29824, 387),
    (29840, 387),
    (29856, 386),
    (30000, 385),
    (30016, 385),
    (30048, 384),
    (30080, 383)
  ],
  #[
    (30320, 382),
    (30336, 382),
    (30432, 381),
    (30592, 380),
    (30640, 379),
    (30720, 378),
    (30816, 377),
    (30848, 376),
    (30912, 375),
    (30960, 374),
    (31104, 373),
    (31120, 372),
    (31392, 371),
    (31616, 370),
    (31760, 369),
    (31776, 369),
    (31808, 368),
    (31872, 367),
    (32080, 366),
    (32128, 365),
    (32352, 364),
    (32384, 363),
    (32400, 363),
    (32544, 362),
    (32704, 361),
    (32720, 361),
    (32768, 360),
    (32896, 359),
    (33120, 358),
    (33152, 358),
    (33280, 357),
    (33312, 357)
  ],
  #[
    (33408, 356),
    (33504, 355),
    (33520, 355),
    (33600, 354),
    (33664, 353),
    (33680, 352),
    (33792, 351),
    (33840, 351),
    (33888, 350),
    (33920, 349),
    (34176, 348),
    (34272, 347),
    (34432, 346),
    (34464, 346),
    (34480, 346),
    (34560, 345),
    (34640, 344),
    (34688, 343),
    (34800, 342),
    (35120, 341),
    (35232, 340),
    (35280, 339),
    (35392, 338),
    (35440, 337),
    (35456, 337),
    (35712, 336),
    (35808, 335),
    (35920, 334),
    (35968, 334),
    (36000, 333),
    (36224, 332),
    (36384, 331)
  ],
  #[
    (36560, 330),
    (36576, 329),
    (36736, 328),
    (36768, 327),
    (36880, 326),
    (37040, 325),
    (37184, 324),
    (37200, 324),
    (37248, 323),
    (37344, 322),
    (37360, 322),
    (37504, 321),
    (37728, 320),
    (37760, 319),
    (38080, 317),
    (38112, 316),
    (38160, 316),
    (38272, 315),
    (38304, 315),
    (38320, 314),
    (38400, 313),
    (38496, 312),
    (38528, 312),
    (38784, 311),
    (38880, 310),
    (38960, 309),
    (38976, 309),
    (39040, 308),
    (39264, 307),
    (39280, 307),
    (39296, 306),
    (39456, 305)
  ],
  #[
    (39552, 304),
    (39600, 304),
    (39808, 303),
    (39872, 302),
    (39920, 302),
    (40032, 301),
    (40064, 301),
    (40224, 300),
    (40240, 300),
    (40320, 299),
    (40416, 298),
    (40560, 297),
    (40576, 296),
    (40720, 295),
    (40832, 294),
    (41088, 293),
    (41184, 292),
    (41344, 291),
    (41376, 291),
    (41568, 290),
    (41664, 289),
    (41680, 288),
    (41760, 287),
    (41840, 287),
    (41856, 286),
    (42112, 285),
    (42144, 285),
    (42336, 284),
    (42368, 284),
    (42480, 283),
    (42528, 283),
    (42560, 282)
  ],
  #[
    (42624, 282),
    (42880, 281),
    (42912, 281),
    (43008, 280),
    (43104, 279),
    (43136, 279),
    (43280, 278),
    (43392, 277),
    (43456, 277),
    (43488, 276),
    (43520, 276),
    (43648, 275),
    (43760, 274),
    (43872, 273),
    (43904, 273),
    (43920, 273),
    (44256, 272),
    (44352, 271),
    (44400, 271),
    (44416, 271),
    (44448, 270),
    (44560, 269),
    (44640, 269),
    (44672, 268),
    (44832, 267),
    (45040, 266),
    (45184, 265),
    (45216, 265),
    (45248, 265),
    (45440, 264),
    (45520, 263),
    (45680, 262)
  ],
  #[
    (45952, 261),
    (45984, 260),
    (46144, 259),
    (46160, 259),
    (46368, 258),
    (46464, 257),
    (46720, 256),
    (46752, 255),
    (46800, 255),
    (46944, 254),
    (46960, 253),
    (46976, 253),
    (47040, 253),
    (47136, 252),
    (47232, 251),
    (47440, 250),
    (47488, 250),
    (47744, 249),
    (47904, 248),
    (47920, 248),
    (47936, 248),
    (48080, 247),
    (48096, 247),
    (48240, 246),
    (48256, 246),
    (48288, 246),
    (48384, 245),
    (48512, 244),
    (48560, 243),
    (48640, 243),
    (48768, 242),
    (48832, 241)
  ],
  #[
    (48864, 241),
    (49024, 240),
    (49040, 240),
    (49200, 239),
    (49360, 238),
    (49520, 237),
    (49536, 237),
    (49728, 236),
    (49792, 235),
    (49824, 235),
    (50016, 234),
    (50048, 234),
    (50208, 233),
    (50304, 232),
    (50480, 231),
    (50560, 230),
    (50624, 230),
    (50816, 229),
    (51120, 228),
    (51280, 227),
    (51328, 226),
    (51440, 225),
    (51520, 225),
    (51552, 224),
    (51584, 224),
    (51600, 224),
    (51760, 223),
    (51840, 222),
    (51936, 222),
    (52096, 221),
    (52128, 221),
    (52240, 220)
  ],
  #[
    (52352, 220),
    (52416, 219),
    (52512, 218),
    (52560, 218),
    (52608, 218),
    (52720, 217),
    (52864, 216),
    (52880, 216),
    (53120, 215),
    (53248, 214),
    (53280, 214),
    (53376, 213),
    (53472, 213),
    (53632, 211),
    (53760, 211),
    (53840, 210),
    (53856, 210),
    (53888, 210),
    (54048, 209),
    (54144, 208),
    (54160, 208),
    (54432, 207),
    (54624, 206),
    (54640, 206),
    (54656, 205),
    (54816, 204),
    (55008, 203),
    (55104, 202),
    (55168, 202),
    (55280, 201),
    (55296, 201),
    (55392, 201)
  ],
  #[
    (55424, 200),
    (55584, 199),
    (55936, 198),
    (56000, 198),
    (56080, 197),
    (56192, 196),
    (56320, 196),
    (56352, 195),
    (56400, 195),
    (56448, 195),
    (56704, 193),
    (56720, 193),
    (56736, 193),
    (56880, 192),
    (56896, 192),
    (56928, 192),
    (56960, 192),
    (57216, 191),
    (57312, 190),
    (57344, 190),
    (57472, 189),
    (57504, 189),
    (57520, 189),
    (57696, 188),
    (57728, 188),
    (57792, 188),
    (57984, 187),
    (58160, 186),
    (58272, 186),
    (58464, 185),
    (58496, 184),
    (58640, 184)
  ],
  #[
    (58688, 183),
    (58848, 182),
    (58880, 182),
    (59008, 181),
    (59040, 181),
    (59120, 181),
    (59232, 180),
    (59264, 180),
    (59424, 179),
    (59440, 179),
    (59760, 178),
    (59776, 178),
    (60000, 177),
    (60032, 177),
    (60080, 176),
    (60192, 176),
    (60288, 175),
    (60480, 174),
    (60544, 174),
    (60560, 174),
    (60576, 174),
    (60768, 173),
    (60880, 172),
    (61056, 171),
    (61200, 170),
    (61312, 170),
    (61376, 169),
    (61520, 169),
    (61536, 169),
    (61568, 168),
    (61728, 168),
    (61840, 167)
  ],
  #[
    (61920, 166),
    (62080, 166),
    (62112, 165),
    (62208, 165),
    (62272, 165),
    (62336, 164),
    (62496, 164),
    (62592, 163),
    (62688, 163),
    (62848, 162),
    (62960, 161),
    (63104, 160),
    (63168, 160),
    (63264, 160),
    (63360, 159),
    (63456, 159),
    (63600, 158),
    (63616, 158),
    (63648, 158),
    (63760, 157),
    (63872, 157),
    (64000, 156),
    (64064, 156),
    (64080, 156),
    (64128, 155),
    (64224, 155),
    (64384, 154),
    (64608, 153),
    (64640, 153),
    (64720, 153),
    (64800, 152),
    (64880, 152)
  ],
  #[
    (64896, 152),
    (64960, 151),
    (64992, 151),
    (65152, 150),
    (65376, 149),
    (65408, 149),
    (65568, 149),
    (65680, 148),
    (65840, 147),
    (65856, 147),
    (65920, 147),
    (65952, 147),
    (66160, 146),
    (66176, 146),
    (66320, 145),
    (66336, 145),
    (66432, 145)
  ]
]

private def upperRowsSize : Nat := 721

private def upperRowsAt (i : Nat) : (Nat × Nat) :=
  (upperRowsBlocks[i/32]!)[i%32]!

set_option maxRecDepth 6000 in
private def primeRowsBlocks : Array (Array (Nat × Nat × Nat × Nat × Nat)) := #[
  #[
    (1, 0, 0x0, 0, 0),
    (19, 8, 0x204020402020100, 8, 1455477752380),
    (23, 1, 0x3, 9, 1498956013249),
    (29, 1, 0x5, 10, 1533438771869),
    (31, 1, 0x1, 11, 1565696836385),
    (37, 1, 0x5, 12, 1592723863412),
    (41, 1, 0x3, 13, 1617114107314),
    (43, 1, 0x1, 14, 1640369921267),
    (47, 1, 0x3, 15, 1661646517011),
    (53, 1, 0x5, 16, 1680514441539),
    (59, 1, 0x5, 17, 1697463594081),
    (61, 1, 0x1, 18, 1713857036703),
    (67, 1, 0x5, 19, 1728782409837),
    (71, 1, 0x3, 20, 1742866916879),
    (73, 1, 0x1, 21, 1756565547015),
    (79, 1, 0x5, 22, 1769223774863),
    (83, 1, 0x3, 23, 1781271967634),
    (89, 1, 0x5, 24, 1792507922690),
    (97, 1, 0x7, 25, 1802817201040),
    (101, 1, 0x3, 26, 1812718191139),
    (103, 1, 0x1, 27, 1822426929003),
    (107, 1, 0x3, 28, 1831772723395),
    (109, 1, 0x1, 29, 1840947035321),
    (113, 1, 0x3, 30, 1849796592843),
    (127, 1, 0xd, 31, 1857670608591),
    (131, 1, 0x3, 32, 1865304196377),
    (133, 0, 0x0, 32, 1865304196377),
    (135, 0, 0x0, 32, 1865304196377),
    (136, 0, 0x0, 32, 1865304196377),
    (137, 1, 0x0, 33, 1872603466449),
    (138, 0, 0x0, 33, 1872603466449),
    (139, 1, 0x0, 34, 1879797711053)
  ],
  #[
    (140, 0, 0x0, 34, 1879797711053),
    (141, 0, 0x0, 34, 1879797711053),
    (143, 0, 0x0, 34, 1879797711053),
    (144, 0, 0x0, 34, 1879797711053),
    (145, 0, 0x0, 34, 1879797711053),
    (149, 1, 0x3, 35, 1886509120448),
    (150, 0, 0x0, 35, 1886509120448),
    (151, 1, 0x0, 36, 1893131637004),
    (152, 0, 0x0, 36, 1893131637004),
    (153, 0, 0x0, 36, 1893131637004),
    (155, 0, 0x0, 36, 1893131637004),
    (156, 0, 0x0, 36, 1893131637004),
    (157, 1, 0x0, 37, 1899501063755),
    (158, 0, 0x0, 37, 1899501063755),
    (160, 0, 0x0, 37, 1899501063755),
    (163, 1, 0x2, 38, 1905636033080),
    (164, 0, 0x0, 38, 1905636033080),
    (167, 1, 0x2, 39, 1911624057032),
    (170, 0, 0x0, 39, 1911624057032),
    (171, 0, 0x0, 39, 1911624057032),
    (172, 0, 0x0, 39, 1911624057032),
    (173, 1, 0x0, 40, 1917404403852),
    (175, 0, 0x0, 40, 1917404403852),
    (176, 0, 0x0, 40, 1917404403852),
    (177, 0, 0x0, 40, 1917404403852),
    (179, 1, 0x1, 41, 1922990996030),
    (180, 0, 0x0, 41, 1922990996030),
    (181, 1, 0x0, 42, 1928515857908),
    (182, 0, 0x0, 42, 1928515857908),
    (183, 0, 0x0, 42, 1928515857908),
    (184, 0, 0x0, 42, 1928515857908),
    (189, 0, 0x0, 42, 1928515857908)
  ],
  #[
    (190, 0, 0x0, 42, 1928515857908),
    (191, 1, 0x0, 43, 1933751460002),
    (192, 0, 0x0, 43, 1933751460002),
    (193, 1, 0x0, 44, 1938932807152),
    (195, 0, 0x0, 44, 1938932807152),
    (197, 1, 0x1, 45, 1944008949283),
    (198, 0, 0x0, 45, 1944008949283),
    (199, 1, 0x0, 46, 1949034074911),
    (200, 0, 0x0, 46, 1949034074911),
    (202, 0, 0x0, 46, 1949034074911),
    (203, 0, 0x0, 46, 1949034074911),
    (204, 0, 0x0, 46, 1949034074911),
    (205, 0, 0x0, 46, 1949034074911),
    (207, 0, 0x0, 46, 1949034074911),
    (211, 1, 0x3, 47, 1953773411403),
    (212, 0, 0x0, 47, 1953773411403),
    (213, 0, 0x0, 47, 1953773411403),
    (214, 0, 0x0, 47, 1953773411403),
    (215, 0, 0x0, 47, 1953773411403),
    (217, 0, 0x0, 47, 1953773411403),
    (219, 0, 0x0, 47, 1953773411403),
    (220, 0, 0x0, 47, 1953773411403),
    (222, 0, 0x0, 47, 1953773411403),
    (223, 1, 0x0, 48, 1958257716335),
    (224, 0, 0x0, 48, 1958257716335),
    (225, 0, 0x0, 48, 1958257716335),
    (226, 0, 0x0, 48, 1958257716335),
    (227, 1, 0x0, 49, 1962663002678),
    (228, 0, 0x0, 49, 1962663002678),
    (229, 1, 0x0, 50, 1967029814905),
    (230, 0, 0x0, 50, 1967029814905),
    (231, 0, 0x0, 50, 1967029814905)
  ],
  #[
    (232, 0, 0x0, 50, 1967029814905),
    (233, 1, 0x0, 51, 1971321660398),
    (234, 0, 0x0, 51, 1971321660398),
    (235, 0, 0x0, 51, 1971321660398),
    (236, 0, 0x0, 51, 1971321660398),
    (238, 0, 0x0, 51, 1971321660398),
    (239, 1, 0x0, 52, 1975505760816),
    (240, 0, 0x0, 52, 1975505760816),
    (241, 1, 0x0, 53, 1979655138409),
    (243, 0, 0x0, 53, 1979655138409),
    (244, 0, 0x0, 53, 1979655138409),
    (248, 0, 0x0, 53, 1979655138409),
    (250, 0, 0x0, 53, 1979655138409),
    (251, 1, 0x0, 54, 1983639202154),
    (252, 0, 0x0, 54, 1983639202154),
    (253, 0, 0x0, 54, 1983639202154),
    (255, 0, 0x0, 54, 1983639202154),
    (257, 1, 0x1, 55, 1987530252737),
    (259, 0, 0x0, 55, 1987530252737),
    (261, 0, 0x0, 55, 1987530252737),
    (262, 0, 0x0, 55, 1987530252737),
    (263, 1, 0x0, 56, 1991332534105),
    (265, 0, 0x0, 56, 1991332534105),
    (267, 0, 0x0, 56, 1991332534105),
    (268, 0, 0x0, 56, 1991332534105),
    (269, 1, 0x0, 57, 1995050006223),
    (270, 0, 0x0, 57, 1995050006223),
    (271, 1, 0x0, 58, 1998740043123),
    (273, 0, 0x0, 58, 1998740043123),
    (274, 0, 0x0, 58, 1998740043123),
    (277, 1, 0x2, 59, 2002350151426),
    (279, 0, 0x0, 59, 2002350151426)
  ],
  #[
    (280, 0, 0x0, 59, 2002350151426),
    (281, 1, 0x0, 60, 2005908870287),
    (282, 0, 0x0, 60, 2005908870287),
    (283, 1, 0x0, 61, 2009442439191),
    (284, 0, 0x0, 61, 2009442439191),
    (285, 0, 0x0, 61, 2009442439191),
    (286, 0, 0x0, 61, 2009442439191),
    (288, 0, 0x0, 61, 2009442439191),
    (289, 0, 0x0, 61, 2009442439191),
    (291, 0, 0x0, 61, 2009442439191),
    (292, 0, 0x0, 61, 2009442439191),
    (293, 1, 0x0, 62, 2012855408474),
    (294, 0, 0x0, 62, 2012855408474),
    (295, 0, 0x0, 62, 2012855408474),
    (296, 0, 0x0, 62, 2012855408474),
    (297, 0, 0x0, 62, 2012855408474),
    (300, 0, 0x0, 62, 2012855408474),
    (301, 0, 0x0, 62, 2012855408474),
    (302, 0, 0x0, 62, 2012855408474),
    (303, 0, 0x0, 62, 2012855408474),
    (304, 0, 0x0, 62, 2012855408474),
    (305, 0, 0x0, 62, 2012855408474),
    (306, 0, 0x0, 62, 2012855408474),
    (307, 1, 0x0, 63, 2016112737464),
    (308, 0, 0x0, 63, 2016112737464),
    (309, 0, 0x0, 63, 2016112737464),
    (310, 0, 0x0, 63, 2016112737464),
    (311, 1, 0x0, 64, 2019328171547),
    (312, 0, 0x0, 64, 2019328171547),
    (313, 1, 0x0, 65, 2022523059725),
    (314, 0, 0x0, 65, 2022523059725),
    (315, 0, 0x0, 65, 2022523059725)
  ],
  #[
    (316, 0, 0x0, 65, 2022523059725),
    (317, 1, 0x0, 66, 2025677633857),
    (318, 0, 0x0, 66, 2025677633857),
    (319, 0, 0x0, 66, 2025677633857),
    (320, 0, 0x0, 66, 2025677633857),
    (321, 0, 0x0, 66, 2025677633857),
    (322, 0, 0x0, 66, 2025677633857),
    (323, 0, 0x0, 66, 2025677633857),
    (324, 0, 0x0, 66, 2025677633857),
    (325, 0, 0x0, 66, 2025677633857),
    (326, 0, 0x0, 66, 2025677633857),
    (327, 0, 0x0, 66, 2025677633857),
    (328, 0, 0x0, 66, 2025677633857),
    (329, 0, 0x0, 66, 2025677633857),
    (330, 0, 0x0, 66, 2025677633857),
    (331, 1, 0x0, 67, 2028698781893),
    (332, 0, 0x0, 67, 2028698781893),
    (333, 0, 0x0, 67, 2028698781893),
    (334, 0, 0x0, 67, 2028698781893),
    (336, 0, 0x0, 67, 2028698781893),
    (337, 1, 0x0, 68, 2031666140943),
    (338, 0, 0x0, 68, 2031666140943),
    (339, 0, 0x0, 68, 2031666140943),
    (340, 0, 0x0, 68, 2031666140943),
    (341, 0, 0x0, 68, 2031666140943),
    (342, 0, 0x0, 68, 2031666140943),
    (343, 0, 0x0, 68, 2031666140943),
    (344, 0, 0x0, 68, 2031666140943),
    (346, 0, 0x0, 68, 2031666140943),
    (347, 1, 0x0, 69, 2034547985323),
    (348, 0, 0x0, 69, 2034547985323),
    (349, 1, 0x0, 70, 2037413314835)
  ],
  #[
    (351, 0, 0x0, 70, 2037413314835),
    (352, 0, 0x0, 70, 2037413314835),
    (353, 1, 0x0, 71, 2040246176024),
    (354, 0, 0x0, 71, 2040246176024),
    (355, 0, 0x0, 71, 2040246176024),
    (356, 0, 0x0, 71, 2040246176024),
    (357, 0, 0x0, 71, 2040246176024),
    (359, 1, 0x1, 72, 2043031691344),
    (360, 0, 0x0, 72, 2043031691344),
    (361, 0, 0x0, 72, 2043031691344),
    (362, 0, 0x0, 72, 2043031691344),
    (363, 0, 0x0, 72, 2043031691344),
    (364, 0, 0x0, 72, 2043031691344),
    (365, 0, 0x0, 72, 2043031691344),
    (366, 0, 0x0, 72, 2043031691344),
    (367, 1, 0x0, 73, 2045756486984),
    (369, 0, 0x0, 73, 2045756486984),
    (370, 0, 0x0, 73, 2045756486984),
    (371, 0, 0x0, 73, 2045756486984),
    (372, 0, 0x0, 73, 2045756486984),
    (373, 1, 0x0, 74, 2048437452131),
    (374, 0, 0x0, 74, 2048437452131),
    (375, 0, 0x0, 74, 2048437452131),
    (376, 0, 0x0, 74, 2048437452131),
    (378, 0, 0x0, 74, 2048437452131),
    (379, 1, 0x0, 75, 2051075974558),
    (380, 0, 0x0, 75, 2051075974558),
    (381, 0, 0x0, 75, 2051075974558),
    (382, 0, 0x0, 75, 2051075974558),
    (383, 1, 0x0, 76, 2053686940615),
    (385, 0, 0x0, 76, 2053686940615),
    (386, 0, 0x0, 76, 2053686940615)
  ],
  #[
    (387, 0, 0x0, 76, 2053686940615),
    (388, 0, 0x0, 76, 2053686940615),
    (389, 1, 0x0, 77, 2056257634702),
    (390, 0, 0x0, 77, 2056257634702),
    (391, 0, 0x0, 77, 2056257634702),
    (393, 0, 0x0, 77, 2056257634702),
    (395, 0, 0x0, 77, 2056257634702),
    (396, 0, 0x0, 77, 2056257634702),
    (397, 1, 0x0, 78, 2058776526389),
    (398, 0, 0x0, 78, 2058776526389),
    (399, 0, 0x0, 78, 2058776526389),
    (401, 1, 0x1, 79, 2061270291975),
    (402, 0, 0x0, 79, 2061270291975),
    (403, 0, 0x0, 79, 2061270291975),
    (405, 0, 0x0, 79, 2061270291975),
    (406, 0, 0x0, 79, 2061270291975),
    (407, 0, 0x0, 79, 2061270291975),
    (409, 1, 0x1, 80, 2063715279750),
    (410, 0, 0x0, 80, 2063715279750),
    (411, 0, 0x0, 80, 2063715279750),
    (412, 0, 0x0, 80, 2063715279750),
    (413, 0, 0x0, 80, 2063715279750),
    (414, 0, 0x0, 80, 2063715279750),
    (415, 0, 0x0, 80, 2063715279750),
    (417, 0, 0x0, 80, 2063715279750),
    (418, 0, 0x0, 80, 2063715279750),
    (421, 2, 0x200, 82, 2068477211506),
    (423, 0, 0x0, 82, 2068477211506),
    (424, 0, 0x0, 82, 2068477211506),
    (425, 0, 0x0, 82, 2068477211506),
    (426, 0, 0x0, 82, 2068477211506),
    (427, 0, 0x0, 82, 2068477211506)
  ],
  #[
    (428, 0, 0x0, 82, 2068477211506),
    (430, 0, 0x0, 82, 2068477211506),
    (431, 1, 0x0, 83, 2070797397120),
    (433, 1, 0x1, 84, 2073106865942),
    (434, 0, 0x0, 84, 2073106865942),
    (435, 0, 0x0, 84, 2073106865942),
    (437, 0, 0x0, 84, 2073106865942),
    (439, 1, 0x1, 85, 2075384770270),
    (440, 0, 0x0, 85, 2075384770270),
    (442, 0, 0x0, 85, 2075384770270),
    (444, 1, 0x0, 86, 2077642106613),
    (446, 0, 0x0, 86, 2077642106613),
    (447, 0, 0x0, 86, 2077642106613),
    (448, 0, 0x0, 86, 2077642106613),
    (449, 1, 0x0, 87, 2079869278105),
    (450, 0, 0x0, 87, 2079869278105),
    (451, 0, 0x0, 87, 2079869278105),
    (455, 0, 0x0, 87, 2079869278105),
    (457, 1, 0x1, 88, 2082057461912),
    (458, 0, 0x0, 88, 2082057461912),
    (459, 0, 0x0, 88, 2082057461912),
    (460, 0, 0x0, 88, 2082057461912),
    (462, 1, 0x0, 89, 2084226659308),
    (463, 1, 0x0, 90, 2086386486521),
    (465, 0, 0x0, 90, 2086386486521),
    (466, 0, 0x0, 90, 2086386486521),
    (469, 1, 0x0, 91, 2088527814144),
    (470, 0, 0x0, 91, 2088527814144),
    (472, 0, 0x0, 91, 2088527814144),
    (474, 0, 0x0, 91, 2088527814144),
    (477, 0, 0x0, 91, 2088527814144),
    (478, 0, 0x0, 91, 2088527814144)
  ],
  #[
    (479, 1, 0x0, 92, 2090615496816),
    (480, 0, 0x0, 92, 2090615496816),
    (481, 0, 0x0, 92, 2090615496816),
    (483, 0, 0x0, 92, 2090615496816),
    (485, 0, 0x0, 92, 2090615496816),
    (486, 0, 0x0, 92, 2090615496816),
    (489, 1, 0x0, 93, 2092668884906),
    (491, 1, 0x1, 94, 2094705544783),
    (492, 0, 0x0, 94, 2094705544783),
    (493, 0, 0x0, 94, 2094705544783),
    (494, 0, 0x0, 94, 2094705544783),
    (496, 0, 0x0, 94, 2094705544783),
    (497, 0, 0x0, 94, 2094705544783),
    (499, 1, 0x1, 95, 2096709552799),
    (501, 0, 0x0, 95, 2096709552799),
    (502, 0, 0x0, 95, 2096709552799),
    (505, 1, 0x0, 96, 2098697624369),
    (506, 0, 0x0, 96, 2098697624369),
    (508, 0, 0x0, 96, 2098697624369),
    (509, 1, 0x0, 97, 2100662260911),
    (512, 0, 0x0, 97, 2100662260911),
    (513, 0, 0x0, 97, 2100662260911),
    (514, 0, 0x0, 97, 2100662260911),
    (515, 0, 0x0, 97, 2100662260911),
    (519, 0, 0x0, 97, 2100662260911),
    (520, 0, 0x0, 97, 2100662260911),
    (521, 1, 0x0, 98, 2102581646707),
    (522, 0, 0x0, 98, 2102581646707),
    (524, 1, 0x0, 99, 2104493692596),
    (525, 0, 0x0, 99, 2104493692596),
    (527, 0, 0x0, 99, 2104493692596),
    (529, 0, 0x0, 99, 2104493692596)
  ],
  #[
    (530, 0, 0x0, 99, 2104493692596),
    (533, 0, 0x0, 99, 2104493692596),
    (535, 0, 0x0, 99, 2104493692596),
    (536, 0, 0x0, 99, 2104493692596),
    (537, 0, 0x0, 99, 2104493692596),
    (539, 0, 0x0, 99, 2104493692596),
    (542, 1, 0x1, 100, 2106342121431),
    (543, 0, 0x0, 100, 2106342121431),
    (544, 0, 0x0, 100, 2106342121431),
    (546, 0, 0x0, 100, 2106342121431),
    (547, 1, 0x0, 101, 2108170274995),
    (549, 0, 0x0, 101, 2108170274995),
    (552, 0, 0x0, 101, 2108170274995),
    (555, 0, 0x0, 101, 2108170274995),
    (556, 0, 0x0, 101, 2108170274995),
    (558, 1, 0x0, 102, 2109965607131),
    (560, 0, 0x0, 102, 2109965607131),
    (564, 1, 0x2, 103, 2111741806065),
    (565, 0, 0x0, 103, 2111741806065),
    (566, 0, 0x0, 103, 2111741806065),
    (567, 0, 0x0, 103, 2111741806065),
    (569, 1, 0x1, 104, 2113499275309),
    (574, 1, 0x1, 105, 2115250588794),
    (576, 0, 0x0, 105, 2115250588794),
    (577, 1, 0x0, 106, 2116983691047),
    (578, 0, 0x0, 106, 2116983691047),
    (580, 0, 0x0, 106, 2116983691047),
    (583, 0, 0x0, 106, 2116983691047),
    (585, 0, 0x0, 106, 2116983691047),
    (589, 1, 0x1, 107, 2118687268559),
    (590, 0, 0x0, 107, 2118687268559),
    (591, 0, 0x0, 107, 2118687268559)
  ],
  #[
    (593, 1, 0x1, 108, 2120373609199),
    (594, 0, 0x0, 108, 2120373609199),
    (595, 0, 0x0, 108, 2120373609199),
    (596, 0, 0x0, 108, 2120373609199),
    (598, 0, 0x0, 108, 2120373609199),
    (600, 1, 0x0, 109, 2122043058280),
    (603, 1, 0x0, 110, 2123706951790),
    (607, 1, 0x3, 111, 2125354398247),
    (610, 0, 0x0, 111, 2125354398247),
    (611, 0, 0x0, 111, 2125354398247),
    (614, 1, 0x1, 112, 2126985719617),
    (617, 1, 0x2, 113, 2128606465159),
    (618, 0, 0x0, 113, 2128606465159),
    (622, 1, 0x0, 114, 2130221974044),
    (623, 0, 0x0, 114, 2130221974044),
    (627, 0, 0x0, 114, 2130221974044),
    (628, 0, 0x0, 114, 2130221974044),
    (629, 0, 0x0, 114, 2130221974044),
    (632, 1, 0x1, 115, 2131806760097),
    (637, 0, 0x0, 115, 2131806760097),
    (642, 1, 0x3, 116, 2133366822499),
    (643, 1, 0x0, 117, 2134922032452),
    (645, 0, 0x0, 117, 2134922032452),
    (646, 0, 0x0, 117, 2134922032452),
    (648, 1, 0x0, 118, 2136467627506),
    (649, 0, 0x0, 118, 2136467627506),
    (651, 0, 0x0, 118, 2136467627506),
    (652, 0, 0x0, 118, 2136467627506),
    (653, 1, 0x0, 119, 2137999021074),
    (657, 0, 0x0, 119, 2137999021074),
    (659, 1, 0x1, 120, 2139516471756),
    (664, 1, 0x1, 121, 2141029331060)
  ],
  #[
    (665, 0, 0x0, 121, 2141029331060),
    (666, 0, 0x0, 121, 2141029331060),
    (669, 0, 0x0, 121, 2141029331060),
    (670, 0, 0x0, 121, 2141029331060),
    (674, 1, 0x2, 122, 2142515215161),
    (677, 1, 0x2, 123, 2143992320035),
    (678, 0, 0x0, 123, 2143992320035),
    (681, 0, 0x0, 123, 2143992320035),
    (682, 0, 0x0, 123, 2143992320035),
    (686, 1, 0x0, 124, 2145456448878),
    (687, 0, 0x0, 124, 2145456448878),
    (688, 0, 0x0, 124, 2145456448878),
    (694, 1, 0x2, 125, 2146903626880),
    (696, 0, 0x0, 125, 2146903626880),
    (700, 0, 0x0, 125, 2146903626880),
    (707, 1, 0x0, 126, 2148330160403),
    (708, 0, 0x0, 126, 2148330160403),
    (710, 1, 0x0, 127, 2149740597638),
    (711, 0, 0x0, 127, 2149740597638),
    (713, 0, 0x0, 127, 2149740597638),
    (715, 0, 0x0, 127, 2149740597638),
    (716, 0, 0x0, 127, 2149740597638),
    (720, 1, 0x2, 128, 2151131418222),
    (724, 0, 0x0, 128, 2151131418222),
    (726, 0, 0x0, 128, 2151131418222),
    (730, 1, 0x0, 129, 2152506934040),
    (731, 0, 0x0, 129, 2152506934040),
    (733, 1, 0x1, 130, 2153871190520),
    (736, 0, 0x0, 130, 2153871190520),
    (740, 1, 0x2, 131, 2155224370492),
    (741, 0, 0x0, 131, 2155224370492),
    (747, 1, 0x1, 132, 2156570265512)
  ],
  #[
    (750, 0, 0x0, 132, 2156570265512),
    (752, 1, 0x0, 133, 2157901823434),
    (754, 0, 0x0, 133, 2157901823434),
    (755, 0, 0x0, 133, 2157901823434),
    (756, 0, 0x0, 133, 2157901823434),
    (762, 2, 0x400, 135, 2160536887843),
    (763, 0, 0x0, 135, 2160536887843),
    (768, 0, 0x0, 135, 2160536887843),
    (769, 1, 0x0, 136, 2161837277960),
    (774, 1, 0x3, 137, 2163130939020),
    (777, 0, 0x0, 137, 2163130939020),
    (780, 0, 0x0, 137, 2163130939020),
    (783, 0, 0x0, 137, 2163130939020),
    (785, 0, 0x0, 137, 2163130939020),
    (788, 1, 0x1, 138, 2164401587050),
    (792, 0, 0x0, 138, 2164401587050),
    (793, 0, 0x0, 138, 2164401587050),
    (798, 1, 0x3, 139, 2165656292194),
    (803, 0, 0x0, 139, 2165656292194),
    (809, 1, 0x5, 140, 2166892386137),
    (810, 0, 0x0, 140, 2166892386137),
    (811, 1, 0x0, 141, 2168125431759),
    (814, 0, 0x0, 141, 2168125431759),
    (816, 0, 0x0, 141, 2168125431759),
    (818, 0, 0x0, 141, 2168125431759),
    (830, 4, 0x2040202, 145, 2172973987842),
    (835, 0, 0x0, 145, 2172973987842),
    (836, 0, 0x0, 145, 2172973987842),
    (842, 1, 0x2, 146, 2174165882955),
    (844, 0, 0x0, 146, 2174165882955),
    (853, 1, 0x8, 147, 2175338215897),
    (863, 3, 0x40203, 150, 2178827969944)
  ],
  #[
    (864, 0, 0x0, 150, 2178827969944),
    (868, 0, 0x0, 150, 2178827969944),
    (871, 0, 0x0, 150, 2178827969944),
    (872, 0, 0x0, 150, 2178827969944),
    (875, 0, 0x0, 150, 2178827969944),
    (877, 1, 0x1, 151, 2179968220799),
    (879, 0, 0x0, 151, 2179968220799),
    (882, 1, 0x1, 152, 2181103294578),
    (883, 1, 0x0, 153, 2182235797409),
    (888, 1, 0x3, 154, 2183363193124),
    (889, 0, 0x0, 154, 2183363193124),
    (894, 0, 0x0, 154, 2183363193124),
    (896, 0, 0x0, 154, 2183363193124),
    (901, 0, 0x0, 154, 2183363193124),
    (902, 0, 0x0, 154, 2183363193124),
    (903, 0, 0x0, 154, 2183363193124),
    (909, 1, 0x3, 155, 2184465728956),
    (911, 1, 0x1, 156, 2185563423796),
    (913, 0, 0x0, 156, 2185563423796),
    (917, 0, 0x0, 156, 2185563423796),
    (922, 1, 0x1, 157, 2186651563077),
    (925, 0, 0x0, 157, 2186651563077),
    (929, 1, 0x3, 158, 2187727989341),
    (934, 0, 0x0, 158, 2187727989341),
    (935, 0, 0x0, 158, 2187727989341),
    (949, 3, 0x60401, 161, 2190913890665),
    (950, 0, 0x0, 161, 2190913890665),
    (951, 0, 0x0, 161, 2190913890665),
    (957, 1, 0x1, 162, 2191963208608),
    (958, 0, 0x0, 162, 2191963208608),
    (970, 1, 0x8, 163, 2192997334771),
    (972, 1, 0x0, 164, 2194027200888)
  ],
  #[
    (978, 1, 0x4, 165, 2195050742341),
    (980, 0, 0x0, 165, 2195050742341),
    (982, 0, 0x0, 165, 2195050742341),
    (987, 1, 0x0, 166, 2196068036338),
    (992, 1, 0x3, 167, 2197077118073),
    (995, 0, 0x0, 167, 2197077118073),
    (996, 0, 0x0, 167, 2197077118073),
    (1008, 1, 0x0, 168, 2198080127100),
    (1021, 4, 0x2060400, 172, 2202019160405),
    (1028, 0, 0x0, 172, 2202019160405),
    (1034, 2, 0x202, 174, 2203957146720),
    (1036, 0, 0x0, 174, 2203957146720),
    (1037, 0, 0x0, 174, 2203957146720),
    (1038, 0, 0x0, 174, 2203957146720),
    (1046, 1, 0x0, 175, 2204919610627),
    (1048, 0, 0x0, 175, 2204919610627),
    (1057, 2, 0x200, 177, 2206824374258),
    (1062, 1, 0x3, 178, 2207766881326),
    (1068, 1, 0x0, 179, 2208707615098),
    (1072, 1, 0x0, 180, 2209643068793),
    (1077, 0, 0x0, 180, 2209643068793),
    (1079, 0, 0x0, 180, 2209643068793),
    (1085, 0, 0x0, 180, 2209643068793),
    (1088, 1, 0x1, 181, 2210563031994),
    (1090, 0, 0x0, 181, 2210563031994),
    (1091, 1, 0x0, 182, 2211479622278),
    (1092, 0, 0x0, 182, 2211479622278),
    (1101, 2, 0x400, 184, 2213306112389),
    (1108, 1, 0x1, 185, 2214212730702),
    (1111, 1, 0x0, 186, 2215114443957),
    (1116, 0, 0x0, 186, 2215114443957),
    (1121, 1, 0x0, 187, 2216009699104)
  ],
  #[
    (1124, 1, 0x1, 188, 2216900171054),
    (1138, 1, 0x4, 189, 2217785910646),
    (1140, 0, 0x0, 189, 2217785910646),
    (1144, 0, 0x0, 189, 2217785910646),
    (1151, 1, 0x6, 190, 2218654720376),
    (1163, 2, 0xa01, 192, 2220381868291),
    (1174, 1, 0x7, 193, 2221235839255),
    (1177, 0, 0x0, 193, 2221235839255),
    (1184, 1, 0x3, 194, 2222082579305),
    (1192, 1, 0x2, 195, 2222925039288),
    (1204, 2, 0x800, 197, 2224595901722),
    (1206, 0, 0x0, 197, 2224595901722),
    (1207, 0, 0x0, 197, 2224595901722),
    (1211, 0, 0x0, 197, 2224595901722),
    (1230, 4, 0x6060401, 201, 2227873327854),
    (1247, 2, 0x600, 203, 2229494082975),
    (1250, 1, 0x1, 204, 2230294723487),
    (1256, 0, 0x0, 204, 2230294723487),
    (1262, 1, 0x2, 205, 2231089004662),
    (1269, 0, 0x0, 205, 2231089004662),
    (1270, 0, 0x0, 205, 2231089004662),
    (1278, 1, 0x6, 206, 2231872090018),
    (1282, 1, 0x0, 207, 2232653950846),
    (1295, 3, 0x20600, 210, 2234983762600),
    (1308, 4, 0x4020401, 214, 2238055982780),
    (1310, 0, 0x0, 214, 2238055982780),
    (1313, 0, 0x0, 214, 2238055982780),
    (1326, 2, 0x205, 216, 2239571135164),
    (1335, 1, 0x0, 217, 2240324714666),
    (1352, 0, 0x0, 217, 2240324714666),
    (1358, 0, 0x0, 217, 2240324714666),
    (1379, 3, 0x60602, 220, 2242519329537)
  ],
  #[
    (1381, 1, 0x1, 221, 2243243442498),
    (1382, 0, 0x0, 221, 2243243442498),
    (1396, 0, 0x0, 221, 2243243442498),
    (1398, 0, 0x0, 221, 2243243442498),
    (1407, 1, 0x0, 222, 2243958238781),
    (1433, 5, 0x402040e01, 227, 2247469100291),
    (1440, 1, 0x5, 228, 2248164027323),
    (1445, 0, 0x0, 228, 2248164027323),
    (1460, 4, 0x6020401, 232, 2250917924405),
    (1461, 0, 0x0, 232, 2250917924405),
    (1477, 1, 0x9, 233, 2251597734058),
    (1497, 5, 0x402040203, 238, 2254961141329),
    (1498, 0, 0x0, 238, 2254961141329),
    (1515, 2, 0xc00, 240, 2256290066104),
    (1516, 0, 0x0, 240, 2256290066104),
    (1520, 0, 0x0, 240, 2256290066104),
    (1533, 2, 0x802, 242, 2257599832786),
    (1539, 0, 0x0, 242, 2257599832786),
    (1543, 1, 0x3, 243, 2258247920925),
    (1547, 0, 0x0, 243, 2258247920925),
    (1578, 5, 0x408060401, 248, 2261453549868),
    (1590, 2, 0x400, 250, 2262718574029),
    (1592, 0, 0x0, 250, 2262718574029),
    (1610, 4, 0x2060404, 254, 2265213139297),
    (1614, 1, 0x2, 255, 2265833102099),
    (1633, 3, 0x60204, 258, 2267682298619),
    (1640, 1, 0x3, 259, 2268293172168),
    (1644, 0, 0x0, 259, 2268293172168),
    (1653, 0, 0x0, 259, 2268293172168),
    (1655, 0, 0x0, 259, 2268293172168),
    (1677, 4, 0x2040601, 263, 2270697036576),
    (1680, 0, 0x0, 263, 2270697036576)
  ],
  #[
    (1693, 1, 0xc, 264, 2271287704030),
    (1700, 2, 0x203, 266, 2272465560739),
    (1717, 1, 0x8, 267, 2273050698246),
    (1755, 6, 0x606080a0203, 273, 2276506415906),
    (1775, 1, 0x3, 274, 2277074920738),
    (1795, 4, 0x2040601, 278, 2279317088016),
    (1798, 0, 0x0, 278, 2279317088016),
    (1824, 3, 0xc0a02, 281, 2280973062567),
    (1838, 1, 0x6, 282, 2281519212212),
    (1843, 0, 0x0, 282, 2281519212212),
    (1851, 1, 0x3, 283, 2282060630728),
    (1876, 4, 0x2040609, 287, 2284201971252),
    (1882, 2, 0x200, 289, 2285266934279),
    (1908, 3, 0x60c06, 292, 2286846737677),
    (1911, 0, 0x0, 292, 2286846737677),
    (1940, 3, 0x21201, 295, 2288404673794),
    (1947, 0, 0x0, 295, 2288404673794),
    (1968, 2, 0x201, 297, 2289430315088),
    (1977, 1, 0x4, 298, 2289937157460),
    (1984, 1, 0x1, 299, 2290442463169),
    (2000, 4, 0x2040602, 303, 2292448491829),
    (2022, 3, 0x60802, 306, 2293940793814),
    (2029, 2, 0x204, 308, 2294926987347),
    (2062, 2, 0xe09, 310, 2295904515895),
    (2083, 4, 0x20c0600, 314, 2297833187160),
    (2125, 5, 0x20c0a0203, 319, 2300214429034),
    (2136, 2, 0x203, 321, 2301153396376),
    (2140, 1, 0x0, 322, 2301621342094),
    (2147, 2, 0x200, 324, 2302555049112),
    (2200, 3, 0x120805, 327, 2303941192134),
    (2212, 2, 0x402, 329, 2304848222357),
    (2240, 4, 0x2100800, 333, 2306644000501)
  ],
  #[
    (2264, 2, 0x802, 335, 2307534078977),
    (2293, 6, 0x60608040202, 341, 2310167628720),
    (2332, 3, 0x20c03, 344, 2311468780204),
    (2336, 1, 0x0, 345, 2311897412865),
    (2340, 1, 0x2, 346, 2312324945998),
    (2349, 2, 0x600, 348, 2313178189715),
    (2380, 4, 0x60e0601, 352, 2314870270094),
    (2394, 4, 0x4060200, 356, 2316546371485),
    (2403, 1, 0x4, 357, 2316963211835),
    (2427, 3, 0x60607, 360, 2318204425042),
    (2469, 5, 0x80c060409, 365, 2320245117466),
    (2475, 1, 0x3, 366, 2320649484631),
    (2480, 1, 0x1, 367, 2321053198801),
    (2510, 1, 0x16, 368, 2321452719376),
    (2525, 1, 0xa, 369, 2321849387364),
    (2561, 6, 0x60206040805, 375, 2324206977443),
    (2572, 0, 0x0, 375, 2324206977443),
    (2577, 0, 0x0, 375, 2324206977443),
    (2604, 3, 0x20c01, 378, 2325366329683),
    (2626, 3, 0x40804, 381, 2326513268991),
    (2637, 1, 0x6, 382, 2326893063901),
    (2648, 1, 0x9, 383, 2327270850074),
    (2741, 17, 0xa020a0602040806040204060608040208, 400, 2333577450880),
    (2808, 9, 0x20406020c0a0e0407, 409, 2336814110546),
    (2840, 3, 0x40e0a, 412, 2337874313989),
    (2853, 2, 0x802, 414, 2338576809228),
    (2893, 4, 0x8120403, 418, 2339970078017),
    (2934, 5, 0xa08060603, 423, 2341687959368),
    (2948, 1, 0x4, 424, 2342028211154),
    (2976, 5, 0x206060404, 429, 2343715926944),
    (3012, 3, 0xa0216, 432, 2344714709260),
    (3019, 1, 0x6, 433, 2345045944768)
  ],
  #[
    (3063, 5, 0xc08040e03, 438, 2346689520502),
    (3109, 5, 0x1406040c03, 443, 2348310088373),
    (3164, 4, 0x1a100209, 447, 2349586045526),
    (3255, 12, 0x216080408060c04060c0202, 459, 2353328723043),
    (3324, 9, 0x4060606021c0c0201, 468, 2356060832773),
    (3415, 12, 0x6100210020a020c040c0204, 480, 2359624180241),
    (3424, 0, 0x0, 480, 2359624180241),
    (3434, 1, 0x8, 481, 2359915470657),
    (3472, 6, 0x2040204080e, 487, 2361649080035),
    (3521, 4, 0x60c0812, 491, 2362790479226),
    (3531, 2, 0x205, 493, 2363357372694),
    (3633, 15, 0x80604060e0a020a0c020a06020601, 508, 2367548041722),
    (3654, 2, 0x603, 510, 2368097492644),
    (3731, 10, 0x80a0804060e04020c04, 520, 2370805846913),
    (3810, 9, 0x6040e0a0206160601, 529, 2373192431433),
    (3930, 16, 0x6040206041208040e0a02040e0a020a, 545, 2377318891358),
    (3968, 4, 0x14040c00, 549, 2378332330189),
    (4006, 3, 0x20c14, 552, 2379082769739),
    (4058, 8, 0x602160602060600, 560, 2381067674157),
    (4084, 2, 0x60e, 562, 2381558351556),
    (4098, 2, 0x206, 564, 2382047110137),
    (4222, 14, 0x2060a181202040e060402100c00, 578, 2385413244106),
    (4237, 2, 0x206, 580, 2385886057370),
    (4432, 22, 0x20c0c06120a06080a020a1e08060a020a02060a0203, 602, 2390973403834),
    (4464, 5, 0x606040608, 607, 2392096548351),
    (4716, 28, 0xc0c060a060602060402101206060810060c0218040204060e0a0210, 635, 2398197149882),
    (4734, 4, 0x4060204, 639, 2399043442923),
    (4844, 11, 0xe040c0206040204180810, 650, 2401338507340),
    (4960, 13, 0x6080604020c0a060e0c060a10, 663, 2403984153243),
    (5040, 12, 0x10020a02060406060e040206, 675, 2406384438845),
    (5081, 4, 0x412080a, 679, 2407173865328),
    (5319, 25, 0x6061002060c18040204120c080a08040e061c060606020c05, 704, 2411983566176)
  ],
  #[
    (5341, 2, 0xa03, 706, 2412358941881),
    (5387, 4, 0x61e0405, 710, 2413104314736),
    (5555, 22, 0x406020c04021204020616060204060c020406080605, 732, 2417132270381),
    (5630, 7, 0x200a0804060601, 739, 2418386863983),
    (5787, 20, 0x41e06020414060a0804060e0a02040204060208, 759, 2421897638929),
    (5813, 4, 0x6060a03, 763, 2422586938917),
    (6097, 32, 0x20a06060e06040608120414061c0e0c04140610020a020604060206040c0607, 795, 2427966878625),
    (6313, 26, 0xa020c0a060206060a12080406080402180a0c080a020a080c03, 821, 2432153383627),
    (6720, 46, 0xa06020a020a060c020610120c0812040602060a020412081e0a08041202160618080a06060602060a0608060603, 867, 2439212963836),
    (6756, 2, 0x40c, 869, 2439509920061),
    (6793, 6, 0x20a02100204, 875, 2440395139886),
    (7183, 42, 0x12081602060c06180a0c0e040c08060c04060806060406020a021e060408100c02060610080402041409, 917, 2446415781920),
    (7440, 25, 0x10061218120210020a0c020a0e1e060406080a0602040e0603, 942, 2449843738274),
    (7812, 45, 0x41e02040c0e04060e040804060804140604120e040c020606040c020a0206040806060a080a0206041202060a, 987, 2455758745370),
    (8064, 26, 0x60e160602101e0c020c0406080c0612040204060e0c0c060604, 1013, 2459038816481),
    (8223, 18, 0x20a120c0804060e1806060a080402060c04, 1031, 2461249957159),
    (8620, 41, 0xa0210080a1404020a06080c22060e040c0206041e020a08060a180c060e0402040e04061406040207, 1072, 2466125702171),
    (8928, 37, 0x1e061404020c0a02060a020c0414041208060604060c06060806040804080610060c020402, 1109, 2470351284458),
    (9057, 16, 0x6020c10020406021c02060c0a080400, 1125, 2472130949449),
    (9191, 14, 0x6080c04060e040612060c180801, 1139, 2473664192263),
    (9920, 83, 0x60e040c0c02060c06040c06080c04060c02120604060c0216080a02100c060c020604060c0e240408060c0a0e060c06060402160204020a02060a06060e06160602040e0408120a02041410020c060c060407, 1222, 2482356052856),
    (10000, 7, 0x612080a020602, 1229, 2483059946639),
    (10416, 45, 0x8160c0e0604020a080a020c10020408060604140c120c04080604080a020616080406020c0a020616021c0206, 1274, 2487471220449),
    (10869, 48, 0x60206060a06200a080a120e0604060c021204140406060c08040e0606040816081c02100c020c0a0e0402041404020a, 1322, 2491981668306),
    (10964, 9, 0x80a021c060c02060d, 1331, 2492806041952),
    (12019, 109, 0x414060a020a060c020606040e06060a140418060204060806060c060402220c0c0210020a080414180c04140406081c02160810060602060c041404060e0c0c060a0e1002160804060c0c08060c040608041a101404020a020a120c02041406040c020a020a14180a06080608, 1440, 2502288965944),
    (12254, 25, 0x20a020c100806220204080618060402060418021606020411, 1465, 2504347967928),
    (13157, 99, 0x414060c0604061e0e060604180204021204060608060c1204020604080604240c0c06020c0a080a12060e0412080a0608120c060606041206020a0c060608100606020c0a0608060604080610060e040c0804080a0c02041a040e06160c0804080608, 1564, 2512145933324),
    (13888, 77, 0x402040e120a0216080a08120402061606020a020c04020406020a141006080610060e0a0e100e0a0e0c0a080606060a1404060c02100e1c0206040e040c0618080a080c0a021e040606080401, 1641, 2517838138897),
    (14204, 29, 0x14040e060406241404020a0e06120412020a021e041e020a080604020c, 1670, 2519904034681),
    (14705, 50, 0x100e0c040e060402061c021c020406020606040e100e0a120c020a0608040804060c021216060e0402120a0c1e0206160e02, 1720, 2523361124833),
    (14880, 23, 0xa0210080c040608100e04080408060606040608060407, 1743, 2524916481581)
  ],
  #[
    (16025, 121, 0x60a12020c160e040606060c02060412240608060606040e06060c0a020402042c040804060c0204020c0a0c0612020c0a080a0e100e041406060a08040c0e0c0a0806040c020a12020a0606080a020a060206041208060a1206060e0c0c0a02060a0e060a0806040c08160e041e0e0c0604080a061a060406, 1864, 2532749974719),
    (16666, 64, 0x4060210020c0c041e06060806120a1a0606041802040e060604061e0c06020c0a060e121c060e0412020606180402042a020c10080606040e04020402041807, 1928, 2536666070394),
    (17361, 68, 0x80a080606041206022212081602040c02061008160e060a080610180606080402060a1206060210140606040612020c0604081c0c02060c1818040c060c1a0406021206, 1996, 2540661454853),
    (18939, 158, 0x204020c1e0a14240604060e1008060c0c060c0a0c080a18141806041e0c021002040e0a0c140406080406060e0c041208040e0c0c100204060c02120c040212040606060c080a0c14060a0204060216080c10020a0204021c18020604060c02120a06020a02060c0a120c0c020a14100206160c020a08100618020c0a021e040e0a0210020604120c140a0c06020606060412060c0c021008040204060f, 2154, 2549390807472),
    (19230, 26, 0x60204180212061002122206020604120e0612040816060e0c07, 2180, 2550752847664),
    (22321, 320, 0x40c08040204020c0c122404120c0204060e04060c0210020c0606040c0c0206040e0a06060e1012060812120c0a0804080a0212040e040c0e060a060c020a0e0c120a0c0c021e04020a020a020a080604021c0602040e04060204060e220e0c0604060804021e06120402041e06081614060a120204080a0606080604120e060c1606021c08040204020a120212040c080a081204020a0806100828021210020c060402040c0c020a0e0c1216020c100c061e0c02060a0c0c0218040222020a1404080604140a020406060806041a0a12080c10020c121206040c0c02040e06060406060c12080c041206020a0e04020c060a020c0c0a080616021606080a0216060c08100e0406020c0c0a080a020a06143406060e06060c060a020a18060c0606060206060a060804020402040e0c04060206280e0a080c1006080a0c0600, 2500, 2566184939034),
    (22727, 40, 0x604080a02060c0a120804021002062802041206020a140a12020c10060608180c060a0c02120615, 2540, 2567959155089),
    (23148, 43, 0xc0e120c060a080402040c020a02060406080a140a021206100e0618060a020624060414040608120a020b, 2583, 2569833031870),
    (27777, 448, 0x6040c020604020420040602101406100e061c021e0a020a021216060216080c060412020a1e0618081e100204060c060c021c0e060c24101202040c0e04060602100c0e06120606160602041406120a020a0210020c0a060c080c120612160602060604020a02060604020c160608061e06120c04121a0c04080a140a0c0608060a080606100e0a081204080c041a04020a020c0a12060e0606060a080c1606020408101e0c0c08040e0402100c12080406020c060a0e1006120206161202061608040c0608100e0a0e06060a0e04060c0c06020c0604021014040e34020606040608100c021212060a080604120c0204022808060406080a1e060c02060a06140604060e0a0e1014040212180a0206040e0a1404020a120c12080406140c0a060c0e040e10180c060806060c1c080c121614040e060a080a1208041a0412020606100c06020c16080c241e04080a06140610020a120e040c0804020406060806060a0c060e06040c06080c04060e1c0c06020a06060806040c18020408060c0c10060608060402161e020a0602061e0402040e0604060c0e040204080a0206160c180e0c100e121c020c120606060a0e04020c0a121812060204081006080a, 3031, 2587483879686),
    (29761, 196, 0x2060c1206220c0206160804120c0c060804021e06041a120a140a0608060c0a020a020414100806061008060a1212080c0a0c02060a0c06060e060a06020616180e041a06040204081e120c1006060c081608040810061404060e04120c060216060c08060a1206020408060c0406020c0406060c06020c0a02060414040e06100e100806041202060a0624021e0a020a08060402300a080a1202120c1c0c020a020a060c0c0614040812040e100608060402160210080a200414040608060406020c01, 3227, 2594302635339),
    (31250, 141, 0x20a0608041a04060204120602040810021e0a020a060c0c060e061e06061608040614120c0a020a06020a020a0c080616080a061e0e060406080c060a0c06060626101202040e0a0c080c04021602121204180c02161406120406060e16020a060c120c08060a060c081602040e060406060602120c0c1210021606180c14060424020606040c0e040e100e1b, 3368, 2598919606772),
    (35714, 427, 0x6360e06040212041a06040204060c02101e0c020a0e040c06080c120a0e0c040606140a020c0a061806141e0c0604080c0c0604080a06020c0a060218042a12020c0a1406100e060616020402160c1a1204020a080a08120a060806061002121206040c02062206061206020a020c040c020c120a0812160c02060a0e0a08060a02040e0a06060206160e04021c0c0c020a060c02043e041206020c161e06140406080c120412080606160210020c061204020a06020a12080a1820060408060402040c020a0206040806100e0408120a06080a08041e0e04060c0e12060402040c020c060a0c0228180c0804080a02120a021e060610080a0212040c08060a0e0606040c020c10020610060216121a0406021c020408060408161e0204060e0622060e0c0a0206100806040602180402180406060c0c18020c060a020a140406020604060c0e04020c0604022404060e04140a0c02060a0e10021602120a06060806040206160212060c0a080a063210080a0e0a021e12061602120a0c020402160c1404060806101406120a061404020a0e04021608040848040204081614040606020c1e0604080602, 3795, 2611700202306),
    (41666, 564, 0x804060e060406020606040e1e060412020606100c0c0e0a1e020c0a020618060a0822120c06060e0a020406080a020c060402100c06020a0e0420041406040810060612140c0c0a060618060e040c0e0402060c0604060c0e100804080c1e0a020436020a120c06080612100c020a0c080606040c0c1a040204241a040608360606180c04061214040c08060a021602040c0c0606181802061204140604081210081c0e04060806060a06020a020616080c0a080c1006080a06180804081c08040c1a0c060c0a140a020604260a0804140a0c0e0a02040810021206040c082a0a020604020a080a080a12020412060e06060406080a20040212041a10060c06140a02040e0c1206060a0c060c120c081012020a08060a0204080610060210020c0a1202060a180206040e2a2802060402102610061412040206040e040c06080c1602060c12040806060a0e041e061e0e1006081c0e040204140406062c0a080a080a08061012020c1002221e1206021c0608060a0e0c10020a060204060c020a080c060406080406141006120e0c120a0602041202100804021e04140a140610020a080a0c141006140a1a04080a1202060a0612061a040c020604060c020c0a060e0a0e0c0c10020406020c060c0a1208040c06080606120a060816080c040c0804080a0c02041a040e0604020a06122c060a140a0216060608061008060c0a0c0c0812041a0a0e0616020a0e0a0606181404020408060a0608060c120a0c0c02120a060c0c0206160602041a0c060610020e, 4359, 2626311066357),
    (44642, 281, 0x80a02041e08100e060604020c0c060406081e04201c06020a0e063a0c020604020406081c0e04020c0a080c1c020604080a0c02100c060c0c0206041406040e0406020a080a141602160e3408040204020412062004061416080a0210060e04020a060c02041e0218120c0618060a0e10080402063c0a020616080c0a180e10060c0c120812100e0a1a040c020c12060a0e0a0c06080a06080616022404060c020a081804060e061008060a080a0602040806060a1206021e160c06020c18180a08040e060402040608060418020406060c060e0a0c06081008060a0218120c04020c0c040606020a0c12081e0c060a020a12140402040e10020c0a020406060e100806040608100c02061e040818060a0216080a20060c02, 4640, 2632829533744),
    (52083, 687, 0xc020a0618060c120e040216080c1006080616020a060e0a020a0e060a1202121c0206160804060e0c0a06120608060c040e0c0c12040608100602060c0c0a0206040602060618160c0204020c161404140610020a0c0e040204180c060e040216260a020c040c1e080412020c0616060e100212060a080a060c200c04060e0c1210180c1404141c060204061e0206040c0e0a062402121206061804060e04120804080a14040e0a021e04060e1e12060610020604080a08060a081002040e0a02160602220e04020a06021c0e06120a0c080c04060c02041a0a06020c100e100c02041806060e0a06260a020a0602061812040e040812040c06021002160204180602180a120210081e0c040602061006020c121002040806160c0c0e0604020c0a060c021014062812060c020a020a180204080a0c06020c06040612023402040c0c021804081204120816020606041a06040602060a0e0c1804020a0e0c120c0418020c120a0c0c08121804060810061a0a020a120c0618140606240408060c040806100608160c0c0e06120a020a060c022202041404020a02121602040e0a060e0a080a0c06140a0606080606040620120a0c020a120206120a020c160806060406080a120e100e121c0c0204060806040812061c02060a18140424180e120c0c0a060816020a02060424020c06041404140c040602100e0604060e120a021006080a1a0c04080a0c060e060406021c0c121e020c0a1202061606020a18080a140c04020a120606081e040602120c0a021606200a080c060406320612060a0c0806040204260c0406060e1e0a060e040608120a120e0a02120c040c080a1406060a2a06060e0a0e0c10120204080a020a0e040812040c0e24060a021216020604060224061008280614040c0804060e0c0a081006080c100804140a0c080c0402120c0c120a020c041a060404, 5327, 2647050149635),
    (60275, 756, 0xc02061c06082802060c0a06061404020a0206062404080c040e120a0e0616082208101e180c060c081206040e06100806160206040816020604061e0e0604121a040c1802040e06040216020a0806060a080a02060a0834080a1404060c020a020a0e10080a08120406060e0a0608060a021606020a020c060c0c041406100804020604083a2a02100806100806100c06060812041a120a021606061206061a1e0418020a020c0a06080a020c0a02041a100804261c0606020c060408060412021002041212020a1a06060408060c040e160e041a041406100212160606080a14060a02040608160e06040806040c080a0c0e040804240806100c021c02180a06140a1e0e1008060a06120210021c0e040c020a080a1202120a020c060a0e0604080c0c0a080c040e0c0604260604061406060a0c06020a020c040212100e100608040218040606140a0612020a0e060a08041a04120c0206161a0a0204080a06020c0a0204060e0a06060e10080a06080a1a160c1e02040e0a021c020a1208041212080a0c020606061c0c021e06060a1412100204061202040812160606080604020406080606181e0c04060e060a080604021606020a020a060e0a20060c120a0e120c10021c0c12081608040204021216200a060e0a020406061e0810140a080618060c0406021c0c081204060e0a0816020a1a04081212041e0c08060610180608041e06061410020606101202040e040c060212040e04020418140606100206040602180604060e1008040812060a081222180c0e040c0c060c140a08180a0c18020a08061c080c0c04061202060406140408120c06160806040e1c0c0212060c18040e0604060606020c0402161202161404181a0c0412080406140412061a040e0a12020a021c06021e040810020a0c02120c040c0804020a0812041e0e041208060406060e1210020c0604120216140406180e0c0a0e06060a020c0612061c0804121a04080406080a020c0c060a0c2004142a04080a060228080c0a02160806040c0e160c0602040e0a0614061213, 6083, 2660523702507),
    (68467, 723, 0x20406260a121416121e0212160c08060402240a0e061c020c0c100c060c121e06080c06040e040602041a0a08100e0a0e0a0c060c06060e0402060a080a0e0a141c140c0c060c0a020a080c0a06080c0c0604080418060e0402060a020a0816140604201210020a0e100c0204021602060c0c040c020a081218060c0408060a0c121a040e0a02040c08041e06060e0a020a140c0c061c0c020a060c080c040e1e0a0e0c1008061002100c0804060e0a081804060812120a1406040c020c040624081620121e0c060408181c02040e060c0414060408240a0212060616020616120e10080402060412140c101e020a02040606020c0a1406040e040c080a0c0602100606080402100216121e020a0e0406060e0c0a0e041a040e100612020a121a0a140406020414060c0604080a020a12080a1404021008061c120e0a0602120a0c020612042006120a0212101e08100e0c04021c06060804080a0c020a0e280e0a061e020c061e0412082806081002120408220608061c02100e04021c0e120a0e041a040e06060a141c141006062606040c02100e0604060c080c12060a080a060606021204080a02120c060406020a020a12120806061606060e0604140412020a0c06020c0a0608060a060e04020c12041e061e0c02121e12040e0a06120606081c02280204020a021e0a020612061804080a1808120a120c080a0c08160e0418060e06060a0e06060a120e0a061a06040e0604060824061012200414040c08040218280e0606060a02121c020406020a14120a0e0406081606080c0406020c060c1006121e080a120612062018061606060e100608060a06080606040e04061416020606041808040e06040c020616180806160210060e040602220608160816080c2a10020a0c0816082206080c04140628080a060e0402040c020a02120a260a120e060a020414040608100e0a12020a020a0608060604060c320c060c0c04240806100e100e0a140a06060e18040d, 6806, 2671767594362),
    (69444, 87, 0x80418020c0604081e0414043204020a08060c120604021c0c020610080a2406061e020a080a081e10140a08060402060a02102a0206160e06041206060810020c0c040e0a1406160e100e1804080a0e060a0206060405, 6893, 2673029521188),
    (77636, 736, 0x40614040e0406060602061006080412020a020618100c022206080a08040810061a0c0a0204020c060402180c0a14040e0c0424080c0c16060c06060e0c1c020c06180606180a02180a06020a121404060e0414101412060610021218040612121202041208040e06060a081612021210080a02180a1e0e0616020604060c12062c04020a12061404080a0228081c0204060206040c1a0406121e0e10140c180406060806180c0a0c02040e060414060c0c0a02061c06060e040c020606060a08182a061804020a020c0a0e060a080610120c08100e0c04060602100c0c02060c10181a042604080c04023412080406140606040e0408040e0c04061812080a020c10020a020406080c221e0c020c0a0e06060a1404060c0212121204081606021c02040e06041e06060e040608161a0c0a060204080c0a06020a060c1e020610061404140604121a0c0a0804200a0e060a080a021804240c0e0618060c0a060c02061608061804020a08060c0a08061206062206060c06140c041e080a06020a140412060c0e1210063008280806061e0c10021204021206040c14040e06040c06080c04060804060c020a2406141e04180606080c060c0a06020a0c0204140604241208040e1e06040c0c02061e0a26040c0e0c041806140a06021002160204020a26040206161e06020a020c041406040c0c140606040c0810060810080a0c06020c060c0606100c02120c10141606020408061608100e240418060c020c0a1814040602120a06080a06020c0a021804060606020604020a1806180204080c0418121404060806040e0a1e080c0a14100c0c02060a020a0c06020c1002060c0a0c020a0e040602121e0a0e10180c0816140406120c06020c12060a02160c0816060c02061602060c0a061e0c020616180608040c081216080408061006021002040e061002100204060c140c060a0c140a0602040620120a02120c1612020a0e0402060c1e0c040216021c0c060e10081e1e2412280204020a080604060c, 7629, 2683047660841),
    (83333, 505, 0xc1a04020a0e0a020406020c041a28141008040c0608040c180e06061012181a0a0c0206240a18020c0606061204021c020402162a06120e0604080a140406020a120216080606040c020606241c060e0c0a020a2006160c061404060804020a0e04060c080a0c020a3806100c02060a080402041e02040e0a0606020a1202100e10060816121a04080c0c0a1404020c0c060412020a080a082a06040602040e060a082e0612120c081c020c0604060c1808060a022a060a14040210080a061a0c12040e0606160204020a080402040c0c1a0a1404060606020c220e10020c0a060e060402100c020a180c0e04020406020c061602060a0804200a140a0e160210021602121614120610060c0c081608060a0c0c06020a0c02100e04060e0402061e041e06140c1216020a08060618042004020c1006060e04020c060604020a18080c3a02040204120c180204060804080c0a12020a0c06260c1e1206040c0c02040e0c0a080c040e0a081204060e120a021c080606160602040806160810181404082a0a02240c0a120804020a14040e100e0606060406022a1008060a0626040614100e0a060602100c021606020c0a080c1c020a1a221406180604061206121208041a0a020c060604061202101416140a080a0e0a081006081212041e061a040e0a1a0c040e0a0c0e040c080406020c0a0206160c0604, 8134, 2689324125943),
    (91525, 715, 0xe061e040204140a0c0e0406060804022416060606081e040606081e060a140406020a020a0206160210022e0e0a0c080c0618100e0604060e181006080a02120a0626121606061202120c060a0c021210240e0402040c0c1208041e021e0402041206020c062818080a0810080c0a0e040206040e0a0e16060e121002040806160804020604060c06060e04141006080a020618120a060c020a0c0e040c080640080a020a0204140610080402061804021c060602060c0a0e120a060c0e040e0606060a08220c0e0a1404081806040e04060e24100e040606060e040c020c060a14040806060418120e1210060e0a0606080a1802040204060206041218060c08280e0402040608220210022a180a0e0616020624040c0e1228020a06140c1c0212040e0c2208280c180e0a20120c04020a0e040c02100c0e06180604081014160806041a10080412021204060804081606020a02060a18020418020406060210060602120a081e0a06060e041418160e06040e060c041404021c020a1806021c02100c020c04140c1608041802120c0c0a080c0a0204360804060806181e0c040e0a0e0a0812040c30021c0c08060c16060216080a0e0a06080c120a0e0a080a020c04020a120c0e0402041206060806041e08040e04080a1206060e04021c060828020a060c083a0216060e2406040606020a02180c1e121006080c16020612040c06020c0604140616120806041a12100204080a02101e0c06021c02120a06260c040608060a0c0206220c0e0c0c060a020406140c0c0a060c120c020a060e1c062a020a021e100210061a0a0e060c060c0406120e06041202281e08120a020c0604120e0406080606060a0e060a020c1c021c020406082410080a06020a0c080a021014060604062016060206061e0618040e1e060c0a080c12040c0e0a14160e040c181202100c1a0a0c021204080c060c100204142814060c0a06060608060a06020a061a100205, 8849, 2697505731970),
    (99717, 718, 0x402120a0c0612140c041a04060804081602041a0a121e08160804060e060412021e1c0c1202060a080a200a08180a0204020c0a060e06041a0c1206040e060c120a06080a0210020a0204060e0402120c1c020616062406020c040216140616020c0618180a02120a0e0c100c060608060a0e0a080412020a08161404020412021c0c06180608061c240e061614180a06180602160e0606120c04082404080a020a0204020c1018020a062a12180e1602240402180402060a080402180c0a022404060c0c061a0a06020604022818021218120a121a0a06020a0206180a0e160822120e040204080a060e061614040e24060414040216020a080a0606080a02061c061a0406122a0c020618041a0a140406080a080406080c0c121818100602061e04080c06041a0a020a0c12020c0a080c281214060a1a040c0c02100c020a12060606140a08040c26060a020a02060a1a0a06080604060632120408040e06100c080c0a080414180408040612020c0a060c080a0e1e0c0a061808060606041206020c060a0c020c180a0c140406080402040c0824060c060406200a02101a040e10180206040e040812040804061814040e100624021c080a060e0a0c020c04020a02101e060e1006020606061602121c02060c04060c0210120c08180a0c062010021e0406020a141006081018020a0e0408041208040e0a020a080402101418100216180216141002122e08160614120402041806140604020406021024080c180606220806040c140402120604020a020a1e0c080a120c0602120a060806061206062e08061c02060a0e0616061a04020408120a0c080a020a0c0608100e060a08060a020a020c0a06020c041e0c0c020a062c040e0a0c06021c0c060c020c04020408060604060e10060e1c12080604060602100e0a0204140a18080418061a0a081806061c020604060804120c24061a040e0a020406140a0e041416080c1222080a1e080604021e0c03, 9567, 2705021802709),
    (107909, 700, 0x61008060a0e04020a240e040c0e061602040e0606101806140c06041212360222060e04084014060408100e1e06041208101208040e0c220e0412020a0c06020c04140c1c0e100204080c100e041a06040602061e160e040216060204080c061204060c0c060204080c0a06021c300204061e0e22020a08060a060e061206040608120a020c0406060c02040c1218020406120206122206020c061036020c06100e0606040e0a0e100608100c08220c3002060a12061a0a080a060e041e0606062606100804020a0806040818120c1e0604080a0606060212040608042a08060a020c0a02100c1a0618061e0a1a22060804140c100c06060e1006140c0a1202120418020c0a060c02100e0606060406080a020412080c101a040e120a0206060a0e160c06020c2a12060a020c1614040c020c0a0626040602181804060c0c021804060612021c06060e0c0c060604020a020a02040c20060a0e1618020418020a0e122e14040c060c0c06081806160806040606080414121c0c0e061c020c0a0602041e08100e0c100234060e2206061e1218060204080a021206240612100e160210021e04060c120c120e041806023c160204060e060420040e061804080408060a14040210140a0e0418020a1e0816080c1002062206020a08040c0e0402060a140c0a120e04021602060a02100c0804060c020c0a0e06120a08041a0c0604061802041a0a0812160206040e0412080c120a0c0e10080412080c180402040e0a020c06060a12140a080c10060e040c06080a1e06060206062e0c0204060e0a0c020a0816020402041208120c18060c0a0c06180e0606040e06360612060c0a020c121606081e04061404141c080412200a020a0e0402060a080a0e0a0c1e06080a020c1002040e0a1410060c08041e18060e04060e1002161406220c080618100c02120a200610061404060c140604060608100614061c0c0201, 10267, 2711770049095),
    (116101, 704, 0x20a2a060e12160602101e021c020a080402040c0206040c06080c040e0a020406020606060a0806220e10061406120a020408120a0806180a0e1c020a1e081624021206060406020a060216140a0c0e0c0a12140a021206040612140c06042402060c0418061a1c0c0c06180c0e06120a02100804080408061e16020a080a020a060218040c020610061206360608060610200c1e061c0e0a080c1204080a1e08040e0402041a06040e1e180606040618020a120c0c060e06060a0e0c0c0604083006120a0c0e040210020a12080402221a0a18021e180a1202180c0408160e101422020a080402100c0228082e060e04140c0402040602060402040c08060612040602120c0a020c040204060e120c100c0c06020604081812100c18080c100c0210320418060e1612020c060604020c10240614161e1a0622020c0a020604180606020a1208040206040e0a060812120a0e0a080a08060a1202061e0c1614040e06041e0614160206060a0e04020616080a0206061012020a181e08060c040e0c0c060c0426060c0c0c040204141804080412241a06040e06101e02060a18020a06140426061006020a060c2604060c02280c081204080606040204080a1202100e1c0206061e0612041202121e1e04060c060e06060a0608040204060e0a0618020a0c02121204060c3c1410020a140a0804080a0e040c2616200a240e0604080c10061e1a120612060a0606080a0e0a0204020a020a0c0e04260a14042c0a021612020a0c0806040c14060412020a1a0a0210020a080a1a0604080c04061a0a080a06120c0e18120a021c020a0c0602060c0a0806180a0e0c180c0a140406020a02040e06060a0e06040204080624061204060216080a0c0c12021e1c0606062c100e040c08040c0e04022202041212080c1602120c042a0804021008100e0a0606080a020408121608041202120a1214040e0a020408120a140a0e040d, 10971, 2718058543408),
    (124293, 702, 0xe1c0210120e060a020a120608060a02180a142e140408060406140c0a080c18180a140408040e0c041e14040204080c06180a060810060c12080a021c0204140a0e0406020c16080a0606080c060412020420120c0412140a140a0c08060c161a100608160806120a120e0a061e0806040e0a081e041202060c0a0606081e0c10080a021612081e0a0228020a02121204180612060204080c061204062a02060402181014040216140606040c140c0a0204021c061202100e12120c10020a02060402060a0e041a040c020c060a0c1406100e0a36021824060a0e0a1a1804020a0c02100c02060c060610081006080612100606021212180a020a0602060a0606080412080c04081e28080a020c060c102a0e040216120206060604141e040204080a020a080a0c06080c040e04060606200c040e0a0210080412020c060a0e0612040c140a080606060c1c081e2a040e0c0406080c16120c14060a061e0e0a0e0a060c0e0406241206060c020a1202061806120a020a080a1806021e0a0c12020a08040e040c0e0a020c0c0a0e16020a020a060c020414060a0614160606060210140a0e2a120a021c1a04260a0c0204021818060406240804060e1c021606020a02040e0c0a080606360624040e0604020406120c120c0c12020c1e06040816081204060804081c0c02100e060c16060e241608060418060c020a0c0e0408122e14040e0604021c0602161202061014220c1404060806042a020a02040e1614060c0a0602041a0a020616020c0a08060a06061404060c06021606020c10180228060816020a0c06080402360606040e1810020a0816020a0c1a0c0a080a02100e060a0218041e06080a081e120a02040e061804080c0a06140402040c08160e12100608100606022a060a0c0c1202061206122e0e1e0a0204021810080c0a0e04060e0c18060a0c080a0c240e06040c0e04260a020c0a08120a120605, 11673, 2723899981042),
    (132485, 692, 0x1e02100c06140c04060e1002100e0c0414060a0608041e1a040c060e180406200c0a021c12200a0c06020606120a06021e0c0a02280e0402060c0a060c120204060e101e020c0a06140a1412180c0604080a021c0206040612200a08062404060806041a1002120a080a2016060e10020a1e080412120c02160608040c1e360e10020c0c060414040e281e060606180602060406020a021e0a1a0610080604180606080c0a08100c020a140a02040e06061e04180c0602060c120c0a02100c181406160c0806040c060810061220040806101202100806220c260a180606080c040e0c241c020a02160e0402061c0e0604020a080a020616080408060414100216120e061c14040206040e2206020c0c0406122a060206100806160c0c0e0c0a080604020a020a080a02101418060c041404020c062e060c021e180a06080604021c081204081c0c021c020a1406060406060c0c0612020c06040c1a0406020c060a14040e10120210080a020c100e06061c06020c2e060e0c18120616140a08240406080a060612020a1a12100806060a0602060c0a020a06060806061c0206040608041e080c160e06061c061814041a0a140c0a140406020c060a0c020616020a121a0612060a1416021c0e04022a16060c06140a3602060c0c042a1404060804060e060a0c081e0c0a12020a12200406181206020406080c040e0a0c18260a08040e060604240e10080402040c0c1a16080c04140a120c14060406080406020a2604120804020616020a182a080a0c020c180a06060e06040e06040e0a080a020c06041406280c0c12020a1a120c0c0610080c040c120e0a1208040c1208120c0a020c06040e22080a0c02040606081e0a180c0e0c0406021c200a020a2c06180414060a020406020a060e12040e04060e06041a0a20180a0612020c1014040c060c0c0e04023c040c020604021c06020403, 12365, 2729292987540),
    (140677, 703, 0xe04140a020a06080a061e06021006062c0414040614040206040614120c0c060c0414100c060e0c0a060e0a060e06040810140c28020c042c0a0804060c021804120e060a080c0a1806120c0e1c0606080a080c060610120222080a0c060212180a1a0a0806041802120a060e0c040612020612040614040602040612061a28020c0a08240a020c120c0c220c2c0a08160e06120604060e06160c081602041e1808042c04120e0604080c120c0604060206040c1e060e0418080a0210061404020c1002160c0e04081606200406021e0c060a0210060e041a06061602060c060c2208060a1a0a0608061002240402121204180c0e061c060e0a060828060e060a1a04060e061e120c10080618060406180e0606040e0604060c0212121806160c140a08040608061806040c0c021c020a301e06020408060a0c02062e08060412020a081c02220810020c0606100210022206021c0e04021c0e0c0604060804080a12020a080a061208040e0402040e060c0a08060406080a061a040c0e0a0e060a0e040c0e1806160c0618020a0e0a060e2202280810020c06061c080a0c1e0c06180e0c04060212041a0a0c020a0e06040606020604080a0c1a160e120a0204020c10020412060c02160e0402120a12120204060e10140a020c040c0816140c120c0c120a060e0a020a080a260418020408160e060a060c021e120c180c0a1808100204081e1e0c040204064406040e121c061410021c020604060c0206062202041206060e10080606100e060a08182404020604120606080622060c020c040e1e2a04140a0c12020a140c240a0606020c0612040c081002220e0c0c10021614060c1e0408160e0c04081c020c0a060210140402060a080c1c0c0e040e0c0420040806060a0e04120c0614181204060804021212120618040206121036020406020a120c020604080a0c060e0a0608040804122a06080402040c0c0805, 13068, 2734442211690),
    (148869, 677, 0x60206180c180a0212101404020a1202160204180606121e06180c060e040c120c020c120a1208040c060e0616081c02161e060e16060206160e0402040810200c060a02280810141c0c12261204061a100c06060806040812040c12060e10020a0e120c0406180c0e060406180e10061806021e0a0804060e1806060a0c080c060406140a1802060a020c12100c0c021e0a08060a1a10021216020406180c080c04180222080606040e0c06180a12061812120204081608160806161214040c060206241c0c0e060a1206020c0a0c1806080a020612180a12080a0606120c14181206100e040206120a020a0212041202040e10021c0612122006040c0816060c02041e020c06100602121206041e020c0c1c02040c0e04020a0e0a060804080a080a0612080a140c2a040e061008062206060e1026060c0c1216061406060a0c02180a0606140a0e120a020424080a0c1a0c060a06060e060c0a081e04081e1212040606080616021c0e1002120a0c0c0e040218041e08120c04080a120c06060612141e0402040216241e020a1806120e1204061206261c02062802040608060a060c240e0a080c0c0a081002160c0810140402100e0a08060406020c06060a061218060c0e1e18042604061202040806042a141212041802040e1e0a3c0c020604060e0a2004061802041a041a0c0a02100c0218160c021810260a02060a0210060806060406081c2010140606120c0a0c0c1e08161a22060806061204060e0a02061c0c0c021e0604080a080c0c10140a021204060e0a24080a02120412080a140402061e0c0a020a080a0206040e040c080604060c0e240c0a12020a02101412041a0a061a0c0622080406120608060610080a020c0a120212041a0a0e06160606061412220606260a140c0402160204180206040e1012060c02120a020c1c060203, 13745, 2739120081884),
    (156250, 631, 0xc020a3c060c0804080a14120a0212160804561c020418020a02100c0c08040e06041a060a0804020a080604120806041a060c0a060c020a0c1202100c081c0c080a140a0e0c0402040626060a0e04081612140c0a06020a1404060810122004020c16140a08060c0a260604061e0e06040216081210080a021210060e060418080a0c021816020616020a06021c141608061c14100608160e04120c060c080a0c0c020a14040e10021c021602041a100e0a0602060606040e101a0406260402060c100216020a061e183606080604060e120c2808120c04121a06180406020a020a0c120c0806060a060c021c080c060a0612061a060406020a0c38280e041406120c040204083a08040816060606021e0a02121606080402040c020a1208060a0e180606240a0e10020a060612021e041806020c12280210020c0604020a0e0408040e340e040614120a080c060a06080624180c120a02040e16020a020a0e22021c021c0602040e0c16020618040e0c040c0224040c0e0a06060806100806061602040612060c08040c0608060a08100606141204061a060a02160e0402220e0a061406040204180c0c12020606040c141e220602160e040210020a0c06021e0a0c06080406020c160e061e060c0a0218160e0a260a2006041202040c0c08120a060e06182208040e0606120402041e0e0616020c28081002040602060604181214180a060206060a06080c1e0a081602100e120a020a0614060616020a180c1404080a12020c0402163c0204141810020a080a020a02100606021e12120402060c060c0406140a080a0e0c0a120c06020a1a100e0a0c02060a1806020a020c0a080a02041406060a0e061e04081002040608161203, 14376, 2743259061507),
    (164442, 678, 0x20a061a0a06080610140c0a080c0c10020a060216080a080a18021e041404120e060c100c0e0402040602062e1208120c0a02060606160816080a120c08042012060c1206040606080c1c0606121a1e0402040824100602060a1a040c0e0a060c02300a06140c0c060c0a02120412020a082e022206021006081002180a140a060c08160606080a06021e04081c020a08040e04060c08060616080c060c0a08100e06041802040612061410060c140616021e103204020a0806060616080c42180a120c140624060408100606020c0a18020a1e0206041e0818180406020a080a020a020c221812020c100c0812040602120c04060e04200a02062a04140a0e1602060a0e06160e041a040c1422080a08040e1e06100c0606080610080c100c02221a0414040210140c0c040612081804020c100c020c0a060c060c020a020a0602100c08041a0c220810021c0c120e06060a0e060a0e180604380a0c0e0a06120e060412181802040602061810020c0a0816022806140c1c020c040e06160c060204080604061802100e06040e0a0204240206061c1202060a0c02121204081204060614060a0e040e1c0c020a120812063606040e0a06020c0a02060426061012060e240604140c16120e040e1c0e040e06280c0e060a020a02102024060a0e0c04060e060a0806040c0e0a080c1228060e0a0c0e16080402060a0c1a0a1808120a020412080c1c12020c10240618120c08060408281202180604080c0a1a0406080a0e0616021608060c2a0a02120a020a30080a02101404061806061418040210121e0c0216060e040c0c0204020c0606040c020a0206041208040e160806120616140406020c1206061c080418021c0c020c2e080a06120210201006080c040c080402060c120a08041208040c26120a120204141e1002300a0806120a0c260a020402, 15054, 2747487521064),
    (172634, 669, 0xe0c040608060a0c080c16020a123002060604020a0c1a1006080c0a08060a0e041410140402040e120a020c0406141e040e0a141204060c08360a0806061c080408060c18040c0804061e0204180e06060a1206020c060c04080c220c0c060c020a0c1a0a080402120a0c1802122a0c0c120616080a02121e180a0204021e1c0c0c02180402040e0610240e041a06160c0608100608060a0e040818040606020a081e04060c141606080612061816060c021c06060e0a1a061c1404060c02060a0204060e1c060e0c040e060408040e060a080a0c1a120c0a021212060a1208120c041e060806040e060412021e10060608061c0606081002121810020a0e0604080a0606141008100e1608160804060c0e1e120a1a040812040c0602060618180a06021602121204120816120e040e0a02040e1e0a02040c0e2206180c02060612060c30160c081206060c061014041e0c020c1002281208060418080a12060602101812260610081e0c0408060a0614100e042a08101214060c04180608060a1a101224060c080408060a0234081602060c0c12121c060e16080604020a0e043206101e080c1606020408060a060e0c28020a0c06022802060c1c0810060e040e0a1e020406080c060406140408060a0204081608060612120c0a26040608040204021210081002280210140a0e0a020a0e0c040806040602041a04061436100e1c0c080604061e0606021e10020408100e0c0a120c12060e0c0604301212140c0406081e160e060a1e0e04061418040c060c141e1c0206040204021c060e24060a0c02120a06020a0806040c200a0606080606280608040c12060c0e04021206280e04120816080c1c1e0e0604140a02060424020c180a2a120c2a02060a0c141204180e160612060e0a1a040204120c060c26120a1a0616020400, 15723, 2751455528064),
    (180826, 684, 0xc02040e061602121e160c1412060630061006020616080606120a1a1206160c080a0e0a060e060412020612040c0602060c0a1e02121828140402120a141006020a080c0c040204081006080604023010060602060606161e06061202180402100c0206120a140a020a02060a0e100608160e04080a080c040812040e0a020c0c061806041e060c08120a1404061e060612180804080a061a060a080408220e160c06020a0c020406080c040e06160c02040608060c18043804020a26040c0608040602041a0406021606120c0c02060c160602160e0604200a02100614060c1c020a0210081014040e120a0e0a0e0a0216021c021014160c0e04060e0c04060e0402042a02100c0e060418021204300c021e18160c240e06161206060806220204060c1a04200a0e0412120e0c1210060602240624040e04080a30180602041206061a1206040212040c1e081e0a020a06020a021806061c020c161a0a0c12020a0206121006020c060a0c020406081606021c0c02040c0c060e0c04060e040206040e042612060a060806060a0c1202061806220206120a02040612020418020c10020c0a02120a0c06120e060a0608121c021602041a040e0a08040e0a0e10020a141c1e140414060c120a060e16080a021e0c100612060c0e0a062012460c1a16020a0206161a0a0c021e100c020c0a06081012081608161a0604020c0c101218060e06040c060e040e100c0224062404060c020a0e0c12061216140a0602120c0a081204021014181c0c08060610140a0c020604060c021c020a0e0c0408240a06080c0618060a0c0c080c180402041e020c1006080c040c020a0804120c121a0c0c0604081e0406080a2a0246020a260c04021206040e1e0a02100206061c0804260c0616060e100216060606080424320606040806041416060e1c080a1404081606080a06080608, 16407, 2755325101954)
  ],
  #[
    (189018, 677, 0x60c101a040c0206061014160602040e0a02041a0a0c0c0e180a0804060806060418140c0c0618101e06081c080a0e1006060e0a060c140a08120a06060804080a080c0c34080a080c0c04061e4e080406180e0a0c1404060c020a0e06060a12141e06180c1e0a0c0c12080a0c02040222180e0c1012061e06020616080a06081006080606060c0a02221a04240e0402061204080406081602060402040c140a08040212061012062c0c1e1c060606020a122a06140a02040e0a061202060c0a08120402120a120e04020c1246020a120e1216060c02221a060a02100c0c0606080a02101404180204081e060604061a1608040e0406060e06100c02060418060e060414041410020a02061008160e04020a0e0c0408060a02041a0a14160618020a060804060204081c08060a1a0c1c1e02060420040e06040818180a0c2006060a0608040c0608180a0c0602060606180616020418020a08240a02161410060602062e181406060a080a0612120210020412021e060408061e060616020a0e1006180828120e040c0c120c06020c120a140c0a02061804141006180608100e04081206041806020c0a0618020a1a04062a060e0c22023004020a060816181a1206060406022a040c020604020a08060c0a0c0228080606040c0c060e0a020a06020a0614040c2c0c1810201c0216080c06040e18120c0c0414040206160606140a060c12080a0e0a061a22020a0e061602040c020c0a0e04060608120c0c120a060e1002040e0a0c08061c02220c0206180c1212120406180816020a08120a02060c0406020a1e020a060c0210020c100e0a0e0c0408060a0c021002221818020a0e0402060c0a0804061218021c140a020432040c0e0a0c02280212120c0a020a1a3a02040e0604140a1806020a02060a1a10122406120216080c10022a0a2a180c1814, 17084, 2758985733429),
    (197210, 668, 0x42a020c0a0e06100c06060e041a0a0e060a021e22080c061606021210060e121c02120c0c0a080a0c061202040e1e100e04120c0602120412021612060e0a2a082a0618040c0c0206182e0806060406020a141606180608160804061e06060e04020424020a06060e06040e062e08120406140a0804020402160c060e123c060c28020c100e040e0a0c0e100e06060c1e060a020c0a081e04060c060c0c1a06041e020414060406120e0c06120402040e062208040e1e10060c0816020402160c08060426041214060604061404020a0c060626120a0c1a10060e1804081c0c122406121e0e280204182406120c120816060c0806040c020c1e0a0e0a0e16060804022e080604020a020c061c020c0604120806060a0e041418100e1e0c04020414040e0a081c060e18060c0406080a1e06060206060a140a1a12160e042a0c0602120a06080628141006080c1204060c0c02060a0c1208061c0204061206060e10060c080a0e0a08060628140a1e06020c04020a0e04020a0e0406080a1e0222021e18100806041a04021204020a240804080c06042402040e0c0c100c080a0606260604060810060816081018120804261804020418020a080a18021e0a0806040c06020c1e06161410020a0e04020c0a020a0612060602060402061c3c0c022802101e020c060426100c1202040e04140a120e0a0806060618123a0804080a02121c0608060c040e06040e0604062406020a1e020a080a06140610080402041e06080610243e060c0412020a12080a080c040e0c0a0c06241a160c120818041e0c14041e0806060a060c0212100c0e06041206021c0612021e0a0e0a140c0406140a080a1802040e060a180c1206060810020c0606041802040c0e060a020c100804020a1a04240e04020c0a06180c1212020a0c3c0612021600, 17752, 2762445795585),
    (205402, 662, 0x20622120c080c0a1e0e100e0a020a0e100e060a0804120806100c06140a020c2404061a100806041a100c0224120604020a1e02100e0c1c0c1a120a0c020c0414062404060216061412040206041e14060406020616020a080a0230123c0a020a0806041a0622080c18040606080a0c060210061a0a020c18040c0e160c021210020406302c060402040c0e0a1a0c0a060e1246020a12020a0218060402120a020a021002040602100e1e100606080402180a20183c060c1006060c0c0608061210020a0e120a02121212061216140402040e040c180e0c0616020a0608160e0a12140a1a0c0a1e20060a060614040e040c1212020c220c0c120e043602060c0a0c1404020c120a140412060c08060a0e0408040e0408220e040204020c0c0604060c020a0e0c1608120a06060818060c0c0a0804140a1e060c0204021216020c180a020c1e16081614061e040e1602060a1a040c0c12020c061c180c0614041202040c2a02120604080a0c020612240a080a0828080a0e0a120e121e0c0604080604381e100612061e0612020a0806060a0c061a0414101406041a0a0806060c06160e1e18160804060608060420061c020a0c140c0414160c06020408100618020a020a08180a0806040c141012021210082416020a02041a0406120c0608041406100e0610081816060e24040e0c1c022a0616200a02040c1814060408060a0204081c0228080a020604020406062a081c0e120c100e0c06040e0a0e0604121214041a0c0c0a060216020a0e040c060e1c020a0e0a0c14041202060a120218040e06220c120c06080a1a040c0e042a020604020a0e06060c1002043206180418060608060c1c020c0a06061a0406140c0a02180402100c120e1c1a0c12041e06020a020a0c06021c0c02040e060408040e0a0c0a, 18414, 2765735627530),
    (208333, 250, 0xe0a1208040210081608060406122a06020a080a0c1a060a080c1c0602041802040e06060a082e08160e0c0a0c021c061416020a1e06020a080a0e0a1a0414060c040612020406020c060a020a06060e0a180818060418020a0216060806120c10020c1c020604121e0c060822060c1404080c041428020c060a0606020c0a0834060206060414041e32300a020c041406042a081008120c06060a060e1c06020408100e1204062604080a02060a0c020c040c0c060606080402181e280204081204080606060c10020a0e040606020c181e04200a0e062214042612280204061206080c040e1e06040c080a0c0e0604060e0a0c08060402040e, 18664, 2766944131897),
    (216525, 660, 0xe100c1e140a140412060218120a021c1a041a1006200610081006080606040c140a180e280216060e0c060c0a061e0606080a061a041a040e100e1e0402061606241e0e0a200a0e04060e0c0a020c041a12060408160602160c080c12060c0c0a2a06080412080a0212240a0e0c3a061418041a1608100e04120e06041202040c0804120804062012060406060c0818040e1c02120a0c020a0810020c0606060c0622080a080a0c2a0c0e181006120602160c0e10060804260412060c080a020a0c02040e0c04140402040e0a120e06160c0e06061608280e0a0608360a08040e0a020c0a20040e060a200a0e060c2a0a060816020a0c080a0c120206120a0612060608060a0c08180a06020c16060c0c180e0604140c060c2e06080606100804021008060a1a0a0e4c12060602121206220608060c043206160c0608060a0e04081c0e1038040c26040c120204141006140a0806121218120a20120a14060a020424020a020406082a060a0c08041e060e040c12020a1202040e0414160e0a020c1024060206180c100806181e04140a060e061006080c18060a020a02040e06060a1802162004140604020a020a202806120e060a020406200c040e0c040c02061e0c16080c0604260c100c0c12022a180604180804060e0618100e04020a1e020c1804021210060e060a060804141002040e040c0e0408040e0408041a1210060c08180406060c060e0a020a1e1a04060e10020604080c12041818020a060e120a0c0810021810020a02040e060a0e1614060c0a080a1e080c0a0c0204060e060a060c1e02040608100606080a020c0a060e0c18221208180a081804021c021c02041410020c22061e080c1c140a0816020a0e060a1a041212020c18180a06020a02060414060402100818100204080c1e03, 19324, 2770052930792),
    (224717, 674, 0x60c10060824040c06080c0c0a06240e0c0a1206060c060e0616260408180a0806040818060a0c060c0c0804140612041202100c1e020c0a060806100c1e0618120210360602040602062a16020406240e10020c1e040c200c1c02040e160e0c0c0616020a0614160e061602060c060a0c0806040e060604020c0a0206043812041a040c18020a020c120a02100c020a0e06060a0c061e060e061002101806020408062a12061c140c0418060c0e1e041406100c06201812100e0a0c060c020a08060606120414163002041e020a020c0a0e040222060810020c060c04080a021e04020a2012121812040e060a181a0a0806040204061e060c02041e021210060e120a021c0c080c060a080622020a0206420a060816140a0c0606080a06020418020c3a0806040606020a0c1a302206020c0c040204080a02040c02121e040e04060c0e0a1a0c0a0c0608060432180a060e060a060810022802161a0a0804081204080406120614060a0c241a1c0c08060c0406123c06240206041a0402060c060a0204060e0616080a1404080a060e0a020a14040204081204060e120604021c02120a0606080c0a1e0e0406060e0c18040c0e041802120c060a0828020a080c041a1c061e121a0a0e100606080c0c060c0a0c0210080402100206100612240e10080604060e0a0c0e160c0c0e0402061e0414060a0c02040c0c080c1c0212040608041e120206060a0e0402100c080a080646081e10060e1614160606060e06041404020408161a1216020a20041802062a0a14061e0c0a180806060a140604060e0612182802040c022802120a1a06120a080a020c0a120204020a0c02040e06040224120c0c06040c06021e06062404061e0c0c180618020a1206141c02060a021612080a0c1a0c040602120406080c0c10181208040206180a1e0602100219, 19998, 2773108439644),
    (232909, 672, 0x60a0e060a08061804080a1818020a1e020a120c06140a0c0e0a061404121a0a0e0c1c02060c06100602120a0e0406181a042c2a0a12021012180c08060c0a0206160224060424060e041404120810060c12020c04020c0a143c0a081810120c120204080a12080408040e041a0a0c021002120a020c0a1e0c080a021008061206040c06021c121a1c2616021c0c0e0c0a0c02100216080a1202060426120a020c1006080c1c06020406120e0a1a0a140a06240e1e04020a0c20061608040e0412260402040e0c040c020c1002060c0a081012060606080a0e2806060e060a060c08040e040c1e0e160210020c0a0222063002060412060e12040602060406020c0c0a060804060c2a0206040e0c0a020616080402120a0c080c120a1a0a0e060406141608160c1a10060804020a0e06040e0a080a0e040e0606041e0c2c0a180e0616020618060a020a0e04020c0a0606060c1e02041410060e040212061e1e0a1202060a08060604121410020406021e0a080406081006020a1a18060c040614040602121806120a0c080402102a08040e0a0614100c1a0a14040c1a0436140414161e082e0e0a0c080616080a02160210020606040c0c02061804020c1204081002040806160c0c0806060a06083c04120e0a0612020c0c10020c0a0806061012021204081c1a10143006180604021e1c140402040e0a060608100c2c06160606080606060a0c081e12040210141804140a021206120c10020c0a14180618101a0a0e10020a060e1c08040614040c18240e06060c0606100c06020a0c1e120c140a080c1c020a021002100c1808060c22080a06020a12020c2802040e0604060e12041a042c0a02120402040222080a021806100e0402043204020408060a0e0a140a020a06180e1e1008120412080a020c060a0c062012101a0c1006080b, 20670, 2776045672689),
    (241101, 641, 0xe0a02060a020c0a0e101e08060a1e0e060a020c0a060c0c120e1c0614040606080c061812120a0810080a0210142208060c0c0624040c2a08120402061620040c0804023006061804120c081204080c100e0a02040218060408160e060a0e04240e06100602060c180414041a100612020c0a121e080a0c0e0a080c0a0e040804060c141c140a0206061c02041a0a0e04200a0e0a0c080604021e160804140a1220060c101a04061a181206041202160e040212060c04081c0c08160c1202040e060c0a0810080a0c24121a10020a14120406080c0c1006141804060216080a08061018060e0a08060a0606140a080402060a200604060c022802060c0a080414040204081e120a12061202061e1e0a0e040e0c041a060a02060a2a0c0c1a0a08102616143a0816060c120c0c060c0e0406060e18100e18060a02040608062e021002040e0a1808120a02221e080c04020a020a02360618040602160c08060a0606021216060c0e12240a0e16080c041802060a0c1416080c0604260604061a04061a1e0c0a02280e0a0e1204140a08060a200414120c101808120a020c06162402120402042004181814060a02280e060a0e12060c040e04061404062406022a1c140c1c0212101e020a140c1204060c2a060c08160c06081e0402040e0a020a06020c100e0a0e18060c040e16020604080a0c14060a0606081e0a0e0618100e0a02101806020a02100c1a060402041a301612020a0804021806060a0c1416060806040204060e060c0a080a120e0610180e160e0a0e1c02100204061e02120a0e3c120c041e140402040e06161404080a0822060228140c280e04020a240e0406060c02041a040e0c100c080a14120a0c02100218041e0c0230221802181209, 21311, 2778749669719),
    (249293, 675, 0x1e0414040c060c0c06260a0204140406080a1416141e060a3e060a0204080a02060a0c0c0608100806041a040c0e040c06121a10020c060c0c0406080a1a0604181a06040c0e060a18060c120e061c06080a0602180a0e0c1c020c0a020a0614041202120a0c060806060a080c16020402220e041a0c0c0a0614061210020c120a020a140a0c060e040228021014040204020a0c1a0610020a12260c0c060c0c10020a0c061404021c0816140a080c0616080a2a2a0c0e04022418061608180604060206040606080a3206100602060a060608041e081204021206161202041802040816080c120c040c020c18041e240c140a0c060e0a021c0c06140406120608060a060e061012020a021618182006160602040e161e020a0210120c021c20060c0c0606061204081c020a120e0a02061c020418021c060602060c180402221202060412062c120412080c0a0804062a1a0604021612021614040c200604061a280e042604080c040c02100204181a061606060e0c0a080c0412021c02040e100608061006080612160e0c0a08060616060c0804060c020c0a060c06140a0204061e0806041802121612020a060c080c12042c0a0c0c060e1014160e0616120806060c0a140a0c060c3c0204021c0218040c080a18020406180e060606041e080604081804020a12020a1818200a26041406061206061e0604080c10020a080a0e042a140c0a122c040c180e06042c06060a080a061a100210180804120c08060408040e0c28120c020a1208040c0e04020616060e0610060e1c141e060c040e101a0418020a0e120a12080a0e0a0230100c02060a0c0c080a020c0414060406060e180606040e0a020a200c101404080c040c08042402040816060210061404021614060a0c0c081c021c021206040606080a0c140a02060414161806081c0e0a0f, 21986, 2781502665582),
    (250000, 58, 0x1002041404140c1e0a080402041406100e12100e0c0a06121a060c0c280e0406141602060c040e0402220e0a0204060602160e060a1a0c0c0611, 22044, 2781734997318),
    (258192, 647, 0xc040e0c04080604020622061e08041a0402061c061a120a0e0a0204020414280608340e0402041202100e120c10141e161410020408100e0c04061e0602120a12020c120a0e040606080a0e0a12021e0c060a1412100806100810240e160e0a12081c020c0c042a120c021c0e2202160c1a0a08041e060e0a020a061418120604060c021c121e0216060e0c180606163c080c0a02060c06100e040804180e160810020a021e0c04020a0e1804020a140a080a08040602242404060e0a14041e0c08060408041404180210141c060608040c0e04020a0e18061e0c0a0c1410360602040816080c04020a0206180c0406060e0a0e060612040614040c0e060a060804120c02100c0c0806040c180204180c0806041406060a02100e24040c14041e2414121c021c0e0a180612060608281e080a0216082404020a12120e0616240c120606020c06120406061212020c120a02061608040e1e04080a0c020a08060c0a08100e1602120a0c0204140402061c060e0a06061806080c0c1608060604061e060c02060c06160e221a040e46020414180616120e240a140408160c1206020c060606040828020406260c061806040e0412181a1806041206181208181c120608060c0c0a080a0818121204061404060618140a0e100c0804060606080426162a080c040c120c02160602160e0604060812040e0a021612021c181e06180e0a0e10020a022a061204060608060c0a08060406180606020c18061c0606181a060418020418020a02100204060c02060c0a061a120c060a08040206121e0a0e0a02040c021e1e12040e0c040810060806060a18020a020c060c060a0606081e1824282a020a260a080a0e062a122406160c0806361e1006180e1212100602060606040e0606, 22691, 2784281424437),
    (266384, 653, 0xc0a0602122404020a0c0816122606120610080c060c06040602160602041202040e06101a04241e080a020a0e060a0c06061406180a080a0c060206520206061c0804060e04021c02120a0c0c081804060e04122a0204142404020a0c02060a180e180606060a0c060618020c2a100e0406060e10020a120c140604080a200a0210120204080a06060806040822261006060c120212041206180228181406220c140c0604060c08160c060e062a0a200a021c0204060e0c0a080c0c0616021006181a04020a080610020a120c02040e06100602102a021608062e1406041a0a020c0612060618040c02060a0c022e0608060c0a020c040e2e140a060e04020a120c0e04080a080c04260a080a0c0606060810180e1c18080c1c08040e0618220c1802220602060a0e0c040c180602061006180e100e0a021606020a0c140a1a160c08041212020c060a080a200a0810060e1806220204080606060a0206180a12021614180604020c2a1e0622181808040e0c04121208060a181e0204060c12080606040e061c060e2a040c0c06020414120a1a060a080616140a140a0c063602281a0c0c060a02100c0e04020c0c040e0a080a141c0e060a020408280210120c080618060424061404121416060804120206040c26061006080c160204020c0c18180a0c300620120402060a020a08221a16082218060602060a0218120606041a281a0408060a0c12020a14120a0614060a0e0a0e04080406021014061e0a060e0a0828060216080a0e0a060228120c20062a0a06020a120608060402061c0216420e0a080a08060604080a1e021e10181412061008101406040c0e0406060e040e160608060402041a0c060c0c0c0616080412140606100806040e10141006020a02121006180c08160e04, 23344, 2786770973599),
    (274576, 656, 0xc1c120e04020a12142a040810201206060c10060e0a0c020c0a060810081002040e0a0c0c081c0e0c0a12080418020c0a060c0212181e0612060a0e220c080a0c2c0a020c0c040c20121806040e1e101842080a1a0a021606020a021014280606180812040e06180a0606020c040e1c020a06020a0c1a060a06081008103204021e060a02161202180a18081e12160e040e0a02041a1e18041a0606040810020c0a0602040608040c120c1202040608120418020a020604081e0a2622060e0a120206160c021c0c081006120c060804080c1204141002101806140a24060c02121006180212042010020a060c080c1614101a040606122c0a02040c080c0a0e061e0408062202120c120c0a0e1006080a1e0606081006080a0e2812080c1602061c020c0c120a080c0a0c0806160c12080604060e0a0204080c12101e020a0806100e1c081c0608060c04080c10021c020a060608121804060e0a020a1818020c1606021c0e061c0608101a0604081c3c0804120c081204060c12140c0a12061412060c12040c0806280c140a020a0614040204061a0a08060a2418060e060a020a080c0604020a1a0a0e1c14060610020a061802040e0604200a0608040c0e161202120402040216060204060c020a0e04081c2012061806221a0a06020a020a0608061c14243c2e06080c040e101a04080a1212140a2016060e061e0a2a02120c1006060206060a0e061804120806060a120e0a020a06020622020604060c0204060810020a0806060c0c060a120204060e040c020a120c06020c060a020a0210140c180a060216060c1a04020a0e040606141804060222300c1412060a06060e04060e06060c0a0206180418021014041e0828080a0c0204020406081006081e040c261c1e020a021c021e060a10, 24000, 2789197453665),
    (282768, 662, 0x3606040606080402060a2c120a0c06080442060614160c0e0402100206061c240204080c061c0c020a08360a0e101802040602120c0622080a0804120c0c0e0604021c06140a080a02041a04060608060a060e0a1202220e060a0204060e04020c1c02100606020a0804124e020604261206040e0c060414060c061602060a06141002160806160e240c060a140a1a120c0406080a06060608040c0e04080c1006140628020a08160c060804021008220c0e060406060206160c0206041806080c180c280224160c020a061206141804060e06040c080c042c0a081204021c0818061204080a0e0a120816061e14060a1806260c060a141602120a140a08041206060e0a06060e04020a120c1e021c080c0a08060a2c10080c062a300a081008061e06060406020a241a1206100614221e0602060c0a020c1206100806040206220e0a0218100c0210140c0c04060602120a120204080628020406020a1416181406180a0612082a0a08180406080a02100e1c02041404081810080c0a0c0c1206202a1006060206180c12101404021e060406260c0418060e040222020412020a120210120e060a3602060a260a2016080412060c020c100806041e060806063a020a0e0a0c1e0e041a100804140a020a06120e1608060604020424020c0418120e2202220806180604020618041a0a0e040c14060c0604260c10020c0c04060e041a10140604080a1412040608160e181608041e02040204120804080c060c0616020a060204060e102c0a0e1e0a061a0c0a080c16080c060a121806020a020618060c0a120c021c020604021804140604120e1210020c0a1e060c18140612100602060610022a04180606080c180a140c0406080c16141204060806040606020c061804061a0c100c020c040e0c06221212080402, 24662, 2791573332738),
    (290960, 641, 0x241a120a0816020a06120c1806181a04061806020604021e040204060e042412060204120c0810021804020c0a14060a0e0a0804140a44060a0e0a080c06161404120606181a0a0602060604020a0c0c0e060a060e2808120c0606040204301208041208060604300c0e061e040e0c040e1020160c08060a0e100614100c080c06180a0c06080a140406021c1404080a02120a020a021002060420040e0a06020a02120406020a061a100210061e18020c060a060e1e0610120222080604120804024006060c080c0a021c060c0e061c060e0a0e0616020a2004060e0a1a0a060e120604080a022a1c140c1008041a101e26060c220e06040606021c080c0c0624101e0c080a0228120e1216080c22020a2a0c2c0604240608060618060a020a0c060c02040e1c0c0606080a0804140a0806061c020a2c040c06082e360e1c120c0c0c06080a02120c0a08060a0e16120e060412022406040216060e06060406080a02041a060a0e040c0c0222200c28062c1c08221a1e0a020c06180a08040e040218040c421e020c042a0806040608120a0c020a18060612020a0210020c1e0a02040e060c04141804060606120c2c221a100c0204021e180616080c120a0c1202060c0a0c081612081012140c1e0a120210181206020c0606041406120a0204020406020610060c08160206120a1e02040e0c0a0c0c060c021206060a1412060a06140a080c101e1218020612060402041a0a120c02060412020c06120a1802060a1214181204080c1c240c0216060e040608061602061614180a121e020616020612040602120c16080a0c0218102408061c420e0c0a38040e0a02120414060c04060c02040e1c181202060a0e040e2a04020412080c12040e06120c180400, 25303, 2793807832811),
    (299152, 629, 0xa1806080c18040618020a060c063206282408060616021002161202180a0e10020406020c10140a0e060c0604142e1e061a1810020a1a041406040c140414160e0a0e0a020a0e10020a0204360606180e060c0a08160212040e1614040e04081c0c0816020c040e161e080c100818120c06060406060c08300a0e0610060c020a12121206060e060c2a1c1a0606040e2a16080a1214100e040c060c1a042004020a021c0c080a02420a02040812041802040e04080a020a061406040e060c182404060210020406200a02040e0a020420043c08060a06300c0806041202060610080c121816080c12100c18060e0a0612140c0a0206061c0602160204020a08060406060c200a080a08181804061e3e0a14040e0c180436120206040c06181806180e06160806060c0c0a1212020c2218060c1e0206180a02041a0a06020a1a04021804081206120a1e080c0604060606080c0406141c1e0e0a02060c420c16060e0a140c0616081c0606081e0606041202040212040c081204060e040c0c12020a020a081204182408060a0e060a0c020a061a102a061e021e04180c12061214060610140412080c060c040e043824180a0608060c0a120e2a060c0a122a060204240806061602041802120610080606060a321c0e0604240c0c1e0c120804120c06081012061a0a0602060a0e0606061e041a18040c0c080a0e1804060606020a120e220c0e040c08180a08121012080a082802180a060828020a020a0c140a06180e04083016020c0a080c0414040c1a0c1c081006140a020c100c021c3206040c08120c060c0a180e0402122a040204080a0c06200606100e0424080a08120402181e0604020c0c2202041806080606100802, 25932, 2795939893610),
    (307344, 669, 0x2240c060604060602060a2a0c02100206101208120a020c0c22020c0a122604020616060e060a06060e04061202060c1c120e0a0c1404020c1c080a36020a0e1608040c06080c0c060a0614060a020c120c0a080a0210021c26040606081e100216020a080a060c1e0822080c060c0c1c180e060a2c060604080a1212140c0a020a060216023618060c0a0806040c120c120c18080604020616081204060204061808060a020c0a20100e1806060c0a3e040c0c06020a0818160e040602042402120c0606041a0402040e040c120210120612080a0806060c0a060e16180c080c160c2402060c040e06060a0c080412021206040c061202120a0608121c021614061e06061218060a02181c080a0c02040e0a060c08040c0e1816060e0a12120c140c0a0e160e1212040e0a0c0206041e02041802041406060a120204080a200402120406200a0c140a0206040614040e0a06080606040c0e281e1e06080414160602101404140a060204080a060606020a120e060c060c121006080604021e0a0c0c080c180c1e121012140c040606020606040c26061818100e0c060c460c12020a08060c220608160210020418140c3a2c0a0204020c1e060a060e060604140a18020a1214041e06020424081608040c08061008120a0804022e1e0804021008040c12060e061612020c10020c10241404020412081c020412060c0e042c0610060c0c0e101404060608160224040c080c061c020c0a0c081204080604060c021c080a06060c0210081e0406020c0c2e0c0204020a121808040e101e14040c0804021002161e080604081c0204180c020c120a14101e14060a0e0a0608120a0818060c0a14040e241e0616060c080c0a0210020a121e060e22021c0c06080c16020402181c021008041208040218040c06180614161a10060c0812, 26601, 2798145780250),
    (315536, 636, 0x20604180c0e060a020c100c02120c040c0c24200c0c06041818060c02341206060e10080c0a180216061a0414060a0e181c180e061c02060a0e180408040e2a0a0e04140402060a0c1406100e1006180e0c121006022802060c0a1e200402040e040606080618100c0216080c04061e0e0426120604020406020a080c10020a0c0c0806041a04142e060e16020c0604060c140a08160212060a0608060c04060804061a0a1e063e0a0c060816080a020a0e060408100612081608042c0a02040e04021216062c0616060e0a080418020406021e0c18061002281406100e060a1206021602041e140402100c0602120a02180a082812180e0606040e0c1204060c12021606020c10020a08040c060206040224280e060c060a0218040c0206101a12060636100c0228060e040c2a02040618021804020412062c0622020604060c02043c14061c0c0e160c0c060c06140406020c2a22060806060414100e0c0c3a0806060c0c0a121412041a0c0610061e020604120c080a1806080402060a0e041e1410240e06040806062404060c0812040c08060a1a12100204181416080a1e0606020624060c28020a0614040620061006021e0c2806021e161404021c0c0e10020a200612061e06041e0806181006060c12021002120a0c020a080414041e0c1404082a040212040c06020a080a121e14060a14060a0c021008041416060c060204080a260c06040204180c1e0602160e04081c0c260a0c1412160212180a0e04120e0a06020a02060a0216140a0e0c1c181a0604060602060a021c0e1e063c040804080c0a06080c1e0a0e0a0e221e14100c12020c100c08063a1a1612020412120c06020412140606220608060c1e0a141c0e0a02100e0610, 27237, 2800187570481),
    (323728, 665, 0x60408300406121802060a020c120c1c02220204180216061e020406020a1202063c1602060a1a06340c06081608060406181a120604021c060c0c1202120a0e060c0a2a18020a020c0a141228141002040e061002060a020c0a0c0e04060c26041a040c0806062e020a0c08300a0c02040608101416021e1c020c040e06060a060c021804080a08160c02240a0c26040e0406020412141606080a0c0c021c120e100c02061210060210062628021206100e0a060e0c0408120a02060406020a0c2a080c061204060612061422120e0414060a060e0a360c020c040c0c20060a0804060c1e1808121c0e0606120a020a141002121c0216060c081e060616120e100c020a260a0c0e0a021204021c021206041e1a0406021606060612021206040c020c1002100c08061e06040812040e2212020a020630060a0e04021c08040602062220060a020c0a140616080c0a060608100c020606100c08041e0608040c0608180a14160e0c0a120e0a0c0e04020a1404180804080c06041a161e1e0206041206021216080a060602100c1e020606180c0a08040206120c0c1c0c080c0a0222141e060a0e0c0c0c041a1c020a0e04060c020a02060a0c0c0e041202060c0a02060c180a14041a3610060e040c02060402220212101e1208041e08060604021c020a020c060a0816080c1e04080a060204180612240c0206180610060c080c1c080a02120604022a0a0204061e120c080a080c2422020a06081012080a080c1e04060e120c040c0c120206061c0210080a06080a06240e0402060a12020c0c040c2606060424180602061602100e0a06140c120a140412140406140c10021204060c08040c180e06180c0a0e06100e04021c1a0a060c0c1e08060a021806161208181c0804240204060e061c0c0e040e0604140a08040a, 27902, 2802268567737),
    (331920, 656, 0x20a08060c1c021612140408100e1c0e04021c0c2604060e0a0218040204060e04080a0c26041818081602120a02040e0c061206120a080a0e0406180c0c0606060e1c1212140c040e100e281a0a080c0a1202040e10021c02041412120a02100608060412080a02120c041412060630281e0602040e041406180c1002100216021018060804020a0e0420120a06021c061e06080606041202120610080c0604062a081206043c020c0a060c20060606180406060806120a020a0e0606041e06120e100e1002280c120806280e0c04080a02040c0c020a0e0a1802060a0e0a18140c0a0c060216061a121c141e0a021204060822020a08101802060418200c1614100c02040c021c020a241806021e2a0a080a0e100206100e0a0204180c08060616061e24062a02060c060a1a04020a08061e18040c0e0c12061c080a0210020c0a02040e0a0212161202100e121006060e120a1410020a0c0204180c060c06020c060406140a0c020a0206360406060c020604120c0e0c042402060a0e101e0630080c240606040602060a200406021014160804020420340620041e06080606120402181006020c040c0e04020c0a022206120c1208044410021c0e340620100e120c060402040216060c020c041406221806061e06080412140a020606100c24061802040810020412060e0c04020a0806180c04140a1a1c020414041a0a0e04060608120a201e060a0e0a02061e1612020a02100c0206120a14280c02100c081006020a0804060804021804080a1e0804120216081c020a080a080a060e0a1a0a08100c0e060412021804021e1c06060e0606120412020a020604081006061e140c0a1202062a0c100606020a14120a080c0c060c040810060e1614181e061206041404142a121002040816081e, 28558, 2804269811755),
    (340112, 636, 0x818060a0204080c06041410201024141816020c0604060c1e080a0216141c06020c06040c060e040c0c061a120c0a1a1822141810200a0810121a060a08100c180e0c0a0c020a060e040c1404121a1806222012101a0a060c240c0e040c0806100e0a14040e0a321c02060604140c2214040c0c12080a020412060e16060210020c0c0406080a02040c0e06120604060e0c040602060c041256060a121a040c081e0c04020a1202040602061014180c16080a1418060a0c080a0c0606120218280204080c0616021e041a100e1c02060c06040c0e0c0a08040210260402040c0c242018060a0c140a080a08100806061020120a020c1008061c020414040614040206041e180e060c040e04060c120e06060a06080c120402061204081c1a121006180c08240a2c0a0204080c04020a0c121206060816080406021614120a021e2a040c1814040e160e0a0c0804022418040e0a1a04080c060a0c0818120c0c0a120c080c1e040e0604140c061c022206121812080c0c1c080622020a0c12080604061208041406040e04080c1002040e0a202206020c101232060406060c060218060412060c0e060a080612102a0c02061c02040e062812020402120a0608100e10020c16081c0e10200a0606060e18061c06180c08060c0a1808100e120c060c280e24120a0204080a0c141002060c0a0c06061410082208121806100e0604020c1606020a060608160e101208040608180c040c02101406120c0a1a1608180402041a16080a0206041a040224040e0c12100608160e220c0c0c12060e120c0c2e120606260402063004140c040204060e0618060c064c0806100e0a0c1e020c04020a080412020c1e040e120c100e1c020a0218060a0e061000, 29194, 2806162785654),
    (348304, 647, 0x120a06060602120408120a120e340e06180a0c0e060a08040204020c0a020612041e08040e181c080c1606020c0c10020c0a241416080c120408100216060e0604142e061a0a2a120c0c12020a1e060c06061208040e0604060612020a021e1c02060402060a081e28021204061e0c0e04061212261e0c0c120a0c1e020a06020a0c14060c1c020606040e1c201006060206040804120204021204080c0c060a0c061a100224060a060e121606020610060e060c1c08041a10121a100e101202060c101e0606080c12040c080a06020414060c0a060e0c04061e060212040614040e10061808060a020a1412223212042408041e02061c0c26040618141614061602060a0e120604021014040810060e0a060e16020c0604062006041e1a0a020a120e0a080a0c0c14182e0e041a1806062e080a0614061c021204060606020606060a080402120c040204060824061c1e0e120414220c080406140c04063c020606040c020c10022a121614060c0a08041a0a02060412020c040c020c1c08300a0c12020a02062404060e0402040e1606080a061214061008060a0c0e2806080c0a0e121e1216141e0a1202061006080c1204081e041824060c060e0606280806181006140618100c0210021c08180a06020c0c0402041214100218100206160806060408240c18061804020a020a020a2c0a1404060204141020100c0c0c060824040216060e1c0e06160c060c06060e060a120c0e160e060a0e10020c0414420a08060a020a080a06060804240608100c0c081e122404140402100e0a12141612020402040806040606080c120a1e080a0804020a14220e10061a0408060a0e120a080402040e1216260418020412140c0406060c1e0210180e1006181a0a120e2802060404, 29841, 2808042488415),
    (356496, 647, 0xc0e0406022a0c241206100c0c180212181618021c020408060a0c081026103602100c0204140412180e060616080c10060e0a1e020414120a12080a181212020c0a080c0a0204060602101406100e0a2610021204080a0e0a24321216200c10020a06060e0a06080a02060412020a0e0406020a082a1c020408160806041e080c100c08060a18020c0c0a060e041820061c020c06360a06020a080412140a0806040212100806060406061e0c02040204261c0c060e0604121806121a0402040608060a0626180a0804060e060c0a02220e06060a0e060a140a1a0c0c060414040c0c02060a08240a1a041a0c10020c060a0e120a0c1e1208040804181e1a220216060c0c020a0e0612120c0c04061a0a141216020a08160218100e0c04060c02042a0e040c021c141e18040e0c060c0a1e06140c1204060212041212020a020604120c02060408100612081c0204120c080c10080c300a0c020c1008040c0806160e10140c1c020a061a180408041212080612060a0c0210020414101806080a2c0c180c160c0e06120a0c140a0e0c04060816020c04021e0a080402120a021c0606261606120c18120210020606060406080c1606020a0810062a0804060c120822060e060c0414060406020a080c160e061c0804180618020c1c122c060604060602060c1e041a04360c18080c1206160c14161a040e04023006041a160e040e0a060204080606042016080406020a060c08061c06180c080c1e041a220e0a0c0e180a0c08060a0606300c020604020a060206040c0e0606120a0c321e04080c040606260c0c0a060c021c0804201002280c0e0402061606200c060610200a0606120816260a1206080c1e040c08040606142818020406080604020a020c060c160e1e1002, 30488, 2809878651406),
    (364688, 629, 0x120c0e10060e06120c1c02040e0a0e1c0c08040e0a0606120e06180c040c080a0c0212041a120a1406040c1e0c02181806042604260c0a080a020618060a0c02101e0804140a1a06060406140c1c0806122808160804080606060a0804061a060a121802061c0204120602040602100e0c042406020c28060c14060c0406021e3406020c040612021e04060810020a0e1008061e040c322a0604060212060a0e2418041e120c0828300e0a060c020a0c0e0c040608060406080618060a020a2c040c080a0c0e100e04061e08060c0c0a060218180a0e0606061210080a06021804021c240806040212061014042408100c0206063c100c080a080c0408120c060c0406080c0a02240a0606020c0a060822081e040e040204021c183012021624140a020c0a02040e060402280620060a02180402040e16020a1460040c1a1204260a1e020c240412120e10360e060a0e04020a060e1804061a0406060c020448021212040c0e10140634120e1c120e3610060806100c060c260610080c160c0612020c0a1e081204021c0816020a120c14041a040c0c02060c0c04140c160224040e06040608120a2006160e0a0e040606080616141602040216020a06020c1212120a0e10060e06040c0806060a0c021e180606040612021e0a200c040c0c0c060c020a2c1812040e0c0406020a02041e0e0604060c141602042c061806041214220806060a361e18140a060608100606020c1c020406180e06060604060206041e06021206040c020604082208061e24060a200c120604021c1a0a020a0816020a120c02120a1e081602041404061a10200a0804080a0c0e0402220612260a02102a0c0c061e081e101a1e0c0c04020c10180804, 31117, 2811622889669),
    (372880, 624, 0x60c0c0806040c0806061804060c0c060e0a02120c0a0608100810020444100c0e10080c0a081e0408041406040e28020c06040c06020616122c0606120c060a0e2806020a0c0e0a0e120a0e060a020a021e18040c0608060622122a12141e061806060a1e0e0c0c2404120c0812061e1c020418060c02060c0a0804080a1806020c04060e160c02180a020a200c040c020c1c024e1e16060804060222180c0822241e0608060a021e0c060406061a0a0e0a0812120a0606080c0a020c04020a0c0c0e700e061804060806180a0c0e0c120c0a0e0604180c0c060606080412020c1e0414101a0a080402061c02280c0816061e0c020c0a3818040e300412320a022e08160c12080a0e060a06240e060a0c1a06040e161202060426060a06320a081c0c120810181e020a02060a1e06080c1c2402040e180c040e1c0c080a08061014120604200c1e060420041e0608061e0a02041e08121204080c0c0604080a0606120c12084008281406040c0e04080a08041e080406140c060c0a0c0c0e0a0c020c10080a06180c020c060a0c12200c041a1e06160c240804021e040c02100c020a0c060c0812180c0402181c14100606020c06040e0a060e0c12060a060c080c0a06020a0c121404360606080a02040e062e1808062e1a04060e120c04021602040e0a0c0e2404020c10060e060a080a140c0604060c060c080402061606061806141816020a060c120e1c08041a340c021c0c060c060e0a02300a060e1c020c10140412020a1406040e0402120a06020406141204060222080c18061806040222060212120c16060e0c0a080a0c1214061812040e06040e12120610020a1208040614181c2a0602040816120802, 31741, 2813315228042),
    (381072, 638, 0xa0e0a12080a1206060e06160c081c020a02180402121006141818100632060a0c06021e1c06181e141602060606120622060e1e040210020a08041202101418040204080a20060a020c2e0c0c062a02040e1020040e04060e0c1206040c1406180a1a1804021204060c020c040e101a0a12060216080a120c0228080a02061012020604121a0a0e0c1206060442080a020a0e060a0e0a14060a060822061404020a140a0e04080c0a12080a0e2e020408100e120412061416080c0406200a12080a0c020a08120a0e060a1a040e0a2006161208241c060608100c020a061e0e0c040c020c0a1a0c060c1e1204080c121234180e16080c0412080c0a080a0c0c140618061c140a0612060c1202040e060a0608160e060c420610021006080a021e060418061a0c160e0a02180a0806181c0c081e0a2a060e10020406180602240606040e040804060806120a021c080c0a0c08161206020412060e0606041a1002120a12060602062e120614162c0a06082a040620100c12060e061c0210120e0a120c0602040e040804240816022a1008220c08060c040e2202041e0614040c08100e180604061406040c021c0e0a0602061e061012020408121e1c0216020402040e06040e0622060608160602060a02040608180a060e0a021804020604180e0a14060a06081e0a02120c0a08060c0a080c0c0a060c0e04020408100c0224101e14061e12160e04022a0a1e08040e0c04120602043014100e0c040e0a0c0e06061204060e061006020a140a0c060c060c08061c062a02160e2806140420041818080408120a082e060824100c0218040606360e1002040806040c1a0406122a0210020408060604020a0e061824120a0e1e0c041806021c0218101400, 32379, 2815007753853),
    (389264, 626, 0x4081e100204060c0818060c0a061a0a060c0204140c1c021804021c0204060c14160e0a14040804141e100c0204021210061e30061a0c0a140a060204060c380c1204060c20060c18040e06100614180402040806041a1006020a120e0a062a200402040e24040236040e28080a120e0610060e18040212120a080a1a0a1a1614060a1e0e0c041e061a1e0c10061a0c060a1a1804020a0e04080a0e1c1406060618100e0a0e04020a0e24061e04240c1e201e1008040614040c1a04060c080a02161214060610140c1222060210020a12020a02061806041a040212100e0c0406082e0c020604060c020a02180a200406021614061818040c14060414121006060e06120a0c1e021e2e020412080a0e0a06020a06020c16060c12080c0a26100e0604020c1c1404061e020a0c060c1a1806160c060c020a02121606020a0c120c0e0c1c0c14160606122604060e0604260610060e040e12040612201204080c0a08041e0e180c0a06020604201e04141008100c0e10020a020a1202040614180a060e1006080a1406120a0c060c140c100e040e060c0a12060812161e02040c08060a060e0a080618061e0a021602061206040c02160e1008100606021e06181e0a02120616181a1206060a0e06280228081206041e06060210020408120a0c060c0c141216060e240a0204060e041e06061808060c04120212060a1e020c060c0a140c06040c0e04081608040e1e061c0224120a0606141c20040e0c0a022812082e0e100e0408181012020a020c1c0606140634060c1818021e04080a0218060a180e16060216260a12080402040e16060e06120414060c0c0606040218041404120c02220e060a020c1c0c0240061404, 33005, 2816633157014),
    (397456, 651, 0x40230060c04060e22020408061806100e06061c021c02181c06140a06060e0a0e100e0c12060406060c2004020a26640e060406180c140a060206041214040e10060806040e1e1e06060a0e22020414041a0c0a0206180a0c08160e0402100810260c040c0c1212020a021c1e0c06200c0c06040e16022e2412080412120e0a060e1e060a0e10260604140412200604060c0216180636020c060a060e0c0a080c1e0a02100e0c0604120602040e041416080c041e06060c0204140c22121218080a020402181c0c080604020604121a1e0604020c1216020616140610060c081c2a0210180204061e081c140c0a08120c0a0e120c041806181a0a0e0a140c0a080c100e10020a121e08040204063212120c0a0c0608040c0e060604120c08121206040204060e060a0212041e080616260a021206040c1e140a020c100e0a0620060c040614040e06100c06060e0402040e1c0e040618020c06061c02040c120e1606020c060412020424060212040e181e061012120c061814060c0c100e0c040618060e2206140c0408060c160210020a0204020a0c060c08040818120604060c12020a020c120a0614160c0c140616120e040c020a060c0e1806100c2004020c06100612020c121608040806221a10122022020a2604020406080606100e061e0a080a1802100c0212160e040812100e1e06040608120a020a1202160602063c040606081216080c120a120c0804020a060e041e021206421c0e0c180406020408100e0c040c02060610021006080606041410120812280c020a06021e04062006040206040e060a182a020a080a0e0406060e040c08060618120a141606080a0c0c06140a0e0c18040816081e0c0a020402160602040e061804120e0a2402120c0c3604020a0e0404, 33656, 2818288632279),
    (405648, 616, 0x1e040816180c0c0206160206040e22021806061c1a040212180c0a08100606020c060a0c14160e3402100216020a08120a120204080a080a5a0206060a082404063c0e06164a28120602040e060a0806160c12020604140a02061822020c1212040210021c081006020c0a062604060e121e1608040602100c020a0c0612200c0c0a060c12020c1e041a1c08040e100602120c1c0e040c0e0a0e04020a1a0c102c062a04120618080412080c1606080a021626120412081e061210020408060622020a2a0204142a0c0604080418060e061c02040204060c2a063c120c0806040216080a0c020a0608102c18101404080a0210020a02100608160e0a0e1002183a020402181002121204060608061e06061602040e160806101406160c0e0424021c2004121202121602220614100c02120c1e043806040e0c0a18060c080a021608240606160816060c2a060c0e0a080c040e0a0c14220e060c0418200c06040c0e40060e10020a081602160608180c06041214242a0a0e100c0c08120a2a080a08060a060e100c020406140a080c1e061c0e10061202101202161406041a0c0418020c0c1012023a06060c0804120804081c020c0a14041a040c0e0406060e100e041806020a0822061806020a020a1a460204060816020c061810080a0c020c0618060412080408100c08220c081c080c040e101806180c02062a0c1c0212120a020c2a060a02120a0c0c0806041e120e040204081212060a0e180c04060602100c08100e06060c160806062416060e0a02041a0a0e04060e0604060c1e080a0c0c120e0a1e12141204082404020402160602180a0e1e0a240602161202040216021804140a02, 34272, 2819823024066),
    (413840, 629, 0x1418041406101206021606021c18200a0816060e0406062c10120e0c063a36061a040c080a1a06040e100810020c1002120402060a0210140612161412060424020a200a12180e16201632040c0c020a080a060c02120406182c060612062e0e0a2c04061e0e0c0414041e06020a080402100e0a0e06040e0a120806100c0204020c0c060a181406040e04242a080a020c0a141c0804020a060c020414040c1a041404021606060806061c02180c0c06041406160c1e080a0e0a1a181c06020a08160e041a0a0e1008060c120c0412080a1202040602101e181a042a180e0c060c06180a02060a0e100e100c08160602041e1a0a2006060a06020c100828020a08060418060c021006121202160e0406021c1e02160602160218061822140a060614060a080a18080406020a0c06140a080604200408101404060c02100222121e0c080a061e0e0606121006060816080420060c0a12020c040624021204060216141e0a0e0a2016120c06140a06060e0a12080c060a140a022a0c10180806100e04061418060a020a020c1210060608102c0a0e0624060c0a08180402040e0a0e0a120e06041a1c0c080c0a0c0606060206061804200604240e0616081608121006020a0c180612060e12040e0a0c0e060a0206240612060406081e0c060c060c160c08060628060c06020c060c22241206080a020a1a04060c08040e0a0608100c020c040c0c0218040c1224180c181e0c0c122c180a0e1614060412320a0c1202180c0c100228080402040c020c100e04060602122218140610140c0a08040e0426040e0628180606022e061814061e0a0e10060216080a021e1008160206061c020a12120e040e120c0a06020c0604020a080a, 34901, 2821358373712),
    (422032, 638, 0x200a0e1e1e06102c101806122a020c0a0602060402061e040e04060c0c02302a10080a0c020a06140a06080c10140c0a08120a180620221208040e040c0e0a02120a0c021e0c040e0a0c140a1a0c0a14280204022802060412020a0c0e0606280806063a0e0616020c061e120412020c0a121202160e10060804080a08040204060e1602060a0c141c021c0e2e06181a0604081c022806140402061c142a040612020a020c180a200a0806241c0e060402060c0c040204140a0e1608060406080a060e0606101220160c0e06060a140c121e0a02060c0a0e06361c020402043204060614160606060c14060c04060c06061206020c0606040c080c0c120c0a200a1404021c020426062a12160c0c1404200a08100602060402060a120e0a060e280c080a0804080c1c141608060412080c0412020a0e16020606060a2010020c0618120a12140a0c0e04020406021c1416060c080622020412060c120c0210020c16060e122404020622060e06120a0c140c0c0a0e0c04060804081c0608061008340e04020a121a060a3c060816020a060c18242a1a10121e06021c0e061e0c120a0204060e040e10021602040606020604021c1a2a0a12060806041412220806040228120c06300c0c060e0a060606020c061e16060c260412020c04181e08041406040e04080a080c041202041a0a08060a14060a120c08161412120a0224182e021216120c0c02100c0606060816020c0a0e0408160812160e060c0a14060a0e0604120e1818060a0e060402041a060a0c02040606080402180a020c12041e060c060e1212101406040612021210080610060e100210021c06080a12140408060414161a160206040e06100804120c0204201e1c0c18080a02040e08, 35539, 2822885277268),
    (430224, 636, 0x2e08121c020a140426060402101202120a0606020c060406020a02061c021804061406122802040812120402040c02100c200a0206120c0412080a0206060a1202040e12040e040c0816060c02122e0204060c120e0406060e101416020a080a0812281a0a1e1406341a0a0c080a180206041412120a260a06060806120604320a020406060c0816060e10022a120a20100e2404021816021204062c0406060c0204062c0a2406020606041406040216020a06020a14061e0402120a241802061e12060406061e3c0216060c260c060604241406040806040602040e16020a121206120218041e0204020418200c12220e160206040218041a0c0418021e0a0c02041404120804122a0c08060a02040e04020616020a061e140406141c140a020a0e28122a060e060c061e160c080a0e221404120e041e021e1c0c020c040c320412020a12141c0804140a0804060c0212060c0a0804420c141c0c20060c1c0e100c02120c10021c0212040218060a0e1e040c080c060a0206160e041a0a082802181006120c0c02120c18061e06161a04060c0216060c06020c0a02062206020c1c02121006080c0616260414040e0a020a121a0c0a141204061a2e08040812280204060e040c08180c1206060a080a08040e0a020c2a0a080c04020a020c100c122c040e0a060618140c0a020a060c02160e060a1e1220100e0616020a06200606100c0602041208040e0a0e2a061210080a0206041202061204080c120c062806060c060606081006080a18060c0e122a040c0c02040c020a0206041e1806081c0206042604060c201e06280806040606020c3a140616180e1008060a0e120a02120414120604081606142a040810020a020a0204060806061008, 36175, 2824377938335)
  ],
  #[
    (438416, 644, 0x80a0e240c100c0e060a0c060c080a0c08221a0a02282a02120c1018120606180e1c0e060c0c120a26120a0e0a1a06060418020a0c2a1e0e040606080a0804180204360c0c021806061e1c0608060a140612120a20060408041802120a060626160c060e060604062c1812120c0a0c080a2c10020a020a18060e160216060e10141602100206101802040e04140c0a122a0e1e04021008040614160e240a0e0604141e06040614220e0a060e0a1802180a060e040816020a0816260a060c0c0602161e1208040206040e041a0a0606020604060c0c1a161e0c020a081002041a0c0a061a0a1404060e060a18021e040602120a0804081602042c12043008040e060a08060604020c1c08060a080a0804060806041416121802120a06180c240e04140a02280c0816080a0216061404120204060e0a06180c0806041a060c0606100c080a0c0c1a1804020414062a0a12021c0e04140c2a060610020c1e041a0604120c1206141602060a020a0c0606141e06162406061e02100e0a08160614040804060e120a12140406020604080c16060806240a120612060608060c0a02101e0e060412021c08100e180c0a0e2202040c2006060a0608340216061218020a080a02120c100804080c16080c04140c0a02100e0a06060e06100e06041a0a0e18042004020c0604021018180608060a0606081006080a240e0412080c04060c02040618021804020414121c02160e160804022404060806100e220c08221e02060c061812040806180a120e0a12020a060e12060a0c12140606220810060e0c04120804120c060216081c0c020a060804060c0e061204080c0a060e1002040602100e0a02061c0e2e020c0a08120a1a04020c0c2214061012240e0a0e100e0a020a0822, 36819, 2825861129932),
    (446608, 640, 0x61c080c101e1a040c0e061810020a02180a140a0e100e060a021e04061806020a260c060c18061c0c200622021806062808060612061216080a12021606260408220810020c1608060a061a041e08160e0a060e064018120e0a0e04080a201e0c040e0c10260606041224020a02121608040e10081c0806040608060412081006080a02181c1a0c18061608040e1012140c0406080a0204061e0e0406020c0616120234020402220e0402060a122c1606020606101404060804140a20040e1606020c041e0c0216080a060c02060402100e2e0e060a02060412140a0c021c1e14060c041404020a080a200c160e1006080406061214060a060630020a080a0e0606060406120e1204060206061206061c0c0e0402100216060e060408060a022a1018121206060206060a12080408060a060e0c1204083a0e0a081602040222060e10020a02120c0a0828021e041e06081c080c1c06080c0a06080c04060e060408120c0c1c081c0204080a02042012100e0a06140a24020a02100c020a240e180a061e14100c0606141206060a1404061214120c0616122a020a1e0c1a1206060412240204080a0c1e06080402061606140a020c1216020418060c021c080a1e0e120a0c02220c08160806061c02040810020a3c020a02100206060a120206041a1c020a200604060c180806041208160c08160c060e04140402060c1c1e08062808100e120a0804080c1e100c08100608041a0c0c0c060a08040618060e0c040614061608120c120604060812160812160804120c02060c1c0e0a080a240e0a06142412100c080610080a2a1236021206040c06080c04180e0c0a0810060e04022218081c0c0e061e04061806080c0a0c1412120604020412140c18041402, 37459, 2827307539590),
    (454800, 608, 0x160e0424020a021e06240a120618021e04021c0606121e022208160812040614120a0614180610020a06020c1018080a201e10021606020a0c120806100c12080a06120c1a040e0a180228141c0204140c0408100204060e10021c020a061a420a1e2a02060414120c060a08041416080c0a080a021014040e06040e0c2214180622061a041e32040c1a0a08060a180e1c1e0c02102604120e0a081e0a0204020a02162c0a2a08100e2220040e0a1e06060e0c0a140a021c2c04062408060a081614061602040c0c06020412060e16060818060a0c1206180e0a080a020a02040614100c08161a06061204141228021c0e0a1a1206061204060216021c2a061202041232060604180c060c1a10061416060e0c040e06060402160c06020a0c06020604020a140622080c100e1c06021810020c06120618041a0a0606020616140a080a0c08060a060c06200a0206060a1202120c0406080a061808180a0e0a0212060604260a080a0c02100804080a0c082a1c120c0e0a0e0a0608122a0604080406080a18080c12160204060806460e12041202060c12120a060e0c0a08040c1206020c06101206021c020a080412020c0a0e0a061a2808040204181e0c14180406020408060a0e160608181c080618060a14220204140a241e0c441e180a080606040c1e0804063608220806060a080a021002120a1214060a1a040e0a0c0816122406080a0612120c02040618020c160806280212062404140628021c0e060c1c0e040c0206040c120830160804083004020a0e0c04060e040e0624040e0c06160c0e22080a120e12120c0a0210020a12180c082e060806160e04380a2600, 38067, 2828656604425),
    (462992, 611, 0x1e060a1a0a020c060a080c0a0e3622060608061014040608060a020c16120c06020c0a060c1e06020a0e180610020a0818040c180614042408181216080a2012120406061206061a1c1e06060e180c041a041a12181002540a0e04020a180e0c120604120c08280e1c0c1802041802040e0c161a060406080a0218040c12061a10080c180418120822060222060212040602060412020c120606040c141c020c1014060a06320a020c18100e060406080a14120a120c360e0c2208060a060806180c2404081614100e0616080a0e0a14100c08040602060a0c0c1a341808060a1e24060c0c0e0c1c0e2e0c0e06160210080408040e46020c1e0a0204141006180e0604140a020414040c08160e1804060e1c0c02280e16022a0a0602060a060e060604060804020a12080414060c100e1e0c0a06022a120a12120e060c0c0a080a0c06140402180a021e12061c2a0602160e06180604060846140c0a06020a0632043206060406080c12160602241e0a0e1222080c040e0a20121c0e0a080604080a08160c02240c06061e0604260a1a0c0a080402040c0e0418060e0c1c0206040e0c0c100c0c061e020c16120206041e080616080a020a0c140a1a1602120406320a02121602041a0a1e0e041a040206120a020414060a0c02040e0a06060e042604060c0c12061a0a0e0414240a2a080a1e1a10021e0a02101e0e0a0e0a060806040c08100c080c1612120e1204121406161814060a0e0402160c141804021206101406040e16020a06020a1206060c0c06080c1c0c02060c0408121606021804060812180604080a1a180628060e16080c120402180c0a020c10021e0a02041416, 38678, 2829988308239),
    (471184, 644, 0x60c1602240a02100c1422080622020a060806180c04060e041a060c1c08041e120c081614060a020414060c0a02040e1c0c080a080c0c10020a0806040e0c04020c0a1e0c0e100e040212100c08100806040206160c060804122a020402041214121c0e0a0c12140c100c021c08120c0a0806120c040618061a040e100812040e18061612020c1c0e1e120a120e120a02040c140a1214040c0e0c04080a0c0e18100c0e06161e2006161a0a060e280e060402040e0a080a14040e16080c1602120a0606060810060806061204060e060c04140618120a0602120a0c0c1220120c061e041e0c06120c022808040e10060e040c0804021c0804080a140a080a180e0a0c0e180402040c020a0222060e1e0a18060608100e0a080a020c060a0804020a0614041e08060c04140406060c020402180a060e121c1214040c140420160218040c0e0c18061204121202122a0408060628062006040c260622120e0a1a040e0406062c16020c12101806060608060a1422200a120e24040c12080a12140a06060e042a12020a120e121e0408060408120a06080a140c1e10020c1008062e080c0c0a0210141204121416140a060c1418061e0a0c0636061e0e0c18040624060c0212060c04060c3002160e040204020a120e0c120a02060406141606020408060a140a020a020c0406080c12160e1806040602180402040e0402062a0c18101a040e0c041a04080a021026040c080c0a12061e020a14181002120a021006060e180c0418021c020406020a1e080c160e0c0a080a060e0a0e1c020c10021006060c120206101406120a06061806120e100e060a060e221e0c06080a020a1218020402040e220c1814041202060a060608160c020a060c0606120818360a3c021c0a, 39322, 2831367007477),
    (479376, 638, 0xe1e0a080a0c14041404080a0c080a0224060a0632280c020418081804140606040e0c0412080a080a0c080a020a0e12061006020a02100e121c0e0604180e0a060228081e0a021606020a08060604060804082808041230020c060a021c06080a12020c120a120c0c12020418260a0e041a061c0e1212060a0810020a020c0616021c0804062c06220e041a10060e04020c1006060e1c08161e1a1602120c0c041410121e080c2e0e12280e041a100c02040216080430080a140412060c02121c1418060a0612060c1202160c08061608040804083c06061c020a2606040c06140c060c041e12141e0606040e241018061a04060c02061612020a02040e0c0612101806060e0406080a021212040608100e040c0e04060216081804020a020a140a02100206100e2214060c1c0e0c100c0206040e16020a02101202041a0408060a021c0e0a0c260a08040620060a020a08160e3606120a08040608060604082a0a081c0216080a0c060e1c022404080c120a24020a020c0a06081e0402060c2406041416020a140c0406120804121a16120c0e1c060c08060a081218040e0a0606080c120c060a12020c0a02040c0c0c14060412062c1c12020c06043c0c0e10060e121e1002040806060406120206120a0216081c0204180218060a120608161e08100204061206080c0618100c3e060c101e1802100c0218180c0a060e12061e0c0a140a020c0604121a040822180c021002122e080c240a0c0602161410020c0a080c100c08040236041a04080c0606040c0824040606180816260a060c020610060816120606180e0c0a0c141c0210060e0604020c0a0816020a0e0412120e060c0c0610060e100c20040c0224280c0210020412060c1808100602, 39960, 2832709414216),
    (487568, 610, 0x36120804060206060a1202041a060406120e24060414160e1c06021804062c160c060e061006021c0806100e061602040e0610261e060c0414100c020a2408100e040206040e0a020414100c060e0a140c1002060c0a20060a1a0a06020a021c080a02060a060e0c221802120a0c021018060e100c140a080a02040e1e101212120e0a063c0204082a1816020c100c120e0a26060a061418180a0c12200a0e060616060c080c0424303602061e04061806080a0c141204060c0c08160c24183c0e182a0a08060c1206180c3004120804020a14220c2604021c020a0816060e180408160c18021218100e1606080c0a120216060606140c0c06180a081c1412100816180e060a0e0a021002160e060604061206080a0c1a16060e0a08220e06060a121404080a0e180a18020a080c0a140a0e061c081e04080604080a021e0c04180c1e1a0a1e0e2e0e0a06181202180a02180a08100e100608060a0c0c0206041202041404120806061804181e0c0806040206122a040e0a0606020606100c0804180e1c12140a02040e0a0e0a380610020616140c060408041422181e1a040c060c0204061806060e1210021e1602040c0806100c060e1e0c061612120c0c14160e10081608060a142404020430121404081204060e040606080a0e0c04060e061008160c06020c0a0c081204080a081e1c0e0c18100e0c0c0c0612062e0e3c040e060a0c0806060408060424020a0216080a12080406061206020c0c120c4e0622020a0e0a1406060a140a020a0204140402042a0e04020c1e060c0a021216060c08100e06060a0804303e0a0618060c0c08120a14040c08100c140a020a200a00, 40570, 2833971289201),
    (495760, 645, 0x602240606160c140a080a020402160210020604021e10141e04080c040c080c0c0c060a020c04060e10060c0c081c140a0c12140a020a060e06042604180204141e1c1406060a0e041a1806280e0616020a0606060804060e06060a061404081204081204140402161202161a1c021c061404020c0a060c0e0a1e060c020a060e18161814060c1606080a0608120a0c061e0e06061c02060c1614040e06240402040e101e0e04080a0210240e10060e180406061a0a082a12060a0e1e040204181212140c0a0c021c060c0c02060a0810080a0c08060604020a02101a12061006080c160c380a080a0c120e28120c0602041a0a020c22020c0c060a020a02100e180c1c0c14041404200a08040606080c3a14060c18040218720a14060a06020606120c0406180608121c181a060a060e040e1608060a1a0a060c0c1e0810020c06061012020a2a02060418020408061620060628060e040c020604021c0212060c0a20060c1e04080a0c082e02161202240a0216020a06020c0a0608160e120a0c082e0c021c08242202120c04081c0c0204020c0a0602041214060c1204062004181a1c1a041a060604120206121006120e0a081e040608062818020c10020c0c100210021c020a0e100212040e0a060e0406021e120a2a020a02040e0616122a0e04020c0a24060816080a080412021216061206081e10140610021614060c120418060e040828080a18080a080c160c1a0c0c040e121c060618060c140a060e0606060a0c02240a0206060a06081e061c1a0a1e0e1216020a0602121c0608060408040602061018020c0a060204120204061a0a08040618320c061e0a02060612061e0a240602101e0c020a081204060e0c1008060a08060c0a1806020c1e04020c14, 41215, 2835283165542),
    (503952, 614, 0x80a0210200a0c06180602100c0c0206120a1a0a2c0a0618020a020a061e0c02062a121e0c0a080a061206020c0a080c160e060a14121002040e060a260c0a06082e180e160e1e0c18100224160e060c0a0c14060a02280c0e040c1212080a021210062604061a0a06020c240a0c080c103612141810020c0a14240a1e080c1c06060210060e041a0c041a040e061014161a160c0206040e180a260c0c04020a20160e061008100e34080a1e0c18080a081210180218120c100e1804060608060606040e101206020a120e0c220606020a060c181404060e0a020a02120406080c16081602100e240c0604060e0610062a1a10080c28080a08120a020c100c0e041404140616080c04120c1e080a020402160c120204060e22060204180e0c100c141e06040c0e1018060e041a22120e0622080a0c0612020408060406020c0c040c0e060a140c0a1a040c0e0a021614101406061c020c16060c1a060a0e18121606021602060a020604020a12200418060606200c040c0e0a0608101a1602181e0c0406020c060c0a062a020a1a06041e020c100614061804021804180206161e060204061806120c1e1e0c021e121c0e04141810020c100c08280e06040c0806061c1e1a0402100c08120c1c021e04080a080a0c0c0608041a1e060a081204060e100c02060a0c060c0c1a060616260c100e0606060a020a0804122a1406120c04140402121812040618060c02220e1e060c0406020c0616081804181a100e160810060c26161a041e260c06060604060c060e0c1c12260406140a06060206181c021212061824042c060a0c0c140c180a0608060610081806101a160206160206040e0408, 41829, 2836511632218),
    (512144, 624, 0x2408220c1a0a020c061c021606180c06120608100c140a08061e220c080c16240204180c0804060e0a0812040c140a0e06040608160812041a0a0e04061e080a1212060e0a020a08100602060a021c0c02161a0412060e060c0c2e020a0c0c122a1404060e0a1406102a021008063a0204021606020c10021630120606022e021204121e0c080c0c1012060608060a0e041416140a06140c0a020406060c021018121a040c08120a021e0c0414060420040e101a04060818060402061606060e0a140c0a0804060608061608241c080c0c0414041a041e0c1404060612180c061236020a0e160e10080a1a04240e04080406080c0c0604060222140618060c0a122c121020120610022404020a080a120e040e0a0c06140c06281406040e12041a0418020c100608060a1a100c1e1a0606040e24040c020a1e080a081012020a06122c0c060c06061002160e1806100612061a0a18080604120e22140402061e1e0a14120c0a020a02120c040c0c4814041e0c020a021206040618020616141e060a14160c12080406060e0c12061c0c06080a1e0c021e0a0204141012140a0602120a0c0e040218060a0c12020a1a06180c18060408060402240a0c060c260c120a0218100c060c120c18440a080c16080c1e06042c04081e040e0420100210021606060e04060e0606061c0e160e0a020a080c0c0a0c1212020a1e020a120c0602060c1204022806120c0e061602120a0606060e061206060a02100204240206100e060406081c0810060e04021e0412020a14282c060604061e0c020a08061e101404022a060c04360e0a021206040c0e0c04080a14161a0c0c0a06180602060412121e0c0e1e060a0c060e060406, 42453, 2837739980467),
    (520336, 629, 0x4020a060c261c142a16060c081e0604140c0a0216081218040c0804020a1208122e0e060406122004140a0c08101404180818060418020c0c04020c0a0c1e18060e16080a020c06042a060e040e0c0a12020a18200a140a020c0a060206101e06141606021c1416121a04201204020402160c06020c040204080c120a20240a0e0a08240a0c0c2402041410020c0616022e0e100c081e0c0a02041802100c080c06100602060a0c021018020a1e12080a0e121204081218040c1e08064608060408040648021206040606080c0612040222020406020c060a020a0228060804060c08061806220e0c0a060c06020c0c06041206060812162604060206060612280c0c02040e0a0210140418060618080a080a12241e060804080c0a06140a140402060c0a0218160212041206180c080c04020a0e100e060a020a1a041a0a061802040e06040e0a060e0a0602040618240e18041a061818120a0c06061e0e0c040e041a0a140604020a140424080606040e0a020c120a0e0a081018140c1e301c140406020c061c0c120e2a04020424121404062016022e4a120a061e0e1006080606060a08041a0a0e0c0604060206161e0c120206040210320a120c020604060e2e14040c121412040e0a1404140c061602040e0a120e0a1e1404060e0a0c02120406021c0804080a0e22060e0612120a1e020a300c02060c0a080408160608040618080a263c0412021c0206220804080c0a1a040e0606160602041806080c12241e04020a14061606021210080606060a0e040c020a0c121e0206040e04082a0616021006120c060e061804021c0c080610140c0c04020a0206041a06060a0e04061e180e0a1e24140c0a181212022a281402, 43082, 2838958399067),
    (528528, 633, 0x1002120412240e060a020a080a2c0c040e0a1a101806140618041a0604140a06260a021c0c08060402280c080c0c100c1208180a060e2404080c1c021c2606041404080a1206181a1224060616080408060c0418060e06240a08160e1c020418060c02100e0618120a0206060438041e06060806061204260c0610060230040e0412020610080616020c0a06020c04060812120a021c0c140a021018060c0c061a06040608063c0a0602060c1612080a0e06041e021212041e0e0402040c020c0a2c04120804020a0e0a140610021e16081c08041e08040806040c140616082208060a0c1e08040c1802180604120602160c060c02040c0206280e2a040606140c0a06021804060e060a1a3a0e0c040c0210020a020604020a0602060c1606140406061a0418020c2e0c180612020c2422060246020a020a2c1810021602121002040620161208040e0c0a021002040812161a04060e0c060a08060406320a12140c0a14041a0a14121c0810060804120c0c240804020a1202061c06140402120a02160812040218041a060a0e101e0602101a0a242a06061e0828140c042c120a0e121c020c04182004020a0e040e0a021018180204080c120c040e0a02040c02160e1620100c12020414120a140a1a0412080a02220e061c060216080c060402100c081806041e0e1e04060c020c0a1412060c340614060a06020a081e0c060412020c0a0e040614100e16020a021026160e0a060c02040608100606080c18121c020610080604021c0c080a120e10080c1e16020406060810120c2c0c04060210020c1c0c0204060e160818160e0c04181a18040c1a040e04080c1e10020a0c021212041202124e040e06040c02100c020a060204080a02, 43715, 2840165520622),
    (536720, 615, 0x2120c0a0614120c0c101e021c021204120c0c0608040204021210081614041e0c120606020606180a0608060a0c022802061e0a020c120a02061c06120812060a0e0402122812020a26120a0c0e060a0e120c120604061a0a12021210021812060c0c0a02065208041a0a02100e101e1e06080a0c0e0c0c0a08120a14042618040e062a16060c080a18061a060a020c100c3c200a1a0a020a020a06020c0a0614040612181214122208180420041a0c060c0406121e0c0c1208041a061e180c0a0e040e0a02040e0a06060806041202060420060c1006081614060a0c08181e0a0e04060212161e08280c08180622320606220e0a12080a1a06040e06220204080c0a080616020c0a121412160c0e0a021216020604060c1e021e0c280e041a0c0a0c06020a0e060c06181204120618060c020c0402280e0a060206160c2402040812040e0c0c06181002040e0618060a060c082a0606041404060c2a0618081c061208040806063a080a180608060a060806040216063e1e0c10061e06080a0216080a0212041a1810184a180606040606200c06120a0e0a1a06180406140a0c120216081c14061c06060816240e1c0804060806041a0a18060e0a020a12020a08180a060c200604021e120a0602040e060636040e1c08041e060e06041a06040e0c060a020c0a1206060e062206082406180c0a0e0604120c0602060c041206063818120a060204380406120e100204060810080c121018021e100c0204181230020a120c180806100e06061c020c120408101e021804180206040e062e020606040614040c1202041412121c02040e1e0a020a0c080c102c0a02100c0606081c02060c341e, 44330, 2841320175875),
    (544912, 613, 0x608060402101818060e0c0a0c021e04020412201014040e0c34061a040c0e0a0614161a041a065802040e2418100606200604060e0a02420a08040206041a0426120a0c020406060c02040c0e100e0402040e043806040e0a080a0216140604060828020c1e06062224141804140604081c0204080a020616060c080604060e1018020408060408121024200a02120c061e0408060a020a141224060a1806080c0a0e18040614060450040c080c0a060c02040e16080610060e06281e3018060c12020a0e120c0a0806100e04080a08040206120a020a080a1a0402160602041410181a0c1e16060e12120406080420060a0c061808041a12180a0206160204060602060c04180e1608161a0a0c06020c0a1e08120c04120c060e10080c1c0c0804200a1a0c1614060c1c36061806080c1c0e061602060412260a0606020a02300a06020c0c0a12021002160602280818042a02060604061202042406120c021212100e10060206060a080a120212161214302e1a160210120e060402280e16120e060a02180a0e0a0c02060408302818020402161e022e0c26040810020a02060a18020618040e0c240408060c0c1002040608042a081e06102c040804062c061e0c060610020a0c06080c0c10020a020c2e021c18080a0c0608180604060218060a0e220c0c021e0a1802160602040e10080a022e02240402060414040204180e0616021e120a3216060e10061806061e12060608041406041e0618060c181a0c0c040e16141e540a0216061a040c1814060c1c080c18060a0c0c0e0a06240c08041a0408060c0406020a1212060e040606081216020a080a24020a0c02040216060e08, 44943, 2842453672688),
    (553104, 615, 0x4020414060a0608061816080c36040e0c04180c06080c0c1002041e0602121602041a120a261606021c1a040c12020a0804420204121a0c1810120c0804120216180e2a0a0e06040c021e06061002120a1412040812060a0602300c061e04081c060e0a0c020606041404120c0602360a060c0c08060414100e06161214101406121008120a0e100c24020c0c0a12240e10060806180604140c0a0e06041404080a0c021c062a0210020a12020a0c1a06180c040e0c0c100204060e060a0c021e180c0a0c061812020c0a06020c300a120e1c1406040c1a1c021608040806180a020a06260a020c1612021c021c06061a1c060e1806103210020a02040e0606060a081012060212101202121002040e100602061620060c0a120c0c300804062016020a1208120a180204020c0a1218060212220e0406020a2606041a1206060418080a080604020424080c0a08041e0c0e060a060e1c06200c0c0a0e0a0c0210020c1c02060c12060a080616080c04180e121c14040c06080c0c240a1406120a060e0a1424042a062a080c121204120804021e12060a06060e121c120212040c080a0812060a081608100c020606040c120c1e0c020a0e0406020424140a120216080408063420060c120604061a18100e1e0a060e0406121a0c0c0604123c2a080c0a120806060a120c0c02040e0c040e16180e1e0c064612060608040812061c06140a0c0206160e120616020c1c0602041a040e06100c02102a0c0806040c060c06140a14102402100e0a0210080c300c04061404080a141c02060a0606180e0604180606082a102a26180a1208120a0e1c12020a0e18040218061804062c1002180a0806, 45558, 2843573790622),
    (555555, 182, 0x21e041a1612021c08160c0c1e0608060a1404021e0c2a18180a0c06080604140a020c34080a0818041806020426060402040c120606020a0c0806061014040816080616020606100e1804260418240e06100c0222061e1e0e040618061a041802120a08041e0806061c020a1a2206080c0a12021c0c0212041806120c1a16140a020a0e0618040c060e12061014060a02060a0c0c060e0c04061a0a08060a080610062a060c2a1e0218041412040e0c0a120c021012, 45740, 2843902129534)
  ]
]

private def primeRowsSize : Nat := 784

private def primeRowsAt (i : Nat) : (Nat × Nat × Nat × Nat × Nat) :=
  (primeRowsBlocks[i/32]!)[i%32]!

end ColtonH3Data

namespace ColtonH3Data

open Finset ColtonHarmonic


def scale : Nat := 1000000000000

def boundary (i : Nat) : Nat := (primeRowsAt (i)).1

def rankAt (i : Nat) : Nat := (primeRowsAt (i)).2.2.2.1

def weightAt (i : Nat) : Nat := (primeRowsAt (i)).2.2.2.2

def offsetsAt (i : Nat) : List Nat :=
  let row := (primeRowsAt (i))
  decodeOffsets row.2.1 row.2.2.1 0

def primeStep (i : Nat) : Prop :=
  let lo := boundary i + 1
  let len := boundary (i+1) - boundary i
  let offsets := offsetsAt (i+1)
  1 ≤ boundary i ∧ boundary i ≤ boundary (i+1) ∧ boundary (i+1)+1 ≤ 10240000 ∧
    (∀ k ∈ offsets, k < len) ∧ offsets.SortedLT ∧ offsetsMask offsets = ColtonSieve.primeMask lo len ∧
    rankAt (i+1) = rankAt i + offsets.length ∧
    weightAt (i+1) = weightAt i + (offsets.map (fun p => scale/(lo+p))).sum

instance (i : Nat) : Decidable (primeStep i) := by
  unfold primeStep
  infer_instance

set_option maxRecDepth 20000 in
/-- All verified transitions share one induction for rank and reciprocal counts. -/
theorem ranks_correct (steps : ∀ i, i+1 < primeRowsSize → primeStep i)
    {i : Nat} (hi : i < primeRowsSize) :
    rankAt i = (boundary i).primeCounting ∧ weightAt i = weightedPrefix scale (boundary i) := by
  induction i with
  | zero => decide +kernel
  | succ i ih =>
    obtain ⟨hr, hw⟩ := ih (by omega)
    obtain ⟨hlo,hs,hu,hRange,hSorted,hMask,hRank,hWeight⟩ := steps i hi
    have hl : 2 ≤ boundary i+1 := by omega
    have hhu : boundary i+1+(boundary (i+1)-boundary i) ≤ 10240000 := by omega
    have fresh := weighted_segment scale hl hhu hRange
      (hSorted.pairwise.imp fun h => ne_of_lt h) hMask
    have lower : boundary i + 1 - 1 = boundary i := by omega
    have upper : boundary i + 1 + (boundary (i+1) - boundary i) - 1 = boundary (i+1) := by omega
    rw [lower,upper] at fresh
    exact ⟨hRank.trans (hr ▸ fresh.1.symm),hWeight.trans (hw ▸ fresh.2.symm)⟩

end ColtonH3Data


namespace ColtonH3Data

private def primeBatch (start count : Nat) : Bool :=
  (List.range' start count).all (fun i => decide (primeStep i))

private lemma primeBatch_at {start count i : Nat} (check : primeBatch start count = true)
    (lo : start ≤ i) (hi : i < start+count) : primeStep i :=
  of_decide_eq_true (List.all_eq_true.mp check i
    (List.mem_range'.mpr ⟨i-start, by omega, by simp; omega⟩))


set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch0 : PLift (primeBatch 0 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch1 : PLift (primeBatch 16 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch2 : PLift (primeBatch 32 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch3 : PLift (primeBatch 48 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch4 : PLift (primeBatch 64 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch5 : PLift (primeBatch 80 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch6 : PLift (primeBatch 96 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch7 : PLift (primeBatch 112 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch8 : PLift (primeBatch 128 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch9 : PLift (primeBatch 144 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch10 : PLift (primeBatch 160 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch11 : PLift (primeBatch 176 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch12 : PLift (primeBatch 192 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch13 : PLift (primeBatch 208 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch14 : PLift (primeBatch 224 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch15 : PLift (primeBatch 240 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch16 : PLift (primeBatch 256 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch17 : PLift (primeBatch 272 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch18 : PLift (primeBatch 288 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch19 : PLift (primeBatch 304 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch20 : PLift (primeBatch 320 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch21 : PLift (primeBatch 336 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch22 : PLift (primeBatch 352 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch23 : PLift (primeBatch 368 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch24 : PLift (primeBatch 384 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch25 : PLift (primeBatch 400 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch26 : PLift (primeBatch 416 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch27 : PLift (primeBatch 432 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch28 : PLift (primeBatch 448 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch29 : PLift (primeBatch 464 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch30 : PLift (primeBatch 480 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch31 : PLift (primeBatch 496 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch32 : PLift (primeBatch 512 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch33 : PLift (primeBatch 528 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch34 : PLift (primeBatch 544 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch35 : PLift (primeBatch 560 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch36 : PLift (primeBatch 576 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch37 : PLift (primeBatch 592 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch38 : PLift (primeBatch 608 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch39 : PLift (primeBatch 624 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch40 : PLift (primeBatch 640 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch41 : PLift (primeBatch 656 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch42 : PLift (primeBatch 672 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch43 : PLift (primeBatch 688 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch44 : PLift (primeBatch 704 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch45 : PLift (primeBatch 720 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch46 : PLift (primeBatch 736 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch47 : PLift (primeBatch 752 16 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def primeBatch48 : PLift (primeBatch 768 15 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem primeSteps (i : Nat) (hi : i+1 < primeRowsSize) : primeStep i := by
  have hsize : primeRowsSize = 784 := by decide +kernel
  rw [hsize] at hi
  have all : (0 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 80) ∨ (80 ≤ i ∧ i < 96) ∨ (96 ≤ i ∧ i < 112) ∨ (112 ≤ i ∧ i < 128) ∨ (128 ≤ i ∧ i < 144) ∨ (144 ≤ i ∧ i < 160) ∨ (160 ≤ i ∧ i < 176) ∨ (176 ≤ i ∧ i < 192) ∨ (192 ≤ i ∧ i < 208) ∨ (208 ≤ i ∧ i < 224) ∨ (224 ≤ i ∧ i < 240) ∨ (240 ≤ i ∧ i < 256) ∨ (256 ≤ i ∧ i < 272) ∨ (272 ≤ i ∧ i < 288) ∨ (288 ≤ i ∧ i < 304) ∨ (304 ≤ i ∧ i < 320) ∨ (320 ≤ i ∧ i < 336) ∨ (336 ≤ i ∧ i < 352) ∨ (352 ≤ i ∧ i < 368) ∨ (368 ≤ i ∧ i < 384) ∨ (384 ≤ i ∧ i < 400) ∨ (400 ≤ i ∧ i < 416) ∨ (416 ≤ i ∧ i < 432) ∨ (432 ≤ i ∧ i < 448) ∨ (448 ≤ i ∧ i < 464) ∨ (464 ≤ i ∧ i < 480) ∨ (480 ≤ i ∧ i < 496) ∨ (496 ≤ i ∧ i < 512) ∨ (512 ≤ i ∧ i < 528) ∨ (528 ≤ i ∧ i < 544) ∨ (544 ≤ i ∧ i < 560) ∨ (560 ≤ i ∧ i < 576) ∨ (576 ≤ i ∧ i < 592) ∨ (592 ≤ i ∧ i < 608) ∨ (608 ≤ i ∧ i < 624) ∨ (624 ≤ i ∧ i < 640) ∨ (640 ≤ i ∧ i < 656) ∨ (656 ≤ i ∧ i < 672) ∨ (672 ≤ i ∧ i < 688) ∨ (688 ≤ i ∧ i < 704) ∨ (704 ≤ i ∧ i < 720) ∨ (720 ≤ i ∧ i < 736) ∨ (736 ≤ i ∧ i < 752) ∨ (752 ≤ i ∧ i < 768) ∨ (768 ≤ i ∧ i < 783) := by omega
  rcases all with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact primeBatch_at primeBatch0.down h.1 h.2
  · exact primeBatch_at primeBatch1.down h.1 h.2
  · exact primeBatch_at primeBatch2.down h.1 h.2
  · exact primeBatch_at primeBatch3.down h.1 h.2
  · exact primeBatch_at primeBatch4.down h.1 h.2
  · exact primeBatch_at primeBatch5.down h.1 h.2
  · exact primeBatch_at primeBatch6.down h.1 h.2
  · exact primeBatch_at primeBatch7.down h.1 h.2
  · exact primeBatch_at primeBatch8.down h.1 h.2
  · exact primeBatch_at primeBatch9.down h.1 h.2
  · exact primeBatch_at primeBatch10.down h.1 h.2
  · exact primeBatch_at primeBatch11.down h.1 h.2
  · exact primeBatch_at primeBatch12.down h.1 h.2
  · exact primeBatch_at primeBatch13.down h.1 h.2
  · exact primeBatch_at primeBatch14.down h.1 h.2
  · exact primeBatch_at primeBatch15.down h.1 h.2
  · exact primeBatch_at primeBatch16.down h.1 h.2
  · exact primeBatch_at primeBatch17.down h.1 h.2
  · exact primeBatch_at primeBatch18.down h.1 h.2
  · exact primeBatch_at primeBatch19.down h.1 h.2
  · exact primeBatch_at primeBatch20.down h.1 h.2
  · exact primeBatch_at primeBatch21.down h.1 h.2
  · exact primeBatch_at primeBatch22.down h.1 h.2
  · exact primeBatch_at primeBatch23.down h.1 h.2
  · exact primeBatch_at primeBatch24.down h.1 h.2
  · exact primeBatch_at primeBatch25.down h.1 h.2
  · exact primeBatch_at primeBatch26.down h.1 h.2
  · exact primeBatch_at primeBatch27.down h.1 h.2
  · exact primeBatch_at primeBatch28.down h.1 h.2
  · exact primeBatch_at primeBatch29.down h.1 h.2
  · exact primeBatch_at primeBatch30.down h.1 h.2
  · exact primeBatch_at primeBatch31.down h.1 h.2
  · exact primeBatch_at primeBatch32.down h.1 h.2
  · exact primeBatch_at primeBatch33.down h.1 h.2
  · exact primeBatch_at primeBatch34.down h.1 h.2
  · exact primeBatch_at primeBatch35.down h.1 h.2
  · exact primeBatch_at primeBatch36.down h.1 h.2
  · exact primeBatch_at primeBatch37.down h.1 h.2
  · exact primeBatch_at primeBatch38.down h.1 h.2
  · exact primeBatch_at primeBatch39.down h.1 h.2
  · exact primeBatch_at primeBatch40.down h.1 h.2
  · exact primeBatch_at primeBatch41.down h.1 h.2
  · exact primeBatch_at primeBatch42.down h.1 h.2
  · exact primeBatch_at primeBatch43.down h.1 h.2
  · exact primeBatch_at primeBatch44.down h.1 h.2
  · exact primeBatch_at primeBatch45.down h.1 h.2
  · exact primeBatch_at primeBatch46.down h.1 h.2
  · exact primeBatch_at primeBatch47.down h.1 h.2
  · exact primeBatch_at primeBatch48.down h.1 h.2

end ColtonH3Data

namespace ColtonH3Data

open Finset ColtonHarmonic


def smallPrimes : Array Nat := #[2,3,5,7,11,13,17,19]

def smoothFactors (i : Nat) : List Nat :=
  (List.range 8).flatMap (fun j =>
    List.replicate (((smoothWord i) >>> (5*j)) % 32) smallPrimes[j]!)

def smoothValue (i : Nat) : Nat := (smoothFactors i).prod

def smoothNumerator (i : Nat) : Nat := scale / smoothValue i

def groupValue (i : Nat) : Nat := (groupRowsAt (i)).1.prod

def groupLow (i : Nat) : Nat := (groupRowsAt (i)).2.1

def groupHigh (i : Nat) : Nat := (groupRowsAt (i)).2.2

def groupNumerator (i : Nat) : Nat := (weightAt (groupHigh i) - weightAt (groupLow i)) / groupValue i

private def divisorCount (fs : List Nat) : Nat := ∏ p ∈ fs.toFinset, (fs.count p + 1)

private theorem primeFactors_of {fs : List Nat} (hp : ∀ p ∈ fs, p.Prime) :
    fs.prod.primeFactors = fs.toFinset ∧ ∀ p : Nat, fs.prod.factorization p = fs.count p := by
  have same := Nat.primeFactorsList_unique (n := fs.prod) rfl hp
  constructor
  · rw [← Nat.toFinset_factors]
    ext p
    exact List.mem_toFinset.trans (same.mem_iff.symm.trans List.mem_toFinset.symm)
  · intro p
    rw [← Nat.primeFactorsList_count_eq]
    exact (same.count_eq p).symm

private theorem divisorCount_correct {fs : List Nat} (hp : ∀ p ∈ fs, p.Prime) (hpos : 0 < fs.prod) :
    fs.prod.divisors.card = divisorCount fs := by
  have h := primeFactors_of hp
  unfold divisorCount
  rw [Nat.card_divisors hpos.ne', h.1]
  exact prod_congr rfl fun p _ => by rw [h.2 p]

def smoothValid (i : Nat) : Prop :=
  let fs := smoothFactors i
  (∀ p ∈ fs, p.Prime) ∧ 0 < fs.prod ∧ fs.prod ≤ 20000000 ∧
    2 * divisorCount fs ∣ fs.prod ∧ fs.toFinset.sup id ≤ 19

instance (i : Nat) : Decidable (smoothValid i) := by
  unfold smoothValid
  infer_instance

def groupValid (i : Nat) : Prop :=
  let fs := (groupRowsAt (i)).1
  let lower := boundary (groupLow i)
  let upper := boundary (groupHigh i)
  (∀ p ∈ fs, p.Prime) ∧ 0 < fs.prod ∧ 4 * divisorCount fs ∣ fs.prod ∧
    max 19 (fs.toFinset.sup id) ≤ lower ∧ lower ≤ upper ∧
    groupLow i < primeRowsSize ∧ groupHigh i < primeRowsSize ∧
    upper = min 555555 (20000000 / fs.prod)

instance (i : Nat) : Decidable (groupValid i) := by
  unfold groupValid
  infer_instance

private theorem injOn_of_order (value : Nat → Nat) (n : Nat)
    (steps : ∀ i, i+1 < n → value i < value (i+1)) : Set.InjOn value ↑(range n) := by
  have h : StrictMonoOn value (Set.Iio n) := strictMonoOn_of_lt_add_one Set.ordConnected_Iio
    (fun i _ _ hi => steps i hi)
  intro a ha b hb e
  exact h.injOn (mem_range.mp ha) (mem_range.mp hb) e

set_option maxRecDepth 20000 in
/-- Exact harmonic half of Colton H3 from checked smooth rows, verified prime
prefix endpoints, and certified cofactor rows. -/
theorem exactHarmonic
    (steps : ∀ i, i+1 < primeRowsSize → primeStep i)
    (smoothChecks : ∀ i < smoothSize, smoothValid i)
    (groupChecks : ∀ i < groupRowsSize, groupValid i)
    (smoothOrder : ∀ i, i+1 < smoothSize → smoothValue i < smoothValue (i+1))
    (groupOrder : ∀ i, i+1 < groupRowsSize → groupValue i < groupValue (i+1))
    (numerical : 502000000000 ≤ (∑ i ∈ range smoothSize, smoothNumerator i) +
      (∑ i ∈ range groupRowsSize, groupNumerator i)) :
    (251/500 : ℚ) ≤ ∑ k ∈ generators 20000000, 1 / (k : ℚ) := by
  let S := (range smoothSize).image smoothValue
  let M := range groupRowsSize
  have small (k : Nat) (hk : k ∈ S) : k ∈ generators 20000000 := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
    obtain ⟨hpr,hp,hb,hd,_⟩ := smoothChecks i (mem_range.mp hi)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp,hb⟩,hp,(divisorCount_correct hpr hp).symm ▸ hd⟩
  have small_top (k : Nat) (hk : k ∈ S) : k.primeFactors.sup id ≤ 19 := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
    obtain ⟨hpr,_,_,_,ht⟩ := smoothChecks i (mem_range.mp hi)
    exact (primeFactors_of hpr).1.symm ▸ ht
  have good (i : Nat) (hi : i ∈ M) : 0 < groupValue i ∧ 4*(groupValue i).divisors.card ∣ groupValue i := by
    obtain ⟨hpr,hp,hd,_⟩ := groupChecks i (mem_range.mp hi)
    exact ⟨hp,(divisorCount_correct hpr hp).symm ▸ hd⟩
  have loc (i : Nat) (hi : i ∈ M) : max 19 ((groupValue i).primeFactors.sup id) ≤ boundary (groupLow i) := by
    obtain ⟨hpr,_,_,hlo,_⟩ := groupChecks i (mem_range.mp hi)
    exact (primeFactors_of hpr).1.symm ▸ hlo
  have valid_range (i : Nat) (hi : i ∈ M) : boundary (groupLow i) ≤ min 555555 (20000000/groupValue i) := by
    obtain ⟨_,_,_,_,hr,_,_,he⟩ := groupChecks i (mem_range.mp hi)
    exact hr.trans_eq he
  have endpoints (i : Nat) (hi : i ∈ M) :
      weightAt (groupHigh i) = weightedPrefix scale (min 555555 (20000000/groupValue i)) ∧
      weightAt (groupLow i) = weightedPrefix scale (boundary (groupLow i)) := by
    obtain ⟨_,_,_,_,_,hl,hh,he⟩ := groupChecks i (mem_range.mp hi)
    exact ⟨(ranks_correct steps hh).2.trans (congrArg _ he), (ranks_correct steps hl).2⟩
  have bound := lower_bound (ι := Nat) 20000000 19 555555 scale (by decide) S M groupValue
    (boundary ∘ groupLow) (weightAt ∘ groupLow) (weightAt ∘ groupHigh) small small_top
    (injOn_of_order _ _ groupOrder) good loc valid_range endpoints
  apply le_trans _ bound
  have hs : (∑ k ∈ S, scale/k) = ∑ i ∈ range smoothSize, smoothNumerator i := by
    unfold S smoothNumerator
    rw [sum_image (injOn_of_order _ _ smoothOrder)]
  rw [hs]
  change (251/500 : ℚ) ≤ (((∑ i ∈ range smoothSize, smoothNumerator i) +
    (∑ i ∈ range groupRowsSize, groupNumerator i) : ℕ) : ℚ) / scale
  have hscale : (0 : ℚ) < scale := by decide
  apply (le_div_iff₀ hscale).2
  have hm : (251/500 : ℚ) * scale = (502000000000 : ℚ) := by norm_num [scale]
  rw [hm]
  exact_mod_cast numerical

end ColtonH3Data

namespace ColtonH3Data

open Finset

private theorem sumThroughBlocks (f cumulative : Nat → Nat) (width count : Nat)
    (zero : cumulative 0 = 0)
    (steps : ∀ j < count, cumulative (j+1) = cumulative j + ∑ t ∈ range width, f (width*j+t))
    (j : Nat) (hj : j ≤ count) : (∑ i ∈ range (width*j), f i) = cumulative j := by
  induction j with
  | zero => simpa using zero.symm
  | succ j ih =>
    rw [Nat.mul_succ, sum_range_add, ih (by omega)]
    exact (steps j (by omega)).symm

private def smoothPrefixValues : Array Nat := #[0, 337602267859, 347408307406, 351390127636, 353535931738, 354823517885, 355611686355, 356137809686, 356524847183, 356821333690, 357052177693, 357235356937, 357383947158, 357506052706, 357608321667, 357695042633, 357769173714, 357832999109, 357888298596, 357936246209, 357978494448, 358016063409, 358049120921, 358078227276, 358104259205, 358127459290, 358148361995, 358167106300, 358184298056, 358199984485, 358214264781, 358227232927, 358239071496, 358250000007, 358260041922, 358269305918, 358277850833, 358285760574, 358293116011, 358299963593, 358306393274, 358312403313, 358318025616, 358323264198, 358328181914, 358332801222, 358337178547, 358341295839, 358345177164, 358348863084, 358352339389, 358355635380, 358358770084, 358361737780, 358364552452, 358367212557, 358369734129]

private def smoothPrefix (j : Nat) : Nat := smoothPrefixValues[j]!

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock0 : PLift (smoothPrefix (0+1) = smoothPrefix 0 +
      ∑ t ∈ range 48, smoothNumerator (48*0+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock1 : PLift (smoothPrefix (1+1) = smoothPrefix 1 +
      ∑ t ∈ range 48, smoothNumerator (48*1+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock2 : PLift (smoothPrefix (2+1) = smoothPrefix 2 +
      ∑ t ∈ range 48, smoothNumerator (48*2+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock3 : PLift (smoothPrefix (3+1) = smoothPrefix 3 +
      ∑ t ∈ range 48, smoothNumerator (48*3+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock4 : PLift (smoothPrefix (4+1) = smoothPrefix 4 +
      ∑ t ∈ range 48, smoothNumerator (48*4+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock5 : PLift (smoothPrefix (5+1) = smoothPrefix 5 +
      ∑ t ∈ range 48, smoothNumerator (48*5+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock6 : PLift (smoothPrefix (6+1) = smoothPrefix 6 +
      ∑ t ∈ range 48, smoothNumerator (48*6+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock7 : PLift (smoothPrefix (7+1) = smoothPrefix 7 +
      ∑ t ∈ range 48, smoothNumerator (48*7+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock8 : PLift (smoothPrefix (8+1) = smoothPrefix 8 +
      ∑ t ∈ range 48, smoothNumerator (48*8+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock9 : PLift (smoothPrefix (9+1) = smoothPrefix 9 +
      ∑ t ∈ range 48, smoothNumerator (48*9+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock10 : PLift (smoothPrefix (10+1) = smoothPrefix 10 +
      ∑ t ∈ range 48, smoothNumerator (48*10+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock11 : PLift (smoothPrefix (11+1) = smoothPrefix 11 +
      ∑ t ∈ range 48, smoothNumerator (48*11+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock12 : PLift (smoothPrefix (12+1) = smoothPrefix 12 +
      ∑ t ∈ range 48, smoothNumerator (48*12+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock13 : PLift (smoothPrefix (13+1) = smoothPrefix 13 +
      ∑ t ∈ range 48, smoothNumerator (48*13+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock14 : PLift (smoothPrefix (14+1) = smoothPrefix 14 +
      ∑ t ∈ range 48, smoothNumerator (48*14+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock15 : PLift (smoothPrefix (15+1) = smoothPrefix 15 +
      ∑ t ∈ range 48, smoothNumerator (48*15+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock16 : PLift (smoothPrefix (16+1) = smoothPrefix 16 +
      ∑ t ∈ range 48, smoothNumerator (48*16+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock17 : PLift (smoothPrefix (17+1) = smoothPrefix 17 +
      ∑ t ∈ range 48, smoothNumerator (48*17+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock18 : PLift (smoothPrefix (18+1) = smoothPrefix 18 +
      ∑ t ∈ range 48, smoothNumerator (48*18+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock19 : PLift (smoothPrefix (19+1) = smoothPrefix 19 +
      ∑ t ∈ range 48, smoothNumerator (48*19+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock20 : PLift (smoothPrefix (20+1) = smoothPrefix 20 +
      ∑ t ∈ range 48, smoothNumerator (48*20+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock21 : PLift (smoothPrefix (21+1) = smoothPrefix 21 +
      ∑ t ∈ range 48, smoothNumerator (48*21+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock22 : PLift (smoothPrefix (22+1) = smoothPrefix 22 +
      ∑ t ∈ range 48, smoothNumerator (48*22+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock23 : PLift (smoothPrefix (23+1) = smoothPrefix 23 +
      ∑ t ∈ range 48, smoothNumerator (48*23+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock24 : PLift (smoothPrefix (24+1) = smoothPrefix 24 +
      ∑ t ∈ range 48, smoothNumerator (48*24+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock25 : PLift (smoothPrefix (25+1) = smoothPrefix 25 +
      ∑ t ∈ range 48, smoothNumerator (48*25+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock26 : PLift (smoothPrefix (26+1) = smoothPrefix 26 +
      ∑ t ∈ range 48, smoothNumerator (48*26+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock27 : PLift (smoothPrefix (27+1) = smoothPrefix 27 +
      ∑ t ∈ range 48, smoothNumerator (48*27+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock28 : PLift (smoothPrefix (28+1) = smoothPrefix 28 +
      ∑ t ∈ range 48, smoothNumerator (48*28+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock29 : PLift (smoothPrefix (29+1) = smoothPrefix 29 +
      ∑ t ∈ range 48, smoothNumerator (48*29+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock30 : PLift (smoothPrefix (30+1) = smoothPrefix 30 +
      ∑ t ∈ range 48, smoothNumerator (48*30+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock31 : PLift (smoothPrefix (31+1) = smoothPrefix 31 +
      ∑ t ∈ range 48, smoothNumerator (48*31+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock32 : PLift (smoothPrefix (32+1) = smoothPrefix 32 +
      ∑ t ∈ range 48, smoothNumerator (48*32+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock33 : PLift (smoothPrefix (33+1) = smoothPrefix 33 +
      ∑ t ∈ range 48, smoothNumerator (48*33+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock34 : PLift (smoothPrefix (34+1) = smoothPrefix 34 +
      ∑ t ∈ range 48, smoothNumerator (48*34+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock35 : PLift (smoothPrefix (35+1) = smoothPrefix 35 +
      ∑ t ∈ range 48, smoothNumerator (48*35+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock36 : PLift (smoothPrefix (36+1) = smoothPrefix 36 +
      ∑ t ∈ range 48, smoothNumerator (48*36+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock37 : PLift (smoothPrefix (37+1) = smoothPrefix 37 +
      ∑ t ∈ range 48, smoothNumerator (48*37+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock38 : PLift (smoothPrefix (38+1) = smoothPrefix 38 +
      ∑ t ∈ range 48, smoothNumerator (48*38+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock39 : PLift (smoothPrefix (39+1) = smoothPrefix 39 +
      ∑ t ∈ range 48, smoothNumerator (48*39+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock40 : PLift (smoothPrefix (40+1) = smoothPrefix 40 +
      ∑ t ∈ range 48, smoothNumerator (48*40+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock41 : PLift (smoothPrefix (41+1) = smoothPrefix 41 +
      ∑ t ∈ range 48, smoothNumerator (48*41+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock42 : PLift (smoothPrefix (42+1) = smoothPrefix 42 +
      ∑ t ∈ range 48, smoothNumerator (48*42+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock43 : PLift (smoothPrefix (43+1) = smoothPrefix 43 +
      ∑ t ∈ range 48, smoothNumerator (48*43+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock44 : PLift (smoothPrefix (44+1) = smoothPrefix 44 +
      ∑ t ∈ range 48, smoothNumerator (48*44+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock45 : PLift (smoothPrefix (45+1) = smoothPrefix 45 +
      ∑ t ∈ range 48, smoothNumerator (48*45+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock46 : PLift (smoothPrefix (46+1) = smoothPrefix 46 +
      ∑ t ∈ range 48, smoothNumerator (48*46+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock47 : PLift (smoothPrefix (47+1) = smoothPrefix 47 +
      ∑ t ∈ range 48, smoothNumerator (48*47+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock48 : PLift (smoothPrefix (48+1) = smoothPrefix 48 +
      ∑ t ∈ range 48, smoothNumerator (48*48+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock49 : PLift (smoothPrefix (49+1) = smoothPrefix 49 +
      ∑ t ∈ range 48, smoothNumerator (48*49+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock50 : PLift (smoothPrefix (50+1) = smoothPrefix 50 +
      ∑ t ∈ range 48, smoothNumerator (48*50+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock51 : PLift (smoothPrefix (51+1) = smoothPrefix 51 +
      ∑ t ∈ range 48, smoothNumerator (48*51+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock52 : PLift (smoothPrefix (52+1) = smoothPrefix 52 +
      ∑ t ∈ range 48, smoothNumerator (48*52+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock53 : PLift (smoothPrefix (53+1) = smoothPrefix 53 +
      ∑ t ∈ range 48, smoothNumerator (48*53+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock54 : PLift (smoothPrefix (54+1) = smoothPrefix 54 +
      ∑ t ∈ range 48, smoothNumerator (48*54+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumBlock55 : PLift (smoothPrefix (55+1) = smoothPrefix 55 +
      ∑ t ∈ range 48, smoothNumerator (48*55+t)) := ⟨by decide +kernel⟩

private theorem smoothSumStep (j : Nat) (hj : j < 56) :
    smoothPrefix (j+1) = smoothPrefix j + ∑ t ∈ range 48, smoothNumerator (48*j+t) := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 ∨ j = 32 ∨ j = 33 ∨ j = 34 ∨ j = 35 ∨ j = 36 ∨ j = 37 ∨ j = 38 ∨ j = 39 ∨ j = 40 ∨ j = 41 ∨ j = 42 ∨ j = 43 ∨ j = 44 ∨ j = 45 ∨ j = 46 ∨ j = 47 ∨ j = 48 ∨ j = 49 ∨ j = 50 ∨ j = 51 ∨ j = 52 ∨ j = 53 ∨ j = 54 ∨ j = 55 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact smoothSumBlock0.down
  · exact smoothSumBlock1.down
  · exact smoothSumBlock2.down
  · exact smoothSumBlock3.down
  · exact smoothSumBlock4.down
  · exact smoothSumBlock5.down
  · exact smoothSumBlock6.down
  · exact smoothSumBlock7.down
  · exact smoothSumBlock8.down
  · exact smoothSumBlock9.down
  · exact smoothSumBlock10.down
  · exact smoothSumBlock11.down
  · exact smoothSumBlock12.down
  · exact smoothSumBlock13.down
  · exact smoothSumBlock14.down
  · exact smoothSumBlock15.down
  · exact smoothSumBlock16.down
  · exact smoothSumBlock17.down
  · exact smoothSumBlock18.down
  · exact smoothSumBlock19.down
  · exact smoothSumBlock20.down
  · exact smoothSumBlock21.down
  · exact smoothSumBlock22.down
  · exact smoothSumBlock23.down
  · exact smoothSumBlock24.down
  · exact smoothSumBlock25.down
  · exact smoothSumBlock26.down
  · exact smoothSumBlock27.down
  · exact smoothSumBlock28.down
  · exact smoothSumBlock29.down
  · exact smoothSumBlock30.down
  · exact smoothSumBlock31.down
  · exact smoothSumBlock32.down
  · exact smoothSumBlock33.down
  · exact smoothSumBlock34.down
  · exact smoothSumBlock35.down
  · exact smoothSumBlock36.down
  · exact smoothSumBlock37.down
  · exact smoothSumBlock38.down
  · exact smoothSumBlock39.down
  · exact smoothSumBlock40.down
  · exact smoothSumBlock41.down
  · exact smoothSumBlock42.down
  · exact smoothSumBlock43.down
  · exact smoothSumBlock44.down
  · exact smoothSumBlock45.down
  · exact smoothSumBlock46.down
  · exact smoothSumBlock47.down
  · exact smoothSumBlock48.down
  · exact smoothSumBlock49.down
  · exact smoothSumBlock50.down
  · exact smoothSumBlock51.down
  · exact smoothSumBlock52.down
  · exact smoothSumBlock53.down
  · exact smoothSumBlock54.down
  · exact smoothSumBlock55.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def smoothSumTail : PLift ((∑ t ∈ range 25, smoothNumerator (48*56+t)) =
    1261469) := ⟨by decide +kernel⟩

set_option maxRecDepth 10000 in
private theorem smoothTotal : (∑ i ∈ range smoothSize, smoothNumerator i) = 358370995598 := by
  have hsize : smoothSize = 48*56+25 := by decide +kernel
  have hfirst := sumThroughBlocks smoothNumerator smoothPrefix 48 56
    (by decide) smoothSumStep 56 (by omega)
  rw [hsize, sum_range_add, hfirst, smoothSumTail.down]
  decide +kernel

private def groupPrefixValues : Array Nat := #[0, 125132509828, 132580096315, 136050090373, 138061506021, 139357255283, 140287163490, 140972858474, 141550511892, 142102350194, 142520243308, 142879584381, 143168289329, 143392031729, 143578483173]

private def groupPrefix (j : Nat) : Nat := groupPrefixValues[j]!

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def groupSumBlock0 : PLift (groupPrefix (0+1) = groupPrefix 0 +
      ∑ t ∈ range 48, groupNumerator (48*0+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def groupSumBlock1 : PLift (groupPrefix (1+1) = groupPrefix 1 +
      ∑ t ∈ range 48, groupNumerator (48*1+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def groupSumBlock2 : PLift (groupPrefix (2+1) = groupPrefix 2 +
      ∑ t ∈ range 48, groupNumerator (48*2+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def groupSumBlock3 : PLift (groupPrefix (3+1) = groupPrefix 3 +
      ∑ t ∈ range 48, groupNumerator (48*3+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def groupSumBlock4 : PLift (groupPrefix (4+1) = groupPrefix 4 +
      ∑ t ∈ range 48, groupNumerator (48*4+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def groupSumBlock5 : PLift (groupPrefix (5+1) = groupPrefix 5 +
      ∑ t ∈ range 48, groupNumerator (48*5+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def groupSumBlock6 : PLift (groupPrefix (6+1) = groupPrefix 6 +
      ∑ t ∈ range 48, groupNumerator (48*6+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def groupSumBlock7 : PLift (groupPrefix (7+1) = groupPrefix 7 +
      ∑ t ∈ range 48, groupNumerator (48*7+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def groupSumBlock8 : PLift (groupPrefix (8+1) = groupPrefix 8 +
      ∑ t ∈ range 48, groupNumerator (48*8+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def groupSumBlock9 : PLift (groupPrefix (9+1) = groupPrefix 9 +
      ∑ t ∈ range 48, groupNumerator (48*9+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def groupSumBlock10 : PLift (groupPrefix (10+1) = groupPrefix 10 +
      ∑ t ∈ range 48, groupNumerator (48*10+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def groupSumBlock11 : PLift (groupPrefix (11+1) = groupPrefix 11 +
      ∑ t ∈ range 48, groupNumerator (48*11+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def groupSumBlock12 : PLift (groupPrefix (12+1) = groupPrefix 12 +
      ∑ t ∈ range 48, groupNumerator (48*12+t)) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def groupSumBlock13 : PLift (groupPrefix (13+1) = groupPrefix 13 +
      ∑ t ∈ range 48, groupNumerator (48*13+t)) := ⟨by decide +kernel⟩

private theorem groupSumStep (j : Nat) (hj : j < 14) :
    groupPrefix (j+1) = groupPrefix j + ∑ t ∈ range 48, groupNumerator (48*j+t) := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact groupSumBlock0.down
  · exact groupSumBlock1.down
  · exact groupSumBlock2.down
  · exact groupSumBlock3.down
  · exact groupSumBlock4.down
  · exact groupSumBlock5.down
  · exact groupSumBlock6.down
  · exact groupSumBlock7.down
  · exact groupSumBlock8.down
  · exact groupSumBlock9.down
  · exact groupSumBlock10.down
  · exact groupSumBlock11.down
  · exact groupSumBlock12.down
  · exact groupSumBlock13.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private def groupSumTail : PLift ((∑ t ∈ range 18, groupNumerator (48*14+t)) =
    52966470) := ⟨by decide +kernel⟩

set_option maxRecDepth 10000 in
private theorem groupTotal : (∑ i ∈ range groupRowsSize, groupNumerator i) = 143631449643 := by
  have hsize : groupRowsSize = 48*14+18 := by decide +kernel
  have hfirst := sumThroughBlocks groupNumerator groupPrefix 48 14
    (by decide) groupSumStep 14 (by omega)
  rw [hsize, sum_range_add, hfirst, groupSumTail.down]
  decide +kernel

/-- The exact harmonic numerator, reconstructed from narrow checked sums. -/
theorem lowerNumerics : 502000000000 ≤ (∑ i ∈ range smoothSize, smoothNumerator i) +
    (∑ i ∈ range groupRowsSize, groupNumerator i) := by
  rw [smoothTotal, groupTotal]
  decide

end ColtonH3Data

namespace ColtonH3Data

open Finset ColtonHarmonic

private def smoothCondition (i : Nat) : Prop :=
  smoothValid i ∧ (i+1 < smoothSize → smoothValue i < smoothValue (i+1))

private instance (i : Nat) : Decidable (smoothCondition i) := by
  unfold smoothCondition
  infer_instance

private def smoothBatch (start count : Nat) : Bool :=
  (List.range' start count).all (fun i => decide (smoothCondition i))

private lemma smoothBatch_at {start count i : Nat} (check : smoothBatch start count = true)
    (lo : start ≤ i) (hi : i < start+count) : smoothCondition i :=
  of_decide_eq_true (List.all_eq_true.mp check i
    (List.mem_range'.mpr ⟨i-start, by omega, by simp; omega⟩))


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch0 : PLift (smoothBatch 0 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch1 : PLift (smoothBatch 64 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch2 : PLift (smoothBatch 128 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch3 : PLift (smoothBatch 192 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch4 : PLift (smoothBatch 256 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch5 : PLift (smoothBatch 320 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch6 : PLift (smoothBatch 384 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch7 : PLift (smoothBatch 448 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch8 : PLift (smoothBatch 512 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch9 : PLift (smoothBatch 576 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch10 : PLift (smoothBatch 640 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch11 : PLift (smoothBatch 704 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch12 : PLift (smoothBatch 768 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch13 : PLift (smoothBatch 832 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch14 : PLift (smoothBatch 896 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch15 : PLift (smoothBatch 960 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch16 : PLift (smoothBatch 1024 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch17 : PLift (smoothBatch 1088 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch18 : PLift (smoothBatch 1152 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch19 : PLift (smoothBatch 1216 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch20 : PLift (smoothBatch 1280 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch21 : PLift (smoothBatch 1344 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch22 : PLift (smoothBatch 1408 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch23 : PLift (smoothBatch 1472 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch24 : PLift (smoothBatch 1536 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch25 : PLift (smoothBatch 1600 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch26 : PLift (smoothBatch 1664 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch27 : PLift (smoothBatch 1728 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch28 : PLift (smoothBatch 1792 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch29 : PLift (smoothBatch 1856 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch30 : PLift (smoothBatch 1920 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch31 : PLift (smoothBatch 1984 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch32 : PLift (smoothBatch 2048 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch33 : PLift (smoothBatch 2112 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch34 : PLift (smoothBatch 2176 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch35 : PLift (smoothBatch 2240 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch36 : PLift (smoothBatch 2304 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch37 : PLift (smoothBatch 2368 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch38 : PLift (smoothBatch 2432 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch39 : PLift (smoothBatch 2496 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch40 : PLift (smoothBatch 2560 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch41 : PLift (smoothBatch 2624 64 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def smoothBatch42 : PLift (smoothBatch 2688 25 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem smoothChecked (i : Nat) (hi : i < smoothSize) : smoothCondition i := by
  have hsize : smoothSize = 2713 := by decide +kernel
  rw [hsize] at hi
  have all : (0 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 128) ∨ (128 ≤ i ∧ i < 192) ∨ (192 ≤ i ∧ i < 256) ∨ (256 ≤ i ∧ i < 320) ∨ (320 ≤ i ∧ i < 384) ∨ (384 ≤ i ∧ i < 448) ∨ (448 ≤ i ∧ i < 512) ∨ (512 ≤ i ∧ i < 576) ∨ (576 ≤ i ∧ i < 640) ∨ (640 ≤ i ∧ i < 704) ∨ (704 ≤ i ∧ i < 768) ∨ (768 ≤ i ∧ i < 832) ∨ (832 ≤ i ∧ i < 896) ∨ (896 ≤ i ∧ i < 960) ∨ (960 ≤ i ∧ i < 1024) ∨ (1024 ≤ i ∧ i < 1088) ∨ (1088 ≤ i ∧ i < 1152) ∨ (1152 ≤ i ∧ i < 1216) ∨ (1216 ≤ i ∧ i < 1280) ∨ (1280 ≤ i ∧ i < 1344) ∨ (1344 ≤ i ∧ i < 1408) ∨ (1408 ≤ i ∧ i < 1472) ∨ (1472 ≤ i ∧ i < 1536) ∨ (1536 ≤ i ∧ i < 1600) ∨ (1600 ≤ i ∧ i < 1664) ∨ (1664 ≤ i ∧ i < 1728) ∨ (1728 ≤ i ∧ i < 1792) ∨ (1792 ≤ i ∧ i < 1856) ∨ (1856 ≤ i ∧ i < 1920) ∨ (1920 ≤ i ∧ i < 1984) ∨ (1984 ≤ i ∧ i < 2048) ∨ (2048 ≤ i ∧ i < 2112) ∨ (2112 ≤ i ∧ i < 2176) ∨ (2176 ≤ i ∧ i < 2240) ∨ (2240 ≤ i ∧ i < 2304) ∨ (2304 ≤ i ∧ i < 2368) ∨ (2368 ≤ i ∧ i < 2432) ∨ (2432 ≤ i ∧ i < 2496) ∨ (2496 ≤ i ∧ i < 2560) ∨ (2560 ≤ i ∧ i < 2624) ∨ (2624 ≤ i ∧ i < 2688) ∨ (2688 ≤ i ∧ i < 2713) := by omega
  rcases all with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact smoothBatch_at smoothBatch0.down h.1 h.2
  · exact smoothBatch_at smoothBatch1.down h.1 h.2
  · exact smoothBatch_at smoothBatch2.down h.1 h.2
  · exact smoothBatch_at smoothBatch3.down h.1 h.2
  · exact smoothBatch_at smoothBatch4.down h.1 h.2
  · exact smoothBatch_at smoothBatch5.down h.1 h.2
  · exact smoothBatch_at smoothBatch6.down h.1 h.2
  · exact smoothBatch_at smoothBatch7.down h.1 h.2
  · exact smoothBatch_at smoothBatch8.down h.1 h.2
  · exact smoothBatch_at smoothBatch9.down h.1 h.2
  · exact smoothBatch_at smoothBatch10.down h.1 h.2
  · exact smoothBatch_at smoothBatch11.down h.1 h.2
  · exact smoothBatch_at smoothBatch12.down h.1 h.2
  · exact smoothBatch_at smoothBatch13.down h.1 h.2
  · exact smoothBatch_at smoothBatch14.down h.1 h.2
  · exact smoothBatch_at smoothBatch15.down h.1 h.2
  · exact smoothBatch_at smoothBatch16.down h.1 h.2
  · exact smoothBatch_at smoothBatch17.down h.1 h.2
  · exact smoothBatch_at smoothBatch18.down h.1 h.2
  · exact smoothBatch_at smoothBatch19.down h.1 h.2
  · exact smoothBatch_at smoothBatch20.down h.1 h.2
  · exact smoothBatch_at smoothBatch21.down h.1 h.2
  · exact smoothBatch_at smoothBatch22.down h.1 h.2
  · exact smoothBatch_at smoothBatch23.down h.1 h.2
  · exact smoothBatch_at smoothBatch24.down h.1 h.2
  · exact smoothBatch_at smoothBatch25.down h.1 h.2
  · exact smoothBatch_at smoothBatch26.down h.1 h.2
  · exact smoothBatch_at smoothBatch27.down h.1 h.2
  · exact smoothBatch_at smoothBatch28.down h.1 h.2
  · exact smoothBatch_at smoothBatch29.down h.1 h.2
  · exact smoothBatch_at smoothBatch30.down h.1 h.2
  · exact smoothBatch_at smoothBatch31.down h.1 h.2
  · exact smoothBatch_at smoothBatch32.down h.1 h.2
  · exact smoothBatch_at smoothBatch33.down h.1 h.2
  · exact smoothBatch_at smoothBatch34.down h.1 h.2
  · exact smoothBatch_at smoothBatch35.down h.1 h.2
  · exact smoothBatch_at smoothBatch36.down h.1 h.2
  · exact smoothBatch_at smoothBatch37.down h.1 h.2
  · exact smoothBatch_at smoothBatch38.down h.1 h.2
  · exact smoothBatch_at smoothBatch39.down h.1 h.2
  · exact smoothBatch_at smoothBatch40.down h.1 h.2
  · exact smoothBatch_at smoothBatch41.down h.1 h.2
  · exact smoothBatch_at smoothBatch42.down h.1 h.2

private def groupCondition (i : Nat) : Prop :=
  groupValid i ∧ (i+1 < groupRowsSize → groupValue i < groupValue (i+1))

private instance (i : Nat) : Decidable (groupCondition i) := by
  unfold groupCondition
  infer_instance

private def groupBatch (start count : Nat) : Bool :=
  (List.range' start count).all (fun i => decide (groupCondition i))

private lemma groupBatch_at {start count i : Nat} (check : groupBatch start count = true)
    (lo : start ≤ i) (hi : i < start+count) : groupCondition i :=
  of_decide_eq_true (List.all_eq_true.mp check i
    (List.mem_range'.mpr ⟨i-start, by omega, by simp; omega⟩))


set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch0 : PLift (groupBatch 0 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch1 : PLift (groupBatch 32 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch2 : PLift (groupBatch 64 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch3 : PLift (groupBatch 96 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch4 : PLift (groupBatch 128 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch5 : PLift (groupBatch 160 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch6 : PLift (groupBatch 192 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch7 : PLift (groupBatch 224 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch8 : PLift (groupBatch 256 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch9 : PLift (groupBatch 288 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch10 : PLift (groupBatch 320 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch11 : PLift (groupBatch 352 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch12 : PLift (groupBatch 384 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch13 : PLift (groupBatch 416 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch14 : PLift (groupBatch 448 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch15 : PLift (groupBatch 480 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch16 : PLift (groupBatch 512 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch17 : PLift (groupBatch 544 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch18 : PLift (groupBatch 576 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch19 : PLift (groupBatch 608 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch20 : PLift (groupBatch 640 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def groupBatch21 : PLift (groupBatch 672 18 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem groupChecked (i : Nat) (hi : i < groupRowsSize) : groupCondition i := by
  have hsize : groupRowsSize = 690 := by decide +kernel
  rw [hsize] at hi
  have all : (0 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ (96 ≤ i ∧ i < 128) ∨ (128 ≤ i ∧ i < 160) ∨ (160 ≤ i ∧ i < 192) ∨ (192 ≤ i ∧ i < 224) ∨ (224 ≤ i ∧ i < 256) ∨ (256 ≤ i ∧ i < 288) ∨ (288 ≤ i ∧ i < 320) ∨ (320 ≤ i ∧ i < 352) ∨ (352 ≤ i ∧ i < 384) ∨ (384 ≤ i ∧ i < 416) ∨ (416 ≤ i ∧ i < 448) ∨ (448 ≤ i ∧ i < 480) ∨ (480 ≤ i ∧ i < 512) ∨ (512 ≤ i ∧ i < 544) ∨ (544 ≤ i ∧ i < 576) ∨ (576 ≤ i ∧ i < 608) ∨ (608 ≤ i ∧ i < 640) ∨ (640 ≤ i ∧ i < 672) ∨ (672 ≤ i ∧ i < 690) := by omega
  rcases all with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact groupBatch_at groupBatch0.down h.1 h.2
  · exact groupBatch_at groupBatch1.down h.1 h.2
  · exact groupBatch_at groupBatch2.down h.1 h.2
  · exact groupBatch_at groupBatch3.down h.1 h.2
  · exact groupBatch_at groupBatch4.down h.1 h.2
  · exact groupBatch_at groupBatch5.down h.1 h.2
  · exact groupBatch_at groupBatch6.down h.1 h.2
  · exact groupBatch_at groupBatch7.down h.1 h.2
  · exact groupBatch_at groupBatch8.down h.1 h.2
  · exact groupBatch_at groupBatch9.down h.1 h.2
  · exact groupBatch_at groupBatch10.down h.1 h.2
  · exact groupBatch_at groupBatch11.down h.1 h.2
  · exact groupBatch_at groupBatch12.down h.1 h.2
  · exact groupBatch_at groupBatch13.down h.1 h.2
  · exact groupBatch_at groupBatch14.down h.1 h.2
  · exact groupBatch_at groupBatch15.down h.1 h.2
  · exact groupBatch_at groupBatch16.down h.1 h.2
  · exact groupBatch_at groupBatch17.down h.1 h.2
  · exact groupBatch_at groupBatch18.down h.1 h.2
  · exact groupBatch_at groupBatch19.down h.1 h.2
  · exact groupBatch_at groupBatch20.down h.1 h.2
  · exact groupBatch_at groupBatch21.down h.1 h.2

/-- The harmonic inequality in the exact 20,000,000-generator reduction. -/
theorem harmonic (steps : ∀ i, i+1 < primeRowsSize → primeStep i) :
    (251/500 : ℚ) ≤ ∑ k ∈ generators 20000000, 1 / (k : ℚ) :=
  exactHarmonic steps (fun i hi => (smoothChecked i hi).1)
    (fun i hi => (groupChecked i hi).1)
    (fun i hi => (smoothChecked i (by omega)).2 hi)
    (fun i hi => (groupChecked i (by omega)).2 hi) lowerNumerics

end ColtonH3Data

namespace ColtonH3Data

open Finset


def upperCofactor (i : Nat) : Nat := (upperRowsAt (i)).1

def upperIndex (i : Nat) : Nat := (upperRowsAt (i)).2

def upperTriangle (i : Nat) : Nat :=
  let r := rankAt (upperIndex i)
  r * (r+1) / 2

def upperRow (i : Nat) : Prop :=
  36 ≤ upperCofactor i ∧ upperCofactor i ≤ 66445 ∧ upperIndex i < primeRowsSize ∧
    boundary (upperIndex i) = 20000000 / upperCofactor i

instance (i : Nat) : Decidable (upperRow i) := by
  unfold upperRow
  infer_instance

private def upperBatch (start count : Nat) : Bool :=
  (List.range' start count).all (fun i => decide (upperRow i))

private lemma upperBatch_at {start count i : Nat} (check : upperBatch start count = true)
    (lo : start ≤ i) (hi : i < start+count) : upperRow i :=
  of_decide_eq_true (List.all_eq_true.mp check i
    (List.mem_range'.mpr ⟨i-start, by omega, by simp; omega⟩))


set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch0 : PLift (upperBatch 0 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch1 : PLift (upperBatch 32 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch2 : PLift (upperBatch 64 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch3 : PLift (upperBatch 96 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch4 : PLift (upperBatch 128 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch5 : PLift (upperBatch 160 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch6 : PLift (upperBatch 192 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch7 : PLift (upperBatch 224 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch8 : PLift (upperBatch 256 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch9 : PLift (upperBatch 288 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch10 : PLift (upperBatch 320 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch11 : PLift (upperBatch 352 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch12 : PLift (upperBatch 384 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch13 : PLift (upperBatch 416 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch14 : PLift (upperBatch 448 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch15 : PLift (upperBatch 480 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch16 : PLift (upperBatch 512 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch17 : PLift (upperBatch 544 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch18 : PLift (upperBatch 576 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch19 : PLift (upperBatch 608 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch20 : PLift (upperBatch 640 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch21 : PLift (upperBatch 672 32 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperBatch22 : PLift (upperBatch 704 17 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem upperValid (i : Nat) (hi : i < upperRowsSize) : upperRow i := by
  have hsize : upperRowsSize = 721 := by decide +kernel
  rw [hsize] at hi
  have all : (0 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ (96 ≤ i ∧ i < 128) ∨ (128 ≤ i ∧ i < 160) ∨ (160 ≤ i ∧ i < 192) ∨ (192 ≤ i ∧ i < 224) ∨ (224 ≤ i ∧ i < 256) ∨ (256 ≤ i ∧ i < 288) ∨ (288 ≤ i ∧ i < 320) ∨ (320 ≤ i ∧ i < 352) ∨ (352 ≤ i ∧ i < 384) ∨ (384 ≤ i ∧ i < 416) ∨ (416 ≤ i ∧ i < 448) ∨ (448 ≤ i ∧ i < 480) ∨ (480 ≤ i ∧ i < 512) ∨ (512 ≤ i ∧ i < 544) ∨ (544 ≤ i ∧ i < 576) ∨ (576 ≤ i ∧ i < 608) ∨ (608 ≤ i ∧ i < 640) ∨ (640 ≤ i ∧ i < 672) ∨ (672 ≤ i ∧ i < 704) ∨ (704 ≤ i ∧ i < 721) := by omega
  rcases all with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact upperBatch_at upperBatch0.down h.1 h.2
  · exact upperBatch_at upperBatch1.down h.1 h.2
  · exact upperBatch_at upperBatch2.down h.1 h.2
  · exact upperBatch_at upperBatch3.down h.1 h.2
  · exact upperBatch_at upperBatch4.down h.1 h.2
  · exact upperBatch_at upperBatch5.down h.1 h.2
  · exact upperBatch_at upperBatch6.down h.1 h.2
  · exact upperBatch_at upperBatch7.down h.1 h.2
  · exact upperBatch_at upperBatch8.down h.1 h.2
  · exact upperBatch_at upperBatch9.down h.1 h.2
  · exact upperBatch_at upperBatch10.down h.1 h.2
  · exact upperBatch_at upperBatch11.down h.1 h.2
  · exact upperBatch_at upperBatch12.down h.1 h.2
  · exact upperBatch_at upperBatch13.down h.1 h.2
  · exact upperBatch_at upperBatch14.down h.1 h.2
  · exact upperBatch_at upperBatch15.down h.1 h.2
  · exact upperBatch_at upperBatch16.down h.1 h.2
  · exact upperBatch_at upperBatch17.down h.1 h.2
  · exact upperBatch_at upperBatch18.down h.1 h.2
  · exact upperBatch_at upperBatch19.down h.1 h.2
  · exact upperBatch_at upperBatch20.down h.1 h.2
  · exact upperBatch_at upperBatch21.down h.1 h.2
  · exact upperBatch_at upperBatch22.down h.1 h.2

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def upperNumeric : PLift ((∑ i ∈ range upperRowsSize, upperTriangle i) = 1735192103) := ⟨by decide +kernel⟩

set_option maxRecDepth 20000 in
theorem upperCounts (steps : ∀ i, i+1 < primeRowsSize → primeStep i)
    (i : Nat) (hi : i < upperRowsSize) :
    rankAt (upperIndex i) = (20000000 / upperCofactor i).primeCounting := by
  obtain ⟨_,_,hidx,hend⟩ := upperValid i hi
  rw [(ranks_correct steps hidx).1,hend]

/-- Candidate cofactors for the exponent-one upper estimate. -/
def upperSet : Finset Nat := (range upperRowsSize).image upperCofactor

set_option maxRecDepth 20000 in
theorem upperSum (steps : ∀ i, i+1 < primeRowsSize → primeStep i) :
    ∑ m ∈ upperSet, (20000000/m).primeCounting * ((20000000/m).primeCounting+1) / 2 ≤ 1735192103 := by
  calc
    _ ≤ ∑ i ∈ range upperRowsSize,
          (20000000/upperCofactor i).primeCounting * ((20000000/upperCofactor i).primeCounting+1) / 2 := by
        unfold upperSet
        exact sum_image_le_of_nonneg (s := range upperRowsSize) (g := upperCofactor)
          (f := fun m => (20000000/m).primeCounting*((20000000/m).primeCounting+1)/2)
          (fun _ _ => Nat.zero_le _)
    _ = ∑ i ∈ range upperRowsSize, upperTriangle i := by
        apply sum_congr rfl
        intro i hi
        rw [upperTriangle, upperCounts steps i (mem_range.mp hi)]
    _ = _ := upperNumeric.down

end ColtonH3Data

namespace ColtonH3Upper

open Finset
open scoped Nat

def limit : ℕ := 20000000
def maxPrime (k : ℕ) : ℕ := k.primeFactors.sup id
def generators : Finset ℕ :=
  (Icc 1 limit).filter (fun k => 0 < k ∧ 2*k.divisors.card ∣ k)

private theorem card_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (p^e).divisors.card = e+1 := by
  rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply_prime_pow hp]

theorem split_prime {k p : ℕ} (hk : 0 < k) (hp : p.Prime) :
    k = p^(k.factorization p) * ordCompl[p] k ∧
    k.divisors.card = (k.factorization p+1)*(ordCompl[p] k).divisors.card := by
  have eq := Nat.ordProj_mul_ordCompl_eq_self k p
  exact ⟨eq.symm, by
    conv_lhs => rw [← eq]
    rw [Nat.Coprime.card_divisors_mul ((Nat.coprime_ordCompl hp hk.ne').pow_left _),
      card_prime_pow hp]⟩

theorem eight_or_twelve {k : ℕ} (hk : 0 < k) (good : 2*k.divisors.card ∣ k) :
    8 ∣ k ∨ 12 ∣ k := by
  let e := k.factorization 2
  have hp : Nat.Prime 2 := Nat.prime_two
  let m := ordCompl[2] k
  have hpowers : ∀ {i}, 2^i ∣ k ↔ i ≤ e := hp.pow_dvd_iff_le_factorization hk.ne'
  obtain ⟨split, divisors⟩ := split_prime hk hp
  change k = 2^e*m at split
  change k.divisors.card = (e+1)*m.divisors.card at divisors
  rw [divisors, ← Nat.mul_assoc] at good
  by_cases large : 3 ≤ e
  · exact Or.inl (hpowers.mpr large)
  · interval_cases e
    · have d : 2 ∣ k := (dvd_mul_right 2 m.divisors.card).trans (by simpa using good)
      have h := (hpowers (i := 1)).mp d
      omega
    · have d : 4 ∣ k := (dvd_mul_right 4 m.divisors.card).trans (by simpa using good)
      have h := (hpowers (i := 2)).mp d
      omega
    · have three : 3 ∣ k := (show 3 ∣ 2*(2+1)*m.divisors.card from
        dvd_mul_of_dvd_left (by decide) _).trans good
      have four : 4 ∣ k := (hpowers (i := 2)).mpr (by decide)
      exact Or.inr (Nat.lcm_dvd four three)

private def multiples (d : ℕ) : Finset ℕ :=
  (Icc 1 (limit/d)).image (d*·)

private theorem mem_multiples {d k : ℕ} (hd : 0 < d) :
    k ∈ multiples d ↔ 0 < k ∧ k ≤ limit ∧ d ∣ k := by
  rw [multiples, mem_image]
  constructor
  · rintro ⟨j,hj,rfl⟩
    obtain ⟨lo,hi⟩ := mem_Icc.mp hj
    exact ⟨Nat.mul_pos hd lo, by simpa only [Nat.mul_comm d j] using (Nat.le_div_iff_mul_le hd).mp hi,
      dvd_mul_right _ _⟩
  · rintro ⟨pos,hi,⟨j,rfl⟩⟩
    exact ⟨j, mem_Icc.mpr ⟨by
      by_contra! zero
      have jzero : j = 0 := by omega
      simp [jzero] at pos,
      (Nat.le_div_iff_mul_le hd).mpr (by rwa [Nat.mul_comm])⟩,rfl⟩

private theorem card_multiples {d : ℕ} (hd : 0 < d) :
    (multiples d).card = limit/d := by
  rw [multiples, card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left hd h),
    Nat.card_Icc]
  simp

theorem generator_card : generators.card ≤ 3333333 := by
  have inter : multiples 8 ∩ multiples 12 = multiples 24 := by
    ext k
    simp only [mem_inter, mem_multiples (by decide : 0 < 8),
      mem_multiples (by decide : 0 < 12), mem_multiples (by decide : 0 < 24)]
    constructor
    · rintro ⟨⟨pos,hi,d₈⟩,_,_,d₁₂⟩
      exact ⟨pos,hi,Nat.lcm_dvd d₈ d₁₂⟩
    · rintro ⟨pos,hi,d₂₄⟩
      exact ⟨⟨pos,hi,(show 8 ∣ 24 by decide).trans d₂₄⟩,
        ⟨pos,hi,(show 12 ∣ 24 by decide).trans d₂₄⟩⟩
  have unionSize := card_union_add_card_inter (multiples 8) (multiples 12)
  rw [inter, card_multiples (by decide), card_multiples (by decide),
    card_multiples (by decide)] at unionSize
  have subset : generators ⊆ multiples 8 ∪ multiples 12 := by
    intro k hk
    obtain ⟨range,pos,good⟩ := mem_filter.mp hk
    have hi := (mem_Icc.mp range).2
    exact (eight_or_twelve pos good).elim
      (fun h => mem_union_left _ ((mem_multiples (by decide)).mpr ⟨pos,hi,h⟩))
      (fun h => mem_union_right _ ((mem_multiples (by decide)).mpr ⟨pos,hi,h⟩))
  have := card_le_card subset
  norm_num [limit] at unionSize
  omega

theorem small_prime_contribution :
    ∑ k ∈ generators.filter (fun k => maxPrime k ≤ 300), (maxPrime k).primeCounting ≤ 206666646 := by
  let s := generators.filter (fun k => maxPrime k ≤ 300)
  have cap : (300 : Nat).primeCounting = 62 := by decide +kernel
  calc
    _ ≤ ∑ _ ∈ s, 62 := sum_le_sum (fun k hk => cap ▸
      Nat.monotone_primeCounting (mem_filter.mp hk).2)
    _ = s.card*62 := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_right 62 ((card_filter_le _ _).trans generator_card)

end ColtonH3Upper

namespace ColtonH3Upper

open Finset
open scoped Nat

private theorem maxPrime_mem {k : ℕ} (hk : k ∈ generators) :
    maxPrime k ∈ k.primeFactors := by
  have good := (mem_filter.mp hk).2
  have h : 1 < k := by
    by_contra! lo
    have one : k = 1 := by omega
    subst k
    norm_num at good
  simpa [maxPrime] using Finset.sup_mem_of_nonempty (f := id) (Nat.nonempty_primeFactors.mpr h)

theorem prime_maxPrime {k : ℕ} (hk : k ∈ generators) : (maxPrime k).Prime :=
  Nat.prime_of_mem_primeFactors (maxPrime_mem hk)

private theorem no_large_factor_in_divisor_count {m p : ℕ} (hm : 0 < m)
    (upper : m ≤ limit) (hp : p.Prime) (large : 300 < p) :
    ¬ p ∣ m.divisors.card := by
  rw [Nat.card_divisors hm.ne']
  intro hd
  obtain ⟨q,hq,hpq⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp) _).mp hd
  have hprime := Nat.prime_of_mem_primeFactors hq
  have low : m.factorization q < 25 := by
    by_contra! too
    have hm25 := Nat.le_of_dvd hm ((hprime.pow_dvd_iff_le_factorization hm.ne').mpr too)
    have hq25 := Nat.pow_le_pow_left hprime.two_le 25
    unfold limit at upper
    norm_num at hq25
    omega
  have hpq' := Nat.le_of_dvd (Nat.succ_pos _) hpq
  omega

def multiplicity (k : ℕ) : ℕ := k.factorization (maxPrime k)
def cofactor (k : ℕ) : ℕ := ordCompl[maxPrime k] k

theorem large_prime_shape {k : ℕ} (hk : k ∈ generators) (large : 300 < maxPrime k) :
    let p := maxPrime k
    let e := multiplicity k
    let m := cofactor k
    k = p^e*m ∧ 0 < m ∧ (e = 1 ∨ e = 2) ∧ 2*(e+1)*m.divisors.card ∣ m := by
  obtain ⟨range,pos,good⟩ := mem_filter.mp hk
  let p := maxPrime k
  let e := multiplicity k
  let m := cofactor k
  change k = p^e*m ∧ 0 < m ∧ (e = 1 ∨ e = 2) ∧ 2*(e+1)*m.divisors.card ∣ m
  have hlimit := (mem_Icc.mp range).2
  have hp := prime_maxPrime hk
  have ep : 1 ≤ e := (hp.dvd_iff_one_le_factorization pos.ne').mp
    (Nat.dvd_of_mem_primeFactors (maxPrime_mem hk))
  have eu : e ≤ 2 := by
    by_contra! too
    have pk : p^3 ≤ k := Nat.le_of_dvd pos ((hp.pow_dvd_iff_le_factorization pos.ne').mpr too)
    have gp := Nat.pow_le_pow_left (show 301 ≤ p by exact large) 3
    unfold limit at hlimit
    norm_num at gp
    omega
  have mp : 0 < m := Nat.ordCompl_pos p pos.ne'
  have ml : m ≤ limit := (Nat.ordCompl_le k p).trans hlimit
  obtain ⟨split, card⟩ := split_prime pos hp
  have hsmall : ¬ p ∣ 2*(e+1) := by
    intro h
    have := Nat.le_of_dvd (show 0 < 2*(e+1) by omega) h
    change 300 < p at large
    omega
  have hnot : ¬ p ∣ 2*(e+1)*m.divisors.card := by
    intro h
    exact (hp.dvd_mul.mp h).elim hsmall (no_large_factor_in_divisor_count mp ml hp large)
  have dk : 2*(e+1)*m.divisors.card ∣ k := by
    simpa only [card, Nat.mul_assoc, e, multiplicity, m, cofactor, p] using good
  exact ⟨split,mp,by omega,Nat.dvd_ordCompl_of_dvd_not_dvd dk hnot⟩

private theorem min_cofactor_one {m : ℕ} (pos : 0 < m) (h : 4*m.divisors.card ∣ m) : 36 ≤ m := by
  by_contra! hlo
  have table : ∀ i : Fin 36, 0 < i.val → ¬ 4*i.val.divisors.card ∣ i.val := by decide +kernel
  exact table ⟨m,hlo⟩ pos h

private theorem min_cofactor_two {m : ℕ} (pos : 0 < m) (h : 6*m.divisors.card ∣ m) : 72 ≤ m := by
  by_contra! hlo
  have table : ∀ i : Fin 72, 0 < i.val → ¬ 6*i.val.divisors.card ∣ i.val := by decide +kernel
  exact table ⟨m,hlo⟩ pos h

theorem cofactor_moduli {m : ℕ} (pos : 0 < m) (good : 4*m.divisors.card ∣ m) :
    16 ∣ m ∨ 12 ∣ m := by
  let e := m.factorization 2
  let d := (ordCompl[2] m).divisors.card
  have power : ∀ {i}, 2^i ∣ m ↔ i ≤ e := Nat.prime_two.pow_dvd_iff_le_factorization pos.ne'
  have hcard : m.divisors.card = (e+1)*d := (split_prime pos Nat.prime_two).2
  rw [hcard, ← Nat.mul_assoc] at good
  by_cases large : 4 ≤ e
  · exact Or.inl (power.mpr large)
  · interval_cases e
    · have four : 4 ∣ m := (dvd_mul_right 4 d).trans (by simpa using good)
      exact False.elim (by have := (power (i := 2)).mp four; omega)
    · have four : 4 ∣ m := (dvd_mul_of_dvd_left (show 4 ∣ 8 by decide) d).trans good
      exact False.elim (by have := (power (i := 2)).mp four; omega)
    · have four : 4 ∣ m := (power (i := 2)).mpr (by decide)
      have three : 3 ∣ m := (dvd_mul_of_dvd_left (show 3 ∣ 12 by decide) d).trans good
      exact Or.inr (Nat.lcm_dvd four three)
    · have sixteen : 16 ∣ m := (dvd_mul_right 16 d).trans good
      exact False.elim (by have := (power (i := 4)).mp sixteen; omega)

private theorem prime_rank_strict {p q : ℕ} (less : p < q) (prime : q.Prime) :
    p.primeCounting < q.primeCounting := by
  have h := Nat.monotone_primeCounting' (show p+1 ≤ q by omega)
  change p.primeCounting ≤ q.primeCounting' at h
  have step : q.primeCounting = q.primeCounting' + 1 := by
    change Nat.count Nat.Prime (q+1) = Nat.count Nat.Prime q + 1
    simp [Nat.count_succ, prime]
  omega

private theorem triangle_bound (n : ℕ) :
    ∑ p ∈ n.primesLE, p.primeCounting ≤ n.primeCounting*(n.primeCounting+1)/2 := by
  have inj : Set.InjOn Nat.primeCounting n.primesLE := by
    intro a ha b hb eq
    have p := Nat.prime_of_mem_primesLE ha
    have q := Nat.prime_of_mem_primesLE hb
    rcases lt_trichotomy a b with lt | same | gt
    · exact (prime_rank_strict lt q).ne eq |>.elim
    · exact same
    · exact (prime_rank_strict gt p).ne eq.symm |>.elim
  have sub : n.primesLE.image Nat.primeCounting ⊆ range (n.primeCounting+1) := by
    intro x h
    obtain ⟨p,hp,rfl⟩ := mem_image.mp h
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.monotone_primeCounting (Nat.le_of_mem_primesLE hp)))
  calc
    _ = ∑ r ∈ n.primesLE.image Nat.primeCounting, r := (sum_image inj).symm
    _ ≤ ∑ r ∈ range (n.primeCounting+1), r :=
      sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)
    _ = _ := by rw [sum_range_id, Nat.add_sub_cancel, Nat.mul_comm]

def firstPower : Finset ℕ := generators.filter (fun k => 300 < maxPrime k ∧ multiplicity k = 1)
def secondPower : Finset ℕ := generators.filter (fun k => 300 < maxPrime k ∧ multiplicity k = 2)

theorem firstPower_le (cofactors : Finset ℕ)
    (complete : ∀ m, 1 ≤ m → m ≤ 66445 → 4*m.divisors.card ∣ m → m ∈ cofactors) :
    ∑ k ∈ firstPower, (maxPrime k).primeCounting ≤
      ∑ m ∈ cofactors, (limit/m).primeCounting*((limit/m).primeCounting+1)/2 := by
  let f (k : ℕ) : (Σ _ : ℕ, ℕ) := ⟨cofactor k,maxPrime k⟩
  let slots := cofactors.sigma (fun m => (limit/m).primesLE)
  have params {k : ℕ} (hk : k ∈ firstPower) :
      k = maxPrime k * cofactor k ∧ cofactor k ∈ cofactors ∧
        maxPrime k ∈ (limit/cofactor k).primesLE := by
    obtain ⟨gen,large,one⟩ := mem_filter.mp hk
    obtain ⟨split,pos,_,dvd⟩ := large_prime_shape gen large
    have hkmax := (mem_Icc.mp (mem_filter.mp gen).1).2
    rw [one, pow_one] at split
    rw [one] at dvd
    have prod_bound : maxPrime k * cofactor k ≤ limit := split ▸ hkmax
    have cap_m : cofactor k ≤ 66445 := by
      have h := Nat.mul_le_mul_right (cofactor k) (show 301 ≤ maxPrime k by exact large)
      have h' := h.trans prod_bound
      unfold limit at h'
      omega
    exact ⟨split, complete _ pos cap_m dvd, Nat.mem_primesLE.mpr
      ⟨(Nat.le_div_iff_mul_le pos).mpr prod_bound,prime_maxPrime gen⟩⟩
  have inj : Set.InjOn f firstPower := by
    intro a ha b hb eq
    have eq_m := congrArg Sigma.fst eq
    have eq_p := congrArg (fun x : (Σ _ : ℕ, ℕ) => x.2) eq
    change cofactor a = cofactor b at eq_m
    change maxPrime a = maxPrime b at eq_p
    rw [(params ha).1,(params hb).1,eq_m,eq_p]
  have sub : firstPower.image f ⊆ slots := by
    intro x hx
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hx
    exact mem_sigma.mpr ⟨(params hk).2.1,(params hk).2.2⟩
  calc
    _ = ∑ x ∈ firstPower.image f, x.2.primeCounting := (sum_image inj).symm
    _ ≤ ∑ x ∈ slots, x.2.primeCounting :=
      sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)
    _ = ∑ m ∈ cofactors, ∑ p ∈ (limit/m).primesLE, p.primeCounting := by
      simp only [slots, sum_sigma]
    _ ≤ _ := sum_le_sum (fun m _ => triangle_bound (limit/m))

end ColtonH3Upper

namespace ColtonH3Upper

open Finset

private theorem boundedPairCard (s : Finset Nat) (f g : Nat → Nat) (a b c d : Nat)
    (fit : ∀ n ∈ s, a ≤ f n ∧ f n ≤ b ∧ c ≤ g n ∧ g n ≤ d)
    (injective : Set.InjOn (fun n => (f n,g n)) ↑s) :
    s.card ≤ (b+1-a)*(d+1-c) := by
  let t := (Icc a b) ×ˢ (Icc c d)
  have into (n : ℕ) (hn : n ∈ s) : (f n,g n) ∈ t := by
    obtain ⟨lo,hi,lo',hi'⟩ := fit n hn
    exact (mem_product (s := Icc a b) (t := Icc c d)).mpr
      ⟨mem_Icc.mpr ⟨lo,hi⟩,mem_Icc.mpr ⟨lo',hi'⟩⟩
  have h : s.card ≤ t.card := card_le_card_of_injOn (s := s) (t := t) _ into injective
  simpa only [t,card_product,Nat.card_Icc] using h

private theorem boundedPairSum (s : Finset Nat) (f g w : Nat → Nat) (a b c d cap : Nat)
    (fit : ∀ n ∈ s, a ≤ f n ∧ f n ≤ b ∧ c ≤ g n ∧ g n ≤ d)
    (injective : Set.InjOn (fun n => (f n,g n)) ↑s)
    (limited : ∀ n ∈ s, w n ≤ cap) :
    ∑ n ∈ s, w n ≤ (b+1-a)*(d+1-c)*cap := by
  calc
    _ ≤ ∑ _ ∈ s, cap := sum_le_sum limited
    _ = s.card*cap := by rw [sum_const,smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right cap (boundedPairCard s f g a b c d fit injective)

private def trialDivisors : Finset Nat := {2,3,5,7,11,13,17,19,23}

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem primeCap : (527 : Nat).primeCounting ≤ 100 := by
  let can := (range 528).filter (fun p => p ∈ trialDivisors ∨ ∀ d ∈ trialDivisors, ¬ d ∣ p)
  have contain : Nat.primesLE 527 ⊆ can := by
    intro p hp
    obtain ⟨hp_le,hp_prime⟩ := Nat.mem_primesLE.mp hp
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hp_le), ?_⟩
    by_cases h : p ∈ trialDivisors
    · exact Or.inl h
    · right
      intro d hd dvd
      have hd2 : 2 ≤ d := by
        simp only [trialDivisors,mem_insert,mem_singleton] at hd
        omega
      have he := (Nat.dvd_prime_two_le hp_prime hd2).mp dvd
      exact h (he ▸ hd)
  have count : can.card ≤ 100 := by decide +kernel
  rw [← Nat.primesLE_card_eq_primeCounting]
  exact (card_le_card contain).trans count

private theorem secondPower_params (k : ℕ) (hk : k ∈ secondPower) :
    k = (maxPrime k)^2 * cofactor k ∧
      301 ≤ maxPrime k ∧ maxPrime k ≤ 527 ∧ 1 ≤ cofactor k ∧ cofactor k ≤ 220 := by
  change k ∈ generators.filter (fun n => 300 < maxPrime n ∧ multiplicity n = 2) at hk
  obtain ⟨gen,large,two⟩ := mem_filter.mp hk
  obtain ⟨split,pos,_,dvd⟩ := large_prime_shape gen large
  have hkmax := (mem_Icc.mp (mem_filter.mp gen).1).2
  rw [two] at split dvd
  have low := min_cofactor_two pos dvd
  have prod_bound : (maxPrime k)^2 * cofactor k ≤ limit := split ▸ hkmax
  have pm : maxPrime k ≤ 527 := by
    by_contra! h
    have h₁ := Nat.pow_le_pow_left (show 528 ≤ maxPrime k by omega) 2
    have h₂ := Nat.mul_le_mul h₁ low
    have h₃ := h₂.trans prod_bound
    norm_num [limit] at h₃
  have cm : cofactor k ≤ 220 := by
    have h₁ := Nat.pow_le_pow_left (show 301 ≤ maxPrime k by exact large) 2
    have h₂ := (Nat.mul_le_mul_right (cofactor k) h₁).trans prod_bound
    norm_num [limit] at h₂
    omega
  exact ⟨split,large,pm,pos,cm⟩

/-- The largest prime squared leaves a cofactor at most 220. The pair of
largest prime and cofactor identifies the generator. -/
theorem secondPower_le :
    ∑ k ∈ secondPower, (maxPrime k).primeCounting ≤ 4994000 := by
  have inj : Set.InjOn (fun k => (maxPrime k,cofactor k)) ↑secondPower := by
    intro a ha b hb eq
    have eq_p : maxPrime a = maxPrime b := congrArg Prod.fst eq
    have eq_m : cofactor a = cofactor b := congrArg Prod.snd eq
    calc
      a = (maxPrime a)^2 * cofactor a := (secondPower_params a ha).1
      _ = (maxPrime b)^2 * cofactor b := by rw [eq_p,eq_m]
      _ = b := (secondPower_params b hb).1.symm
  refine boundedPairSum secondPower maxPrime cofactor (fun k => (maxPrime k).primeCounting)
    301 527 1 220 100 (fun k hk => (secondPower_params k hk).2) inj ?_
  intro k hk
  exact (Nat.monotone_primeCounting (secondPower_params k hk).2.2.1).trans primeCap

/-- The low-largest-prime, exponent-one and exponent-two contributions bound
the excluded-prime sum. -/
theorem excluded_bound (cofactors : Finset ℕ)
    (complete : ∀ m, 1 ≤ m → m ≤ 66445 → 4*m.divisors.card ∣ m → m ∈ cofactors)
    (numeric : ∑ m ∈ cofactors, (limit/m).primeCounting*((limit/m).primeCounting+1)/2 ≤
      1772500000) :
    ∑ k ∈ generators, (maxPrime k).primeCounting ≤ 2000000000 := by
  let term (k : ℕ) := (maxPrime k).primeCounting
  let small := generators.filter (fun k => maxPrime k ≤ 300)
  let large := generators.filter (fun k => ¬ maxPrime k ≤ 300)
  have first_iff (k : ℕ) : k ∈ firstPower ↔ k ∈ generators ∧ 300 < maxPrime k ∧ multiplicity k = 1 := by
    change k ∈ generators.filter (fun n => 300 < maxPrime n ∧ multiplicity n = 1) ↔ _
    exact mem_filter
  have second_iff (k : ℕ) : k ∈ secondPower ↔ k ∈ generators ∧ 300 < maxPrime k ∧ multiplicity k = 2 := by
    change k ∈ generators.filter (fun n => 300 < maxPrime n ∧ multiplicity n = 2) ↔ _
    exact mem_filter
  have large_iff (k : ℕ) : k ∈ large ↔ k ∈ generators ∧ ¬ maxPrime k ≤ 300 := by
    change k ∈ generators.filter (fun n => ¬ maxPrime n ≤ 300) ↔ _
    exact mem_filter
  have groups : large = firstPower ∪ secondPower := by
    apply Finset.ext
    intro k
    constructor
    · intro hk
      obtain ⟨gen,hn⟩ := (large_iff k).mp hk
      have hi : 300 < maxPrime k := lt_of_not_ge hn
      rcases (large_prime_shape gen hi).2.2.1 with one | two
      · exact mem_union_left _ ((first_iff k).mpr ⟨gen,hi,one⟩)
      · exact mem_union_right _ ((second_iff k).mpr ⟨gen,hi,two⟩)
    · intro hk
      rcases mem_union.mp hk with h | h
      · obtain ⟨gen,hi,_⟩ := (first_iff k).mp h
        exact (large_iff k).mpr ⟨gen,hi.not_ge⟩
      · obtain ⟨gen,hi,_⟩ := (second_iff k).mp h
        exact (large_iff k).mpr ⟨gen,hi.not_ge⟩
  have disj : Disjoint firstPower secondPower := by
    apply disjoint_left.mpr
    intro k hk hq
    have h₁ := ((first_iff k).mp hk).2.2
    have h₂ := ((second_iff k).mp hq).2.2
    omega
  have partition : (∑ k ∈ generators, term k) =
      (∑ k ∈ small, term k) + (∑ k ∈ large, term k) :=
    (sum_filter_add_sum_filter_not (s := generators) (p := fun k => maxPrime k ≤ 300) term).symm
  have partition_large : (∑ k ∈ large, term k) =
      (∑ k ∈ firstPower, term k) + (∑ k ∈ secondPower, term k) :=
    (congrArg (fun S : Finset ℕ => ∑ k ∈ S, term k) groups).trans (sum_union disj)
  have small_le : (∑ k ∈ small, term k) ≤ 206666646 := small_prime_contribution
  have first_le : (∑ k ∈ firstPower, term k) ≤ 1772500000 :=
    (firstPower_le cofactors complete).trans numeric
  have second_le : (∑ k ∈ secondPower, term k) ≤ 4994000 := secondPower_le
  change ∑ k ∈ generators, term k ≤ 2000000000
  calc
    _ = (∑ k ∈ small, term k) + ((∑ k ∈ firstPower, term k) + (∑ k ∈ secondPower, term k)) :=
      partition.trans (congrArg _ partition_large)
    _ ≤ 206666646 + (1772500000 + 4994000) := Nat.add_le_add small_le (Nat.add_le_add first_le second_le)
    _ ≤ _ := by decide

end ColtonH3Upper

namespace ColtonH3Upper

open Finset
open scoped Nat

private theorem square_of_odd_divisors {n : Nat} (hn : 0 < n) (odd : Odd n.divisors.card) :
    ∃ r : Nat, n = r^2 := by
  let r := ∏ p ∈ n.primeFactors, p^(n.factorization p/2)
  refine ⟨r,?_⟩
  have hfac (p : Nat) (hp : p ∈ n.primeFactors) : n.factorization p/2*2 = n.factorization p := by
    rw [Nat.card_divisors hn.ne'] at odd
    have dvd := Finset.dvd_prod_of_mem (fun q => n.factorization q+1) hp
    have parity := Nat.odd_iff.mp (odd.of_dvd_nat dvd)
    omega
  calc
    n = ∏ p ∈ n.primeFactors, p^(n.factorization p) := by
      simpa only [Finsupp.prod, Nat.support_factorization] using (Nat.prod_factorization_pow_eq_self hn.ne').symm
    _ = ∏ p ∈ n.primeFactors, (p^(n.factorization p/2))^2 := by
      apply prod_congr rfl
      intro p hp
      rw [← pow_mul, hfac p hp]
    _ = r^2 := by unfold r; rw [Finset.prod_pow]

/-- A cofactor with 2-adic valuation two is 36 times a square. The other
possible cofactors are divisible by sixteen. -/
theorem cofactor_square_or_sixteen {m : Nat} (pos : 0 < m) (good : 4*m.divisors.card ∣ m) :
    16 ∣ m ∨ ∃ r : Nat, m = 36*r^2 := by
  by_cases sixteen : 16 ∣ m
  · exact Or.inl sixteen
  have twelve := (cofactor_moduli pos good).resolve_left sixteen
  let e := m.factorization 2
  let o := ordCompl[2] m
  let d := o.divisors.card
  have power : ∀ {a : Nat}, 2^a ∣ m ↔ a ≤ e := Nat.prime_two.pow_dvd_iff_le_factorization pos.ne'
  have split : m = 2^e*o := (split_prime pos Nat.prime_two).1
  have card : m.divisors.card = (e+1)*d := (split_prime pos Nat.prime_two).2
  have ge : 2 ≤ e := power.mp ((show 4 ∣ 12 by decide).trans twelve)
  have lt : e < 4 := lt_of_not_ge (fun h => sixteen (power.mpr h))
  have two : e = 2 := by
    by_contra different
    have three : e = 3 := by omega
    have dvd : 16*d ∣ m := by simpa only [card, three, Nat.reduceAdd, ← Nat.mul_assoc, Nat.reduceMul] using good
    exact sixteen ((dvd_mul_right 16 d).trans dvd)
  have m_eq : m = 4*o := by simpa only [two, Nat.reducePow] using split
  have cancel : 3*d ∣ o := by
    have dvd := good
    rw [card,two,m_eq] at dvd
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 4) dvd
  have no_even : ¬ Even o := by
    rw [even_iff_two_dvd]
    exact Nat.prime_two.coprime_iff_not_dvd.mp (Nat.coprime_ordCompl Nat.prime_two pos.ne')
  have odd : Odd o := Nat.not_even_iff_odd.mp no_even
  have odd_d : Odd d := odd.of_dvd_nat ((dvd_mul_left d 3).trans cancel)
  have o_pos : 0 < o := Nat.ordCompl_pos 2 pos.ne'
  obtain ⟨s,hs⟩ := square_of_odd_divisors o_pos odd_d
  have div_s : 3 ∣ s := by
    have div_o : 3 ∣ o := (dvd_mul_right 3 d).trans cancel
    rw [hs, pow_two] at div_o
    exact (Nat.prime_three.dvd_mul.mp div_o).elim id id
  obtain ⟨r,hr⟩ := div_s
  exact Or.inr ⟨r, by rw [m_eq,hs,hr]; ring⟩

end ColtonH3Upper

namespace ColtonH3Data

open Finset

private def coverBits : Nat → Nat
  | 0 => 0
  | n+1 => coverBits n ||| 2^(upperCofactor n)

private def coverage : Nat := 0x1000000000000000000000001000100000000000000000000000000000000000100010000000000000000000000000000000000000000000000000001000000010000000000000001000100000000000000000000000000000000000000010000000000000000000000000001000000000000000000000000000000000000000100000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000010000000000000001000100000000000000000001000000000000000000010000000000000000000100000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000001000000000001000100000000000000010000000000000000000000000000000100000000000000000000000000010000000000000000000000000001000000010001000000000000000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000100000000000000000000000000000000000100000000000000000000000000010000000000000000000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000000000000000000000100000000000000010000000000000001000000000000000000000001000000010000000000000000000000000000000000000001000000000000000000010000000000000000000000000001000000000000000000000000000000000000000100000001000100000000000000000000000000000000000100000000000000010000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000000000000000000010000000000000000000000000001000000000000000000000000000000000000000000000001000100010000000000000001000000000000000000000000000000000000000000000001000000000000000000000001000000000000000000000000000100000000000100000001000000000000000000000000000000000000000000000000000000010001000000000000000000000000000000000000000000000000000000000000000000000000000000010001000000000000000000000000000000000000000100000001000000000000000000000000000100000000000000000001000000010000000000000000000000000000000100000001000000000000000000000000000000000000000100000000000100000000000000000000000000000000000100000001000000000000000000000000000000000000000000000001000000000000000000000000000100000000000000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000100000001000000000000000000000000000000000000000000010001000000010000000000000000000000000000000100000001000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000001000000010001000000000000000000000000000000000001000100010000000000000000000000000000000000000000000000000000000000000001000000000001000000000001000000010000000000000000000000000000000100000000000000000000000000010000000000000000000100000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000100000001000000000000000000000001000100000000000000000000000000010000000000000001000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000100010001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000010001000000000000000000000001000000000000000000000000000000000000000100000001000100000000000000000001000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000001000000000000000000000001000000010000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000100010000000000000000000000000000000000010000000000000000000000000001000000000001000000000001000000000000000000000001000000000000000100000000000000000000000000010000000000000000000000000001000000010000000000000000000000000000000000000001000000000000000000000001000000000000000000010000000000000000000000000000000000000001000100000001000000010000000000000000000100000000000000000000000000010000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000100000000000000010000000000000000000100000000000000000000000000000000000000000001000000000000000000000001000000000000000000000000000000000000000100000001000000000000000000000000000000000000000000000001000000010000000000000001000000000000000000000000000000000000000000000001000100000000000000000000000000000000000000010000000000000000000000000000000000000001000000000000000000000000000000000000000100010000000000000000000000000000000000000001000000010000000000000001000000000000000000000000000000010000000000000000000100000000000100000000000000000000000000000001000000000000000000000001000000010001000000000000000000000000000000000001000100000000000000000000000000000000000100010001000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000010000000000000000000000000000000000000000000000000001000000000000000000000001000000000000000000000001000000000000000100010001000000000000000000000000000000000001000000000001000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000000000000000000000000000000000000000000000000000100010000000000000000000000000000000000000001000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000010000000000000000000100000000000000000000000000000000000000000000000100000001000000010000000000000000000000000000000000010000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000100000001000000000000000000010000000000000000000000000001000000010001000000000001000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000001000100000001000000000000000000000000000100000000000000000000000000010000000000000000000000000000000100000001000000010000000000000001000000000000000000000000000100000000000000000000000000000000000100000001000000000000000000000001000000000000000000000001000000010000000000000000000000000000000000000000000000000000000000000001000000000000000100000001000000000001000000000000000000000000000100000001000000000000000000000000000000000000000000000001000000010000000000000000000000000000000000000000000000000000000000000001000100000000000000000001000000000000000000010001000000000000000000000001000000000000000000000000000000000000000000000001000000010000000000000000000000000000000000000001000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000010000000000000000000000000000000000010001000000000000000000000000000000000001000000000000000000000001000000000000000000010001000000000000000000000000000000000000000100000001000000000000000000000000000100000000000100000000000000010000000000000000000000000000000000000000000000000001000000000001000000000000000000000001000000000000000000000000000000000000000100010001000000000000000000000000000000000000000000000000000000010000000000000001000100000000000000000001000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000001000000000000000000000001000000000000000000010001000000010000000000000000000000000001000000000001000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000010001000000000000000000000001000000000001000100000000000000000000000000000000000100000000000000000000000000000000000000010000000000000000000000000001000000010000000000000000000000000000000000000001000100000000000000000000000000000000000000000001000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000010000000000010000000000000000000000000001000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100010000000000010000000000000000000000000001000000000001000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000100000000000100000000000000000001000000000000000000010001000000010000000000000000000000000000000000000001000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000001000000000001000000000001000000000000000000000000000100010000000000000001000000000000000000010001000000000000000000000001000000000000000000000001000000010000000000000000000000000000000100000001000000000000000000000000000000000000000000000000000000010000000000000000000000000000000100000000000100010000000000000000000000000000000000000001000000000000000000000000000000000001000100000001000000000000000000000000000000000000000000000000000000010000000000010000000000000000000000000000000000000000000000000001000000000000000100000001000100000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000010001000000000000000000000000000000000001000000000001000000000000000100000001000000000000000000000001000000000000000000010000000000010000000000000000000000000000000000000001000000000000000000000001000100000000000000000000000000000000000000000000000000000000000100000001000000010001000000000000000000000000000000000001000100010000000000000000000000000000000000000001000000000000000000000000000000000001000000000001000000000000000000000000000100000000000100000000000000000000000000000000000000000000000100000001000000010001000000000000000000000000000000000000000000000000000000000001000000000000000000010000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000010001000000000000000100000001000000000000000000000001000000000000000000000001000100000000000000000000000000000000000100010000000000000000000000000000000000000001000000000000000000010000000000000000000000000000000000000001000000010000000000000001000000000000000000000001000000000000000000000000000000000000000100000001000100000000000000000000000000000000000000000000000000010000000000000000000000000001000000000001000000000000000000000001000100000000000100000000000000000000000000000000000000000000001100000001000000000000000000000000000000000000000000000001000000010000000000000000000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000000001000000000000000100000000000000000000000000010000000000000000000000000001000000010001000000000000000000000000000000000000000100000000000000000000000000000000000000010000000000000000000000000000000000000000000100000001000000010000000000000000000100000000000000000001000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000100000001000000000000000000000000000000000000000100000000000000010000000000000000000000000000000000000000000000000000000000010001000000000000000000000000000000000000000000000000000000000000000100000001000000000000000000000001000000000000000000000001000000010000000000000001000000000001000000000001000000000000000000000001000100000000000000000000000000000000001000010000000000000000000000000001000000000001000000000000000000000000000000000001000100010000000000000000000000000000000000000001000000010000000000000001000000000000000000000001000000000000000000000000000100000000000000000001000000000000000000010000000000000000000000000001000000010000000000000000000000000000000000000000000000000000000000000000000000000000000100010001000000000000000000000000000000000001000100000000000000000000000000000000000000000000000000000000000000010000000000010000000000000000000000000001000000000001000000000001000000000000000000000001000000000000000000000001000000000000000100010000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000001000000000000000000000000000100000001000100010000000000000000000000000000000000010001000000010000000000000000000000000000000000000001000000000000000000000001000000000000000000000001000000000000000000010000000000000000000100000001000000000000000000000001000000000000000100000001000100010000000000000000000000000000000000010000000000000000000000000001000000000001000000000000000000010000000000000000000100000000000100000000000000000000000000000000000000000000000000000001000000010000000000000001000000000000000000000001000000000000000000000000000000000000000000000001000000000000000000000000000000000000000100000001000000000000000000000000000100000000000000000000000000010000000000000000000000000000000000000001000000010001000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000001000000010000000000000000000100000000000000000001000000000000000000010001000000000000000000000001000000000001000000000000000000000000000000000000000100000000000000000000000000000000000000010001000000010000000000000000000000000000000000000001000000000000000000000001000000000000000000000000000000000000000000000001000000000000000100000000000000000000000000000000000000000000000000000001000100010000000000000000000000000000000000010001000000000000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000010000000000010000000000000000000000000000000000010001000000000000000000000000000000000001000000000000000000000000000000000000000000010001000000000000000000000000000000000001000100000001000000000000000000000000000100000000000100000001000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000001000100000000000000000000000000000000000100000001000000000000000000000000000000000001000000000001000000010000000000000001000100000000000000000000000000000000000000010001000000000000000000000001000000000001000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000100000000000000000000000000000000000000010000000000000000000100000001000000000001000000000000000000000000000000000001000000010000000000000000000000000000000000010001000000000000000000000000000000000000000100000001000000000000000000000000000100000000000100000001000000000000000000010000000000000000000000000001000000010000000000000000000000000000000000000001000000000000000000000001000000000000000000000000000000000000000000000001000000000001000100000001000000000000000000000000000000000000000000000000000000010000000000010000000000000000000000000001000000000000000000000001000000000000000000000000000100000000000000000000000000000000000100010001000000010000000000000000000000000001000000000001000000010000000000000000000100000000000000000000000000000000001000010001000000000000000000000001000000000001000000000000000000000000000100000001000100000000000000000001000000000000000100000001000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000010000000000000000000100000001000000000000000000000001000000000000000000000001000000010000000000000001000000000000000000010001000000000000000000000001000000000000000000000001000000000000000000000000000100000000000000000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000000000001000100010000000000000001000000000000000000010001000000000000000000000000000000000000000100000001000000000000000000000000000100000000000000000000000000010000000000000000000000000000000000000001000000000001000000000001000000000000000100000001000100000000000000000000000000000000000100010000000000000000000000000000000000000000000000000001000000010000000000000000000000000000000000000000000000000000000000010001000000000000000000000001000000000000000000000001000000000000000100000001000000000000000000000000000000000000000000010001000000010000000000000000000000000001000000000001000000000000000000000001000100000000000000000000000000000000000000010000000000000000000000000001000000000000000000000000000000000000000000000001000100010000000000000000000000000000000000000001000000000000000000000001000000000000000000000000000000010000000000000000000100000000000100000000000000000000000000010000000000000000000100000001000000010000000000000000000000000000000000000001000100000000000000000001000000000000000000010001000000000000000000000000000000000000000100000001000000000000000000000000000100000000000000000001000000010000000000010001000000000000000000000001000000000001000000000001000000000000000000000001000100000000000000000000000000000000000100010001000000000000000000000000000000000001000000000001000000010000000000000000000100000000000000000001000000010000000000000001000000000000000000000001000000000001000000000000000000000000000100000001000100000000001000000000

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def coverage_ok : PLift (coverage = coverBits upperRowsSize) := ⟨by decide +kernel⟩

private theorem coverBit (n m : Nat) :
    (coverBits n).testBit m = true ↔ ∃ i, i < n ∧ upperCofactor i = m := by
  induction n with
  | zero => simp [coverBits]
  | succ n ih =>
    simp only [coverBits, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow,
      decide_eq_true_eq, ih]
    constructor
    · rintro (⟨i,hi,h⟩ | h)
      · exact ⟨i,by omega,h⟩
      · exact ⟨n,by omega,h⟩
    · rintro ⟨i,hi,h⟩
      by_cases hn : i = n
      · exact Or.inr (hn ▸ h)
      · exact Or.inl ⟨i,by omega,h⟩

private def upperDivisorCount (m : Nat) : Nat :=
  let fs := m.factorization
  m.primeFactors.prod (fun p => fs p + 1)

private def eligible (m : Nat) : Bool :=
  decide (16 ∣ m ∨ 12 ∣ m) && decide (4*upperDivisorCount m ∣ m)

private def completenessCheck (start width : Nat) : Bool :=
  (List.range' start width).all (fun m => !eligible m || coverage.testBit m)

private theorem completeness_at {start width m : Nat}
    (checked : completenessCheck start width = true) (lo : start ≤ m)
    (hi : m < start+width) (needed : eligible m = true) : coverage.testBit m = true := by
  have in_segment : m ∈ List.range' start width :=
    List.mem_range'.mpr ⟨m-start, by omega, by simp; omega⟩
  simpa [needed] using (List.all_eq_true.mp checked m in_segment)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def ck0 : PLift (completenessCheck 1 1024 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def ck1 : PLift (completenessCheck 1025 1024 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def ck2 : PLift (completenessCheck 2049 1024 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def ck3 : PLift (completenessCheck 3073 1024 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def ck4 : PLift (completenessCheck 4097 1024 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def ck5 : PLift (completenessCheck 5121 1024 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def ck6 : PLift (completenessCheck 6145 1024 = true) := ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def ck7 : PLift (completenessCheck 7169 1024 = true) := ⟨by decide +kernel⟩

theorem low_cofactors_complete (m : Nat) (lo : 1 ≤ m) (hi : m ≤ 8192)
    (good : 4*m.divisors.card ∣ m) : m ∈ (range upperRowsSize).image upperCofactor := by
  have correct : upperDivisorCount m = m.divisors.card := (Nat.card_divisors (by omega)).symm
  have eligible_m : eligible m = true := by
    simp [eligible, ColtonH3Upper.cofactor_moduli lo good, correct, good]
  have covered : coverage.testBit m = true := by
    by_cases h4097 : m < 4097
    · by_cases h2049 : m < 2049
      · by_cases h1025 : m < 1025
        · exact completeness_at ck0.down (by omega : 1 ≤ m) (by omega : m < 1025) eligible_m
        · exact completeness_at ck1.down (by omega : 1025 ≤ m) (by omega : m < 2049) eligible_m
      · by_cases h3073 : m < 3073
        · exact completeness_at ck2.down (by omega : 2049 ≤ m) (by omega : m < 3073) eligible_m
        · exact completeness_at ck3.down (by omega : 3073 ≤ m) (by omega : m < 4097) eligible_m
    · by_cases h6145 : m < 6145
      · by_cases h5121 : m < 5121
        · exact completeness_at ck4.down (by omega : 4097 ≤ m) (by omega : m < 5121) eligible_m
        · exact completeness_at ck5.down (by omega : 5121 ≤ m) (by omega : m < 6145) eligible_m
      · by_cases h7169 : m < 7169
        · exact completeness_at ck6.down (by omega : 6145 ≤ m) (by omega : m < 7169) eligible_m
        · exact completeness_at ck7.down (by omega : 7169 ≤ m) (by omega : m < 8193) eligible_m
  rw [coverage_ok.down, coverBit] at covered
  obtain ⟨i,hi,he⟩ := covered
  exact mem_image.mpr ⟨i,mem_range.mpr hi,he⟩

end ColtonH3Data

namespace ColtonH3Data

open Finset

def triangular (n : Nat) : Nat := n*(n+1)/2
def upperCost (m : Nat) : Nat := triangular (20000000/m).primeCounting

private theorem triangular_mono : Monotone triangular := by
  intro a b hab
  exact Nat.div_le_div_right (Nat.mul_le_mul hab (Nat.succ_le_succ hab))

abbrev UpperBand := Nat × Nat × Nat

private def bandScore (band : UpperBand) : Nat :=
  (band.2.1-band.1) * triangular (rankAt band.2.2)

private def checkedBands (value : Nat → Nat) : List UpperBand → Nat → Nat → Bool
  | [], start, stop => decide (start = stop)
  | b :: rest, start, stop =>
    decide (b.1 = start ∧ start < b.2.1 ∧ b.2.1 ≤ stop ∧
      b.2.2 < primeRowsSize ∧ 20000000/value start ≤ boundary b.2.2) &&
        checkedBands value rest b.2.1 stop

private theorem sum_le_bands (steps : ∀ i, i+1 < primeRowsSize → primeStep i)
    (value : Nat → Nat) (mono : Monotone value) (pos : ∀ i, 0 < i → 0 < value i)
    (bands : List UpperBand) {start stop : Nat} (hs : 0 < start)
    (verified : checkedBands value bands start stop = true) :
    (∑ i ∈ Ico start stop, upperCost (value i)) ≤ (bands.map bandScore).sum := by
  induction bands generalizing start with
  | nil =>
    have eq : start = stop := of_decide_eq_true verified
    subst stop
    simp
  | cons b rest ih =>
    simp only [checkedBands, Bool.and_eq_true, decide_eq_true_eq] at verified
    obtain ⟨⟨anchor,forward,last,idx,bound⟩,tail⟩ := verified
    have chunk :
        (∑ i ∈ Ico start b.2.1, upperCost (value i)) ≤ bandScore b := by
      have per {i : Nat} (hi : i ∈ Ico start b.2.1) :
          upperCost (value i) ≤ triangular (rankAt b.2.2) := by
        have div : 20000000/value i ≤ 20000000/value start :=
          Nat.div_le_div_left (mono (mem_Ico.mp hi).1) (pos start hs)
        rw [(ranks_correct steps idx).1]
        exact triangular_mono (Nat.monotone_primeCounting (div.trans bound))
      calc
        _ ≤ ∑ _ ∈ Ico start b.2.1, triangular (rankAt b.2.2) := sum_le_sum (fun _ => per)
        _ = _ := by simp [bandScore, anchor, Nat.card_Ico, Nat.mul_comm]
    have remain := ih (hs.trans forward) tail
    rw [← sum_Ico_consecutive _ forward.le last]
    exact Nat.add_le_add chunk remain

def cofactor16 (i : Nat) : Nat := 16*i
def cofactor36 (i : Nat) : Nat := 36*i^2

def large16 : Finset Nat := (Ico 513 4153).image cofactor16
def large36 : Finset Nat := (Ico 16 43).image cofactor36

def allCofactors : Finset Nat := upperSet ∪ large16 ∪ large36

private theorem sum_union_nat_le {s t : Finset Nat} (f : Nat → Nat) :
    (∑ a ∈ s ∪ t, f a) ≤ (∑ a ∈ s, f a) + (∑ a ∈ t, f a) := by
  have h := sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  omega

theorem coarseBound (steps : ∀ i, i+1 < primeRowsSize → primeStep i)
    (bands16 bands36 : List UpperBand)
    (checked16 : checkedBands cofactor16 bands16 513 4153 = true)
    (checked36 : checkedBands cofactor36 bands36 16 43 = true)
    (numeric16 : (bands16.map bandScore).sum ≤ 36940649)
    (numeric36 : (bands36.map bandScore).sum ≤ 351370) :
    ∑ m ∈ allCofactors, upperCost m ≤ 1772500000 := by
  have bound16 : (∑ m ∈ large16, upperCost m) ≤ 36940649 := by
    apply (sum_image_le_of_nonneg (s := Ico 513 4153) (g := cofactor16)
      (f := upperCost) (fun _ _ => Nat.zero_le _)).trans
    refine (sum_le_bands steps cofactor16 (fun _ _ h => Nat.mul_le_mul_left 16 h) ?_
      bands16 (by decide) checked16).trans numeric16
    intro i hi
    exact Nat.mul_pos (by decide) hi
  have bound36 : (∑ m ∈ large36, upperCost m) ≤ 351370 := by
    apply (sum_image_le_of_nonneg (s := Ico 16 43) (g := cofactor36)
      (f := upperCost) (fun _ _ => Nat.zero_le _)).trans
    refine (sum_le_bands steps cofactor36
      (fun _ _ h => Nat.mul_le_mul_left 36 (Nat.pow_le_pow_left h 2)) ?_
      bands36 (by decide) checked36).trans numeric36
    intro i hi
    exact Nat.mul_pos (by decide) (Nat.pow_pos hi)
  have base : (∑ m ∈ upperSet, upperCost m) ≤ 1735192103 := upperSum steps
  calc
    _ ≤ (∑ m ∈ upperSet ∪ large16, upperCost m) + (∑ m ∈ large36, upperCost m) :=
      sum_union_nat_le _
    _ ≤ 1735192103 + 36940649 + 351370 :=
      Nat.add_le_add ((sum_union_nat_le _).trans (Nat.add_le_add base bound16)) bound36
    _ ≤ _ := by decide

end ColtonH3Data

namespace ColtonH3Data

open Finset

/-- An exact check through 8192 and the two coarse families cover all eligible
cofactors needed for the exponent-one bound. -/
theorem coarse_complete
    (small : ∀ m : Nat, 1 ≤ m → m ≤ 8192 → 4*m.divisors.card ∣ m → m ∈ upperSet)
    (m : Nat) (pos : 1 ≤ m) (bound : m ≤ 66445) (good : 4*m.divisors.card ∣ m) :
    m ∈ allCofactors := by
  by_cases covered : m ≤ 8192
  · exact mem_union_left _ (mem_union_left _ (small m pos covered good))
  rcases ColtonH3Upper.cofactor_square_or_sixteen pos good with divisible | square
  · obtain ⟨i,hi⟩ := divisible
    have lower : 513 ≤ i := by omega
    have upper : i < 4153 := by omega
    have included : m ∈ large16 := by
      change m ∈ (Ico 513 4153).image cofactor16
      exact mem_image.mpr ⟨i,mem_Ico.mpr ⟨lower,upper⟩,hi.symm⟩
    exact mem_union_left _ (mem_union_right _ included)
  · obtain ⟨r,hr⟩ := square
    have lower : 16 ≤ r := by
      by_contra! tooSmall
      have powBound := Nat.pow_le_pow_left (show r ≤ 15 by omega) 2
      have productBound : 36*r^2 ≤ 8100 := Nat.mul_le_mul_left 36 powBound
      omega
    have upper : r < 43 := by
      by_contra! tooLarge
      have powBound := Nat.pow_le_pow_left tooLarge 2
      have productBound : 66564 ≤ 36*r^2 := Nat.mul_le_mul_left 36 powBound
      omega
    have included : m ∈ large36 := by
      change m ∈ (Ico 16 43).image cofactor36
      exact mem_image.mpr ⟨r,mem_Ico.mpr ⟨lower,upper⟩,hr.symm⟩
    exact mem_union_right _ included

end ColtonH3Data

namespace ColtonH3Data

open Finset

set_option maxRecDepth 16000 in
private def bands16 : List UpperBand := [
  (513,515,618),
  (515,520,617),
  (520,522,616),
  (522,525,615),
  (525,532,614),
  (532,534,613),
  (534,535,612),
  (535,536,611),
  (536,545,610),
  (545,552,609),
  (552,558,608),
  (558,565,607),
  (565,568,606),
  (568,582,605),
  (582,584,604),
  (584,585,603),
  (585,588,602),
  (588,600,601),
  (600,606,600),
  (606,616,599),
  (616,618,598),
  (618,625,597),
  (625,630,596),
  (630,632,595),
  (632,635,594),
  (635,642,593),
  (642,644,592),
  (644,654,591),
  (654,655,590),
  (655,664,589),
  (664,666,588),
  (666,675,587),
  (675,678,586),
  (678,680,585),
  (680,685,584),
  (685,695,583),
  (695,696,582),
  (696,704,581),
  (704,712,580),
  (712,728,579),
  (728,735,578),
  (735,738,577),
  (738,744,576),
  (744,745,575),
  (745,755,574),
  (755,756,573),
  (756,760,572),
  (760,762,571),
  (762,765,570),
  (765,774,569),
  (774,776,568),
  (776,785,567),
  (785,786,566),
  (786,792,565),
  (792,808,564),
  (808,810,563),
  (810,812,562),
  (812,815,561),
  (815,822,560),
  (822,824,559),
  (824,825,558),
  (825,834,557),
  (834,835,556),
  (835,846,555),
  (846,855,554),
  (855,856,553),
  (856,865,552),
  (865,868,551),
  (868,872,550),
  (872,888,549),
  (888,894,548),
  (894,895,547),
  (895,904,546),
  (904,905,545),
  (905,906,544),
  (906,920,543),
  (920,924,542),
  (924,936,541),
  (936,942,540),
  (942,952,539),
  (952,954,538),
  (954,955,537),
  (955,965,536),
  (965,975,535),
  (975,978,534),
  (978,984,533),
  (984,985,532),
  (985,990,531),
  (990,995,530),
  (995,1000,529),
  (1000,1002,528),
  (1002,1016,527),
  (1016,1032,526),
  (1032,1035,525),
  (1035,1036,524),
  (1036,1038,523),
  (1038,1048,522),
  (1048,1055,521),
  (1055,1062,520),
  (1062,1064,519),
  (1064,1074,518),
  (1074,1086,517),
  (1086,1092,516),
  (1092,1096,515),
  (1096,1098,514),
  (1098,1112,513),
  (1112,1115,512),
  (1115,1120,511),
  (1120,1125,510),
  (1125,1128,509),
  (1128,1135,508),
  (1135,1144,507),
  (1144,1145,506),
  (1145,1146,505),
  (1146,1148,504),
  (1148,1152,503),
  (1152,1158,502),
  (1158,1160,501),
  (1160,1165,500),
  (1165,1170,499),
  (1170,1176,498),
  (1176,1182,497),
  (1182,1192,496),
  (1192,1194,495),
  (1194,1204,494),
  (1204,1205,493),
  (1205,1206,492),
  (1206,1208,491),
  (1208,1215,490),
  (1215,1224,489),
  (1224,1239,488),
  (1239,1254,487),
  (1254,1256,486),
  (1256,1259,485),
  (1259,1266,484),
  (1266,1272,483),
  (1272,1275,482),
  (1275,1277,481),
  (1277,1285,480),
  (1285,1288,479),
  (1288,1304,478),
  (1304,1305,477),
  (1305,1314,476),
  (1314,1315,475),
  (1315,1316,474),
  (1316,1336,473),
  (1336,1337,472),
  (1337,1345,471),
  (1345,1350,470),
  (1350,1355,469),
  (1355,1362,468),
  (1362,1368,467),
  (1368,1371,466),
  (1371,1374,465),
  (1374,1383,464),
  (1383,1385,463),
  (1385,1386,462),
  (1386,1394,461),
  (1394,1397,460),
  (1397,1405,459),
  (1405,1407,458),
  (1407,1415,457),
  (1415,1416,456),
  (1416,1421,455),
  (1421,1424,454),
  (1424,1427,453),
  (1427,1432,452),
  (1432,1434,451),
  (1434,1439,450),
  (1439,1446,449),
  (1446,1447,448),
  (1447,1464,447),
  (1464,1480,446),
  (1480,1483,445),
  (1483,1494,444),
  (1494,1496,443),
  (1496,1505,442),
  (1505,1527,441),
  (1527,1530,440),
  (1530,1534,439),
  (1534,1540,438),
  (1540,1542,437),
  (1542,1544,436),
  (1544,1555,435),
  (1555,1565,434),
  (1565,1575,433),
  (1575,1577,432),
  (1577,1585,431),
  (1585,1591,430),
  (1591,1595,429),
  (1595,1601,428),
  (1601,1607,427),
  (1607,1613,426),
  (1613,1624,425),
  (1624,1626,424),
  (1626,1637,423),
  (1637,1639,422),
  (1639,1652,421),
  (1652,1654,420),
  (1654,1656,419),
  (1656,1661,418),
  (1661,1665,417),
  (1665,1672,416),
  (1672,1685,415),
  (1685,1687,414),
  (1687,1697,413),
  (1697,1703,412),
  (1703,1708,411),
  (1708,1710,410),
  (1710,1720,409),
  (1720,1725,408),
  (1725,1734,407),
  (1734,1744,406),
  (1744,1746,405),
  (1746,1751,404),
  (1751,1756,403),
  (1756,1759,402),
  (1759,1764,401),
  (1764,1766,400),
  (1766,1784,399),
  (1784,1794,398),
  (1794,1799,397),
  (1799,1815,396),
  (1815,1817,395),
  (1817,1820,394),
  (1820,1831,393),
  (1831,1833,392),
  (1833,1841,391),
  (1841,1844,390),
  (1844,1852,389),
  (1852,1863,388),
  (1863,1866,387),
  (1866,1875,386),
  (1875,1877,385),
  (1877,1880,384),
  (1880,1894,383),
  (1894,1900,382),
  (1900,1912,381),
  (1912,1915,380),
  (1915,1918,379),
  (1918,1924,378),
  (1924,1927,377),
  (1927,1932,376),
  (1932,1935,375),
  (1935,1941,374),
  (1941,1945,373),
  (1945,1960,372),
  (1960,1975,371),
  (1975,1985,370),
  (1985,1988,369),
  (1988,1991,368),
  (1991,2004,367),
  (2004,2007,366),
  (2007,2020,365),
  (2020,2023,364),
  (2023,2033,363),
  (2033,2043,362),
  (2043,2046,361),
  (2046,2056,360),
  (2056,2070,359),
  (2070,2080,358),
  (2080,2087,357),
  (2087,2094,356),
  (2094,2098,355),
  (2098,2101,354),
  (2101,2105,353),
  (2105,2112,352),
  (2112,2116,351),
  (2116,2119,350),
  (2119,2134,349),
  (2134,2141,348),
  (2141,2152,347),
  (2152,2159,346),
  (2159,2163,345),
  (2163,2167,344),
  (2167,2174,343),
  (2174,2193,342),
  (2193,2201,341),
  (2201,2205,340),
  (2205,2209,339),
  (2209,2213,338),
  (2213,2229,337),
  (2229,2237,336),
  (2237,2245,335),
  (2245,2249,334),
  (2249,2261,333),
  (2261,2273,332),
  (2273,2282,331),
  (2282,2286,330),
  (2286,2294,329),
  (2294,2298,328),
  (2298,2303,327),
  (2303,2315,326),
  (2315,2324,325),
  (2324,2328,324),
  (2328,2333,323),
  (2333,2341,322),
  (2341,2355,321),
  (2355,2359,320),
  (2359,2368,319),
  (2368,2377,318),
  (2377,2381,317),
  (2381,2391,316),
  (2391,2395,315),
  (2395,2400,314),
  (2400,2404,313),
  (2404,2423,312),
  (2423,2428,311),
  (2428,2432,310),
  (2432,2437,309),
  (2437,2451,308),
  (2451,2456,307),
  (2456,2466,306),
  (2466,2471,305),
  (2471,2486,304),
  (2486,2491,303),
  (2491,2501,302),
  (2501,2511,301),
  (2511,2516,300),
  (2516,2526,299),
  (2526,2531,298),
  (2531,2536,297),
  (2536,2541,296),
  (2541,2552,295),
  (2552,2567,294),
  (2567,2573,293),
  (2573,2583,292),
  (2583,2594,291),
  (2594,2599,290),
  (2599,2605,289),
  (2605,2610,288),
  (2610,2616,287),
  (2616,2632,286),
  (2632,2643,285),
  (2643,2654,284),
  (2654,2660,283),
  (2660,2677,282),
  (2677,2683,281),
  (2683,2694,280),
  (2694,2700,279),
  (2700,2712,278),
  (2712,2718,277),
  (2718,2724,276),
  (2724,2730,275),
  (2730,2742,274),
  (2742,2766,273),
  (2766,2772,272),
  (2772,2778,271),
  (2778,2784,270),
  (2784,2791,269),
  (2791,2797,268),
  (2797,2809,267),
  (2809,2822,266),
  (2822,2835,265),
  (2835,2841,264),
  (2841,2854,263),
  (2854,2867,262),
  (2867,2874,261),
  (2874,2881,260),
  (2881,2894,259),
  (2894,2901,258),
  (2901,2914,257),
  (2914,2921,256),
  (2921,2928,255),
  (2928,2935,254),
  (2935,2942,253),
  (2942,2949,252),
  (2949,2963,251),
  (2963,2984,250),
  (2984,2991,249),
  (2991,3005,248),
  (3005,3013,247),
  (3013,3020,246),
  (3020,3027,245),
  (3027,3034,244),
  (3034,3042,243),
  (3042,3049,242),
  (3049,3064,241),
  (3064,3072,240),
  (3072,3079,239),
  (3079,3095,238),
  (3095,3102,237),
  (3102,3110,236),
  (3110,3126,235),
  (3126,3133,234),
  (3133,3141,233),
  (3141,3149,232),
  (3149,3157,231),
  (3157,3173,230),
  (3173,3189,229),
  (3189,3197,228),
  (3197,3206,227),
  (3206,3214,226),
  (3214,3222,225),
  (3222,3230,224),
  (3230,3239,223),
  (3239,3256,222),
  (3256,3264,221),
  (3264,3273,220),
  (3273,3281,219),
  (3281,3290,218),
  (3290,3299,217),
  (3299,3316,216),
  (3316,3325,215),
  (3325,3334,214),
  (3334,3343,213),
  (3343,3352,212),
  (3352,3361,211),
  (3361,3370,210),
  (3370,3379,209),
  (3379,3397,208),
  (3397,3406,207),
  (3406,3416,206),
  (3416,3425,205),
  (3425,3435,204),
  (3435,3444,203),
  (3444,3454,202),
  (3454,3463,201),
  (3463,3473,200),
  (3473,3492,199),
  (3492,3502,198),
  (3502,3512,197),
  (3512,3522,196),
  (3522,3532,195),
  (3532,3542,194),
  (3542,3552,193),
  (3552,3572,192),
  (3572,3582,191),
  (3582,3592,190),
  (3592,3603,189),
  (3603,3624,188),
  (3624,3634,187),
  (3634,3645,186),
  (3645,3655,185),
  (3655,3666,184),
  (3666,3677,183),
  (3677,3688,182),
  (3688,3699,181),
  (3699,3710,180),
  (3710,3732,179),
  (3732,3743,178),
  (3743,3754,177),
  (3754,3766,176),
  (3766,3777,175),
  (3777,3788,174),
  (3788,3800,173),
  (3800,3811,172),
  (3811,3823,171),
  (3823,3835,170),
  (3835,3847,169),
  (3847,3859,168),
  (3859,3870,167),
  (3870,3882,166),
  (3882,3895,165),
  (3895,3907,164),
  (3907,3919,163),
  (3919,3931,162),
  (3931,3944,161),
  (3944,3956,160),
  (3956,3969,159),
  (3969,3981,158),
  (3981,3994,157),
  (3994,4007,156),
  (4007,4020,155),
  (4020,4033,154),
  (4033,4046,153),
  (4046,4059,152),
  (4059,4072,151),
  (4072,4085,150),
  (4085,4099,149),
  (4099,4112,148),
  (4112,4126,147),
  (4126,4140,146),
  (4140,4153,145)
]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def valid16 : PLift (checkedBands cofactor16 bands16 513 4153 = true) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def score16 : PLift ((bands16.map bandScore).sum ≤ 36940649) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 16000 in
private def bands36 : List UpperBand := [
  (16,17,605),
  (17,18,591),
  (18,19,578),
  (19,20,561),
  (20,21,546),
  (21,22,530),
  (22,23,516),
  (23,24,496),
  (24,25,478),
  (25,26,457),
  (26,27,441),
  (27,28,421),
  (28,29,400),
  (29,30,383),
  (30,31,363),
  (31,32,345),
  (32,33,326),
  (33,34,308),
  (34,35,289),
  (35,36,273),
  (36,37,256),
  (37,38,238),
  (38,39,222),
  (39,40,205),
  (40,41,189),
  (41,42,174),
  (42,43,158)
]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def valid36 : PLift (checkedBands cofactor36 bands36 16 43 = true) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def score36 : PLift ((bands36.map bandScore).sum ≤ 351370) :=
  ⟨by decide +kernel⟩

theorem coarse_upper (steps : ∀ i, i+1 < primeRowsSize → primeStep i) :
    ∑ m ∈ allCofactors, upperCost m ≤ 1772500000 :=
  coarseBound steps bands16 bands36 valid16.down valid36.down score16.down score36.down

end ColtonH3Data

theorem OMA.solution : OMA.R_OeisA111291_colton_conjecture_R1.H3 := by
  refine ⟨ColtonH3Data.harmonic ColtonH3Data.primeSteps, ?_⟩
  exact ColtonH3Upper.excluded_bound ColtonH3Data.allCofactors
    (ColtonH3Data.coarse_complete ColtonH3Data.low_cofactors_complete)
    (ColtonH3Data.coarse_upper ColtonH3Data.primeSteps)