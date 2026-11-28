import FormalConjectures.OEIS.«111291»
import Mathlib
/-!
# Colton's conjecture conditional on explicit prime estimates

We certify the 610 middle grid inequalities from the two Dusart bounds.
For each multiplier bin we round its multiplier and exclusion count upward,
and count products with primes using exact small ranks and dyadic log bounds.
Nineteen intervals give uniform bounds on the product counts throughout the grid.
The kernel checks the multiplier lists, small ranks, grid endpoints and interval budgets. Only the Dusart estimates remain analytically open. The first
grid and harmonic-tail hypotheses already have merged sibling proofs by Genbox.

The generator argument is due to Joshua Zelinsky, J. Integer Sequences 5,
Article 02.2.8. The finite generator family and use of Dusart follow Leandre
Jack, doi:10.5281/zenodo.23874061. The reduction after the middle certificate
adapts the merged R1 by marcusbuffett, including its seed certificate and
its prime-interval argument based on Genbox's asymptotic proof.
The packed primality mask uses Genbox’s segmented sieve from the merged H1 proof.
Credit: @MrSeizy.
-/
namespace ColtonSieve

open Finset

/-- The first entries of a periodic mask have no gaps in units of its stride. -/
private def pulses (step len : Nat) : Nat :=
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
private def phase (lo p : Nat) : Nat := p * ((lo+p-1)/p) - lo

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
private def progressionMask (width lo len p : Nat) : Nat :=
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
private def primeMask (lo len : Nat) : Nat := liveMask 1 lo len

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

end ColtonSieve


namespace ColtonMiddle
open Nat Real Finset

private def upper (z : ℕ) := 1000*z / (693*z.log2-1100)
private def lower (z : ℕ) := 1000*z / (694*(z.log2+1)-1000)

private theorem log_bounds (z : ℕ) (hz : 2 ≤ z) :
    693 * (z.log2 : ℝ) ≤ 1000 * Real.log z ∧
    1000 * Real.log z ≤ 694 * ((z.log2 : ℝ)+1) := by
  have h1 : (2:ℝ)^z.log2 ≤ z := by exact_mod_cast Nat.log2_self_le (by omega : z ≠ 0)
  have h2 : (z:ℝ) ≤ (2:ℝ)^(z.log2+1) := by exact_mod_cast (Nat.lt_log2_self (n:=z)).le
  have ha := Real.log_le_log (by positivity) h1
  have hb := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at ha hb
  push_cast at hb
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ (z.log2:ℝ) by positivity)
        (show 0 ≤ Real.log 2 - 693/1000 by linarith [Real.log_two_gt_d9])]
  · nlinarith [mul_nonneg (show 0 ≤ (z.log2:ℝ)+1 by positivity)
        (show 0 ≤ 694/1000 - Real.log 2 by linarith [Real.log_two_lt_d9])]

private theorem upper_ok (h : ∀ x : ℝ, 60184 ≤ x →
    (⌊x⌋₊.primeCounting : ℝ) ≤ x/(Real.log x-11/10)) {z : ℕ} (hz : 60184 ≤ z) :
    z.primeCounting ≤ upper z := by
  have hbits : 15 ≤ z.log2 := Nat.le_log2 (by omega) |>.2 (by omega)
  have hD : 1100 < 693*z.log2 := by omega
  have ha := (log_bounds z (by omega)).1
  have hd : 0 < Real.log z - 11/10 := by
    have hz' : 15 ≤ (z.log2 : ℝ) := by exact_mod_cast hbits
    linarith
  have hu := h z (by exact_mod_cast hz)
  rw [Nat.floor_natCast, le_div_iff₀ hd] at hu
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 693*z.log2-1100)).2
  have hcast : ((693*z.log2-1100 : ℕ):ℝ) = 693*(z.log2:ℝ)-1100 := by
    rw [Nat.cast_sub hD.le]; push_cast; ring
  exact_mod_cast (show (z.primeCounting : ℝ) * ((693*z.log2-1100 : ℕ):ℝ) ≤ 1000*z by
    rw [hcast]
    nlinarith [mul_nonneg (Nat.cast_nonneg z.primeCounting)
      (sub_nonneg.mpr ha)])

set_option maxRecDepth 4000 in
private theorem lower_ok (h : ∀ x : ℝ, 5393 ≤ x →
    x/(Real.log x-1) ≤ (⌊x⌋₊.primeCounting : ℝ)) {z : ℕ} (hz : 5393 ≤ z) :
    lower z ≤ z.primeCounting := by
  have hbits : 12 ≤ z.log2 := Nat.le_log2 (by omega) |>.2 (by omega)
  have hD : 1000 < 694*(z.log2+1) := by omega
  obtain ⟨ha,hb⟩ := log_bounds z (by omega)
  have hd : 0 < Real.log z - 1 := by
    have hz' : 12 ≤ (z.log2 : ℝ) := by exact_mod_cast hbits
    linarith
  have hl := h z (by exact_mod_cast hz)
  rw [Nat.floor_natCast, div_le_iff₀ hd] at hl
  have hcast : ((694*(z.log2+1)-1000 : ℕ):ℝ) = 694*((z.log2:ℝ)+1)-1000 := by
    rw [Nat.cast_sub hD.le]; push_cast; ring
  apply Nat.div_le_of_le_mul
  exact_mod_cast (show (1000:ℝ)*z ≤ ((694*(z.log2+1)-1000 : ℕ):ℝ) * z.primeCounting by
    rw [hcast]
    linarith only [hl, mul_nonneg (Nat.cast_nonneg z.primeCounting) (sub_nonneg.mpr hb)])

private def rankPacked : ℕ := 0x2c6b1ac6b1ac6b1ac5b16c5b16c5b16c4b12c4b12c4b12c4b12c4b12c4b12c4b12c4b12c4b12c4b12c4b12c4b12c4b12c4b12c4b12c3b0ec3b0ec2b0ac2b0ac2b0ac2b0ac2b0ac2b0ac2b0ac1b06c1b06c1b06c1b06c1b06c0b02c0b02c0b02c0b02c0b02c0b02c0b02bfafebfafebfafebeafabeafabeafabdaf6bdaf6bdaf6bdaf6bdaf6bdaf6bdaf6bdaf6bcaf2bbaeebbaeebbaeebaaeabaaeabaaeabaaeabaaeabaaeab9ae6b9ae6b9ae6b9ae6b9ae6b9ae6b9ae6b9ae6b9ae6b9ae6b9ae6b9ae6b8ae2b8ae2b7adeb6adab6adab5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b4ad2b4ad2b4ad2b4ad2b4ad2b4ad2b3aceb3aceb3aceb3aceb2acab2acab2acab2acab2acab1ac6b1ac6b1ac6b1ac6b0ac2b0ac2afabeafabeafabeafabeafabeafabeafabeaeabaaeabaaeabaadab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6adab6acab2acab2acab2abaaeabaaeabaaeaaaaaaaaaaaaaaaa9aa6a8aa2a8aa2a8aa2a8aa2a8aa2a8aa2a7a9ea7a9ea7a9ea6a9aa6a9aa5a96a5a96a5a96a5a96a5a96a5a96a5a96a5a96a5a96a4a92a4a92a4a92a4a92a3a8ea3a8ea3a8ea3a8ea3a8ea3a8ea2a8aa2a8aa2a8aa2a8aa2a8aa2a8aa2a8aa2a8aa1a86a0a82a0a82a0a82a0a82a0a829fa7e9ea7a9ea7a9ea7a9da769da769ca729ca729ca729ba6e9ba6e9ba6e9aa6a9aa6a9aa6a9aa6a9aa6a9aa6a9aa6a99a6699a6698a6297a5e97a5e97a5e97a5e97a5e96a5a96a5a96a5a95a5695a5695a5695a5694a5294a5294a5293a4e93a4e92a4a91a4691a4691a4691a4691a4691a4690a4290a4290a4290a4290a428fa3e8fa3e8fa3e8ea3a8ea3a8ea3a8ea3a8ea3a8ea3a8ea3a8da368da368da368da368da368da368ca328ca328ca328ba2e8ba2e8ba2e8ba2e8ba2e8aa2a8aa2a8aa2a8aa2a8aa2a8aa2a8aa2a8aa2a8aa2a8aa2a8aa2a8aa2a8aa2a8aa2a8aa2a89a2689a2689a2689a2689a2689a2689a2688a2288a2287a1e87a1e87a1e87a1e87a1e87a1e86a1a85a1685a1685a1684a1284a1283a0e82a0a82a0a81a0681a0681a0681a0681a0681a0681a0681a0681a0681a0681a0681a0680a0280a0280a0280a027f9fe7f9fe7f9fe7f9fe7f9fe7f9fe7f9fe7f9fe7f9fe7e9fa7e9fa7d9f67d9f67d9f67c9f27b9ee7b9ee7b9ee7b9ee7b9ee7b9ee7b9ee7b9ee7b9ee7a9ea7a9ea7a9ea7a9ea7a9ea7a9ea799e6799e6799e6799e6799e6799e6789e2789e2789e2779de779de779de779de779de769da769da769da759d6759d6759d6749d2739ce739ce739ce729ca729ca719c6709c2709c2709c2709c2709c2709c2709c2709c26f9be6f9be6f9be6f9be6f9be6f9be6f9be6f9be6f9be6e9ba6e9ba6e9ba6d9b66d9b66d9b66c9b26c9b26c9b26c9b26b9ae6b9ae6b9ae6b9ae6b9ae6b9ae6b9ae6b9ae6a9aa6a9aa6a9aa699a6699a6699a6699a6699a6699a6689a26799e6799e6799e6799e6799e6799e6799e6799e6799e6799e6799e6799e6699a6699a6599664992649926398e6398e6398e6298a6298a6298a6298a6298a6298a6298a6198661986619866198661986609825f97e5f97e5f97e5f97e5f97e5f97e5f97e5f97e5f97e5e97a5e97a5e97a5d9765d9765d9765c9725c9725b96e5b96e5b96e5a96a5a96a5a96a5a96a5a96a5a96a5a96a5a96a5a96a599665896258962589625896258962589625795e5795e5795e5795e5795e5795e5695a5695a5695a55956559565595655956559565595655956559565595654952549525495254952549525394e5394e5394e5294a5294a5294a5294a5194651946519465194651946509424f93e4f93e4f93e4f93e4f93e4e93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4e93a4d9364d9364d9364d9364c9324c9324c9324b92e4b92e4b92e4b92e4b92e4a92a4992649926499264992649926489224791e4791e4791e4691a4691a4691a4691a4691a4591644912449124491244912449124390e4290a4290a4290a4290a4290a419064090240902409023f8fe3f8fe3f8fe3f8fe3f8fe3e8fa3e8fa3e8fa3e8fa3e8fa3e8fa3e8fa3e8fa3e8fa3e8fa3e8fa3e8fa3d8f63d8f63d8f63d8f63d8f63d8f63d8f63d8f63d8f63c8f23b8ee3b8ee3a8ea3a8ea3a8ea3a8ea3a8ea3a8ea3a8ea398e6398e6398e6388e2388e2378de368da368da368da368da368da368da368da368da358d6358d6358d6358d6358d6358d6348d2348d2348d2338ce328ca328ca328ca328ca328ca328ca318c6318c6318c6308c2308c2308c2308c2308c2308c2308c2308c22f8be2f8be2f8be2e8ba2d8b62d8b62d8b62d8b62d8b62d8b62d8b62d8b62d8b62d8b62d8b62c8b22c8b22c8b22b8ae2a8aa2a8aa2a8aa298a6298a6298a6288a2288a22789e2689a2689a2689a2689a2689a2689a2589625896258962589625896258962589625896258962589625896248922489224892248922489224892248922489224892248922388e2388e2288a2288a2288a2288a2288a2288a218862088220882208821f87e1f87e1e87a1d8761d8761d8761c8721c8721b86e1b86e1b86e1b86e1b86e1b86e1b86e1b86e1b86e1a86a1a86a1a86a1a86a1986619866188621886218862188621886218862188621785e1785e1785e1785e1785e1685a1585615856148521485214852148521485214852148521384e1384e1384e1384e1384e1284a1184611846118461184611846118461184611846118461084210842108420f83e0f83e0e83a0e83a0e83a0e83a0e83a0e83a0e83a0d8360d8360d8360d8360d8360c8320b82e0b82e0b82e0a82a0a82a0a82a0a82a0a82a0a82a0a82a0a82a0a82a0a82a0a82a0982609826098260882208822088220781e0781e0781e0781e0681a0681a0681a0681a0681a0581605816058160581604812048120380e0380e0380e0280a0280a0280a0280a0280a0280a0280a018060180600801ff7fdff7fdff7fdff7fdff7fdff7fdfe7f9fe7f9fe7f9fe7f9fe7f9fe7f9fe7f9fe7f9fd7f5fd7f5fd7f5fc7f1fc7f1fc7f1fb7edfb7edfb7edfb7edfa7e9fa7e9fa7e9f97e5f97e5f87e1f87e1f87e1f77ddf77ddf77ddf77ddf77ddf77ddf77ddf67d9f67d9f67d9f67d9f67d9f57d5f47d1f47d1f47d1f47d1f47d1f37cdf37cdf37cdf37cdf37cdf37cdf27c9f17c5f17c5f17c5f17c5f17c5f07c1f07c1f07c1ef7bdee7b9ee7b9ee7b9ed7b5ed7b5ec7b1eb7adeb7adeb7adeb7adeb7adea7a9ea7a9ea7a9e97a5e97a5e97a5e97a5e97a5e97a5e87a1e87a1e87a1e87a1e779de779de779de779de779de779de779de779de779de779de779de6799e5795e5795e4791e378de378de2789e2789e2789e2789e1785e1785e1785e1785e1785e1785e1785e1785e0781e0781e0781e0781e0781e0781e0781e0781e0781e0781df77ddf77ddf77dde779de779de779de779de779de779de779de779dd775dc771dc771dc771dc771dc771dc771dc771dc771db76dda769da769da769da769da769d9765d8761d8761d8761d8761d8761d8761d775dd775dd6759d6759d6759d6759d6759d6759d5755d4751d4751d4751d374dd374dd2749d2749d2749d1745d1745d1745d0741d0741d0741cf73dce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739cd735cd735cd735cd735cd735cd735cc731cb72dcb72dca729c9725c9725c9725c9725c9725c9725c9725c9725c9725c9725c9725c8721c8721c8721c8721c771dc771dc6719c6719c6719c6719c5715c5715c5715c4711c4711c4711c4711c4711c4711c370dc370dc2709c2709c2709c1705c1705c1705c1705c1705c1705c0701bf6fdbf6fdbe6f9be6f9be6f9be6f9be6f9be6f9be6f9be6f9be6f9be6f9be6f9be6f9be6f9bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bc6f1bb6edbb6edbb6edbb6edbb6edba6e9ba6e9ba6e9ba6e9ba6e9ba6e9ba6e9ba6e9ba6e9ba6e9b96e5b96e5b96e5b86e1b86e1b76ddb76ddb76ddb76ddb76ddb76ddb66d9b66d9b66d9b56d5b56d5b56d5b56d5b56d5b56d5b46d1b46d1b46d1b46d1b36cdb36cdb26c9b26c9b26c9b26c9b26c9b26c9b26c9b16c5b16c5b06c1b06c1b06c1b06c1af6bdaf6bdaf6bdaf6bdaf6bdae6b9ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ac6b1ab6adab6adab6adaa6a9aa6a9aa6a9a96a5a96a5a86a1a86a1a86a1a86a1a86a1a86a1a86a1a769da769da769da769da769da769da6699a6699a6699a6699a6699a5695a5695a5695a5695a4691a4691a4691a368da368da368da2689a2689a2689a2689a2689a1685a1685a1685a1685a0681a0681a0681a0681a0681a0681a0681a0681a06819f67d9f67d9e6799e6799e6799d6759d6759d6759d6759c6719c6719c6719b66d9b66d9a6699a6699a6699a6699a6699a6699a6699966599665996659966599665996659966599665986619765d9765d966599665996659956559465194651946519465194651946519364d9364d9364d9364d9364d926499264992649926499264992649926499164591645906419064190641906418f63d8f63d8f63d8f63d8f63d8e6398d6358d6358d6358d6358d6358c6318c6318c6318b62d8a6298a629896258962589625896258862188621886218761d8761d8661985615856158461184611846118360d8360d8360d826098260982609826098160581605806017f5fd7f5fd7f5fd7f5fd7f5fd7e5f97e5f97e5f97e5f97e5f97e5f97e5f97d5f57d5f57d5f57d5f57d5f57d5f57c5f17c5f17b5ed7b5ed7b5ed7b5ed7a5e97a5e97a5e97a5e97a5e97a5e97a5e97a5e9795e5785e1785e1785e1785e1785e1785e1775dd775dd775dd775dd775dd775dd775dd775dd775dd775dd775dd765d9765d9765d9755d5745d1745d1745d1735cd735cd725c9725c9725c9725c9715c5715c5715c5715c5715c5705c1705c1705c1705c1705c1705c1705c1705c1705c16f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6f5bd6e5b96e5b96d5b56d5b56d5b56c5b16c5b16c5b16c5b16b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6a5a96a5a96a5a9695a5695a5685a1685a1685a1685a1685a1685a1685a16759d6759d6759d6659966599665996559565595655956559565595655956459164591645916358d6358d6258962589625896158560581605815f57d5f57d5f57d5e5795e5795e5795e5795e5795e5795e5795d5755d5755d5755c5715c5715b56d5b56d5b56d5a56959565595655956558561585615856158561585615856158561585615856158561585615755d56559565595655956559565595655955555555555455154551545515354d5354d5354d525495254952549525495154551545505414f53d4f53d4f53d4f53d4f53d4f53d4f53d4f53d4e5394e5394e5394e5394d5354d5354c5314b52d4b52d4b52d4b52d4b52d4b52d4b52d4b52d4a5294a5294a5294a52949525495254952548521485214751d4751d4751d4751d4751d4751d4751d4751d4751d4751d4751d4751d4651946519465194651946519465194651946519465194551545515455154551544511445114451144511445114350d4250942509415054150541505405013f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3f4fd3e4f93d4f53d4f53d4f53d4f53d4f53d4f53c4f13c4f13c4f13c4f13c4f13b4ed3a4e93a4e9394e5384e1384e1384e1384e1384e1384e1374dd374dd374dd364d9364d9364d9364d9364d9354d5354d5354d5354d5354d5354d5354d5344d1344d1344d1344d1344d1334cd324c9324c9324c9324c9324c9314c5314c5314c5304c1304c1304c1304c12f4bd2f4bd2e4b92d4b52d4b52c4b12c4b12c4b12b4ad2b4ad2b4ad2b4ad2a4a92a4a92a4a9294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5284a12749d2749d2749d2749d2749d2749d2749d2749d264992549525495254952549525495254952549525495254952449124491244912348d2348d2348d2248922489224892248922489224892148521485214852148521485204811f47d1f47d1e4791d4751d4751c4711c4711c4711b46d1b46d1b46d1b46d1b46d1b46d1b46d1a4691a4691a4691a4691a4691a4691a4691a469194651946519465194651846118461184611846118461184611745d1745d1745d1745d1745d1645916459164591645916459164591545514451144511344d1344d1344d1244912449124491244912449124491244912449124491144511445114451044110441104410f43d0f43d0f43d0e4390e4390e4390e4390d4350d4350d4350d4350d4350c4310b42d0b42d0b42d0b42d0b42d0b42d0a4290a4290a4290a4290a4290942508421084210741d0741d0741d0741d0741d0741d0741d0741d0741d0741d0741d0741d0641905415054150441104411044110340d0340d0340d0340d0340d0340d0340d0340d0340d0340d024090240902409024090240901405014050140500400ff3fcff3fcff3fcfe3f8fe3f8fd3f4fc3f0fc3f0fc3f0fb3ecfb3ecfa3e8fa3e8fa3e8fa3e8fa3e8fa3e8fa3e8f93e4f93e4f83e0f83e0f83e0f83e0f73dcf73dcf63d8f63d8f63d8f63d8f53d4f53d4f53d4f43d0f43d0f33ccf33ccf33ccf23c8f23c8f23c8f23c8f23c8f23c8f13c4f13c4f13c4f13c4f03c0f03c0f03c0f03c0f03c0f03c0ef3bcef3bcef3bcef3bcef3bcef3bcee3b8ee3b8ee3b8ed3b4ed3b4ec3b0eb3aceb3acea3a8e93a4e93a4e93a4e93a4e93a4e83a0e83a0e83a0e83a0e83a0e83a0e739ce739ce739ce6398e5394e5394e4390e4390e4390e4390e338ce338ce338ce2388e2388e1384e0380e0380df37cdf37cdf37cdf37cdf37cdf37cdf37cde378de378de378de378de378dd374dd374dd374dd374dd374dd374dd374dd374dd374dc370dc370dc370dc370db36cdb36cdb36cda368da368da368d9364d9364d9364d9364d9364d9364d9364d9364d9364d9364d9364d9364d9364d9364d9364d9364d9364d8360d8360d8360d735cd6358d6358d6358d6358d6358d6358d5354d5354d4350d334cd334cd2348d2348d2348d1344d0340d0340d0340cf33ccf33cce338cd334cd334cd334cd334cd334cd334cd334cd334cd334cc330cc330cc330cc330cc330cb32ccb32ccb32ccb32ccb32ccb32cca328ca328ca328c9324c8320c8320c8320c731cc731cc731cc6318c6318c5314c5314c5314c5314c5314c5314c4310c4310c4310c4310c330cc330cc330cc2308c2308c2308c1304c1304c1304c1304c1304c0300c0300c0300c0300bf2fcbf2fcbf2fcbf2fcbf2fcbe2f8bd2f4bd2f4bd2f4bd2f4bd2f4bd2f4bd2f4bd2f4bd2f4bd2f4bd2f4bc2f0bc2f0bc2f0bb2ecbb2ecbb2ecba2e8ba2e8ba2e8ba2e8b92e4b92e4b92e4b82e0b82e0b82e0b72dcb72dcb62d8b52d4b52d4b42d0b42d0b42d0b42d0b42d0b42d0b42d0b42d0b42d0b32ccb32ccb32ccb22c8b12c4b12c4b12c4b12c4b12c4b02c0af2bcaf2bcaf2bcaf2bcaf2bcae2b8ae2b8ae2b8ad2b4ac2b0ac2b0ac2b0ac2b0ac2b0ab2acaa2a8aa2a8aa2a8a92a4a92a4a82a0a82a0a82a0a82a0a82a0a82a0a729ca729ca729ca6298a6298a6298a6298a5294a5294a5294a4290a4290a4290a328ca328ca2288a2288a2288a2288a2288a2288a2288a1284a1284a1284a0280a0280a02809f27c9f27c9e2789e2789e2789e2789d2749d2749d2749d2749d2749c2709c2709c2709c2709b26c9b26c9a2689a2689a2689a2689a2689a2689a2689a2689a2689a2689926499264982609725c9725c962589625896258962589625896258962589525495254942509324c9324c922489224892248922489224892248922489124491244912449124491244902408f23c8f23c8e2388d2348d2348d2348d2348d2348c2308b22c8b22c8b22c8b22c8b22c8b22c8a2288a2288a2288a2288a2288922489224892248922489224892248922488220882208721c8721c8721c8721c8621886218852148521485214842108421084210842108320c8320c822088220882208812048120481204802008020080200802007f1fc7f1fc7f1fc7f1fc7f1fc7e1f87e1f87e1f87e1f87d1f47d1f47d1f47d1f47d1f47c1f07c1f07c1f07c1f07b1ec7b1ec7b1ec7a1e87a1e8791e4791e4791e4791e4791e4791e4781e0771dc771dc771dc761d8761d8761d8751d4751d4741d0731cc731cc731cc731cc731cc721c8721c8721c8721c8721c8721c8711c4701c0701c06f1bc6f1bc6f1bc6e1b86e1b86e1b86d1b46c1b06c1b06c1b06b1ac6b1ac6b1ac6a1a86a1a86a1a86a1a86a1a8691a4691a4691a4681a06719c6719c6719c66198661986619865194651946519465194651946419064190641906318c6318c6318c6318c6318c6318c6318c6318c6318c621886118461184611846118461184611846018060180601805f17c5f17c5e1785e1785e1785e1785d1745d1745c1705c1705c1705c1705b16c5b16c5b16c5b16c5b16c5b16c5a1685a1685916458160581605715c5715c5715c5715c56158561585615855154551545415054150541505314c52148521485214852148521485114450140501405014050140501404f13c4f13c4f13c4f13c4e1384e1384d1344d1344d1344d1344c1304c1304c1304b12c4b12c4a1284a1284a128491244912449124481204812048120481204711c4711c4711c46118461184511444110441104411044110441104310c4310c4310c421084210842108421084210842108421084110441104401003f0fc3f0fc3e0f83e0f83e0f83e0f83e0f83e0f83e0f83d0f43d0f43d0f43d0f43d0f43c0f03b0ec3b0ec3a0e83a0e83a0e8390e4380e0380e0380e0370dc370dc370dc360d8360d8360d8350d4350d4350d4350d4350d4340d0330cc330cc330cc320c8320c8310c4300c0300c02f0bc2f0bc2f0bc2f0bc2f0bc2f0bc2e0b82e0b82e0b82e0b82e0b82e0b82d0b42c0b02c0b02b0ac2a0a82a0a82a0a82a0a82a0a8290a4280a0280a0280a02709c2709c2709c26098260982509425094250942409024090240902308c2208822088220882208822088210842008020080200801f07c1f07c1e0781e0781e0781e0781e0781e0781e0781d0741d0741c0701b06c1b06c1a0681906419064180601806018060180601705c1705c1705c1605816058150541505415054140501304c1304c120481204812048110441004010040100400f03c0f03c0f03c0e0380e0380d0340c0300c0300b02c0b02c0b02c0a02809024090240902408020080200701c06018060180501404010040100300c020080100000
private def rank (i : ℕ) := (rankPacked >>> (10*i)) % 1024

private def pointPacked : ℕ := 0x205aa76cbbb77e428d5d65edecb8ca02559782d120d0ea1d4facfcf0d67262a31347f5be61b4962b96cdfa2adfe25a8df5ba0c0967a09fb6d1519466564c8e862a2537cd19980e9dba8a895de19fb8bef96e5dc0798ba595b8c9a85f95cb66f9fb37550d46eec1a14be8e2dbed650f41e5b1ab13bea9bece514d0d83b069d52cb19e019d04957075190751e34677cbd245ce57ae08ad1069ec04d0b42713fcf392903498eddbfe3f3da5f7a570f6cb1d87fc43c318a531e50eae6caa205f394b05b720acdf952909156368848729b14d4cf2735e0533e7992c5c30ca8e0ad2938316753cf7528c0cb6c873fe2f05e884e3e0b78133fa1ba2cc1dab9e148aea9940117c2a99c03237c0a63f0702693288c40260d2c9e3c4b81c312698126a937c969c60d81a224bbfea5191c8f5a8413e5222f6db87f97488722cffe6821478e18f38c81df0b4ea3c1fad090072e07b9d03e8c691e264be15c2475a82e5cb8c1cb262b8f4e06ffcd26de121b50654681d86a9765c1fac19ff767a3d2c657489ab14318bec3eb499c6091090cd46178d85544cc85be9d65bb50166afc165e1c577c09b4f27155672c1fcb45344df0dffa144f3ca5c17c4f41b47a5d41354b56287244b700886be412664084c44447cd78a874911834922d7c04457bfc02ac10ab41800a70410cb4aefd10fdda2b40bc83dea48fd0ed0f19ec56b2743aee8790c4f0e5fa42fcc2438179375d800dae55eaca8c3563a6b37a60d0592ce1ddc32d11130d870c64f1760f54305e37a74210bcc0d92f0e82e0992a154c0b3a87aa78942bd1ad868570ab004dc208c29b525b27290a2c2ea866e027b2a9976c009aeb2bac92c25c8f7eba6f093742b65aac23f6dee09a108c59404d468223b3b6404c08595fa8012c2094f86a2a107f2620d67ec1f030e40cdc07905ae419381d8481ea87f07330cf485101c18648207506da3dfa403c1abdd2a4e1c0685b67fa1381973f3e5946063541bb1df41839fa445bf05e8ad6e54e0170f21ae8ff059fc9c6ac7c15f2af8430c055a693f760c14e3f2235c50518608580ac13e2407960504d9865c0b0412ecf99924c049db38302bc12038456ad10464c29e81a011254ee7708042e901f791c1051ce874f503fafa2d7d800f887f21e9d03c9e091a3300ec8e300257039b24a2608c0e128279aac036ea93068180d64ebaa2c2034452746eac0cbfb22a45c031c05fdd2940c226ecbcba02f5aaa218b40b8cbf595a302d1286d35380afe465901b02ae689296440a76aad1e68028d555ee71009f59814b17026dda2a82b4097abd86acf024fe34c8e180905ce6f6f402335e0eb100089681c8f13021838a1668c082c9211f4201fe6210dde407c7bd229a201e5ca3a64080767c40316001ce61c2504c070c6ac458a01b81a0a6d0806b5785aa3401a2e528d6a80662b679e81018eb5df4b580613f173e16017b7f92e5d005c8f817cbd016936443e3405819b93ae10157ce87ec04053daf571c301473d7f648c04fd08f762f013778d2311c04bf80150aa012876a7793c0484ee42a0f011a2d9fdc54044d2eecb98010c94cf976404181f4316a00ffa3b8f2cc03e59e22ebc00f35246f4d403b58c022be00e798c855a40387cadbd7a00dc6feab17c035c3e1d3e000d1d0b5f6280332ca9424900c7b48808ec030b565dcb700be1510a20402e5c8d6c3300b4ec4d5b5402c20a8b89e00ac3485efb002a00529e5d00a3e848a874027fa372f55009c0266f7280260d12dea000947df2391402437b1b682008d5638a2c402278ee9817008686c25188020cfb2844700800b4e811801f3af3ed890079dfd0e3a801db9b612100074006f1ac801c4b085df3006e697e4f6c01aee05d4ef00691780e78c019a1d4836700640724583801865a4f64d005f353f125c01738b1b98e005a9ece89340161a3edcc8005640f5511c01509997dee005218f9559801406175990004e244225540130f166085004a6057533401223fc52bc0046cadeeb7401144365ee50043619bfbb00106f38c6c10040226d2d1800fa47e87e1003d0b4b6fec00ee3890891003a1a48b74c00e2bdfc8ce00374d8ec4b400d7d1017010034a35e025c00cd6acc86200321a0c6ba400c384df4cb002fb004831c00ba190b5d5002d63c4553400b1216e913002b33dc875400a8986f54d00291eef725c00a078b9287002723b048500098bd394c3002540e2448c0091611b94e00237557e5e0008a5fc76820021bff232600083b4dcdd900201fa00418007d5c32038001e935d5e84007751d0453001d1a32cc34007191f1f13001bb334c434006c18ffde8001a5d8317100066e38f2e50019184862b80061ee5f29e0017e2b98d58005d36573a60016bc1546700058b884f9f0015a3a38e240054721a5cb001498b542540050606bf0200139aa3b134004c80ef3070012a8d031480048d138f250011c2a3be3c00454efbe030010e78e9a980041f8070a200101707f5fc003eca4487c000f508d97c0003bc3b82ac000e93a38d900038e27e417000ddfd3de04003624ca68b000d34ae3f00003388e66c8000c91c7cf8c00310d31367000bf6bad518002eb01dc90000b63267bf4002c703247a000ad6ae9ad8002a4c070b2000a50fb795c00284245c0a0009d1b99924002651a89410009589981c8002478f964a0008e54f8f300022b71103200087793c25400210ad679800080f219448001f733e5bb0007abb7cb70001def4a20300074d1852c8001c7e078180006f308131c001b1e8fe6b00069d4ece200019d007d3400064bb6fb580018919e5e40005fe0da69c0017628cafb0005b42250540016421584700056dc6cf2400152f84b8000052acf332000142a2ed400004eb11aa5800133170a540004ae6666c0001244aed5b000474a7854c001163558b500043db0f64800108cd80c10004096066dc000fc0b065c0003d7952b90000efe5f1a70003a8302bec000e456ad0e00037b13cf0c000d956008d00035023e930000cedd0d2b00032745aa08000c4e548b10003005f8c14000bb6879950002db5944a0000b260b3150002b81bb4a0000a9c8518500029690da3c000a199f6ca000276a3c31800099d08700000258407f3c0009267254700023b54149c0008b5930bc00021fcc734400084a24194000205986a100007e3e265c0001eca79bf40007828e15b0001d4ea75b0000725ea6120001be5224300006cdbd6e00001a8d08b3c000679d02be000194583ca8000629ee317000180dc6ff80005dde59c000016e50fa5800059586f0300015caa4714000550a4fc700014bdd505000050f14bc900013bdf98240004d0ad3f000012ca7221c000495478b600011e2a6cec00045cbe89e000110606c90000426eeec60001034084980003f3b71830000f6c282c80003c2f71120000eade9a080003949065a0000df8d5d7c000368661bb0000d4c7bbd400033e5c9e90000ca86faf800031659adf0000c0c4b3cc0002f0444d50000b77ace300002cc04b440000aea37d240002a9843fd0000a6393b48000288ad64400009e36c7480002696b9f90000969720b000024bab6ce00008f5584b400022f5a37e0000886d6b4c00021466519000081da844c0001fabee5100007b98b4c00001e253ed2000075a414600001cb162a100006ff8eb0c0001b4f718700006a93ae8c00019fe8e7a00006571005000018bde71a0000608dab54000178cb32800005be6a22c000166a340b00005778fd0c0001555b45b00005341f808000144e876d00004f3ef148000135408e600004b6d676c00012659c59000047caf8000001182ace1000044555df800010aaacc60000410a704c0000fdd152600003de820980000f19659c00003aec79cc0000e5f23f4000038159f0c0000daddbde00003561ca6c0000d051ea4000032cf4be00000c6482e60000305c88340000bcba45800002e07f7fc0000b3a238300002bd026b00000aafa589000029b3b1b40000a2bd3ee000027b1478800009ae5c60000025c7a6f00000936f086000023f59e2400008c545cb0000223a0a200000859153400002093d5e000007f21b3100001f01f9bc0000790177300001d837abc0000732ccc400001c176a0400006da00e200001abce43c00006857c5a0000197310fc00006350a6300001839224c00005e878c20000170e5424000059f97a5000015f1ebe4000055a3989000014e337f40000518331d000013e18f4800004d95b25000012ec50f8000049d8a6200001202e3d800004649b7a00001124b628000042e6adf000010513d2800003fad6b900000f87f4c800003c9bed400000ec85f58000039b048600000e12052c000036e8aa100000d6474680000344355f00000cbf40ac000031bea5000000c2202c800002f5904a00000b8c588c00002d10f5b00000afde48400002ae50b700000a764db8000028d3eaa000009f53f7c000026dc48f0000097a6938000024fcebd000009057e3400002334a7e000008963570000021826030000082c496c00001fe5059000007c7780000001e5b95e00000767823800001ce51b70000070c2c2800001b80ac6000006b53cc800001a2d6a2000006627dcc000018ea80d00000613bb84000017b726c000005c8c4c8000016929c1000005816ac00000157c2a00000053d80e40000147322c000004fcdcc800001376e0c000004bf560c00001286c6700000484c644000011a23df0000044d08e0000010c8b8800000417fb1000000ff9ae5000003e57bb000000f349e0000003b56b3c00000e790ca00000387abac00000dc68500000035c207400000d1c97a00000332ae5c00000c7ada70000030b3b8800000be0e86000002e5af5000000b4e614000002c1f24400000ac2e9a0000029fee1000000a3e2a70000027f8d7c000009bfd0c
private def point (i : ℕ) := (pointPacked >>> (46*i)) % 70368744177664

private def wordPacked : ℕ := 0x710001f00000b20007c0000381001f00000902007c0000480401f00001000807c0000480101f00001000207c00001c0041f00000500087c0000040011f00000100027c0000ad0001e0000152000780000981001e00001102007800006c0401e0000230080780000700101e0000240020780000300041e00000900087800000c0011e00003140007400006c8001d00001a0400740000500801d00001e0100740000800201d00001e0040740000700081d00000f00107400001c0021d0000344000700000588001c0000120400700000780801c00001c0100700000940201c00001e00407000007c0081c0000130010700000200021c0000030004700000c90001b00001520006c0000681001b00001602006c0000640401b00002400806c00008c0101b00001b00206c0000440041b00000700086c0000080011b00002e4000680000941001a0000180200680000880401a0000250080680000800101a00001f0020680000400041a00000900086800000c0011a00002e4000640000c8100190000140200640000600401900002500806400008801019000020002064000040004190000040008640000100011900002e4000600000a41001800001202006000007404018000021008060000098010180000240020600000400041800000c0008600000080011800003240005c0000bc1001700000f02005c0000900401700002100805c00009c0101700001f00205c0000500041700000b00085c000008001170000304000580000781001600001d0200580000840401600001c00805800009001016000024002058000054004160000070008580000040011600003740005400006810015000025020054000074040150000220080540000900101500001e0020540000400041500000a0008540000080011500003340005000006410014000026020050000060040140000220080500000a80101400001f002050000050004140000090008500000080011400003140004c0000641001300002402004c0000600401300002600804c0000940101300002300204c0000440041300000a00084c0000080011300002f2000480000081001200003d0200480000640401200002200804800007c010120000270020480000500041200000b000848000014001120000020002480000d48001100003f020044000044040110000240080440000b801011000022002044000048004110000060008440000100011100001620004000009c080100000080100400000480201000000e0040400000340081000000b001040000010002100000010004400000748000f80001702003e0000280400f80001200803e0000600100f80001700203e00002c0040f80000700083e0000080010f80001820003c0000780800f00000a01003c00003c0200f00001600403c0000540080f00000900103c0000140020f00000300043c00005c8000e80001c02003a0000240400e80001100803a0000480100e80001200203a0000380040e80000600083a0000748000e0000240200380000200400e0000130080380000500100e00000e0020380000240040e0000050008380000080010e0000182000360000940800d8000070100360000340200d80000f0040360000540080d80000c0010360000100020d8000030004360000748000d00001802003400003c0400d00000f0080340000600100d0000150020340000240040d0000080008340000080010d00000100023400006c8000c80001802003200003c0400c80001000803200005c0100c80001200203200003c0040c80000600083200000c0010c80000b2000300000381000c00001a0200300000340400c00001100803000004c0100c0000100020300000300040c0000060008300000080010c00001a04002e00005c0800b80001001002e0000340200b80001400402e0000500080b80000f00102e00000c0020b80000200042e0000741000b00001502002c0000240400b00001400802c0000540100b00001500202c0000280040b00000400082c0000080010b00001804002a00006c0800a80000a01002a0000500200a80001400402a0000480080a80000b00102a0000240020a80000300042a00006c1000a0000170200280000240400a00001100802800004c0100a0000170020280000380040a0000080008280000140010a00001a04002600003808009800016010026000040020098000110040260000540080980000f001026000014002098000030004260000701000900000c020024000058040090000110080240000580100900001700202400002c0040900000900082400000c001090000180400220000380800880001401002200003c020088000120040220000680080880000c001022000020002088000030004220000500800800000d0100200000140200800000c0040200000300080800000800102000001c0020800000100042000003008007c0001601001f00001402007c0000a00401f00002000807c0000600101f00000800207c0000100041f0000440800780001001001e00001c0200780000c00401e0000300080780000700101e0000100020780000d02001d0000480400740000500801d0000280100740000c00201d00002c0040740000300081d0000040010740000b02001c0000400400700000500801c0000200100700001100201c0000140040700000400081c0000040010700000d02001b00003404006c0000500801b00003801006c0000a00201b00002400406c0000300081b00000800106c0000d02001a00005c0400680000600801a00001c0100680000700201a0000200040680000800081a0000080010680000f020019000048040064000050080190000300100640000b002019000020004064000040008190000080010640001302001800004c0400600000500801800001c0100600000e002018000024004060000030008180000040010600000100021800002c08005c0000d01001700001c02005c0000800401700003400805c0000900101700001000205c000030004170000340800580000d0100160000200200580000c00401600003000805800008001016000018002058000020004160000440800540000f010015000024020054000070040150000380080540000a001015000018002054000010004150000300800500000f0100140000180200500000a0040140000240080500000a00101400000c0020500000200041400004408004c0000c01001300002002004c0000b00401300002c00804c0000900101300001400204c000010004130000380800480000e0100120000140200480000800401200004400804800009001012000008002048000010004120000040008480000f020011000024040044000080080110000380100440000700201100002c0040440000500081100000c0010440000602001000000c0400400000500801000001401004000007002010000014004040000040008100000080010400000802000f80000c04003e0000800800f80001001003e0000700200f80002000403e0000100080f80000400083e0000702000f00001004003c0000400800f00001001003c0000800200f00001400403c0000200080f00000800103c0000302000e80002404003a0000a00800e80000c01003a0000400200e80002000403a0000200080e8000200400380000800800e0000140100380000500200e0000200040380000200080e0000100010380000901000d80002c0200360000500400d8000100080360000600100d8000080020360000200040d8000040008360000a01000d0000280200340000300400d0000200080340000500100d0000080020340000100040d0000040008340000501000c80001c0200320000200400c80001c0080320000800100c8000080020320000401000c0000300200300000300400c00001c0080300000600100c0000040020300000300040c00002804002e0000900800b80001001002e0000600200b80001800402e0000300080b80000400102e0000801000b00003002002c0000200400b00001400802c0000700100b00000c00202c0000200040b00001c04002a0000700800a80000c01002a0000600200a80002000402a0000300080a80000800102a0000901000a0000280200280000600400a00001c0080280000500100a0000080020280000100040a000020040026000070080098000080100260000700200980002800402600004000809800008001026000090100090000200200240000500400900000c008024000070010090000080020240000200040900002004002200008008008800018010022000040020088000180040220000400080880000c0010220000301000800001402002000001004008000014008020000050010080000040020200000100040800000400042000005010007c0000402001f00001004007c0000c00801f00004001007c0000800201f00001000207c0001004001e0000500800780000c01001e0000300200780000c00401e0000200040780001404001d0000200800740000c01001d0000300200740001000401d0000300080740000400101d0000301000700000c02001c0000200400700000c00801c0000100100700000800201c0000100040700001004001b00001008006c0000c01001b00003002006c0001800401b00002000806c0000400101b0000301000680000802001a0000300400680001400801a0000400100680001000201a00001000206800018020019000060040064000040080190000400100640000c00201900001000406400010020018000030040060000080080180000500100600000c0020180000200040600001402001700006004005c0001000801700002001005c0000800201700001000405c00018020016000080040058000040040160000300080580000c00101600005008005400014010015000020020054000180040150000300080540001002001400003004005000008008014000060010050000100020140000200040500000802001300008004004c0000800801300002001004c0000400201300002000404c0001402001200006004004800008008012000030010048000100020120000200040480000400081200005008004400010010011000030020044000100040110000300080440000400101100002008004000008010010000020020040000040040100000200040400000c02000f80003004003e0000800400f80002000803e0000802000f00002004003c0000800400f00003000803c0000802000e80002004003a0000800800e80001001003a0000800200e8000200800380000c01000e0000200200380000c00400e0000100040380000c02000d8000200400360000400800d8000100100360000800200d8000100040360000802000d0000200400340000800800d0000200100340000400200d0000100040340000c02000c8000100400320000800800c8000200100320000800200c8000200800300000801000c0000100200300000800400c0000300080300000800100c00002008002e0000400800b80001001002e0000c00200b80001000402e0001001000b00001002002c0000800400b00003000802c0000400100b00001004002a0001000800a80003001002a0000400200a8000400400280000c00800a0000100100280000400200a0000200040280000c0100098000300200260000c002009800020004026000040100090000300200240000c004009000030008024000100100088000400200220000400400880002000802200004001008800020040020000080080080000100080200000800100800002002001f00004002007c0001000201f0000401000780002002001e0000400400780001000801e0000800100780003000801d0000c01000700002002001c0000400400700001000801c00004010006c0001002001b00004004006c0001000401b00004000806c0002004001a0000800800680001001001a0000400200680001004001900004008006400020008019000040100060000100100180000800100600001000201800008010005c0004002001700004002005c0001000401700004010005800020010016000040020058000100400150000400800540001001001500004002005400020040014000040080050000100100140000c00200500002000401400008008004c00010010013000040080048000100100120000400200480001000401200008004004400010008011000040010044000100200100000400200400001000401000008008003e0002001000f80004004003c0001000800f00008008003a0001001000e80004001003a0001002000e0000400400380001000400e0000400400360001000400d8000400080360001002000d0000400400340002000800c8000400800300002001000c00004008002e0001001000b80004004002c0001002000a80004002002a0001000400a8000400800280001001000a00004001002800010020009800040040026000100080098000400800240001001000900004001002400010020008800040020022000100040088000800100200001001000780004001001e0001001000740004002001d0001000400740004004001b00010004006c0008002001a000100040068000400400190001001000600004002001800010004005c000800200160001001000540004001001500010008005000040010013000100100048000400080120001001000440008002001100010002003e0004002000e0001000400380004000800d8001001000340004001000b80010008002c0004001000a8001000800280004001000a0001000400240004002000780010004001e00040010007000100080019000400100060001000800120004002000400010008000f00040020002e001001000080004004000180010010000500040040001200100200002400402000003001008000008
private def word (i : ℕ) := (wordPacked >>> (46*i)) % 70368744177664

private def row (i : ℕ) : ℕ × ℕ × ℕ := (word i % 1048576, (word i >>> 20) % 65536, word i >>> 36)

set_option maxRecDepth 10000 in
private def witnessesBlock0 : Array (List ℕ) := #[[0x600100008], [0x1000c40010000c], [0x2000c400100024], [0x2000c600100048], [0x10014800100050], [0x1000ca00100060], [0xe00100080], [0x800a2000c4001000b4]]
set_option maxRecDepth 10000 in
private def witnessesBlock1 : Array (List ℕ) := #[[0x800a1000c8001000f0], [0x800e2000c4001000fc], [0x2000ca00100120], [0x1000ce00100180], [0x80162000c40010018c], [0x1001cc001001c0], [0x800a1000ca001001e0], [0x801a2000c4001001d4]]
set_option maxRecDepth 10000 in
private def witnessesBlock2 : Array (List ℕ) := #[[0x800e10014800100230], [0x10014e00100280], [0x80222000c400100264], [0x800e1000ca001002a0], [0x80262000c4001002ac], [0x800a2000c8001002d0], [0x802e2000c40010033c], [0x3000ca00100360]]
set_option maxRecDepth 10000 in
private def witnessesBlock3 : Array (List ℕ) := #[[0x1001ce00100380], [0x801610014800100370], [0x5000c4001003cc], [0x801a10014800100410,0x80161000ca00100420], [0x803a2000c400100414], [0x2000ce00100480], [0x803e2000c40010045c], [0x1000a1000c8001004b0]]
set_option maxRecDepth 10000 in
private def witnessesBlock4 : Array (List ℕ) := #[[0x801a1000ca001004e0], [0x800e1000cc00100540], [0x804a2000c400100534], [0x802210014800100550,0x1002ce00100580], [0x800a2000ca001005a0], [0x8026100148001005f0], [0x80522000c4001005c4], [0x80562000c40010060c]]
set_option maxRecDepth 10000 in
private def witnessesBlock5 : Array (List ℕ) := #[[0x800a4000c400100654], [0x80221000ca00100660,0x10034e00100680], [0x40070800a1000c800100690], [0x805e2000c40010069c], [0x1000a2000c600100708], [0x80261000ca00100720], [0x802e10014800100730], [0x800a1000ce00100780]]
set_option maxRecDepth 10000 in
private def witnessesBlock6 : Array (List ℕ) := #[[0x806a2000c400100774], [0x300148001007d0,0x800e2000ca001007e0], [0x800a3000c800100870], [0x10044e00100880], [0x80762000c40010084c], [0x800e10014c001008c0], [0x802e1000ca001008a0], [0x807a2000c400100894]]
set_option maxRecDepth 10000 in
private def witnessesBlock7 : Array (List ℕ) := #[[0x1004ce00100980], [0x803a10014800100910], [0x80862000c40010096c], [0x10015200100a00], [0x803e100148001009b0], [0x808e2000c4001009fc], [0x800e1000ce00100a80], [0x400b0800a1000c800100a50]]
set_option maxRecDepth 10000 in
private def witnessesBlock8 : Array (List ℕ) := #[[0x80922000c400100a44], [0x803a1000ca00100ae0], [0x1005ce00100b80], [0x809e2000c400100b1c], [0x804a10014800100b90,0x803e1000ca00100ba0], [0x80a62000c400100bac], [0x400d0800a1000c800100c30,0x80162000ca00100c60], [0x805210014800100cd0]]
set_option maxRecDepth 10000 in
private def witnessesBlock9 : Array (List ℕ) := #[[0x80b22000c400100c84], [0x3000ce00100d80], [0x40070800a1000ca00100d20], [0x805610014800100d70], [0x1000e2000c600100dc8], [0x804a1000ca00100de0], [0x80c22000c400100da4], [0x1000a2000c800100e10]]
set_option maxRecDepth 10000 in
private def witnessesBlock10 : Array (List ℕ) := #[[0x10074e00100e80], [0x80ca2000c400100e34,0x80ce2000c400100e7c], [0x801a2000ca00100ea0], [0x805e10014800100eb0], [0x80521000ca00100f60,0x1007ce00100f80], [0x80d62000c400100f0c,0x80da2000c400100f54], [0x800e2000cc00100fc0], [0x40110800a1000c800100ff0]]
set_option maxRecDepth 10000 in
private def witnessesBlock11 : Array (List ℕ) := #[[0x80e22000c400100fe4], [0x800a3000ca001010e0], [0x80161000ce00101080], [0x80561000ca00101020,0x806a10014800101090], [0x800e10014e00101180], [0x40130800a1000c8001011d0], [0x805e1000ca001011a0], [0x80fe2000c4001011dc]]
set_option maxRecDepth 10000 in
private def witnessesBlock12 : Array (List ℕ) := #[[0x10094e00101280], [0x81062000c40010126c,0x807610014800101270], [0x40014600101388,0x40070800a2000c8001013b0], [0x80222000ca00101320,0x80161001cc00101340,0x801a1000ce00101380], [0x806a1000ca001013e0], [0x807a10014800101310], [0x81122000c400101344,0x81162000c40010138c], [0x400b0800a1000ca001014a0]]
set_option maxRecDepth 10000 in
private def witnessesBlock13 : Array (List ℕ) := #[[0x100a4e00101480], [0x8086100148001014f0], [0x812a2000c4001014f4], [0x80262000ca00101560], [0x100ace00101580,0x40170800a1000c800101590], [0x812e2000c40010153c], [0x800a2000ce00101680], [0x801a1001cc001016c0]]
set_option maxRecDepth 10000 in
private def witnessesBlock14 : Array (List ℕ) := #[[0x80761000ca00101620,0x808e10014800101630,0x8092100148001016d0,0x807a1000ca001016e0], [0x813a2000c400101614,0x81462000c4001016ec], [0x1000d600101800], [0x1800a1000c800101770,0x800e3000ca001017a0], [0x100bce00101780], [0x814e2000c40010177c], [0x400b0800e10014800101810,0x400d0800a1000ca00101860], [0x809e100148001018b0]]
set_option maxRecDepth 10000 in
private def witnessesBlock15 : Array (List ℕ) := #[[0x815a2000c400101854], [0x80221000ce00101980], [0x802e2000ca001019e0], [0x80861000ca00101920,0x80a6100148001019f0], [0x81662000c40010192c,0x816a2000c400101974], [0x3000d000101b00], [0x40070800a1000cc00101a40], [0x100d4e00101a80]]
set_option maxRecDepth 10000 in
private def witnessesBlock16 : Array (List ℕ) := #[[0x808e1000ca00101aa0], [0x817e2000c400101adc], [0x801610014e00101b80], [0x401d0800a1000c800101b30], [0x80921000ca00101b60,0x80b210014800101bd0], [0x81822000c400101b24,0x818a2000c400101bb4,0x818e2000c400101bfc], [0x400d0800e10014800101c70,0x80261000ce00101c80,0x400b0800e1000ca00101ce0], [0x2000a1000c400101d4c,0x800a1000d200101e00]]
set_option maxRecDepth 10000 in
private def witnessesBlock17 : Array (List ℕ) := #[[0x80221001cc00101dc0], [0x401f0800a1000c800101d10], [0x100ece00101d80,0x809e1000ca00101da0], [0x81a62000c400101dac], [0x5000ca00101e60], [0x400b0800a2000c800101ef0], [0x80c210014800101e50,0x100f4e00101e80], [0x800e2000ce00101f80,0x1000a4000c400101fa4]]
set_option maxRecDepth 10000 in
private def witnessesBlock18 : Array (List ℕ) := #[[0x40110800a1000ca00101fe0], [0x80a61000ca00101f20,0x80ca10014800101f90], [0x81be2000c400101f5c,0x81c62000c400101fec], [0x40071000a1000c8001020d0], [0x801a10014e00102080,0x80261001cc00102140], [0x803a2000ca001020a0], [0x80ce10014800102030,0x80b21000ca00102160,0x80d610014800102170,0x1010ce00102180], [0x81ca2000c400102034,0x81d22000c4001020c4,0x81de2000c40010219c,0x81e22000c4001021e4]]
set_option maxRecDepth 10000 in
private def witnessesBlock19 : Array (List ℕ) := #[[0x100162000c600102208,0x400d0800e1000ca00102220,0x40130800a1000ca001023a0], [0x802e1000ce00102280,0x40250800a1000c8001022b0,0x803e2000ca001022e0], [0x80da10014800102210,0x80e210014800102350,0x1011ce00102380], [0x81f62000c40010234c], [0x1000e1000cc001024c0,0x1000a1000ce00102580], [0x400d0800a2000c800102490,0x80163000ca00102520,0x40110800e10014800102530], [0x80c21000ca00102460,0x10124e00102480,0x80ca1000ca001025e0], [0x82022000c400102424,0x820e2000c4001024fc,0x821a2000c4001025d4]]
set_option maxRecDepth 10000 in
private def witnessesBlock20 : Array (List ℕ) := #[[0x40014800102710,0x40070800a2000ca00102760], [0x80161001ce00102680], [0x40290800a1000c800102670], [0x80ce1000ca001026a0,0x1013ce00102780,0x80fe100148001027b0], [0x821e2000c40010261c,0x822a2000c4001026f4,0x82322000c400102784,0x82362000c4001027cc], [0x40130800e10014800102990], [0x802e1001cc00102840,0x402b0800a1000c800102850,0x804a2000ca001029a0], [0x80d61000ca00102820,0x80da1000ca001028e0,0x8106100148001028f0,0x1014ce00102980]]
set_option maxRecDepth 10000 in
private def witnessesBlock21 : Array (List ℕ) := #[[0x824a2000c400102934], [0x1000a3000c800102a30], [0x802210014e00102a80,0x801a3000ca00102be0,0x1002d400102c00], [0x40170800a1000ca00102b20,0x803a1000ce00102b80], [0x80e21000ca00102a60], [0x811210014800102ad0,0x82662000c400102b2c,0x811610014800102b70,0x826e2000c400102bbc], [0x80070800a1000c800102df0], [0x40110800e1000ca00102ca0,0x400d0801610014800102cb0,0x801a1001ce00102d80]]
set_option maxRecDepth 10000 in
private def witnessesBlock22 : Array (List ℕ) := #[[0x402f0800a1000c800102c10], [0x10164e00102c80], [0x82722000c400102c04,0x827a2000c400102c94], [0x1800a1000ca00102ee0,0x800e3000cc00102f40], [0x802610014e00102f80,0x1001a2000c600102f88,0x40110800a2000c800102fd0], [0x80522000ca00102e20,0x803e1000ce00102e80], [0x80fe1000ca00102fa0], [0x812a10014800102e90,0x812e10014800102f30]]
set_option maxRecDepth 10000 in
private def witnessesBlock23 : Array (List ℕ) := #[[0x82962000c400102e8c,0x82a22000c400102f64], [0x80162000ce00103180,0x40130800e1000ca001031e0], [0x80562000ca00103060,0x40350800a1000c8001031b0], [0x10184e00103080,0x81061000ca00103120], [0x813a10014800103110], [0x82b62000c4001030cc,0x82ba2000c400103114,0x82c22000c4001031a4], [0x800a4000ca001032a0], [0x400b1000a1000c800103390]]
set_option maxRecDepth 10000 in
private def witnessesBlock24 : Array (List ℕ) := #[[0x40170800e10014800103250,0x803a1001cc001032c0], [0x10194e00103280,0x1019ce00103380], [0x8146100148001032f0,0x81121000ca00103360], [0x82ce2000c40010327c,0x82de2000c40010339c], [0x40070800a1000ce00103480], [0x40130800a2000c800103570,0x400d080161000ca001035a0], [0x805e2000ca001034e0], [0x101ace00103580]]
set_option maxRecDepth 10000 in
private def witnessesBlock25 : Array (List ℕ) := #[[0x81161000ca00103420,0x814e10014800103430], [0x82ea2000c400103474,0x82f62000c40010354c,0x82fe2000c4001035dc], [0x800e300148001036b0], [0x803e1001cc00103640,0x401d0800a1000ca00103660,0x804a1000ce00103780], [0x101b4e00103680,0x403b0800a1000c800103750], [0x815a10014800103610,0x812a1000ca001037e0,0x8166100148001037f0], [0x830a2000c4001036b4,0x831a2000c4001037d4], [0x80223000ca00103960,0x400b0800e1000cc001039c0]]
set_option maxRecDepth 10000 in
private def witnessesBlock26 : Array (List ℕ) := #[[0x802e10014e00103980], [0x101c4e00103880,0x403d0800a1000c800103930], [0x816a10014800103890,0x812e1000ca001038a0], [0x83222000c400103864,0x83322000c400103984], [0x40110801610014800103a70,0x801a2000ce00103a80,0x80221001ce00103b80], [0x401f0800a1000ca00103a20,0x806a2000ca00103ba0], [0x813a1000ca00103ae0,0x817e10014800103bb0], [0x83462000c400103aec,0x834a2000c400103b34]]
set_option maxRecDepth 10000 in
private def witnessesBlock27 : Array (List ℕ) := #[[0x400d1000a1000c800103cf0,0x400b0800a2000ca00103de0], [0x40170800e1000ca00103c60,0x80521000ce00103d80], [0x818210014800103c50,0x81461000ca00103d20,0x818a10014800103d90], [0x835e2000c400103c9c,0x83622000c400103ce4,0x836e2000c400103dbc], [0x30014e00103e80,0x1000a4000c600103f48], [0x401d0800e10014800103f70], [0x40430800a1000c800103ed0,0x101fce00103f80], [0x818e10014800103e30,0x814e1000ca00103ea0]]
set_option maxRecDepth 10000 in
private def witnessesBlock28 : Array (List ℕ) := #[[0x83762000c400103e4c,0x83822000c400103f24], [0x800a3000ce00104380], [0x80263000ca00104020,0x40130801610014800104150,0x80261001ce00104280], [0x80561000ce00104080,0x40170800a2000c8001040b0,0x804a1001cc001040c0,0x401f0800e100148001043d0], [0x1020ce00104180,0x80762000ca00104260,0x40470800a1000c800104290], [0x815a1000ca001040e0,0x81a6100148001041f0,0x81661000ca00104320,0x816a1000ca001043e0], [0x83922000c400104044,0x839a2000c4001040d4,0x839e2000c40010411c,0x83a62000c4001041ac,0x83be2000c40010435c], [0x2000d600104800]]
set_option maxRecDepth 10000 in
private def witnessesBlock29 : Array (List ℕ) := #[[0x800e10015200104600,0x1800a2000c800104650], [0x400d0800e1000cc00104440,0x40110801a10014800104510,0x4011080161000ca00104620,0x801a1002ce00104780], [0x40250800a1000ca00104560,0x805e1000ce00104680,0x80521001cc001047c0], [0x40490800a1000c800104470,0x807a2000ca001044a0], [0x10224e00104480,0x1022ce00104580,0x81be100148001045b0,0x81c6100148001046f0,0x81ca10014800104790,0x817e1000ca001047a0], [0x83ce2000c40010447c,0x83d62000c40010450c,0x83e62000c40010462c,0x83ee2000c4001046bc,0x83fa2000c400104794], [0x1000e1000ce00104980,0x800a5000c800104bf0], [0x400d0800a2000ca00104920]]
set_option maxRecDepth 10000 in
private def witnessesBlock30 : Array (List ℕ) := #[[0x803a10014e00104880,0x80561001cc00104b40], [0x404f0800a1000c800104a10,0x80862000ca00104b60], [0x81821000ca00104860,0x81d2100148001048d0,0x818a1000ca001049e0,0x10254e00104a80,0x818e1000ca00104aa0,0x81de10014800104ab0,0x81e210014800104b50,0x1025ce00104b80], [0x84122000c400104944,0x84162000c40010498c], [0x40070800a2000cc00104ec0,0x800e6000c400104fbc], [0x80222000ce00104c80,0x40130801a10014800104d30,0x4013080161000ca00104e60,0x40111000a1000c800104fb0], [0x401d0800e1000ca00104c20,0x40290800a1000ca00104ce0,0x803e10014e00104d80,0x802e3000ca00104da0,0x40170801610014800104f10,0x806a1000ce00104f80], [0x40530800a1000c800104dd0,0x808e2000ca00104fe0]]
set_option maxRecDepth 10000 in
private def witnessesBlock31 : Array (List ℕ) := #[[0x81f610014800104e70,0x10274e00104e80,0x81a61000ca00104f20], [0x843a2000c400104c14,0x84462000c400104cec,0x845a2000c400104e54,0x84662000c400104f2c], [0x100222000c600105148,0x400b0800a1000ce00105280,0x40110801a1000ca001052e0], [0x802e1001ce00105080,0x402b0800a1000ca001050a0,0x40250800e100148001050f0,0x401f0800e1000ca00105160,0x401d0800a2000c800105190,0x805e1001cc00105240], [0x80922000ca00105220,0x40590800a1000c800105370], [0x820210014800105050,0x1028ce00105180,0x820e10014800105230,0x1029ce00105380,0x81be1000ca001053a0], [0x84722000c400105004,0x84762000c40010504c,0x84822000c400105124,0x84962000c40010528c,0x84a22000c400105364], [0x1000a3000ca00105460,0x3001cc001055c0,0x2000a2000c4001057e4]]
set_option maxRecDepth 10000 in
private def witnessesBlock32 : Array (List ℕ) := #[[0x80262000ce00105580,0x8016300148001055f0,0x400b0800e2000ca001056a0], [0x401f0800a2000c800105730], [0x821a10014800105410,0x821e100148001054b0,0x81c61000ca00105520,0x81ca1000ca001055e0,0x102b4e00105680,0x822a10014800105690,0x81d21000ca00105760,0x8232100148001057d0], [0x84ae2000c40010543c,0x84b22000c400105484,0x84be2000c40010555c,0x84ca2000c400105634,0x84d22000c4001056c4,0x84d62000c40010570c], [0x800a2000d200105a00], [0x40131000a1000c800105910,0x40110800e1000cc00105940], [0x402f0800a1000ca00105820,0x40290800e100148001059b0], [0x80761000ce00105880,0x809e2000ca001058e0,0x40610800a1000c800105af0,0x807a1000ce00105b80]]
set_option maxRecDepth 10000 in
private def witnessesBlock33 : Array (List ℕ) := #[[0x823610014800105870,0x102cce00105980,0x81de1000ca001059a0,0x81e21000ca00105a60,0x102d4e00105a80,0x824a10014800105b90], [0x84ee2000c4001058bc,0x85022000c400105a24,0x85062000c400105a6c,0x850e2000c400105afc,0x851a2000c400105bd4], [0x800e3000ce00105e80,0x1000a5000c400105eec], [0x40130801a1000ca00105ca0,0x80221002ce00105d80,0x40110800a2000ca00105fa0], [0x804a10014e00105c80,0x806a1001cc00105cc0,0x40170801a10014800105d70,0x402b0800e10014800105e10,0x4017080161000ca00105ee0], [0x80a62000ca00105d60,0x40650800a1000c800105eb0], [0x81f61000ca00105e20,0x102fce00105f80,0x826610014800105ff0], [0x85262000c400105cac,0x852a2000c400105cf4,0x85422000c400105ea4,0x854a2000c400105f34]]
set_option maxRecDepth 10000 in
private def witnessesBlock34 : Array (List ℕ) := #[[0x40071000a2000c800106270], [0x400b0800e10014c00106040,0x400d0800a1000ce00106180,0x40130800e1000cc001063c0], [0x40250800e1000ca00106120,0x803a3000ca001061e0,0x40350800a1000ca00106360,0x401d08016100148001063b0], [0x40670800a1000c800106090], [0x82021000ca00106060,0x10304e00106080,0x826e10014800106130,0x10314e00106280,0x820e1000ca001062a0,0x1031ce00106380], [0x85562000c40010600c,0x85662000c40010612c,0x8272100148001061d0,0x857a2000c400106294,0x827a10014800106310,0x858a2000c4001063b4], [0x8000c400106684], [0x401308022100148001064f0,0x100262000c600106588,0x801a30014800106590,0x400d0800e2000ca00106660]]
set_option maxRecDepth 10000 in
private def witnessesBlock35 : Array (List ℕ) := #[[0x803a1001ce00106580,0x805210014e00106680,0x402f0800e100148001066d0,0x802e2000ce00106780], [0x80b22000ca00106420,0x406b0800a1000c800106450,0x80861000ce00106480,0x406d0800a1000c800106630,0x80761001cc00106740], [0x821a1000ca001064e0,0x821e1000ca001065a0,0x822a1000ca001067e0], [0x859e2000c40010651c,0x829610014800106770], [0x85ae2000c40010663c,0x85ba2000c400106714,0x85c62000c4001067ec], [0x1800e10014800106b30], [0x80261002ce00106880,0x40130800a2000ca00106ae0], [0x40250800a2000c800106810,0x803e3000ca001068a0,0x401f0801610014800106a90,0x805610014e00106b80,0x40290800e1000ca00106ba0,0x40171000a1000c800106bd0]]
set_option maxRecDepth 10000 in
private def witnessesBlock36 : Array (List ℕ) := #[[0x40710800a1000c8001069f0,0x808e1000ce00106a80,0x807a1001cc00106ac0], [0x82321000ca00106960,0x1034ce00106980,0x82361000ca00106a20], [0x82a210014800106950], [0x85ce2000c40010687c,0x85de2000c40010699c,0x85ea2000c400106a74,0x85f22000c400106b04], [0x1000e2000cc00106e40], [0x801610015200106e00,0x802210034e00106e80], [0x803e1001ce00106c80], [0x80c22000ca00106d20,0x80921000ce00106d80,0x403b0800a1000ca00106ea0]]
set_option maxRecDepth 10000 in
private def witnessesBlock37 : Array (List ℕ) := #[[0x824a1000ca00106de0,0x1037ce00106f80], [0x82b610014800106c70,0x82ba10014800106d10,0x82c210014800106e50], [0x86022000c400106c24,0x860a2000c400106cb4,0x86262000c400106eac], [0x1000a2000ce00107080], [0x800b0800a1000c800107170,0x400d0800e10014c001071c0,0x400b0800e1000ce00107380], [0x40170801a1000ca00107020,0x402b0800e1000ca001070e0,0x40290800a2000c800107350,0x40350800e100148001073f0], [0x80ca2000ca001071a0,0x403d0800a1000ca00107260,0x80ce2000ca001073e0], [0x1038ce00107180,0x10394e00107280,0x82661000ca00107320]]
set_option maxRecDepth 10000 in
private def witnessesBlock38 : Array (List ℕ) := #[[0x82ce10014800107030,0x82de100148001072b0], [0x863a2000c400107014,0x86522000c4001071c4,0x86562000c40010720c,0x866a2000c400107374,0x866e2000c4001073bc], [0x2000a1000c800107530,0x800a1000d600107800], [0x805e10014e00107580,0x401d0801a100148001075d0,0x401d080161000ca001077a0], [0x80861001cc00107540,0x809e1000ce00107680,0x407f0800a1000c800107710], [0x103a4e00107480,0x826e1000ca001074a0,0x103bce00107780], [0x82ea10014800107490,0x82721000ca00107560,0x82f610014800107670,0x827a1000ca001076e0,0x82fe100148001077b0], [0x86762000c40010744c,0x867a2000c400107494,0x868e2000c4001075fc,0x86aa2000c4001077f4]]
set_option maxRecDepth 10000 in
private def witnessesBlock39 : Array (List ℕ) := #[[0x5000ce00107980], [0x4013080221000ca00107920,0x802610034e00107b80], [0x40170800e1000cc001078c0,0x402b0800a2000c8001078f0,0x40170802210014800107a30,0x402f0800e1000ca00107b60], [0x80d62000ca00107860,0x80da2000ca00107aa0,0x40830800a1000c800107ad0], [0x103c4e00107880], [0x830a10014800107990], [0x86b22000c400107884,0x86b62000c4001078cc,0x86be2000c40010795c,0x86da2000c400107b54,0x86e22000c400107be4], [0x1e00108000]]
set_option maxRecDepth 10000 in
private def witnessesBlock40 : Array (List ℕ) := #[[0x1000a4000c800107e90], [0x40110800a1000ce00107f80], [0x804a3000ca00107ce0,0x401f0801a10014800107df0,0x802e1002ce00107e80,0x40250801610014800107f30,0x401f080161000ca00107fe0], [0x808e1001cc00107c40,0x80a61000ce00107c80,0x40430800a1000ca00107da0,0x80e22000ca00107f20,0x80921001cc00107fc0], [0x103ece00107d80], [0x831a10014800107c10,0x82961000ca00107c20,0x832210014800107d50,0x82a21000ca00107e60,0x833210014800107fd0], [0x86e62000c400107c2c,0x86ee2000c400107cbc,0x87162000c400107f8c], [0x1800e1000ca001080a0,0x40071000a1000cc00108340,0x800a3000d000108700]]
set_option maxRecDepth 10000 in
private def witnessesBlock41 : Array (List ℕ) := #[[0x801a10015200108200,0x80161000d400108400,0x8022300148001084d0,0x40110800e2000ca001085e0], [0x40170800a2000ca00108160,0x804a1001ce00108180,0x803a2000ce00108280,0x402f0800a2000c800108430,0x806a10014e00108480,0x401d1000a1000c8001087f0], [0x403b0800e10014800108110,0x40470800a1000ca00108520,0x403d0800e10014800108570,0x80b21000ce00108580], [0x40890800a1000c800108070,0x10404e00108080,0x408b0800a1000c800108250,0x1041ce00108380,0x10434e00108680,0x1043ce00108780], [0x82b61000ca00108220,0x82ba1000ca001082e0,0x8346100148001082f0,0x834a10014800108390,0x82c21000ca00108460,0x82ce1000ca001086a0,0x835e100148001086b0,0x836210014800108750], [0x871e2000c40010801c,0x872e2000c40010813c,0x87422000c4001082a4,0x87522000c4001083c4,0x875a2000c400108454,0x87662000c40010852c,0x87722000c400108604,0x878e2000c4001087fc], [0x80070800a2000c8001089d0,0x1800a2000ca00108ca0], [0x400d0800e1000ce00108880,0x40130800a1000ce00108e80]]
set_option maxRecDepth 10000 in
private def witnessesBlock42 : Array (List ℕ) := #[[0x40170802610014800108890,0x80523000ca00108a60,0x40350800e1000ca00108b20,0x803e2000ce00108b80,0x40290801610014800108cf0,0x401d0801a1000ca00108d60,0x80521001ce00108f80], [0x40490800a1000ca001088e0,0x809e1001cc00108a40,0x80fe2000ca00108ee0], [0x10454e00108a80,0x40950800a1000c800108bb0,0x10464e00108c80,0x1046ce00108d80,0x40970800a1000c800108d90], [0x836e10014800108930,0x82de1000ca001089a0,0x837610014800108a70,0x82ea1000ca00108be0,0x838210014800108c50,0x82f61000ca00108e20,0x839210014800108ed0,0x82fe1000ca00108fa0], [0x87962000c40010888c,0x87a22000c400108964,0x87ae2000c400108a3c,0x87be2000c400108b5c,0x87ca2000c400108c34,0x87e22000c400108de4,0x87ea2000c400108e74,0x87f62000c400108f4c,0x87fa2000c400108f94], [0x1000a1000d200109600,0x800a5000ca001097e0], [0x802630014800109470,0x80163000ce00109480,0x40110800e10014c001094c0,0x40130800e2000ca001095a0], [0x80563000ca00109120,0x401f1000a1000c800109150,0x4017080221000ca001092a0,0x402b08016100148001093d0,0x1002e2000c6001094c8,0x40350800a2000c800109510,0x802e10034e00109580,0x40250801a10014800109650,0x80561001ce00109680,0x401f0801a1000ca00109720]]
set_option maxRecDepth 10000 in
private def witnessesBlock43 : Array (List ℕ) := #[[0x80a61001cc00109140,0x80c21000ce00109180,0x40430800e10014800109290,0x81062000ca00109360,0x807610014e00109380,0x404f0800a1000ca00109420,0x80ca1000ce00109780], [0x10494e00109280,0x409d0800a1000c800109330], [0x839a10014800109010,0x839e100148001090b0,0x830a1000ca001091e0,0x83a6100148001091f0,0x831a1000ca001094e0,0x83be100148001095b0,0x83221000ca00109660], [0x880e2000c4001090fc,0x88122000c400109144,0x881e2000c40010921c,0x88322000c400109384,0x88362000c4001093cc,0x884a2000c400109534,0x884e2000c40010957c,0x885a2000c400109654], [0x40070800a2000ce00109d80], [0x400b1000a2000c800109ab0,0x800d0800a1000c800109e70], [0x401d0800e1000cc00109840,0x4025080161000ca001098a0,0x401d0802210014800109a10,0x805e3000ca00109ea0,0x803a1002ce00109f80], [0x807a10014e00109880,0x80ce1000ce00109a80,0x403b0800e1000ca00109ae0,0x40470800e10014800109b50,0x40530800a1000ca00109ba0,0x80b21001cc00109bc0,0x40490800e10014800109fb0]]
set_option maxRecDepth 10000 in
private def witnessesBlock44 : Array (List ℕ) := #[[0x40a30800a1000c8001098d0,0x104cce00109980,0x81122000ca00109a20,0x104dce00109b80,0x81162000ca00109c60,0x40a70800a1000c800109c90], [0x83ce10014800109830,0x83321000ca00109960,0x83d610014800109970,0x83e610014800109bf0,0x104e4e00109c80,0x83461000ca00109d20,0x83ee10014800109d30,0x834a1000ca00109de0,0x104f4e00109e80,0x83fa10014800109f10], [0x887e2000c4001098dc,0x88862000c40010996c,0x888a2000c4001099b4,0x88922000c400109a44,0x889e2000c400109b1c,0x88aa2000c400109bf4,0x88ba2000c400109d14,0x88c62000c400109dec,0x88d22000c400109ec4], [0x1000e3000ca0010a560,0x800e1000d60010a800], [0x400d080162000ca0010a0e0,0x802610044e0010a180,0x40130800e10014c0010a640], [0x402f080161001480010a190,0x401f0800e1000cc0010a2c0,0x401d0800a2000ca0010a320,0x4017080261000ca0010a3e0,0x805e1001ce0010a480,0x401f080221001480010a4b0,0x804a2000ce0010a680,0x40290801a1001480010a690], [0x403d0800e1000ca0010a020,0x80d61000ce0010a080,0x80da1000ce0010a380,0x403b0800a2000c80010a5f0,0x40590800a1000ca0010a6e0,0x808610014e0010a780], [0x40ad0800a1000c80010a230,0x812a2000ca0010a7a0,0x40b30800a1000c80010a7d0]]
set_option maxRecDepth 10000 in
private def witnessesBlock45 : Array (List ℕ) := #[[0x835e1000ca0010a1a0,0x83621000ca0010a260,0x84121001480010a2d0,0x84161001480010a370,0x836e1000ca0010a4a0,0x1052ce0010a580,0x83761000ca0010a620], [0x88fe2000c40010a1dc,0x89022000c40010a224,0x89162000c40010a38c,0x89262000c40010a4ac,0x893a2000c40010a614,0x89462000c40010a6ec,0x89522000c40010a7c4], [0x3001ce0010ab80,0x2000a2000c60010afc8], [0x80221001520010aa00,0x400b0800e2000cc0010ad40,0x801a3000ce0010af80], [0x4029080161000ca0010a920,0x803e1002ce0010aa80,0x401d080261001480010ac30,0x40170800a1000ce0010ac80,0x40251000a1000c80010ad70,0x401f0800a2000ca0010ae60,0x402b0801a1001480010aeb0], [0x80e21000ce0010a980,0x80c21001cc0010a9c0,0x403d0800a2000c80010ab90,0x404f0800e1001480010acd0,0x40430800e1000ca0010afe0], [0x40b50800a1000c80010a9b0,0x812e2000ca0010a9e0], [0x83821000ca0010a860,0x10544e0010a880,0x843a1001480010a910,0x84461001480010aaf0,0x83921000ca0010ab60,0x839a1000ca0010ace0,0x1056ce0010ad80,0x839e1000ca0010ada0,0x845a1001480010ae10,0x10574e0010ae80,0x83a61000ca0010af20,0x84661001480010aff0]]
set_option maxRecDepth 10000 in
private def witnessesBlock46 : Array (List ℕ) := #[[0x89622000c40010a8e4,0x897a2000c40010aa94,0x89822000c40010ab24,0x898e2000c40010abfc,0x899a2000c40010acd4,0x899e2000c40010ad1c,0x89aa2000c40010adf4,0x89c22000c40010afa4], [0x80070800a1000cc0010b7c0], [0x40110800e1000ce0010b280,0x100161000ce0010b580,0x400d1000a2000c80010b6d0], [0x402b080161000ca0010b160,0x806a3000ca0010b2e0,0x802e3001480010b3b0,0x40250801a1000ca0010b460,0x40170800e2000ca0010b520,0x4035080161001480010b630], [0x80ca1001cc0010b0c0,0x808e10014e0010b180,0x80ce1001cc0010b440,0x40530800e1001480010b590,0x40610800a1000ca0010b5e0,0x809210014e0010b680], [0x813a2000ca0010b0a0,0x40bf0800a1000c80010b310,0x40c10800a1000c80010b4f0,0x81462000ca0010b760], [0x10584e0010b080,0x84721001480010b1d0,0x84761001480010b270,0x1059ce0010b380,0x83be1000ca0010b3a0,0x84821001480010b450,0x83ce1000ca0010b6a0,0x84961001480010b770,0x105bce0010b780], [0x89d62000c40010b10c,0x89fa2000c40010b394,0x89fe2000c40010b3dc,0x8a062000c40010b46c,0x8a122000c40010b544,0x8a162000c40010b58c,0x8a222000c40010b664,0x8a2a2000c40010b6f4,0x8a2e2000c40010b73c,0x8a362000c40010b7cc]]
set_option maxRecDepth 10000 in
private def witnessesBlock47 : Array (List ℕ) := #[[0x1000e5000c40010ba0c,0x1800a1000ce0010bb80,0x800e3000d00010bd00], [0x80261001520010be00], [0x401f080261001480010b810,0x80522000ce0010b880,0x401d080221000ca0010b8e0,0x806a1001ce0010b980,0x803a10034e0010bc80,0x402f0801a1001480010bef0], [0x40470800e1000ca0010ba60,0x80d61001cc0010bb40,0x40430800a2000c80010bc70,0x40650800a1000ca0010bd60,0x80fe1000ce0010be80,0x80da1001cc0010bec0,0x40490800e1000ca0010bfa0], [0x40c50800a1000c80010b8b0,0x40c70800a1000c80010ba90,0x814e2000ca0010bbe0], [0x83d61000ca0010b820,0x84a21001480010b950,0x105d4e0010ba80,0x83e61000ca0010bb20,0x84ae1001480010bb30,0x84b21001480010bbd0,0x83ee1000ca0010bca0,0x105ece0010bd80,0x84be1001480010bdb0,0x83fa1000ca0010bee0,0x105fce0010bf80,0x84ca1001480010bf90], [0x8a4e2000c40010b97c,0x8a522000c40010b9c4,0x8a5e2000c40010ba9c,0x8aa22000c40010bf64], [0x400b0800e10014e0010c080,0x40130800e1000ce0010c780]]
set_option maxRecDepth 10000 in
private def witnessesBlock48 : Array (List ℕ) := #[[0x40291000a1000c80010c030,0x80562000ce0010c180,0x402f080161000ca0010c1e0,0x40250800e1000cc0010c240,0x802e10044e0010c380,0x4025080221001480010c490,0x401f080221000ca0010c5a0,0x40290801a1000ca0010c7e0], [0x40670800a1000ca0010c120,0x40590800e1001480010c2b0,0x81061000ce0010c480,0x809e10014e0010c580,0x80e21001cc0010c5c0,0x80763000ca0010c720,0x40470800a2000c80010c7b0], [0x815a2000ca0010c2a0,0x40d30800a1000c80010c5d0], [0x84d21001480010c0d0,0x84d61001480010c170,0x10614e0010c280,0x84121000ca0010c360,0x84161000ca0010c420,0x84ee1001480010c530,0x10634e0010c680], [0x8aae2000c40010c03c,0x8aba2000c40010c114,0x8aca2000c40010c234,0x8aee2000c40010c4bc,0x8b022000c40010c624], [0x8000c60010cd08], [0x800a4000ce0010ca80], [0x400d0800e2000cc0010ccc0,0x1003580010d000]]
set_option maxRecDepth 10000 in
private def witnessesBlock49 : Array (List ℕ) := #[[0x40170800e10014c0010c940,0x803e10034e0010c980,0x402b1000a1000c80010c990,0x804a1002ce0010cb80,0x401d080261000ca0010cea0], [0x406b0800a1000ca0010c8a0,0x403b080161001480010cad0,0x406d0800a1000ca0010cc60,0x40490800a2000c80010cd50,0x807a3000ca0010cde0,0x80761001ce0010ce80,0x404f0800e1000ca0010cf60,0x80a610014e0010cf80], [0x81662000ca0010c960,0x816a2000ca0010cba0,0x81121000ce0010cd80], [0x85021001480010c850,0x10644e0010c880,0x85061001480010c8f0,0x850e1001480010ca30,0x843a1000ca0010cae0,0x851a1001480010cc10,0x10664e0010cc80,0x84461000ca0010cd20,0x85261001480010cdf0,0x852a1001480010ce90], [0x8b1e2000c40010c81c,0x8b262000c40010c8ac,0x8b2a2000c40010c8f4,0x8b322000c40010c984,0x8b3e2000c40010ca5c,0x8b4e2000c40010cb7c,0x8b562000c40010cc0c,0x8b5a2000c40010cc54,0x8b662000c40010cd2c,0x8b7e2000c40010cedc], [0x3000d60010d800], [0x40070800a1000d20010d200,0x800e5000ca0010d4a0], [0x4011080162000ca0010d260,0x400d080161000ce0010d680]]
set_option maxRecDepth 10000 in
private def witnessesBlock50 : Array (List ℕ) := #[[0x40250800a2000ca0010d020,0x401d0802e1001480010d070,0x402b0801a1000ca0010d1a0,0x805e2000ce0010d380,0x40290800e1000cc0010d740,0x40350801a1001480010d750], [0x403d080161001480010d1b0,0x40710800a1000ca0010d3e0,0x40610800e1001480010d430,0x807a1001ce0010d580], [0x81161000ce0010d080,0x40df0800a1000c80010d110,0x40e30800a1000c80010d4d0,0x40e50800a1000c80010d6b0,0x817e2000ca0010d6e0], [0x845a1000ca0010d0e0,0x1068ce0010d180,0x85421001480010d250,0x10694e0010d280,0x84661000ca0010d320,0x854a1001480010d390,0x84721000ca0010d560,0x85561001480010d570,0x84761000ca0010d620,0x106bce0010d780,0x85661001480010d7f0], [0x8b922000c40010d044,0x8b962000c40010d08c,0x8b9e2000c40010d11c,0x8ba22000c40010d164,0x8baa2000c40010d1f4,0x8bb62000c40010d2cc,0x8bce2000c40010d47c,0x8be62000c40010d62c,0x8bf62000c40010d74c], [0x800e30014c0010dac0,0x1000e2000ce0010dc80,0x40071000a4000c40010dd7c,0x1001da0010e000], [0x2005840070800a2000c80010d890,0x80161001540010dc00], [0x401d0800a1000ce0010d980,0x4029080221001480010d9d0,0x802e1004ce0010da80,0x4035080161000ca0010daa0,0x4025080261001480010dbb0,0x402f1000a1000c80010dc50,0x401f080261000ca0010dce0,0x401f0802e1001480010ded0]]
set_option maxRecDepth 10000 in
private def witnessesBlock51 : Array (List ℕ) := #[[0x40530800e1000ca0010d9e0,0x40650800e1001480010dcf0,0x404f0800a2000c80010de30,0x80fe1001cc0010de40,0x80b210014e0010de80], [0x81822000ca0010d920,0x40e90800a1000c80010da70,0x818a2000ca0010dda0,0x812a1000ce0010df80,0x818e2000ca0010dfe0], [0x84821000ca0010d860,0x106c4e0010d880,0x857a1001480010db10,0x106dce0010db80,0x84961000ca0010dc20,0x106ece0010dd80,0x858a1001480010dd90,0x84a21000ca0010de60], [0x8c0e2000c40010d8fc,0x8c1a2000c40010d9d4,0x8c222000c40010da64,0x8c2e2000c40010db3c,0x8c3e2000c40010dc5c,0x8c462000c40010dcec,0x8c562000c40010de0c,0x8c5e2000c40010de9c], [0x400d0800e10014e0010e380,0x80223000ce0010e580], [0x80521002ce0010e180,0x402b0800e1000cc0010e1c0,0x803a3001480010e290,0x401d0800e2000ca0010e460,0x402b080221001480010e470,0x402f0801a1000ca0010e520,0x802e1001520010e600,0x40290800a2000ca0010e6a0], [0x40670800e1001480010e150,0x80863000ca0010e220,0x81061001cc0010e540,0x4043080161001480010e650], [0x40ef0800a1000c80010e010,0x40f10800a1000c80010e1f0,0x812e1000ce0010e280]]
set_option maxRecDepth 10000 in
private def witnessesBlock52 : Array (List ℕ) := #[[0x10704e0010e080,0x84ae1000ca0010e0a0,0x859e1001480010e0b0,0x84b21000ca0010e160,0x84be1000ca0010e3a0,0x10724e0010e480,0x84ca1000ca0010e5e0,0x10734e0010e680,0x84d21000ca0010e760,0x1073ce0010e780], [0x8c7a2000c40010e094,0x8c822000c40010e124,0x8c8e2000c40010e1fc,0x8c922000c40010e244,0x8c9a2000c40010e2d4,0x85ae1001480010e330,0x8ca62000c40010e3ac,0x85ba1001480010e510,0x85c61001480010e6f0], [0x8caa2000c40010e3f4,0x8cb62000c40010e4cc,0x8cca2000c40010e634], [0x2000a1000ca0010ea60,0x40070800a3000cc0010ec40], [0x4013080162000ca0010eb20,0x40111000a2000c80010ef10], [0x401f0800a1000ce0010e880,0x4025080221000ca0010ebe0,0x80561002ce0010ec80,0x1003a2000c60010ec88,0x806a2000ce0010ee80], [0x40530800a2000c80010e970,0x40590800e1000ca0010e9a0,0x406b0800e1001480010ea10,0x80861001ce0010ea80,0x407f0800a1000ca0010ee20,0x406d0800e1001480010ee70,0x808e3000ca0010efa0,0x403b0801a1001480010efb0], [0x40fb0800a1000c80010eb50,0x813a1000ce0010eb80,0x81a62000ca0010ed60,0x81121001cc0010efc0]]
set_option maxRecDepth 10000 in
private def witnessesBlock53 : Array (List ℕ) := #[[0x84d61000ca0010e820,0x1074ce0010e980,0x84ee1000ca0010eca0,0x1077ce0010ef80], [0x85ce1001480010e830,0x85de1001480010eab0,0x85ea1001480010ec90,0x85f21001480010edd0], [0x8cf22000c40010e904,0x8cfe2000c40010e9dc,0x8d062000c40010ea6c,0x8d0a2000c40010eab4,0x8d3a2000c40010ee14,0x8d422000c40010eea4,0x8d462000c40010eeec], [0x5000d00010f300], [0x400b0800a2000ce0010f780], [0x804a10034e0010f080,0x40170800e1000ce0010f180,0x402b0800a2000ca0010f1e0,0x803e3001480010f230,0x4029080261001480010f370,0x401f0800e2000ca0010f420,0x803a10044e0010f680,0x402f0800e1000cc0010f6c0], [0x80c210014e0010f280,0x403b080161000ca0010f360,0x4047080161001480010f410,0x40830800a1000ca0010f5a0,0x80923000ca0010f660,0x40710800e1001480010f730,0x403d0801a1001480010f7d0], [0x41010800a1000c80010f0f0,0x81161001cc0010f340,0x81461000ce0010f480,0x41070800a1000c80010f690]]
set_option maxRecDepth 10000 in
private def witnessesBlock54 : Array (List ℕ) := #[[0x85021000ca0010f060,0x85061000ca0010f120,0x850e1000ca0010f2a0,0x1079ce0010f380,0x851a1000ca0010f4e0,0x107ace0010f580,0x85261000ca0010f720,0x852a1000ca0010f7e0], [0x86021001480010f050,0x860a1001480010f190,0x86261001480010f5f0], [0x8d5a2000c40010f054,0x8d722000c40010f204,0x8d762000c40010f24c,0x8d8a2000c40010f3b4,0x8d9a2000c40010f4d4,0x8da62000c40010f5ac,0x8db22000c40010f684,0x8dbe2000c40010f75c], [0x3001520010fa00,0x1000a4000ca0010fd20], [0x40110801a2000ca0010f8a0,0x400d080161001cc0010fa40,0x1001a1000ce0010fd80,0x2006840070800a2000c80010fff0], [0x40351000a1000c80010f870,0x402f080221001480010f9b0,0x401d0802e1000ca0010fa20,0x401d0800e10014c0010fdc0,0x402b080261001480010ff50], [0x808e1001ce0010f880,0x40590800a2000c80010fa50,0x4049080161001480010faf0,0x403d080161000ca0010fba0,0x80ca10014e0010fc80,0x40610800e1000ca0010fea0,0x80921001ce0010ff80], [0x814e1000ce0010fa80,0x81be2000ca0010fae0,0x410d0800a1000c80010fc30,0x410f0800a1000c80010fe10,0x81c62000ca0010ff60]]
set_option maxRecDepth 10000 in
private def witnessesBlock55 : Array (List ℕ) := #[[0x107cce0010f980,0x107dce0010fb80,0x85421000ca0010fc60,0x854a1000ca0010fde0,0x107f4e0010fe80], [0x863a1001480010f910,0x86521001480010fcd0,0x86561001480010fd70], [0x8de22000c40010f9e4,0x8dee2000c40010fabc,0x8df62000c40010fb4c,0x8dfa2000c40010fb94,0x8e122000c40010fd44,0x8e262000c40010feac], [0x1800e1000cc00110140,0x40071000a1000ce00110680,0x800a3000d200110e00], [0x80263000ce00110080,0x80161000d600110800,0x40131000a2000c800110b30,0x40110800e2000cc00110bc0,0x80110800a1000c800110ef0], [0x40350801a1000ca00110260,0x805e1002ce00110280,0x4029080221000ca00110560,0x803e10044e00110780,0x4025080261000ca001107a0,0x402f0800a2000ca00110860,0x40250802e100148001109f0,0x805210034e00110a80,0x401f0802e1000ca00110b60,0x1003e2000c600110e48,0x401f0800e10014c00110f40], [0x80ce10014e00110180,0x40650800e1000ca00110920,0x80762000ce00110980,0x809e3000ca00110aa0,0x80d610014e00110b80,0x40670800e1000ca00110e60,0x404f0801610014800110f90], [0x40890800a1000ca001100e0,0x81ca2000ca001101a0,0x815a1000ce00110380,0x41150800a1000c8001103b0,0x408b0800a1000ca001104a0,0x812a1001cc001104c0,0x81d22000ca00110620,0x41190800a1000c800110770,0x812e1001cc00110840,0x411b0800a1000c800110950,0x81661000ce00110c80,0x81de2000ca00110ce0,0x81e22000ca00110f20,0x816a1000ce00110f80]]
set_option maxRecDepth 10000 in
private def witnessesBlock56 : Array (List ℕ) := #[[0x85561000ca00110020,0x85661000ca00110320,0x10824e00110480,0x1082ce00110580,0x857a1000ca001106e0,0x858a1000ca001109e0,0x859e1000ca00110da0,0x10874e00110e80], [0x866a10014800110090,0x866e10014800110130,0x867610014800110270,0x867a10014800110310,0x868e10014800110630,0x86aa10014800110a90,0x86b210014800110bd0,0x86b610014800110c70,0x86be10014800110db0], [0x8e3e2000c40011005c,0x8e4e2000c40011017c,0x8e6e2000c4001103bc,0x8e8a2000c4001105b4,0x8e962000c40011068c,0x8e9e2000c40011071c,0x8ea22000c400110764,0x8eaa2000c4001107f4,0x8eae2000c40011083c,0x8ec22000c4001109a4,0x8eda2000c400110b54,0x8ee62000c400110c2c,0x8ef22000c400110d04,0x8f162000c400110f8c,0x8f1a2000c400110fd4], [0x7000ca00111160], [0x800e40014800111170], [0x40130801a2000ca001115e0,0x4011080161000ce00111880], [0x402b080221000ca00111220,0x803a1004ce00111380,0x40250800a1000ce00111580,0x40350800e1000cc00111640,0x402f0802610014800111710,0x805610034e00111780,0x401f0803a100148001118f0,0x40350802210014800111990,0x4017080162000ca00111ca0], [0x40430801a10014800111030,0x80da10014e00111080,0x40610800a2000c8001110d0,0x807a2000ce00111280,0x4043080161000ca00111460,0x809e1001ce00111480,0x403b1000a1000c800111490,0x407f0800e100148001115d0,0x80a63000ca00111820,0x406b0800e1000ca001118e0,0x80e210014e00111a80,0x40650800a2000c800111c10,0x40530801610014800111d50,0x403d1000a1000c800111df0,0x406d0800e1000ca00111e20,0x40830800e10014800111e90,0x403b0801a1000ca00111fa0]]
set_option maxRecDepth 10000 in
private def witnessesBlock57 : Array (List ℕ) := #[[0x41250800a1000c8001112b0,0x813a1001cc001112c0,0x40950800a1000ca00111760,0x81f62000ca00111a60,0x40970800a1000ca00111b20,0x81461001cc00111d40,0x817e1000ce00111e80,0x41330800a1000c800111fd0], [0x1088ce00111180,0x108b4e00111680,0x108cce00111980,0x108e4e00111c80,0x108ece00111d80], [0x85ae1000ca001110a0,0x86da10014800111210,0x85ba1000ca001112e0,0x86e210014800111350,0x86e6100148001113f0,0x85c61000ca00111520,0x86ee10014800111530,0x85ce1000ca001116a0,0x85de1000ca001119a0,0x871610014800111b70,0x85ea1000ca00111be0,0x871e10014800111cb0,0x85f21000ca00111d60,0x872e10014800111f30], [0x8f3a2000c400111214,0x8f3e2000c40011125c,0x8f6a2000c400111574,0x8f762000c40011164c,0x8f862000c40011176c,0x8f922000c400111844,0x8f9a2000c4001118d4,0x8f9e2000c40011191c,0x8fa62000c4001119ac,0x8fb62000c400111acc,0x8fc22000c400111ba4,0x8fd62000c400111d0c,0x8fda2000c400111d54,0x8fee2000c400111ebc], [0x40071000a3000c800112750], [0x2005840070800a1000cc001120c0,0x400d0800a2000ce00112480,0x80163000d000112900,0x40110800e10014e00112980,0x40130800e2000cc00112b40], [0x804a30014800112110,0x803a10015200112200,0x40250800e2000ca00112360,0x806a1002ce00112380,0x4029080261000ca00112420,0x803e1004ce00112680,0x40290802e100148001126b0,0x40350800a2000ca00112a20,0x402f080221000ca00112ba0], [0x40470801a10014800112070,0x40670800a2000c8001121b0,0x80a61001ce00112280,0x4047080161000ca001124e0,0x40490801a10014800112890,0x40710800e1000ca001128a0,0x403d0801a1000ca00112960,0x80b23000ca00112c60,0x406b0800a2000c800112cf0,0x4049080161000ca00112d20,0x80862000ce00112d80]]
set_option maxRecDepth 10000 in
private def witnessesBlock58 : Array (List ℕ) := #[[0x82022000ca00112120,0x81821000ce00112180,0x41370800a1000c800112390,0x814e1001cc00112440,0x409d0800a1000ca00112660,0x818a1000ce00112780,0x820e2000ca001127e0,0x818e1000ce00112a80,0x40890800e10014800112bb0,0x821a2000ca00112ea0,0x815a1001cc00112ec0], [0x10904e00112080,0x41390800a1000c800112570,0x1092ce00112580,0x10944e00112880,0x413d0800a1000c800112930,0x1095ce00112b80,0x10964e00112c80,0x1097ce00112f80], [0x86021000ca00112060,0x860a1000ca001121e0,0x874210014800112250,0x8752100148001124d0,0x875a10014800112610,0x86261000ca00112720,0x8766100148001127f0,0x8772100148001129d0,0x863a1000ca00112ae0,0x878e10014800112e30,0x86521000ca00112f60,0x879610014800112f70], [0x900a2000c4001120b4,0x901e2000c40011221c,0x902a2000c4001122f4,0x90422000c4001124a4,0x90462000c4001124ec,0x904e2000c40011257c,0x90522000c4001125c4,0x90662000c40011272c,0x907e2000c4001128dc,0x90822000c400112924,0x90a22000c400112b64,0x90a62000c400112bac,0x90b22000c400112c84,0x90ba2000c400112d14,0x90be2000c400112d5c,0x90d22000c400112ec4,0x90e22000c400112fe4], [0x80070800a4000c400113614,0x40014e00113880], [0x80161001d400113400,0x801a1000d600113800,0x4013080161000ce00113980], [0x401d0800e1000ce00113080,0x805e10034e00113180,0x402b080261000ca00113260,0x40290800a1000ce00113380,0x402b0802e10014800113510,0x803e10015200113600,0x802e3000ce00113680,0x804a10044e00113a80,0x40350802610014800113ab0,0x40250802e1000ca00113f20], [0x405908016100148001131f0,0x406d0800a2000c800113290,0x403b0800e1000cc001135c0,0x80b21001ce00113780,0x403b0802210014800113970,0x40431000a1000c800113a10,0x80fe10014e00113d80,0x40710800a2000c800113dd0,0x808e2000ce00113f80]]
set_option maxRecDepth 10000 in
private def witnessesBlock59 : Array (List ℕ) := #[[0x408b0800e10014800113010,0x821e2000ca001130e0,0x40a30800a1000ca001131a0,0x822a2000ca001137a0,0x40a70800a1000ca00113920,0x81661001cc00113940,0x82322000ca00113c20,0x81a61000ce00113c80,0x816a1001cc00113cc0,0x82362000ca00113e60], [0x10994e00113280,0x109a4e00113480,0x109ace00113580,0x414b0800a1000c800113650,0x109dce00113b80,0x41510800a1000c800113bf0], [0x86561000ca00113020,0x87a210014800113150,0x87ae10014800113330,0x866a1000ca001133e0,0x866e1000ca001134a0,0x87be100148001135b0,0x86761000ca00113620,0x867a1000ca001136e0,0x87ca10014800113790,0x868e1000ca00113aa0,0x87e210014800113b50,0x87ea10014800113c90,0x87f610014800113e70,0x87fa10014800113f10,0x86aa1000ca00113fe0], [0x91062000c40011326c,0x91362000c4001135cc,0x913e2000c40011365c,0x914a2000c400113734,0x915a2000c400113854,0x917a2000c400113a94,0x917e2000c400113adc,0x91862000c400113b6c,0x91962000c400113c8c,0x91b62000c400113ecc,0x91ba2000c400113f14,0x91c22000c400113fa4], [0x1000e3000cc00114ac0], [0x4011080161001cc00114740,0x400b0800a1000d200114a00,0x40110801a1000ce00114b80,0x40130800e10014e00114c80,0x80165000ca00114e20,0x2008840070800a2000c800114eb0], [0x805230014800114050,0x402b0800a1000ce00114280,0x40290800e2000ca001142e0,0x40171000a2000c800114370,0x40250800e10014c001143c0,0x401f0800e1000ce00114580,0x803a1005ce00114d80,0x402f080261000ca00114ee0,0x40250803a10014800114f50,0x805630014800114ff0], [0x403d0800e1000cc00114040,0x404f0801a100148001140f0,0x403d0802210014800114410,0x80761002ce00114480,0x404f080161000ca001145e0,0x40430801a1000ca001146a0,0x80c23000ca00114760,0x810610014e00114780,0x80922000ce00114880,0x403b0800a2000ca00114be0,0x40471000a1000c800114cd0,0x407f0800e1000ca00114d60,0x40610801610014800114d70,0x807a1002ce00114f80]]
set_option maxRecDepth 10000 in
private def witnessesBlock60 : Array (List ℕ) := #[[0x40ad0800a1000ca00114460,0x40950800e100148001145f0,0x824a2000ca001149a0,0x40970800e10014800114a50,0x817e1001cc00114e40,0x81be1000ce00114e80,0x40b30800a1000ca00114fa0], [0x10a04e00114080,0x10a0ce00114180,0x10a1ce00114380,0x415b0800a1000c800114550,0x10a34e00114680,0x415d0800a1000c800114730,0x10a4ce00114980,0x10a54e00114a80,0x41610800a1000c800114af0], [0x86b21000ca00114160,0x86b61000ca00114220,0x880e10014800114230,0x8812100148001142d0,0x86be1000ca001143a0,0x881e100148001144b0,0x8832100148001147d0,0x883610014800114870,0x86da1000ca001148e0,0x86e21000ca00114a60,0x86e61000ca00114b20,0x884a10014800114b90,0x884e10014800114c30,0x86ee1000ca00114ca0,0x885a10014800114e10], [0x91d22000c4001140c4,0x91de2000c40011419c,0x91ea2000c400114274,0x91f22000c400114304,0x920a2000c4001144b4,0x920e2000c4001144fc,0x923a2000c400114814,0x92462000c4001148ec,0x924a2000c400114934,0x92562000c400114a0c,0x925e2000c400114a9c,0x926a2000c400114b74,0x92862000c400114d6c,0x92922000c400114e44,0x929a2000c400114ed4,0x929e2000c400114f1c,0x92aa2000c400114ff4], [0x1000a3000ce00115180,0x2000a2000c800115f90], [0x80130800a1000c800115270,0x800b0800a2000c800115450,0x2006840070800a1000cc00115540,0x400b0800e2000ce00115a80,0x400b1000a4000c400115c0c,0x801a3000d000115f00], [0x40170801a2000ca00115060,0x401f0803a1000ca00115120,0x402f0802e100148001151d0,0x4035080221000ca001151e0,0x402b0800e2000ca001152a0,0x806a10034e00115880,0x805210044e00115c80,0x804a1004ce00115f80], [0x40530801a10014800115130,0x80c21001ce00115380,0x80ca3000ca001154e0,0x40491000a1000c800115630,0x4053080161000ca00115660,0x403d0800a2000ca00115720,0x40830800e1000ca001157e0,0x40470801a1000ca00115a20,0x40650801610014800115b30,0x80ce3000ca00115ba0,0x403b0802610014800115e50,0x40430800e1000cc00115fc0]]
set_option maxRecDepth 10000 in
private def witnessesBlock61 : Array (List ℕ) := #[[0x81821001cc001151c0,0x40b50800a1000ca00115360,0x81c61000ce00115480,0x811210014e00115680,0x409d0800e10014800115770,0x81ca1000ce00115780,0x818a1001cc001158c0,0x82662000ca00115960,0x811610014e00115b80,0x818e1001cc00115c40,0x81d21000ce00115d80,0x826e2000ca00115de0], [0x10a84e00115080,0x41670800a1000c800115090,0x10a94e00115280,0x10aace00115580,0x416f0800a1000c800115810,0x10acce00115980,0x41750800a1000c800115db0,0x10af4e00115e80], [0x887e100148001153b0,0x87161000ca00115420,0x8886100148001154f0,0x888a10014800115590,0x871e1000ca001155a0,0x8892100148001156d0,0x872e1000ca001158a0,0x889e100148001158b0,0x88aa10014800115a90,0x87421000ca00115c60,0x88ba10014800115d10,0x88c610014800115ef0,0x87521000ca00115f60], [0x92b22000c400115084,0x92be2000c40011515c,0x92d62000c40011530c,0x92e22000c4001153e4,0x92ee2000c4001154bc,0x930a2000c4001156b4,0x93122000c400115744,0x931e2000c40011581c,0x93362000c4001159cc,0x93462000c400115aec,0x93522000c400115bc4,0x935a2000c400115c54,0x938e2000c400115ffc], [0x40070800a4000ca00116260,0x800a2000d600116800,0x80070800a1000ce00116f80], [0x400d0801610014e00116580,0x2005840071000a1000c8001168f0,0x4013080222000ca00116b60,0x4013080161001cc00116dc0], [0x402f0800a1000ce00116080,0x40290802e1000ca001161a0,0x803e1005ce00116480,0x40250803e10014800116670,0x40290800e10014c001166c0,0x401d080162000ca001166e0,0x40170800e2000cc00116a40,0x805610044e00116d80,0x805e30014800116f30], [0x80ca1001ce00116180,0x40670801610014800116210,0x809e2000ce00116380,0x40490801a1000ca001163e0,0x404308022100148001163f0,0x407f0800a2000c800116530,0x80ce1001ce00116880,0x80d63000ca00116920,0x40590801a10014800116990,0x403d0802610014800116a30,0x4059080161000ca00116f20,0x406b0801610014800116fd0,0x80da3000ca00116fe0]]
set_option maxRecDepth 10000 in
private def witnessesBlock62 : Array (List ℕ) := #[[0x40a30800e10014800116490,0x40bf0800a1000ca00116620,0x81de1000ce00116680,0x40890800e1000ca001167a0,0x81e21000ce00116980,0x40c10800a1000ca001169e0,0x408b0800e1000ca00116ce0,0x40a70800e10014800116d50], [0x82722000ca00116020,0x10b14e00116280,0x417b0800a1000c800116350,0x827a2000ca001164a0,0x417f0800a1000c800116710,0x10b3ce00116780,0x41850800a1000c800116cb0], [0x88d2100148001160d0,0x875a1000ca001160e0,0x87661000ca00116320,0x87721000ca00116560,0x88fe100148001167b0,0x890210014800116850,0x878e1000ca00116aa0,0x891610014800116b70,0x10b5ce00116b80,0x87961000ca00116c20,0x892610014800116df0,0x87a21000ca00116e60,0x10b74e00116e80], [0x93b22000c400116284,0x93c62000c4001163ec,0x93d62000c40011650c,0x93de2000c40011659c,0x93ea2000c400116674,0x93ee2000c4001166bc,0x93fa2000c400116794,0x94262000c400116aac,0x943e2000c400116c5c,0x94422000c400116ca4,0x94622000c400116ee4], [0x1000de00118000], [0x1000a5000c800117bb0], [0x40130801a1000ce00117280,0x2009840070800a2000c800117610,0x40110800a2000ce00117e80], [0x804a10015200117200,0x402f0800e2000ca00117220,0x402b0802e1000ca001172e0,0x40290803a10014800117390,0x402b0800e10014c00117840,0x4035080261000ca001179a0,0x4017080161000ce00117b80,0x40350802e10014800117cf0,0x401f080162000ca00117fa0]]
set_option maxRecDepth 10000 in
private def witnessesBlock63 : Array (List ℕ) := #[[0x40830800a2000c800117070,0x80861002ce00117080,0x404f1000a1000c800117250,0x40470800e1000cc001174c0,0x80a62000ce00117580,0x80d61001ce00117680,0x406d08016100148001176b0,0x403b080221000ca00117820,0x40430800a2000ca001178e0,0x40470802210014800117930,0x80e23000ca00117d60,0x80da1001ce00117d80,0x40490800e1000cc00117f40,0x807610034e00117f80], [0x81a61001cc00117140,0x40c50800a1000ca00117160,0x812a10014e00117480,0x40c70800a1000ca00117520,0x81f61000ce00117880,0x812e10014e00117980,0x40ad0800e10014800117a70], [0x418d0800a1000c800117430,0x82962000ca00117460,0x41910800a1000c8001177f0,0x82a22000ca00117b20,0x41990800a1000c800117f70], [0x87ae1000ca001170a0,0x893a10014800117110,0x10b8ce00117180,0x8946100148001172f0,0x10b9ce00117380,0x87be1000ca001173a0,0x8952100148001174d0,0x87ca1000ca001175e0,0x896210014800117750,0x10bbce00117780,0x87e21000ca00117a60,0x10bd4e00117a80,0x897a10014800117b10,0x87ea1000ca00117be0,0x898210014800117c50,0x10be4e00117c80,0x87f61000ca00117e20,0x898e10014800117e30,0x87fa1000ca00117ee0], [0x94722000c400117004,0x947a2000c400117094,0x94922000c400117244,0x94ae2000c40011743c,0x94c22000c4001175a4,0x94c62000c4001175ec,0x94ce2000c40011767c,0x94de2000c40011779c,0x94ea2000c400117874,0x94f62000c40011794c,0x94fe2000c4001179dc,0x95022000c400117a24,0x950a2000c400117ab4,0x95162000c400117b8c,0x95262000c400117cac,0x952e2000c400117d3c,0x95322000c400117d84,0x953e2000c400117e5c,0x95522000c400117fc4], [0x1800e2000ca001181e0,0x40071000a2000cc001189c0], [0x40110801a1001cc001182c0,0x400d0800a1000d200118600,0x801a5000ca00118ae0,0x80162000d400118c00], [0x1004a2000c600118108,0x40250800e1000ce00118480,0x80521004ce00118580,0x402b0803a100148001185b0,0x803a3000ce00118780,0x40290803e10014800118d30,0x40350800a1000ce00118d80,0x805e10044e00118f80]]
set_option maxRecDepth 10000 in
private def witnessesBlock64 : Array (List ℕ) := #[[0x404f0801a1000ca00118120,0x404908022100148001183d0,0x40710801610014800118470,0x403d080221000ca001184e0,0x40531000a1000c800118510,0x808e1002ce00118680,0x40610801a10014800118a10,0x80e21001ce00118b80,0x807a10034e00118c80,0x40430802610014800118dd0,0x40470800a2000ca00118f60], [0x40890800a2000c800118150,0x82021000ce00118180,0x81be1001cc00118640,0x408b0800a2000c8001186f0,0x40950800e1000ca00118720,0x40b30800e10014800118790,0x813a10014e00118880,0x820e1000ce00118a80,0x40d30800a1000ca00118ba0,0x40b50800e10014800118bf0,0x40970800e1000ca00118c60,0x81c61001cc00118d40], [0x82b62000ca00118660,0x82ba2000ca001188a0,0x41a30800a1000c8001188d0,0x41a50800a1000c800118ab0,0x82c22000ca00118d20], [0x899a10014800118010,0x10c04e00118080,0x899e100148001180b0,0x10c14e00118280,0x89aa10014800118290,0x880e1000ca001182a0,0x88121000ca00118360,0x881e1000ca001185a0,0x89c210014800118650,0x88321000ca00118960,0x89d610014800118970,0x10c4ce00118980,0x88361000ca00118a20,0x884a1000ca00118de0,0x10c74e00118e80,0x884e1000ca00118ea0,0x89fa10014800118f10,0x89fe10014800118fb0], [0x95562000c40011800c,0x956a2000c400118174,0x957a2000c400118294,0x95822000c400118324,0x959e2000c40011851c,0x95b22000c400118684,0x95ca2000c400118834,0x95ce2000c40011887c,0x95da2000c400118954,0x95e22000c4001189e4,0x95e62000c400118a2c,0x96062000c400118c6c,0x96222000c400118e64,0x962a2000c400118ef4,0x96362000c400118fcc], [0x800a4000d000119500,0x80070800a3000c800119d70], [0x20068400b0800a2000c800119230,0x400b1000e1000cc00119440,0x80221000d600119800,0x100163000ca00119860,0x400d0800e2000ce00119980,0x400d1000a4000c400119b54,0x400b1000a1000ce00119c80,0x1801610014800119ff0], [0x40250803a1000ca00119260,0x40170800e10014e00119280,0x402f0802e1000ca00119560,0x401d1000a2000c8001197d0,0x80561004ce00119880,0x805210015200119a00,0x402f0800e10014c00119b40,0x806a30014800119e10]]
set_option maxRecDepth 10000 in
private def witnessesBlock65 : Array (List ℕ) := #[[0x4061080161000ca00119020,0x80b22000ce00119080,0x80921002ce00119180,0x40530801a1000ca001194a0,0x40650801a10014800119a50,0x40490800a2000ca00119aa0,0x404f0800e1000cc00119ec0], [0x81ca1001cc001190c0,0x821a1000ce00119380,0x821e1000ce00119680,0x814610014e00119780,0x81d21001cc001197c0,0x409d0800e1000ca00119c20,0x822a1000ce00119f80], [0x82ce2000ca001193e0,0x41af0800a1000c800119410,0x41b10800a1000c8001195f0,0x41b70800a1000c800119b90,0x82de2000ca00119ce0,0x41bb0800a1000c800119f50], [0x885a1000ca001190e0,0x8a06100148001190f0,0x8a12100148001192d0,0x8a1610014800119370,0x10ca4e00119480,0x8a2210014800119550,0x10cace00119580,0x8a2a10014800119690,0x8a2e10014800119730,0x887e1000ca001197a0,0x8a3610014800119870,0x88861000ca00119920,0x888a1000ca001199e0,0x10cd4e00119a80,0x88921000ca00119b60,0x10cdce00119b80,0x8a4e10014800119c30,0x8a5210014800119cd0,0x10cece00119d80,0x889e1000ca00119da0,0x10cf4e00119e80,0x8a5e10014800119eb0,0x88aa1000ca00119fe0], [0x96462000c4001190ec,0x96522000c4001191c4,0x965a2000c400119254,0x967e2000c4001194dc,0x968e2000c4001195fc,0x96a22000c400119764,0x96ae2000c40011983c,0x96ba2000c400119914,0x96ca2000c400119a34,0x96de2000c400119b9c,0x96f62000c400119d4c,0x97122000c400119f44,0x971a2000c400119fd4], [0x800e5000cc0011a940,0x1800e10014c0011acc0], [0x2006840071000a1000c80011aa90,0x40130800a2000ce0011ab80,0x80164001480011adb0], [0x402b0803e1001480011a090,0x40350800e2000ca0011a160,0x803e3000ce0011a280,0x401d0801a2000ca0011a820,0x804a1005ce0011a980,0x402f0803a1001480011a9f0,0x80561001520011ae00,0x40250803e1000ca0011ae20,0x40290800e1000ce0011ae80]]
set_option maxRecDepth 10000 in
private def witnessesBlock66 : Array (List ℕ) := #[[0x4065080161000ca0011a0a0,0x40591000a1000c80011a130,0x40670801a1001480011a270,0x404f080221001480011a3b0,0x403b080261000ca0011a460,0x4047080261001480011a590,0x403b0802e1001480011a810,0x4067080161000ca0011a8e0,0x4043080221000ca0011ab20,0x80fe3000ca0011aca0], [0x814e10014e0011a180,0x40bf0800e1001480011a1d0,0x40df0800a1000ca0011a220,0x81de1001cc0011a240,0x40950800a2000c80011a310,0x82321000ce0011a580,0x81e21001cc0011a5c0,0x40c10800e1001480011a630,0x82361000ce0011a880,0x40970800a2000c80011a8b0,0x40e30800a1000ca0011a9a0,0x40a30800e1000ca0011abe0,0x40e50800a1000ca0011ad60,0x40c50800e1001480011aef0], [0x82ea2000ca0011a3a0,0x41c10800a1000c80011a4f0,0x82f62000ca0011aa60,0x41c90800a1000c80011ac70,0x82fe2000ca0011aee0], [0x88ba1000ca0011a2e0,0x10d1ce0011a380,0x88c61000ca0011a520,0x88d21000ca0011a760,0x8aa21001480011a950,0x10d54e0011aa80,0x8aae1001480011ab30,0x10d64e0011ac80,0x8aba1001480011ad10,0x10d6ce0011ad80,0x10d7ce0011af80,0x8aca1001480011af90,0x88fe1000ca0011afa0], [0x97262000c40011a0ac,0x97322000c40011a184,0x97362000c40011a1cc,0x976e2000c40011a5bc,0x97722000c40011a604,0x97862000c40011a76c,0x97962000c40011a88c,0x979e2000c40011a91c,0x97ba2000c40011ab14,0x97c22000c40011aba4,0x97d22000c40011acc4,0x97ea2000c40011ae74,0x97f62000c40011af4c], [0x800e30014e0011b580], [0x40130801a1001cc0011b040,0x2005840070800a2000ca0011b120,0x100221000ce0011b180,0x2008840070800a1000cc0011be40], [0x401f1000a2000c80011b3f0,0x4017080222000ca0011b7e0,0x4017080161001cc0011bac0,0x40290803a1000ca0011bde0,0x805e1004ce0011be80]]
set_option maxRecDepth 10000 in
private def witnessesBlock67 : Array (List ℕ) := #[[0x4049080261001480011b170,0x40590801a1000ca0011b1e0,0x809e1002ce0011b280,0x403d080261000ca0011b2a0,0x406b0801a1001480011b2b0,0x808610034e0011b380,0x40530800e1000cc0011b3c0,0x80c22000ce0011b480,0x407f080161001480011b490,0x403d0802e1001480011b670,0x4053080221001480011b8f0,0x406b080161000ca0011b960,0x81063000ca0011ba20,0x403b0800a1000ce0011ba80,0x406d0801a1001480011bad0,0x404f0800a2000ca0011bc60,0x80fe1001ce0011bc80], [0x815a10014e0011b080,0x40c70800e1001480011b350,0x40e90800a1000ca0011b4e0,0x40a70800e1000ca0011b660,0x81f61001cc0011b740,0x824a1000ce0011b780,0x409d0800a2000c80011b990,0x816610014e0011bf80], [0x41cd0800a1000c80011b030,0x41cf0800a1000c80011b210,0x830a2000ca0011b5a0,0x41d30800a1000c80011b5d0,0x831a2000ca0011bea0], [0x89021000ca0011b060,0x89161000ca0011b420,0x8aee1001480011b530,0x10db4e0011b680,0x89261000ca0011b720,0x8b021001480011b850,0x10dc4e0011b880,0x10dcce0011b980,0x893a1000ca0011bae0,0x10ddce0011bb80,0x8b1e1001480011bcb0,0x89461000ca0011bd20,0x8b261001480011bdf0,0x8b2a1001480011be90,0x89521000ca0011bf60,0x8b321001480011bfd0], [0x980e2000c40011b0fc,0x98162000c40011b18c,0x98222000c40011b264,0x984a2000c40011b534,0x985e2000c40011b69c,0x98622000c40011b6e4,0x98822000c40011b924,0x98b62000c40011bccc,0x98be2000c40011bd5c,0x98c22000c40011bda4,0x98da2000c40011bf54], [0x1000a2000d20011c200], [0x80261000d60011c800,0x80223000d00011cb00,0x100165000c40011cb6c], [0x40170801a1000ce0011c080,0x803e10074e0011c180,0x806a10044e0011c280,0x402b0800e1000ce0011c380,0x200b840070800a2000c80011c4d0,0x401f0801a2000ca0011c560,0x402f0803e1001480011c750,0x401d0800e2000cc0011c8c0,0x40350802e1000ca0011c920,0x4025080162000ca0011c9e0,0x40350800e10014c0011cfc0]]
set_option maxRecDepth 10000 in
private def witnessesBlock68 : Array (List ℕ) := #[[0x406d080161000ca0011c1a0,0x4083080161001480011c250,0x4047080221000ca0011c4a0,0x80ca2000ce0011c680,0x40611000a1000c80011c6b0,0x80a61002ce0011c880,0x403d0800a1000ce0011c980,0x81061001ce0011ca80,0x40710801a1001480011cb10,0x80763001480011ccf0,0x808e10034e0011cd80,0x80ce2000ce0011cf80], [0x40ef0800a1000ca0011c020,0x82021001cc0011c1c0,0x40f10800a1000ca0011c3e0,0x816a10014e0011c480,0x40ad0800e1000ca0011c620,0x40a30800a2000c80011ca70,0x820e1001cc0011cc40,0x82661000ce0011cc80,0x40d30800e1001480011cd90,0x81123000ca0011ce60], [0x41df0800a1000c80011c110,0x83222000ca0011c320,0x41e70800a1000c80011c890,0x83322000ca0011cc20,0x41eb0800a1000c80011cc50], [0x8b3e1001480011c1b0,0x89621000ca0011c260,0x8b4e1001480011c430,0x8b561001480011c570,0x10e2ce0011c580,0x8b5a1001480011c610,0x897a1000ca0011c6e0,0x10e3ce0011c780,0x8b661001480011c7f0,0x89821000ca0011c860,0x898e1000ca0011caa0,0x10e5ce0011cb80,0x8b7e1001480011cbb0,0x899a1000ca0011cce0,0x899e1000ca0011cda0,0x8b921001480011ced0,0x8b961001480011cf70,0x89aa1000ca0011cfe0], [0x98e62000c40011c02c,0x98ee2000c40011c0bc,0x99062000c40011c26c,0x99122000c40011c344,0x99222000c40011c464,0x992a2000c40011c4f4,0x993a2000c40011c614,0x99662000c40011c92c,0x996a2000c40011c974,0x99722000c40011ca04,0x99762000c40011ca4c,0x998e2000c40011cbfc,0x99c62000c40011cfec], [0x400b1000a3000c80011d010,0x40110801610014e0011d380,0x800d0800a2000c80011db50,0x400d1000e1000cc0011ddc0], [0x402b0803a1000ca0011d3a0,0x805e1001520011d600,0x80521005ce0011d780,0x100522000c60011d8c8,0x40290804a1001480011da10,0x40290803e1000ca0011dca0,0x401d080161000ce0011de80], [0x403b0800e2000ca0011d0a0,0x4049080221000ca0011d160,0x4071080161000ca0011d220,0x40530800a2000ca0011d2e0,0x40590800e1000cc0011d340,0x404f080261001480011d510,0x4059080221001480011d8d0,0x40610801a1000ca0011d8e0,0x40651000a1000c80011d970,0x809210034e0011da80,0x807a3001480011dc90,0x4043080261000ca0011dd60]]
set_option maxRecDepth 10000 in
private def witnessesBlock69 : Array (List ℕ) := #[[0x826e1000ce0011d280,0x81163000ca0011d520,0x40a70800a2000c80011d5b0,0x40b30800e1000ca0011d5e0,0x40fb0800a1000ca0011d6a0,0x821a1001cc0011d6c0,0x4089080161001480011d6f0,0x821e1001cc0011da40,0x40b50800e1000ca0011db20,0x817e10014e0011dd80,0x408b080161001480011ddd0,0x81121001ce0011df80], [0x41f30800a1000c80011d3d0,0x82721000ce0011d580,0x83462000ca0011d760,0x41f70800a1000c80011d790,0x834a2000ca0011d9a0,0x827a1000ce0011db80,0x41fd0800a1000c80011dd30], [0x10e84e0011d080,0x8b9e1001480011d0b0,0x8ba21001480011d150,0x8baa1001480011d290,0x89c21000ca0011d460,0x8bb61001480011d470,0x10ea4e0011d480,0x10eb4e0011d680,0x89d61000ca0011d820,0x8bce1001480011d830,0x10ecce0011d980,0x8be61001480011dbf0,0x10ee4e0011dc80,0x8bf61001480011de70,0x89fa1000ca0011dee0,0x89fe1000ca0011dfa0], [0x99ca2000c40011d034,0x99d62000c40011d10c,0x99e22000c40011d1e4,0x99ee2000c40011d2bc,0x99f62000c40011d34c,0x9a022000c40011d424,0x9a062000c40011d46c,0x9a1e2000c40011d61c,0x9a262000c40011d6ac,0x9a3e2000c40011d85c,0x9a422000c40011d8a4,0x9a562000c40011da0c,0x9a5a2000c40011da54,0x9a7a2000c40011dc94,0x9a7e2000c40011dcdc,0x9a9e2000c40011df1c,0x9aaa2000c40011dff4], [0x40071800a2000c80011ec30], [0x4013080221000ce0011e480,0x400d1000a1000ce0011e780], [0x40350803a1001480011e050,0x401f0800e2000cc0011e840,0x4017080262000ca0011eba0,0x402f0800e1000ce0011ed80,0x80561005ce0011ee80,0x80170800a1000c80011eff0], [0x403d0800e2000ca0011e060,0x80d62000ce0011e180,0x40430802e1001480011e190,0x40671000a1000c80011e2d0,0x80b21002ce0011e980,0x80da2000ce0011ea80,0x40650801a1000ca0011ec60,0x4053080261001480011ecd0]]
set_option maxRecDepth 10000 in
private def witnessesBlock70 : Array (List ℕ) := #[[0x41010800a1000ca0011e1e0,0x818210014e0011e280,0x822a1001cc0011e4c0,0x81161001ce0011e680,0x40ad0800a2000c80011e690,0x40df0800e1001480011e7d0,0x82321001cc0011ebc0,0x818a10014e0011ec80,0x41070800a1000ca0011ed20,0x82361001cc0011ef40], [0x835e2000ca0011e4e0,0x83622000ca0011e720,0x42090800a1000c80011e870,0x420b0800a1000c80011ea50,0x836e2000ca0011ede0], [0x8a061000ca0011e120,0x8c0e1001480011e230,0x8a121000ca0011e360,0x10f1ce0011e380,0x8c1a1001480011e410,0x8a161000ca0011e420,0x8c221001480011e550,0x10f2ce0011e580,0x8a221000ca0011e660,0x8c2e1001480011e730,0x8a2a1000ca0011e7e0,0x10f44e0011e880,0x8a2e1000ca0011e8a0,0x8c3e1001480011e9b0,0x8a361000ca0011ea20,0x8c461001480011eaf0,0x10f5ce0011eb80,0x8c561001480011ed70,0x8a4e1000ca0011eea0,0x8c5e1001480011eeb0,0x8a521000ca0011ef60,0x10f7ce0011ef80], [0x9ad22000c40011e2c4,0x9af22000c40011e504,0x9b022000c40011e624,0x9b0a2000c40011e6b4,0x9b0e2000c40011e6fc,0x9b162000c40011e78c,0x9b1a2000c40011e7d4,0x9b462000c40011eaec,0x9b562000c40011ec0c,0x9b6e2000c40011edbc,0x9b7a2000c40011ee94,0x9b8e2000c40011effc], [0x800e2000d60011f800], [0x2009840070800a1000cc0011f2c0,0x180161000ca0011f320,0x400d080161001ce0011f480,0x2005880070800a1000c80011f950,0x801a4001480011fbd0,0x40110800a1000d20011fe00,0x2006840070800a2000ca0011ffe0], [0x402b0804a1001480011f130,0x804a3000ce0011f380,0x402b0803e1000ca0011f3e0,0x806a1004ce0011f780,0x4029080162000ca0011fb60,0x401d0800e10014e0011fb80,0x402f0803a1000ca0011ff20,0x401f080161000ce0011ff80], [0x40590800a2000ca0011f4a0,0x807610044e0011f580,0x406b1000a1000c80011f590,0x40670801a1000ca0011f620,0x40430800a1000ce0011f680,0x404f080221000ca0011f7a0,0x4047080261000ca0011f9e0,0x80e22000ce0011fc80,0x403b0802e1000ca0011fce0,0x40610800e1000cc0011fd40,0x40470802e1001480011fe50,0x406d1000a1000c80011fef0]]
set_option maxRecDepth 10000 in
private def witnessesBlock71 : Array (List ℕ) := #[[0x40e30800e1001480011f090,0x818e10014e0011f180,0x40e50800e1001480011f4f0,0x40bf0800e1000ca0011f560,0x812a3000ca0011f6e0,0x40b30800a2000c80011f770,0x410d0800a1000ca0011f860,0x40c10800e1000ca0011faa0,0x410f0800a1000ca0011fc20,0x40b50800a2000c80011fd10,0x812e3000ca0011fda0,0x40e90800e1001480011fdb0], [0x82961000ce0011f080,0x83762000ca0011f260,0x83822000ca0011f920,0x82a21000ce0011f980,0x421d0800a1000c80011fb30], [0x8a5e1000ca0011f1a0,0x10f94e0011f280,0x8c7a1001480011f310,0x8c821001480011f450,0x8c8e1001480011f630,0x8c921001480011f6d0,0x8c9a1001480011f810,0x10fc4e0011f880,0x8ca61001480011f9f0,0x10fd4e0011fa80,0x10fece0011fd80,0x8aa21000ca0011fe60,0x10ff4e0011fe80], [0x9b922000c40011f044,0x9b9a2000c40011f0d4,0x9ba62000c40011f1ac,0x9baa2000c40011f1f4,0x9bb62000c40011f2cc,0x9bca2000c40011f434,0x9bce2000c40011f47c,0x9be62000c40011f62c,0x9bfa2000c40011f794,0x9bfe2000c40011f7dc,0x9c122000c40011f944,0x8caa1001480011fa90,0x9c2e2000c40011fb3c,0x9c3a2000c40011fc14,0x8cb61001480011fc70,0x9c422000c40011fca4,0x9c4e2000c40011fd7c,0x9c5e2000c40011fe9c,0x9c6a2000c40011ff74,0x8cca1001480011ff90], [0x800a8000c400120094,0x1800e1000ce00120280,0x40070800a5000c800121390], [0x80263000d000120100,0x80225000ca00120460,0x400b0800e3000cc001207c0,0x40130801610014e00120a80,0x20088400b0800a2000c800120df0,0x40110800e2000ce00121780,0x40111000a4000c4001219e4,0x100261000ce00121d80], [0x40350803e10014800120170,0x40170800a2000ce00120580,0x100562000c600120808,0x40251000a2000c800120850,0x40170801a1001cc00120b40,0x806a10015200121200,0x402b080162000ca00121420,0x804a10074e00121880,0x805e1005ce00121c80,0x40250801a2000ca00121d20,0x401f0800e10014e00121e80,0x402f0804a10014800121f70], [0x809e10034e00120180,0x40610802210014800120350,0x407f0801a100148001203f0,0x403b0800e10014c00120440,0x807a10044e00120680,0x4049080261000ca00120820,0x406b0801a1000ca001209a0,0x808630014800120b70,0x407f080161000ca00120be0,0x40490802e10014800120cb0,0x403d0802e1000ca00120e20,0x40430800e2000ca00120fa0,0x40590802610014800121070,0x4053080221000ca00121120,0x40711000a1000c8001211b0,0x40650800e1000cc00121240,0x406d0801a1000ca00121360,0x40830801a10014800121430,0x40470800a1000ce00121480,0x80c21002ce00121580,0x403d0800e10014c001215c0,0x403b0803a100148001216b0,0x40650802210014800121890,0x80a610034e00121b80,0x4083080161000ca00121c60,0x40670800e1000cc00121cc0]]
set_option maxRecDepth 10000 in
private def witnessesBlock72 : Array (List ℕ) := #[[0x40950801610014800120030,0x824a1001cc001200c0,0x40c50800e1000ca00120520,0x40970801610014800120710,0x41150800a1000ca00120760,0x812a1001ce00120980,0x40c70800e1000ca00120a60,0x40ef0800e10014800120ad0,0x41190800a1000ca00120ee0,0x40f10800e10014800120f30,0x81a610014e00120f80,0x812e1001ce00121080,0x813a3000ca001211e0,0x411b0800a1000ca001212a0,0x40bf0800a2000c800121930,0x82661001cc00121940,0x409d0801610014800121bb0,0x40c10800a2000c800121ed0], [0x42230800a1000c8001200d0,0x83922000ca00120220,0x839a2000ca001206a0,0x82b61000ce00120880,0x839e2000ca001208e0,0x422d0800a1000c800120a30,0x82ba1000ce00120b80,0x83a62000ca00120d60,0x42330800a1000c800120fd0,0x82c21000ce00121180,0x42390800a1000c800121570,0x423b0800a1000c800121750,0x82ce1000ce00121a80,0x83be2000ca00121ae0,0x42410800a1000c800121cf0], [0x8aae1000ca001200a0,0x8aba1000ca001202e0,0x1101ce00120380,0x11024e00120480,0x8aca1000ca001205e0,0x1103ce00120780,0x11064e00120c80,0x8aee1000ca00120ca0,0x1106ce00120d80,0x8b021000ca00121060,0x11094e00121280,0x1109ce00121380,0x8b1e1000ca001215a0,0x110b4e00121680,0x8b261000ca00121720,0x8b2a1000ca001217e0,0x8b321000ca00121960,0x8b3e1000ca00121ba0,0x8b4e1000ca00121ea0,0x110fce00121f80], [0x9c762000c40012004c,0x9c962000c40012028c,0x9cae2000c40012043c,0x8cf2100148001205d0,0x8cfe100148001207b0,0x8d06100148001208f0,0x8d0a10014800120990,0x8d3a10014800121110,0x8d4210014800121250,0x8d46100148001212f0,0x8d5a10014800121610,0x8d72100148001219d0,0x8d7610014800121a70,0x8d8a10014800121d90], [0x9cb22000c400120484,0x9cba2000c400120514,0x9cd62000c40012070c,0x9ce22000c4001207e4,0x9cea2000c400120874,0x9cfa2000c400120994,0x9d0e2000c400120afc,0x9d1e2000c400120c1c,0x9d2a2000c400120cf4,0x9d362000c400120dcc,0x9d622000c4001210e4,0x9d6e2000c4001211bc,0x9d722000c400121204,0x9d862000c40012136c,0x9da22000c400121564,0x9daa2000c4001215f4,0x9db62000c4001216cc,0x9dda2000c400121954,0x9dde2000c40012199c,0x9df22000c400121b04,0x9e0e2000c400121cfc,0x9e162000c400121d8c,0x9e1a2000c400121dd4,0x9e2e2000c400121f3c], [0x80070800a2000cc00122740,0x1000e6000c400122e24,0x1800a2000ce00123280], [0x100162000ce00122080,0x400d1000a3000c800122470,0x40110801a10014e00122880,0x400b0800a4000ca00122ce0,0x2008840071000a1000c800122dd0,0x4013080221001cc00123540,0x40130800a1000d200123a00,0x1001a3000ca00123a60,0x801a1002d400123c00], [0x402f0803e1000ca00122260,0x402b08052100148001226f0,0x802e1000d600122800,0x80523000ce00122980,0x401d080222000ca00122aa0,0x40350800e1000ce00122c80,0x401d080161001cc00122e40,0x401d0801a1000ce00123580,0x40290804a1000ca001238e0,0x200e840070800a2000c800123af0,0x804a1007ce00123d80]]
set_option maxRecDepth 10000 in
private def witnessesBlock73 : Array (List ℕ) := #[[0x40610800a2000ca001221a0,0x40670802210014800122330,0x40490800a1000ce00122380,0x40710801a1000ca001226e0,0x403d0803a100148001228d0,0x808e30014800122ab0,0x80ca1002ce00122b80,0x40470800e2000ca00122f20,0x80761004ce00123080,0x406b0800e1000cc001231c0,0x404f080261000ca001232e0,0x80ce1002ce00123680,0x4059080221000ca00123760,0x404f0802e100148001237d0,0x40650800a2000ca00123820,0x406b0802210014800123870,0x808610044e00123980,0x809230014800123a50,0x80fe2000ce00123b80,0x403b0803e10014800123b90,0x406d0800e1000cc00123c40,0x40490800e2000ca00123ee0,0x40610802610014800123ff0], [0x826e1001cc00122040,0x40fb0800e10014800122510,0x41250800a1000ca00122560,0x813a1001ce00122580,0x81463000ca00122620,0x40d30800e1000ca001229e0,0x40c50800a2000c800122a10,0x40890801a10014800122c90,0x81be10014e00122d80,0x40c70800a2000c800122fb0,0x40a30801610014800123050,0x41010800e10014800123230,0x814e3000ca001233a0,0x408b0801a100148001234b0,0x4089080161000ca00123520,0x81c610014e00123780,0x81461001ce00123a80,0x81ca10014e00123c80,0x408b080161000ca00123d60,0x40a70801610014800123e10,0x41070800e10014800123f50,0x41330800a1000ca00123fa0], [0x82721001cc001223c0,0x83ce2000ca001223e0,0x424b0800a1000c800122650,0x82de1000ce00122680,0x83d62000ca00122860,0x827a1001cc00122ac0,0x42510800a1000c800122bf0,0x82ea1000ce00122f80,0x83e62000ca00123160,0x42570800a1000c800123190,0x42590800a1000c800123370,0x83ee2000ca001235e0,0x82f61000ce00123880,0x425f0800a1000c800123910,0x83fa2000ca00123ca0,0x82fe1000ce00123e80,0x42650800a1000c800123eb0], [0x8b561000ca00122020,0x8b5a1000ca001220e0,0x1110ce00122180,0x11114e00122280,0x8b661000ca00122320,0x11124e00122480,0x1113ce00122780,0x8b7e1000ca001227a0,0x11154e00122a80,0x8b921000ca00122b60,0x8b961000ca00122c20,0x8b9e1000ca00122da0,0x8ba21000ca00122e60,0x11174e00122e80,0x8baa1000ca00122fe0,0x1118ce00123180,0x8bb61000ca00123220,0x111a4e00123480,0x8bce1000ca001236a0,0x8be61000ca00123b20,0x8bf61000ca00123e20,0x111fce00123f80], [0x8d9a10014800122010,0x8da6100148001221f0,0x8db2100148001223d0,0x8dbe100148001225b0,0x8de210014800122b50,0x8dee10014800122d30,0x8df610014800122e70,0x8dfa10014800122f10,0x8e12100148001232d0,0x8e26100148001235f0,0x8e3e100148001239b0,0x8e4e10014800123c30], [0x9e4a2000c400122134,0x9e522000c4001221c4,0x9e622000c4001222e4,0x9e862000c40012256c,0x9e8e2000c4001225fc,0x9e9a2000c4001226d4,0x9e9e2000c40012271c,0x9ea62000c4001227ac,0x9eb22000c400122884,0x9eb62000c4001228cc,0x9ece2000c400122a7c,0x9ed62000c400122b0c,0x9efe2000c400122ddc,0x9f2a2000c4001230f4,0x9f422000c4001232a4,0x9f462000c4001232ec,0x9f4e2000c40012337c,0x9f5a2000c400123454,0x9f662000c40012352c,0x9f6a2000c400123574,0x9f762000c40012364c,0x9fa22000c400123964,0x9fa62000c4001239ac,0x9fb22000c400123a84,0x9fd22000c400123cc4,0x9fde2000c400123d9c,0x9ff62000c400123f4c,0x9ffa2000c400123f94], [0x2800a1000c8001249f0,0x40071000a3000ca00124ea0,0x800a5000ce00125f80], [0x80265000ca00124120,0x20098400b0800a2000c800124bd0,0x2006880070800a1000c800125530,0x40130800e2000ce00125680,0x40131000a4000c40012592c]]
set_option maxRecDepth 10000 in
private def witnessesBlock74 : Array (List ℕ) := #[[0x40350803a1000ca00124060,0x40291000a2000c800124090,0x80563000ce00124480,0x402f080162000ca001245a0,0x40250800e2000cc001246c0,0x4017080221000ce00124a80,0x401f080222000ca001250e0,0x805210074e00125280,0x402b0804a1000ca001254a0,0x401f080161001cc001254c0,0x40290801a2000ca001257a0,0x402f0805210014800125a30,0x200b840070800a1000cc00125bc0,0x401f0801a1000ce00125c80,0x402b1000a2000c800125cb0], [0x40430802e1000ca001241e0,0x80b210034e00124280,0x406d0802210014800124310,0x40670800a2000ca00124360,0x807a1004ce00124380,0x40430800e10014c00124a40,0x80d61002ce00124c80,0x81062000ce00124d80,0x807610015200124e00,0x403d0803e10014800124ef0,0x4053080261000ca00124f60,0x404f0800a1000ce00125080,0x40710800e1000cc00125140,0x407f1000a1000c800125350,0x40530802e10014800125490,0x80da1002ce00125780,0x406508026100148001257b0,0x40710802210014800125850,0x406b0800a2000ca001259e0,0x808e10044e00125b80,0x40430803a10014800125f30], [0x81d210014e00124680,0x41370800a1000ca00124720,0x815a3000ca001247e0,0x814e1001ce00124880,0x40df0800e1000ca00124960,0x410d0800e10014800124c70,0x410f0800e100148001250d0,0x40d30800a2000c800125170,0x40ad08016100148001252b0,0x40e30800e1000ca001253e0,0x81de10014e00125580,0x40e50800e1000ca00125920,0x81e210014e00125a80,0x81663000ca00125c20,0x40950801a10014800125d50,0x815a1001ce00125d80,0x41150800e10014800125df0], [0x42690800a1000c800124270,0x82961001cc00124340,0x426b0800a1000c800124450,0x830a1000ce00124780,0x84122000ca00124a20,0x41390800a1000ca00124ae0,0x84162000ca00124c60,0x82a21001cc00124dc0,0x42770800a1000c800124f90,0x413d0800a1000ca00125260,0x831a1000ce00125380,0x42810800a1000c8001258f0,0x83221000ce00125980,0x42830800a1000c800125ad0,0x42870800a1000c800125e90,0x82b61001cc00125f40], [0x11204e00124080,0x8c0e1000ca001242a0,0x8c1a1000ca001244e0,0x1122ce00124580,0x8c221000ca00124660,0x8c2e1000ca001248a0,0x1124ce00124980,0x8c3e1000ca00124ba0,0x8c461000ca00124d20,0x11274e00124e80,0x8c561000ca00125020,0x1128ce00125180,0x8c5e1000ca001251a0,0x112a4e00125480,0x8c7a1000ca001256e0,0x8c821000ca00125860,0x112c4e00125880,0x8c8e1000ca00125aa0,0x8c921000ca00125b60,0x8c9a1000ca00125ce0,0x112f4e00125e80,0x8ca61000ca00125f20], [0x8e6e10014800124130,0x8e8a10014800124590,0x8e9610014800124770,0x8e9e100148001248b0,0x8ea210014800124950,0x8eaa10014800124a90,0x8eae10014800124b30,0x8ec210014800124e50,0x8eda10014800125210,0x8ee6100148001253f0,0x8ef2100148001255d0,0x8f1610014800125b70,0x8f1a10014800125c10,0x8caa1000ca00125fe0], [0xa0062000c40012406c,0xa01e2000c40012421c,0xa03e2000c40012445c,0xa0422000c4001244a4,0xa04a2000c400124534,0xa0562000c40012460c,0xa0722000c400124804,0xa07a2000c400124894,0xa07e2000c4001248dc,0xa0a22000c400124b64,0xa0d22000c400124ec4,0xa0e62000c40012502c,0xa0f22000c400125104,0xa0f62000c40012514c,0xa10a2000c4001252b4,0xa10e2000c4001252fc,0xa1222000c400125464,0xa1262000c4001254ac,0xa13a2000c400125614,0xa1462000c4001256ec,0xa14a2000c400125734,0xa15e2000c40012589c,0xa1622000c4001258e4,0xa1762000c400125a4c,0xa1822000c400125b24,0xa1922000c400125c44], [0x40072000a2000c40012673c,0x40070800a2000d200127600,0x1800a4000c8001278d0,0x800e6000ca00127de0,0x10015e00128000]]
set_option maxRecDepth 10000 in
private def witnessesBlock75 : Array (List ℕ) := #[[0x400d0800e3000cc00126640,0x40130801a10014e00126980,0x20088400d0800a2000c800126d90,0x2009840071000a1000c800126f70,0x801a1000d800127000,0x40111000e1000cc001270c0,0x800b0800e1000cc00127b40,0x40111000a1000ce00127d80], [0x806a1005ce00126180,0x200f840070800a2000c800126250,0x4025080161000ce00126280,0x40350804a100148001264d0,0x40350803e1000ca00126820,0x401d080262000ca00126be0,0x802e3000d000126d00,0x1005e2000c600126d48,0x805610074e00126f80,0x402b0801a2000ca001274e0,0x402f0805610014800127790,0x40170801610014e00127880,0x805e3000ce00127a80,0x80521007ce00127b80], [0x807a10015200126200,0x40670802610014800126390,0x40470802e1000ca00126460,0x406d0800a2000ca00126520,0x40831000a1000c800126610,0x809e30014800126930,0x4061080221000ca00126a60,0x407f0801a1000ca00126b20,0x403b0800e1000ce00126b80,0x809210044e00126c80,0x40470800e10014c00126d40,0x80e21002ce00126d80,0x404f0800e2000ca00126e20,0x40530800a1000ce00126e80,0x40490802e1000ca001275a0,0x80c210034e00127680,0x4059080261000ca00127a20,0x406b0802610014800127b50,0x40710800a2000ca00127ba0,0x80861004ce00127c80,0x40830801a1000ca00127ea0,0x40490800e10014c00127ec0,0x40590802e10014800127fb0], [0x816a3000ca001262e0,0x40e90800e1000ca001263a0,0x40970801a10014800126570,0x4095080161000ca001266a0,0x41190800e100148001266b0,0x40b30801610014800126750,0x81122000ce00126880,0x411b0800e10014800126b10,0x40b50801610014800126e30,0x4097080161000ca00126ee0,0x81162000ce00127180,0x81661001ce00127280,0x40df0800a2000c800127330,0x40ef0800e1000ca00127360,0x81f610014e00127380,0x40f10800e1000ca001278a0,0x816a1001ce00127980,0x409d0801a10014800127dd0,0x40e30800a2000c800127e70], [0x843a2000ca001260a0,0x82ba1001cc001262c0,0x428d0800a1000c800126430,0x83321000ce00126580,0x84462000ca00126760,0x82c21001cc001269c0,0x42930800a1000c8001269d0,0x42950800a1000c800126bb0,0x414b0800a1000ca00126ca0,0x845a2000ca001272a0,0x82ce1001cc00127440,0x83461000ce00127480,0x42a10800a1000c8001276f0,0x834a1000ce00127780,0x41510800a1000ca001277e0,0x84662000ca00127960,0x42a50800a1000c800127ab0], [0x11304e00126080,0x1131ce00126380,0x11334e00126680,0x1133ce00126780,0x11354e00126a80,0x11384e00127080,0x113ace00127580,0x113f4e00127e80,0x113fce00127f80], [0x8f3a10014800126110,0x8f3e100148001261b0,0x8cb61000ca00126220,0x8cca1000ca001265e0,0x8f6a10014800126890,0x8f7610014800126a70,0x8f8610014800126cf0,0x8cf21000ca00126d60,0x8f9210014800126ed0,0x8cfe1000ca00126fa0,0x8f9a10014800127010,0x8f9e100148001270b0,0x8d061000ca00127120,0x8d0a1000ca001271e0,0x8fa6100148001271f0,0x8fb610014800127470,0x8fc210014800127650,0x8fd610014800127970,0x8fda10014800127a10,0x8d3a1000ca00127ae0,0x8d421000ca00127c60,0x8d461000ca00127d20,0x8fee10014800127d30], [0xa1ce2000c40012607c,0xa1e22000c4001261e4,0xa1e62000c40012622c,0xa1fa2000c400126394,0xa20a2000c4001264b4,0xa2162000c40012658c,0xa22a2000c4001266f4,0xa24e2000c40012697c,0xa25a2000c400126a54,0xa2722000c400126c04,0xa28a2000c400126db4,0xa28e2000c400126dfc,0xa2b22000c400127084,0xa2be2000c40012715c,0xa2c62000c4001271ec,0xa2d22000c4001272c4,0xa2de2000c40012739c,0xa3022000c400127624,0xa3062000c40012766c,0xa31a2000c4001277d4,0xa3362000c4001279cc,0xa3422000c400127aa4,0xa34a2000c400127b34,0xa34e2000c400127b7c,0xa3562000c400127c0c,0xa3862000c400127f6c,0xa38a2000c400127fb4]]
set_option maxRecDepth 10000 in
private def witnessesBlock76 : Array (List ℕ) := #[[0x40071800a1000cc00129040,0x1000e3000ce00129580,0x800e1000da0012a000], [0x1001a5000c4001281ac,0x400d080162000ce00128380,0x4011080161001ce00128e80,0x400d0800a4000ca00129220,0x400b0800a1000d400129400,0x802240014800129810,0x3002ce00129980,0x2008840070800a2000ca00129d60,0x20068400b1000a1000c800129e50], [0x40290800e2000cc001285c0,0x40250800e10014e00128780,0x402f0804a1000ca00128c20,0x401d0800a2000ce00128c80,0x4017080261000ce00128f80,0x4035080162000ca00128fe0,0x401d0801a1001cc001293c0,0x402f1000a2000c8001294f0,0x402b080521000ca00129520,0x401f080262000ca001296a0,0x80561007ce00129a80], [0x403d0800e1000ce00128080,0x403b0803a1000ca001281a0,0x40470803a10014800128370,0x4065080221000ca001283e0,0x406d0802610014800128730,0x80a630014800128870,0x40430803e10014800128910,0x40530800e2000ca00128da0,0x80ca10034e00129080,0x4067080221000ca001290a0,0x40490803a10014800129590,0x403d0803a1000ca00129760,0x407f0800e1000cc00129ac0,0x40590800a1000ce00129b80,0x80ce10034e00129d80,0x808610015200129e00,0x40710802610014800129ef0,0x809e10044e00129f80], [0x41250800e100148001280f0,0x40891000a1000c800128230,0x820210014e00128280,0x40e50800a2000c800128410,0x817e3000ca001284a0,0x409d080161000ca001287a0,0x81823000ca00128b60,0x408b1000a1000c800128b90,0x40e90800a2000c800128f50,0x40bf0801610014800129090,0x820e10014e00129180,0x40fb0800e1000ca001292e0,0x40a30801a10014800129630,0x40c10801610014800129770,0x818a3000ca001298e0,0x40890801a1000ca00129be0,0x817e1001ce00129c80,0x812a2000ce00129e80,0x41330800e10014800129f90,0x818e3000ca00129fa0], [0x84722000ca00128020,0x42ab0800a1000c800128050,0x82de1001cc00128240,0x84762000ca00128260,0x835e1000ce00128680,0x42b30800a1000c8001287d0,0x84822000ca00128920,0x83621000ce00128980,0x415b0800a1000ca00128aa0,0x82ea1001cc00128cc0,0x415d0800a1000ca00128e60,0x42bd0800a1000c800129130,0x836e1000ce00129280,0x84962000ca00129460,0x41610800a1000ca001295e0,0x82f61001cc00129740,0x83761000ce00129880,0x42c50800a1000c8001298b0,0x84a22000ca00129b20,0x82fe1001cc00129e40], [0x1140ce00128180,0x11424e00128480,0x1142ce00128580,0x11444e00128880,0x11454e00128a80,0x1145ce00128b80,0x1146ce00128d80,0x1149ce00129380,0x114a4e00129480,0x114bce00129780], [0x8d5a1000ca001280e0,0x900a10014800128190,0x901e100148001284b0,0x8d721000ca00128560,0x8d761000ca00128620,0x902a10014800128690,0x8d8a1000ca001289e0,0x904210014800128a50,0x904610014800128af0,0x904e10014800128c30,0x905210014800128cd0,0x8d9a1000ca00128ce0,0x8da61000ca00128f20,0x906610014800128ff0,0x8db21000ca00129160,0x8dbe1000ca001293a0,0x907e100148001293b0,0x908210014800129450,0x90a210014800129950,0x90a6100148001299f0,0x8de21000ca00129a60,0x90b210014800129bd0,0x8dee1000ca00129ca0,0x90ba10014800129d10,0x90be10014800129db0,0x8df61000ca00129e20,0x8dfa1000ca00129ee0]]
set_option maxRecDepth 10000 in
private def witnessesBlock77 : Array (List ℕ) := #[[0xa3a22000c400128164,0xa3ae2000c40012823c,0xa3ce2000c40012847c,0xa3de2000c40012859c,0xa3ea2000c400128674,0xa3f62000c40012874c,0xa41a2000c4001289d4,0xa43a2000c400128c14,0xa43e2000c400128c5c,0xa4462000c400128cec,0xa4522000c400128dc4,0xa4562000c400128e0c,0xa4622000c400128ee4,0xa46e2000c400128fbc,0xa4822000c400129124,0xa48e2000c4001291fc,0xa4a62000c4001293ac,0xa4be2000c40012955c,0xa4e22000c4001297e4,0xa4e62000c40012982c,0xa4f22000c400129904,0xa4fa2000c400129994,0xa51e2000c400129c1c,0xa52e2000c400129d3c], [0x1000a3000d00012a300,0x2000a2000ca0012bf20], [0x1801a1001480012ae90,0x801630014e0012af80,0x20098400d0800a2000c80012b6b0,0x40131000e1000cc0012ba40], [0x4029080161000ce0012a480,0x402b0800e2000cc0012a540,0x4035080521001480012a710,0x805e10074e0012a980,0x4017080221001cc0012ac40,0x402f0801a2000ca0012af60,0x40170800a1000d20012b200,0x803a1000d60012b800,0x401f0800a2000ce0012b980,0x802e5000ca0012baa0], [0x808e1004ce0012a280,0x407f080221001480012a2b0,0x80761005ce0012a680,0x404f0802e1000ca0012a960,0x406b080221000ca0012aa20,0x403b0804a1001480012aa30,0x403b0803e1000ca0012ade0,0x40830800e1000cc0012afc0,0x40470803e1001480012afd0,0x4061080261000ca0012b320,0x404f0800e10014c0012b340,0x80921004ce0012b580,0x406d080221000ca0012b6e0,0x80b23001480012b750,0x80d610034e0012b780,0x4083080221001480012b7f0,0x40610802e1001480012b930,0x80fe1002ce0012ba80,0x40590800e2000ca0012bce0,0x807a1005ce0012bd80,0x40430800e1000ce0012bf80], [0x40ef0800a2000c80012a030,0x40a3080161000ca0012a060,0x821a10014e0012a080,0x41010800e1000ca0012a2a0,0x81821001ce0012a380,0x40c5080161001480012a530,0x821e10014e0012a580,0x408b0801a1000ca0012a5a0,0x40f10800a2000c80012a5d0,0x40a70801a1001480012a670,0x812e2000ce0012a780,0x41370800e1001480012a850,0x40c7080161001480012ac10,0x40a7080161000ca0012b0e0,0x818a1001ce0012b180,0x41070800e1000ca0012b260,0x822a10014e0012b480,0x818e1001ce0012b880,0x40951000a1000c80012ba70,0x823210014e0012be80,0x40ad0801a1001480012bed0], [0x41670800a1000ca0012a120,0x83821000ce0012a180,0x84ae2000ca0012a1e0,0x42cf0800a1000c80012a210,0x84b22000ca0012a420,0x830a1001cc0012a8c0,0x84be2000ca0012aae0,0x41390800e1001480012acb0,0x83921000ce0012ad80,0x416f0800a1000ca0012b020,0x84ca2000ca0012b1a0,0x839a1000ce0012b380,0x413d0800e1001480012b570,0x84d22000ca0012b620,0x839e1000ce0012b680,0x831a1001cc0012b6c0,0x84d62000ca0012b860,0x41750800a1000ca0012bb60,0x83a61000ce0012bc80,0x83221001cc0012bdc0], [0x11544e0012a880,0x42d70800a1000c80012a990,0x1155ce0012ab80,0x11574e0012ae80,0x42dd0800a1000c80012af30,0x11594e0012b280,0x42e30800a1000c80012b4d0,0x42e70800a1000c80012b890,0x115dce0012bb80]]
set_option maxRecDepth 10000 in
private def witnessesBlock78 : Array (List ℕ) := #[[0x90d21001480012a0d0,0x90e21001480012a350,0x8e121000ca0012a360,0x8e261000ca0012a720,0x91061001480012a8f0,0x8e3e1000ca0012aba0,0x8e4e1000ca0012aea0,0x91361001480012b070,0x913e1001480012b1b0,0x914a1001480012b390,0x8e6e1000ca0012b4a0,0x915a1001480012b610,0x8e8a1000ca0012b9e0,0x917a1001480012bb10,0x917e1001480012bbb0,0x8e961000ca0012bc20,0x91861001480012bcf0,0x8e9e1000ca0012bda0,0x8ea21000ca0012be60,0x91961001480012bf70,0x8eaa1000ca0012bfe0], [0xa55e2000c40012a09c,0xa5662000c40012a12c,0xa56a2000c40012a174,0xa5722000c40012a204,0xa57e2000c40012a2dc,0xa5822000c40012a324,0xa59a2000c40012a4d4,0xa5a22000c40012a564,0xa5be2000c40012a75c,0xa5fa2000c40012ab94,0xa60e2000c40012acfc,0xa61a2000c40012add4,0xa6322000c40012af84,0xa64e2000c40012b17c,0xa65a2000c40012b254,0xa66e2000c40012b3bc,0xa6862000c40012b56c,0xa68a2000c40012b5b4,0xa6922000c40012b644,0xa69e2000c40012b71c,0xa6ae2000c40012b83c,0xa6ba2000c40012b914,0xa6ce2000c40012ba7c,0xa6d22000c40012bac4,0xa6da2000c40012bb54,0xa6f62000c40012bd4c,0xa7022000c40012be24,0xa70e2000c40012befc,0xa7162000c40012bf8c], [0x40070800a4000cc0012c4c0,0x800e8000c40012cd9c], [0x40131000a1000ce0012c880,0x40111000a3000c80012cd30,0x4013080161001ce0012db80], [0x401f0801a1001cc0012c140,0x4025080222000ca0012c3a0,0x402b080161000ce0012c580,0x200b8400b0800a2000c80012c790,0x4035080561001480012c830,0x4025080161001cc0012c840,0x806a3000ce0012cb80,0x40290800e10014e0012cd80,0x40250801a1000ce0012d180,0x402f080521000ca0012d2a0,0x40170800e2000ce0012d480,0x40171000a4000c40012d7bc,0x2012840070800a2000c80012d870,0x805e1007ce0012d880,0x40350804a1000ca0012df60], [0x403d0804a1001480012c150,0x80a610044e0012c180,0x40490803e1001480012c330,0x80da10034e0012c480,0x403d0803e1000ca0012c520,0x808e1001520012c600,0x407f0800a2000ca0012ca60,0x40530802e1000ca0012cbe0,0x404f0803a1001480012cbf0,0x4065080261000ca0012cfa0,0x4071080221000ca0012d060,0x81061002ce0012d080,0x40650802e1001480012d5f0,0x40530800e10014c0012d640,0x40610800a1000ce0012d780,0x40430803a1000ca0012d8a0,0x80921001520012da00,0x403b080162000ca0012da20,0x4067080261000ca0012dde0,0x80e210034e0012de80], [0x40fb0800a2000c80012c1f0,0x410d0800e1000ca0012c220,0x813a2000ce0012c280,0x823610014e0012c380,0x40971000a1000c80012c3d0,0x410f0800e1000ca0012c760,0x81a63000ca0012c820,0x40ad080161000ca0012c9a0,0x40890800e1000cc0012cf40,0x41010800a2000c80012d2d0,0x40d3080161001480012d550,0x40950801a1000ca0012d660,0x41150800e1000ca0012d720,0x40b30801a1001480012d730,0x4089080221001480012d7d0,0x408b0800e1000cc0012d9c0,0x824a10014e0012dc80,0x81462000ce0012dd80,0x40b50801a1001480012df50,0x409d1000a1000c80012dff0], [0x84ee2000ca0012c5e0,0x417b0800a1000ca0012c6a0,0x83321001cc0012cbc0,0x417f0800a1000ca0012ce20,0x83be1000ce0012ce80,0x85022000ca0012d120,0x85062000ca0012d360,0x414b0800e1001480012d410,0x850e2000ca0012d7e0,0x41850800a1000ca0012d960,0x83ce1000ce0012da80,0x83461001cc0012dd40,0x851a2000ca0012dea0]]
set_option maxRecDepth 10000 in
private def witnessesBlock79 : Array (List ℕ) := #[[0x42ef0800a1000c80012c010,0x11604e0012c080,0x42f50800a1000c80012c5b0,0x1163ce0012c780,0x42f90800a1000c80012c970,0x1164ce0012c980,0x11654e0012ca80,0x11664e0012cc80,0x1167ce0012cf80,0x43010800a1000c80012d0f0,0x1169ce0012d380,0x43050800a1000c80012d4b0,0x116ace0012d580,0x116b4e0012d680,0x116cce0012d980,0x116fce0012df80], [0x8eae1000ca0012c0a0,0x8ec21000ca0012c460,0x91b61001480012c470,0x91ba1001480012c510,0x91c21001480012c650,0x91d21001480012c8d0,0x8eda1000ca0012c8e0,0x91de1001480012cab0,0x8ee61000ca0012cb20,0x91ea1001480012cc90,0x8ef21000ca0012cd60,0x91f21001480012cdd0,0x920a1001480012d190,0x920e1001480012d230,0x8f161000ca0012d420,0x8f1a1000ca0012d4e0,0x923a1001480012d910,0x8f3a1000ca0012dae0,0x92461001480012daf0,0x924a1001480012db90,0x8f3e1000ca0012dba0,0x92561001480012dd70,0x925e1001480012deb0], [0xa7222000c40012c064,0xa7262000c40012c0ac,0xa73a2000c40012c214,0xa73e2000c40012c25c,0xa75e2000c40012c49c,0xa7762000c40012c64c,0xa7862000c40012c76c,0xa7aa2000c40012c9f4,0xa7b22000c40012ca84,0xa7be2000c40012cb5c,0xa7d62000c40012cd0c,0xa7da2000c40012cd54,0xa7e62000c40012ce2c,0xa7f22000c40012cf04,0xa7fe2000c40012cfdc,0xa8362000c40012d3cc,0xa8422000c40012d4a4,0xa85e2000c40012d69c,0xa8662000c40012d72c,0xa8762000c40012d84c,0xa88a2000c40012d9b4,0xa89a2000c40012dad4,0xa8b22000c40012dc84,0xa8d62000c40012df0c,0xa8de2000c40012df9c,0xa8e22000c40012dfe4], [0x1800a1000d20012ee00,0x1000a5000ca0012f760], [0x80264001480012e630,0x80221002d40012ec00,0x2009840070800a2000ca0012ec20,0x20068400b0800e1000cc0012eec0,0x1001a2000ce0012f880,0x800b0800a4000c40012fdb4], [0x401d080221000ce0012e380,0x402f0800e2000cc0012e440,0x803e1000d60012e800,0x40351000a2000c80012e950,0x40170801a10014e0012eb80,0x401d0802e2000ca0012ee60,0x402b0800e10014e0012f080,0x200b840071000a1000c80012f2b0,0x402f080561000ca0012f5e0,0x805210094e0012f680,0x200e840070800a1000cc0012f940,0x4017080261001cc0012fcc0], [0x40830800a2000ca0012e0e0,0x40670802e1001480012e450,0x40470800e1000ce0012e980,0x809e1004ce0012ee80,0x40530803a1001480012f030,0x407f080261001480012f210,0x403d080162000ca0012f2e0,0x403b080521001480012f3f0,0x80b210044e0012f480,0x40650800a1000ce0012f580,0x80c23001480012f5d0,0x406b080261000ca0012fa60,0x40610800e2000ca0012fbe0,0x404f0803e1001480012fd50,0x40490800e1000ce0012fe80,0x40590802e1000ca0012ffa0], [0x40970801a1000ca0012e020,0x41190800e1000ca0012e1a0,0x40b3080161000ca0012e260,0x408b080221001480012e270,0x81a61001ce0012e280,0x41070800a2000c80012e3b0,0x411b0800e1000ca0012e6e0,0x40b5080161000ca0012eaa0,0x814e2000ce0012ef80,0x81be3000ca0012f0a0,0x81121002ce0012f180,0x410d0800a2000c80012f490,0x410f0800a2000c80012fa30,0x40a31000a1000c80012fc10,0x81161002ce0012fc80,0x409d0801a1000ca0012fd60,0x81c63000ca0012fe20,0x40df080161001480012fe90,0x826610014e0012ff80]]
set_option maxRecDepth 10000 in
private def witnessesBlock80 : Array (List ℕ) := #[[0x83d61000ce0012e080,0x834a1001cc0012e0c0,0x41510800e1001480012e130,0x85262000ca0012e560,0x852a2000ca0012e7a0,0x418d0800a1000ca0012e860,0x83e61000ce0012ec80,0x41910800a1000ca0012efe0,0x835e1001cc0012f240,0x83ee1000ce0012f280,0x85422000ca0012f520,0x83621001cc0012f5c0,0x415b0800e1001480012f710,0x854a2000ca0012f9a0,0x415d0800e1001480012fb70,0x83fa1000ce0012fb80,0x41990800a1000ca0012fee0], [0x43130800a1000c80012e1d0,0x11724e0012e480,0x1172ce0012e580,0x1173ce0012e780,0x11744e0012e880,0x11754e0012ea80,0x431d0800a1000c80012eb30,0x1176ce0012ed80,0x1179ce0012f380,0x43290800a1000c80012f670,0x432b0800a1000c80012f850,0x117cce0012f980,0x117ece0012fd80], [0x926a1001480012e090,0x8f6a1000ca0012e3e0,0x92861001480012e4f0,0x8f761000ca0012e620,0x92921001480012e6d0,0x929a1001480012e810,0x929e1001480012e8b0,0x8f861000ca0012e920,0x92aa1001480012ea90,0x8f921000ca0012eb60,0x92b21001480012ebd0,0x8f9a1000ca0012ece0,0x8f9e1000ca0012eda0,0x92be1001480012edb0,0x8fa61000ca0012ef20,0x92d61001480012f170,0x8fb61000ca0012f220,0x92e21001480012f350,0x8fc21000ca0012f460,0x92ee1001480012f530,0x8fd61000ca0012f820,0x8fda1000ca0012f8e0,0x930a1001480012f990,0x93121001480012fad0,0x8fee1000ca0012fca0,0x931e1001480012fcb0], [0xa8ea2000c40012e074,0xa91a2000c40012e3d4,0xa9322000c40012e584,0xa93e2000c40012e65c,0xa9422000c40012e6a4,0xa9622000c40012e8e4,0xa96e2000c40012e9bc,0xa97a2000c40012ea94,0xa9962000c40012ec8c,0xa9aa2000c40012edf4,0xa9c62000c40012efec,0xa9ce2000c40012f07c,0xaa0a2000c40012f4b4,0xaa162000c40012f58c], [0xaa222000c40012f664,0xaa2e2000c40012f73c,0xaa3e2000c40012f85c,0xaa4a2000c40012f934,0xaa522000c40012f9c4,0xaa562000c40012fa0c,0xaa6e2000c40012fbbc,0xaa7a2000c40012fc94,0xaa822000c40012fd24,0xaa862000c40012fd6c,0xaa922000c40012fe44], [0x1800e2000cc001303c0,0x40071000a2000ce00131380,0x2000a4000c400131704], [0x400b0800e10015200130200,0x400b1800a2000c800130570,0x40110801a1001ce00130580,0x2008880070800a1000c800130cf0,0x80162000d600131800,0x4005840070800a1000c800131a10], [0x806a10074e00130080,0x40350801a2000ca00130720,0x402f080161000ce00130780,0x40350805e10014800130a70,0x803a3000d000130f00,0x4029080222000ca00131020,0x801d0800a1000c800131470,0x4029080161001cc00131540,0x1006a2000c600131608,0x401f080221000ce00131680,0x4025080262000ca001316e0,0x1002e1000ce00131980,0x805610094e00131b80,0x401d0801610014e00131d80,0x40290801a1000ce00131f80]]
set_option maxRecDepth 10000 in
private def witnessesBlock81 : Array (List ℕ) := #[[0x406b0802e10014800130110,0x80861005ce00130280,0x40470803a1000ca00130420,0x40670800a1000ce00130480,0x40430804a100148001306b0,0x406d080261000ca001308a0,0x408308026100148001309d0,0x40590800e10014c00130ac0,0x40430803e1000ca00130ae0,0x403d0805210014800130d90,0x406d0802e10014800130f70,0x80a61004ce00131480,0x80ca30014800131510,0x809e10015200131600,0x403b08056100148001318d0,0x40490803a1000ca001319e0,0x40650800e2000ca00131b60,0x80763000ce00131c80], [0x41250800e1000ca00130120,0x40890800a2000ca001302a0,0x81ca3000ca001304e0,0x40bf0801a100148001307f0,0x826e10014e00130980,0x815a2000ce00130a80,0x41150800a2000c800130b10,0x40e30801610014800130c50,0x81be1001ce00130c80,0x408b0800a2000ca00130de0,0x40950800e1000cc00130e40,0x40a71000a1000c800130ed0,0x40c10801a10014800131010,0x81d23000ca00131260,0x40e50801610014800131330,0x40bf080161000ca001313e0,0x41190800a2000c800131650,0x40950802210014800131790,0x40970800e1000cc001318c0,0x81c61001ce00131a80,0x40a30801a1000ca00131aa0,0x411b0800a2000c800131bf0,0x40c1080161000ca00131c20], [0x836e1001cc00130040,0x85562000ca00130060,0x41610800e10014800130430,0x83761001cc00130740,0x85662000ca00130960,0x84121000ce00130d80,0x827210014e00130e80,0x84161000ce00131080,0x41670800e10014800131150,0x41a30800a1000ca001311a0,0x83821001cc001311c0,0x857a2000ca001314a0,0x41a50800a1000ca00131560,0x827a10014e00131880,0x858a2000ca00131da0,0x83921001cc00131fc0], [0x43350800a1000c8001301b0,0x1181ce00130380,0x43370800a1000c800130390,0x11834e00130680,0x433b0800a1000c800130750,0x11844e00130880,0x433d0800a1000c800130930,0x1185ce00130b80,0x1187ce00130f80,0x1188ce00131180,0x43470800a1000c800131290,0x118ace00131580,0x118bce00131780,0x118f4e00131e80,0x43550800a1000c800131fb0], [0x933610014800130070,0x900a1000ca001301e0,0x9346100148001302f0,0x9352100148001304d0,0x901e1000ca001305a0,0x935a10014800130610,0x902a1000ca001307e0,0x90421000ca00130c60,0x90461000ca00130d20,0x938e10014800130e30,0x904e1000ca00130ea0,0x90521000ca00130f60,0x90661000ca00131320,0x93b2100148001313d0,0x93c6100148001316f0,0x907e1000ca001317a0,0x90821000ca00131860,0x93d610014800131970,0x93de10014800131ab0,0x93ea10014800131c90,0x93ee10014800131d30,0x90a21000ca00131e60,0x93fa10014800131f10,0x90a61000ca00131f20], [0xaabe2000c40013015c,0xaaca2000c400130234,0xaace2000c40013027c,0xaad62000c40013030c,0xaafa2000c400130594,0xaafe2000c4001305dc,0xab062000c40013066c,0xab1e2000c40013081c,0xab222000c400130864,0xab2e2000c40013093c,0xab362000c4001309cc,0xab6a2000c400130d74,0xab762000c400130e4c,0xab822000c400130f24,0xab8a2000c400130fb4,0xab9a2000c4001310d4,0xabae2000c40013123c,0xabee2000c4001316bc,0xac0e2000c4001318fc,0xac122000c400131944,0xac1e2000c400131a1c,0xac262000c400131aac,0xac2a2000c400131af4,0xac322000c400131b84,0xac362000c400131bcc,0xac4a2000c400131d34,0xac662000c400131f2c], [0x8000ca00133420], [0x40072000a1000c800133450,0x80070800a3000ca00133ae0]]
set_option maxRecDepth 10000 in
private def witnessesBlock82 : Array (List ℕ) := #[[0x40131000a3000c800132190,0x40110800e3000cc00132340,0x20068400b0800a2000ca00132460,0x40130802210014e00132780,0x400b1000e1000ce00132880,0x801a30014e00132c80,0x80110800a2000c800132cd0,0x1801a1000ca001337e0], [0x401f0802e2000ca00132220,0x2014840070800a2000c800132730,0x200f840070800a1000cc00132dc0,0x4035080521000ca00132ee0,0x806a1007ce00133580,0x402b080222000ca00133660,0x402f0800e10014e00133680,0x401d080261000ce00133a80,0x402b080161001cc00133bc0], [0x406b0800a1000ce00132280,0x40530803e10014800132410,0x80ce300148001324b0,0x4071080261000ca00132520,0x40590803a10014800132690,0x407f080221000ca001329a0,0x40670800e2000ca00132b20,0x40710802e10014800132c30,0x808e1005ce00133080,0x406d0800a1000ce00133180,0x403b0804a1000ca001332a0,0x403d08056100148001333b0,0x40470804a100148001334f0,0x807a3000ce00133780,0x80c210044e00133880,0x40470803e1000ca00133960,0x80fe10034e00133980,0x4043080162000ca00133d20,0x404f0800e1000ce00133d80,0x403b1000a2000c800133db0,0x80a610015200133e00], [0x40c50801a10014800132050,0x40e908016100148001320f0,0x81ca1001ce00132180,0x40970802210014800132230,0x81662000ce00132580,0x41330800e1000ca001325e0,0x81de3000ca001326a0,0x40c70801a10014800132870,0x40ad1000a1000c800132af0,0x40c5080161000ca00132ca0,0x81e23000ca00132d60,0x40890802610014800132d70,0x40a70801a1000ca00132e20,0x816a2000ce00132e80,0x81d21001ce00132f80,0x41370800e1000ca00133060,0x812a1002ce00133380,0x40c7080161000ca001334e0,0x40ef0801610014800133590,0x41250800a2000c800133810,0x409d0800e1000cc00133840,0x408b0802610014800133950,0x40f10801610014800133c70,0x812e1002ce00133e80], [0x416f0800e100148001322d0,0x839a1001cc001326c0,0x41af0800a1000ca00132820,0x859e2000ca001328e0,0x839e1001cc00132a40,0x843a1000ce00132b80,0x41b10800a1000ca00132be0,0x41750800e10014800132ff0,0x83a61001cc00133140,0x84461000ce00133480,0x41390800e1000ca001335a0,0x41b70800a1000ca00133720,0x829610014e00133b80,0x417b0800e10014800133d10,0x41bb0800a1000ca00133ea0], [0x11904e00132080,0x43590800a1000c800132370,0x1191ce00132380,0x11924e00132480,0x435b0800a1000c800132550,0x11934e00132680,0x435f0800a1000c800132910,0x1194ce00132980,0x85ae2000ca001331e0,0x436d0800a1000c800133630,0x85ba2000ca001338a0,0x43710800a1000c8001339f0,0x43730800a1000c800133bd0,0x85c62000ca00133f60,0x43770800a1000c800133f90], [0x90b21000ca00132160,0x90ba1000ca001322e0,0x90be1000ca001323a0,0x9426100148001325f0,0x90d21000ca00132760,0x943e100148001329b0,0x944210014800132a50,0x90e21000ca00132a60,0x11954e00132a80,0x1196ce00132d80,0x946210014800132f50,0x91061000ca00133120,0x9472100148001331d0,0x11994e00133280,0x947a10014800133310,0x9492100148001336d0,0x91361000ca00133a20,0x94ae10014800133b30,0x913e1000ca00133ba0,0x119e4e00133c80,0x914a1000ca00133de0,0x94c210014800133e50,0x94c610014800133ef0,0x119fce00133f80], [0xac722000c400132004,0xac7a2000c400132094,0xac8a2000c4001321b4,0xac9e2000c40013231c,0xacaa2000c4001323f4,0xacd22000c4001326c4,0xacda2000c400132754,0xacde2000c40013279c,0xacea2000c400132874,0xad262000c400132cac,0xad2e2000c400132d3c,0xad3e2000c400132e5c,0xad522000c400132fc4,0xad5e2000c40013309c,0xad6a2000c400133174,0xad7a2000c400133294,0xad862000c40013336c,0xad9e2000c40013351c,0xada62000c4001335ac,0xadb22000c400133684,0xadb62000c4001336cc,0xadc22000c4001337a4,0xadca2000c400133834,0xadd62000c40013390c,0xadda2000c400133954,0xadee2000c400133abc,0xadf22000c400133b04,0xae122000c400133d44,0xae1e2000c400133e1c]]
set_option maxRecDepth 10000 in
private def witnessesBlock83 : Array (List ℕ) := #[[0x40070800a1000d600134800,0x800e5000ce00135280,0x1800e10014e00135980], [0x400b0800a5000c800134350,0x80261002d400134400,0x4011080162000ce00134980,0x40110800a4000ca00135ca0], [0x40250800a2000ce00134080,0x40350800e2000cc001342c0,0x803e3000d000134500,0x402b0801a1000ce00134680,0x200b8400d0800a2000c8001348f0,0x40250801a1001cc001349c0,0x40171000e1000cc00134d40,0x2015840070800a2000c800134e90,0x401f0801610014e00135480,0x4035080561000ca001356a0,0x40171000a1000ce00135e80,0x401d080221001cc00135ec0], [0x4083080221000ca00134320,0x80d6300148001343f0,0x40610802e1000ca001344a0,0x80921005ce00134780,0x406b0800e2000ca00134aa0,0x40490804a10014800134c10,0x80b21004ce00134d80,0x403d0804a1000ca00134e60,0x40710800a1000ce00134f80,0x40490803e1000ca001350a0,0x40610800e10014c001350c0,0x810610034e00135380,0x80da30014800135390,0x807610074e00135780,0x403d1000a2000c8001359d0,0x406d0800e2000ca00135a60,0x40430805210014800135a70,0x80ca10044e00135a80,0x404f0803a1000ca00135b20,0x40590803e10014800135e30,0x403b0801a2000ca00135ee0], [0x409d0802210014800134210,0x81de1001ce00134480,0x40950800a2000ca00134620,0x40b31000a1000c800134710,0x40ad0801a1000ca00134b60,0x81e21001ce00134b80,0x81f63000ca00134f20,0x40b51000a1000c800135070,0x40970800a2000ca00135160,0x40a30800e1000cc001357c0,0x40d30801a10014800135930,0x817e2000ce00135b80,0x40fb0801610014800135ed0,0x41330800a2000c800135f70,0x813a1002ce00135f80], [0x413d0800e1000ca00134020,0x845a1000ce00134380,0x417f0800e100148001345d0,0x83be1001cc00134640,0x41c10800a1000ca001349e0,0x82a210014e00134a80,0x84661000ce00134c80,0x41850800e100148001352f0,0x83ce1001cc00135440,0x84721000ce00135580,0x84761000ce00135880,0x41c90800a1000ca001358e0,0x83d61001cc00135b40], [0x85ce2000ca001343e0,0x85de2000ca00134ce0,0x438b0800a1000c800135250,0x85ea2000ca001353a0,0x438f0800a1000c800135610,0x85f22000ca00135820,0x43970800a1000c800135d90], [0x94ce10014800134030,0x915a1000ca001340e0,0x11a0ce00134180,0x11a14e00134280,0x94de100148001342b0,0x94ea10014800134490,0x94f610014800134670,0x917a1000ca001346e0,0x917e1000ca001347a0,0x94fe100148001347b0,0x950210014800134850,0x91861000ca00134920,0x950a10014800134990,0x951610014800134b70,0x91961000ca00134c20,0x952610014800134df0,0x11a74e00134e80,0x952e10014800134f30,0x953210014800134fd0,0x11a84e00135080,0x11a8ce00135180,0x953e100148001351b0,0x91b61000ca00135220,0x91ba1000ca001352e0,0x91c21000ca00135460,0x9552100148001354d0,0x955610014800135570,0x11ab4e00135680,0x91d21000ca00135760,0x956a10014800135890,0x91de1000ca001359a0,0x957a10014800135b10,0x91ea1000ca00135be0,0x958210014800135c50,0x11ae4e00135c80,0x91f21000ca00135d60,0x11aece00135d80]]
set_option maxRecDepth 10000 in
private def witnessesBlock84 : Array (List ℕ) := #[[0xae462000c4001340ec,0xae4e2000c40013417c,0xae662000c40013432c,0xae822000c400134524,0xaeba2000c400134914,0xaec62000c4001349ec,0xaeee2000c400134cbc,0xaef62000c400134d4c,0xaf1a2000c400134fd4,0xaf2a2000c4001350f4,0xaf362000c4001351cc,0xaf3e2000c40013525c,0xaf4a2000c400135334,0xaf662000c40013552c,0xaf722000c400135604,0xaf7e2000c4001356dc,0xaf922000c400135844,0xaf962000c40013588c,0xafaa2000c4001359f4,0xafc22000c400135ba4,0xafd22000c400135cc4,0xafe62000c400135e2c,0xafea2000c400135e74,0xaffe2000c400135fdc], [0x40071000a4000c8001375f0,0x1001de00138000], [0x40130801a1001ce00136080,0x2005840070800a2000cc00136240,0x2009880070800a1000c8001368d0,0x20088400b1000a1000c800136c90,0x800d0800e1000cc00137740], [0x805e10094e00136580,0x401d0800a1000d200136600,0x4035080161000ce00136a80,0x4029080262000ca00136c60,0x803a5000ca001370e0,0x8056100a4e00137180,0x401f080261000ce00137380,0x4017080161001ce00137580,0x804a1000d600137800], [0x403b0805e10014800136290,0x40650802e1000ca00136720,0x40530800e1000ce00136780,0x80ce10044e00136b80,0x4047080162000ca00136ea0,0x40610803a10014800136f10,0x80e2300148001372d0,0x40650800e10014c001373c0,0x807a10074e00137480,0x40670802e1000ca00137860,0x40710800e2000ca001379e0,0x80b210015200137a00,0x403d0801a2000ca00137c20,0x403d0805e10014800137ff0], [0x40a308022100148001361f0,0x82023000ca00136360,0x81822000ce00136480,0x40d3080161000ca00136660,0x40b30801a1000ca001368a0,0x4089080221000ca00136960,0x41370800a2000c800136ab0,0x40a70800e1000cc00136cc0,0x81f61001ce00136e80,0x40b50801a1000ca00137260,0x409d0800a2000ca00137320,0x41010801610014800137370,0x409508026100148001374b0,0x408b080221000ca00137620,0x818a2000ce00137680,0x40a70802210014800137730,0x820e3000ca001377a0,0x811210034e00137a80,0x40bf1000a1000c800137f50,0x818e2000ce00137f80], [0x41cd0800a1000ca00136060,0x84821000ce00136180,0x82b610014e00136380,0x41cf0800a1000ca00136420,0x418d0800e10014800136470,0x414b0800e1000ca001364e0,0x82ba10014e00136880,0x83e61001cc00136940,0x41d30800a1000ca00136ba0,0x41910800e10014800136d30,0x83ee1001cc00137040,0x41390800a2000c800137050,0x84961000ce00137080,0x82c210014e00137280,0x41510800e1000ca001374a0,0x84a21000ce00137980,0x83fa1001cc00137ac0,0x413d0800a2000c800137b90,0x41990800e10014800137eb0], [0x86022000ca00136120,0x860a2000ca001365a0,0x43a10800a1000c8001366f0,0x43a90800a1000c800136e70,0x43ad0800a1000c800137230,0x86262000ca00137560,0x43b30800a1000c8001377d0,0x43b90800a1000c800137d70]]
set_option maxRecDepth 10000 in
private def witnessesBlock85 : Array (List ℕ) := #[[0x959e100148001360b0,0x920a1000ca001361e0,0x11b14e00136280,0x920e1000ca001362a0,0x95b2100148001363d0,0x11b34e00136680,0x95ca10014800136790,0x95ce10014800136830,0x11b4ce00136980,0x95da10014800136a10,0x923a1000ca00136ae0,0x95e210014800136b50,0x95e610014800136bf0,0x11b64e00136c80,0x92461000ca00136d20,0x924a1000ca00136de0,0x11b7ce00136f80,0x92561000ca00137020,0x9606100148001370f0,0x925e1000ca001371a0,0x926a1000ca001373e0,0x962210014800137550,0x962a10014800137690,0x963610014800137870,0x11bc4e00137880,0x92861000ca00137920,0x964610014800137af0,0x92921000ca00137b60,0x11bdce00137b80,0x965210014800137cd0,0x929a1000ca00137ce0,0x11bece00137d80,0x929e1000ca00137da0,0x965a10014800137e10,0x11bf4e00137e80,0x92aa1000ca00137fe0], [0xb00e2000c4001360fc,0xb0262000c4001362ac,0xb03a2000c400136414,0xb06a2000c400136774,0xb06e2000c4001367bc,0xb0762000c40013684c,0xb0862000c40013696c,0xb0922000c400136a44,0xb09a2000c400136ad4,0xb0aa2000c400136bf4,0xb0ce2000c400136e7c,0xb0e22000c400136fe4,0xb0ee2000c4001370bc,0xb0fa2000c400137194,0xb0fe2000c4001371dc,0xb10a2000c4001372b4,0xb11e2000c40013741c,0xb1362000c4001375cc,0xb13a2000c400137614,0xb14e2000c40013777c,0xb15a2000c400137854,0xb1662000c40013792c,0xb1722000c400137a04,0xb1822000c400137b24,0xb18e2000c400137bfc,0xb1a22000c400137d64,0xb1ae2000c400137e3c,0xb1b22000c400137e84,0xb1be2000c400137f5c], [0x40130800e3000cc001381c0,0x800b0800a1000ce00138b80,0x2009840110800a2000c800138c70,0x400d0800e10015200138e00,0x400d1800a2000c800139210,0x400b0800e1000d400139c00], [0x200e8400b0800a2000c800138130,0x802e40014800138270,0x402f080222000ca001382e0,0x801f0800a1000c8001384f0,0x402f080161001cc001388c0,0x200b840070800a2000ca001389a0,0x401d0800e2000ce00139180,0x402f0801a1000ce00139480,0x401d1000a4000c400139594,0x402b080262000ca00139720,0x401f080221001cc00139a40,0x40290800a2000ce00139a80,0x2017840070800a2000c800139d50,0x40350800e10014e00139f80], [0x40430805610014800138450,0x40670800e10014c00138540,0x40530803a1000ca001386a0,0x4049080162000ca00138760,0x80863000ce00138880,0x407f080261000ca001388e0,0x403b080521000ca00138b20,0x809e1005ce00138c80,0x80d610044e00138d80,0x40470805210014800138db0,0x407f0802e100148001390d0,0x404f0804a10014800139170,0x80761007ce00139280,0x40650803a10014800139350,0x404f0803e1000ca00139660,0x80c21004ce00139980,0x406b0802e1000ca00139ae0,0x80da10044e00139e80], [0x81461002ce00138080,0x40970802610014800138090,0x82021001ce00138380,0x811610034e00138780,0x41070801610014800138810,0x40c11000a1000c8001388b0,0x40df0801a100148001389f0,0x821a3000ca00138be0,0x40ad0800e1000cc00138c40,0x821e3000ca001392a0,0x40a30800a2000ca001394e0,0x814e1002ce00139680,0x40ad0802210014800139710,0x40df080161000ca001397e0,0x820e1001ce00139880,0x40e30801a10014800139a30,0x40c51000a1000c800139b70,0x410d0801610014800139cb0], [0x82ce10014e00138180,0x41df0800a1000ca00138220,0x84ae1000ce00138280,0x84b21000ce00138580,0x84be1000ce00138e80,0x415b0800e1000ca00138ee0,0x84121001cc00138fc0,0x41e70800a1000ca00139120,0x84161001cc00139340,0x415d0800e1000ca00139420,0x41a30800e10014800139490,0x82de10014e00139580,0x84ca1000ce00139780,0x41eb0800a1000ca001398a0,0x41a50800e100148001398f0,0x84d21000ce00139d80,0x41610800e1000ca00139ea0], [0x863a2000ca001380a0,0x43c70800a1000c800138a90,0x86522000ca00138e20,0x43cb0800a1000c800138e50,0x86562000ca00139060,0x43d10800a1000c8001393f0,0x43d70800a1000c800139990,0x866a2000ca00139ba0,0x866e2000ca00139de0]]
set_option maxRecDepth 10000 in
private def witnessesBlock86 : Array (List ℕ) := #[[0x92b21000ca00138160,0x92be1000ca001383a0,0x967e100148001383b0,0x11c24e00138480,0x968e10014800138630,0x92d61000ca00138820,0x96a210014800138950,0x11c4ce00138980,0x92e21000ca00138a60,0x96ae10014800138b30,0x92ee1000ca00138ca0,0x96ba10014800138d10,0x11c7ce00138f80,0x96ca10014800138f90,0x930a1000ca001391e0,0x96de100148001392b0,0x93121000ca00139360,0x11c9ce00139380,0x931e1000ca001395a0,0x96f610014800139670,0x93361000ca00139a20,0x971210014800139ad0,0x11cdce00139b80,0x971a10014800139c10,0x93461000ca00139d20,0x972610014800139df0,0x93521000ca00139f60,0x973210014800139fd0], [0xb1ca2000c400138034,0xb1d62000c40013810c,0xb1ea2000c400138274,0xb1fa2000c400138394,0xb22a2000c4001386f4,0xb2362000c4001387cc,0xb2622000c400138ae4,0xb2662000c400138b2c,0xb28a2000c400138db4,0xb2922000c400138e44,0xb2a22000c400138f64,0xb2b62000c4001390cc,0xb2f22000c400139504,0xb3022000c400139624,0xb3262000c4001398ac,0xb32e2000c40013993c,0xb3322000c400139984,0xb3462000c400139aec,0xb3522000c400139bc4,0xb3562000c400139c0c,0xb3622000c400139ce4,0xb36a2000c400139d74,0xb38e2000c400139ffc], [0x2000a1000ce0013a980,0x40070800a3000d00013b100,0x800a1000dc0013c000], [0x400b1000a3000ca0013a020,0x801a2000d60013a800,0x4013080162000ce0013ac80,0x80163001cc0013af40,0x400d1000e1000ce0013bb80], [0x401f0800a1000d20013a200,0x40290801a1001cc0013a4c0,0x40350805e1000ca0013a620,0x803e5000ca0013ada0,0x401d0801a10014e0013ae80,0x4025080221000ce0013af80,0x200e840071000a1000c80013b790,0x40250802e2000ca0013bd60,0x200f8400b0800a2000c80013bf10], [0x403b0800e2000cc0013a140,0x40430804a1000ca0013a1a0,0x4083080261000ca0013a560,0x40670803a1001480013a570,0x40590800e1000ce0013a680,0x4049080521001480013a750,0x406b0800e10014c0013a840,0x403d080521000ca0013a9e0,0x40610803e1001480013abb0,0x406d0802e1000ca0013ac20,0x40830802e1001480013ad90,0x40431000a2000c80013ae30,0x807a1007ce0013b180,0x403b080561000ca0013b760,0x407f0800a1000ce0013b880,0x406d0800e10014c0013b9c0,0x4047080561001480013ba10,0x80a61005ce0013ba80,0x808e3000ce0013be80,0x80ca1004ce0013bf80,0x40530804a1001480013bfb0], [0x40e50801a1001480013a250,0x40bf0801a1000ca0013a320,0x410f080161001480013a390,0x409d080261001480013a430,0x40c71000a1000c80013a4d0,0x822a3000ca0013a6e0,0x40e3080161000ca0013a860,0x40a70800a2000ca0013ab60,0x40b30800e1000cc0013abc0,0x40c10801a1000ca0013ace0,0x821a1001ce0013ad80,0x40e5080161000ca0013b0a0,0x40e90801a1001480013b290,0x82323000ca0013b460,0x821e1001ce0013b480,0x81a62000ce0013b580,0x4095080221000ca0013b5e0,0x40b50800e1000cc0013b640,0x40b3080221001480013b6f0,0x815a1002ce0013b780,0x4115080161001480013b830,0x82363000ca0013bb20], [0x84d61000ce0013a080,0x414b0800a2000c80013a2f0,0x82ea10014e0013a480,0x41f30800a1000ca0013a7a0,0x41670800e1000ca0013ae60,0x41af0800e1001480013aed0,0x41f70800a1000ca0013af20,0x84ee1000ce0013b280,0x843a1001cc0013b2c0,0x41b10800e1001480013b330,0x82f610014e0013b380,0x41510800a2000c80013b3d0,0x41fd0800a1000ca0013ba60,0x84461001cc0013bd40,0x82fe10014e0013bd80]]
set_option maxRecDepth 10000 in
private def witnessesBlock87 : Array (List ℕ) := #[[0x43df0800a1000c80013a110,0x86762000ca0013a260,0x867a2000ca0013a4a0,0x43e50800a1000c80013a6b0,0x868e2000ca0013afe0,0x43f10800a1000c80013b1f0,0x43f50800a1000c80013b5b0,0x43fb0800a1000c80013bb50,0x43fd0800a1000c80013bd30,0x86aa2000ca0013bfa0], [0x97361001480013a070,0x935a1000ca0013a0e0,0x11d14e0013a280,0x11d2ce0013a580,0x11d3ce0013a780,0x11d44e0013a880,0x976e1001480013a930,0x97721001480013a9d0,0x11d54e0013aa80,0x938e1000ca0013aaa0,0x11d5ce0013ab80,0x97861001480013acf0,0x97961001480013af70,0x11d84e0013b080,0x979e1001480013b0b0,0x93b21000ca0013b160,0x97ba1001480013b510,0x93c61000ca0013b520,0x97c21001480013b650,0x11db4e0013b680,0x93d61000ca0013b820,0x97d21001480013b8d0,0x11dcce0013b980,0x93de1000ca0013b9a0,0x93ea1000ca0013bbe0,0x11de4e0013bc80,0x97ea1001480013bc90,0x93ee1000ca0013bca0,0x97f61001480013be70,0x93fa1000ca0013bee0], [0xb39e2000c40013a11c,0xb3b62000c40013a2cc,0xb3da2000c40013a554,0xb3fa2000c40013a794,0xb4062000c40013a86c,0xb40a2000c40013a8b4,0xb4222000c40013aa64,0xb42e2000c40013ab3c,0xb4422000c40013aca4,0xb4462000c40013acec,0xb45a2000c40013ae54,0xb45e2000c40013ae9c,0xb46a2000c40013af74,0xb47e2000c40013b0dc,0xb49a2000c40013b2d4,0xb4a22000c40013b364,0xb4d22000c40013b6c4,0xb4d62000c40013b70c,0xb4f62000c40013b94c,0xb4fa2000c40013b994,0xb50e2000c40013bafc,0xb5122000c40013bb44,0xb5262000c40013bcac,0xb54e2000c40013bf7c], [0xc0070800a2000c80013c4b0,0x40071800a2000ca0013d860], [0x40130800a4000ca0013c1e0,0x400b2000a2000c40013c6cc,0x100223000ca0013cf60,0x20098400b1000a1000c80013d3b0,0x20088400b0800e1000cc0013d5c0,0x400d0800a5000c80013db30,0x400b0800a2000d20013de00], [0x805e100a4e0013c380,0x401d080261001cc0013c440,0x402b0800a2000ce0013c780,0x40171000a3000c80013ca50,0x2012840070800a1000cc0013cb40,0x401f0800e2000ce0013d080,0x40170802210014e0013d180,0x402b0801a1001cc0013d240,0x806a10094e0013d480,0x401f1000a4000c40013d4dc,0x80521000d60013d800], [0x80e210044e0013c080,0x403d0800e2000cc0013c0c0,0x40530803e1000ca0013c4e0,0x40590803a1000ca0013c7e0,0x406b0803a1001480013c9b0,0x80c21001520013ca00,0x808610074e0013cb80,0x403b080161000ce0013cd80,0x40710802e1000ca0013cea0,0x403b0806a1001480013d130,0x404f080162000ca0013d1a0,0x40650803e1001480013d270,0x80ce1004ce0013d280,0x100762000c60013d308,0x40430801a2000ca0013d3e0,0x4049080561001480013d4f0,0x40830800a1000ce0013d680,0x403d080561000ca0013d7a0,0x40430805e1001480013d810,0x40470804a1000ca0013d920,0x80923000ce0013d980,0x406d0803a1001480013dbd0,0x40710800e10014c0013dcc0], [0x40c50801a1000ca0013c060,0x40e9080161000ca0013c120,0x40b5080221001480013c190,0x4097080221000ca0013c2a0,0x4119080161001480013c5f0,0x40a3080261001480013c7d0,0x812a10034e0013c880,0x822a1001ce0013c980,0x40c70801a1000ca0013ca20,0x40ef0801a1001480013caf0,0x411b080161001480013ccd0,0x40ad0800a2000ca0013cd20,0x4089080261000ca0013d020,0x40f10801a1001480013d310,0x812e10034e0013d580,0x82321001ce0013d780,0x81661002ce0013d880,0x40890802e1001480013d8b0,0x40ef080161000ca0013d9e0,0x824a3000ca0013dce0,0x40d31000a1000c80013dd10,0x408b080261000ca0013de60,0x82361001ce0013de80,0x40a7080261001480013df90]]
set_option maxRecDepth 10000 in
private def witnessesBlock88 : Array (List ℕ) := #[[0x41b70800e1001480013c050,0x85021000ce0013c180,0x416f0800e1000ca0013c360,0x85061000ce0013c480,0x41bb0800e1001480013c910,0x850e1000ce0013ca80,0x830a10014e0013cc80,0x845a1001cc0013cec0,0x415b0800a2000c80013cff0,0x42090800a1000ca0013d0e0,0x41750800e1000ca0013d320,0x851a1000ce0013d380,0x420b0800a1000ca0013d4a0,0x415d0800a2000c80013d590,0x41c10800e1001480013d630,0x84661001cc0013d940,0x85261000ce0013dc80,0x852a1000ce0013df80], [0x86b22000ca0013c420,0x86b62000ca0013c660,0x44070800a1000c80013c690,0x44090800a1000c80013c870,0x86be2000ca0013cae0,0x440f0800a1000c80013ce10,0x44190800a1000c80013d770,0x441b0800a1000c80013d950,0x86da2000ca0013daa0,0x86e22000ca0013df20], [0x980e1001480013c230,0x98161001480013c370,0x98221001480013c550,0x11e2ce0013c580,0x11e34e0013c680,0x94261000ca0013c720,0x984a1001480013cb90,0x943e1000ca0013cba0,0x94421000ca0013cc60,0x11e74e0013ce80,0x985e1001480013ceb0,0x98621001480013cf50,0x11e7ce0013cf80,0x94621000ca0013d260,0x98821001480013d450,0x94721000ca0013d560,0x947a1000ca0013d6e0,0x11ed4e0013da80,0x94921000ca0013db60,0x98b61001480013dc70,0x11eece0013dd80,0x98be1001480013ddb0,0x98c21001480013de50], [0xb5562000c40013c00c,0xb55a2000c40013c054,0xb5622000c40013c0e4,0xb5722000c40013c204,0xb5922000c40013c444,0xb59e2000c40013c51c,0xb5aa2000c40013c5f4,0xb5ae2000c40013c63c,0xb5c62000c40013c7ec,0xb5e62000c40013ca2c,0xb5f62000c40013cb4c,0xb5fe2000c40013cbdc,0xb60a2000c40013ccb4,0xb6462000c40013d0ec,0xb64a2000c40013d134,0xb65e2000c40013d29c,0xb6622000c40013d2e4,0xb66e2000c40013d3bc,0xb6762000c40013d44c,0xb6822000c40013d524,0xb68e2000c40013d5fc,0xb69e2000c40013d71c,0xb6aa2000c40013d7f4,0xb6b22000c40013d884,0xb6ca2000c40013da34,0xb6d62000c40013db0c,0xb6e62000c40013dc2c,0xb6fe2000c40013dddc,0xb7062000c40013de6c], [0x1000a4000ce0013f480], [0x40110801a2000ce0013e280,0x80130800a2000c80013f750,0x800b0800a3000c80013fcf0,0x2006840070800a2000cc0013ffc0], [0x804a3000d00013e700,0x401d0802e1000ce0013e880,0x402f080262000ca0013eca0,0x401f0801a10014e0013ef80,0x805e100ace0013f280,0x401f0803a2000ca0013f360,0x802e1002d40013f400,0x4035080222000ca0013f5a0,0x200f840071000a1000c80013f930,0x40250801610014e0013f980,0x4035080161001cc0013fc40], [0x80fe3001480013e030,0x40670803e1001480013e5d0,0x40471000a2000c80013e670,0x407f0800e2000ca0013e820,0x403d080161000ce0013ee80,0x80ca1001520013f200,0x403d0806a1001480013f250,0x404f080521001480013f430,0x40490804a1000ca0013f4e0,0x80d61004ce0013f880,0x40610800e1000ce0013fa80,0x81063001480013ff70,0x80b21005ce0013ff80]]
set_option maxRecDepth 10000 in
private def witnessesBlock89 : Array (List ℕ) := #[[0x40f1080161000ca0013e220,0x816a1002ce0013e380,0x408b0802e1001480013e710,0x409d080221000ca0013e8e0,0x40bf0800e1000cc0013eac0,0x81be2000ce0013eb80,0x40b30800a2000ca0013eee0,0x4125080161001480013ef30,0x40c10800e1000cc0013f540,0x40bf080221001480013f6b0,0x40b50800a2000ca0013fa20,0x40fb0801a1001480013fbb0,0x813a10034e0013fc80,0x81c62000ce0013fd80], [0x831a10014e0013e080,0x41610800a2000c80013e0d0,0x417b0800e1000ca0013e2e0,0x84721001cc0013e3c0,0x84761001cc0013e740,0x41c90800e1001480013e7b0,0x832210014e0013ea80,0x417f0800e1000ca0013ed60,0x41cd0800e1001480013f070,0x85421000ce0013f180,0x41670800a2000c80013f1b0,0x84821001cc0013f1c0,0x41cf0800e1001480013f4d0,0x421d0800a1000ca0013f660,0x854a1000ce0013f780,0x41850800e1000ca0013fd20,0x41d30800e1001480013fd90,0x833210014e0013fe80], [0x86e62000ca0013e160,0x44250800a1000c80013e2b0,0x44270800a1000c80013e490,0x86ee2000ca0013e5e0,0x442d0800a1000c80013ea30,0x443f0800a1000c80013fb10,0x87162000ca0013fc60,0x44430800a1000c80013fed0], [0x94ae1000ca0013e0a0,0x11f0ce0013e180,0x98da1001480013e210,0x98e61001480013e3f0,0x94c21000ca0013e460,0x11f24e0013e480,0x94c61000ca0013e520,0x98ee1001480013e530,0x11f34e0013e680,0x94ce1000ca0013e6a0,0x11f3ce0013e780,0x99061001480013e8f0,0x11f4ce0013e980,0x94de1000ca0013e9a0,0x99121001480013ead0,0x94ea1000ca0013ebe0,0x99221001480013ed50,0x11f6ce0013ed80,0x94f61000ca0013ee20,0x992a1001480013ee90,0x94fe1000ca0013efa0,0x95021000ca0013f060,0x11f84e0013f080,0x993a1001480013f110,0x950a1000ca0013f1e0,0x95161000ca0013f420,0x11face0013f580,0x11fb4e0013f680,0x95261000ca0013f720,0x99661001480013f7f0,0x996a1001480013f890,0x952e1000ca0013f8a0,0x95321000ca0013f960,0x99721001480013f9d0,0x99761001480013fa70,0x11fdce0013fb80,0x953e1000ca0013fba0,0x998e1001480013fe30,0x95521000ca0013ff60], [0xb7222000c40013e064,0xb73a2000c40013e214,0xb74e2000c40013e37c,0xb77e2000c40013e6dc,0xb78a2000c40013e7b4,0xb7a22000c40013e964,0xb7ae2000c40013ea3c,0xb7b22000c40013ea84,0xb7de2000c40013ed9c,0xb7ee2000c40013eebc,0xb8122000c40013f144,0xb8262000c40013f2ac,0xb8322000c40013f384,0xb84e2000c40013f57c,0xb8562000c40013f60c,0xb85a2000c40013f654,0xb8662000c40013f72c,0xb87a2000c40013f894,0xb88a2000c40013f9b4,0xb8962000c40013fa8c,0xb89e2000c40013fb1c,0xb8aa2000c40013fbf4], [0x40071000a1000d200141a00,0x2000a3000c800141eb0,0x40070800a5000ca00142720,0x800a3000d600143800], [0x20088400d1000a1000c800140bf0,0x801a10015800141000,0x20088400b0800a2000ca00141be0,0x802230014e00142680,0x800d0800a4000c400142d74,0x2005840071000a2000c800143ad0], [0x401f080261001cc001406c0,0x80561000d600140800,0x40350801a1000ce00140980,0x201a840070800a2000c800141370,0x4029080221000ce00141580,0x40170801a1001ce00141680,0x4025080261000ce00141e80,0x200b880070800a1000c800142090,0x402f0800a2000ce00142180,0x200e8400d0800a2000c800142450,0x40290802e2000ca001424e0,0x401d1000e1000cc001429c0,0x402f0801a1001cc00142d40,0x401f0802e1000ce00142d80,0x2014840070800a1000cc00143440,0x806a100a4e00143e80,0x40170800e3000cc00143ec0,0x401d1000a1000ce00143f80]]
set_option maxRecDepth 10000 in
private def witnessesBlock90 : Array (List ℕ) := #[[0x40710803a10014800140010,0x40491000a2000c800140290,0x4053080162000ca00140320,0x40590804a10014800140510,0x808e10074e00140580,0x80ce10015200140600,0x4043080521000ca00140620,0x40830800e2000ca001407a0,0x403b0800e10014e00140880,0x40590803e1000ca00140aa0,0x80da1004ce00140b80,0x406b0803e10014800140c90,0x40470801a2000ca00140e60,0x80861007ce00140e80,0x403b0805e1000ca00140fe0,0x40470805e100148001412d0,0x1007a2000c600141688,0x40610803a1000ca00141ee0,0x40430800e2000cc00141f40,0x406d0803e10014800141ff0,0x809210074e00142280,0x40650800e1000ce00142480,0x404f0805610014800142590,0x40530805210014800142770,0x809e3000ce00142a80,0x403d0800e10014e00142b80,0x40490801a2000ca00142ba0,0x80d610015200142e00,0x40490805e10014800143030,0x80e21004ce00143180,0x403d0805e1000ca00143320,0x80fe10044e00143780,0x4043080561000ca00143860,0x40670800e1000ce00143980], [0x40c10802210014800140150,0x824a1001ce00140180,0x40ad0802610014800140330,0x40890800a1000ce00140380,0x40d30801a1000ca001404a0,0x81ca2000ce00140680,0x40c50800e1000cc00140a40,0x40fb080161000ca00140b60,0x82663000ca00140c20,0x40a3080221000ca00140f20,0x408b0800a1000ce00141280,0x41010801a10014800141410,0x40c70800e1000cc001414c0,0x40df1000a1000c800141550,0x40c50802210014800141690,0x81d22000ce00141880,0x826e3000ca001419a0,0x817e1002ce00141a80,0x41330801610014800141f50,0x40c70802210014800142130,0x814610034e00142380,0x4101080161000ca00142420,0x81821002ce00142580,0x4095080261000ca001425a0,0x40b308026100148001426d0,0x40e31000a1000c800142810,0x40a7080221000ca001428a0,0x41070801a10014800142c70,0x41370801610014800142d10,0x811230014800142e50,0x40950802e10014800142ef0,0x40e51000a1000c800143170,0x40bf0800a2000ca00143260,0x82661001ce00143280,0x40b508026100148001432b0,0x81de2000ce00143380,0x4097080261000ca001433e0,0x40890800e2000ca001436e0,0x818a1002ce00143b80,0x81e22000ce00143c80,0x4107080161000ca00143ce0,0x40970802e10014800143d50,0x814e10034e00143d80,0x40c10800a2000ca00143da0,0x811630014800143df0,0x40df0801a1000ca00143f20], [0x85561000ce00140080,0x42230800a1000ca001401a0,0x84961001cc00140340,0x416f0800a2000c800140830,0x85661000ce00140c80,0x84a21001cc00140dc0,0x418d0800e1000ca00141220,0x422d0800a1000ca00141460,0x834610014e00141780,0x41df0800e100148001417d0,0x84ae1001cc00141840,0x41750800a2000c800141910,0x857a1000ce00141b80,0x84b21001cc00141bc0,0x834a10014e00141c80,0x41910800e1000ca00141ca0,0x42330800a1000ca00141fa0,0x82723000ca00142060,0x84be1001cc00142640,0x858a1000ce00142780,0x41e70800e10014800142950,0x417b0800a2000c8001429f0,0x42390800a1000ca00142ae0,0x827a3000ca00142de0,0x423b0800a1000ca00142ea0,0x84ca1001cc001430c0,0x41990800e1000ca001431a0,0x41eb0800e10014800143210,0x413908016100148001433f0,0x417f0800a2000c800143530,0x835e10014e00143580,0x859e1000ce00143680,0x84d21001cc001437c0,0x42410800a1000ca001439e0,0x836210014e00143a80,0x84d61001cc00143b40], [0x44450800a1000c8001400b0,0x871e2000ca001400e0,0x44490800a1000c800140470,0x872e2000ca001409e0,0x444f0800a1000c800140a10,0x44550800a1000c800140fb0,0x87422000ca00141520,0x445d0800a1000c800141730,0x44630800a1000c800141cd0,0x87522000ca00141e20,0x44690800a1000c800142270,0x875a2000ca001422a0,0x87662000ca00142960,0x87722000ca00143020,0x447f0800a1000c800143710,0x44810800a1000c8001438f0,0x878e2000ca00143fe0], [0x95561000ca00140020,0x12014e00140280,0x956a1000ca001403e0,0x957a1000ca001406e0,0x99c6100148001406f0,0x1203ce00140780,0x99ca10014800140790,0x95821000ca00140860,0x99d610014800140970,0x12054e00140a80,0x99e210014800140b50,0x99ee10014800140d30,0x959e1000ca00140da0,0x99f610014800140e70,0x9a0210014800141050,0x12084e00141080,0x9a06100148001410f0,0x95b21000ca00141160,0x1208ce00141180,0x1209ce00141380,0x120a4e00141480,0x9a1e100148001414b0,0x95ca1000ca001415e0,0x9a26100148001415f0,0x95ce1000ca001416a0,0x95da1000ca001418e0,0x120cce00141980,0x9a3e100148001419b0,0x9a4210014800141a50,0x95e21000ca00141a60,0x95e61000ca00141b20,0x9a5610014800141d70,0x9a5a10014800141e10,0x120fce00141f80,0x12104e00142080,0x96061000ca00142120,0x9a7a10014800142310,0x9a7e100148001423b0,0x96221000ca00142660,0x962a1000ca001427e0,0x12144e00142880,0x9a9e100148001428b0,0x1214ce00142980,0x96361000ca00142a20,0x9aaa10014800142a90,0x12164e00142c80,0x96461000ca00142d20,0x12174e00142e80,0x96521000ca00142f60,0x1217ce00142f80,0x9ad2100148001430d0,0x965a1000ca001430e0,0x121a4e00143480,0x9af2100148001435d0,0x967e1000ca001437a0,0x9b0210014800143850,0x121c4e00143880,0x9b0a10014800143990,0x9b0e10014800143a30,0x968e1000ca00143aa0,0x9b1610014800143b70,0x9b1a10014800143c10,0x96a21000ca00143e60], [0xb8e62000c40014002c,0xb9022000c400140224,0xb9162000c40014038c,0xb91a2000c4001403d4,0xb9322000c400140584,0xb9462000c4001406ec,0xb94a2000c400140734,0xb96a2000c400140974,0xb96e2000c4001409bc,0xb9922000c400140c44,0xb9c22000c400140fa4,0xb9e62000c40014122c,0xb9f22000c400141304,0xba122000c400141544,0xba362000c4001417cc,0xba422000c4001418a4,0xba462000c4001418ec,0xba6a2000c400141b74,0xba722000c400141c04,0xba7e2000c400141cdc,0xba822000c400141d24,0xba962000c400141e8c,0xbaa62000c400141fac,0xbaba2000c400142114,0xbac62000c4001421ec,0xbad22000c4001422c4,0xbae22000c4001423e4,0xbaea2000c400142474,0xbaf62000c40014254c,0xbafa2000c400142594,0xbb0e2000c4001426fc,0xbb122000c400142744,0xbb2a2000c4001428f4,0xbb322000c400142984,0xbb3e2000c400142a5c,0xbb4a2000c400142b34,0xbb4e2000c400142b7c,0xbb662000c400142d2c,0xbb6e2000c400142dbc,0xbb8a2000c400142fb4,0xbbae2000c40014323c,0xbbb62000c4001432cc,0xbbc22000c4001433a4,0xbbea2000c400143674,0xbbf22000c400143704,0xbc022000c400143824,0xbc0e2000c4001438fc,0xbc162000c40014398c,0xbc262000c400143aac,0xbc2e2000c400143b3c,0xbc4a2000c400143d34,0xbc562000c400143e0c,0xbc5e2000c400143e9c], [0x7000ce00144580,0x2000de00148000], [0x800e40014c001445c0,0x80070800a2000ce00144e80,0x1000e6000c600145c48,0x800e10015a00146000,0x80071800a1000c800147c70]]
set_option maxRecDepth 10000 in
private def witnessesBlock91 : Array (List ℕ) := #[[0x400d1000a3000ca001448e0,0x20098400b0800e1000cc00144940,0x100225000c40014494c,0x30034e00144a80,0x4006840070800a1000c800145510,0x40130801a2000ce00145780,0x801a3001cc00145ac0,0x20068400b0800e2000ca00146620,0x80168000c4001467ac,0x4013080221001ce00146a80,0x400d2000a2000c400147694], [0x40170802610014e00144480,0x402b080221000ce00144880,0x200b840110800a2000c800144bb0,0x4025080221001cc00144cc0,0x80523000d000145300,0x40250800a1000d200145600,0x402b0802e2000ca001458a0,0x401d080161001ce00145c80,0x804a5000ca001463e0,0x40290801610014e00146780,0x805e1000d600146800,0x2015840070800a1000cc001468c0,0x803a40014800146cd0,0x4035080262000ca00146ce0,0x200f8400d0800a2000c800146d70,0x4017080162000ce00147280,0x401f1000e1000cc00147340,0x806a100ace00147380,0x200e840070800a2000ca001475e0,0x20128400b0800a2000c8001478b0], [0x80da10015200144200,0x807610094e00144380,0x4047080521000ca001443a0,0x40710803e100148001446b0,0x407f0802e1000ca00144760,0x404f0804a1000ca00144820,0x40650803a1000ca00144a60,0x808e1007ce00144c80,0x4059080162000ca00144d60,0x4043080161000ce00145180,0x40430806a100148001455b0,0x404f1000a2000c8001456f0,0x407f0800e10014c00145740,0x810610044e00145980,0x40530805610014800145b50,0x80c21005ce00145b80,0x40470800e2000cc00145e40,0x40670803a1000ca00146020,0x80a63000ce00146080,0x40610804a10014800146190,0x4049080521000ca00146260,0x406b0800e1000ce00146380,0x403d08076100148001464b0,0x40610803e1000ca001467a0,0x403b080222000ca00146860,0x807a10094e00146880,0x40830802e1000ca001469e0,0x80e210015200146a00,0x80921007ce00146b80,0x403b080161001cc00146fc0,0x40590805210014800147450,0x406d0800e1000ce00147880,0x4047080561000ca001478e0,0x809e10074e00147980,0x40830800e10014c00147a40,0x40490800e2000cc00147dc0,0x403b0801a1000ce00147e80,0x407f0803a10014800147ef0,0x40530804a1000ca00147fa0], [0x826e1001ce00144080,0x40e91000a1000c800144430,0x410d0801a100148001444d0,0x818e1002ce00144680,0x408b0800e2000ca001446a0,0x410f0801a10014800144cf0,0x40ad080221000ca00144ee0,0x40e30801a1000ca001452a0,0x40d30800e1000cc001453c0,0x40c50800a2000ca00145420,0x410d080161000ca001455a0,0x40e50801a1000ca00145c60,0x40950800a1000ce00145d80,0x410f080161000ca00145de0,0x409d080261000ca00145ea0,0x40c70800a2000ca00145f60,0x40ef1000a1000c800146050,0x40d308022100148001460f0,0x815a10034e00146480,0x41150801a10014800146550,0x409d0802e10014800146870,0x81f62000ce00146980,0x40f11000a1000c8001469b0,0x40970800a1000ce00146c80,0x40bf0802610014800146e10,0x40e90801a1000ca00146fe0,0x40b3080221000ca00147520,0x41190801a10014800147590,0x4115080161000ca001476a0,0x40c108026100148001479f0,0x411b0801a10014800147db0], [0x413d08016100148001441b0,0x41f30800e10014800144390,0x41850800a2000c800144610,0x82721001ce00144780,0x836e10014e00144980,0x41a30800e1000ca00144be0,0x41f70800e10014800144c50,0x424b0800a1000ca00144ca0,0x84ee1001cc00145040,0x41a50800e1000ca00145120,0x837610014e00145380,0x827a1001ce00145580,0x42510800a1000ca001457e0,0x41fd0800e10014800145970,0x418d0800a2000c800145c90,0x82963000ca00145d20,0x85021001cc001461c0,0x838210014e00146280,0x42570800a1000ca00146320,0x85061001cc00146540,0x42590800a1000ca001466e0,0x41910800a2000c8001467d0,0x41af0800e1000ca00146b60,0x850e1001cc00146c40,0x41b10800e1000ca001470a0,0x82a23000ca00147160,0x414b08016100148001471d0,0x425f0800a1000ca00147220,0x42090800e100148001473b0,0x839210014e00147680,0x851a1001cc001476c0,0x420b0800e10014800147810,0x42650800a1000ca00147d60,0x41990800a2000c800147e50], [0x448b0800a1000c800144250,0x85ae1000ce00144280,0x87962000ca00144460,0x44930800a1000c8001449d0,0x87a22000ca00144b20,0x85ba1000ce00144b80,0x87ae2000ca001451e0,0x449d0800a1000c800145330,0x85c61000ce00145480,0x44a30800a1000c8001458d0,0x85ce1000ce00145a80,0x87be2000ca00145ae0,0x44a90800a1000c800145e70,0x87ca2000ca001461a0,0x44b10800a1000c8001465f0,0x85de1000ce00146680,0x87e22000ca00146f20,0x85ea1000ce00146f80,0x44bd0800a1000c800147130,0x87ea2000ca001473a0,0x44c10800a1000c8001474f0,0x85f21000ce00147580,0x87f62000ca00147a60,0x44c70800a1000c800147a90,0x87fa2000ca00147ca0], [0x96ae1000ca001440a0,0x1220ce00144180,0x96ba1000ca001442e0,0x9b46100148001442f0,0x9b5610014800144570,0x96ca1000ca001445e0,0x9b6e10014800144930,0x96de1000ca001449a0,0x9b7a10014800144b10,0x1226ce00144d80,0x96f61000ca00144e20,0x9b8e10014800144e30,0x9b9210014800144ed0,0x1227ce00144f80,0x9b9a10014800145010,0x9ba6100148001451f0,0x12294e00145280,0x9baa10014800145290,0x97121000ca00145360,0x9bb610014800145470,0x971a1000ca001454e0,0x122b4e00145680,0x97261000ca00145720,0x9bca10014800145790,0x9bce10014800145830,0x97321000ca00145960,0x97361000ca00145a20,0x9be610014800145bf0,0x122f4e00145e80,0x9bfa10014800145f10,0x122fce00145f80,0x9bfe10014800145fb0,0x1230ce00146180,0x9c12100148001462d0,0x976e1000ca001464a0,0x97721000ca00146560,0x1232ce00146580,0x9c2e10014800146730,0x9c3a10014800146910,0x97861000ca00146920,0x9c4210014800146a50,0x97961000ca00146c20,0x9c4e10014800146c30,0x1236ce00146d80,0x979e1000ca00146da0,0x12374e00146e80,0x9c5e10014800146eb0,0x12384e00147080,0x9c6a10014800147090,0x9c7610014800147270,0x97ba1000ca001472e0,0x97c21000ca00147460,0x123a4e00147480,0x97d21000ca00147760,0x9c9610014800147770,0x123bce00147780,0x123d4e00147a80,0x9cae10014800147b30,0x97ea1000ca00147be0,0x123e4e00147c80,0x97f61000ca00147e20], [0x9cb210014800147bd0,0x9cba10014800147d10]]
set_option maxRecDepth 10000 in
private def witnessesBlock92 : Array (List ℕ) := #[[0xbc7a2000c400144094,0xbc922000c400144244,0xbc9a2000c4001442d4,0xbc9e2000c40014431c,0xbcda2000c400144754,0xbce22000c4001447e4,0xbd122000c400144b44,0xbd1e2000c400144c1c,0xbd2a2000c400144cf4,0xbd422000c400144ea4,0xbd5a2000c400145054,0xbd762000c40014524c,0xbd822000c400145324,0xbd8a2000c4001453b4,0xbd8e2000c4001453fc,0xbd962000c40014548c,0xbdba2000c400145714,0xbdc62000c4001457ec,0xbdde2000c40014599c,0xbdee2000c400145abc,0xbdfa2000c400145b94,0xbe022000c400145c24,0xbe1a2000c400145dd4,0xbe1e2000c400145e1c,0xbe362000c400145fcc,0xbe722000c400146404,0xbe922000c400146644,0xbe962000c40014668c,0xbea22000c400146764,0xbece2000c400146a7c,0xbeea2000c400146c74,0xbef62000c400146d4c,0xbf0a2000c400146eb4,0xbf222000c400147064,0xbf2e2000c40014713c,0xbf322000c400147184,0xbf3a2000c400147214,0xbf4a2000c400147334,0xbf5e2000c40014749c,0xbf6a2000c400147574,0xbf762000c40014764c,0xbfa62000c4001479ac,0xbfc22000c400147ba4,0xbfce2000c400147c7c,0xbfd62000c400147d0c,0xbfe62000c400147e2c,0xbffe2000c400147fdc], [0x40071000a3000cc00149d40,0x800a5000d00014bf00], [0x20098400d1000a1000c8001485d0,0x20088400d0800e1000cc00148840,0x400d0800a2000d200149200,0x20098400b0800a2000ca001497a0,0x802630014e0014a380,0x80163000d40014a400,0x40110800e1001520014a600,0x40111800a2000c80014ab50,0x400b1000e2000cc0014bcc0,0x40110801a1002ce0014bf80], [0x80563000d000148900,0x401f1000a1000ce00148a80,0x40170800a4000ca00148c60,0x40250800e2000ce00148d80,0x401d0802e1001cc00148f40,0x4029080261000ce00149080,0x40251000a4000c4001492b4,0x402b0801610014e00149e80,0x200b8400b1000a1000c80014a1f0,0x40350800a2000ce0014a880,0x401f080161001ce0014a980,0x402f080221000ce0014ae80,0x40250801a10014e0014b280,0x40350801a1001cc0014b5c0,0x40250803a2000ca0014b720,0x803e4001480014baf0,0x2012840071000a1000c80014be10], [0x404f0801a2000ca00148360,0x404f0805e10014800148850,0x80ca1005ce00148980,0x201d840070800a2000c800148990,0x406b0803a1000ca00148ba0,0x403d080222000ca00148ea0,0x40531000a2000c800148f30,0x40650804a10014800148fd0,0x4047080161000ce00149380,0x40430800e10014e00149480,0x403b0806a1000ca001494a0,0x40650803e1000ca00149620,0x403d080161001cc00149640,0x40470806a100148001497f0,0x4049080561000ca00149920,0x40430805e1000ca00149ce0,0x80ce1005ce0014a080,0x406d0803a1000ca0014a160,0x40710800e1000ce0014a280,0x40830803a1001480014a330,0x403d0801a1000ce0014a580,0x40670804a1001480014a6f0,0x4059080561001480014abf0,0x40670803e1000ca0014ad60,0x4061080162000ca0014b060,0x201e840070800a2000c80014b0f0,0x80b23000ce0014b180,0x80a610074e0014b380,0x4049080161000ce0014b480,0x80fe1004ce0014b680,0x40490806a1001480014b910,0x8076100a4e0014b980,0x403d0806a1000ca0014bc60,0x40530801a2000ca0014bde0,0x404f080521000ca0014bea0], [0x40b5080221000ca001481e0,0x82022000ce00148480,0x4119080161000ca00148720,0x81a61002ce00148880,0x40a3080261000ca00148960,0x816610034e00148b80,0x812a30014800148c10,0x811210044e00148c80,0x40ef0801a1000ca00148d20,0x411b080161000ca00148f60,0x40c508026100148001491b0,0x40df0800e1000cc001492c0,0x40a30802e10014800149390,0x40950800e2000ca00149560,0x40f10801a1000ca001496e0,0x816a10034e00149880,0x40fb1000a1000c800149890,0x409d0800a1000ce00149980,0x812e30014800149bb0,0x811610044e00149d80,0x40c70802610014800149d90,0x40890802e1000ca00149da0,0x820e2000ce00149f80,0x40df080221001480014a0b0,0x40d30800a2000ca0014a2e0,0x40970800e2000ca0014a520,0x40a7080261000ca0014a5e0,0x41250801a1001480014a650,0x40e30800e1000cc0014a7c0,0x40890800e10014c0014aec0,0x408b0802e1000ca0014aee0,0x40a70802e1001480014b050,0x40e50800e1000cc0014b240,0x41011000a1000c80014b4b0,0x40e3080221001480014b5f0,0x4125080161000ca0014b8a0,0x821a2000ce0014ba80], [0x41b70800e1000ca00148060,0x839a10014e00148080,0x85261001cc00148140,0x852a1001cc001484c0,0x42690800a1000ca001484e0,0x839e10014e00148580,0x41510801610014800148670,0x82961001ce00148680,0x426b0800a1000ca001488a0,0x41bb0800e1000ca00148ae0,0x83a610014e00148f80,0x82b63000ca00149320,0x85421001cc001499c0,0x82ba3000ca001499e0,0x41a30800a2000c800149a70,0x41c10800e1000ca00149aa0,0x82a21001ce00149b80,0x42770800a1000ca00149f20,0x421d0800e10014800149f70,0x41a50800a2000c80014a010,0x854a1001cc0014a0c0,0x82c23000ca0014a760,0x415b080161001480014a8d0,0x85561001cc0014ab40,0x42230800e1001480014ac90,0x83be10014e0014ad80,0x41c90800e1000ca0014afa0,0x415d080161001480014afb0,0x42810800a1000ca0014b1e0,0x42830800a1000ca0014b5a0,0x85661001cc0014b940,0x41cd0800e1000ca0014ba20,0x82ce3000ca0014bba0,0x41af0800a2000c80014bc30,0x42870800a1000ca0014bd20,0x4161080161001480014bd70,0x82b61001ce0014be80,0x41cf0800e1000ca0014bf60], [0x44cd0800a1000c800148030,0x86021000ce00148180,0x44cf0800a1000c800148210,0x860a1000ce00148780,0x44d50800a1000c8001487b0,0x880e2000ca001487e0,0x88122000ca00148a20,0x881e2000ca001490e0,0x44e10800a1000c8001492f0,0x88322000ca00149c20,0x44eb0800a1000c800149c50,0x86261000ce00149c80,0x88362000ca00149e60,0x884a2000ca0014a9a0,0x863a1000ce0014ab80,0x884e2000ca0014abe0,0x44fd0800a1000c80014ad30,0x44ff0800a1000c80014af10,0x885a2000ca0014b2a0,0x45030800a1000c80014b2d0,0x45090800a1000c80014b870,0x450b0800a1000c80014ba50,0x86521000ce0014bd80,0x45110800a1000c80014bff0]]
set_option maxRecDepth 10000 in
private def witnessesBlock93 : Array (List ℕ) := #[[0x12414e00148280,0x980e1000ca001482a0,0x1241ce00148380,0x98161000ca00148420,0x98221000ca00148660,0x984a1000ca00148de0,0x12474e00148e80,0x1248ce00149180,0x985e1000ca001491a0,0x98621000ca00149260,0x12494e00149280,0x124ace00149580,0x124bce00149780,0x98821000ca00149860,0x124d4e00149a80,0x1250ce0014a180,0x98b61000ca0014a220,0x98be1000ca0014a3a0,0x98c21000ca0014a460,0x12524e0014a480,0x12534e0014a680,0x1253ce0014a780,0x98da1000ca0014a8e0,0x12554e0014aa80,0x98e61000ca0014ab20,0x12564e0014ac80,0x98ee1000ca0014aca0,0x1257ce0014af80,0x99061000ca0014b120,0x99121000ca0014b360,0x125ace0014b580,0x99221000ca0014b660,0x992a1000ca0014b7e0,0x125c4e0014b880,0x993a1000ca0014bae0,0x125dce0014bb80], [0x9cd610014800148170,0x9ce210014800148350,0x9cea10014800148490,0x9cfa10014800148710,0x9d0e10014800148a30,0x9d1e10014800148cb0,0x9d2a10014800148e90,0x9d3610014800149070,0x9d6210014800149750,0x9d6e10014800149930,0x9d72100148001499d0,0x9d8610014800149cf0,0x9da21001480014a150,0x9daa1001480014a290,0x9db61001480014a470,0x9dda1001480014aa10,0x9dde1001480014aab0,0x9df21001480014add0,0x9e0e1001480014b230,0x9e161001480014b370,0x9e1a1001480014b410,0x9e2e1001480014b730,0x9e4a1001480014bb90,0x9e521001480014bcd0,0x9e621001480014bf50], [0xc0222000c400148264,0xc0362000c4001483cc,0xc03a2000c400148414,0xc04e2000c40014857c,0xc0522000c4001485c4,0xc05a2000c400148654,0xc0662000c40014872c,0xc08e2000c4001489fc,0xc09a2000c400148ad4,0xc0a22000c400148b64,0xc0be2000c400148d5c,0xc0c62000c400148dec,0xc0ca2000c400148e34,0xc0d22000c400148ec4,0xc0ee2000c4001490bc,0xc0fa2000c400149194,0xc1122000c400149344,0xc1422000c4001496a4,0xc1562000c40014980c,0xc1622000c4001498e4,0xc1722000c400149a04,0xc1862000c400149b6c,0xc18a2000c400149bb4,0xc1c62000c400149fec,0xc1ce2000c40014a07c,0xc1da2000c40014a154,0xc1de2000c40014a19c,0xc1f62000c40014a34c,0xc1fe2000c40014a3dc,0xc21a2000c40014a5d4,0xc2262000c40014a6ac,0xc26a2000c40014ab74,0xc2822000c40014ad24,0xc2922000c40014ae44,0xc29e2000c40014af1c,0xc2b22000c40014b084,0xc2b62000c40014b0cc,0xc2be2000c40014b15c,0xc2e62000c40014b42c,0xc2fa2000c40014b594,0xc30a2000c40014b6b4,0xc32a2000c40014b8f4,0xc32e2000c40014b93c,0xc3422000c40014baa4,0xc35e2000c40014bc9c,0xc3662000c40014bd2c,0xc36a2000c40014bd74,0xc3822000c40014bf24,0xc38e2000c40014bffc], [0x4001520014e200,0x1800a4000ca0014f1a0], [0x100263000ca0014c260,0x80222000d60014c800,0x400b1000a2000ce0014d580,0x20088400d0800a2000ca0014db20,0x40111000e1000ce0014e180,0x20068400b0800e10014c0014e340,0x800d0800a1000ce0014f380,0x800b0800e1000ce0014f680,0x2006840071000a2000c80014ffb0], [0x402f0802e2000ca0014c020,0x4029080221001cc0014c3c0,0x200f840070800a2000ca0014c4a0,0x401d1000a3000c80014c770,0x402b080261000ce0014c980,0x200b840130800a2000c80014cd10,0x40290800a1000d20014ce00,0x4025080261001cc0014ce40,0x401d0802210014e0014d080,0x2017840070800a1000cc0014d1c0,0x80525000ca0014dd60,0x806a100bce0014dd80,0x401f0802e1001cc0014dfc0,0x1003a1000ce0014ed80,0x20148400b0800a2000c80014f470,0x805e3000d00014f500,0x806a1000d60014f800,0x803a1002d40014fc00,0x40250802e1000ce0014fc80,0x402b080221001cc0014ff40], [0x40530805e1001480014c310,0x809e1007ce0014c880,0x40710803a1000ca0014cce0,0x407f0803e1001480014ce50,0x80d61005ce0014ce80,0x40590804a1000ca0014d2e0,0x4043080761001480014d350,0x406b0804a1001480014d530,0x808610094e0014d780,0x40470800e10014e0014da80,0x4061080521001480014dad0,0x406b0803e1000ca0014dbe0,0x404f0800e2000cc0014dc40,0x81061004ce0014dc80,0x4065080162000ca0014e1e0,0x807a100a4e0014e280,0x40470805e1000ca0014e360,0x40591000a2000c80014e390,0x80da1005ce0014e580,0x406d0804a1001480014ec50,0x403b080262000ca0014ed20,0x100862000c60014ee88,0x406d0803e1000ca0014f320,0x8076100ace0014f480,0x40830803e1001480014f510,0x80fe1001520014f600,0x404f080561000ca0014f9e0,0x4067080162000ca0014faa0,0x4053080521000ca0014fc20,0x40430807a1001480014fd30,0x40490800e10014e0014fd80], [0x408b0800e10014c0014c040,0x40e5080221001480014c090,0x40bf080221000ca0014c1a0,0x821e2000ce0014c380,0x40a30800a1000ce0014c680,0x40e90800e1000cc0014c740,0x40fb0801a1000ca0014c7a0,0x81be1002ce0014ca80,0x813a3001480014ca90,0x40c1080221000ca0014ce60,0x40ad080261000ca0014d0a0,0x41071000a1000c80014d0d0,0x409d0800e2000ca0014d460,0x40e9080221001480014d5d0,0x817e10034e0014d980,0x40890803a1001480014d990,0x40ad0802e1001480014db70,0x822a2000ce0014de80,0x41330801a1001480014df30,0x81c61002ce0014e080,0x40a70800a1000ce0014e480,0x40d3080261001480014e4d0,0x41010801a1000ca0014e4e0,0x40df0800a2000ca0014e660,0x818210034e0014e680,0x40ef0800e1000cc0014e6c0,0x40c5080221000ca0014e7e0,0x81ca1002ce0014eb80,0x408b0803a1001480014ebb0,0x410d1000a1000c80014ecf0,0x41370801a1001480014ef70,0x82322000ce0014f080,0x40f10800e1000cc0014f140,0x4133080161000ca0014f260,0x812a10044e0014f280,0x40c7080221000ca0014f4a0,0x40ef080221001480014f5b0,0x410f1000a1000c80014f650,0x81463001480014f970,0x82362000ce0014f980,0x40b3080261000ca0014fb60,0x40e30800a2000ca0014fce0]]
set_option maxRecDepth 10000 in
private def witnessesBlock94 : Array (List ℕ) := #[[0x83ce10014e0014c180,0x41b10800a2000c80014c1d0,0x422d0800e1001480014c270,0x82ba1001ce0014c580,0x428d0800a1000ca0014c860,0x41d30800e1000ca0014c9e0,0x857a1001cc0014cac0,0x83d610014e0014cb80,0x42330800e1001480014cf90,0x4167080161001480014d210,0x41b70800a2000c80014d2b0,0x82c21001ce0014d380,0x42930800a1000ca0014d3a0,0x82de3000ca0014d6a0,0x42950800a1000ca0014d760,0x858a1001cc0014d8c0,0x42390800e1001480014dcb0,0x41bb0800a2000c80014ddf0,0x83e610014e0014df80,0x423b0800e1001480014e110,0x82ce1001ce0014e880,0x41df0800e1000ca0014e960,0x83ee10014e0014e980,0x859e1001cc0014ea40,0x82ea3000ca0014eae0,0x416f080161001480014ed90,0x42a10800a1000ca0014ede0,0x42410800e1001480014ee30,0x41c10800a2000c80014eed0,0x42a50800a1000ca0014f560,0x41390801a1001480014f790,0x83fa10014e0014f880,0x41e70800e1000ca0014fe60,0x82f63000ca0014ff20], [0x86561000ce0014c080,0x45150800a1000c80014c3b0,0x45170800a1000c80014c590,0x887e2000ca0014c6e0,0x451b0800a1000c80014c950,0x88862000ca0014cb60,0x888a2000ca0014cda0,0x866a1000ce0014cf80,0x88922000ca0014d220,0x866e1000ce0014d280,0x45270800a1000c80014d490,0x45290800a1000c80014d670,0x86761000ce0014d880,0x889e2000ca0014d8e0,0x867a1000ce0014db80,0x452f0800a1000c80014dc10,0x88aa2000ca0014dfa0,0x88ba2000ca0014e8a0,0x868e1000ce0014ea80,0x88c62000ca0014ef60,0x88d22000ca0014f620,0x85ae1001cc0014f840,0x45510800a1000c80014fbf0,0x86aa1000ce0014ff80], [0x12614e0014c280,0x99661000ca0014c320,0x996a1000ca0014c3e0,0x12624e0014c480,0x99721000ca0014c560,0x99761000ca0014c620,0x1263ce0014c780,0x998e1000ca0014caa0,0x1266ce0014cd80,0x1268ce0014d180,0x126a4e0014d480,0x99c61000ca0014d520,0x99ca1000ca0014d5e0,0x126b4e0014d680,0x99d61000ca0014d820,0x99e21000ca0014da60,0x99ee1000ca0014dca0,0x99f61000ca0014de20,0x9a021000ca0014e060,0x9a061000ca0014e120,0x1271ce0014e380,0x9a1e1000ca0014e5a0,0x9a261000ca0014e720,0x9a3e1000ca0014eba0,0x9a421000ca0014ec60,0x12764e0014ec80,0x9a561000ca0014f020,0x9a5a1000ca0014f0e0,0x1278ce0014f180,0x127ace0014f580,0x9a7a1000ca0014f6e0,0x127bce0014f780,0x9a7e1000ca0014f7a0,0x127d4e0014fa80,0x127dce0014fb80,0x9a9e1000ca0014fda0,0x127f4e0014fe80,0x9aaa1000ca0014ffe0], [0x9e861001480014c4f0,0x9e8e1001480014c630,0x9e9a1001480014c810,0x9e9e1001480014c8b0,0x9ea61001480014c9f0,0x9eb21001480014cbd0,0x9eb61001480014cc70,0x9ece1001480014d030,0x9ed61001480014d170,0x9efe1001480014d7b0,0x9f2a1001480014de90,0x9f421001480014e250,0x9f461001480014e2f0,0x9f4e1001480014e430,0x9f5a1001480014e610,0x9f661001480014e7f0,0x9f6a1001480014e890,0x9f761001480014ea70,0x9fa21001480014f150,0x9fa61001480014f1f0,0x9fb21001480014f3d0,0x9fd21001480014f8d0,0x9fde1001480014fab0,0x9ff61001480014fe70,0x9ffa1001480014ff10], [0xc3ae2000c40014c23c,0xc3ba2000c40014c314,0xc3ca2000c40014c434,0xc3d22000c40014c4c4,0xc3e22000c40014c5e4,0xc3ea2000c40014c674,0xc3f62000c40014c74c,0xc4062000c40014c86c,0xc4122000c40014c944,0xc41e2000c40014ca1c,0xc4362000c40014cbcc,0xc4422000c40014cca4,0xc44a2000c40014cd34,0xc4562000c40014ce0c,0xc4622000c40014cee4,0xc4722000c40014d004,0xc4962000c40014d28c,0xc49e2000c40014d31c,0xc4c62000c40014d5ec,0xc4ce2000c40014d67c,0xc4e62000c40014d82c,0xc4ea2000c40014d874,0xc4fe2000c40014d9dc,0xc50a2000c40014dab4,0xc50e2000c40014dafc,0xc5222000c40014dc64,0xc53a2000c40014de14,0xc53e2000c40014de5c,0xc5462000c40014deec,0xc56e2000c40014e1bc,0xc57a2000c40014e294,0xc5b62000c40014e6cc,0xc5c22000c40014e7a4,0xc5ca2000c40014e834,0xc5da2000c40014e954,0xc5ee2000c40014eabc,0xc6062000c40014ec6c,0xc6122000c40014ed44,0xc6162000c40014ed8c,0xc64e2000c40014f17c,0xc6522000c40014f1c4,0xc65e2000c40014f29c,0xc6662000c40014f32c,0xc66a2000c40014f374,0xc68a2000c40014f5b4,0xc6a22000c40014f764,0xc6a62000c40014f7ac,0xc6b22000c40014f884,0xc6c62000c40014f9ec,0xc6d62000c40014fb0c,0xc7062000c40014fe6c], [0xc0070800a1000cc00150640,0x1000e3000d000152b00], [0x400b2000a1000c800150910,0x40110800a5000c800150af0,0x20098400d0800e1000cc001510c0,0x100222000ce00151480,0x400b0800a1000d600152800,0x40130800e10015200153200,0x801a8000c4001534b4,0x40131800a2000c8001537f0,0x80165000ce00153880,0x2008840070800a2000cc00153ac0], [0x80250800a1000c800150370,0x402b0800a1000d200150a00,0x40250803e2000ca00150a60,0x40290800e2000ce00150b80,0x402f0801610014e00150c80,0x40291000a4000c400151144,0x80565000ca00151a20,0x401f1000a3000c800151bd0,0x401f0802210014e00152580,0x401d0801a1001ce00152780,0x200b8400b0800e1000cc00153040,0x20158400b0800a2000c800153250,0x200e880070800a1000c800153430,0x40290801a10014e00153480,0x40290803a2000ca001539a0,0x402f080261000ce00153b80]]
set_option maxRecDepth 10000 in
private def witnessesBlock95 : Array (List ℕ) := #[[0x4043080222000ca00150160,0x80a61007ce00150680,0x40490805e1000ca001506a0,0x4043080161001cc001509c0,0x80b210074e00150a80,0x40650805210014800150e10,0x80e21005ce00151380,0x40590801a2000ca001515a0,0x40610805610014800151770,0x404f080161000ce00151780,0x403d080262000ca001517e0,0x40430801a1000ce00151a80,0x40710804a10014800151a90,0x40590805e10014800151b30,0x40530800e2000cc00151b40,0x404f0806a10014800151c70,0x40470807610014800151d10,0x80c23000ce00151d80,0x810610015200151e00,0x807a100ace00151f80,0x808e10094e00152180,0x40710803e1000ca001521a0,0x2021840070800a2000c800152710,0x406708052100148001527b0,0x406b080162000ca00152c20,0x403b0800a2000ce00152f80,0x40430806a1000ca001533a0,0x407f0800e1000ce00153580,0x4053080561000ca00153a60,0x403b0801a1001cc00153e40], [0x40f10802210014800150050,0x818a10034e00150080,0x81d21002ce00150180,0x41070801a1000ca00150220,0x4137080161000ca001502e0,0x812e10044e00150380,0x40a30800e2000ca001503a0,0x40950802e1000ca00150520,0x40b30802e10014800150690,0x40e50800a2000ca00150820,0x40b5080261000ca001509a0,0x818e10034e00150d80,0x40ad0800a1000ce00151180,0x41151000a1000c800151270,0x40b50802e100148001514f0,0x81121004ce00151580,0x40970802e1000ca00151660,0x40950800e10014c001517c0,0x814e300148001518b0,0x40e90800a2000ca00151ea0,0x410d0801a1000ca00151f60,0x81de1002ce00152280,0x40a70800e2000ca00152320,0x41191000a1000c800152530,0x40fb0800e1000cc001525c0,0x824a2000ce00152680,0x81161004ce00152880,0x410f0801a1000ca00152920,0x40970800e10014c00152940,0x40df0802610014800152c10,0x81e21002ce00152d80,0x411b1000a1000c800152e90,0x40890803e10014800152f30,0x40fb0802210014800153570,0x813a10044e00153680,0x40b30800a1000ce00153e80], [0x42ab0800a1000ca001500a0,0x41750801610014800150230,0x424b0800e10014800150410,0x82de1001ce00150480,0x41c90800a2000c800150550,0x413d0801a100148001507d0,0x41eb0800e1000ca001508e0,0x4139080161000ca00150b20,0x82fe3000ca00150ca0,0x42b30800a1000ca00150fa0,0x41cd0800a2000c800151090,0x42510800e10014800151130,0x41cf0800a2000c800151630,0x841210014e00151680,0x417b08016100148001516d0,0x82ea1001ce00151980,0x841610014e00151b80,0x413d080161000ca00151ba0,0x41f30800e1000ca00151de0,0x42570800e10014800151e50,0x830a3000ca001520e0,0x41d30800a2000c800152170,0x42bd0800a1000ca00152260,0x42590800e100148001522b0,0x417f0801610014800152490,0x41f70800e1000ca00152860,0x82f61001ce00152e80,0x425f0800e10014800152fd0,0x42c50800a1000ca00153160,0x41fd0800e1000ca00153820,0x41850801610014800153930,0x831a3000ca00153be0,0x82fe1001ce00153c80,0x42650800e10014800153cf0], [0x45570800a1000c800150190,0x85ba1001cc001502c0,0x86b21000ce00150580,0x455d0800a1000c800150730,0x86b61000ce00150880,0x85c61001cc00150d40,0x86be1000ce00150e80,0x45650800a1000c800150eb0,0x88fe2000ca00150ee0,0x89022000ca00151120,0x85ce1001cc00151440,0x89162000ca00151c60,0x45770800a1000c800151f90,0x85de1001cc00152240,0x86da1000ce00152380,0x89262000ca00152560,0x45810800a1000c8001528f0,0x86e21000ce00152980,0x86e61000ce00152c80,0x85ea1001cc00152cc0,0x893a2000ca001530a0,0x86ee1000ce00153280,0x85f21001cc001533c0,0x458f0800a1000c800153610,0x89462000ca00153760,0x45930800a1000c8001539d0,0x45950800a1000c800153bb0,0x89522000ca00153e20,0x45990800a1000c800153f70], [0x9ad21000ca00150760,0x1284ce00150980,0x9af21000ca00150d60,0x1287ce00150f80,0x9b021000ca00151060,0x12884e00151080,0x9b0a1000ca001511e0,0x9b0e1000ca001512a0,0x9b161000ca00151420,0x9b1a1000ca001514e0,0x128c4e00151880,0x128e4e00151c80,0x9b461000ca00151d20,0x128f4e00151e80,0x9b561000ca00152020,0x12924e00152480,0x9b6e1000ca001524a0,0x9b7a1000ca001526e0,0x9b8e1000ca00152aa0,0x9b921000ca00152b60,0x1295ce00152b80,0x9b9a1000ca00152ce0,0x9ba61000ca00152f20,0x9baa1000ca00152fe0,0x12984e00153080,0x1298ce00153180,0x9bb61000ca00153220,0x1299ce00153380,0x9bca1000ca001535e0,0x9bce1000ca001536a0,0x129bce00153780,0x129d4e00153a80,0x9be61000ca00153b20,0x129ece00153d80,0x9bfa1000ca00153ee0,0x129fce00153f80,0x9bfe1000ca00153fa0], [0xa006100148001500f0,0xa01e100148001504b0,0xa03e100148001509b0,0xa04210014800150a50,0xa04a10014800150b90,0xa05610014800150d70,0xa072100148001511d0,0xa07a10014800151310,0xa07e100148001513b0,0xa0a210014800151950,0xa0d2100148001520d0,0xa0e6100148001523f0,0xa0f2100148001525d0,0xa0f610014800152670,0xa10a10014800152990,0xa10e10014800152a30,0xa12210014800152d50,0xa12610014800152df0,0xa13a10014800153110,0xa146100148001532f0,0xa14a10014800153390,0xa15e100148001536b0,0xa16210014800153750,0xa17610014800153a70,0xa18210014800153c50,0xa19210014800153ed0], [0xc71e2000c40015001c,0xc72a2000c4001500f4,0xc74e2000c40015037c,0xc75a2000c400150454,0xc7622000c4001504e4,0xc77e2000c4001506dc,0xc78a2000c4001507b4,0xc7922000c400150844,0xc7aa2000c4001509f4,0xc7ba2000c400150b14,0xc7c62000c400150bec,0xc7de2000c400150d9c,0xc7e62000c400150e2c,0xc7f22000c400150f04,0xc80a2000c4001510b4,0xc8162000c40015118c,0xc82e2000c40015133c,0xc8322000c400151384,0xc8522000c4001515c4,0xc87a2000c400151894,0xc8822000c400151924,0xc8862000c40015196c,0xc89a2000c400151ad4,0xc8be2000c400151d5c,0xc8ce2000c400151e7c,0xc8d62000c400151f0c,0xc8f22000c400152104,0xc8fa2000c400152194,0xc8fe2000c4001521dc,0xc90a2000c4001522b4,0xc9362000c4001525cc,0xc9422000c4001526a4,0xc95e2000c40015289c,0xc96a2000c400152974,0xc9762000c400152a4c,0xc98a2000c400152bb4,0xc9962000c400152c8c,0xc99a2000c400152cd4,0xc9ae2000c400152e3c,0xc9b22000c400152e84,0xc9ba2000c400152f14,0xc9be2000c400152f5c,0xc9ea2000c400153274,0xc9ee2000c4001532bc,0xc9f62000c40015334c,0xca022000c400153424,0xca0e2000c4001534fc,0xca262000c4001536ac,0xca322000c400153784,0xca4e2000c40015397c,0xca622000c400153ae4,0xca7a2000c400153c94,0xca862000c400153d6c,0xca962000c400153e8c,0xca9e2000c400153f1c], [0x1000a3000d200154600]]
set_option maxRecDepth 10000 in
private def witnessesBlock96 : Array (List ℕ) := #[[0x40130801a1002ce00154e80,0x80262000d600155800,0x100265000c400155aac,0x20098400d0800a2000ca00156d60,0x400b1000a4000c800157030,0x40131000e1000ce00157480,0x1002de00158000], [0x2014840071000a1000c800154150,0x40170801a2000ce00154180,0x401f0803a1000ce00154480,0x4035080221000ce00154780,0x20128400d0800a2000c8001548d0,0x402b0800e2000ce00154a80,0x40251000e1000cc00154fc0,0x402b1000a4000c40015508c,0x4029080261001cc00155340,0x803e1002d400155400,0x4017080221001ce00155880,0x401d0800e3000cc00155a40,0x40350802e2000ca00155b60,0x401d0802610014e00156180,0x200e840110800a2000c800156a90,0x40251000a1000ce00156b80,0x201a840070800a1000cc00156f40,0x402b0801a10014e00157580,0x402f080221001cc00157640,0x200b8400d1000a1000c800157990,0x402b0803a2000ca00157ae0], [0x40610804a1000ca001541e0,0x404908076100148001541f0,0x406d080162000ca001544e0,0x403d080761000ca001545a0,0x809210094e00154680,0x40470807a10014800154970,0x40650805610014800154d30,0x4047080222000ca00154de0,0x80ca3000ce00155380,0x40611000a2000c800155410,0x4047080161001cc001556c0,0x4059080521000ca00155860,0x4053080161000ce00155980,0x406b0805210014800155af0,0x403d0800a2000ce00155c80,0x8086100a4e00155d80,0x40530806a10014800155eb0,0x40830800e1000ce00155f80,0x80b21007ce00156380,0x407f0803a1000ca00156520,0x404f0800e10014e00156680,0x40670805610014800156810,0x40470801a1000ce00156880,0x8076100bce00156a80,0x403d0801a1001cc00156bc0,0x80ce3000ce00156e80,0x40490807a10014800156f90,0x404f0805e1000ca00157060,0x4049080222000ca00157420,0x406d0805210014800157490,0x2023840070800a2000c8001575d0,0x4071080162000ca00157660,0x40650804a1000ca00157960,0x40590800e2000cc001579c0,0x4049080161001cc00157d40,0x80c210074e00157e80], [0x40ef0800a2000ca00154060,0x40d3080221000ca00154120,0x408b0803e10014800154290,0x40e308026100148001543d0,0x41010800e1000cc00154540,0x40950803a10014800154650,0x41150801a1000ca00154660,0x815a30014800154790,0x409d0802e1000ca00154a20,0x40f10800a2000ca00154ba0,0x40b50800a1000ce00154d80,0x40e50802610014800154fb0,0x40bf080261000ca001550e0,0x40ad0800e2000ca00155260,0x41010802210014800155550,0x40970803a10014800155870,0x41190801a1000ca001559e0,0x811210015200155a00,0x81a610034e00155b80,0x40bf0802e10014800155cd0,0x41251000a1000c800155d70,0x409d0800e10014c00155dc0,0x40c1080261000ca00155f20,0x411b0801a1000ca001563a0,0x81f61002ce00156480,0x41070800e1000cc001564c0,0x82662000ce00156580,0x40e90802610014800156770,0x814610044e00156980,0x40c10802e10014800156b30,0x811610015200156e00,0x41070802210014800157530,0x816630014800157670,0x826e2000ce00157780,0x40c5080261000ca00157ba0,0x40a30802e1000ca00157de0], [0x414b0801a100148001540b0,0x41df0800a2000c800154330,0x42cf0800a1000ca00154420,0x42690800e100148001545b0,0x843a10014e00154880,0x83223000ca00154960,0x426b0800e10014800154a10,0x830a1001ce00155180,0x418d08016100148001554b0,0x414b080161000ca00155560,0x844610014e00155780,0x42090800e1000ca001557a0,0x41510801a10014800155910,0x41e70800a2000c8001559b0,0x420b0800e1000ca00155ce0,0x41910801610014800156270,0x42770800e10014800156450,0x83323000ca00156460,0x41eb0800a2000c8001564f0,0x831a1001ce00156d80,0x4151080161000ca00156e20,0x845a10014e00157080,0x42810800e10014800157a30,0x41f30800a2000c800157b70,0x83221001ce00157b80,0x41990801610014800157df0,0x42830800e10014800157e90,0x846610014e00157f80], [0x86021001cc001541c0,0x459f0800a1000c800154510,0x89622000ca00154720,0x860a1001cc001548c0,0x45a70800a1000c800154c90,0x45ab0800a1000c800155050,0x87161000ce00155080,0x45ad0800a1000c800155230,0x42d70800a1000ca00155320,0x897a2000ca001554a0,0x871e1000ce00155680,0x45b30800a1000c8001557d0,0x89822000ca00155920,0x42dd0800a1000ca00155e60,0x898e2000ca00155fe0,0x86261001cc00156140,0x872e1000ce00156280,0x45bf0800a1000c800156310,0x899a2000ca001566a0,0x899e2000ca001568e0,0x42e30800a1000ca001569a0,0x45c90800a1000c800156c70,0x45cb0800a1000c800156e50,0x89aa2000ca00156fa0,0x42e70800a1000ca00157120,0x87421000ce00157180,0x45cf0800a1000c800157210,0x863a1001cc001572c0,0x45d10800a1000c8001573f0,0x45d50800a1000c8001577b0,0x89c22000ca00157d20,0x45db0800a1000c800157d50,0x87521000ce00157d80], [0x12a04e00154080,0x12a14e00154280,0x9c121000ca00154360,0x12a2ce00154580,0x9c2e1000ca001548a0,0x12a4ce00154980,0x9c3a1000ca00154ae0,0x12a5ce00154b80,0x9c421000ca00154c60,0x12a64e00154c80,0x9c4e1000ca00154ea0,0x12a7ce00154f80,0x9c5e1000ca001551a0,0x9c6a1000ca001553e0,0x12aa4e00155480,0x12aace00155580,0x9c761000ca00155620,0x12ad4e00155a80,0x9c961000ca00155c20,0x12af4e00155e80,0x12b04e00156080,0x9cae1000ca001560a0,0x12b3ce00156780,0x12b64e00156c80,0x12b94e00157280,0x12b9ce00157380,0x12bb4e00157680,0x12bc4e00157880,0x12bcce00157980], [0xa1ce10014800154830,0xa1e210014800154b50,0xa1e610014800154bf0,0xa1fa10014800154f10,0xa20a10014800155190,0xa21610014800155370,0xa22a10014800155690,0xa24e10014800155c30,0xa25a10014800155e10,0x9cb21000ca00156160,0xa272100148001561d0,0x9cba1000ca001562e0,0xa28a10014800156590,0xa28e10014800156630,0x9cd61000ca00156820,0x9ce21000ca00156a60,0xa2b210014800156bd0,0x9cea1000ca00156be0,0xa2be10014800156db0,0x9cfa1000ca00156ee0,0xa2c610014800156ef0,0xa2d2100148001570d0,0x9d0e1000ca001572a0,0xa2de100148001572b0,0x9d1e1000ca001575a0,0x9d2a1000ca001577e0,0xa30210014800157850,0xa306100148001578f0,0x9d361000ca00157a20,0xa31a10014800157c10]]
set_option maxRecDepth 10000 in
private def witnessesBlock97 : Array (List ℕ) := #[[0xcae62000c40015442c,0xcb022000c400154624,0xcb1a2000c4001547d4,0xcb262000c4001548ac,0xcb2e2000c40015493c,0xcb3a2000c400154a14,0xcb3e2000c400154a5c,0xcb562000c400154c0c,0xcb622000c400154ce4,0xcb7a2000c400154e94,0xcb9a2000c4001550d4,0xcb9e2000c40015511c,0xcbb22000c400155284,0xcbc22000c4001553a4,0xcbee2000c4001556bc,0xcbf22000c400155704,0xcc0a2000c4001558b4,0xcc162000c40015598c,0xcc1e2000c400155a1c,0xcc2a2000c400155af4,0xcc4e2000c400155d7c,0xcc522000c400155dc4,0xcc6a2000c400155f74,0xcc762000c40015604c,0xcc7e2000c4001560dc,0xcc962000c40015628c,0xcca62000c4001563ac,0xccb22000c400156484,0xccca2000c400156634,0xccd22000c4001566c4,0xccde2000c40015679c,0xccf62000c40015694c,0xcd022000c400156a24,0xcd062000c400156a6c,0xcd1e2000c400156c1c,0xcd362000c400156dcc,0xcd3e2000c400156e5c,0xcd5a2000c400157054,0xcd662000c40015712c,0xcd862000c40015736c,0xcd922000c400157444,0xcd962000c40015748c,0xcdaa2000c4001575f4,0xcdba2000c400157714,0xcdde2000c40015799c,0xcdea2000c400157a74,0xce2e2000c400157f3c,0xce322000c400157f84], [0x40070800a4000ce00158980,0x80070800a1000d20015be00], [0x800d0800a3000c8001591f0,0x400d0801610015200159600,0x400d1000e2000cc00159940,0x40111000a3000ca00159a60,0x40130800a5000c80015a2d0,0x2005840071000a1000cc0015a3c0,0x100161000d40015ac00,0x4013080222000ce0015ad80,0x801a1001d80015b000,0x80223001cc0015b1c0,0x400d1000a2000ce0015b680], [0x402f0800a1000d200158200,0x401f0801a1001ce00158280,0x2015840071000a1000c8001582f0,0x40290802e1000ce00158680,0x200b8400b0800a2000ca00158f20,0x200f880070800a1000c800159010,0x4025080161001ce00159080,0x805e5000ca001593a0,0x402b080261001cc001595c0,0x40290803e2000ca001595e0,0x806a3000d000159700,0x401d080162000ce00159b80,0x802e30014e00159d80,0x1003e1000ce0015a180,0x804a4001480015a550,0x20178400b0800a2000c80015ae10,0x2012840070800a2000ca0015b0e0,0x40350801610014e0015b180,0x401f0800e3000cc0015b8c0,0x401d0800a4000ca0015bc20], [0x40470806a1000ca00158320,0x80761000d600158800,0x1008e2000c6001589c8,0x40610801a2000ca00158aa0,0x40651000a2000c800158c50,0x40490801a1000ce00158f80,0x40830803a1000ca001590a0,0x40610805e100148001590b0,0x40670804a1000ca00159520,0x4043080262000ca00159820,0x807a100bce00159980,0x4059080561000ca00159b20,0x2024840070800a2000c800159d30,0x406b0805610014800159dd0,0x8086100ace0015a080,0x80d63000ce0015a480,0x4071080521001480015a7d0,0x40671000a2000c80015a870,0x40490806a1000ca0015aae0,0x40530800e10014e0015ac80,0x808e100a4e0015af80,0x404f080761001480015b090,0x80fe1005ce0015b480,0x809e10094e0015b580,0x40530805e1000ca0015b6e0,0x807a1000d60015b800,0x80ca10074e0015b880,0x406d080561001480015b8b0,0x407f0804a1001480015bc70,0x4059080161000ce0015bc80,0x80da3000ce0015bf80], [0x40b30800e2000ca001581a0,0x40fb0800a2000ca001583e0,0x410d0800e1000cc00158440,0x82021002ce00158580,0x816a30014800158610,0x812a1004ce00158780,0x40c50802e100148001587f0,0x40c7080261000ca001589e0,0x40ef0802610014800158b10,0x814e10044e00158b80,0x40df080221000ca00158da0,0x410f0800e1000cc00158ec0,0x409d0803a10014800158ed0,0x40b50800e2000ca00159160,0x40a30800e10014c00159240,0x41250801a1000ca00159460,0x410d0802210014800159510,0x40c70802e10014800159650,0x40f108026100148001596f0,0x40bf0800a1000ce00159880,0x812e1004ce00159a80,0x40890800e1000ce00159e80,0x41331000a1000c800159f10,0x410f0802210014800159fb0,0x40a70802e1000ca0015a060,0x40950803e1001480015a370,0x41010800a2000ca0015a5a0,0x820e1002ce0015a680,0x40e3080221000ca0015a720,0x40c10800a1000ce0015a780,0x81be10034e0015a980,0x41150800e1000cc0015ae40,0x41371000a1000c80015b1d0,0x408b0800e1000ce0015b380,0x40e5080221000ca0015b3e0,0x40a70800e10014c0015b540,0x40970803e1001480015b6d0,0x815a10044e0015be80,0x4115080221001480015bf90], [0x82722000ce00158080,0x415b0801a100148001581b0,0x83463000ca00158620,0x41f70800a2000c8001586b0,0x42870800e10014800158750,0x415d0801a100148001589d0,0x421d0800e1000ca00158c20,0x834a3000ca00158ce0,0x847210014e00158e80,0x827a2000ce00159280,0x847610014e00159380,0x428d0800e10014800159470,0x415b080161000ca00159760,0x83321001ce00159780,0x41fd0800a2000c800159790,0x41610801a10014800159a10,0x42230800e1000ca00159be0,0x415d080161000ca00159fa0,0x41a3080161001480015a050,0x42930800e1001480015a190,0x848210014e0015a280,0x42950800e1001480015a5f0,0x41a5080161001480015a730,0x835e3000ca0015aea0,0x4161080161000ca0015b020,0x41670801a1001480015b270,0x83623000ca0015b560,0x422d0800e1000ca0015b620,0x42090800a2000c80015b950,0x83461001ce0015ba80,0x41391000a1000c80015bb30,0x849610014e0015bb80,0x420b0800a2000c80015bef0], [0x42ef0800a1000ca00158020,0x875a1000ce00158380,0x86521001cc001587c0,0x89d62000ca00158860,0x45e70800a1000c800158890,0x86561001cc00158b40,0x42f50800a1000ca00158b60,0x87661000ce00158c80,0x42f90800a1000ca001592e0,0x45f30800a1000c8001593d0,0x87721000ce00159580,0x45fb0800a1000c800159b50,0x89fa2000ca00159ca0,0x866a1001cc00159cc0,0x89fe2000ca00159ee0,0x866e1001cc0015a040,0x43010800a1000ca0015a1e0,0x8a062000ca0015a360,0x46070800a1000c80015a690,0x86761001cc0015a740,0x43050800a1000ca0015a960,0x8a122000ca0015aa20,0x878e1000ce0015aa80,0x867a1001cc0015aac0,0x460d0800a1000c80015ac30,0x8a162000ca0015ac60,0x46110800a1000c80015aff0,0x87961000ce0015b080,0x8a222000ca0015b320,0x46170800a1000c80015b590,0x8a2a2000ca0015b7a0,0x87a21000ce0015b980,0x8a2e2000ca0015b9e0,0x868e1001cc0015bc40,0x461f0800a1000c80015bd10,0x8a362000ca0015be60]]
set_option maxRecDepth 10000 in
private def witnessesBlock98 : Array (List ℕ) := #[[0x12c0ce00158180,0x12c44e00158880,0x12c54e00158a80,0x12c6ce00158d80,0x12c8ce00159180,0x12ca4e00159480,0x12cb4e00159680,0x12cfce00159f80,0x12d1ce0015a380,0x12d44e0015a880,0x12d5ce0015ab80,0x12d74e0015ae80,0x12d94e0015b280,0x12dbce0015b780,0x12dece0015bd80], [0xa33610014800158070,0xa34210014800158250,0x9d621000ca00158260,0xa34a10014800158390,0xa34e10014800158430,0x9d6e1000ca001584a0,0x9d721000ca00158560,0xa35610014800158570,0x9d861000ca00158920,0xa38610014800158cf0,0xa38a10014800158d90,0x9da21000ca00158e60,0x9daa1000ca00158fe0,0xa3a210014800159150,0x9db61000ca00159220,0xa3ae10014800159330,0xa3ce10014800159830,0x9dda1000ca001598e0,0x9dde1000ca001599a0,0xa3de10014800159ab0,0xa3ea10014800159c90,0x9df21000ca00159d60,0xa3f610014800159e70,0x9e0e1000ca0015a2a0,0xa41a1001480015a410,0x9e161000ca0015a420,0x9e1a1000ca0015a4e0,0x9e2e1000ca0015a8a0,0xa43a1001480015a910,0xa43e1001480015a9b0,0xa4461001480015aaf0,0xa4521001480015acd0,0xa4561001480015ad70,0x9e4a1000ca0015ade0,0xa4621001480015af50,0x9e521000ca0015af60,0xa46e1001480015b130,0x9e621000ca0015b260,0xa4821001480015b450,0xa48e1001480015b630,0x9e861000ca0015b920,0xa4a61001480015b9f0,0x9e8e1000ca0015baa0,0x9e9a1000ca0015bce0,0x9e9e1000ca0015bda0,0xa4be1001480015bdb0,0x9ea61000ca0015bf20], [0xce6a2000c400158374,0xce6e2000c4001583bc,0xce9a2000c4001586d4,0xcea62000c4001587ac,0xceaa2000c4001587f4,0xcebe2000c40015895c,0xced62000c400158b0c,0xceda2000c400158b54,0xcee62000c400158c2c,0xceee2000c400158cbc,0xcefe2000c400158ddc,0xcf2a2000c4001590f4,0xcf362000c4001591cc,0xcf3a2000c400159214,0xcf4e2000c40015937c,0xcf5e2000c40015949c,0xcf662000c40015952c,0xcf722000c400159604,0xcf822000c400159724,0xcf8a2000c4001597b4,0xcfa22000c400159964,0xcfc62000c400159bec,0xcfde2000c400159d9c,0xd0062000c40015a06c,0xd00e2000c40015a0fc,0xd01a2000c40015a1d4,0xd0262000c40015a2ac,0xd0362000c40015a3cc,0xd03e2000c40015a45c,0xd0422000c40015a4a4,0xd0622000c40015a6e4,0xd07a2000c40015a894,0xd07e2000c40015a8dc,0xd0922000c40015aa44,0xd0a22000c40015ab64,0xd0b62000c40015accc,0xd0ba2000c40015ad14,0xd0c22000c40015ada4,0xd0ce2000c40015ae7c,0xd0ea2000c40015b074,0xd1022000c40015b224,0xd12e2000c40015b53c,0xd13e2000c40015b65c,0xd1762000c40015ba4c,0xd17a2000c40015ba94,0xd1822000c40015bb24,0xd1aa2000c40015bdf4,0xd1b22000c40015be84,0xd1b62000c40015becc,0xd1be2000c40015bf5c], [0x1000e5000ca0015d060,0x800e3000d60015e800], [0x20088400b0800e2000ca0015c0a0,0x20068800b0800a1000c80015c2b0,0x400b0800a3000d00015cd00,0x40112000a2000c40015d624,0x2009840070800a2000cc0015d840,0x180162000ca0015d960,0x2009840111000a1000c80015ea10,0x2005880070800a2000c80015ebf0,0x80110800e1000cc0015ed40,0x400d2000a1000c80015f370,0x40110800a2000d20015fa00,0x180221001480015ff50], [0x401f0802610014e0015c080,0x402f0800e2000ce0015c880,0x200f840110800a2000c80015ca30,0x402b0802e1000ce0015cb80,0x402f1000a4000c40015cf1c,0x80170800a2000c80015cfd0,0x40250802e1001cc0015d140,0x200e8400b1000a1000c80015d750,0x20148400d0800a2000c80015db10,0x402b0803e2000ca0015dba0,0x40291000e1000cc0015e2c0,0x4035080261000ce0015e680,0x402f0801a10014e0015f780,0x4017080261001ce0015f980,0x402f0803a2000ca0015fd60,0x401f080162000ce0015fe80], [0x40590806a1001480015c210,0x407f0803e1000ca0015c460,0x40650801a2000ca0015c520,0x4043080761000ca0015ca60,0x40650805e1001480015cb70,0x406b0804a1000ca0015cca0,0x4047080861001480015ce90,0x4061080521000ca0015d360,0x80ce10074e0015d580,0x8092100a4e0015d880,0x100922000c60015dac8,0x80c21007ce0015df80,0x403b080221000ce0015e080,0x406b1000a2000c80015e0b0,0x404f0807a1001480015e1f0,0x40670801a2000ca0015e260,0x81061005ce0015e280,0x40430800a2000ce0015e380,0x404f080222000ca0015e6e0,0x406d0804a1000ca0015e860,0x40670805e1001480015e8d0,0x40830804a1001480015eab0,0x4047080262000ca0015eda0,0x4071080561001480015ee70,0x404f080161001cc0015f0c0,0x40830803e1000ca0015f2e0,0x40430801a1001cc0015f440,0x80e23000ce0015f580,0x808e100ace0015f680,0x403b0802e2000ca0015f6a0,0x40610800e2000cc0015f7c0,0x4049080861001480015f870,0x4053080761001480015fa50,0x40430807a1000ca0015fca0,0x406d1000a2000c80015fcd0,0x80a610094e0015ff80], [0x41190800e1000cc0015c340,0x81c610034e0015c380,0x40a30803a1001480015c530,0x40c50800a1000ce0015c580,0x41070800a2000ca0015c760,0x821a1002ce0015c780,0x40e9080221000ca0015cd60,0x411b0800e1000cc0015cdc0,0x81ca10034e0015d080,0x40890803a1000ca0015d1e0,0x812a1001520015d200,0x40fb080261001480015d250,0x821e1002ce0015d280,0x813a1004ce0015d380,0x40ad0802e1000ca0015d420,0x817e3001480015d430,0x40c70800a1000ce0015d480,0x4119080221001480015d4d0,0x41330801a1000ca0015d8a0,0x40d3080261000ca0015df60,0x411b080221001480015df70,0x40bf0800e2000ca0015e020,0x81823001480015e3d0,0x812e1001520015e600,0x408b0803a1000ca0015e7a0,0x410d0800a2000ca0015e920,0x40a70803a1001480015e970,0x40ad0800e10014c0015e9c0,0x81d210034e0015ea80,0x41370801a1000ca0015ec20,0x40d30802e1001480015ec90,0x40c10800e2000ca0015efe0,0x409d0803e1001480015f0f0,0x816610044e0015f180,0x822a1002ce0015f380,0x40ef080221000ca0015f3a0,0x410f0800a2000ca0015f460,0x4101080261001480015f5f0]]
set_option maxRecDepth 10000 in
private def witnessesBlock99 : Array (List ℕ) := #[[0x42a10800e1001480015c030,0x834a1001ce0015c180,0x42330800e1000ca0015c5e0,0x4167080161000ca0015c8e0,0x42a50800e1001480015c8f0,0x41af080161001480015c990,0x836e3000ca0015c9a0,0x84a210014e0015ca80,0x413d1000a1000c80015cdf0,0x41b1080161001480015d070,0x82962000ce0015d180,0x416f0801a1001480015d2f0,0x42390800e1000ca0015d5a0,0x42ab0800e1001480015d610,0x83763000ca0015d720,0x84ae10014e0015d980,0x423b0800e1000ca0015dae0,0x84b210014e0015de80,0x835e1001ce0015e480,0x41b7080161001480015e510,0x42b30800e1001480015e790,0x416f080161000ca0015e9e0,0x42410800e1000ca0015eaa0,0x41750801a1001480015eb50,0x83823000ca0015eb60,0x83621001ce0015eb80,0x82a22000ce0015ec80,0x84be10014e0015ed80,0x421d0800a2000c80015f190,0x41bb080161001480015f2d0,0x41390801a1000ca0015f5e0,0x84ca10014e0015fc80,0x42bd0800e1001480015fd70], [0x46230800a1000c80015c0d0,0x87ae1000ce0015c280,0x43130800a1000ca0015c3a0,0x462b0800a1000c80015c850,0x8a4e2000ca0015cbe0,0x462f0800a1000c80015cc10,0x8a522000ca0015ce20,0x87be1000ce0015ce80,0x86aa1001cc0015d4c0,0x8a5e2000ca0015d4e0,0x431d0800a1000ca0015d660,0x87ca1000ce0015d780,0x463d0800a1000c80015d930,0x86b21001cc0015dbc0,0x46410800a1000c80015dcf0,0x86b61001cc0015df40,0x46470800a1000c80015e290,0x46490800a1000c80015e470,0x86be1001cc0015e640,0x464d0800a1000c80015e830,0x87e21000ce0015e980,0x43290800a1000ca0015ece0,0x46530800a1000c80015edd0,0x87ea1000ce0015ef80,0x432b0800a1000ca0015f0a0,0x87f61000ce0015f880,0x8aa22000ca0015fb20,0x87fa1000ce0015fb80,0x86da1001cc0015fec0], [0x12e24e0015c480,0x12e34e0015c680,0x12e4ce0015c980,0x12e64e0015cc80,0x12e6ce0015cd80,0x12edce0015db80,0x12ee4e0015dc80,0x12f0ce0015e180,0x12f2ce0015e580,0x12f3ce0015e780,0x12f74e0015ee80,0x46550800a1000c80015efb0,0x12f84e0015f080,0x12fa4e0015f480,0x465b0800a1000c80015f550,0x12fd4e0015fa80,0x12fece0015fd80,0x46650800a1000c80015feb0], [0x9eb21000ca0015c160,0x9eb61000ca0015c220,0xa4e21001480015c350,0xa4e61001480015c3f0,0xa4f21001480015c5d0,0x9ece1000ca0015c6a0,0xa4fa1001480015c710,0x9ed61000ca0015c820,0xa51e1001480015ccb0,0xa52e1001480015cf30,0x9efe1000ca0015cfa0,0xa55e1001480015d6b0,0x9f2a1000ca0015d7e0,0xa5661001480015d7f0,0xa56a1001480015d890,0xa5721001480015d9d0,0xa57e1001480015dbb0,0xa5821001480015dc50,0x9f421000ca0015dc60,0x9f461000ca0015dd20,0x9f4e1000ca0015dea0,0xa59a1001480015e010,0x9f5a1000ca0015e0e0,0xa5a21001480015e150,0x9f661000ca0015e320,0x9f6a1000ca0015e3e0,0xa5be1001480015e5b0,0x9f761000ca0015e620,0x9fa21000ca0015ee60,0xa5fa1001480015ef10,0x9fa61000ca0015ef20,0x9fb21000ca0015f160,0xa60e1001480015f230,0xa61a1001480015f410,0x9fd21000ca0015f760,0xa6321001480015f7d0,0x9fde1000ca0015f9a0,0xa64e1001480015fc30,0xa65a1001480015fe10,0x9ff61000ca0015fe20,0x9ffa1000ca0015fee0], [0xd1da2000c40015c154,0xd1ee2000c40015c2bc,0xd2062000c40015c46c,0xd20a2000c40015c4b4,0xd2222000c40015c664,0xd2422000c40015c8a4,0xd2462000c40015c8ec,0xd27e2000c40015ccdc,0xd28e2000c40015cdfc,0xd2ba2000c40015d114,0xd2ca2000c40015d234,0xd2d22000c40015d2c4,0xd2de2000c40015d39c,0xd2ea2000c40015d474,0xd3062000c40015d66c,0xd30e2000c40015d6fc,0xd31e2000c40015d81c,0xd3362000c40015d9cc,0xd3422000c40015daa4,0xd34e2000c40015db7c,0xd3562000c40015dc0c,0xd37e2000c40015dedc,0xd3862000c40015df6c,0xd3aa2000c40015e1f4,0xd3ae2000c40015e23c,0xd3c62000c40015e3ec,0xd3d22000c40015e4c4,0xd3da2000c40015e554,0xd3e62000c40015e62c,0xd4022000c40015e824,0xd4262000c40015eaac,0xd43a2000c40015ec14,0xd44a2000c40015ed34,0xd45e2000c40015ee9c,0xd49e2000c40015f31c,0xd4aa2000c40015f3f4,0xd4be2000c40015f55c,0xd4ca2000c40015f634,0xd4d62000c40015f70c,0xd4da2000c40015f754,0xd4e62000c40015f82c,0xd5062000c40015fa6c,0xd5122000c40015fb44,0xd5162000c40015fb8c,0xd52e2000c40015fd3c,0xd53a2000c40015fe14], [0x1800e2000ce00160780,0x80071000a4000c400160e64,0x2000a4000c600162e08,0x40070800a6000c800163ab0], [0x400b0800e10015400160400,0x400b1800a2000ca00160ae0,0x400d0800a1000d600161800,0x801a5000ce00162b80], [0x40291000a1000ce00160180,0x2017840071000a1000c800160630,0x200e840130800a2000c800160db0,0x40251000a3000c8001618f0,0x402f080261001cc00161ac0,0x401f0800a4000ca00162160,0x200b8400d0800e1000cc001621c0,0x20158400d0800a2000c800162430,0x40250802210014e00162480,0x401f0803a1001cc00162540,0x80290800a1000c8001627f0,0x4035080221001cc001628c0,0x4029080161001ce00162a80,0x402b1000e1000cc00162c40,0x40350800a1000d200163600,0x200f8400b1000a1000c800163e70]]
set_option maxRecDepth 10000 in
private def witnessesBlock100 : Array (List ℕ) := #[[0x404f0801a1000ce00160480,0x201d840070800a1000cc00160cc0,0x80d610074e00160f80,0x4065080521000ca001610e0,0x2027840070800a2000c800161350,0x403d080221000ce00161380,0x40590800e10014e00161580,0x4049080262000ca00161860,0x8076100d4e00161b80,0x4061080561000ca00161c20,0x406b0801a2000ca00161ce0,0x80ca1007ce00161d80,0x40710804a1000ca00161fe0,0x40590805e1000ca001620a0,0x8092100ace00162180,0x404f0806a1000ca00162220,0x4047080761000ca001622e0,0x406b0805e10014800162390,0x407f080162000ca001623a0,0x8086100bce00162680,0x403d0802e2000ca00162a60,0x80da10074e00162c80,0x40530807a10014800162e30,0x4067080521000ca00162fa0,0x4053080222000ca00163360,0x40711000a2000c800163510,0x40650800e2000cc001636c0,0x80763000d000163900,0x406d0801a2000ca00163a20,0x80ce1007ce00163c80,0x40470800a2000ce00163d80,0x4053080161001cc00163dc0], [0x40f1080221000ca00160060,0x41250800e1000cc00160240,0x816a10044e00160280,0x818a30014800160310,0x40b30802e1000ca001607e0,0x82321002ce00160980,0x81461004ce00160c80,0x40c50800e2000ca00160f60,0x81de10034e00161180,0x818e300148001612b0,0x82361002ce00161480,0x41250802210014800161490,0x41150800a2000ca00161620,0x40b50802e1000ca00161920,0x41070802610014800161990,0x40950800e1000ce00161c80,0x40b30800e10014c00161e40,0x81e210034e00161e80,0x40c70800e2000ca00161f20,0x40ad0803a10014800161fd0,0x813a10015200162200,0x81121005ce00162780,0x40a30803e10014800162b10,0x41190800a2000ca00162ca0,0x40d30800a1000ce00162e80,0x40b50800e10014c00162fc0,0x40890804a10014800163010,0x40970800e1000ce00163180,0x814e1004ce00163280,0x40df080261000ca001634e0,0x411b0800a2000ca001637e0,0x40890803e1000ca001638a0,0x410d0802610014800163d30,0x81161005ce00163e80], [0x836e1001ce00160080,0x42230800a2000c800160270,0x4175080161000ca001602a0,0x417b0801a100148001603b0,0x424b0800e1000ca001604e0,0x83923000ca00160660,0x84d210014e00160680,0x41c10801610014800160770,0x413d0801a1000ca00160960,0x84d610014e00160b80,0x83761001ce00160e80,0x42c50800e10014800160ef0,0x414b1000a1000c800160f90,0x839a3000ca001613e0,0x417f0801a100148001613f0,0x42510800e1000ca001614a0,0x82b62000ce00161980,0x839e3000ca00161aa0,0x417b080161000ca00161b60,0x422d0800a2000c800161e90,0x82ba2000ce00162280,0x41c908016100148001622f0,0x83821001ce00162380,0x42570800e1000ca00162460,0x42cf0800e100148001624d0,0x83a63000ca00162820,0x84ee10014e00162980,0x42590800e1000ca001629a0,0x41511000a1000c800162bb0,0x417f080161000ca00162be0,0x41850801a10014800162c50,0x42330800a2000c800162f70,0x41cd08016100148001630b0,0x82c22000ce00163480,0x41cf0801610014800163790,0x425f0800e1000ca00163960,0x83921001ce00163f80], [0x8aae2000ca001601e0,0x43350800a1000ca00160360,0x86e21001cc001605c0,0x43370800a1000ca00160720,0x8aba2000ca001608a0,0x86e61001cc00160940,0x880e1000ce00160a80,0x88121000ce00160d80,0x433b0800a1000ca00160ea0,0x86ee1001cc00161040,0x8aca2000ca001611a0,0x433d0800a1000ca00161260,0x881e1000ce00161680,0x43470800a1000ca00162520,0x88321000ce00162580,0x8aee2000ca001625e0,0x88361000ce00162880,0x8b022000ca00163120,0x87161001cc00163340,0x42d70800e10014800163650,0x884a1000ce00163780,0x871e1001cc00163a40,0x884e1000ce00163a80,0x43550800a1000ca00163f60], [0x1301ce00160380,0x1302ce00160580,0x13044e00160880,0x46790800a1000c800161170,0x13094e00161280,0x467f0800a1000c800161710,0x130bce00161780,0x130c4e00161880,0x46830800a1000c800161ad0,0x46850800a1000c800161cb0,0x13104e00162080,0x1316ce00162d80,0x1317ce00162f80,0x13184e00163080,0x469d0800a1000c800163330,0x131b4e00163680,0x46a10800a1000c8001636f0,0x46a30800a1000c8001638d0,0x131cce00163980,0x131dce00163b80], [0xa0061000ca00160120,0xa66e10014800160130,0xa686100148001604f0,0xa68a10014800160590,0xa01e1000ca001605a0,0xa692100148001606d0,0xa69e100148001608b0,0xa6ae10014800160b30,0xa03e1000ca00160ba0,0xa0421000ca00160c60,0xa6ba10014800160d10,0xa04a1000ca00160de0,0xa0561000ca00161020,0xa6ce10014800161030,0xa6d2100148001610d0,0xa6da10014800161210,0xa0721000ca00161560,0xa6f610014800161670,0xa07a1000ca001616e0,0xa07e1000ca001617a0,0xa70210014800161850,0xa70e10014800161a30,0xa71610014800161b70,0xa72210014800161d50,0xa72610014800161df0,0xa0a21000ca00161e60,0xa73a10014800162110,0xa73e100148001621b0,0xa75e100148001626b0,0xa0d21000ca00162760,0xa77610014800162a70,0xa0e61000ca00162b20,0xa78610014800162cf0,0xa0f21000ca00162d60,0xa0f61000ca00162e20,0xa10a1000ca001631e0,0xa7aa10014800163290,0xa10e1000ca001632a0,0xa7b2100148001633d0,0xa7be100148001635b0,0xa1221000ca00163660,0xa1261000ca00163720,0xa7d610014800163970,0xa7da10014800163a10,0xa13a1000ca00163ae0,0xa7e610014800163bf0,0xa1461000ca00163d20,0xa7f210014800163dd0,0xa14a1000ca00163de0,0xa7fe10014800163fb0], [0xd5722000c400160204,0xd5762000c40016024c,0xd58a2000c4001603b4,0xd59a2000c4001604d4,0xd5ba2000c400160714,0xd5c62000c4001607ec,0xd5d62000c40016090c,0xd5e22000c4001609e4,0xd5f62000c400160b4c,0xd6262000c400160eac,0xd64e2000c40016117c,0xd6622000c4001612e4,0xd6662000c40016132c,0xd67a2000c400161494,0xd67e2000c4001614dc,0xd6962000c40016168c,0xd69e2000c40016171c,0xd6aa2000c4001617f4,0xd6d22000c400161ac4,0xd6da2000c400161b54,0xd6de2000c400161b9c,0xd6f62000c400161d4c,0xd71a2000c400161fd4,0xd72e2000c40016213c,0xd7322000c400162184,0xd7462000c4001622ec,0xd74a2000c400162334,0xd7522000c4001623c4,0xd77a2000c400162694,0xd79a2000c4001628d4,0xd7ce2000c400162c7c,0xd7d62000c400162d0c,0xd7e62000c400162e2c,0xd7f22000c400162f04,0xd7fa2000c400162f94,0xd8122000c400163144,0xd81e2000c40016321c,0xd82e2000c40016333c,0xd8462000c4001634ec,0xd85e2000c40016369c,0xd86a2000c400163774,0xd8722000c400163804,0xd8822000c400163924,0xd8ae2000c400163c3c,0xd8b22000c400163c84,0xd8d22000c400163ec4], [0xc0071000a1000c8001647d0,0x40072000a1000ca001668a0,0x80070800a3000cc001675c0]]
set_option maxRecDepth 10000 in
private def witnessesBlock101 : Array (List ℕ) := #[[0x40131000a3000ca00164320,0x100262000ce00165880,0x80263001cc00165d40,0x100163000ce00166180,0x20088400b0800e10014c00166440,0x400d1000a4000c800166d50,0x20098400b0800e2000ca00166de0,0x400b1000a1000d200167200,0x10035e00168000], [0x805240014800164190,0x40250803a1000ce00164980,0x806a5000ca001649e0,0x40170800e10015200164a00,0x402b1000a1000ce00164c80,0x2014840070800a2000ca00164e60,0x40171800a2000c800165130,0x402f0802e1000ce00165580,0x804a1002d400165c00,0x402f0803e2000ca00166720,0x201a8400b0800a2000c8001667b0,0x40170801a1002ce00166c80,0x40290802e1001cc00167240,0x402b080161001ce00167780,0x802e2000d600167800,0x200f840130800a2000c800167890], [0x4061080161000ce00164080,0x406d0805e100148001640f0,0x201e840070800a1000cc00164140,0x40610806a10014800164690,0x80861000d600164800,0x4049080761000ca00164f20,0x40470801a1001cc00164f40,0x807a100d4e00165080,0x40530801a1000ce00165280,0x809e100a4e00165380,0x40490808e100148001653b0,0x4083080162000ca00165520,0x40670800e2000cc00165640,0x403b0801610014e00165680,0x40470807a1000ca00165820,0x407f0805210014800165b30,0x4065080561000ca00165ca0,0x2029840070800a2000c800166210,0x80e210074e00166680,0x405908076100148001668f0,0x40490800a2000ce00166a80,0x406b080521000ca00166d20,0x80b210094e00166e80,0x807a3000d000166f00,0x40530806a1000ca001671a0,0x40710801a2000ca001674a0,0x404f0808610014800167610,0x80d61007ce00167a80,0x40710805e10014800167bb0,0x40490801a1001cc00167cc0,0x4067080561000ca00167ce0], [0x40fb080221000ca00164020,0x40df0802e100148001642d0,0x408b0804a10014800164730,0x410f0802610014800164910,0x824a1002ce00164b80,0x41330800e1000cc00164bc0,0x408b0803e1000ca00164fe0,0x40e3080261000ca00165160,0x40a70803e100148001651d0,0x40950803a1000ca00165460,0x40b30803a10014800165630,0x817e10044e00165780,0x814610015200165e00,0x41330802210014800165ef0,0x81f610034e00165f80,0x40e30802e10014800165f90,0x40e5080261000ca00165fa0,0x41370800e1000cc001660c0,0x4101080221000ca00166660,0x40b50803a10014800166850,0x818210044e00166880,0x40970803a1000ca00166a20,0x815a1004ce00166b80,0x41150802610014800166cb0,0x40e50802e10014800166df0,0x40bf0802e1000ca00166f60,0x41250800a2000ca00167020,0x81a630014800167070,0x409d0800e1000ce00167080,0x41370802210014800167430,0x40e9080261000ca00167c20,0x40d30800e2000ca00167da0], [0x42390800a2000c800164050,0x850210014e00164280,0x4185080161000ca001644a0,0x41d30801610014800164550,0x423b0800a2000c8001645f0,0x850610014e00164780,0x42650800e1000ca00164920,0x418d0801a10014800164cd0,0x839a1001ce00164d80,0x414b0801a1000ca00164da0,0x82ce2000ce00164f80,0x83be3000ca001650a0,0x850e10014e00165180,0x42690800e1000ca001653a0,0x839e1001ce00165480,0x42410800a2000c8001656d0,0x426b0800e1000ca001658e0,0x415b1000a1000c800165a90,0x41910801a10014800165d10,0x851a10014e00166080,0x83a61001ce00166280,0x415d1000a1000c8001663f0,0x418d080161000ca001665a0,0x41510801a1000ca00166ae0,0x41390800e1000cc00166b40,0x83ce3000ca00166ba0,0x41df0801610014800166e90,0x852610014e00166f80,0x424b0800a2000c8001672f0,0x82de2000ce00167380,0x852a10014e00167480,0x4191080161000ca00167620,0x41611000a1000c8001676b0,0x42770800e1000ca00167860,0x83d63000ca00167920,0x41990801a10014800167d90,0x41390802210014800167ed0], [0x8b1e2000ca001640e0,0x42dd0800e10014800164370,0x885a1000ce00164380,0x8b262000ca00164560,0x43590800a1000ca001646e0,0x8b2a2000ca001647a0,0x872e1001cc00164840,0x435b0800a1000ca00164aa0,0x8b322000ca00164c20,0x42e30800e10014800165090,0x435f0800a1000ca00165220,0x8b3e2000ca001652e0,0x42e70800e10014800165950,0x87421001cc001659c0,0x8b4e2000ca00165be0,0x887e1000ce00165e80,0x8b562000ca00166060,0x8b5a2000ca001662a0,0x88861000ce00166480,0x888a1000ce00166780,0x87521001cc001667c0,0x8b662000ca00166960,0x42ef0800e10014800166ad0,0x436d0800a1000ca00166c60,0x88921000ce00166d80,0x875a1001cc00166ec0,0x43710800a1000ca001673e0,0x889e1000ce00167680,0x8b7e2000ca001676e0,0x43730800a1000ca001677a0,0x42f50800e100148001677f0,0x87661001cc00167940,0x43770800a1000ca00167f20,0x88aa1000ce00167f80], [0x1320ce00164180,0x46ad0800a1000c800164230,0x13224e00164480,0x13244e00164880,0x13254e00164a80,0x46b90800a1000c800164d70,0x13274e00164e80,0x46bb0800a1000c800164f50,0x46c50800a1000c8001658b0,0x132cce00165980,0x132d4e00165a80,0x132e4e00165c80,0x132ece00165d80,0x46cd0800a1000c800166030,0x1331ce00166380,0x46d30800a1000c8001665d0,0x46d90800a1000c800166b70,0x46df0800a1000c800167110,0x1338ce00167180,0x13394e00167280,0x133ace00167580,0x133c4e00167880,0x133dce00167b80,0x133ece00167d80], [0xa15e1000ca001641a0,0xa1621000ca00164260,0xa1761000ca00164620,0xa1821000ca00164860,0xa83610014800164870,0xa84210014800164a50,0xa1921000ca00164b60,0xa85e10014800164eb0,0xa86610014800164ff0,0xa87610014800165270,0xa88a10014800165590,0xa1ce1000ca001656a0,0xa89a10014800165810,0xa1e21000ca00165a60,0xa1e61000ca00165b20,0xa8b210014800165bd0,0xa1fa1000ca00165ee0,0xa8d610014800166170,0xa20a1000ca001661e0,0xa8de100148001662b0,0xa8e210014800166350,0xa2161000ca00166420,0xa8ea10014800166490,0xa22a1000ca001667e0,0xa91a10014800166c10,0xa24e1000ca00166ea0,0xa93210014800166fd0,0xa25a1000ca001670e0,0xa93e100148001671b0,0xa94210014800167250,0xa2721000ca00167560,0xa96210014800167750,0xa96e10014800167930,0xa28a1000ca001679e0,0xa28e1000ca00167aa0,0xa97a10014800167b10,0xa99610014800167f70]]
set_option maxRecDepth 10000 in
private def witnessesBlock102 : Array (List ℕ) := #[[0xd8ee2000c4001640bc,0xd9022000c400164224,0xd90e2000c4001642fc,0xd9262000c4001644ac,0xd93e2000c40016465c,0xd95a2000c400164854,0xd9662000c40016492c,0xd96e2000c4001649bc,0xd9962000c400164c8c,0xd99e2000c400164d1c,0xd9b62000c400164ecc,0xd9c22000c400164fa4,0xd9c62000c400164fec,0xd9d22000c4001650c4,0xd9de2000c40016519c,0xd9fe2000c4001653dc,0xda0e2000c4001654fc,0xda3a2000c400165814,0xda3e2000c40016585c,0xda762000c400165c4c,0xda862000c400165d6c,0xda922000c400165e44,0xda9a2000c400165ed4,0xdac22000c4001661a4,0xdaca2000c400166234,0xdae22000c4001663e4,0xdb122000c400166744,0xdb3a2000c400166a14,0xdb422000c400166aa4,0xdb522000c400166bc4,0xdb662000c400166d2c,0xdb6a2000c400166d74,0xdb8a2000c400166fb4,0xdb8e2000c400166ffc,0xdba62000c4001671ac,0xdbbe2000c40016735c,0xdc022000c400167824,0xdc062000c40016786c,0xdc0e2000c4001678fc,0xdc1a2000c4001679d4,0xdc322000c400167b84,0xdc3e2000c400167c5c,0xdc4a2000c400167d34,0xdc5a2000c400167e54,0xdc662000c400167f2c,0xdc6e2000c400167fbc], [0x100070800a2000c400169834,0x800e5000d00016a500], [0x40132000a2000c4001685ec,0x400b0800a5000ca001686a0,0x2008840071000a2000c800168970,0x2009840110800e1000cc00169fc0,0x2006840071000a1000cc0016aa40,0x40130800a2000d20016ae00,0x400d080161000d40016b400], [0x401d0802e10014e00168380,0x40350800e2000ce00168580,0x200e8400b0800e1000cc00168ac0,0x40351000a4000c400168cf4,0x805640014800168fb0,0x200b8400d0800a2000ca001691e0,0x40250801a1001ce00169380,0x40171000e1000ce00169a80,0x2015840070800a2000ca00169d20,0x401d0801a2000ce0016a080,0x2012880070800a1000c80016a3b0,0x40290804a2000ca0016aaa0,0x20178400d0800a2000c80016b670,0x40250803e1000ce0016b880,0x40350801a10014e0016ba80,0x401d080221001ce0016bd80,0x402f1000e1000cc0016bf40], [0x4065080161000ce00168280,0x808e100bce00168480,0x40490807a1000ca001685e0,0x40650806a100148001688d0,0x406d080521000ca00168be0,0x403d0801610014e00168d80,0x40830805210014800168e70,0x403b080261000ce00169180,0x406b0800e2000cc00169540,0x404f080262000ca001698a0,0x80da1007ce00169980,0x40590807a1001480016a090,0x40610800e10014e0016a180,0x809e100ace0016a280,0x4067080161000ce0016a380,0x80a6100a4e0016a580,0x4059080222000ca0016a620,0x808e1000d60016a800,0x40670806a1001480016a9f0,0x407f080561001480016aa90,0x4043080221000ce0016ac80,0x40610805e1000ca0016ada0,0x4059080161001cc0016b140,0x80fe3000ce0016b280,0x8092100bce0016b380,0x406d0800e2000cc0016b4c0,0x406b080561000ca0016bd60], [0x40c10802e1000ca001680a0,0x41190802610014800168470,0x814e10015200168600,0x820210034e00168680,0x40bf0800e10014c00168740,0x40df0800a1000ce00168880,0x818a10044e00168a80,0x40e90802e10014800168ab0,0x40ad0803e10014800168bf0,0x4107080221000ca00168ca0,0x411b0802610014800169050,0x82661002ce00169880,0x40c10800e10014c001698c0,0x818e10044e00169b80,0x4089080162000ca00169f60,0x40c50802e1000ca0016a320,0x81661004ce0016a480,0x40e30800a1000ce0016a680,0x40ef080261000ca0016a6e0,0x409d0803a1000ca0016ab60,0x820e10034e0016ad80,0x826e1002ce0016ae80,0x40a30800e1000ce0016af80,0x812a1005ce0016b180,0x410d080221000ca0016b2e0,0x40c70802e1000ca0016b460,0x40f1080261000ca0016b520,0x40e50800a1000ce0016b580,0x40ef0802e1001480016b5d0,0x816a1004ce0016b780,0x408b080162000ca0016b820,0x40950804a1001480016bad0,0x40c50800e10014c0016bbc0,0x41330800a2000ca0016bee0,0x410f080221000ca0016bfa0], [0x413d0800e1000cc00168040,0x42510800a2000c8001683d0,0x41e70801610014800168a10,0x83be1001ce00168c80,0x82ea2000ce00168e80,0x854210014e00169280,0x42810800e1000ca001692a0,0x41671000a1000c8001692d0,0x413d0802210014800169410,0x83e63000ca00169420,0x42570800a2000c8001694b0,0x4199080161000ca00169720,0x41eb08016100148001697d0,0x42830800e1000ca001697e0,0x42590800a2000c800169a50,0x415b0801a1000ca00169ba0,0x854a10014e00169c80,0x83ee3000ca0016a1a0,0x42870800e1000ca0016a260,0x415d0801a1000ca0016a560,0x41a30801a1001480016a630,0x83ce1001ce0016a880,0x82f62000ce0016a980,0x425f0800a2000c80016ab30,0x855610014e0016ab80,0x41a50801a1001480016ae50,0x428d0800e1000ca0016b220,0x41f3080161001480016b350,0x83fa3000ca0016b5e0,0x83d61001ce0016b680,0x416f1000a1000c80016b850,0x41610801a1000ca0016b8e0,0x82721002ce0016b980,0x82fe2000ce0016bb80,0x42650800a2000c80016bc10,0x856610014e0016bf80], [0x42f90800e100148001680b0,0x8b922000ca00168220,0x87721001cc001683c0,0x8b962000ca00168460,0x8b9e2000ca001688e0,0x8ba22000ca00168b20,0x88ba1000ce00168b80,0x8baa2000ca00168fa0,0x43010800e10014800169230,0x88c61000ce00169480,0x8bb62000ca00169660,0x43050800e10014800169af0,0x878e1001cc00169c40,0x88d21000ce00169d80,0x87961001cc0016a340,0x8bce2000ca0016a3e0,0x438b0800a1000ca0016a4a0,0x438f0800a1000ca0016ac20,0x87a21001cc0016adc0,0x8be62000ca0016b160,0x87ae1001cc0016b840,0x43130800e1001480016b990,0x8bf62000ca0016ba60,0x43970800a1000ca0016bb20,0x88fe1000ce0016be80]]
set_option maxRecDepth 10000 in
private def witnessesBlock103 : Array (List ℕ) := #[[0x13404e00168080,0x1340ce00168180,0x46f10800a1000c8001681f0,0x1343ce00168780,0x46f70800a1000c800168790,0x1344ce00168980,0x46fb0800a1000c800168b50,0x46fd0800a1000c800168d30,0x1347ce00168f80,0x13484e00169080,0x134ace00169580,0x134b4e00169680,0x47090800a1000c800169870,0x134f4e00169e80,0x134fce00169f80,0x47130800a1000c80016a1d0,0x1353ce0016a780,0x13554e0016aa80,0x471f0800a1000c80016ad10,0x135a4e0016b480,0x47270800a1000c80016b490,0x135e4e0016bc80], [0xa2b21000ca00168160,0xa9aa10014800168290,0xa2be1000ca001683a0,0xa2c61000ca00168520,0xa9c6100148001686f0,0xa2d21000ca00168760,0xa9ce10014800168830,0xa2de1000ca001689a0,0xa3021000ca00169060,0xa3061000ca00169120,0xaa0a10014800169190,0xaa1610014800169370,0xa31a1000ca001694e0,0xa3361000ca00169a20,0xa3421000ca00169c60,0xa34a1000ca00169de0,0xa34e1000ca00169ea0,0xa3561000ca0016a020,0xa3861000ca0016a920,0xa38a1000ca0016a9e0,0xa3a21000ca0016ae60,0xa3ae1000ca0016b0a0,0xa3ce1000ca0016b6a0,0xa3de1000ca0016b9a0,0xa3ea1000ca0016bbe0,0xa3f61000ca0016be20], [0xaa2210014800169550,0xaa2e10014800169730,0xaa3e100148001699b0,0xaa4a10014800169b90,0xaa5210014800169cd0,0xaa5610014800169d70,0xaa6e1001480016a130,0xaa7a1001480016a310,0xaa821001480016a450,0xaa861001480016a4f0,0xaa921001480016a6d0,0xaabe1001480016adb0,0xaaca1001480016af90,0xaace1001480016b030,0xaad61001480016b170,0xaafa1001480016b710,0xaafe1001480016b7b0,0xab061001480016b8f0,0xab1e1001480016bcb0,0xab221001480016bd50,0xab2e1001480016bf30], [0xdc722000c400168004,0xdc7e2000c4001680dc,0xdcae2000c40016843c,0xdcb62000c4001684cc,0xdcde2000c40016879c,0xdcf22000c400168904,0xdcfe2000c4001689dc,0xdd0a2000c400168ab4,0xdd262000c400168cac,0xdd2e2000c400168d3c,0xdd3a2000c400168e14,0xdd462000c400168eec,0xdd4a2000c400168f34,0xdd622000c4001690e4,0xdd6e2000c4001691bc,0xdd822000c400169324,0xdd862000c40016936c,0xdd9a2000c4001694d4,0xdda62000c4001695ac,0xddce2000c40016987c,0xddd62000c40016990c,0xde0a2000c400169cb4,0xde122000c400169d44,0xde162000c400169d8c,0xde222000c400169e64,0xde4e2000c40016a17c,0xde522000c40016a1c4,0xde822000c40016a524,0xde8a2000c40016a5b4,0xde962000c40016a68c,0xde9a2000c40016a6d4,0xdea22000c40016a764,0xdeae2000c40016a83c,0xdede2000c40016ab9c,0xdeea2000c40016ac74,0xdefa2000c40016ad94,0xdf022000c40016ae24,0xdf062000c40016ae6c,0xdf4a2000c40016b334,0xdf562000c40016b40c,0xdf662000c40016b52c,0xdf862000c40016b76c,0xdf9e2000c40016b91c,0xdfa22000c40016b964,0xdfb62000c40016bacc,0xdfba2000c40016bb14,0xdfce2000c40016bc7c,0xdfda2000c40016bd54,0xdfea2000c40016be74,0xdff22000c40016bf04], [0x800e3001520016d600,0x2800a2000c80016ddd0,0x40071000a4000ca0016ebe0], [0x2005840070800a2000ce0016c480,0x20088400d0800e2000ca0016cc60,0x80228000c40016cec4,0x40068400b0800a1000c80016ced0,0x400d0800a3000d00016db00,0x800d0800e1000ce0016ee80,0x4013080221002ce0016f080,0x2006880070800a2000c80016ff90], [0x40350803a2000ca0016c120,0x40291000a3000c80016c1b0,0x402b0802e1001cc0016c2c0,0x802b0800a1000c80016c570,0x201a840071000a1000c80016cb10,0x40290802210014e0016ce80,0x40170800a5000c80016d290,0x40250800e3000cc0016d440,0x40250802610014e0016dd80,0x4017080222000ce0016df80,0x4035080261001cc0016e240,0x402f1000a1000ce0016e280,0x200e8400d1000a1000c80016e730,0x2012840110800a2000c80016e910,0x401f0802e10014e0016f680,0x40290803a1000ce0016f780,0x1002e3000ca0016f960,0x402b0804a2000ca0016fde0,0x200f8400b0800e1000cc0016fe40], [0x40430802e2000ca0016c5a0,0x40590801a1000ce0016c780,0x4071080521000ca0016c960,0x4053080861001480016c9d0,0x403d080261000ce0016ca80,0x404f080761000ca0016d3e0,0x80e21007ce0016d780,0x80921000d60016d800,0x202c840070800a2000c80016d830,0x404f0808e1001480016d8d0,0x403b080221001cc0016db40,0x1009e2000c60016db48,0x406d080561000ca0016dda0,0x2021840070800a1000cc0016dec0,0x4083080561001480016e050,0x407f0804a1000ca0016e220,0x406b080161000ce0016e580,0x40650800e10014e0016e780,0x81063000ce0016e880,0x40590806a1000ca0016e8e0,0x403b0800a1000d20016ea00,0x406b0806a1001480016ec30,0x4053080262000ca0016ee20,0x8086100d4e0016ef80,0x404f0800a2000ce0016f180,0x40710800e2000cc0016f3c0,0x40650805e1000ca0016f420,0x4047080861000ca0016f7e0,0x80a6100ace0016f880,0x407f1000a2000c80016f9f0,0x4061080761001480016fc70]]
set_option maxRecDepth 10000 in
private def witnessesBlock104 : Array (List ℕ) := #[[0x815a1001520016c200,0x40bf0803a1001480016c2f0,0x40950803e1000ca0016c420,0x40f10802e1001480016c430,0x40b30803e1001480016c610,0x812e1005ce0016c880,0x4125080261001480016cbb0,0x40c70800e10014c0016cd40,0x81be3001480016ce30,0x40970804a1001480016d1f0,0x40e90800a1000ce0016d380,0x821a10034e0016d480,0x40c10803a1001480016d510,0x41370800a2000ca0016d560,0x40b50803e1001480016d970,0x40a70800e1000ce0016d980,0x4089080521001480016db50,0x40970803e1000ca0016db60,0x40df0800e2000ca0016dc20,0x821e10034e0016e180,0x4115080221000ca0016e5e0,0x40a30803a1000ca0016eca0,0x81c63001480016ed70,0x408b080521001480016f4f0,0x40c50803a1001480016f950,0x40e30800e2000ca0016fba0,0x40fb080261000ca0016fc60,0x81ca3001480016fd10,0x81661001520016fe00,0x4119080221000ca0016ff60], [0x41a3080161000ca0016c060,0x41f7080161001480016c110,0x42930800e1000ca0016c1e0,0x42950800e1000ca0016c720,0x42690800a2000c80016c750,0x41a5080161000ca0016c8a0,0x414b0800e1000cc0016c9c0,0x426b0800a2000c80016ccf0,0x827a1002ce0016cf80,0x83e61001ce0016d280,0x41751000a1000c80016d470,0x41fd080161001480016d5b0,0x41670801a1000ca0016d620,0x830a2000ce0016d680,0x41af0801a1001480016d6f0,0x857a10014e0016d880,0x84123000ca0016de60,0x414b080221001480016de70,0x41b10801a1001480016df10,0x83ee1001ce0016e080,0x41390800a2000ca0016e0a0,0x84163000ca0016e520,0x42a10800e1000ca0016e6a0,0x41510800e1000cc0016e940,0x858a10014e0016ec80,0x42770800a2000c80016eeb0,0x417b1000a1000c80016f090,0x42a50800e1000ca0016f120,0x41af080161000ca0016f1e0,0x83fa1001ce0016f580,0x413d0800a2000ca0016f720,0x41b70801a1001480016f770,0x41b1080161000ca0016fa20,0x831a2000ce0016fa80,0x416f0801a1000ca0016fd20,0x4151080221001480016fe50,0x4209080161001480016fef0], [0x89021000ce0016c180,0x87be1001cc0016c640,0x8c0e2000ca0016c7e0,0x43a10800a1000ca0016cde0,0x8c1a2000ca0016cea0,0x431d0800e1001480016cf70,0x89161000ce0016d080,0x87ca1001cc0016d0c0,0x8c222000ca0016d320,0x8c2e2000ca0016d9e0,0x89261000ce0016dc80,0x43a90800a1000ca0016dce0,0x8c3e2000ca0016e2e0,0x43ad0800a1000ca0016e460,0x87e21001cc0016e5c0,0x8c462000ca0016e760,0x43290800e1001480016e9b0,0x893a1000ce0016eb80,0x87ea1001cc0016ecc0,0x432b0800e1001480016ee10,0x43b30800a1000ca0016efa0,0x8c562000ca0016f060,0x89461000ce0016f480,0x8c5e2000ca0016f4e0,0x87f61001cc0016f740,0x87fa1001cc0016fac0,0x43b90800a1000ca0016fae0,0x89521000ce0016fd80], [0x13604e0016c080,0x13614e0016c280,0x1361ce0016c380,0x47370800a1000c80016c390,0x1362ce0016c580,0x13634e0016c680,0x47450800a1000c80016d0b0,0x1368ce0016d180,0x136ace0016d580,0x474b0800a1000c80016d650,0x474f0800a1000c80016da10,0x136dce0016db80,0x47510800a1000c80016dbf0,0x136f4e0016de80,0x47550800a1000c80016dfb0,0x47570800a1000c80016e190,0x1371ce0016e380,0x13724e0016e480,0x13734e0016e680,0x1374ce0016e980,0x13754e0016ea80,0x47610800a1000c80016eaf0,0x1376ce0016ed80,0x13794e0016f280,0x1379ce0016f380,0x476d0800a1000c80016f630,0x137cce0016f980,0x47730800a1000c80016fbd0,0x137f4e0016fe80,0x137fce0016ff80], [0xa41a1000ca0016c4e0,0xa43a1000ca0016cae0,0xa43e1000ca0016cba0,0xa4461000ca0016cd20,0xa4521000ca0016cf60,0xa4561000ca0016d020,0xa4621000ca0016d260,0xa46e1000ca0016d4a0,0xa4821000ca0016d860,0xa48e1000ca0016daa0,0xa4a61000ca0016df20,0xa4be1000ca0016e3a0,0xa4e21000ca0016ea60,0xa4e61000ca0016eb20,0xa4f21000ca0016ed60,0xa4fa1000ca0016eee0,0xa51e1000ca0016f5a0,0xa52e1000ca0016f8a0], [0xab361001480016c070,0xab6a1001480016c890,0xab761001480016ca70,0xab821001480016cc50,0xab8a1001480016cd90,0xab9a1001480016d010,0xabae1001480016d330,0xabee1001480016dd30,0xac0e1001480016e230,0xac121001480016e2d0,0xac1e1001480016e4b0,0xac261001480016e5f0,0xac2a1001480016e690,0xac321001480016e7d0,0xac361001480016e870,0xac4a1001480016eb90,0xac661001480016eff0,0xac721001480016f1d0,0xac7a1001480016f310,0xac8a1001480016f590,0xac9e1001480016f8b0,0xacaa1001480016fa90], [0xe0022000c40016c024,0xe01a2000c40016c1d4,0xe0462000c40016c4ec,0xe0522000c40016c5c4,0xe06e2000c40016c7bc,0xe0762000c40016c84c,0xe0aa2000c40016cbf4,0xe0b22000c40016cc84,0xe0b62000c40016cccc,0xe0ce2000c40016ce7c,0xe0e22000c40016cfe4,0xe0f22000c40016d104,0xe0fa2000c40016d194,0xe10a2000c40016d2b4,0xe1222000c40016d464,0xe12a2000c40016d4f4,0xe1462000c40016d6ec,0xe1522000c40016d7c4,0xe1722000c40016da04,0xe17e2000c40016dadc,0xe18e2000c40016dbfc,0xe1962000c40016dc8c,0xe1a22000c40016dd64,0xe1ae2000c40016de3c,0xe1be2000c40016df5c,0xe1ca2000c40016e034,0xe1de2000c40016e19c,0xe1f62000c40016e34c,0xe1fa2000c40016e394,0xe2062000c40016e46c,0xe2122000c40016e544,0xe2322000c40016e784,0xe2422000c40016e8a4,0xe24e2000c40016e97c,0xe25a2000c40016ea54,0xe2722000c40016ec04,0xe2862000c40016ed6c,0xe28a2000c40016edb4,0xe2962000c40016ee8c,0xe2ba2000c40016f114,0xe2c22000c40016f1a4,0xe2ce2000c40016f27c,0xe2da2000c40016f354,0xe2e62000c40016f42c,0xe2fe2000c40016f5dc,0xe3222000c40016f864,0xe3322000c40016f984,0xe33e2000c40016fa5c,0xe3522000c40016fbc4,0xe3622000c40016fce4,0xe3862000c40016ff6c,0xe38e2000c40016fffc], [0x2009840110800a2000ca001718e0,0x400b1000e3000ca00171b20,0x400d1800a2000ca00172420,0x20098400b0800e10014c001724c0,0x80110800a4000c4001724d4,0x180221000ca00173260,0x400b0800e1000d600173800]]
set_option maxRecDepth 10000 in
private def witnessesBlock105 : Array (List ℕ) := #[[0x200e8400b0800a2000ca00170260,0x80521002d400170c00,0x402f080161001ce00171180,0x200b840070800a2000cc00171340,0x803a30014e00171480,0x401f0801a2000ce00171580,0x402b1000a3000c800171610,0x402b0802210014e00172380,0x40350802e1000ce00172480,0x4025080162000ce00172780,0x200b840111000a1000c8001728d0,0x805e40014800172bf0,0x401f080221001ce00173480,0x40350803e2000ca00173860,0x2017840070800a2000ca00173aa0], [0x80765000ca00170020,0x80c210094e00170280,0x404f0801a1001cc00170540,0x406d080161000ce00170680,0x807a100ece00170780,0x404f0809210014800170a30,0x40670800e10014e00170a80,0x406d0806a10014800170d50,0x404f0807a1000ca00170f20,0x80863000d000171100,0x4047080221000ce00171280,0x403d080221001cc001716c0,0x40670805e1000ca00171760,0x40830804a1000ca001719a0,0x4071080561000ca00171e20,0x80b2100a4e00172080,0x201d8400b0800a2000c800172150,0x403d0800a1000d200172600,0x4049080861000ca00172a20,0x4053080761000ca00172c60,0x40470802e2000ca00172d20,0x80fe10074e00173180,0x40530808e10014800173190,0x40831000a2000c800173230,0x40430801610014e00173280,0x40610807a10014800173910,0x807a5000ca00173ce0,0x4061080222000ca00173f20], [0x40ef0800a1000ce00170080,0x81a610044e00170180,0x822a10034e00170880,0x40e50800e2000ca00170b60,0x40c70803a10014800170b70,0x40fb0802e10014800170c10,0x411b080221000ca00170c20,0x813a1005ce00170d80,0x40f10800a1000ce00170f80,0x816a10015200171200,0x817e1004ce00171680,0x409d0804a10014800171750,0x40a70803a1000ca00171820,0x40ad0800e1000ce00171880,0x40d30802e1000ca00171be0,0x81d230014800171c50,0x41330802610014800171ed0,0x409d0803e1000ca00172120,0x823210034e00172280,0x4101080261000ca00172720,0x81821004ce00172980,0x40e90800e2000ca00172ae0,0x823610034e00172f80,0x408908056100148001730f0,0x4095080162000ca001733e0,0x40d30800e10014c00173640,0x41370802610014800173690,0x41010802e10014800173730,0x81123000ce00173980,0x40bf0803e10014800173a50], [0x42ab0800e1000ca001700e0,0x417f1000a1000c800170350,0x859e10014e00170580,0x420b08016100148001705d0,0x41bb0801a100148001707b0,0x42810800a2000c800170ad0,0x83222000ce00170c80,0x42830800a2000c800171070,0x41b7080161000ca001712e0,0x42b30800e1000ca001715e0,0x41750801a1000ca00171a60,0x42870800a2000c800171bb0,0x82961002ce00171c80,0x415b0800e1000cc00171dc0,0x41851000a1000c800171f70,0x84121001ce00171f80,0x41c10801a10014800172010,0x843a3000ca001721e0,0x41bb080161000ca00172360,0x84161001ce00172680,0x415d0800e1000cc00172840,0x428d0800a2000c800172c90,0x42bd0800e1000ca00173020,0x83322000ce00173080,0x415b0802210014800173370,0x84463000ca00173620,0x417b0801a1000ca001737a0,0x41c1080161000ca00173c20,0x41610800e1000cc00173d40,0x42930800a2000c800173d70,0x82a21002ce00173d80,0x415d0802210014800173e10], [0x43350800e100148001703f0,0x8c7a2000ca001704a0,0x43370800e10014800170850,0x8c822000ca00170920,0x89621000ce00170980,0x880e1001cc00170c40,0x88121001cc00170fc0,0x8c8e2000ca00170fe0,0x433b0800e10014800171110,0x8c922000ca00171220,0x43c70800a1000ca00171520,0x433d0800e10014800171570,0x8c9a2000ca001716a0,0x85ae10014e00171980,0x881e1001cc00171a40,0x897a1000ce00171b80,0x43cb0800a1000ca00171ca0,0x8ca62000ca00171d60,0x89821000ce00172180,0x43d10800a1000ca001727e0,0x85ba10014e00172880,0x898e1000ce00172a80,0x43470800e10014800172b50,0x88321001cc00172bc0,0x88361001cc00172f40,0x43d70800a1000ca00173320,0x899a1000ce00173380,0x899e1000ce00173680,0x85c610014e00173780,0x89aa1000ce00173f80], [0x47790800a1000c800170170,0x13824e00170480,0x1385ce00170b80,0x13874e00170e80,0x13884e00171080,0x478b0800a1000c800171250,0x1389ce00171380,0x478d0800a1000c800171430,0x138bce00171780,0x138d4e00171a80,0x138ece00171d80,0x8caa2000ca00171fa0,0x479d0800a1000c800172330,0x479f0800a1000c800172510,0x1392ce00172580,0x8cb62000ca00172660,0x1395ce00172b80,0x8cca2000ca001731a0,0x47b50800a1000c8001739b0,0x47bb0800a1000c800173f50], [0xa55e1000ca001701a0,0xa5661000ca00170320,0xa56a1000ca001703e0,0xa5721000ca00170560,0xa57e1000ca001707a0,0xa5821000ca00170860,0xa59a1000ca00170ce0,0xa5a21000ca00170e60,0xa5be1000ca001713a0,0xa5fa1000ca00171ee0,0xa60e1000ca001722a0,0xa61a1000ca001724e0,0xa6321000ca00172960,0x13964e00172c80,0x13974e00172e80,0xa64e1000ca00172ea0,0xa65a1000ca001730e0,0xa66e1000ca001734a0,0x139ace00173580,0x139c4e00173880,0xa6861000ca00173920,0xa68a1000ca001739e0,0x139d4e00173a80,0xa6921000ca00173b60,0xa69e1000ca00173da0,0x139f4e00173e80], [0xacd2100148001700d0,0xacda10014800170210,0xacde100148001702b0,0xacea10014800170490,0xad2610014800170df0,0xad2e10014800170f30,0xad3e100148001711b0,0xad52100148001714d0,0xad5e100148001716b0,0xad6a10014800171890,0xad7a10014800171b10,0xad8610014800171cf0,0xad9e100148001720b0,0xada6100148001721f0,0xadb2100148001723d0,0xadb610014800172470,0xadc210014800172650,0xadca10014800172790,0xadd610014800172970,0xadda10014800172a10,0xadee10014800172d30,0xadf210014800172dd0,0xae12100148001732d0,0xae1e100148001734b0,0xae4610014800173af0,0xae4e10014800173c30,0xae6610014800173ff0]]
set_option maxRecDepth 10000 in
private def witnessesBlock106 : Array (List ℕ) := #[[0xe3aa2000c4001701f4,0xe3b62000c4001702cc,0xe3da2000c400170554,0xe3ee2000c4001706bc,0xe3fe2000c4001707dc,0xe4122000c400170944,0xe42a2000c400170af4,0xe42e2000c400170b3c,0xe43a2000c400170c14,0xe4522000c400170dc4,0xe46a2000c400170f74,0xe4b22000c400171484,0xe4ba2000c400171514,0xe4c62000c4001715ec,0xe4d62000c40017170c,0xe4de2000c40017179c,0xe4ea2000c400171874,0xe4ee2000c4001718bc,0xe4f62000c40017194c,0xe51a2000c400171bd4,0xe5322000c400171d84,0xe53e2000c400171e5c,0xe54e2000c400171f7c,0xe55a2000c400172054,0xe5662000c40017212c,0xe56e2000c4001721bc,0xe5922000c400172444,0xe5962000c40017248c,0xe59e2000c40017251c,0xe5a22000c400172564,0xe5d22000c4001728c4,0xe5da2000c400172954,0xe5e62000c400172a2c,0xe5f22000c400172b04,0xe60e2000c400172cfc,0xe64a2000c400173134,0xe6562000c40017320c,0xe65e2000c40017329c,0xe66a2000c400173374,0xe6822000c400173524,0xe68e2000c4001735fc,0xe6b62000c4001738cc,0xe6be2000c40017395c,0xe6ce2000c400173a7c,0xe6d62000c400173b0c,0xe6e62000c400173c2c,0xe6f22000c400173d04,0xe6fe2000c400173ddc,0xe7062000c400173e6c], [0x40070800a3000d200176200,0x1800a5000c800176a70,0x800a1000de00178000], [0x40110801610015200174e00,0x2009840071000a2000c800174e50,0x801a2000d800175000,0x40111000e2000cc00175240,0x80163001ce00175e80,0x80130800e1000cc00176740,0x4008840070800a1000c800176890,0x800b0800e2000cc001771c0,0x40111000a2000ce00177880], [0x40290801a1001ce00174980,0x402b0803a1000ce00174e80,0x40250800a4000ca00175120,0x200e840170800a2000c8001753f0,0x40250803a1001cc001755c0,0x2014880070800a1000c800175b70,0x200f8400d1000a1000c800176110,0x402f0802e1001cc001763c0,0x80561002d400176400,0x40290803e1000ce00177280,0x20128400b1000a1000c8001773d0,0x200f8400b0800a2000ca00177e20], [0x809e100bce00174080,0x407f0801a2000ca00174160,0x403b0800e2000ce00174280,0x4049080221000ce00174580,0x40650807610014800174630,0x40590808610014800174770,0x2023840070800a1000cc001747c0,0x4071080161000ce00174880,0x407f0805e10014800174950,0x403b1000a4000c400174acc,0x4061080161001cc00174b40,0x40530800a2000ce00174b80,0x80ca10094e00174c80,0x40710806a10014800174f90,0x406b0800e10014e00175080,0x808e100d4e00175980,0x406b0805e1000ca00175de0,0x201e8400b0800a2000c800175f30,0x40530801a1001cc00176040,0x40490802e2000ca001760e0,0x40610801a1000ce00176380,0x40530809210014800176570,0x809e1000d600176800,0x40530807a1000ca00176aa0,0x40670807610014800176b10,0x810610074e00176b80,0x4059080262000ca00176e60,0x80ce10094e00177180,0x406d0800e10014e00177380,0x4043080261000ce00177580,0x2030840070800a2000c8001775b0,0x80b2100ace00177980,0x40830801a2000ca00177be0,0x2024840070800a1000cc00177c40,0x808e3000d000177d00,0x403b0801a10014e00177d80], [0x81de30014800174b30,0x408b0805610014800174bd0,0x4125080221000ca00174be0,0x4097080162000ca00174ca0,0x40c10803e10014800174db0,0x818a1004ce00174f80,0x4107080261000ca001751e0,0x81461005ce00175280,0x81163000ce00175480,0x40b30800e1000ce00175780,0x40ad0803a1000ca00175960,0x40ef0800e2000ca00175a20,0x40fb0800a1000ce00175a80,0x81e230014800175ad0,0x40a30804a10014800175cb0,0x41070802e10014800176250,0x818e1004ce00176280,0x40a30803e1000ca001766e0,0x81be10044e00176780,0x40f10800e2000ca001769e0,0x40b50800e1000ce00176c80,0x40890804a1000ca00176ce0,0x824a10034e00177080,0x40c50803e10014800177470,0x40950805210014800177510,0x817e10015200177600,0x40d30803a10014800177830,0x410d080261000ca00177ca0], [0x41c90801a10014800174090,0x41390802610014800174270,0x42950800a2000c800174310,0x421d08016100148001743b0,0x418d1000a1000c8001744f0,0x42c50800e1000ca00174520,0x414b0800a2000ca001745e0,0x417f0801a1000ca00174b20,0x41cd0801a100148001750d0,0x41610802210014800175350,0x41911000a1000c8001757b0,0x845a3000ca001757e0,0x42230801610014800175850,0x41cf0801a100148001758f0,0x413d0802610014800175a30,0x41670800e1000cc00175cc0,0x41c9080161000ca00175d20,0x83462000ce00175d80,0x42cf0800e1000ca00175f60,0x42a10800a2000c8001764d0,0x843a1001ce00176580,0x834a2000ce00176680,0x41510800a2000ca001767a0,0x41850801a1000ca00176860,0x41d30801a10014800176930,0x84663000ca00176c20,0x41cd080161000ca00176da0,0x42a50800a2000c800177010,0x41670802210014800177330,0x82b61002ce00177480,0x41cf080161000ca001775e0,0x84461001ce00177a80,0x422d0801610014800177ab0,0x41991000a1000c800177d30,0x82ba1002ce00177f80], [0x884a1001cc001740c0,0x85ce10014e00174180,0x43df0800a1000ca00174220,0x884e1001cc00174440,0x43550800e100148001749f0,0x43e50800a1000ca00174d60,0x885a1001cc00174ec0,0x89c21000ce00175180,0x43590800e100148001752b0,0x85de10014e00175580,0x435b0800e10014800175710,0x435f0800e10014800175fd0,0x89d61000ce00176080,0x43f10800a1000ca001763e0,0x85ea10014e00176480,0x43f50800a1000ca00176b60,0x887e1001cc00176e40,0x85f210014e00176e80,0x42d70800e1000ca00177460,0x88861001cc00177540,0x43fb0800a1000ca001776a0,0x888a1001cc001778c0,0x43fd0800a1000ca00177a60,0x89fa1000ce00177b80,0x436d0800e10014800177e70,0x89fe1000ce00177e80,0x88921001cc00177fc0]]
set_option maxRecDepth 10000 in
private def witnessesBlock107 : Array (List ℕ) := #[[0x47c30800a1000c8001746d0,0x8cf22000ca00174820,0x47c90800a1000c800174c70,0x8cfe2000ca00174ee0,0x47cd0800a1000c800175030,0x47cf0800a1000c800175210,0x8d062000ca00175360,0x8d0a2000ca001755a0,0x47d30800a1000c8001755d0,0x47db0800a1000c800175d50,0x47e10800a1000c8001762f0,0x47eb0800a1000c800176c50,0x47ed0800a1000c800176e30,0x8d3a2000ca001770a0,0x8d422000ca00177520,0x8d462000ca00177760,0x47f70800a1000c800177790], [0xa6ae1000ca001740a0,0xa6ba1000ca001742e0,0x13a1ce00174380,0xa6ce1000ca001746a0,0xa6d21000ca00174760,0x13a3ce00174780,0xa6da1000ca001748e0,0x13a54e00174a80,0x13a6ce00174d80,0xa6f61000ca00174e20,0xa7021000ca00175060,0xa70e1000ca001752a0,0xa7161000ca00175420,0xa7221000ca00175660,0xa7261000ca00175720,0x13ac4e00175880,0xa73a1000ca00175ae0,0x13adce00175b80,0xa73e1000ca00175ba0,0x13ae4e00175c80,0x13b0ce00176180,0xa75e1000ca001761a0,0xa7761000ca00176620,0x13b44e00176880,0xa7861000ca00176920,0x13b54e00176a80,0x13b6ce00176d80,0xa7aa1000ca00176fe0,0xa7b21000ca00177160,0xa7be1000ca001773a0,0x13bb4e00177680,0x13bbce00177780,0xa7d61000ca00177820,0xa7da1000ca001778e0,0xa7e61000ca00177b20,0x13be4e00177c80,0xa7f21000ca00177d60,0xa7fe1000ca00177fa0], [0xae8210014800174450,0xaeba10014800174d10,0xaec610014800174ef0,0xaeee10014800175530,0xaef610014800175670,0xaf1a10014800175c10,0xaf2a10014800175e90,0xaf3610014800176070,0xaf3e100148001761b0,0xaf4a10014800176390,0xaf66100148001767f0,0xaf72100148001769d0,0xaf7e10014800176bb0,0xaf9210014800176ed0,0xaf9610014800176f70,0xafaa10014800177290,0xafc210014800177650,0xafd2100148001778d0,0xafe610014800177bf0,0xafea10014800177c90,0xaffe10014800177fb0], [0xe7422000c4001742a4,0xe7462000c4001742ec,0xe75a2000c400174454,0xe7722000c400174604,0xe7822000c400174724,0xe7962000c40017488c,0xe7a62000c4001749ac,0xe7d62000c400174d0c,0xe7e22000c400174de4,0xe7fa2000c400174f94,0xe8022000c400175024,0xe81e2000c40017521c,0xe8262000c4001752ac,0xe8322000c400175384,0xe8362000c4001753cc,0xe86e2000c4001757bc,0xe88a2000c4001759b4,0xe8aa2000c400175bf4,0xe8ae2000c400175c3c,0xe8c62000c400175dec,0xe8d22000c400175ec4,0xe8da2000c400175f54,0xe9022000c400176224,0xe9162000c40017638c,0xe9222000c400176464,0xe92e2000c40017653c,0xe93a2000c400176614,0xe94a2000c400176734,0xe95e2000c40017689c,0xe9762000c400176a4c,0xe9922000c400176c44,0xe9a62000c400176dac,0xe9c22000c400176fa4,0xe9e22000c4001771e4,0xe9fe2000c4001773dc,0xea122000c400177544,0xea2e2000c40017773c,0xea3a2000c400177814,0xea5a2000c400177a54,0xea662000c400177b2c,0xea762000c400177c4c,0xea822000c400177d24,0xeaa22000c400177f64], [0x5000d600179800], [0xc0070800a2000ca00178960], [0x20088800b0800a1000c800178870,0x20088400d0800e10014c00178dc0,0x20098400d0800e2000ca00179920,0x80268000c400179bcc,0x400d1000a1000d200179e00], [0x401d080261001ce00178880,0x40290800e3000cc00179140,0x803e30014e00179180,0x201a8400d0800a2000c8001791d0,0x40171000a3000ca001794a0,0x40290802610014e00179b80,0x40351000e1000cc00179bc0]]
set_option maxRecDepth 10000 in
private def witnessesBlock108 : Array (List ℕ) := #[[0x406d0805e1000ca00178120,0x403d0800e2000ce00178180,0x40830805e10014800178410,0x403b0803a2000ca001784e0,0x40650807a10014800178550,0x40610806a1000ca001787e0,0x403d1000a4000c400178a14,0x4065080222000ca00178ba0,0x8092100d4e00178e80,0x201d840071000a1000c800178ff0,0x100a62000c600179188,0x40490808e1000ca001797a0,0x4065080161001cc00179840,0x80a6100bce00179e80,0x40470801610014e0017a080,0x407f080521000ca0017a0a0], [0x814e1005ce00178080,0x40df0802e1000ca00178360,0x40891000a2000c800178690,0x41010800a1000ce00178780,0x40c70803e100148001787d0,0x408b0804a1000ca001788a0,0x81c610044e00178980,0x818210015200178a00,0x410f080261000ca00178ae0,0x40a70804a10014800178af0,0x410d0802e10014800178d70,0x40970805210014800178eb0,0x40a70803e1000ca00179560,0x409d080162000ca001796e0,0x81ca10044e00179a80,0x40b30803a1000ca00179aa0,0x410f0802e10014800179bd0,0x40df0800e10014c00179f40], [0x84723000ca00178060,0x42ab0800a2000c8001780f0,0x41d3080161000ca00178660,0x416f0800e1000cc001786c0,0x84763000ca00178720,0x42330801610014800178f50,0x418d0801a1000ca00178f60,0x835e2000ce00179380,0x82c21002ce00179580,0x42b30800a2000c800179770,0x41df0801a100148001799f0,0x84823000ca00179b60,0x83622000ce00179c80,0x845a1001ce00179d80,0x416f0802210014800179db0,0x415b0800a2000ca00179fe0], [0x860210014e00178280,0x42dd0800e1000ca00178420,0x8a061000ce00178480,0x43710800e10014800178730,0x889e1001cc00178a40,0x43730800e10014800178b90,0x860a10014e00178c80,0x44070800a1000ca00178d20,0x8a121000ce00178d80,0x8a161000ce00179080,0x44090800a1000ca001790e0,0x42e30800e1000ca001793e0,0x43770800e10014800179450,0x88aa1001cc001794c0,0x8a221000ce00179980,0x440f0800a1000ca00179c20,0x42e70800e1000ca00179e60,0x8a2a1000ce00179f80], [0x8d5a2000ca001782a0,0x48050800a1000c8001784b0,0x480f0800a1000c800178e10,0x8d722000ca00179020,0x8d762000ca00179260,0x48150800a1000c8001793b0,0x8d8a2000ca00179da0,0x48210800a1000c800179ef0,0x48230800a1000c80017a0d0], [0x13c1ce00178380,0x13c2ce00178580,0x13c34e00178680,0xa8361000ca00178a20,0x13c5ce00178b80,0xa8421000ca00178c60,0xa85e1000ca001791a0,0x13c94e00179280,0xa8661000ca00179320,0x13ca4e00179480,0xa8761000ca00179620,0x13cc4e00179880,0xa88a1000ca001799e0,0xa89a1000ca00179ce0], [0xb00e10014800178230,0xb026100148001785f0,0xb03a10014800178910,0xb06a10014800179090,0xb06e10014800179130,0xb07610014800179270,0xb086100148001794f0,0xb092100148001796d0,0xb09a10014800179810,0xb0aa10014800179a90,0xb0ce1001480017a030], [0xeaca2000c400178234,0xeade2000c40017839c,0xeae22000c4001783e4,0xeaee2000c4001784bc,0xeaf62000c40017854c,0xeafa2000c400178594,0xeb022000c400178624,0xeb1a2000c4001787d4,0xeb1e2000c40017881c,0xeb322000c400178984,0xeb362000c4001789cc,0xeb422000c400178aa4,0xeb6e2000c400178dbc,0xeb7a2000c400178e94,0xeb7e2000c400178edc,0xeb862000c400178f6c,0xebaa2000c4001791f4,0xebba2000c400179314,0xebce2000c40017947c,0xebde2000c40017959c,0xec0a2000c4001798b4,0xec0e2000c4001798fc,0xec222000c400179a64,0xec462000c400179cec,0xec622000c400179ee4,0xec6a2000c400179f74,0xec6e2000c400179fbc,0xec762000c40017a04c]]
private def witnessesBlocks : Array (Array (List ℕ)) := #[witnessesBlock0, witnessesBlock1, witnessesBlock2, witnessesBlock3, witnessesBlock4, witnessesBlock5, witnessesBlock6, witnessesBlock7, witnessesBlock8, witnessesBlock9, witnessesBlock10, witnessesBlock11, witnessesBlock12, witnessesBlock13, witnessesBlock14, witnessesBlock15, witnessesBlock16, witnessesBlock17, witnessesBlock18, witnessesBlock19, witnessesBlock20, witnessesBlock21, witnessesBlock22, witnessesBlock23, witnessesBlock24, witnessesBlock25, witnessesBlock26, witnessesBlock27, witnessesBlock28, witnessesBlock29, witnessesBlock30, witnessesBlock31, witnessesBlock32, witnessesBlock33, witnessesBlock34, witnessesBlock35, witnessesBlock36, witnessesBlock37, witnessesBlock38, witnessesBlock39, witnessesBlock40, witnessesBlock41, witnessesBlock42, witnessesBlock43, witnessesBlock44, witnessesBlock45, witnessesBlock46, witnessesBlock47, witnessesBlock48, witnessesBlock49, witnessesBlock50, witnessesBlock51, witnessesBlock52, witnessesBlock53, witnessesBlock54, witnessesBlock55, witnessesBlock56, witnessesBlock57, witnessesBlock58, witnessesBlock59, witnessesBlock60, witnessesBlock61, witnessesBlock62, witnessesBlock63, witnessesBlock64, witnessesBlock65, witnessesBlock66, witnessesBlock67, witnessesBlock68, witnessesBlock69, witnessesBlock70, witnessesBlock71, witnessesBlock72, witnessesBlock73, witnessesBlock74, witnessesBlock75, witnessesBlock76, witnessesBlock77, witnessesBlock78, witnessesBlock79, witnessesBlock80, witnessesBlock81, witnessesBlock82, witnessesBlock83, witnessesBlock84, witnessesBlock85, witnessesBlock86, witnessesBlock87, witnessesBlock88, witnessesBlock89, witnessesBlock90, witnessesBlock91, witnessesBlock92, witnessesBlock93, witnessesBlock94, witnessesBlock95, witnessesBlock96, witnessesBlock97, witnessesBlock98, witnessesBlock99, witnessesBlock100, witnessesBlock101, witnessesBlock102, witnessesBlock103, witnessesBlock104, witnessesBlock105, witnessesBlock106, witnessesBlock107, witnessesBlock108]
private def witnesses (i : ℕ) : List ℕ := (witnessesBlocks[i/8]!)[i%8]!
private def keys (i : ℕ) := (witnesses i).map (fun w => w%524288)
private def primeBits : ℕ := 0x28000000220000000a00808228000228800200008028000020200808000228200000828028008a20a00800008000820208000820008020008000800200800200200808208200800008820028000800200000028220008800820000020200808008028000000220820220220000208008220800000020008208800000a28000220820208008000228220208800000000800800828008020200800020800220000808020808000200208208800020a00800820808000820a00200820208220208000820008800808808020028800000220008200000800808808200a00a00200020208000000028808200000208a08800000a00000828800000220000208028020800a08220008208020000220000020a20808208008228000000020020028000a00808800008000008008800008820200000028000020200020828200220000220800200200208020008000a00000808820020020208008820220000008000800008a00a00800020028800008220028028020000200000200820208000808028000000820028200020a08200820000000200808020000800208820028000220000220820020220008208808000020200000028000800a00200800228800008a00000020200000800800208a00808028008000a20208220000200200008008808220200a08000020220a00200a08000028000000a00000000820000808028200020800220020028200208800820200220800a00008220800a00000808028000800820028220800800200000000220208008020008200208228000028a00a08020820008200000828800220200008028800008000a00208008220020808008820008820000820020000020200828008000a20a00000028200200808820000000820000228008028200a00220000220000808208820020820208808808200020800a20008028000808020000228020808008000000020800220028220000000a00808200800000800820008a20008820000208a00a00800020020220800200000208200808a08008020800200000828000800000020028008820200208000228820008008008208000008800000028800800220800220220808800008220000800220028208800a00a08808208020200a08800028200008000820000800000800028000a00800a00800200000008220808020a20008200800020200000a08008200000200800800220020208008820208220a00a00000008220200020028208000808a20000200a00a00028000008800200828028020800a08000800020020200008828200a20000808000000200808800028000020800000808020820a08020808208200a00200828208020000808820228000008020020200a00808008028020820008220808000220000208000000800200220000208000a00a08828220020808208020220000000828800008200808820008028a20a00020000000200808820800000220a00228000228200000828820028820208208000000220008020008208000a08008000008a20000800808020220008200000020820a00208800020200200028028220820008a00820208a00200820008008200800000020008800a08a20000020200008828000200200208020828228000800020820200020800a00000228820008028000208220800028008008200008020808028020000000808200a00a08028028028200800000800028800208a00020020a00208000828000020a08228008000020000220028228220000808800200a20008028000208800200a08000020820200808820008a00200020820208820008028020028020a08a00820020200000a28808000800008200028000a00a00220028220820a00000020028a00000808808200220800a20000008000a00800008220020800808800220200a00000028208800200200808208020200008820208800200028828008020008808028020a20208a20820228020008008808000a00200000828220200800020000008820200208800208200208828820008220a08000028008820808a00020228000808220000020000808028828000a00200a28008200800200a00820228820208000028000a00008208008028a20800200020200200800a20800020820808028008028800000a20800008020a08a08800220220208820020200200208a28020020a20208a20008020000808208000000020a00228828228000200800828208800808208020200a00000820808208a20000828028020a00a08800820208220008208808020220000228800228800200a28028008020008808820220820200808020208800a08228020028820a08200828208020800028008220220200228808220a00a00808808220820208a00820008a20008028828208200a08a20020028a00a08220828028220008a28808220a20a08228828228a2b
private def descPart0 : List (ℕ × ℕ × ℕ) := [(8,128,1),(12,128,1),(36,32,1),(72,16,1),(80,16,1),(96,16,1),(128,16,1),(184,8,1),(240,8,1),(256,8,1),(288,8,1),(384,4,1),(400,8,1),(448,4,1),(480,4,1),(480,8,1),(576,4,1),(640,4,1),(640,8,1),(672,4,1),(704,8,1),(736,4,1),(832,16,1),(864,2,1),(896,4,1),(896,8,1),(992,2,1),(1088,8,2),(1088,16,1),(1152,2,1),(1152,16,1),(1216,4,1)]
private def descPart1 : List (ℕ × ℕ × ℕ) := [(1280,8,1),(1344,4,1),(1344,16,1),(1408,8,2),(1472,4,1),(1536,8,1),(1536,16,1),(1600,16,1),(1664,4,1),(1664,8,2),(1728,4,1),(1728,16,1),(1856,4,1),(1856,8,1),(1856,16,1),(1920,4,1),(1920,16,1),(2048,4,2),(2176,4,1),(2176,8,1),(2176,32,1),(2304,4,1),(2304,16,1),(2304,32,1),(2432,8,1),(2432,16,1),(2432,32,1),(2560,4,1),(2560,16,1),(2560,32,1),(2688,4,1),(2688,8,1)]
private def descPart2 : List (ℕ × ℕ × ℕ) := [(2688,32,1),(2816,16,1),(2944,16,1),(2944,32,1),(3072,16,2),(3072,32,1),(3200,8,2),(3328,16,1),(3328,32,1),(3456,2,1),(3456,4,1),(3456,16,1),(3584,4,1),(3584,16,1),(3584,32,1),(3712,4,1),(3712,16,1),(3712,32,2),(3840,8,1),(3840,16,1),(3968,16,2),(3968,32,2),(4096,4,1),(4096,8,1),(4096,32,1),(4352,4,1),(4352,8,1),(4352,16,2),(4608,4,1),(4608,8,1),(4608,16,1),(4608,32,1)]
private def descPart3 : List (ℕ × ℕ × ℕ) := [(4864,16,1),(4864,32,2),(5120,4,2),(5120,8,3),(5120,16,1),(5120,32,1),(5120,64,2),(5376,8,1),(5376,16,1),(5376,32,1),(5376,64,1),(5632,8,1),(5632,16,2),(5632,64,1),(5888,4,1),(5888,8,1),(5888,32,4),(5888,64,2),(6144,2,1),(6144,4,2),(6144,16,1),(6144,64,1),(6400,8,2),(6400,32,1),(6400,64,1),(6656,8,1),(6656,16,1),(6656,32,2),(6656,64,2),(6912,2,1),(6912,4,1),(6912,16,1)]
private def descPart4 : List (ℕ × ℕ × ℕ) := [(6912,32,1),(6912,64,1),(7168,8,1),(7168,16,1),(7168,32,2),(7168,64,3),(7424,8,3),(7680,4,2),(7680,8,1),(7680,16,1),(7680,32,2),(7680,64,1),(7936,2,1),(7936,8,1),(7936,32,2),(8192,4,2),(8192,8,1),(8192,32,2),(8192,64,2),(8704,4,1),(8704,8,2),(8704,16,1),(8704,32,4),(8704,64,4),(9216,8,3),(9216,16,3),(9216,32,3),(9216,64,1),(9728,4,2),(9728,8,3),(9728,32,3),(9728,64,3)]
private def descPart5 : List (ℕ × ℕ × ℕ) := [(10240,4,2),(10240,8,1),(10240,16,1),(10240,32,3),(10240,64,4),(10752,8,1),(10752,16,3),(10752,32,4),(10752,64,1),(11264,4,1),(11264,8,3),(11264,16,2),(11264,32,1),(11264,64,4),(11776,4,1),(11776,8,3),(11776,16,1),(11776,32,1),(11776,128,2),(12288,4,2),(12288,8,3),(12288,16,2),(12288,32,1),(12288,64,2),(12288,128,2),(12800,8,2),(12800,16,2),(12800,32,2),(12800,64,1),(12800,128,3),(13312,4,1),(13312,8,1)]
private def descPart6 : List (ℕ × ℕ × ℕ) := [(13312,16,2),(13312,32,2),(13312,64,2),(13312,128,2),(13824,4,1),(13824,8,2),(13824,16,1),(13824,32,1),(13824,64,2),(13824,128,3),(14336,4,1),(14336,16,3),(14336,32,2),(14336,64,3),(14336,128,2),(14848,8,2),(14848,16,1),(14848,32,2),(14848,64,2),(14848,128,2),(15360,8,3),(15360,16,2),(15360,64,2),(15360,128,2),(15872,8,2),(15872,16,2),(15872,64,3),(15872,128,3),(16384,4,2),(16384,16,1),(16384,32,2),(16384,64,2)]
private def descPart7 : List (ℕ × ℕ × ℕ) := [(16384,128,2),(17408,4,1),(17408,8,3),(17408,16,4),(17408,32,3),(17408,64,4),(17408,128,5),(18432,2,1),(18432,4,2),(18432,8,4),(18432,16,3),(18432,32,2),(18432,64,6),(18432,128,5),(19456,4,2),(19456,8,1),(19456,16,2),(19456,32,2),(19456,64,8),(19456,128,2),(20480,4,2),(20480,8,4),(20480,16,6),(20480,32,2),(20480,64,3),(20480,128,4),(21504,8,3),(21504,16,6),(21504,32,2),(21504,64,5),(21504,128,5),(22528,4,3)]
private def descPart8 : List (ℕ × ℕ × ℕ) := [(22528,8,3),(22528,16,1),(22528,64,8),(22528,128,6),(23552,4,1),(23552,8,2),(23552,16,2),(23552,32,4),(23552,64,6),(23552,128,5),(24576,4,2),(24576,8,3),(24576,16,5),(24576,32,2),(24576,64,3),(24576,128,4),(25600,4,1),(25600,8,3),(25600,16,4),(25600,32,1),(25600,64,6),(25600,128,6),(26624,2,1),(26624,8,4),(26624,16,4),(26624,32,5),(26624,64,3),(26624,128,2),(26624,256,3),(27648,4,1),(27648,8,2),(27648,16,6)]
private def descPart9 : List (ℕ × ℕ × ℕ) := [(27648,32,3),(27648,64,3),(27648,128,1),(27648,256,4),(28672,4,1),(28672,8,2),(28672,16,1),(28672,32,3),(28672,64,2),(28672,128,3),(28672,256,3),(29696,4,1),(29696,8,3),(29696,16,4),(29696,32,3),(29696,64,3),(29696,128,2),(29696,256,5),(30720,4,2),(30720,16,3),(30720,32,3),(30720,64,3),(30720,128,5),(30720,256,4),(31744,2,1),(31744,8,2),(31744,16,4),(31744,32,3),(31744,64,1),(31744,128,1),(31744,256,5),(32768,1,1)]
private def descPart10 : List (ℕ × ℕ × ℕ) := [(32768,4,1),(32768,8,1),(32768,16,5),(32768,32,5),(32768,64,1),(32768,128,5),(32768,256,3),(34816,4,3),(34816,8,4),(34816,16,6),(34816,32,4),(34816,64,6),(34816,128,8),(34816,256,8),(36864,4,2),(36864,8,2),(36864,16,7),(36864,32,3),(36864,64,5),(36864,128,8),(36864,256,9),(38912,4,2),(38912,8,4),(38912,16,10),(38912,32,7),(38912,64,2),(38912,128,7),(38912,256,8),(40960,4,1),(40960,8,2),(40960,16,5),(40960,32,7)]
private def descPart11 : List (ℕ × ℕ × ℕ) := [(40960,64,6),(40960,128,10),(40960,256,9),(43008,4,2),(43008,8,3),(43008,16,8),(43008,32,6),(43008,64,3),(43008,128,7),(43008,256,7),(45056,4,2),(45056,8,3),(45056,16,7),(45056,32,5),(45056,64,2),(45056,128,12),(45056,256,8),(47104,4,1),(47104,8,3),(47104,16,6),(47104,32,6),(47104,64,4),(47104,128,9),(47104,256,10),(49152,4,3),(49152,8,1),(49152,16,6),(49152,32,7),(49152,64,3),(49152,128,12),(49152,256,4),(51200,8,2)]
private def descPart12 : List (ℕ × ℕ × ℕ) := [(51200,16,8),(51200,32,7),(51200,64,2),(51200,128,7),(51200,256,5),(53248,2,1),(53248,4,1),(53248,8,2),(53248,16,5),(53248,32,8),(53248,64,3),(53248,128,10),(53248,256,10),(55296,2,1),(55296,4,2),(55296,8,2),(55296,16,6),(55296,32,4),(55296,64,5),(55296,128,11),(55296,256,9),(57344,4,4),(57344,8,2),(57344,16,8),(57344,32,5),(57344,64,5),(57344,128,8),(57344,256,8),(59392,8,2),(59392,16,8),(59392,32,4),(59392,64,3)]
private def descPart13 : List (ℕ × ℕ × ℕ) := [(59392,128,10),(59392,256,9),(59392,512,3),(61440,4,2),(61440,8,2),(61440,16,5),(61440,32,8),(61440,64,4),(61440,128,4),(61440,256,4),(61440,512,7),(63488,2,1),(63488,8,1),(63488,16,8),(63488,32,7),(63488,64,4),(63488,128,8),(63488,256,3),(63488,512,8),(65536,4,2),(65536,8,4),(65536,16,5),(65536,32,7),(65536,64,5),(65536,128,5),(65536,256,3),(65536,512,6),(69632,4,3),(69632,8,5),(69632,16,11),(69632,32,7),(69632,64,14)]
private def descPart14 : List (ℕ × ℕ × ℕ) := [(69632,128,8),(69632,256,9),(69632,512,15),(73728,2,1),(73728,4,1),(73728,8,2),(73728,16,9),(73728,32,17),(73728,64,8),(73728,128,5),(73728,256,14),(73728,512,14),(77824,4,1),(77824,8,5),(77824,16,9),(77824,32,11),(77824,64,11),(77824,128,8),(77824,256,12),(77824,512,17),(81920,4,2),(81920,8,3),(81920,16,10),(81920,32,9),(81920,64,10),(81920,128,6),(81920,256,15),(81920,512,12),(86016,4,1),(86016,8,6),(86016,16,10),(86016,32,14)]
private def descPart15 : List (ℕ × ℕ × ℕ) := [(86016,64,7),(86016,128,9),(86016,256,15),(86016,512,17),(90112,4,2),(90112,8,6),(90112,16,8),(90112,32,12),(90112,64,12),(90112,128,8),(90112,256,13),(90112,512,13),(94208,4,3),(94208,8,4),(94208,16,9),(94208,32,13),(94208,64,8),(94208,128,7),(94208,256,13),(94208,512,11),(98304,2,1),(98304,4,1),(98304,8,3),(98304,16,9),(98304,32,14),(98304,64,7),(98304,128,5),(98304,256,19),(98304,512,19),(102400,4,2),(102400,8,4),(102400,16,8)]
private def descPart16 : List (ℕ × ℕ × ℕ) := [(102400,32,11),(102400,64,12),(102400,128,5),(102400,256,18),(102400,512,15),(106496,4,2),(106496,8,8),(106496,16,8),(106496,32,7),(106496,64,7),(106496,128,6),(106496,256,23),(106496,512,13),(110592,4,2),(110592,8,3),(110592,16,9),(110592,32,10),(110592,64,14),(110592,128,5),(110592,256,13),(110592,512,13),(114688,4,1),(114688,8,4),(114688,16,5),(114688,32,17),(114688,64,8),(114688,128,5),(114688,256,16),(114688,512,11),(118784,4,1),(118784,8,3),(118784,16,11)]
private def descPart17 : List (ℕ × ℕ × ℕ) := [(118784,32,12),(118784,64,10),(118784,128,5),(118784,256,18),(118784,512,13),(122880,8,4),(122880,16,7),(122880,32,12),(122880,64,12),(122880,128,7),(122880,256,16),(122880,512,17),(126976,4,1),(126976,8,2),(126976,16,6),(126976,32,8),(126976,64,10),(126976,128,5),(126976,256,22),(126976,512,12),(131072,4,1),(131072,8,7),(131072,16,8),(131072,32,12),(131072,64,12),(131072,128,5),(131072,256,13),(131072,512,20),(139264,4,3),(139264,8,8),(139264,16,12),(139264,32,26)]
private def descPart18 : List (ℕ × ℕ × ℕ) := [(139264,64,18),(139264,128,15),(139264,256,20),(139264,512,14),(139264,1024,24),(147456,4,3),(147456,8,9),(147456,16,11),(147456,32,23),(147456,64,22),(147456,128,17),(147456,256,22),(147456,512,12),(147456,1024,28),(155648,4,3),(155648,8,5),(155648,16,15),(155648,32,21),(155648,64,17),(155648,128,16),(155648,256,22),(155648,512,14),(155648,1024,26),(163840,4,5),(163840,8,8),(163840,16,14),(163840,32,23),(163840,64,19),(163840,128,17),(163840,256,9),(163840,512,23),(163840,1024,27)]
private def descPart19 : List (ℕ × ℕ × ℕ) := [(172032,4,3),(172032,8,9),(172032,16,11),(172032,32,18),(172032,64,20),(172032,128,20),(172032,256,10),(172032,512,27),(172032,1024,24),(180224,4,2),(180224,8,4),(180224,16,10),(180224,32,21),(180224,64,21),(180224,128,20),(180224,256,9),(180224,512,21),(180224,1024,29),(188416,4,2),(188416,8,3),(188416,16,15),(188416,32,20),(188416,64,20),(188416,128,13),(188416,256,16),(188416,512,23),(188416,1024,26),(196608,4,2),(196608,8,6),(196608,16,12),(196608,32,16),(196608,64,19)]
private def descPart20 : List (ℕ × ℕ × ℕ) := [(196608,128,17),(196608,256,13),(196608,512,26),(196608,1024,14),(196608,8192,11),(204800,4,3),(204800,8,6),(204800,16,15),(204800,32,18),(204800,64,23),(204800,128,16),(204800,256,15),(204800,512,24),(204800,8192,27),(212992,2,1),(212992,4,2),(212992,8,8),(212992,16,9),(212992,32,21),(212992,64,24),(212992,128,15),(212992,256,15),(212992,512,24),(212992,8192,29),(221184,4,3),(221184,8,4),(221184,16,12),(221184,32,21),(221184,64,15),(221184,128,13),(221184,256,7),(221184,512,37)]
private def descPart21 : List (ℕ × ℕ × ℕ) := [(221184,8192,24),(229376,4,2),(229376,8,5),(229376,16,9),(229376,32,14),(229376,64,20),(229376,128,19),(229376,256,8),(229376,512,36),(229376,8192,29),(237568,8,6),(237568,16,14),(237568,32,18),(237568,64,18),(237568,128,17),(237568,256,9),(237568,512,28),(237568,8192,23),(245760,4,3),(245760,8,5),(245760,16,9),(245760,32,21),(245760,64,22),(245760,128,15),(245760,256,10),(245760,512,30),(245760,8192,24),(253952,4,2),(253952,8,7),(253952,16,11),(253952,32,23),(253952,64,24)]
private def descPart22 : List (ℕ × ℕ × ℕ) := [(253952,128,18),(253952,256,10),(253952,512,23),(253952,8192,29),(262144,4,1),(262144,8,4),(262144,16,11),(262144,32,13),(262144,64,14),(262144,128,18),(262144,256,8),(262144,512,39),(262144,8192,22),(278528,4,4),(278528,8,6),(278528,16,18),(278528,32,34),(278528,64,46),(278528,128,36),(278528,256,17),(278528,512,63),(278528,8192,53),(294912,2,2),(294912,4,5),(294912,8,11),(294912,16,20),(294912,32,39),(294912,64,31),(294912,128,34),(294912,256,25),(294912,512,61),(294912,1024,2)]
private def descPart23 : List (ℕ × ℕ × ℕ) := [(294912,8192,47),(311296,4,2),(311296,8,10),(311296,16,17),(311296,32,35),(311296,64,37),(311296,128,38),(311296,256,24),(311296,512,36),(311296,1024,25),(311296,16384,49),(327680,4,2),(327680,8,9),(327680,16,20),(327680,32,31),(327680,64,42),(327680,128,34),(327680,256,24),(327680,512,38),(327680,1024,25),(327680,16384,51),(344064,4,2),(344064,8,10),(344064,16,16),(344064,32,30),(344064,64,36),(344064,128,34),(344064,256,29),(344064,512,37),(344064,1024,26),(344064,16384,55),(360448,4,1)]
private def descPart24 : List (ℕ × ℕ × ℕ) := [(360448,8,7),(360448,16,21),(360448,32,36),(360448,64,36),(360448,128,28),(360448,256,33),(360448,512,29),(360448,1024,30),(360448,16384,48),(376832,4,2),(376832,8,11),(376832,16,20),(376832,32,31),(376832,64,39),(376832,128,33),(376832,256,36),(376832,512,15),(376832,1024,47),(376832,16384,50),(393216,4,2),(393216,8,12),(393216,16,16),(393216,32,36),(393216,64,38),(393216,128,33),(393216,256,29),(393216,512,18),(393216,1024,41),(393216,16384,46),(409600,4,4),(409600,8,4),(409600,16,16)]
private def descPart25 : List (ℕ × ℕ × ℕ) := [(409600,32,32),(409600,64,34),(409600,128,37),(409600,256,24),(409600,512,20),(409600,1024,50),(409600,16384,46),(425984,4,3),(425984,8,9),(425984,16,16),(425984,32,31),(425984,64,32),(425984,128,37),(425984,256,34),(425984,512,24),(425984,1024,37),(425984,16384,46),(442368,4,2),(442368,8,7),(442368,16,17),(442368,32,27),(442368,64,35),(442368,128,36),(442368,256,25),(442368,512,22),(442368,1024,26),(442368,8192,21),(442368,16384,50),(458752,4,3),(458752,8,8),(458752,16,19),(458752,32,31)]
private def descPart26 : List (ℕ × ℕ × ℕ) := [(458752,64,30),(458752,128,37),(458752,256,28),(458752,512,30),(458752,1024,18),(458752,8192,22),(458752,16384,52),(475136,8,7),(475136,16,15),(475136,32,28),(475136,64,30),(475136,128,32),(475136,256,30),(475136,512,20),(475136,1024,26),(475136,8192,27),(475136,16384,49),(491520,4,3),(491520,8,9),(491520,16,12),(491520,32,36),(491520,64,28),(491520,128,35),(491520,256,27),(491520,512,17),(491520,1024,38),(491520,8192,21),(491520,16384,43),(507904,2,1),(507904,4,1),(507904,8,5),(507904,16,7)]
private def descPart27 : List (ℕ × ℕ × ℕ) := [(507904,32,16),(507904,64,18),(507904,128,16),(507904,256,18),(507904,512,9),(507904,1024,14),(507904,8192,11),(507904,16384,28)]
private def descriptors := descPart0 ++ descPart1 ++ descPart2 ++ descPart3 ++ descPart4 ++ descPart5 ++ descPart6 ++ descPart7 ++ descPart8 ++ descPart9 ++ descPart10 ++ descPart11 ++ descPart12 ++ descPart13 ++ descPart14 ++ descPart15 ++ descPart16 ++ descPart17 ++ descPart18 ++ descPart19 ++ descPart20 ++ descPart21 ++ descPart22 ++ descPart23 ++ descPart24 ++ descPart25 ++ descPart26 ++ descPart27

private def batch (pred : ℕ → Bool) (start len : ℕ) : Bool :=
  (List.range' start len).all pred

private theorem at_batch {f : ℕ → Bool} {s len i : ℕ} (h : batch f s len = true)
    (hlo : s ≤ i) (hhi : i < s+len) : f i = true :=
  List.all_eq_true.mp h _ (List.mem_range'_1.mpr ⟨hlo,hhi⟩)

private def isPrime (p : ℕ) := decide (2 ≤ p ∧ p < 14000) && primeBits.testBit (p-2)

private theorem mask_eq : primeBits = ColtonSieve.primeMask 2 13998 := by decide +kernel

private theorem isPrime_iff {p : ℕ} (hp : p < 14000) : isPrime p = true ↔ p.Prime := by
  by_cases hlo : 2 ≤ p
  · have h := @ColtonSieve.primeMask_bit 2 13998 (p-2) (by decide) (by decide) (by omega)
    rw [Nat.add_sub_of_le hlo] at h
    simpa only [isPrime,decide_eq_true (And.intro hlo hp), Bool.true_and,mask_eq] using h
  · have hn : ¬p.Prime := fun h => hlo h.two_le
    simp [isPrime,hlo,hn]

private theorem isPrime_proof {p : ℕ} (h : isPrime p = true) : p.Prime := by
  have hd := of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
  exact (isPrime_iff hd.2).1 h

private def rankStep (i : ℕ) : Bool :=
  rank (i+1) == rank i + (if isPrime (i+1) then 1 else 0)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert0 : PLift (batch rankStep 0 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert1 : PLift (batch rankStep 128 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert2 : PLift (batch rankStep 256 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert3 : PLift (batch rankStep 384 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert4 : PLift (batch rankStep 512 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert5 : PLift (batch rankStep 640 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert6 : PLift (batch rankStep 768 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert7 : PLift (batch rankStep 896 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert8 : PLift (batch rankStep 1024 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert9 : PLift (batch rankStep 1152 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert10 : PLift (batch rankStep 1280 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert11 : PLift (batch rankStep 1408 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert12 : PLift (batch rankStep 1536 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert13 : PLift (batch rankStep 1664 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert14 : PLift (batch rankStep 1792 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert15 : PLift (batch rankStep 1920 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert16 : PLift (batch rankStep 2048 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert17 : PLift (batch rankStep 2176 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert18 : PLift (batch rankStep 2304 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert19 : PLift (batch rankStep 2432 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert20 : PLift (batch rankStep 2560 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert21 : PLift (batch rankStep 2688 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert22 : PLift (batch rankStep 2816 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert23 : PLift (batch rankStep 2944 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert24 : PLift (batch rankStep 3072 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert25 : PLift (batch rankStep 3200 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert26 : PLift (batch rankStep 3328 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert27 : PLift (batch rankStep 3456 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert28 : PLift (batch rankStep 3584 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert29 : PLift (batch rankStep 3712 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert30 : PLift (batch rankStep 3840 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert31 : PLift (batch rankStep 3968 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert32 : PLift (batch rankStep 4096 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert33 : PLift (batch rankStep 4224 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert34 : PLift (batch rankStep 4352 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert35 : PLift (batch rankStep 4480 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert36 : PLift (batch rankStep 4608 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert37 : PLift (batch rankStep 4736 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert38 : PLift (batch rankStep 4864 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert39 : PLift (batch rankStep 4992 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert40 : PLift (batch rankStep 5120 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert41 : PLift (batch rankStep 5248 128 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def rankStepsCert42 : PLift (batch rankStep 5376 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 2000000 in
private theorem rankSteps (i : ℕ) (hi : i < 5392) : rankStep i = true := by
  by_cases h21 : i < 2688
  · by_cases h10 : i < 1280
    · by_cases h5 : i < 640
      · by_cases h2 : i < 256
        · by_cases h1 : i < 128
          · exact at_batch rankStepsCert0.down (by omega) (by omega)
          · exact at_batch rankStepsCert1.down (by omega) (by omega)
        · by_cases h3 : i < 384
          · exact at_batch rankStepsCert2.down (by omega) (by omega)
          · by_cases h4 : i < 512
            · exact at_batch rankStepsCert3.down (by omega) (by omega)
            · exact at_batch rankStepsCert4.down (by omega) (by omega)
      · by_cases h7 : i < 896
        · by_cases h6 : i < 768
          · exact at_batch rankStepsCert5.down (by omega) (by omega)
          · exact at_batch rankStepsCert6.down (by omega) (by omega)
        · by_cases h8 : i < 1024
          · exact at_batch rankStepsCert7.down (by omega) (by omega)
          · by_cases h9 : i < 1152
            · exact at_batch rankStepsCert8.down (by omega) (by omega)
            · exact at_batch rankStepsCert9.down (by omega) (by omega)
    · by_cases h15 : i < 1920
      · by_cases h12 : i < 1536
        · by_cases h11 : i < 1408
          · exact at_batch rankStepsCert10.down (by omega) (by omega)
          · exact at_batch rankStepsCert11.down (by omega) (by omega)
        · by_cases h13 : i < 1664
          · exact at_batch rankStepsCert12.down (by omega) (by omega)
          · by_cases h14 : i < 1792
            · exact at_batch rankStepsCert13.down (by omega) (by omega)
            · exact at_batch rankStepsCert14.down (by omega) (by omega)
      · by_cases h18 : i < 2304
        · by_cases h16 : i < 2048
          · exact at_batch rankStepsCert15.down (by omega) (by omega)
          · by_cases h17 : i < 2176
            · exact at_batch rankStepsCert16.down (by omega) (by omega)
            · exact at_batch rankStepsCert17.down (by omega) (by omega)
        · by_cases h19 : i < 2432
          · exact at_batch rankStepsCert18.down (by omega) (by omega)
          · by_cases h20 : i < 2560
            · exact at_batch rankStepsCert19.down (by omega) (by omega)
            · exact at_batch rankStepsCert20.down (by omega) (by omega)
  · by_cases h32 : i < 4096
    · by_cases h26 : i < 3328
      · by_cases h23 : i < 2944
        · by_cases h22 : i < 2816
          · exact at_batch rankStepsCert21.down (by omega) (by omega)
          · exact at_batch rankStepsCert22.down (by omega) (by omega)
        · by_cases h24 : i < 3072
          · exact at_batch rankStepsCert23.down (by omega) (by omega)
          · by_cases h25 : i < 3200
            · exact at_batch rankStepsCert24.down (by omega) (by omega)
            · exact at_batch rankStepsCert25.down (by omega) (by omega)
      · by_cases h29 : i < 3712
        · by_cases h27 : i < 3456
          · exact at_batch rankStepsCert26.down (by omega) (by omega)
          · by_cases h28 : i < 3584
            · exact at_batch rankStepsCert27.down (by omega) (by omega)
            · exact at_batch rankStepsCert28.down (by omega) (by omega)
        · by_cases h30 : i < 3840
          · exact at_batch rankStepsCert29.down (by omega) (by omega)
          · by_cases h31 : i < 3968
            · exact at_batch rankStepsCert30.down (by omega) (by omega)
            · exact at_batch rankStepsCert31.down (by omega) (by omega)
    · by_cases h37 : i < 4736
      · by_cases h34 : i < 4352
        · by_cases h33 : i < 4224
          · exact at_batch rankStepsCert32.down (by omega) (by omega)
          · exact at_batch rankStepsCert33.down (by omega) (by omega)
        · by_cases h35 : i < 4480
          · exact at_batch rankStepsCert34.down (by omega) (by omega)
          · by_cases h36 : i < 4608
            · exact at_batch rankStepsCert35.down (by omega) (by omega)
            · exact at_batch rankStepsCert36.down (by omega) (by omega)
      · by_cases h40 : i < 5120
        · by_cases h38 : i < 4864
          · exact at_batch rankStepsCert37.down (by omega) (by omega)
          · by_cases h39 : i < 4992
            · exact at_batch rankStepsCert38.down (by omega) (by omega)
            · exact at_batch rankStepsCert39.down (by omega) (by omega)
        · by_cases h41 : i < 5248
          · exact at_batch rankStepsCert40.down (by omega) (by omega)
          · by_cases h42 : i < 5376
            · exact at_batch rankStepsCert41.down (by omega) (by omega)
            · exact at_batch rankStepsCert42.down (by omega) (by omega)


private theorem rank_ok (i : ℕ) (hi : i < 5393) : rank i = i.primeCounting := by
  induction i with
  | zero => decide +kernel
  | succ i ih =>
    have h := eq_of_beq (rankSteps i (by omega))
    change rank (i+1) = rank i + _ at h
    rw [h, ih (by omega)]
    simp only [isPrime_iff (p:=i+1) (by omega)]
    exact (Nat.count_succ Nat.Prime (i+1)).symm

private def excl (v : ℕ) := if v < 5393 then rank v else v+1
private theorem excl_ok (v : ℕ) : v.primeCounting ≤ excl v := by
  unfold excl
  split
  · rw [rank_ok _ ‹_›]
  · exact Nat.count_le Nat.Prime

private def low (z : ℕ) := if z < 5393 then rank z else lower z
private theorem low_ok (h : ∀ x : ℝ, 5393 ≤ x →
    x/(Real.log x-1) ≤ (⌊x⌋₊.primeCounting : ℝ)) (z : ℕ) : low z ≤ z.primeCounting := by
  unfold low
  split
  · rw [rank_ok _ ‹_›]
  · exact lower_ok h (by omega)

private def unpack : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f+1, w => if w=0 then [] else
    List.replicate ((w >>> 14)%32) (w%16384) ++ unpack f (w >>> 19)

private def rowOK (r : ℕ × ℕ × ℕ) (w : ℕ) : Bool :=
  let k := w%524288
  let fs := unpack 6 (w >>> 19)
  decide (fs.prod = k) && fs.all isPrime && decide
    (0 < k ∧ k ≤ 500000 ∧ k ≤ r.1 ∧
      2 * (fs.toFinset.prod (fun p => fs.count p + 1)) ∣ k ∧
      excl (max (fs.toFinset.sup id) (4096/k)) ≤ r.2.1)

private def valid (i : ℕ) : Bool :=
  (witnesses i).length == (row i).2.2 && (witnesses i).all (rowOK (row i))

private theorem factor_data {k : ℕ} {fs : List ℕ} (he : fs.prod = k) (hp : ∀ p ∈ fs, p.Prime) :
    fs.toFinset = k.primeFactors ∧ ∀ p, fs.count p = k.factorization p := by
  have perm := Nat.primeFactorsList_unique (n := k) he hp
  constructor
  · rw [← Nat.toFinset_factors]
    ext p
    exact List.mem_toFinset.trans (perm.mem_iff.trans List.mem_toFinset.symm)
  · intro p
    rw [← Nat.primeFactorsList_count_eq]
    exact perm.count_eq p

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert0 : PLift (batch valid 0 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert1 : PLift (batch valid 16 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert2 : PLift (batch valid 32 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert3 : PLift (batch valid 48 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert4 : PLift (batch valid 64 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert5 : PLift (batch valid 80 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert6 : PLift (batch valid 96 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert7 : PLift (batch valid 112 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert8 : PLift (batch valid 128 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert9 : PLift (batch valid 144 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert10 : PLift (batch valid 160 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert11 : PLift (batch valid 176 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert12 : PLift (batch valid 192 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert13 : PLift (batch valid 208 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert14 : PLift (batch valid 224 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert15 : PLift (batch valid 240 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert16 : PLift (batch valid 256 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert17 : PLift (batch valid 272 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert18 : PLift (batch valid 288 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert19 : PLift (batch valid 304 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert20 : PLift (batch valid 320 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert21 : PLift (batch valid 336 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert22 : PLift (batch valid 352 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert23 : PLift (batch valid 368 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert24 : PLift (batch valid 384 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert25 : PLift (batch valid 400 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert26 : PLift (batch valid 416 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert27 : PLift (batch valid 432 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert28 : PLift (batch valid 448 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert29 : PLift (batch valid 464 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert30 : PLift (batch valid 480 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert31 : PLift (batch valid 496 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert32 : PLift (batch valid 512 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert33 : PLift (batch valid 528 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert34 : PLift (batch valid 544 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert35 : PLift (batch valid 560 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert36 : PLift (batch valid 576 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert37 : PLift (batch valid 592 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert38 : PLift (batch valid 608 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert39 : PLift (batch valid 624 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert40 : PLift (batch valid 640 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert41 : PLift (batch valid 656 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert42 : PLift (batch valid 672 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert43 : PLift (batch valid 688 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert44 : PLift (batch valid 704 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert45 : PLift (batch valid 720 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert46 : PLift (batch valid 736 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert47 : PLift (batch valid 752 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert48 : PLift (batch valid 768 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert49 : PLift (batch valid 784 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert50 : PLift (batch valid 800 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert51 : PLift (batch valid 816 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert52 : PLift (batch valid 832 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert53 : PLift (batch valid 848 16 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def validRowsCert54 : PLift (batch valid 864 8 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 2000000 in
private theorem validRows (i : ℕ) (hi : i < 872) : valid i = true := by
  by_cases h27 : i < 432
  · by_cases h13 : i < 208
    · by_cases h6 : i < 96
      · by_cases h3 : i < 48
        · by_cases h1 : i < 16
          · exact at_batch validRowsCert0.down (by omega) (by omega)
          · by_cases h2 : i < 32
            · exact at_batch validRowsCert1.down (by omega) (by omega)
            · exact at_batch validRowsCert2.down (by omega) (by omega)
        · by_cases h4 : i < 64
          · exact at_batch validRowsCert3.down (by omega) (by omega)
          · by_cases h5 : i < 80
            · exact at_batch validRowsCert4.down (by omega) (by omega)
            · exact at_batch validRowsCert5.down (by omega) (by omega)
      · by_cases h9 : i < 144
        · by_cases h7 : i < 112
          · exact at_batch validRowsCert6.down (by omega) (by omega)
          · by_cases h8 : i < 128
            · exact at_batch validRowsCert7.down (by omega) (by omega)
            · exact at_batch validRowsCert8.down (by omega) (by omega)
        · by_cases h11 : i < 176
          · by_cases h10 : i < 160
            · exact at_batch validRowsCert9.down (by omega) (by omega)
            · exact at_batch validRowsCert10.down (by omega) (by omega)
          · by_cases h12 : i < 192
            · exact at_batch validRowsCert11.down (by omega) (by omega)
            · exact at_batch validRowsCert12.down (by omega) (by omega)
    · by_cases h20 : i < 320
      · by_cases h16 : i < 256
        · by_cases h14 : i < 224
          · exact at_batch validRowsCert13.down (by omega) (by omega)
          · by_cases h15 : i < 240
            · exact at_batch validRowsCert14.down (by omega) (by omega)
            · exact at_batch validRowsCert15.down (by omega) (by omega)
        · by_cases h18 : i < 288
          · by_cases h17 : i < 272
            · exact at_batch validRowsCert16.down (by omega) (by omega)
            · exact at_batch validRowsCert17.down (by omega) (by omega)
          · by_cases h19 : i < 304
            · exact at_batch validRowsCert18.down (by omega) (by omega)
            · exact at_batch validRowsCert19.down (by omega) (by omega)
      · by_cases h23 : i < 368
        · by_cases h21 : i < 336
          · exact at_batch validRowsCert20.down (by omega) (by omega)
          · by_cases h22 : i < 352
            · exact at_batch validRowsCert21.down (by omega) (by omega)
            · exact at_batch validRowsCert22.down (by omega) (by omega)
        · by_cases h25 : i < 400
          · by_cases h24 : i < 384
            · exact at_batch validRowsCert23.down (by omega) (by omega)
            · exact at_batch validRowsCert24.down (by omega) (by omega)
          · by_cases h26 : i < 416
            · exact at_batch validRowsCert25.down (by omega) (by omega)
            · exact at_batch validRowsCert26.down (by omega) (by omega)
  · by_cases h41 : i < 656
    · by_cases h34 : i < 544
      · by_cases h30 : i < 480
        · by_cases h28 : i < 448
          · exact at_batch validRowsCert27.down (by omega) (by omega)
          · by_cases h29 : i < 464
            · exact at_batch validRowsCert28.down (by omega) (by omega)
            · exact at_batch validRowsCert29.down (by omega) (by omega)
        · by_cases h32 : i < 512
          · by_cases h31 : i < 496
            · exact at_batch validRowsCert30.down (by omega) (by omega)
            · exact at_batch validRowsCert31.down (by omega) (by omega)
          · by_cases h33 : i < 528
            · exact at_batch validRowsCert32.down (by omega) (by omega)
            · exact at_batch validRowsCert33.down (by omega) (by omega)
      · by_cases h37 : i < 592
        · by_cases h35 : i < 560
          · exact at_batch validRowsCert34.down (by omega) (by omega)
          · by_cases h36 : i < 576
            · exact at_batch validRowsCert35.down (by omega) (by omega)
            · exact at_batch validRowsCert36.down (by omega) (by omega)
        · by_cases h39 : i < 624
          · by_cases h38 : i < 608
            · exact at_batch validRowsCert37.down (by omega) (by omega)
            · exact at_batch validRowsCert38.down (by omega) (by omega)
          · by_cases h40 : i < 640
            · exact at_batch validRowsCert39.down (by omega) (by omega)
            · exact at_batch validRowsCert40.down (by omega) (by omega)
    · by_cases h48 : i < 768
      · by_cases h44 : i < 704
        · by_cases h42 : i < 672
          · exact at_batch validRowsCert41.down (by omega) (by omega)
          · by_cases h43 : i < 688
            · exact at_batch validRowsCert42.down (by omega) (by omega)
            · exact at_batch validRowsCert43.down (by omega) (by omega)
        · by_cases h46 : i < 736
          · by_cases h45 : i < 720
            · exact at_batch validRowsCert44.down (by omega) (by omega)
            · exact at_batch validRowsCert45.down (by omega) (by omega)
          · by_cases h47 : i < 752
            · exact at_batch validRowsCert46.down (by omega) (by omega)
            · exact at_batch validRowsCert47.down (by omega) (by omega)
      · by_cases h51 : i < 816
        · by_cases h49 : i < 784
          · exact at_batch validRowsCert48.down (by omega) (by omega)
          · by_cases h50 : i < 800
            · exact at_batch validRowsCert49.down (by omega) (by omega)
            · exact at_batch validRowsCert50.down (by omega) (by omega)
        · by_cases h53 : i < 848
          · by_cases h52 : i < 832
            · exact at_batch validRowsCert51.down (by omega) (by omega)
            · exact at_batch validRowsCert52.down (by omega) (by omega)
          · by_cases h54 : i < 864
            · exact at_batch validRowsCert53.down (by omega) (by omega)
            · exact at_batch validRowsCert54.down (by omega) (by omega)


private theorem valid_info {i : ℕ} (hi : i < 872) :
    (keys i).length = (row i).2.2 ∧ ∀ k ∈ keys i, 0 < k ∧ k ≤ 500000 ∧ k ≤ (row i).1 ∧
    2*k.divisors.card ∣ k ∧ (max (k.primeFactors.sup id) (4096/k)).primeCounting ≤ (row i).2.1 := by
  have hv := validRows i hi
  simp only [valid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hv
  refine ⟨by simpa only [keys,List.length_map] using hv.1, ?_⟩
  intro k hk
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hk
  have ht := hv.2 w hw
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
  obtain ⟨⟨hkprod,hpr⟩,hpos,hk1,hk2,hd,he⟩ := ht
  obtain ⟨hs,hf⟩ := factor_data hkprod (fun p hp => isPrime_proof (hpr p hp))
  rw [hs] at he hd
  simp only [hf, ← Nat.card_divisors hpos.ne'] at hd
  exact ⟨hpos,hk1,hk2,hd,(excl_ok _).trans he⟩

private def ix := List.range 872
private def allKeys := ix.flatMap keys
private def fresh : ℕ → List ℕ → Bool
  | _, [] => true
  | s, k::ks => !(s.testBit k) && fresh (s ||| (1 <<< k)) ks

private theorem fresh_ok {s : ℕ} {l : List ℕ} (h : fresh s l = true) :
    l.Nodup ∧ ∀ k ∈ l, s.testBit k = false := by
  induction l generalizing s with
  | nil => simp
  | cons k ks ih =>
    change (!(s.testBit k) && fresh (s ||| (1 <<< k)) ks) = true at h
    obtain ⟨hk,ht⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hd,hs⟩ := ih ht
    have hbit : s.testBit k = false := by simpa using hk
    constructor
    · apply List.nodup_cons.mpr
      refine ⟨?_,hd⟩
      intro hm
      have := hs k hm
      simp [Nat.testBit_or, Nat.testBit_shiftLeft] at this
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hbit
      · have := hs j hj
        rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
        exact this.1

set_option maxHeartbeats 0 in
set_option maxRecDepth 60000 in
private theorem distinctKeys : allKeys.Nodup := by
  apply (fresh_ok (s := 0) (l := allKeys) ?_).1
  decide +kernel

private def grid (j : ℕ) := (fun x : ℕ => x+x/40)^[j] 4096
private theorem grid_succ (j : ℕ) : grid (j+1) = grid j + grid j/40 := by
  simp only [grid, Function.iterate_succ_apply']

private def step (i : ℕ) := point (i+1) == point i + point i/40
set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def transitionsCert0 : PLift (batch step 0 100 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def transitionsCert1 : PLift (batch step 100 100 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def transitionsCert2 : PLift (batch step 200 100 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def transitionsCert3 : PLift (batch step 300 100 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def transitionsCert4 : PLift (batch step 400 100 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def transitionsCert5 : PLift (batch step 500 100 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def transitionsCert6 : PLift (batch step 600 10 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 2000000 in
private theorem transitions (i : ℕ) (hi : i < 610) : step i = true := by
  by_cases h3 : i < 300
  · by_cases h1 : i < 100
    · exact at_batch transitionsCert0.down (by omega) (by omega)
    · by_cases h2 : i < 200
      · exact at_batch transitionsCert1.down (by omega) (by omega)
      · exact at_batch transitionsCert2.down (by omega) (by omega)
  · by_cases h5 : i < 500
    · by_cases h4 : i < 400
      · exact at_batch transitionsCert3.down (by omega) (by omega)
      · exact at_batch transitionsCert4.down (by omega) (by omega)
    · by_cases h6 : i < 600
      · exact at_batch transitionsCert5.down (by omega) (by omega)
      · exact at_batch transitionsCert6.down (by omega) (by omega)

private theorem point_ok (i : ℕ) (hi : i ≤ 610) : point i = grid (317+i) := by
  induction i with
  | zero => decide +kernel
  | succ i ih =>
    have h := eq_of_beq (transitions i (by omega))
    change point (i+1) = point i + point i/40 at h
    rw [h, ih (by omega)]
    exact (grid_succ _).symm

set_option maxHeartbeats 100000 in
set_option maxRecDepth 10000 in
private theorem descriptor_eq : ix.map row = descriptors := by decide +kernel

private def S : ℕ := 1000000000000000
private def den (v : ℕ) := 694*(v.log2+1)-1000
private def ld (v : ℕ) := 1000*v/den v
private def slope (L U k e : ℕ) :=
    1000*S/(k*den (U/k)) - ((e+2)*S/L + 1)

private theorem slope_le {x L U k e : ℕ} (hl : L ≤ x) (hu : x ≤ U)
    (hk : 0 < k) (hlk : 5393 ≤ L/k) :
    x*slope L U k e ≤ S*(ld (x/k) - e) := by
  let q := x/k
  let D := den (U/k)
  let d := den q
  have hq : 5393 ≤ q := hlk.trans (Nat.div_le_div_right hl)
  have hUq : q ≤ U/k := Nat.div_le_div_right hu
  have hlog : q.log2 ≤ (U/k).log2 :=
    (Nat.le_log2 (by omega)).2 ((Nat.log2_self_le (by omega : q ≠ 0)).trans hUq)
  have hD : d ≤ D := by dsimp [D,d,den]; omega
  have h12 : 12 ≤ q.log2 := (Nat.le_log2 (by omega)).2 (by omega)
  have hd : 1000 ≤ d := by dsimp [d,den]; omega
  have hDpos : 0 < k*D := Nat.mul_pos hk (by omega)
  let r := ld q
  have hdq : 1000*q ≤ (r+1)*d :=
    (Nat.lt_mul_div_succ (1000*q) (by omega : 0 < d)).le.trans_eq (Nat.mul_comm ..)
  have hkq : x ≤ (q+1)*k := (Nat.lt_mul_div_succ x hk).le.trans_eq (Nat.mul_comm ..)
  have hmain : 1000*x ≤ k*D*(r+2) := by
    calc
      _ ≤ 1000*((q+1)*k) := Nat.mul_le_mul_left _ hkq
      _ = k*(1000*q+1000) := by ring
      _ ≤ k*((r+1)*d+d) := Nat.mul_le_mul_left _ (by omega)
      _ = k*d*(r+2) := by ring
      _ ≤ _ := by gcongr
  let a := 1000*S/(k*D)
  have hfloor : a*(k*D) ≤ 1000*S := Nat.div_mul_le_self ..
  have ha : x*a ≤ S*(r+2) := by
    apply Nat.le_of_mul_le_mul_right (c := k*D) _ hDpos
    calc
      x*a*(k*D) = x*(a*(k*D)) := by ring
      _ ≤ x*(1000*S) := Nat.mul_le_mul_left _ hfloor
      _ = S*(1000*x) := by ring
      _ ≤ S*(k*D*(r+2)) := Nat.mul_le_mul_left S hmain
      _ = S*(r+2)*(k*D) := by ring
  let b := (e+2)*S/L+1
  have hLpos : 0 < L := by
    have := Nat.div_le_self L k
    omega
  have hb : (e+2)*S ≤ x*b :=
    (Nat.lt_mul_div_succ ((e+2)*S) hLpos).le.trans (Nat.mul_le_mul_right b hl)
  change x*(a-b) ≤ S*(r-e)
  rw [Nat.mul_sub, Nat.mul_sub]
  rw [Nat.mul_add] at ha
  rw [Nat.add_mul, Nat.mul_comm e S] at hb
  omega


private theorem upper_slope {x du d w cnt p : ℕ} (hpos : 0 < du) (hdu : du ≤ d)
    (hup : p ≤ 1000*(x+x/40)/d) (hs : 1025*S ≤ 2*w*du) (hb : x*w ≤ S*cnt) :
    p ≤ 2*cnt := by
  have hdpos : 0 < d := lt_of_lt_of_le hpos hdu
  have hp : p*d ≤ 1000*(x+x/40) := (Nat.le_div_iff_mul_le hdpos).mp hup
  have hspos : 0 < S := by decide
  apply Nat.le_of_mul_le_mul_right (c := du*S) _ (Nat.mul_pos hpos hspos)
  calc
    p*(du*S) = (p*du)*S := by ring
    _ ≤ (p*d)*S := by gcongr
    _ ≤ (1000*(x+x/40))*S := Nat.mul_le_mul_right _ hp
    _ ≤ (1025*x)*S := Nat.mul_le_mul_right _ (by omega)
    _ = x*(1025*S) := by ring
    _ ≤ x*(2*w*du) := Nat.mul_le_mul_left x hs
    _ = 2*(x*w)*du := by ring
    _ ≤ 2*(S*cnt)*du := by gcongr
    _ = 2*cnt*(du*S) := by ring

private def coefficient (L U k e : ℕ) :=
  if L/k < 5393 then S*(rank (L/k)-e)/U else slope L U k e

private def coeffRow (L U : ℕ) (r : ℕ × ℕ × ℕ) :=
  r.2.2 * coefficient L U r.1 r.2.1

private theorem coeff_bound
    (hL : ∀ x : ℝ, 5393 ≤ x → x/(Real.log x-1) ≤ (⌊x⌋₊.primeCounting : ℝ))
    {x L U k e : ℕ} (hl : L ≤ x) (hu : x ≤ U) (hk : 0 < k) :
    x*coefficient L U k e ≤ S*((x/k).primeCounting-e) := by
  unfold coefficient
  split
  · rename_i hs
    have hpi := Nat.monotone_primeCounting (Nat.div_le_div_right (c:=k) hl)
    calc
      _ ≤ U*(S*(rank (L/k)-e)/U) := Nat.mul_le_mul_right _ hu
      _ ≤ S*(rank (L/k)-e) := Nat.mul_div_le ..
      _ ≤ _ := by rw [rank_ok _ hs]; exact Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hpi e)
  · rename_i hs
    have hq : 5393 ≤ x/k := (Nat.le_of_not_gt hs).trans (Nat.div_le_div_right hl)
    apply (slope_le hl hu hk (by omega)).trans
    exact Nat.mul_le_mul_left S (Nat.sub_le_sub_right (lower_ok hL hq) _)

private def bands : Array (ℕ × ℕ) :=
  #[(0,8),(9,17),(18,24),(25,37),(38,48),(49,66),(67,81),(82,104),(105,134),
    (135,173),(174,216),(217,289),(290,354),(355,403),(404,457),(458,502),
    (503,553),(554,597),(598,609)]

private def band (i : ℕ) := (List.range 19).find? (fun a => i ≤ (bands[a]!).2) |>.getD 0
private def leftEnd (a : ℕ) := point (bands[a]!).1
private def rightEnd (a : ℕ) := point (bands[a]!).2
private def upperDen (z : ℕ) := 693*z.log2-1100
private def bandDen (a : ℕ) := upperDen (point ((bands[a]!).1+1))

private def cover (i : ℕ) := let a := band i; decide
  (a < 19 ∧ leftEnd a ≤ point i ∧ point i ≤ rightEnd a ∧
    1000000 ≤ point i ∧ 60184 ≤ point (i+1) ∧ 0 < bandDen a ∧ bandDen a ≤ upperDen (point (i+1)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def coversCert0 : PLift (batch cover 0 64 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def coversCert1 : PLift (batch cover 64 64 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def coversCert2 : PLift (batch cover 128 64 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def coversCert3 : PLift (batch cover 192 64 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def coversCert4 : PLift (batch cover 256 64 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def coversCert5 : PLift (batch cover 320 64 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def coversCert6 : PLift (batch cover 384 64 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def coversCert7 : PLift (batch cover 448 64 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def coversCert8 : PLift (batch cover 512 64 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def coversCert9 : PLift (batch cover 576 34 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 2000000 in
private theorem covers (i : ℕ) (hi : i < 610) : cover i = true := by
  by_cases h5 : i < 320
  · by_cases h2 : i < 128
    · by_cases h1 : i < 64
      · exact at_batch coversCert0.down (by omega) (by omega)
      · exact at_batch coversCert1.down (by omega) (by omega)
    · by_cases h3 : i < 192
      · exact at_batch coversCert2.down (by omega) (by omega)
      · by_cases h4 : i < 256
        · exact at_batch coversCert3.down (by omega) (by omega)
        · exact at_batch coversCert4.down (by omega) (by omega)
  · by_cases h7 : i < 448
    · by_cases h6 : i < 384
      · exact at_batch coversCert5.down (by omega) (by omega)
      · exact at_batch coversCert6.down (by omega) (by omega)
    · by_cases h8 : i < 512
      · exact at_batch coversCert7.down (by omega) (by omega)
      · by_cases h9 : i < 576
        · exact at_batch coversCert8.down (by omega) (by omega)
        · exact at_batch coversCert9.down (by omega) (by omega)


private def score (a : ℕ) := (descriptors.map (coeffRow (leftEnd a) (rightEnd a))).sum
private def bandBudget (a : ℕ) := decide (1025*S ≤ 2*score a*bandDen a)

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert0 : PLift (batch bandBudget 0 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert1 : PLift (batch bandBudget 1 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert2 : PLift (batch bandBudget 2 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert3 : PLift (batch bandBudget 3 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert4 : PLift (batch bandBudget 4 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert5 : PLift (batch bandBudget 5 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert6 : PLift (batch bandBudget 6 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert7 : PLift (batch bandBudget 7 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert8 : PLift (batch bandBudget 8 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert9 : PLift (batch bandBudget 9 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert10 : PLift (batch bandBudget 10 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert11 : PLift (batch bandBudget 11 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert12 : PLift (batch bandBudget 12 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert13 : PLift (batch bandBudget 13 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert14 : PLift (batch bandBudget 14 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert15 : PLift (batch bandBudget 15 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert16 : PLift (batch bandBudget 16 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert17 : PLift (batch bandBudget 17 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 30000 in
private def bandBudgetsCert18 : PLift (batch bandBudget 18 1 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 2000000 in
private theorem bandBudgets (i : ℕ) (hi : i < 19) : bandBudget i = true := by
  by_cases h9 : i < 9
  · by_cases h4 : i < 4
    · by_cases h2 : i < 2
      · by_cases h1 : i < 1
        · exact at_batch bandBudgetsCert0.down (by omega) (by omega)
        · exact at_batch bandBudgetsCert1.down (by omega) (by omega)
      · by_cases h3 : i < 3
        · exact at_batch bandBudgetsCert2.down (by omega) (by omega)
        · exact at_batch bandBudgetsCert3.down (by omega) (by omega)
    · by_cases h6 : i < 6
      · by_cases h5 : i < 5
        · exact at_batch bandBudgetsCert4.down (by omega) (by omega)
        · exact at_batch bandBudgetsCert5.down (by omega) (by omega)
      · by_cases h7 : i < 7
        · exact at_batch bandBudgetsCert6.down (by omega) (by omega)
        · by_cases h8 : i < 8
          · exact at_batch bandBudgetsCert7.down (by omega) (by omega)
          · exact at_batch bandBudgetsCert8.down (by omega) (by omega)
  · by_cases h14 : i < 14
    · by_cases h11 : i < 11
      · by_cases h10 : i < 10
        · exact at_batch bandBudgetsCert9.down (by omega) (by omega)
        · exact at_batch bandBudgetsCert10.down (by omega) (by omega)
      · by_cases h12 : i < 12
        · exact at_batch bandBudgetsCert11.down (by omega) (by omega)
        · by_cases h13 : i < 13
          · exact at_batch bandBudgetsCert12.down (by omega) (by omega)
          · exact at_batch bandBudgetsCert13.down (by omega) (by omega)
    · by_cases h16 : i < 16
      · by_cases h15 : i < 15
        · exact at_batch bandBudgetsCert14.down (by omega) (by omega)
        · exact at_batch bandBudgetsCert15.down (by omega) (by omega)
      · by_cases h17 : i < 17
        · exact at_batch bandBudgetsCert16.down (by omega) (by omega)
        · by_cases h18 : i < 18
          · exact at_batch bandBudgetsCert17.down (by omega) (by omega)
          · exact at_batch bandBudgetsCert18.down (by omega) (by omega)


private theorem count_le {f : ℕ → ℕ} {l : List ℕ} {b : ℕ} (h : ∀ k ∈ l, b ≤ f k) :
    l.length * b ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, Nat.add_mul, one_mul, List.map_cons, List.sum_cons]
    have := h a (by simp)
    have := ih (fun k hk => h k (by simp [hk]))
    omega

private theorem sum_groups (f : ℕ → ℕ) (s : List ℕ) :
    ((s.flatMap keys).map f).sum = (s.map (fun i => ((keys i).map f).sum)).sum := by
  induction s with
  | nil => rfl
  | cons i s ih => simp [ih]

set_option maxRecDepth 8000 in
private theorem middle (hL : ∀ x : ℝ, 5393 ≤ x →
    x/(Real.log x-1) ≤ (⌊x⌋₊.primeCounting : ℝ))
    (hU : ∀ x : ℝ, 60184 ≤ x → (⌊x⌋₊.primeCounting : ℝ) ≤ x/(Real.log x-11/10))
    (j : ℕ) (hj : 317 ≤ j) (hu : j < 927) :
    let x := grid j
    let G := ((Icc 1 (min 500000 (x/2))).filter (fun k : ℕ => 0 < k ∧ 2*k.divisors.card ∣ k))
    (x+x/40).primeCounting ≤ 2*(307 + ∑ k ∈ G,
      ((x/k).primeCounting - (max (k.primeFactors.sup id) (4096/k)).primeCounting)) := by
  let i := j-317
  have hi : i < 610 := by dsimp [i]; omega
  have hp := point_ok i (by omega)
  have hp' := point_ok (i+1) (by omega)
  have he : 317+i = j := by dsimp [i]; omega
  rw [he] at hp
  rw [← Nat.add_assoc, he, grid_succ] at hp'
  let c := band i
  have hc : c < 19 ∧ leftEnd c ≤ point i ∧ point i ≤ rightEnd c ∧
    1000000 ≤ point i ∧ 60184 ≤ point (i+1) ∧ 0 < bandDen c ∧ bandDen c ≤ upperDen (point (i+1)) :=
    of_decide_eq_true (covers i hi)
  obtain ⟨h19,hl,hu',hbig,hup,hden,hden'⟩ := hc
  rw [hp] at hl hu' hbig
  rw [hp'] at hup hden'
  have hb : 1025*S ≤ 2*score c*bandDen c := of_decide_eq_true (bandBudgets c h19)
  let x := grid j
  let f := fun k : ℕ => (x/k).primeCounting - (max (k.primeFactors.sup id) (4096/k)).primeCounting
  let G := ((Icc 1 (min 500000 (x/2))).filter (fun k : ℕ => 0 < k ∧ 2*k.divisors.card ∣ k))
  have big : 1000000 ≤ x := hbig
  have hs : allKeys.toFinset ⊆ G := by
    intro k hk
    obtain ⟨a,ha,hk⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hk)
    obtain ⟨hk0,hk1,_,hd,_⟩ := (valid_info (List.mem_range.mp ha)).2 k hk
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hk0,le_min hk1 (by omega)⟩, hk0,hd⟩
  let frow := fun a => coeffRow (leftEnd c) (rightEnd c) (row a)
  have hgroup (a : ℕ) (ha : a ∈ ix) : x*frow a ≤ S*((keys a).map f).sum := by
    obtain ⟨hsize,hvalid⟩ := valid_info (List.mem_range.mp ha)
    let w := coefficient (leftEnd c) (rightEnd c) (row a).1 (row a).2.1
    calc
      _ = (keys a).length*(x*w) := by dsimp [frow,coeffRow,w]; rw [hsize]; ring
      _ ≤ ((keys a).map (fun k => S*f k)).sum := by
        apply count_le
        intro k hk
        obtain ⟨hk0,_,hk2,_,he⟩ := hvalid k hk
        apply (coeff_bound hL hl hu' (hk0.trans_le hk2)).trans
        exact Nat.mul_le_mul_left _ (tsub_le_tsub (Nat.monotone_primeCounting
          (Nat.div_le_div_left hk2 hk0)) he)
      _ = _ := List.sum_map_mul_left ..
  have hsub : (allKeys.map f).sum ≤ ∑ k ∈ G, f k := by
    rw [← List.sum_toFinset f distinctKeys]
    exact Finset.sum_le_sum_of_subset hs
  have hsum : x*score c ≤ S*(∑ k ∈ G, f k) := by
    calc
      _ = (ix.map (fun a => x*frow a)).sum := by
        rw [List.sum_map_mul_left]
        simp only [score, ← descriptor_eq,List.map_map]
        rfl
      _ ≤ (ix.map (fun a => S*((keys a).map f).sum)).sum := List.sum_le_sum hgroup
      _ = S*(allKeys.map f).sum := by rw [List.sum_map_mul_left,allKeys,sum_groups f ix]
      _ ≤ _ := Nat.mul_le_mul_left _ hsub
  have hupp := upper_ok hU hup
  have hcomp := upper_slope hden hden' hupp hb hsum
  change (x+x/40).primeCounting ≤ 2*(307+∑ k ∈ G, f k)
  exact hcomp.trans (Nat.mul_le_mul_left 2 (by omega))

end ColtonMiddle

open Nat Finset OeisA111291

namespace OMA.R_OeisA111291_colton_conjecture_R2

/-- The first 317 integer comparisons, ending at 10,222,860. -/
def H1 : Prop := ∀ j < 317,
    let x := (fun m : ℕ => m + m / 40)^[j] 4096
    let G := ((Icc 1 (min 10000 (x/2))).filter (fun k : ℕ => 0 < k ∧ 2 * k.divisors.card ∣ k))
    (x + x/40).primeCounting ≤ 2 * (307 + (∑ k ∈ G, ((x/k).primeCounting - (max (k.primeFactors.sup id) (4096/k)).primeCounting)))

/-- Finite harmonic mass and excluded prime counts of Zelinsky’s generators. -/
def H2 : Prop :=
  let G := ((Icc 1 20000000).filter (fun k : ℕ => 0 < k ∧ 2 * k.divisors.card ∣ k))
  (251/500 : ℚ) ≤ ∑ k ∈ G, 1/(k:ℚ) ∧
    ∑ k ∈ G, (k.primeFactors.sup id).primeCounting ≤ 2000000000

/-- Dusart's explicit prime-counting estimates, theorem 6.9, equation (6.6). -/
def H3 : Prop :=
  (∀ x : ℝ, 5393 ≤ x → x / (Real.log x - 1) ≤ (⌊x⌋₊.primeCounting : ℝ)) ∧
  (∀ x : ℝ, 60184 ≤ x → (⌊x⌋₊.primeCounting : ℝ) ≤ x / (Real.log x - 11/10))


open Nat

private theorem prime_le_top {p k : ℕ} (hp : p.Prime) (hd : p ∣ k) (hk : k ≠ 0) :
    p ≤ (k.primeFactors.sup id) :=
  Finset.le_sup (f := id) (hp.mem_primeFactors hd hk)

private theorem product_good {k p : ℕ} (hk : (0 < k ∧ 2 * k.divisors.card ∣ k)) (hp : p.Prime)
    (hlt : (k.primeFactors.sup id) < p) : (k * p).IsRefactorable := by
  have hnd : ¬p ∣ k := fun h => hlt.not_ge (prime_le_top hp h hk.1.ne')
  have hc : k.Coprime p := hp.coprime_iff_not_dvd.mpr hnd |>.symm
  refine ⟨Nat.mul_pos hk.1 hp.pos, ?_⟩
  rw [Nat.Coprime.card_divisors_mul hc, hp.divisors]
  simpa [hp.ne_one, Ne.symm hp.ne_one, Nat.mul_comm] using dvd_mul_of_dvd_left hk.2 p

private theorem maxPrime_inj {k p l q : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hp : p.Prime) (hq : q.Prime) (hkp : (k.primeFactors.sup id) < p) (hlq : (l.primeFactors.sup id) < q)
    (h : k * p = l * q) : k = l ∧ p = q := by
  have step {u v r s : ℕ} (hu : 0 < u) (hr : r.Prime) (hs : s.Prime)
      (hus : (u.primeFactors.sup id) < s) (heq : v * r = u * s) : r ≤ s := by
    have hd : r ∣ u * s := heq ▸ dvd_mul_left r v
    rcases hr.dvd_mul.mp hd with hdu | hds
    · exact (prime_le_top hr hdu hu.ne').trans hus.le
    · exact Nat.le_of_dvd hs.pos hds
  have he := le_antisymm (step hl hp hq hlq h) (step hk hq hp hkp h.symm)
  subst q
  exact ⟨Nat.eq_of_mul_eq_mul_right hp.pos h, rfl⟩

/-- Count all refactorables up to the seed cutoff, then count the larger products.
The prime exceeding every prime divisor of its generator uniquely identifies the pair. -/
theorem seed_add_generated {B n : ℕ} (hBn : B ≤ n) (G : Finset ℕ)
    (hG : ∀ k ∈ G, (0 < k ∧ 2 * k.divisors.card ∣ k)) :
    countRefactorableNat B + (∑ k ∈ G, ((n/k).primeCounting - (max (k.primeFactors.sup id) (B/k)).primeCounting)) ≤ countRefactorableNat n := by
  classical
  let seed := (Icc 1 B).filter IsRefactorable
  let choices (k : ℕ) := primesLE (n / k) \ primesLE ((max (k.primeFactors.sup id) (B/k)))
  have specs {k p : ℕ} (hp : p ∈ choices k) :
      p.Prime ∧ (max (k.primeFactors.sup id) (B/k)) < p ∧ p ≤ n / k := by
    obtain ⟨hp₁, hp₂⟩ := mem_sdiff.mp hp
    obtain ⟨hp₃, hp₄⟩ := mem_primesLE.mp hp₁
    exact ⟨hp₄, lt_of_not_ge (fun h => hp₂ (mem_primesLE.mpr ⟨h, hp₄⟩)), hp₃⟩
  have hs (k : ℕ) : (n / k).primeCounting - ((max (k.primeFactors.sup id) (B/k))).primeCounting ≤ (choices k).card := by
    rw [← primesLE_card_eq_primeCounting, ← primesLE_card_eq_primeCounting,
      show (choices k).card = _ from Finset.card_sdiff ..]
    exact Nat.sub_le_sub_left (Finset.card_le_card Finset.inter_subset_left) _
  let products := G.sigma choices
  have hpgt {k p : ℕ} (hk : 0 < k) (hp : (max (k.primeFactors.sup id) (B/k)) < p) : B < k * p := by
    have h := (Nat.div_lt_iff_lt_mul hk).mp ((le_max_right _ _).trans_lt hp)
    simpa [Nat.mul_comm] using h
  let f : ℕ ⊕ (Σ _k : ℕ, ℕ) → ℕ := Sum.elim id (fun t => t.1 * t.2)
  calc
    _ ≤ seed.card + products.card := by
      dsimp only [products]
      rw [Finset.card_sigma]
      exact Nat.add_le_add_left (Finset.sum_le_sum (fun k _ => hs k)) _
    _ = (seed.disjSum products).card := (Finset.card_disjSum _ _).symm
    _ ≤ _ := by
      unfold countRefactorableNat
      apply Finset.card_le_card_of_injOn f
      · rintro (a | ⟨k, p⟩) h
        · have ha := Finset.mem_filter.mp (Finset.inl_mem_disjSum.mp h)
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp ha.1).1, (mem_Icc.mp ha.1).2.trans hBn⟩, ha.2⟩
        · obtain ⟨hk, hp⟩ := Finset.mem_sigma.mp (Finset.inr_mem_disjSum.mp h)
          obtain ⟨hpp, hpl, hpu⟩ := specs hp
          have hgen := hG k hk
          have hgood := product_good hgen hpp ((le_max_left _ _).trans_lt hpl)
          refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hgood.1, ?_⟩, hgood⟩
          change k * p ≤ n
          simpa only [Nat.mul_comm p k] using (Nat.le_div_iff_mul_le hgen.1).mp hpu
      · rintro (a | ⟨k, p⟩) ha (b | ⟨l, q⟩) hb heq
        · exact congrArg Sum.inl heq
        · have ha' := (mem_Icc.mp (mem_filter.mp (Finset.inl_mem_disjSum.mp ha)).1).2
          obtain ⟨hl, hq⟩ := Finset.mem_sigma.mp (Finset.inr_mem_disjSum.mp hb)
          have hgt : B < l * q := hpgt (hG l hl).1 (specs hq).2.1
          change a = l * q at heq
          omega
        · have hb' := (mem_Icc.mp (mem_filter.mp (Finset.inl_mem_disjSum.mp hb)).1).2
          obtain ⟨hk, hp⟩ := Finset.mem_sigma.mp (Finset.inr_mem_disjSum.mp ha)
          have hgt : B < k * p := hpgt (hG k hk).1 (specs hp).2.1
          change k * p = b at heq
          omega
        · obtain ⟨hk, hp⟩ := Finset.mem_sigma.mp (Finset.inr_mem_disjSum.mp ha)
          obtain ⟨hl, hq⟩ := Finset.mem_sigma.mp (Finset.inr_mem_disjSum.mp hb)
          obtain ⟨rfl, rfl⟩ := maxPrime_inj (hG k hk).1 (hG l hl).1 (specs hp).1 (specs hq).1
            ((le_max_left _ _).trans_lt (specs hp).2.1) ((le_max_left _ _).trans_lt (specs hq).2.1) heq
          rfl





private theorem row_refactorable (fs : List ℕ) (hp : ∀ p ∈ fs, p.Prime)
    (ht : fs.toFinset.prod (fun p => fs.count p + 1) ∣ fs.prod) :
    fs.prod.IsRefactorable := by
  have hn := List.prod_pos (s := fs) (fun p h => (hp p h).pos)
  have hperm := Nat.primeFactorsList_unique (n := fs.prod) rfl hp
  have hset : fs.toFinset = fs.prod.primeFactors := by
    rw [← Nat.toFinset_factors]
    ext p
    simp only [List.mem_toFinset]
    exact hperm.mem_iff
  refine ⟨hn, ?_⟩
  rw [Nat.card_divisors hn.ne', ← hset]
  convert ht using 1
  congr 1
  funext p
  rw [← Nat.primeFactorsList_count_eq, hperm.count_eq p]

private theorem seed_count_succ (n : ℕ) : countRefactorableNat (n+1) =
    countRefactorableNat n + if (n+1).IsRefactorable then 1 else 0 := by
  have he : Icc 1 (n+1) = insert (n+1) (Icc 1 n) := by ext i; simp; omega
  have hnot : n+1 ∉ (Icc 1 n).filter IsRefactorable := by simp
  by_cases h : (n+1).IsRefactorable <;> simp [countRefactorableNat, he, h, hnot, Finset.filter_insert]

/-- Each entry gives a proper divisor of a composite, or zero for a possible prime.
A factor list with the specified product certifies a contribution to the lower count. -/
private theorem seed_block (b p r e q t : ℕ) (rows : List (ℕ × List ℕ))
    (hb : b.primeCounting ≤ p ∧ r ≤ countRefactorableNat b ∧
      ∀ n ≤ b, n.primeCounting ≤ 2 * countRefactorableNat n)
    (cert : rows.foldr (fun row next n u v =>
      let m := n+1
      let d := row.1
      let fs := row.2
      let u' := u + if d = 0 then 1 else 0
      let v' := v + if fs.prod = m then 1 else 0
      decide (m = 1 ∨ d = 0 ∨ (1 < d ∧ d < m ∧ d ∣ m)) &&
        (if fs.prod = m then fs.all (fun a => decide a.Prime) &&
          decide (fs.toFinset.prod (fun a => fs.count a + 1) ∣ m) else true) &&
        decide (u' ≤ 2*v') && next m u' v')
      (fun n u v => decide (n = e ∧ u = q ∧ v = t)) b p r = true) :
    e.primeCounting ≤ q ∧ t ≤ countRefactorableNat e ∧
      ∀ n ≤ e, n.primeCounting ≤ 2 * countRefactorableNat n := by
  induction rows generalizing b p r with
  | nil =>
    simp only [List.foldr_nil, decide_eq_true_eq] at cert
    obtain ⟨rfl,rfl,rfl⟩ := cert
    exact hb
  | cons row rows ih =>
    rcases row with ⟨d,fs⟩
    simp only [List.foldr_cons, Bool.and_eq_true, decide_eq_true_eq] at cert
    obtain ⟨⟨⟨hd,hfs⟩,hgap⟩,hnext⟩ := cert
    apply ih _ _ _ _ hnext
    have hπ : (b+1).primeCounting ≤ p + if d = 0 then 1 else 0 := by
      have he : (b+1).primeCounting = b.primeCounting + if (b+1).Prime then 1 else 0 :=
        Nat.count_succ _ _
      rw [he]
      apply Nat.add_le_add hb.1
      by_cases hpr : (b+1).Prime
      · have hz : d = 0 := by
          rcases hd with hone | hz | ⟨hd₂,hdm,hdvd⟩
          · have := hpr.two_le
            omega
          · exact hz
          · rcases hpr.eq_one_or_self_of_dvd d hdvd with he | he <;> omega
        simp [hpr,hz]
      · simp [hpr]
    have hT : r + (if fs.prod = b+1 then 1 else 0) ≤ countRefactorableNat (b+1) := by
      rw [seed_count_succ]
      apply Nat.add_le_add hb.2.1
      by_cases he : fs.prod = b+1
      · simp only [if_pos he, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hfs
        have hgood := row_refactorable fs hfs.1 (he ▸ hfs.2)
        simp [he, he ▸ hgood]
      · simp [he]
    refine ⟨hπ,hT,?_⟩
    intro n hn
    by_cases h : n ≤ b
    · exact hb.2.2 n h
    · have : n = b+1 := by omega
      subst n
      exact (hπ.trans hgap).trans (Nat.mul_le_mul_left _ hT)


private theorem seed_0 : (0 : ℕ).primeCounting ≤ 0 ∧ 0 ≤ countRefactorableNat 0 ∧
    ∀ n ≤ 0, n.primeCounting ≤ 2 * countRefactorableNat n := by
  simp [countRefactorableNat, Nat.primeCounting, Nat.primeCounting', Nat.count_one, Nat.not_prime_zero]

private theorem seed_32 : (32 : ℕ).primeCounting ≤ 11 ∧ 7 ≤ countRefactorableNat 32 ∧
    ∀ n ≤ 32, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 0 0 0 _ _ _ [
    (1,[]), (0,[2]), (0,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2]),
    (3,[3,3]), (2,[]), (0,[]), (2,[2,2,3]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[2,3,3]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[])] seed_0
  decide +kernel

private theorem seed_64 : (64 : ℕ).primeCounting ≤ 18 ∧ 11 ≤ countRefactorableNat 64 ∧
    ∀ n ≤ 64, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 32 11 7 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,5]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[2,2,2,7]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,5]), (0,[]), (2,[]), (3,[]), (2,[])] seed_32
  decide +kernel

private theorem seed_96 : (96 : ℕ).primeCounting ≤ 24 ∧ 16 ≤ countRefactorableNat 96 ∧
    ∀ n ≤ 96, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 64 18 11 _ _ _ [
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3]),
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[2,2,2,2,5]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,7]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,11]),
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,2,2,3])] seed_64
  decide +kernel

private theorem seed_128 : (128 : ℕ).primeCounting ≤ 31 ∧ 19 ≤ countRefactorableNat 128 ∧
    ∀ n ≤ 128, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 96 24 16 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,13]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,3]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (11,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,2,2])] seed_96
  decide +kernel

private theorem seed_160 : (160 : ℕ).primeCounting ≤ 37 ∧ 23 ≤ countRefactorableNat 160 ∧
    ∀ n ≤ 160, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 128 31 19 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,11]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,17]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,19]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,13]), (0,[]), (2,[]), (3,[]), (2,[])] seed_128
  decide +kernel

private theorem seed_192 : (192 : ℕ).primeCounting ≤ 43 ∧ 25 ≤ countRefactorableNat 192 ∧
    ∀ n ≤ 192, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 160 37 23 _ _ _ [
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (13,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,5]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,23]),
    (5,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[])] seed_160
  decide +kernel

private theorem seed_224 : (224 : ℕ).primeCounting ≤ 48 ∧ 26 ≤ countRefactorableNat 224 ∧
    ∀ n ≤ 224, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 192 43 25 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,17]), (5,[]), (2,[]), (3,[]), (2,[]),
    (11,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (0,[]), (2,[])] seed_192
  decide +kernel

private theorem seed_256 : (256 : ℕ).primeCounting ≤ 54 ∧ 32 ≤ countRefactorableNat 256 ∧
    ∀ n ≤ 256, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 224 48 26 _ _ _ [
    (3,[3,3,5,5]), (2,[]), (0,[]), (2,[2,2,3,19]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,29]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,3,5]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (13,[]), (2,[2,2,2,31]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,7]), (11,[]), (2,[]), (3,[]), (2,[])] seed_224
  decide +kernel

private theorem seed_288 : (288 : ℕ).primeCounting ≤ 61 ∧ 34 ≤ countRefactorableNat 288 ∧
    ∀ n ≤ 288, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 256 54 32 _ _ _ [
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,23]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[2,2,2,2,2,3,3])] seed_256
  decide +kernel

private theorem seed_320 : (320 : ℕ).primeCounting ≤ 66 ∧ 35 ≤ countRefactorableNat 320 ∧
    ∀ n ≤ 320, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 288 61 34 _ _ _ [
    (17,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[2,2,2,37]),
    (3,[]), (2,[]), (13,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[])] seed_288
  decide +kernel

private theorem seed_352 : (352 : ℕ).primeCounting ≤ 70 ∧ 38 ≤ countRefactorableNat 352 ∧
    ∀ n ≤ 352, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 320 66 35 _ _ _ [
    (3,[]), (2,[]), (17,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,41]),
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (7,[]), (2,[2,2,2,43]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,29]), (0,[]), (2,[]), (3,[]), (2,[])] seed_320
  decide +kernel

private theorem seed_384 : (384 : ℕ).primeCounting ≤ 76 ∧ 42 ≤ countRefactorableNat 384 ∧
    ∀ n ≤ 384, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 352 70 38 _ _ _ [
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3,5]),
    (19,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,31]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,47]),
    (13,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,2,2,3])] seed_352
  decide +kernel

private theorem seed_416 : (416 : ℕ).primeCounting ≤ 80 ∧ 43 ≤ countRefactorableNat 416 ∧
    ∀ n ≤ 416, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 384 76 42 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (17,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3,11]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (5,[]), (2,[])] seed_384
  decide +kernel

private theorem seed_448 : (448 : ℕ).primeCounting ≤ 86 ∧ 47 ≤ countRefactorableNat 448 ∧
    ∀ n ≤ 448, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 416 80 43 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,53]),
    (5,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]), (0,[]), (2,[]),
    (3,[3,3,7,7]), (2,[]), (0,[]), (2,[2,2,3,37]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,2,2,2,7])] seed_416
  decide +kernel

private theorem seed_480 : (480 : ℕ).primeCounting ≤ 92 ∧ 51 ≤ countRefactorableNat 480 ∧
    ∀ n ≤ 480, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 448 86 47 _ _ _ [
    (0,[]), (2,[2,3,3,5,5]), (11,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,13]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,59]),
    (11,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,3,5])] seed_448
  decide +kernel

private theorem seed_512 : (512 : ℕ).primeCounting ≤ 97 ∧ 54 ≤ countRefactorableNat 512 ∧
    ∀ n ≤ 512, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 480 92 51 _ _ _ [
    (13,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[2,2,2,61]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,41]), (17,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3,7]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[])] seed_480
  decide +kernel

private theorem seed_544 : (544 : ℕ).primeCounting ≤ 100 ∧ 56 ≤ countRefactorableNat 544 ∧
    ∀ n ≤ 544, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 512 97 54 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,43]), (11,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]),
    (23,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (5,[]), (2,[2,2,2,67]),
    (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[])] seed_512
  decide +kernel

private theorem seed_576 : (576 : ℕ).primeCounting ≤ 105 ∧ 59 ≤ countRefactorableNat 576 ∧
    ∀ n ≤ 576, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 544 100 56 _ _ _ [
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (13,[]), (2,[2,2,2,2,5,7]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,47]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,71]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[])] seed_544
  decide +kernel

private theorem seed_608 : (608 : ℕ).primeCounting ≤ 111 ∧ 61 ≤ countRefactorableNat 608 ∧
    ∀ n ≤ 608, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 576 105 59 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (11,[]), (2,[2,2,2,73]),
    (3,[]), (2,[]), (0,[]), (2,[]), (19,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,5,5]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[])] seed_576
  decide +kernel

private theorem seed_640 : (640 : ℕ).primeCounting ≤ 115 ∧ 66 ≤ countRefactorableNat 640 ∧
    ∀ n ≤ 640, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 608 111 61 _ _ _ [
    (3,[]), (2,[]), (13,[]), (2,[2,2,3,3,17]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (5,[5,5,5,5]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]), (0,[]), (2,[2,2,2,79]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,53]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,2,2,2,2,5])] seed_608
  decide +kernel

private theorem seed_672 : (672 : ℕ).primeCounting ≤ 121 ∧ 68 ≤ countRefactorableNat 672 ∧
    ∀ n ≤ 672, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 640 115 66 _ _ _ [
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,83]),
    (5,[]), (2,[]), (23,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[2,2,2,2,2,3,7])] seed_640
  decide +kernel

private theorem seed_704 : (704 : ℕ).primeCounting ≤ 126 ∧ 69 ≤ countRefactorableNat 704 ∧
    ∀ n ≤ 704, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 672 121 68 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,19]), (5,[]), (2,[]), (3,[]), (2,[]),
    (13,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (17,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (19,[]), (2,[])] seed_672
  decide +kernel

private theorem seed_736 : (736 : ℕ).primeCounting ≤ 130 ∧ 73 ≤ countRefactorableNat 736 ∧
    ∀ n ≤ 736, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 704 126 69 _ _ _ [
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,59]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,89]),
    (23,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,3,3,5]),
    (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (17,[]), (2,[2,2,3,61]), (0,[]), (2,[]), (3,[]), (2,[])] seed_704
  decide +kernel

private theorem seed_768 : (768 : ℕ).primeCounting ≤ 135 ∧ 73 ≤ countRefactorableNat 768 ∧
    ∀ n ≤ 768, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 736 130 73 _ _ _ [
    (11,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[])] seed_736
  decide +kernel

private theorem seed_800 : (800 : ℕ).primeCounting ≤ 139 ∧ 75 ≤ countRefactorableNat 800 ∧
    ∀ n ≤ 800, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 768 135 73 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[2,2,2,97]),
    (3,[]), (2,[]), (19,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[2,2,2,3,3,11]),
    (13,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (17,[]), (2,[])] seed_768
  decide +kernel

private theorem seed_832 : (832 : ℕ).primeCounting ≤ 145 ∧ 79 ≤ countRefactorableNat 832 ∧
    ∀ n ≤ 832, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 800 139 75 _ _ _ [
    (3,[]), (2,[]), (11,[]), (2,[2,2,3,67]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,101]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (19,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,103]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,23]), (0,[]), (2,[]), (3,[]), (2,[])] seed_800
  decide +kernel

private theorem seed_864 : (864 : ℕ).primeCounting ≤ 150 ∧ 82 ≤ countRefactorableNat 864 ∧
    ∀ n ≤ 864, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 832 145 79 _ _ _ [
    (7,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (29,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (7,[]), (2,[]),
    (3,[]), (2,[]), (23,[]), (2,[2,2,3,71]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,107]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,3,3,3])] seed_832
  decide +kernel

private theorem seed_896 : (896 : ℕ).primeCounting ≤ 154 ∧ 87 ≤ countRefactorableNat 896 ∧
    ∀ n ≤ 896, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 864 150 82 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (13,[]), (2,[2,2,2,109]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,73]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,2,5,11]),
    (0,[]), (2,[2,3,3,7,7]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]), (5,[]), (2,[2,2,2,2,2,2,2,7])] seed_864
  decide +kernel

private theorem seed_928 : (928 : ℕ).primeCounting ≤ 157 ∧ 88 ≤ countRefactorableNat 928 ∧
    ∀ n ≤ 928, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 896 154 87 _ _ _ [
    (3,[]), (2,[]), (29,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[2,2,2,113]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (11,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (13,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[])] seed_896
  decide +kernel

private theorem seed_960 : (960 : ℕ).primeCounting ≤ 162 ∧ 90 ≤ countRefactorableNat 960 ∧
    ∀ n ≤ 960, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 928 157 88 _ _ _ [
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,3,3,13]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (23,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,79]), (13,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[])] seed_928
  decide +kernel

private theorem seed_992 : (992 : ℕ).primeCounting ≤ 167 ∧ 91 ≤ countRefactorableNat 992 ∧
    ∀ n ≤ 992, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 960 162 90 _ _ _ [
    (31,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,3,3,3]), (7,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (23,[]), (2,[]), (0,[]), (2,[])] seed_960
  decide +kernel

private theorem seed_1024 : (1024 : ℕ).primeCounting ≤ 172 ∧ 93 ≤ countRefactorableNat 1024 ∧
    ∀ n ≤ 1024, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 992 167 91 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,83]), (0,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[2,2,2,127]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[])] seed_992
  decide +kernel

private theorem seed_1056 : (1056 : ℕ).primeCounting ≤ 177 ∧ 97 ≤ countRefactorableNat 1056 ∧
    ∀ n ≤ 1056, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1024 172 93 _ _ _ [
    (5,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]), (0,[]), (2,[2,2,2,2,5,13]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,3,29]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,131]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,2,2,3,11])] seed_1024
  decide +kernel

private theorem seed_1088 : (1088 : ℕ).primeCounting ≤ 181 ∧ 98 ≤ countRefactorableNat 1088 ∧
    ∀ n ≤ 1088, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1056 177 97 _ _ _ [
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (11,[]), (2,[2,2,3,89]), (0,[]), (2,[]), (3,[]), (2,[]),
    (29,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]),
    (23,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[])] seed_1056
  decide +kernel

private theorem seed_1120 : (1120 : ℕ).primeCounting ≤ 187 ∧ 102 ≤ countRefactorableNat 1120 ∧
    ∀ n ≤ 1120, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1088 181 98 _ _ _ [
    (3,[3,3,11,11]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,137]),
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[2,2,2,139]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3,31]), (0,[]), (2,[]), (3,[]), (2,[])] seed_1088
  decide +kernel

private theorem seed_1152 : (1152 : ℕ).primeCounting ≤ 190 ∧ 103 ≤ countRefactorableNat 1152 ∧
    ∀ n ≤ 1152, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1120 187 102 _ _ _ [
    (19,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (17,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (31,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,2,2,3,3])] seed_1120
  decide +kernel

private theorem seed_1184 : (1184 : ℕ).primeCounting ≤ 194 ∧ 105 ≤ countRefactorableNat 1184 ∧
    ∀ n ≤ 1184, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1152 190 103 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (19,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,97]), (5,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,3,7,7]),
    (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[])] seed_1152
  decide +kernel

private theorem seed_1216 : (1216 : ℕ).primeCounting ≤ 198 ∧ 109 ≤ countRefactorableNat 1216 ∧
    ∀ n ≤ 1216, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1184 194 105 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[]), (29,[]), (2,[]), (3,[]), (2,[2,2,2,149]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[2,2,2,2,3,5,5]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (17,[]), (2,[2,2,2,151]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,101]), (0,[]), (2,[]), (3,[]), (2,[])] seed_1184
  decide +kernel

private theorem seed_1248 : (1248 : ℕ).primeCounting ≤ 203 ∧ 112 ≤ countRefactorableNat 1248 ∧
    ∀ n ≤ 1248, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1216 198 109 _ _ _ [
    (0,[]), (2,[]), (23,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3,17]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,103]), (0,[]), (2,[]), (3,[]), (2,[]),
    (17,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (29,[]), (2,[2,2,2,2,2,3,13])] seed_1216
  decide +kernel

private theorem seed_1280 : (1280 : ℕ).primeCounting ≤ 207 ∧ 115 ≤ countRefactorableNat 1280 ∧
    ∀ n ≤ 1280, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1248 203 112 _ _ _ [
    (0,[]), (2,[2,5,5,5,5]), (3,[]), (2,[]), (7,[]), (2,[]), (5,[]), (2,[2,2,2,157]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,5,7]), (13,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (31,[]), (2,[]),
    (19,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[])] seed_1248
  decide +kernel

private theorem seed_1312 : (1312 : ℕ).primeCounting ≤ 214 ∧ 118 ≤ countRefactorableNat 1312 ∧
    ∀ n ≤ 1312, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1280 207 115 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,107]), (5,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,163]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,109]), (7,[]), (2,[]), (3,[]), (2,[])] seed_1280
  decide +kernel

private theorem seed_1344 : (1344 : ℕ).primeCounting ≤ 217 ∧ 121 ≤ countRefactorableNat 1344 ∧
    ∀ n ≤ 1344, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1312 214 118 _ _ _ [
    (13,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (11,[]), (2,[2,2,3,3,37]), (31,[]), (2,[]), (3,[]), (2,[2,2,2,167]),
    (7,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[2,2,2,2,2,2,3,7])] seed_1312
  decide +kernel

private theorem seed_1376 : (1376 : ℕ).primeCounting ≤ 220 ∧ 124 ≤ countRefactorableNat 1376 ∧
    ∀ n ≤ 1376, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1344 217 121 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]), (7,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,113]), (23,[]), (2,[]), (3,[]), (2,[2,2,2,2,5,17]),
    (0,[]), (2,[]), (29,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3,19]),
    (37,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[])] seed_1344
  decide +kernel

private theorem seed_1408 : (1408 : ℕ).primeCounting ≤ 222 ∧ 126 ≤ countRefactorableNat 1408 ∧
    ∀ n ≤ 1408, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1376 220 124 _ _ _ [
    (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,173]),
    (5,[]), (2,[]), (19,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (23,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,2,2,2,2,11])] seed_1376
  decide +kernel

private theorem seed_1440 : (1440 : ℕ).primeCounting ≤ 228 ∧ 128 ≤ countRefactorableNat 1440 ∧
    ∀ n ≤ 1440, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1408 222 126 _ _ _ [
    (0,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (13,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,179]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,3,3,5])] seed_1408
  decide +kernel

private theorem seed_1472 : (1472 : ℕ).primeCounting ≤ 233 ∧ 129 ≤ countRefactorableNat 1472 ∧
    ∀ n ≤ 1472, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1440 228 128 _ _ _ [
    (11,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[2,2,2,181]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (31,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (0,[]), (2,[])] seed_1440
  decide +kernel

private theorem seed_1504 : (1504 : ℕ).primeCounting ≤ 239 ∧ 130 ≤ countRefactorableNat 1504 ∧
    ∀ n ≤ 1504, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1472 233 129 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3,41]), (7,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (19,[]), (2,[]), (3,[]), (2,[])] seed_1472
  decide +kernel

private theorem seed_1536 : (1536 : ℕ).primeCounting ≤ 242 ∧ 134 ≤ countRefactorableNat 1536 ∧
    ∀ n ≤ 1536, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1504 239 130 _ _ _ [
    (5,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (17,[]), (2,[]), (3,[]), (2,[]), (37,[]), (2,[]), (7,[]), (2,[2,2,2,2,5,19]),
    (3,[3,3,13,13]), (2,[]), (0,[]), (2,[2,2,3,127]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,191]),
    (11,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[])] seed_1504
  decide +kernel

private theorem seed_1568 : (1568 : ℕ).primeCounting ≤ 247 ∧ 136 ≤ countRefactorableNat 1568 ∧
    ∀ n ≤ 1568, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1536 242 134 _ _ _ [
    (29,[]), (2,[]), (3,[]), (2,[]), (23,[]), (2,[]), (0,[]), (2,[2,2,2,193]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,3,43]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[])] seed_1536
  decide +kernel

private theorem seed_1600 : (1600 : ℕ).primeCounting ≤ 251 ∧ 139 ≤ countRefactorableNat 1600 ∧
    ∀ n ≤ 1600, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1568 247 136 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,131]), (11,[]), (2,[]), (3,[]), (2,[2,2,2,197]),
    (19,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (37,[]), (2,[2,2,2,199]),
    (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[])] seed_1568
  decide +kernel

private theorem seed_1632 : (1632 : ℕ).primeCounting ≤ 258 ∧ 141 ≤ countRefactorableNat 1632 ∧
    ∀ n ≤ 1632, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1600 251 139 _ _ _ [
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,3,3,5]), (0,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[2,2,2,2,2,3,17])] seed_1600
  decide +kernel

private theorem seed_1664 : (1664 : ℕ).primeCounting ≤ 261 ∧ 144 ≤ countRefactorableNat 1664 ∧
    ∀ n ≤ 1664, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1632 258 141 _ _ _ [
    (23,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[]),
    (3,[]), (2,[]), (31,[]), (2,[2,2,3,137]), (5,[]), (2,[]), (3,[]), (2,[]),
    (17,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,3,3,23]),
    (0,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,2,2,13])] seed_1632
  decide +kernel

private theorem seed_1696 : (1696 : ℕ).primeCounting ≤ 264 ∧ 148 ≤ countRefactorableNat 1696 ∧
    ∀ n ≤ 1696, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1664 261 144 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,139]), (0,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (23,[]), (2,[2,2,2,2,3,5,7]),
    (41,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (7,[]), (2,[2,2,2,211]),
    (3,[]), (2,[]), (19,[]), (2,[2,2,3,3,47]), (0,[]), (2,[]), (3,[]), (2,[])] seed_1664
  decide +kernel

private theorem seed_1728 : (1728 : ℕ).primeCounting ≤ 269 ∧ 148 ≤ countRefactorableNat 1728 ∧
    ∀ n ≤ 1728, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1696 264 148 _ _ _ [
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (29,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[])] seed_1696
  decide +kernel

private theorem seed_1760 : (1760 : ℕ).primeCounting ≤ 274 ∧ 148 ≤ countRefactorableNat 1760 ∧
    ∀ n ≤ 1760, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1728 269 148 _ _ _ [
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (37,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[])] seed_1728
  decide +kernel

private theorem seed_1792 : (1792 : ℕ).primeCounting ≤ 278 ∧ 150 ≤ countRefactorableNat 1792 ∧
    ∀ n ≤ 1792, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1760 274 148 _ _ _ [
    (3,[]), (2,[]), (41,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]),
    (29,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (0,[]), (2,[2,2,2,223]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,149]), (0,[]), (2,[]), (3,[]), (2,[])] seed_1760
  decide +kernel

private theorem seed_1824 : (1824 : ℕ).primeCounting ≤ 281 ∧ 154 ≤ countRefactorableNat 1824 ∧
    ∀ n ≤ 1824, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1792 278 150 _ _ _ [
    (11,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[2,2,2,3,3,5,5]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (13,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,151]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,227]),
    (23,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,3,19])] seed_1792
  decide +kernel

private theorem seed_1856 : (1856 : ℕ).primeCounting ≤ 283 ∧ 156 ≤ countRefactorableNat 1856 ∧
    ∀ n ≤ 1856, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1824 281 154 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (31,[]), (2,[]), (0,[]), (2,[2,2,2,229]),
    (3,[]), (2,[]), (5,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[2,2,2,2,5,23]),
    (7,[]), (2,[]), (19,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (43,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]), (5,[]), (2,[])] seed_1824
  decide +kernel

private theorem seed_1888 : (1888 : ℕ).primeCounting ≤ 289 ∧ 158 ≤ countRefactorableNat 1888 ∧
    ∀ n ≤ 1888, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1856 283 156 _ _ _ [
    (3,[]), (2,[]), (11,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,233]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,157]), (5,[]), (2,[]), (3,[]), (2,[])] seed_1856
  decide +kernel

private theorem seed_1920 : (1920 : ℕ).primeCounting ≤ 293 ∧ 161 ≤ countRefactorableNat 1920 ∧
    ∀ n ≤ 1920, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1888 289 158 _ _ _ [
    (0,[]), (2,[]), (31,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,53]), (23,[]), (2,[]), (3,[]), (2,[2,2,2,239]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[2,2,2,2,2,2,2,3,5])] seed_1888
  decide +kernel

private theorem seed_1952 : (1952 : ℕ).primeCounting ≤ 297 ∧ 163 ≤ countRefactorableNat 1952 ∧
    ∀ n ≤ 1952, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1920 293 161 _ _ _ [
    (17,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (41,[]), (2,[2,2,2,241]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (13,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (29,[]), (2,[2,2,2,3,3,3,3,3]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[])] seed_1920
  decide +kernel

private theorem seed_1984 : (1984 : ℕ).primeCounting ≤ 299 ∧ 165 ≤ countRefactorableNat 1984 ∧
    ∀ n ≤ 1984, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1952 297 163 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,163]), (19,[]), (2,[]), (3,[]), (2,[]),
    (37,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,5,11]), (7,[]), (2,[]), (3,[]), (2,[])] seed_1952
  decide +kernel

private theorem seed_2016 : (2016 : ℕ).primeCounting ≤ 305 ∧ 169 ≤ countRefactorableNat 2016 ∧
    ∀ n ≤ 2016, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 1984 299 165 _ _ _ [
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,2,5,5,5]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,167]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,251]),
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,2,2,3,3,7])] seed_1984
  decide +kernel

private theorem seed_2048 : (2048 : ℕ).primeCounting ≤ 309 ∧ 170 ≤ countRefactorableNat 2048 ∧
    ∀ n ≤ 2048, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2016 305 169 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (43,[]), (2,[]), (7,[]), (2,[]),
    (3,[3,3,3,3,5,5]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (19,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (13,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (23,[]), (2,[])] seed_2016
  decide +kernel

private theorem seed_2080 : (2080 : ℕ).primeCounting ≤ 312 ∧ 172 ≤ countRefactorableNat 2080 ∧
    ∀ n ≤ 2080, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2048 309 170 _ _ _ [
    (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,257]),
    (11,[]), (2,[]), (29,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (19,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,173]), (31,[]), (2,[]), (3,[]), (2,[])] seed_2048
  decide +kernel

private theorem seed_2112 : (2112 : ℕ).primeCounting ≤ 318 ∧ 174 ≤ countRefactorableNat 2112 ∧
    ∀ n ≤ 2112, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2080 312 172 _ _ _ [
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3,29]),
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[2,2,2,263]),
    (5,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[])] seed_2080
  decide +kernel

private theorem seed_2144 : (2144 : ℕ).primeCounting ≤ 324 ∧ 175 ≤ countRefactorableNat 2144 ∧
    ∀ n ≤ 2144, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2112 318 174 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (29,[]), (2,[]), (13,[]), (2,[]),
    (3,[]), (2,[]), (11,[]), (2,[2,2,3,3,59]), (5,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[])] seed_2112
  decide +kernel

private theorem seed_2176 : (2176 : ℕ).primeCounting ≤ 326 ∧ 181 ≤ countRefactorableNat 2176 ∧
    ∀ n ≤ 2176, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2144 324 175 _ _ _ [
    (3,[]), (2,[]), (19,[]), (2,[2,2,3,179]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,269]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[2,2,2,2,3,3,3,5]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (11,[]), (2,[2,2,2,271]),
    (3,[]), (2,[]), (13,[]), (2,[2,2,3,181]), (41,[]), (2,[]), (3,[]), (2,[2,2,2,2,2,2,2,17])] seed_2144
  decide +kernel

private theorem seed_2208 : (2208 : ℕ).primeCounting ≤ 329 ∧ 184 ≤ countRefactorableNat 2208 ∧
    ∀ n ≤ 2208, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2176 326 181 _ _ _ [
    (7,[]), (2,[2,3,3,11,11]), (0,[]), (2,[]), (3,[]), (2,[]), (37,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (7,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3,61]), (13,[]), (2,[]), (3,[]), (2,[]),
    (31,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,3,23])] seed_2176
  decide +kernel

private theorem seed_2240 : (2240 : ℕ).primeCounting ≤ 333 ∧ 187 ≤ countRefactorableNat 2240 ∧
    ∀ n ≤ 2240, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2208 329 184 _ _ _ [
    (47,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[2,2,2,277]),
    (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[]), (23,[]), (2,[2,2,2,3,3,31]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,2,5,7])] seed_2208
  decide +kernel

private theorem seed_2272 : (2272 : ℕ).primeCounting ≤ 337 ∧ 189 ≤ countRefactorableNat 2272 ∧
    ∀ n ≤ 2272, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2240 333 187 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,281]),
    (13,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (37,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (31,[]), (2,[2,2,2,283]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[])] seed_2240
  decide +kernel

private theorem seed_2304 : (2304 : ℕ).primeCounting ≤ 342 ∧ 190 ≤ countRefactorableNat 2304 ∧
    ∀ n ≤ 2304, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2272 337 189 _ _ _ [
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (43,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (29,[]), (2,[2,2,3,191]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[])] seed_2272
  decide +kernel

private theorem seed_2336 : (2336 : ℕ).primeCounting ≤ 345 ∧ 192 ≤ countRefactorableNat 2336 ∧
    ∀ n ≤ 2336, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2304 342 190 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,193]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,2,5,29]),
    (11,[]), (2,[]), (23,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]),
    (17,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[])] seed_2304
  decide +kernel

private theorem seed_2368 : (2368 : ℕ).primeCounting ≤ 350 ∧ 195 ≤ countRefactorableNat 2368 ∧
    ∀ n ≤ 2368, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2336 345 192 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,5,13]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,293]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (13,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[]),
    (3,[]), (2,[]), (17,[]), (2,[2,2,3,197]), (5,[]), (2,[]), (3,[]), (2,[])] seed_2336
  decide +kernel

private theorem seed_2400 : (2400 : ℕ).primeCounting ≤ 357 ∧ 196 ≤ countRefactorableNat 2400 ∧
    ∀ n ≤ 2400, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2368 350 195 _ _ _ [
    (23,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,199]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[])] seed_2368
  decide +kernel

private theorem seed_2432 : (2432 : ℕ).primeCounting ≤ 360 ∧ 198 ≤ countRefactorableNat 2432 ∧
    ∀ n ≤ 2432, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2400 357 196 _ _ _ [
    (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (29,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,67]), (19,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (41,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (11,[]), (2,[2,2,2,2,2,2,2,19])] seed_2400
  decide +kernel

private theorem seed_2464 : (2464 : ℕ).primeCounting ≤ 364 ∧ 199 ≤ countRefactorableNat 2464 ∧
    ∀ n ≤ 2464, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2432 360 198 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (31,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (5,[]), (2,[2,2,2,307]),
    (3,[]), (2,[]), (0,[]), (2,[]), (23,[]), (2,[]), (3,[]), (2,[])] seed_2432
  decide +kernel

private theorem seed_2496 : (2496 : ℕ).primeCounting ≤ 367 ∧ 201 ≤ countRefactorableNat 2496 ∧
    ∀ n ≤ 2496, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2464 364 199 _ _ _ [
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (37,[]), (2,[2,2,2,2,5,31]),
    (3,[]), (2,[]), (13,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,311]),
    (19,[]), (2,[]), (47,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[])] seed_2464
  decide +kernel

private theorem seed_2528 : (2528 : ℕ).primeCounting ≤ 369 ∧ 202 ≤ countRefactorableNat 2528 ∧
    ∀ n ≤ 2528, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2496 367 201 _ _ _ [
    (11,[]), (2,[]), (3,[]), (2,[]), (41,[]), (2,[]), (0,[]), (2,[2,2,2,313]),
    (3,[]), (2,[]), (23,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (7,[]), (2,[])] seed_2496
  decide +kernel

private theorem seed_2560 : (2560 : ℕ).primeCounting ≤ 375 ∧ 206 ≤ countRefactorableNat 2560 ∧
    ∀ n ≤ 2560, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2528 369 202 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,211]), (17,[]), (2,[]), (3,[]), (2,[2,2,2,317]),
    (43,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3,71]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,2,2,2,2,2,2,5])] seed_2528
  decide +kernel

private theorem seed_2592 : (2592 : ℕ).primeCounting ≤ 377 ∧ 206 ≤ countRefactorableNat 2592 ∧
    ∀ n ≤ 2592, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2560 375 206 _ _ _ [
    (13,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (31,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (29,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[])] seed_2560
  decide +kernel

private theorem seed_2624 : (2624 : ℕ).primeCounting ≤ 381 ∧ 207 ≤ countRefactorableNat 2624 ∧
    ∀ n ≤ 2624, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2592 377 206 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (23,[]), (2,[]),
    (3,[3,3,17,17]), (2,[]), (19,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (43,[]), (2,[])] seed_2592
  decide +kernel

private theorem seed_2656 : (2656 : ℕ).primeCounting ≤ 383 ∧ 210 ≤ countRefactorableNat 2656 ∧
    ∀ n ≤ 2656, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2624 381 207 _ _ _ [
    (3,[]), (2,[]), (37,[]), (2,[2,2,3,3,73]), (11,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[2,2,2,2,3,5,11]),
    (19,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[2,2,2,331]),
    (3,[]), (2,[]), (11,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[])] seed_2624
  decide +kernel

private theorem seed_2688 : (2688 : ℕ).primeCounting ≤ 390 ∧ 213 ≤ countRefactorableNat 2688 ∧
    ∀ n ≤ 2688, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2656 383 210 _ _ _ [
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3,37]),
    (5,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,223]), (0,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,2,2,3,7])] seed_2656
  decide +kernel

private theorem seed_2720 : (2720 : ℕ).primeCounting ≤ 397 ∧ 215 ≤ countRefactorableNat 2720 ∧
    ∀ n ≤ 2720, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2688 390 213 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[2,2,2,337]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,3,5,5]), (37,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (0,[]), (2,[])] seed_2688
  decide +kernel

private theorem seed_2752 : (2752 : ℕ).primeCounting ≤ 401 ∧ 217 ≤ countRefactorableNat 2752 ∧
    ∀ n ≤ 2752, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2720 397 215 _ _ _ [
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,227]), (5,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (13,[]), (2,[]),
    (3,[]), (2,[]), (41,[]), (2,[2,2,3,229]), (0,[]), (2,[]), (3,[]), (2,[])] seed_2720
  decide +kernel

private theorem seed_2784 : (2784 : ℕ).primeCounting ≤ 404 ∧ 220 ≤ countRefactorableNat 2784 ∧
    ∀ n ≤ 2784, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2752 401 217 _ _ _ [
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (31,[]), (2,[]),
    (11,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (17,[]), (2,[2,2,3,3,7,11]), (47,[]), (2,[]), (3,[]), (2,[2,2,2,347]),
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[2,2,2,2,2,3,29])] seed_2752
  decide +kernel

private theorem seed_2816 : (2816 : ℕ).primeCounting ≤ 409 ∧ 222 ≤ countRefactorableNat 2816 ∧
    ∀ n ≤ 2816, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2784 404 220 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,349]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,233]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (53,[]), (2,[]), (3,[]), (2,[]), (29,[]), (2,[]), (5,[]), (2,[])] seed_2784
  decide +kernel

private theorem seed_2848 : (2848 : ℕ).primeCounting ≤ 413 ∧ 224 ≤ countRefactorableNat 2848 ∧
    ∀ n ≤ 2848, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2816 409 222 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,353]),
    (5,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (17,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,79]), (5,[]), (2,[]), (3,[]), (2,[])] seed_2816
  decide +kernel

private theorem seed_2880 : (2880 : ℕ).primeCounting ≤ 417 ∧ 226 ≤ countRefactorableNat 2880 ∧
    ∀ n ≤ 2880, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2848 413 224 _ _ _ [
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[]),
    (3,[]), (2,[]), (47,[]), (2,[2,2,3,239]), (19,[]), (2,[]), (3,[]), (2,[2,2,2,359]),
    (13,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[])] seed_2848
  decide +kernel

private theorem seed_2912 : (2912 : ℕ).primeCounting ≤ 421 ∧ 228 ≤ countRefactorableNat 2912 ∧
    ∀ n ≤ 2912, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2880 417 226 _ _ _ [
    (43,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,241]), (11,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,11,11]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (41,[]), (2,[])] seed_2880
  decide +kernel

private theorem seed_2944 : (2944 : ℕ).primeCounting ≤ 424 ∧ 230 ≤ countRefactorableNat 2944 ∧
    ∀ n ≤ 2944, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2912 421 228 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (23,[]), (2,[]), (37,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (29,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (5,[]), (2,[2,2,2,367]),
    (3,[]), (2,[]), (0,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[2,2,2,2,2,2,2,23])] seed_2912
  decide +kernel

private theorem seed_2976 : (2976 : ℕ).primeCounting ≤ 429 ∧ 233 ≤ countRefactorableNat 2976 ∧
    ∀ n ≤ 2976, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2944 424 230 _ _ _ [
    (5,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[2,2,2,3,3,41]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[2,2,2,2,5,37]),
    (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,2,2,3,31])] seed_2944
  decide +kernel

private theorem seed_3008 : (3008 : ℕ).primeCounting ≤ 431 ∧ 235 ≤ countRefactorableNat 3008 ∧
    ∀ n ≤ 3008, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 2976 429 233 _ _ _ [
    (13,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (19,[]), (2,[2,2,2,373]),
    (3,[]), (2,[]), (29,[]), (2,[2,2,3,3,83]), (7,[]), (2,[]), (3,[]), (2,[]),
    (41,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (31,[]), (2,[])] seed_2976
  decide +kernel

private theorem seed_3040 : (3040 : ℕ).primeCounting ≤ 435 ∧ 237 ≤ countRefactorableNat 3040 ∧
    ∀ n ≤ 3040, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3008 431 235 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,251]), (23,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (7,[]), (2,[2,2,2,379]),
    (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[])] seed_3008
  decide +kernel

private theorem seed_3072 : (3072 : ℕ).primeCounting ≤ 439 ∧ 240 ≤ countRefactorableNat 3072 ∧
    ∀ n ≤ 3072, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3040 435 237 _ _ _ [
    (0,[]), (2,[2,3,3,13,13]), (17,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (43,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,3,5,17]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,383]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (37,[]), (2,[])] seed_3040
  decide +kernel

private theorem seed_3104 : (3104 : ℕ).primeCounting ≤ 442 ∧ 242 ≤ countRefactorableNat 3104 ∧
    ∀ n ≤ 3104, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3072 439 240 _ _ _ [
    (7,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,257]), (5,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,3,3,43]),
    (19,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (29,[]), (2,[])] seed_3072
  decide +kernel

private theorem seed_3136 : (3136 : ℕ).primeCounting ≤ 445 ∧ 244 ≤ countRefactorableNat 3136 ∧
    ∀ n ≤ 3136, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3104 442 242 _ _ _ [
    (3,[]), (2,[]), (13,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,389]),
    (11,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,3,5,13]),
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (53,[]), (2,[]),
    (3,[]), (2,[]), (31,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[])] seed_3104
  decide +kernel

private theorem seed_3168 : (3168 : ℕ).primeCounting ≤ 448 ∧ 246 ≤ countRefactorableNat 3168 ∧
    ∀ n ≤ 3168, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3136 445 244 _ _ _ [
    (0,[]), (2,[]), (43,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (47,[]), (2,[]), (23,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,263]), (7,[]), (2,[]), (3,[]), (2,[]),
    (29,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,3,3,11])] seed_3136
  decide +kernel

private theorem seed_3200 : (3200 : ℕ).primeCounting ≤ 452 ∧ 247 ≤ countRefactorableNat 3200 ∧
    ∀ n ≤ 3200, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3168 448 246 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]), (5,[]), (2,[2,2,2,397]),
    (3,[]), (2,[]), (11,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (31,[]), (2,[]), (3,[]), (2,[]), (23,[]), (2,[]), (7,[]), (2,[])] seed_3168
  decide +kernel

private theorem seed_3232 : (3232 : ℕ).primeCounting ≤ 457 ∧ 250 ≤ countRefactorableNat 3232 ∧
    ∀ n ≤ 3232, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3200 452 247 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,89]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,401]),
    (0,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,269]), (0,[]), (2,[]), (3,[]), (2,[])] seed_3200
  decide +kernel

private theorem seed_3264 : (3264 : ℕ).primeCounting ≤ 461 ∧ 253 ≤ countRefactorableNat 3264 ∧
    ∀ n ≤ 3264, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3232 457 250 _ _ _ [
    (53,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (41,[]), (2,[2,2,2,3,3,3,3,5]),
    (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (17,[]), (2,[]),
    (3,[3,3,19,19]), (2,[]), (0,[]), (2,[2,2,3,271]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[])] seed_3232
  decide +kernel

private theorem seed_3296 : (3296 : ℕ).primeCounting ≤ 462 ∧ 256 ≤ countRefactorableNat 3296 ∧
    ∀ n ≤ 3296, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3264 461 253 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[2,2,2,409]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3,7,13]), (29,[]), (2,[]), (3,[]), (2,[2,2,2,2,5,41]),
    (17,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]),
    (11,[]), (2,[]), (3,[]), (2,[]), (37,[]), (2,[]), (5,[]), (2,[])] seed_3264
  decide +kernel

private theorem seed_3328 : (3328 : ℕ).primeCounting ≤ 468 ∧ 257 ≤ countRefactorableNat 3328 ∧
    ∀ n ≤ 3328, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3296 462 256 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (31,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,277]), (5,[]), (2,[]), (3,[]), (2,[])] seed_3296
  decide +kernel

private theorem seed_3360 : (3360 : ℕ).primeCounting ≤ 473 ∧ 259 ≤ countRefactorableNat 3360 ∧
    ∀ n ≤ 3360, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3328 468 257 _ _ _ [
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (47,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[2,2,2,419]),
    (7,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,3,5,7])] seed_3328
  decide +kernel

private theorem seed_3392 : (3392 : ℕ).primeCounting ≤ 478 ∧ 262 ≤ countRefactorableNat 3392 ∧
    ∀ n ≤ 3392, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3360 473 259 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (7,[]), (2,[2,2,2,421]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,281]), (0,[]), (2,[]), (3,[]), (2,[]),
    (11,[]), (2,[]), (31,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[2,2,2,3,3,47]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[])] seed_3360
  decide +kernel

private theorem seed_3424 : (3424 : ℕ).primeCounting ≤ 480 ∧ 264 ≤ countRefactorableNat 3424 ∧
    ∀ n ≤ 3424, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3392 478 262 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,283]), (43,[]), (2,[]), (3,[]), (2,[]),
    (19,[]), (2,[]), (41,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (13,[]), (2,[2,2,3,3,5,19]), (11,[]), (2,[]), (3,[]), (2,[])] seed_3392
  decide +kernel

private theorem seed_3456 : (3456 : ℕ).primeCounting ≤ 482 ∧ 267 ≤ countRefactorableNat 3456 ∧
    ∀ n ≤ 3456, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3424 480 264 _ _ _ [
    (5,[]), (2,[]), (23,[]), (2,[]), (3,[]), (2,[]), (47,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (19,[]), (2,[2,2,2,2,5,43]),
    (3,[]), (2,[]), (11,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,431]),
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,2,2,2,2,3,3,3])] seed_3424
  decide +kernel

private theorem seed_3488 : (3488 : ℕ).primeCounting ≤ 487 ∧ 268 ≤ countRefactorableNat 3488 ∧
    ∀ n ≤ 3488, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3456 482 267 _ _ _ [
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[2,2,2,433]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (23,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (59,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (11,[]), (2,[])] seed_3456
  decide +kernel

private theorem seed_3520 : (3520 : ℕ).primeCounting ≤ 491 ∧ 271 ≤ countRefactorableNat 3520 ∧
    ∀ n ≤ 3520, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3488 487 268 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,97]), (7,[]), (2,[]), (3,[]), (2,[]),
    (13,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (31,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (0,[]), (2,[2,2,2,439]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,293]), (0,[]), (2,[]), (3,[]), (2,[])] seed_3488
  decide +kernel

private theorem seed_3552 : (3552 : ℕ).primeCounting ≤ 497 ∧ 274 ≤ countRefactorableNat 3552 ∧
    ∀ n ≤ 3552, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3520 491 271 _ _ _ [
    (7,[]), (2,[]), (13,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,3,3,7,7]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,443]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (53,[]), (2,[2,2,2,2,2,3,37])] seed_3520
  decide +kernel

private theorem seed_3584 : (3584 : ℕ).primeCounting ≤ 502 ∧ 274 ≤ countRefactorableNat 3584 ∧
    ∀ n ≤ 3584, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3552 497 274 _ _ _ [
    (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]),
    (43,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[])] seed_3552
  decide +kernel

private theorem seed_3616 : (3616 : ℕ).primeCounting ≤ 505 ∧ 276 ≤ countRefactorableNat 3616 ∧
    ∀ n ≤ 3616, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3584 502 274 _ _ _ [
    (3,[]), (2,[]), (17,[]), (2,[]), (37,[]), (2,[]), (3,[]), (2,[2,2,2,449]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (59,[]), (2,[2,2,2,2,3,3,5,5]),
    (13,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (23,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[])] seed_3584
  decide +kernel

private theorem seed_3648 : (3648 : ℕ).primeCounting ≤ 510 ∧ 277 ≤ countRefactorableNat 3648 ∧
    ∀ n ≤ 3648, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3616 505 276 _ _ _ [
    (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,3,101]), (0,[]), (2,[]), (3,[]), (2,[]),
    (11,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[])] seed_3616
  decide +kernel

private theorem seed_3680 : (3680 : ℕ).primeCounting ≤ 514 ∧ 278 ≤ countRefactorableNat 3680 ∧
    ∀ n ≤ 3680, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3648 510 277 _ _ _ [
    (41,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]), (5,[]), (2,[2,2,2,457]),
    (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (19,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (13,[]), (2,[])] seed_3648
  decide +kernel

private theorem seed_3712 : (3712 : ℕ).primeCounting ≤ 518 ∧ 283 ≤ countRefactorableNat 3712 ∧
    ∀ n ≤ 3712, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3680 514 278 _ _ _ [
    (3,[]), (2,[]), (29,[]), (2,[2,2,3,307]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,461]),
    (7,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (7,[]), (2,[2,2,2,463]),
    (3,[]), (2,[]), (11,[]), (2,[2,2,3,3,103]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,2,2,2,2,29])] seed_3680
  decide +kernel

private theorem seed_3744 : (3744 : ℕ).primeCounting ≤ 522 ∧ 286 ≤ countRefactorableNat 3744 ∧
    ∀ n ≤ 3744, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3712 518 283 _ _ _ [
    (47,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (61,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,311]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,467]),
    (37,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (19,[]), (2,[2,2,2,2,2,3,3,13])] seed_3712
  decide +kernel

private theorem seed_3776 : (3776 : ℕ).primeCounting ≤ 525 ∧ 288 ≤ countRefactorableNat 3776 ∧
    ∀ n ≤ 3776, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3744 522 286 _ _ _ [
    (5,[]), (2,[]), (3,[]), (2,[]), (23,[]), (2,[]), (11,[]), (2,[]),
    (3,[]), (2,[]), (5,[]), (2,[2,2,3,313]), (13,[]), (2,[]), (3,[]), (2,[2,2,2,2,5,47]),
    (0,[]), (2,[]), (53,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (5,[]), (2,[])] seed_3744
  decide +kernel

private theorem seed_3808 : (3808 : ℕ).primeCounting ≤ 529 ∧ 289 ≤ countRefactorableNat 3808 ∧
    ∀ n ≤ 3808, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3776 525 288 _ _ _ [
    (3,[]), (2,[]), (0,[]), (2,[]), (19,[]), (2,[]), (3,[]), (2,[]),
    (5,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (29,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,317]), (5,[]), (2,[]), (3,[]), (2,[])] seed_3776
  decide +kernel

private theorem seed_3840 : (3840 : ℕ).primeCounting ≤ 532 ∧ 291 ≤ countRefactorableNat 3840 ∧
    ∀ n ≤ 3840, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3808 529 289 _ _ _ [
    (13,[]), (2,[]), (37,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,3,3,53]),
    (11,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (43,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[2,2,2,479]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[])] seed_3808
  decide +kernel

private theorem seed_3872 : (3872 : ℕ).primeCounting ≤ 536 ∧ 292 ≤ countRefactorableNat 3872 ∧
    ∀ n ≤ 3872, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3840 532 291 _ _ _ [
    (23,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,107]), (0,[]), (2,[]), (3,[]), (2,[]),
    (7,[]), (2,[]), (17,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (53,[]), (2,[]), (7,[]), (2,[])] seed_3840
  decide +kernel

private theorem seed_3904 : (3904 : ℕ).primeCounting ≤ 539 ∧ 293 ≤ countRefactorableNat 3904 ∧
    ∀ n ≤ 3904, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3872 536 292 _ _ _ [
    (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]), (13,[]), (2,[]),
    (0,[]), (2,[]), (3,[]), (2,[]), (17,[]), (2,[]), (5,[]), (2,[2,2,2,487]),
    (3,[]), (2,[]), (7,[]), (2,[]), (47,[]), (2,[]), (3,[]), (2,[])] seed_3872
  decide +kernel

private theorem seed_3936 : (3936 : ℕ).primeCounting ≤ 546 ∧ 296 ≤ countRefactorableNat 3936 ∧
    ∀ n ≤ 3936, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3904 539 293 _ _ _ [
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (7,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[2,2,3,3,109]), (5,[]), (2,[]), (3,[]), (2,[2,2,2,491]),
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,2,2,3,41])] seed_3904
  decide +kernel

private theorem seed_3968 : (3968 : ℕ).primeCounting ≤ 549 ∧ 297 ≤ countRefactorableNat 3968 ∧
    ∀ n ≤ 3968, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3936 546 296 _ _ _ [
    (31,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]), (0,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (11,[]), (2,[]), (3,[]), (2,[]),
    (59,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (37,[]), (2,[]),
    (17,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (0,[]), (2,[2,2,2,2,2,2,2,31])] seed_3936
  decide +kernel

private theorem seed_4000 : (4000 : ℕ).primeCounting ≤ 550 ∧ 299 ≤ countRefactorableNat 4000 ∧
    ∀ n ≤ 4000, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 3968 549 297 _ _ _ [
    (3,[]), (2,[]), (11,[]), (2,[2,2,3,331]), (29,[]), (2,[]), (3,[]), (2,[]),
    (41,[]), (2,[]), (23,[]), (2,[]), (3,[]), (2,[]), (7,[]), (2,[]),
    (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (13,[]), (2,[2,2,2,499]),
    (3,[]), (2,[]), (5,[]), (2,[]), (7,[]), (2,[]), (3,[]), (2,[])] seed_3968
  decide +kernel

private theorem seed_4032 : (4032 : ℕ).primeCounting ≤ 557 ∧ 301 ≤ countRefactorableNat 4032 ∧
    ∀ n ≤ 4032, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 4000 550 299 _ _ _ [
    (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]),
    (19,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[]), (5,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[2,2,2,503]),
    (5,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[]), (29,[]), (2,[2,2,2,2,2,2,3,3,7])] seed_4000
  decide +kernel

private theorem seed_4064 : (4064 : ℕ).primeCounting ≤ 560 ∧ 304 ≤ countRefactorableNat 4064 ∧
    ∀ n ≤ 4064, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 4032 557 301 _ _ _ [
    (37,[]), (2,[]), (3,[]), (2,[]), (11,[]), (2,[]), (7,[]), (2,[]),
    (3,[]), (2,[]), (13,[]), (2,[2,2,3,337]), (5,[]), (2,[]), (3,[]), (2,[]),
    (0,[]), (2,[2,3,3,3,3,5,5]), (0,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[2,2,2,3,13,13]),
    (0,[]), (2,[]), (3,[]), (2,[]), (31,[]), (2,[]), (17,[]), (2,[])] seed_4032
  decide +kernel

private theorem seed_4096 : (4096 : ℕ).primeCounting ≤ 564 ∧ 307 ≤ countRefactorableNat 4096 ∧
    ∀ n ≤ 4096, n.primeCounting ≤ 2 * countRefactorableNat n := by
  apply seed_block 4064 560 304 _ _ _ [
    (3,[]), (2,[]), (7,[]), (2,[2,2,3,3,113]), (13,[]), (2,[]), (3,[]), (2,[2,2,2,509]),
    (0,[]), (2,[]), (5,[]), (2,[]), (3,[]), (2,[]), (0,[]), (2,[2,2,2,2,3,5,17]),
    (7,[]), (2,[]), (3,[]), (2,[]), (5,[]), (2,[]), (61,[]), (2,[]),
    (3,[]), (2,[]), (0,[]), (2,[]), (0,[]), (2,[]), (3,[]), (2,[])] seed_4064
  decide +kernel

private theorem initial_certificate : 307 ≤ countRefactorableNat 4096 ∧
    ∀ n ≤ 4096, n.primeCounting ≤ 2 * countRefactorableNat n := seed_4096.2



private theorem log_large {x : ℝ} (hx : 4 ≤ x) : (11/10 : ℝ) < Real.log x := by
  have h := Real.log_le_log (by norm_num : (0:ℝ) < 2 ^ 2) (show (2:ℝ)^2 ≤ x by linarith)
  rw [Real.log_pow] at h
  exact (show (11/10 : ℝ) < 2 * 0.6931471803 by norm_num).trans_le
    ((mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (by norm_num : (0:ℝ) ≤ 2)).trans h)

private theorem pi_cutoff (hL : H3) :
    (1000000000000 : ℝ) ≤ ((2^45 : ℕ).primeCounting : ℝ) := by
  have h := hL.1 ((2^45 : ℕ) : ℝ) (by norm_num)
  rw [Nat.floor_natCast] at h
  have hlog : Real.log ((2^45 : ℕ) : ℝ) = 45 * Real.log 2 := by
    rw [show ((2^45 : ℕ) : ℝ) = (2 : ℝ)^45 by norm_num, Real.log_pow]
    norm_num
  have hp := log_large (x := ((2^45 : ℕ) : ℝ)) (by norm_num)
  apply le_trans _ h
  apply (le_div_iff₀ (sub_pos.mpr ((by norm_num : (1:ℝ) < 11/10).trans hp))).mpr
  rw [hlog]
  norm_num
  linarith [Real.log_two_lt_d9]

private theorem pi_scale (hL : H3) {n k : ℕ} (hn : (2^45 : ℕ) ≤ n)
    (hk2 : 2 ≤ k) (hkM : k ≤ 20000000) :
    (n.primeCounting : ℝ) / k ≤ ((n / k).primeCounting : ℝ) := by
  have hlarge : 35184372088832 ≤ (n : ℝ) := by exact_mod_cast hn
  have hk : 2 ≤ (k : ℝ) := by exact_mod_cast hk2
  have hmax : (k : ℝ) ≤ 20000000 := by exact_mod_cast hkM
  have hkpos : 0 < (k : ℝ) := by linarith
  have hx : 5393 ≤ (n : ℝ) / k := (le_div_iff₀ hkpos).mpr (by linarith)
  have hlo := hL.1 _ hx
  rw [Nat.floor_div_natCast, Nat.floor_natCast] at hlo
  have hup := hL.2 (n : ℝ) (by linarith)
  rw [Nat.floor_natCast] at hup
  have hd := log_large (x := (n : ℝ)/k) (by linarith)
  have hlogk := Real.log_le_log (by norm_num : (0:ℝ)<2) hk
  calc
    _ ≤ (n : ℝ) / (Real.log n - 11/10) / k := div_le_div_of_nonneg_right hup hkpos.le
    _ = ((n : ℝ)/k) / (Real.log n - 11/10) := div_right_comm ..
    _ ≤ ((n : ℝ)/k) / (Real.log ((n:ℝ)/k) - 1) := by
      apply div_le_div_of_nonneg_left (by positivity) (by linarith)
      rw [Real.log_div (by positivity) (by positivity)]
      linarith [Real.log_two_gt_d9]
    _ ≤ _ := hlo

private theorem tail (hG : H2) (hL : H3) (n : ℕ) (hn : (2^45 : ℕ) ≤ n) :
    n.primeCounting ≤ 2 * countRefactorableNat n := by
  let S := ((Icc 1 20000000).filter (fun k : ℕ => 0 < k ∧ 2 * k.divisors.card ∣ k))
  have hs (k : ℕ) (hk : k ∈ S) : (0 < k ∧ 2 * k.divisors.card ∣ k) := (mem_filter.mp hk).2
  have hscale (k : ℕ) (hk : k ∈ S) :
      (n.primeCounting : ℝ) * (1 / (k : ℝ)) ≤
      ((((n/k).primeCounting - ((k.primeFactors.sup id)).primeCounting : ℕ) : ℝ) + ((k.primeFactors.sup id)).primeCounting) := by
    have hd : 2 ∣ k := dvd_trans (dvd_mul_right 2 k.divisors.card) (hs k hk).2
    have hk2 := Nat.le_of_dvd (hs k hk).1 hd
    have hu := (mem_Icc.mp (mem_filter.mp hk).1).2
    calc
      _ = (n.primeCounting : ℝ) / k := by ring
      _ ≤ ((n/k).primeCounting : ℝ) := pi_scale hL hn hk2 hu
      _ ≤ _ := by
        exact_mod_cast (show (n/k).primeCounting ≤ ((n/k).primeCounting - ((k.primeFactors.sup id)).primeCounting) + ((k.primeFactors.sup id)).primeCounting by omega)
  have hsum := Finset.sum_le_sum hscale
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hrec : (251/500 : ℝ) ≤ ∑ k ∈ S, 1/(k:ℝ) := by
    have hv := (Rat.cast_le (K := ℝ)).mpr hG.1
    push_cast at hv
    exact hv
  have herror : (∑ k ∈ S, (((k.primeFactors.sup id)).primeCounting : ℝ)) ≤ 2000000000 := by
    exact_mod_cast hG.2
  have hgen := seed_add_generated (zero_le n) S hs
  have hnum : (∑ k ∈ S, ((((n/k).primeCounting - ((k.primeFactors.sup id)).primeCounting : ℕ) : ℝ))) ≤
      (countRefactorableNat n : ℝ) := by
    exact_mod_cast (show (∑ k ∈ S, ((n/k).primeCounting - ((k.primeFactors.sup id)).primeCounting)) ≤
        countRefactorableNat n by simpa [countRefactorableNat] using hgen)
  have hbig : (1000000000000 : ℝ) ≤ (n.primeCounting : ℝ) :=
    (pi_cutoff hL).trans (by exact_mod_cast Nat.monotone_primeCounting hn)
  have ht := (mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg n.primeCounting)).trans hsum
  exact_mod_cast (show (n.primeCounting : ℝ) ≤ 2 * countRefactorableNat n by linarith)



private theorem count_mono : Monotone countRefactorableNat := by
  intro m n h
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right h)

private theorem reaches (x : ℕ → ℕ) (hzero : x 0 = 4096)
    (hsucc : ∀ j, x (j+1) = x j + x j / 40) : 2^45 ≤ x 927 := by
  have hlo (j : ℕ) : 40 ≤ x j := by
    induction j with
    | zero => omega
    | succ j ih => rw [hsucc]; omega
  have hstep (j : ℕ) : 41 * (x j - 40) ≤ 40 * (x (j+1) - 40) := by
    rw [hsucc]
    have := hlo j
    omega
  have hg (j : ℕ) : 41^j * 4056 ≤ 40^j * (x j - 40) := by
    induction j with
    | zero => simp [hzero]
    | succ j ih =>
      calc
        41^(j+1) * 4056 = 41 * (41^j * 4056) := by ring
        _ ≤ 41 * (40^j * (x j - 40)) := Nat.mul_le_mul_left _ ih
        _ = 40^j * (41 * (x j - 40)) := by ring
        _ ≤ 40^j * (40 * (x (j+1) - 40)) := Nat.mul_le_mul_left _ (hstep j)
        _ = 40^(j+1) * (x (j+1) - 40) := by ring
  have cert : 40^927 * (2^45 - 40 : ℕ) ≤ 41^927 * 4056 := by decide +kernel
  have h : (2^45-40 : ℕ) ≤ x 927 - 40 :=
    Nat.le_of_mul_le_mul_left (cert.trans (hg 927)) (pow_pos (by decide) _)
  calc
    2^45 = (2^45-40)+40 := by decide
    _ ≤ (x 927-40)+40 := Nat.add_le_add_right h 40
    _ = x 927 := Nat.sub_add_cancel (hlo 927)

theorem main : H1 → H2 → H3 → type_of% @OeisA111291.colton_conjecture := by
  intro h₁ h₃ h₄ n
  have h₂ := ColtonMiddle.middle h₄.1 h₄.2
  by_cases hn : n ≤ 2^45
  · let f (m : ℕ) := m + m/40
    let x (j : ℕ) := f^[j] 4096
    have hx (j : ℕ) : x (j+1) = x j + x j/40 := Function.iterate_succ_apply' f j 4096
    have lower (j : ℕ) : 4096 ≤ x j := by
      induction j with
      | zero => exact le_rfl
      | succ j ih => rw [hx]; omega
    have upto (j : ℕ) (hj : j ≤ 927) : ∀ m ≤ x j, m.primeCounting ≤ 2 * countRefactorableNat m := by
      induction j with
      | zero => exact initial_certificate.2
      | succ j ih =>
        intro m hm
        by_cases hmj : m ≤ x j
        · exact ih (by omega) m hmj
        · let G := ((Icc 1 (min (if j < 317 then 10000 else 500000) (x j/2))).filter (fun k : ℕ => 0 < k ∧ 2 * k.divisors.card ∣ k))
          have hcount := seed_add_generated (lower j) G (fun _ hk => (mem_filter.mp hk).2)
          have hbudget := (Nat.add_le_add_right initial_certificate.1 _).trans hcount
          have hgrid : (x (j+1)).primeCounting ≤ 2 * (307 + (∑ k ∈ G, (((x j)/k).primeCounting - (max (k.primeFactors.sup id) (4096/k)).primeCounting))) := by
            rw [hx]
            by_cases hs : j < 317
            · simpa only [G, if_pos hs] using h₁ j hs
            · simpa only [G, if_neg hs, ColtonMiddle.grid, x, f] using h₂ j (by omega) (by omega)
          exact ((Nat.monotone_primeCounting hm).trans hgrid).trans
            (Nat.mul_le_mul_left 2 (hbudget.trans (count_mono (by omega))))
    exact upto 927 le_rfl n (hn.trans (reaches x rfl hx))
  · exact tail h₃ h₄ n (by omega)

end OMA.R_OeisA111291_colton_conjecture_R2
