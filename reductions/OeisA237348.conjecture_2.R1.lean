import FormalConjectures.OEIS.«237348»
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# A parity and character-sum reduction for A237348

The finite certificate below checks the strict cutoffs and proves that each
cutoff itself is excluded. Above 128 we retain pairs of the required parity
and detect their exact sum by additive characters modulo n+1.
Credit: @Pixelstorm44.
-/
namespace OMA.R_OeisA237348_conjecture_2_R1

theorem rank_table (f : ℕ → ℕ) (L : ℕ) (first : f 1 = 2)
    (steps : ∀ i : Fin L, let a := f (i.val+1); let b := f (i.val+2)
      a ≤ b ∧ b.Prime ∧ Nat.count (fun t => (a+t).Prime) (b-a) = 1)
    {k : ℕ} (lo : 0 < k) (hi : k ≤ L+1) :
    Nat.nth Nat.Prime (k-1) = f k := by
  have aux (i : ℕ) (hi : i ≤ L) :
      (f (i+1)).Prime ∧ Nat.count Nat.Prime (f (i+1)) = i := by
    induction i with
    | zero => rw [Nat.zero_add, first]; decide
    | succ i ih =>
      obtain ⟨hab, hp, hcount⟩ := steps ⟨i, by omega⟩
      refine ⟨hp, ?_⟩
      obtain ⟨_, prev⟩ := ih (by omega)
      have h := Nat.count_add Nat.Prime (f (i+1)) (f (i+2)-f (i+1))
      rw [Nat.add_sub_of_le hab, prev, hcount] at h
      exact h
  obtain ⟨hp, hc⟩ := aux (k-1) (by omega)
  rw [Nat.sub_add_cancel lo] at hp hc
  rw [← hc, Nat.nth_count hp]

-- Above 75 and below 76², a single factorial gcd detects every composite.
theorem factorial_test {v : ℕ} (h : 75 < v ∧ v < 5776) :
    v.Coprime (Nat.factorial 75) ↔ v.Prime := by
  constructor
  · intro hc
    have hfac := (Nat.coprime_factorial_iff (by omega : v ≠ 1)).mp hc
    by_contra hnp
    have hs := Nat.minFac_sq_le_self (by omega : 0 < v) hnp
    have hpow := Nat.pow_le_pow_left (by omega : 76 ≤ v.minFac) 2
    omega
  · intro hp
    exact hp.coprime_factorial_of_lt h.1

set_option maxRecDepth 16000 in
set_option maxHeartbeats 14000000 in
theorem finite_boundary :
    let p := fun k : ℕ => Nat.nth Nat.Prime (k-1)
    let T : Fin 10 → ℕ := ![2,11,4,15,31,4,2,77,4,7]
    let good := fun (d : Fin 10) (n : ℕ) => ∃ k m : ℕ,
      0 < k ∧ 0 < m ∧ n = k+m ∧
      (p k + 2*(d.val+1)).Prime ∧ (p (p m) + 2*(d.val+1)).Prime
    ∀ d, (¬ good d (T d)) ∧ ∀ n ≤ 128, T d < n → good d n := by
  let T : Fin 10 → ℕ := ![2,11,4,15,31,4,2,77,4,7]
  let fast (v : ℕ) : Decidable (Nat.Prime v) :=
    if h : 75 < v ∧ v < 5776 then decidable_of_iff _ (factorial_test h)
    else Nat.decidablePrime v
  -- One-based prime ranks, grouped into blocks of 24 for kernel evaluation.
  let a : Array (Array ℕ) := #[#[0,2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83],
    #[89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211],
    #[223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353],
    #[359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499],
    #[503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653],
    #[659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823],
    #[827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991],
    #[997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153],
    #[1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319],
    #[1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499],
    #[1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669],
    #[1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873],
    #[1877,1879,1889,1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,2029,2039,2053,2063],
    #[2069,2081,2083,2087,2089,2099,2111,2113,2129,2131,2137,2141,2143,2153,2161,2179,2203,2207,2213,2221,2237,2239,2243,2251],
    #[2267,2269,2273,2281,2287,2293,2297,2309,2311,2333,2339,2341,2347,2351,2357,2371,2377,2381,2383,2389,2393,2399,2411,2417],
    #[2423,2437,2441,2447,2459,2467,2473,2477,2503,2521,2531,2539,2543,2549,2551,2557,2579,2591,2593,2609,2617,2621,2633,2647],
    #[2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713,2719,2729,2731,2741,2749,2753,2767,2777,2789,2791,2797],
    #[2801,2803,2819,2833,2837,2843,2851,2857,2861,2879,2887,2897,2903,2909,2917,2927,2939,2953,2957,2963,2969,2971,2999,3001],
    #[3011,3019,3023,3037,3041,3049,3061,3067,3079,3083,3089,3109,3119,3121,3137,3163,3167,3169,3181,3187,3191,3203,3209,3217],
    #[3221,3229,3251,3253,3257,3259,3271,3299,3301,3307,3313,3319,3323,3329,3331,3343,3347,3359,3361,3371,3373,3389,3391,3407],
    #[3413,3433,3449,3457,3461,3463,3467,3469,3491,3499,3511,3517,3527,3529,3533,3539,3541,3547,3557,3559,3571,3581,3583,3593],
    #[3607,3613,3617,3623,3631,3637,3643,3659,3671,3673,3677,3691,3697,3701,3709,3719,3727,3733,3739,3761,3767,3769,3779,3793],
    #[3797,3803,3821,3823,3833,3847,3851,3853,3863,3877,3881,3889,3907,3911,3917,3919,3923,3929,3931,3943,3947,3967,3989,4001],
    #[4003,4007,4013,4019,4021,4027,4049,4051,4057,4073,4079,4091,4093,4099,4111,4127,4129,4133,4139,4153,4157,4159,4177,4201],
    #[4211,4217,4219,4229,4231,4241,4243,4253,4259,4261,4271,4273,4283,4289,4297,4327,4337,4339,4349,4357,4363,4373,4391,4397],
    #[4409,4421,4423,4441,4447,4451,4457,4463,4481,4483,4493,4507,4513,4517,4519,4523,4547,4549,4561,4567,4583,4591,4597,4603],
    #[4621,4637,4639,4643,4649,4651,4657,4663,4673,4679,4691,4703,4721,4723,4729,4733,4751,4759,4783,4787,4789,4793,4799,4801],
    #[4813,4817,4831,4861,4871,4877,4889,4903,4909,4919,4931,4933,4937,4943,4951,4957,4967,4969,4973,4987,4993,4999,5003,5009],
    #[5011,5021,5023,5039,5051,5059,5077,5081,5087,5099,5101,5107,5113,5119,5147,5153,5167,5171,5179,5189,5197,5209,5227,5231],
    #[5233,5237,5261,5273,5279,5281,5297,5303,5309,5323,5333,5347,5351,5381,5387,5393,5399,5407,5413,5417,5419,5431,5437,5441],
    #[5443]]
  let f := fun i : ℕ => (a[i/24]?.getD #[])[i%24]?.getD 0
  have steps : ∀ i : Fin 719, let u := f (i.val+1); let v := f (i.val+2)
      u ≤ v ∧ v.Prime ∧ Nat.count (fun t => (u+t).Prime) (v-u) = 1 := by decide
  have eqn {k : ℕ} (lo : 0 < k) (hi : k ≤ 720) :
      Nat.nth Nat.Prime (k-1) = f k := by
    apply rank_table f 719 (by decide) _ lo hi
    have same : fast = Nat.decidablePrime := Subsingleton.elim _ _
    rw [same] at steps
    exact steps
  have bounds : ∀ m : Fin 129, 0 < m.val → 0 < f m.val ∧ f m.val ≤ 720 := by decide
  have cutoff : ∀ d, T d ≤ 128 := by decide
  have sharp : ∀ d (m : Fin 129), 0 < m.val → m.val < T d →
      ¬ ((f (T d-m.val)+2*(d.val+1)).Prime ∧
        (f (f m.val)+2*(d.val+1)).Prime) := by decide
  -- Row d, column n gives a candidate for m. Every used entry is checked below.
  let w : Array (Array ℕ) := #[#[0,0,0,1,1,2,1,2,1,2,3,1,2,3,1,2,3,4,1,2,3,1,
    2,3,4,23,6,1,2,1,2,3,4,7,1,2,1,2,3,4,7,6,1,2,
    1,2,1,2,3,4,1,2,3,1,2,3,4,14,1,2,3,1,2,3,4,1,
    2,3,4,24,1,2,3,4,14,6,7,13,14,30,23,24,1,2,1,2,3,4,
    7,6,1,2,3,4,13,6,7,14,29,1,2,3,4,14,6,1,2,3,4,40,
    1,2,3,4,1,2,3,1,2,3,4,1,2,3,4,65,6,7,24],
    #[0,0,0,0,0,0,0,0,0,0,0,0,8,1,8,1,8,11,10,11,1,17,
    8,1,10,11,1,8,1,10,1,17,1,8,32,8,11,8,11,1,11,10,11,35,
    17,1,8,35,10,1,36,1,8,47,10,11,8,32,8,11,1,11,35,32,1,17,
    1,8,54,10,11,1,47,8,11,10,1,50,8,1,10,11,17,8,36,10,1,17,
    10,1,42,1,17,8,1,10,1,32,8,11,10,8,17,8,11,10,11,17,38,50,
    17,36,17,1,36,50,38,32,1,54,8,36,10,1,36,8,36,10,11],
    #[0,0,0,0,0,2,2,2,2,2,3,2,3,2,2,2,3,2,2,3,2,2,
    3,2,3,2,3,2,2,2,2,3,4,5,2,3,4,5,2,2,3,2,2,3,
    4,2,2,3,4,5,2,2,3,2,3,4,2,2,2,3,2,2,3,4,5,2,
    2,3,4,2,3,2,3,2,3,2,2,3,2,3,4,5,6,9,8,9,2,3,
    2,3,2,2,3,4,5,6,8,8,2,3,4,5,2,3,2,2,3,2,3,2,
    2,3,2,2,2,3,4,5,2,3,2,2,3,4,5,2,3,4,5],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,1,1,2,3,1,
    2,3,7,1,2,1,2,3,14,7,22,1,2,3,1,2,3,7,14,1,2,3,
    1,2,3,7,22,14,7,27,1,2,3,23,40,1,1,2,3,29,22,7,7,14,
    23,27,65,29,14,14,29,1,2,3,60,53,1,2,1,2,3,27,1,2,3,71,
    1,2,3,14,60,1,2,1,2,3,74,7,23,7,23,60,1,1,2,3,14,1,
    1,2,3,103,22,7,7,14,14,27,1,2,3,14,100,1,2,1,2],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,1,11,12,1,5,12,1,1,18,16,5,1,
    26,11,12,5,11,1,12,1,18,5,1,5,18,26,5,1,12,11,1,5,1,12,
    5,36,5,1,12,1,11,5,11,1,1,16,36,5,5,1,12,1,16,1,1,5,
    18,1,5,11,12,5,12,11,1,12,16,11,5,16,1,18,16,31,5,1,26,51,
    26,5,1,12,26,31,1,11,1,18,5,26,5,1,18,37,1,5,1],
    #[0,0,0,0,0,2,2,2,3,2,2,3,2,2,3,2,3,2,3,2,2,2,
    2,3,4,5,2,2,2,3,4,5,6,2,3,2,2,3,2,3,4,2,3,2,
    2,3,4,5,2,2,3,2,2,3,2,3,2,2,3,2,2,3,2,3,4,5,
    6,7,8,11,2,2,3,4,5,2,3,4,5,2,2,3,2,2,2,2,3,4,
    5,2,3,4,5,2,2,2,2,3,4,2,3,4,5,6,2,3,4,5,6,2,
    3,4,2,2,3,4,2,2,2,3,2,3,4,2,3,4,5,6,7],
    #[0,0,0,1,1,2,4,4,1,2,1,1,2,4,4,13,1,1,1,2,4,4,
    7,7,1,1,2,4,4,13,7,1,2,9,1,2,1,2,28,4,1,2,1,2,
    9,4,1,2,7,4,1,2,7,4,9,20,1,1,1,2,4,4,7,1,2,9,
    4,1,2,7,4,9,1,1,2,4,4,1,2,7,4,9,1,2,13,4,20,1,
    1,2,4,4,20,7,7,9,9,25,1,2,13,4,30,1,1,2,4,4,1,1,
    1,2,4,4,1,2,7,4,9,1,2,1,2,20,1,2,13,4,20],
    #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,5,5,12,8,8,15,16,1,12,19,
    15,5,16,1,8,19,1,5,12,38,5,15,16,1,1,19,45,5,1,1,8,8,
    5,1,12,8,8,5,1,12,1,19,5,15,1,8,19,8,5,12,38],
    #[0,0,0,0,0,2,3,2,2,3,2,2,2,3,6,2,2,3,2,3,2,3,
    2,3,2,2,2,3,6,6,6,2,2,3,2,3,2,2,3,9,2,3,2,2,
    2,3,2,3,6,2,2,3,10,2,2,3,2,3,2,3,6,9,6,9,2,3,
    10,2,3,2,3,6,2,3,9,10,6,2,2,3,10,2,3,13,2,2,3,2,
    2,2,3,2,3,6,9,6,2,3,2,3,6,2,3,9,10,6,2,3,9,10,
    6,2,2,3,2,3,6,13,2,2,3,9,2,3,2,3,2,2,2],
    #[0,0,0,0,0,0,0,0,1,4,1,4,3,4,1,6,1,1,1,3,3,4,
    6,6,1,1,3,3,4,1,6,3,4,1,1,3,3,4,6,6,7,1,1,3,
    1,4,3,4,7,6,7,28,9,13,13,1,1,1,3,3,4,6,6,1,9,1,
    4,1,4,3,1,7,1,1,3,3,4,6,1,7,1,4,1,4,3,4,7,1,
    7,3,4,14,1,1,3,3,4,1,6,1,4,3,4,1,6,3,4,9,1,1,
    1,3,3,4,6,6,7,1,9,3,1,13,3,4,22,6,7,20,9]]
  have cases_ok : ∀ (d : Fin 10) (j : Fin 129), T d < j.val →
      let m := (w[d.val]?.getD #[])[j.val]?.getD 0
      0 < m ∧ m < j.val ∧ (f (j.val-m)+2*(d.val+1)).Prime ∧
        (f (f m)+2*(d.val+1)).Prime := by decide
  dsimp only
  intro d
  constructor
  · rintro ⟨k,m,hk,hm,hs,h1,h2⟩
    change T d = k+m at hs
    have hT := cutoff d
    have hb := bounds ⟨m, by omega⟩ hm
    change (Nat.nth Nat.Prime (k-1)+2*(d.val+1)).Prime at h1
    change (Nat.nth Nat.Prime (Nat.nth Nat.Prime (m-1)-1)+2*(d.val+1)).Prime at h2
    rw [eqn hk (by omega)] at h1
    rw [eqn hm (by omega), eqn hb.1 hb.2] at h2
    have hkm : T d-m = k := by omega
    apply sharp d ⟨m, by omega⟩ hm (by dsimp; omega)
    simpa only [hkm] using And.intro h1 h2
  · intro n hn ht
    let m := (w[d.val]?.getD #[])[n]?.getD 0
    obtain ⟨hm, hmn, h1, h2⟩ := cases_ok d ⟨n, by omega⟩ ht
    change 0 < m at hm
    change m < n at hmn
    have hb := bounds ⟨m, by omega⟩ hm
    refine ⟨n-m, m, by omega, hm, by omega, ?_, ?_⟩
    · rw [eqn (by omega) (by omega)]
      exact h1
    · rw [eqn hm (by omega), eqn hb.1 hb.2]
      exact h2

-- Coarse distribution can be studied from the two parity counts on each side.
def H1 : Prop := ∀ (d : Fin 10) (n : ℕ), 128 < n →
  let p := fun k : ℕ => Nat.nth Nat.Prime (k-1)
  let A := (Finset.Ico 1 n).filter fun k => (p k+2*(d.val+1)).Prime
  let B := (Finset.Ico 1 n).filter fun m => (p (p m)+2*(d.val+1)).Prime
  let S := (A.product B).filter fun z => (z.1+z.2)%2 = n%2
  2 * (A.card * B.card) ≤ 5 * S.card

-- The signed nonzero-frequency contribution. Within each compatible parity
-- class the double sum factors into two one-dimensional exponential sums.
def H2 : Prop := ∀ (d : Fin 10) (n : ℕ), 128 < n →
  let p := fun k : ℕ => Nat.nth Nat.Prime (k-1)
  let A := (Finset.Ico 1 n).filter fun k => (p k+2*(d.val+1)).Prime
  let B := (Finset.Ico 1 n).filter fun m => (p (p m)+2*(d.val+1)).Prime
  let S := (A.product B).filter fun z => (z.1+z.2)%2 = n%2
  0 < 2 * ((A.card : ℝ) * B.card) +
    5 * ∑ h ∈ (Finset.univ : Finset (ZMod (n+1))).erase 0,
      ∑ z ∈ S, (ZMod.stdAddChar (((z.1 : ZMod (n+1)) + (z.2 : ZMod (n+1)) - (n : ZMod (n+1)))*h)).re

theorem nonzero_modes {q : ℕ} [NeZero q] (x : ZMod q) (hx : x ≠ 0) :
    ∑ h ∈ (Finset.univ : Finset (ZMod q)).erase 0, (ZMod.stdAddChar (x*h)).re = -1 := by
  have hall : ∑ h : ZMod q, ZMod.stdAddChar (x*h) = 0 :=
    AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hx)
  have h := Finset.univ.sum_erase_add (fun j : ZMod q => ZMod.stdAddChar (x*j))
    (Finset.mem_univ (0 : ZMod q))
  rw [hall] at h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.re_sum, mul_zero, AddChar.map_zero_eq_one,
    Complex.one_re, Complex.zero_re] at hr
  linarith

theorem no_alias {k m n : ℕ} (hk : k < n) (hm : m < n)
    (he : (k : ZMod (n+1)) + m - n = 0) : n = k+m := by
  have h := (ZMod.natCast_eq_natCast_iff' (k+m) n (n+1)).mp (by
    push_cast; exact sub_eq_zero.mp he)
  rw [Nat.mod_eq_of_lt (Nat.lt_succ_self n)] at h
  by_cases hs : k+m < n+1
  · rwa [Nat.mod_eq_of_lt hs, eq_comm] at h
  · rw [Nat.mod_eq_sub_mod (by omega : n+1 ≤ k+m),
      Nat.mod_eq_of_lt (by omega)] at h
    omega

-- Any solution also yields arbitrarily large pairs of primes at each of the
-- ten prescribed distances. The case d = 0 in Fin 10 gives twin primes.
theorem necessary_prime_pairs (solution : type_of% @OeisA237348.conjecture_2)
    (d : Fin 10) (M : ℕ) :
    ∃ q : ℕ, M < q ∧ q.Prime ∧ (q+2*(d.val+1)).Prime := by
  let T : ℕ := ![2,11,4,15,31,4,2,77,4,7] d
  let n := 2*(M+T+1)
  obtain ⟨k,m,hk,hm,hs,hA,hB⟩ := solution d n (by change T < 2*(M+T+1); omega)
  have hk' := Nat.add_two_le_nth_prime (k-1)
  have hm' := Nat.add_two_le_nth_prime (m-1)
  have hmm' := Nat.add_two_le_nth_prime (Nat.nth Nat.Prime (m-1)-1)
  dsimp only [n] at hs
  by_cases h : M < Nat.nth Nat.Prime (k-1)
  · exact ⟨_, h, Nat.prime_nth_prime _, hA⟩
  · exact ⟨_, by omega, Nat.prime_nth_prime _, hB⟩

theorem main : H1 → H2 → type_of% @OeisA237348.conjecture_2 := by
  intro coarse cancel d n hn
  by_cases hsmall : n ≤ 128
  · exact (finite_boundary d).2 n hsmall hn
  have hbig : 128 < n := by omega
  let p := fun k : ℕ => Nat.nth Nat.Prime (k-1)
  let A := (Finset.Ico 1 n).filter fun k => (p k+2*(d.val+1)).Prime
  let B := (Finset.Ico 1 n).filter fun m => (p (p m)+2*(d.val+1)).Prime
  let S := (A.product B).filter fun z => (z.1+z.2)%2 = n%2
  let x := fun z : ℕ × ℕ => (z.1 : ZMod (n+1)) + z.2 - n
  have hmain : 2 * ((A.card : ℝ)*B.card) ≤ 5*(S.card : ℝ) := by
    exact_mod_cast coarse d n hbig
  have hminor : 0 < 2 * ((A.card : ℝ)*B.card) +
      5 * ∑ h ∈ (Finset.univ : Finset (ZMod (n+1))).erase 0,
        ∑ z ∈ S, (ZMod.stdAddChar (x z * h)).re := cancel d n hbig
  by_contra hnone
  have hx (z : ℕ × ℕ) (hz : z ∈ S) : x z ≠ 0 := by
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
    obtain ⟨hka,hpa⟩ := Finset.mem_filter.mp ha
    obtain ⟨hmb,hpb⟩ := Finset.mem_filter.mp hb
    obtain ⟨hk,hkn⟩ := Finset.mem_Ico.mp hka
    obtain ⟨hm,hmn⟩ := Finset.mem_Ico.mp hmb
    intro he
    exact hnone ⟨z.1,z.2,hk,hm,no_alias hkn hmn he,hpa,hpb⟩
  rw [Finset.sum_comm] at hminor
  have hs : (∑ z ∈ S, ∑ h ∈ (Finset.univ : Finset (ZMod (n+1))).erase 0,
      (ZMod.stdAddChar (x z*h)).re) = -(S.card : ℝ) := calc
    _ = ∑ _z ∈ S, (-1 : ℝ) := Finset.sum_congr rfl fun z hz => nonzero_modes _ (hx z hz)
    _ = _ := by simp
  rw [hs] at hminor
  linarith

end OMA.R_OeisA237348_conjecture_2_R1
