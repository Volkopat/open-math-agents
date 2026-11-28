import OMAReductions.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1
import Mathlib
/-!
The window sieve and population-count correctness proofs are adapted from upstream PR #12751
for A262999, which credits Neal Patel’s A262995Refutation.lean (commit
e0c9810910fd2faa896326257d0a7b95216756cc). The divisor basis, window width, and
certificates below are specialized to the prime count at ninety million.

  MIT License

  Copyright (c) 2026 Neal Patel

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the 'Software'), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED 'AS IS', WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.

-/

namespace FinitePrimeEstimate



/-! ## Bitmask of the multiples of `d` -/

/-- `m ||| (m <<< s)`. -/
def dbl (s m : ℕ) : ℕ := m ||| (m <<< s)

/-- The bitmask of the multiples of `d` below `d * 2 ^ t`, built by doubling. -/
def multMask (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => dbl (d * 2 ^ t) (multMask d t)

theorem testBit_multMask {d : ℕ} (hd : 0 < d) (t i : ℕ) :
    (multMask d t).testBit i = true ↔ d ∣ i ∧ i < d * 2 ^ t := by
  induction t generalizing i with
  | zero =>
    rw [multMask, Nat.testBit_one_eq_true_iff_self_eq_zero, pow_zero, mul_one]
    constructor
    · rintro rfl
      exact ⟨dvd_zero d, hd⟩
    · rintro ⟨hdvd, hlt⟩
      exact Nat.eq_zero_of_dvd_of_lt hdvd hlt
  | succ t ih =>
    rw [multMask, dbl, Nat.testBit_lor, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_iff, ih, ih]
    have hs : d ∣ d * 2 ^ t := dvd_mul_right d _
    have hpow : d * 2 ^ (t + 1) = d * 2 ^ t + d * 2 ^ t := by ring
    rw [hpow]
    constructor
    · rintro (⟨hdvd, hlt⟩ | ⟨hle, hdvd, hlt⟩)
      · exact ⟨hdvd, by omega⟩
      · refine ⟨?_, by omega⟩
        have h := Nat.dvd_add hdvd hs
        rwa [Nat.sub_add_cancel hle] at h
    · rintro ⟨hdvd, hlt⟩
      by_cases hle : d * 2 ^ t ≤ i
      · right
        exact ⟨hle, Nat.dvd_sub hdvd hs, by omega⟩
      · left
        exact ⟨hdvd, by omega⟩

/-- The bits of `B` not in `M`. -/
def clear (B M : ℕ) : ℕ := B ^^^ (B &&& M)

theorem testBit_clear (B M i : ℕ) :
    (clear B M).testBit i = (B.testBit i && !M.testBit i) := by
  rw [clear, Nat.testBit_xor, Nat.testBit_land]
  cases B.testBit i <;> cases M.testBit i <;> rfl

/-! ## A windowed sieve of Eratosthenes on bitmasks -/

/-- The number of doublings after which `d * 2 ^ t` exceeds `S`. -/
def tB (S d : ℕ) : ℕ := Nat.log2 (S / d) + 1

theorem lt_mul_two_pow_tB {S d : ℕ} (hd : 0 < d) : S < d * 2 ^ tB S d := by
  have h1 : S / d < 2 ^ tB S d := Nat.lt_log2_self
  have h2 : S < d * (S / d + 1) := Nat.lt_mul_div_succ S hd
  calc S < d * (S / d + 1) := h2
    _ ≤ d * 2 ^ tB S d := Nat.mul_le_mul_left d h1

/-- The least multiple of `d` that is at least `max lo (2 * d)`. -/
def firstMult (lo d : ℕ) : ℕ := (max lo (2 * d) + d - 1) / d * d

theorem dvd_firstMult (lo d : ℕ) : d ∣ firstMult lo d := Dvd.intro_left _ rfl

theorem le_firstMult {lo d : ℕ} (hd : 0 < d) : max lo (2 * d) ≤ firstMult lo d := by
  set m := max lo (2 * d)
  have hdm := Nat.div_add_mod (m + d - 1) d
  have hmod := Nat.mod_lt (m + d - 1) hd
  rw [firstMult, Nat.mul_comm]
  set q := (m + d - 1) / d
  set r := (m + d - 1) % d
  omega

theorem firstMult_le {lo d x : ℕ} (hd : 0 < d) (hdx : d ∣ x) (hx : max lo (2 * d) ≤ x) :
    firstMult lo d ≤ x := by
  obtain ⟨y, rfl⟩ := hdx
  rw [firstMult, Nat.mul_comm d y]
  apply Nat.mul_le_mul_right
  · rw [Nat.div_le_iff_le_mul_add_pred hd]
    set m := max lo (2 * d)
    set z := d * y
    omega

/-- One sieve step on the window `[lo, lo + S)`: clear the multiples `x` of `d` with
`2 * d ≤ x`. -/
def stepW (lo S d B : ℕ) : ℕ := clear B (multMask d (tB S d) <<< (firstMult lo d - lo))

theorem testBit_stepW {lo S d B i : ℕ} (hd : 0 < d) (hi : i < S) :
    (stepW lo S d B).testBit i = true ↔
      B.testBit i = true ∧ ¬ (2 * d ≤ lo + i ∧ d ∣ lo + i) := by
  rw [stepW, testBit_clear, Bool.and_eq_true, Bool.not_eq_true', Nat.testBit_shiftLeft,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, Bool.eq_false_iff, ne_eq,
    testBit_multMask hd]
  have hc := le_firstMult (lo := lo) hd
  have hcd := dvd_firstMult lo d
  have hS := lt_mul_two_pow_tB (S := S) hd
  rw [max_le_iff] at hc
  apply and_congr_right
  intro _
  constructor
  · rintro (hlt | hnot) ⟨h2d, hdvd⟩
    · have hle := firstMult_le (lo := lo) hd hdvd (max_le_iff.mpr ⟨by omega, h2d⟩)
      omega
    · apply hnot
      have hle := firstMult_le (lo := lo) hd hdvd (max_le_iff.mpr ⟨by omega, h2d⟩)
      refine ⟨?_, by omega⟩
      have h := Nat.dvd_sub hdvd hcd
      rwa [show lo + i - firstMult lo d = i - (firstMult lo d - lo) by omega] at h
  · intro hnot
    by_cases hlt : i < firstMult lo d - lo
    · left; omega
    · right
      rintro ⟨hdvd, _⟩
      apply hnot
      refine ⟨by omega, ?_⟩
      have h := Nat.dvd_add hdvd hcd
      rwa [show i - (firstMult lo d - lo) + firstMult lo d = lo + i by omega] at h

/-- The window `[lo, lo + S)` with the integers below `2` removed. -/
def initW (lo S : ℕ) : ℕ := (2 ^ S - 1) ^^^ (2 ^ (2 - lo) - 1)

theorem testBit_initW {lo S i : ℕ} (hi : i < S) :
    (initW lo S).testBit i = true ↔ 2 ≤ lo + i := by
  rw [initW, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one,
    decide_eq_true hi, Bool.true_xor, Bool.not_eq_true', decide_eq_false_iff_not]
  omega

/-- The sieve of the window `[lo, lo + S)` by the list `ds`: bit `i` stands for `lo + i`. -/
def sieveW (lo S : ℕ) (ds : List ℕ) : ℕ := ds.foldl (fun B d => stepW lo S d B) (initW lo S)

theorem testBit_foldl_stepW {lo S i : ℕ} (hi : i < S) (ds : List ℕ) (hds : ∀ d ∈ ds, 0 < d) :
    ∀ B : ℕ, (ds.foldl (fun B d => stepW lo S d B) B).testBit i = true ↔
      B.testBit i = true ∧ ∀ d ∈ ds, ¬ (2 * d ≤ lo + i ∧ d ∣ lo + i) := by
  induction ds with
  | nil => intro B; simp
  | cons d ds ih =>
    intro B
    rw [List.foldl_cons, ih (fun e he => hds e (List.mem_cons_of_mem d he)),
      testBit_stepW (hds d List.mem_cons_self) hi, List.forall_mem_cons, and_assoc]

theorem testBit_sieveW {lo S i : ℕ} (hi : i < S) (ds : List ℕ) (hds : ∀ d ∈ ds, 0 < d) :
    (sieveW lo S ds).testBit i = true ↔
      2 ≤ lo + i ∧ ∀ d ∈ ds, ¬ (2 * d ≤ lo + i ∧ d ∣ lo + i) := by
  rw [sieveW, testBit_foldl_stepW hi ds hds, testBit_initW hi]

theorem sieve_cond_iff_prime {N x : ℕ} (hx : x < N) (ds : List ℕ)
    (hall : ∀ p : ℕ, p.Prime → p * p < N → p ∈ ds) (hds : ∀ d ∈ ds, 2 ≤ d) :
    (2 ≤ x ∧ ∀ d ∈ ds, ¬ (2 * d ≤ x ∧ d ∣ x)) ↔ x.Prime := by
  constructor
  · rintro ⟨h2, hnone⟩
    by_contra hnp
    have hx1 : x ≠ 1 := by omega
    have hq := Nat.minFac_prime hx1
    have hsq : x.minFac ^ 2 ≤ x := Nat.minFac_sq_le_self (by omega) hnp
    have hmem : x.minFac ∈ ds := hall _ hq (by nlinarith)
    apply hnone _ hmem
    refine ⟨?_, Nat.minFac_dvd x⟩
    obtain ⟨y, hy⟩ := Nat.minFac_dvd x
    have hy2 : 2 ≤ y := by
      by_contra hy2
      interval_cases y
      · omega
      · rw [mul_one] at hy
        exact hnp (hy ▸ hq)
    nlinarith
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    rintro d hd ⟨h2d, hdvd⟩
    rcases hp.eq_one_or_self_of_dvd d hdvd with h1 | hself
    · have := hds d hd
      omega
    · have := hp.two_le
      omega

/-! ## Population count by SWAR -/

/-- The sum of the first `L` base-`2 ^ w` digits of `x`. -/
def dsum (w : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | L + 1, x => x % 2 ^ w + dsum w L (x / 2 ^ w)

/-- `(q ^ L - 1) / (q - 1) = 1 + q + ... + q ^ (L - 1)`. -/
theorem geo_succ {q : ℕ} (hq : 2 ≤ q) (L : ℕ) :
    (q ^ (L + 1) - 1) / (q - 1) = q * ((q ^ L - 1) / (q - 1)) + 1 := by
  obtain ⟨s, hs⟩ : q - 1 ∣ q ^ L - 1 := by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 L
  have h1 : 1 ≤ q ^ L := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ (L + 1) := Nat.one_le_pow _ _ (by omega)
  have hpos : 0 < q - 1 := by omega
  have key : q ^ (L + 1) - 1 = (q - 1) * (q * s + 1) := by
    zify [h1, h2, (by omega : 1 ≤ q)] at hs ⊢
    rw [pow_succ]
    linear_combination (q : ℤ) * hs
  rw [key, hs, Nat.mul_div_cancel_left _ hpos, Nat.mul_div_cancel_left _ hpos]

/-- The mask selecting the low `w` bits of each of `L` consecutive `2 * w`-bit fields,
in closed form. -/
def evenMask (w L : ℕ) : ℕ := (2 ^ w - 1) * (((2 ^ (2 * w)) ^ L - 1) / (2 ^ (2 * w) - 1))

theorem evenMask_succ (w L : ℕ) :
    evenMask w (L + 1) = 2 ^ (2 * w) * evenMask w L + (2 ^ w - 1) := by
  have hq : 2 ≤ 2 ^ (2 * w) ∨ w = 0 := by
    rcases Nat.eq_zero_or_pos w with h | h
    · exact Or.inr h
    · left
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases hq with hq | rfl
  · rw [evenMask, evenMask, geo_succ hq]
    ring
  · simp [evenMask]

/-- One SWAR step: add adjacent `w`-bit fields into `2 * w`-bit fields. -/
def swar (w L x : ℕ) : ℕ := (x &&& evenMask w L) + ((x >>> w) &&& evenMask w L)

theorem land_evenMask_succ (w L x : ℕ) :
    x &&& evenMask w (L + 1) = 2 ^ (2 * w) * ((x / 2 ^ (2 * w)) &&& evenMask w L) + x % 2 ^ w := by
  have hpow : 2 ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h1 : 2 ^ w - 1 < 2 ^ (2 * w) := by have := Nat.one_le_two_pow (n := w); omega
  have h2 : x % 2 ^ w < 2 ^ (2 * w) := lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hpow
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, evenMask_succ, Nat.testBit_two_pow_mul_add _ h1,
    Nat.testBit_two_pow_mul_add _ h2]
  split_ifs with hj
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Bool.and_comm]
  · rw [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]

theorem swar_succ (w L x : ℕ) :
    swar w (L + 1) x =
      2 ^ (2 * w) * swar w L (x / 2 ^ (2 * w)) + (x % 2 ^ w + x / 2 ^ w % 2 ^ w) := by
  have hshift : x >>> w / 2 ^ (2 * w) = (x / 2 ^ (2 * w)) >>> w := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [swar, swar, land_evenMask_succ, land_evenMask_succ, hshift, Nat.shiftRight_eq_div_pow x w]
  ring

theorem dsum_swar {w : ℕ} (hw : 0 < w) (L : ℕ) :
    ∀ x : ℕ, dsum (2 * w) L (swar w L x) = dsum w (2 * L) x := by
  induction L with
  | zero => intro x; rfl
  | succ L ih =>
    intro x
    have hd0 : x % 2 ^ w < 2 ^ w := Nat.mod_lt _ (by positivity)
    have hd1 : x / 2 ^ w % 2 ^ w < 2 ^ w := Nat.mod_lt _ (by positivity)
    have hpow : 2 ^ w + 2 ^ w ≤ 2 ^ (2 * w) := by
      rw [← two_mul, ← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hr : x % 2 ^ w + x / 2 ^ w % 2 ^ w < 2 ^ (2 * w) := by omega
    have hdiv : x / 2 ^ w / 2 ^ w = x / 2 ^ (2 * w) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add, two_mul]
    rw [swar_succ, show 2 * (L + 1) = 2 * L + 1 + 1 by ring, dsum, dsum, dsum,
      Nat.add_comm (2 ^ (2 * w) * _), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hr, zero_add, ih, hdiv, add_assoc]

theorem dsum_swar' {w w2 L L2 : ℕ} (hw : 0 < w) (hw2 : w2 = 2 * w) (hL2 : L2 = 2 * L)
    (x : ℕ) : dsum w2 L (swar w L x) = dsum w L2 x := by
  rw [hw2, hL2, dsum_swar hw]

def pc (x : ℕ) : ℕ := (swar 131072 1 (swar 65536 2 (swar 32768 4 (swar 16384 8 (swar 8192 16 (swar 4096 32 (swar 2048 64 (swar 1024 128 (swar 512 256 (swar 256 512 (swar 128 1024 (swar 64 2048 (swar 32 4096 (swar 16 8192 (swar 8 16384 (swar 4 32768 (swar 2 65536 (swar 1 131072 x)))))))))))))))))) % 2 ^ 262144

theorem pc_eq_dsum (x : ℕ) : pc x = dsum 1 262144 x := by
  have h : pc x = dsum 262144 1 (swar 131072 1 (swar 65536 2 (swar 32768 4 (swar 16384 8 (swar 8192 16 (swar 4096 32 (swar 2048 64 (swar 1024 128 (swar 512 256 (swar 256 512 (swar 128 1024 (swar 64 2048 (swar 32 4096 (swar 16 8192 (swar 8 16384 (swar 4 32768 (swar 2 65536 (swar 1 131072 x)))))))))))))))))) := by rw [pc, dsum, dsum, add_zero]
  rw [h,
    dsum_swar' (w := 131072) (w2 := 262144) (L := 1) (L2 := 2) (by norm_num) rfl rfl,
    dsum_swar' (w := 65536) (w2 := 131072) (L := 2) (L2 := 4) (by norm_num) rfl rfl,
    dsum_swar' (w := 32768) (w2 := 65536) (L := 4) (L2 := 8) (by norm_num) rfl rfl,
    dsum_swar' (w := 16384) (w2 := 32768) (L := 8) (L2 := 16) (by norm_num) rfl rfl,
    dsum_swar' (w := 8192) (w2 := 16384) (L := 16) (L2 := 32) (by norm_num) rfl rfl,
    dsum_swar' (w := 4096) (w2 := 8192) (L := 32) (L2 := 64) (by norm_num) rfl rfl,
    dsum_swar' (w := 2048) (w2 := 4096) (L := 64) (L2 := 128) (by norm_num) rfl rfl,
    dsum_swar' (w := 1024) (w2 := 2048) (L := 128) (L2 := 256) (by norm_num) rfl rfl,
    dsum_swar' (w := 512) (w2 := 1024) (L := 256) (L2 := 512) (by norm_num) rfl rfl,
    dsum_swar' (w := 256) (w2 := 512) (L := 512) (L2 := 1024) (by norm_num) rfl rfl,
    dsum_swar' (w := 128) (w2 := 256) (L := 1024) (L2 := 2048) (by norm_num) rfl rfl,
    dsum_swar' (w := 64) (w2 := 128) (L := 2048) (L2 := 4096) (by norm_num) rfl rfl,
    dsum_swar' (w := 32) (w2 := 64) (L := 4096) (L2 := 8192) (by norm_num) rfl rfl,
    dsum_swar' (w := 16) (w2 := 32) (L := 8192) (L2 := 16384) (by norm_num) rfl rfl,
    dsum_swar' (w := 8) (w2 := 16) (L := 16384) (L2 := 32768) (by norm_num) rfl rfl,
    dsum_swar' (w := 4) (w2 := 8) (L := 32768) (L2 := 65536) (by norm_num) rfl rfl,
    dsum_swar' (w := 2) (w2 := 4) (L := 65536) (L2 := 131072) (by norm_num) rfl rfl,
    dsum_swar' (w := 1) (w2 := 2) (L := 131072) (L2 := 262144) (by norm_num) rfl rfl]

theorem dsum_one_eq_count (L : ℕ) :
    ∀ x : ℕ, dsum 1 L x = Nat.count (fun i => x.testBit i = true) L := by
  induction L with
  | zero => intro x; rfl
  | succ L ih =>
    intro x
    rw [dsum, Nat.count_succ', ih, pow_one]
    simp only [Nat.testBit_div_two]
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h, add_comm]

theorem count_lt_and {len M : ℕ} (q : ℕ → Prop) [DecidablePred q] (h : len ≤ M) :
    Nat.count (fun i => i < len ∧ q i) M = Nat.count q len := by
  induction M, h using Nat.le_induction with
  | base =>
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    congr 1
    apply Finset.filter_congr
    intro i hi
    rw [Finset.mem_range] at hi
    simp [hi]
  | succ M hM ih =>
    rw [Nat.count_succ, ih]
    simp only [show ¬ M < len by omega, false_and, if_false, add_zero]

/-- The number of set bits of `B` at positions `a, ..., a + len - 1`, for `len ≤ 262144`. -/
def segCount (B a len : ℕ) : ℕ := pc ((B >>> a) % 2 ^ len)

theorem segCount_eq {len : ℕ} (B a : ℕ) (hlen : len ≤ 262144) :
    segCount B a len = Nat.count (fun i => B.testBit (a + i) = true) len := by
  rw [segCount, pc_eq_dsum, dsum_one_eq_count, ← count_lt_and _ hlen]
  congr 1
  funext i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Bool.and_eq_true, decide_eq_true_iff]

/-! ## Certified tables of prime counts -/

theorem count_congr_lt {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] {n : ℕ}
    (h : ∀ i < n, p i ↔ q i) : Nat.count p n = Nat.count q n := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  intro i hi
  exact h i (Finset.mem_range.mp hi)

/-! ## The sieving primes: the primes below `9487` -/

/-- The prime bitmask of `[0, 9487)`, sieved by `2, ..., 97`. -/
def smallSieve : ℕ := sieveW 0 9487 (List.range' 2 96)

theorem testBit_smallSieve {i : ℕ} (hi : i < 9487) : smallSieve.testBit i = true ↔ i.Prime := by
  have hpos : ∀ d ∈ List.range' 2 96, 0 < d := by
    intro d hd
    rw [List.mem_range'_1] at hd
    omega
  have hall : ∀ p : ℕ, p.Prime → p * p < 9487 → p ∈ List.range' 2 96 := by
    intro p hp hpp
    have h2 := hp.two_le
    rw [List.mem_range'_1]
    constructor
    · exact h2
    · nlinarith
  have h2 : ∀ d ∈ List.range' 2 96, 2 ≤ d := by
    intro d hd
    rw [List.mem_range'_1] at hd
    omega
  rw [smallSieve, testBit_sieveW hi _ hpos,
    sieve_cond_iff_prime (by omega : 0 + i < 9487) _ hall h2, zero_add]


/-- The primes below `9487`. -/
def ds : List ℕ := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
  59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
  137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223,
  227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311,
  313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
  419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
  509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613,
  617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719,
  727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827,
  829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
  947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049,
  1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163,
  1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283,
  1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423,
  1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511,
  1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619,
  1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747,
  1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877,
  1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003,
  2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129,
  2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267,
  2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377,
  2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503,
  2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657,
  2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741,
  2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861,
  2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011,
  3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167,
  3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301,
  3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413,
  3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541,
  3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671,
  3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797,
  3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923,
  3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057,
  4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211,
  4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337,
  4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481,
  4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621,
  4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751,
  4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909,
  4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011,
  5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167,
  5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309,
  5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443,
  5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573,
  5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711,
  5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849,
  5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007,
  6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133,
  6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271,
  6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379,
  6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563,
  6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701,
  6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833,
  6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971,
  6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121,
  7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253,
  7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457,
  7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561,
  7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691,
  7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853,
  7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009,
  8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161,
  8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291,
  8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443,
  8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609,
  8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731,
  8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861,
  8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011,
  9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161,
  9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311,
  9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433,
  9437, 9439, 9461, 9463, 9467, 9473, 9479]

theorem ds_eq : ds = (List.range 9487).filter (fun p => smallSieve.testBit p) := by
  decide +kernel

theorem mem_ds {p : ℕ} : p ∈ ds ↔ p < 9487 ∧ p.Prime := by
  rw [ds_eq, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hp, hbit⟩
    exact ⟨hp, (testBit_smallSieve hp).mp hbit⟩
  · rintro ⟨hp, hprime⟩
    exact ⟨hp, (testBit_smallSieve hp).mpr hprime⟩

/-- Sieving by `ds` is exact below `9487 ^ 2`. -/
def NMax : ℕ := 9487 * 9487

theorem testBit_sieveW_ds {lo S : ℕ} (hN : lo + S ≤ NMax) :
    ∀ i < S, (sieveW lo S ds).testBit i = true ↔ (lo + i).Prime := by
  intro i hi
  have hpos : ∀ d ∈ ds, 0 < d := fun d hd => (mem_ds.mp hd).2.pos
  have h2 : ∀ d ∈ ds, 2 ≤ d := fun d hd => (mem_ds.mp hd).2.two_le
  have hall : ∀ p : ℕ, p.Prime → p * p < NMax → p ∈ ds := by
    intro p hp hpp
    refine mem_ds.mpr ⟨?_, hp⟩
    by_contra hbig
    unfold NMax at hpp
    nlinarith
  rw [testBit_sieveW hi _ hpos, sieve_cond_iff_prime (by omega : lo + i < NMax) _ hall h2]


def claimAt (p : ℕ) : Prop :=
  ∃ h : ℕ, 0 < h ∧ 2 ^ h ≤ p ^ 256 ∧
    let u := 693147 * h
    let v := 256000000
    p * u * v + p.primeCounting * (u * v + v ^ 2) ≤ p.primeCounting * u ^ 2

def endpoint (l r count h : ℕ) : Prop :=
  0 < h ∧ 2^h ≤ l^256 ∧
    let u := 693147*h
    let v := 256000000
    u*v+v^2 ≤ u^2 ∧ r*(u*v) ≤ count*(u^2-(u*v+v^2))

theorem certify {l r c h p : ℕ} (e : endpoint l r c h)
    (hl : l ≤ p) (hr : p ≤ r) (hc : c ≤ p.primeCounting) : claimAt p := by
  obtain ⟨hp, power, sub, ineq⟩ := e
  refine ⟨h,hp,power.trans (Nat.pow_le_pow_left hl 256),?_⟩
  dsimp only
  let u := 693147*h
  let v := 256000000
  change p*u*v + p.primeCounting*(u*v+v^2) ≤ p.primeCounting*u^2
  have a : p*(u*v) ≤ p.primeCounting*(u^2-(u*v+v^2)) :=
    (Nat.mul_le_mul_right _ hr).trans (ineq.trans (Nat.mul_le_mul_right _ hc))
  calc
    _ = p*(u*v) + p.primeCounting*(u*v+v^2) := by rw [Nat.mul_assoc p]
    _ ≤ p.primeCounting*(u^2-(u*v+v^2)) + p.primeCounting*(u*v+v^2) := Nat.add_le_add_right a _
    _ = _ := by rw [← Nat.mul_add, Nat.sub_add_cancel sub]


instance (l r c h : ℕ) : Decidable (endpoint l r c h) := by unfold endpoint; infer_instance

/-- A certificate records the width and binary logarithm witness for each subinterval. -/
def checkCuts (pop : ℕ → ℕ → ℕ) (lo width final : ℕ) :
    ℕ → ℕ → List (ℕ × ℕ) → Bool
  | i, c, [] => i == width && c == final
  | i, c, (len,h) :: rest =>
    decide (i + len ≤ width) &&
      (decide (lo+i+len ≤ 1772201) || decide (endpoint (lo+i) (lo+i+len-1) c h)) &&
      checkCuts pop lo width final (i+len) (c+pop i len) rest

def RangeResult (lo hi a b : ℕ) : Prop :=
  Nat.count Nat.Prime lo = a →
    Nat.count Nat.Prime hi = b ∧ ∀ p, 1772201 ≤ p → lo ≤ p → p < hi → claimAt p

theorem cuts_sound {pop : ℕ → ℕ → ℕ} {lo width b : ℕ}
    (addCount : ∀ i len, i+len ≤ width →
      Nat.count Nat.Prime (lo+(i+len)) = Nat.count Nat.Prime (lo+i) + pop i len)
    (xs : List (ℕ × ℕ)) (i c : ℕ)
    (hc : checkCuts pop lo width b i c xs = true) : RangeResult (lo+i) (lo+width) c b := by
  induction xs generalizing i c with
  | nil =>
    simp only [checkCuts, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl,rfl⟩ := hc
    intro h
    exact ⟨h,by intros; omega⟩
  | cons x rest ih =>
    rcases x with ⟨len,h⟩
    simp only [checkCuts, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨fit,check⟩,tail⟩ := hc
    intro start
    have next := addCount i len fit
    rw [start] at next
    obtain ⟨last,later⟩ := ih (i+len) (c+pop i len) tail next
    refine ⟨last,?_⟩
    intro p low left right
    by_cases after : lo+(i+len) ≤ p
    · exact later p low after right
    · rcases check with small | bound
      · omega
      · apply certify bound left (by omega)
        change c ≤ Nat.primeCounting' (p+1)
        rw [← start]
        exact Nat.monotone_primeCounting' (by omega)

theorem join_result {lo mid hi a b c : ℕ} (h : RangeResult lo mid a b)
    (k : RangeResult mid hi b c) : RangeResult lo hi a c := by
  intro start
  obtain ⟨middle,first⟩ := h start
  obtain ⟨last,second⟩ := k middle
  exact ⟨last, fun p low left right => by
    by_cases e : p < mid
    · exact first p low left e
    · exact second p low (by omega) right⟩

theorem oneBlock (lo w a b : ℕ) (xs : List (ℕ × ℕ))
    (size : w ≤ 262144) (bound : lo+w ≤ NMax)
    (checked : checkCuts (segCount (sieveW lo w ds)) lo w b 0 a xs = true) :
    RangeResult lo (lo+w) a b := by
  have inc (i len : ℕ) (hi : i+len ≤ w) :
      Nat.count Nat.Prime (lo+(i+len)) =
      Nat.count Nat.Prime (lo+i) + segCount (sieveW lo w ds) i len := by
    rw [← Nat.add_assoc, Nat.count_add Nat.Prime (lo+i) len, segCount_eq _ _ (by omega)]
    congr 1
    exact count_congr_lt (fun t ht => by
      simpa [Nat.add_assoc] using (testBit_sieveW_ds bound (i+t) (by omega)).symm)
  simpa only [Nat.add_zero] using cuts_sound inc xs 0 a checked

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block0 : PLift (RangeResult 0 262144 0 23000) :=
  ⟨oneBlock 0 262144 0 23000 [
    (262144,0)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block1 : PLift (RangeResult 262144 524288 23000 43390) :=
  ⟨oneBlock 262144 262144 23000 43390 [
    (262144,0)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block2 : PLift (RangeResult 524288 786432 43390 62946) :=
  ⟨oneBlock 524288 262144 43390 62946 [
    (262144,0)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block3 : PLift (RangeResult 786432 1048576 62946 82025) :=
  ⟨oneBlock 786432 262144 62946 82025 [
    (262144,0)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block4 : PLift (RangeResult 1048576 1310720 82025 100786) :=
  ⟨oneBlock 1048576 262144 82025 100786 [
    (262144,0)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block5 : PLift (RangeResult 1310720 1572864 100786 119268) :=
  ⟨oneBlock 1310720 262144 100786 119268 [
    (262144,0)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block6 : PLift (RangeResult 1572864 1835008 119268 137524) :=
  ⟨oneBlock 1572864 262144 119268 137524 [
    (199337,0),(345,5313),(346,5313),(346,5313),(669,5314),(719,5314),(732,5314),(626,5314),
    (613,5314),(559,5314),(533,5314),(373,5314),(776,5315),(800,5315),(732,5315),(746,5315),
    (733,5315),(666,5315),(573,5315),(950,5316),(893,5316),(786,5316),(720,5316),(586,5316),
    (599,5316),(965,5317),(826,5317),(680,5317),(587,5317),(599,5317),(560,5317),(520,5317),
    (573,5317),(846,5318),(813,5318),(706,5318),(733,5318),(747,5318),(573,5318),(887,5319),
    (826,5319),(894,5319),(826,5319),(787,5319),(693,5319),(1008,5320),(880,5320),(760,5320),
    (654,5320),(653,5320),(667,5320),(693,5320),(1036,5321),(934,5321),(960,5321),(920,5321),
    (800,5321),(1091,5322),(920,5322),(907,5322),(841,5322),(880,5322),(1104,5323),(881,5323),
    (814,5323),(641,5323),(640,5323),(667,5323),(587,5323),(879,5324),(814,5324),(841,5324),
    (854,5324),(814,5324),(801,5324),(1160,5325),(1041,5325),(961,5325),(975,5325),(947,5325),
    (1362,5326),(1161,5326),(197,5326)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block7 : PLift (RangeResult 1835008 2097152 137524 155611) :=
  ⟨oneBlock 1835008 262144 137524 155611 [
    (1125,5326),(921,5326),(1096,5327),(975,5327),(788,5327),(694,5327),(641,5327),(561,5327),
    (896,5328),(882,5328),(921,5328),(868,5328),(802,5328),(734,5328),(1071,5329),(1029,5329),
    (868,5329),(909,5329),(668,5329),(628,5329),(1112,5330),(949,5330),(908,5330),(976,5330),
    (1029,5330),(1233,5331),(1189,5331),(1083,5331),(1002,5331),(923,5331),(1234,5332),(1217,5332),
    (1109,5332),(1163,5332),(1490,5333),(1457,5333),(1217,5333),(1096,5333),(1425,5334),(1297,5334),
    (1190,5334),(1163,5334),(1466,5335),(1364,5335),(1150,5335),(1218,5335),(1453,5336),(1257,5336),
    (1178,5336),(1137,5336),(1481,5337),(1298,5337),(1338,5337),(1191,5337),(1563,5338),(1432,5338),
    (1285,5338),(1604,5339),(1486,5339),(1271,5339),(1071,5339),(1391,5340),(1299,5340),(1138,5340),
    (1018,5340),(1338,5341),(1313,5341),(1299,5341),(1218,5341),(1554,5342),(1393,5342),(1393,5342),
    (1353,5342),(1689,5343),(1354,5343),(1339,5343),(1153,5343),(1502,5344),(1367,5344),(1367,5344),
    (1394,5344),(1732,5345),(1581,5345),(1461,5345),(1653,5346),(1475,5346),(1354,5346),(1627,5347),
    (1636,5347),(1582,5347),(1461,5347),(1709,5348),(1730,5348),(1623,5348),(1777,5349),(1556,5349),
    (1489,5349),(1859,5350),(1664,5350),(1382,5350),(1726,5351),(1624,5351),(1596,5351),(1369,5351),
    (1567,5352),(1436,5352),(1275,5352),(1527,5353),(1262,5353),(1168,5353),(993,5353),(873,5353),
    (1126,5354),(1074,5354),(1034,5354),(1020,5354),(967,5354),(1328,5355),(1330,5355),(1222,5355),
    (1074,5355),(967,5355),(1343,5356),(1276,5356),(1062,5356),(1020,5356),(1398,5357),(1330,5357),
    (1183,5357),(1074,5357),(1183,5357),(1587,5358),(1411,5358),(1277,5358),(1182,5358),(1522,5359),
    (1451,5359),(1317,5359),(1385,5359),(1684,5360),(1559,5360),(1372,5360),(1806,5361),(1761,5361),
    (1614,5361),(1888,5362),(1788,5362),(1655,5362),(1916,5363),(1628,5363),(1641,5363),(1547,5363),
    (1743,5364),(1776,5364),(1722,5364),(1932,5365),(1736,5365),(1669,5365),(1799,5366),(1844,5366),
    (1562,5366),(1921,5367),(1602,5367),(1481,5367),(1802,5368),(1589,5368),(1494,5368),(1361,5368),
    (1749,5369),(1683,5369),(1455,5369),(1333,5369),(1872,5370),(1684,5370),(1455,5370),(1819,5371),
    (1738,5371),(1604,5371),(1766,5372),(1604,5372),(1401,5372),(1402,5372),(1687,5373),(1442,5373),
    (1389,5373),(1240,5373),(1607,5374),(1537,5374),(1483,5374),(1281,5374),(1690,5375),(1564,5375),
    (1203,5375)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block8 : PLift (RangeResult 2097152 2359296 155611 173514) :=
  ⟨oneBlock 2097152 262144 155611 173514 [
    (1634,5376),(1524,5376),(1417,5376),(1375,5376),(1706,5377),(1605,5377),(1552,5377),(1389,5377),
    (1788,5378),(1633,5378),(1376,5378),(1309,5378),(1695,5379),(1660,5379),(1539,5379),(1817,5380),
    (1566,5380),(1363,5380),(1269,5380),(1684,5381),(1607,5381),(1566,5381),(1350,5381),(1753,5382),
    (1553,5382),(1364,5382),(1391,5382),(1714,5383),(1553,5383),(1472,5383),(1783,5384),(1864,5384),
    (1621,5384),(1500,5384),(1730,5385),(1594,5385),(1541,5385),(1866,5386),(1811,5386),(1838,5386),
    (1770,5386),(2031,5387),(1879,5387),(1662,5387),(1789,5388),(1771,5388),(1555,5388),(2073,5389),
    (1771,5389),(1745,5389),(2088,5390),(1867,5390),(1636,5390),(1914,5391),(1813,5391),(1596,5391),
    (1637,5391),(1943,5392),(1799,5392),(1638,5392),(1957,5393),(1746,5393),(1367,5393),(1340,5393),
    (1606,5394),(1584,5394),(1394,5394),(1517,5394),(1770,5395),(1896,5395),(1679,5395),(1758,5396),
    (1612,5396),(1489,5396),(1287,5396),(1583,5397),(1328,5397),(1273,5397),(1205,5397),(1640,5398),
    (1585,5398),(1544,5398),(1436,5398),(1722,5399),(1599,5399),(1545,5399),(1490,5399),(1764,5400),
    (1586,5400),(1504,5400),(1288,5400),(1589,5401),(1599,5401),(1383,5401),(1383,5401),(1577,5402),
    (1396,5402),(1342,5402),(1261,5402),(1220,5402),(1674,5403),(1681,5403),(1628,5403),(1823,5404),
    (1709,5404),(1614,5404),(1587,5404),(1988,5405),(1954,5405),(1954,5405),(2369,5406),(2022,5406),
    (1899,5406),(2181,5407),(1737,5407),(1534,5407),(1452,5407),(1843,5408),(1724,5408),(1616,5408),
    (1966,5409),(1765,5409),(1603,5409),(1507,5409),(1968,5410),(1928,5410),(1738,5410),(1956,5411),
    (1820,5411),(1793,5411),(1671,5411),(1863,5412),(1671,5412),(1589,5412),(1782,5413),(1712,5413),
    (1441,5413),(1331,5413),(1662,5414),(1467,5414),(1441,5414),(1400,5414),(1169,5414),(1459,5415),
    (1345,5415),(1455,5415),(1291,5415),(1705,5416),(1496,5416),(1319,5416),(1291,5416),(1197,5416),
    (1570,5417),(1415,5417),(1101,5417),(1115,5417),(1061,5417),(1409,5418),(1264,5418),(1170,5418),
    (1129,5418),(1088,5418),(1356,5419),(1251,5419),(232,5419)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block9 : PLift (RangeResult 2359296 2621440 173514 191308) :=
  ⟨oneBlock 2359296 262144 173514 191308 [
    (1251,5419),(1170,5419),(1007,5419),(1398,5420),(1415,5420),(1401,5420),(1279,5420),(1184,5420),
    (1590,5421),(1470,5421),(1266,5421),(1252,5421),(966,5421),(1360,5422),(1320,5422),(1171,5422),
    (1102,5422),(1048,5422),(1538,5423),(1444,5423),(1307,5423),(1184,5423),(1185,5423),(1607,5424),
    (1634,5424),(1444,5424),(1280,5424),(1144,5424),(1364,5425),(1348,5425),(1430,5425),(1362,5425),
    (1665,5426),(1485,5426),(1431,5426),(1335,5426),(1144,5426),(1530,5427),(1349,5427),(1227,5427),
    (1062,5427),(1009,5427),(1545,5428),(1335,5428),(1322,5428),(1268,5428),(1226,5428),(1588,5429),
    (1595,5429),(1349,5429),(1186,5429),(1159,5429),(1548,5430),(1418,5430),(1241,5430),(1104,5430),
    (995,5430),(1413,5431),(1378,5431),(1200,5431),(981,5431),(901,5431),(777,5431),(1373,5432),
    (1214,5432),(1064,5432),(1078,5432),(1077,5432),(969,5432),(1347,5433),(1296,5433),(1255,5433),
    (1105,5433),(1160,5433),(1635,5434),(1447,5434),(1310,5434),(1160,5434),(1173,5434),(1664,5435),
    (1474,5435),(1351,5435),(1393,5435),(1228,5435),(1570,5436),(1365,5436),(1242,5436),(1188,5436),
    (1119,5436),(1422,5437),(1256,5437),(1215,5437),(1120,5437),(955,5437),(942,5437),(1396,5438),
    (1243,5438),(1106,5438),(983,5438),(970,5438),(1024,5438),(1520,5439),(1352,5439),(1325,5439),
    (1093,5439),(915,5439),(1330,5440),(1284,5440),(1189,5440),(1174,5440),(1025,5440),(1025,5440),
    (1372,5441),(1394,5441),(1216,5441),(1202,5441),(1080,5441),(1038,5441),(1497,5442),(1271,5442),
    (1258,5442),(1175,5442),(1121,5442),(1567,5443),(1421,5443),(1162,5443),(998,5443),(971,5443),
    (902,5443),(1308,5444),(1272,5444),(1340,5444),(1381,5444),(1271,5444),(1501,5445),(1546,5445),
    (1504,5445),(1436,5445),(1217,5445),(1722,5446),(1463,5446),(1382,5446),(1176,5446),(1094,5446),
    (1450,5447),(1354,5447),(1286,5447),(1231,5447),(944,5447),(1424,5448),(1395,5448),(1177,5448),
    (1122,5448),(1108,5448),(1095,5448),(1507,5449),(1300,5449),(1191,5449),(1122,5449),(1095,5449),
    (1027,5449),(1481,5450),(1437,5450),(1123,5450),(1026,5450),(1096,5450),(1523,5451),(1424,5451),
    (1342,5451),(1232,5451),(1164,5451),(1136,5451),(1649,5452),(1643,5452),(1370,5452),(1492,5452),
    (1965,5453),(1822,5453),(1698,5453),(1534,5453),(1940,5454),(1781,5454),(1589,5454),(1616,5454),
    (1452,5454),(1845,5455),(1768,5455),(1548,5455),(1343,5455),(1751,5456),(1549,5456),(1370,5456),
    (1261,5456),(1220,5456),(1642,5457),(1494,5457),(1481,5457),(1466,5457),(1371,5457),(1606,5458)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block10 : PLift (RangeResult 2621440 2883584 191308 209014) :=
  ⟨oneBlock 2621440 262144 191308 209014 [
    (1478,5458),(1385,5458),(1343,5458),(1810,5459),(1522,5459),(1317,5459),(1275,5459),(1399,5459),
    (1921,5460),(1811,5460),(1550,5460),(1330,5460),(1221,5460),(1607,5461),(1674,5461),(1536,5461),
    (1496,5461),(1924,5462),(1811,5462),(1688,5462),(1647,5462),(1440,5462),(1927,5463),(1976,5463),
    (1880,5463),(2134,5464),(1894,5464),(2018,5464),(1688,5464),(2026,5465),(1633,5465),(1524,5465),
    (1387,5465),(1318,5465),(1821,5466),(1593,5466),(1524,5466),(1429,5466),(1808,5467),(1745,5467),
    (1593,5467),(1483,5467),(1484,5467),(1948,5468),(1841,5468),(1730,5468),(1553,5468),(2073,5469),
    (2006,5469),(1690,5469),(1512,5469),(2075,5470),(1979,5470),(1910,5470),(1649,5470),(2145,5471),
    (2048,5471),(1952,5471),(2035,5471),(2188,5472),(2035,5472),(1760,5472),(2038,5473),(1939,5473),
    (1719,5473),(1650,5473),(1930,5474),(1609,5474),(1541,5474),(1472,5474),(1361,5474),(2001,5475),
    (1802,5475),(1568,5475),(1555,5475),(1837,5476),(1665,5476),(1582,5476),(1321,5476),(1238,5476),
    (1784,5477),(1569,5477),(1514,5477),(1541,5477),(1473,5477),(1840,5478),(1734,5478),(1652,5478),
    (1363,5478),(1924,5479),(1790,5479),(1707,5479),(1501,5479),(1363,5479),(1816,5480),(1597,5480),
    (1474,5480),(1528,5480),(1446,5480),(1846,5481),(1501,5481),(1322,5481),(1336,5481),(1157,5481),
    (1654,5482),(1419,5482),(1364,5482),(1377,5482),(1378,5482),(1780,5483),(1846,5483),(1681,5483),
    (1474,5483),(1433,5483),(2043,5484),(2067,5484),(1999,5484),(1750,5484),(2265,5485),(2178,5485),
    (2178,5485),(2557,5486),(2192,5486),(1957,5486),(1862,5486),(2462,5487),(2371,5487),(2358,5487),
    (2657,5488),(2552,5488),(2179,5488),(2617,5489),(2510,5489),(2263,5489),(2770,5490),(2387,5490),
    (2180,5490),(1987,5490),(2414,5491),(2401,5491),(2057,5491),(2374,5492),(2333,5492),(2001,5492),
    (1725,5492),(2156,5493),(1131,5493)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block11 : PLift (RangeResult 2883584 3145728 209014 226549) :=
  ⟨oneBlock 2883584 262144 209014 226549 [
    (1989,5493),(1836,5493),(2281,5494),(2154,5494),(1988,5494),(1795,5494),(2173,5495),(1933,5495),
    (1782,5495),(1782,5495),(2174,5496),(2072,5496),(1892,5496),(1851,5496),(2204,5497),(2031,5497),
    (1796,5497),(1658,5497),(2178,5498),(2114,5498),(2045,5498),(1811,5498),(2262,5499),(1949,5499),
    (1935,5499),(1673,5499),(2084,5500),(2046,5500),(1977,5500),(1797,5500),(2100,5501),(1950,5501),
    (1728,5501),(1535,5501),(2074,5502),(1978,5502),(1770,5502),(1673,5502),(1300,5502),(1800,5503),
    (1756,5503),(1716,5503),(1521,5503),(1508,5503),(1953,5504),(1951,5504),(1785,5504),(1549,5504),
    (1927,5505),(1869,5505),(1674,5505),(1550,5505),(1619,5505),(2095,5506),(2021,5506),(1896,5506),
    (1702,5506),(1986,5507),(1897,5507),(1772,5507),(1661,5507),(2265,5508),(2063,5508),(1897,5508),
    (1938,5508),(2280,5509),(2133,5509),(1967,5509),(1994,5509),(2351,5510),(2009,5510),(1773,5510),
    (1731,5510),(1579,5510),(1952,5511),(1815,5511),(1787,5511),(1538,5511),(2064,5512),(1871,5512),
    (1773,5512),(1441,5512),(1497,5512),(1803,5513),(1690,5513),(1705,5513),(1580,5513),(1414,5513),
    (1957,5514),(1705,5514),(1469,5514),(1442,5514),(1372,5514),(1737,5515),(1594,5515),(1553,5515),
    (1373,5515),(1428,5515),(1193,5515),(1488,5516),(1359,5516),(1262,5516),(1235,5516),(1234,5516),
    (1179,5516),(1768,5517),(1720,5517),(1678,5517),(1637,5517),(1525,5517),(2061,5518),(1873,5518),
    (1693,5518),(1568,5518),(1609,5518),(2229,5519),(2095,5519),(1985,5519),(1720,5519),(2176,5520),
    (1860,5520),(1513,5520),(1623,5520),(1499,5520),(2067,5521),(1943,5521),(1791,5521),(1638,5521),
    (1485,5521),(1999,5522),(1875,5522),(1985,5522),(1833,5522),(2250,5523),(2042,5523),(1777,5523),
    (1736,5523),(2266,5524),(2028,5524),(1972,5524),(1778,5524),(1570,5524),(2101,5525),(1848,5525),
    (1260,5525)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block12 : PLift (RangeResult 3145728 3407872 226549 244069) :=
  ⟨oneBlock 3145728 262144 226549 244069 [
    (1644,5525),(1528,5525),(2034,5526),(1959,5526),(1876,5526),(1890,5526),(2369,5527),(2043,5527),
    (1876,5527),(1570,5527),(1487,5527),(2191,5528),(2099,5528),(1863,5528),(1876,5528),(2387,5529),
    (2113,5529),(1975,5529),(1626,5529),(2208,5530),(2295,5530),(2030,5530),(1919,5530),(1891,5530),
    (2377,5531),(2267,5531),(2100,5531),(2031,5531),(2643,5532),(2644,5532),(2225,5532),(2812,5533),
    (2783,5533),(2435,5533),(3106,5534),(2770,5534),(2574,5534),(2478,5534),(2816,5535),(2742,5535),
    (2533,5535),(3111,5536),(3077,5536),(2701,5536),(3043,5537),(2882,5537),(2562,5537),(3073,5538),
    (2744,5538),(2619,5538),(3200,5539),(2814,5539),(2730,5539),(3133,5540),(2856,5540),(2787,5540),
    (3385,5541),(2857,5541),(2704,5541),(3164,5542),(2997,5542),(2704,5542),(3125,5543),(2789,5543),
    (2453,5543),(2988,5544),(2705,5544),(2649,5544),(2538,5544),(3004,5545),(2720,5545),(2440,5545),
    (2978,5546),(2818,5546),(2665,5546),(2951,5547),(2721,5547),(2414,5547),(2400,5547),(3024,5548),
    (2651,5548),(2484,5548),(3054,5549),(2624,5549),(2248,5549),(2553,5550),(2415,5550),(1982,5550),
    (2206,5550),(2765,5551),(2667,5551),(2318,5551),(2150,5551),(2893,5552),(2570,5552),(2374,5552),
    (2192,5552),(2895,5553),(2640,5553),(2277,5553),(2897,5554),(2683,5554),(2514,5554),(2585,5554),
    (897,5555)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block13 : PLift (RangeResult 3407872 3670016 244069 261378) :=
  ⟨oneBlock 3407872 262144 244069 261378 [
    (2813,5555),(2697,5555),(2725,5555),(3111,5556),(2851,5556),(2586,5556),(3070,5557),(2950,5557),
    (2656,5557),(3255,5558),(3118,5558),(3076,5558),(3453,5559),(3398,5559),(3063,5559),(3413,5560),
    (3231,5560),(2924,5560),(3191,5561),(2826,5561),(2658,5561),(3124,5562),(2911,5562),(2448,5562),
    (2197,5562),(2776,5563),(2450,5563),(2099,5563),(1848,5563),(2302,5564),(2351,5564),(2156,5564),
    (1918,5564),(2444,5565),(2072,5565),(2129,5565),(2058,5565),(2376,5566),(2170,5566),(2157,5566),
    (2045,5566),(1778,5566),(2224,5567),(2129,5567),(1891,5567),(1681,5567),(1429,5567),(1932,5568),
    (1737,5568),(1723,5568),(1597,5568),(1527,5568),(2116,5569),(1835,5569),(1682,5569),(1471,5569),
    (1303,5569),(1149,5569),(1852,5570),(1878,5570),(1612,5570),(1401,5570),(1290,5570),(1163,5570),
    (1177,5570),(1812,5571),(1654,5571),(1640,5571),(1444,5571),(1331,5571),(1192,5571),(1953,5572),
    (1795,5572),(1668,5572),(1655,5572),(1472,5572),(1290,5572),(1801,5573),(1725,5573),(1599,5573),
    (1346,5573),(1318,5573),(1248,5573),(1220,5573),(1706,5574),(1725,5574),(1599,5574),(1472,5574),
    (1165,5574),(1051,5574),(996,5574),(1764,5575),(1627,5575),(1613,5575),(1445,5575),(1459,5575),
    (1347,5575),(1919,5576),(1881,5576),(1852,5576),(1880,5576),(1712,5576),(1782,5576),(2314,5577),
    (2288,5577),(1993,5577),(1979,5577),(2653,5578),(2527,5578),(2400,5578),(2218,5578),(2852,5579),
    (2443,5579),(2176,5579),(2092,5579),(2601,5580),(2387,5580),(2065,5580),(1867,5580),(1447,5580),
    (1999,5581),(1925,5581),(1952,5581),(1755,5581),(1517,5581),(1475,5581),(1988,5582),(1995,5582),
    (1405,5582)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block14 : PLift (RangeResult 3670016 3932160 261378 278737) :=
  ⟨oneBlock 3670016 262144 261378 278737 [
    (1741,5582),(1588,5582),(2355,5583),(2107,5583),(2192,5583),(2290,5583),(1911,5583),(2428,5584),
    (2248,5584),(2151,5584),(2037,5584),(1771,5584),(2472,5585),(2460,5585),(2319,5585),(2179,5585),
    (2769,5586),(2348,5586),(2319,5586),(1940,5586),(2729,5587),(2447,5587),(2320,5587),(2250,5587),
    (2759,5588),(2687,5588),(2630,5588),(2615,5588),(3142,5589),(3010,5589),(2659,5589),(2363,5589),
    (2835,5590),(2518,5590),(2575,5590),(2448,5590),(3005,5591),(2829,5591),(2350,5591),(2740,5592),
    (2533,5592),(2365,5592),(2069,5592),(1886,5592),(2517,5593),(2408,5593),(2252,5593),(2182,5593),
    (2688,5594),(2521,5594),(2281,5594),(2070,5594),(1830,5594),(2296,5595),(2268,5595),(2197,5595),
    (1957,5595),(2707,5596),(2437,5596),(2197,5596),(2155,5596),(1944,5596),(2794,5597),(2705,5597),
    (2550,5597),(2451,5597),(2895,5598),(2734,5598),(2621,5598),(2240,5598),(2841,5599),(2649,5599),
    (2593,5599),(2453,5599),(2970,5600),(2720,5600),(2467,5600),(2298,5600),(2915,5601),(2693,5601),
    (2538,5601),(2228,5601),(2876,5602),(2552,5602),(2313,5602),(2172,5602),(2666,5603),(2581,5603),
    (2412,5603),(2172,5603),(2823,5604),(2639,5604),(2638,5604),(2652,5604),(3037,5605),(2752,5605),
    (2427,5605),(2342,5605),(2997,5606),(2767,5606),(2554,5606),(2230,5606),(3056,5607),(2724,5607),
    (2640,5607),(2527,5607),(944,5608)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block15 : PLift (RangeResult 3932160 4194304 278737 295947) :=
  ⟨oneBlock 3932160 262144 278737 295947 [
    (3159,5608),(2782,5608),(2654,5608),(2583,5608),(3104,5609),(2881,5609),(2909,5609),(3459,5610),
    (3008,5610),(2740,5610),(2457,5610),(2925,5611),(2571,5611),(2387,5611),(2275,5611),(2927,5612),
    (2825,5612),(2657,5612),(2486,5612),(2802,5613),(2530,5613),(2332,5613),(2176,5613),(2762,5614),
    (2346,5614),(2205,5614),(2149,5614),(1950,5614),(2369,5615),(2459,5615),(2319,5615),(2036,5615),
    (2036,5615),(2554,5616),(2376,5616),(2262,5616),(2163,5616),(2093,5616),(2628,5617),(2517,5617),
    (2348,5617),(2362,5617),(3082,5618),(2928,5618),(2801,5618),(2744,5618),(3325,5619),(3028,5619),
    (2603,5619),(2660,5619),(3074,5620),(2801,5620),(2633,5620),(2405,5620),(2963,5621),(2943,5621),
    (2860,5621),(2660,5621),(3149,5622),(2987,5622),(2747,5622),(2576,5622),(3279,5623),(3157,5623),
    (2648,5623),(3238,5624),(3201,5624),(3045,5624),(2733,5624),(3269,5625),(2848,5625),(2492,5625),
    (2394,5625),(2975,5626),(2762,5626),(2352,5626),(1983,5626),(2679,5627),(2452,5627),(2338,5627),
    (2210,5627),(1956,5627),(2738,5628),(2636,5628),(2423,5628),(2325,5628),(2211,5628),(2995,5629),
    (2878,5629),(2736,5629),(2410,5629),(2970,5630),(2722,5630),(2481,5630),(2297,5630),(3071,5631),
    (3021,5631),(2836,5631),(1851,5631)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block16 : PLift (RangeResult 4194304 4456448 295947 313085) :=
  ⟨oneBlock 4194304 262144 295947 313085 [
    (3307,5632),(3092,5632),(2837,5632),(2652,5632),(3389,5633),(3121,5633),(3007,5633),(2653,5633),
    (3306,5634),(3121,5634),(2938,5634),(2653,5634),(3195,5635),(2923,5635),(2697,5635),(2256,5635),
    (3042,5636),(2909,5636),(2485,5636),(2427,5636),(3200,5637),(2981,5637),(2768,5637),(2613,5637),
    (3230,5638),(2926,5638),(2570,5638),(2485,5638),(3290,5639),(2755,5639),(2542,5639),(2344,5639),
    (2130,5639),(2824,5640),(2401,5640),(2330,5640),(2074,5640),(2669,5641),(2600,5641),(2416,5641),
    (2316,5641),(2188,5641),(2828,5642),(2644,5642),(2316,5642),(2274,5642),(2231,5642),(2660,5643),
    (2317,5643),(2374,5643),(2260,5643),(1975,5643),(2706,5644),(2346,5644),(2331,5644),(2289,5644),
    (1976,5644),(2637,5645),(2346,5645),(2176,5645),(1948,5645),(1948,5645),(2554,5646),(2233,5646),
    (2033,5646),(2048,5646),(1821,5646),(1664,5646),(2400,5647),(2219,5647),(2332,5647),(2106,5647),
    (1835,5647),(1678,5647),(2474,5648),(2418,5648),(2191,5648),(1992,5648),(1850,5648),(2575,5649),
    (2249,5649),(2148,5649),(1822,5649),(1622,5649),(1608,5649),(2307,5650),(2150,5650),(1878,5650),
    (1751,5650),(1665,5650),(1751,5650),(2352,5651),(2335,5651),(2221,5651),(2206,5651),(2107,5651),
    (2036,5651),(2768,5652),(2676,5652),(2364,5652),(2207,5652),(2221,5652),(2999,5653),(2933,5653),
    (2677,5653),(2607,5653),(3214,5654),(603,5654)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block17 : PLift (RangeResult 4456448 4718592 313085 330177) :=
  ⟨oneBlock 4456448 262144 313085 330177 [
    (2972,5654),(2820,5654),(2678,5654),(3289,5655),(3134,5655),(2920,5655),(2650,5655),(3377,5656),
    (3120,5656),(2921,5656),(2978,5656),(3750,5657),(3406,5657),(3121,5657),(2794,5657),(3524,5658),
    (3450,5658),(3036,5658),(2637,5658),(3328,5659),(3008,5659),(2737,5659),(2524,5659),(3130,5660),
    (3009,5660),(2667,5660),(2396,5660),(3047,5661),(2767,5661),(2596,5661),(2510,5661),(2268,5661),
    (2907,5662),(2868,5662),(2810,5662),(2368,5662),(3067,5663),(3096,5663),(2925,5663),(2725,5663),
    (2297,5663),(3084,5664),(3011,5664),(2712,5664),(2683,5664),(3286,5665),(2926,5665),(2912,5665),
    (2797,5665),(3275,5666),(2969,5666),(2855,5666),(2670,5666),(3577,5667),(3213,5667),(2841,5667),
    (2885,5667),(3422,5668),(3214,5668),(2999,5668),(2642,5668),(2570,5668),(3255,5669),(3042,5669),
    (2643,5669),(2671,5669),(3314,5670),(2929,5670),(2514,5670),(2315,5670),(2129,5670),(2859,5671),
    (2701,5671),(2615,5671),(2415,5671),(2258,5671),(3176,5672),(2902,5672),(2887,5672),(2658,5672),
    (3608,5673),(3145,5673),(2759,5673),(2930,5673),(3554,5674),(3317,5674),(2917,5674),(2745,5674),
    (3413,5675),(2303,5675)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block18 : PLift (RangeResult 4718592 4980736 330177 347259) :=
  ⟨oneBlock 4718592 262144 330177 347259 [
    (3131,5675),(2946,5675),(2574,5675),(3302,5676),(3118,5676),(3190,5676),(2961,5676),(3576,5677),
    (3419,5677),(3090,5677),(2761,5677),(3322,5678),(3119,5678),(2862,5678),(2733,5678),(3352,5679),
    (3178,5679),(2962,5679),(2476,5679),(3341,5680),(2992,5680),(2991,5680),(2620,5680),(2476,5680),
    (3086,5681),(2721,5681),(2634,5681),(2477,5681),(2290,5681),(3304,5682),(3093,5682),(2606,5682),
    (2435,5682),(3191,5683),(3094,5683),(2907,5683),(2693,5683),(2249,5683),(3065,5684),(2837,5684),
    (2721,5684),(2865,5684),(2522,5684),(3169,5685),(2865,5685),(2765,5685),(2723,5685),(3357,5686),
    (2981,5686),(2852,5686),(2651,5686),(2637,5686),(3418,5687),(3225,5687),(2766,5687),(2508,5687),
    (3450,5688),(3196,5688),(3083,5688),(3168,5688),(3911,5689),(3742,5689),(3699,5689),(3212,5689),
    (4144,5690),(3614,5690),(3341,5690),(3026,5690),(3846,5691),(3657,5691),(3414,5691),(4020,5692),
    (3802,5692),(3515,5692),(3357,5692),(3980,5693),(3803,5693),(3558,5693),(3172,5693),(4212,5694),
    (4005,5694),(3545,5694),(4273,5695),(1200,5695)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block19 : PLift (RangeResult 4980736 5242880 347259 364195) :=
  ⟨oneBlock 4980736 262144 347259 364195 [
    (4154,5695),(3833,5695),(4692,5696),(4480,5696),(3876,5696),(4753,5697),(4179,5697),(3935,5697),
    (3417,5697),(4168,5698),(3964,5698),(3749,5698),(4515,5699),(4065,5699),(3664,5699),(3505,5699),
    (4116,5700),(3650,5700),(3462,5700),(4421,5701),(4052,5701),(3608,5701),(3406,5701),(4251,5702),
    (3910,5702),(3622,5702),(4340,5703),(4184,5703),(3795,5703),(3479,5703),(4243,5704),(3940,5704),
    (3495,5704),(4217,5705),(3969,5705),(3524,5705),(3538,5705),(4392,5706),(3884,5706),(3784,5706),
    (4438,5707),(4173,5707),(3841,5707),(3496,5707),(4342,5708),(3914,5708),(3684,5708),(4258,5709),
    (4001,5709),(3857,5709),(3325,5709),(4031,5710),(3743,5710),(3441,5710),(3066,5710),(3976,5711),
    (3600,5711),(3643,5711),(3542,5711),(3965,5712),(3845,5712),(3629,5712),(3413,5712),(4127,5713),
    (3846,5713),(3572,5713),(4216,5714),(929,5714)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block20 : PLift (RangeResult 5242880 5505024 364195 381113) :=
  ⟨oneBlock 5242880 262144 364195 381113 [
    (3940,5714),(3875,5714),(3876,5714),(4551,5715),(3977,5715),(3818,5715),(4597,5716),(4309,5716),
    (4079,5716),(4715,5717),(4151,5717),(3849,5717),(3748,5717),(4488,5718),(4167,5718),(4094,5718),
    (4808,5719),(4182,5719),(3966,5719),(3533,5719),(4436,5720),(4082,5720),(3851,5720),(4584,5721),
    (4371,5721),(4270,5721),(3563,5721),(4443,5722),(4098,5722),(3924,5722),(4475,5723),(4012,5723),
    (4012,5723),(3824,5723),(4782,5724),(4503,5724),(4099,5724),(4640,5725),(4360,5725),(3855,5725),
    (3667,5725),(4384,5726),(4201,5726),(3783,5726),(4661,5727),(4420,5727),(3986,5727),(3812,5727),
    (4550,5728),(4102,5728),(4102,5728),(4610,5729),(4479,5729),(4233,5729),(3857,5729),(4556,5730),
    (4205,5730),(3858,5730),(4544,5731),(4191,5731),(3816,5731),(3584,5731),(3636,5732)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block21 : PLift (RangeResult 5505024 5767168 381113 397906) :=
  ⟨oneBlock 5505024 262144 381113 397906 [
    (4179,5732),(4091,5732),(3541,5732),(4378,5733),(3933,5733),(3643,5733),(4279,5734),(3847,5734),
    (3991,5734),(3818,5734),(4267,5735),(3848,5735),(3500,5735),(3211,5735),(3967,5736),(3805,5736),
    (3559,5736),(3573,5736),(4332,5737),(3704,5737),(3574,5737),(3429,5737),(4061,5738),(3893,5738),
    (3560,5738),(3415,5738),(4107,5739),(3778,5739),(3705,5739),(3330,5739),(4139,5740),(3663,5740),
    (3503,5740),(3243,5740),(3055,5740),(3983,5741),(3591,5741),(3171,5741),(2954,5741),(3770,5742),
    (3432,5742),(3114,5742),(2940,5742),(2838,5742),(3585,5743),(3201,5743),(3056,5743),(2840,5743),
    (2607,5743),(3356,5744),(3201,5744),(2985,5744),(3014,5744),(2796,5744),(3677,5745),(3681,5745),
    (3463,5745),(3101,5745),(3840,5746),(3769,5746),(3724,5746),(3522,5746),(3088,5746),(4060,5747),
    (3712,5747),(3189,5747),(3058,5747),(3992,5748),(3654,5748),(3450,5748),(3306,5748),(4183,5749),
    (3771,5749),(1549,5749)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block22 : PLift (RangeResult 5767168 6029312 397906 414771) :=
  ⟨oneBlock 5767168 262144 397906 414771 [
    (3178,5749),(2843,5749),(2857,5749),(3635,5750),(3235,5750),(2988,5750),(2741,5750),(2538,5750),
    (3363,5751),(3207,5751),(2959,5751),(2655,5751),(2466,5751),(3482,5752),(3396,5752),(3177,5752),
    (2931,5752),(2554,5752),(3674,5753),(3207,5753),(2874,5753),(2728,5753),(2453,5753),(3445,5754),
    (3208,5754),(2888,5754),(2671,5754),(2772,5754),(2468,5754),(3565,5755),(3223,5755),(2874,5755),
    (2483,5755),(2366,5755),(3393,5756),(3108,5756),(2846,5756),(2773,5756),(2498,5756),(2628,5756),
    (3716,5757),(3442,5757),(3167,5757),(3195,5757),(2759,5757),(3836,5758),(3603,5758),(3355,5758),
    (3196,5758),(4202,5759),(4111,5759),(3880,5759),(3705,5759),(4437,5760),(4360,5760),(3981,5760),
    (3793,5760),(4500,5761),(4156,5761),(3823,5761),(3488,5761),(4489,5762),(4041,5762),(3663,5762),
    (3271,5762),(3169,5762),(3896,5763),(3751,5763),(3621,5763),(3242,5763),(3957,5764),(3811,5764),
    (3592,5764),(3475,5764),(3345,5764),(4223,5765),(3883,5765),(3709,5765),(1951,5765)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block23 : PLift (RangeResult 6029312 6291456 414771 431502) :=
  ⟨oneBlock 6029312 262144 414771 431502 [
    (4777,5766),(4175,5766),(3594,5766),(3302,5766),(4287,5767),(3682,5767),(3666,5767),(3551,5767),
    (3274,5767),(3971,5768),(3652,5768),(3377,5768),(3333,5768),(3027,5768),(4018,5769),(3522,5769),
    (3290,5769),(3101,5769),(3904,5770),(3727,5770),(3713,5770),(3450,5770),(3203,5770),(4156,5771),
    (3888,5771),(3611,5771),(3320,5771),(4203,5772),(3801,5772),(3539,5772),(3408,5772),(3161,5772),
    (4031,5773),(3846,5773),(3787,5773),(3351,5773),(4369,5774),(3978,5774),(3890,5774),(3643,5774),
    (3336,5774),(4272,5775),(3701,5775),(3410,5775),(3031,5775),(3954,5776),(3906,5776),(3805,5776),
    (3512,5776),(3265,5776),(4016,5777),(3732,5777),(3251,5777),(3061,5777),(2770,5777),(3918,5778),
    (3587,5778),(3426,5778),(3120,5778),(2931,5778),(3804,5779),(3559,5779),(3296,5779),(3208,5779),
    (2946,5779),(4070,5780),(3690,5780),(3589,5780),(3325,5780),(3005,5780),(4249,5781),(4070,5781),
    (1751,5781)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block24 : PLift (RangeResult 6291456 6553600 431502 448182) :=
  ⟨oneBlock 6291456 262144 431502 448182 [
    (3632,5781),(3458,5781),(4646,5782),(4568,5782),(4275,5782),(3896,5782),(4635,5783),(4408,5783),
    (4218,5783),(3896,5783),(5019,5784),(4569,5784),(4145,5784),(3854,5784),(4730,5785),(4322,5785),
    (4088,5785),(3548,5785),(4675,5786),(4074,5786),(3739,5786),(3197,5786),(4227,5787),(3768,5787),
    (3461,5787),(3228,5787),(3038,5787),(4069,5788),(3900,5788),(3477,5788),(3257,5788),(3010,5788),
    (4072,5789),(3755,5789),(3551,5789),(3287,5789),(2951,5789),(3858,5790),(3419,5790),(3171,5790),
    (3054,5790),(2718,5790),(3905,5791),(3712,5791),(3523,5791),(3128,5791),(3098,5791),(3952,5792),
    (3596,5792),(3406,5792),(3070,5792),(2880,5792),(3926,5793),(3641,5793),(3216,5793),(3144,5793),
    (3041,5793),(2997,5793),(3901,5794),(3598,5794),(3466,5794),(3158,5794),(2911,5794),(3860,5795),
    (3569,5795),(3496,5795),(3203,5795),(2998,5795),(3937,5796),(3716,5796),(3570,5796),(1663,5796)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block25 : PLift (RangeResult 6553600 6815744 448182 464881) :=
  ⟨oneBlock 6553600 262144 448182 464881 [
    (3106,5796),(4013,5797),(3936,5797),(3673,5797),(3365,5797),(3190,5797),(4163,5798),(3908,5798),
    (3863,5798),(3703,5798),(3366,5798),(4328,5799),(3967,5799),(3791,5799),(3645,5799),(3396,5799),
    (4478,5800),(4349,5800),(3967,5800),(3602,5800),(4584,5801),(4115,5801),(3778,5801),(3646,5801),
    (3309,5801),(4413,5802),(3939,5802),(3574,5802),(3149,5802),(3017,5802),(3947,5803),(3736,5803),
    (3574,5803),(3223,5803),(2900,5803),(3966,5804),(3487,5804),(3340,5804),(3150,5804),(3033,5804),
    (4072,5805),(3825,5805),(3810,5805),(3487,5805),(3503,5805),(4310,5806),(4221,5806),(3972,5806),
    (3561,5806),(3489,5806),(4416,5807),(3958,5807),(3914,5807),(3606,5807),(4787,5808),(4721,5808),
    (4193,5808),(3739,5808),(3504,5808),(4469,5809),(4164,5809),(3887,5809),(3592,5809),(4237,5810),
    (3887,5810),(3843,5810),(3638,5810),(3534,5810),(4116,5811)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block26 : PLift (RangeResult 6815744 7077888 464881 481615) :=
  ⟨oneBlock 6815744 262144 464881 481615 [
    (4218,5811),(4034,5811),(3712,5811),(3506,5811),(4435,5812),(4241,5812),(3844,5812),(3757,5812),
    (4732,5813),(4300,5813),(4256,5813),(4021,5813),(4036,5813),(5177,5814),(4682,5814),(4404,5814),
    (4183,5814),(5239,5815),(5021,5815),(4581,5815),(4184,5815),(5126,5816),(4787,5816),(4302,5816),
    (4347,5816),(5115,5817),(4685,5817),(4465,5817),(4406,5817),(5295,5818),(5054,5818),(5067,5818),
    (4407,5818),(5461,5819),(5172,5819),(4834,5819),(5655,5820),(5188,5820),(4937,5820),(4541,5820),
    (5645,5821),(5174,5821),(4776,5821),(4277,5821),(5488,5822),(5057,5822),(4939,5822),(4763,5822),
    (5830,5823),(5573,5823),(5278,5823),(6275,5824),(5677,5824),(5014,5824),(4809,5824),(162,5825)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block27 : PLift (RangeResult 7077888 7340032 481615 498177) :=
  ⟨oneBlock 7077888 262144 481615 498177 [
    (5897,5825),(5428,5825),(5118,5825),(6151,5826),(5767,5826),(5590,5826),(6538,5827),(6033,5827),
    (5532,5827),(4753,5827),(5615,5828),(5180,5828),(4901,5828),(5957,5829),(5491,5829),(5196,5829),
    (4945,5829),(5992,5830),(5123,5830),(4829,5830),(4490,5830),(5657,5831),(5139,5831),(4844,5831),
    (4536,5831),(5573,5832),(5140,5832),(4860,5832),(5797,5833),(5362,5833),(4979,5833),(4816,5833),
    (5832,5834),(5451,5834),(4965,5834),(4847,5834),(5747,5835),(5541,5835),(5010,5835),(4730,5835),
    (5870,5836),(5645,5836),(4981,5836),(6036,5837),(5366,5837),(5247,5837),(4850,5837),(6055,5838),
    (4742,5838)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block28 : PLift (RangeResult 7340032 7602176 498177 514705) :=
  ⟨oneBlock 7340032 262144 498177 514705 [
    (4959,5838),(4409,5838),(5587,5839),(5265,5839),(4925,5839),(4616,5839),(5812,5840),(5428,5840),
    (5207,5840),(6200,5841),(5546,5841),(5060,5841),(4677,5841),(5702,5842),(5179,5842),(4928,5842),
    (4678,5842),(5722,5843),(5430,5843),(4988,5843),(4737,5843),(6051,5844),(5521,5844),(5003,5844),
    (4473,5844),(5376,5845),(5123,5845),(4901,5845),(4591,5845),(5676,5846),(4917,5846),(4592,5846),
    (4371,5846),(5473,5847),(4874,5847),(4593,5847),(4135,5847),(4945,5848),(4949,5848),(4475,5848),
    (4476,5848),(4224,5848),(5409,5849),(5111,5849),(4743,5849),(4181,5849),(5456,5850),(4788,5850),
    (4462,5850),(3960,5850),(5269,5851),(5069,5851),(1902,5851)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block29 : PLift (RangeResult 7602176 7864320 514705 531252) :=
  ⟨oneBlock 7602176 262144 514705 531252 [
    (4689,5851),(4626,5851),(5923,5852),(5218,5852),(4553,5852),(4701,5852),(5794,5853),(5293,5853),
    (4820,5853),(4613,5853),(5710,5854),(5323,5854),(5057,5854),(4614,5854),(5862,5855),(5414,5855),
    (4910,5855),(4733,5855),(6014,5856),(5607,5856),(5074,5856),(4630,5856),(5812,5857),(5696,5857),
    (5164,5857),(4704,5857),(5773,5858),(5283,5858),(4602,5858),(4484,5858),(5509,5859),(5181,5859),
    (4795,5859),(4396,5859),(5603,5860),(5300,5860),(4589,5860),(4130,5860),(3923,5860),(5178,5861),
    (4931,5861),(4664,5861),(4575,5861),(5449,5862),(5183,5862),(4620,5862),(4191,5862),(4058,5862),
    (5498,5863),(5377,5863),(4902,5863),(4577,5863),(819,5864)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block30 : PLift (RangeResult 7864320 8126464 531252 547712) :=
  ⟨oneBlock 7864320 262144 531252 547712 [
    (5869,5864),(5199,5864),(5082,5864),(4889,5864),(6084,5865),(5646,5865),(5304,5865),(4697,5865),
    (5778,5866),(5528,5866),(5098,5866),(4683,5866),(5871,5867),(5470,5867),(5069,5867),(4847,5867),
    (6143,5868),(5456,5868),(5040,5868),(4700,5868),(5821,5869),(5545,5869),(5131,5869),(4997,5869),
    (5988,5870),(5517,5870),(5028,5870),(4790,5870),(5830,5871),(5311,5871),(4969,5871),(4658,5871),
    (5611,5872),(5030,5872),(4970,5872),(4525,5872),(4302,5872),(5750,5873),(5431,5873),(4957,5873),
    (4674,5873),(5725,5874),(5209,5874),(4764,5874),(4260,5874),(5328,5875),(4839,5875),(4602,5875),
    (4245,5875),(3993,5875),(3891,5876)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block31 : PLift (RangeResult 8126464 8388608 547712 564163) :=
  ⟨oneBlock 8126464 262144 547712 564163 [
    (5436,5876),(4915,5876),(4454,5876),(3979,5876),(5189,5877),(4781,5877),(4618,5877),(4396,5877),
    (4247,5877),(5342,5878),(4901,5878),(4605,5878),(4485,5878),(5643,5879),(5155,5879),(4679,5879),
    (4516,5879),(4397,5879),(5738,5880),(5408,5880),(4948,5880),(4665,5880),(5816,5881),(5350,5881),
    (5305,5881),(4844,5881),(5925,5882),(5455,5882),(4875,5882),(4622,5882),(4340,5882),(5543,5883),
    (5545,5883),(4861,5883),(4490,5883),(5666,5884),(5487,5884),(5025,5884),(4743,5884),(6087,5885),
    (5473,5885),(5041,5885),(4700,5885),(4565,5885),(5825,5886),(5801,5886),(5161,5886),(4537,5886),
    (5709,5887),(5192,5887),(5103,5887),(4561,5887)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block32 : PLift (RangeResult 8388608 8650752 564163 580619) :=
  ⟨oneBlock 8388608 262144 564163 580619 [
    (5943,5888),(5684,5888),(5179,5888),(4716,5888),(4375,5888),(5719,5889),(5373,5889),(4911,5889),
    (4450,5889),(5544,5890),(5180,5890),(4436,5890),(4213,5890),(4034,5890),(5355,5891),(4973,5891),
    (4466,5891),(4139,5891),(3960,5891),(5450,5892),(5242,5892),(4884,5892),(4616,5892),(4184,5892),
    (5559,5893),(5227,5893),(4841,5893),(4691,5893),(4572,5893),(5743,5894),(5437,5894),(5184,5894),
    (4811,5894),(5986,5895),(5721,5895),(5274,5895),(4723,5895),(6243,5896),(6095,5896),(5647,5896),
    (5275,5896),(6472,5897),(6021,5897),(5724,5897),(5544,5897),(6670,5898),(6127,5898),(5560,5898),
    (5396,5898),(6571,5899),(4,5899)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block33 : PLift (RangeResult 8650752 8912896 580619 597016) :=
  ⟨oneBlock 8650752 262144 580619 597016 [
    (6020,5899),(6023,5899),(5726,5899),(6665,5900),(6084,5900),(5458,5900),(5383,5900),(6596,5901),
    (6160,5901),(5698,5901),(5324,5901),(6825,5902),(6504,5902),(6086,5902),(5639,5902),(6875,5903),
    (6207,5903),(5864,5903),(5550,5903),(7059,5904),(6566,5904),(5969,5904),(7645,5905),(6851,5905),
    (6299,5905),(5911,5905),(6994,5906),(6553,5906),(6031,5906),(5793,5906),(6730,5907),(6152,5907),
    (5928,5907),(7167,5908),(6467,5908),(5779,5908),(5630,5908),(6919,5909),(6438,5909),(5900,5909),
    (5556,5909),(6432,5910),(688,5910)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block34 : PLift (RangeResult 8912896 9175040 597016 613334) :=
  ⟨oneBlock 8912896 262144 597016 613334 [
    (6199,5910),(5886,5910),(5647,5910),(7049,5911),(6619,5911),(6127,5911),(5633,5911),(7054,5912),
    (6097,5912),(5829,5912),(5231,5912),(6536,5913),(6323,5913),(6024,5913),(5769,5913),(6601,5914),
    (5921,5914),(5427,5914),(5113,5914),(6291,5915),(5892,5915),(5398,5915),(5159,5915),(6446,5916),
    (5788,5916),(5399,5916),(5130,5916),(4771,5916),(6077,5917),(5774,5917),(5610,5917),(5145,5917),
    (6427,5918),(6194,5918),(5356,5918),(4907,5918),(6177,5919),(5671,5919),(5402,5919),(5357,5919),
    (5103,5919),(6332,5920),(5687,5920),(5193,5920),(4954,5920),(1419,5921)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block35 : PLift (RangeResult 9175040 9437184 613334 629686) :=
  ⟨oneBlock 9175040 262144 613334 629686 [
    (6175,5921),(6018,5921),(5673,5921),(5300,5921),(6655,5922),(6064,5922),(5704,5922),(5405,5922),
    (5241,5922),(6721,5923),(6305,5923),(5900,5923),(5331,5923),(6981,5924),(6680,5924),(5916,5924),
    (5587,5924),(6852,5925),(6426,5925),(5857,5925),(5513,5925),(6932,5926),(6368,5926),(6143,5926),
    (5528,5926),(6967,5927),(6384,5927),(6084,5927),(5515,5927),(7167,5928),(6700,5928),(6310,5928),
    (5950,5928),(7023,5929),(6521,5929),(6206,5929),(5607,5929),(6892,5930),(6313,5930),(5952,5930),
    (5623,5930),(6763,5931),(2892,5931)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block36 : PLift (RangeResult 9437184 9699328 629686 646005) :=
  ⟨oneBlock 9437184 262144 629686 646005 [
    (5926,5931),(5579,5931),(5218,5931),(6514,5932),(5819,5932),(5505,5932),(5310,5932),(6683,5933),
    (5986,5933),(5745,5933),(5386,5933),(4756,5933),(6613,5934),(6212,5934),(5597,5934),(5162,5934),
    (6348,5935),(6228,5935),(5778,5935),(5538,5935),(6653,5936),(6485,5936),(5749,5936),(5373,5936),
    (5179,5936),(6809,5937),(6681,5937),(6125,5937),(5825,5937),(6995,5938),(6472,5938),(6006,5938),
    (5796,5938),(7076,5939),(6487,5939),(6263,5939),(5917,5939),(7216,5940),(6805,5940),(6444,5940),
    (6068,5940),(7387,5941),(6430,5941)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block37 : PLift (RangeResult 9699328 9961472 646005 662226) :=
  ⟨oneBlock 9699328 262144 646005 662226 [
    (6069,5941),(5679,5941),(7167,5942),(6506,5942),(6101,5942),(6010,5942),(7413,5943),(6943,5943),
    (6448,5943),(5801,5943),(7267,5944),(6539,5944),(6088,5944),(5607,5944),(7032,5945),(6706,5945),
    (6419,5945),(5999,5945),(7158,5946),(7158,5946),(6586,5946),(6045,5946),(7284,5947),(6692,5947),
    (5941,5947),(5821,5947),(5384,5947),(6718,5948),(6108,5948),(5596,5948),(5355,5948),(6979,5949),
    (6274,5949),(5777,5949),(5296,5949),(4950,5949),(6263,5950),(5853,5950),(5583,5950),(5342,5950),
    (6569,5951),(5618,5951)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block38 : PLift (RangeResult 9961472 10223616 662226 678426) :=
  ⟨oneBlock 9961472 262144 662226 678426 [
    (5625,5951),(5298,5951),(4846,5951),(6318,5952),(5720,5952),(5194,5952),(4847,5952),(4456,5952),
    (5901,5953),(5391,5953),(5209,5953),(4803,5953),(4683,5953),(4321,5953),(5832,5954),(5587,5954),
    (5376,5954),(5015,5954),(4728,5954),(6244,5955),(5965,5955),(5301,5955),(5001,5955),(4865,5955),
    (6430,5956),(5890,5956),(5574,5956),(4881,5956),(4760,5956),(6195,5957),(5831,5957),(5530,5957),
    (5062,5957),(4761,5957),(6457,5958),(6088,5958),(5606,5958),(5304,5958),(4778,5958),(6265,5959),
    (5743,5959),(5321,5959),(5034,5959),(4386,5959),(5789,5960),(5593,5960),(5065,5960),(4583,5960),
    (4070,5960),(622,5961)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block39 : PLift (RangeResult 10223616 10485760 678426 694716) :=
  ⟨oneBlock 10223616 262144 678426 694716 [
    (5745,5961),(5624,5961),(5458,5961),(4855,5961),(4433,5961),(5980,5962),(5731,5962),(5399,5962),
    (5142,5962),(4902,5962),(4690,5962),(6152,5963),(5535,5963),(5264,5963),(4918,5963),(4298,5963),
    (5991,5964),(5266,5964),(5129,5964),(4858,5964),(4526,5964),(6312,5965),(5900,5965),(5402,5965),
    (4859,5965),(4542,5965),(4330,5965),(5912,5966),(5659,5966),(5101,5966),(4739,5966),(4542,5966),
    (6143,5967),(6084,5967),(5796,5967),(5207,5967),(4891,5967),(6632,5968),(6084,5968),(5872,5968),
    (5375,5968),(4922,5968),(6667,5969),(6131,5969),(5692,5969),(5421,5969),(5270,5969),(6855,5970),
    (1908,5970)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block40 : PLift (RangeResult 10485760 10747904 694716 710976) :=
  ⟨oneBlock 10485760 262144 694716 710976 [
    (6217,5970),(6041,5970),(5603,5970),(7132,5971),(6767,5971),(6359,5971),(5755,5971),(5151,5971),
    (6655,5972),(6255,5972),(6088,5972),(5650,5972),(5394,5972),(7053,5973),(6694,5973),(5939,5973),
    (5470,5973),(7164,5974),(6620,5974),(6015,5974),(5622,5974),(5335,5974),(6672,5975),(6515,5975),
    (6107,5975),(5563,5975),(7160,5976),(6834,5976),(6395,5976),(5927,5976),(5760,5976),(7560,5977),
    (7107,5977),(6774,5977),(6230,5977),(7793,5978),(7562,5978),(7244,5978),(6610,5978),(7904,5979),
    (5448,5979)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block41 : PLift (RangeResult 10747904 11010048 710976 727128) :=
  ⟨oneBlock 10747904 262144 710976 727128 [
    (7032,5979),(6565,5979),(7925,5980),(7111,5980),(6536,5980),(6309,5980),(5447,5980),(7144,5981),
    (6810,5981),(6356,5981),(5932,5981),(7377,5982),(6901,5982),(6448,5982),(6281,5982),(5933,5982),
    (7459,5983),(7009,5983),(6509,5983),(5995,5983),(7465,5984),(6919,5984),(6465,5984),(6223,5984),
    (5874,5984),(7396,5985),(6845,5985),(6693,5985),(6148,5985),(7735,5986),(7406,5986),(6876,5986),
    (6634,5986),(8104,5987),(7408,5987),(7089,5987),(6378,5987),(7898,5988),(3509,5988)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block42 : PLift (RangeResult 11010048 11272192 727128 743287) :=
  ⟨oneBlock 11010048 262144 727128 743287 [
    (7006,5988),(6363,5988),(5894,5988),(7495,5989),(6895,5989),(6592,5989),(6168,5989),(5819,5989),
    (7774,5990),(7260,5990),(6821,5990),(6441,5990),(7947,5991),(7716,5991),(7140,5991),(6943,5991),
    (8468,5992),(7248,5992),(6747,5992),(6111,5992),(8034,5993),(7476,5993),(7158,5993),(6627,5993),
    (8617,5994),(8205,5994),(7387,5994),(7008,5994),(8395,5995),(7752,5995),(7252,5995),(6523,5995),
    (8083,5996),(7693,5996),(7374,5996),(6919,5996),(2793,5997)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block43 : PLift (RangeResult 11272192 11534336 743287 759401) :=
  ⟨oneBlock 11272192 262144 743287 759401 [
    (7876,5997),(7163,5997),(6844,5997),(6723,5997),(7883,5998),(7255,5998),(7028,5998),(6481,5998),
    (6360,5998),(7677,5999),(6969,5999),(6664,5999),(6331,5999),(7789,6000),(7212,6000),(6575,6000),
    (6241,6000),(7627,6001),(7412,6001),(6803,6001),(6212,6001),(5998,6001),(7680,6002),(6821,6002),
    (6440,6002),(6121,6002),(5560,6002),(7580,6003),(7140,6003),(7004,6003),(6487,6003),(7859,6004),
    (7279,6004),(6959,6004),(6336,6004),(5713,6004),(7243,6005),(6799,6005)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block44 : PLift (RangeResult 11534336 11796480 759401 775549) :=
  ⟨oneBlock 11534336 262144 759401 775549 [
    (6788,6005),(6581,6005),(8479,6006),(7844,6006),(7266,6006),(6855,6006),(8273,6007),(7997,6007),
    (7434,6007),(6826,6007),(6705,6007),(8569,6008),(8515,6008),(7649,6008),(6751,6008),(8257,6009),
    (8182,6009),(7665,6009),(7057,6009),(8354,6010),(7864,6010),(7241,6010),(7149,6010),(8619,6011),
    (7972,6011),(7394,6011),(6785,6011),(8534,6012),(8019,6012),(7411,6012),(6847,6012),(8571,6013),
    (7640,6013),(7731,6013),(2320,6013)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block45 : PLift (RangeResult 11796480 12058624 775549 791652) :=
  ⟨oneBlock 11796480 262144 775549 791652 [
    (6919,6013),(8820,6014),(8159,6014),(7733,6014),(7124,6014),(8599,6015),(7734,6015),(7202,6015),
    (6759,6015),(8834,6016),(7979,6016),(7812,6016),(7172,6016),(8733,6017),(8331,6017),(7692,6017),
    (7112,6017),(9380,6018),(8409,6018),(8027,6018),(7800,6018),(9462,6019),(8548,6019),(7892,6019),
    (7526,6019),(9241,6020),(8214,6020),(7863,6020),(7268,6020),(8867,6021),(8154,6021),(7621,6021),
    (5158,6021)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block46 : PLift (RangeResult 12058624 12320768 791652 807738) :=
  ⟨oneBlock 12058624 262144 791652 807738 [
    (9217,6022),(8811,6022),(8018,6022),(7378,6022),(8925,6023),(8142,6023),(7669,6023),(7349,6023),
    (8962,6024),(8204,6024),(7793,6024),(7640,6024),(9274,6025),(8404,6025),(7931,6025),(7153,6025),
    (8884,6026),(8085,6026),(7475,6026),(7536,6026),(6986,6026),(8724,6027),(8224,6027),(7583,6027),
    (6835,6027),(8822,6028),(8119,6028),(7752,6028),(6913,6028),(8874,6029),(8547,6029),(8044,6029),
    (3871,6029)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block47 : PLift (RangeResult 12320768 12582912 807738 823749) :=
  ⟨oneBlock 12320768 262144 807738 823749 [
    (7652,6029),(9218,6030),(8350,6030),(7633,6030),(7098,6030),(9056,6031),(9223,6031),(8382,6031),
    (7848,6031),(9536,6032),(8918,6032),(8659,6032),(10489,6033),(9501,6033),(8874,6033),(8324,6033),
    (9977,6034),(9120,6034),(8815,6034),(8142,6034),(9603,6035),(8495,6035),(7991,6035),(7884,6035),
    (9687,6036),(8527,6036),(8084,6036),(7702,6036),(9174,6037),(8529,6037),(1653,6037)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block48 : PLift (RangeResult 12582912 12845056 823749 839845) :=
  ⟨oneBlock 12582912 262144 823749 839845 [
    (7793,6037),(7535,6037),(9104,6038),(8790,6038),(8164,6038),(7689,6038),(9585,6039),(8960,6039),
    (8318,6039),(7614,6039),(9149,6040),(8594,6040),(8289,6040),(7646,6040),(9722,6041),(8580,6041),
    (8627,6041),(8107,6041),(9957,6042),(9485,6042),(8690,6042),(10683,6043),(9991,6043),(9456,6043),
    (8691,6043),(10492,6044),(9779,6044),(8968,6044),(8616,6044),(5070,6045)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block49 : PLift (RangeResult 12845056 13107200 839845 855732) :=
  ⟨oneBlock 12845056 262144 839845 855732 [
    (9930,6045),(9536,6045),(8984,6045),(10829,6046),(9644,6046),(9278,6046),(10421,6047),(9646,6047),
    (8927,6047),(8269,6047),(9908,6048),(9265,6048),(8622,6048),(7933,6048),(9762,6049),(8777,6049),
    (8179,6049),(7965,6049),(9724,6050),(9452,6050),(8564,6050),(7920,6050),(9517,6051),(9132,6051),
    (7876,6051),(7293,6051),(9339,6052),(8475,6052),(7755,6052),(1222,6052)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block50 : PLift (RangeResult 13107200 13369344 855732 871735) :=
  ⟨oneBlock 13107200 262144 855732 871735 [
    (7238,6052),(8901,6053),(8308,6053),(8001,6053),(7480,6053),(6974,6053),(8802,6054),(7926,6054),
    (7313,6054),(7083,6054),(8992,6055),(8633,6055),(8127,6055),(7544,6055),(7115,6055),(9138,6056),
    (8343,6056),(7683,6056),(7193,6056),(8960,6057),(8360,6057),(7992,6057),(7424,6057),(6887,6057),
    (8569,6058),(8193,6058),(7870,6058),(7517,6058),(9006,6059),(8715,6059),(7995,6059),(7381,6059),
    (6481,6059)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block51 : PLift (RangeResult 13369344 13631488 871735 887642) :=
  ⟨oneBlock 13369344 262144 871735 887642 [
    (9299,6060),(8640,6060),(7935,6060),(7458,6060),(9435,6061),(8642,6061),(7935,6061),(7353,6061),
    (7046,6061),(8843,6062),(8060,6062),(7477,6062),(6816,6062),(8758,6063),(8200,6063),(7463,6063),
    (7124,6063),(6711,6063),(8411,6064),(8033,6064),(7372,6064),(6788,6064),(6419,6064),(8204,6065),
    (7727,6065),(7112,6065),(6759,6065),(6374,6065),(8304,6066),(7989,6066),(7359,6066),(7220,6066),
    (6914,6066),(7964,6067)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block52 : PLift (RangeResult 13631488 13893632 887642 903648) :=
  ⟨oneBlock 13631488 262144 887642 903648 [
    (8168,6067),(7652,6067),(7176,6067),(6700,6067),(8809,6068),(8684,6068),(8084,6068),(7438,6068),
    (9401,6069),(8623,6069),(8178,6069),(7793,6069),(7317,6069),(8978,6070),(8194,6070),(8057,6070),
    (7395,6070),(6949,6070),(8755,6071),(8288,6071),(8150,6071),(7657,6071),(9592,6072),(8921,6072),
    (8274,6072),(7567,6072),(7059,6072),(9492,6073),(8907,6073),(8076,6073),(7783,6073),(9776,6074),
    (251,6074)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block53 : PLift (RangeResult 13893632 14155776 903648 919552) :=
  ⟨oneBlock 13893632 262144 903648 919552 [
    (9165,6074),(9062,6074),(8508,6074),(10615,6075),(9725,6075),(9017,6075),(8433,6075),(9914,6076),
    (9157,6076),(8388,6076),(7788,6076),(6972,6076),(9076,6077),(8343,6077),(7743,6077),(7327,6077),
    (9698,6078),(8899,6078),(8067,6078),(7344,6078),(6959,6078),(9106,6079),(8685,6079),(8100,6079),
    (7576,6079),(7068,6079),(9499,6080),(8732,6080),(8101,6080),(7840,6080),(7237,6081)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block54 : PLift (RangeResult 14155776 14417920 919552 935512) :=
  ⟨oneBlock 14155776 262144 919552 935512 [
    (9200,6081),(8519,6081),(8056,6081),(7302,6081),(9220,6082),(8335,6082),(7765,6082),(7257,6082),
    (6748,6082),(8797,6083),(8398,6083),(7859,6083),(7382,6083),(6841,6083),(9051,6084),(8601,6084),
    (8307,6084),(7737,6084),(9674,6085),(8987,6085),(8648,6085),(7800,6085),(7430,6085),(9528,6086),
    (9390,6086),(9019,6086),(8233,6086),(10415,6087),(9962,6087),(9545,6087),(8138,6087)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block55 : PLift (RangeResult 14417920 14680064 935512 951351) :=
  ⟨oneBlock 14417920 262144 935512 951351 [
    (10704,6088),(9824,6088),(9069,6088),(8622,6088),(10599,6089),(9780,6089),(9102,6089),(8823,6089),
    (8083,6089),(9930,6090),(9273,6090),(8501,6090),(8038,6090),(9999,6091),(9274,6091),(8827,6091),
    (8271,6091),(10485,6092),(9986,6092),(9245,6092),(8843,6092),(7995,6092),(9907,6093),(8984,6093),
    (8506,6093),(7502,6093),(9868,6094),(9248,6094),(4856,6094)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block56 : PLift (RangeResult 14680064 14942208 951351 967230) :=
  ⟨oneBlock 14680064 262144 951351 967230 [
    (8360,6094),(7998,6094),(10215,6095),(9235,6095),(8663,6095),(8153,6095),(10377,6096),(9777,6096),
    (9082,6096),(8587,6096),(8201,6096),(10572,6097),(9794,6097),(9098,6097),(8775,6097),(10439,6098),
    (9703,6098),(9162,6098),(9147,6098),(10757,6099),(10122,6099),(9302,6099),(8360,6099),(10626,6100),
    (9845,6100),(9011,6100),(8439,6100),(7774,6100),(2570,6101)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block57 : PLift (RangeResult 14942208 15204352 967230 983029) :=
  ⟨oneBlock 14942208 262144 967230 983029 [
    (9780,6101),(9445,6101),(8394,6101),(7730,6101),(9853,6102),(8937,6102),(8735,6102),(7917,6102),
    (7436,6102),(9599,6103),(9109,6103),(8551,6103),(8026,6103),(10209,6104),(9512,6104),(8692,6104),
    (7966,6104),(7625,6104),(10016,6105),(9112,6105),(8446,6105),(7998,6105),(7441,6105),(9436,6106),
    (8959,6106),(8247,6106),(8184,6106),(7690,6106),(9538,6107),(8681,6107),(880,6107)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block58 : PLift (RangeResult 15204352 15466496 983029 998840) :=
  ⟨oneBlock 15204352 262144 983029 998840 [
    (7895,6107),(7288,6107),(9638,6108),(8899,6108),(8482,6108),(8157,6108),(7677,6108),(9878,6109),
    (9489,6109),(9010,6109),(8297,6109),(7802,6109),(9980,6110),(9460,6110),(8810,6110),(7989,6110),
    (7571,6110),(9849,6111),(9415,6111),(8440,6111),(7696,6111),(9670,6112),(9045,6112),(8116,6112),
    (7590,6112),(7217,6112),(9306,6113),(8490,6113),(7947,6113),(7358,6113),(5683,6113)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block59 : PLift (RangeResult 15466496 15728640 998840 1014733) :=
  ⟨oneBlock 15466496 262144 998840 1014733 [
    (6710,6113),(8865,6114),(8320,6114),(7871,6114),(7329,6114),(7143,6114),(9399,6115),(9128,6115),
    (8508,6115),(8104,6115),(7501,6115),(9997,6116),(9532,6116),(8819,6116),(8199,6116),(8122,6116),
    (10052,6117),(9503,6117),(8898,6117),(8386,6117),(10602,6118),(9799,6118),(9179,6118),(8946,6118),
    (8342,6118),(10239,6119),(9770,6119),(8885,6119),(8654,6119),(7342,6119)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block60 : PLift (RangeResult 15728640 15990784 1014733 1030567) :=
  ⟨oneBlock 15728640 262144 1014733 1030567 [
    (10070,6120),(9538,6120),(8996,6120),(8345,6120),(10503,6121),(9602,6121),(9122,6121),(8268,6121),
    (7509,6121),(9953,6122),(9061,6122),(8751,6122),(8192,6122),(7743,6122),(10644,6123),(10103,6123),
    (9450,6123),(8985,6123),(11118,6124),(10229,6124),(9374,6124),(9018,6124),(8599,6124),(10786,6125),
    (9904,6125),(9221,6125),(8786,6125),(10274,6126)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block61 : PLift (RangeResult 15990784 16252928 1030567 1046324) :=
  ⟨oneBlock 15990784 262144 1030567 1046324 [
    (10317,6126),(9627,6126),(8803,6126),(8260,6126),(10524,6127),(9861,6127),(9146,6127),(8122,6127),
    (7671,6127),(10237,6128),(9599,6128),(8931,6128),(8480,6128),(10416,6129),(9864,6129),(9228,6129),
    (8621,6129),(8451,6129),(10191,6130),(9509,6130),(8717,6130),(8172,6130),(7629,6130),(10029,6131),
    (9634,6131),(9231,6131),(8439,6131),(8049,6131),(6386,6132)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block62 : PLift (RangeResult 16252928 16515072 1046324 1062101) :=
  ⟨oneBlock 16252928 262144 1046324 1062101 [
    (9884,6132),(9481,6132),(9015,6132),(8191,6132),(10574,6133),(9996,6133),(9576,6133),(8581,6133),
    (7587,6133),(10007,6134),(9096,6134),(8691,6134),(7915,6134),(7292,6134),(9798,6135),(9144,6135),
    (8584,6135),(8149,6135),(7542,6135),(9791,6136),(9472,6136),(9224,6136),(8274,6136),(7544,6136),
    (10048,6137),(9489,6137),(8868,6137),(8727,6137),(8167,6137),(3437,6138)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block63 : PLift (RangeResult 16515072 16777216 1062101 1077871) :=
  ⟨oneBlock 16515072 262144 1062101 1077871 [
    (10276,6138),(9491,6138),(8791,6138),(8169,6138),(10049,6139),(9493,6139),(8932,6139),(7999,6139),
    (7781,6139),(7563,6139),(9950,6140),(9494,6140),(9043,6140),(8234,6140),(7704,6140),(10161,6141),
    (9745,6141),(8905,6141),(8577,6141),(7909,6141),(10434,6142),(9482,6142),(8875,6142),(8345,6142),
    (7972,6142),(10381,6143),(9733,6143),(9297,6143),(8549,6143),(810,6143)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block64 : PLift (RangeResult 16777216 17039360 1077871 1093705) :=
  ⟨oneBlock 16777216 262144 1077871 1093705 [
    (11073,6144),(10280,6144),(10186,6144),(9065,6144),(9019,6144),(11301,6145),(10577,6145),(9659,6145),
    (8786,6145),(8287,6145),(10875,6146),(9722,6146),(9317,6146),(8804,6146),(11115,6147),(10301,6147),
    (9818,6147),(9334,6147),(9148,6147),(11936,6148),(11035,6148),(10505,6148),(9944,6148),(12194,6149),
    (11582,6149),(8281,6149)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block65 : PLift (RangeResult 17039360 17301504 1093705 1109376) :=
  ⟨oneBlock 17039360 262144 1093705 1109376 [
    (10411,6149),(9556,6149),(11783,6150),(11382,6150),(10696,6150),(10103,6150),(12431,6151),(11509,6151),
    (10666,6151),(9950,6151),(12190,6152),(11230,6152),(10247,6152),(9296,6152),(8423,6152),(10749,6153),
    (10015,6153),(9298,6153),(8798,6153),(11475,6154),(10657,6154),(10032,6154),(9128,6154),(8643,6154),
    (11126,6155),(2350,6155)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block66 : PLift (RangeResult 17301504 17563648 1109376 1125209) :=
  ⟨oneBlock 17301504 262144 1109376 1125209 [
    (10649,6155),(10097,6155),(9925,6155),(12664,6156),(11893,6156),(10723,6156),(9864,6156),(9193,6156),
    (11878,6157),(11147,6157),(10787,6157),(10318,6157),(12449,6158),(11773,6158),(11023,6158),(10071,6158),
    (12770,6159),(12399,6159),(11853,6159),(11275,6159),(13201,6160),(12277,6160),(11964,6160),(1951,6160)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block67 : PLift (RangeResult 17563648 17825792 1125209 1140879) :=
  ⟨oneBlock 17563648 262144 1125209 1140879 [
    (10872,6160),(13399,6161),(12747,6161),(11685,6161),(10795,6161),(13221,6162),(12703,6162),(11796,6162),
    (10734,6162),(12856,6163),(12048,6163),(11533,6163),(10705,6163),(12787,6164),(12129,6164),(11190,6164),
    (10050,6164),(12375,6165),(11740,6165),(11255,6165),(10771,6165),(13306,6166),(1447,6166)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block68 : PLift (RangeResult 17825792 18087936 1140879 1156532) :=
  ⟨oneBlock 17825792 262144 1140879 1156532 [
    (12077,6166),(11101,6166),(10241,6166),(12455,6167),(12042,6167),(11321,6167),(10540,6167),(12887,6168),
    (11793,6168),(11261,6168),(10839,6168),(13522,6169),(13156,6169),(12546,6169),(11983,6169),(14158,6170),
    (12986,6170),(11860,6170),(11155,6170),(13339,6171),(12456,6171),(8426,6171)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block69 : PLift (RangeResult 18087936 18350080 1156532 1172267) :=
  ⟨oneBlock 18087936 262144 1156532 1172267 [
    (10384,6171),(10047,6171),(12723,6172),(11817,6172),(10924,6172),(10534,6172),(12622,6173),(11538,6173),
    (11036,6173),(9784,6173),(12224,6174),(11445,6174),(11038,6174),(10506,6174),(10240,6174),(12720,6175),
    (12356,6175),(11557,6175),(10774,6175),(13278,6176),(12608,6176),(12232,6176),(9757,6176)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block70 : PLift (RangeResult 18350080 18612224 1172267 1187884) :=
  ⟨oneBlock 18350080 262144 1172267 1187884 [
    (13586,6177),(12328,6177),(11483,6177),(10903,6177),(13109,6178),(12691,6178),(11657,6178),(10717,6178),
    (13745,6179),(12583,6179),(11534,6179),(10656,6179),(12909,6180),(11864,6180),(11113,6180),(10454,6180),
    (9780,6180),(12465,6181),(11381,6181),(11020,6181),(10283,6181),(13336,6182),(2547,6182)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block71 : PLift (RangeResult 18612224 18874368 1187884 1203569) :=
  ⟨oneBlock 18612224 262144 1187884 1203569 [
    (12223,6182),(11382,6182),(10850,6182),(13487,6183),(13000,6183),(12232,6183),(10977,6183),(13403,6184),
    (12437,6184),(11434,6184),(11073,6184),(10681,6184),(13210,6185),(12503,6185),(11608,6185),(11043,6185),
    (13158,6186),(12175,6186),(11641,6186),(10999,6186),(13543,6187),(9085,6187)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block72 : PLift (RangeResult 18874368 19136512 1203569 1219173) :=
  ⟨oneBlock 18874368 262144 1203569 1219173 [
    (12351,6187),(11079,6187),(10137,6187),(12393,6188),(11787,6188),(11378,6188),(10846,6188),(13783,6189),
    (12589,6189),(11585,6189),(11240,6189),(13730,6190),(12686,6190),(11681,6190),(11053,6190),(10535,6190),
    (13067,6191),(12060,6191),(11526,6191),(10505,6191),(12715,6192),(12360,6192),(1058,6192)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block73 : PLift (RangeResult 19136512 19398656 1219173 1234798) :=
  ⟨oneBlock 19136512 262144 1219173 1234798 [
    (11633,6192),(10586,6192),(13525,6193),(12472,6193),(11546,6193),(10870,6193),(10321,6193),(12547,6194),
    (11877,6194),(10810,6194),(10401,6194),(13152,6195),(12100,6195),(11346,6195),(10402,6195),(10089,6195),
    (12833,6196),(12448,6196),(11316,6196),(10797,6196),(13472,6197),(12513,6197),(5088,6197)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block74 : PLift (RangeResult 19398656 19660800 1234798 1250343) :=
  ⟨oneBlock 19398656 262144 1234798 1250343 [
    (11669,6197),(11192,6197),(14033,6198),(12986,6198),(12609,6198),(11918,6198),(13964,6199),(13114,6199),
    (11951,6199),(11196,6199),(10473,6199),(13063,6200),(12032,6200),(10946,6200),(10271,6200),(12459,6201),
    (11467,6201),(11137,6201),(10445,6201),(10020,6201),(12785,6202),(11800,6202),(614,6202)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block75 : PLift (RangeResult 19660800 19922944 1250343 1266011) :=
  ⟨oneBlock 19660800 262144 1250343 1266011 [
    (10871,6202),(10305,6202),(9534,6202),(12260,6203),(11928,6203),(11188,6203),(10291,6203),(12914,6204),
    (12497,6204),(11662,6204),(11206,6204),(10198,6204),(13256,6205),(12719,6205),(11680,6205),(10956,6205),
    (13737,6206),(13021,6206),(11965,6206),(11210,6206),(10831,6206),(13025,6207),(4890,6207)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block76 : PLift (RangeResult 19922944 20185088 1266011 1281651) :=
  ⟨oneBlock 19922944 262144 1266011 1281651 [
    (12432,6207),(11621,6207),(11148,6207),(13949,6208),(12804,6208),(12064,6208),(11418,6208),(14227,6209),
    (13263,6209),(12901,6209),(11924,6209),(14568,6210),(13769,6210),(12793,6210),(12100,6210),(11359,6210),
    (13839,6211),(12606,6211),(11945,6211),(11156,6211),(10258,6212)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block77 : PLift (RangeResult 20185088 20447232 1281651 1297106) :=
  ⟨oneBlock 20185088 262144 1281651 1297106 [
    (13977,6212),(12766,6212),(11662,6212),(10607,6212),(13450,6213),(12895,6213),(11869,6213),(10908,6213),
    (13949,6214),(12707,6214),(12140,6214),(11461,6214),(13880,6215),(12883,6215),(12189,6215),(11653,6215),
    (10990,6215),(13782,6216),(12569,6216),(11560,6216),(10914,6216),(3333,6217)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block78 : PLift (RangeResult 20447232 20709376 1297106 1312746) :=
  ⟨oneBlock 20447232 262144 1297106 1312746 [
    (13029,6217),(12461,6217),(11720,6217),(10695,6217),(9921,6217),(13077,6218),(12480,6218),(11737,6218),
    (10791,6218),(10066,6218),(12993,6219),(12403,6219),(11534,6219),(11203,6219),(13508,6220),(12862,6220),
    (12121,6220),(10842,6220),(10479,6220),(13314,6221),(13070,6221),(11838,6221)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block79 : PLift (RangeResult 20709376 20971520 1312746 1328230) :=
  ⟨oneBlock 20709376 262144 1312746 1328230 [
    (11855,6221),(11238,6221),(14115,6222),(13104,6222),(12282,6222),(11399,6222),(14172,6223),(13232,6223),
    (12395,6223),(11369,6223),(10232,6223),(13821,6224),(12618,6224),(12097,6224),(11355,6224),(14447,6225),
    (13205,6225),(12320,6225),(11547,6225),(10283,6225),(13573,6226),(1485,6226)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block80 : PLift (RangeResult 20971520 21233664 1328230 1343756) :=
  ⟨oneBlock 20971520 262144 1328230 1343756 [
    (12165,6226),(12054,6226),(11280,6226),(14389,6227),(13652,6227),(12546,6227),(12040,6227),(11440,6227),
    (14007,6228),(13133,6228),(11852,6228),(11284,6228),(14522,6229),(13262,6229),(12597,6229),(11191,6229),
    (10701,6229),(13680,6230),(12806,6230),(11809,6230),(10972,6230),(762,6230)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block81 : PLift (RangeResult 21233664 21495808 1343756 1359382) :=
  ⟨oneBlock 21233664 262144 1343756 1359382 [
    (13560,6231),(12476,6231),(11874,6231),(11495,6231),(11211,6231),(14302,6232),(13253,6232),(12304,6232),
    (11465,6232),(10881,6232),(13618,6233),(12812,6233),(12100,6233),(11452,6233),(10376,6233),(13709,6234),
    (12624,6234),(11770,6234),(11454,6234),(14794,6235),(14193,6235),(421,6235)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block82 : PLift (RangeResult 21495808 21757952 1359382 1374873) :=
  ⟨oneBlock 21495808 262144 1359382 1374873 [
    (13266,6235),(11756,6235),(10918,6235),(13778,6236),(12929,6236),(12075,6236),(11236,6236),(14548,6237),
    (13739,6237),(13105,6237),(11982,6237),(11333,6237),(14117,6238),(13235,6238),(12395,6238),(11762,6238),
    (11224,6238),(14303,6239),(13411,6239),(12319,6239),(8713,6239)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block83 : PLift (RangeResult 21757952 22020096 1374873 1390439) :=
  ⟨oneBlock 21757952 262144 1374873 1390439 [
    (14909,6240),(13968,6240),(13397,6240),(12590,6240),(11687,6240),(14721,6241),(13844,6241),(13114,6241),
    (12133,6241),(15333,6242),(14464,6242),(13323,6242),(12705,6242),(12198,6242),(15695,6243),(14783,6243),
    (13515,6243),(12771,6243),(15658,6244),(1336,6244)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block84 : PLift (RangeResult 22020096 22282240 1390439 1405839) :=
  ⟨oneBlock 22020096 262144 1390439 1405839 [
    (14385,6244),(14151,6244),(13755,6244),(16320,6245),(14820,6245),(13298,6245),(12410,6245),(15317,6246),
    (14299,6246),(13475,6246),(12396,6246),(15550,6247),(14460,6247),(12970,6247),(12018,6247),(11225,6247),
    (14072,6248),(13305,6248),(12353,6248),(1565,6248)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block85 : PLift (RangeResult 22282240 22544384 1405839 1421284) :=
  ⟨oneBlock 22282240 262144 1405839 1421284 [
    (11566,6248),(10672,6248),(13861,6249),(13212,6249),(12483,6249),(11277,6249),(14268,6250),(13261,6250),
    (12501,6250),(11374,6250),(10771,6250),(13915,6251),(12899,6251),(11630,6251),(10995,6251),(10472,6251),
    (13577,6252),(12758,6252),(11997,6252),(11219,6252),(10696,6252),(6740,6253)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block86 : PLift (RangeResult 22544384 22806528 1421284 1436785) :=
  ⟨oneBlock 22544384 262144 1421284 1436785 [
    (13657,6253),(13046,6253),(12476,6253),(11665,6253),(10999,6253),(14077,6254),(13255,6254),(12874,6254),
    (11430,6254),(10493,6254),(13930,6255),(13273,6255),(12591,6255),(11939,6255),(11257,6255),(14466,6256),
    (13688,6256),(12815,6256),(11878,6256),(14842,6257),(7493,6257)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block87 : PLift (RangeResult 22806528 23068672 1436785 1452313) :=
  ⟨oneBlock 22806528 262144 1436785 1452313 [
    (13154,6257),(12213,6257),(11245,6257),(10705,6257),(14378,6258),(13518,6258),(12661,6258),(11898,6258),
    (15246,6259),(14394,6259),(13489,6259),(12456,6259),(11725,6259),(14846,6260),(13761,6260),(13110,6260),
    (12633,6260),(12188,6260),(15192,6261),(13332,6261)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block88 : PLift (RangeResult 23068672 23330816 1452313 1467772) :=
  ⟨oneBlock 23068672 262144 1452313 1467772 [
    (13417,6261),(12730,6261),(15250,6262),(14498,6262),(13225,6262),(12479,6262),(11604,6262),(15294,6263),
    (14580,6263),(13243,6263),(12226,6263),(11288,6263),(14560,6264),(13708,6264),(12705,6264),(12117,6264),
    (15731,6265),(14600,6265),(14282,6265),(4607,6265)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block89 : PLift (RangeResult 23330816 23592960 1467772 1483173) :=
  ⟨oneBlock 23330816 262144 1467772 1483173 [
    (12919,6265),(12072,6265),(15427,6266),(14809,6266),(13537,6266),(12153,6266),(15358,6267),(14176,6267),
    (13411,6267),(12569,6267),(12155,6267),(15546,6268),(14083,6268),(13382,6268),(12332,6268),(15684,6269),
    (15136,6269),(13862,6269),(13098,6269),(435,6269)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block90 : PLift (RangeResult 23592960 23855104 1483173 1498551) :=
  ⟨oneBlock 23592960 262144 1483173 1498551 [
    (11835,6269),(15300,6270),(14437,6270),(13626,6270),(12384,6270),(12018,6270),(15408,6271),(14487,6271),
    (13501,6271),(12306,6271),(15483,6272),(14140,6272),(13407,6272),(12691,6272),(11974,6272),(15240,6273),
    (14063,6273),(13664,6273),(12152,6273),(4028,6273)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block91 : PLift (RangeResult 23855104 24117248 1498551 1514022) :=
  ⟨oneBlock 23855104 262144 1498551 1514022 [
    (10719,6273),(14298,6274),(13444,6274),(12711,6274),(12026,6274),(11835,6274),(14963,6275),(14147,6275),
    (12888,6275),(12140,6275),(11295,6275),(14896,6276),(14341,6276),(13257,6276),(12237,6276),(15576,6277),
    (14901,6277),(13992,6277),(12781,6277),(9697,6277)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block92 : PLift (RangeResult 24117248 24379392 1514022 1529497) :=
  ⟨oneBlock 24117248 262144 1514022 1529497 [
    (15533,6278),(14027,6278),(13389,6278),(13039,6278),(12305,6278),(15410,6279),(14667,6279),(13535,6279),
    (13104,6279),(12467,6279),(15789,6280),(14765,6280),(14287,6280),(13394,6280),(16933,6281),(15692,6281),
    (14592,6281),(13923,6281),(5293,6281)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block93 : PLift (RangeResult 24379392 24641536 1529497 1544878) :=
  ⟨oneBlock 24379392 262144 1529497 1544878 [
    (16676,6282),(15870,6282),(15073,6282),(14037,6282),(12999,6282),(16163,6283),(14724,6283),(14151,6283),
    (13097,6283),(16684,6284),(15605,6284),(14951,6284),(13801,6284),(12972,6284),(16331,6285),(15289,6285),
    (13900,6285),(9821,6285)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block94 : PLift (RangeResult 24641536 24903680 1544878 1560304) :=
  ⟨oneBlock 24641536 262144 1544878 1560304 [
    (12457,6285),(15689,6286),(15068,6286),(14620,6286),(13823,6286),(17504,6287),(16651,6287),(15133,6287),
    (13985,6287),(13793,6287),(17024,6288),(15520,6288),(14545,6288),(13221,6288),(16477,6289),(15778,6289),
    (14835,6289),(6021,6289)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block95 : PLift (RangeResult 24903680 25165824 1560304 1575661) :=
  ⟨oneBlock 24903680 262144 1560304 1575661 [
    (13446,6289),(16586,6290),(15365,6290),(14247,6290),(13465,6290),(13081,6290),(16344,6291),(15527,6291),
    (14617,6291),(13323,6291),(16356,6292),(15690,6292),(14923,6292),(13868,6292),(13373,6292),(17264,6293),
    (15645,6293),(9024,6293)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block96 : PLift (RangeResult 25165824 25427968 1575661 1590923) :=
  ⟨oneBlock 25165824 262144 1575661 1590923 [
    (13668,6293),(12752,6293),(16351,6294),(14624,6294),(13570,6294),(12323,6294),(11188,6294),(14972,6295),
    (14339,6295),(13172,6295),(12341,6295),(11734,6295),(15496,6296),(14566,6296),(13174,6296),(11992,6296),
    (11527,6296),(15413,6297),(14616,6297),(4326,6297)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block97 : PLift (RangeResult 25427968 25690112 1590923 1606310) :=
  ⟨oneBlock 25427968 262144 1590923 1606310 [
    (12705,6297),(11897,6297),(11370,6297),(15170,6298),(14874,6298),(13627,6298),(12299,6298),(11164,6298),
    (15279,6299),(14637,6299),(13565,6299),(12525,6299),(12189,6299),(15788,6300),(14655,6300),(13504,6300),
    (13071,6300),(12335,6300),(15209,6301),(6281,6301)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block98 : PLift (RangeResult 25690112 25952256 1606310 1621721) :=
  ⟨oneBlock 25690112 262144 1606310 1621721 [
    (14073,6301),(13154,6301),(12625,6301),(11618,6301),(15270,6302),(14564,6302),(14020,6302),(12724,6302),
    (12195,6302),(15955,6303),(15191,6303),(14551,6303),(13494,6303),(12614,6303),(15840,6304),(15274,6304),
    (14105,6304),(13385,6304),(11492,6304)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block99 : PLift (RangeResult 25952256 26214400 1621721 1637054) :=
  ⟨oneBlock 25952256 262144 1621721 1637054 [
    (16160,6305),(14844,6305),(14380,6305),(13627,6305),(12538,6305),(16171,6306),(15231,6306),(14173,6306),
    (13373,6306),(12236,6306),(16265,6307),(14945,6307),(14352,6307),(13584,6307),(12654,6307),(16278,6308),
    (15028,6308),(13666,6308),(2639,6308)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block100 : PLift (RangeResult 26214400 26476544 1637054 1652422) :=
  ⟨oneBlock 26214400 262144 1637054 1652422 [
    (12885,6308),(16850,6309),(15415,6309),(13844,6309),(13204,6309),(12514,6309),(16223,6310),(15097,6310),
    (14456,6310),(13206,6310),(12212,6310),(16123,6311),(15228,6311),(14651,6311),(14474,6311),(13417,6311),
    (16409,6312),(15503,6312),(433,6312)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block101 : PLift (RangeResult 26476544 26738688 1652422 1667776) :=
  ⟨oneBlock 26476544 262144 1652422 1667776 [
    (14910,6312),(13980,6312),(13322,6312),(16873,6313),(16051,6313),(15232,6313),(14608,6313),(13228,6313),
    (17336,6314),(15861,6314),(14883,6314),(14161,6314),(17893,6315),(16586,6315),(15575,6315),(14468,6315),
    (13971,6315),(3206,6316)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block102 : PLift (RangeResult 26738688 27000832 1667776 1683115) :=
  ⟨oneBlock 26738688 262144 1667776 1683115 [
    (17044,6316),(15497,6316),(14712,6316),(13556,6316),(12754,6316),(16398,6317),(15372,6317),(14296,6317),
    (13703,6317),(12900,6317),(16942,6318),(15904,6318),(14812,6318),(14026,6318),(17467,6319),(16902,6319),
    (15585,6319),(4274,6319)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block103 : PLift (RangeResult 27000832 27262976 1683115 1698416) :=
  ⟨oneBlock 27000832 262144 1683115 1698416 [
    (14698,6319),(13756,6319),(17578,6320),(16054,6320),(15187,6320),(14464,6320),(14047,6320),(17738,6321),
    (16473,6321),(15720,6321),(14868,6321),(18440,6322),(17232,6322),(16011,6322),(14758,6322),(13987,6322),
    (11133,6323)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block104 : PLift (RangeResult 27262976 27525120 1698416 1713701) :=
  ⟨oneBlock 27262976 262144 1698416 1713701 [
    (16607,6323),(15146,6323),(14504,6323),(13363,6323),(17072,6324),(16177,6324),(15116,6324),(13912,6324),
    (13125,6324),(17053,6325),(15955,6325),(15392,6325),(14718,6325),(13288,6325),(17100,6326),(15973,6326),
    (14704,6326),(2939,6326)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block105 : PLift (RangeResult 27525120 27787264 1713701 1729040) :=
  ⟨oneBlock 27525120 262144 1713701 1729040 [
    (13934,6326),(17627,6327),(16619,6327),(15816,6327),(15124,6327),(15028,6327),(18172,6328),(17297,6328),
    (15786,6328),(14870,6328),(13760,6328),(17110,6329),(16222,6329),(15789,6329),(15355,6329),(18681,6330),
    (4954,6330)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block106 : PLift (RangeResult 27787264 28049408 1729040 1744365) :=
  ⟨oneBlock 27787264 262144 1729040 1744365 [
    (17077,6330),(15759,6330),(14988,6330),(13524,6330),(17041,6331),(15922,6331),(15344,6331),(14395,6331),
    (13783,6331),(17940,6332),(16666,6332),(15812,6332),(15121,6332),(18645,6333),(17263,6333),(16877,6333),
    (5987,6333)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block107 : PLift (RangeResult 28049408 28311552 1744365 1759651) :=
  ⟨oneBlock 28049408 262144 1744365 1759651 [
    (15589,6333),(18513,6334),(17669,6334),(16848,6334),(15223,6334),(14209,6334),(18512,6335),(17125,6335),
    (15853,6335),(14324,6335),(13922,6335),(18093,6336),(17304,6336),(15904,6336),(15550,6336),(17506,6337)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block108 : PLift (RangeResult 28311552 28573696 1759651 1774897) :=
  ⟨oneBlock 28311552 262144 1759651 1774897 [
    (18503,6337),(17323,6337),(16052,6337),(14683,6337),(18588,6338),(17456,6338),(16086,6338),(15201,6338),
    (14685,6338),(18330,6339),(16750,6339),(16089,6339),(15574,6339),(19470,6340),(18009,6340),(9345,6340)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block109 : PLift (RangeResult 28573696 28835840 1774897 1790108) :=
  ⟨oneBlock 28573696 262144 1774897 1790108 [
    (16283,6340),(15592,6340),(19051,6341),(18124,6341),(17029,6341),(16095,6341),(15063,6341),(19276,6342),
    (17177,6342),(16339,6342),(15630,6342),(19289,6343),(17728,6343),(16938,6343),(15246,6343),(7284,6343)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block110 : PLift (RangeResult 28835840 29097984 1790108 1805352) :=
  ⟨oneBlock 28835840 262144 1790108 1805352 [
    (18610,6344),(17651,6344),(16779,6344),(15555,6344),(14845,6344),(18884,6345),(17847,6345),(16460,6345),
    (14928,6345),(14187,6345),(18222,6346),(17076,6346),(16302,6346),(14931,6346),(13931,6346),(15936,6347)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block111 : PLift (RangeResult 29097984 29360128 1805352 1820645) :=
  ⟨oneBlock 29097984 262144 1805352 1820645 [
    (16896,6347),(15869,6347),(15030,6347),(13805,6347),(17864,6348),(16485,6348),(15388,6348),(14646,6348),
    (13274,6348),(17105,6349),(16100,6349),(15197,6349),(14390,6349),(14261,6349),(18264,6350),(17329,6350),
    (10241,6350)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block112 : PLift (RangeResult 29360128 29622272 1820645 1835828) :=
  ⟨oneBlock 29360128 262144 1820645 1835828 [
    (16221,6350),(15441,6350),(18973,6351),(17687,6351),(15799,6351),(14718,6351),(13749,6351),(17793,6352),
    (16867,6352),(15576,6352),(14704,6352),(14107,6352),(18195,6353),(16822,6353),(15691,6353),(15078,6353),
    (4723,6353)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block113 : PLift (RangeResult 29622272 29884416 1835828 1851080) :=
  ⟨oneBlock 29622272 262144 1835828 1851080 [
    (14019,6353),(17711,6354),(16630,6354),(15985,6354),(14822,6354),(14305,6354),(18613,6355),(18006,6355),
    (16246,6355),(14889,6355),(13742,6355),(17644,6356),(16329,6356),(15344,6356),(14391,6356),(14294,6356),
    (9174,6357)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block114 : PLift (RangeResult 29884416 30146560 1851080 1866444) :=
  ⟨oneBlock 29884416 262144 1851080 1866444 [
    (18208,6357),(17334,6357),(16089,6357),(15379,6357),(20079,6358),(18742,6358),(17789,6358),(16867,6358),
    (16012,6358),(20225,6359),(18955,6359),(17840,6359),(17081,6359),(20660,6360),(10884,6360)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block115 : PLift (RangeResult 30146560 30408704 1866444 1881720) :=
  ⟨oneBlock 30146560 262144 1866444 1881720 [
    (19468,6360),(17698,6360),(16777,6360),(21031,6361),(19899,6361),(18784,6361),(17458,6361),(21386,6362),
    (20419,6362),(19159,6362),(18545,6362),(22597,6363),(20504,6363),(8419,6363)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block116 : PLift (RangeResult 30408704 30670848 1881720 1896956) :=
  ⟨oneBlock 30408704 262144 1881720 1896956 [
    (19556,6363),(17739,6363),(21013,6364),(19473,6364),(18308,6364),(17095,6364),(21400,6365),(20479,6365),
    (19055,6365),(18036,6365),(17437,6365),(21548,6366),(20239,6366),(10766,6366)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block117 : PLift (RangeResult 30670848 30932992 1896956 1912154) :=
  ⟨oneBlock 30670848 262144 1896956 1912154 [
    (19246,6366),(23082,6367),(21667,6367),(20194,6367),(18787,6367),(22629,6368),(21185,6368),(19809,6368),
    (18935,6368),(22856,6369),(21868,6369),(20557,6369),(11329,6369)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block118 : PLift (RangeResult 30932992 31195136 1912154 1927204) :=
  ⟨oneBlock 30932992 262144 1912154 1927204 [
    (18568,6369),(22372,6370),(20771,6370),(18764,6370),(18035,6370),(22047,6371),(19981,6371),(18751,6371),
    (17180,6371),(21139,6372),(20340,6372),(19289,6372),(17684,6372),(7223,6372)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block119 : PLift (RangeResult 31195136 31457280 1927204 1942384) :=
  ⟨oneBlock 31195136 262144 1927204 1942384 [
    (20977,6373),(19697,6373),(18659,6373),(17397,6373),(15922,6373),(21027,6374),(19602,6374),(18274,6374),
    (17610,6374),(21495,6375),(19994,6375),(18909,6375),(17759,6375),(14822,6375)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block120 : PLift (RangeResult 31457280 31719424 1942384 1957543) :=
  ⟨oneBlock 31457280 262144 1942384 1957543 [
    (20544,6376),(19155,6376),(17600,6376),(16222,6376),(20586,6377),(19158,6377),(18494,6377),(17506,6377),
    (16224,6377),(20798,6378),(19146,6378),(18108,6378),(17605,6378),(16390,6378),(4608,6379)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block121 : PLift (RangeResult 31719424 31981568 1957543 1972741) :=
  ⟨oneBlock 31719424 262144 1957543 1972741 [
    (20017,6379),(18614,6379),(17268,6379),(16440,6379),(20830,6380),(19541,6380),(18358,6380),(17400,6380),
    (16898,6380),(21269,6381),(19463,6381),(18587,6381),(17063,6381),(20396,6382)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block122 : PLift (RangeResult 31981568 32243712 1972741 1987890) :=
  ⟨oneBlock 31981568 262144 1972741 1987890 [
    (20370,6382),(19288,6382),(17845,6382),(16270,6382),(20636,6383),(19583,6383),(18188,6383),(18042,6383),
    (16631,6383),(21123,6384),(19733,6384),(18418,6384),(16925,6384),(19092,6385)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block123 : PLift (RangeResult 32243712 32505856 1987890 2003091) :=
  ⟨oneBlock 32243712 262144 1987890 2003091 [
    (20176,6385),(18632,6385),(17658,6385),(17075,6385),(21220,6386),(19983,6386),(18846,6386),(17613,6386),
    (22339,6387),(20716,6387),(19142,6387),(18265,6387),(17454,6387),(13025,6388)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block124 : PLift (RangeResult 32505856 32768000 2003091 2018258) :=
  ⟨oneBlock 32505856 262144 2003091 2018258 [
    (21072,6388),(19681,6388),(18691,6388),(17342,6388),(21903,6389),(20773,6389),(19310,6389),(18434,6389),
    (22162,6390),(21085,6390),(20126,6390),(18843,6390),(17657,6390),(5065,6391)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block125 : PLift (RangeResult 32768000 33030144 2018258 2033399) :=
  ⟨oneBlock 32768000 262144 2018258 2033399 [
    (21664,6391),(20065,6391),(18830,6391),(17302,6391),(21742,6392),(20327,6392),(19223,6392),(18037,6392),
    (22390,6393),(21437,6393),(20607,6393),(19421,6393),(18040,6393),(3059,6394)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block126 : PLift (RangeResult 33030144 33292288 2033399 2048560) :=
  ⟨oneBlock 33030144 262144 2033399 2048560 [
    (22081,6394),(20253,6394),(18709,6394),(17734,6394),(22344,6395),(21183,6395),(19867,6395),(18728,6395),
    (17705,6395),(21906,6396),(20439,6396),(19480,6396),(18439,6396),(3276,6397)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block127 : PLift (RangeResult 33292288 33554432 2048560 2063689) :=
  ⟨oneBlock 33292288 262144 2048560 2063689 [
    (23070,6397),(21466,6397),(20329,6397),(19109,6397),(23776,6398),(22447,6398),(21194,6398),(19957,6398),
    (18690,6398),(23145,6399),(21735,6399),(19847,6399),(7379,6399)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block128 : PLift (RangeResult 33554432 33816576 2063689 2078843) :=
  ⟨oneBlock 33554432 262144 2063689 2078843 [
    (23784,6400),(22650,6400),(20908,6400),(19444,6400),(18093,6400),(22707,6401),(21302,6401),(20277,6401),
    (19057,6401),(23032,6402),(22543,6402),(21208,6402),(7139,6402)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block129 : PLift (RangeResult 33816576 34078720 2078843 2093862) :=
  ⟨oneBlock 33816576 262144 2078843 2093862 [
    (19506,6402),(24059,6403),(22693,6403),(21488,6403),(20056,6403),(24483,6404),(22599,6404),(20597,6404),
    (19391,6404),(18252,6404),(22565,6405),(21105,6405),(5350,6405)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block130 : PLift (RangeResult 34078720 34340864 2093862 2108859) :=
  ⟨oneBlock 34078720 262144 2093862 2108859 [
    (18881,6405),(17588,6405),(22532,6406),(20815,6406),(19382,6406),(17867,6406),(16499,6406),(21198,6407),
    (19776,6407),(18050,6407),(17055,6407),(16095,6407),(20954,6408),(15452,6408)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block131 : PLift (RangeResult 34340864 34603008 2108859 2123972) :=
  ⟨oneBlock 34340864 262144 2108859 2123972 [
    (18144,6408),(16683,6408),(15120,6408),(20302,6409),(19099,6409),(18055,6409),(16246,6409),(15677,6409),
    (20628,6410),(19395,6410),(18466,6410),(17602,6410),(16298,6410),(21085,6411),(9344,6411)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block132 : PLift (RangeResult 34603008 34865152 2123972 2138970) :=
  ⟨oneBlock 34603008 262144 2123972 2138970 [
    (19541,6411),(18159,6411),(17051,6411),(15355,6411),(19669,6412),(18570,6412),(17168,6412),(16418,6412),
    (14983,6412),(19472,6413),(18590,6413),(17757,6413),(16812,6413),(15230,6413),(13860,6413),(3509,6414)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block133 : PLift (RangeResult 34865152 35127296 2138970 2154052) :=
  ⟨oneBlock 34865152 262144 2138970 2154052 [
    (19309,6414),(18527,6414),(17630,6414),(16538,6414),(15820,6414),(20470,6415),(19492,6415),(18057,6415),
    (16866,6415),(15660,6415),(20160,6416),(18778,6416),(17505,6416),(16331,6416),(11001,6416)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block134 : PLift (RangeResult 35127296 35389440 2154052 2169168) :=
  ⟨oneBlock 35127296 262144 2154052 2169168 [
    (14841,6416),(19689,6417),(18879,6417),(17426,6417),(16317,6417),(15518,6417),(14816,6417),(19870,6418),
    (18784,6418),(17283,6418),(16108,6418),(15455,6418),(20571,6419),(19196,6419),(17391,6419)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block135 : PLift (RangeResult 35389440 35651584 2169168 2184255) :=
  ⟨oneBlock 35389440 262144 2169168 2184255 [
    (16984,6419),(16470,6419),(21192,6420),(19770,6420),(18529,6420),(17076,6420),(16081,6420),(15003,6420),
    (20150,6421),(19153,6421),(18124,6421),(16589,6421),(15463,6421),(20656,6422),(10904,6422)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block136 : PLift (RangeResult 35651584 35913728 2184255 2199279) :=
  ⟨oneBlock 35651584 262144 2184255 2199279 [
    (18900,6422),(17931,6422),(16576,6422),(15351,6422),(20086,6423),(19290,6423),(18065,6423),(17150,6423),
    (16513,6423),(20937,6424),(19603,6424),(18607,6424),(17218,6424),(16140,6424),(9777,6424)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block137 : PLift (RangeResult 35913728 36175872 2199279 2214355) :=
  ⟨oneBlock 35913728 262144 2199279 2214355 [
    (20032,6425),(19002,6425),(17777,6425),(16372,6425),(15407,6425),(20857,6426),(20133,6426),(19054,6426),
    (17339,6426),(16374,6426),(15508,6426),(20762,6427),(19499,6427),(18289,6427),(5739,6427)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block138 : PLift (RangeResult 36175872 36438016 2214355 2229453) :=
  ⟨oneBlock 36175872 262144 2214355 2229453 [
    (16244,6427),(15004,6427),(19897,6428),(19011,6428),(17639,6428),(17360,6428),(16167,6428),(21990,6429),
    (20110,6429),(19538,6429),(18442,6429),(17462,6429),(21827,6430),(20473,6430),(980,6430)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block139 : PLift (RangeResult 36438016 36700160 2229453 2244481) :=
  ⟨oneBlock 36438016 262144 2229453 2244481 [
    (19036,6430),(17759,6430),(17170,6430),(16238,6430),(21226,6431),(19691,6431),(18613,6431),(16960,6431),
    (16551,6431),(21701,6432),(20219,6432),(18860,6432),(17847,6432),(16145,6432),(4128,6433)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block140 : PLift (RangeResult 36700160 36962304 2244481 2259433) :=
  ⟨oneBlock 36700160 262144 2244481 2259433 [
    (20928,6433),(19486,6433),(17882,6433),(17375,6433),(16557,6433),(21572,6434),(20454,6434),(18589,6434),
    (17394,6434),(16413,6434),(15283,6434),(19808,6435),(17970,6435),(17054,6435),(5379,6435)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block141 : PLift (RangeResult 36962304 37224448 2259433 2274583) :=
  ⟨oneBlock 36962304 262144 2259433 2274583 [
    (15684,6435),(15106,6435),(20659,6436),(19381,6436),(18349,6436),(17236,6436),(16238,6436),(15223,6436),
    (20580,6437),(20236,6437),(19531,6437),(17959,6437),(16945,6437),(22120,6438),(6897,6438)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block142 : PLift (RangeResult 37224448 37486592 2274583 2289574) :=
  ⟨oneBlock 37224448 262144 2274583 2289574 [
    (20022,6438),(18667,6438),(16914,6438),(16047,6438),(20960,6439),(19701,6439),(18588,6439),(17507,6439),
    (16508,6439),(15656,6439),(21323,6440),(19541,6440),(17968,6440),(16871,6440),(5871,6440)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block143 : PLift (RangeResult 37486592 37748736 2289574 2304655) :=
  ⟨oneBlock 37486592 262144 2289574 2304655 [
    (15783,6440),(21275,6441),(20511,6441),(19462,6441),(17857,6441),(16661,6441),(21784,6442),(20743,6442),
    (19318,6442),(17909,6442),(17516,6442),(16254,6442),(21329,6443),(15742,6443)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block144 : PLift (RangeResult 37748736 38010880 2304655 2319602) :=
  ⟨oneBlock 37748736 262144 2304655 2319602 [
    (19442,6443),(17797,6443),(16699,6443),(21854,6444),(20029,6444),(19669,6444),(18111,6444),(16473,6444),
    (15358,6444),(20923,6445),(19819,6445),(17983,6445),(17230,6445),(15868,6445),(4889,6446)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block145 : PLift (RangeResult 38010880 38273024 2319602 2334718) :=
  ⟨oneBlock 38010880 262144 2319602 2334718 [
    (21150,6446),(19511,6446),(18593,6446),(17954,6446),(17346,6446),(16003,6446),(21550,6447),(20072,6447),
    (18777,6447),(18317,6447),(17136,6447),(22569,6448),(21223,6448),(11943,6448)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block146 : PLift (RangeResult 38273024 38535168 2334718 2349759) :=
  ⟨oneBlock 38273024 262144 2334718 2349759 [
    (19531,6448),(18632,6448),(17976,6448),(23392,6449),(21424,6449),(20046,6449),(18996,6449),(17207,6449),
    (23034,6450),(21739,6450),(20328,6450),(18884,6450),(18310,6450),(2645,6451)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block147 : PLift (RangeResult 38535168 38797312 2349759 2364789) :=
  ⟨oneBlock 38535168 262144 2349759 2364789 [
    (23229,6451),(21366,6451),(19724,6451),(18969,6451),(17476,6451),(22513,6452),(21221,6452),(19629,6452),
    (18858,6452),(18283,6452),(23762,6453),(22259,6453),(14855,6453)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block148 : PLift (RangeResult 38797312 39059456 2364789 2379786) :=
  ⟨oneBlock 38797312 262144 2364789 2379786 [
    (20568,6453),(19304,6453),(18106,6453),(23718,6454),(22590,6454),(21261,6454),(19997,6454),(25655,6455),
    (23777,6455),(22118,6455),(20575,6455),(18851,6455),(5624,6456)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block149 : PLift (RangeResult 39059456 39321600 2379786 2394890) :=
  ⟨oneBlock 39059456 262144 2379786 2394890 [
    (23993,6456),(22631,6456),(21416,6456),(20200,6456),(19100,6456),(24777,6457),(22799,6457),(21058,6457),
    (20236,6457),(19202,6457),(23959,6458),(22773,6458)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block150 : PLift (RangeResult 39321600 39583744 2394890 2409895) :=
  ⟨oneBlock 39321600 262144 2394890 2409895 [
    (22915,6458),(21504,6458),(20257,6458),(25277,6459),(24154,6459),(22609,6459),(21459,6459),(26215,6460),
    (25078,6460),(23747,6460),(22416,6460),(6513,6460)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block151 : PLift (RangeResult 39583744 39845888 2409895 2424907) :=
  ⟨oneBlock 39583744 262144 2409895 2424907 [
    (26920,6461),(25772,6461),(24935,6461),(23093,6461),(22042,6461),(27440,6462),(25070,6462),(23640,6462),
    (22292,6462),(27557,6463),(13383,6463)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block152 : PLift (RangeResult 39845888 40108032 2424907 2439815) :=
  ⟨oneBlock 39845888 262144 2424907 2439815 [
    (24697,6463),(23151,6463),(21424,6463),(27183,6464),(24832,6464),(22908,6464),(21427,6464),(27202,6465),
    (25033,6465),(23240,6465),(21047,6465)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block153 : PLift (RangeResult 40108032 40370176 2439815 2454858) :=
  ⟨oneBlock 40108032 262144 2439815 2454858 [
    (20928,6465),(26729,6466),(25071,6466),(23408,6466),(21748,6466),(20349,6466),(25616,6467),(24432,6467),
    (23281,6467),(22179,6467),(27674,6468),(729,6468)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block154 : PLift (RangeResult 40370176 40632320 2454858 2469725) :=
  ⟨oneBlock 40370176 262144 2454858 2469725 [
    (26209,6468),(25046,6468),(22725,6468),(21212,6468),(26923,6469),(25099,6469),(23750,6469),(22416,6469),
    (27107,6470),(24988,6470),(16669,6470)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block155 : PLift (RangeResult 40632320 40894464 2469725 2484775) :=
  ⟨oneBlock 40632320 262144 2469725 2484775 [
    (22130,6470),(21136,6470),(26403,6471),(24860,6471),(23955,6471),(22836,6471),(21600,6471),(27561,6472),
    (25573,6472),(24420,6472),(21670,6472)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block156 : PLift (RangeResult 40894464 41156608 2484775 2499710) :=
  ⟨oneBlock 40894464 262144 2484775 2499710 [
    (27975,6473),(25692,6473),(23699,6473),(22398,6473),(21575,6473),(26812,6474),(25152,6474),(23160,6474),
    (22188,6474),(27933,6475),(15560,6475)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block157 : PLift (RangeResult 41156608 41418752 2499710 2514594) :=
  ⟨oneBlock 41156608 262144 2499710 2514594 [
    (25380,6475),(23740,6475),(22603,6475),(28186,6476),(25672,6476),(23974,6476),(22426,6476),(21239,6476),
    (27121,6477),(25198,6477),(16605,6477)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block158 : PLift (RangeResult 41418752 41680896 2514594 2529470) :=
  ⟨oneBlock 41418752 262144 2514594 2529470 [
    (22107,6477),(20930,6477),(26910,6478),(24971,6478),(23521,6478),(21758,6478),(27934,6479),(25239,6479),
    (23212,6479),(21332,6479),(20211,6479),(4019,6480)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block159 : PLift (RangeResult 41680896 41943040 2529470 2544401) :=
  ⟨oneBlock 41680896 262144 2529470 2544401 [
    (25735,6480),(24600,6480),(22935,6480),(21452,6480),(20412,6480),(26329,6481),(24852,6481),(23862,6481),
    (21966,6481),(20729,6481),(26218,6482),(3054,6482)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block160 : PLift (RangeResult 41943040 42205184 2544401 2559336) :=
  ⟨oneBlock 41943040 262144 2544401 2559336 [
    (23600,6482),(22465,6482),(20353,6482),(18984,6482),(24639,6483),(23343,6483),(21643,6483),(20555,6483),
    (19333,6483),(25154,6484),(23973,6484),(18102,6484)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block161 : PLift (RangeResult 42205184 42467328 2559336 2574297) :=
  ⟨oneBlock 42205184 262144 2559336 2574297 [
    (21694,6484),(20360,6484),(26412,6485),(25016,6485),(24077,6485),(22789,6485),(21040,6485),(26845,6486),
    (25236,6486),(23486,6486),(21802,6486),(3387,6486)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block162 : PLift (RangeResult 42467328 42729472 2574297 2589210) :=
  ⟨oneBlock 42467328 262144 2574297 2589210 [
    (27373,6487),(26395,6487),(24744,6487),(22863,6487),(21624,6487),(26738,6488),(25178,6488),(23626,6488),
    (22751,6488),(21083,6488),(19769,6489)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block163 : PLift (RangeResult 42729472 42991616 2589210 2604053) :=
  ⟨oneBlock 42729472 262144 2589210 2604053 [
    (25469,6489),(23877,6489),(22474,6489),(21450,6489),(27391,6490),(25682,6490),(23468,6490),(21669,6490),
    (19967,6490),(26157,6491),(24315,6491),(225,6491)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block164 : PLift (RangeResult 42991616 43253760 2604053 2618966) :=
  ⟨oneBlock 42991616 262144 2604053 2618966 [
    (22570,6491),(20945,6491),(19756,6491),(25286,6492),(23972,6492),(23063,6492),(21510,6492),(20222,6492),
    (26596,6493),(24587,6493),(23017,6493),(10620,6493)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block165 : PLift (RangeResult 43253760 43515904 2618966 2633905) :=
  ⟨oneBlock 43253760 262144 2618966 2633905 [
    (20990,6493),(19316,6493),(25263,6494),(24062,6494),(22443,6494),(21088,6494),(20228,6494),(25878,6495),
    (24182,6495),(23356,6495),(21554,6495),(13784,6495)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block166 : PLift (RangeResult 43515904 43778048 2633905 2648744) :=
  ⟨oneBlock 43515904 262144 2633905 2648744 [
    (27156,6496),(25641,6496),(24665,6496),(22830,6496),(21012,6496),(26813,6497),(24637,6497),(23049,6497),
    (21610,6497),(20172,6497),(24559,6498)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block167 : PLift (RangeResult 43778048 44040192 2648744 2663655) :=
  ⟨oneBlock 43778048 262144 2648744 2663655 [
    (24716,6498),(22772,6498),(21449,6498),(20506,6498),(19481,6498),(25088,6499),(23024,6499),(21468,6499),
    (20973,6499),(20394,6499),(26630,6500),(15643,6500)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block168 : PLift (RangeResult 44040192 44302336 2663655 2678553) :=
  ⟨oneBlock 44040192 262144 2663655 2678553 [
    (23629,6500),(22531,6500),(21026,6500),(19355,6500),(24965,6501),(23296,6501),(21989,6501),(20814,6501),
    (19821,6501),(25449,6502),(23697,6502),(15572,6502)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block169 : PLift (RangeResult 44302336 44564480 2678553 2693393) :=
  ⟨oneBlock 44302336 262144 2678553 2693393 [
    (22489,6502),(20701,6502),(19411,6502),(25654,6503),(23668,6503),(22293,6503),(21036,6503),(19944,6503),
    (26187,6504),(24218,6504),(22943,6504),(13600,6504)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block170 : PLift (RangeResult 44564480 44826624 2693393 2708355) :=
  ⟨oneBlock 44564480 262144 2693393 2708355 [
    (20550,6504),(19732,6504),(26359,6505),(24652,6505),(23361,6505),(21440,6505),(20944,6505),(26777,6506),
    (25352,6506),(24209,6506),(22785,6506),(5983,6506)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block171 : PLift (RangeResult 44826624 45088768 2708355 2723262) :=
  ⟨oneBlock 44826624 262144 2708355 2723262 [
    (20793,6506),(26386,6507),(25290,6507),(23418,6507),(21944,6507),(20503,6507),(27087,6508),(25277,6508),
    (23819,6508),(22097,6508),(21699,6508),(3831,6509)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block172 : PLift (RangeResult 45088768 45350912 2723262 2738200) :=
  ⟨oneBlock 45088768 262144 2723262 2738200 [
    (27684,6509),(25663,6509),(24188,6509),(22233,6509),(21073,6509),(26700,6510),(25931,6510),(24557,6510),
    (23347,6510),(22004,6510),(18764,6511)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block173 : PLift (RangeResult 45350912 45613056 2738200 2753124) :=
  ⟨oneBlock 45350912 262144 2738200 2753124 [
    (27895,6511),(26516,6511),(24660,6511),(22903,6511),(29694,6512),(28244,6512),(26073,6512),(24962,6512),
    (23122,6512),(28075,6513)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block174 : PLift (RangeResult 45613056 45875200 2753124 2767974) :=
  ⟨oneBlock 45613056 262144 2753124 2767974 [
    (28035,6513),(26426,6513),(24651,6513),(30766,6514),(28817,6514),(27425,6514),(26131,6514),(23196,6514),
    (29630,6515),(17067,6515)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block175 : PLift (RangeResult 45875200 46137344 2767974 2782805) :=
  ⟨oneBlock 45875200 262144 2767974 2782805 [
    (27111,6515),(25887,6515),(24858,6515),(30698,6516),(28047,6516),(26587,6516),(24763,6516),(31216,6517),
    (29363,6517),(13614,6517)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block176 : PLift (RangeResult 46137344 46399488 2782805 2797625) :=
  ⟨oneBlock 46137344 262144 2782805 2797625 [
    (26033,6517),(24302,6517),(30526,6518),(28985,6518),(27011,6518),(25352,6518),(23112,6518),(29472,6519),
    (28177,6519),(19174,6519)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block177 : PLift (RangeResult 46399488 46661632 2797625 2812509) :=
  ⟨oneBlock 46399488 262144 2797625 2812509 [
    (24933,6519),(23746,6519),(29711,6520),(27899,6520),(26339,6520),(24829,6520),(22954,6520),(29286,6521),
    (28153,6521),(24294,6521)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block178 : PLift (RangeResult 46661632 46923776 2812509 2827371) :=
  ⟨oneBlock 46661632 262144 2812509 2827371 [
    (25057,6521),(23770,6521),(30074,6522),(27775,6522),(26083,6522),(24804,6522),(31239,6523),(29026,6523),
    (27481,6523),(16835,6523)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block179 : PLift (RangeResult 46923776 47185920 2827371 2842191) :=
  ⟨oneBlock 46923776 262144 2827371 2842191 [
    (24977,6523),(31146,6524),(29230,6524),(27602,6524),(25892,6524),(23849,6524),(29461,6525),(28072,6525),
    (26510,6525),(15405,6525)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block180 : PLift (RangeResult 47185920 47448064 2842191 2856983) :=
  ⟨oneBlock 47185920 262144 2842191 2856983 [
    (24361,6525),(30912,6526),(28475,6526),(26764,6526),(25186,6526),(24055,6526),(30123,6527),(28397,6527),
    (26685,6527),(17186,6527)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block181 : PLift (RangeResult 47448064 47710208 2856983 2871770) :=
  ⟨oneBlock 47448064 262144 2856983 2871770 [
    (23440,6527),(29415,6528),(28733,6528),(26723,6528),(25261,6528),(23631,6528),(29805,6529),(28140,6529),
    (25646,6529),(21350,6529)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block182 : PLift (RangeResult 47710208 47972352 2871770 2886618) :=
  ⟨oneBlock 47710208 262144 2871770 2886618 [
    (22597,6529),(29329,6530),(27164,6530),(25385,6530),(24088,6530),(22675,6530),(29569,6531),(28282,6531),
    (26187,6531),(24342,6531),(2526,6531)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block183 : PLift (RangeResult 47972352 48234496 2886618 2901307) :=
  ⟨oneBlock 47972352 262144 2886618 2901307 [
    (30770,6532),(28087,6532),(26874,6532),(24412,6532),(22466,6532),(29646,6533),(27992,6533),(25830,6533),
    (24217,6533),(21850,6533)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block184 : PLift (RangeResult 48234496 48496640 2901307 2916148) :=
  ⟨oneBlock 48234496 262144 2901307 2916148 [
    (28659,6534),(26948,6534),(25735,6534),(24387,6534),(22939,6534),(29543,6535),(27885,6535),(26204,6535),
    (23958,6535),(22677,6535),(3209,6536)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block185 : PLift (RangeResult 48496640 48758784 2916148 2930883) :=
  ⟨oneBlock 48496640 262144 2916148 2930883 [
    (29236,6536),(28372,6536),(25876,6536),(23979,6536),(22980,6536),(29524,6537),(26929,6537),(25796,6537),
    (24050,6537),(22285,6537),(3117,6538)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block186 : PLift (RangeResult 48758784 49020928 2930883 2945718) :=
  ⟨oneBlock 48758784 262144 2930883 2945718 [
    (28211,6538),(26317,6538),(25318,6538),(24353,6538),(22389,6538),(21539,6538),(27776,6539),(26221,6539),
    (24923,6539),(23325,6539),(11772,6539)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block187 : PLift (RangeResult 49020928 49283072 2945718 2960538) :=
  ⟨oneBlock 49020928 262144 2945718 2960538 [
    (29010,6540),(27125,6540),(25343,6540),(24261,6540),(22430,6540),(21030,6540),(27773,6541),(26529,6541),
    (25531,6541),(23898,6541),(9214,6541)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block188 : PLift (RangeResult 49283072 49545216 2960538 2975410) :=
  ⟨oneBlock 49283072 262144 2960538 2975410 [
    (21680,6541),(28079,6542),(26651,6542),(25335,6542),(23885,6542),(22587,6542),(29735,6543),(27704,6543),
    (26572,6543),(25422,6543),(4494,6543)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block189 : PLift (RangeResult 49545216 49807360 2975410 2990235) :=
  ⟨oneBlock 49545216 262144 2975410 2990235 [
    (23377,6543),(30343,6544),(29192,6544),(27509,6544),(25610,6544),(24027,6544),(30500,6545),(28597,6545),
    (27230,6545),(15759,6545)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block190 : PLift (RangeResult 49807360 50069504 2990235 3005005) :=
  ⟨oneBlock 49807360 262144 2990235 3005005 [
    (24454,6545),(31006,6546),(29402,6546),(27851,6546),(26519,6546),(24768,6546),(31448,6547),(29407,6547),
    (27689,6547),(9600,6547)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block191 : PLift (RangeResult 50069504 50331648 3005005 3019815) :=
  ⟨oneBlock 50069504 262144 3005005 3019815 [
    (24774,6547),(31438,6548),(30111,6548),(28311,6548),(26210,6548),(24693,6548),(31546,6549),(29149,6549),
    (27615,6549),(8297,6549)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block192 : PLift (RangeResult 50331648 50593792 3019815 3034622) :=
  ⟨oneBlock 50331648 262144 3019815 3034622 [
    (25922,6549),(24430,6549),(30989,6550),(28603,6550),(27069,6550),(25685,6550),(24251,6550),(30997,6551),
    (29275,6551),(14923,6551)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block193 : PLift (RangeResult 50593792 50855936 3034622 3049425) :=
  ⟨oneBlock 50593792 262144 3034622 3049425 [
    (27180,6551),(25589,6551),(32038,6552),(29981,6552),(28263,6552),(26460,6552),(25527,6552),(32297,6553),
    (30319,6553),(4490,6553)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block194 : PLift (RangeResult 50855936 51118080 3049425 3064128) :=
  ⟨oneBlock 50855936 262144 3049425 3064128 [
    (28533,6553),(26782,6553),(25047,6553),(31606,6554),(29390,6554),(27637,6554),(25368,6554),(23448,6554),
    (30446,6555),(13887,6555)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block195 : PLift (RangeResult 51118080 51380224 3064128 3078902) :=
  ⟨oneBlock 51118080 262144 3064128 3078902 [
    (28378,6555),(26189,6555),(24237,6555),(31336,6556),(29099,6556),(28131,6556),(26144,6556),(24341,6556),
    (31261,6557),(13028,6557)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block196 : PLift (RangeResult 51380224 51642368 3078902 3093673) :=
  ⟨oneBlock 51380224 262144 3078902 3093673 [
    (29567,6557),(28219,6557),(26148,6557),(23861,6557),(30753,6558),(29576,6558),(27756,6558),(26637,6558),
    (25301,6558),(14326,6559)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block197 : PLift (RangeResult 51642368 51904512 3093673 3108470) :=
  ⟨oneBlock 51642368 262144 3093673 3108470 [
    (30867,6559),(28412,6559),(26657,6559),(24888,6559),(32422,6560),(30437,6560),(29285,6560),(28283,6560),
    (26278,6560),(4615,6561)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block198 : PLift (RangeResult 51904512 52166656 3108470 3123186) :=
  ⟨oneBlock 51904512 262144 3108470 3123186 [
    (32762,6561),(30743,6561),(28972,6561),(27486,6561),(25363,6561),(32592,6562),(31082,6562),(28677,6562),
    (24467,6562)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block199 : PLift (RangeResult 52166656 52428800 3123186 3137912) :=
  ⟨oneBlock 52166656 262144 3123186 3137912 [
    (24981,6562),(32400,6563),(30386,6563),(28196,6563),(26324,6563),(24318,6563),(31490,6564),(30173,6564),
    (28469,6564),(5407,6564)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block200 : PLift (RangeResult 52428800 52690944 3137912 3152659) :=
  ⟨oneBlock 52428800 262144 3137912 3152659 [
    (25969,6564),(33285,6565),(30830,6565),(29041,6565),(27102,6565),(25647,6565),(32541,6566),(31237,6566),
    (26492,6566)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block201 : PLift (RangeResult 52690944 52953088 3152659 3167411) :=
  ⟨oneBlock 52690944 262144 3152659 3167411 [
    (27469,6566),(26220,6566),(32952,6567),(31024,6567),(29302,6567),(27679,6567),(25973,6567),(33096,6568),
    (28429,6568)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block202 : PLift (RangeResult 52953088 53215232 3167411 3182144) :=
  ⟨oneBlock 52953088 262144 3167411 3182144 [
    (29213,6568),(27399,6568),(25660,6568),(32787,6569),(30817,6569),(29444,6569),(27170,6569),(26233,6569),
    (33398,6570),(23,6570)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block203 : PLift (RangeResult 53215232 53477376 3182144 3196877) :=
  ⟨oneBlock 53215232 262144 3182144 3196877 [
    (30799,6570),(28948,6570),(27910,6570),(26672,6570),(33542,6571),(31881,6571),(29103,6571),(27380,6571),
    (25756,6571),(153,6572)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block204 : PLift (RangeResult 53477376 53739520 3196877 3211562) :=
  ⟨oneBlock 53477376 262144 3196877 3211562 [
    (32545,6572),(30413,6572),(28070,6572),(26397,6572),(24571,6572),(31368,6573),(29732,6573),(28677,6573),
    (26267,6573),(4104,6573)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block205 : PLift (RangeResult 53739520 54001664 3211562 3226289) :=
  ⟨oneBlock 53739520 262144 3211562 3226289 [
    (24925,6573),(32113,6574),(29921,6574),(28197,6574),(26086,6574),(24429,6574),(32457,6575),(30211,6575),
    (28870,6575),(4935,6575)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block206 : PLift (RangeResult 54001664 54263808 3226289 3240945) :=
  ⟨oneBlock 54001664 262144 3226289 3240945 [
    (26850,6575),(25052,6575),(32518,6576),(30450,6576),(28774,6576),(27184,6576),(25090,6576),(32342,6577),
    (29584,6577),(4300,6577)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block207 : PLift (RangeResult 54263808 54525952 3240945 3255602) :=
  ⟨oneBlock 54263808 262144 3240945 3255602 [
    (27746,6577),(26150,6577),(24457,6577),(32385,6578),(30057,6578),(27427,6578),(25819,6578),(23942,6578),
    (31572,6579),(12589,6579)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block208 : PLift (RangeResult 54525952 54788096 3255602 3270346) :=
  ⟨oneBlock 54525952 262144 3255602 3270346 [
    (28818,6579),(27515,6579),(25454,6579),(24516,6579),(32336,6580),(30587,6580),(28509,6580),(26463,6580),
    (24755,6580),(13191,6580)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block209 : PLift (RangeResult 54788096 55050240 3270346 3285031) :=
  ⟨oneBlock 54788096 262144 3270346 3285031 [
    (31508,6581),(29736,6581),(27324,6581),(25311,6581),(23317,6581),(30577,6582),(29524,6582),(27914,6582),
    (26138,6582),(10795,6582)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block210 : PLift (RangeResult 55050240 55312384 3285031 3299749) :=
  ⟨oneBlock 55050240 262144 3285031 3299749 [
    (24445,6582),(32700,6583),(30971,6583),(28941,6583),(26712,6583),(24984,6583),(23677,6583),(31522,6584),
    (29516,6584),(8676,6584)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block211 : PLift (RangeResult 55312384 55574528 3299749 3314407) :=
  ⟨oneBlock 55312384 262144 3299749 3314407 [
    (26979,6584),(25139,6584),(23613,6584),(31649,6585),(29638,6585),(28029,6585),(26083,6585),(24455,6585),
    (31271,6586),(15288,6586)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block212 : PLift (RangeResult 55574528 55836672 3314407 3329184) :=
  ⟨oneBlock 55574528 262144 3314407 3329184 [
    (28666,6586),(26707,6586),(25550,6586),(23990,6586),(31952,6587),(30303,6587),(29010,6587),(27820,6587),
    (25655,6587),(12491,6588)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block213 : PLift (RangeResult 55836672 56098816 3329184 3343885) :=
  ⟨oneBlock 55836672 262144 3329184 3343885 [
    (32509,6588),(30542,6588),(28630,6588),(26783,6588),(24535,6588),(32525,6589),(30883,6589),(28752,6589),
    (26985,6589)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block214 : PLift (RangeResult 56098816 56360960 3343885 3358629) :=
  ⟨oneBlock 56098816 262144 3343885 3358629 [
    (26154,6589),(25025,6589),(32706,6590),(31593,6590),(29663,6590),(27984,6590),(26054,6590),(33555,6591),
    (29410,6591)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block215 : PLift (RangeResult 56360960 56623104 3358629 3373243) :=
  ⟨oneBlock 56360960 262144 3358629 3373243 [
    (29723,6591),(27418,6591),(25369,6591),(32658,6592),(30293,6592),(28632,6592),(27069,6592),(25541,6592),
    (33170,6593),(2271,6593)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block216 : PLift (RangeResult 56623104 56885248 3373243 3387982) :=
  ⟨oneBlock 56623104 262144 3373243 3387982 [
    (31269,6593),(29627,6593),(28468,6593),(27544,6593),(35650,6594),(33344,6594),(31697,6594),(29867,6594),
    (14678,6594)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block217 : PLift (RangeResult 56885248 57147392 3387982 3402704) :=
  ⟨oneBlock 56885248 262144 3387982 3402704 [
    (25872,6594),(34269,6595),(32795,6595),(29838,6595),(28511,6595),(26511,6595),(33909,6596),(32246,6596),
    (18193,6596)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block218 : PLift (RangeResult 57147392 57409536 3402704 3417453) :=
  ⟨oneBlock 57147392 262144 3402704 3417453 [
    (29512,6596),(27826,6596),(35195,6597),(32957,6597),(31293,6597),(30469,6597),(28621,6597),(36417,6598),
    (9854,6598)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block219 : PLift (RangeResult 57409536 57671680 3417453 3432079) :=
  ⟨oneBlock 57409536 262144 3417453 3432079 [
    (33765,6598),(31567,6598),(28928,6598),(27264,6598),(35102,6599),(33320,6599),(31236,6599),(29101,6599),
    (11861,6599)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block220 : PLift (RangeResult 57671680 57933824 3432079 3446670) :=
  ⟨oneBlock 57671680 262144 3432079 3446670 [
    (36110,6600),(33410,6600),(31460,6600),(29088,6600),(27660,6600),(35189,6601),(32692,6601),(31044,6601),
    (5491,6601)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block221 : PLift (RangeResult 57933824 58195968 3446670 3461303) :=
  ⟨oneBlock 57933824 262144 3446670 3461303 [
    (28664,6601),(27328,6601),(34309,6602),(31873,6602),(30629,6602),(29098,6602),(27063,6602),(34976,6603),
    (18204,6603)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block222 : PLift (RangeResult 58195968 58458112 3461303 3475972) :=
  ⟨oneBlock 58195968 262144 3461303 3475972 [
    (31405,6603),(29607,6603),(28228,6603),(26697,6603),(33677,6604),(31884,6604),(30672,6604),(28703,6604),
    (21271,6604)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block223 : PLift (RangeResult 58458112 58720256 3475972 3490654) :=
  ⟨oneBlock 58458112 262144 3475972 3490654 [
    (34911,6605),(32494,6605),(31283,6605),(29499,6605),(27766,6605),(35750,6606),(34031,6606),(31608,6606),
    (4802,6606)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block224 : PLift (RangeResult 58720256 58982400 3490654 3505349) :=
  ⟨oneBlock 58720256 262144 3490654 3505349 [
    (29313,6606),(27939,6606),(35813,6607),(34491,6607),(32522,6607),(30687,6607),(28835,6607),(37037,6608),
    (5507,6608)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block225 : PLift (RangeResult 58982400 59244544 3505349 3519916) :=
  ⟨oneBlock 58982400 262144 3505349 3519916 [
    (33536,6608),(31264,6608),(30204,6608),(27611,6608),(35904,6609),(32819,6609),(31286,6609),(29097,6609),
    (10423,6609)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block226 : PLift (RangeResult 59244544 59506688 3519916 3534536) :=
  ⟨oneBlock 59244544 262144 3519916 3534536 [
    (26201,6609),(33863,6610),(32470,6610),(30702,6610),(28647,6610),(26222,6610),(34765,6611),(32543,6611),
    (16731,6611)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block227 : PLift (RangeResult 59506688 59768832 3534536 3549187) :=
  ⟨oneBlock 59506688 262144 3534536 3549187 [
    (29439,6611),(28349,6611),(26361,6611),(34188,6612),(32936,6612),(30509,6612),(28791,6612),(27006,6612),
    (24565,6613)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block228 : PLift (RangeResult 59768832 60030976 3549187 3563837) :=
  ⟨oneBlock 59768832 262144 3549187 3563837 [
    (33358,6613),(31795,6613),(29975,6613),(28594,6613),(26521,6613),(34583,6614),(32222,6614),(30013,6614),
    (15083,6614)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block229 : PLift (RangeResult 60030976 60293120 3563837 3578436) :=
  ⟨oneBlock 60030976 262144 3563837 3578436 [
    (27739,6614),(35485,6615),(33440,6615),(31266,6615),(29462,6615),(27390,6615),(26074,6615),(34994,6616),
    (16294,6616)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block230 : PLift (RangeResult 60293120 60555264 3578436 3593095) :=
  ⟨oneBlock 60293120 262144 3578436 3593095 [
    (31060,6616),(29888,6616),(27866,6616),(26467,6616),(35495,6617),(32895,6617),(30905,6617),(29118,6617),
    (18450,6617)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block231 : PLift (RangeResult 60555264 60817408 3593095 3607791) :=
  ⟨oneBlock 60555264 262144 3593095 3607791 [
    (35551,6618),(33675,6618),(32141,6618),(30472,6618),(28785,6618),(36596,6619),(34727,6619),(30197,6619)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block232 : PLift (RangeResult 60817408 61079552 3607791 3622464) :=
  ⟨oneBlock 60817408 262144 3607791 3622464 [
    (31026,6619),(30156,6619),(38109,6620),(35610,6620),(33298,6620),(31545,6620),(29924,6620),(32476,6621)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block233 : PLift (RangeResult 61079552 61341696 3622464 3636940) :=
  ⟨oneBlock 61079552 262144 3622464 3636940 [
    (36032,6621),(33574,6621),(31397,6621),(28648,6621),(36801,6622),(34710,6622),(32736,6622),(28246,6622)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block234 : PLift (RangeResult 61341696 61603840 3636940 3651509) :=
  ⟨oneBlock 61341696 262144 3636940 3651509 [
    (27995,6622),(26171,6622),(34657,6623),(32471,6623),(30817,6623),(29230,6623),(27189,6623),(35376,6624),
    (18238,6624)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block235 : PLift (RangeResult 61603840 61865984 3651509 3666133) :=
  ⟨oneBlock 61603840 262144 3651509 3666133 [
    (31523,6624),(29623,6624),(28071,6624),(26382,6624),(34394,6625),(32987,6625),(30591,6625),(28666,6625),
    (19907,6625)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block236 : PLift (RangeResult 61865984 62128128 3666133 3680788) :=
  ⟨oneBlock 61865984 262144 3666133 3680788 [
    (26181,6625),(34744,6626),(32284,6626),(30629,6626),(28687,6626),(27101,6626),(35379,6627),(33572,6627),
    (13567,6627)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block237 : PLift (RangeResult 62128128 62390272 3680788 3695396) :=
  ⟨oneBlock 62128128 262144 3680788 3695396 [
    (31439,6627),(29705,6627),(27628,6627),(35680,6628),(33510,6628),(31314,6628),(30167,6628),(29135,6628),
    (13566,6628)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block238 : PLift (RangeResult 62390272 62652416 3695396 3709902) :=
  ⟨oneBlock 62390272 262144 3695396 3709902 [
    (36062,6629),(33685,6629),(32046,6629),(29883,6629),(28279,6629),(36161,6630),(33183,6630),(31493,6630),
    (1352,6630)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block239 : PLift (RangeResult 62652416 62914560 3709902 3724578) :=
  ⟨oneBlock 62652416 262144 3709902 3724578 [
    (29044,6630),(27557,6630),(26070,6630),(34790,6631),(33087,6631),(31583,6631),(29370,6631),(27527,6631),
    (23116,6632)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block240 : PLift (RangeResult 62914560 63176704 3724578 3739129) :=
  ⟨oneBlock 62914560 262144 3724578 3739129 [
    (35093,6632),(32941,6632),(30996,6632),(29020,6632),(26822,6632),(35677,6633),(33503,6633),(31188,6633),
    (6904,6633)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block241 : PLift (RangeResult 63176704 63438848 3739129 3753756) :=
  ⟨oneBlock 63176704 262144 3739129 3753756 [
    (29034,6633),(27434,6633),(36298,6634),(34422,6634),(32156,6634),(29705,6634),(27896,6634),(26932,6634),
    (18267,6635)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block242 : PLift (RangeResult 63438848 63700992 3753756 3768344) :=
  ⟨oneBlock 63438848 262144 3753756 3768344 [
    (34533,6635),(32990,6635),(30792,6635),(29033,6635),(27342,6635),(35887,6636),(33587,6636),(31626,6636),
    (6354,6636)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block243 : PLift (RangeResult 63700992 63963136 3768344 3783040) :=
  ⟨oneBlock 63700992 262144 3768344 3783040 [
    (29296,6636),(27533,6636),(36373,6637),(34827,6637),(32815,6637),(31038,6637),(30041,6637),(38702,6638),
    (1519,6638)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block244 : PLift (RangeResult 63963136 64225280 3783040 3797618) :=
  ⟨oneBlock 63963136 262144 3783040 3797618 [
    (36241,6638),(33987,6638),(31652,6638),(29741,6638),(38598,6639),(36429,6639),(34128,6639),(21368,6639)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block245 : PLift (RangeResult 64225280 64487424 3797618 3812178) :=
  ⟨oneBlock 64225280 262144 3797618 3812178 [
    (31034,6639),(28561,6639),(37903,6640),(35656,6640),(33440,6640),(31612,6640),(30072,6640),(33866,6641)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block246 : PLift (RangeResult 64487424 64749568 3812178 3826648) :=
  ⟨oneBlock 64487424 262144 3812178 3826648 [
    (35955,6641),(34291,6641),(32091,6641),(29366,6641),(37370,6642),(35058,6642),(33315,6642),(24698,6642)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block247 : PLift (RangeResult 64749568 65011712 3826648 3841195) :=
  ⟨oneBlock 64749568 262144 3826648 3841195 [
    (29117,6642),(26967,6642),(35777,6643),(34116,6643),(31187,6643),(30036,6643),(28156,6643),(36567,6644),
    (10221,6644)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block248 : PLift (RangeResult 65011712 65273856 3841195 3855730) :=
  ⟨oneBlock 65011712 262144 3841195 3855730 [
    (34094,6644),(33326,6644),(30701,6644),(28838,6644),(26349,6644),(35416,6645),(32958,6645),(31045,6645),
    (9417,6645)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block249 : PLift (RangeResult 65273856 65536000 3855730 3870366) :=
  ⟨oneBlock 65273856 262144 3855730 3870366 [
    (28554,6645),(27167,6645),(35885,6646),(33980,6646),(30880,6646),(30355,6646),(28712,6646),(28017,6646),
    (18594,6647)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block250 : PLift (RangeResult 65536000 65798144 3870366 3884835) :=
  ⟨oneBlock 65536000 262144 3870366 3884835 [
    (35316,6647),(33071,6647),(30648,6647),(29004,6647),(26497,6647),(35660,6648),(33601,6648),(31212,6648),
    (7135,6648)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block251 : PLift (RangeResult 65798144 66060288 3884835 3899509) :=
  ⟨oneBlock 65798144 262144 3884835 3899509 [
    (28855,6648),(27552,6648),(36875,6649),(34471,6649),(32742,6649),(30641,6649),(29590,6649),(27692,6649),
    (13726,6650)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block252 : PLift (RangeResult 66060288 66322432 3899509 3914148) :=
  ⟨oneBlock 66060288 262144 3899509 3914148 [
    (36538,6650),(34528,6650),(32391,6650),(29917,6650),(29154,6650),(37956,6651),(36007,6651),(25653,6651)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block253 : PLift (RangeResult 66322432 66584576 3914148 3928698) :=
  ⟨oneBlock 66322432 262144 3914148 3928698 [
    (33157,6651),(31193,6651),(40646,6652),(37709,6652),(35370,6652),(33504,6652),(31961,6652),(18604,6653)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block254 : PLift (RangeResult 66584576 66846720 3928698 3943236) :=
  ⟨oneBlock 66584576 262144 3928698 3943236 [
    (39015,6653),(37444,6653),(35188,6653),(33713,6653),(31152,6653),(39865,6654),(37467,6654),(8300,6654)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block255 : PLift (RangeResult 66846720 67108864 3943236 3957809) :=
  ⟨oneBlock 66846720 262144 3943236 3957809 [
    (34119,6654),(32904,6654),(30479,6654),(39626,6655),(37048,6655),(34793,6655),(32841,6655),(20334,6655)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block256 : PLift (RangeResult 67108864 67371008 3957809 3972379) :=
  ⟨oneBlock 67108864 262144 3957809 3972379 [
    (40645,6656),(37156,6656),(35646,6656),(33645,6656),(32083,6656),(30573,6656),(39844,6657),(12552,6657)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block257 : PLift (RangeResult 67371008 67633152 3972379 3986942) :=
  ⟨oneBlock 67371008 262144 3972379 3986942 [
    (36489,6657),(34685,6657),(32750,6657),(41909,6658),(39493,6658),(37270,6658),(35709,6658),(3839,6658)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block258 : PLift (RangeResult 67633152 67895296 3986942 4001502) :=
  ⟨oneBlock 67633152 262144 3986942 4001502 [
    (32294,6658),(41653,6659),(39127,6659),(37751,6659),(34798,6659),(32591,6659),(41483,6660),(2447,6660)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block259 : PLift (RangeResult 67895296 68157440 4001502 4016043) :=
  ⟨oneBlock 67895296 262144 4001502 4016043 [
    (38994,6660),(37095,6660),(35483,6660),(32850,6660),(41704,6661),(39393,6661),(36625,6661)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block260 : PLift (RangeResult 68157440 68419584 4016043 4030567) :=
  ⟨oneBlock 68157440 262144 4016043 4030567 [
    (34623,6661),(32381,6661),(41752,6662),(39621,6662),(37260,6662),(34441,6662),(31995,6662),(10071,6663)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block261 : PLift (RangeResult 68419584 68681728 4030567 4045061) :=
  ⟨oneBlock 68419584 262144 4030567 4045061 [
    (40989,6663),(38166,6663),(36586,6663),(34022,6663),(31949,6663),(40936,6664),(38563,6664),(933,6664)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block262 : PLift (RangeResult 68681728 68943872 4045061 4059529) :=
  ⟨oneBlock 68681728 262144 4045061 4059529 [
    (36016,6664),(34197,6664),(31547,6664),(40849,6665),(37584,6665),(35749,6665),(34185,6665),(12017,6665)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block263 : PLift (RangeResult 68943872 69206016 4059529 4074043) :=
  ⟨oneBlock 68943872 262144 4059529 4074043 [
    (30681,6665),(40220,6666),(38524,6666),(35721,6666),(33630,6666),(31523,6666),(40472,6667),(11373,6667)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block264 : PLift (RangeResult 69206016 69468160 4074043 4088625) :=
  ⟨oneBlock 69206016 262144 4074043 4088625 [
    (37271,6667),(34570,6667),(31885,6667),(30355,6667),(40182,6668),(38044,6668),(36769,6668),(13068,6668)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block265 : PLift (RangeResult 69468160 69730304 4088625 4103202) :=
  ⟨oneBlock 69468160 262144 4088625 4103202 [
    (34070,6668),(32111,6668),(41406,6669),(39750,6669),(36655,6669),(34837,6669),(33272,6669),(10043,6670)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block266 : PLift (RangeResult 69730304 69992448 4103202 4117621) :=
  ⟨oneBlock 69730304 262144 4103202 4117621 [
    (42007,6670),(39773,6670),(37052,6670),(35472,6670),(32699,6670),(41661,6671),(33480,6671)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block267 : PLift (RangeResult 69992448 70254592 4117621 4132158) :=
  ⟨oneBlock 69992448 262144 4117621 4132158 [
    (36232,6671),(34439,6671),(32211,6671),(41506,6672),(38833,6672),(37098,6672),(34309,6672),(7516,6672)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block268 : PLift (RangeResult 70254592 70516736 4132158 4146727) :=
  ⟨oneBlock 70254592 262144 4132158 4146727 [
    (32542,6672),(41777,6673),(39724,6673),(37530,6673),(35318,6673),(33736,6673),(41517,6674)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block269 : PLift (RangeResult 70516736 70778880 4146727 4161148) :=
  ⟨oneBlock 70516736 262144 4146727 4161148 [
    (40738,6674),(38829,6674),(36191,6674),(33911,6674),(42474,6675),(39822,6675),(30179,6675)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block270 : PLift (RangeResult 70778880 71041024 4161148 4175642) :=
  ⟨oneBlock 70778880 262144 4161148 4175642 [
    (35272,6675),(33287,6675),(42079,6676),(39982,6676),(37462,6676),(35625,6676),(33241,6676),(5196,6677)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block271 : PLift (RangeResult 71041024 71303168 4175642 4190151) :=
  ⟨oneBlock 71041024 262144 4175642 4190151 [
    (42467,6677),(40039,6677),(37485,6677),(35698,6677),(33042,6677),(43033,6678),(30380,6678)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block272 : PLift (RangeResult 71303168 71565312 4190151 4204720) :=
  ⟨oneBlock 71303168 262144 4190151 4204720 [
    (38695,6678),(35925,6678),(34052,6678),(32230,6678),(42678,6679),(40819,6679),(37745,6679)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block273 : PLift (RangeResult 71565312 71827456 4204720 4219149) :=
  ⟨oneBlock 71565312 262144 4204720 4219149 [
    (36023,6679),(34177,6679),(43478,6680),(40927,6680),(37912,6680),(35766,6680),(32411,6680),(1450,6681)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block274 : PLift (RangeResult 71827456 72089600 4219149 4233650) :=
  ⟨oneBlock 71827456 262144 4219149 4233650 [
    (42505,6681),(39928,6681),(37816,6681),(35568,6681),(33200,6681),(42625,6682),(30502,6682)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block275 : PLift (RangeResult 72089600 72351744 4233650 4248269) :=
  ⟨oneBlock 72089600 262144 4233650 4248269 [
    (38873,6682),(37157,6682),(34739,6682),(45043,6683),(42872,6683),(40759,6683),(22701,6683)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block276 : PLift (RangeResult 72351744 72613888 4248269 4262696) :=
  ⟨oneBlock 72351744 262144 4248269 4262696 [
    (37330,6683),(34999,6683),(44435,6684),(41498,6684),(38635,6684),(37068,6684),(28179,6684)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block277 : PLift (RangeResult 72613888 72876032 4262696 4277186) :=
  ⟨oneBlock 72613888 262144 4262696 4277186 [
    (44171,6685),(41351,6685),(39170,6685),(36885,6685),(34295,6685),(44248,6686),(22024,6686)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block278 : PLift (RangeResult 72876032 73138176 4277186 4291691) :=
  ⟨oneBlock 72876032 262144 4277186 4291691 [
    (40626,6686),(38784,6686),(36295,6686),(46121,6687),(43633,6687),(41160,6687),(15525,6687)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block279 : PLift (RangeResult 73138176 73400320 4291691 4306139) :=
  ⟨oneBlock 73138176 262144 4291691 4306139 [
    (37417,6687),(34459,6687),(43891,6688),(41457,6688),(38864,6688),(37091,6688),(28965,6688)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block280 : PLift (RangeResult 73400320 73662464 4306139 4320618) :=
  ⟨oneBlock 73400320 262144 4306139 4320618 [
    (45008,6689),(41668,6689),(38819,6689),(36790,6689),(35272,6689),(45495,6690),(19092,6690)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block281 : PLift (RangeResult 73662464 73924608 4320618 4335111) :=
  ⟨oneBlock 73662464 262144 4320618 4335111 [
    (41552,6690),(39525,6690),(36932,6690),(46415,6691),(43813,6691),(41221,6691),(12686,6691)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block282 : PLift (RangeResult 73924608 74186752 4335111 4349470) :=
  ⟨oneBlock 73924608 262144 4335111 4349470 [
    (38413,6691),(36340,6691),(45396,6692),(42763,6692),(38667,6692),(36551,6692),(24014,6692)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block283 : PLift (RangeResult 74186752 74448896 4349470 4363944) :=
  ⟨oneBlock 74186752 262144 4349470 4363944 [
    (44878,6693),(42360,6693),(39544,6693),(36711,6693),(34901,6693),(45055,6694),(18695,6694)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block284 : PLift (RangeResult 74448896 74711040 4363944 4378336) :=
  ⟨oneBlock 74448896 262144 4363944 4378336 [
    (41611,6694),(38253,6694),(35966,6694),(33285,6694),(43914,6695),(41297,6695),(27818,6695)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block285 : PLift (RangeResult 74711040 74973184 4378336 4392840) :=
  ⟨oneBlock 74711040 262144 4378336 4392840 [
    (37023,6695),(34776,6695),(33308,6695),(43525,6696),(40536,6696),(38913,6696),(34063,6696)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block286 : PLift (RangeResult 74973184 75235328 4392840 4407319) :=
  ⟨oneBlock 74973184 262144 4392840 4407319 [
    (34425,6696),(44361,6697),(40662,6697),(38954,6697),(36666,6697),(34770,6697),(32306,6698)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block287 : PLift (RangeResult 75235328 75497472 4407319 4421818) :=
  ⟨oneBlock 75235328 262144 4407319 4421818 [
    (43449,6698),(41232,6698),(38755,6698),(36552,6698),(46718,6699),(44707,6699),(10731,6699)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block288 : PLift (RangeResult 75497472 75759616 4421818 4436262) :=
  ⟨oneBlock 75497472 262144 4421818 4436262 [
    (40962,6699),(38489,6699),(36216,6699),(45509,6700),(43483,6700),(41041,6700),(16444,6700)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block289 : PLift (RangeResult 75759616 76021760 4436262 4450822) :=
  ⟨oneBlock 75759616 262144 4436262 4450822 [
    (37615,6700),(35778,6700),(45906,6701),(43747,6701),(41422,6701),(38860,6701),(18816,6701)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block290 : PLift (RangeResult 76021760 76283904 4450822 4465181) :=
  ⟨oneBlock 76021760 262144 4450822 4465181 [
    (48416,6702),(45001,6702),(42353,6702),(39959,6702),(37686,6702),(46798,6703),(1931,6703)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block291 : PLift (RangeResult 76283904 76546048 4465181 4479580) :=
  ⟨oneBlock 76283904 262144 4465181 4479580 [
    (43812,6703),(40769,6703),(38582,6703),(36256,6703),(46749,6704),(43288,6704),(12688,6704)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block292 : PLift (RangeResult 76546048 76808192 4479580 4493914) :=
  ⟨oneBlock 76546048 262144 4479580 4493914 [
    (39970,6704),(37151,6704),(34878,6704),(45025,6705),(41893,6705),(39090,6705),(24137,6705)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block293 : PLift (RangeResult 76808192 77070336 4493914 4508405) :=
  ⟨oneBlock 76808192 262144 4493914 4508405 [
    (35095,6705),(45588,6706),(43114,6706),(40344,6706),(38497,6706),(37146,6706),(22360,6707)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block294 : PLift (RangeResult 77070336 77332480 4508405 4522828) :=
  ⟨oneBlock 77070336 262144 4508405 4522828 [
    (45227,6707),(42591,6707),(40264,6707),(38315,6707),(36314,6707),(45851,6708),(13582,6708)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block295 : PLift (RangeResult 77332480 77594624 4522828 4537276) :=
  ⟨oneBlock 77332480 262144 4522828 4537276 [
    (42069,6708),(39929,6708),(37483,6708),(35361,6708),(45084,6709),(42690,6709),(19528,6709)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block296 : PLift (RangeResult 77594624 77856768 4537276 4551635) :=
  ⟨oneBlock 77594624 262144 4537276 4551635 [
    (39417,6709),(36582,6709),(33896,6709),(44009,6710),(42269,6710),(39446,6710),(26525,6710)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block297 : PLift (RangeResult 77856768 78118912 4551635 4566107) :=
  ⟨oneBlock 77856768 262144 4551635 4566107 [
    (35321,6710),(45891,6711),(43833,6711),(41215,6711),(38408,6711),(36850,6711),(20626,6712)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block298 : PLift (RangeResult 78118912 78381056 4566107 4580465) :=
  ⟨oneBlock 78118912 262144 4566107 4580465 [
    (45638,6712),(42898,6712),(40417,6712),(37883,6712),(34939,6712),(45366,6713),(15003,6713)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block299 : PLift (RangeResult 78381056 78643200 4580465 4594833) :=
  ⟨oneBlock 78381056 262144 4580465 4594833 [
    (41720,6713),(38574,6713),(36125,6713),(33609,6713),(44564,6714),(42655,6714),(24897,6714)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block300 : PLift (RangeResult 78643200 78905344 4594833 4609257) :=
  ⟨oneBlock 78643200 262144 4594833 4609257 [
    (38051,6714),(35960,6714),(33905,6714),(45476,6715),(42610,6715),(39837,6715),(26305,6715)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block301 : PLift (RangeResult 78905344 79167488 4609257 4623685) :=
  ⟨oneBlock 78905344 262144 4609257 4623685 [
    (35419,6715),(33106,6715),(44006,6716),(40991,6716),(39020,6716),(37068,6716),(32534,6716)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block302 : PLift (RangeResult 79167488 79429632 4623685 4638111) :=
  ⟨oneBlock 79167488 262144 4623685 4638111 [
    (45491,6717),(43036,6717),(40260,6717),(37433,6717),(34881,6717),(32739,6717),(28304,6718)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block303 : PLift (RangeResult 79429632 79691776 4638111 4652488) :=
  ⟨oneBlock 79429632 262144 4638111 4652488 [
    (43090,6718),(40420,6718),(38142,6718),(35555,6718),(33395,6718),(43861,6719),(27681,6719)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block304 : PLift (RangeResult 79691776 79953920 4652488 4666902) :=
  ⟨oneBlock 79691776 262144 4652488 4666902 [
    (39927,6719),(38353,6719),(35200,6719),(33076,6719),(43950,6720),(41479,6720),(30159,6720)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block305 : PLift (RangeResult 79953920 80216064 4666902 4681194) :=
  ⟨oneBlock 79953920 262144 4666902 4681194 [
    (37476,6720),(34520,6720),(44377,6721),(41589,6721),(40011,6721),(37457,6721),(26714,6721)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block306 : PLift (RangeResult 80216064 80478208 4681194 4695703) :=
  ⟨oneBlock 80216064 262144 4681194 4695703 [
    (33012,6721),(44518,6722),(42504,6722),(40121,6722),(37120,6722),(36057,6722),(28812,6722)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block307 : PLift (RangeResult 80478208 80740352 4695703 4710061) :=
  ⟨oneBlock 80478208 262144 4695703 4710061 [
    (45099,6723),(42990,6723),(39424,6723),(37212,6723),(35000,6723),(45364,6724),(17055,6724)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block308 : PLift (RangeResult 80740352 81002496 4710061 4724549) :=
  ⟨oneBlock 80740352 262144 4710061 4724549 [
    (41961,6724),(40202,6724),(37853,6724),(36154,6724),(47117,6725),(44051,6725),(14806,6725)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block309 : PLift (RangeResult 81002496 81264640 4724549 4739078) :=
  ⟨oneBlock 81002496 262144 4724549 4739078 [
    (41132,6725),(39660,6725),(38098,6725),(49180,6726),(46683,6726),(43509,6726),(3882,6726)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block310 : PLift (RangeResult 81264640 81526784 4739078 4753449) :=
  ⟨oneBlock 81264640 262144 4739078 4753449 [
    (41085,6726),(37898,6726),(48808,6727),(45952,6727),(43790,6727),(41834,6727),(2777,6727)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block311 : PLift (RangeResult 81526784 81788928 4753449 4767804) :=
  ⟨oneBlock 81526784 262144 4753449 4767804 [
    (38405,6727),(48658,6728),(46131,6728),(43368,6728),(40931,6728),(38649,6728),(6002,6729)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block312 : PLift (RangeResult 81788928 82051072 4767804 4782250) :=
  ⟨oneBlock 81788928 262144 4767804 4782250 [
    (48478,6729),(45486,6729),(42825,6729),(40680,6729),(38501,6729),(46174,6730)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block313 : PLift (RangeResult 82051072 82313216 4782250 4796525) :=
  ⟨oneBlock 82051072 262144 4782250 4796525 [
    (47281,6730),(44755,6730),(42643,6730),(39417,6730),(48995,6731),(39053,6731)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block314 : PLift (RangeResult 82313216 82575360 4796525 4810934) :=
  ⟨oneBlock 82313216 262144 4796525 4810934 [
    (43226,6731),(41363,6731),(38564,6731),(36434,6731),(47476,6732),(44546,6732),(10535,6732)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block315 : PLift (RangeResult 82575360 82837504 4810934 4825378) :=
  ⟨oneBlock 82575360 262144 4810934 4825378 [
    (41550,6732),(38759,6732),(36801,6732),(48167,6733),(45429,6733),(42578,6733),(8860,6733)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block316 : PLift (RangeResult 82837504 83099648 4825378 4839736) :=
  ⟨oneBlock 82837504 262144 4825378 4839736 [
    (40554,6733),(39040,6733),(49253,6734),(46862,6734),(43873,6734),(41194,6734),(1368,6734)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block317 : PLift (RangeResult 83099648 83361792 4839736 4854030) :=
  ⟨oneBlock 83099648 262144 4839736 4854030 [
    (38159,6734),(48879,6735),(45633,6735),(42316,6735),(40152,6735),(37506,6735),(9499,6736)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block318 : PLift (RangeResult 83361792 83623936 4854030 4868420) :=
  ⟨oneBlock 83361792 262144 4854030 4868420 [
    (47924,6736),(45107,6736),(42684,6736),(40227,6736),(37443,6736),(48759,6737)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block319 : PLift (RangeResult 83623936 83886080 4868420 4882806) :=
  ⟨oneBlock 83623936 262144 4868420 4882806 [
    (46273,6737),(42605,6737),(39718,6737),(38514,6737),(36195,6737),(47435,6738),(11404,6738)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block320 : PLift (RangeResult 83886080 84148224 4882806 4897170) :=
  ⟨oneBlock 83886080 262144 4882806 4897170 [
    (44632,6738),(42492,6738),(41098,6738),(38607,6738),(49417,6739),(44922,6739),(976,6739)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block321 : PLift (RangeResult 84148224 84410368 4897170 4911469) :=
  ⟨oneBlock 84148224 262144 4897170 4911469 [
    (42691,6739),(39799,6739),(36962,6739),(48216,6740),(45600,6740),(43038,6740),(5838,6740)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block322 : PLift (RangeResult 84410368 84672512 4911469 4925819) :=
  ⟨oneBlock 84410368 262144 4911469 4925819 [
    (39710,6740),(37776,6740),(49768,6741),(46587,6741),(43492,6741),(40379,6741),(4432,6741)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block323 : PLift (RangeResult 84672512 84934656 4925819 4940115) :=
  ⟨oneBlock 84672512 262144 4925819 4940115 [
    (37684,6741),(49032,6742),(46406,6742),(43584,6742),(40919,6742),(38149,6742),(6370,6742)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block324 : PLift (RangeResult 84934656 85196800 4940115 4954440) :=
  ⟨oneBlock 84934656 262144 4940115 4954440 [
    (48223,6743),(45776,6743),(42611,6743),(40116,6743),(37846,6743),(35730,6743),(11842,6744)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block325 : PLift (RangeResult 85196800 85458944 4954440 4968863) :=
  ⟨oneBlock 85196800 262144 4954440 4968863 [
    (45961,6744),(42996,6744),(40553,6744),(38815,6744),(36510,6744),(48103,6745),(9206,6745)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block326 : PLift (RangeResult 85458944 85721088 4968863 4983175) :=
  ⟨oneBlock 85458944 262144 4968863 4983175 [
    (45464,6745),(42882,6745),(41007,6745),(37926,6745),(35621,6745),(47562,6746),(11682,6746)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block327 : PLift (RangeResult 85721088 85983232 4983175 4997564) :=
  ⟨oneBlock 85721088 262144 4983175 4997564 [
    (43134,6746),(41116,6746),(38966,6746),(36659,6746),(48339,6747),(45495,6747),(8435,6747)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block328 : PLift (RangeResult 85983232 86245376 4997564 5011869) :=
  ⟨oneBlock 85983232 262144 4997564 5011869 [
    (42208,6747),(39487,6747),(37285,6747),(49118,6748),(45915,6748),(42989,6748),(5142,6748)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block329 : PLift (RangeResult 86245376 86507520 5011869 5026243) :=
  ⟨oneBlock 86245376 262144 5011869 5026243 [
    (39913,6748),(37807,6748),(35723,6748),(46924,6749),(44425,6749),(42135,6749),(15217,6749)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block330 : PLift (RangeResult 86507520 86769664 5026243 5040596) :=
  ⟨oneBlock 86507520 262144 5026243 5040596 [
    (38884,6749),(37348,6749),(48547,6750),(45999,6750),(43175,6750),(40264,6750),(7927,6750)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block331 : PLift (RangeResult 86769664 87031808 5040596 5054960) :=
  ⟨oneBlock 86769664 262144 5040596 5054960 [
    (37572,6750),(49361,6751),(46006,6751),(44180,6751),(41029,6751),(38582,6751),(5414,6751)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block332 : PLift (RangeResult 87031808 87293952 5054960 5069299) :=
  ⟨oneBlock 87031808 262144 5054960 5069299 [
    (50255,6752),(47547,6752),(43722,6752),(41569,6752),(39329,6752),(36987,6752),(2735,6753)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block333 : PLift (RangeResult 87293952 87556096 5069299 5083569) :=
  ⟨oneBlock 87293952 262144 5069299 5083569 [
    (48897,6753),(45641,6753),(42627,6753),(38991,6753),(36906,6753),(48585,6754),(497,6754)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block334 : PLift (RangeResult 87556096 87818240 5083569 5097854) :=
  ⟨oneBlock 87556096 262144 5083569 5097854 [
    (46427,6754),(43391,6754),(41065,6754),(38446,6754),(35792,6754),(47473,6755),(9550,6755)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block335 : PLift (RangeResult 87818240 88080384 5097854 5112278) :=
  ⟨oneBlock 87818240 262144 5097854 5112278 [
    (44293,6755),(41589,6755),(39606,6755),(37435,6755),(49115,6756),(46800,6756),(3306,6756)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block336 : PLift (RangeResult 88080384 88342528 5112278 5126667) :=
  ⟨oneBlock 88080384 262144 5112278 5126667 [
    (44633,6756),(41940,6756),(39337,6756),(36958,6756),(49831,6757),(47602,6757),(1843,6757)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block337 : PLift (RangeResult 88342528 88604672 5126667 5140858) :=
  ⟨oneBlock 88342528 262144 5126667 5140858 [
    (44448,6757),(41377,6757),(39809,6757),(51043,6758),(47023,6758),(38444,6758)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block338 : PLift (RangeResult 88604672 88866816 5140858 5155239) :=
  ⟨oneBlock 88604672 262144 5140858 5155239 [
    (40927,6758),(39349,6758),(37056,6758),(48689,6759),(45582,6759),(43236,6759),(7305,6759)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block339 : PLift (RangeResult 88866816 89128960 5155239 5169585) :=
  ⟨oneBlock 88866816 262144 5155239 5169585 [
    (40759,6759),(38700,6759),(51333,6760),(48055,6760),(44968,6760),(38329,6760)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block340 : PLift (RangeResult 89128960 89391104 5169585 5183901) :=
  ⟨oneBlock 89128960 262144 5169585 5183901 [
    (40066,6760),(38189,6760),(49997,6761),(47666,6761),(45078,6761),(41148,6761)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block341 : PLift (RangeResult 89391104 89653248 5183901 5198132) :=
  ⟨oneBlock 89391104 262144 5183901 5198132 [
    (38934,6761),(50915,6762),(47553,6762),(44826,6762),(41635,6762),(38281,6762)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block342 : PLift (RangeResult 89653248 89915392 5198132 5212358) :=
  ⟨oneBlock 89653248 262144 5198132 5212358 [
    (36412,6762),(48078,6763),(44575,6763),(41348,6763),(38241,6763),(37240,6763),(16250,6763)] (by decide) (by decide) (by decide +kernel)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private def block343 : PLift (RangeResult 89915392 90000000 5212358 5216954) :=
  ⟨oneBlock 89915392 84608 5212358 5216954 [
    (48037,6764),(36571,6764)] (by decide) (by decide) (by decide +kernel)⟩

private theorem complete : RangeResult 0 90000000 0 5216954 :=
  (join_result (join_result (join_result (join_result (join_result (join_result (join_result (join_result block0.down block1.down) (join_result block2.down (join_result block3.down block4.down))) (join_result (join_result block5.down block6.down) (join_result block7.down (join_result block8.down block9.down)))) (join_result (join_result (join_result block10.down block11.down) (join_result block12.down (join_result block13.down block14.down))) (join_result (join_result block15.down (join_result block16.down block17.down)) (join_result block18.down (join_result block19.down block20.down))))) (join_result (join_result (join_result (join_result block21.down block22.down) (join_result block23.down (join_result block24.down block25.down))) (join_result (join_result block26.down (join_result block27.down block28.down)) (join_result block29.down (join_result block30.down block31.down)))) (join_result (join_result (join_result block32.down block33.down) (join_result block34.down (join_result block35.down block36.down))) (join_result (join_result block37.down (join_result block38.down block39.down)) (join_result block40.down (join_result block41.down block42.down)))))) (join_result (join_result (join_result (join_result (join_result block43.down block44.down) (join_result block45.down (join_result block46.down block47.down))) (join_result (join_result block48.down block49.down) (join_result block50.down (join_result block51.down block52.down)))) (join_result (join_result (join_result block53.down block54.down) (join_result block55.down (join_result block56.down block57.down))) (join_result (join_result block58.down (join_result block59.down block60.down)) (join_result block61.down (join_result block62.down block63.down))))) (join_result (join_result (join_result (join_result block64.down block65.down) (join_result block66.down (join_result block67.down block68.down))) (join_result (join_result block69.down (join_result block70.down block71.down)) (join_result block72.down (join_result block73.down block74.down)))) (join_result (join_result (join_result block75.down block76.down) (join_result block77.down (join_result block78.down block79.down))) (join_result (join_result block80.down (join_result block81.down block82.down)) (join_result block83.down (join_result block84.down block85.down))))))) (join_result (join_result (join_result (join_result (join_result (join_result block86.down block87.down) (join_result block88.down (join_result block89.down block90.down))) (join_result (join_result block91.down block92.down) (join_result block93.down (join_result block94.down block95.down)))) (join_result (join_result (join_result block96.down block97.down) (join_result block98.down (join_result block99.down block100.down))) (join_result (join_result block101.down (join_result block102.down block103.down)) (join_result block104.down (join_result block105.down block106.down))))) (join_result (join_result (join_result (join_result block107.down block108.down) (join_result block109.down (join_result block110.down block111.down))) (join_result (join_result block112.down (join_result block113.down block114.down)) (join_result block115.down (join_result block116.down block117.down)))) (join_result (join_result (join_result block118.down block119.down) (join_result block120.down (join_result block121.down block122.down))) (join_result (join_result block123.down (join_result block124.down block125.down)) (join_result block126.down (join_result block127.down block128.down)))))) (join_result (join_result (join_result (join_result (join_result block129.down block130.down) (join_result block131.down (join_result block132.down block133.down))) (join_result (join_result block134.down block135.down) (join_result block136.down (join_result block137.down block138.down)))) (join_result (join_result (join_result block139.down block140.down) (join_result block141.down (join_result block142.down block143.down))) (join_result (join_result block144.down (join_result block145.down block146.down)) (join_result block147.down (join_result block148.down block149.down))))) (join_result (join_result (join_result (join_result block150.down block151.down) (join_result block152.down (join_result block153.down block154.down))) (join_result (join_result block155.down (join_result block156.down block157.down)) (join_result block158.down (join_result block159.down block160.down)))) (join_result (join_result (join_result block161.down block162.down) (join_result block163.down (join_result block164.down block165.down))) (join_result (join_result block166.down (join_result block167.down block168.down)) (join_result block169.down (join_result block170.down block171.down)))))))) (join_result (join_result (join_result (join_result (join_result (join_result (join_result block172.down block173.down) (join_result block174.down (join_result block175.down block176.down))) (join_result (join_result block177.down block178.down) (join_result block179.down (join_result block180.down block181.down)))) (join_result (join_result (join_result block182.down block183.down) (join_result block184.down (join_result block185.down block186.down))) (join_result (join_result block187.down (join_result block188.down block189.down)) (join_result block190.down (join_result block191.down block192.down))))) (join_result (join_result (join_result (join_result block193.down block194.down) (join_result block195.down (join_result block196.down block197.down))) (join_result (join_result block198.down (join_result block199.down block200.down)) (join_result block201.down (join_result block202.down block203.down)))) (join_result (join_result (join_result block204.down block205.down) (join_result block206.down (join_result block207.down block208.down))) (join_result (join_result block209.down (join_result block210.down block211.down)) (join_result block212.down (join_result block213.down block214.down)))))) (join_result (join_result (join_result (join_result (join_result block215.down block216.down) (join_result block217.down (join_result block218.down block219.down))) (join_result (join_result block220.down block221.down) (join_result block222.down (join_result block223.down block224.down)))) (join_result (join_result (join_result block225.down block226.down) (join_result block227.down (join_result block228.down block229.down))) (join_result (join_result block230.down (join_result block231.down block232.down)) (join_result block233.down (join_result block234.down block235.down))))) (join_result (join_result (join_result (join_result block236.down block237.down) (join_result block238.down (join_result block239.down block240.down))) (join_result (join_result block241.down (join_result block242.down block243.down)) (join_result block244.down (join_result block245.down block246.down)))) (join_result (join_result (join_result block247.down block248.down) (join_result block249.down (join_result block250.down block251.down))) (join_result (join_result block252.down (join_result block253.down block254.down)) (join_result block255.down (join_result block256.down block257.down))))))) (join_result (join_result (join_result (join_result (join_result (join_result block258.down block259.down) (join_result block260.down (join_result block261.down block262.down))) (join_result (join_result block263.down block264.down) (join_result block265.down (join_result block266.down block267.down)))) (join_result (join_result (join_result block268.down block269.down) (join_result block270.down (join_result block271.down block272.down))) (join_result (join_result block273.down (join_result block274.down block275.down)) (join_result block276.down (join_result block277.down block278.down))))) (join_result (join_result (join_result (join_result block279.down block280.down) (join_result block281.down (join_result block282.down block283.down))) (join_result (join_result block284.down (join_result block285.down block286.down)) (join_result block287.down (join_result block288.down block289.down)))) (join_result (join_result (join_result block290.down block291.down) (join_result block292.down (join_result block293.down block294.down))) (join_result (join_result block295.down (join_result block296.down block297.down)) (join_result block298.down (join_result block299.down block300.down)))))) (join_result (join_result (join_result (join_result (join_result block301.down block302.down) (join_result block303.down (join_result block304.down block305.down))) (join_result (join_result block306.down block307.down) (join_result block308.down (join_result block309.down block310.down)))) (join_result (join_result (join_result block311.down block312.down) (join_result block313.down (join_result block314.down block315.down))) (join_result (join_result block316.down (join_result block317.down block318.down)) (join_result block319.down (join_result block320.down block321.down))))) (join_result (join_result (join_result (join_result block322.down block323.down) (join_result block324.down (join_result block325.down block326.down))) (join_result (join_result block327.down (join_result block328.down block329.down)) (join_result block330.down (join_result block331.down block332.down)))) (join_result (join_result (join_result block333.down block334.down) (join_result block335.down (join_result block336.down block337.down))) (join_result (join_result block338.down (join_result block339.down block340.down)) (join_result block341.down (join_result block342.down block343.down)))))))))

end FinitePrimeEstimate

theorem OMA.solution : OMA.R_Firoozbakht_firoozbakht_conjecture_consequence_R1_H1_R1.H2 := by
  intro p lower upper _
  exact (FinitePrimeEstimate.complete (by rfl)).2 p lower (Nat.zero_le _) upper
