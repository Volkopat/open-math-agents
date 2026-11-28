import OMAStatements.S_oeis_a262999
import Mathlib

/-!
# A disproof of Sun's conjecture on OEIS A262999

The conjecture says that `a(n) = 1` only for `n` in an explicit finite list. We show
`a(7872413) = 1`: the only pair is `(15015, 4749)`, with
`π(112732620) + π(22553001) = 6450605 + 1421808 = 7872413`.

Method. The values `π(k(k+1)/2)` for `k ≤ 16689` and `π(m^2)` for `m ≤ 11801` are certified
by a windowed bitmask sieve of Eratosthenes evaluated by the kernel (`decide +kernel`). Since
`π(T_16689) > 7872413` and `π(11801^2) > 7872413`, every pair has `k ≤ 16688` and `m ≤ 11800`.
A merge of the two sorted value lists `π(T_k)` and `7872413 - π(m^2)` finds the single common
value `6450605`, and monotonicity of `π` pins down `k = 15015` and `m = 4749`.

Attribution. The sieve (`multMask`, `stepW`, `sieveW`, ...), the SWAR population count
(`dsum`, `swar`, `pc`, ...) and the certified-table checker (`Good`, `chk`, ...) are adapted
from Neal Patel's refutation of A262995,
https://github.com/thatnealpatel/proofs, file
Proofs/Sorry/NumberComplexity/A262995Refutation.lean at commit
e0c9810910fd2faa896326257d0a7b95216756cc, used under the MIT License:

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

(Double quotes in the notice are written as single quotes, since this repository forbids the
double-quote character.) Changes: larger windows and sieving primes, a 32768-bit population
count with a closed-form mask, a two-sequence chunk checker, and a merge-based pair check.
-/

namespace OMA.A262999Disproof

open OMA.S_oeis_a262999

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

/-- Population count of the low `32768` bits, by fifteen SWAR steps. -/
def pc (x : ℕ) : ℕ :=
  swar 16384 1 (swar 8192 2 (swar 4096 4 (swar 2048 8 (swar 1024 16 (swar 512 32
    (swar 256 64 (swar 128 128 (swar 64 256 (swar 32 512 (swar 16 1024 (swar 8 2048
      (swar 4 4096 (swar 2 8192 (swar 1 16384 x)))))))))))))) % 2 ^ 32768

theorem pc_eq_dsum (x : ℕ) : pc x = dsum 1 32768 x := by
  have h : pc x = dsum 32768 1 (swar 16384 1 (swar 8192 2 (swar 4096 4 (swar 2048 8
      (swar 1024 16 (swar 512 32 (swar 256 64 (swar 128 128 (swar 64 256 (swar 32 512
        (swar 16 1024 (swar 8 2048 (swar 4 4096 (swar 2 8192 (swar 1 16384 x))))))))))))))) := by
    rw [pc, dsum, dsum, add_zero]
  rw [h, dsum_swar' (w := 16384) (w2 := 32768) (L := 1) (L2 := 2) (by norm_num) rfl rfl,
    dsum_swar' (w := 8192) (w2 := 16384) (L := 2) (L2 := 4) (by norm_num) rfl rfl,
    dsum_swar' (w := 4096) (w2 := 8192) (L := 4) (L2 := 8) (by norm_num) rfl rfl,
    dsum_swar' (w := 2048) (w2 := 4096) (L := 8) (L2 := 16) (by norm_num) rfl rfl,
    dsum_swar' (w := 1024) (w2 := 2048) (L := 16) (L2 := 32) (by norm_num) rfl rfl,
    dsum_swar' (w := 512) (w2 := 1024) (L := 32) (L2 := 64) (by norm_num) rfl rfl,
    dsum_swar' (w := 256) (w2 := 512) (L := 64) (L2 := 128) (by norm_num) rfl rfl,
    dsum_swar' (w := 128) (w2 := 256) (L := 128) (L2 := 256) (by norm_num) rfl rfl,
    dsum_swar' (w := 64) (w2 := 128) (L := 256) (L2 := 512) (by norm_num) rfl rfl,
    dsum_swar' (w := 32) (w2 := 64) (L := 512) (L2 := 1024) (by norm_num) rfl rfl,
    dsum_swar' (w := 16) (w2 := 32) (L := 1024) (L2 := 2048) (by norm_num) rfl rfl,
    dsum_swar' (w := 8) (w2 := 16) (L := 2048) (L2 := 4096) (by norm_num) rfl rfl,
    dsum_swar' (w := 4) (w2 := 8) (L := 4096) (L2 := 8192) (by norm_num) rfl rfl,
    dsum_swar' (w := 2) (w2 := 4) (L := 8192) (L2 := 16384) (by norm_num) rfl rfl,
    dsum_swar' (w := 1) (w2 := 2) (L := 16384) (L2 := 32768) (by norm_num) rfl rfl]

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

/-- The number of set bits of `B` at positions `a, ..., a + len - 1`, for `len ≤ 32768`. -/
def segCount (B a len : ℕ) : ℕ := pc ((B >>> a) % 2 ^ len)

theorem segCount_eq {len : ℕ} (B a : ℕ) (hlen : len ≤ 32768) :
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

/-- The list `L` records the number of primes below `f (j + i)` at its index `i`. -/
def Good (f : ℕ → ℕ) (j : ℕ) (L : List ℕ) : Prop :=
  ∀ i < L.length, Nat.count Nat.Prime (f (j + i)) = L.getD i 0

theorem Good.append {f : ℕ → ℕ} {j j' : ℕ} {L1 L2 : List ℕ} (h1 : Good f j L1)
    (h2 : Good f j' L2) (hj : j + L1.length = j') : Good f j (L1 ++ L2) := by
  intro i hi
  rw [List.length_append] at hi
  by_cases hlt : i < L1.length
  · rw [List.getD_append _ _ _ _ hlt]
    exact h1 i hlt
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    have h := h2 (i - L1.length) (by omega)
    rwa [show j' + (i - L1.length) = j + i by omega] at h

theorem Good.count_eq {f : ℕ → ℕ} {j : ℕ} {L : List ℕ} (h : Good f j L) {i c : ℕ}
    (hi : i < L.length) (hc : L.getD i 0 = c) : Nat.count Nat.Prime (f (j + i)) = c :=
  (h i hi).trans hc

/-- Checker for claimed prime counts along `f j, f (j + 1), ...`, starting from the count `c`
below `f j`, using the bitmask `B` of the primes in the window `[lo, lo + S)`. -/
def chk (f : ℕ → ℕ) (B lo S : ℕ) : ℕ → ℕ → List ℕ → Bool
  | _, _, [] => true
  | j, c, v :: l =>
      (lo ≤ f j && f j ≤ f (j + 1) && f (j + 1) - f j ≤ 32768 && f (j + 1) ≤ lo + S &&
        v == c + segCount B (f j - lo) (f (j + 1) - f j)) && chk f B lo S (j + 1) v l

theorem chk_sound (f : ℕ → ℕ) (B lo S : ℕ)
    (hB : ∀ i < S, B.testBit i = true ↔ (lo + i).Prime) (l : List ℕ) :
    ∀ j c : ℕ, chk f B lo S j c l = true → Nat.count Nat.Prime (f j) = c →
      Good f (j + 1) l := by
  induction l with
  | nil => intro j c _ _ i hi; simp at hi
  | cons v l ih =>
    intro j c hchk hc
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
    obtain ⟨⟨⟨⟨⟨hlo, hmono⟩, hgap⟩, hS⟩, hv⟩, hrest⟩ := hchk
    have hcount : Nat.count Nat.Prime (f (j + 1)) = v := by
      have hsplit : f (j + 1) = f j + (f (j + 1) - f j) := by omega
      rw [hsplit, Nat.count_add, hc, hv, segCount_eq _ _ hgap]
      congr 1
      apply count_congr_lt
      intro i hi
      rw [hB _ (by omega), show lo + (f j - lo + i) = f j + i by omega]
    have hgood := ih (j + 1) v hrest hcount
    intro i hi
    rcases i with _ | i
    · simpa using hcount
    · have h := hgood i (by simpa using hi)
      rw [List.getD_cons_succ, ← h, show j + 1 + (i + 1) = j + 1 + 1 + i by omega]

/-! ## The sieving primes: the primes below `11833` -/

/-- The prime bitmask of `[0, 11833)`, sieved by `2, ..., 108`. -/
def smallSieve : ℕ := sieveW 0 11833 (List.range' 2 107)

theorem testBit_smallSieve {i : ℕ} (hi : i < 11833) : smallSieve.testBit i = true ↔ i.Prime := by
  have hpos : ∀ d ∈ List.range' 2 107, 0 < d := by
    intro d hd
    rw [List.mem_range'_1] at hd
    omega
  have hall : ∀ p : ℕ, p.Prime → p * p < 11833 → p ∈ List.range' 2 107 := by
    intro p hp hpp
    have h2 := hp.two_le
    rw [List.mem_range'_1]
    constructor
    · exact h2
    · nlinarith
  have h2 : ∀ d ∈ List.range' 2 107, 2 ≤ d := by
    intro d hd
    rw [List.mem_range'_1] at hd
    omega
  rw [smallSieve, testBit_sieveW hi _ hpos,
    sieve_cond_iff_prime (by omega : 0 + i < 11833) _ hall h2, zero_add]


/-- The primes below `11833`. -/
def ds : List ℕ := (List.range 11833).filter (fun p => smallSieve.testBit p)

theorem ds_eq : ds = (List.range 11833).filter (fun p => smallSieve.testBit p) := rfl

theorem mem_ds {p : ℕ} : p ∈ ds ↔ p < 11833 ∧ p.Prime := by
  rw [ds_eq, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hp, hbit⟩
    exact ⟨hp, (testBit_smallSieve hp).mp hbit⟩
  · rintro ⟨hp, hprime⟩
    exact ⟨hp, (testBit_smallSieve hp).mpr hprime⟩

/-- Sieving by `ds` is exact below `11833 ^ 2`. -/
def NMax : ℕ := 11833 * 11833

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

/-! ## The two point sequences -/

/-- The number of primes below `fA k` is `π(k(k+1)/2)`. -/
def fA (k : ℕ) : ℕ := k * (k + 1) / 2 + 1

/-- The number of primes below `fB m` is `π(m ^ 2)`. -/
def fB (m : ℕ) : ℕ := m ^ 2 + 1

theorem count_fA (k : ℕ) : Nat.count Nat.Prime (fA k) = Nat.primeCounting (k * (k + 1) / 2) := rfl

theorem count_fB (m : ℕ) : Nat.count Nat.Prime (fB m) = Nat.primeCounting (m ^ 2) := rfl

/-- One window `[lo, lo + S)`, sieved once, checks a run of each sequence. -/
def chk2 (lo S jA cA : ℕ) (LA : List ℕ) (jB cB : ℕ) (LB : List ℕ) : Bool :=
  chk fA (sieveW lo S ds) lo S jA cA LA && chk fB (sieveW lo S ds) lo S jB cB LB

theorem chk2_sound {lo S jA cA : ℕ} {LA : List ℕ} {jB cB : ℕ} {LB : List ℕ}
    (hN : lo + S ≤ NMax) (h : chk2 lo S jA cA LA jB cB LB = true)
    (hA : Nat.count Nat.Prime (fA jA) = cA) (hB : Nat.count Nat.Prime (fB jB) = cB) :
    Good fA (jA + 1) LA ∧ Good fB (jB + 1) LB := by
  rw [chk2, Bool.and_eq_true] at h
  exact ⟨chk_sound fA _ lo S (testBit_sieveW_ds hN) LA jA cA h.1 hA,
    chk_sound fB _ lo S (testBit_sieveW_ds hN) LB jB cB h.2 hB⟩

theorem hc0A : Nat.count Nat.Prime (fA 0) = 0 := by decide

theorem hc0B : Nat.count Nat.Prime (fB 0) = 0 := by decide

/-- Second differences, zigzag, in base-8 varint nibbles. -/
def dec : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | f+1, p, d, z, m, y =>
    if y % 16 < 8 then
      let z := z + y % 16 * m
      let e := if z % 2 = 0 then d + z / 2 else d - (z + 1) / 2
      (p + e) :: dec f (p + e) e 0 1 (y / 16)
    else dec f p d (z + (y % 16 - 8) * m) (8 * m) (y / 16)

/-! ## The windows

Window `w` is `[w * 2 ^ 20, w * 2 ^ 20 + 2 ^ 20 + 2 ^ 15)`. `LA_w` lists `π(T_k)` and `LB_w`
lists `π(m ^ 2)` for the points whose previous point lies in `[w * 2 ^ 20, (w + 1) * 2 ^ 20)`.
-/

def LA_0 : List ℕ := dec 2149 0 0 0 1 0x2319281f3e1f361f3851d1c731e1293583b425462d22e62f42a2912800172c19192a5194a4f582f293a4b38328755451e12e1f01291e22a32b17381961c4d3a4319382d7431e41d21a381939181d32a193a732e493a1f7422e2f033c2f1c1f12a1394e2b3e4b67282b5c692a41c2d1e2181b4331e15541a51a1b2c293b38283191b1a3407382b1e21b181b42a44d2e1e4696e2f1b2c2941e5313a3d41e2f4a2b52e22b1e719181e391812e3b21c62e392b483f3c1b1841a67712b2c1a3941e7667192a1f193a3b2e181e3d43e4b1e2f3c3d384494a1b64283b281b31a31e1951a1d1e02192964851d1821d66282b1e391821e3b383462f2a71c1d1e2f2e1d74a1b474e5f1a1b61a2f5c2d1831a1b1f3e191f1c1c3952818336291e31c7322161e391c562b3c0023f1c53a2d2c2d1c42712a32d1e292a53c1d501f684f193a1a596e4912a1f251c001c12952a1a292c5b481e2b738391e1832b54e191f4672c4f18582d1b4e3b73a1931a3b2c1a1a3956181a2f32801c1d0351c183a3f1143233c3d522e551f3e390582b2f24a21d1e2b2c493e2943a1b2d143876183d742819128282923d3a1931a43d6a3b1c1e2d1193e1b02291a1a31918383b223103a2b3c4b1e12a71b3621a2b2a3912e1d21c22a4918234281b41f1e61b6394819118283551d62001c2b1a381b2b62a11d56141f3c1f6181f32a71282b6663571a3611c1d235382b32e1f294c7701c2931c19618451f2c192e291c1d3a2f31850141c1f41c61f2e3b2a552c291e191f2a1d3825550281f32441a1b601b261a319636191c2b12e731c191a43011a2f2a4522d3a1b1c5293e5191966006292a21d11a0411b381b1e19191828197251b1802831343283f482b1862b1c21c291e062b422c1f101d41c11b2a1b21a311a22b2842928734181921831718001e391c21c2d2a391c4231c2962e5295262c73b2c2c1f71a3321a1f21a4187291c1c1d383d41814331a2b3a1b1a2b1c282f6202321941a7131c61b1821d1c061d2e19319651a01c2f2a55326282b1e1951e3181d1c1b252c2d3c1d110601b1e3176651a7461d41a22f282401b18101873281d31c71e11b1281d01a74281b1f441e1d1801d1a1c761b4125018181f1241a54353662a394610031a50651a294673281b28196202d1e6161d616301e1d451121c1921c151a751241a719618422d41e3221b281963182b61a1512a2b0641f38741f381f18501a70191a641b041251a1332851162301072a71e290762210181a191918341401c2d1a506051e1961741a771851c1931c041d1c1b28540171811b2811f3831504518100021870742181f28192181b2412011a532261f1c4401b031a112142122331181b18181d6218131204371e7360251c321518071a31227627645234632342371c47619404233611a2b285004005621141476322252163211a5001031a03340181d1a1234011223641d1c345434025183203206323202000000020141000201221020140

def LB_0 : List ℕ := dec 1585 0 0 0 1 0x41b1b582972b7e5921b2e1f12c1f1383d19583d23a2f6483f1a65632844b3c4b2e442901e2a1b3541a1e4d41e1812d2a2013f2c1a311e3c3b5918283e1b2c496032e2f42802f0383f5e193904383902e3b3a1e2b56384903c1b53c4d048395241d684b2e51d25a794c185f582b4122c391e51c1d602c2d1a19201f3e3923a64d3a351e1a61f182b1c2d2816071a1b1928381d235196019181e41a391c293a719418143d3c271a291a2812d42a3d3c1960192a1d1252e72e1b2d6232e02294651e591e1e11e3918282f2a34211b4182a16b3e1a51b2e5191a1a3d1a181a2291c3a7b5c2b483b1e291811e321b61c65d682910663b1c2a392811f158493e291847293c2a5b22a43b3847706684f1b1a21d4c69283a3b20281c5b3c3c19291821b2a23903e1185902872e1a1d391e1b1e72c2182b52e191923a3b43c3f6274c1b1b2382d50382b529381d2a2a1d19066172c1f394e292e32c392b28402f6e2f293a24b2c191a52a292645222a3932e1d01e1d21a2d3c2f62c1f62b02a1b2e2d1a180031e1f1d1c1d482d28622d2a72871d181f5c3b284d581d2d281c518295481391a41393a31c2b2c181901b1c2c4b2c562d4c291f2e1f1a191c182b1c312e1d2c3d2a2024d1e1e241d1c1d2e1b62b1a22a712241b1b1a5418322c2951e25352a519281d1851c2b281e3d1a192c19214a4d11483954c2f1c1b52a2b281e52d2e2711d3e1d521a21f2c1d42031f2a11d2a673621a101f0444232f2c1851c2b28031a2d218281930251e1b25621a1b1862f38322d3e1f401c2d1e193a493c19521a42b01c6772a19661b502c1f112a5701387191e70111e5171a2b2c71e51a2f1c1a73656421f42652a191c1f561e2f1c1c229180451e1d182292835181b1811a01d2a371861b11e11d1a31281d21c7443718042291871a51e41b41264291851c192a73528291c19672e12962819650191e30621d180161625191a61b21c1d67281b28197281f1c1a11d11c50018021b44191e1912c31f1c2521360218196002314322003181040721a15211e2b1a181f1820401b2874014131850671a23272182194654163121601212140122116100202324102141214120040

def LA_1 : List ℕ := dec 1020 82061 103 0 1 0x1b451f3e191e4d5c22f11832b4a1f51e1f3c2f4c4b2e2b23a1d2f5483b2c2c2f461f2b4a1c694c1243942a51c293c1b2d54819381d1e32d3a3f6387595e543f2e5191a1a0619193b581a1f3a4d2182533e1d1c1312f382d2a528394e4d182c71c2939281e61f61f1e1e191b2a393a1c18752d18113968394c19393c293343c2d1d382b2e2b28018290031a741c19621f4c1839187392a2d35a11d1f3e352241b21a71a31f3e1f19443e6b1a72a1a19194e2f2f7e4d329382d4c192b3b581e429485b11a66501d4819484b3f2a2c191901c0051c33a592e52c697685184b4e2a7b6832b2a1d1e1d1a5392e484d11c487d4a3f5e3d3a3926482b296142c42f1a1a4f4e111f2c3f381f1803d3c01a2a3b6292a3d4a65292e2f1d7e3b294a723f3c4d3e42e7f5c43b58592a1a51a291e491e194a03b1c61618182e7f2c473e2941c492d1e1a483b2a12b1e3a3f7192e26115283b2c173e5d2a1a72c1d186291d18674a3b32e3191816b19c3f73c372d1e2e2b181911e17281d2a1f1932a351e19182e593a2b664f6c2d2a192d484f78193b013a1f1c11d048013d1a2c3f1c18321a3f2c2912a1a411141b2a2d1871813192c1d211b181a1281751c732f38181b72e5284d4831e2d281f2c1941b41b2282928241c4f5a3d1a1129381f1c5219382d3e192b72c295c2d52a3193b481e3f22a42d1c21c3d3c1c2d72c1911e63d1e

def LB_1 : List ℕ := dec 731 82025 145 0 1 0x4c4b41f381a1b602d3e59382d4a18551d2a673b1c1c28391c3d4e2d3248592e1f382291833c72e3d181f3a1f2b6a5d19381f3e02d1b63a18592e1d53c62c4d2a1f1924e4d1e7282859194e7720041d3a3e4b21d02b3e3e3f1e2d1a61a594c1f76c4d2301800724e02904910481829233c2f74a72d24a4d183e6941828193c4d6a3d2d14c75b682b3a18591a21e1f3a604932e5b6e1f192a18191e1d3f44e5297818f1884f2a2291a2d686d3e2a3d3f5e2295785b132c3c5d4c5d4a22b663f4c5d383c72f2a3d4a1c2d1d25a4f4e04d1c02c4d2e1831d3a51942d04c49248243a7d1c43811f3b12838571a62d1f3c1e2d5483923a5d4c2f5c1f5191f2c1e1b41e2b752a72811b1e22d6383f4c31d392a31e18183593a7181184d4c1e45942a1c51f4e286b1a418111d181d04e292c12f21e51f1e51f2e3961c181e2d2285d2c2c3f5c1f2b4831631a295471e158691c1e5596a4b22e0061f291a5c3d2a1b2d3a11b2a291a1a3f6c1d1f1a7282918

def LA_2 : List ℕ := dec 812 155681 135 0 1 0x182d4c291849381c734b2e482b352b1ac4f191901d28383b1c5f5c1f06c1b2f0283b48764f583b4e392873b6c5b3c1a1d49481292a2f2a03482b1d1f381e1b28492a1d655e3d22f5a3d3e34d184a3d4c3b191c291e2c03d1e31c394a1d2a2d51e1941c3c7f6a1d392851c2a391c39282c1d43f52837c3f3f6182c3b19281e3f585d6e297481b3f3a0192871a3942c3f2a22c3d584d2e3954a2c3d053a3b4c691c24002f683f61c2f2a1d1e1b2a196535e292f41c194f4e0624d3e1b3e039395a41f1a2c39394a101a11722d481b2181b392e1f2a462d4e4d61e283b1a1f68591a3a2b72c2f2b6a1894e34e1f2f21c2c4f1a1c733c1d52b481d1a0192a2d4854f4a3b281a3b181a61f2872819441192a3b2e3b2a292e484947285f6e42d1f74e1d293c294a1929318394e4b5e5d6a3974e2d2d3e1919194e39538191862b382b1d648294d2c3c1b714182c75439531a344a3b1d1b382e183b02a521b1b2a1a3d1a1861e19195a5b5293e475c5d1e1b031e1b2e43f611a19384392c4932a61c31c6b38181e3d583d1c12b3e1b3a4b11e1e29181b251e1a

def LB_2 : List ℕ := dec 573 155778 201 0 1 0x1819771a1a05f6e3d18391c85b3f3d6e1d184d281c5e692c1d2e0494a42b283f4872e5d281e2d01a1c185b184a1f1c2d51a4e2d3b58181f597e592c6595863f1a2a1d1c1501b38471a492e384f2c2d3a03b393c785b1f1e13f5c3d1a4c2f1c61931e537183b3c3e3b453b7824b381381994a61f03a1f52419481d391881f6b7e5f19481d31968769383e3d4e5d54a18507191e253b23c2d1a3c493837612e393a06d5c6b6c2e5923a2b1b1e0382f1d3e372871c3b31a341e3d27a5f2c61b51c3d183a1e4f4c7d19c2d5d582f2c181f483d1f2e2b3a314e4d651f6a7d6e11d244b783b391e1e702e1a2d24942e1b1e4b1c7c5961a3701a4b3a28282f3e7b2a75822931f2a1c14d4a554e5922d2a4a2d291e1c2b2c32d4819284b3e1f02191a

def LA_3 : List ℕ := dec 681 226586 167 0 1 0x1f1e2f643a1f2a1d4695c2d585d4e29281905c3d7324e4b2a5b18283e3f37486f6e65b484b4c1b28192d7c4f11b67211a140328191a35b1b818d3a2c2f281f582f13b118381180395c3b594c22d182c18693e132a224f1e582963b72a293c1b2e701e2f1c771e1b3e4f3c4b2a63e591a385b3a2f261c281f23f7c4f5c4d281d2b386282b37e5d1b5761e02e3f282f1d1a1e1f1e1e496e2b551d1a1c2b2a41a1f494e3f2e2c4d7a4b2d5e2e2f191042291a13f2a2803b6183285129782f31d2e1a2b281f1902a1d441e72d485284913811c1b2d7879418386b6e1932961c6282d28394c792e4a2f61f3c4f38191b28596a495e3f12a0414d4e1a7d4e1a1d4e3d2b3a6186f6c02d1d56a2a2d192c4b3e1d4938281811d2d2a1e41f1d21e51e2e4b3a55d4a26186b4c443938329183c392a2d3a1e5d1f3a2e3d2c5652f6c5b195e4b631e130386b7e3d2e591e4c6f681f1c1f3b5a1b4

def LB_3 : List ℕ := dec 481 226635 232 0 1 0x392f384a056f4c1b1a2c296381e4d44e2d3f14e1f1d384d5e591481a2d42a193d6032c22b4a1d1304e5d58273b413a1c1f2a6b2c1f2a2a3b266171b6a57d3c03a2963e2d1b223e4f013a518491a4d6c183b2c3d7a15b1a4184197a5b1d59198191194b03c1b38161f7293e6426b481c3284d485e491f2a33f3c695e1d19395a51f6c3f51a1c383f495e1d1b3e3938283f2948484b3c6b282c393e1d2f4c282d3e5921c1a572f4e591e32241c42b294e4b3a1f48394385b684d4d1aa384b0513f5a41d1b61a2492a185c6b3e4f2c1c2f23e4d4a5f58181f3586f62c1b61e3d2c1d2e3d32c62b1838194739583c6b1b282e

def LA_4 : List ℕ := dec 592 295984 187 0 1 0x35e1d191d5a49043a2d2d2e1d3c1b621832859286726346191f3c595a54f5a51612853b2e311b1c753c2f2a1c2b39282a282d2d784b252d5a1b181944514a5901f2a387b682e3949185a3b24a6d4c1f2c1d18232d5a1f2e6d6a591811b12a282b2a1e1b5b5c1b1e1e4d1a281c1f18b7c3a22b51d3a51c3971e74a02f1832a3b4e3f06291c5c4f2a3d6a6b7168297761a54c4d2a5d3a5a5f42d2c621b483f2a2811e5f2c2c3b6219587b7e7f7c4b2b3c181824b14a1f1a291685963f5a3818f3a5e5d2a52c3197483d1c193844901841e1f1d3d5c182f28231a2f28001b1c12d3580593811d382d283c2b53a2d1a232d55c1918b18a5361a3948392c02b1d4c3592e6c7f483b3a729281282d4c4b6a7b3e0393e01f2451934c3d64a4d2e182d1d1e61c3b2c3f2e422

def LB_4 : List ℕ := dec 445 295947 262 0 1 0x1a1a677196c18b282a180182a4d1c639583b2c49484f5e796e23f5a11b3b2e291a2c3b2e25b4e2c392c1f54192a186392a44f181803c5d04e19183f3a1a2b2a3b581d1f6e1bd3821c35c3b1b1c54c5f3a381993a484a7d2a2286d4804a1d2d1b7a4d182b3c41f2a395918c192973e63d11c4a18f1a4831b1825c194d281182593e484b3b4c3c6f2c2a2b03c491f6a1f4b6801f1c41b1c73855d3e11e4d02a193a3b3a3b3a1d285d27c6f38293c4f19a6d5e1b394a3901b15a3b3a2902e2b1b2e3f4a614d2c31d5c3f3a1a3d1c52839282929787918e5938291b28452b0386

def LA_5 : List ℕ := dec 552 364278 220 0 1 0x3b1e3f3c2e3f3c2b0191e3c3923e7f6e2f62841c592e1b4b1e6e3b2a42b51a493e40293b7a73d381e391e1e3943182593c3e39183e49742c1d48392f56c55b5c5a596d184e1d2c4d21856873b2f787918a1d03b1a185676371b2e18596a6b181e402a292978792d7e52b1c52e3e4b3912a21c1a4f3828392e1b12961e2293821f1c183b386191833b44a4f184a1b02f2c2b21b6853f1d1c2b7a4b3c511d2e6493831d1a2c472f1d2a281e3d3a4d36e4d1a1d2586f67e2d5f7683b1e1e18292e1b1f5b6a383d2c2a695a2d291e733c31d1f5e1b1f381b59381e2b4184c7b58551f181e5191e21870181d2818918a5d3a62e73d1a358391f1a1a2d2a1b1d683f06a5b42d4a3f71a7c392d283b2c2f2c2e13b2b3e2d

def LB_5 : List ℕ := dec 414 364290 305 0 1 0x5b6c71a492e1b2a41a2922d18834d32d5c1f5c5b28593a1852d5c4b3e2f385721d194a691be5f393a2e292f182e3b1dc1cf4d7c193b1e318a3f7d18a2b5a590182e391961b2c391e4b4a1a1c3d2e18918c51a1c772d42e1c4b6a3f1834f7e2b1f2c628696e2b1e4f21a41c1918392d7e293f1872a3e1f1d5a59381f2e72a5d2381825d6e3d0383d1f1b81992d68293e294a3d1891982805f7c6f1860181d3e39584d1d4a6d5c1c3b2e2b2b6c593c2c4b4e4f282b3b1aa4b1b1a1821921d603a2d4c4d32a4b3a5c4d172184e18d2e7

def LA_6 : List ℕ := dec 498 431563 221 0 1 0x692e21d2a18d1cc5919482f1b1f681d2d64e591f7a3b1a1b1953a1c1b1d6283b385753a3b1c1e401f3643154562c2e293d685b41e5f1c4832d382291f5804a4f191e692e1a32a4f3a275a3f1c183b41c0383f461a4b384c1bd4a4823b1b3e2a06b6a52b2c1b2e3931a2b3e4918e18d52c1931885f73876294c5d3e394a1f1d2815e3f75618181d72d2e31b481c4d2a1e492a1d4518112a394c5181d21d1e194a4f6c6d1e1b483393a387b1b4a1d6661c1f2b73e71a11e1897a2e4972a295c6d4a191871b15c7d2c3e4b4c3f3e2d2e12f2a183f74e7528243b5482f1a132a3d1a45a6b3a1a1186d5e2f01a41d4a5b4c49561842818492932c38

def LB_6 : List ℕ := dec 359 431738 321 0 1 0x29576394c1d181b1b2e1d61f1e2a3b1c1d283c4f3a2d3c4d4c494c4919c1ad4c1b631f5833e3b2d1e3d1b7e7f4a1955a386f1e39471b4c1f2c18211b53864b2c2b7a1ad3c1c3d5c286b6c3d3813f384d4e21f4d2c3a187011a393e39525e1a3b041816b3e19380542b01a71c5196e4d1a722852e4f63e3b4a59394e361e1f6d1881964f6a32d1c1e5d6c12b1b383d3a561181e3f2a39181828062f1968491f2c53a56181d23b3e191d281c59282f1881f5f1b5a

def LA_7 : List ℕ := dec 489 498188 224 0 1 0x5f685d682f38111d4928181a3a4b3a3d485f5c392c192a35b4a1974e182f2c5b584f1c61d3e313b281f438282973f3a4a5391a3b1e3485282f4e1bd6a541c1831a1c5b3a1c04d584943d2c6c18f3c282a1d2b1e21c3f28181d2a1d2d5c5d282a1d43e492a4f3c011f2e1e2b185b7e1d21b1b1c1f3c4f4a31b3c49282d0558412f6c19f5a496c4d2a284c18b5c7f681b04a18b5a2a2b485b281c293d4c395871d5191a74e193f2a182b482b3b58524c1a931b82f73d201e2d1c1a3c3b7a1bb1ba692b3c2d503872b781b54d7a2f49383a12b2b587f5c1834859485b19382c3901484931a64c4b182833d2c2f43a3d181c3b1e3e228

def LB_7 : List ℕ := dec 347 498421 326 0 1 0x290584b6c2b7b28383c2f1b1c02f481e4b2425a3b6192b192e3e2b1d1f3a1e3695c2c4b1a2b3a182a281df18a314c71a3938184d191d381a1b2a3a1897c54b4c2f2e4d046a5f58195d581d1e1f1c2b3c1a2d1291e295e491e44f37a1a1f59583f281e6a1992a660395e3d281a74d1c1a384f222a1a3f3a1d183b4c61e1df2983f492b2e523e63b7a6d6394383d188019b18c2d196a491696c2a3185f34c4928181b196e4b62822b3d2c18419568

def LA_8 : List ℕ := dec 472 564294 248 0 1 0x2c3b472968692e76e18d186c491d381d2b2a1d1b7a4b180183e79185a6f62e2c2d141f2a4879586d18c5b1e22b181d381d1858692c7101b4e5b581b3e4b1e3b1b2a38352a47391a2172b4a1e4d3c2d3c383b3f1c381f4a391f383a5f19a1ab1a51c1b2c02a2b4a391b193c3f183a495281c691a8193d2a5f19c792874e3b6a199382180281f4d7e6b4e1a5b4a396a79591ce4f2d2e3b56c3b58493a5b3812d1c191c2a19252b17c1e19f19e18b1e393c5a4f2b6a2d33c4d192c1b2c713c3b2d28591c839118b1aa4f43c5d5a5f4862f1e5383922a1f291c381c191f19481f4e491b4a64942d1a7a18f6c4f48

def LB_8 : List ℕ := dec 341 564420 362 0 1 0x183b1a181b72a3978491393e6d18a4f481b3a596c19b582a2f3c4f784f4f18e492a3d192c1a5c7f1e4293e1d3c345f7681e2b3a2f191c3d63c494a36c1bf5824a18968185c1a923b3e2a2382b2d3a4d486f682911881993e2c1f4b18c291b3b4e2e3b5f198693e4193a1bf1ba5b1c4d7c2a4d3a3f2052a1d18567819978791d19a3b3b5e2944d4a728336d2c18a1b18f1b87b1e3c6b4e391e2e2f2869682b7e7b23c483b2d2e1a7f6c115

def LA_9 : List ℕ := dec 434 629694 264 0 1 0x381d192b5e594c2d5c592e5b5a191b1a3e5d2194c392c5c1cb18c4d5c395e4f292e2911e06e1a919a4f1d2a4183f21e4b4e1b183825d334e1a406d2c7a1d3f42b5a191d1c0194945e53d2e11b1c383b19381f153c1a5b3a393c4f2a183a3b2f6c49382b2c2d682f383d182d43844d6c691e2b1e3e1f1d2c181b392c5423a2d23f18685b18c4d1818918e5b1d5a1c6d1c622a31851a3c19d6c51d42d3a4b2e1c4e7943e1c1f40797a35d4e284b3a5f781d1a71f2a4b6e5129476b5e2196835f3e022d2c2b5e5f784b1b192a21a3b4e01f4968497c2b796a2b2c

def LB_9 : List ℕ := dec 316 629686 374 0 1 0x5e1f39584b785b3e4d584b281a3d38396e594a5b4a6a1bf4c19578696c3b193859321e183e491b2f19e1b4b1a785b1a2d382b2c718d18e51d62f7e4d384975c1f32b1948191e4d4c32a3d7e394d5e3d1c31c1d6918c190028794c221c4d1c4c184933c19918a3d1b3c2b4e2b2c196539182d2e2e049198493942e592e1c73b48284f5a2b62e4975d6a718e1994e1d45b19e4d385d638192a4797e213933c

def LA_10 : List ℕ := dec 420 694725 288 0 1 0x26f18852e1d2594c2e2d185b1e2e4b77e5b1c5c2f14f58193e5f74c1a393e392c1d182f41c461c5d282e4b1c6e4f491a3a1e1b285d6e5d432a2b5e73d2c1b2e3f2c3b5a3d2f2c3a5f482494e52a19684d1a7f3e1e45b4e1e4b04c1f593e2a3b283e2d1963c1f3e7b5a6f19a6b3e5b7c293f2e22d02828591a186c5b1b19281e1f3e1d2e4971e1c2b439318c4d5c2f6b6a1d1b45a2f3938585f1e22d586b2c483f3a2d4f3a414385f4a1d494e181c1a5f18182c72d1c3a2b38393c69583b2e3856b2a7385b6a2906a6d483f586f381d3a3918

def LB_10 : List ℕ := dec 293 695064 418 0 1 0x4b1a4e3c7f2c15c69524d1aa7918e29694c1a2b591ac2d2f2c053b6e17d3e294a5c1c95a4c4f4836b28182828594c02f1d483f4461c697818583b7d5e4f17e6d1c1c3b1c72c41c72c0391b4a497a6b74c7d3e5a69197c296f7e2b5e1f5d2a2e394d2a6828692e3d3c484b35a2b43b42e1d3a18b3e1b2c251b3f7a191a392e185b5e71a1a592c4487f3c25b5e195854920285b

def LA_11 : List ℕ := dec 394 759550 295 0 1 0x1c0295c2b1d1a2b1a6c4f1b2f1d485e72e7f2e1b1f4e2a19d18c3f0285383b2b3a4b3a471e4e18f4e16f381d585784d1843d2a7f2e48285d187c3f2f2a5264a2f3e1af481e1e4f185a1f56296a5b02e3387972c23c1952d2c191e4a5b3a33b5c395d4e1b584b2e1f3a1a6f65c286b1c293a2b783b1f193d4822e3e1ef1c83f4484b03c191e797a36f67a4f1884d63131b3a3952844d291b81f394a3b3161e494e039182861997e54b1b84b291c2d1a3f1e6c0186b43d6195c41b3a3f32c182f3a1b02b395e

def LB_11 : List ℕ := dec 296 759732 416 0 1 0x194e671d291ba7d7b2c2e7c195b56382902d3e1829287d5c2d18e18b19e2cb1a81e4c2a2b62b1895e1a19686b3c2b58366b1a385f6a4287b1884d3e1f359287a3d2f14a483b02b3e19b7a3293e4a19d3e3c1d669485a6f1b1a61881ed7a1a182f5831991a86f04c5c391d03d7a18948719b28a3b565f7a6f5c2b1c4c1b94a1a5a3b4292f31da3f6f3d1618a1f2b2c43b4c2d4f68

def LA_12 : List ℕ := dec 379 824042 310 0 1 0x1ce5d2b2d57e119d18c3b44e3b2a6f18c3594c2d043c1f1691b81896382b6e5f382f7a1a918281c28293a3f1f2a1e2b33c7f7a2f3a1d22d3c4e19d38203d1bc6d2a6b183a3847696e1f39582b393c62d53e292d65a42904a6d41c1d1b7c76d4e3b18e5b2e5d44c182a18d2e3c5f5a2e19d2e5a6d1a52838193a5d3c2d1a219483f55a4f3a191e1a590784901b496e75f18859281d22e1b1c4291f6a1f3f63c4916e392f601c3694c6a4d3a492831f2c1c181f1a185d4c3f48331f71e432

def LB_12 : List ℕ := dec 270 824086 439 0 1 0x18282d5f19a4d2e41b31e382f01e495e3b2b58393828693c7a1df6e11486f3e4595a3f43c15b1ae18f601d1ac18d435e5492c19341e2f31282d5e1d2a1f2f017e7d186a3b62d4e2a19b5c295c7f1a182d718c0390039682d1c494e74819b19c76b7484d5e1d3f4e51a2b182e3f471c2e4f1f7e79719a69481a19f1981c45948194d3e18493861b

def LA_13 : List ℕ := dec 369 887676 340 0 1 0x454484f6c591a03c3b2a1a2d5d4a285d2a1e2a394281b51e2b1c4a4942851a1d1891882c3b1e22b194865d7c3d53e4b13f5c1f4c2b3794e2a11a2918c1bd3e2c1e1b2d1e2915c7d5851e1b3f3c381b2d3a2b581f281d1f1804393c3c1a94861e761891a82932a7f7c596c6f1ae6b2831b29297e1f2d4a4b4e65f7a3f1181e3b3a2d4653f4e1f1f194e3b2a31f19c1af682f3d58382d2a3b4158292f6b3e583e4f6818f4381838593e6b5e291d3e1e4d4e2f4b03e21382d73f

def LB_13 : List ℕ := dec 269 888061 454 0 1 0x7a2f68193154c01f4b3e691e4e3b3e2d1e3f4822483d4d384e6d2a1382f2c1d2e3d32f1e4e1d1c91dc29291aa1c94a3e72b5f1ae5d1a1074e5f283c383d1c2b1c2d3a3f3e3f3c796a1c3792e19a7b4a39587f1a6a5921886b3c2d63e3d51a34b2a393a1d2c3d6c559391cc591918196e1bb71ba3b7a1fb7c1e51c4f4a1b3c693a2f2a496a1919

def LA_14 : List ℕ := dec 349 951352 333 0 1 0x418793e33c593c2a1d57d7c1e2b2a1f1b2a41b0282819b683382d51b1b5e184d2e12f21a293861873b7e7d583d4a2b4e2b24928182e31d52e2f18c18f2d3e2b2c6452d2381d1c31a6b481e3d2e01d74a5d6c1b191f5c31d2e6292f6b7e1a2b5c6d48292854184b3c4b1986b2831a291a1944291a2a31f382f12c01f2c7e19b3b2e1b3a41d2c31e3d015e3f1a2b42b7c4b5b681f1e192a25b4c01b3a7f2a3e62b195c5f2a2a2f2a29319a19d3e4d2c

def LB_14 : List ℕ := dec 254 951630 494 0 1 0x3d2963a1d1a549282c64f7c5975e1a918a41d593c485f3e72d22c34e4d1a1f6c594c1a1895e18183f5e54f1b01a582f5d7c3d2819192293e2f384d7a3935c292c191af4c4c2a4f3a1d7584d1b682929484b03c5b186e4d1c1f2c73c6e28d2a6862d63a4916e6d382d19828f19851a3c7d7e694e1ad7e54283393a775e191a9

def LA_15 : List ℕ := dec 335 1015011 332 0 1 0x182a1d1b62c2f1e291a282f2a6c6f67103c2d2b1c01c18286b5e692e5393e283a391b2a4a5b26183b787f3c218b7e43f3a2d18e197f3c31e19d1b83f34a2b1d1c2e2b395a1a6d5c281b4181c18d2a541e5a3b7b2c38482b4b1c2a3a792a1b2829482b6e7b4822a2d595a171d15a3913a4d7819b02818a3f2d4a1693a7181a47751e351a1d16a394d4e7f18e0291b6c691e1f4064d2a1803a594a41f2e1a66941881f5b238172b48

def LB_15 : List ℕ := dec 242 1014761 462 0 1 0x3c4f7a6972e656c7928051e3f1831aa1bb2801974a1e1d284a19919a6f2c1b1d394a02b6c42b1b6d683e3d1a523687b6c2b2e1e5b1f51a5a6922c1e6b6833d1f3a1828652a181996e4b2c384b4e1791d18c485d4a7f1a4c28696381f2f3e3845f2f68182d6e59494c39596c133841f2a4a7b685b1e182f1a4e

def LA_16 : List ℕ := dec 332 1078185 356 0 1 0x1b66f6c318f6a714c2946c3f1d3b5a3f481b32b2a3f3c2e41d23a5b11c6918e3f319c7b31f1c703e1f2b14a2f2c381b2f5b1e6a5b7478145d1e62801b6d4a1b581d41b2a4a691e5c6f1e4b1d51982f3b05a1d31c41f2a4e18f1c54185c49201e1b382d482d53d6c1d494e6b5a233f2c3c4f293a4d1cc5f2e2f3d2a1a53f18818b18a1f5d1a1887f6f1bc4d4c17194a2d2f3c2b6a16f6c6f5c3c7d1e4c1f1f4b4c3c594b1b869

def LB_16 : List ℕ := dec 242 1077871 500 0 1 0x1b1e2f2e1ab4a4c181c2a292b2918c7b1b25a3d5e284d6b2c2a1685b1f2c691aa7d05a2f4c41bd582c6b3a7a55d382a27d76a42b58074f18a19f39198397281c283f7839592a191882f2d581d1e1933502f381c595c3d72d1b8494592a1d2a2f6e6d3e77d4c4a72c45d2c48186b65c53b5a3b5f1986b1b4e29

def LA_17 : List ℕ := dec 330 1141085 344 0 1 0x3f1c4818f1c81af18e693a2e1f25818f58191495a3d6e19d18119a3b3f5c3f3a4e391939133d6a543b6a29495c395b1a83b2b684f28212f4c32c5f6e2d1f2814e3b4d58769484a1c18d1c12c1a2291c1b4a3c5d3618795c19691b8491e2f1f781ad19e2d1a6b77a392821e22d7e3b5f3a2a1e3925b4e104a4d1b1d2c7e691e4e792f6c54f7a39191e2c4f381b2d1f4e2f64f78595a2f284a2b1c2f32e02967b19a352a1b2a

def LB_17 : List ℕ := dec 251 1141346 497 0 1 0x6b586f1881f4b19a3b4e19b18e6f123e18b1e19c7f18a6b1cc795918697c3292821a493a3f785b5a2d396c2b382b43a2c199687d1c1a819b176e3f3a3d1aa7d11c4d183d6e1b3d7c199681e1af6833e61d18c7b02a2a793e192c75941cc18d18a1cd682c3f3a1f3a5b2e4f2c3d2873b19c5b7845f3e18391891ca1f2c1b

def LA_18 : List ℕ := dec 326 1203747 363 0 1 0x481d486e18f1f1e55c76d36e28691c484f2b382b5c2b1e3938291b182e1c284f01d005875b5e1d2c2c3f32f1d18a18d584f198364b0684f4a794821c5f6818f1983a6939585c1df1ae6f74c2a7f4a1b682b6b1c5a1c3f185d1ac74f262b484b3a1c44291e3f1c2b7e4f4667c1cb3a1917e4b1e1895a62e18f19e19d5e4a1b18596183f1982d2943f1e119e1ab1a5e5b3a1991a8741b4c18b14a79483a2f1a85f34e5b6

def LB_18 : List ℕ := dec 238 1203838 508 0 1 0x181e1b81df6a21d2d185a5f6a6b1a5b1ae59618493c3e4694195c186d4e4a3b2b3d18e18918586818968291932a3f1a1919c1cf5c2e3b3b318818f01a87d3918e494b1aa2d13f284d4a5a4b3c4921c3447e1cd3e181c1a5d1c3681a919c61f5f3a4c53b66b1cc18f6e1d18d18a486b624b3581e1c53a2d

def LA_19 : List ℕ := dec 313 1266059 394 0 1 0x2b3f57e5b7383f4c181d339193e71a1f1b05c1b3e3b2b3c24d7a18d7a4b2e3f4c496a5b3a4d062e591823e43d18a595c1bb483a2a1a5d4f7a4e1eb7c3a3b483b1887b3f3a1a1b1f6c2a3b791884907e295b4a1d58591e1a5d04e4f23871e558492d1f3c3c1d2f26a4b02a3d1f64e61e1f4f18e2d1993e4b5e181b18583b12a2f1d1811a1a4d1e38191a2d1b2d18849482b1f1e213c218f6a4d6e2d13f

def LB_19 : List ℕ := dec 223 1266272 548 0 1 0x43f5c2b29196a2973b2c4f1aa1bf19e41a2974d6c229496c34d3c3d1b1e4911ae791c85d1a919e2c3d6f19c692c056e2d1a97c62b7e18b4a3b384e6b5c33d434593c1b6e2818b75a387f784f2e05d6e06c1ad6e5b3d184c4b1b87f4a1a6b14c5b2a5a5924d5c6183906681ab6e1b64b

def LA_20 : List ℕ := dec 310 1328294 364 0 1 0x7f5e291a293e1d3a5f5c19f4c1f38181d718c2d7f4e181b381d3f5a22f4677a5f018b1de6917818f1d6a61952f4e2f61a492848496c3d2a3f36e1ad7a3d21a528183292c1b12a1a3d1a81ab6c7b72c52d1a4282e1f48797e5d1a2b1c1c743a1b3f4c293a493c3d1c29182d2a3b3c1a4e4d3e1b1b3a1d3d3e2c4b596c6e2f7b1e4c01997c29196a1971f6e1af418c1891c783f591e1e1818591a18a

def LB_20 : List ℕ := dec 226 1328530 535 0 1 0x1d75c196281d792f7c2f2c6a6b3a4f683f1c3818b6e3c3f1b1f019a18d23819183945e18b7a3d7a2d4d7a1cd1aa491f7a5b583f63a16a18b285f3e6b3a24a3a6b681f4f2a54c67d18a14f3c293d1b2e1d7c7194a192b2d6c19f7a7c1a956a1af1aa6b1a84f1c59194e3b5c6f35c2f4b18a

def LA_21 : List ℕ := dec 293 1390529 376 0 1 0x1e4d2a2c291f53a18f18c2a2d41e322942c11819f1a83b31a2b5c3d2829193d5c58697c6d283c5b1a1c2e5f583f1c49481a1b2f3e5d4872a373827819f3393c3a33495c29393e2d1e1e4f3c321c1d586b62c1a49482d681b3693a3a7918e2f2c18d6c522e293a7d53c01b17e6b1c1f4a5f4e4918e5d4c3b3b7c1d3f2a2b1d5e1b3d4c2f21a12e2b182a387d48537d5e6f4a78

def LB_21 : List ℕ := dec 215 1390706 557 0 1 0x492a62f1a7f7c4c1f294e3b441b1b3e4f4c11936f188381974e2d2d3e4b1c1d13e2b1d495e2e59481884d1cb1ac1d64f19c1a95c5b4e331a03a18d19e4b1a1a12a3f283f5a1f73c3b3e381d96a291c7c7d42861c1f2e391884d4f02a384d41e3b18a4b3a2a3b2a1cd6c2f3c

def LA_22 : List ℕ := dec 295 1452337 399 0 1 0x61d6c3b1a5d2a03b19c1cf1b81d2f2c595e189683c3942482f12b4a3f5968286d3a3e4b2c1c7c1ad18c6d3f6c291e332b3e2f2b6e3d381941a71a3d1c182f13197803b2d2c54c7901bc7f1b3e459381d52c2e2f5c7d18e6d72f6e1ab1be7d3a3c1b1c1d1a2a12e1ab5a2f6919e423d3c6f2e1f19a5f03d1c3819282486d56c49481c3b481cf2c383e1d33e12929519c39392f38

def LB_22 : List ℕ := dec 218 1452323 558 0 1 0x481887d392c4978593e2a1992a2a2863e392973c19d7a3d6e5b486a5f781eb7c7581892e6363a29484f22e4f3b3e4a1a79383a19f29c1af43c393925e51b6a7f2d66e7b6a1f182e282c1c95c18d1aa286b2c595e17d5e52e13a7b1be18f19a3d1a966a291c6a18f3e383c1bb6c

def LA_23 : List ℕ := dec 291 1514172 409 0 1 0x18a2b7818d284d1b665e6f24c492383e1a1b491d23801c39291a02e293a12c46d4c1f05819d585d5e2c291a5e6f691be2f2f1a7b2a1aa18931982d6d2c496e2b13941918a7f1aa1897e18f5a2f7c4d181b191e1b6a19f381841b3e593e1a4b718a19b1d86b41c4f4c49052c193f48684b494a311e41d2941c3d667a19d5e285f2b782d381a6b583d6c4d5d685918a3d7a5f

def LB_23 : List ℕ := dec 216 1514061 591 0 1 0x1e84f1f41b9386e592a03b7a3c1b793d1ac2a1db4a518a2d4b1ce19d4284f4c1ab1de394a5f1a2a2f692c7c691a81cd5a2f581ab4c1285e2c1d918e2c3d3c6f4c3c19b4c1b4e593a3b196c4c3f22d0195242e3b61e32e3f31e7f7e4c6d486d3c1a5a6b51981b923c3f28c1e9

def LA_24 : List ℕ := dec 290 1575667 430 0 1 0x23a6c5f1a1e3b1438392f41c5852f6d1ee6d3d1a4e1896c2b3e1f2e196b3c1b31c6843d4d718c1991ca692d196c3f387049283918a6d1f7c1f5919c7d483b282f7c2a1c92c381f18e1df1bc295e3b3d1d3b4a785d2c3d2c3d1d6c11a3b493c2b4a2c1c3d3e197951a1c1b4c1d7c6948391d2d2a75e2d2a2e5f2d2a4184f3c285c189552e4e392e1b2c6d1982f591a3a5b7

def LB_24 : List ℕ := dec 202 1575914 604 0 1 0x782b32e5f4c16f281ae1ad1b18a2b31a694e2a335b15c4a2979183a6c7d297e3d4c1af7c2b4b5e2b3e1d03b181b818d2b184e7f1de481ef691ba1a2b655f7828294d1b7a1c1c2b294b3019e2944591b519c13189585b2a4a186b3a19485e5f1a1c1b693c49

def LA_25 : List ℕ := dec 279 1637378 439 0 1 0x1a282d1e5f1a81991ac4b4b21886f2b28053a1d5e5d6b683b4e31f1e5a55d2c2c39597e1d283d5b1b83d6493a02b3e1d62933a1d603b1a83f696e194d286c189483e59581f3e2b1cd1a818387b6a7f4c1c2b431e192a3e7f64a217f3c2e71f5a2c1ad578396e7b1c28318e4d018b282d2a2a483d21f481c285b4f4c6a4d29383a1ad3e7c3f1ce1ef3c1f39

def LB_25 : List ℕ := dec 210 1637054 611 0 1 0x4f4e75d7e7f1ac6d1e17d7c4d4a5a7f4918683f584c5f1a49184e518d5c4e491e493a4a18f4a2849187a3d2d2a4d1ba1d91c834f1a829f19c4a1bd1882f2c490282e487b1a2c5f3e4d6e28189187188791c7e2a5d18f1a2a3a22d586e1ad0282f5c2d3f5c6c55d4b18

def LA_26 : List ℕ := dec 279 1698572 433 0 1 0x31a5d1c81af1a5c0491e2b2a3a19d7c4e315b5c71995c03a102e18b4c3f1e4a181d4e18f1e3972c5e419392f2c3e5918c1893e49221a3e4d294a5c59685d3c556d784c1b919e697a6d1a7d197a4c1f3d3a38497a19d4a4c1892e2b18a31cf4c4491ae69281a2b381b503d1aa491862d2b7a319b185a2b1a2e18d7a3f188195b3e35d4c3c3b2a3292968386b

def LB_26 : List ℕ := dec 205 1698785 595 0 1 0x392c1c3d6a5d3a3d3c4d1da1d7b383d11c484819d19381e1a85f1891f1c582a06d4e3b7a5b1d764a6b2a6e5c1a96c5f18686d286a7f1eb19e19e18f18c18293d381a18b19a582c918c62842b3c2d565c62f3f1ae1bf3381e2f3c4b1ca1ab4c6b7c71b23b18e29

def LA_27 : List ℕ := dec 276 1759946 443 0 1 0x594a18a18d2c3e594192f7a1916d1ca2b4a1b5d1f6e7f2e2c22284d2e62f1c2d3a2f3819026c7b02e492a2c594e4d43e3c2f6b1dc6f296d1b85f1c4c2f496a18d18c2f48189486c1c1ab3c1a2b4a3a495b28294c1834c2d391f4811b2b5c6d2a2e491d81dd191882d384b1c63a3b191e6b3b18c4a01f547d7e5918a1b292d2e4c6b2a1a2c381a94c3b18

def LB_27 : List ℕ := dec 199 1759738 624 0 1 0x6f1b81b2d1c3f2d19a3f2918c19781af4f18e75e7b63c76d582a7b1882b4e7f4482d3267a1cb1ee691bf1b84d4821d292c182b1a8692f07a3b1693e281e381af4e2a3f3e5b1a2e4a19d6e1c5d2e5c4f51af5e1da6d1c5f4a791ee6b2d4a293a123b2f28

def LA_28 : List ℕ := dec 260 1820905 454 0 1 0x4d19585d1cc5f57387b2e1c01c5b19e1a95c2a3d6c5d41b1831c731856e3b392d1a3a52c31e18f2681f183a2f72a4b1f6e75b786919e4f4f548282f783b26b5a3f101e4e491c4c33d23c4b685643d193f591dc6d2d7a2694a4d1885f18c1ad3c6a594f1885958384f28691e385918e292d393e382f284491881f23f21a6a1e919a4d

def LB_28 : List ℕ := dec 190 1820960 638 0 1 0x4e397c3f73818d5a1c1f2e4f5a1d1c1a2d2914c2b4a1e19d3e1d6c3e18b791bc7b19c5f2a5b38225b1fe1f91d1ae5f1a86f5d2c183f5e1c1c192a45381a1d7b5918a492a4676781af7a491a048333b395a3a6b64a3b6c7d1aa15b1f7e1af1e

def LA_29 : List ℕ := dec 258 1882143 447 0 1 0x1d292a27191a154758491e3f3d1ba2d5f3e05f518c42c394f18382c7f7e5619282b02942d2e4f1dc18f1987b564a5e1a92c3b71e2f7c1e5d3c2b3a6b4a2d7c4b1895e1a2f43c5f2a2e2c1bd1da6d384f1ac19b5a502e4f1e192e2f7583d3a49191f3a4d1ac59192a1a5d2e03a3f18a4f1af1da49464e796a3f184d1aa1b13e3f29

def LB_29 : List ℕ := dec 189 1882095 659 0 1 0x6958593a03d38385d4c1b929c1d95818f4a6e3c6d293e43b4a3c31f6d13e1384819d6e581b6d2b2c37c2d3b384b1e4c5d1b2e5b2a18483b4a6f618c39192a53f2e281b1d4a18b3b4c18a6f2a3d2a1e3d1b81a9242e5a79381928785b781eb

def LA_30 : List ℕ := dec 257 1942672 446 0 1 0x6367f4e3a69687c1bd26c61bb3e19c4d3b1a1c2d4a1301895c3e4b583d581bf681aa18d686b5c3b2811c6f3b18e1f4a18d3968684d72c1d1a31c1c3c6f19197e7928284d6e6b1cc1ed6871a6e1ad4872f6428234b3c5e3f51f3c5e1ab684958183695e1d1ad1da5f3c2c4b284d2e7e18f18282918f19e2a01e1d12a3d3c151f3c

def LB_30 : List ℕ := dec 190 1942592 629 0 1 0x1c4c1ff1ea7f19c1d4b6818f7826d6e391e2a5f1f782d38395d28a7d1e1e4f5c1892f18e2e29f1aa18a1b95a3c393a3e5d6919c7f3a11583b34e1f5b1c2f1c482b4f1ca4f495e1b1e22a1f492497e2d483d1f6a3b56f4c2a7c5b294a463b4e

def LA_31 : List ℕ := dec 248 2003327 465 0 1 0x5e0418a19b6e3b5b19e1af2a4c22f475a79682f3f2a24826d6a4d3e1e19d1ba7b2e6e7b2d57c292c5f78192f441f441a191c1b2f6c1b1a3f1e41a77a18d2e2b3c2b2b4a3b43d3a186b6c582d2f2f4a42c4b4c5b5c38691c52d1c5c6f18c7d381b1b282c4f42a3e1cf1ae2e2934d68797e3f495a2f03e2e5f281d3c19

def LB_31 : List ℕ := dec 179 2003492 665 0 1 0x668583f12f2b38293a3b2e0193b4582b281d666d18a618d3e2e2a39586d381b3f1a819b7a7f19a2b12c5b1aa1892e1d72e5f1f3e294a3e5b3b5c4c5b719c6f2c5956e1c18d581a29593c5e1ab18c3c4934d483902a5a5902c2d

def LA_32 : List ℕ := dec 246 2063947 498 0 1 0x1c281f1c1b1e2e76b28441a52a4b3c7919c3818d18e18d719818b384c19296a5912851e693a1d2c49419a7b3e3d0536829381d31f295a2d63b483b4382d782918b5a62c2d4d1819e1ad5a643a293b19282c4b2d78492f582b4a1b1a96a5c2a4b534f481e2e495c7d4819183836f1887d5c3c3f1c1f193a3e6d1c6b

def LB_32 : List ℕ := dec 172 2063961 686 0 1 0x73e4b198693b183e29244d1ba6d4c6f1e2c5c4d787d2a1a491e1f297a3f4e4d393e3c281f2d01182d21a068189582c18f3e20184c079519a6d5f6c39286c2ad1ba7c397b2e297c5f685b3e029376a192f3a1a1f3d29

def LA_33 : List ℕ := dec 240 2124206 490 0 1 0x3d56e2d19382194c4d395a5b41e2e519115e71b18d19c1b2c1b9781d3945a185c6f28694c2f63c105a18b2e3f3c3d2e6755c71a79422e582f2b4f18e4f4a39383c79684f1f3c3a3b5c6d33c7f1a81d394d485a5d384919182b1ba596e4d65f1a2381891ac3e592c3d1b193c01d221a849319b1986f18a189

def LB_33 : List ℕ := dec 167 2124357 683 0 1 0x1e6c3b2a1a005d1a3d18c4d1e4a15b43c0491b3d18e1862b2b1b278287d41385b4c5283a5d3b7a1f42f65a4f5a23f2a293833d397a5829919a194c18d31c19c33946d6818d1e81a1f5b74a5f6e581819f4a2b1f

def LA_34 : List ℕ := dec 240 2184437 484 0 1 0x194c2955b4a4a1d2b791dc7d2f1b19c66b484b5e3b1f19818916391e3a1612a4f581e197b4e293a2918b5e1cc18d1b6d7a41f1d1c485f2e3e23d19a7b183a793c2c4b4c18f6c4f581b4829686b186b1e7585f19a3f157a7d6228282d2e532a5b2e6d68519819b43b2e2c1d287b4c19381c4a6b1e1a391d38

def LB_34 : List ℕ := dec 189 2184335 708 0 1 0x1891bc1b1bb487c4f2396b19c5a19d3e5a19b18e189652c2e4b1bc1a97861ab6a291ab1b8585b18d1e81d95e4e3d1e1e5819919c7b5a6f7818b4119a71396d4a6918c2c1f1639018c2d2d687b4918e19481c91e4a3a1af5a2c18a7b272a79

def LA_35 : List ℕ := dec 254 2244526 486 0 1 0x5813b1c196a7b1ba1cf1f1e819f1c4c4f1e04b1aa1b1b71a4b2d1da2a96a585b2a53a4918c3c1ed2981bb1d154c2c7d1818c7d5a2b1f3a487b2a1f1c81ab66c2f4f2b4c192c1b4a2b55d1c4f7c3b2d1a8393c5f283c7d18c6d284c1893e2f481c191b18491cc119194d2291e71de7b1ab3a1a6818b4e4d1f41bc1a96c282d1

def LB_35 : List ℕ := dec 175 2245115 677 0 1 0x2831e1f1d82bb1aa4d584f3a4b1aa71c19b2f1aa19b3e2922e4c2c73b39591aa2d3d3c1c292c387b3e781894e73f2c291a48691b4901a18a2c4f22f6c6d5a4b3d1a83d2911bc52a1895394e19e2ad587e6f77f1d82d4818

def LA_36 : List ℕ := dec 242 2304935 512 0 1 0x44c7f7a4718d1ca2f19d4c3a2b782d19162a0293a4d2d18e3b1a42b1886b5f193e1c4c29596a1d3b184b3c19e6b4c19f3e4a31b287b7c5f374e2d2e6f7c7195c79781b18d5e6918c43d2e47d1a85d19e1db2a2a292a1b1da1d903c1f3c182d6d1d81b7b1a5a18f4c3861b455c1db1e7a1b4c691c1e5b1ca1c9

def LB_36 : List ℕ := dec 166 2304655 717 0 1 0x6c2f3a492c15f6a1b5c1d2f684d5c792c4a57282d1896e6063d3a6918c1b1e19d1bc71b7b18c18b64a3f2a5c591a2a691f18c1f4219197c1d96c595e6e1a95a1e1c5f2c48795e6f6a42c3f3f04e5c5f537819d

def LA_37 : List ℕ := dec 236 2365153 516 0 1 0x182b1d81991c2b33d7c6f4a2c7281a4d22a3f391a818d581b1d5d2a5a42f18e3b393f18c2e1e9383c1a1b618a19b37c2d492d3c2c183f4a2c19919c7d1a1956592e6a586f31e3f3e54c2d55e7903194e395c01a93e3c4586b4b18c2b4f1b869193c1a52d1c19b284c5e1d1896e34f2b4c2e2f19a6f2d

def LB_37 : List ℕ := dec 176 2364973 737 0 1 0x381512b02b4e1a3a28199284918a3d35d2d19c2b3c2e19d1dc1ad1d6e18f1981c7d18e4b6d1983918a69393a3f1b1b7b29e4a1bb114a6a7d5c6f1a2c5918a4f1b482a6d6e2d11e1b6e3d4f3d3c3e1b394c5f1918a2d3a18d

def LA_38 : List ℕ := dec 226 2425155 517 0 1 0x1c6d23d5a4f2d4a23a66d193e1e1d1a591e1f4e4b5e2e192b1963e1a49181a496a0293a4f12a5f18a3d1d181c1f31e1c183f18a2d7b4a4f5829194c196f18a3d2a6f586d1be15f7a5f4c01b1b7a1d97e1c4d38291b4819d1bc5d2a4a5b4a2635934c4c1c9682c2a2a5d6392d6e72e3b719

def LB_38 : List ℕ := dec 167 2425368 724 0 1 0x7b7b18a4b496e1c19b5a1e2f21f1e3f1ca5943f1985f4e5d6c2b3c36b1f1ba1c9381b3c3e2914a18d38192d1aa19b1b24a3f7f2c819f7a3f4a7b7a6b6a691d1c194c4f6e2191a194f7a6d6e3382b7b4e52c1b1b

def LA_39 : List ℕ := dec 221 2485158 492 0 1 0x482e392f385b484a5918295f4c1c1d4a274b282e3f7a72f6390281b383f3a5a6d7c194f1e218a1992b396843c5d377e1b19f4c3297a1a4f7818d2c38273d151a381e594e1f1a1a5618b6c4a3b18b18e6b1c81ad1c06c7f5e5b11c1826a4f3e1893a1e2c1891a4e21d2c2f482b382c

def LB_39 : List ℕ := dec 163 2484861 690 0 1 0x7c3f3c1b94c6e4d2969583a391c1b03c244d181b3c2b19a7f1ce1cf6e4a1bd1d7a719396e2f3b4b4e18a4d062839292b3c6a18d6871e281ab1bc4f6921ba1cd6e626f5811a3a2d3f784d3b6a2f3822a1e4a

def LA_40 : List ℕ := dec 225 2544710 525 0 1 0x14a2c72f5968192814a592c386f2d582a2b3b2f7a7b1ba1ad19e4f19481c793e282d4a1b1df1ce641d2b15c1b482918f19823d2d581591c2b6e6b68395a4f6c1b1f795e1e1d655e18b5d4e4c291b18a1eb19818724b19c6d2e64f32918e2f787b2d1a118e1f7d2818e7d12c186385d1d6

def LB_40 : List ℕ := dec 171 2544902 741 0 1 0x1ae391c6f1c3e584f68792f4c3c1ef18842b18e19d1aa191a97e1a49591881901b5a2694e23f282919295c295c5b7a01ab3c5a691aa1af5b1984b18c1ff2881919919e4f3e7951882c3959619c7d618a18f4a3866b0

def LA_41 : List ℕ := dec 227 2604472 535 0 1 0x1a813b6c4d5b486918381f7872b7a1c1b91da2bf28a4b391b5e2a1a1ab1881f6b19e391d386918e559678294f6a5d3c1c4f7e5d4b261d4a2b18c18b292a3a181d1b5d1dc1ad5a319385d1da1f91e183e1c2f21381b2822f1e018796a2a4f3c1dd28c3f191b6a3f293904c1e280793a5c66f

def LB_41 : List ℕ := dec 168 2604212 766 0 1 0x19e282f4b26f5e4b1ec19b1be1ab19c1ab385f7c486b3a5f1986b436a4f4e2c7f4e51e1a3b18d3a267e19f1d18e181a918e392a2194a18d37e26f5e13823f1a291e1f4819d1ae492c2d39191e1b8199481e1a19d

def LA_42 : List ℕ := dec 224 2663878 562 0 1 0x1db4e1cb1ec3f1986f385f581843d2b2c3c292a3f1e5a4b76f1cc1991f81df7a71b72a18b1e7a7b582e6f02e3f7c48189291b84b6b296e2b190783b3d5e6b6c74e2d5b2a47282c1cb18e28192c1d3b581b495a5a7d618b2a4e6382b2a2a18b05a3f5e6b4c62b5a3d18281a7d382c2d6f

def LB_42 : List ℕ := dec 165 2664215 781 0 1 0x7f19b781ca1891846a6b4f6e62b1a4a6d395a1ba1cd6a6f19a1cf1e4a1c3d1b2928a1cd01be1c91e4b581f6a3b3d7a2e4b32b1d1b81ed685e291f3a596c02d19b191ae4a39294b7e794e1a2f7a4f582b3d069

def LA_43 : List ℕ := dec 218 2723423 508 0 1 0x4a1d4d5e3f194a4f39287c61a96a492a5c481bd4a32f1c54b4e3e4b548791ac54b5e4619d584f295c4829571a186918a3d4a4d02b7a19b1a6c597c1b18b5e1b02e581f1af4c3d3c54e4819f7a4a7f2392f2882ad486a239195a1d1a2b392b18a23c591b18e2b2f3c6f1c1c1c68

def LB_43 : List ℕ := dec 160 2723396 743 0 1 0x3a7364b2491b81896291e85b3b1c7b3c5b6a293c5b1dc1cd28e6d4f592f1ce4d192e3b5c3b7681bb19e1d91ce63d7643e19795491fe181895a71ab18e5d1d1aa7f46e792a4918c1c3f6a192818b44e2a

def LA_44 : List ℕ := dec 222 2783089 541 0 1 0x191c5c2f4923e0695e2c1e182b5e19f2c2c719b6c23a2a4d4d7c45692f18a39582d2e2d2b4a4b1a1a5b1a82d6d5a4a2818974e4d2e75a7b48392c18d1ce7b1887d1ea1bd297e797382a18919812852f49481a2e3d5f1d819f3e1f28491c3c4c2b192f787b05819d586a1ab5e2a391e

def LB_44 : List ℕ := dec 154 2783224 766 0 1 0x384e49395a18b18c4a1c45b41c19b7a1b3c4b3c5e1e93a1a5e04b1a1a4b36869686a7f494e192c3b1a1b18b1fa491383b7c28d19a3b5e3e1d7d3a2a26b19a3b4f3c319c4d1f672869382f38184

def LA_45 : List ℕ := dec 217 2842742 559 0 1 0x1aa1a94a18b1a85b3918a73f3d68392b15e06a7b5e7b2b4a4a6b19e7d2d5a551e1731a1ab19a5d2e586d4c4f783c6b4b683e2918b3e1886d1c128182e3b5d4e618492e11b1e1c19f19e2f2a5f284b1a82b1c1c694e194c19931c682a1c1cb684b4c1f3e1991a852d481a4d229

def LB_45 : List ℕ := dec 157 2842819 797 0 1 0x1dc7b18f1d81bb6e292b3c7f2a7c4c1b6b3483f6c18f18a3d1c41f291b2d2e485f6a1d2854c5d4c691f7a3e2f2f586f2a12a1f791b81f1ab2a1ae3186b582d2f391c85d51f05e1df1ea1d1c481bf1

def LA_46 : List ℕ := dec 215 2901667 557 0 1 0x293283a6f3e7d1a03c5829596a2d3a1b51f2f1981969284f1ea693d6c18f1bc18d1c72f4e23c3972f2a2c3e4f1b6b285e291681851f29785f181b0481ed1dc2a287f2861b97c5a2b7e7d18a28f5a28496819491ac5d581d28199585b4818a6d5b385818d4e2c494e6f6e2b2

def LB_46 : List ℕ := dec 163 2902019 794 0 1 0x3a69784f1a18f1e19c4f3e6182f5b1aa2d18b5a7a4d3c4b192e5b6e194a1ad1a7e481fb2b1da18d18e3c4d2c1f2a18b1b829f2de4d4d77d7c1884b5c2ab7a3f1ac5d1818a3d55911ba1bb4583f1a1974c3b

def LA_47 : List ℕ := dec 211 2960786 551 0 1 0x2c2b4a12d421f81fb232a11e3c3f1e2618d4e2b1c6a6b3d1fc28f1fc18f2b1ba7f6c1af1681a33d4a1f6793e482e1ad4c1f1ec1dd7c793c28181d91cc1d18494e1c791987d2e382b2b73c1d696c497e393e1f5f787d75e2518e19951b785943821897c1e5b287c18d58

def LB_47 : List ℕ := dec 153 2961184 792 0 1 0x3c596a1f38585d1d1f7a372c7d1f5c1a491981c91e81b919a61c94c4e695a1e1db19e281db1dc6a1bf3a1c281bf1ae4523f18a189684d171b55c454d5c19b6a4e3d4e1bd1881b35c792c47e69

def LA_48 : List ℕ := dec 206 3020048 581 0 1 0x18a5d1a58183d25c1c6d283b3e3d1e3a53f1c65c4f2e28492f2f386c69182e3e4d1e4e7b6b5c18e794a1d3b18a18d1f1ac6b7c18b2b1c2b1a3a3c1d4b5a3d2b2b4e4786d5283182a791882f191a2a6b5c2b791a81d492c1e41b191a263d381a5a18d5c292c774d

def LB_48 : List ℕ := dec 163 3020247 818 0 1 0x4a5b1da19d1b84b1b2b282f58494a2194e291993e2e5b18e2a5d681892d1dc1bb1bc1892e3b6c3b3d3a18b2e18c18d19a795b181fc5f292f5e6d19c18f19c18b3e18d18e3b22a11b02c6b18a5a6f15a594d

def LA_49 : List ℕ := dec 208 3079149 602 0 1 0x3d3d5849181a5f11ca1a9281c5801b695a2391f6a3d3a4f4f1ea593b5e4f27819b7c5f594a482f4e4b4a2b182b2e2f43a797c193e1b91ae192e1cb2c22c3f2a382185b158381b1891de4d2d4e5f1ac18b2497c7d1c2b7803d42b3c3f48384e1af1da7d494a1d3b49

def LB_49 : List ℕ := dec 163 3078902 834 0 1 0x2a918a4b3291987b118a481a94a186b6c31b928e1895c19b1ce1cb6e1bf5e4e2d19a18d1861b3c18b18e2e1bd1aa181cd4a29381f18e18f3a4c4d5c45491ba1af3b1ba1eb2a1a84f1f1d4c519a4f11f3695

def LA_50 : List ℕ := dec 208 3138200 555 0 1 0x4b2c1991987f481d33c58292d4f185a2b691a5c3d5c1c91dc3e2b919e5a3a2b6f52b6e191a6a1a9385d19e3b702a2f7a4b5f4c2119e1d9783b2f7874d4918a4e6b2b55e2c18f3d1da6948018b7c2923a1d2e3f1894a184c73f6e1e1ad6802e11819d7e02c4b591b8

def LB_50 : List ℕ := dec 155 3138091 765 0 1 0x483b4d4a4d381c81c95b19c3d694c26d28a1ed4c1d818f291b91be2a5a1db1e1be1b9282e4818918483c2d3b43836d7a45d5e31bb1bc29487b483c41b592f519e5d1ba1eb5e2e2e7b4e4297b2bc

def LA_51 : List ℕ := dec 200 3197208 553 0 1 0x1318a45b186c3b7d5e28439198792f782d6d018829392a71b2c423a3c1bf6c1a4c6d2f31c44c18f28384c693b1e81db188387d3b3c2d1e4e6e1c923c6f2e1881897c2e21b91883b181182a592917823e19d1b2a4968580392f582a4b486f4e49182e1b6e

def LB_51 : List ℕ := dec 151 3197012 813 0 1 0x6188184f18e59697c3787f3e79197e4f2c5f7c2b7e2d3b76c19b2a195e1bd6e5a7d1aa7b2e2915d7a781bd4938784d1aa181ed1d86f282394f18e2a191cd18c1b19a2f597c2959681d1b186

def LA_52 : List ℕ := dec 202 3256051 603 0 1 0x1891aa4a1ab1c81a91aa6d4f3e4a3d2b413a1d557c6d1d1ae1bf1a318c1d3f3e1c4b391a02a71a4a4d486f5c284f2b1c184f1e6c3b392e6385f7c694f2e1ac5f1b782c1d7b2c4a7b6e4b1f18c1ad1c4c2a4b6481d41a2b287d5c794a41c5b1a1981b4d5a7d

def LB_52 : List ℕ := dec 150 3256332 857 0 1 0x1fe18b5811b2f2c1f493e4819b18e2b3918818f3e2a65a18d3f5c22b7a7b2a6c4f4f43b48181b3e1d121af2884d3e6a1d18d5c4592a291f381b19e6b4e4b2b1818f3c1c829d1aa18e5b199

def LA_53 : List ℕ := dec 200 3314869 590 0 1 0x29591b287c1a93a6a4f4d18e418d1887d6c3a2d21e2b1c72d1e19193818191a5b4a1ab1ca4e791b3a1e592f1b385849532a511b1f5a2c3a1bb19a1d7b5e4f1983d5e39393c3d6c5d4c396d1c81c95c01fa2ab61b4e24d4e495a57f7c5a7919484d485c4d

def LB_53 : List ℕ := dec 146 3314554 867 0 1 0x28b1fa181ad18818f1be1f6f486c3f481f1d144921ac1cf7c4f2f2881d96a1d791f6e2b1191c733a6e7b4e7d41984b585f2c24859292b3a1de1db4d281f6e391c5b7a287f2a3a581cd

def LA_54 : List ℕ := dec 192 3373692 577 0 1 0x69382018641b3b1e1e24b3e3d2c193802c3818f5a43961f2c2c7f23c3918c1b92f1ce2b1f3f1ac1ab18a74f19c19f681b113928585f1295c2c3d2e53d3f1d83d2a3d19919a1b1791be51d7a1891a5f48222f2d6a7a29d1ec7b1b2964872b4e5c

def LB_54 : List ℕ := dec 146 3373381 823 0 1 0x3d5c2b285a692f3c393e4d3782e319d1a8297d3c7c2891aa11a95c6818d1dc1af6a1a5394a71ad2a81ed1a583e2b75d1ae1f3e1ed18a76d1ba2a0492f1f2a5d19a3b2e7f7183842c5c

def LA_55 : List ℕ := dec 196 3432481 587 0 1 0x5a581c918a482d2d3d2e292e3b6e5b1a591cc42996c4c22a669481a194818d5e06b2d1c818d3a1a783b189686b1e385a5959198495e3f2f49784a3d102f1941e2f7a6f18e1b184d1e291c51e1d2a4f1b4e381a4f2853c18f4a4e6b2e5a494b1e7a29

def LB_55 : List ℕ := dec 144 3432759 848 0 1 0x1ee1df1da31ff5c5c7d19c1993818e1fb5e384c4f6a4b4c18d6c1af6e3a5f1c82f1a92e67a6b428781ad4d1ac1193b1b62d1882a2c6f1e2f15e3f39318c391a1d392e29783b1484d

def LA_56 : List ℕ := dec 206 3490964 623 0 1 0x5e4c4a18d1e0387919c6b186c19f1962c38684b59183a6b5c191b191c81af283a1db1c84e2b1c595a18b181f1f81e95191ca1b696e3f184c1ab276a24c1a91dc1ff7e2b3e2e4b4b52e683b2f5e318a1cf1c3b1886d4c3b1a1b19c1c962d1e18c1ad1e81bb26a5f

def LB_56 : List ℕ := dec 145 3490734 881 0 1 0x5c37e6d1c393e44a19b4f6c6863b6d184a1f1987d1c1891a8383818d2a3f4c1b6d784833b3c47b57a62a1b91e1aa128f1886a293d1aa295913d7818d18a3a1ef286e6919c1a91987d

def LA_57 : List ℕ := dec 198 3549300 640 0 1 0x681e2a1b1b2d4f5c188595e7b1811881dd6818d3c1ae69184e5d182c03c2f393d2e281a87b791aa1eb18a6a1bf3c1886b0595c5c3b2c1c3b5b1b1e7a292c5943484d7e2d1d381d59581b484b1e18f7c6a4f2e7919e29693c1282e7d4d5c2a1f285294d

def LB_57 : List ℕ := dec 140 3550044 889 0 1 0x2a6c2b493f1bc596a5f383d3f3b28e1bf7c24b5c1a6b42f2ae2db18e18d1cc1ed1e8691b1b5a6c1d19f394818c2a1dd3c7a3572f3a61c4b6f1de6b3e02f1c29581f7d5a4293f

def LA_58 : List ℕ := dec 194 3608240 645 0 1 0x2f5c2f396e1c3f3e47d6a1af1ca392a25f76e42d472b19c19d188391839718c5f5b5a5b2e2e2f18e4b294392e181b18e4f1f6a182891ae5968294b1e5854d1ca6f3b2a1b291ce18d239186a6f2f4a2d1c2c4b1e683d1f386919c597c1df018c18f

def LB_58 : List ℕ := dec 143 3608211 893 0 1 0x2f7a7d4c5c18794a1ad1de5924f6c4594c4a3d295c1bf1f87b4f2c494818e692f2e1e21e581b1a91f5e04d4c4a6a1ab3819d28818f1a19385b71c3a18f2881b9583b2e4c1cf4a2d

def LA_59 : List ℕ := dec 190 3666139 623 0 1 0x1b19839281a48791f7e591f12f19e7f3e41f35a119d1ae1b1a33f4b1881a6e19b1c1e4d619686f2e3c4d01a3d781912c3d19b18c2d4918c2b1a1c3c019f6c4e1994a3e294c1bd3685b4e6b6a01e481bb1ac6f18183a3b3e4b193864e5d1f1e

def LB_59 : List ℕ := dec 138 3666576 883 0 1 0x18c1e3f7a5b39686d3918a1b34f1a85d3a5687d21a1bc7f29771c73e6f3c3b1aa2e18f19d684f1aa1f3e2b12a393c18482b91ce7d1a2c1e1c82ab7c491aa5f1b293c6e18b6

def LA_60 : List ℕ := dec 194 3724673 646 0 1 0x7e5f5285387d41bc4f19d1f818d3b491fa18b48694c1b1981b3d6d18e2f33681895e1a1893a2a191bf2cc37f43b581b592c1e2c1f3b1e19281986f7e19d3c6f7e2b1b1c2c5f1b7c2f4f7a1e2b32e47f1aa2bb1bc19c2b3b4b681b1c3d1e3b5c17d

def LB_60 : List ℕ := dec 141 3724694 915 0 1 0x1cc1cb2c781e918a7e1cd1aa1a92a14c5b4e4e287b3a2f5c4d4a5f685d19d38a19d55d4e6f6c2e792a291ae44f393e192d5e18d4a495c3e1932c491cb2883c5f2b2e61291e18f

def LA_61 : List ℕ := dec 185 3783069 642 0 1 0x1a381b5f7c191b5c5d2d31c5c6e5f18b5c14e1cb19e6c1b91ac594d683d21b3d18825f1be18f1e281e55b6818964c2b4e391b2802a6f12e2b4e1e4961c18a1dd3b2e6e1d65e5b2d1b51ee6b4b1f318e7f41a2d2a1e1a2962c1d486b1b

def LB_61 : List ℕ := dec 143 3783314 910 0 1 0x487d1ae19918a4919b1aa4a2d4b2c19287818b19e1891912d2c51cc7f37e1bd785b71919818f6e21ad4e7784d519819b18f1884e5a6d797c1ac1ab596e5f585d7c3b481a5d5c18d

def LA_62 : List ℕ := dec 189 3841668 643 0 1 0x684b7e15921b1a3e2291a395e2c7d3e4f18859394c2c3d3e1e591c45a1cf19c6d18e651ad1aa591a818f181e754c595a6935b3c1e1a3d4b4c1ea1d91fc6b1ad4a482b2b62b3c5a11a93a1884d2d19a6d1f1ae1d919c4976c7d71ba1fd1c3a

def LB_62 : List ℕ := dec 141 3841215 902 0 1 0x31e87b51a5b1d83f1894c1ca1bd2f786b2e683b60481af4c4c65d18e5f2c4f4828392e1f1cd4e5e693d2aa1f2c1d96a192b1f2c1bc2bb2be1bb18a591a195c73f491ce2ab2a5c

def LA_63 : List ℕ := dec 181 3899607 666 0 1 0x4873c2e1bd7a28191e6b16e04f1a66e2f691b31a4a5e5d4284f1b5a31b4a3d2c6d1e452e283d1b4d18c1a1d3c1f3f5c1cd1ac1b21c3a5f3c193a1bd5c1e63a6b2819d5c7c2d1882f1c94c5a3797a1cb19a1880793e2f4b7a2c1bb

def LB_63 : List ℕ := dec 131 3899761 937 0 1 0x19e4b5e396193b1882b1b3d1fa1ef2b71ba01b5596c2b3e2b5d5e1b91cc75b591ce2f1c1b3697a6704181c918a5c5f191af1ec7e3f1af6a1869119c64b585b6e1dd

def LA_64 : List ℕ := dec 185 3957973 659 0 1 0x587b0287c1af1cc1f97c1522e396e7d4b5a01a5b1987f6c519d1bc339018281e1e1bb383182e1e4b1c5a1c91c82c4f1f19597c4a18d282c1e3b385b2b6a1f587d2c1e3a495a194b1d2d1aa1df1da2d1d17a7b1b2e3f5c1a487b1881a9

def LB_64 : List ℕ := dec 144 3957809 938 0 1 0x1e7b18c391c18d18c24d3a4818d484f1e187e1ab1e18a6f21c87f796284e2f1b292981e91e7f1a82d381b73a19f581c2f28281918a1ab2d18e1cd1ea1b918a3c1a93a66a5d1bc299

def LA_65 : List ℕ := dec 173 4016108 647 0 1 0x2a18a1dd1ae3a5d7b3c6a314f04838281b94919a4b68296e6f283e6d0295a2d04e3a6b3a2d2f583e695d6c481f6b1a7859281a3729294a6e6b483b3b1b2a5f1ee3d74f2f7a1c63d2e1d483f2d37a3b5b3c302e4d6e2f1

def LB_65 : List ℕ := dec 129 4016265 908 0 1 0x4c1b519c1ed5c2e291d291ee1f91f28582d7a1519d1a6a6f1ee19d581bb1ee795b2c1b81b94c6d1be6d73d1884c4f59533a5c6f02e5c5f45c6f62a2d34281b12e

def LA_66 : List ℕ := dec 183 4074480 667 0 1 0x18d6e2f1fa18d21a96818c5d1a393869582a61f2d2e2f17872a2f795a71e22c7b1ca18b791e1c84b49582b1b91d82b2e7d19a7d295802c392a3e75b4b4c2c2b4c5f2c6a7d386b783a5d7b5c18818933822e4d3e491883d5a1e1f18f

def LB_66 : List ℕ := dec 130 4074960 931 0 1 0x7a4c759491a8293a1ab7e3e6d2c394a3c187d1e35c33b41891ae2b5281e91f81a1bf1986b2c23e585918d6c31c195818d45c1c1db1981a1d1f5e3f01bc7918c1bd

def LA_67 : List ℕ := dec 184 4132716 655 0 1 0x1a22f1a5a18d06a4f181ba4f1d18d31ba49191d1831ba4d6f1c583931f2a6f1da1a93e482b4f1a18e19b4c12c1c486d4d01b3e4a1969583b1ee4b2928f1de4b2c4594c3c481dd1e4b28c596b3c2f293c1985b291e1801d19b1bc1e2f

def LB_67 : List ℕ := dec 141 4132346 959 0 1 0x2c5d3e386b1e218e3e29d181ac1995c3d1de1bb55c491818f7c6e77d3188192b328c2dd584b1881c5b1f2be1892af1fa6b293c1b81db49481aa1d96a596a3818f19c4b1d2a179

def LA_68 : List ℕ := dec 183 4190616 662 0 1 0x2f23d196282d4e3c2d6d4f19e391d19e6f3e3f1c639385e1c93a18c69019a794e6d19c1b92a56c2f791981ad1ec1ab4e3b381e84b1ef5a15e67b25a794a581a93c5b5e58792a2a3b5b1fa18f1a1c18b3c71e2d18a1d291f2a7e5b1b

def LB_68 : List ℕ := dec 134 4190971 937 0 1 0x3d1e1b91881c3e4919d4c3c2a2a596a1ab487e1d91dc5d18c5f57a1b94a2e4b397a793c681aa1ff618e1d18d3c1b7e1ab1b3a3e2d1b6d38828d7391b31ba3d21d19e7f

def LA_69 : List ℕ := dec 186 4248408 649 0 1 0x1af1a8593a4f582f3d5c581991a6e6b2e1c3d2819c3f18d2e7a6f31a23e5d4b3a6c692a01f4a3d1e64f18a7d7e6d1b7c7d3b6a6a4b1bc1ed1882f1df2c81cf581837c19f3a4867b18c1fd19e18f18c281c1f3f1ba19974834b4a1c5f78

def LB_69 : List ℕ := dec 126 4248286 927 0 1 0x18b2b7c3d64918e6f3a1b20583a6b2c22d3b6e7f21ae1ed18e02d2c3f2c1a1f3181891ce2e1f41996e19f1aa2f19e1bb1a82f6f2e1991cc111d04e7b2a402e

def LA_70 : List ℕ := dec 174 4306379 650 0 1 0x6c5a4d6d1b81ad6863f17c7018f1b8291f4c19d2a2a391da1ab56a18f1b1aa24e18923c6b4e292918a1eb7e6c7f283921e293c2a493a1c5916c49381e594f5a13963a1d19a5d1d1b3f31886f5a3b6c59319a791a2c3c1d

def LB_70 : List ℕ := dec 128 4306691 920 0 1 0x2918c6f5e1893e2819381d2a18181c9684e1975828b1fc7e59792c1e3d681eb1da69439684d4e1b113c1d5c18f292a2d581b1a81ad291f6a5263b1be19f1a819

def LA_71 : List ℕ := dec 181 4364029 699 0 1 0x6e1b2d5e19b2c5e19b191ba492c71d0193a2b382d25a1eb19a31872b6a4a19d583d3d581c2291ae6b2b1b18786f1c4b18828b19e1c4c4c19b51c4818f19c1cb18a3e5b382d16e196f7e18391ad3e2a1881b193b1c1d5c1a291d7b

def LB_71 : List ℕ := dec 123 4364533 960 0 1 0x5c6929385931b85f61934c3f64e1df5a78796e2c5b35f7e2a19c1af281f7818d1c7f181fe3f3f25292f19a691c1b783f01982cb7c61ca1af38391c85b69

def LA_72 : List ℕ := dec 169 4422178 693 0 1 0x1f283a6e3d491885d3f21f1aa4d1ab7a387585b24c06f67e07d38191e42f192a396a32d182e1b1a59211a2d5d1da3819d3e3d282b5a4f291cc1cf1e4a5a18f2b1ea6f1d296c3d1c4d0184e5c1990685b1884b4b1b

def LB_72 : List ℕ := dec 131 4421893 959 0 1 0x1d1c1fc4b5f5e18d191b81c934a19a19b6c281a97a1c6f4a1913d1c5c2922f18c1bf585b4f1f805b3691ce1d91f81bb148792ac1bd183e4b71419c18b2c3c718b4e

def LA_73 : List ℕ := dec 172 4479895 691 0 1 0x781f3a2f74c693e15e2959718a2f4b78592d2d6a5c18f18a19f1ac187d3182a29481a918823f2e0374e395c1f2d1bd18e4e1f6b4e5a3d28292f3e3833f7d1aa2a18f7c1b63e1d391f281b81a91e691c7a3b18e1af1b2

def LB_73 : List ℕ := dec 128 4480501 981 0 1 0x3d1984d2d7c7b6e193b3c496c5f6918a318c1ab19c19f3c1d2a19f1aa3f4e3f11986d1e7d185e7f5c4e1f4b581801cf1fc1b97c2a2c4f181c41c1af19c3c3d7b

def LA_74 : List ℕ := dec 172 4537277 710 0 1 0x5e1a919a5b7b18c29393a1e7d1d8694e2b3f7a1c2d5f42a392c6e297f19a3b02835b3a7681bd619e196f31a5a125f119a7924e1f184f1aa1af1d382e45f2e482a1f3f482d4c192d5b2c581d4a7b1dc1bb7c18f1ba1df

def LB_74 : List ℕ := dec 129 4537472 972 0 1 0x18a5d6c18d3e4d1e391ba185b1b1bc5f7b3a4b1cc596b1be2f41996e1c1bf1bc1d7918781869425c1f2f7e1993d5a1a6d1de49493c0381cf581984f1a2c494c4d

def LA_75 : List ℕ := dec 173 4594913 686 0 1 0x45951b696c2919c17b2872c7a1fd19812b2e31f1d2d6a791982d181b3c5f1ec7d5d19c7f2b6a2d313f1be7f31ac1db3a1b718486f5c5a2a6f2b1891fc2a19d5c591e181ae1ef7a581ab1b3a21a19b1a869781b7487f5c

def LB_75 : List ℕ := dec 129 4595730 991 0 1 0x19a1b18d6d4a1f81bb4c391ba2a91bc492a56d6c4f2c7e2b6d1b81d57f6e3f18662d6a7b4b4e6c1cb1da1d11bd1f85d3818b1a82a4f6c1eb7a1918f7a3a4c1897

def LA_76 : List ℕ := dec 177 4653021 674 0 1 0x41a18e1df19c0192f1c61a2816d3a3e5a1a92944a16d5819c1db35e691fc1ad2e394a5d282b6819b1c5c5a18f1ba3f281894e1e5b185911de7b296e18318819f3f2f4e11e581bf6a7d1ca18d5c1c4d1e4d1fa18b1918d5e78

def LB_76 : List ℕ := dec 120 4653450 991 0 1 0x1d87f5a2d1a3f1885d2d6a482f6f4487f1c818b1f1a7e21f77d585b51de5b6a3f72e7b1f2d1cc5b2c1b82b7d5f384c16b1f5c483a1dd4c28c1eb5d3e

def LA_77 : List ℕ := dec 170 4710770 712 0 1 0x692a5819f6e487b2a19d1bc53a1a91a1aa1cb3819818f4e2e1d285975384b1e4d1d819f585d7e5d1c18e59212f1891aa4c5f43c5f3e3b2e6b5a35b2e2a18c1bd5f1a864f4a1b3e701c03d3f728c1ef3c2a13c18f2a

def LB_77 : List ℕ := dec 127 4710494 1016 0 1 0x77978192c1b96e5e1b91a81b91ae18b1c84f3e795d3e28495e4919a19b5c481a19b2f1a82911a6b3e49738358491cb2a818d4e53e2d681ff3c1981182f18b28

def LA_78 : List ℕ := dec 173 4768313 683 0 1 0x18b19a1a911ca76e7b1f37b7c231391cc4f4922c5d1f1e81b96a18a2d928a19b2e55e5d3c31c5f381d1a187818d4c781eb6c5e3d6d18e281dd181c8592f5d7e1e29493c7b19a5194e7f582a189483a2a7f191ac18b188

def LB_78 : List ℕ := dec 134 4768060 973 0 1 0x596a1d92ca2e6b3919919e55f1dc2b6b2e393a4d1fc28f1ca1af1e1986f4e4f61c2b4e1c23b1de2a919c2d1bb1ea31df1e819b63d4e6a3b4919a1a97e1a1b919a4f18c

def LA_79 : List ℕ := dec 169 4825392 702 0 1 0x39198595b5c3d4a7e791d1972f19c41b5f6c1ac7f491b1d383a794c4c392d5d1a806f781d3d22e2a1b4e1891c1aa1cd07783e1893c1c182f3a4f4e4f44813c18f19c2d1eb1cc3d2b1e81ef5c3b783b2181f59383e

def LB_79 : List ℕ := dec 122 4825873 1005 0 1 0x18e7b3c492881bb3f2b7e2a2b1d2ac2894394a5f19e5f292c3e3d387b1ae4f3c7d1cc2891883b682c2c6f1b4c433b1c684b18d5e2d1884d3b6a259494e

def LA_80 : List ℕ := dec 166 4883383 716 0 1 0x2f2f6a2496f1aa1bb1ea496b3c41939482a696e24f3e3d1cc1eb6e67d1a83b138491993a18c1cb19c2a3918818b2a4f1bc5d18b3a5e397e1ad6e2d03a00282b2d36b28c1897a3b2859292a4f7a1d7b59198024

def LB_80 : List ℕ := dec 127 4882871 1029 0 1 0x794e1918b3e5a518b5c1b2f1e5c3941f1fc2bb1ba7d7866919d1ac19f1aa184e7f185818b2c2b1aa18b5e1a2b1e1b74b1ac21d2c1bf782f61cd1aa19b1fe1a9

def LA_81 : List ℕ := dec 173 4940196 693 0 1 0x3e6b19c1d1f731977c4b2f5e77d1de19d3a4f1d1da4f11c7d2c3c595a2c493a687f4d5d681bc1bf583e1d94c4e391a3d1fe1bd4b75c1b1b8491cf6e785b61c4c6d284f11ca4f1ad19c18f1ce1d4c3b1bd1bc4d1d4b1be

def LB_81 : List ℕ := dec 129 4940115 977 0 1 0x1891aa1b49163e1891ea29f1d83d3d41cc5f591e2b58181a001c9585c2a1bd5e4f3e4a4e1cb56e1982895e18a7d19a18b1a6f2ae2af7e3918c4818d4c1bf1f28e

def LA_82 : List ℕ := dec 170 4998221 728 0 1 0x7918a3e18d78131c2a7b3938718c0394f7a18f1e5e44f2a2a1e7919801bf4b2a85d1e185d6a18f5d1ea797e7d4e7f181a82f593e1e5d1ae2b1ab18c697a4b47a5b2a5b7e19f1c8394d185e29d1c83e1b9583c781ab

def LB_82 : List ℕ := dec 124 4997850 1006 0 1 0x7b2c3806e5d284f4f6a582b26f4c2183c491f1d82eb1dc1d6a5f2c1cd1ae192922d1ac19f1886d1ca6f2f7b29a18f18c7d1d2a7e2b6d1e1891a8693c4e1b

def LA_83 : List ℕ := dec 169 5055089 725 0 1 0x6c1a91cc6b3a18195b1881e4b22a1a3b18f29e18f1d5a4f5c1b2d5c4b1e5c19b1c1ac1893b6e5d296a44b584f63d419c6b3c1b3b1e1b8197f4e4b15c1ad6a2a7d4c687f3f19c1fd2dc1f9687319a579387f2c6e4d

def LB_83 : List ℕ := dec 126 5055885 1012 0 1 0x18f6e691ba4f491883b1e54d19e1996c5391e1c1c387b1885b2c5d1d19c3b3b4a1c929c19b281d1ac2c19d182e6f5c18d6a1a293d1886f1d5a1cc1a95d4a1c

def LA_84 : List ℕ := dec 164 5112987 751 0 1 0x1fd19e197587b1e18a1c1af7c6f19a7d1891ae5b119c19b1e3a2d6101e281c6b1c2a684f3a18b2d5c5f1ba3b1d1a87d7e4d1902852b191896a31c81d94a1873e6929581f1d7d7a62e7829b7a1cc2f4f1c18f

def LB_84 : List ℕ := dec 119 5113190 1023 0 1 0x1fb18e4d1c5a5a1d91a82b1bf1ae491b25a4f1f6e1d485f21d81c94e1ad48383e2e181d2c5b7c695d3f7e4c4d4e4d6d6e01cd5c3e1d82dd2b856f1e

def LA_85 : List ℕ := dec 168 5169697 701 0 1 0x2b6e3d2c1d188189182f1aa49795a191c4c4d3e6e1bd3a691ac3919b7a42c1f6a4f2c31f281f581d92882f3f4b45839218e19f328196839291981db7e6f1884d1a85f57d1cc6d4d188294f1c281f3e18791d6c7c

def LB_85 : List ℕ := dec 121 5169759 998 0 1 0x3c3d18e3b318d2887d1f2804a6e1894d18e791f4e1a58059282e26f1cc7f5f3a381d4818d3c3a12c5d5b6e1a8691bb1ea1ad5e4f3b6a5a7918d19a1a8

def LA_86 : List ℕ := dec 161 5227389 750 0 1 0x1b3a6d19a1284d5c2f1b4831a18f7c32a33e1bf1d2f1aa371d1ae792b23a1d0293d1ea19b2595e1ac1bf7c7b04e2b19e2bb1f82c5f5f2c42a1bd28a185f7b1ba2b1f18591b19e1c918e1e16f1aa1a693d

def LB_86 : List ℕ := dec 122 5227600 1061 0 1 0x5a18f4c4e718781ad7a6d3a218c591af3b1aa1d01dc28b5e13b3d28e1cf2d6a7a4d7d1a875f1ae5d491e5f291e84f3f1985d5938593c1bc1ef1cc1a1bf

def LA_87 : List ℕ := dec 168 5284048 750 0 1 0x76d19a11f7f3c7c4d28319d28a1b93f18e1e1cb29a7f28318b1d5c19e4f12b3853585e1ed5e29282281e91ce5d3f18a5919e7d15f1ca2928281c919a1a1ad781e2b2a4c1b7b581a18b5e1885918f5a6f7c2b4a4d

def LB_87 : List ℕ := dec 110 5284836 1061 0 1 0x63c4d1891be1e1ab1e2c1f486f1cc5f4e1ed029c18f282319a6f51c291c19b41d6c6c6b397e3a1cb1be6f295e31a1c74f38687d4b54e39

def LA_88 : List ℕ := dec 162 5341632 729 0 1 0x4c791ca2d7b1aa19b7e219d1e3a6b1da6b46d1ac1b18b1ec79481b4c5f282f3c19958795e1bc1ed6e7d46a397a18b1e64818b77c2a6b4e19d3c1ee4b1994382a1e7f68349501a84f6f3c6c2f3e39392c28

def LB_88 : List ℕ := dec 119 5341226 1043 0 1 0x3c6a2d2294c6f192b2b82a91c1a81c9298592c381bf7a7d3d6c1ae28f2e331b81bf3e18696a485b6b28a491996e1e3b1833f18a3d2f61b819d4c197

def LA_89 : List ℕ := dec 167 5398741 758 0 1 0x18b4c6a1cb19e19b188292b1c38797c1a189418c5a1dd297c18b7831cb1fa2f42e1d2e4914f1a1e2a4a3b49191b85e1ff2a2c5f1ae5a1ab2a496c2d6b1a8618b7c4d5e596d1aa4f3f328c1d918e5f1e692b7c3d

def LB_89 : List ℕ := dec 119 5398898 1073 0 1 0x4824d4a74a691f31ea2ab1ee2e1db2818d1e81ef1ce1e6b1dc1bd6b7c2d7821eb29a118f3a2a484f2e3b4919e693c6a1cd283818d18e63a2d18f186

def LA_90 : List ℕ := dec 163 5455450 727 0 1 0x6c394d2d82bf1ca3b4d2a4b1ae2b7199582e4d3c124a6d7c3b61f51ba1df5a1d3b51ae28b1aa491c1c12a5d1f18481e2b1aa1e93a1ce7d6b783a6f1c18797c27819f3a381db1ba2d792881b94e71e6b19e

def LB_90 : List ℕ := dec 119 5455902 1065 0 1 0x6a297c4d1ae1db1c018a5d3f5581781c91be6f1f1fa1eb282b1c593c294829194f4c18e2f5d5c681ad5c2e4b193b28819d1e1bb1c818918c291182f

def LA_91 : List ℕ := dec 156 5513365 775 0 1 0x1887f484f1d34a483d163c5b487b6a5929e4f1d7d18f1ac6c18d19382c63c18d48584b291a97e3e1813b691ba3f6b1ba1bf1a81f61c1a3d78592b04a292811d3e5d19c1dd18e7b1e68594b4c3e7b

def LB_91 : List ℕ := dec 112 5513324 1094 0 1 0x1884f59491ce3d32818199583e1ae4f2896a4a4b1e4c1e6b7e6d5f281886919383d4719a79483c1d7a1ff1a82b1e745191891ba6b2b6a189

def LA_92 : List ℕ := dec 159 5569846 762 0 1 0x18d7e6f3a1a84b01f1d1e5c51f1d1c21191b91aa6c2a6a1dd1a1d7a1a1cb4c44e7926a4918d1d86f597e4a59188393d1b1fa29b182c294c3d286e1f5b2b4a5b7c3f18b1ac3d58394978618c1f91ba7d

def LB_92 : List ℕ := dec 114 5569770 1076 0 1 0x19919e18f7e5c7d3c74c64b1d5a1dd1ca6c4a6b18b19c792c5c1bf584c1c948348218e18b45e1ab63e792ac6b7f64193d48481895e18c3934d

def LA_93 : List ℕ := dec 161 5626705 761 0 1 0x6a7d1b1d1ba5e1a92d3a4f1d86d1b496c2d386381bd7a1f3a1d39182e2d1be1eb782a3a1ad7a1af2881bb1bc57f1c2f1ae28b15d2ca391b285b5d7a723e292f397a1b19e1e971ca7f1f19a19f61c595e6

def LB_93 : List ℕ := dec 120 5627671 1077 0 1 0x6c6f1d7e2e5b291a18c18952c5e2e1ef6a6e1ed18e218e6f2c1c496d2ae1bb6c593919a2d93e1ce1c1c28d1c818d1b82d6b1a81818b284a3d0492f7a

def LA_94 : List ℕ := dec 159 5683843 776 0 1 0x11d85f2e283e183b1e1cd19c47a4f3e6d4645f1c1b87b1aa1894c18d1a1ac594d7c5919f2a819d1ac19f4f18e1df19c5d38684584930487b65a6f295e2d386c281dd6e1d1c3384b4d7c19f1ac4f2a4b

def LB_94 : List ℕ := dec 119 5684788 1098 0 1 0x2ae1d1c4c1e3d19d7e1ae494902f7b2aa6f18c2b1dd29c495974b19c1a18d4c1ab05c6e5c4f1c1f3b19a2a95e4c1ca7f1d3b3e782891ce1cd1ba19f

def LA_95 : List ℕ := dec 159 5741078 816 0 1 0x19c1994e31a81b97a1ad1a5a3b1d1a7e1bd1882a2b6e1cd4a18e1991c03f6c4d383f5a4b4b382e1a1d16918a2e1967d583a493a1af18a01a5419b1b85d58051d7e18d1e1ae7f1a91ee4b2d5e3b1a1f9

def LB_95 : List ℕ := dec 103 5740894 1168 0 1 0x7d427c3f3952f581b3f7a41d2287191f1384b2c18919837b2e783b484f38186f4c1d1a1497a1f2f1ca1cd1be4f5b18a33d182f9

def LA_96 : List ℕ := dec 149 5797822 786 0 1 0x193f4e3c51d9285818e1d1896b1ae1e3f49378691bc1ad3811a3a7d61b7a387946b19e36d5c3a2a79292e23c492b295c707e1ad15c449292e2a2e6d78192a6c1892c1cd1bc051af2be1ed

def LB_96 : List ℕ := dec 114 5798347 1060 0 1 0x5e5f3a3f1d2e1be1e92b18e3d4b3c581bd1be3d51f3a382d1ed28a3b3a4e18f2a122f2d1a6e37f6a1d7b19e1a5f781b1ac6f1bd1a83c1bf1da

def LA_97 : List ℕ := dec 155 5854932 759 0 1 0x4f4b5a2d3838301d1c1c91e86b01ae1ff19e4d2919e7d3a4691be19968294b53843d2c2a19b1de419b3804d6a1c4a59022d1d5a293f19e6b2a2d5b18c19b18a4e1d92ca18b3f19419a1a9281848

def LB_97 : List ℕ := dec 117 5855132 1092 0 1 0x2cb418c5b1ac2b51db1ca291a593c4f1a818b5c4e1bb1887b4c4d1f18a18d1f81ab35b7c18e3b6b2a3b3e664f1a0691d81ad28c19d4b1c81bd582

def LA_98 : List ℕ := dec 155 5911713 759 0 1 0x1a94d4e6e69595e3b2b1829a1cd2e796a5a3f1ad1bc387f4918c2a18b2d6a5f1be18f74e18b1fc18f53b1a1882c7d7c3d2f3c5d5e1a5e2995a1a0328495c3a5d6e5f23819594a318b19c4192e1c

def LB_98 : List ℕ := dec 116 5912318 1044 0 1 0x1cf486e1a97c1cf1be5c18b41c81bd1d19c7d02c18b3e4e2f2d291ae595f4c1dc18f181f4d18c481ad2d1e381f3c3e5291b1f2d18c1bd18c01d8

def LA_99 : List ℕ := dec 149 5968491 740 0 1 0x2c6f3386a165d1c7e1af7c3381c1cd483485d5e2d3e4b2813382d1bf2da7b1d2b291cc6b5a492f2f1a12b4d1a85a5b3d1aa1ff1983a4495f6e5d18c1894841a37e1cb6c1c18f5c5a2918e

def LB_99 : List ℕ := dec 111 5968439 1071 0 1 0x4f5c47a19b1da1cd2e1ae6b18b35e487b4a02918304a5b1e7783c29f7818911c856c29f2a1fe4f18d2f1ce1b91e6c5c1fb2881fd1ca3c2a

def LA_100 : List ℕ := dec 149 6025761 789 0 1 0x2b5c396a2b5d4e6d786919c1ab6861b4c2e1af7e6f1b81af06a5e793b18a5f1b2e5e18f4d19c1a7921c5a392a04e19d1ba1cb3a1d1182e73f2e05a192b6f1ca3b12f5483f18a18d4c385d

def LB_100 : List ℕ := dec 112 6025009 1117 0 1 0x485d1884b193b5a1976383a5f1b1aa1cb6e7a1cf7c54b4e18d1ba1ad383c3e1bf2886f6a1b95919e5593e15e49295e719f1982e6d1883d3b

def LA_101 : List ℕ := dec 159 6082307 793 0 1 0x4a7e4e1ef4863a4b1f6d1ba1ae2ab1de1bb6a2c6f19a1af391dc5b3c4f3d618c1af18c7d7c39483f4919a49182e5d1bc6d4d6f4e7c15a719b3f1a8594e19494c5a5f2d6b1aa587d018c19f2c1a78199

def LB_101 : List ℕ := dec 108 6082761 1121 0 1 0x2ac1a9338494d1c1da7f2f6e5d45b1f85d593f18851b91ba1b19118485d1be19f6f228a3d61f95a7c1e5b786d19d1ea1c7f6c497c18d

def LA_102 : List ℕ := dec 152 6139052 815 0 1 0x2e1af1ba2f51b51c3b3d19e6f72c3c1d1f1f4c2f33d7e1993a1a5a5d5c1d51a2e2a1bf783e4919d1ea1cf1ae396e1cb5a397e4d2a3c1e9188292a3a1b91b801f618b1ca2b284a1d9618a6b2b

def LB_102 : List ℕ := dec 115 6138482 1146 0 1 0x3b286b1bc1ad0691c81a92a3a182b4d787b1b181886f1ac3d1b19a1eb1bc797f687c397b4c484f1aa29f7815b1c87b687f1b81841ef1fa1ed2a

def LA_103 : List ℕ := dec 140 6195388 777 0 1 0x2e2a63c4d291a282d3c1f7a1f189194a394381979681d819b0611b2f682d184d4e793a591ae1f7f3a68394f68705d18a493a5f581cf1bc7a3f2d6e692c18b5c6a418d716a13c

def LB_103 : List ℕ := dec 109 6195709 1091 0 1 0x781a3a7b3e5b6e3a2a1cd2c797a2c491a85f2c294918c018d284d218a7d6e3b1f182c697a25d18f2da7d191e18c28b1cc1c1e93c5a18e

def LA_104 : List ℕ := dec 149 6252102 813 0 1 0x1cf1aa7c1ad4a1e181f2b5c2d5d1cc18b57e393b2a5e1bf4a1f3c7a7b51883828f1c19c3f6a1f1ab1ca791c21a42c7d24f18a291a5872832f381d391891da75d1d1b819d1619c3189282f

def LB_104 : List ℕ := dec 118 6252198 1150 0 1 0x1a1ba1bb6a58593e18d18e1a77d18e3e2c918c28c1c93a4e19d411e829f1ba6f5c1a928e1fd56e19f28a2a1b1f795818b1ac3d493e3f18a1818919

def LA_105 : List ℕ := dec 149 6309098 803 0 1 0x1a77e5d5f1a81894842e1894b6e18c6d15b6a5f1c87f2d18a2b3861893b686a293d1992a81993d13e684a1eb19c5c19d1c183b5b491dc3f5c14e3b1e1e1a94c4f287c56f528a1cd431e3d

def LB_105 : List ℕ := dec 121 6308977 1172 0 1 0x1991fe1e918a189188797f2882d2d4b291e81cb1983a2d1ad5e1a6a18d581bd3c1ca481d91de1af0594f1b87784a2f1c1895f19e5c1d929c1fb7e11fb

def LA_106 : List ℕ := dec 152 6365918 809 0 1 0x1e3e2a4c6d1c1e1bf5e1b819b6829591aa18d1a78682b1ed78587d1a4f4a2f1d819b4e5d22828396a49581bb19e182d19a199291193e5c1c1b6b2e5b2f5c01996c18a5c5b26f2b1c81dd6a19

def LB_106 : List ℕ := dec 111 6365543 1121 0 1 0x483837e18f1bf2dc6b6d7e4a1d92ae22d91ea51ad48383c19794c119a1ab3c2e3a485d189018819c6918b321d19f2c86e5b7d4c1b93c188

def LA_107 : List ℕ := dec 144 6422410 841 0 1 0x282c3874f4a1eb4c7a19f1a86b4188285905d5c5c2b373396a01db1e82a693b49281be1994a2b5e6d2b3c6a62d6f31a8292f1e3919c1e92ac6f4d1c0118b7c2e1ed28a384d2871bd

def LB_107 : List ℕ := dec 111 6422614 1178 0 1 0x1ce4b395b2601f6c4c2d1ad1ea6d1aa18f391be1fb198387918d29e1bb4a1844f587e1b927e3d2d18818928a1bd52d396c28f3ea1bb61cf

def LA_108 : List ℕ := dec 148 6479075 819 0 1 0x19b7a2e5c6f61e19b5e646d1aa04f5c2d2d2c1ae28b4c2d2c719e1891981cf1ac1b971a81b18a1bf4196c1896c1e5f2e1a2c18c2cb1a871d3a18b3e296a584b5b5a3e19d183a4b58623f

def LB_108 : List ℕ := dec 108 6478730 1167 0 1 0x7f1ba1e697b1be6b2b1bc3b3e6d181bc29b618a381d39481e91da2a45f281bf2ec28b5e486a1cf618691e5e3c5d2c4c1ab1e718861a9

def LA_109 : List ℕ := dec 153 6535018 811 0 1 0x1979397a18818b1a18b7a4d1cc18f4d18c191a87d19b2b6c1c6591c818f586d283e4c1cd19a392d682b0491aa393f2e2a4d7a1eb791fa473a381f691bc1ab2a7e1d1d6f5a181d1ad19c3d2f6e

def LB_109 : List ℕ := dec 106 6534902 1152 0 1 0x19b2f5e3e4939118e1dd1ae18e1bd6f385c4d781b3d291b83919f7e3b5a6d1c81895e391e3bf3880582941c07a7b2f6481bb384978

def LA_110 : List ℕ := dec 148 6591255 797 0 1 0x3f6a7d1a6a5c6f393c487b18a3d134b1b581e2b65f1ac1af3e7a29d2fc1c95b3e3d1981f3a3b5848794e1af5a18381cf1cc2a2f5b1e3e5d491bc1e1b7b7c1b95e2e6d1ac5e1d937c1b2e

def LB_110 : List ℕ := dec 113 6591377 1125 0 1 0x1a182f1ec19973a12c3f1818f18c6b18e1ab7a3691ae1ad7383a1ae18f5c3e299686818f1fc1af1928692e19a3901ad19a5f2aa1cb282918a

def LA_111 : List ℕ := dec 151 6647931 822 0 1 0x6b1de5b3d2f18a1f3c1fb1be797849282c19f1ae59481b2a4e1fd19831f2c03f286f1ec1c91cc19d2f18c3c39192b482a51b5492f2aa1cf6f1e1ee1dd531da2d19d2b18e1e57a1d92a1f4c7

def LB_111 : List ℕ := dec 102 6648315 1180 0 1 0x2a81db3f1ca5d6b06e1b4f3e1d1a5c218f2a3847b2782b1a791ee3b291b5822d791ea1bd19b29e1bf281da1ff7c192a32b4c7d

def LA_112 : List ℕ := dec 147 6704641 817 0 1 0x1df1ac19f2e491da1bd3a1e8691c18b791bc1d6c7b4e7b6e2991ca6a5d7c31cb782d2e51a181e4f3a791c5e7a6f2b3d1b1e494a1f81b94852e595b7a5c1b1df578538194a5e1bd3b18a

def LB_112 : List ℕ := dec 117 6704097 1183 0 1 0x6f595a5d58782c4c2cd6c6c4d19e1af19f1ba2e5e6d2d1f684d1be1bb4a19919c18c18f1c948292aa1b91da7b295d1aa391f91dc395858491992c

def LA_113 : List ℕ := dec 146 6760882 798 0 1 0x118b1ce2f19f28a1ad28596a3b4c6819b4e495d1e1dc1cb1ca1c91ca691a1c4d318e3d1f1a692c1c5218c3f1d2d2a3d01ac18d29618e293b29233d291de1d91d8593f1a06e55d2b1ba

def LB_113 : List ℕ := dec 105 6761403 1149 0 1 0x1e1af28a1ab585d44a18756b2c4e7a6d2e4b5e7f1c83f4f51c5929a794d2a3918a18d491fe6f2d1a1ab2e481ba18d49584a19919a

def LA_114 : List ℕ := dec 144 6817111 827 0 1 0x7c3c1ab1f68385394f51ee1cf1d1aa23921881ad6c4b3f2f58187d18e6c2d7d5e396b2c2f681c2b3b18e18838b1a83c1f4e1a938581f5e5948593e1b4f1aa1f2b583f1b391c56a2b

def LB_114 : List ℕ := dec 106 6817535 1173 0 1 0x1ce1cd1c6e1b6d1f1b81c91c831d6a7f5c2bf1e84b01b86d781db182b282c281aa39f29a1b3b391ac4f1887d35e3b7a793e5b1d5e7

def LA_115 : List ℕ := dec 148 6873756 846 0 1 0x5b692f18b1dc3c334a1cb3a6f18e2f1aa6d48119918d3982d1d91885e1bd5e3f394e1918a19f32c43d1e2f17818d1bc6d1b81fb1a8791c18391fa294f58189787f1ea2bb5e4c3f30283b

def LB_115 : List ℕ := dec 106 6874085 1191 0 1 0x18b6f5f2d818918e1db18d1fc1c3b2c3f1df48a29f18819d18c28f1ea2819d2e01395919a2c1b2b484d1182884b41997a6f061b629

def LA_116 : List ℕ := dec 129 6929741 796 0 1 0x495d3c77f7a4c1b5a1897a04b683b2b1c381b3f1e2a1e1e939e28b61d73b3c4e18173e7901a296a4f6d19a4b1a2e495e2f51e3293c4c2f2a7d6c693f386801e6e

def LB_116 : List ℕ := dec 105 6929631 1146 0 1 0x18c199292a7f2ca19f584851893c33c5b1c2d1f82893e6f1e7a3f1a8491a918e392d29382c3f3a62b3f1c81d5c1fb7a6f2a6c2a4e

def LA_117 : List ℕ := dec 155 6985882 818 0 1 0x4e291d1f2a1f82ad397818e1df1ca1ab7a3c3e19f3f2a4e791e3a1d481aa2ad1b81cd3c5e292484f2f1ce1cf7e5d292a1b87f2c6818f2b18c3b7e5f5f1c51c18b1cc6d2d5a18e2e92bc18b1a188

def LB_117 : List ℕ := dec 98 6986517 1198 0 1 0x291f11ba4b1dd1dc54d6e4a4b1b919a5b43c19c19d1b6d18c42d1e781b94e597a2c44694a48197d691ca6d3f385e6f5c1f

def LA_118 : List ℕ := dec 138 7042445 855 0 1 0x1f79181c81c95e497a4e1df28380582e05d532f2c5819d1de1cb5c3a15f392838293283f28195852b7c2f13f1ae691f2c1ed19c7a292b182d38199683a1c4b6c1bf19c691e

def LB_118 : List ℕ := dec 99 7042627 1192 0 1 0x3a2322c4e1fb1ba182818e2bf1be593c4f2a27e19918f1ee1cb2c38503e15c3d4a1a6d1ef1b81aa7f2a2b4b19e4f1c2d348

def LA_119 : List ℕ := dec 134 7099209 835 0 1 0x2f2f441f5c59282d7e21a7b24e4c2d38418f2818f1de1a393928393f29c1fd28262d1ca1bf4819f1e86f05a43f5a43d2b26a5f2c45b5c18f1cc1ad1ce1dd18c22c3f2e

def LB_119 : List ℕ := dec 100 7098958 1218 0 1 0x4b19591cc1eb1ae119e1ab5a01f18c18d3b419a6f71b18819b31884d54f6a1b519e4f3c7d018a3d2d4b7a184f297a1c2e1bb

def LA_120 : List ℕ := dec 137 7155270 841 0 1 0x6a292d1ce1ff1c87b4e1044d381c6b5e6b18c18b484918c486b2d4c394e7b2f582e1b7a19d1e2e69285c381bd5c1881cd681963b583f4c3b3e5d3c59287a2b3b2f481a2e3

def LB_120 : List ℕ := dec 100 7155403 1197 0 1 0x593a6d2c1a6c5f74e19f7c41e9198481aa28d1c83d29f2a829383b5b7e21a1af1c86b4c5b4a2d2e6b6e07918e7b2e191ae5d

def LA_121 : List ℕ := dec 137 7211588 873 0 1 0x1c376c1db1fa1cb4a1e192296d198694a7a181af1bc19919e1c95c29482d7918e5f6e7b5e4819595a5b6e4f1581b1d61b11aa1e95c4d2e39383b385f682e6d5a3c1a3c1cd

def LB_121 : List ℕ := dec 103 7210877 1186 0 1 0x4f1e7c1e97c3b5e49796e493a1ee1bd73c2f2b6a1cd6a4a1c928c3d2f3a2e19b7a5818f2c3c1d6d194818b18e2b02181ae1af7c

def LA_122 : List ℕ := dec 144 7267108 856 0 1 0x7b29a19b181a3a2d1bb1cc4b484f5f6e6818d41be1a92b7e392a2c18d1187c6f2b7e4e3f2a5b319c1eb1a8394a5d1aa396f781af681c1c4f1b8693959291dc2d79682d6b2a4c1f3c

def LB_122 : List ℕ := dec 103 7267668 1193 0 1 0x19e5f5a219f6818491f382b18c7f3c14a4918f1ac218b1fe1d4f3b6e493c1968594a1bd1ae6d18a1918b18d1ec2f3a1af1821c8

def LA_123 : List ℕ := dec 144 7323958 867 0 1 0x393a186c1bb2c6a381ab18c18d1881bf2981cb1a4d2804b1ae5c1a96f1ec4f24d18a7b18a5f5e1db6c681bd18c283f3911a81891a684d2e1d1d14d5831f2c1ae01af419a3b2f4f28

def LB_123 : List ℕ := dec 111 7323711 1240 0 1 0x1cd1881f3d6e2913e1cb18e1a2bb1fa1d93d82c93b29a1ab1c73e391b929c1bf19819f2c18c1bb1b81295f12c3a7f1ec3a1d91ae1b1d91a

def LA_124 : List ℕ := dec 137 7379899 859 0 1 0x19d2a3c1c581ff5a19a018b686f18285a5d19819b5c13d4b1d1bc3b3b18c591f1e4d2e19e481af7f1cc2b2c6f57c6b11c184e2f2b4b1884e6f3d1ba1c95a1e1b193e23292

def LB_124 : List ℕ := dec 108 7379685 1180 0 1 0x18918818e2bb18c1ce1a96b386c295c5f4e1db38188393e396c1ed2b871dd5a1a818d7d1c81b9683c1c797804b4185e1ab1be4f791ee

def LA_125 : List ℕ := dec 134 7436133 853 0 1 0x72c5b4c1b581d5b1a6497e1b3d3a1d5e296d4818e5f1d7d5d2881c93e18381a2e4d3d1ce3d5b28191e28492c1b1831b918a181e4a219d1ac3b481cb1da6f2b484b5e1a

def LB_125 : List ℕ := dec 103 7436001 1230 0 1 0x1d6e2ad1c8586f559188301f7e691a2c4d1ff1f84911884b195a18a1cd1d6e11c6b2a1bf1ac71cc1db4a1ae2991bc1d919e3a69

def LA_126 : List ℕ := dec 146 7491587 862 0 1 0x1881897a1a92a2b18c1d1e1db2aa59481bf2bc2db1e85d2f4a5734a54e18d2b5c2e7f1dc1ab1a84d3d23e1c91d81af3c4c553a18f7e3a1893a5e191f4b391d19819829d5e318b1ee2d

def LB_126 : List ℕ := dec 103 7492336 1210 0 1 0x4681df3c18c119b28c1b91a818f3e19b585a4b6e1a1db6a1c81af5a287d1a4d2a29687382b52f1ba2f4d1894a1ea1fd4e1db2b8

def LA_127 : List ℕ := dec 134 7548248 886 0 1 0x1b1be591a91e87d18a18d7b1ba5b1aa3f2d5f1ba7f385e287f1b786b06681ad1a1fe1af31e2d3c183d63861e4d5b1b8518b291b18c63b2d194a3a6942b1f85e19b077d

def LB_127 : List ℕ := dec 110 7547840 1245 0 1 0x1fc186d18c618d18b1da6e1892f1832a81eb2f3e5b7a6b1b84f6f1cc7b1a3b3819c19b3f1ba7d1cd1fe1b696f2c828b3e1cc18e1ad419b

def LA_128 : List ℕ := dec 129 7604005 886 0 1 0x18f4b7a7d2a1be1a9686b7b5862a5214e3b031b2b2e1b685b63f1ee1992d29282c51887b2a1d718e3f491882f494e3d6d7e7b585c293b5c1cb1be7d19c6b44b3a

def LB_128 : List ℕ := dec 95 7604542 1292 0 1 0x19f4c7b1ac183d1db7a184c7d1ae6b1c4961b5e1b12a4b44f1bc2f1c2f584b1aa4b5b190791ae781bf42e5d1bc591db

def LA_129 : List ℕ := dec 138 7660238 839 0 1 0x7c490292a5928819b1eb2e1ae3f2ae2ad4c7d18e19497a1ad198192a1a92882a928a1b91f6e6841df5e3586d3c37a1e91e8187b42e1f2802f6f2c2c327e3b4b281e4f3a19e

def LB_129 : List ℕ := dec 100 7660438 1210 0 1 0x1ba1cf4c191bc2bd47c28c2c91a7c6d6c4b3618c1cb1981cb18e18a1eb188191f1c3a1f1e61a2b47b1c2d3c18a3f592a1a7a

def LA_130 : List ℕ := dec 134 7716369 888 0 1 0x1c7a3a5f3d591ac3f3a282f1ca1dd1a1a4d2c7a4f2d2c2a5d5e35d4c2b1948382879065e1d97c1d1b1ca18d3f2b281885f383d2b1e87f19d6e292a591aa51cb1da5d28

def LB_130 : List ℕ := dec 95 7716234 1252 0 1 0x291e84d2af2ac1f64d1ea1df485f4c4a1d2d3a2b2e18b3a19837f6a18b1c63e4829d1885e495386597918842c6d3e2e

def LA_131 : List ℕ := dec 130 7772113 906 0 1 0x2b3e17d4a14d1a85a33b292d683918f21ea39781af74a7b586a1c1894e19d28381e5e694e7d183318c392e4924481e96e4e29b2881a1c1cd7a697c4f386f1ec1b9

def LB_131 : List ℕ := dec 97 7772551 1262 0 1 0x5e7d171c1fe6b1b3b6a2f929c1ba19b192d2a1981f695d668284818f4b4c18825929781d919c28929c3d492d2e491882d

def LA_132 : List ℕ := dec 109 7827837 887 0 1 0x1d18c5b1901f82994824d3c3801a191f19918e4f6818818f491991be5a3f3e1895822c6d7e18d19c3d4e597e1b91923872c28829b31c6

def LB_132 : List ℕ := dec 77 7827577 1262 0 1 0x1fa5b4f1e81f95e391a1c7c1cf1b181be3b1bf187c1c591a7e691f6a2524f2b2d1be1ba2d93e4

/-! ## The assembled tables -/

def TA_132 : List ℕ := LA_132

def TB_132 : List ℕ := LB_132

def TA_131 : List ℕ := LA_131 ++ TA_132

def TB_131 : List ℕ := LB_131 ++ TB_132

def TA_130 : List ℕ := LA_130 ++ TA_131

def TB_130 : List ℕ := LB_130 ++ TB_131

def TA_129 : List ℕ := LA_129 ++ TA_130

def TB_129 : List ℕ := LB_129 ++ TB_130

def TA_128 : List ℕ := LA_128 ++ TA_129

def TB_128 : List ℕ := LB_128 ++ TB_129

def TA_127 : List ℕ := LA_127 ++ TA_128

def TB_127 : List ℕ := LB_127 ++ TB_128

def TA_126 : List ℕ := LA_126 ++ TA_127

def TB_126 : List ℕ := LB_126 ++ TB_127

def TA_125 : List ℕ := LA_125 ++ TA_126

def TB_125 : List ℕ := LB_125 ++ TB_126

def TA_124 : List ℕ := LA_124 ++ TA_125

def TB_124 : List ℕ := LB_124 ++ TB_125

def TA_123 : List ℕ := LA_123 ++ TA_124

def TB_123 : List ℕ := LB_123 ++ TB_124

def TA_122 : List ℕ := LA_122 ++ TA_123

def TB_122 : List ℕ := LB_122 ++ TB_123

def TA_121 : List ℕ := LA_121 ++ TA_122

def TB_121 : List ℕ := LB_121 ++ TB_122

def TA_120 : List ℕ := LA_120 ++ TA_121

def TB_120 : List ℕ := LB_120 ++ TB_121

def TA_119 : List ℕ := LA_119 ++ TA_120

def TB_119 : List ℕ := LB_119 ++ TB_120

def TA_118 : List ℕ := LA_118 ++ TA_119

def TB_118 : List ℕ := LB_118 ++ TB_119

def TA_117 : List ℕ := LA_117 ++ TA_118

def TB_117 : List ℕ := LB_117 ++ TB_118

def TA_116 : List ℕ := LA_116 ++ TA_117

def TB_116 : List ℕ := LB_116 ++ TB_117

def TA_115 : List ℕ := LA_115 ++ TA_116

def TB_115 : List ℕ := LB_115 ++ TB_116

def TA_114 : List ℕ := LA_114 ++ TA_115

def TB_114 : List ℕ := LB_114 ++ TB_115

def TA_113 : List ℕ := LA_113 ++ TA_114

def TB_113 : List ℕ := LB_113 ++ TB_114

def TA_112 : List ℕ := LA_112 ++ TA_113

def TB_112 : List ℕ := LB_112 ++ TB_113

def TA_111 : List ℕ := LA_111 ++ TA_112

def TB_111 : List ℕ := LB_111 ++ TB_112

def TA_110 : List ℕ := LA_110 ++ TA_111

def TB_110 : List ℕ := LB_110 ++ TB_111

def TA_109 : List ℕ := LA_109 ++ TA_110

def TB_109 : List ℕ := LB_109 ++ TB_110

def TA_108 : List ℕ := LA_108 ++ TA_109

def TB_108 : List ℕ := LB_108 ++ TB_109

def TA_107 : List ℕ := LA_107 ++ TA_108

def TB_107 : List ℕ := LB_107 ++ TB_108

def TA_106 : List ℕ := LA_106 ++ TA_107

def TB_106 : List ℕ := LB_106 ++ TB_107

def TA_105 : List ℕ := LA_105 ++ TA_106

def TB_105 : List ℕ := LB_105 ++ TB_106

def TA_104 : List ℕ := LA_104 ++ TA_105

def TB_104 : List ℕ := LB_104 ++ TB_105

def TA_103 : List ℕ := LA_103 ++ TA_104

def TB_103 : List ℕ := LB_103 ++ TB_104

def TA_102 : List ℕ := LA_102 ++ TA_103

def TB_102 : List ℕ := LB_102 ++ TB_103

def TA_101 : List ℕ := LA_101 ++ TA_102

def TB_101 : List ℕ := LB_101 ++ TB_102

def TA_100 : List ℕ := LA_100 ++ TA_101

def TB_100 : List ℕ := LB_100 ++ TB_101

def TA_99 : List ℕ := LA_99 ++ TA_100

def TB_99 : List ℕ := LB_99 ++ TB_100

def TA_98 : List ℕ := LA_98 ++ TA_99

def TB_98 : List ℕ := LB_98 ++ TB_99

def TA_97 : List ℕ := LA_97 ++ TA_98

def TB_97 : List ℕ := LB_97 ++ TB_98

def TA_96 : List ℕ := LA_96 ++ TA_97

def TB_96 : List ℕ := LB_96 ++ TB_97

def TA_95 : List ℕ := LA_95 ++ TA_96

def TB_95 : List ℕ := LB_95 ++ TB_96

def TA_94 : List ℕ := LA_94 ++ TA_95

def TB_94 : List ℕ := LB_94 ++ TB_95

def TA_93 : List ℕ := LA_93 ++ TA_94

def TB_93 : List ℕ := LB_93 ++ TB_94

def TA_92 : List ℕ := LA_92 ++ TA_93

def TB_92 : List ℕ := LB_92 ++ TB_93

def TA_91 : List ℕ := LA_91 ++ TA_92

def TB_91 : List ℕ := LB_91 ++ TB_92

def TA_90 : List ℕ := LA_90 ++ TA_91

def TB_90 : List ℕ := LB_90 ++ TB_91

def TA_89 : List ℕ := LA_89 ++ TA_90

def TB_89 : List ℕ := LB_89 ++ TB_90

def TA_88 : List ℕ := LA_88 ++ TA_89

def TB_88 : List ℕ := LB_88 ++ TB_89

def TA_87 : List ℕ := LA_87 ++ TA_88

def TB_87 : List ℕ := LB_87 ++ TB_88

def TA_86 : List ℕ := LA_86 ++ TA_87

def TB_86 : List ℕ := LB_86 ++ TB_87

def TA_85 : List ℕ := LA_85 ++ TA_86

def TB_85 : List ℕ := LB_85 ++ TB_86

def TA_84 : List ℕ := LA_84 ++ TA_85

def TB_84 : List ℕ := LB_84 ++ TB_85

def TA_83 : List ℕ := LA_83 ++ TA_84

def TB_83 : List ℕ := LB_83 ++ TB_84

def TA_82 : List ℕ := LA_82 ++ TA_83

def TB_82 : List ℕ := LB_82 ++ TB_83

def TA_81 : List ℕ := LA_81 ++ TA_82

def TB_81 : List ℕ := LB_81 ++ TB_82

def TA_80 : List ℕ := LA_80 ++ TA_81

def TB_80 : List ℕ := LB_80 ++ TB_81

def TA_79 : List ℕ := LA_79 ++ TA_80

def TB_79 : List ℕ := LB_79 ++ TB_80

def TA_78 : List ℕ := LA_78 ++ TA_79

def TB_78 : List ℕ := LB_78 ++ TB_79

def TA_77 : List ℕ := LA_77 ++ TA_78

def TB_77 : List ℕ := LB_77 ++ TB_78

def TA_76 : List ℕ := LA_76 ++ TA_77

def TB_76 : List ℕ := LB_76 ++ TB_77

def TA_75 : List ℕ := LA_75 ++ TA_76

def TB_75 : List ℕ := LB_75 ++ TB_76

def TA_74 : List ℕ := LA_74 ++ TA_75

def TB_74 : List ℕ := LB_74 ++ TB_75

def TA_73 : List ℕ := LA_73 ++ TA_74

def TB_73 : List ℕ := LB_73 ++ TB_74

def TA_72 : List ℕ := LA_72 ++ TA_73

def TB_72 : List ℕ := LB_72 ++ TB_73

def TA_71 : List ℕ := LA_71 ++ TA_72

def TB_71 : List ℕ := LB_71 ++ TB_72

def TA_70 : List ℕ := LA_70 ++ TA_71

def TB_70 : List ℕ := LB_70 ++ TB_71

def TA_69 : List ℕ := LA_69 ++ TA_70

def TB_69 : List ℕ := LB_69 ++ TB_70

def TA_68 : List ℕ := LA_68 ++ TA_69

def TB_68 : List ℕ := LB_68 ++ TB_69

def TA_67 : List ℕ := LA_67 ++ TA_68

def TB_67 : List ℕ := LB_67 ++ TB_68

def TA_66 : List ℕ := LA_66 ++ TA_67

def TB_66 : List ℕ := LB_66 ++ TB_67

def TA_65 : List ℕ := LA_65 ++ TA_66

def TB_65 : List ℕ := LB_65 ++ TB_66

def TA_64 : List ℕ := LA_64 ++ TA_65

def TB_64 : List ℕ := LB_64 ++ TB_65

def TA_63 : List ℕ := LA_63 ++ TA_64

def TB_63 : List ℕ := LB_63 ++ TB_64

def TA_62 : List ℕ := LA_62 ++ TA_63

def TB_62 : List ℕ := LB_62 ++ TB_63

def TA_61 : List ℕ := LA_61 ++ TA_62

def TB_61 : List ℕ := LB_61 ++ TB_62

def TA_60 : List ℕ := LA_60 ++ TA_61

def TB_60 : List ℕ := LB_60 ++ TB_61

def TA_59 : List ℕ := LA_59 ++ TA_60

def TB_59 : List ℕ := LB_59 ++ TB_60

def TA_58 : List ℕ := LA_58 ++ TA_59

def TB_58 : List ℕ := LB_58 ++ TB_59

def TA_57 : List ℕ := LA_57 ++ TA_58

def TB_57 : List ℕ := LB_57 ++ TB_58

def TA_56 : List ℕ := LA_56 ++ TA_57

def TB_56 : List ℕ := LB_56 ++ TB_57

def TA_55 : List ℕ := LA_55 ++ TA_56

def TB_55 : List ℕ := LB_55 ++ TB_56

def TA_54 : List ℕ := LA_54 ++ TA_55

def TB_54 : List ℕ := LB_54 ++ TB_55

def TA_53 : List ℕ := LA_53 ++ TA_54

def TB_53 : List ℕ := LB_53 ++ TB_54

def TA_52 : List ℕ := LA_52 ++ TA_53

def TB_52 : List ℕ := LB_52 ++ TB_53

def TA_51 : List ℕ := LA_51 ++ TA_52

def TB_51 : List ℕ := LB_51 ++ TB_52

def TA_50 : List ℕ := LA_50 ++ TA_51

def TB_50 : List ℕ := LB_50 ++ TB_51

def TA_49 : List ℕ := LA_49 ++ TA_50

def TB_49 : List ℕ := LB_49 ++ TB_50

def TA_48 : List ℕ := LA_48 ++ TA_49

def TB_48 : List ℕ := LB_48 ++ TB_49

def TA_47 : List ℕ := LA_47 ++ TA_48

def TB_47 : List ℕ := LB_47 ++ TB_48

def TA_46 : List ℕ := LA_46 ++ TA_47

def TB_46 : List ℕ := LB_46 ++ TB_47

def TA_45 : List ℕ := LA_45 ++ TA_46

def TB_45 : List ℕ := LB_45 ++ TB_46

def TA_44 : List ℕ := LA_44 ++ TA_45

def TB_44 : List ℕ := LB_44 ++ TB_45

def TA_43 : List ℕ := LA_43 ++ TA_44

def TB_43 : List ℕ := LB_43 ++ TB_44

def TA_42 : List ℕ := LA_42 ++ TA_43

def TB_42 : List ℕ := LB_42 ++ TB_43

def TA_41 : List ℕ := LA_41 ++ TA_42

def TB_41 : List ℕ := LB_41 ++ TB_42

def TA_40 : List ℕ := LA_40 ++ TA_41

def TB_40 : List ℕ := LB_40 ++ TB_41

def TA_39 : List ℕ := LA_39 ++ TA_40

def TB_39 : List ℕ := LB_39 ++ TB_40

def TA_38 : List ℕ := LA_38 ++ TA_39

def TB_38 : List ℕ := LB_38 ++ TB_39

def TA_37 : List ℕ := LA_37 ++ TA_38

def TB_37 : List ℕ := LB_37 ++ TB_38

def TA_36 : List ℕ := LA_36 ++ TA_37

def TB_36 : List ℕ := LB_36 ++ TB_37

def TA_35 : List ℕ := LA_35 ++ TA_36

def TB_35 : List ℕ := LB_35 ++ TB_36

def TA_34 : List ℕ := LA_34 ++ TA_35

def TB_34 : List ℕ := LB_34 ++ TB_35

def TA_33 : List ℕ := LA_33 ++ TA_34

def TB_33 : List ℕ := LB_33 ++ TB_34

def TA_32 : List ℕ := LA_32 ++ TA_33

def TB_32 : List ℕ := LB_32 ++ TB_33

def TA_31 : List ℕ := LA_31 ++ TA_32

def TB_31 : List ℕ := LB_31 ++ TB_32

def TA_30 : List ℕ := LA_30 ++ TA_31

def TB_30 : List ℕ := LB_30 ++ TB_31

def TA_29 : List ℕ := LA_29 ++ TA_30

def TB_29 : List ℕ := LB_29 ++ TB_30

def TA_28 : List ℕ := LA_28 ++ TA_29

def TB_28 : List ℕ := LB_28 ++ TB_29

def TA_27 : List ℕ := LA_27 ++ TA_28

def TB_27 : List ℕ := LB_27 ++ TB_28

def TA_26 : List ℕ := LA_26 ++ TA_27

def TB_26 : List ℕ := LB_26 ++ TB_27

def TA_25 : List ℕ := LA_25 ++ TA_26

def TB_25 : List ℕ := LB_25 ++ TB_26

def TA_24 : List ℕ := LA_24 ++ TA_25

def TB_24 : List ℕ := LB_24 ++ TB_25

def TA_23 : List ℕ := LA_23 ++ TA_24

def TB_23 : List ℕ := LB_23 ++ TB_24

def TA_22 : List ℕ := LA_22 ++ TA_23

def TB_22 : List ℕ := LB_22 ++ TB_23

def TA_21 : List ℕ := LA_21 ++ TA_22

def TB_21 : List ℕ := LB_21 ++ TB_22

def TA_20 : List ℕ := LA_20 ++ TA_21

def TB_20 : List ℕ := LB_20 ++ TB_21

def TA_19 : List ℕ := LA_19 ++ TA_20

def TB_19 : List ℕ := LB_19 ++ TB_20

def TA_18 : List ℕ := LA_18 ++ TA_19

def TB_18 : List ℕ := LB_18 ++ TB_19

def TA_17 : List ℕ := LA_17 ++ TA_18

def TB_17 : List ℕ := LB_17 ++ TB_18

def TA_16 : List ℕ := LA_16 ++ TA_17

def TB_16 : List ℕ := LB_16 ++ TB_17

def TA_15 : List ℕ := LA_15 ++ TA_16

def TB_15 : List ℕ := LB_15 ++ TB_16

def TA_14 : List ℕ := LA_14 ++ TA_15

def TB_14 : List ℕ := LB_14 ++ TB_15

def TA_13 : List ℕ := LA_13 ++ TA_14

def TB_13 : List ℕ := LB_13 ++ TB_14

def TA_12 : List ℕ := LA_12 ++ TA_13

def TB_12 : List ℕ := LB_12 ++ TB_13

def TA_11 : List ℕ := LA_11 ++ TA_12

def TB_11 : List ℕ := LB_11 ++ TB_12

def TA_10 : List ℕ := LA_10 ++ TA_11

def TB_10 : List ℕ := LB_10 ++ TB_11

def TA_9 : List ℕ := LA_9 ++ TA_10

def TB_9 : List ℕ := LB_9 ++ TB_10

def TA_8 : List ℕ := LA_8 ++ TA_9

def TB_8 : List ℕ := LB_8 ++ TB_9

def TA_7 : List ℕ := LA_7 ++ TA_8

def TB_7 : List ℕ := LB_7 ++ TB_8

def TA_6 : List ℕ := LA_6 ++ TA_7

def TB_6 : List ℕ := LB_6 ++ TB_7

def TA_5 : List ℕ := LA_5 ++ TA_6

def TB_5 : List ℕ := LB_5 ++ TB_6

def TA_4 : List ℕ := LA_4 ++ TA_5

def TB_4 : List ℕ := LB_4 ++ TB_5

def TA_3 : List ℕ := LA_3 ++ TA_4

def TB_3 : List ℕ := LB_3 ++ TB_4

def TA_2 : List ℕ := LA_2 ++ TA_3

def TB_2 : List ℕ := LB_2 ++ TB_3

def TA_1 : List ℕ := LA_1 ++ TA_2

def TB_1 : List ℕ := LB_1 ++ TB_2

def TA_0 : List ℕ := LA_0 ++ TA_1

def TB_0 : List ℕ := LB_0 ++ TB_1

/-- `tabA[k] = π(k(k+1)/2)`. -/
def tabA : List ℕ := 0 :: TA_0

/-- `tabB[m] = π(m ^ 2)`. -/
def tabB : List ℕ := 0 :: TB_0

theorem base0 (f : ℕ → ℕ) (h : Nat.count Nat.Prime (f 0) = 0) : Good f 0 [0] := by
  intro i hi
  obtain rfl : i = 0 := by simpa using hi
  simpa using h

set_option maxHeartbeats 400000000 in
/-- All window checks run inside one proof, so that the kernel checks run one after another on
one thread and reuse its memory. -/
theorem goodAB : Good fA 0 tabA ∧ Good fB 0 tabB := by
  have ck_0 : chk2 0 1081344 0 0 LA_0 0 0 LB_0 = true := by decide +kernel
  have g_0 : Good fA 1 LA_0 ∧ Good fB 1 LB_0 :=
    chk2_sound (by norm_num [NMax]) ck_0
      hc0A
      hc0B
  have ck_1 : chk2 1048576 1081344 1448 82061 LA_1 1024 82025 LB_1 = true := by decide +kernel
  have g_1 : Good fA 1449 LA_1 ∧ Good fB 1025 LB_1 :=
    chk2_sound (by norm_num [NMax]) ck_1
      (g_0.1.count_eq (i := 1447) (by decide +kernel) (by decide +kernel))
      (g_0.2.count_eq (i := 1023) (by decide +kernel) (by decide +kernel))
  have ck_2 : chk2 2097152 1081344 2048 155681 LA_2 1449 155778 LB_2 = true := by decide +kernel
  have g_2 : Good fA 2049 LA_2 ∧ Good fB 1450 LB_2 :=
    chk2_sound (by norm_num [NMax]) ck_2
      (g_1.1.count_eq (i := 599) (by decide +kernel) (by decide +kernel))
      (g_1.2.count_eq (i := 424) (by decide +kernel) (by decide +kernel))
  have ck_3 : chk2 3145728 1081344 2508 226586 LA_3 1774 226635 LB_3 = true := by decide +kernel
  have g_3 : Good fA 2509 LA_3 ∧ Good fB 1775 LB_3 :=
    chk2_sound (by norm_num [NMax]) ck_3
      (g_2.1.count_eq (i := 459) (by decide +kernel) (by decide +kernel))
      (g_2.2.count_eq (i := 324) (by decide +kernel) (by decide +kernel))
  have ck_4 : chk2 4194304 1081344 2896 295984 LA_4 2048 295947 LB_4 = true := by decide +kernel
  have g_4 : Good fA 2897 LA_4 ∧ Good fB 2049 LB_4 :=
    chk2_sound (by norm_num [NMax]) ck_4
      (g_3.1.count_eq (i := 387) (by decide +kernel) (by decide +kernel))
      (g_3.2.count_eq (i := 273) (by decide +kernel) (by decide +kernel))
  have ck_5 : chk2 5242880 1081344 3238 364278 LA_5 2290 364290 LB_5 = true := by decide +kernel
  have g_5 : Good fA 3239 LA_5 ∧ Good fB 2291 LB_5 :=
    chk2_sound (by norm_num [NMax]) ck_5
      (g_4.1.count_eq (i := 341) (by decide +kernel) (by decide +kernel))
      (g_4.2.count_eq (i := 241) (by decide +kernel) (by decide +kernel))
  have ck_6 : chk2 6291456 1081344 3547 431563 LA_6 2509 431738 LB_6 = true := by decide +kernel
  have g_6 : Good fA 3548 LA_6 ∧ Good fB 2510 LB_6 :=
    chk2_sound (by norm_num [NMax]) ck_6
      (g_5.1.count_eq (i := 308) (by decide +kernel) (by decide +kernel))
      (g_5.2.count_eq (i := 218) (by decide +kernel) (by decide +kernel))
  have ck_7 : chk2 7340032 1081344 3831 498188 LA_7 2710 498421 LB_7 = true := by decide +kernel
  have g_7 : Good fA 3832 LA_7 ∧ Good fB 2711 LB_7 :=
    chk2_sound (by norm_num [NMax]) ck_7
      (g_6.1.count_eq (i := 283) (by decide +kernel) (by decide +kernel))
      (g_6.2.count_eq (i := 200) (by decide +kernel) (by decide +kernel))
  have ck_8 : chk2 8388608 1081344 4096 564294 LA_8 2897 564420 LB_8 = true := by decide +kernel
  have g_8 : Good fA 4097 LA_8 ∧ Good fB 2898 LB_8 :=
    chk2_sound (by norm_num [NMax]) ck_8
      (g_7.1.count_eq (i := 264) (by decide +kernel) (by decide +kernel))
      (g_7.2.count_eq (i := 186) (by decide +kernel) (by decide +kernel))
  have ck_9 : chk2 9437184 1081344 4344 629694 LA_9 3072 629686 LB_9 = true := by decide +kernel
  have g_9 : Good fA 4345 LA_9 ∧ Good fB 3073 LB_9 :=
    chk2_sound (by norm_num [NMax]) ck_9
      (g_8.1.count_eq (i := 247) (by decide +kernel) (by decide +kernel))
      (g_8.2.count_eq (i := 174) (by decide +kernel) (by decide +kernel))
  have ck_10 : chk2 10485760 1081344 4579 694725 LA_10 3239 695064 LB_10 = true := by decide +kernel
  have g_10 : Good fA 4580 LA_10 ∧ Good fB 3240 LB_10 :=
    chk2_sound (by norm_num [NMax]) ck_10
      (g_9.1.count_eq (i := 234) (by decide +kernel) (by decide +kernel))
      (g_9.2.count_eq (i := 166) (by decide +kernel) (by decide +kernel))
  have ck_11 : chk2 11534336 1081344 4803 759550 LA_11 3397 759732 LB_11 = true := by decide +kernel
  have g_11 : Good fA 4804 LA_11 ∧ Good fB 3398 LB_11 :=
    chk2_sound (by norm_num [NMax]) ck_11
      (g_10.1.count_eq (i := 223) (by decide +kernel) (by decide +kernel))
      (g_10.2.count_eq (i := 157) (by decide +kernel) (by decide +kernel))
  have ck_12 : chk2 12582912 1081344 5017 824042 LA_12 3548 824086 LB_12 = true := by decide +kernel
  have g_12 : Good fA 5018 LA_12 ∧ Good fB 3549 LB_12 :=
    chk2_sound (by norm_num [NMax]) ck_12
      (g_11.1.count_eq (i := 213) (by decide +kernel) (by decide +kernel))
      (g_11.2.count_eq (i := 150) (by decide +kernel) (by decide +kernel))
  have ck_13 : chk2 13631488 1081344 5221 887676 LA_13 3693 888061 LB_13 = true := by decide +kernel
  have g_13 : Good fA 5222 LA_13 ∧ Good fB 3694 LB_13 :=
    chk2_sound (by norm_num [NMax]) ck_13
      (g_12.1.count_eq (i := 203) (by decide +kernel) (by decide +kernel))
      (g_12.2.count_eq (i := 144) (by decide +kernel) (by decide +kernel))
  have ck_14 : chk2 14680064 1081344 5418 951352 LA_14 3832 951630 LB_14 = true := by decide +kernel
  have g_14 : Good fA 5419 LA_14 ∧ Good fB 3833 LB_14 :=
    chk2_sound (by norm_num [NMax]) ck_14
      (g_13.1.count_eq (i := 196) (by decide +kernel) (by decide +kernel))
      (g_13.2.count_eq (i := 138) (by decide +kernel) (by decide +kernel))
  have ck_15 : chk2 15728640 1081344 5609 1015011 LA_15 3966 1014761 LB_15 = true := by decide +kernel
  have g_15 : Good fA 5610 LA_15 ∧ Good fB 3967 LB_15 :=
    chk2_sound (by norm_num [NMax]) ck_15
      (g_14.1.count_eq (i := 190) (by decide +kernel) (by decide +kernel))
      (g_14.2.count_eq (i := 133) (by decide +kernel) (by decide +kernel))
  have ck_16 : chk2 16777216 1081344 5793 1078185 LA_16 4096 1077871 LB_16 = true := by decide +kernel
  have g_16 : Good fA 5794 LA_16 ∧ Good fB 4097 LB_16 :=
    chk2_sound (by norm_num [NMax]) ck_16
      (g_15.1.count_eq (i := 183) (by decide +kernel) (by decide +kernel))
      (g_15.2.count_eq (i := 129) (by decide +kernel) (by decide +kernel))
  have ck_17 : chk2 17825792 1081344 5971 1141085 LA_17 4223 1141346 LB_17 = true := by decide +kernel
  have g_17 : Good fA 5972 LA_17 ∧ Good fB 4224 LB_17 :=
    chk2_sound (by norm_num [NMax]) ck_17
      (g_16.1.count_eq (i := 177) (by decide +kernel) (by decide +kernel))
      (g_16.2.count_eq (i := 126) (by decide +kernel) (by decide +kernel))
  have ck_18 : chk2 18874368 1081344 6144 1203747 LA_18 4345 1203838 LB_18 = true := by decide +kernel
  have g_18 : Good fA 6145 LA_18 ∧ Good fB 4346 LB_18 :=
    chk2_sound (by norm_num [NMax]) ck_18
      (g_17.1.count_eq (i := 172) (by decide +kernel) (by decide +kernel))
      (g_17.2.count_eq (i := 121) (by decide +kernel) (by decide +kernel))
  have ck_19 : chk2 19922944 1081344 6312 1266059 LA_19 4464 1266272 LB_19 = true := by decide +kernel
  have g_19 : Good fA 6313 LA_19 ∧ Good fB 4465 LB_19 :=
    chk2_sound (by norm_num [NMax]) ck_19
      (g_18.1.count_eq (i := 167) (by decide +kernel) (by decide +kernel))
      (g_18.2.count_eq (i := 118) (by decide +kernel) (by decide +kernel))
  have ck_20 : chk2 20971520 1081344 6476 1328294 LA_20 4580 1328530 LB_20 = true := by decide +kernel
  have g_20 : Good fA 6477 LA_20 ∧ Good fB 4581 LB_20 :=
    chk2_sound (by norm_num [NMax]) ck_20
      (g_19.1.count_eq (i := 163) (by decide +kernel) (by decide +kernel))
      (g_19.2.count_eq (i := 115) (by decide +kernel) (by decide +kernel))
  have ck_21 : chk2 22020096 1081344 6636 1390529 LA_21 4693 1390706 LB_21 = true := by decide +kernel
  have g_21 : Good fA 6637 LA_21 ∧ Good fB 4694 LB_21 :=
    chk2_sound (by norm_num [NMax]) ck_21
      (g_20.1.count_eq (i := 159) (by decide +kernel) (by decide +kernel))
      (g_20.2.count_eq (i := 112) (by decide +kernel) (by decide +kernel))
  have ck_22 : chk2 23068672 1081344 6792 1452337 LA_22 4803 1452323 LB_22 = true := by decide +kernel
  have g_22 : Good fA 6793 LA_22 ∧ Good fB 4804 LB_22 :=
    chk2_sound (by norm_num [NMax]) ck_22
      (g_21.1.count_eq (i := 155) (by decide +kernel) (by decide +kernel))
      (g_21.2.count_eq (i := 109) (by decide +kernel) (by decide +kernel))
  have ck_23 : chk2 24117248 1081344 6945 1514172 LA_23 4911 1514061 LB_23 = true := by decide +kernel
  have g_23 : Good fA 6946 LA_23 ∧ Good fB 4912 LB_23 :=
    chk2_sound (by norm_num [NMax]) ck_23
      (g_22.1.count_eq (i := 152) (by decide +kernel) (by decide +kernel))
      (g_22.2.count_eq (i := 107) (by decide +kernel) (by decide +kernel))
  have ck_24 : chk2 25165824 1081344 7094 1575667 LA_24 5017 1575914 LB_24 = true := by decide +kernel
  have g_24 : Good fA 7095 LA_24 ∧ Good fB 5018 LB_24 :=
    chk2_sound (by norm_num [NMax]) ck_24
      (g_23.1.count_eq (i := 148) (by decide +kernel) (by decide +kernel))
      (g_23.2.count_eq (i := 105) (by decide +kernel) (by decide +kernel))
  have ck_25 : chk2 26214400 1081344 7241 1637378 LA_25 5120 1637054 LB_25 = true := by decide +kernel
  have g_25 : Good fA 7242 LA_25 ∧ Good fB 5121 LB_25 :=
    chk2_sound (by norm_num [NMax]) ck_25
      (g_24.1.count_eq (i := 146) (by decide +kernel) (by decide +kernel))
      (g_24.2.count_eq (i := 102) (by decide +kernel) (by decide +kernel))
  have ck_26 : chk2 27262976 1081344 7384 1698572 LA_26 5222 1698785 LB_26 = true := by decide +kernel
  have g_26 : Good fA 7385 LA_26 ∧ Good fB 5223 LB_26 :=
    chk2_sound (by norm_num [NMax]) ck_26
      (g_25.1.count_eq (i := 142) (by decide +kernel) (by decide +kernel))
      (g_25.2.count_eq (i := 101) (by decide +kernel) (by decide +kernel))
  have ck_27 : chk2 28311552 1081344 7525 1759946 LA_27 5321 1759738 LB_27 = true := by decide +kernel
  have g_27 : Good fA 7526 LA_27 ∧ Good fB 5322 LB_27 :=
    chk2_sound (by norm_num [NMax]) ck_27
      (g_26.1.count_eq (i := 140) (by decide +kernel) (by decide +kernel))
      (g_26.2.count_eq (i := 98) (by decide +kernel) (by decide +kernel))
  have ck_28 : chk2 29360128 1081344 7663 1820905 LA_28 5419 1820960 LB_28 = true := by decide +kernel
  have g_28 : Good fA 7664 LA_28 ∧ Good fB 5420 LB_28 :=
    chk2_sound (by norm_num [NMax]) ck_28
      (g_27.1.count_eq (i := 137) (by decide +kernel) (by decide +kernel))
      (g_27.2.count_eq (i := 97) (by decide +kernel) (by decide +kernel))
  have ck_29 : chk2 30408704 1081344 7799 1882143 LA_29 5515 1882095 LB_29 = true := by decide +kernel
  have g_29 : Good fA 7800 LA_29 ∧ Good fB 5516 LB_29 :=
    chk2_sound (by norm_num [NMax]) ck_29
      (g_28.1.count_eq (i := 135) (by decide +kernel) (by decide +kernel))
      (g_28.2.count_eq (i := 95) (by decide +kernel) (by decide +kernel))
  have ck_30 : chk2 31457280 1081344 7932 1942672 LA_30 5609 1942592 LB_30 = true := by decide +kernel
  have g_30 : Good fA 7933 LA_30 ∧ Good fB 5610 LB_30 :=
    chk2_sound (by norm_num [NMax]) ck_30
      (g_29.1.count_eq (i := 132) (by decide +kernel) (by decide +kernel))
      (g_29.2.count_eq (i := 93) (by decide +kernel) (by decide +kernel))
  have ck_31 : chk2 32505856 1081344 8063 2003327 LA_31 5702 2003492 LB_31 = true := by decide +kernel
  have g_31 : Good fA 8064 LA_31 ∧ Good fB 5703 LB_31 :=
    chk2_sound (by norm_num [NMax]) ck_31
      (g_30.1.count_eq (i := 130) (by decide +kernel) (by decide +kernel))
      (g_30.2.count_eq (i := 92) (by decide +kernel) (by decide +kernel))
  have ck_32 : chk2 33554432 1081344 8192 2063947 LA_32 5793 2063961 LB_32 = true := by decide +kernel
  have g_32 : Good fA 8193 LA_32 ∧ Good fB 5794 LB_32 :=
    chk2_sound (by norm_num [NMax]) ck_32
      (g_31.1.count_eq (i := 128) (by decide +kernel) (by decide +kernel))
      (g_31.2.count_eq (i := 90) (by decide +kernel) (by decide +kernel))
  have ck_33 : chk2 34603008 1081344 8319 2124206 LA_33 5883 2124357 LB_33 = true := by decide +kernel
  have g_33 : Good fA 8320 LA_33 ∧ Good fB 5884 LB_33 :=
    chk2_sound (by norm_num [NMax]) ck_33
      (g_32.1.count_eq (i := 126) (by decide +kernel) (by decide +kernel))
      (g_32.2.count_eq (i := 89) (by decide +kernel) (by decide +kernel))
  have ck_34 : chk2 35651584 1081344 8444 2184437 LA_34 5971 2184335 LB_34 = true := by decide +kernel
  have g_34 : Good fA 8445 LA_34 ∧ Good fB 5972 LB_34 :=
    chk2_sound (by norm_num [NMax]) ck_34
      (g_33.1.count_eq (i := 124) (by decide +kernel) (by decide +kernel))
      (g_33.2.count_eq (i := 87) (by decide +kernel) (by decide +kernel))
  have ck_35 : chk2 36700160 1081344 8567 2244526 LA_35 6059 2245115 LB_35 = true := by decide +kernel
  have g_35 : Good fA 8568 LA_35 ∧ Good fB 6060 LB_35 :=
    chk2_sound (by norm_num [NMax]) ck_35
      (g_34.1.count_eq (i := 122) (by decide +kernel) (by decide +kernel))
      (g_34.2.count_eq (i := 87) (by decide +kernel) (by decide +kernel))
  have ck_36 : chk2 37748736 1081344 8689 2304935 LA_36 6144 2304655 LB_36 = true := by decide +kernel
  have g_36 : Good fA 8690 LA_36 ∧ Good fB 6145 LB_36 :=
    chk2_sound (by norm_num [NMax]) ck_36
      (g_35.1.count_eq (i := 121) (by decide +kernel) (by decide +kernel))
      (g_35.2.count_eq (i := 84) (by decide +kernel) (by decide +kernel))
  have ck_37 : chk2 38797312 1081344 8809 2365153 LA_37 6229 2364973 LB_37 = true := by decide +kernel
  have g_37 : Good fA 8810 LA_37 ∧ Good fB 6230 LB_37 :=
    chk2_sound (by norm_num [NMax]) ck_37
      (g_36.1.count_eq (i := 119) (by decide +kernel) (by decide +kernel))
      (g_36.2.count_eq (i := 84) (by decide +kernel) (by decide +kernel))
  have ck_38 : chk2 39845888 1081344 8927 2425155 LA_38 6313 2425368 LB_38 = true := by decide +kernel
  have g_38 : Good fA 8928 LA_38 ∧ Good fB 6314 LB_38 :=
    chk2_sound (by norm_num [NMax]) ck_38
      (g_37.1.count_eq (i := 117) (by decide +kernel) (by decide +kernel))
      (g_37.2.count_eq (i := 83) (by decide +kernel) (by decide +kernel))
  have ck_39 : chk2 40894464 1081344 9044 2485158 LA_39 6395 2484861 LB_39 = true := by decide +kernel
  have g_39 : Good fA 9045 LA_39 ∧ Good fB 6396 LB_39 :=
    chk2_sound (by norm_num [NMax]) ck_39
      (g_38.1.count_eq (i := 116) (by decide +kernel) (by decide +kernel))
      (g_38.2.count_eq (i := 81) (by decide +kernel) (by decide +kernel))
  have ck_40 : chk2 41943040 1081344 9159 2544710 LA_40 6477 2544902 LB_40 = true := by decide +kernel
  have g_40 : Good fA 9160 LA_40 ∧ Good fB 6478 LB_40 :=
    chk2_sound (by norm_num [NMax]) ck_40
      (g_39.1.count_eq (i := 114) (by decide +kernel) (by decide +kernel))
      (g_39.2.count_eq (i := 81) (by decide +kernel) (by decide +kernel))
  have ck_41 : chk2 42991616 1081344 9273 2604472 LA_41 6557 2604212 LB_41 = true := by decide +kernel
  have g_41 : Good fA 9274 LA_41 ∧ Good fB 6558 LB_41 :=
    chk2_sound (by norm_num [NMax]) ck_41
      (g_40.1.count_eq (i := 113) (by decide +kernel) (by decide +kernel))
      (g_40.2.count_eq (i := 79) (by decide +kernel) (by decide +kernel))
  have ck_42 : chk2 44040192 1081344 9385 2663878 LA_42 6637 2664215 LB_42 = true := by decide +kernel
  have g_42 : Good fA 9386 LA_42 ∧ Good fB 6638 LB_42 :=
    chk2_sound (by norm_num [NMax]) ck_42
      (g_41.1.count_eq (i := 111) (by decide +kernel) (by decide +kernel))
      (g_41.2.count_eq (i := 79) (by decide +kernel) (by decide +kernel))
  have ck_43 : chk2 45088768 1081344 9496 2723423 LA_43 6715 2723396 LB_43 = true := by decide +kernel
  have g_43 : Good fA 9497 LA_43 ∧ Good fB 6716 LB_43 :=
    chk2_sound (by norm_num [NMax]) ck_43
      (g_42.1.count_eq (i := 110) (by decide +kernel) (by decide +kernel))
      (g_42.2.count_eq (i := 77) (by decide +kernel) (by decide +kernel))
  have ck_44 : chk2 46137344 1081344 9606 2783089 LA_44 6793 2783224 LB_44 = true := by decide +kernel
  have g_44 : Good fA 9607 LA_44 ∧ Good fB 6794 LB_44 :=
    chk2_sound (by norm_num [NMax]) ck_44
      (g_43.1.count_eq (i := 109) (by decide +kernel) (by decide +kernel))
      (g_43.2.count_eq (i := 77) (by decide +kernel) (by decide +kernel))
  have ck_45 : chk2 47185920 1081344 9715 2842742 LA_45 6870 2842819 LB_45 = true := by decide +kernel
  have g_45 : Good fA 9716 LA_45 ∧ Good fB 6871 LB_45 :=
    chk2_sound (by norm_num [NMax]) ck_45
      (g_44.1.count_eq (i := 108) (by decide +kernel) (by decide +kernel))
      (g_44.2.count_eq (i := 76) (by decide +kernel) (by decide +kernel))
  have ck_46 : chk2 48234496 1081344 9822 2901667 LA_46 6946 2902019 LB_46 = true := by decide +kernel
  have g_46 : Good fA 9823 LA_46 ∧ Good fB 6947 LB_46 :=
    chk2_sound (by norm_num [NMax]) ck_46
      (g_45.1.count_eq (i := 106) (by decide +kernel) (by decide +kernel))
      (g_45.2.count_eq (i := 75) (by decide +kernel) (by decide +kernel))
  have ck_47 : chk2 49283072 1081344 9928 2960786 LA_47 7021 2961184 LB_47 = true := by decide +kernel
  have g_47 : Good fA 9929 LA_47 ∧ Good fB 7022 LB_47 :=
    chk2_sound (by norm_num [NMax]) ck_47
      (g_46.1.count_eq (i := 105) (by decide +kernel) (by decide +kernel))
      (g_46.2.count_eq (i := 74) (by decide +kernel) (by decide +kernel))
  have ck_48 : chk2 50331648 1081344 10033 3020048 LA_48 7095 3020247 LB_48 = true := by decide +kernel
  have g_48 : Good fA 10034 LA_48 ∧ Good fB 7096 LB_48 :=
    chk2_sound (by norm_num [NMax]) ck_48
      (g_47.1.count_eq (i := 104) (by decide +kernel) (by decide +kernel))
      (g_47.2.count_eq (i := 73) (by decide +kernel) (by decide +kernel))
  have ck_49 : chk2 51380224 1081344 10137 3079149 LA_49 7168 3078902 LB_49 = true := by decide +kernel
  have g_49 : Good fA 10138 LA_49 ∧ Good fB 7169 LB_49 :=
    chk2_sound (by norm_num [NMax]) ck_49
      (g_48.1.count_eq (i := 103) (by decide +kernel) (by decide +kernel))
      (g_48.2.count_eq (i := 72) (by decide +kernel) (by decide +kernel))
  have ck_50 : chk2 52428800 1081344 10240 3138200 LA_50 7241 3138091 LB_50 = true := by decide +kernel
  have g_50 : Good fA 10241 LA_50 ∧ Good fB 7242 LB_50 :=
    chk2_sound (by norm_num [NMax]) ck_50
      (g_49.1.count_eq (i := 102) (by decide +kernel) (by decide +kernel))
      (g_49.2.count_eq (i := 72) (by decide +kernel) (by decide +kernel))
  have ck_51 : chk2 53477376 1081344 10342 3197208 LA_51 7313 3197012 LB_51 = true := by decide +kernel
  have g_51 : Good fA 10343 LA_51 ∧ Good fB 7314 LB_51 :=
    chk2_sound (by norm_num [NMax]) ck_51
      (g_50.1.count_eq (i := 101) (by decide +kernel) (by decide +kernel))
      (g_50.2.count_eq (i := 71) (by decide +kernel) (by decide +kernel))
  have ck_52 : chk2 54525952 1081344 10443 3256051 LA_52 7385 3256332 LB_52 = true := by decide +kernel
  have g_52 : Good fA 10444 LA_52 ∧ Good fB 7386 LB_52 :=
    chk2_sound (by norm_num [NMax]) ck_52
      (g_51.1.count_eq (i := 100) (by decide +kernel) (by decide +kernel))
      (g_51.2.count_eq (i := 71) (by decide +kernel) (by decide +kernel))
  have ck_53 : chk2 55574528 1081344 10543 3314869 LA_53 7455 3314554 LB_53 = true := by decide +kernel
  have g_53 : Good fA 10544 LA_53 ∧ Good fB 7456 LB_53 :=
    chk2_sound (by norm_num [NMax]) ck_53
      (g_52.1.count_eq (i := 99) (by decide +kernel) (by decide +kernel))
      (g_52.2.count_eq (i := 69) (by decide +kernel) (by decide +kernel))
  have ck_54 : chk2 56623104 1081344 10642 3373692 LA_54 7525 3373381 LB_54 = true := by decide +kernel
  have g_54 : Good fA 10643 LA_54 ∧ Good fB 7526 LB_54 :=
    chk2_sound (by norm_num [NMax]) ck_54
      (g_53.1.count_eq (i := 98) (by decide +kernel) (by decide +kernel))
      (g_53.2.count_eq (i := 69) (by decide +kernel) (by decide +kernel))
  have ck_55 : chk2 57671680 1081344 10740 3432481 LA_55 7595 3432759 LB_55 = true := by decide +kernel
  have g_55 : Good fA 10741 LA_55 ∧ Good fB 7596 LB_55 :=
    chk2_sound (by norm_num [NMax]) ck_55
      (g_54.1.count_eq (i := 97) (by decide +kernel) (by decide +kernel))
      (g_54.2.count_eq (i := 69) (by decide +kernel) (by decide +kernel))
  have ck_56 : chk2 58720256 1081344 10837 3490964 LA_56 7663 3490734 LB_56 = true := by decide +kernel
  have g_56 : Good fA 10838 LA_56 ∧ Good fB 7664 LB_56 :=
    chk2_sound (by norm_num [NMax]) ck_56
      (g_55.1.count_eq (i := 96) (by decide +kernel) (by decide +kernel))
      (g_55.2.count_eq (i := 67) (by decide +kernel) (by decide +kernel))
  have ck_57 : chk2 59768832 1081344 10933 3549300 LA_57 7732 3550044 LB_57 = true := by decide +kernel
  have g_57 : Good fA 10934 LA_57 ∧ Good fB 7733 LB_57 :=
    chk2_sound (by norm_num [NMax]) ck_57
      (g_56.1.count_eq (i := 95) (by decide +kernel) (by decide +kernel))
      (g_56.2.count_eq (i := 68) (by decide +kernel) (by decide +kernel))
  have ck_58 : chk2 60817408 1081344 11029 3608240 LA_58 7799 3608211 LB_58 = true := by decide +kernel
  have g_58 : Good fA 11030 LA_58 ∧ Good fB 7800 LB_58 :=
    chk2_sound (by norm_num [NMax]) ck_58
      (g_57.1.count_eq (i := 95) (by decide +kernel) (by decide +kernel))
      (g_57.2.count_eq (i := 66) (by decide +kernel) (by decide +kernel))
  have ck_59 : chk2 61865984 1081344 11123 3666139 LA_59 7866 3666576 LB_59 = true := by decide +kernel
  have g_59 : Good fA 11124 LA_59 ∧ Good fB 7867 LB_59 :=
    chk2_sound (by norm_num [NMax]) ck_59
      (g_58.1.count_eq (i := 93) (by decide +kernel) (by decide +kernel))
      (g_58.2.count_eq (i := 66) (by decide +kernel) (by decide +kernel))
  have ck_60 : chk2 62914560 1081344 11217 3724673 LA_60 7932 3724694 LB_60 = true := by decide +kernel
  have g_60 : Good fA 11218 LA_60 ∧ Good fB 7933 LB_60 :=
    chk2_sound (by norm_num [NMax]) ck_60
      (g_59.1.count_eq (i := 93) (by decide +kernel) (by decide +kernel))
      (g_59.2.count_eq (i := 65) (by decide +kernel) (by decide +kernel))
  have ck_61 : chk2 63963136 1081344 11310 3783069 LA_61 7998 3783314 LB_61 = true := by decide +kernel
  have g_61 : Good fA 11311 LA_61 ∧ Good fB 7999 LB_61 :=
    chk2_sound (by norm_num [NMax]) ck_61
      (g_60.1.count_eq (i := 92) (by decide +kernel) (by decide +kernel))
      (g_60.2.count_eq (i := 65) (by decide +kernel) (by decide +kernel))
  have ck_62 : chk2 65011712 1081344 11403 3841668 LA_62 8063 3841215 LB_62 = true := by decide +kernel
  have g_62 : Good fA 11404 LA_62 ∧ Good fB 8064 LB_62 :=
    chk2_sound (by norm_num [NMax]) ck_62
      (g_61.1.count_eq (i := 92) (by decide +kernel) (by decide +kernel))
      (g_61.2.count_eq (i := 64) (by decide +kernel) (by decide +kernel))
  have ck_63 : chk2 66060288 1081344 11494 3899607 LA_63 8128 3899761 LB_63 = true := by decide +kernel
  have g_63 : Good fA 11495 LA_63 ∧ Good fB 8129 LB_63 :=
    chk2_sound (by norm_num [NMax]) ck_63
      (g_62.1.count_eq (i := 90) (by decide +kernel) (by decide +kernel))
      (g_62.2.count_eq (i := 64) (by decide +kernel) (by decide +kernel))
  have ck_64 : chk2 67108864 1081344 11585 3957973 LA_64 8192 3957809 LB_64 = true := by decide +kernel
  have g_64 : Good fA 11586 LA_64 ∧ Good fB 8193 LB_64 :=
    chk2_sound (by norm_num [NMax]) ck_64
      (g_63.1.count_eq (i := 90) (by decide +kernel) (by decide +kernel))
      (g_63.2.count_eq (i := 63) (by decide +kernel) (by decide +kernel))
  have ck_65 : chk2 68157440 1081344 11675 4016108 LA_65 8256 4016265 LB_65 = true := by decide +kernel
  have g_65 : Good fA 11676 LA_65 ∧ Good fB 8257 LB_65 :=
    chk2_sound (by norm_num [NMax]) ck_65
      (g_64.1.count_eq (i := 89) (by decide +kernel) (by decide +kernel))
      (g_64.2.count_eq (i := 63) (by decide +kernel) (by decide +kernel))
  have ck_66 : chk2 69206016 1081344 11765 4074480 LA_66 8320 4074960 LB_66 = true := by decide +kernel
  have g_66 : Good fA 11766 LA_66 ∧ Good fB 8321 LB_66 :=
    chk2_sound (by norm_num [NMax]) ck_66
      (g_65.1.count_eq (i := 89) (by decide +kernel) (by decide +kernel))
      (g_65.2.count_eq (i := 63) (by decide +kernel) (by decide +kernel))
  have ck_67 : chk2 70254592 1081344 11854 4132716 LA_67 8382 4132346 LB_67 = true := by decide +kernel
  have g_67 : Good fA 11855 LA_67 ∧ Good fB 8383 LB_67 :=
    chk2_sound (by norm_num [NMax]) ck_67
      (g_66.1.count_eq (i := 88) (by decide +kernel) (by decide +kernel))
      (g_66.2.count_eq (i := 61) (by decide +kernel) (by decide +kernel))
  have ck_68 : chk2 71303168 1081344 11942 4190616 LA_68 8445 4190971 LB_68 = true := by decide +kernel
  have g_68 : Good fA 11943 LA_68 ∧ Good fB 8446 LB_68 :=
    chk2_sound (by norm_num [NMax]) ck_68
      (g_67.1.count_eq (i := 87) (by decide +kernel) (by decide +kernel))
      (g_67.2.count_eq (i := 62) (by decide +kernel) (by decide +kernel))
  have ck_69 : chk2 72351744 1081344 12029 4248408 LA_69 8506 4248286 LB_69 = true := by decide +kernel
  have g_69 : Good fA 12030 LA_69 ∧ Good fB 8507 LB_69 :=
    chk2_sound (by norm_num [NMax]) ck_69
      (g_68.1.count_eq (i := 86) (by decide +kernel) (by decide +kernel))
      (g_68.2.count_eq (i := 60) (by decide +kernel) (by decide +kernel))
  have ck_70 : chk2 73400320 1081344 12116 4306379 LA_70 8568 4306691 LB_70 = true := by decide +kernel
  have g_70 : Good fA 12117 LA_70 ∧ Good fB 8569 LB_70 :=
    chk2_sound (by norm_num [NMax]) ck_70
      (g_69.1.count_eq (i := 86) (by decide +kernel) (by decide +kernel))
      (g_69.2.count_eq (i := 61) (by decide +kernel) (by decide +kernel))
  have ck_71 : chk2 74448896 1081344 12202 4364029 LA_71 8629 4364533 LB_71 = true := by decide +kernel
  have g_71 : Good fA 12203 LA_71 ∧ Good fB 8630 LB_71 :=
    chk2_sound (by norm_num [NMax]) ck_71
      (g_70.1.count_eq (i := 85) (by decide +kernel) (by decide +kernel))
      (g_70.2.count_eq (i := 60) (by decide +kernel) (by decide +kernel))
  have ck_72 : chk2 75497472 1081344 12288 4422178 LA_72 8689 4421893 LB_72 = true := by decide +kernel
  have g_72 : Good fA 12289 LA_72 ∧ Good fB 8690 LB_72 :=
    chk2_sound (by norm_num [NMax]) ck_72
      (g_71.1.count_eq (i := 85) (by decide +kernel) (by decide +kernel))
      (g_71.2.count_eq (i := 59) (by decide +kernel) (by decide +kernel))
  have ck_73 : chk2 76546048 1081344 12373 4479895 LA_73 8750 4480501 LB_73 = true := by decide +kernel
  have g_73 : Good fA 12374 LA_73 ∧ Good fB 8751 LB_73 :=
    chk2_sound (by norm_num [NMax]) ck_73
      (g_72.1.count_eq (i := 84) (by decide +kernel) (by decide +kernel))
      (g_72.2.count_eq (i := 60) (by decide +kernel) (by decide +kernel))
  have ck_74 : chk2 77594624 1081344 12457 4537277 LA_74 8809 4537472 LB_74 = true := by decide +kernel
  have g_74 : Good fA 12458 LA_74 ∧ Good fB 8810 LB_74 :=
    chk2_sound (by norm_num [NMax]) ck_74
      (g_73.1.count_eq (i := 83) (by decide +kernel) (by decide +kernel))
      (g_73.2.count_eq (i := 58) (by decide +kernel) (by decide +kernel))
  have ck_75 : chk2 78643200 1081344 12541 4594913 LA_75 8869 4595730 LB_75 = true := by decide +kernel
  have g_75 : Good fA 12542 LA_75 ∧ Good fB 8870 LB_75 :=
    chk2_sound (by norm_num [NMax]) ck_75
      (g_74.1.count_eq (i := 83) (by decide +kernel) (by decide +kernel))
      (g_74.2.count_eq (i := 59) (by decide +kernel) (by decide +kernel))
  have ck_76 : chk2 79691776 1081344 12625 4653021 LA_76 8928 4653450 LB_76 = true := by decide +kernel
  have g_76 : Good fA 12626 LA_76 ∧ Good fB 8929 LB_76 :=
    chk2_sound (by norm_num [NMax]) ck_76
      (g_75.1.count_eq (i := 83) (by decide +kernel) (by decide +kernel))
      (g_75.2.count_eq (i := 58) (by decide +kernel) (by decide +kernel))
  have ck_77 : chk2 80740352 1081344 12708 4710770 LA_77 8986 4710494 LB_77 = true := by decide +kernel
  have g_77 : Good fA 12709 LA_77 ∧ Good fB 8987 LB_77 :=
    chk2_sound (by norm_num [NMax]) ck_77
      (g_76.1.count_eq (i := 82) (by decide +kernel) (by decide +kernel))
      (g_76.2.count_eq (i := 57) (by decide +kernel) (by decide +kernel))
  have ck_78 : chk2 81788928 1081344 12790 4768313 LA_78 9044 4768060 LB_78 = true := by decide +kernel
  have g_78 : Good fA 12791 LA_78 ∧ Good fB 9045 LB_78 :=
    chk2_sound (by norm_num [NMax]) ck_78
      (g_77.1.count_eq (i := 81) (by decide +kernel) (by decide +kernel))
      (g_77.2.count_eq (i := 57) (by decide +kernel) (by decide +kernel))
  have ck_79 : chk2 82837504 1081344 12871 4825392 LA_79 9102 4825873 LB_79 = true := by decide +kernel
  have g_79 : Good fA 12872 LA_79 ∧ Good fB 9103 LB_79 :=
    chk2_sound (by norm_num [NMax]) ck_79
      (g_78.1.count_eq (i := 80) (by decide +kernel) (by decide +kernel))
      (g_78.2.count_eq (i := 57) (by decide +kernel) (by decide +kernel))
  have ck_80 : chk2 83886080 1081344 12953 4883383 LA_80 9159 4882871 LB_80 = true := by decide +kernel
  have g_80 : Good fA 12954 LA_80 ∧ Good fB 9160 LB_80 :=
    chk2_sound (by norm_num [NMax]) ck_80
      (g_79.1.count_eq (i := 81) (by decide +kernel) (by decide +kernel))
      (g_79.2.count_eq (i := 56) (by decide +kernel) (by decide +kernel))
  have ck_81 : chk2 84934656 1081344 13033 4940196 LA_81 9216 4940115 LB_81 = true := by decide +kernel
  have g_81 : Good fA 13034 LA_81 ∧ Good fB 9217 LB_81 :=
    chk2_sound (by norm_num [NMax]) ck_81
      (g_80.1.count_eq (i := 79) (by decide +kernel) (by decide +kernel))
      (g_80.2.count_eq (i := 56) (by decide +kernel) (by decide +kernel))
  have ck_82 : chk2 85983232 1081344 13114 4998221 LA_82 9273 4997850 LB_82 = true := by decide +kernel
  have g_82 : Good fA 13115 LA_82 ∧ Good fB 9274 LB_82 :=
    chk2_sound (by norm_num [NMax]) ck_82
      (g_81.1.count_eq (i := 80) (by decide +kernel) (by decide +kernel))
      (g_81.2.count_eq (i := 56) (by decide +kernel) (by decide +kernel))
  have ck_83 : chk2 87031808 1081344 13193 5055089 LA_83 9330 5055885 LB_83 = true := by decide +kernel
  have g_83 : Good fA 13194 LA_83 ∧ Good fB 9331 LB_83 :=
    chk2_sound (by norm_num [NMax]) ck_83
      (g_82.1.count_eq (i := 78) (by decide +kernel) (by decide +kernel))
      (g_82.2.count_eq (i := 56) (by decide +kernel) (by decide +kernel))
  have ck_84 : chk2 88080384 1081344 13273 5112987 LA_84 9386 5113190 LB_84 = true := by decide +kernel
  have g_84 : Good fA 13274 LA_84 ∧ Good fB 9387 LB_84 :=
    chk2_sound (by norm_num [NMax]) ck_84
      (g_83.1.count_eq (i := 79) (by decide +kernel) (by decide +kernel))
      (g_83.2.count_eq (i := 55) (by decide +kernel) (by decide +kernel))
  have ck_85 : chk2 89128960 1081344 13351 5169697 LA_85 9441 5169759 LB_85 = true := by decide +kernel
  have g_85 : Good fA 13352 LA_85 ∧ Good fB 9442 LB_85 :=
    chk2_sound (by norm_num [NMax]) ck_85
      (g_84.1.count_eq (i := 77) (by decide +kernel) (by decide +kernel))
      (g_84.2.count_eq (i := 54) (by decide +kernel) (by decide +kernel))
  have ck_86 : chk2 90177536 1081344 13430 5227389 LA_86 9497 5227600 LB_86 = true := by decide +kernel
  have g_86 : Good fA 13431 LA_86 ∧ Good fB 9498 LB_86 :=
    chk2_sound (by norm_num [NMax]) ck_86
      (g_85.1.count_eq (i := 78) (by decide +kernel) (by decide +kernel))
      (g_85.2.count_eq (i := 55) (by decide +kernel) (by decide +kernel))
  have ck_87 : chk2 91226112 1081344 13507 5284048 LA_87 9552 5284836 LB_87 = true := by decide +kernel
  have g_87 : Good fA 13508 LA_87 ∧ Good fB 9553 LB_87 :=
    chk2_sound (by norm_num [NMax]) ck_87
      (g_86.1.count_eq (i := 76) (by decide +kernel) (by decide +kernel))
      (g_86.2.count_eq (i := 54) (by decide +kernel) (by decide +kernel))
  have ck_88 : chk2 92274688 1081344 13585 5341632 LA_88 9606 5341226 LB_88 = true := by decide +kernel
  have g_88 : Good fA 13586 LA_88 ∧ Good fB 9607 LB_88 :=
    chk2_sound (by norm_num [NMax]) ck_88
      (g_87.1.count_eq (i := 77) (by decide +kernel) (by decide +kernel))
      (g_87.2.count_eq (i := 53) (by decide +kernel) (by decide +kernel))
  have ck_89 : chk2 93323264 1081344 13662 5398741 LA_89 9661 5398898 LB_89 = true := by decide +kernel
  have g_89 : Good fA 13663 LA_89 ∧ Good fB 9662 LB_89 :=
    chk2_sound (by norm_num [NMax]) ck_89
      (g_88.1.count_eq (i := 76) (by decide +kernel) (by decide +kernel))
      (g_88.2.count_eq (i := 54) (by decide +kernel) (by decide +kernel))
  have ck_90 : chk2 94371840 1081344 13738 5455450 LA_90 9715 5455902 LB_90 = true := by decide +kernel
  have g_90 : Good fA 13739 LA_90 ∧ Good fB 9716 LB_90 :=
    chk2_sound (by norm_num [NMax]) ck_90
      (g_89.1.count_eq (i := 75) (by decide +kernel) (by decide +kernel))
      (g_89.2.count_eq (i := 53) (by decide +kernel) (by decide +kernel))
  have ck_91 : chk2 95420416 1081344 13815 5513365 LA_91 9769 5513324 LB_91 = true := by decide +kernel
  have g_91 : Good fA 13816 LA_91 ∧ Good fB 9770 LB_91 :=
    chk2_sound (by norm_num [NMax]) ck_91
      (g_90.1.count_eq (i := 76) (by decide +kernel) (by decide +kernel))
      (g_90.2.count_eq (i := 53) (by decide +kernel) (by decide +kernel))
  have ck_92 : chk2 96468992 1081344 13890 5569846 LA_92 9822 5569770 LB_92 = true := by decide +kernel
  have g_92 : Good fA 13891 LA_92 ∧ Good fB 9823 LB_92 :=
    chk2_sound (by norm_num [NMax]) ck_92
      (g_91.1.count_eq (i := 74) (by decide +kernel) (by decide +kernel))
      (g_91.2.count_eq (i := 52) (by decide +kernel) (by decide +kernel))
  have ck_93 : chk2 97517568 1081344 13965 5626705 LA_93 9876 5627671 LB_93 = true := by decide +kernel
  have g_93 : Good fA 13966 LA_93 ∧ Good fB 9877 LB_93 :=
    chk2_sound (by norm_num [NMax]) ck_93
      (g_92.1.count_eq (i := 74) (by decide +kernel) (by decide +kernel))
      (g_92.2.count_eq (i := 53) (by decide +kernel) (by decide +kernel))
  have ck_94 : chk2 98566144 1081344 14040 5683843 LA_94 9929 5684788 LB_94 = true := by decide +kernel
  have g_94 : Good fA 14041 LA_94 ∧ Good fB 9930 LB_94 :=
    chk2_sound (by norm_num [NMax]) ck_94
      (g_93.1.count_eq (i := 74) (by decide +kernel) (by decide +kernel))
      (g_93.2.count_eq (i := 52) (by decide +kernel) (by decide +kernel))
  have ck_95 : chk2 99614720 1081344 14115 5741078 LA_95 9981 5740894 LB_95 = true := by decide +kernel
  have g_95 : Good fA 14116 LA_95 ∧ Good fB 9982 LB_95 :=
    chk2_sound (by norm_num [NMax]) ck_95
      (g_94.1.count_eq (i := 74) (by decide +kernel) (by decide +kernel))
      (g_94.2.count_eq (i := 51) (by decide +kernel) (by decide +kernel))
  have ck_96 : chk2 100663296 1081344 14189 5797822 LA_96 10034 5798347 LB_96 = true := by decide +kernel
  have g_96 : Good fA 14190 LA_96 ∧ Good fB 10035 LB_96 :=
    chk2_sound (by norm_num [NMax]) ck_96
      (g_95.1.count_eq (i := 73) (by decide +kernel) (by decide +kernel))
      (g_95.2.count_eq (i := 52) (by decide +kernel) (by decide +kernel))
  have ck_97 : chk2 101711872 1081344 14263 5854932 LA_97 10086 5855132 LB_97 = true := by decide +kernel
  have g_97 : Good fA 14264 LA_97 ∧ Good fB 10087 LB_97 :=
    chk2_sound (by norm_num [NMax]) ck_97
      (g_96.1.count_eq (i := 73) (by decide +kernel) (by decide +kernel))
      (g_96.2.count_eq (i := 51) (by decide +kernel) (by decide +kernel))
  have ck_98 : chk2 102760448 1081344 14336 5911713 LA_98 10138 5912318 LB_98 = true := by decide +kernel
  have g_98 : Good fA 14337 LA_98 ∧ Good fB 10139 LB_98 :=
    chk2_sound (by norm_num [NMax]) ck_98
      (g_97.1.count_eq (i := 72) (by decide +kernel) (by decide +kernel))
      (g_97.2.count_eq (i := 51) (by decide +kernel) (by decide +kernel))
  have ck_99 : chk2 103809024 1081344 14409 5968491 LA_99 10189 5968439 LB_99 = true := by decide +kernel
  have g_99 : Good fA 14410 LA_99 ∧ Good fB 10190 LB_99 :=
    chk2_sound (by norm_num [NMax]) ck_99
      (g_98.1.count_eq (i := 72) (by decide +kernel) (by decide +kernel))
      (g_98.2.count_eq (i := 50) (by decide +kernel) (by decide +kernel))
  have ck_100 : chk2 104857600 1081344 14482 6025761 LA_100 10240 6025009 LB_100 = true := by decide +kernel
  have g_100 : Good fA 14483 LA_100 ∧ Good fB 10241 LB_100 :=
    chk2_sound (by norm_num [NMax]) ck_100
      (g_99.1.count_eq (i := 72) (by decide +kernel) (by decide +kernel))
      (g_99.2.count_eq (i := 50) (by decide +kernel) (by decide +kernel))
  have ck_101 : chk2 105906176 1081344 14554 6082307 LA_101 10292 6082761 LB_101 = true := by decide +kernel
  have g_101 : Good fA 14555 LA_101 ∧ Good fB 10293 LB_101 :=
    chk2_sound (by norm_num [NMax]) ck_101
      (g_100.1.count_eq (i := 71) (by decide +kernel) (by decide +kernel))
      (g_100.2.count_eq (i := 51) (by decide +kernel) (by decide +kernel))
  have ck_102 : chk2 106954752 1081344 14626 6139052 LA_102 10342 6138482 LB_102 = true := by decide +kernel
  have g_102 : Good fA 14627 LA_102 ∧ Good fB 10343 LB_102 :=
    chk2_sound (by norm_num [NMax]) ck_102
      (g_101.1.count_eq (i := 71) (by decide +kernel) (by decide +kernel))
      (g_101.2.count_eq (i := 49) (by decide +kernel) (by decide +kernel))
  have ck_103 : chk2 108003328 1081344 14697 6195388 LA_103 10393 6195709 LB_103 = true := by decide +kernel
  have g_103 : Good fA 14698 LA_103 ∧ Good fB 10394 LB_103 :=
    chk2_sound (by norm_num [NMax]) ck_103
      (g_102.1.count_eq (i := 70) (by decide +kernel) (by decide +kernel))
      (g_102.2.count_eq (i := 50) (by decide +kernel) (by decide +kernel))
  have ck_104 : chk2 109051904 1081344 14768 6252102 LA_104 10443 6252198 LB_104 = true := by decide +kernel
  have g_104 : Good fA 14769 LA_104 ∧ Good fB 10444 LB_104 :=
    chk2_sound (by norm_num [NMax]) ck_104
      (g_103.1.count_eq (i := 70) (by decide +kernel) (by decide +kernel))
      (g_103.2.count_eq (i := 49) (by decide +kernel) (by decide +kernel))
  have ck_105 : chk2 110100480 1081344 14839 6309098 LA_105 10493 6308977 LB_105 = true := by decide +kernel
  have g_105 : Good fA 14840 LA_105 ∧ Good fB 10494 LB_105 :=
    chk2_sound (by norm_num [NMax]) ck_105
      (g_104.1.count_eq (i := 70) (by decide +kernel) (by decide +kernel))
      (g_104.2.count_eq (i := 49) (by decide +kernel) (by decide +kernel))
  have ck_106 : chk2 111149056 1081344 14910 6365918 LA_106 10543 6365543 LB_106 = true := by decide +kernel
  have g_106 : Good fA 14911 LA_106 ∧ Good fB 10544 LB_106 :=
    chk2_sound (by norm_num [NMax]) ck_106
      (g_105.1.count_eq (i := 70) (by decide +kernel) (by decide +kernel))
      (g_105.2.count_eq (i := 49) (by decide +kernel) (by decide +kernel))
  have ck_107 : chk2 112197632 1081344 14980 6422410 LA_107 10593 6422614 LB_107 = true := by decide +kernel
  have g_107 : Good fA 14981 LA_107 ∧ Good fB 10594 LB_107 :=
    chk2_sound (by norm_num [NMax]) ck_107
      (g_106.1.count_eq (i := 69) (by decide +kernel) (by decide +kernel))
      (g_106.2.count_eq (i := 49) (by decide +kernel) (by decide +kernel))
  have ck_108 : chk2 113246208 1081344 15050 6479075 LA_108 10642 6478730 LB_108 = true := by decide +kernel
  have g_108 : Good fA 15051 LA_108 ∧ Good fB 10643 LB_108 :=
    chk2_sound (by norm_num [NMax]) ck_108
      (g_107.1.count_eq (i := 69) (by decide +kernel) (by decide +kernel))
      (g_107.2.count_eq (i := 48) (by decide +kernel) (by decide +kernel))
  have ck_109 : chk2 114294784 1081344 15119 6535018 LA_109 10691 6534902 LB_109 = true := by decide +kernel
  have g_109 : Good fA 15120 LA_109 ∧ Good fB 10692 LB_109 :=
    chk2_sound (by norm_num [NMax]) ck_109
      (g_108.1.count_eq (i := 68) (by decide +kernel) (by decide +kernel))
      (g_108.2.count_eq (i := 48) (by decide +kernel) (by decide +kernel))
  have ck_110 : chk2 115343360 1081344 15188 6591255 LA_110 10740 6591377 LB_110 = true := by decide +kernel
  have g_110 : Good fA 15189 LA_110 ∧ Good fB 10741 LB_110 :=
    chk2_sound (by norm_num [NMax]) ck_110
      (g_109.1.count_eq (i := 68) (by decide +kernel) (by decide +kernel))
      (g_109.2.count_eq (i := 48) (by decide +kernel) (by decide +kernel))
  have ck_111 : chk2 116391936 1081344 15257 6647931 LA_111 10789 6648315 LB_111 = true := by decide +kernel
  have g_111 : Good fA 15258 LA_111 ∧ Good fB 10790 LB_111 :=
    chk2_sound (by norm_num [NMax]) ck_111
      (g_110.1.count_eq (i := 68) (by decide +kernel) (by decide +kernel))
      (g_110.2.count_eq (i := 48) (by decide +kernel) (by decide +kernel))
  have ck_112 : chk2 117440512 1081344 15326 6704641 LA_112 10837 6704097 LB_112 = true := by decide +kernel
  have g_112 : Good fA 15327 LA_112 ∧ Good fB 10838 LB_112 :=
    chk2_sound (by norm_num [NMax]) ck_112
      (g_111.1.count_eq (i := 68) (by decide +kernel) (by decide +kernel))
      (g_111.2.count_eq (i := 47) (by decide +kernel) (by decide +kernel))
  have ck_113 : chk2 118489088 1081344 15394 6760882 LA_113 10886 6761403 LB_113 = true := by decide +kernel
  have g_113 : Good fA 15395 LA_113 ∧ Good fB 10887 LB_113 :=
    chk2_sound (by norm_num [NMax]) ck_113
      (g_112.1.count_eq (i := 67) (by decide +kernel) (by decide +kernel))
      (g_112.2.count_eq (i := 48) (by decide +kernel) (by decide +kernel))
  have ck_114 : chk2 119537664 1081344 15462 6817111 LA_114 10934 6817535 LB_114 = true := by decide +kernel
  have g_114 : Good fA 15463 LA_114 ∧ Good fB 10935 LB_114 :=
    chk2_sound (by norm_num [NMax]) ck_114
      (g_113.1.count_eq (i := 67) (by decide +kernel) (by decide +kernel))
      (g_113.2.count_eq (i := 47) (by decide +kernel) (by decide +kernel))
  have ck_115 : chk2 120586240 1081344 15530 6873756 LA_115 10982 6874085 LB_115 = true := by decide +kernel
  have g_115 : Good fA 15531 LA_115 ∧ Good fB 10983 LB_115 :=
    chk2_sound (by norm_num [NMax]) ck_115
      (g_114.1.count_eq (i := 67) (by decide +kernel) (by decide +kernel))
      (g_114.2.count_eq (i := 47) (by decide +kernel) (by decide +kernel))
  have ck_116 : chk2 121634816 1081344 15597 6929741 LA_116 11029 6929631 LB_116 = true := by decide +kernel
  have g_116 : Good fA 15598 LA_116 ∧ Good fB 11030 LB_116 :=
    chk2_sound (by norm_num [NMax]) ck_116
      (g_115.1.count_eq (i := 66) (by decide +kernel) (by decide +kernel))
      (g_115.2.count_eq (i := 46) (by decide +kernel) (by decide +kernel))
  have ck_117 : chk2 122683392 1081344 15664 6985882 LA_117 11077 6986517 LB_117 = true := by decide +kernel
  have g_117 : Good fA 15665 LA_117 ∧ Good fB 11078 LB_117 :=
    chk2_sound (by norm_num [NMax]) ck_117
      (g_116.1.count_eq (i := 66) (by decide +kernel) (by decide +kernel))
      (g_116.2.count_eq (i := 47) (by decide +kernel) (by decide +kernel))
  have ck_118 : chk2 123731968 1081344 15731 7042445 LA_118 11124 7042627 LB_118 = true := by decide +kernel
  have g_118 : Good fA 15732 LA_118 ∧ Good fB 11125 LB_118 :=
    chk2_sound (by norm_num [NMax]) ck_118
      (g_117.1.count_eq (i := 66) (by decide +kernel) (by decide +kernel))
      (g_117.2.count_eq (i := 46) (by decide +kernel) (by decide +kernel))
  have ck_119 : chk2 124780544 1081344 15798 7099209 LA_119 11171 7098958 LB_119 = true := by decide +kernel
  have g_119 : Good fA 15799 LA_119 ∧ Good fB 11172 LB_119 :=
    chk2_sound (by norm_num [NMax]) ck_119
      (g_118.1.count_eq (i := 66) (by decide +kernel) (by decide +kernel))
      (g_118.2.count_eq (i := 46) (by decide +kernel) (by decide +kernel))
  have ck_120 : chk2 125829120 1081344 15864 7155270 LA_120 11218 7155403 LB_120 = true := by decide +kernel
  have g_120 : Good fA 15865 LA_120 ∧ Good fB 11219 LB_120 :=
    chk2_sound (by norm_num [NMax]) ck_120
      (g_119.1.count_eq (i := 65) (by decide +kernel) (by decide +kernel))
      (g_119.2.count_eq (i := 46) (by decide +kernel) (by decide +kernel))
  have ck_121 : chk2 126877696 1081344 15930 7211588 LA_121 11264 7210877 LB_121 = true := by decide +kernel
  have g_121 : Good fA 15931 LA_121 ∧ Good fB 11265 LB_121 :=
    chk2_sound (by norm_num [NMax]) ck_121
      (g_120.1.count_eq (i := 65) (by decide +kernel) (by decide +kernel))
      (g_120.2.count_eq (i := 45) (by decide +kernel) (by decide +kernel))
  have ck_122 : chk2 127926272 1081344 15995 7267108 LA_122 11311 7267668 LB_122 = true := by decide +kernel
  have g_122 : Good fA 15996 LA_122 ∧ Good fB 11312 LB_122 :=
    chk2_sound (by norm_num [NMax]) ck_122
      (g_121.1.count_eq (i := 64) (by decide +kernel) (by decide +kernel))
      (g_121.2.count_eq (i := 46) (by decide +kernel) (by decide +kernel))
  have ck_123 : chk2 128974848 1081344 16061 7323958 LA_123 11357 7323711 LB_123 = true := by decide +kernel
  have g_123 : Good fA 16062 LA_123 ∧ Good fB 11358 LB_123 :=
    chk2_sound (by norm_num [NMax]) ck_123
      (g_122.1.count_eq (i := 65) (by decide +kernel) (by decide +kernel))
      (g_122.2.count_eq (i := 45) (by decide +kernel) (by decide +kernel))
  have ck_124 : chk2 130023424 1081344 16126 7379899 LA_124 11403 7379685 LB_124 = true := by decide +kernel
  have g_124 : Good fA 16127 LA_124 ∧ Good fB 11404 LB_124 :=
    chk2_sound (by norm_num [NMax]) ck_124
      (g_123.1.count_eq (i := 64) (by decide +kernel) (by decide +kernel))
      (g_123.2.count_eq (i := 45) (by decide +kernel) (by decide +kernel))
  have ck_125 : chk2 131072000 1081344 16191 7436133 LA_125 11449 7436001 LB_125 = true := by decide +kernel
  have g_125 : Good fA 16192 LA_125 ∧ Good fB 11450 LB_125 :=
    chk2_sound (by norm_num [NMax]) ck_125
      (g_124.1.count_eq (i := 64) (by decide +kernel) (by decide +kernel))
      (g_124.2.count_eq (i := 45) (by decide +kernel) (by decide +kernel))
  have ck_126 : chk2 132120576 1081344 16255 7491587 LA_126 11495 7492336 LB_126 = true := by decide +kernel
  have g_126 : Good fA 16256 LA_126 ∧ Good fB 11496 LB_126 :=
    chk2_sound (by norm_num [NMax]) ck_126
      (g_125.1.count_eq (i := 63) (by decide +kernel) (by decide +kernel))
      (g_125.2.count_eq (i := 45) (by decide +kernel) (by decide +kernel))
  have ck_127 : chk2 133169152 1081344 16320 7548248 LA_127 11540 7547840 LB_127 = true := by decide +kernel
  have g_127 : Good fA 16321 LA_127 ∧ Good fB 11541 LB_127 :=
    chk2_sound (by norm_num [NMax]) ck_127
      (g_126.1.count_eq (i := 64) (by decide +kernel) (by decide +kernel))
      (g_126.2.count_eq (i := 44) (by decide +kernel) (by decide +kernel))
  have ck_128 : chk2 134217728 1081344 16384 7604005 LA_128 11586 7604542 LB_128 = true := by decide +kernel
  have g_128 : Good fA 16385 LA_128 ∧ Good fB 11587 LB_128 :=
    chk2_sound (by norm_num [NMax]) ck_128
      (g_127.1.count_eq (i := 63) (by decide +kernel) (by decide +kernel))
      (g_127.2.count_eq (i := 45) (by decide +kernel) (by decide +kernel))
  have ck_129 : chk2 135266304 1081344 16448 7660238 LA_129 11631 7660438 LB_129 = true := by decide +kernel
  have g_129 : Good fA 16449 LA_129 ∧ Good fB 11632 LB_129 :=
    chk2_sound (by norm_num [NMax]) ck_129
      (g_128.1.count_eq (i := 63) (by decide +kernel) (by decide +kernel))
      (g_128.2.count_eq (i := 44) (by decide +kernel) (by decide +kernel))
  have ck_130 : chk2 136314880 1081344 16512 7716369 LA_130 11676 7716234 LB_130 = true := by decide +kernel
  have g_130 : Good fA 16513 LA_130 ∧ Good fB 11677 LB_130 :=
    chk2_sound (by norm_num [NMax]) ck_130
      (g_129.1.count_eq (i := 63) (by decide +kernel) (by decide +kernel))
      (g_129.2.count_eq (i := 44) (by decide +kernel) (by decide +kernel))
  have ck_131 : chk2 137363456 1081344 16575 7772113 LA_131 11721 7772551 LB_131 = true := by decide +kernel
  have g_131 : Good fA 16576 LA_131 ∧ Good fB 11722 LB_131 :=
    chk2_sound (by norm_num [NMax]) ck_131
      (g_130.1.count_eq (i := 62) (by decide +kernel) (by decide +kernel))
      (g_130.2.count_eq (i := 44) (by decide +kernel) (by decide +kernel))
  have ck_132 : chk2 138412032 1081344 16638 7827837 LA_132 11765 7827577 LB_132 = true := by decide +kernel
  have g_132 : Good fA 16639 LA_132 ∧ Good fB 11766 LB_132 :=
    chk2_sound (by norm_num [NMax]) ck_132
      (g_131.1.count_eq (i := 62) (by decide +kernel) (by decide +kernel))
      (g_131.2.count_eq (i := 43) (by decide +kernel) (by decide +kernel))
  have GA_132 : Good fA 16639 TA_132 := g_132.1
  have GB_132 : Good fB 11766 TB_132 := g_132.2
  have GA_131 : Good fA 16576 TA_131 := Good.append g_131.1 GA_132 (by decide +kernel)
  have GB_131 : Good fB 11722 TB_131 := Good.append g_131.2 GB_132 (by decide +kernel)
  have GA_130 : Good fA 16513 TA_130 := Good.append g_130.1 GA_131 (by decide +kernel)
  have GB_130 : Good fB 11677 TB_130 := Good.append g_130.2 GB_131 (by decide +kernel)
  have GA_129 : Good fA 16449 TA_129 := Good.append g_129.1 GA_130 (by decide +kernel)
  have GB_129 : Good fB 11632 TB_129 := Good.append g_129.2 GB_130 (by decide +kernel)
  have GA_128 : Good fA 16385 TA_128 := Good.append g_128.1 GA_129 (by decide +kernel)
  have GB_128 : Good fB 11587 TB_128 := Good.append g_128.2 GB_129 (by decide +kernel)
  have GA_127 : Good fA 16321 TA_127 := Good.append g_127.1 GA_128 (by decide +kernel)
  have GB_127 : Good fB 11541 TB_127 := Good.append g_127.2 GB_128 (by decide +kernel)
  have GA_126 : Good fA 16256 TA_126 := Good.append g_126.1 GA_127 (by decide +kernel)
  have GB_126 : Good fB 11496 TB_126 := Good.append g_126.2 GB_127 (by decide +kernel)
  have GA_125 : Good fA 16192 TA_125 := Good.append g_125.1 GA_126 (by decide +kernel)
  have GB_125 : Good fB 11450 TB_125 := Good.append g_125.2 GB_126 (by decide +kernel)
  have GA_124 : Good fA 16127 TA_124 := Good.append g_124.1 GA_125 (by decide +kernel)
  have GB_124 : Good fB 11404 TB_124 := Good.append g_124.2 GB_125 (by decide +kernel)
  have GA_123 : Good fA 16062 TA_123 := Good.append g_123.1 GA_124 (by decide +kernel)
  have GB_123 : Good fB 11358 TB_123 := Good.append g_123.2 GB_124 (by decide +kernel)
  have GA_122 : Good fA 15996 TA_122 := Good.append g_122.1 GA_123 (by decide +kernel)
  have GB_122 : Good fB 11312 TB_122 := Good.append g_122.2 GB_123 (by decide +kernel)
  have GA_121 : Good fA 15931 TA_121 := Good.append g_121.1 GA_122 (by decide +kernel)
  have GB_121 : Good fB 11265 TB_121 := Good.append g_121.2 GB_122 (by decide +kernel)
  have GA_120 : Good fA 15865 TA_120 := Good.append g_120.1 GA_121 (by decide +kernel)
  have GB_120 : Good fB 11219 TB_120 := Good.append g_120.2 GB_121 (by decide +kernel)
  have GA_119 : Good fA 15799 TA_119 := Good.append g_119.1 GA_120 (by decide +kernel)
  have GB_119 : Good fB 11172 TB_119 := Good.append g_119.2 GB_120 (by decide +kernel)
  have GA_118 : Good fA 15732 TA_118 := Good.append g_118.1 GA_119 (by decide +kernel)
  have GB_118 : Good fB 11125 TB_118 := Good.append g_118.2 GB_119 (by decide +kernel)
  have GA_117 : Good fA 15665 TA_117 := Good.append g_117.1 GA_118 (by decide +kernel)
  have GB_117 : Good fB 11078 TB_117 := Good.append g_117.2 GB_118 (by decide +kernel)
  have GA_116 : Good fA 15598 TA_116 := Good.append g_116.1 GA_117 (by decide +kernel)
  have GB_116 : Good fB 11030 TB_116 := Good.append g_116.2 GB_117 (by decide +kernel)
  have GA_115 : Good fA 15531 TA_115 := Good.append g_115.1 GA_116 (by decide +kernel)
  have GB_115 : Good fB 10983 TB_115 := Good.append g_115.2 GB_116 (by decide +kernel)
  have GA_114 : Good fA 15463 TA_114 := Good.append g_114.1 GA_115 (by decide +kernel)
  have GB_114 : Good fB 10935 TB_114 := Good.append g_114.2 GB_115 (by decide +kernel)
  have GA_113 : Good fA 15395 TA_113 := Good.append g_113.1 GA_114 (by decide +kernel)
  have GB_113 : Good fB 10887 TB_113 := Good.append g_113.2 GB_114 (by decide +kernel)
  have GA_112 : Good fA 15327 TA_112 := Good.append g_112.1 GA_113 (by decide +kernel)
  have GB_112 : Good fB 10838 TB_112 := Good.append g_112.2 GB_113 (by decide +kernel)
  have GA_111 : Good fA 15258 TA_111 := Good.append g_111.1 GA_112 (by decide +kernel)
  have GB_111 : Good fB 10790 TB_111 := Good.append g_111.2 GB_112 (by decide +kernel)
  have GA_110 : Good fA 15189 TA_110 := Good.append g_110.1 GA_111 (by decide +kernel)
  have GB_110 : Good fB 10741 TB_110 := Good.append g_110.2 GB_111 (by decide +kernel)
  have GA_109 : Good fA 15120 TA_109 := Good.append g_109.1 GA_110 (by decide +kernel)
  have GB_109 : Good fB 10692 TB_109 := Good.append g_109.2 GB_110 (by decide +kernel)
  have GA_108 : Good fA 15051 TA_108 := Good.append g_108.1 GA_109 (by decide +kernel)
  have GB_108 : Good fB 10643 TB_108 := Good.append g_108.2 GB_109 (by decide +kernel)
  have GA_107 : Good fA 14981 TA_107 := Good.append g_107.1 GA_108 (by decide +kernel)
  have GB_107 : Good fB 10594 TB_107 := Good.append g_107.2 GB_108 (by decide +kernel)
  have GA_106 : Good fA 14911 TA_106 := Good.append g_106.1 GA_107 (by decide +kernel)
  have GB_106 : Good fB 10544 TB_106 := Good.append g_106.2 GB_107 (by decide +kernel)
  have GA_105 : Good fA 14840 TA_105 := Good.append g_105.1 GA_106 (by decide +kernel)
  have GB_105 : Good fB 10494 TB_105 := Good.append g_105.2 GB_106 (by decide +kernel)
  have GA_104 : Good fA 14769 TA_104 := Good.append g_104.1 GA_105 (by decide +kernel)
  have GB_104 : Good fB 10444 TB_104 := Good.append g_104.2 GB_105 (by decide +kernel)
  have GA_103 : Good fA 14698 TA_103 := Good.append g_103.1 GA_104 (by decide +kernel)
  have GB_103 : Good fB 10394 TB_103 := Good.append g_103.2 GB_104 (by decide +kernel)
  have GA_102 : Good fA 14627 TA_102 := Good.append g_102.1 GA_103 (by decide +kernel)
  have GB_102 : Good fB 10343 TB_102 := Good.append g_102.2 GB_103 (by decide +kernel)
  have GA_101 : Good fA 14555 TA_101 := Good.append g_101.1 GA_102 (by decide +kernel)
  have GB_101 : Good fB 10293 TB_101 := Good.append g_101.2 GB_102 (by decide +kernel)
  have GA_100 : Good fA 14483 TA_100 := Good.append g_100.1 GA_101 (by decide +kernel)
  have GB_100 : Good fB 10241 TB_100 := Good.append g_100.2 GB_101 (by decide +kernel)
  have GA_99 : Good fA 14410 TA_99 := Good.append g_99.1 GA_100 (by decide +kernel)
  have GB_99 : Good fB 10190 TB_99 := Good.append g_99.2 GB_100 (by decide +kernel)
  have GA_98 : Good fA 14337 TA_98 := Good.append g_98.1 GA_99 (by decide +kernel)
  have GB_98 : Good fB 10139 TB_98 := Good.append g_98.2 GB_99 (by decide +kernel)
  have GA_97 : Good fA 14264 TA_97 := Good.append g_97.1 GA_98 (by decide +kernel)
  have GB_97 : Good fB 10087 TB_97 := Good.append g_97.2 GB_98 (by decide +kernel)
  have GA_96 : Good fA 14190 TA_96 := Good.append g_96.1 GA_97 (by decide +kernel)
  have GB_96 : Good fB 10035 TB_96 := Good.append g_96.2 GB_97 (by decide +kernel)
  have GA_95 : Good fA 14116 TA_95 := Good.append g_95.1 GA_96 (by decide +kernel)
  have GB_95 : Good fB 9982 TB_95 := Good.append g_95.2 GB_96 (by decide +kernel)
  have GA_94 : Good fA 14041 TA_94 := Good.append g_94.1 GA_95 (by decide +kernel)
  have GB_94 : Good fB 9930 TB_94 := Good.append g_94.2 GB_95 (by decide +kernel)
  have GA_93 : Good fA 13966 TA_93 := Good.append g_93.1 GA_94 (by decide +kernel)
  have GB_93 : Good fB 9877 TB_93 := Good.append g_93.2 GB_94 (by decide +kernel)
  have GA_92 : Good fA 13891 TA_92 := Good.append g_92.1 GA_93 (by decide +kernel)
  have GB_92 : Good fB 9823 TB_92 := Good.append g_92.2 GB_93 (by decide +kernel)
  have GA_91 : Good fA 13816 TA_91 := Good.append g_91.1 GA_92 (by decide +kernel)
  have GB_91 : Good fB 9770 TB_91 := Good.append g_91.2 GB_92 (by decide +kernel)
  have GA_90 : Good fA 13739 TA_90 := Good.append g_90.1 GA_91 (by decide +kernel)
  have GB_90 : Good fB 9716 TB_90 := Good.append g_90.2 GB_91 (by decide +kernel)
  have GA_89 : Good fA 13663 TA_89 := Good.append g_89.1 GA_90 (by decide +kernel)
  have GB_89 : Good fB 9662 TB_89 := Good.append g_89.2 GB_90 (by decide +kernel)
  have GA_88 : Good fA 13586 TA_88 := Good.append g_88.1 GA_89 (by decide +kernel)
  have GB_88 : Good fB 9607 TB_88 := Good.append g_88.2 GB_89 (by decide +kernel)
  have GA_87 : Good fA 13508 TA_87 := Good.append g_87.1 GA_88 (by decide +kernel)
  have GB_87 : Good fB 9553 TB_87 := Good.append g_87.2 GB_88 (by decide +kernel)
  have GA_86 : Good fA 13431 TA_86 := Good.append g_86.1 GA_87 (by decide +kernel)
  have GB_86 : Good fB 9498 TB_86 := Good.append g_86.2 GB_87 (by decide +kernel)
  have GA_85 : Good fA 13352 TA_85 := Good.append g_85.1 GA_86 (by decide +kernel)
  have GB_85 : Good fB 9442 TB_85 := Good.append g_85.2 GB_86 (by decide +kernel)
  have GA_84 : Good fA 13274 TA_84 := Good.append g_84.1 GA_85 (by decide +kernel)
  have GB_84 : Good fB 9387 TB_84 := Good.append g_84.2 GB_85 (by decide +kernel)
  have GA_83 : Good fA 13194 TA_83 := Good.append g_83.1 GA_84 (by decide +kernel)
  have GB_83 : Good fB 9331 TB_83 := Good.append g_83.2 GB_84 (by decide +kernel)
  have GA_82 : Good fA 13115 TA_82 := Good.append g_82.1 GA_83 (by decide +kernel)
  have GB_82 : Good fB 9274 TB_82 := Good.append g_82.2 GB_83 (by decide +kernel)
  have GA_81 : Good fA 13034 TA_81 := Good.append g_81.1 GA_82 (by decide +kernel)
  have GB_81 : Good fB 9217 TB_81 := Good.append g_81.2 GB_82 (by decide +kernel)
  have GA_80 : Good fA 12954 TA_80 := Good.append g_80.1 GA_81 (by decide +kernel)
  have GB_80 : Good fB 9160 TB_80 := Good.append g_80.2 GB_81 (by decide +kernel)
  have GA_79 : Good fA 12872 TA_79 := Good.append g_79.1 GA_80 (by decide +kernel)
  have GB_79 : Good fB 9103 TB_79 := Good.append g_79.2 GB_80 (by decide +kernel)
  have GA_78 : Good fA 12791 TA_78 := Good.append g_78.1 GA_79 (by decide +kernel)
  have GB_78 : Good fB 9045 TB_78 := Good.append g_78.2 GB_79 (by decide +kernel)
  have GA_77 : Good fA 12709 TA_77 := Good.append g_77.1 GA_78 (by decide +kernel)
  have GB_77 : Good fB 8987 TB_77 := Good.append g_77.2 GB_78 (by decide +kernel)
  have GA_76 : Good fA 12626 TA_76 := Good.append g_76.1 GA_77 (by decide +kernel)
  have GB_76 : Good fB 8929 TB_76 := Good.append g_76.2 GB_77 (by decide +kernel)
  have GA_75 : Good fA 12542 TA_75 := Good.append g_75.1 GA_76 (by decide +kernel)
  have GB_75 : Good fB 8870 TB_75 := Good.append g_75.2 GB_76 (by decide +kernel)
  have GA_74 : Good fA 12458 TA_74 := Good.append g_74.1 GA_75 (by decide +kernel)
  have GB_74 : Good fB 8810 TB_74 := Good.append g_74.2 GB_75 (by decide +kernel)
  have GA_73 : Good fA 12374 TA_73 := Good.append g_73.1 GA_74 (by decide +kernel)
  have GB_73 : Good fB 8751 TB_73 := Good.append g_73.2 GB_74 (by decide +kernel)
  have GA_72 : Good fA 12289 TA_72 := Good.append g_72.1 GA_73 (by decide +kernel)
  have GB_72 : Good fB 8690 TB_72 := Good.append g_72.2 GB_73 (by decide +kernel)
  have GA_71 : Good fA 12203 TA_71 := Good.append g_71.1 GA_72 (by decide +kernel)
  have GB_71 : Good fB 8630 TB_71 := Good.append g_71.2 GB_72 (by decide +kernel)
  have GA_70 : Good fA 12117 TA_70 := Good.append g_70.1 GA_71 (by decide +kernel)
  have GB_70 : Good fB 8569 TB_70 := Good.append g_70.2 GB_71 (by decide +kernel)
  have GA_69 : Good fA 12030 TA_69 := Good.append g_69.1 GA_70 (by decide +kernel)
  have GB_69 : Good fB 8507 TB_69 := Good.append g_69.2 GB_70 (by decide +kernel)
  have GA_68 : Good fA 11943 TA_68 := Good.append g_68.1 GA_69 (by decide +kernel)
  have GB_68 : Good fB 8446 TB_68 := Good.append g_68.2 GB_69 (by decide +kernel)
  have GA_67 : Good fA 11855 TA_67 := Good.append g_67.1 GA_68 (by decide +kernel)
  have GB_67 : Good fB 8383 TB_67 := Good.append g_67.2 GB_68 (by decide +kernel)
  have GA_66 : Good fA 11766 TA_66 := Good.append g_66.1 GA_67 (by decide +kernel)
  have GB_66 : Good fB 8321 TB_66 := Good.append g_66.2 GB_67 (by decide +kernel)
  have GA_65 : Good fA 11676 TA_65 := Good.append g_65.1 GA_66 (by decide +kernel)
  have GB_65 : Good fB 8257 TB_65 := Good.append g_65.2 GB_66 (by decide +kernel)
  have GA_64 : Good fA 11586 TA_64 := Good.append g_64.1 GA_65 (by decide +kernel)
  have GB_64 : Good fB 8193 TB_64 := Good.append g_64.2 GB_65 (by decide +kernel)
  have GA_63 : Good fA 11495 TA_63 := Good.append g_63.1 GA_64 (by decide +kernel)
  have GB_63 : Good fB 8129 TB_63 := Good.append g_63.2 GB_64 (by decide +kernel)
  have GA_62 : Good fA 11404 TA_62 := Good.append g_62.1 GA_63 (by decide +kernel)
  have GB_62 : Good fB 8064 TB_62 := Good.append g_62.2 GB_63 (by decide +kernel)
  have GA_61 : Good fA 11311 TA_61 := Good.append g_61.1 GA_62 (by decide +kernel)
  have GB_61 : Good fB 7999 TB_61 := Good.append g_61.2 GB_62 (by decide +kernel)
  have GA_60 : Good fA 11218 TA_60 := Good.append g_60.1 GA_61 (by decide +kernel)
  have GB_60 : Good fB 7933 TB_60 := Good.append g_60.2 GB_61 (by decide +kernel)
  have GA_59 : Good fA 11124 TA_59 := Good.append g_59.1 GA_60 (by decide +kernel)
  have GB_59 : Good fB 7867 TB_59 := Good.append g_59.2 GB_60 (by decide +kernel)
  have GA_58 : Good fA 11030 TA_58 := Good.append g_58.1 GA_59 (by decide +kernel)
  have GB_58 : Good fB 7800 TB_58 := Good.append g_58.2 GB_59 (by decide +kernel)
  have GA_57 : Good fA 10934 TA_57 := Good.append g_57.1 GA_58 (by decide +kernel)
  have GB_57 : Good fB 7733 TB_57 := Good.append g_57.2 GB_58 (by decide +kernel)
  have GA_56 : Good fA 10838 TA_56 := Good.append g_56.1 GA_57 (by decide +kernel)
  have GB_56 : Good fB 7664 TB_56 := Good.append g_56.2 GB_57 (by decide +kernel)
  have GA_55 : Good fA 10741 TA_55 := Good.append g_55.1 GA_56 (by decide +kernel)
  have GB_55 : Good fB 7596 TB_55 := Good.append g_55.2 GB_56 (by decide +kernel)
  have GA_54 : Good fA 10643 TA_54 := Good.append g_54.1 GA_55 (by decide +kernel)
  have GB_54 : Good fB 7526 TB_54 := Good.append g_54.2 GB_55 (by decide +kernel)
  have GA_53 : Good fA 10544 TA_53 := Good.append g_53.1 GA_54 (by decide +kernel)
  have GB_53 : Good fB 7456 TB_53 := Good.append g_53.2 GB_54 (by decide +kernel)
  have GA_52 : Good fA 10444 TA_52 := Good.append g_52.1 GA_53 (by decide +kernel)
  have GB_52 : Good fB 7386 TB_52 := Good.append g_52.2 GB_53 (by decide +kernel)
  have GA_51 : Good fA 10343 TA_51 := Good.append g_51.1 GA_52 (by decide +kernel)
  have GB_51 : Good fB 7314 TB_51 := Good.append g_51.2 GB_52 (by decide +kernel)
  have GA_50 : Good fA 10241 TA_50 := Good.append g_50.1 GA_51 (by decide +kernel)
  have GB_50 : Good fB 7242 TB_50 := Good.append g_50.2 GB_51 (by decide +kernel)
  have GA_49 : Good fA 10138 TA_49 := Good.append g_49.1 GA_50 (by decide +kernel)
  have GB_49 : Good fB 7169 TB_49 := Good.append g_49.2 GB_50 (by decide +kernel)
  have GA_48 : Good fA 10034 TA_48 := Good.append g_48.1 GA_49 (by decide +kernel)
  have GB_48 : Good fB 7096 TB_48 := Good.append g_48.2 GB_49 (by decide +kernel)
  have GA_47 : Good fA 9929 TA_47 := Good.append g_47.1 GA_48 (by decide +kernel)
  have GB_47 : Good fB 7022 TB_47 := Good.append g_47.2 GB_48 (by decide +kernel)
  have GA_46 : Good fA 9823 TA_46 := Good.append g_46.1 GA_47 (by decide +kernel)
  have GB_46 : Good fB 6947 TB_46 := Good.append g_46.2 GB_47 (by decide +kernel)
  have GA_45 : Good fA 9716 TA_45 := Good.append g_45.1 GA_46 (by decide +kernel)
  have GB_45 : Good fB 6871 TB_45 := Good.append g_45.2 GB_46 (by decide +kernel)
  have GA_44 : Good fA 9607 TA_44 := Good.append g_44.1 GA_45 (by decide +kernel)
  have GB_44 : Good fB 6794 TB_44 := Good.append g_44.2 GB_45 (by decide +kernel)
  have GA_43 : Good fA 9497 TA_43 := Good.append g_43.1 GA_44 (by decide +kernel)
  have GB_43 : Good fB 6716 TB_43 := Good.append g_43.2 GB_44 (by decide +kernel)
  have GA_42 : Good fA 9386 TA_42 := Good.append g_42.1 GA_43 (by decide +kernel)
  have GB_42 : Good fB 6638 TB_42 := Good.append g_42.2 GB_43 (by decide +kernel)
  have GA_41 : Good fA 9274 TA_41 := Good.append g_41.1 GA_42 (by decide +kernel)
  have GB_41 : Good fB 6558 TB_41 := Good.append g_41.2 GB_42 (by decide +kernel)
  have GA_40 : Good fA 9160 TA_40 := Good.append g_40.1 GA_41 (by decide +kernel)
  have GB_40 : Good fB 6478 TB_40 := Good.append g_40.2 GB_41 (by decide +kernel)
  have GA_39 : Good fA 9045 TA_39 := Good.append g_39.1 GA_40 (by decide +kernel)
  have GB_39 : Good fB 6396 TB_39 := Good.append g_39.2 GB_40 (by decide +kernel)
  have GA_38 : Good fA 8928 TA_38 := Good.append g_38.1 GA_39 (by decide +kernel)
  have GB_38 : Good fB 6314 TB_38 := Good.append g_38.2 GB_39 (by decide +kernel)
  have GA_37 : Good fA 8810 TA_37 := Good.append g_37.1 GA_38 (by decide +kernel)
  have GB_37 : Good fB 6230 TB_37 := Good.append g_37.2 GB_38 (by decide +kernel)
  have GA_36 : Good fA 8690 TA_36 := Good.append g_36.1 GA_37 (by decide +kernel)
  have GB_36 : Good fB 6145 TB_36 := Good.append g_36.2 GB_37 (by decide +kernel)
  have GA_35 : Good fA 8568 TA_35 := Good.append g_35.1 GA_36 (by decide +kernel)
  have GB_35 : Good fB 6060 TB_35 := Good.append g_35.2 GB_36 (by decide +kernel)
  have GA_34 : Good fA 8445 TA_34 := Good.append g_34.1 GA_35 (by decide +kernel)
  have GB_34 : Good fB 5972 TB_34 := Good.append g_34.2 GB_35 (by decide +kernel)
  have GA_33 : Good fA 8320 TA_33 := Good.append g_33.1 GA_34 (by decide +kernel)
  have GB_33 : Good fB 5884 TB_33 := Good.append g_33.2 GB_34 (by decide +kernel)
  have GA_32 : Good fA 8193 TA_32 := Good.append g_32.1 GA_33 (by decide +kernel)
  have GB_32 : Good fB 5794 TB_32 := Good.append g_32.2 GB_33 (by decide +kernel)
  have GA_31 : Good fA 8064 TA_31 := Good.append g_31.1 GA_32 (by decide +kernel)
  have GB_31 : Good fB 5703 TB_31 := Good.append g_31.2 GB_32 (by decide +kernel)
  have GA_30 : Good fA 7933 TA_30 := Good.append g_30.1 GA_31 (by decide +kernel)
  have GB_30 : Good fB 5610 TB_30 := Good.append g_30.2 GB_31 (by decide +kernel)
  have GA_29 : Good fA 7800 TA_29 := Good.append g_29.1 GA_30 (by decide +kernel)
  have GB_29 : Good fB 5516 TB_29 := Good.append g_29.2 GB_30 (by decide +kernel)
  have GA_28 : Good fA 7664 TA_28 := Good.append g_28.1 GA_29 (by decide +kernel)
  have GB_28 : Good fB 5420 TB_28 := Good.append g_28.2 GB_29 (by decide +kernel)
  have GA_27 : Good fA 7526 TA_27 := Good.append g_27.1 GA_28 (by decide +kernel)
  have GB_27 : Good fB 5322 TB_27 := Good.append g_27.2 GB_28 (by decide +kernel)
  have GA_26 : Good fA 7385 TA_26 := Good.append g_26.1 GA_27 (by decide +kernel)
  have GB_26 : Good fB 5223 TB_26 := Good.append g_26.2 GB_27 (by decide +kernel)
  have GA_25 : Good fA 7242 TA_25 := Good.append g_25.1 GA_26 (by decide +kernel)
  have GB_25 : Good fB 5121 TB_25 := Good.append g_25.2 GB_26 (by decide +kernel)
  have GA_24 : Good fA 7095 TA_24 := Good.append g_24.1 GA_25 (by decide +kernel)
  have GB_24 : Good fB 5018 TB_24 := Good.append g_24.2 GB_25 (by decide +kernel)
  have GA_23 : Good fA 6946 TA_23 := Good.append g_23.1 GA_24 (by decide +kernel)
  have GB_23 : Good fB 4912 TB_23 := Good.append g_23.2 GB_24 (by decide +kernel)
  have GA_22 : Good fA 6793 TA_22 := Good.append g_22.1 GA_23 (by decide +kernel)
  have GB_22 : Good fB 4804 TB_22 := Good.append g_22.2 GB_23 (by decide +kernel)
  have GA_21 : Good fA 6637 TA_21 := Good.append g_21.1 GA_22 (by decide +kernel)
  have GB_21 : Good fB 4694 TB_21 := Good.append g_21.2 GB_22 (by decide +kernel)
  have GA_20 : Good fA 6477 TA_20 := Good.append g_20.1 GA_21 (by decide +kernel)
  have GB_20 : Good fB 4581 TB_20 := Good.append g_20.2 GB_21 (by decide +kernel)
  have GA_19 : Good fA 6313 TA_19 := Good.append g_19.1 GA_20 (by decide +kernel)
  have GB_19 : Good fB 4465 TB_19 := Good.append g_19.2 GB_20 (by decide +kernel)
  have GA_18 : Good fA 6145 TA_18 := Good.append g_18.1 GA_19 (by decide +kernel)
  have GB_18 : Good fB 4346 TB_18 := Good.append g_18.2 GB_19 (by decide +kernel)
  have GA_17 : Good fA 5972 TA_17 := Good.append g_17.1 GA_18 (by decide +kernel)
  have GB_17 : Good fB 4224 TB_17 := Good.append g_17.2 GB_18 (by decide +kernel)
  have GA_16 : Good fA 5794 TA_16 := Good.append g_16.1 GA_17 (by decide +kernel)
  have GB_16 : Good fB 4097 TB_16 := Good.append g_16.2 GB_17 (by decide +kernel)
  have GA_15 : Good fA 5610 TA_15 := Good.append g_15.1 GA_16 (by decide +kernel)
  have GB_15 : Good fB 3967 TB_15 := Good.append g_15.2 GB_16 (by decide +kernel)
  have GA_14 : Good fA 5419 TA_14 := Good.append g_14.1 GA_15 (by decide +kernel)
  have GB_14 : Good fB 3833 TB_14 := Good.append g_14.2 GB_15 (by decide +kernel)
  have GA_13 : Good fA 5222 TA_13 := Good.append g_13.1 GA_14 (by decide +kernel)
  have GB_13 : Good fB 3694 TB_13 := Good.append g_13.2 GB_14 (by decide +kernel)
  have GA_12 : Good fA 5018 TA_12 := Good.append g_12.1 GA_13 (by decide +kernel)
  have GB_12 : Good fB 3549 TB_12 := Good.append g_12.2 GB_13 (by decide +kernel)
  have GA_11 : Good fA 4804 TA_11 := Good.append g_11.1 GA_12 (by decide +kernel)
  have GB_11 : Good fB 3398 TB_11 := Good.append g_11.2 GB_12 (by decide +kernel)
  have GA_10 : Good fA 4580 TA_10 := Good.append g_10.1 GA_11 (by decide +kernel)
  have GB_10 : Good fB 3240 TB_10 := Good.append g_10.2 GB_11 (by decide +kernel)
  have GA_9 : Good fA 4345 TA_9 := Good.append g_9.1 GA_10 (by decide +kernel)
  have GB_9 : Good fB 3073 TB_9 := Good.append g_9.2 GB_10 (by decide +kernel)
  have GA_8 : Good fA 4097 TA_8 := Good.append g_8.1 GA_9 (by decide +kernel)
  have GB_8 : Good fB 2898 TB_8 := Good.append g_8.2 GB_9 (by decide +kernel)
  have GA_7 : Good fA 3832 TA_7 := Good.append g_7.1 GA_8 (by decide +kernel)
  have GB_7 : Good fB 2711 TB_7 := Good.append g_7.2 GB_8 (by decide +kernel)
  have GA_6 : Good fA 3548 TA_6 := Good.append g_6.1 GA_7 (by decide +kernel)
  have GB_6 : Good fB 2510 TB_6 := Good.append g_6.2 GB_7 (by decide +kernel)
  have GA_5 : Good fA 3239 TA_5 := Good.append g_5.1 GA_6 (by decide +kernel)
  have GB_5 : Good fB 2291 TB_5 := Good.append g_5.2 GB_6 (by decide +kernel)
  have GA_4 : Good fA 2897 TA_4 := Good.append g_4.1 GA_5 (by decide +kernel)
  have GB_4 : Good fB 2049 TB_4 := Good.append g_4.2 GB_5 (by decide +kernel)
  have GA_3 : Good fA 2509 TA_3 := Good.append g_3.1 GA_4 (by decide +kernel)
  have GB_3 : Good fB 1775 TB_3 := Good.append g_3.2 GB_4 (by decide +kernel)
  have GA_2 : Good fA 2049 TA_2 := Good.append g_2.1 GA_3 (by decide +kernel)
  have GB_2 : Good fB 1450 TB_2 := Good.append g_2.2 GB_3 (by decide +kernel)
  have GA_1 : Good fA 1449 TA_1 := Good.append g_1.1 GA_2 (by decide +kernel)
  have GB_1 : Good fB 1025 TB_1 := Good.append g_1.2 GB_2 (by decide +kernel)
  have GA_0 : Good fA 1 TA_0 := Good.append g_0.1 GA_1 (by decide +kernel)
  have GB_0 : Good fB 1 TB_0 := Good.append g_0.2 GB_1 (by decide +kernel)
  exact ⟨Good.append (base0 fA hc0A) GA_0 rfl, Good.append (base0 fB hc0B) GB_0 rfl⟩


theorem tabA_length : tabA.length = 16690 := by decide +kernel

theorem tabB_length : tabB.length = 11802 := by decide +kernel

/-- `π(k(k+1)/2) = tabA[k]` for `k ≤ 16689`. -/
theorem primeCounting_tri (k : ℕ) (hk : k ≤ 16689) :
    Nat.primeCounting (k * (k + 1) / 2) = tabA.getD k 0 := by
  rw [← count_fA]
  have h := goodAB.1 k (by rw [tabA_length]; omega)
  rwa [zero_add] at h

/-- `π(m ^ 2) = tabB[m]` for `m ≤ 11801`. -/
theorem primeCounting_sq (m : ℕ) (hm : m ≤ 11801) :
    Nat.primeCounting (m ^ 2) = tabB.getD m 0 := by
  rw [← count_fB]
  have h := goodAB.2 m (by rw [tabB_length]; omega)
  rwa [zero_add] at h

theorem tri_mono {k k' : ℕ} (h : k ≤ k') : k * (k + 1) / 2 ≤ k' * (k' + 1) / 2 :=
  Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

theorem sq_mono {m m' : ℕ} (h : m ≤ m') : m ^ 2 ≤ m' ^ 2 := Nat.pow_le_pow_left h 2

/-! ## A merge of two sorted lists -/

/-- Adjacent entries are in order. -/
def sortedB : List ℕ → Bool
  | a :: b :: l => decide (a ≤ b) && sortedB (b :: l)
  | _ => true

theorem sortedB_tail {a : ℕ} {l : List ℕ} (h : sortedB (a :: l) = true) : sortedB l = true := by
  match l, h with
  | [], _ => rfl
  | b :: l, h =>
    simp only [sortedB, Bool.and_eq_true] at h
    exact h.2

theorem sortedB_head {a : ℕ} : ∀ {l : List ℕ}, sortedB (a :: l) = true → ∀ x ∈ l, a ≤ x
  | [], _, x, hx => by simp at hx
  | b :: l, h, x, hx => by
    simp only [sortedB, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact le_trans h.1 (sortedB_head h.2 x hx)

/-- The common values of two sorted lists, by a merge with fuel `n`. -/
def common : ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | _ + 1, _ :: _, [] => []
  | n + 1, a :: as, b :: bs =>
    if a < b then common n as (b :: bs)
    else if b < a then common n (a :: as) bs
    else a :: common n as bs

theorem mem_common : ∀ (n : ℕ) (as bs : List ℕ), as.length + bs.length ≤ n →
    sortedB as = true → sortedB bs = true → ∀ x, x ∈ as → x ∈ bs → x ∈ common n as bs
  | 0, as, bs, hn, _, _, x, hx, _ => by
    have : as = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp at hx
  | _ + 1, [], _, _, _, _, x, hx, _ => by simp at hx
  | _ + 1, _ :: _, [], _, _, _, x, _, hy => by simp at hy
  | n + 1, a :: as, b :: bs, hn, hsa, hsb, x, hx, hy => by
    simp only [List.length_cons] at hn
    simp only [common]
    by_cases h1 : a < b
    · rw [if_pos h1]
      apply mem_common n as (b :: bs) (by simp only [List.length_cons]; omega)
        (sortedB_tail hsa) hsb x _ hy
      rcases List.mem_cons.mp hx with hxa | hx'
      · exfalso
        rcases List.mem_cons.mp hy with h | h
        · omega
        · have := sortedB_head hsb x h
          omega
      · exact hx'
    · rw [if_neg h1]
      by_cases h2 : b < a
      · rw [if_pos h2]
        apply mem_common n (a :: as) bs (by simp only [List.length_cons]; omega)
          hsa (sortedB_tail hsb) x hx _
        rcases List.mem_cons.mp hy with hyb | hy'
        · exfalso
          rcases List.mem_cons.mp hx with h | h
          · omega
          · have := sortedB_head hsa x h
            omega
        · exact hy'
      · rw [if_neg h2]
        by_cases hxa : x = a
        · rw [hxa]
          exact List.mem_cons_self
        · apply List.mem_cons_of_mem
          apply mem_common n as bs (by omega) (sortedB_tail hsa) (sortedB_tail hsb) x
          · exact (List.mem_cons.mp hx).resolve_left hxa
          · exact (List.mem_cons.mp hy).resolve_left (by omega)

/-! ## The pair check for `n = 7872413` -/

/-- `π(T_k)` for `k ≤ 16688`. -/
def AL : List ℕ := tabA.take 16689

/-- `7872413 - π(m ^ 2)` for `m = 11800, ..., 0`, in increasing order. -/
def BL : List ℕ := ((tabB.take 11801).map (fun y => 7872413 - y)).reverse

theorem merge_check : sortedB AL = true ∧ sortedB BL = true ∧ AL.length + BL.length ≤ 30000 ∧
    common 30000 AL BL = [6450605] := by
  decide +kernel

theorem table_values : tabA.getD 16689 0 = 7873136 ∧ tabB.getD 11801 0 = 7872809 ∧
    tabA.getD 15014 0 = 6449818 ∧ tabA.getD 15015 0 = 6450605 ∧ tabA.getD 15016 0 = 6451439 ∧
    tabB.getD 4748 0 = 1421226 ∧ tabB.getD 4749 0 = 1421808 ∧ tabB.getD 4750 0 = 1422368 := by
  decide +kernel

theorem getD_mem_take {L : List ℕ} {n k : ℕ} (hk : k < n) (hkL : k < L.length) :
    L.getD k 0 ∈ L.take n := by
  rw [List.getD_eq_getElem _ _ hkL]
  have h : k < (L.take n).length := by rw [List.length_take]; omega
  have hm := List.getElem_mem h
  rwa [List.getElem_take] at hm

/-- The only representation of `7872413` is `(15015, 4749)`. -/
theorem uniq (k m : ℕ)
    (heq : Nat.primeCounting (k * (k + 1) / 2) + Nat.primeCounting (m ^ 2) = 7872413) :
    k = 15015 ∧ m = 4749 := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8⟩ := table_values
  obtain ⟨s1, s2, s3, s4⟩ := merge_check
  have hk : k ≤ 16688 := by
    by_contra h
    have := Nat.monotone_primeCounting (tri_mono (show 16689 ≤ k by omega))
    rw [primeCounting_tri 16689 le_rfl, v1] at this
    omega
  have hm : m ≤ 11800 := by
    by_contra h
    have := Nat.monotone_primeCounting (sq_mono (show 11801 ≤ m by omega))
    rw [primeCounting_sq 11801 le_rfl, v2] at this
    omega
  rw [primeCounting_tri k (by omega), primeCounting_sq m (by omega)] at heq
  have hA : tabA.getD k 0 ∈ AL := getD_mem_take (by omega) (by rw [tabA_length]; omega)
  have hB0 : tabB.getD m 0 ∈ tabB.take 11801 :=
    getD_mem_take (by omega) (by rw [tabB_length]; omega)
  have hB : tabA.getD k 0 ∈ BL := by
    rw [BL, List.mem_reverse, show tabA.getD k 0 = 7872413 - tabB.getD m 0 by omega]
    exact List.mem_map.mpr ⟨_, hB0, rfl⟩
  have hc := mem_common 30000 AL BL s3 s1 s2 _ hA hB
  rw [s4, List.mem_singleton] at hc
  constructor
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := Nat.monotone_primeCounting (tri_mono (show k ≤ 15014 by omega))
      rw [primeCounting_tri k (by omega), primeCounting_tri 15014 (by norm_num), v3] at this
      omega
    · have := Nat.monotone_primeCounting (tri_mono (show 15016 ≤ k by omega))
      rw [primeCounting_tri k (by omega), primeCounting_tri 15016 (by norm_num), v5] at this
      omega
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := Nat.monotone_primeCounting (sq_mono (show m ≤ 4748 by omega))
      rw [primeCounting_sq m (by omega), primeCounting_sq 4748 (by norm_num), v6] at this
      omega
    · have := Nat.monotone_primeCounting (sq_mono (show 4750 ≤ m by omega))
      rw [primeCounting_sq m (by omega), primeCounting_sq 4750 (by norm_num), v8] at this
      omega

theorem rep (k m : ℕ) (hk : k = 15015) (hm : m = 4749) :
    Nat.primeCounting (k * (k + 1) / 2) + Nat.primeCounting (m ^ 2) = 7872413 := by
  have e1 := primeCounting_tri k (by omega)
  have e2 := primeCounting_sq m (by omega)
  obtain ⟨-, -, -, v4, -, -, v7, -⟩ := table_values
  subst hk hm
  omega

theorem pairs_eq : pairs 7872413 = {(15015, 4749)} := by
  ext ⟨k, m⟩
  rw [pairs, Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨_, heq⟩
    exact uniq k m heq
  · rintro ⟨hk, hm⟩
    refine ⟨?_, rep k m hk hm⟩
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    omega

theorem a_eq_one : a 7872413 = 1 := by
  rw [a, pairs_eq, Finset.card_singleton]

end OMA.A262999Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a262999.main) := by
  intro h
  have h1 := h.2 7872413 OMA.A262999Disproof.a_eq_one
  simp at h1
