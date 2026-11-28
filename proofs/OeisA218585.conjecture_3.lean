import FormalConjectures.OEIS.«218585»
import Mathlib

/-! Conjecture 3 via the logarithmic cosine moments of angular Eisenstein characters.
This assembly uses the accepted A218585 reductions and leaf proofs in open-math-agents.
The reduction arguments were contributed by Marcus Buffett (#3897, #4334, #5259,
#5645, #6266). The Hecke input is by @JaviSoto (#13350), and positivity and
continuity are by @ivillar (#6512, #6125). The split-prime and Tauberian wrappers
use the versions by Pavel Pleskov (#11411, #11426, #11551). The Euclidean sector
and dyadic arguments credit @PanPapag, and the AP estimate credits Marcus Buffett
(#1835). The Apache-2.0 PNT+ attribution and port details are retained below. The
conjecture 4 cancellation argument is stopped at its logarithmically weighted limit.
-/

section
/- Integrated source: reductions/OeisA218585.conjecture_3.R1 -/
/- First moments of coordinates in the fundamental Eisenstein sector.
The split norm representation proof below is adapted from @PanPapag (#1308).
Summation by parts transfers unweighted sector averages to square-root weights. -/

namespace OMA.SplitPrime

lemma cubicRoot (p : ℕ) (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ r : ZMod p, r ^ 2 + r + 1 = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hd : 3 ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := (ZMod p)ˣ) 3 hd
  have hc : (u : ZMod p) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one]
    rfl
  have hne : (u : ZMod p) ≠ 1 := by
    intro h
    have h' : u = 1 := Units.ext h
    simp [h'] at hu
  refine ⟨u, (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hne)⟩
  linear_combination hc

/-- Pigeonholing a square modulo p gives a nonzero vector with small coordinates. -/
lemma smallVector (p : ℕ) (hp : p.Prime) (r : ZMod p) :
    ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ |a| ≤ p.sqrt ∧ |b| ≤ p.sqrt ∧
      (a : ZMod p) = r * (b : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  let B := Fin (p.sqrt + 1)
  let f (v : B × B) : ZMod p := (v.1.val : ZMod p) - r * v.2.val
  obtain ⟨v, w, hvw, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    simpa [B, ZMod.card] using Nat.lt_succ_sqrt p)
  let a : ℤ := (v.1.val : ℤ) - w.1.val
  let b : ℤ := (v.2.val : ℤ) - w.2.val
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · by_contra! hz
    apply hvw
    apply Prod.ext <;> apply Fin.ext
    · dsimp [a] at hz
      omega
    · dsimp [b] at hz
      omega
  · have hv := v.1.isLt
    have hw := w.1.isLt
    dsimp [B] at hv hw
    rw [abs_le]
    dsimp [a]
    omega
  · have hv := v.2.isLt
    have hw := w.2.isLt
    dsimp [B] at hv hw
    rw [abs_le]
    dsimp [b]
    omega
  · dsimp [a, b]
    push_cast
    dsimp [f] at heq
    linear_combination heq

/-- The small norm is a positive multiple of p strictly below 3p.
The residue 2 modulo 3 is impossible for the norm form. -/
lemma integralRepresentation (p : ℕ) (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ a b : ℤ, a ^ 2 + a * b + b ^ 2 = p := by
  obtain ⟨r, hr⟩ := cubicRoot p hp hmod
  obtain ⟨a, b, hab, ha, hb, heq⟩ := smallVector p hp r
  let q := a ^ 2 + a * b + b ^ 2
  have hd : (p : ℤ) ∣ q := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    dsimp [q]
    push_cast
    rw [heq]
    linear_combination (b : ZMod p) ^ 2 * hr
  have hpos : 0 < q := by
    dsimp [q]
    rcases hab with h | h
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg b, sq_nonneg (a + b)]
    · nlinarith [sq_pos_of_ne_zero h, sq_nonneg a, sq_nonneg (a + b)]
  have hs : p.sqrt * p.sqrt < p :=
    lt_of_le_of_ne (Nat.sqrt_le _) (fun h => hp.prime.not_isSquare ⟨_, h.symm⟩)
  have hbound : q < 3 * p := by
    have hs' : (p.sqrt : ℤ) * p.sqrt < p := by exact_mod_cast hs
    have ha' := mul_self_le_mul_self (abs_nonneg a) ha
    have hb' := mul_self_le_mul_self (abs_nonneg b) hb
    rw [abs_mul_abs_self] at ha' hb'
    dsimp [q]
    nlinarith [sq_nonneg (a - b)]
  obtain ⟨k, hk⟩ := hd
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hkpos : 0 < k := pos_of_mul_pos_right (hk ▸ hpos) hp'.le
  have hksmall : k < 3 := by
    rw [hk, mul_comm (3 : ℤ)] at hbound
    exact (mul_lt_mul_iff_right₀ hp').mp hbound
  have hk1 : k = 1 := by
    by_contra h
    have hk2 : k = 2 := by omega
    have hq : a ^ 2 + a * b + b ^ 2 = (p : ℤ) * 2 := by simpa [q, hk2] using hk
    have h3 : (p : ZMod 3) = 1 := by
      rw [← ZMod.natCast_mod, hmod]
      rfl
    have hbad := congrArg (fun z : ℤ => (z : ZMod 3)) hq
    push_cast at hbad
    rw [h3, one_mul] at hbad
    exact (show ∀ x y : ZMod 3, x ^ 2 + x * y + y ^ 2 ≠ 2 by decide) _ _ hbad
  exact ⟨a, b, by simpa [q, hk1] using hk⟩

/-- Among a, b, and -a-b, two share a weak sign. Each pair has the same norm. -/
lemma nonnegativeRepresentation (p : ℕ) (a b : ℤ) (h : a ^ 2 + a * b + b ^ 2 = p) :
    ∃ x y : ℕ, x ^ 2 + x * y + y ^ 2 = p := by
  have liftPair (u v : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v)
      (hn : u ^ 2 + u * v + v ^ 2 = p) : ∃ x y : ℕ, x ^ 2 + x * y + y ^ 2 = p := by
    refine ⟨u.toNat, v.toNat, ?_⟩
    have he : (u.toNat : ℤ) ^ 2 + (u.toNat : ℤ) * v.toNat + (v.toNat : ℤ) ^ 2 = p := by
      simpa [Int.toNat_of_nonneg hu, Int.toNat_of_nonneg hv] using hn
    exact_mod_cast he
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · exact liftPair a b ha hb h
  · by_cases hs : 0 ≤ -a-b
    · exact liftPair a (-a-b) ha hs (by linear_combination h)
    · exact liftPair (-b) (a+b) (by omega) (by omega) (by linear_combination h)
  · by_cases hs : 0 ≤ -a-b
    · exact liftPair b (-a-b) hb hs (by linear_combination h)
    · exact liftPair (-a) (a+b) (by omega) (by omega) (by linear_combination h)
  · exact liftPair (-a) (-b) (by omega) (by omega) (by linear_combination h)

lemma orderedRepresentation (p : ℕ) (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ x y : ℕ, 0 < y ∧ y < x ∧ x < p ∧ x ^ 2 + x * y + y ^ 2 = p := by
  obtain ⟨a, b, hab⟩ := integralRepresentation p hp hmod
  obtain ⟨u, v, huv⟩ := nonnegativeRepresentation p a b hab
  obtain ⟨x, y, hle, hn⟩ : ∃ x y : ℕ, y ≤ x ∧ x ^ 2 + x * y + y ^ 2 = p := by
    rcases le_total v u with h | h
    · exact ⟨u, v, h, huv⟩
    · exact ⟨v, u, h, by linarith⟩
  have hy : 0 < y := by
    by_contra! hz
    have he : y = 0 := by omega
    exact hp.prime.not_isSquare ⟨x, by simpa [he, pow_two] using hn.symm⟩
  have hne : y ≠ x := by
    rintro rfl
    have hd : 3 ∣ p := ⟨y ^ 2, by nlinarith⟩
    omega
  refine ⟨x, y, hy, lt_of_le_of_ne hle hne, ?_, hn⟩
  nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) x, Nat.pow_pos hy (n := 2)]

/-- Swapping the coordinates interchanges the two roots of the norm form modulo p.
In the ordered sector only one cross product can vanish. -/
lemma uniqueSecond (p : ℕ) (hp : p.Prime) (a b c d : ℕ)
    (hb : 0 < b) (hab : b < a) (hd : 0 < d) (hcd : d < c)
    (h₁ : a ^ 2 + a * b + b ^ 2 = p) (h₂ : c ^ 2 + c * d + d ^ 2 = p) : b = d := by
  let : Fact p.Prime := ⟨hp⟩
  have h₁' : (a : ZMod p) ^ 2 + a * b + b ^ 2 = 0 := by
    simpa using congrArg (fun n : ℕ => (n : ZMod p)) h₁
  have h₂' : (c : ZMod p) ^ 2 + c * d + d ^ 2 = 0 := by
    simpa using congrArg (fun n : ℕ => (n : ZMod p)) h₂
  have hf : ((a : ZMod p) * d - b * c) * (a * c - b * d) = 0 := by
    linear_combination (c : ZMod p) * d * h₁' - (a : ZMod p) * b * h₂'
  have hac : a * c < p := by
    rcases le_total a c with h | h
    · have hsq := Nat.mul_le_mul_right c h
      nlinarith [Nat.mul_pos (hd.trans hcd) hd]
    · have hsq := Nat.mul_le_mul_left a h
      nlinarith [Nat.mul_pos (hb.trans hab) hb]
  have hbc := Nat.mul_lt_mul_of_pos_right hab (by omega : 0 < c)
  have had := Nat.mul_lt_mul_of_pos_left hcd (by omega : 0 < a)
  have hbd := Nat.mul_lt_mul_of_pos_right hab hd
  have liftEq (u v : ℕ) (hu : u < p) (hv : v < p) (h : (u : ZMod p) = v) : u = v := by
    simpa [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] using
      (ZMod.natCast_eq_natCast_iff' u v p).mp h
  have hcross : a * d = b * c := by
    rcases mul_eq_zero.mp hf with h | h
    · exact liftEq _ _ (had.trans hac) (hbc.trans hac) (by simpa using sub_eq_zero.mp h)
    · have he := liftEq (a*c) (b*d) hac (hbd.trans (had.trans hac)) (by simpa using sub_eq_zero.mp h)
      omega
  have he : p * d ^ 2 = p * b ^ 2 := calc
    p * d ^ 2 = (a*d) ^ 2 + (a*d)*(b*d) + (b*d) ^ 2 := by rw [← h₁]; ring
    _ = p * b ^ 2 := by rw [hcross, ← h₂]; ring
  have := Nat.eq_of_mul_eq_mul_left hp.pos he
  nlinarith

lemma findWitness (l : List ℕ) (f : ℕ → Bool) (w : ℕ) (hw : w ∈ l) (hf : f w) :
    f ((l.find? f).getD 0) := by
  cases h : l.find? f with
  | none => exact False.elim ((List.find?_eq_none.mp h w hw) hf)
  | some z => exact List.find?_some h

end OMA.SplitPrime

open OeisA218585 OMA.SplitPrime

private theorem splitNorm : ∀ p : ℕ, p.Prime → p % 3 = 1 → xp p ^ 2 + xp p * yp p + yp p ^ 2 = p := by
  intro p hp hmod
  obtain ⟨x, y, hy, hyx, hxp, hn⟩ := orderedRepresentation p hp hmod
  let X (u : ℕ) := (List.range u).any fun v =>
    0 < v && u ^ 2 + u * v + v ^ 2 == p
  let Y (v : ℕ) := 0 < v && (List.Ico (v + 1) p).any fun u =>
    u ^ 2 + u * v + v ^ 2 == p
  have specX (u : ℕ) : X u ↔ ∃ v < u, 0 < v ∧ u ^ 2 + u * v + v ^ 2 = p := by
    simp [X]
  have specY (v : ℕ) : Y v ↔ 0 < v ∧ ∃ u, (v + 1 ≤ u ∧ u < p) ∧ u ^ 2 + u * v + v ^ 2 = p := by
    simp [Y]
  have hx' : X (xp p) := findWitness (List.range p) X x (List.mem_range.mpr hxp)
    ((specX x).mpr ⟨y, hyx, hy, hn⟩)
  have hy' : Y (yp p) := findWitness (List.range p) Y y (List.mem_range.mpr (hyx.trans hxp))
    ((specY y).mpr ⟨hy, x, ⟨hyx, hxp⟩, hn⟩)
  obtain ⟨v, hvx, hv, h₁⟩ := (specX _).mp hx'
  obtain ⟨hy₀, u, ⟨hyu, _⟩, h₂⟩ := (specY _).mp hy'
  rwa [← uniqueSecond p hp (xp p) v u (yp p) hv hvx hy₀ hyu h₁ h₂]

namespace OMA.R_OeisA218585_conjecture_3_R1

open OeisA218585 Real Filter MeasureTheory Finset
open scoped Topology

-- Hecke's sector theorem for the unweighted counting measure.
def H1 : Prop :=
  let splitPrimes (n : ℕ) := (range n).filter fun p => p.Prime ∧ p % 3 = 1
  let angle (p : ℕ) := (⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩ : ℂ).arg
  ∀ f : ℝ → ℝ, Continuous f →
    Tendsto (fun n => (∑ p ∈ splitPrimes n, f (angle p)) / (splitPrimes n).card)
    atTop (𝓝 ((6 / π) * ∫ t in 0..π / 6, f t))

-- A positive fraction of the split primes lie in the upper dyadic interval.
def H2 : Prop :=
  let splitPrimes (n : ℕ) := (range n).filter fun p => p.Prime ∧ p % 3 = 1
  ∀ᶠ n in atTop,
    (splitPrimes n).card ≤ 3 * ((splitPrimes n).filter fun p => n ≤ 2 * p).card

lemma countsGrow :
    Tendsto (fun n => ((((range n).filter fun p => p.Prime ∧ p % 3 = 1)).card : ℝ)) atTop atTop := by
  let splitPrimes (n : ℕ) := (range n).filter fun p => p.Prime ∧ p % 3 = 1
  let P (p : ℕ) := p.Prime ∧ p % 3 = 1
  have hi : (Set.ofPred P).Infinite :=
    Nat.infinite_setOfPred_prime_modEq_one (k := 3) (by decide)
  apply tendsto_natCast_atTop_atTop.comp
  apply tendsto_atTop_atTop.mpr
  intro k
  refine ⟨Nat.nth P k, fun n hn => ?_⟩
  change k ≤ ((range n).filter P).card
  rw [← Nat.count_eq_card_filter_range, ← Nat.count_nth_of_infinite hi k]
  exact Nat.count_monotone P hn

private theorem uniformPrefix {A count : ℕ → ℝ} (hn : ∀ j, 0 ≤ count j)
    (hz : ∀ j, count j = 0 → A j = 0) (hm : Monotone count)
    (hg : Tendsto count atTop atTop) (h : Tendsto (fun j => A j / count j) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ j ≤ n, |A j| ≤ δ * count n := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp h) δ hδ)
  let C := ∑ j ∈ range K, |A j|
  filter_upwards [hg.eventually_ge_atTop (C / δ)] with n hn' j hj
  by_cases hk : j < K
  · exact (single_le_sum (f := fun j => |A j|) (fun i _ => abs_nonneg (A i))
      (mem_range.mpr hk)).trans (by simpa [mul_comm] using (div_le_iff₀ hδ).mp hn')
  by_cases hc : count j = 0
  · simp [hz j hc, mul_nonneg hδ.le (hn n)]
  have hpos := lt_of_le_of_ne (hn j) (Ne.symm hc)
  have hsmall := hK j (Nat.le_of_not_gt hk)
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos] at hsmall
  exact hsmall.le.trans (mul_le_mul_of_nonneg_left (hm hj) hδ.le)

private theorem weightBound (hd : H2) : ∀ᶠ n : ℕ in atTop,
    √(n : ℝ) * (((range n).filter fun p => p.Prime ∧ p % 3 = 1)).card ≤ 6 * ∑ p ∈ ((range n).filter fun p => p.Prime ∧ p % 3 = 1), √(p : ℝ) := by
  let splitPrimes (n : ℕ) := (range n).filter fun p => p.Prime ∧ p % 3 = 1
  filter_upwards [hd] with n h
  let U := (splitPrimes n).filter fun p => n ≤ 2 * p
  have hc : ((splitPrimes n).card : ℝ) ≤ 3 * (U.card : ℝ) := by exact_mod_cast h
  have hb : √(n : ℝ) * U.card ≤ 2 * ∑ p ∈ splitPrimes n, √(p : ℝ) := calc
    _ = ∑ _p ∈ U, √(n : ℝ) := by simp [mul_comm]
    _ ≤ ∑ p ∈ U, 2 * √(p : ℝ) := sum_le_sum fun p hp => by
      have hv : (n : ℝ) ≤ 2 * p := by exact_mod_cast (mem_filter.mp hp).2
      nlinarith [sq_sqrt (Nat.cast_nonneg p), sq_sqrt (Nat.cast_nonneg n),
        sqrt_nonneg (p : ℝ), sqrt_nonneg (n : ℝ)]
    _ ≤ ∑ p ∈ splitPrimes n, 2 * √(p : ℝ) := sum_le_sum_of_subset_of_nonneg
      (filter_subset _ _) fun _ _ _ => by positivity
    _ = _ := (mul_sum ..).symm
  linarith [mul_le_mul_of_nonneg_left hc (sqrt_nonneg (n : ℝ))]

private theorem transfer (hd : H2) (f : ℕ → ℝ)
    (cancel : Tendsto (fun n => (∑ p ∈ ((range n).filter fun p => p.Prime ∧ p % 3 = 1), f p) / (((range n).filter fun p => p.Prime ∧ p % 3 = 1)).card)
      atTop (𝓝 0)) :
    Tendsto (fun n => (∑ p ∈ ((range n).filter fun p => p.Prime ∧ p % 3 = 1), √(p : ℝ) * f p) /
      ∑ p ∈ ((range n).filter fun p => p.Prime ∧ p % 3 = 1), √(p : ℝ)) atTop (𝓝 0) := by
  let splitPrimes (n : ℕ) := (range n).filter fun p => p.Prime ∧ p % 3 = 1
  let A (n : ℕ) := ∑ p ∈ splitPrimes n, f p
  let count (n : ℕ) : ℝ := (splitPrimes n).card
  let w (j : ℕ) := √(j : ℝ)
  let mass (n : ℕ) := ∑ p ∈ splitPrimes n, w p
  have hw : Monotone w := fun _ _ hj => sqrt_le_sqrt (by exact_mod_cast hj)
  have hc : Monotone count := fun m n h => by
    dsimp [count,splitPrimes]
    exact_mod_cast Finset.card_le_card (filter_subset_filter (fun p : ℕ => p.Prime ∧ p % 3 = 1) (range_mono h))
  have hz (j : ℕ) (h : count j = 0) : A j = 0 := by
    dsimp [count] at h
    have h' : (splitPrimes j).card = 0 := by exact_mod_cast h
    simp [A, card_eq_zero.mp h']
  have abel (n : ℕ) : (∑ p ∈ splitPrimes n, w p * f p) =
      w (n-1) * A n - ∑ j ∈ range (n-1), (w (j+1) - w j) * A (j+1) := by
    simpa [A, splitPrimes, sum_filter, mul_ite] using
      sum_range_by_parts w (fun p => if p.Prime ∧ p % 3 = 1 then f p else 0) n
  apply Metric.tendsto_nhds.mpr
  intro ε he
  let δ := ε / 24
  have hd' : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [uniformPrefix (A := A) (count := count) (fun n => Nat.cast_nonneg _) hz hc
    countsGrow cancel hd', weightBound hd, countsGrow.eventually_ge_atTop 1,
    eventually_ge_atTop 1] with n hsmall hweight hcount hn
  change w n * count n ≤ 6 * mass n at hweight
  change (1 : ℝ) ≤ count n at hcount
  have hmass : 0 < mass n := by
    have hn' : 0 < w n := sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
    nlinarith [mul_pos hn' (show 0 < count n by linarith)]
  have sumBound : |∑ j ∈ range (n-1), (w (j+1) - w j) * A (j+1)| ≤
      w (n-1) * (δ * count n) := calc
    _ ≤ ∑ j ∈ range (n-1), |(w (j+1) - w j) * A (j+1)| := abs_sum_le_sum_abs ..
    _ ≤ ∑ j ∈ range (n-1), (w (j+1) - w j) * (δ * count n) := sum_le_sum fun j hj => by
      have hdif := sub_nonneg.mpr (hw (Nat.le_succ j))
      rw [abs_mul, abs_of_nonneg hdif]
      exact mul_le_mul_of_nonneg_left (hsmall _ (by have := mem_range.mp hj; omega)) hdif
    _ = _ := by rw [← sum_mul, sum_range_sub]; simp [w]
  have hlast := mul_le_mul_of_nonneg_left (hsmall n le_rfl) (sqrt_nonneg ((n-1 : ℕ) : ℝ))
  have hbig := mul_le_mul_of_nonneg_right (hw (Nat.sub_le n 1)) (mul_nonneg hd'.le (Nat.cast_nonneg _ : 0 ≤ count n))
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hmass, div_lt_iff₀ hmass, abel]
  refine (abs_sub _ _).trans_lt ?_
  rw [abs_mul, abs_of_nonneg (sqrt_nonneg _)]
  change w (n-1) * |A n| + _ < ε * mass n
  dsimp only [w] at hlast ⊢
  dsimp only [w] at hbig hweight sumBound
  dsimp [δ] at hbig hlast sumBound
  nlinarith [mul_le_mul_of_nonneg_left hweight he.le, mul_pos he hmass]


private theorem weightedLimit (sieve : H1) (hd : H2) (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun n => (∑ p ∈ ((range n).filter fun p => p.Prime ∧ p % 3 = 1), √(p : ℝ) * g ((⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩ : ℂ).arg)) /
      ∑ p ∈ ((range n).filter fun p => p.Prime ∧ p % 3 = 1), √(p : ℝ)) atTop (𝓝 ((6 / π) * ∫ t in 0..π / 6, g t)) := by
  let splitPrimes (n : ℕ) := (range n).filter fun p => p.Prime ∧ p % 3 = 1
  let angle (p : ℕ) := (⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩ : ℂ).arg
  let L := (6 / π) * ∫ t in 0..π / 6, g t
  have hc : ∀ᶠ n : ℕ in atTop, (splitPrimes n).Nonempty := by
    filter_upwards [eventually_ge_atTop 8] with n hn
    exact ⟨7,mem_filter.mpr ⟨mem_range.mpr (by omega),by decide⟩⟩
  have cancel : Tendsto (fun n => (∑ p ∈ splitPrimes n, (g (angle p) - L)) /
      (splitPrimes n).card) atTop (𝓝 0) := by
    have h := (sieve g hg).sub_const L
    rw [show (6 / π) * (∫ t in 0..π / 6, g t) - L = 0 from sub_self L] at h
    apply h.congr'
    filter_upwards [hc] with n hn
    have hn' : ((splitPrimes n).card : ℝ) ≠ 0 := by exact_mod_cast hn.card_pos.ne'
    change (∑ p ∈ splitPrimes n, g (angle p)) / (splitPrimes n).card - L = _
    rw [sum_sub_distrib]
    simp [sub_div, hn', nsmul_eq_mul]
  have h := (transfer hd (fun p => g (angle p) - L) cancel).add_const L
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 8] with n hn
  have h7 : 7 ∈ splitPrimes n := mem_filter.mpr ⟨mem_range.mpr (by omega),by decide⟩
  have hm : 0 < ∑ p ∈ splitPrimes n, √(p : ℝ) :=
    (by norm_num : (0:ℝ) < √(7 : ℕ)).trans_le (single_le_sum (f := fun p : ℕ => √(p : ℝ)) (fun p _ => sqrt_nonneg (p:ℝ)) h7)
  change (∑ p ∈ splitPrimes n, √(p:ℝ) * (g (angle p) - L)) / (∑ p ∈ splitPrimes n, √(p:ℝ)) + L = (∑ p ∈ splitPrimes n, √(p:ℝ) * g (angle p)) / (∑ p ∈ splitPrimes n, √(p:ℝ))
  simp_rw [mul_sub, sum_sub_distrib, ← sum_mul]
  field_simp
  ring

theorem main : H1 → H2 → type_of% @OeisA218585.conjecture_3 := by
  let splitPrimes (n : ℕ) := (range n).filter fun p => p.Prime ∧ p % 3 = 1
  let angle (p : ℕ) := (⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩ : ℂ).arg
  intro sieve hd
  let g (a b t : ℝ) := a * cos t + b * sin t
  have integral (a b : ℝ) :
      (∫ t in 0..π / 6, g a b t) = a / 2 + b * (1 - √3 / 2) := by
    dsimp [g]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_cos, integral_sin]
    · simp [sin_pi_div_six, cos_pi_div_six]; ring
    all_goals apply Continuous.intervalIntegrable; fun_prop
  have limits (a b : ℝ) : Tendsto (fun n => (∑ p ∈ splitPrimes n, √(p:ℝ) * g a b (angle p)) / ∑ p ∈ splitPrimes n, √(p:ℝ)) atTop (𝓝 ((6 / π) * ∫ t in 0..π / 6, g a b t)) := weightedLimit sieve hd (g a b) (by dsimp [g]; fun_prop)
  have hx := limits 1 (-(√3) / 3)
  have hy := limits 0 (2 * √3 / 3)
  rw [integral] at hx hy
  have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have points (p : ℕ) (hp : p.Prime ∧ p % 3 = 1) :
      √(p : ℝ) * g 1 (-(√3) / 3) (angle p) = xp p ∧
      √(p : ℝ) * g 0 (2 * √3 / 3) (angle p) = yp p := by
    let x : ℝ := xp p
    let y : ℝ := yp p
    let z : ℂ := ⟨x + y / 2, √3 * y / 2⟩
    have hn : x^2 + x*y + y^2 = (p : ℝ) := by dsimp [x,y]; exact_mod_cast splitNorm p hp.1 hp.2
    have hz : ‖z‖ ^ 2 = (p : ℝ) := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      dsimp [z]
      linear_combination hn + (y^2/4)*hs
    have hnorm : ‖z‖ = √(p : ℝ) := by rw [← hz, sqrt_sq (norm_nonneg _)]
    have hc := Complex.norm_mul_cos_arg z
    have hi := Complex.norm_mul_sin_arg z
    rw [hnorm] at hc hi
    change √(p : ℝ) * cos z.arg = x + y / 2 at hc
    change √(p : ℝ) * sin z.arg = √3 * y / 2 at hi
    change √(p : ℝ) * (1 * cos z.arg + -(√3) / 3 * sin z.arg) = x ∧
      √(p : ℝ) * (0 * cos z.arg + 2 * √3 / 3 * sin z.arg) = y
    constructor
    · linear_combination hc - (√3/3)*hi - (y/6)*hs
    · linear_combination (2*√3/3)*hi + (y/3)*hs
  have sx (n : ℕ) : (∑ p ∈ splitPrimes n, √(p : ℝ) * g 1 (-(√3)/3) (angle p)) =
      ∑ p ∈ splitPrimes n, (xp p : ℝ) :=
    sum_congr rfl fun p hp => (points p (mem_filter.mp hp).2).1
  have sy (n : ℕ) : (∑ p ∈ splitPrimes n, √(p : ℝ) * g 0 (2*√3/3) (angle p)) =
      ∑ p ∈ splitPrimes n, (yp p : ℝ) :=
    sum_congr rfl fun p hp => (points p (mem_filter.mp hp).2).2
  simp_rw [sx] at hx
  simp_rw [sy] at hy
  have hpos : 0 < (6 / π) * (0 / 2 + 2 * √3 / 3 * (1 - √3 / 2)) := by
    have : 0 < 1 - √3 / 2 := by nlinarith [sqrt_nonneg (3:ℝ)]
    positivity
  have heq : (6 / π * (1 / 2 + -√3 / 3 * (1 - √3 / 2))) /
      (6 / π * (0 / 2 + 2 * √3 / 3 * (1 - √3 / 2))) = 1 + √3 := by
    apply (div_eq_iff hpos.ne').mpr
    ring_nf
    field_simp
    linear_combination (norm := ring_nf) (2 * √3 - 1) * hs
  have h := hx.div hy hpos.ne'
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 8] with n hn
  have h7 : 7 ∈ splitPrimes n := mem_filter.mpr ⟨mem_range.mpr (by omega),by decide⟩
  have hm : 0 < ∑ p ∈ splitPrimes n, √(p : ℝ) :=
    (by norm_num : (0:ℝ) < √(7 : ℕ)).trans_le (single_le_sum (f := fun p : ℕ => √(p : ℝ)) (fun p _ => sqrt_nonneg (p:ℝ)) h7)
  exact div_div_div_cancel_right₀ hm.ne' _ _

end OMA.R_OeisA218585_conjecture_3_R1
end

section
/- Integrated source: reductions/OeisA218585.conjecture_3.R1.H1.R1 -/
/- The log-weighted prime number theorem for nonprincipal angular Hecke characters
and the ordinary prime number theorem modulo three suffice. The sector geometry and
continuous cosine criterion are adapted from @PanPapag (#1373). We remove the log
weight by comparison with the total Chebyshev prime counting discrepancy. -/

namespace OMA.R_OeisA218585_conjecture_3_R1_H1_R1

open OeisA218585 Real Filter MeasureTheory Finset
open scoped Topology BigOperators

def H1 : Prop :=
  let primes (N : ℕ) := (range N).filter fun p => p.Prime ∧ p % 3 = 1
  let z (p : ℕ) : ℂ := ⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩
  ∀ k : ℕ, k ≠ 0 → Tendsto (fun N =>
    (∑ p ∈ primes N, log p * cos ((k : ℝ) * (6 * (z p).arg))) / N) atTop (𝓝 0)

def H2 : Prop :=
  let primes (N : ℕ) := (range N).filter fun p => p.Prime ∧ p % 3 = 1
  Tendsto (fun N => (∑ p ∈ primes N, log p) / N) atTop (𝓝 (1/2 : ℝ))

lemma ordinate_le_abscissa (p : ℕ) : yp p ≤ xp p := by
  let hasOrdinate (u : ℕ) := (List.range u).any fun v =>
    0 < v && u ^ 2 + u * v + v ^ 2 == p
  let hasAbscissa (v : ℕ) := 0 < v && (List.Ico (v + 1) p).any fun u =>
    u ^ 2 + u * v + v ^ 2 == p
  change ((List.range p).find? hasAbscissa).getD 0 ≤ ((List.range p).find? hasOrdinate).getD 0
  cases hy : (List.range p).find? hasAbscissa with
  | none => simp
  | some y =>
    obtain ⟨hypos, u, ⟨hyu, hup⟩, hu⟩ :
        0 < y ∧ ∃ u, (y + 1 ≤ u ∧ u < p) ∧ u ^ 2 + u * y + y ^ 2 = p := by
      simpa [hasAbscissa] using List.find?_some hy
    have hX : hasOrdinate u := by simpa [hasOrdinate] using
      (show ∃ v < u, 0 < v ∧ u ^ 2 + u * v + v ^ 2 = p from ⟨y, by omega, hypos, hu⟩)
    cases hx : (List.range p).find? hasOrdinate with
    | none => exact False.elim ((List.find?_eq_none.mp hx u (List.mem_range.mpr hup)) hX)
    | some x =>
      obtain ⟨v, hvx, _, hv⟩ : ∃ v < x, 0 < v ∧ x ^ 2 + x * v + v ^ 2 = p := by
        simpa [hasOrdinate] using List.find?_some hx
      change y ≤ x
      by_contra! h
      have hxu : x < u := by omega
      have hvy : v < y := by omega
      nlinarith [Nat.pow_lt_pow_left hxu (by decide : 2 ≠ 0),
        Nat.mul_le_mul hxu.le hvy.le, Nat.pow_le_pow_left hvy.le 2]

lemma sector_angle (p : ℕ) :
    (⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩ : ℂ).arg ∈
      Set.Icc 0 (π / 6) := by
  let x : ℝ := xp p
  let y : ℝ := yp p
  let z : ℂ := ⟨x + y / 2, √3 * y / 2⟩
  change z.arg ∈ _
  have hy : 0 ≤ y := Nat.cast_nonneg _
  have hxy : y ≤ x := by dsimp [x, y]; exact_mod_cast ordinate_le_abscissa p
  have hx : 0 ≤ x := hy.trans hxy
  have hs : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨Complex.arg_nonneg_iff.mpr (show 0 ≤ √3 * y / 2 by positivity), ?_⟩
  by_cases hz : z = 0
  · rw [hz, Complex.arg_zero]; positivity
  have hn := norm_pos_iff.mpr hz
  have hns : ‖z‖ ^ 2 = x ^ 2 + x * y + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [z]
    linear_combination (y ^ 2 / 4) * hs
  have bound : √3 * y ≤ ‖z‖ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ x + 2 * y by positivity),
      show (√3 * y) ^ 2 = 3 * y ^ 2 by rw [mul_pow, hs]]
  rw [Complex.arg_of_re_nonneg (show 0 ≤ x + y / 2 by positivity),
      ← Real.arcsin_sin (x := π / 6) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
      Real.sin_pi_div_six]
  apply Real.monotone_arcsin
  apply (div_le_iff₀ hn).mpr
  change √3 * y / 2 ≤ _
  linarith

open Polynomial Polynomial.Chebyshev

/-- Finite cosine sums are uniformly dense on the fundamental sector. -/
lemma cosine_approximation (f : ℝ → ℝ) (hf : Continuous f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (K : ℕ) (c : ℕ → ℝ), ∀ t ∈ Set.Icc 0 (π / 6),
      |(∑ k ∈ Finset.range K, c k * cos (k * (6 * t))) - f t| < δ := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1
    (fun u => f (arccos u / 6)) (by fun_prop) δ hδ
  let K := p.natDegree + 1
  have hmem : p ∈ degreeLT ℝ K := by
    rw [mem_degreeLT]
    exact p.degree_le_natDegree.trans_lt (by dsimp [K]; exact_mod_cast Nat.lt_succ_self _)
  rw [← Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp),
    show Set.Iio K = (Finset.range K : Set ℕ) by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨K, c, fun t ht => ?_⟩
  have h := hp (cos (6 * t)) (cos_mem_Icc _)
  rw [arccos_cos (by linarith [ht.1]) (by linarith [ht.2]),
    show 6 * t / 6 = t by ring, ← hc] at h
  simpa [eval_finsetSum, eval_smul, chebyshevTsequence, smul_eq_mul] using h

lemma integral_cosine_mode (k : ℕ) (hk : k ≠ 0) :
    (∫ t in 0..π / 6, cos (k * (6 * t))) = 0 := by
  have h : (k : ℝ) * 6 ≠ 0 := by positivity
  simp_rw [← mul_assoc]
  rw [intervalIntegral.integral_comp_mul_left _ h, integral_cos, mul_zero,
    show (k : ℝ) * 6 * (π / 6) = k * π by ring, Real.sin_nat_mul_pi, Real.sin_zero]
  simp

/-- A weighted Weyl criterion on the sector, using the real parts of the angular characters. -/
lemma sector_criterion (P : ℕ → Finset ℕ) (θ : ℕ → ℝ) (w : ℕ → ℕ → ℝ)
    (hθ : ∀ p, θ p ∈ Set.Icc 0 (π / 6)) (hw : ∀ n p, 0 ≤ w n p)
    (hunit : ∀ᶠ n in atTop, ∑ p ∈ P n, w n p = 1)
    (modes : ∀ k : ℕ, k ≠ 0 → Tendsto
      (fun n => ∑ p ∈ P n, w n p * cos (k * (6 * θ p))) atTop (𝓝 0))
    (f : ℝ → ℝ) (hf : Continuous f) :
    Tendsto (fun n => ∑ p ∈ P n, w n p * f (θ p)) atTop
      (𝓝 ((6 / π) * ∫ t in 0..π / 6, f t)) := by
  let M (n : ℕ) (g : ℝ → ℝ) := ∑ p ∈ P n, w n p * g (θ p)
  let J (g : ℝ → ℝ) := (6 / π) * ∫ t in 0..π / 6, g t
  let mode (k : ℕ) (t : ℝ) := cos ((k : ℝ) * (6 * t))
  have hmode (k : ℕ) : Tendsto (fun n => M n (mode k)) atTop (𝓝 (J (mode k))) := by
    by_cases hk : k = 0
    · subst k
      have one : J (mode 0) = 1 := by simp [J, mode]
      rw [one]
      apply tendsto_const_nhds.congr'
      filter_upwards [hunit] with n hn
      simpa [M, mode] using hn.symm
    · simpa [J, mode, integral_cosine_mode k hk] using modes k hk
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, c, happ⟩ := cosine_approximation f hf δ hδ
  let g (t : ℝ) := ∑ k ∈ Finset.range K, c k * mode k t
  have hg : Continuous g := by dsimp [g, mode]; fun_prop
  have rearrange (n : ℕ) : M n g = ∑ k ∈ Finset.range K, c k * M n (mode k) := by
    dsimp [M, g]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have integrate : J g = ∑ k ∈ Finset.range K, c k * J (mode k) := by
    dsimp [J, g]
    rw [intervalIntegral.integral_finsetSum (fun k _ =>
      (show Continuous (fun t => c k * mode k t) by dsimp [mode]; fun_prop).intervalIntegrable _ _)]
    simp_rw [intervalIntegral.integral_const_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hlim : Tendsto (fun n => M n g) atTop (𝓝 (J g)) := by
    simp_rw [rearrange, integrate]
    exact tendsto_finsetSum _ fun k _ => (hmode k).const_mul _
  have hi : |J g - J f| ≤ δ := by
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π / 6)
      (C := δ) (f := fun t => g t - f t) (by
        intro t ht
        rw [Set.uIoc_of_le (by positivity : 0 ≤ π / 6)] at ht
        exact (happ t ⟨ht.1.le, ht.2⟩).le)
    rw [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) (hf.intervalIntegrable _ _)] at hI
    dsimp [J]
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 6 / π)]
    apply (mul_le_mul_of_nonneg_left hI (by positivity : 0 ≤ 6 / π)).trans
    rw [sub_zero, abs_of_pos (by positivity : 0 < π / 6)]
    apply le_of_eq
    field_simp
  filter_upwards [(Metric.tendsto_nhds.mp hlim) δ hδ, hunit] with n hn hu
  have he : |M n g - M n f| ≤ δ := calc
    _ = |∑ p ∈ P n, w n p * (g (θ p) - f (θ p))| := by simp [M, mul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ p ∈ P n, |w n p * (g (θ p) - f (θ p))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P n, w n p * δ := Finset.sum_le_sum fun p _ => by
      rw [abs_mul, abs_of_nonneg (hw n p)]
      exact mul_le_mul_of_nonneg_left (happ _ (hθ p)).le (hw n p)
    _ = δ := by rw [← Finset.sum_mul, hu, one_mul]
  change dist (M n f) (J f) < ε
  rw [Real.dist_eq] at hn ⊢
  have h₁ := abs_le.mp he
  have h₂ := abs_le.mp hi
  have h₃ := abs_lt.mp hn
  dsimp [δ] at *
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

lemma log_gap_tendsto :
    Tendsto (fun N : ℕ => (∑ p ∈ Nat.primesLE N, (log N - log p)) / (N:ℝ)) atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := (Chebyshev.primeCounting_sub_theta_div_log_isBigO.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).exists_pos
  have hlim : Tendsto (fun N : ℕ => C / log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hC.2.bound,eventually_ge_atTop 2] with N hn hN
  have pos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have lp : 0 < log N := log_pos (by exact_mod_cast (show 1 < N by omega))
  change ‖(Nat.primeCounting ⌊(N:ℝ)⌋₊:ℝ) - Chebyshev.theta N / log N‖ ≤ C * ‖(N:ℝ) / log N ^ 2‖ at hn
  rw [Nat.floor_natCast,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (N:ℝ) / log N ^ 2)] at hn
  rw [sum_sub_distrib,sum_const,nsmul_eq_mul,Nat.primesLE_card_eq_primeCounting,
    ← Chebyshev.theta_eq_sum_primesLE_log]
  rw [Real.norm_eq_abs,abs_div,abs_of_pos pos,div_le_div_iff₀ pos lp]
  have he : (Nat.primeCounting N : ℝ)*log N - Chebyshev.theta N =
      ((Nat.primeCounting N:ℝ)-Chebyshev.theta N / log N)*log N := by field_simp
  rw [he,abs_mul,abs_of_pos lp]
  calc
    _ ≤ (C * ((N:ℝ) / log N ^ 2)) * log N * log N :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn lp.le) lp.le
    _ = _ := by field_simp

lemma remove_log_weight (P : ℕ → Finset ℕ) (hP : ∀ N,P N ⊆ Nat.primesLE N)
    (v : ℕ → ℝ) (hv : ∀ p, |v p| ≤ 1) (L : ℝ)
    (hw : Tendsto (fun N => (∑ p ∈ P N, log p * v p) / (N:ℝ)) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => log N * (∑ p ∈ P N, v p) / (N:ℝ)) atTop (𝓝 L) := by
  let E (N : ℕ) := (∑ p ∈ P N, (log N-log p)*v p) / (N:ℝ)
  have hE : Tendsto E atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ log_gap_tendsto
    filter_upwards with N
    have gap (p : ℕ) (hp : p ∈ Nat.primesLE N) : 0 ≤ log N - log p := by
      obtain ⟨hle,hprime⟩ := Nat.mem_primesLE.mp hp
      exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hle))
    change ‖(∑ p ∈ P N, (log N-log p)*v p) / (N:ℝ)‖ ≤ _
    rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (show (0:ℝ) ≤ (N:ℝ) from Nat.cast_nonneg N)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg (hP N) (fun p hp _ => gap p hp))
    apply sum_le_sum
    intro p hp
    rw [abs_mul, abs_of_nonneg (gap p (hP N hp))]
    exact mul_le_of_le_one_right (gap p (hP N hp)) (hv p)
  have h := hE.add hw
  rw [zero_add] at h
  apply h.congr
  intro N
  simp only [E,sub_mul,sum_sub_distrib,← Finset.mul_sum,← add_div]
  ring

theorem main : H1 → H2 → OMA.R_OeisA218585_conjecture_3_R1.H1 := by
  intro modes mass f hf
  let P (N : ℕ) := (range N).filter fun p => p.Prime ∧ p % 3 = 1
  let θ (p : ℕ) := (⟨(xp p : ℝ) + (yp p : ℝ)/2, √3 * (yp p : ℝ)/2⟩ : ℂ).arg
  have sub (N : ℕ) : P N ⊆ Nat.primesLE N := by
    intro p hp
    obtain ⟨hp,hp',_⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨(mem_range.mp hp).le,hp'⟩
  have den : Tendsto (fun N : ℕ => log N * (P N).card / (N:ℝ)) atTop (𝓝 (1/2:ℝ)) := by
    simpa using remove_log_weight P sub (fun _ => 1) (by simp) _ (by simpa [P,H2] using mass)
  have cardpos : ∀ᶠ N in atTop, (P N).Nonempty := by
    filter_upwards [eventually_ge_atTop 8] with N hn
    exact ⟨7,mem_filter.mpr ⟨mem_range.mpr (by omega),by decide⟩⟩
  let w (N p : ℕ) : ℝ := ((P N).card : ℝ)⁻¹
  have hu : ∀ᶠ N in atTop, ∑ p ∈ P N, w N p = 1 := by
    filter_upwards [cardpos] with N hn
    simp [w,hn.card_ne_zero]
  have hc (k : ℕ) (hk : k ≠ 0) : Tendsto
      (fun N => ∑ p ∈ P N, w N p * cos ((k:ℝ)*(6*θ p))) atTop (𝓝 0) := by
    let v (p : ℕ) := cos ((k:ℝ)*(6*θ p))
    have raw := remove_log_weight P sub v (fun p => abs_cos_le_one _) 0 (modes k hk)
    have divlim := raw.div den (by norm_num)
    rw [zero_div] at divlim
    apply divlim.congr'
    filter_upwards [eventually_ge_atTop 2] with N hn
    have l : log N ≠ 0 := (log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
    have n : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    simp only [w,← Finset.mul_sum]
    change log N * (∑ p ∈ P N, v p) / N / (log N * (P N).card / N) = _ * (∑ p ∈ P N,v p)
    by_cases h : (P N).card = 0
    · simp [h]
    · field_simp [l,n,h]
  have he := sector_criterion P θ w sector_angle (by intro n p; dsimp [w]; positivity) hu hc f hf
  change Tendsto (fun n => (∑ p ∈ P n, f (θ p)) / (P n).card) atTop _
  simpa only [w,← Finset.mul_sum,div_eq_inv_mul] using he

end OMA.R_OeisA218585_conjecture_3_R1_H1_R1
end

section
/- Integrated source: reductions/OeisA218585.conjecture_4.R1.H2.R1.H1.R1 -/
/- We separate the boundary behavior of the angular Dirichlet series
from the real Tauberian theorem and the ordinary prime number theorem in
the progression one modulo three. Subtracting the two nonnegative
coefficient sequences gives the signed angular series. -/
namespace OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1
open Finset OeisA218585 Filter Real ArithmeticFunction
open scoped Topology

/-- Hecke's boundary theorem for the two nonnegative shifts of each angular mode. -/
def H1 : Prop :=
  let z (p : ℕ) : ℂ := ⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩
  ∀ k : ℕ, k ≠ 0 → ∀ e : ℝ, |e| = 1 →
    let w (n : ℕ) := if n.Prime ∧ n%3=1 then cos ((k:ℝ)*(6*(z n).arg)) else 0
    ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧
      Set.EqOn G (fun s => LSeries (fun n => ((Λ n * (1+e*w n) : ℝ) : ℂ)) s -
        1/(s-1)) {s | 1 < s.re}

/-- A dominated form of the Wiener–Ikehara theorem for a pole with residue one. -/
def H2 : Prop := ∀ f : ℕ → ℝ, (∀ n, 0 ≤ f n ∧ f n ≤ 2*Λ n) →
  (∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧
    Set.EqOn G (fun s => LSeries (fun n => (f n : ℂ)) s - 1/(s-1)) {s | 1 < s.re}) →
  Tendsto (fun N : ℕ => (∑ n ∈ range N, f n)/N) atTop (𝓝 1)

/-- The ordinary prime number theorem and its theta form, with the same strict cutoff. -/
def H3 : Prop :=
  let P (N : ℕ) := (range N).filter fun p => p.Prime ∧ p%3=1
  Tendsto (fun N : ℕ => ((P N).card:ℝ)*Real.log N/N) atTop (𝓝 (1/2:ℝ)) ∧
  Tendsto (fun N : ℕ => (∑ p ∈ P N, Real.log p)/N) atTop (𝓝 (1/2:ℝ))

end OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1
end

section
/- Integrated source: reductions/OeisA218585.conjecture_4.R1.H2.R1.H1.R1.H1.R1 -/
/- For the incomplete Eisenstein Hecke L-function, the two conjugate
prime ideals above a split prime give twice the angular cosine. The
remaining prime-power terms converge uniformly on the closed half-plane. -/
namespace OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1

open OeisA218585 Real ArithmeticFunction
open scoped Classical

/-- Analyticity and nonvanishing of the incomplete Hecke L-function of
nonzero angular type, together with its logarithmic Euler expansion.
The factor at the ramified prime three is omitted. -/
def H1 : Prop :=
  let z (p : ℕ) : ℂ := ⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩
  ∀ k : ℕ, k ≠ 0 → ∃ (L : ℂ → ℂ) (a : ℕ → ℂ),
    (∀ s : ℂ, 1 ≤ s.re → AnalyticAt ℂ L s ∧ L s ≠ 0) ∧
    (∀ n, ‖a n‖ ≤ Λ n) ∧
    (∀ p : ℕ, p.Prime → a p = ((Λ p * (if p%3=1 then cos ((k:ℝ)*(6*(z p).arg))
      else 0) : ℝ) : ℂ)) ∧
    ∀ s : ℂ, 1 < s.re → LSeries a s = -deriv L s / (2*L s)

/-- Absolute convergence on the closed boundary for the higher prime powers. -/
def H2 : Prop := ∀ b : ℕ → ℂ, (∀ p : ℕ, p.Prime → b p=0) → (∀ n, ‖b n‖ ≤ Λ n) →
  ContinuousOn (LSeries b) {s : ℂ | 1 ≤ s.re}

lemma dominated_series {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ Λ n) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable a s := by
  apply Summable.of_norm_bounded (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm
  intro n
  apply LSeries.norm_term_le
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg] using ha n

theorem main : H1 → H2 → OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1.H1 := by
  intro hecke power k hk e _he
  obtain ⟨L,a,hL,ha,hp,logder⟩ := hecke k hk
  let z (p : ℕ) : ℂ := ⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩
  let w (n : ℕ) := if n.Prime ∧ n%3=1 then cos ((k:ℝ)*(6*(z n).arg)) else 0
  let b (n : ℕ) : ℂ := if n.Prime then 0 else a n
  let v (n : ℕ) : ℂ := (Λ n : ℝ)
  have hb n : ‖b n‖ ≤ Λ n := by dsimp [b]; split <;> simp_all only [norm_zero,vonMangoldt_nonneg]
  have H := power b (fun p h => by simp [b,h]) hb
  let F := vonMangoldt.LFunctionResidueClassAux (q:=1) 1
  have fC : ContinuousOn F {s : ℂ | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have lC : ContinuousOn L {s : ℂ | 1 ≤ s.re} := fun s hs => (hL s hs).1.continuousAt.continuousWithinAt
  have dC : ContinuousOn (deriv L) {s : ℂ | 1 ≤ s.re} := fun s hs =>
    (hL s hs).1.deriv.continuousAt.continuousWithinAt
  refine ⟨fun s => F s + (e:ℂ)*(-deriv L s/(2*L s)-LSeries b s), ?_, ?_⟩
  · exact fC.add (continuousOn_const.mul (((dC.neg.div (continuousOn_const.mul lC)
      (fun s hs => mul_ne_zero (by norm_num) (hL s hs).2))).sub H))
  intro s hs
  have hs' : 1<s.re := hs
  have fId : F s = LSeries v s - 1/(s-1) := by
    have old := vonMangoldt.eqOn_LFunctionResidueClassAux (q:=1) isUnit_one hs'
    rw [show F s = _ from old]
    simp only [Nat.totient_one,Nat.cast_one,inv_one,sub_left_inj]
    apply LSeries_congr
    intro n _
    simp [v,vonMangoldt.residueClass,Subsingleton.elim (n:ZMod 1) (1:ZMod 1)]
  have vSumm : LSeriesSummable v s := ArithmeticFunction.LSeriesSummable_vonMangoldt hs'
  have aSumm := dominated_series ha hs'
  have bSumm := dominated_series hb hs'
  have recombine : (fun n => ((Λ n*(1+e*w n):ℝ):ℂ)) = v + (e:ℂ) • (a-b) := by
    funext n
    simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,v,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_one]
    by_cases hn : n.Prime
    · rw [hp n hn]
      by_cases hm : n%3=1 <;> simp [w,b,hn,hm,z]
      ring
    · simp [w,b,hn]
  change F s + (e:ℂ)*(-deriv L s/(2*L s)-LSeries b s) =
    LSeries (fun n => ((Λ n*(1+e*w n):ℝ):ℂ)) s - 1/(s-1)
  rw [recombine,LSeries_add vSumm ((aSumm.sub bSumm).smul _),LSeries_smul,
    LSeries_sub aSumm bSumm,fId,logder s hs']
  ring

end OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1
end

section
/- Integrated source: reductions/OeisA218585.conjecture_4.R1.H2.R1.H1.R1.H1.R1.H1.R1 -/
/- The de la Vallée Poussin argument for Eisenstein angular characters.
The two angular frequencies k and 2k leave sufficient positivity to
exclude a zero on the boundary. Only the prime coefficients are needed
for this argument because higher prime powers converge there absolutely. -/
namespace OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1
open OeisA218585 Filter Real ArithmeticFunction
open scoped Topology Classical

/-- Continuation and the logarithmic derivative in the open half-plane. -/
def H1 : Prop := let z (p : ℕ) : ℂ := ⟨(xp p:ℝ)+(yp p:ℝ)/2,√3*(yp p:ℝ)/2⟩
  ∀ k : ℕ, k ≠ 0 → ∃ (L : ℂ → ℂ) (a : ℕ → ℂ),
    (∀ s : ℂ, 1 ≤ s.re → AnalyticAt ℂ L s) ∧ (∀ s : ℂ, 1 < s.re → L s ≠ 0) ∧
    (∀ n, ‖a n‖ ≤ Λ n) ∧ (∀ p : ℕ, p.Prime → a p =
      ((Λ p*(if p%3 = 1 then cos ((k:ℝ)*(6*(z p).arg)) else 0):ℝ):ℂ)) ∧
    ∀ s : ℂ, 1 < s.re → LSeries a s = -deriv L s/(2*L s)

/-- The three-four-one trigonometric estimate for split prime coefficients.
The limiting lower bound is -3/2, so -7/4 leaves a fixed margin. -/
def H2 : Prop := ∀ (θ : ℕ → ℝ) (a b : ℕ → ℂ), (∀ n, ‖a n‖ ≤ Λ n) → (∀ n, ‖b n‖ ≤ Λ n) →
  (∀ p : ℕ, p.Prime → a p = ((Λ p*(if p%3 = 1 then cos (θ p) else 0):ℝ):ℂ)) →
  (∀ p : ℕ, p.Prime → b p = ((Λ p*(if p%3 = 1 then cos (2*θ p) else 0):ℝ):ℂ)) →
  ∀ t : ℝ, ∀ᶠ h : ℝ in 𝓝[>] 0, -(7/4:ℝ) ≤ h *
    (4*(LSeries a ((⟨1,t⟩:ℂ)+h)).re + (LSeries b ((⟨1,2*t⟩:ℂ)+h)).re)

lemma horizontal_order {L : ℂ → ℂ} {a : ℕ → ℂ} {s : ℂ} (sr : s.re = 1)
    (an : AnalyticAt ℂ L s) (nz : ∀ z : ℂ, 1 < z.re → L z ≠ 0)
    (eq : ∀ z : ℂ, 1 < z.re → LSeries a z = -deriv L z/(2*L z)) :
    ∃ m : ℕ, (L s = 0 → 0 < m) ∧
      Tendsto (fun h : ℝ => h*(LSeries a (s+h)).re) (𝓝[>] 0) (𝓝 (-(m:ℝ)/2)) := by
  let z (h : ℝ) := s+(h:ℂ)
  have zl : Tendsto z (𝓝[>] 0) (𝓝 s) := by
    have hc : ContinuousAt (fun h : ℝ => s+(h:ℂ)) 0 := by fun_prop
    simpa [z] using hc.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  have half (h : ℝ) (hp : 0 < h) : 1 < (z h).re := by simp [z,sr,hp]
  have good : analyticOrderAt L s ≠ ⊤ := by
    intro top
    obtain ⟨h,zero,hp⟩ := ((zl.eventually (analyticOrderAt_eq_top.mp top)).and
      (self_mem_nhdsWithin : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h)).exists
    exact nz (z h) (half h hp) zero
  let m := analyticOrderNatAt L s
  obtain ⟨g,ga,gn,eg⟩ := (an.analyticOrderNatAt_eq_iff good).mp (rfl : analyticOrderNatAt L s = m)
  have prodEq : L =ᶠ[𝓝 s] (fun w => (w-s)^m*g w) := by
    filter_upwards [eg] with w hw
    simpa [m,smul_eq_mul] using hw
  refine ⟨m,?_,?_⟩
  · intro ls
    by_contra! bad
    have em : m = 0 := by omega
    have h := prodEq.self_of_nhds
    simp [ls,em] at h
    exact gn h.symm
  have hg : ContinuousAt (logDeriv g) s := ga.deriv.continuousAt.div ga.continuousAt gn
  have ht0 : Tendsto (fun h : ℝ => (h:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have li : Tendsto (fun h : ℝ => (m:ℂ)+(h:ℂ)*logDeriv g (z h)) (𝓝[>] 0) (𝓝 (m:ℂ)) := by
    simpa using (tendsto_const_nhds (x:=(m:ℂ))).add (ht0.mul (hg.tendsto.comp zl))
  have inC : Tendsto (fun h : ℝ => (h:ℂ)*LSeries a (z h)) (𝓝[>] 0) (𝓝 (-(m:ℂ)/2)) := by
    apply (li.neg.div_const 2).congr'
    filter_upwards [self_mem_nhdsWithin,zl.eventually prodEq,zl.eventually prodEq.deriv,
      zl.eventually ga.eventually_analyticAt,zl.eventually (ga.continuousAt.eventually_ne gn)] with h hp val der dg gne
    change 0 < h at hp
    have hc : (h:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have diff : z h-s ≠ 0 := by simpa [z] using hc
    have ld : logDeriv L (z h)= (m:ℂ)/(h:ℂ)+logDeriv g (z h) := by
      calc
        _ = logDeriv (fun w => (w-s)^m*g w) (z h) := by simp only [logDeriv_apply,der,val]
        _ = logDeriv (fun w : ℂ => (w-s)^m) (z h)+logDeriv g (z h) :=
          logDeriv_mul _ (pow_ne_zero _ diff) gne (by fun_prop) dg.differentiableAt
        _ = _ := by rw [logDeriv_fun_pow (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w-s) (z h)) m]
                    simp [logDeriv_apply,z,div_eq_mul_inv]
    change -((m:ℂ)+(h:ℂ)*logDeriv g (z h))/2 = (h:ℂ)*LSeries a (z h)
    rw [eq _ (half h hp)]
    have conv : -deriv L (z h)/(2*L (z h))= -logDeriv L (z h)/2 := by rw [logDeriv_apply]; ring
    rw [conv,ld]
    field_simp
  simpa [Function.comp_def,z,Complex.mul_re,Complex.div_ofNat_re] using (Complex.continuous_re.continuousAt.tendsto.comp inC)

theorem main : H1 → H2 → OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1.H1 := by
  intro data positivity k hk
  obtain ⟨L,a,an,nz,ab,ap,ae⟩ := data k hk
  obtain ⟨F,b,fan,fnz,bb,bp,be⟩ := data (2*k) (by omega)
  refine ⟨L,a,fun s hs => ⟨an s hs,?_⟩,ab,ap,ae⟩
  rcases hs.lt_or_eq with inside | boundary
  · exact nz s inside
  · intro bad
    let t := s.im
    let u : ℂ := ⟨1,2*t⟩
    have es : s = (⟨1,t⟩:ℂ) := Complex.ext boundary.symm rfl
    obtain ⟨m,mpos,lm⟩ := horizontal_order boundary.symm (an s boundary.le) nz ae
    obtain ⟨j,_,lj⟩ := horizontal_order (s:=u) rfl (fan u le_rfl) fnz be
    let θ := fun p : ℕ => (k:ℝ)*(6*(⟨(xp p:ℝ)+(yp p:ℝ)/2,√3*(yp p:ℝ)/2⟩:ℂ).arg)
    have bprime (p : ℕ) (pp : p.Prime) :
        b p = ((Λ p*(if p%3 = 1 then cos (2*θ p) else 0):ℝ):ℂ) := by
      convert bp p pp using 1
      dsimp [θ]
      push_cast
      ring_nf
    have eventual := positivity θ a b ab bb ap bprime t
    have lim := (lm.const_mul 4).add lj
    have cmp : -(7/4:ℝ) ≤ 4*(-(m:ℝ)/2)+(-(j:ℝ)/2) := by
      apply ge_of_tendsto lim
      filter_upwards [eventual] with h H
      rw [es]
      dsimp [u] at *
      linarith only [H]
    have hm : (1:ℝ) ≤ m := by exact_mod_cast mpos bad
    have hj := Nat.cast_nonneg j (α:=ℝ)
    linarith

end OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1
end

section
/- Integrated source: proofs/OeisA218585.conjecture_4.R1.H2.R1.H1.R1.H1.R1.H1.R1.H1 -/
-- Credit: @JaviSoto
/- The nontrivial angular character on the Eisenstein lattice. H1 is an
archimedean lattice cancellation statement; H2 is the Euler factorization in
the region of absolute convergence. Removing the ramified factor at 3 gives
zero logarithmic-derivative coefficient there, as the parent requires. -/
namespace OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1
open OeisA218585 Real Filter ArithmeticFunction LSeries
open scoped Topology

/-- Holomorphic continuation of the lattice sum in each nonzero angular mode. -/
def H1 : Prop :=
  let z (u : ℤ × ℤ) : ℂ := u.1 + u.2 * ((1+Complex.I*(Real.sqrt 3 : ℂ))/2)
  let S (m : ℕ) (s : ℂ) := ∑' u : ℤ × ℤ, if z u=0 then (0:ℂ) else
    (z u/(‖z u‖:ℂ))^m*(‖z u‖:ℂ)^(-2*s)
  ∀ m : ℕ, m ≠ 0 → ∃ (F : ℂ → ℂ), (∀ s : ℂ, 1 ≤ s.re → AnalyticAt ℂ F s) ∧
    ∀ s : ℂ, 1<s.re → F s = S m s

/-- Euler factorization into split conjugate primes and norm-square inert primes.
The six units account for the division by six; the factor at three is removed. -/
def H2 : Prop :=
  let z (u : ℤ × ℤ) : ℂ := u.1 + u.2 * ((1+Complex.I*(Real.sqrt 3 : ℂ))/2)
  let S (m : ℕ) (s : ℂ) := ∑' u : ℤ × ℤ, if z u=0 then (0:ℂ) else
    (z u/(‖z u‖:ℂ))^m*(‖z u‖:ℂ)^(-2*s)
  let θ (k p : ℕ) := (k:ℝ)*(6*(⟨(xp p:ℝ)+(yp p:ℝ)/2,√3*(yp p:ℝ)/2⟩:ℂ).arg)
  let phase (k n : ℕ) : ℝ :=
    let p := n.minFac
    let j := n.factorization p
    if p%3=1 then cos (j*θ k p) else if p%3=2 ∧ Even j then 1 else 0
  let a (k n : ℕ) : ℂ := ((Λ n*phase k n : ℝ):ℂ)
  let b (k n : ℕ) : ℂ := a k n/(Real.log n:ℝ)
  ∀ k : ℕ, k≠0 → ∀ s : ℂ, 1<s.re →
    (1-(-1:ℂ)^k*(3:ℂ)^(-s))*(S (6*k) s/6) = Complex.exp (2*LSeries (b k) s)

theorem main : H1 → H2 → OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1.H1 := by
  intro lattice factors k hk
  let z (u : ℤ × ℤ) : ℂ := u.1 + u.2 * ((1+Complex.I*(Real.sqrt 3 : ℂ))/2)
  let S (m : ℕ) (s : ℂ) := ∑' u : ℤ × ℤ, if z u=0 then (0:ℂ) else
    (z u/(‖z u‖:ℂ))^m*(‖z u‖:ℂ)^(-2*s)
  let θ (k p : ℕ) := (k:ℝ)*(6*(⟨(xp p:ℝ)+(yp p:ℝ)/2,√3*(yp p:ℝ)/2⟩:ℂ).arg)
  let phase (k n : ℕ) : ℝ :=
    let p := n.minFac
    let j := n.factorization p
    if p%3=1 then cos (j*θ k p) else if p%3=2 ∧ Even j then 1 else 0
  let a (k n : ℕ) : ℂ := ((Λ n*phase k n : ℝ):ℂ)
  let b (k n : ℕ) : ℂ := a k n/(Real.log n:ℝ)
  obtain ⟨F,an,agree⟩ := lattice (6*k) (Nat.mul_ne_zero (by decide) hk)
  let L (s : ℂ) := (1-(-1:ℂ)^k*(3:ℂ)^(-s))*(F s/6)
  let E (s : ℂ) := Complex.exp (2*LSeries (b k) s)
  have cont (s : ℂ) (hs : 1<s.re) : L s=E s := by
    dsimp only [L,E]; rw [agree s hs]; exact factors k hk s hs
  have ba (n : ℕ) : ‖a k n‖ ≤ Λ n := by
    have h : |phase k n| ≤ 1 := by dsimp [phase]; split_ifs <;> simp [abs_cos_le_one]
    simpa [a,abs_mul,abs_of_nonneg vonMangoldt_nonneg] using
      mul_le_mul_of_nonneg_left h (vonMangoldt_nonneg (n:=n))
  have bb (n : ℕ) : ‖b k n‖ ≤ 1 := by
    by_cases hn : n ≤ 1
    · interval_cases n <;> simp [b,a]
    · have pos := Real.log_pos (by exact_mod_cast (show 1<n by omega) : (1:ℝ)<n)
      change ‖a k n / ((Real.log n : ℝ) : ℂ)‖ ≤ 1
      have nlog : ‖((Real.log n:ℝ):ℂ)‖ = Real.log n := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos]
      rw [norm_div,nlog,div_le_one pos]
      exact (ba n).trans vonMangoldt_le_log
  have logb : LSeries.logMul (b k)=a k := by
    funext n
    by_cases hn : n≤1
    · interval_cases n <;> simp [LSeries.logMul,b,a]
    · have pos := Real.log_pos (by exact_mod_cast (show 1<n by omega) : (1:ℝ)<n)
      have nz : ((Real.log n:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pos.ne'
      simp only [LSeries.logMul,b,←Complex.natCast_log]
      field_simp
  refine ⟨L,a k,?_,fun s hs => (cont s hs) ▸ Complex.exp_ne_zero _,ba,?_,?_⟩
  · intro s hs
    have d := an s hs
    dsimp only [L]
    rw [show (fun z : ℂ => (1-(-1:ℂ)^k*(3:ℂ)^(-z))*(F z/6)) =
      (fun z : ℂ => (1-(-1:ℂ)^k*Complex.exp (Complex.log 3*(-z)))*(F z/6)) by
      funext z; rw [Complex.cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0)]]
    fun_prop
  · intro p hp; simp [a,phase,θ,hp.minFac_eq,hp.factorization_self]
  · intro s hs
    have ac : abscissaOfAbsConv (b k) ≤ (1:ℝ) :=
      abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
        LSeriesSummable_of_bounded_of_one_lt_re (m:=1) (fun n _ => bb n) (by simpa using hy)
    have hd := @LSeries_hasDerivAt (b k) s (ac.trans_lt (by exact_mod_cast hs))
    rw [logb] at hd
    have d := ((hd.const_mul (2:ℂ)).cexp).deriv
    have e : L =ᶠ[𝓝 s] E := by
      filter_upwards [(isOpen_lt (continuous_const (X:=ℂ)) Complex.continuous_re).mem_nhds hs] with z hz
      exact cont z hz
    rw [e.deriv_eq,cont s hs]
    dsimp only [E]
    rw [d]; field_simp [Complex.exp_ne_zero]

end OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1

section
/- Absolute convergence and locally uniform convergence for angular characters
on translates of the Eisenstein lattice. -/

open Complex Real Filter Finset Set
open scoped Topology
namespace OMA.AngularTail

noncomputable def z (u : ℤ × ℤ) : ℂ :=
  (u.1 : ℂ) + u.2 * ((1 + I * (Real.sqrt 3 : ℂ))/2)

noncomputable def g (m : ℕ) (s x : ℂ) : ℂ :=
  if x = 0 then 0 else (x/(‖x‖:ℂ))^m * (‖x‖:ℂ)^(-2*s)

theorem norm_g (m : ℕ) (s x : ℂ) (hx : x ≠ 0) :
    ‖g m s x‖ = ‖x‖^(-2*s.re) := by
  simp [g,hx,norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr hx),
    Complex.mul_re, norm_ne_zero_iff.mpr hx]

theorem differentiable_g (m : ℕ) (x : ℂ) : Differentiable ℂ (fun s => g m s x) := by
  by_cases h : x=0
  · simp [g,h]
  · simp only [g,if_neg h]
    apply Differentiable.const_mul
    exact (differentiable_id.const_mul (-2:ℂ)).const_cpow
      (Or.inl (by exact_mod_cast norm_ne_zero_iff.mpr h))

theorem lattice_norm (u : ℤ × ℤ) : ‖u‖ ≤ 2*‖z u‖ := by
  have re : (z u).re = (u.1:ℝ) + u.2 / 2 := by
    simp [z,Complex.add_re,Complex.mul_re,Complex.div_ofNat_re,Complex.div_ofNat_im]; ring
  have im : (z u).im = (u.2:ℝ)*Real.sqrt 3 / 2 := by
    simp [z,Complex.add_im,Complex.mul_im,Complex.div_ofNat_re,Complex.div_ofNat_im]; ring
  have hr := Complex.abs_re_le_norm (z u)
  have hi := Complex.abs_im_le_norm (z u)
  rw [re] at hr
  rw [im,abs_div,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)] at hi
  norm_num at hi
  have hs : 1 ≤ Real.sqrt 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg 3]
  have hb : |(u.2:ℝ)| ≤ 2*‖z u‖ := by nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg (u.2:ℝ))]
  change max ‖u.1‖ ‖u.2‖ ≤ _
  simp only [Int.norm_eq_abs, max_le_iff]
  refine ⟨?_,hb⟩
  rw [abs_le] at hr hb ⊢
  constructor <;> linarith [hr.1,hr.2,hb.1,hb.2]

theorem lattice_summable (w : ℂ) (hw : w ≠ 0) (b : ℝ) (hb : 2 < b) :
    Summable (fun u : ℤ × ℤ => ‖w*z u‖^(-b)) := by
  have base : Summable (fun u : ℤ×ℤ => ‖u‖^(-b)) := by
    let eqv := (finTwoArrowEquiv ℤ).symm
    have h := eqv.summable_iff.mpr (EisensteinSeries.summable_one_div_norm_rpow hb)
    apply h.congr
    intro u
    change ‖![u.1,u.2]‖^(-b) = ‖u‖^(-b)
    congr 1
    rw [EisensteinSeries.norm_eq_max_natAbs,Prod.norm_def]
    simp [Int.norm_eq_abs]
  apply (base.mul_left ((‖w‖/2)^(-b))).of_nonneg_of_le (fun u => Real.rpow_nonneg (norm_nonneg _) _)
  intro u
  by_cases hu : u=0
  · simp [hu,z,Real.zero_rpow (by linarith : -b≠0)]
  rw [←Real.mul_rpow (by positivity) (norm_nonneg u),norm_mul]
  apply Real.rpow_le_rpow_of_nonpos (mul_pos (by positivity) (norm_pos_iff.mpr hu)) _ (by linarith)
  have h := mul_le_mul_of_nonneg_left (lattice_norm u) (norm_nonneg w)
  linarith

theorem original_scaled (m : ℕ) (w s : ℂ) (hw : w≠0) (hs : 1 < s.re) :
    Summable (fun u : ℤ×ℤ => ‖g m s (w*z u)‖) := by
  have h := lattice_summable w hw (2*s.re) (by linarith)
  apply h.congr
  intro u
  by_cases hz : w*z u=0
  · simp [hz,g,Real.zero_rpow (by linarith : -(2*s.re)≠0)]
  · rw [norm_g _ _ _ hz]; ring_nf

theorem original (m : ℕ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun u : ℤ×ℤ => ‖g m s (z u)‖) := by
  simpa only [one_mul] using original_scaled m 1 s one_ne_zero hs

private theorem powers (u v : ℂ) (hu : ‖u‖=1) (hv : ‖v‖=1) (m : ℕ) :
    ‖u^m-v^m‖ ≤ m*‖u-v‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show u^(m+1)-v^(m+1) = (u^m-v^m)*u+v^m*(u-v) by ring]
    have h := norm_add_le ((u^m-v^m)*u) (v^m*(u-v))
    simp only [norm_mul,norm_pow,hu,hv,one_pow,mul_one,one_mul] at h
    push_cast
    linarith

private theorem dir_diff (x j : ℂ) (hx : x≠0) (hx' : x+j≠0) :
    ‖(x+j)/(‖x+j‖:ℂ)-x/(‖x‖:ℂ)‖*‖x‖ ≤ 2*‖j‖ := by
  let u := (x+j)/(‖x+j‖:ℂ)
  let v := x/(‖x‖:ℂ)
  have hu : ‖u‖=1 := by simp [u,norm_ne_zero_iff.mpr hx']
  have ua : u*(‖x+j‖:ℂ)=x+j := div_mul_cancel₀ _ (by exact_mod_cast norm_ne_zero_iff.mpr hx')
  have va : v*(‖x‖:ℂ)=x := div_mul_cancel₀ _ (by exact_mod_cast norm_ne_zero_iff.mpr hx)
  have eq : (u-v)*(‖x‖:ℂ)=j+u*((‖x‖:ℂ)-‖x+j‖) := by linear_combination ua - va
  have e := norm_add_le j (u*((‖x‖:ℂ)-‖x+j‖))
  rw [←eq,norm_mul,norm_mul,hu,one_mul,←Complex.ofReal_sub] at e
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] at e
  have d := abs_norm_sub_norm_le x (x+j)
  simp only [sub_add_cancel_left,norm_neg] at d
  change ‖u-v‖*‖x‖ ≤ _
  linarith

/-- Uniform translation estimate on an open half-plane, with an absolute
majorant of order |x|^(-5/2) away from the origin. -/
theorem tail (m : ℕ) (s x j : ℂ) (hs : 3/4 ≤ s.re)
    (hr : 2 ≤ ‖x‖) (hj : 2*‖j‖ ≤ ‖x‖) :
    ‖g m s (x+j)-g m s x‖ ≤ (2*‖s‖+m)*‖j‖*(‖x‖/2)^(-(5/2:ℝ)) := by
  let R := ‖x‖/2
  let h := -2*s
  have R1 : 1 ≤ R := by dsimp [R]; linarith
  have Rp : 0 < R := by linarith
  have re : h.re = -2*s.re := by simp [h,Complex.mul_re]
  have hn : h≠0 := by intro e; rw [e] at re; simp at re; linarith
  have rx : R≤‖x‖ := by dsimp [R]; linarith
  have rj : R≤‖x+j‖ := by
    have hh := norm_sub_le (x+j) j
    rw [add_sub_cancel_right] at hh
    dsimp [R]; linarith
  have xpos : x≠0 := norm_pos_iff.mp (Rp.trans_le rx)
  have xjpos : x+j≠0 := norm_pos_iff.mp (Rp.trans_le rj)
  have nh : ‖h‖=2*‖s‖ := by simp [h]
  have derivAt (t : ℝ) (ht : t∈Ici R) := hasDerivAt_ofReal_cpow_const (Rp.trans_le ht).ne' hn
  have bound (t : ℝ) (ht : t∈Ici R) :
      ‖deriv (fun a : ℝ => (a:ℂ)^h) t‖ ≤ 2*‖s‖ * R^(-(5/2:ℝ)) := by
    rw [(derivAt t ht).deriv, norm_mul,nh,Complex.norm_cpow_eq_rpow_re_of_pos (Rp.trans_le ht)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (Real.rpow_le_rpow_of_exponent_le (R1.trans ht) (by simp [re]; linarith : (h-1).re≤-(5/2:ℝ))).trans
      (Real.rpow_le_rpow_of_nonpos Rp ht (by norm_num))
  have radial := (convex_Ici R).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (derivAt t ht).differentiableAt) bound rx rj
  have distnorm := abs_norm_sub_norm_le (x+j) x
  simp only [add_sub_cancel_left] at distnorm
  rw [Real.norm_eq_abs] at radial
  have radial' := radial.trans (mul_le_mul_of_nonneg_left distnorm (by positivity))
  let u := (x+j)/(‖x+j‖:ℂ)
  let v := x/(‖x‖:ℂ)
  have hu : ‖u‖=1 := by simp [u,norm_ne_zero_iff.mpr xjpos]
  have hv : ‖v‖=1 := by simp [v,norm_ne_zero_iff.mpr xpos]
  have dw := dir_diff x j xpos xjpos
  change ‖u-v‖*‖x‖ ≤ _ at dw
  have rad0 : ‖(‖x‖:ℂ)^h‖ ≤ R^(-(5/2:ℝ))*R := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Rp.trans_le rx), ←Real.rpow_add_one Rp.ne',
      show -(5/2:ℝ)+1=-(3/2:ℝ) by norm_num]
    exact (Real.rpow_le_rpow_of_exponent_le (R1.trans rx) (by rw [re]; linarith)).trans
      (Real.rpow_le_rpow_of_nonpos Rp rx (by norm_num))
  have w := mul_le_mul_of_nonneg_right (powers u v hu hv m) (norm_nonneg ((‖x‖:ℂ)^h))
  have angle := w.trans (mul_le_mul_of_nonneg_left rad0 (by positivity))
  have ar : ‖u-v‖*R ≤ ‖j‖ := by dsimp [R]; linarith
  have ang : ‖u^m-v^m‖*‖(‖x‖:ℂ)^h‖ ≤ (m:ℝ)*‖j‖*R^(-(5/2:ℝ)) := by
    nlinarith only [angle,mul_le_mul_of_nonneg_right ar (by positivity : (0:ℝ) ≤ m*R^(-(5/2:ℝ)))]
  rw [g,if_neg xjpos,g,if_neg xpos]
  change ‖u^m*(‖x+j‖:ℂ)^h-v^m*(‖x‖:ℂ)^h‖ ≤ _
  rw [show u^m*(‖x+j‖:ℂ)^h-v^m*(‖x‖:ℂ)^h =
      u^m*((‖x+j‖:ℂ)^h-(‖x‖:ℂ)^h)+(u^m-v^m)*(‖x‖:ℂ)^h by ring]
  apply (norm_add_le ..).trans
  rw [norm_mul,norm_mul,norm_pow,hu,one_pow,one_mul]
  change _ ≤ (2*‖s‖+m)*‖j‖*R^(-(5/2:ℝ))
  nlinarith only [radial',ang]

/-- A single summable majorant works for all complex arguments in the ball
of radius 1/8 about a point on or to the right of Re(s)=1. -/
theorem majorant (m : ℕ) (w j s : ℂ) (hw : w≠0) (hs : 1 ≤ s.re) :
    ∃ M : ℤ×ℤ → ℝ, Summable M ∧ ∀ u t, t∈Metric.ball s (1/8) →
      ‖g m t (w*z u+j)-g m t (w*z u)‖ ≤ M u := by
  classical
  let cut := max 2 (2*‖j‖)
  let G (u : ℤ×ℤ) := cut ≤ ‖w*z u‖
  let F (u : ℤ×ℤ) (t : ℂ) := g m t (w*z u+j)-g m t (w*z u)
  let B := (2*(‖s‖+1)+m)*‖j‖
  let Q (u : ℤ×ℤ) := B*(‖w*z u‖/2)^(-(5/2:ℝ))
  have summ : Summable Q := by
    have hh := (lattice_summable w hw (5/2) (by norm_num)).mul_right ((2:ℝ)^(-(5/2:ℝ)))⁻¹
    apply (hh.mul_left B).congr
    intro u
    change B*(_*_) = B*((‖w*z u‖/2)^(-(5/2:ℝ)))
    rw [Real.div_rpow (norm_nonneg _) (by norm_num : (0:ℝ)≤2),div_eq_mul_inv (‖w*z u‖^_)]
  have ultimately : ∀ᶠ u : ℤ×ℤ in cofinite, G u := by
    have hn : Tendsto (fun u : ℤ×ℤ => ‖u‖) cofinite atTop :=
      tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Topology.IsClosedEmbedding.id
    filter_upwards [hn.eventually_ge_atTop (2*cut/‖w‖)] with u hu
    have h := (div_le_iff₀ (norm_pos_iff.mpr hw)).mp hu
    have h' := mul_le_mul_of_nonneg_right (lattice_norm u) (norm_nonneg w)
    change cut≤‖w*z u‖
    rw [norm_mul]; linarith
  have small (u : ℤ×ℤ) : ∃ c : ℝ, ∀ t ∈ Metric.closedBall s (1/8), ‖F u t‖≤c :=
    (isCompact_closedBall _ _).exists_bound_of_continuousOn
      (((differentiable_g m (w*z u+j)).sub (differentiable_g m (w*z u))).continuous.continuousOn)
  choose c hc using small
  refine ⟨fun u => if G u then Q u else c u,summ.congr_cofinite ?_,?_⟩
  · filter_upwards [ultimately] with u hu; simp [hu]
  intro u t ht
  change _ ≤ if G u then Q u else c u
  by_cases good : G u
  · rw [if_pos good]
    have dist := Metric.mem_ball.mp ht
    rw [dist_eq_norm] at dist
    have nr := norm_sub_le (t-s) (-s)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at nr
    have hre := Complex.abs_re_le_norm (t-s)
    rw [Complex.sub_re,abs_le] at hre
    have h := tail m t (w*z u) j (by linarith [hre.1]) ((le_max_left ..).trans good)
      ((le_max_right ..).trans good)
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg j)
    linarith
  · rw [if_neg good]
    exact hc u t (Metric.ball_subset_closedBall ht)

theorem translated_abs (m : ℕ) (w j s : ℂ) (hw : w≠0) (hs : 1 ≤ s.re) :
    Summable (fun u : ℤ×ℤ => ‖g m s (w*z u+j)-g m s (w*z u)‖) := by
  obtain ⟨M,hM,bound⟩ := majorant m w j s hw hs
  exact hM.of_nonneg_of_le (fun _ => norm_nonneg _) (fun u => bound u s (Metric.mem_ball_self (by norm_num)))

theorem translated (m : ℕ) (w j s : ℂ) (hw : w≠0) (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (fun t => ∑' u : ℤ×ℤ, (g m t (w*z u+j)-g m t (w*z u))) s := by
  obtain ⟨M,hM,bound⟩ := majorant m w j s hw hs
  exact (Complex.differentiableOn_tsum_of_summable_norm hM (fun u =>
    ((differentiable_g m (w*z u+j)).sub (differentiable_g m (w*z u))).differentiableOn)
    Metric.isOpen_ball bound).analyticAt (Metric.ball_mem_nhds _ (by norm_num))

theorem shifted (m : ℕ) (w j s : ℂ) (hw : w≠0) (hs : 1 < s.re) :
    Summable (fun u : ℤ×ℤ => ‖g m s (w*z u+j)‖) :=
  ((translated_abs m w j s hw hs.le).add (original_scaled m w s hw hs)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun u => by
      simpa only [sub_add_cancel] using norm_add_le
        (g m s (w*z u+j)-g m s (w*z u)) (g m s (w*z u)))

end OMA.AngularTail

/- Two different index-seven similarities of the triangular lattice generate
the same coset-cancellation identity but have different angular factors. -/
namespace OMA.AngularSeven
open Complex
abbrev Pair := ℤ × ℤ

def A (u : Pair) : Pair := (2*u.1-u.2,u.1+3*u.2)
def B (u : Pair) : Pair := (3*u.1+u.2,-u.1+2*u.2)
def shift (u : Pair) (j : ℤ) : Pair := (u.1+j,u.2)

def cosA : Fin 7 × Pair ≃ Pair where
  toFun q := shift (A q.2) q.1
  invFun u := let j := (u.1-2*u.2)%7
              let b := (2*u.2-(u.1-j))/7
              (⟨j.toNat,by dsimp [j]; omega⟩,u.2-3*b,b)
  left_inv := by
    rintro ⟨⟨j,hj⟩,a,b⟩
    apply Prod.ext
    · apply Fin.ext; dsimp [shift,A]; omega
    · apply Prod.ext <;> dsimp [shift,A] <;> omega
  right_inv := by
    rintro ⟨x,y⟩
    apply Prod.ext <;> dsimp [shift,A] <;> omega

def cosB : Fin 7 × Pair ≃ Pair where
  toFun q := shift (B q.2) q.1
  invFun u := let j := (u.1+3*u.2)%7
              let b := (u.1-j+3*u.2)/7
              (⟨j.toNat,by dsimp [j]; omega⟩,-u.2+2*b,b)
  left_inv := by
    rintro ⟨⟨j,hj⟩,a,b⟩
    apply Prod.ext
    · apply Fin.ext; dsimp [shift,B]; omega
    · apply Prod.ext <;> dsimp [shift,B] <;> omega
  right_inv := by
    rintro ⟨x,y⟩
    apply Prod.ext <;> dsimp [shift,B] <;> omega

noncomputable def eta : ℂ := (1+I*(Real.sqrt 3 : ℂ))/2
noncomputable def val (u : Pair) : ℂ := u.1 + u.2 * eta

lemma eta_sq : eta^2 = eta-1 := by
  have h : (Real.sqrt 3 : ℂ)^2=3 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  unfold eta
  linear_combination (Real.sqrt 3 : ℂ)^2/4*Complex.I_sq - h/4

lemma val_A (u : Pair) : val (A u) = (2+eta)*val u := by
  dsimp [A,val]; push_cast
  linear_combination -(u.2:ℂ)*eta_sq

lemma val_B (u : Pair) : val (B u) = (3-eta)*val u := by
  dsimp [B,val]; push_cast
  linear_combination (u.2:ℂ)*eta_sq

lemma val_shift (u : Pair) (j : ℤ) : val (shift u j)=val u+j := by
  simp [val,shift]; ring

lemma val_injective : Function.Injective val := by
  rintro ⟨a,b⟩ ⟨c,d⟩ eq
  have im := congrArg Complex.im eq
  have re := congrArg Complex.re eq
  simp [val,eta,Complex.mul_im,Complex.mul_re,Complex.div_ofNat_re,Complex.div_ofNat_im] at im re
  subst d
  have ac : (a:ℝ) = c := by linarith
  exact Prod.ext (by exact_mod_cast ac) rfl

def residue (u : Pair) : ZMod 7 := (u.1:ZMod 7)+5*(u.2:ZMod 7)

lemma residue_A (u : Pair) : residue (A u)=0 := by
  have h : (7:ZMod 7)=0 := by decide
  dsimp [residue,A]; push_cast; linear_combination ((u.1:ZMod 7)+2*u.2)*h

lemma residue_B (u : Pair) : residue (B u)=5*residue u := by
  have h : (7:ZMod 7)=0 := by decide
  dsimp [residue,B]; push_cast; linear_combination -((u.1:ZMod 7)+2*u.2)*h

lemma distinguish {m : ℕ} (hm : m ≠ 0) : (2+eta)^m ≠ (3-eta)^m := by
  let x : Pair := (1,0)
  have vx (f : Pair → Pair) (c : ℂ) (h : ∀ u, val (f u)=c*val u) (n : ℕ) :
      val ((f^[n]) x) = c^n := by
    induction n with
    | zero => simp [val,x]
    | succ n ih => rw [Function.iterate_succ_apply',h,ih,pow_succ']
  have rb (n : ℕ) : residue ((B^[n]) x)=5^n := by
    induction n with
    | zero => simp [residue,x]
    | succ n ih => rw [Function.iterate_succ_apply',residue_B,ih,pow_succ']
  intro eq
  have same := val_injective ((vx A _ val_A m).trans (eq.trans (vx B _ val_B m).symm))
  have bad := congrArg residue same
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  rw [rb,Function.iterate_succ_apply',residue_A] at bad
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact (pow_ne_zero _ (by decide : (5:ZMod 7)≠0)) bad.symm

end OMA.AngularSeven

namespace OMA.AngularSeven
open Complex
open scoped BigOperators ComplexConjugate

lemma coset_sum (E : Fin 7 × Pair ≃ Pair) (F : Pair → ℂ) (c : ℂ)
    (h : Summable F) (h0 : ∀ u, F (E (0,u)) = c * F u) :
    (∑' u, F u) = (∑ j : Fin 7, ∑' u, (F (E (j,u))-F (E (0,u)))) + 7*c*(∑' u, F u) := by
  have s : Summable (fun q => F (E q)) := E.summable_iff.mpr h
  have eqj (j : Fin 7) : ∑' u, (F (E (j,u))-F (E (0,u))) =
      (∑' u, F (E (j,u))) - c*(∑' u, F u) := by
    rw [(s.prod_factor j).tsum_sub (s.prod_factor 0),←tsum_mul_left]
    simp_rw [h0]
  have tot : (∑' u, F u) = ∑ j : Fin 7, ∑' u, F (E (j,u)) := by
    rw [←E.tsum_eq F,s.tsum_prod,tsum_fintype]
  simp_rw [eqj]
  rw [Finset.sum_sub_distrib,←tot]
  simp; ring

noncomputable def g (m : ℕ) (s z : ℂ) : ℂ :=
  if z=0 then 0 else (z/(‖z‖:ℂ))^m*(‖z‖:ℂ)^(-2*s)

lemma g_mul (m : ℕ) (s z w : ℂ) : g m s (z*w)=g m s z*g m s w := by
  by_cases hz : z=0
  · simp [hz,g]
  by_cases hw : w=0
  · simp [hw,g]
  simp only [g,if_neg (mul_ne_zero hz hw),if_neg hz,if_neg hw,norm_mul,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (norm_nonneg z) (norm_nonneg w)]
  rw [mul_div_mul_comm,mul_pow]
  ring

lemma conjugate_factors : star (2+eta) = (3-eta) := by
  rw [show star (2+eta) = conj (2+eta) by rfl]
  have t : conj (2:ℂ)=2 := by exact map_ofNat _ 2
  simp [eta,t]; ring

lemma radius_eq : ‖2+eta‖=‖3-eta‖ := by rw [←conjugate_factors]; exact (Complex.norm_conj _).symm

lemma nonzero_w : 2+eta≠0 := by
  intro h
  have := congrArg Complex.re h
  norm_num [eta,Complex.div_ofNat_re] at this

lemma g_distinguish {m : ℕ} (hm : m≠0) (s : ℂ) : g m s (2+eta) ≠ g m s (3-eta) := by
  have ha := nonzero_w
  have hb : 3-eta≠0 := by
    rw [←conjugate_factors]
    exact (map_ne_zero (starRingEnd ℂ)).mpr ha
  have hn : (‖3-eta‖:ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hb
  simp only [g,if_neg ha,if_neg hb,div_pow,radius_eq]
  intro he
  have eq := mul_right_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl hn)) he
  exact distinguish hm ((div_left_inj' (pow_ne_zero m hn)).mp eq)

lemma g_analytic (m : ℕ) (w s : ℂ) : AnalyticAt ℂ (fun t => g m t w) s := by
  by_cases hw : w=0
  · simp only [hw,g,if_true]; exact analyticAt_const
  have hn : (‖w‖:ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  simp only [g,if_neg hw,Complex.cpow_def_of_ne_zero hn]
  fun_prop

end OMA.AngularSeven

namespace OMA.AngularSeven
open Complex
open scoped BigOperators

noncomputable def S (m : ℕ) (s : ℂ) := ∑' u : Pair, g m s (val u)
noncomputable def T (m : ℕ) (w s : ℂ) :=
  ∑ j : Fin 7, ∑' u : Pair, (g m s (w*val u+j)-g m s (w*val u))
noncomputable def extension (m : ℕ) (s : ℂ) :=
  (T m (3-eta) s-T m (2+eta) s)/(7*(g m s (2+eta)-g m s (3-eta)))

lemma coset_A (m : ℕ) (s : ℂ) (h : Summable (fun u : Pair => g m s (val u))) :
    S m s = T m (2+eta) s + 7*g m s (2+eta)*S m s := by
  have e (j : Fin 7) (u : Pair) : val (cosA (j,u)) = (2+eta)*val u+j := by
    change val (shift (A u) j) = _
    rw [val_shift,val_A]; simp
  have e0 (u : Pair) : val (cosA (0,u)) = (2+eta)*val u := by rw [e]; simp
  have total := coset_sum cosA _ _ h (fun u => by rw [e0,g_mul])
  simpa only [S,T,e0,e] using total

lemma coset_B (m : ℕ) (s : ℂ) (h : Summable (fun u : Pair => g m s (val u))) :
    S m s = T m (3-eta) s + 7*g m s (3-eta)*S m s := by
  have e (j : Fin 7) (u : Pair) : val (cosB (j,u)) = (3-eta)*val u+j := by
    change val (shift (B u) j) = _
    rw [val_shift,val_B]; simp
  have e0 (u : Pair) : val (cosB (0,u)) = (3-eta)*val u := by rw [e]; simp
  have total := coset_sum cosB _ _ h (fun u => by rw [e0,g_mul])
  simpa only [S,T,e0,e] using total

lemma equals_original {m : ℕ} (hm : m≠0) (s : ℂ)
    (h : Summable (fun u : Pair => g m s (val u))) : extension m s = S m s := by
  apply (div_eq_iff (mul_ne_zero (by norm_num) (sub_ne_zero.mpr (g_distinguish hm s)))).mpr
  linear_combination coset_A m s h - coset_B m s h

lemma extension_analytic {m : ℕ} (hm : m≠0) (s : ℂ)
    (H : ∀ w : ℂ, w≠0 → ∀ j : Fin 7, AnalyticAt ℂ
      (fun t => ∑' u : Pair, (g m t (w*val u+j)-g m t (w*val u))) s) :
    AnalyticAt ℂ (extension m) s := by
  have hT (w : ℂ) (hw : w≠0) : AnalyticAt ℂ (T m w) s := by
    apply Finset.analyticAt_fun_sum
    exact fun i _ => H w hw i
  have b : 3-eta≠0 := by
    rw [←conjugate_factors]; exact (map_ne_zero (starRingEnd ℂ)).mpr nonzero_w
  have nn := sub_ne_zero.mpr (g_distinguish hm s)
  exact ((hT _ b).sub (hT _ nonzero_w)).div
    (analyticAt_const.mul ((g_analytic m _ s).sub (g_analytic m _ s))) (mul_ne_zero (by norm_num) nn)

end OMA.AngularSeven
theorem OMA.AngularDeep.analytic : OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1.H1 := by
  intro m hm
  refine ⟨OMA.AngularSeven.extension m,fun s hs => ?_,fun s hs => ?_⟩
  · apply OMA.AngularSeven.extension_analytic hm
    intro w hw j
    exact OMA.AngularTail.translated m w j s hw hs
  · exact OMA.AngularSeven.equals_original hm s (OMA.AngularTail.original m s hs).of_norm
end

section
/- The Euler logarithm for an Eisenstein angular character. Split primes occur
in conjugate pairs, inert primes have norm p², and the ramified prime is omitted. -/
namespace OMA.AngularEuler
open Real Filter ArithmeticFunction LSeries
open scoped Topology

noncomputable def phase (angle : ℕ → ℝ) (n : ℕ) : ℝ :=
  let p := n.minFac
  let j := n.factorization p
  if p%3 = 1 then cos (j*angle p) else if p%3 = 2 ∧ Even j then 1 else 0

noncomputable def a (angle : ℕ → ℝ) (n : ℕ) : ℂ := ((Λ n * phase angle n : ℝ):ℂ)
noncomputable def b (angle : ℕ → ℝ) (n : ℕ) : ℂ := a angle n / (Real.log n : ℝ)
noncomputable def euler (angle : ℕ → ℝ) (s : ℂ) : ℂ := Complex.exp (2*LSeries (b angle) s)


end OMA.AngularEuler
end

section
/- Euler logarithms for bounded completely multiplicative coefficients.
The prime-power logarithm expansion adapts Mathlib's
`DirichletCharacter.eulerProduct_log_eq_LSeries`,
Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean, copyright (c) 2023
Michael Stoll, released under the Apache License 2.0. Here the coefficients
need not be periodic, and the two factors differ on inert primes. -/

namespace OMA.AngularLog
open Complex Nat Filter ArithmeticFunction EulerProduct
open scoped Topology

noncomputable def lift (v : ℕ→ℂ) : ℕ →*₀ ℂ where
  toFun n := if n=0 then 0 else n.factorization.prod (fun p e => (v p)^e)
  map_zero' := by simp
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a=0
    · simp [ha]
    by_cases hb : b=0
    · simp [hb]
    simp [ha,hb,Nat.factorization_mul,Finsupp.prod_add_index',pow_add]

@[simp] theorem lift_prime (v : ℕ→ℂ) {p : ℕ} (hp : p.Prime) : lift v p = v p := by
  simp [lift,hp.ne_zero,hp.factorization]

theorem lift_norm (v : ℕ→ℂ) (hv : ∀ p, ‖v p‖≤1) (n : ℕ) : ‖lift v n‖≤1 := by
  by_cases h : n=0
  · simp [h]
  simp only [lift,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,if_neg h,Finsupp.prod,norm_prod,norm_pow]
  exact Finset.prod_le_one (fun _ _ => by positivity) (fun p _ => pow_le_one₀ (norm_nonneg _) (hv p))

noncomputable def left (angle : ℕ→ℝ) (p : ℕ) : ℂ :=
  if p%3=1 then exp ((angle p:ℂ)*I) else if p%3=2 then 1 else 0

noncomputable def right (angle : ℕ→ℝ) (p : ℕ) : ℂ :=
  if p%3=1 then exp (-((angle p:ℂ)*I)) else if p%3=2 then -1 else 0

theorem left_norm (angle : ℕ→ℝ) (p : ℕ) : ‖left angle p‖≤1 := by
  unfold left; split_ifs <;> simp [Complex.norm_exp]

theorem right_norm (angle : ℕ→ℝ) (p : ℕ) : ‖right angle p‖≤1 := by
  unfold right; split_ifs <;> simp [Complex.norm_exp]

noncomputable def coeff (χ : ℕ →*₀ ℂ) (n : ℕ) : ℂ := χ n*Λ n/Real.log n

theorem coeff_norm (χ : ℕ →*₀ ℂ) (hc : ∀ n, ‖χ n‖≤1) (n : ℕ) : ‖coeff χ n‖≤1 := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> simp [coeff]
  have hn' := Real.log_pos (by exact_mod_cast (show 1 < n by omega) : (1:ℝ)<n)
  simp only [coeff,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (vonMangoldt_nonneg (n:=n)),abs_of_pos hn',div_le_one hn']
  exact (mul_le_of_le_one_left vonMangoldt_nonneg (hc n)).trans vonMangoldt_le_log

theorem exp_series (χ : ℕ →*₀ ℂ) (hc : ∀ n, ‖χ n‖≤1) {s : ℂ} (hs : 1 < s.re) :
    exp (LSeries (coeff χ) s) = LSeries (χ : ℕ→ℂ) s := by
  let f := χ * riemannZetaSummandHom (ne_zero_of_one_lt_re hs)
  have val (n : ℕ) : f n = χ n*(n:ℂ)^(-s) := rfl
  have hf : Summable (fun n => ‖f n‖) := (summable_riemannZetaSummand hs).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => by
      rw [val,norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hc n))
  have eul := exp_tsum_primes_log_eq_tsum (f:=f) hf
  have logs : ∑' p : Primes, -log (1-f p) = LSeries (coeff χ) s := by
    have hlt (p : Primes) : ‖f p‖ < 1 := hf.of_norm.norm_lt_one (f:=f.toMonoidHom) p.prop.one_lt
    rw [tsum_congr (fun p => (hasSum_taylorSeries_neg_log' (hlt p)).tsum_eq.symm),
      LSeries_def₀ (by simp [coeff])]
    let A (n : ℕ) := coeff χ n * (n:ℂ)^(-s)
    have hA : Summable A := by
      apply (summable_riemannZetaSummand hs).of_norm_bounded
      intro n
      change ‖coeff χ n*(n:ℂ)^(-s)‖ ≤ ‖(n:ℂ)^(-s)‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (coeff_norm χ hc n)
    calc
      _ = ∑' (p : Primes) (k : ℕ), A (p^(k+1)) := by
        refine tsum_congr fun p => tsum_congr fun k => ?_
        have hlog : Complex.log p ≠ 0 := mod_cast p.prop.log_ne_zero
        simp [A,coeff,val,mul_pow,←cpow_nat_mul,←natCast_cpow_natCast_mul,
          vonMangoldt_apply_pow,vonMangoldt_apply_prime p.2,field]
        have he := congrArg Complex.ofReal (Real.log_pow (p:ℝ) (k+1))
        push_cast at he
        rw [Complex.ofReal_log (by positivity),Complex.ofReal_pow,Complex.ofReal_natCast] at he
        rw [he]
        field_simp [hlog]
      _ = ∑' n : {n : ℕ // IsPrimePow n}, A n :=
        tsum_primes_pow_eq (hA.subtype _)
      _ = _ := by
        simp only [div_eq_mul_inv _ (_ ^ _),←cpow_neg]
        apply tsum_subtype_eq_of_support_subset
        intro n hn
        contrapose! hn
        simp [A,coeff,vonMangoldt_eq_zero_iff.mpr hn]
  rw [←logs,eul,LSeries_def₀ (by simp)]
  exact tsum_congr fun n => by rw [val,cpow_neg,div_eq_mul_inv]

theorem trace_power (angle : ℕ→ℝ) (p : ℕ) (hp : p.Prime) (j : ℕ) (hj : j≠0) :
    (left angle p)^j+(right angle p)^j = 2*(AngularEuler.phase angle (p^j):ℂ) := by
  simp only [AngularEuler.phase,hp.pow_minFac hj,Nat.factorization_pow_self hp,left,right]
  by_cases s : p%3=1
  · simp only [if_pos s,←Complex.exp_nat_mul]
    have e : ((j:ℂ)*((angle p:ℂ)*I))=(((j:ℝ)*angle p:ℝ):ℂ)*I := by push_cast; ring
    have e' : ((j:ℂ)* -((angle p:ℂ)*I))=((-(j:ℝ)*angle p:ℝ):ℂ)*I := by push_cast; ring
    rw [e,e',Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I]
    simp [neg_mul,Real.cos_neg,Real.sin_neg]; ring
  · simp only [if_neg s]
    by_cases inert : p%3=2
    · by_cases ev : Even j <;> simp [inert,ev,neg_one_pow_eq_ite]; norm_num
    · simp [inert,zero_pow hj]

theorem coeffs (angle : ℕ→ℝ) :
    coeff (lift (left angle)) + coeff (lift (right angle)) = (2:ℂ) • AngularEuler.b angle := by
  funext n
  by_cases pp : IsPrimePow n
  · obtain ⟨p,j,prime,hj,rfl⟩ := (isPrimePow_def _).mp pp
    have hp := Nat.prime_iff.mpr prime
    have hh := trace_power angle p hp j hj.ne'
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,coeff,map_pow,lift_prime _ hp,
      AngularEuler.b,AngularEuler.a,Complex.ofReal_mul,←add_div,←add_mul,hh]
    ring
  · simp [coeff,AngularEuler.b,AngularEuler.a,vonMangoldt_eq_zero_iff.mpr pp]

theorem product (angle : ℕ→ℝ) (s : ℂ) (hs : 1 < s.re) :
    LSeries (lift (left angle) : ℕ→ℂ) s * LSeries (lift (right angle) : ℕ→ℂ) s =
      AngularEuler.euler angle s := by
  have su (χ : ℕ →*₀ ℂ) (hc : ∀n, ‖χ n‖≤1) :
      LSeriesSummable (coeff χ) s := LSeriesSummable_of_bounded_of_one_lt_re
        (m:=1) (fun n _ => coeff_norm χ hc n) hs
  have hl := lift_norm _ (left_norm angle)
  have hr := lift_norm _ (right_norm angle)
  rw [←exp_series _ hl hs,←exp_series _ hr hs,←exp_add,←LSeries_add (su _ hl) (su _ hr),
    coeffs,LSeries_smul,AngularEuler.euler]

noncomputable def arithmetic (v : ℕ→ℂ) : ArithmeticFunction ℂ := ⟨lift v, map_zero _⟩

theorem convolution (angle : ℕ→ℝ) (s : ℂ) (hs : 1 < s.re) :
    LSeries ((arithmetic (left angle)*arithmetic (right angle) : ArithmeticFunction ℂ) : ℕ→ℂ) s =
      AngularEuler.euler angle s := by
  apply (ArithmeticFunction.LSeries_mul' ?_ ?_).trans (product angle s hs)
  · exact LSeriesSummable_of_bounded_of_one_lt_re (m:=1) (fun n _ => lift_norm _ (left_norm angle) n) hs
  · exact LSeriesSummable_of_bounded_of_one_lt_re (m:=1) (fun n _ => lift_norm _ (right_norm angle) n) hs

end OMA.AngularLog
end

section
/- The lattice-coordinate model of the Eisenstein integers. Balanced integer
division rounds both coordinates of x/y; its norm error is at most 3/4. -/
namespace OMA.AngularRing
abbrev R := QuadraticAlgebra ℤ (-1) 1
open QuadraticAlgebra

lemma norm_formula (x : R) : x.norm=x.re^2+x.re*x.im+x.im^2 := by
  rw [norm_def]; ring

lemma norm_nonneg (x : R) : 0≤x.norm := by rw [norm_formula]; nlinarith [sq_nonneg (x.re+x.im),sq_nonneg x.re,sq_nonneg x.im]

lemma norm_pos {x : R} (hx : x≠0) : 0<x.norm := by
  by_contra! hn
  rw [norm_formula] at hn
  have h := sq_nonneg (x.re+x.im)
  apply hx
  ext <;> simp <;> nlinarith [sq_nonneg x.re,sq_nonneg x.im]

def N (x : R) : ℕ := x.norm.toNat
lemma cast_N (x : R) : (N x:ℤ)=x.norm := Int.toNat_of_nonneg (norm_nonneg x)
lemma N_pos {x : R} (hx : x≠0) : 0<N x := by have := norm_pos hx; unfold N; omega
lemma N_mul (x y : R) : N (x*y)=N x*N y := by
  exact Int.ofNat_inj.mp (by simp [cast_N])

def quot (x y : R) : R :=
  let v := x*star y
  ⟨v.re.bdiv (N y), v.im.bdiv (N y)⟩

lemma balanced (t : ℤ) {d : ℕ} (hd : 0<d) : -(d:ℤ) ≤ 2*t.bmod d ∧ 2*t.bmod d ≤ d := by
  have lo := @Int.le_bmod t d hd
  have hi := @Int.bmod_lt t d hd
  omega

lemma norm_rem (x y : R) (hy : y≠0) : N (x-y*quot x y)<N y := by
  let d := N y
  let v := x*star y
  let a := v.re.bmod d
  let b := v.im.bmod d
  have hd : 0<d := N_pos hy
  obtain ⟨al,ah⟩ := balanced v.re hd
  obtain ⟨bl,bh⟩ := balanced v.im hd
  change -(d:ℤ) ≤ 2*a at al
  change 2*a ≤ (d:ℤ) at ah
  change -(d:ℤ) ≤ 2*b at bl
  change 2*b ≤ (d:ℤ) at bh
  have sm : a^2+a*b+b^2 < (d:ℤ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ah) (by linarith : 0≤(d:ℤ)+2*a),
      mul_nonneg (sub_nonneg.mpr bh) (by linarith : 0≤(d:ℤ)+2*b),
      sq_nonneg (a-b),sq_pos_of_pos (by exact_mod_cast hd : (0:ℤ)<d)]
  have he : (x-y*quot x y)*star y = (⟨a,b⟩ : R) := by
    rw [sub_mul,show y*quot x y*star y=(y*star y)*quot x y by ring,
      ←QuadraticAlgebra.algebraMap_norm_eq_mul_star,←cast_N]
    change v-algebraMap ℤ R (d:ℤ)*quot x y=_
    ext
    · simp [quot,v,d,a,Int.bmod_eq_self_sub_mul_bdiv]
    · simp [quot,v,d,b,Int.bmod_eq_self_sub_mul_bdiv]
  have hnr := congrArg QuadraticAlgebra.norm he
  rw [map_mul,QuadraticAlgebra.norm_star,norm_formula (⟨a,b⟩:R)] at hnr
  change (x-y*quot x y).norm*y.norm = a^2+a*b+b^2 at hnr
  have dn : (d:ℤ)=y.norm := cast_N y
  rw [dn,←hnr] at sm
  rw [pow_two] at sm
  have := lt_of_mul_lt_mul_right sm (norm_nonneg y)
  exact_mod_cast (show (N (x-y*quot x y):ℤ)<N y by simpa [cast_N] using this)

instance euclidean : EuclideanDomain R where
  quotient := quot
  remainder x y := x-y*quot x y
  quotient_zero x := by ext <;> simp [quot,N]
  quotient_mul_add_remainder_eq x y := by ring
  r x y := N x<N y
  r_wellFounded := (measure N).wf
  remainder_lt := fun x _ hy => norm_rem x _ hy
  mul_left_not_lt := fun x y hy => not_lt_of_ge (by
    change N x ≤ N (x*y); rw [N_mul]
    exact Nat.le_mul_of_pos_right _ (N_pos hy))

lemma unit_iff (x : R) : IsUnit x ↔ N x=1 := by
  constructor
  · rintro ⟨u,rfl⟩
    have h := N_mul (u:R) (↑(u⁻¹):R)
    simp [N] at h
    exact (mul_eq_one.mp h.symm).1
  · intro h
    apply isUnit_iff_dvd_one.mpr
    refine ⟨star x,?_⟩
    rw [←QuadraticAlgebra.algebraMap_norm_eq_mul_star,←cast_N,h]
    simp

@[simp] theorem N_one : N 1=1 := rfl
@[simp] theorem N_zero : N 0=0 := rfl
@[simp] theorem N_star (x : R) : N (star x)=N x := by simp [N]

lemma N_nat (n : ℕ) : N (n : R)=n^2 := by
  apply Int.ofNat_inj.mp
  rw [cast_N,norm_formula]
  simp

lemma mul_conj (x : R) : x*star x=(N x:R) := by
  rw [←QuadraticAlgebra.algebraMap_norm_eq_mul_star,←cast_N]
  simp

lemma norm_prime {x : R} (hp : (N x).Prime) : Prime x := by
  apply irreducible_iff_prime.mp
  refine ⟨fun hu => hp.ne_one ((unit_iff x).mp hu),fun a b h => ?_⟩
  rw [unit_iff,unit_iff]
  rw [h,N_mul] at hp
  exact ((Nat.prime_mul_iff.mp hp).imp And.right And.right).symm

lemma N_mod_three (x : R) : N x % 3 ≠ 2 := by
  intro h
  have hh : ((N x : ℕ) : ZMod 3)=2 := by rw [←ZMod.natCast_mod,h]; decide
  have he := congrArg (fun z : ℤ => (z : ZMod 3)) (cast_N x)
  rw [norm_formula] at he
  push_cast at he
  rw [hh] at he
  exact (show ∀ a b : ZMod 3, a^2+a*b+b^2 ≠ 2 by decide) _ _ he.symm

lemma inert_prime (p : ℕ) (hp : p.Prime) (hi : p%3=2) : Prime (p:R) := by
  apply irreducible_iff_prime.mp
  refine ⟨?_,fun a b he => ?_⟩
  · rw [unit_iff,N_nat]
    exact ne_of_gt (one_lt_pow₀ hp.one_lt (by decide))
  · by_contra! hn
    have h := congrArg N he
    rw [N_nat,N_mul] at h
    have ab := (hp.mul_eq_prime_sq_iff (mt (unit_iff a).mpr hn.1)
      (mt (unit_iff b).mpr hn.2)).mp h.symm
    exact N_mod_three a (ab.1 ▸ hi)

abbrev ram : R := ⟨1,1⟩
lemma ram_norm : N ram=3 := by decide
lemma ram_prime : Prime ram := norm_prime (ram_norm ▸ (by decide : Nat.Prime 3))

/-- There are precisely six units, represented by the sixth roots of unity. -/
def units : Finset R := {⟨1,0⟩,⟨0,1⟩,⟨-1,1⟩,⟨-1,0⟩,⟨0,-1⟩,⟨1,-1⟩}
lemma card_units : units.card=6 := by decide

lemma mem_units (x : R) : x∈units ↔ IsUnit x := by
  rw [unit_iff]
  constructor
  · intro h
    simp only [units,Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · intro h
    obtain ⟨a,b⟩ := x
    have hn := cast_N (⟨a,b⟩ : R)
    rw [h,norm_formula] at hn
    change (1:ℤ)=a^2+a*b+b^2 at hn
    have ha : a^2≤1 := by nlinarith [sq_nonneg (a+2*b)]
    have hb : b^2≤1 := by nlinarith [sq_nonneg (2*a+b)]
    have ha' : -1≤a ∧ a≤1 := by constructor <;> nlinarith
    have hb' : -1≤b ∧ b≤1 := by constructor <;> nlinarith
    obtain ⟨ha₁,ha₂⟩ := ha'
    obtain ⟨hb₁,hb₂⟩ := hb'
    interval_cases a <;> interval_cases b <;> first | decide | norm_num at hn

lemma dvd_star_iff (x y : R) : x ∣ star y ↔ star x ∣ y := by
  constructor
  · rintro ⟨k,h⟩; exact ⟨star k,by simpa [mul_comm] using congrArg star h⟩
  · rintro ⟨k,h⟩; exact ⟨star k,by simpa [mul_comm] using congrArg star h⟩

lemma lift_norm_dvd {q : R} {p : ℕ} (hp : N q=p) {x : R} (h : p∣N x) :
    q∣x*star x := by
  rw [mul_conj]
  apply dvd_trans (b:=(p:R))
  · rw [←hp,←mul_conj]; exact dvd_mul_right _ _
  · obtain ⟨k,hk⟩ := h; exact ⟨(k:R),by simp [hk]⟩

lemma split_divides {q : R} {p : ℕ} (hp : p.Prime) (hq : N q=p) {x : R} (h : p∣N x) :
    q ∣ x ∨ star q ∣ x := by
  exact ((norm_prime (hq ▸ hp)).dvd_mul.mp (lift_norm_dvd hq h)).imp id (dvd_star_iff q x).mp

lemma inert_divides {p : ℕ} (hp : p.Prime) (hi : p%3=2) {x : R} (h : p ∣ N x) :
    (p : R) ∣ x := by
  have d : (p : R) ∣ x*star x := by
    rw [mul_conj]; obtain ⟨k,hk⟩ := h; exact ⟨(k:R),by simp [hk]⟩
  rcases (inert_prime p hp hi).dvd_mul.mp d with h|h
  · exact h
  · simpa using (dvd_star_iff _ _).mp h

lemma ram_divides {x : R} (h : 3 ∣ N x) : ram ∣ x := by
  obtain h|h := split_divides (by decide) ram_norm h
  · exact h
  · exact dvd_trans (b:=star ram) ⟨(⟨1,-1⟩:R),by decide⟩ h

lemma split_distinct {q : R} {p : ℕ} (hp : p.Prime) (hs : p%3=1) (hq : N q=p) :
    ¬ q ∣ star q := by
  intro hh
  have nq : q.norm=(p:ℤ) := by rw [←cast_N,hq]
  obtain ⟨u,hu⟩ := dvd_sub hh (dvd_refl q)
  have diff := congrArg QuadraticAlgebra.norm hu
  rw [map_mul,nq,norm_formula] at diff
  simp only [QuadraticAlgebra.re_sub,QuadraticAlgebra.im_sub,
    QuadraticAlgebra.re_star,QuadraticAlgebra.im_star] at diff
  let : Fact p.Prime := ⟨hp⟩
  have mod_d := congrArg (fun z : ℤ => (z:ZMod p)) diff
  have mod_q := congrArg (fun z : ℤ => (z:ZMod p)) nq
  rw [norm_formula] at mod_q
  push_cast at mod_q mod_d
  simp only [ZMod.natCast_self,zero_mul] at mod_q mod_d
  have h3 : (3:ZMod p) ≠ 0 := by
    change (↑(3:ℕ):ZMod p)≠0
    rw [Ne,ZMod.natCast_eq_zero_iff]
    intro hd
    have := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd
    exact this.elim hp.ne_one (fun h => by omega)
  have hbi : (3:ZMod p)*(q.im:ZMod p)^2=0 := by linear_combination mod_d
  have hb : (q.im:ZMod p)=0 := by simpa using (mul_eq_zero.mp hbi).resolve_left h3
  have ha : (q.re:ZMod p)=0 := by simpa [hb] using mod_q
  obtain ⟨a,ha'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha
  obtain ⟨b,hb'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb
  have div : (p:R) ∣ q := ⟨⟨a,b⟩,by ext <;> simp [ha',hb']⟩
  obtain ⟨v,hv⟩ := div
  have d := congrArg N hv
  rw [hq,N_mul,N_nat,pow_two,mul_assoc] at d
  have u : 1=p*N v := Nat.eq_of_mul_eq_mul_left hp.pos (by simpa using d)
  exact hp.not_dvd_one ⟨_,u⟩

end OMA.AngularRing
end

section
/- Identification of the split factors with the problem's two finite searches.
Reducing the Eisenstein norm modulo a split prime makes the rational prime
reducible; its two nonunit factors must both have norm p. The six units then
give uniqueness of the representative in the ordered sector. -/
namespace OMA.AngularSplit
open AngularRing QuadraticAlgebra OeisA218585

lemma split_norm {p : ℕ} (hp : p.Prime) (hs : p%3=1) : ∃ q : R, N q=p := by
  let : Fact p.Prime := ⟨hp⟩
  have d : 3∣Fintype.card (ZMod p)ˣ := by
    simp [ZMod.card_units_eq_totient,Nat.totient_prime hp]; omega
  obtain ⟨v,hv⟩ := exists_prime_orderOf_dvd_card (G:=(ZMod p)ˣ) 3 d
  let a := (v : ZMod p).val
  have av : (a : ZMod p)=v := ZMod.natCast_zmod_val _
  have cube : (v:ZMod p)^3=1 := by
    exact congrArg Units.val (show v^3=1 by rw [←hv,pow_orderOf_eq_one])
  have nv : (v:ZMod p)≠1 := by
    intro he
    have he' : v=1 := Units.ext he
    simp [he'] at hv
  have F : (a:ZMod p)^2+a+1=0 := by
    rw [av]
    apply (mul_eq_zero.mp (show ((v:ZMod p)-1)*(v^2+v+1)=0 by linear_combination cube)).resolve_left
      (sub_ne_zero.mpr nv)
  let u : R := ⟨(a:ℤ),1⟩
  have div : (p:ℤ)∣u.norm := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa [norm_formula,u] using F
  have np : ¬Prime (p:R) := by
    intro prime
    have h : (p:R)∣u*star u := by
      rw [←QuadraticAlgebra.algebraMap_norm_eq_mul_star]
      obtain ⟨m,h⟩ := div
      exact ⟨(m:R),by simp [h]⟩
    have no (x : R) (hx : x.im=1 ∨ x.im= -1) : ¬(p:R)∣x := by
      rintro ⟨y,hy⟩
      have im := congrArg QuadraticAlgebra.im hy
      simp at im
      have hd : (p:ℤ)∣x.im := ⟨_,im⟩
      have no1 : ¬(p:ℤ)∣1 := by exact_mod_cast hp.not_dvd_one
      rcases hx with he|he <;> rw [he] at hd
      · exact no1 hd
      · exact no1 (Int.dvd_neg.mp hd)
    exact (prime.dvd_mul.mp h).elim (no _ (Or.inl rfl)) (no _ (Or.inr rfl))
  have notu : ¬IsUnit (p:R) := by
    rw [unit_iff,N_nat]; exact ne_of_gt (one_lt_pow₀ hp.one_lt (by decide))
  by_contra! nex
  apply np
  apply irreducible_iff_prime.mp
  refine ⟨notu,fun x y he => ?_⟩
  by_contra! nu
  have h := congrArg N he
  rw [N_nat,N_mul] at h
  exact nex _ ((hp.mul_eq_prime_sq_iff (mt (unit_iff _).mpr nu.1)
    (mt (unit_iff _).mpr nu.2)).mp h.symm).1

private lemma chamber (a b : ℤ) :
    ∃ u v : ℤ, 0 ≤ v ∧ v ≤ u ∧ u^2+u*v+v^2=a^2+a*b+b^2 := by
  have choice : (0≤b ∧ b≤a) ∨ (0≤a ∧ a≤b) ∨
      (0≤ -b ∧ -b≤ -a) ∨ (0≤ -a ∧ -a≤ -b) ∨
      (0≤ -a-b ∧ -a-b≤a) ∨ (0≤a ∧ a≤ -a-b) ∨
      (0≤ -a-b ∧ -a-b≤b) ∨ (0≤b ∧ b≤ -a-b) ∨
      (0≤a+b ∧ a+b≤ -a) ∨ (0≤ -a ∧ -a≤a+b) ∨
      (0≤a+b ∧ a+b≤ -b) ∨ (0≤ -b ∧ -b≤a+b) := by omega
  rcases choice with h|h|h|h|h|h|h|h|h|h|h|h
  all_goals exact ⟨_,_,h.1,h.2,by ring⟩

lemma sector {p : ℕ} (hp : p.Prime) (hs : p%3=1) :
    ∃ a b : ℕ, 0<b ∧ b<a ∧ a<p ∧ a^2+a*b+b^2=p := by
  obtain ⟨q,hq⟩ := split_norm hp hs
  obtain ⟨u,v,hv,hu,h⟩ := chamber q.re q.im
  rw [←norm_formula,←cast_N,hq] at h
  have hu0 := hv.trans hu
  lift v to ℕ using hv
  lift u to ℕ using hu0
  have eq : u^2+u*v+v^2=p := by exact_mod_cast h
  have hl : v≤u := by exact_mod_cast hu
  have pos : 0<v := by
    by_contra! hz
    have h₀ : v=0 := by omega
    exact hp.prime.not_isSquare ⟨u,by simpa [h₀,pow_two] using eq.symm⟩
  have lt : v<u := by
    by_contra! hh
    have e : v=u := le_antisymm hl hh
    have h3 : 3∣p := ⟨u^2,by rw [←eq,e]; ring⟩
    omega
  refine ⟨u,v,pos,lt,?_,eq⟩
  nlinarith [Nat.le_self_pow (by decide : 2≠0) u,pow_pos pos 2]

lemma unique_sector {p : ℕ} (hp : p.Prime) (x y : R) (hx : N x=p) (hy : N y=p)
    (xp : 0<x.im) (xo : x.im<x.re) (yp : 0<y.im) (yo : y.im<y.re) : x=y := by
  obtain ⟨a,b⟩ := x
  obtain ⟨c,d⟩ := y
  change 0<b at xp; change b<a at xo; change 0<d at yp; change d<c at yo
  have cases (z : R) (hz : N z=p) (div : z ∣ (⟨c,d⟩:R)) :
      ∃ v∈units, (⟨c,d⟩:R)=z*v := by
    obtain ⟨v,e⟩ := div
    have h := congrArg N e
    rw [hy,N_mul,hz] at h
    exact ⟨v,(mem_units _).mpr ((unit_iff _).mpr
      (Nat.eq_of_mul_eq_mul_left hp.pos (by simpa using h.symm))),e⟩
  rcases split_divides hp hx (x:=(⟨c,d⟩:R)) (by rw [hy]) with div|div
  · obtain ⟨v,hv,e⟩ := cases _ hx div
    simp only [units,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals have A := congrArg QuadraticAlgebra.re e; have B := congrArg QuadraticAlgebra.im e
    all_goals simp at A B; ext <;> simp <;> omega
  · obtain ⟨v,hv,e⟩ := cases _ ((N_star _).trans hx) div
    simp only [units,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals have A := congrArg QuadraticAlgebra.re e; have B := congrArg QuadraticAlgebra.im e
    all_goals simp at A B; ext <;> simp <;> omega

def pair (a b : ℕ) : R := ⟨(a:ℤ),(b:ℤ)⟩

@[simp] lemma N_pair (a b : ℕ) : N (pair a b)=a^2+a*b+b^2 := by
  apply Int.ofNat_inj.mp
  rw [cast_N,norm_formula]; simp [pair]

lemma nat_unique {p a b u v : ℕ} (hp : p.Prime) (hb : 0<b) (ha : b<a)
    (hv : 0<v) (hu : v<u) (e : a^2+a*b+b^2=p) (d : u^2+u*v+v^2=p) :
    a=u ∧ b=v := by
  have h := unique_sector hp (pair a b) (pair u v) (by simpa using e) (by simpa using d)
    (by simpa [pair]) (by simpa [pair]) (by simpa [pair]) (by simpa [pair])
  exact ⟨Int.ofNat_inj.mp (congrArg QuadraticAlgebra.re h),
    Int.ofNat_inj.mp (congrArg QuadraticAlgebra.im h)⟩

private lemma find_unique (n c : ℕ) (hc : c<n) (f : ℕ→Bool) (fc : f c)
    (only : ∀ t, f t → t=c) : ((List.range n).find? f).getD 0=c := by
  have some := List.find?_isSome.mpr ⟨c,List.mem_range.mpr hc,fc⟩
  obtain ⟨t,et⟩ := Option.isSome_iff_exists.mp some
  rw [et]; exact only t (List.find?_some et)

theorem specified {p : ℕ} (hp : p.Prime) (hs : p%3=1) :
    N (pair (xp p) (yp p))=p := by
  obtain ⟨u,v,hv,hu,up,e⟩ := sector hp hs
  have X : xp p=u := by
    apply find_unique p u up
    · simp; exact ⟨v,hu,hv,e⟩
    · intro t ht; simp at ht
      obtain ⟨b,bt,bp,hb⟩ := ht
      exact (nat_unique hp bp bt hv hu hb e).1
  have Y : yp p=v := by
    apply find_unique p v (hu.trans up)
    · simp; exact ⟨hv,u,⟨hu,up⟩,e⟩
    · intro t ht; simp at ht
      obtain ⟨tp,a,⟨ta,_⟩,h⟩ := ht
      exact (nat_unique hp tp ta hv hu h e).2
  simpa [X,Y] using e

end OMA.AngularSplit
end

section
/- Finite shells of the Eisenstein lattice and the local counting rules.
All sums carry a multiplicative weight; conjugate split primes overlap precisely
on the shell of multiples of their product. -/
namespace OMA.AngularShell
open AngularRing

def coords : ℤ × ℤ ≃ R where
  toFun x := ⟨x.1,x.2⟩
  invFun z := (z.re,z.im)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def shell (n : ℕ) : Finset R :=
  (((Finset.Icc (-(n:ℤ)) n) ×ˢ (Finset.Icc (-(n:ℤ)) n)).map coords.toEmbedding).filter
    (fun x => N x=n)

@[simp] lemma mem_shell (x : R) (n : ℕ) : x∈shell n ↔ N x=n := by
  refine ⟨fun h => (Finset.mem_filter.mp h).2,fun h => ?_⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨(x.re,x.im),?_,rfl⟩,h⟩
  have e := cast_N x
  rw [h,norm_formula] at e
  have bound (a b : ℤ) (he : (n:ℤ)=a^2+a*b+b^2) : -(n:ℤ)≤a ∧ a≤n := by
    have w := sq_nonneg (2*b+a)
    by_cases hn : n=0
    · subst n
      constructor <;> nlinarith [sq_nonneg a]
    have pos : (1:ℤ) ≤ n := by omega
    constructor <;> by_contra! h
    · nlinarith [mul_nonneg (by omega : 0≤ -a-2) (by omega : 0≤ -a)]
    · nlinarith [mul_nonneg (by omega : 0≤a-2) (by omega : 0≤a)]
  have ha := bound x.re x.im e
  have hb := bound x.im x.re (by linarith)
  simpa using And.intro ha hb

def mult (u : R) (h : u≠0) : R ↪ R := ⟨(u*·),mul_right_injective₀ h⟩

lemma mem_mult (u : R) (h : u≠0) (n : ℕ) (x : R) :
    x ∈ (shell n).map (mult u h) ↔ u∣x ∧ N x=N u*n := by
  constructor
  · rintro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
    exact ⟨⟨y,rfl⟩,by simpa [mult,N_mul] using congrArg (N u*·) ((mem_shell y n).mp hy)⟩
  · rintro ⟨⟨y,rfl⟩,hN⟩
    rw [N_mul] at hN
    exact Finset.mem_map.mpr ⟨y,(mem_shell _ _).mpr (Nat.eq_of_mul_eq_mul_left (N_pos h) hN),rfl⟩

noncomputable def S (w : R →*₀ ℂ) (n : ℕ) : ℂ := ∑ x ∈ shell n,w x

lemma map_sum (w : R →*₀ ℂ) (u : R) (h : u≠0) (n : ℕ) :
    ∑ x ∈ (shell n).map (mult u h), w x = w u*S w n := by
  simp [S,Finset.sum_map,mult,Finset.mul_sum]

lemma split_union {p : ℕ} (hp : p.Prime) {q : R} (hq : N q=p) (n : ℕ) :
    shell (p*n) = (shell n).map (mult q (norm_prime (hq ▸ hp)).ne_zero) ∪
      (shell n).map (mult (star q) (norm_prime ((N_star q).trans hq ▸ hp)).ne_zero) := by
  ext x
  simp only [Finset.mem_union,mem_mult,mem_shell,N_star,hq]
  constructor
  · intro hx
    exact ((split_divides hp hq (hx ▸ dvd_mul_right p n)).imp (⟨·,hx⟩) (⟨·,hx⟩))
  · exact fun h => h.elim And.right And.right

lemma split_empty {p : ℕ} (hp : p.Prime) (hs : p%3=1) {q : R} (hq : N q=p)
    (n : ℕ) (hn : ¬p∣n) :
    Disjoint ((shell n).map (mult q (norm_prime (hq ▸ hp)).ne_zero))
      ((shell n).map (mult (star q) (norm_prime ((N_star q).trans hq ▸ hp)).ne_zero)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hy
  have hq' := (mem_mult _ _ _ _).mp hx
  have hd := ((norm_prime (hq ▸ hp)).dvd_mul.mp hq'.1).resolve_left (split_distinct hp hs hq)
  obtain ⟨z,rfl⟩ := hd
  have hn' := (mem_shell _ _).mp hv
  exact hn ⟨_,by rw [←hn',N_mul,hq]⟩

lemma split_inter {p : ℕ} (hp : p.Prime) (hs : p%3=1) {q : R} (hq : N q=p)
    (n : ℕ) :
    (shell (p*n)).map (mult q (norm_prime (hq ▸ hp)).ne_zero) ∩
      (shell (p*n)).map (mult (star q) (norm_prime ((N_star q).trans hq ▸ hp)).ne_zero) =
    (shell n).map (mult (q*star q) (mul_ne_zero (norm_prime (hq ▸ hp)).ne_zero
      (norm_prime ((N_star q).trans hq ▸ hp)).ne_zero)) := by
  ext x
  simp only [Finset.mem_inter,mem_mult,N_mul,N_star,hq,mul_assoc]
  constructor
  · rintro ⟨⟨hd,hN⟩,⟨⟨y,hy⟩,_⟩⟩
    rw [hy] at hd
    obtain ⟨v,rfl⟩ := ((norm_prime (hq ▸ hp)).dvd_mul.mp hd).resolve_left (split_distinct hp hs hq)
    exact ⟨⟨v,hy.trans (by ring)⟩,hN⟩
  · rintro ⟨h,hN⟩
    exact ⟨⟨dvd_trans (dvd_mul_right _ _) h,hN⟩,⟨dvd_trans (dvd_mul_left _ _) h,hN⟩⟩

lemma split_first (w : R →*₀ ℂ) {p : ℕ} (hp : p.Prime) (hs : p%3=1) {q : R}
    (hq : N q=p) (n : ℕ) (hn : ¬p∣n) :
    S w (p*n)=(w q+w (star q))*S w n := by
  unfold S
  rw [split_union hp hq,Finset.sum_union (split_empty hp hs hq n hn),map_sum,map_sum]
  exact (add_mul ..).symm

lemma split_next (w : R →*₀ ℂ) {p : ℕ} (hp : p.Prime) (hs : p%3=1) {q : R}
    (hq : N q=p) (n : ℕ) :
    S w (p*(p*n))+w q*w (star q)*S w n=(w q+w (star q))*S w (p*n) := by
  let l := (shell (p*n)).map (mult q (norm_prime (hq ▸ hp)).ne_zero)
  let r := (shell (p*n)).map (mult (star q) (norm_prime ((N_star q).trans hq ▸ hp)).ne_zero)
  have h := Finset.sum_union_inter (s₁:=l) (s₂:=r) (f:=fun x => w x)
  unfold l r at h
  rw [←split_union,split_inter hp hs hq,map_sum,map_sum,map_sum,map_mul] at h
  · exact h.trans (add_mul ..).symm
  all_goals assumption

lemma all_mult (u : R) (hu : u≠0) (n : ℕ) (D : ∀ x : R, N x=N u*n → u∣x) :
    shell (N u*n) = (shell n).map (mult u hu) := by
  ext x
  simp only [mem_shell,mem_mult]
  exact ⟨fun e => ⟨D _ e,e⟩,And.right⟩

lemma inert_first (w : R →*₀ ℂ) {p : ℕ} (hp : p.Prime) (hi : p%3=2) (n : ℕ)
    (hn : ¬p∣n) : S w (p*n)=0 := by
  apply Finset.sum_eq_zero
  intro x hx
  have h := (mem_shell _ _).mp hx
  obtain ⟨y,hy⟩ := inert_divides hp hi (h ▸ dvd_mul_right p n)
  rw [hy,N_mul,N_nat,pow_two,mul_assoc] at h
  exact False.elim (hn ⟨_,(Nat.eq_of_mul_eq_mul_left hp.pos h).symm⟩)

lemma inert_next (w : R →*₀ ℂ) {p : ℕ} (hp : p.Prime) (hi : p%3=2) (n : ℕ) :
    S w (p*(p*n))=w (p:R)*S w n := by
  have h := all_mult (p:R) (inert_prime p hp hi).ne_zero n fun x h =>
    inert_divides hp hi (by rw [h,N_nat,pow_two,mul_assoc]; exact dvd_mul_right _ _)
  rw [N_nat,pow_two,mul_assoc] at h
  unfold S; rw [h,map_sum]; rfl

lemma ram_step (w : R →*₀ ℂ) (n : ℕ) : S w (3*n)=w ram*S w n := by
  have h := all_mult ram ram_prime.ne_zero n fun x h =>
    ram_divides (by rw [h,ram_norm]; exact dvd_mul_right _ _)
  rw [ram_norm] at h
  unfold S; rw [h,map_sum]; rfl

def geom (x y : ℂ) (k : ℕ) : ℂ := ∑ j ∈ Finset.range (k+1), x^(k-j)*y^j

lemma geom_zero (x y : ℂ) : geom x y 0=1 := by simp [geom]

lemma geom_succ (x y : ℂ) (k : ℕ) : geom x y (k+1)=x*geom x y k+y^(k+1) := by
  unfold geom
  rw [Finset.sum_range_succ,Finset.mul_sum]
  simp only [Nat.sub_self,pow_zero,one_mul]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [show k+1-j=k-j+1 by have := Finset.mem_range.mp hj; omega,pow_succ]
  ring

lemma geom_rec (x y : ℂ) (k : ℕ) :
    geom x y (k+2)+x*y*geom x y k=(x+y)*geom x y (k+1) := by
  rw [geom_succ x y (k+1),geom_succ x y k,pow_succ y (k+1)]
  ring

lemma arith_mult (v : ℕ→ℂ) : (AngularLog.arithmetic v).IsMultiplicative :=
  ⟨map_one (AngularLog.lift v),fun {_ _} _ => map_mul (AngularLog.lift v) ..⟩

lemma arith_power (a b : ℕ→ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (AngularLog.arithmetic a * AngularLog.arithmetic b) (p^k) = geom (a p) (b p) k := by
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal' (fun u v =>
    AngularLog.arithmetic a u*AngularLog.arithmetic b v),Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun j hj => ?_
  have le : j ≤ k := by simpa using Finset.mem_range.mp hj
  have div : p^k/p^j=p^(k-j) := by
    conv_lhs => rw [←Nat.sub_add_cancel le,pow_add]
    exact Nat.mul_div_cancel _ (pow_pos hp.pos _)
  simp [div,AngularLog.arithmetic,AngularLog.lift_prime _ hp]

lemma split_pow (w : R →*₀ ℂ) {p : ℕ} (hp : p.Prime) (hs : p%3=1) {q : R}
    (hq : N q=p) (n : ℕ) (hn : ¬p∣n) (k : ℕ) :
    S w (p^k*n)=geom (w q) (w (star q)) k*S w n := by
  induction k using Nat.twoStepInduction with
  | zero => simp [geom_zero]
  | one => simpa [geom_succ,geom_zero] using split_first w hp hs hq n hn
  | more k ha hb =>
    have h := split_next w hp hs hq (p^k*n)
    rw [show p*(p^k*n)=p^(k+1)*n by rw [pow_succ',mul_assoc],
      show p*(p^(k+1)*n)=p^(k+2)*n by rw [pow_succ' p (k+1),mul_assoc],ha,hb] at h
    linear_combination h - S w n*geom_rec (w q) (w (star q)) k

lemma inert_pow (w : R →*₀ ℂ) {p : ℕ} (hp : p.Prime) (hi : p%3=2) (hw : w (p:R)=1)
    (n : ℕ) (hn : ¬p∣n) (k : ℕ) : S w (p^k*n)=geom 1 (-1) k*S w n := by
  induction k using Nat.twoStepInduction with
  | zero => simp [geom_zero]
  | one => simpa [geom_succ,geom_zero] using inert_first w hp hi n hn
  | more k ha hb =>
    have h := inert_next w hp hi (p^k*n)
    rw [show p*(p^k*n)=p^(k+1)*n by rw [pow_succ',mul_assoc],
      show p*(p^(k+1)*n)=p^(k+2)*n by rw [pow_succ' p (k+1),mul_assoc],ha,hw,one_mul] at h
    linear_combination h - S w n*geom_rec 1 (-1) k

lemma shell_coeff (w : R →*₀ ℂ) (a b : ℕ→ℂ) (hunit : ∀ u∈units, w u=1)
    (h3 : w ram=0 ∧ a 3=0 ∧ b 3=0)
    (hs : ∀ p : ℕ, p.Prime → p%3=1 → ∃ q : R, N q=p ∧ a p=w q ∧ b p=w (star q))
    (hi : ∀ p : ℕ, p.Prime → p%3=2 → w (p:R)=1 ∧ a p=1 ∧ b p= -1) (n : ℕ) :
    S w n=6*((AngularLog.arithmetic a*AngularLog.arithmetic b) n) := by
  let c := AngularLog.arithmetic a*AngularLog.arithmetic b
  have cm := (arith_mult a).mul (arith_mult b)
  induction n using Nat.recOnPrimePow with
  | zero =>
    rw [ArithmeticFunction.map_zero,mul_zero]
    apply Finset.sum_eq_zero
    intro x hx
    have e := (mem_shell _ _).mp hx
    by_cases h : x=0
    · simp [h]
    · exact False.elim ((N_pos h).ne' e)
  | one =>
    have un : shell 1=units := by ext x; rw [mem_shell,mem_units,unit_iff]
    simp [S,un,Finset.sum_congr rfl hunit,card_units,cm.map_one]
  | prime_pow_mul n p k hp hn hk ih =>
    have cop : (p^k).Coprime n := (hp.coprime_iff_not_dvd.mpr hn).pow_left _
    rw [cm.map_mul_of_coprime cop,arith_power a b hp]
    suffices H : S w (p^k*n)=geom (a p) (b p) k*S w n by rw [H,ih]; ring
    rcases show p=3 ∨ p%3=1 ∨ p%3=2 by
      by_cases h : p%3=0
      · exact Or.inl (((Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h)).resolve_left (by decide)).symm
      · omega with h|h|h
    · subst p
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      simp [pow_succ',mul_assoc,ram_step,h3.1,h3.2.1,h3.2.2,geom_succ]
    · obtain ⟨q,hq,ha,hb⟩ := hs p hp h
      rw [ha,hb]; exact split_pow w hp h hq n hn k
    · obtain ⟨hw,ha,hb⟩ := hi p hp h
      rw [ha,hb]; exact inert_pow w hp h hw n hn k

end OMA.AngularShell
end

section
/- The angular character on the lattice, its values at units and the ramified
prime, and the character with its ramified factor deleted. -/
namespace OMA.AngularWeight
open AngularRing AngularShell Complex
open scoped ComplexConjugate

noncomputable def place : R →+* ℂ :=
  (QuadraticAlgebra.lift ⟨AngularSeven.eta,by
    simp only [neg_one_zsmul,one_zsmul]; linear_combination AngularSeven.eta_sq⟩).toRingHom

lemma place_def (x : R) : place x=(x.re:ℂ)+x.im*AngularSeven.eta := by
  change x.re • (1:ℂ) + x.im • AngularSeven.eta=_
  simp

lemma place_star (x : R) : place (star x)=conj (place x) := by
  have e : conj AngularSeven.eta=1-AngularSeven.eta := by
    unfold AngularSeven.eta
    simp only [map_div₀,map_add,map_one,map_mul,Complex.conj_I,Complex.conj_ofReal,
      show conj (2:ℂ)=2 from map_ofNat _ _]
    ring
  simp [place_def,e]; ring

lemma norm_place (x : R) : ‖place x‖^2=(N x:ℝ) := by
  have h := congrArg place (mul_conj x)
  rw [map_mul,place_star,Complex.mul_conj,map_natCast] at h
  rw [←Complex.normSq_eq_norm_sq]
  exact_mod_cast (show (Complex.normSq (place x):ℂ)=(N x:ℂ) from h)

noncomputable def W (m : ℕ) (hm : m≠0) : R →*₀ ℂ where
  toFun x := (place x / (‖place x‖:ℂ))^m
  map_zero' := by simp [hm]
  map_one' := by simp
  map_mul' x y := by simp [mul_div_mul_comm,mul_pow]

lemma W_posNat (m : ℕ) (hm : m≠0) (n : ℕ) (hn : n≠0) : W m hm (n:R)=1 := by
  simp [W,hn]

lemma W_units (k : ℕ) (hk : k≠0) {u : R} (hu : u∈units) :
    W (6*k) (by positivity) u=1 := by
  have hn := (unit_iff _).mp ((mem_units _).mp hu)
  have norm : ‖place u‖=1 := by nlinarith [norm_place u,norm_nonneg (place u),show (N u:ℝ)=1 by simp [hn]]
  have power : u^6=1 := by
    simp only [units,Finset.mem_insert,Finset.mem_singleton] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  simp [W,norm,pow_mul,←map_pow,power]

lemma W_ram (k : ℕ) (hk : k≠0) : W (6*k) (by positivity) ram=(-1:ℂ)^k := by
  have r6 : ram^6=(-27:R) := by decide
  have n3 : ((‖place ram‖:ℝ):ℂ)^2=3 := by exact_mod_cast (by simpa [ram_norm] using norm_place ram : ‖place ram‖^2=3)
  have n27 : ((‖place ram‖:ℝ):ℂ)^6=27 := by
    rw [show (6:ℕ)=2*3 by decide,pow_mul,n3]; norm_num
  change (place ram / (‖place ram‖:ℂ))^(6*k)=_
  rw [pow_mul,div_pow,←map_pow,r6,n27]
  rw [map_neg,show place (27:R)=27 from map_ofNat _ _]; norm_num

noncomputable def unram (w : R →*₀ ℂ) : R →*₀ ℂ where
  toFun x := if 3∣N x then 0 else w x
  map_zero' := by simp
  map_one' := by simp
  map_mul' x y := by
    simp only [N_mul,Nat.prime_three.dvd_mul,map_mul]
    split_ifs <;> simp_all

lemma W_arg (m : ℕ) (hm : m≠0) (x : R) (hx : place x ≠ 0) :
    W m hm x=exp (((m:ℂ)*(place x).arg)*I) := by
  have hn : (‖place x‖:ℂ)≠0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  have h : place x/(‖place x‖:ℂ)=exp ((place x).arg*I) :=
    (div_eq_iff hn).mpr (by rw [mul_comm,norm_mul_exp_arg_mul_I])
  simp only [W,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,h,←Complex.exp_nat_mul,mul_assoc]

lemma W_star (m : ℕ) (hm : m≠0) (x : R) : W m hm (star x)=conj (W m hm x) := by
  simp [W,place_star]

end OMA.AngularWeight
end

section
/- Regroup the absolutely convergent lattice series by norm, remove the
ramified prime, and identify the resulting Euler factors. -/
namespace OMA.AngularArithmetic
open Complex AngularRing AngularShell AngularWeight OeisA218585
open scoped ComplexConjugate

noncomputable def E (w : R →*₀ ℂ) (s : ℂ) (x : R) := w x * (N x:ℂ)^(-s)

lemma E_mul (w : R →*₀ ℂ) (s : ℂ) (x y : R) : E w s (x*y)=E w s x*E w s y := by
  simp [E,N_mul,Complex.natCast_mul_natCast_cpow]; ring

lemma place_coords (u : ℤ×ℤ) : place (coords u)=AngularTail.z u := by rw [place_def]; rfl

lemma E_eq_g (m : ℕ) (hm : m≠0) (s : ℂ) (x : R) :
    E (W m hm) s x=AngularTail.g m s (place x) := by
  by_cases h : place x=0
  · simp [E,W,AngularTail.g,h,hm]
  simp only [E,W,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,AngularTail.g,if_neg h]
  congr 1
  have n : (N x:ℂ)=(‖place x‖:ℂ)^2 := by exact_mod_cast (norm_place x).symm
  rw [n,show -2*s=(2:ℕ)*(-s) by push_cast; ring]
  symm
  apply Complex.cpow_nat_mul'
  all_goals simp [Complex.arg_ofReal_of_nonneg (norm_nonneg _),Real.pi_pos.le,Real.pi_pos]

lemma E_summable (m : ℕ) (hm : m≠0) {s : ℂ} (hs : 1<s.re) :
    Summable (E (W m hm) s) := by
  apply coords.summable_iff.mp
  simpa only [Function.comp_def,E_eq_g,place_coords] using (AngularTail.original m s hs).of_norm

lemma E_unram (w : R →*₀ ℂ) (s : ℂ) (x : R) :
    E (unram w) s x=(if 3∣N x then 0 else E w s x) := by
  by_cases h : 3∣N x <;> simp [unram,h,E]

lemma unram_sum (w : R →*₀ ℂ) (s : ℂ) (su : Summable (E w s)) :
    (∑' x, E (unram w) s x)=(1-E w s ram)*(∑' x, E w s x) := by
  let bad : Set R := {x | 3∣N x}
  have rs : Summable (bad.indicator (E w s)) := su.indicator _
  have difference : ∀ x, E (unram w) s x = E w s x - bad.indicator (E w s) x := by
    intro x; rw [E_unram]; by_cases h : 3∣N x <;> simp [bad,h,Set.indicator]
  have support : Function.support (bad.indicator (E w s)) ⊆ Set.range (ram*·) := by
    intro x hx
    have h : x∈bad := Set.support_indicator_subset hx
    obtain ⟨v,e⟩ := ram_divides h
    exact ⟨v,e.symm⟩
  have eq := (mul_right_injective₀ ram_prime.ne_zero).tsum_eq support
  have scale (x : R) : bad.indicator (E w s) (ram*x)=E w s ram*E w s x := by
    rw [Set.indicator_of_mem (by simp [bad,N_mul,ram_norm] : ram*x∈bad),E_mul]
  rw [tsum_congr difference,su.tsum_sub rs,←eq,tsum_congr scale,tsum_mul_left]
  ring

lemma by_shell (w : R →*₀ ℂ) (s : ℂ) (su : Summable (E w s)) :
    ∑' x, E w s x = ∑' n : ℕ, S w n*(n:ℂ)^(-s) := by
  rw [←(su.hasSum.tsum_fiberwise N).tsum_eq]
  refine tsum_congr fun n => ?_
  have seteq : N ⁻¹' ({n}:Set ℕ)=(shell n : Set R) := by ext x; simp
  rw [seteq,Finset.tsum_subtype']
  unfold S
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun x hx => by rw [E,(mem_shell _ _).mp hx]

noncomputable def fac (p : ℕ) := AngularSplit.pair (xp p) (yp p)
noncomputable def angle (k p : ℕ) : ℝ := (k:ℝ)*(6*(place (fac p)).arg)

lemma specified_coeff (k : ℕ) (hk : k≠0) (n : ℕ) :
    S (unram (W (6*k) (by positivity))) n =
      6*((AngularLog.arithmetic (AngularLog.left (angle k)) *
        AngularLog.arithmetic (AngularLog.right (angle k))) n) := by
  apply shell_coeff
  · intro u hu
    have hn := (unit_iff _).mp ((mem_units _).mp hu)
    simp [unram,hn,W_units k hk hu]
  · norm_num [unram,ram_norm,AngularLog.left,AngularLog.right]
  · intro p hp hs
    let x := fac p
    have hx : N x=p := AngularSplit.specified hp hs
    have hn : ¬3∣p := by omega
    have non : place x≠0 := by
      intro e
      have h := norm_place x
      rw [hx,e,norm_zero] at h
      have := hp.pos; norm_cast at h; omega
    have v := W_arg (6*k) (by positivity) x non
    have hφ : (((6*k:ℕ):ℂ)*(place x).arg)*I=(angle k p:ℂ)*I := by
      simp [angle,x]; ring
    rw [hφ] at v
    refine ⟨x,hx,?_,?_⟩
    · simpa [unram,hx,hn,AngularLog.left,hs] using v.symm
    · simp [unram,N_star,hx,hn,AngularLog.right,hs,W_star,v,←Complex.exp_conj]
  · intro p hp hi
    have hn : ¬3∣p^2 := by
      intro d
      have := Nat.prime_three.dvd_of_dvd_pow d
      omega
    simp [unram,N_nat,hn,W_posNat _ _ _ hp.ne_zero,AngularLog.left,AngularLog.right,hi]

lemma place_fac (p : ℕ) : place (fac p)=
    (⟨(xp p:ℝ)+(yp p:ℝ)/2,Real.sqrt 3*(yp p:ℝ)/2⟩:ℂ) := by
  apply Complex.ext <;> simp [place_def,fac,AngularSplit.pair,AngularSeven.eta,
    Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,Complex.div_ofNat_re,Complex.div_ofNat_im] <;> ring

theorem factorization (k : ℕ) (hk : k≠0) (s : ℂ) (hs : 1<s.re) :
    (1-(-1:ℂ)^k*(3:ℂ)^(-s))*((∑' u : ℤ×ℤ, AngularTail.g (6*k) s (AngularTail.z u))/6) =
      AngularEuler.euler (angle k) s := by
  let w := W (6*k) (Nat.mul_ne_zero (by decide) hk)
  let c := AngularLog.arithmetic (AngularLog.left (angle k))*AngularLog.arithmetic (AngularLog.right (angle k))
  have su : Summable (E w s) := E_summable _ _ hs
  have ru : Summable (E (unram w) s) := by
    apply (su.indicator {x | ¬3∣N x}).congr
    intro x; rw [E_unram]; by_cases h : 3∣N x <;> simp [h,Set.indicator]
  have sum := unram_sum w s su
  have lattice : ∑' x, E w s x = ∑' u : ℤ×ℤ, AngularTail.g (6*k) s (AngularTail.z u) := by
    rw [←coords.tsum_eq (E w s)]
    exact tsum_congr fun x => by rw [show E w s (coords x)=_ from E_eq_g _ _ _ _,place_coords]
  have ramv : E w s ram=(-1:ℂ)^k*(3:ℂ)^(-s) := by
    simp [E,w,W_ram k hk,ram_norm]
  rw [ramv,lattice,by_shell _ _ ru] at sum
  have coeff : ∀ n, S (unram w) n=6*c n := specified_coeff k hk
  simp_rw [coeff,mul_assoc] at sum
  rw [tsum_mul_left] at sum
  have Eul : (∑' n : ℕ, c n*(n:ℂ)^(-s))=AngularEuler.euler (angle k) s := by
    rw [←AngularLog.convolution _ _ hs,LSeries_def₀ (show c 0=0 by simp)]
    exact tsum_congr fun n => by simp only [cpow_neg,div_eq_mul_inv]
  rw [Eul] at sum
  linear_combination -sum/6

end OMA.AngularArithmetic
end

theorem OMA.AngularDeep.arithmetic : OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1.H2 := by
  intro k hk s hs
  have h := OMA.AngularArithmetic.factorization k hk s hs
  have he : OMA.AngularArithmetic.angle k =
      fun p => (k:ℝ)*(6*(⟨(OeisA218585.xp p:ℝ)+(OeisA218585.yp p:ℝ)/2,
        Real.sqrt 3*(OeisA218585.yp p:ℝ)/2⟩:ℂ).arg) := by
    funext p; rw [OMA.AngularArithmetic.angle,OMA.AngularArithmetic.place_fac]
  rw [he] at h
  exact h

theorem OMA.angularHecke : OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1.H1 :=
  OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1.main OMA.AngularDeep.analytic OMA.AngularDeep.arithmetic
end

section
/- Integrated source: proofs/OeisA218585.conjecture_4.R1.H2.R1.H1.R1.H1.R1.H1.R1.H2 -/
-- Step OeisA218585.conjecture_4.R1.H2.R1.H1.R1.H1.R1.H1.R1.H2: hypothesis H2 of reduction OeisA218585.conjecture_4.R1.H2.R1.H1.R1.H1.R1.H1.R1
-- Credit: @ivillar

/-
The three-four-one estimate. For primes in the class 1 mod 3 the combination
`4 cos x cos u + cos 2x cos 2u` is at least `-3`; prime powers contribute a bounded amount;
and the von Mangoldt series over the class 1 mod 3 has a simple pole of residue 1/2 at 1
(Mathlib's `LFunctionResidueClassAux`), so the limiting lower bound is `-3/2 > -7/4`.
-/
namespace F2Oeis
open Filter Real ArithmeticFunction
open scoped Topology Classical

theorem trig (x u : ℝ) : -3 ≤ 4 * (cos x * cos u) + cos (2 * x) * cos (2 * u) := by
  rw [Real.cos_two_mul, Real.cos_two_mul]
  have h1 := Real.cos_sq_le_one x
  have h2 := Real.cos_sq_le_one u
  nlinarith [sq_nonneg (1 + cos x * cos u), mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

theorem cpow_neg_re (n : ℕ) (hn : n ≠ 0) (x y : ℝ) :
    ((n : ℂ) ^ (-(⟨x, y⟩ : ℂ))).re = (n : ℝ) ^ (-x) * cos (y * Real.log n) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [Complex.cpow_def_of_ne_zero hn', ← Complex.natCast_log, Complex.exp_re,
    Real.rpow_def_of_pos hpos]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im]
  rw [show Real.log n * -x - 0 * -y = Real.log n * -x by ring,
    show Real.log n * -y + 0 * -x = -(y * Real.log n) by ring, Real.cos_neg]

theorem cpow_neg_norm (n : ℕ) (hn : n ≠ 0) (x y : ℝ) :
    ‖(n : ℂ) ^ (-(⟨x, y⟩ : ℂ))‖ = (n : ℝ) ^ (-x) := by
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

theorem term_eq (f : ℕ → ℂ) (s : ℂ) (n : ℕ) (hn : n ≠ 0) :
    LSeries.term f s n = f n * (n : ℂ) ^ (-s) := by
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

theorem summ (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ Λ n) {s : ℂ} (hs : 1 < s.re) : LSeriesSummable f s := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  refine Summable.of_norm_bounded (g := fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) s n‖) h.norm
    (fun n => LSeries.norm_term_le s ?_)
  simpa [abs_of_nonneg vonMangoldt_nonneg] using hf n

theorem rho_le (n : ℕ) (hn : n ≠ 0) (h : ℝ) (hh : 0 < h) :
    (n : ℝ) ^ (-(1 + h)) ≤ 1 / n := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
  calc (n : ℝ) ^ (-(1 + h)) ≤ (n : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = 1 / n := by rw [Real.rpow_neg_one, one_div]

/-- The termwise bound. -/
theorem termwise (θ : ℕ → ℝ) (a b : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ Λ n) (hb : ∀ n, ‖b n‖ ≤ Λ n)
    (hap : ∀ p : ℕ, p.Prime → a p = ((Λ p * (if p % 3 = 1 then cos (θ p) else 0) : ℝ) : ℂ))
    (hbp : ∀ p : ℕ, p.Prime → b p = ((Λ p * (if p % 3 = 1 then cos (2 * θ p) else 0) : ℝ) : ℂ))
    (t h : ℝ) (hh : 0 < h) (n : ℕ) :
    (-3) * (LSeries.term (fun n => ((vonMangoldt.residueClass (1 : ZMod 3) n : ℝ) : ℂ))
        (⟨1 + h, 0⟩ : ℂ) n).re + (-5) * ((if n.Prime then 0 else Λ n) / n) ≤
      4 * (LSeries.term a (⟨1 + h, t⟩ : ℂ) n).re + (LSeries.term b (⟨1 + h, 2 * t⟩ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hρ : 0 < (n : ℝ) ^ (-(1 + h)) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) _
  have hΛ : 0 ≤ Λ n := vonMangoldt_nonneg
  have hRn : 0 ≤ vonMangoldt.residueClass (1 : ZMod 3) n := vonMangoldt.residueClass_nonneg _ n
  have eR : (LSeries.term (fun n => ((vonMangoldt.residueClass (1 : ZMod 3) n : ℝ) : ℂ))
        (⟨1 + h, 0⟩ : ℂ) n).re = vonMangoldt.residueClass (1 : ZMod 3) n * (n : ℝ) ^ (-(1 + h)) := by
    rw [term_eq _ _ _ hn, Complex.re_ofReal_mul, cpow_neg_re n hn]
    simp
  rw [eR, term_eq a _ _ hn, term_eq b _ _ hn]
  by_cases hp : n.Prime
  · rw [hap n hp, hbp n hp, Complex.re_ofReal_mul, Complex.re_ofReal_mul, cpow_neg_re n hn,
      cpow_neg_re n hn, if_pos hp]
    have hmod : ((n : ZMod 3) = 1) ↔ n % 3 = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff']
    by_cases h3 : n % 3 = 1
    · have hR : vonMangoldt.residueClass (1 : ZMod 3) n = Λ n := by
        simp [vonMangoldt.residueClass, Set.indicator, hmod.mpr h3]
      rw [hR, if_pos h3, if_pos h3]
      have key := mul_nonneg (mul_nonneg hΛ hρ.le)
        (sub_nonneg.mpr (trig (θ n) (t * Real.log n)))
      have e2 : 2 * t * Real.log n = 2 * (t * Real.log n) := by ring
      rw [e2, zero_div, mul_zero, add_zero]
      have e3 : 4 * (Λ n * cos (θ n) * ((n : ℝ) ^ (-(1 + h)) * cos (t * Real.log n))) +
          Λ n * cos (2 * θ n) * ((n : ℝ) ^ (-(1 + h)) * cos (2 * (t * Real.log n))) -
          (-3 * (Λ n * (n : ℝ) ^ (-(1 + h)))) = Λ n * (n : ℝ) ^ (-(1 + h)) *
          (4 * (cos (θ n) * cos (t * Real.log n)) + cos (2 * θ n) * cos (2 * (t * Real.log n)) - -3) := by
        ring
      linarith
    · have hR : vonMangoldt.residueClass (1 : ZMod 3) n = 0 := by
        simp [vonMangoldt.residueClass, Set.indicator, mt hmod.mp h3]
      rw [hR, if_neg h3, if_neg h3]
      simp
  · rw [if_neg hp]
    have b1 : |(a n * (n : ℂ) ^ (-(⟨1 + h, t⟩ : ℂ))).re| ≤ Λ n / n := by
      calc |(a n * (n : ℂ) ^ (-(⟨1 + h, t⟩ : ℂ))).re|
          ≤ ‖a n * (n : ℂ) ^ (-(⟨1 + h, t⟩ : ℂ))‖ := Complex.abs_re_le_norm _
        _ = ‖a n‖ * (n : ℝ) ^ (-(1 + h)) := by rw [norm_mul, cpow_neg_norm n hn]
        _ ≤ Λ n * (1 / n) := mul_le_mul (ha n) (rho_le n hn h hh) hρ.le hΛ
        _ = Λ n / n := by ring
    have b2 : |(b n * (n : ℂ) ^ (-(⟨1 + h, 2 * t⟩ : ℂ))).re| ≤ Λ n / n := by
      calc |(b n * (n : ℂ) ^ (-(⟨1 + h, 2 * t⟩ : ℂ))).re|
          ≤ ‖b n * (n : ℂ) ^ (-(⟨1 + h, 2 * t⟩ : ℂ))‖ := Complex.abs_re_le_norm _
        _ = ‖b n‖ * (n : ℝ) ^ (-(1 + h)) := by rw [norm_mul, cpow_neg_norm n hn]
        _ ≤ Λ n * (1 / n) := mul_le_mul (hb n) (rho_le n hn h hh) hρ.le hΛ
        _ = Λ n / n := by ring
    have c1 := (abs_le.mp b1).1
    have c2 := (abs_le.mp b2).1
    have c3 := mul_nonneg hRn hρ.le
    linarith

theorem three_four_one : ∀ (θ : ℕ → ℝ) (a b : ℕ → ℂ), (∀ n, ‖a n‖ ≤ Λ n) → (∀ n, ‖b n‖ ≤ Λ n) →
  (∀ p : ℕ, p.Prime → a p = ((Λ p*(if p%3 = 1 then cos (θ p) else 0):ℝ):ℂ)) →
  (∀ p : ℕ, p.Prime → b p = ((Λ p*(if p%3 = 1 then cos (2*θ p) else 0):ℝ):ℂ)) →
  ∀ t : ℝ, ∀ᶠ h : ℝ in 𝓝[>] 0, -(7/4:ℝ) ≤ h *
    (4*(LSeries a ((⟨1,t⟩:ℂ)+h)).re + (LSeries b ((⟨1,2*t⟩:ℂ)+h)).re) := by
  intro θ a b ha hb hap hbp t
  have hGsum : Summable (fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ)) := by
    have h := vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
    refine h.congr (fun n => ?_)
    have : vonMangoldt.residueClass (0 : ZMod 1) n = Λ n := by
      simp [vonMangoldt.residueClass, Set.indicator, Subsingleton.elim (n : ZMod 1) 0]
    rw [this]
  have hRle : ∀ n, ‖((vonMangoldt.residueClass (1 : ZMod 3) n : ℝ) : ℂ)‖ ≤ Λ n := by
    intro n
    rw [Complex.norm_real, Real.norm_of_nonneg (vonMangoldt.residueClass_nonneg _ n)]
    exact vonMangoldt.residueClass_le _ n
  have key : ∀ h : ℝ, 0 < h →
      -(3/2) - 3 * (h * (vonMangoldt.LFunctionResidueClassAux (1 : ZMod 3) ((1 + h : ℝ) : ℂ)).re)
        - 5 * (h * ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ)) ≤
      h * (4*(LSeries a ((⟨1,t⟩:ℂ)+h)).re + (LSeries b ((⟨1,2*t⟩:ℂ)+h)).re) := by
    intro h hh
    have e1 : (⟨1, t⟩ : ℂ) + (h : ℂ) = ⟨1 + h, t⟩ := by apply Complex.ext <;> simp
    have e2 : (⟨1, 2 * t⟩ : ℂ) + (h : ℂ) = ⟨1 + h, 2 * t⟩ := by apply Complex.ext <;> simp
    have e0 : ((1 + h : ℝ) : ℂ) = ⟨1 + h, 0⟩ := rfl
    rw [e1, e2]
    have hre : ∀ y : ℝ, 1 < (⟨1 + h, y⟩ : ℂ).re := fun y => by simp [hh]
    have A1 := Complex.hasSum_re (summ a ha (hre t)).hasSum
    have B1 := Complex.hasSum_re (summ b hb (hre (2 * t))).hasSum
    have R0 := Complex.hasSum_re (summ _ hRle (hre 0)).hasSum
    have le := hasSum_le (termwise θ a b ha hb hap hbp t h hh)
      ((R0.mul_left (-3)).add (hGsum.hasSum.mul_left (-5))) ((A1.mul_left 4).add B1)
    have eqAux := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 3) (a := 1) isUnit_one
      (show ((1 + h : ℝ) : ℂ) ∈ {s : ℂ | 1 < s.re} by simp [hh])
    have tot : (Nat.totient 3 : ℂ) = 2 := by
      rw [Nat.totient_prime Nat.prime_three]; norm_num
    have hval : (∑' n, LSeries.term (fun n => ((vonMangoldt.residueClass (1 : ZMod 3) n : ℝ) : ℂ))
        (⟨1 + h, 0⟩ : ℂ) n).re =
        (vonMangoldt.LFunctionResidueClassAux (1 : ZMod 3) ((1 + h : ℝ) : ℂ)).re + 1 / (2 * h) := by
      rw [eqAux]
      simp only [tot]
      have e3 : ((2 : ℂ)⁻¹ / (((1 + h : ℝ) : ℂ) - 1)) = ((1 / (2 * h) : ℝ) : ℂ) := by
        push_cast
        field_simp
        ring
      rw [e3, Complex.sub_re, Complex.ofReal_re]
      change (LSeries _ _).re = _
      rw [e0]
      ring
    rw [hval] at le
    have hmul := mul_le_mul_of_nonneg_left le hh.le
    have hne : h ≠ 0 := hh.ne'
    have expand : h * (-3 * ((vonMangoldt.LFunctionResidueClassAux (1 : ZMod 3) ((1 + h : ℝ) : ℂ)).re
        + 1 / (2 * h)) + -5 * ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ)) =
        -(3/2) - 3 * (h * (vonMangoldt.LFunctionResidueClassAux (1 : ZMod 3) ((1 + h : ℝ) : ℂ)).re)
        - 5 * (h * ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ)) := by
      field_simp
      ring
    rw [expand] at hmul
    exact hmul
  have lim : Tendsto (fun h : ℝ =>
      -(3/2) - 3 * (h * (vonMangoldt.LFunctionResidueClassAux (1 : ZMod 3) ((1 + h : ℝ) : ℂ)).re)
        - 5 * (h * ∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ))) (𝓝[>] 0) (𝓝 (-(3/2))) := by
    have hcont := vonMangoldt.continuousOn_LFunctionResidueClassAux (1 : ZMod 3)
    have h1mem : (1 : ℂ) ∈ {s : ℂ | 1 ≤ s.re} := by simp
    have hto : Tendsto (fun h : ℝ => ((1 + h : ℝ) : ℂ)) (𝓝[>] 0) (𝓝[{s : ℂ | 1 ≤ s.re}] 1) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have : Tendsto (fun h : ℝ => ((1 + h : ℝ) : ℂ)) (𝓝 0) (𝓝 (((1 + 0 : ℝ)) : ℂ)) :=
          (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with h hh
        show 1 ≤ ((1 + h : ℝ) : ℂ).re
        rw [Complex.ofReal_re]
        linarith [Set.mem_Ioi.mp hh]
    have haux : Tendsto (fun h : ℝ =>
        (vonMangoldt.LFunctionResidueClassAux (1 : ZMod 3) ((1 + h : ℝ) : ℂ)).re) (𝓝[>] 0)
        (𝓝 (vonMangoldt.LFunctionResidueClassAux (1 : ZMod 3) 1).re) :=
      (Complex.continuous_re.tendsto _).comp ((hcont 1 h1mem).tendsto.comp hto)
    have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have := ((tendsto_const_nhds (x := -(3/2 : ℝ))).sub ((hid.mul haux).const_mul 3)).sub
      ((hid.mul_const (∑' n : ℕ, (if n.Prime then 0 else Λ n) / (n : ℝ))).const_mul 5)
    simpa using this
  filter_upwards [lim.eventually_const_lt (by norm_num : -(7/4:ℝ) < -(3/2)), self_mem_nhdsWithin]
    with h h1 h2
  exact h1.le.trans (key h h2)

end F2Oeis

theorem OMA.angularPositivity : OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1.H2 :=
  F2Oeis.three_four_one
end

section
/- Integrated source: proofs/OeisA218585.conjecture_4.R1.H2.R1.H1.R1.H1.R1.H2 -/
-- Step OeisA218585.conjecture_4.R1.H2.R1.H1.R1.H1.R1.H2: hypothesis H2 of reduction OeisA218585.conjecture_4.R1.H2.R1.H1.R1.H1.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-
A Dirichlet series whose coefficients vanish at the primes and are bounded by the von Mangoldt
function converges absolutely and uniformly on `1 ≤ re s`: its terms are bounded there by
`Λ n / n` restricted to non-primes, which is summable
(`ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div` with modulus `1`).
Continuity follows from the Weierstrass M-test.
-/

namespace OeisA218585StepCont

open ArithmeticFunction

lemma summable_nonprime : Summable fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ) := by
  have h := vonMangoldt.summable_residueClass_non_primes_div (q := 1) (0 : ZMod 1)
  refine h.congr ?_
  intro n
  have hres : vonMangoldt.residueClass (0 : ZMod 1) n = Λ n :=
    Set.indicator_of_mem (show n ∈ {n : ℕ | (n : ZMod 1) = 0} from Subsingleton.elim _ _) _
  rw [hres]

theorem continuousOn_LSeries (b : ℕ → ℂ) (hb : ∀ p : ℕ, p.Prime → b p = 0)
    (hΛ : ∀ n, ‖b n‖ ≤ Λ n) : ContinuousOn (LSeries b) {s : ℂ | 1 ≤ s.re} := by
  have hb0 : b 0 = 0 := by
    have h := hΛ 0
    simpa using h
  show ContinuousOn (fun s : ℂ => ∑' n, LSeries.term b s n) {s : ℂ | 1 ≤ s.re}
  refine continuousOn_tsum (u := fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ)) ?_
    summable_nonprime ?_
  · intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero]
      exact continuousOn_const
    · have e : (fun s : ℂ => LSeries.term b s n) = fun s : ℂ => b n * (n : ℂ) ^ (-s) := by
        funext s
        exact LSeries.term_def₀ hb0 s n
      rw [e]
      exact (continuous_const.mul
        (continuous_neg.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn)))).continuousOn
  · intro n s hs
    have hs' : 1 ≤ s.re := hs
    rw [LSeries.norm_term_eq]
    by_cases h0 : n = 0
    · subst h0
      simp
    · rw [if_neg h0]
      by_cases hp : n.Prime
      · rw [if_pos hp, hb n hp]
        simp
      · rw [if_neg hp]
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
        have hpow : (n : ℝ) ≤ (n : ℝ) ^ s.re := by
          have := Real.rpow_le_rpow_of_exponent_le hn1 hs'
          rwa [Real.rpow_one] at this
        exact div_le_div₀ vonMangoldt_nonneg (hΛ n) (by linarith) hpow

end OeisA218585StepCont

theorem OMA.angularPrimePowers : OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1.H2 :=
  fun b hb hL => OeisA218585StepCont.continuousOn_LSeries b hb hL
end

section
/- Integrated source: proofs/OeisA218585.conjecture_3.R1.H2 -/
/-
# Dyadic counts of primes congruent to one modulo three

The arithmetic progression estimate below is from Marcus Buffett’s proof of Erdős 727,
merged in PR 1835. The Tauberian proof and its original attribution are retained below.
The dyadic unweighting argument is adapted from @PanPapag, commit 98fbdd8. The two reductions require the same prime count.
-/

/-
The proof of θ(x) ~ x (and of the weak prime number theorem it rests on, via the Wiener-Ikehara
tauberian theorem) is ported from the PrimeNumberTheoremAnd project,
  https://github.com/AlexKontorovich/PrimeNumberTheoremAnd , commit 55270df807,
by Alex Kontorovich, Terence Tao and the project's contributors, used under the Apache License 2.0.
Files used, in this order (each in its own section below):
  PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean
  PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean
  PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
  PrimeNumberTheoremAnd/Sobolev.lean
  PrimeNumberTheoremAnd/Fourier.lean
  PrimeNumberTheoremAnd/SmoothExistence.lean
  PrimeNumberTheoremAnd/Wiener.lean (up to and including theorem WeakPNT)
  PrimeNumberTheoremAnd/Consequences.lean (only add_isLittleO'', WeakPNT', WeakPNT'',
    isLittleO_sqrt_mul_log and chebyshev_asymptotic)
Modifications: imports merged into the single import above; blueprint annotations and all
attributes (blueprint, ext, continuity, fun_prop, gcongr, norm_cast) and option settings removed,
with the call sites that relied on them adjusted (an explicit CS.ext lemma, explicit continuity
facts handed to fun_prop, an explicit monotonicity step in place of gcongr); the proofs of
second_fourier and limiting_cor_aux were rewritten so that they compile without the
backward.isDefEq.respectTransparency option; four unproved and unused lemmas of Wiener.lean
(prelim_decay_2, prelim_decay_3, decay_alt and the definition AbsolutelyContinuous) were deleted.
The progression argument also adapts the arithmetic-progression consequence from the same project.
-/

-- Ported from PrimeNumberTheoremAnd: Mathlib/Algebra/Notation/Support.lean, Mathlib/Analysis/Asymptotics/Asymptotics.lean, Mathlib/Analysis/SpecialFunctions/Log/Basic.lean
section PNTX_Base

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function


open Filter Topology

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']


theorem _root_.Filter.Eventually.natCast {f : ℝ → Prop} (hf : ∀ᶠ x in atTop, f x) :
    ∀ᶠ n : ℕ in atTop, f n :=
  tendsto_natCast_atTop_atTop.eventually hf

theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Asymptotics


open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end PNTX_Base

-- Ported from PrimeNumberTheoremAnd: Sobolev.lean
section PNTX_Sobolev

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

theorem CS.ext {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : CS n E}
    (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev W21 := W1 2 ℂ

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const

omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)

end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩

def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2

instance : Neg (CS n E) where neg := neg

@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩

instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

lemma continuous (f : CS n E) : Continuous f := f.h1.continuous

noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv

lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt

lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  refine CS.ext (funext fun x => ?_) ; exact (f.hasDerivAt x |>.const_smul R).deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  refine CS.ext (funext fun v => ?_) ; by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv

lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • _root_.deriv f (R⁻¹ • x)) x := by
  convert hasDerivAt (f.scale R) x ; rw [deriv_scale'] ; rfl

lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩

end CS

namespace trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end trunc

namespace W1

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous

lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f - g) = deriv f - deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)

instance : Sub (W1 n E) where sub := sub

lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := SchwartzMap.derivCLM ℝ ℂ f)

noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

end W1

namespace W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))

noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun

noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz

def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv

instance : Coe (CS 2 ℂ) W21 where coe := ofCS2

instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩

instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

lemma hf (f : W21) : Integrable f := f.integrable zero_le_two

lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two

lemma hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl

end W21

theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by

  -- Definitions
  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv

  -- Properties of h
  have ch {R} : Continuous (fun v => (h R v : ℂ)) :=
    continuous_ofReal.comp <| continuous_const.sub (CS.continuous _)
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    convert! CS.hasDerivAt_scale (g : CS 2 ℝ) R v |>.const_sub 1 using 1
    simp [h', CS.deriv_scale', show g.deriv.toFun = deriv g.toFun from rfl]
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := ((g.scale R).deriv.hasDerivAt v).neg
  have hh1 R v : |h R v| ≤ 1 := by
    by_cases hR : R = 0 <;>
      simp only [CS.scale, funscale, smul_eq_mul, hR, ↓reduceDIte, Pi.zero_apply, sub_zero,
        abs_one, le_refl, h]
    rw [abs_le] ; constructor <;>
    linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul v

  -- Proof
  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)

  · let F R v := ‖h R v * f v‖
    have eh v : ∀ᶠ R in atTop, h R v = 0 := by
      filter_upwards [(vR v).eventually g.zero, eventually_ne_atTop 0] with R hR hR'
      simp [h, hR, CS.scale, hR', funscale, mul_comm R⁻¹]
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R
      exact (ch.mul f.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply Eventually.of_forall ; intro R
      apply Eventually.of_forall ; intro v
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 f.hf.norm e4

  · let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
    · have this R v :
        deriv (deriv (fun v => h R v * f v)) v =
          h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
        have df v : HasDerivAt f (f' v) v := f.hasDerivAt v
        have df' v : HasDerivAt f' (f'' v) v := f'.hasDerivAt v
        have l3 v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v :=
          (dh R v).ofReal_comp.mul (df v)
        have l5 : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v :=
          (dh' R v).ofReal_comp.mul (df v)
        have l7 : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v :=
          (dh R v).ofReal_comp.mul (df' v)
        have d1 : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v :=
          funext (fun v => (l3 v).deriv)
        rw [d1] ; convert! (l5.add l7).deriv using 1 ; ring
      simp_rw [this, F]

    obtain ⟨c1, mg'⟩ := g'.bounded
    obtain ⟨c2, mg''⟩ := g''.bounded
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R ; apply (Continuous.norm ?_).aestronglyMeasurable
      exact ((ch''.mul f.continuous).add ((continuous_const.mul ch').mul f.deriv.continuous)).add
        (ch.mul f.deriv.deriv.continuous)
    have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
      have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have hR' : R ≠ 0 := by linarith
        have : 0 ≤ R := by linarith
        simp only [CS.deriv_scale, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg, abs_mul,
          abs_inv, abs_eq_self.mpr this, ge_iff_le, h']
        simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul]
        convert_to _ ≤ c1 * 1
        · simp
        · rw [mul_comm]
          apply mul_le_mul (mg' _)
            (inv_le_of_inv_le₀ (by linarith) (by simpa using hR)) (by positivity)
          exact (abs_nonneg _).trans (mg' 0)
      have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have e1 : 0 ≤ R := by linarith
        have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le₀ (by linarith) (by simpa using hR)
        have e3 : R ≠ 0 := by linarith
        simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg,
          abs_mul, abs_inv, abs_eq_self.mpr e1, ge_iff_le, h'']
        convert_to _ ≤ 1 * (1 * c2)
        · simp
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        simp only [CS.scale, e3, ↓reduceDIte, funscale, smul_eq_mul] ; apply mg''
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply Eventually.of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp only [Complex.norm_mul,
        Complex.norm_ofNat, norm_real, norm_eq_abs] <;> gcongr
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume :=
      (((f.hf.norm).const_mul _).add ((f.hf'.norm).const_mul _)).add f.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      have evg' : g' =ᶠ[𝓝 0] 0 := by convert! ← g.zero.deriv ; exact deriv_const' _
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by convert! ← evg'.deriv ; exact deriv_const' _
      refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by
          filter_upwards [(vR v).eventually evg'', eventually_ne_atTop 0] with R hR hR'
          simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul,
            neg_eq_zero, mul_eq_zero, inv_eq_zero, hR', false_or, h'']
          simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul, mul_comm R⁻¹]
          exact hR
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh'' v] with R hR ; simp [hR]
      · have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by
          filter_upwards [(vR v).eventually evg'] with R hR
          simp [g'] at hR
          simp [h', CS.deriv_scale', mul_comm R⁻¹, hR]
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh' v] with R hR ; simp [hR]
      · simpa [h] using! ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4

end PNTX_Sobolev

-- Ported from PrimeNumberTheoremAnd: Fourier.lean
section PNTX_Fourier

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 :=
  NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [Circle.norm_coe, one_add_one_eq_two])⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas

theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv

end PNTX_Fourier

-- Ported from PrimeNumberTheoremAnd: SmoothExistence.lean
section PNTX_Smooth

open MeasureTheory Set Real
open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]



lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport, Function.support_id']
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith

end PNTX_Smooth

-- Ported from PrimeNumberTheoremAnd: Wiener.lean (up to and including theorem WeakPNT)
section PNTX_Wiener

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]



noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'

lemma nterm_eq_norm_term {f : ℕ → ℂ} : nterm f σ' n = ‖term f σ' n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]

theorem norm_term_eq_nterm_re (s : ℂ) :
    ‖term f s n‖ = nterm f (s.re) n := by
  simp only [nterm, term, apply_ite (‖·‖), norm_zero, norm_div]
  apply ite_congr rfl (fun _ ↦ rfl)
  intro h
  congr
  refine norm_natCast_cpow_of_pos (by omega) s

lemma hf_coe1 (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hσ : 1 < σ') :
    ∑' i, (‖term f σ' i‖₊ : ENNReal) ≠ ⊤ := by
  simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal]
  norm_cast
  apply Summable.toNNReal
  convert hf σ' hσ with i
  simp [nterm_eq_norm_term]

instance instMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype _
instance instBorelSpace : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)


lemma first_fourier_aux1 (hψ : AEMeasurable ψ) {x : ℝ} (n : ℕ) : AEMeasurable fun (u : ℝ) ↦
    (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖ₑ : ENNReal) := by
  fun_prop

lemma first_fourier_aux2a :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n) / x))) = -(y * ((n) / x).log) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log ((n) / x))) := by ring
    _ = _ := by rw [div_self (by norm_num), one_mul]

lemma first_fourier_aux2 (hx : 0 < x) (n : ℕ) :
    term f σ' n * 𝐞 (-(y * (1 / (2 * π) * Real.log (n / x)))) • ψ y =
    term f (σ' + y * I) n • (ψ y * x ^ (y * I)) := by
  by_cases hn : n = 0
  · simp [term, hn]
  simp only [term, hn, ↓reduceIte]
  calc
    _ = (f n * (cexp ((2 * π * -(y * (1 / (2 * π) * Real.log (n / x)))) * I) /
        ↑((n : ℝ) ^ σ'))) • ψ y := by
      rw [Circle.smul_def, fourierChar_apply, ofReal_cpow (by norm_num)]
      simp only [one_div, mul_inv_rev, mul_neg, ofReal_neg, ofReal_mul, ofReal_ofNat, ofReal_inv,
        neg_mul, smul_eq_mul, ofReal_natCast]
      ring
    _ = (f n * (x ^ (y * I) / n ^ (σ' + y * I))) • ψ y := by
      congr 2
      have l1 : 0 < (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr hn
      have l2 : (x : ℂ) ≠ 0 := by simp [hx.ne.symm]
      have l3 : (n : ℂ) ≠ 0 := by simp [hn]
      rw [Real.rpow_def_of_pos l1, Complex.cpow_def_of_ne_zero l2, Complex.cpow_def_of_ne_zero l3]
      push_cast
      simp_rw [← Complex.exp_sub]
      congr 1
      rw [first_fourier_aux2a, Real.log_div l1.ne.symm hx.ne.symm]
      push_cast
      rw [Complex.ofReal_log hx.le]
      ring
    _ = _ := by simp ; group

lemma first_fourier (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hsupp : Integrable ψ) (hx : 0 < x) (hσ : 1 < σ') :
    ∑' n : ℕ, term f σ' n * (𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))) =
    ∫ t : ℝ, LSeries f (σ' + t * I) * ψ t * x ^ (t * I) := by

  calc
    _ = ∑' n, term f σ' n * ∫ (v : ℝ), 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp only [Real.fourier_eq]
      simp only [one_div, mul_inv_rev, RCLike.inner_apply', conj_trivial]
    _ = ∑' n, ∫ (v : ℝ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp [integral_const_mul]
    _ = ∫ (v : ℝ), ∑' n, term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · refine fun _ ↦ AEMeasurable.aestronglyMeasurable ?_
        have := hsupp.aemeasurable
        fun_prop
      · simp only [enorm_mul]
        simp_rw [lintegral_const_mul'' _ (first_fourier_aux1 hsupp.aemeasurable _)]
        calc
          _ = (∑' (i : ℕ), ‖term f σ' i‖ₑ) * ∫⁻ (a : ℝ), ‖ψ a‖ₑ ∂volume := by
            simp [ENNReal.tsum_mul_right, enorm_eq_nnnorm]
          _ ≠ ⊤ := ENNReal.mul_ne_top (hf_coe1 hf hσ)
            (ne_top_of_lt hsupp.2)
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries]
      rw [← Summable.tsum_smul_const]
      · simp_rw [first_fourier_aux2 hx]
      · apply Summable.of_norm
        convert hf σ' hσ with n
        rw [norm_term_eq_nterm_re]
        simp



lemma second_fourier_integrable_aux1a (hσ : 1 < σ') :
    IntegrableOn (fun (x : ℝ) ↦ cexp (-((x : ℂ) * ((σ' : ℂ) - 1)))) (Ici (-Real.log x)) := by
  norm_cast
  suffices IntegrableOn (fun (x : ℝ) ↦ (rexp (-(x * (σ' - 1))))) (Ici (-x.log)) _ from this.ofReal
  simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x)]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_integrable_aux1 (hcont : Measurable ψ) (hsupp : Integrable ψ) (hσ : 1 < σ') :
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-Real.log x))).prod volume
    Integrable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
    (𝐞 (Multiplicative.ofAdd (-(a * (u / (2 * π))))) : ℂ) • ψ a) ν := by
  intro ν
  constructor
  · apply Measurable.aestronglyMeasurable
    -- `Multiplicative.ofAdd x` is definitionally `x`; unfold it by `change` since `fun_prop`
    -- does not see through it.
    change Measurable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
      (𝐞 (-(a * (u / (2 * π)))) : ℂ) • ψ a)
    simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, smul_eq_mul]
    fun_prop
  · let f1 : ℝ → ENNReal := fun a1 ↦ ‖cexp (-(↑a1 * (↑σ' - 1)))‖ₑ
    let f2 : ℝ → ENNReal := fun a2 ↦ ‖ψ a2‖ₑ
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, Function.uncurry]
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact ENNReal.mul_lt_top (second_fourier_integrable_aux1a hσ).2 hsupp.2

lemma second_fourier_integrable_aux2 (hσ : 1 < σ') :
    IntegrableOn (fun (u : ℝ) ↦ cexp ((1 - ↑σ' - ↑t * I) * ↑u)) (Ioi (-Real.log x)) := by
  refine (integrable_norm_iff (Measurable.aestronglyMeasurable <| by fun_prop)).mp ?_
  suffices IntegrableOn (fun a ↦ rexp (-(σ' - 1) * a)) (Ioi (-x.log)) _ by simpa [Complex.norm_exp]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_aux (hx : 0 < x) :
    -(cexp (-((1 - ↑σ' - ↑t * I) * ↑(Real.log x))) / (1 - ↑σ' - ↑t * I)) =
    ↑(x ^ (σ' - 1)) * (↑σ' + ↑t * I - 1)⁻¹ * ↑x ^ (↑t * I) := by
  calc
    _ = cexp (↑(Real.log x) * ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [← div_neg]; ring_nf
    _ = (x ^ ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), Complex.ofReal_log hx.le]
    _ = (x ^ ((σ' : ℂ) - 1)) * (x ^ (↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hx))]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring

lemma second_fourier (hcont : Measurable ψ) (hsupp : Integrable ψ)
    {x σ' : ℝ} (hx : 0 < x) (hσ : 1 < σ') :
    ∫ u in Ici (-log x), Real.exp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    (x^(σ' - 1) : ℝ) * ∫ t, (1 / (σ' + t * I - 1)) * ψ t * x^(t * I) ∂ volume := by

  conv in ↑(rexp _) * _ => { rw [Real.fourier_real_eq, ← smul_eq_mul, ← integral_smul] }
  rw [MeasureTheory.integral_integral_swap]
  swap
  · exact second_fourier_integrable_aux1 hcont hsupp hσ
  rw [← integral_const_mul]
  congr 1; ext t
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [fun (a b d : ℂ) ↦ show a * (b * (ψ t) * d) = (a * b * d) * ψ t by ring]
  simp_rw [← mul_assoc]
  rw [integral_mul_const]
  congr 1
  push_cast
  simp_rw [← Complex.exp_add]
  have (u : ℝ) :
      -↑u * (↑σ' - 1) + 2 * ↑π * -(↑t * (↑u / (2 * ↑π))) * I = (1 - σ' - t * I) * u := calc
    _ = -↑u * (↑σ' - 1) + (2 * ↑π) / (2 * ↑π) * -(↑t * ↑u) * I := by ring
    _ = -↑u * (↑σ' - 1) + 1 * -(↑t * ↑u) * I := by rw [div_self (by norm_num)]
    _ = _ := by ring
  simp_rw [this]
  let c : ℂ := (1 - ↑σ' - ↑t * I)
  have : c ≠ 0 := by simp [Complex.ext_iff, c, sub_ne_zero.mpr hσ.ne]
  let f' (u : ℝ) := cexp (c * u)
  let f := fun (u : ℝ) ↦ (f' u) / c
  have hderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt f (f' u) u := by
    intro u _
    rw [show f' u = cexp (c * u) * (c * 1) / c by simp only [f']; field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun (x : ℝ) ↦ ‖cexp (c * ↑x)‖ / ‖c‖) atTop (𝓝 (0 / ‖c‖)) by
      simpa [f, f'] using this
    apply Filter.Tendsto.div_const
    suffices Tendsto (· * (1 - σ')) atTop atBot by simpa [Complex.norm_exp, mul_comm (1 - σ'), c]
    exact Tendsto.atTop_mul_const_of_neg (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (second_fourier_integrable_aux2 hσ) hf]
  simpa [f, f'] using second_fourier_aux hx



lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)

lemma decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos _
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast ; simp only [Real.norm_eq_abs, abs_eq_self.2 l1.le]
  have l3 : ‖1 / ((4 : ℂ) * ↑π ^ 2)‖ ≤ (4 * π ^ 2)⁻¹ := by simp
  have key := fourierIntegral_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [F_sub f.hf (f.hf''.const_mul (1 / (4 * ↑π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, l2, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  change _ ≤ W21.norm _
  rw [norm_neg, F_mul, norm_mul, W21.norm]
  gcongr <;> apply VectorFourier.norm_fourierIntegral_le_integral_norm

lemma decay_bounds_cor (ψ : W21) :
    ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  simpa only [div_eq_mul_inv] using ⟨_, decay_bounds_key ψ⟩

lemma continuous_FourierIntegral (ψ : W21) : Continuous (𝓕 (ψ : ℝ → ℂ)) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by simp only [innerₗ_apply_apply, RCLike.inner_apply', conj_trivial, continuous_mul])
    ψ.hf

lemma W21.integrable_fourier (ψ : W21) (hc : c ≠ 0) :
    Integrable fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c) := by
  have l1 (C) : Integrable (fun u ↦ C / (1 + (u / c) ^ 2)) volume := by
    simpa using! (integrable_inv_one_add_sq.comp_div hc).const_mul C
  have l2 : AEStronglyMeasurable (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) volume := by
    apply Continuous.aestronglyMeasurable ; have := continuous_FourierIntegral ψ ; fun_prop
  obtain ⟨C, h⟩ := decay_bounds_cor ψ
  apply @Integrable.mono' ℝ ℂ _ volume _ _ (fun u => C / (1 + (u / c) ^ 2)) (l1 C) l2 ?_
  apply Eventually.of_forall (fun x => h _)





lemma continuous_LSeries_aux (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by

  have l1 i : Continuous fun x : ℝ ↦ term f (σ' + x * I) i := by
    by_cases h : i = 0
    · simpa [h] using continuous_const
    · simpa [h] using! continuous_const.div (continuous_const.cpow (by fun_prop) (by simp [h]))
        (fun x => by simp [h])
  have l2 n (x : ℝ) : ‖term f (σ' + x * I) n‖ = nterm f σ' n := by
    by_cases h : n = 0
    · simp [h, nterm]
    · simp [h, nterm, cpow_add _ _ (Nat.cast_ne_zero.mpr h),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
  exact continuous_tsum l1 hf (fun n x => le_of_eq (l2 n x))

-- Here compact support is used but perhaps it is not necessary
lemma limiting_fourier_aux (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) (σ' : ℝ)
    (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ)
      (u / (2 * π)) = ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l3 : 0 < x := zero_lt_one.trans_le hx
  have l1 (σ') (hσ' : 1 < σ') := first_fourier hf hint l3 hσ'
  have l2 (σ') (hσ' : 1 < σ') := second_fourier ψ.h1.continuous.measurable hint l3 hσ'
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [l3])
  have l6 : Continuous fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    apply ((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    exact l6.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := by
    intro h ; have := congr_arg Complex.re h ; simp at this ; linarith
  have l7 : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    simp only [one_div, ← mul_assoc]
    refine ((continuous_const.mul <| Continuous.inv₀ ?_ e2).mul ψ.h1.continuous).mul l8
    fun_prop
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    apply l7.integrable_of_hasCompactSupport
    exact ψ.h2.mul_left.mul_right.mul_left.mul_left

  simp_rw [l1 σ' hσ', l2 σ' hσ', ← integral_const_mul, ← integral_sub l4 l5]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  left ; left
  field_simp [e2]
  norm_cast
  simp [mul_assoc, ← rpow_add l3]

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i

def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n

/- `nnabla` is the backward difference `u n - u (n+1)`; kept alongside `nabla`
   for summation-by-parts identities that prefer that orientation. -/
def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)

def shift (u : α → E) (n : α) : E := u (n + 1)

@[simp] lemma cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]

lemma cumsum_succ [AddCommMonoid E] {u : ℕ → E} (n : ℕ) :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]

@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]

lemma neg_cumsum [AddCommGroup E] {u : ℕ → E} : -(cumsum u) = cumsum (-u) :=
  funext (fun n => by simp [cumsum])

lemma cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)

omit [Sub α] in
lemma neg_nabla [Ring E] {u : α → E} : -(nabla u) = nnabla u := by ext n ; simp [nabla, nnabla]

omit [Sub α] in
@[simp] lemma nabla_mul [Ring E] {u : α → E} {c : E} : nabla (fun n => c * u n) = c • nabla u := by
  ext n ; simp [nabla, mul_sub]

omit [Sub α] in
@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]

end nabla

lemma Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, sum_range_add, sum_range_one, add_comm 1] ; rfl

lemma Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]

lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} :
    cumsum (a * b) (n + 1) = A (n + 1) * b n - A 0 * b 0 -
    cumsum (shift A * fun i => (b (i + 1) - b i)) n := by
  have l1 : ∑ x ∈ Finset.range (n + 1), A (x + 1) * b x = ∑ x ∈ Finset.range n,
      A (x + 1) * b x + A (n + 1) * b n :=
    Finset.sum_shift_back
  have l2 : ∑ x ∈ Finset.range (n + 1), A x * b x = A 0 * b 0 + ∑ x ∈ Finset.range n,
      A (x + 1) * b (x + 1) :=
    Finset.sum_shift_front
  simp only [cumsum, ha, Pi.mul_apply, nabla, sub_mul, Finset.sum_sub_distrib, l1, l2, shift,
    mul_sub]
  abel

lemma summation_by_parts' {E : Type*} [Ring E] {a b : ℕ → E} {n : ℕ} :
    cumsum (a * b) (n + 1) = cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * nabla b) n := by
  simpa using! summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp)

lemma summation_by_parts'' {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  ext n ; apply summation_by_parts'

lemma summable_iff_bounded {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1

lemma Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO

lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]

lemma BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

lemma BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, norm_eq_abs, Pi.one_apply,
    eventually_atTop]
  constructor <;> intro ⟨C, n₀, h⟩ <;> use C
  · refine ⟨n₀ + N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (m := N) (n := n) (by grind)
    exact h _ <| Nat.add_le_add_iff_right.mp hn
  · exact ⟨n₀, fun n hn => h _ (by grind)⟩

lemma summable_iff_bounded' {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 ≤ u n) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  obtain ⟨N, hu⟩ := eventually_atTop.mp hu
  have e2 : cumsum (fun i ↦ u (i + N)) = fun n => cumsum u (n + N) - cumsum u N := by
    ext n ; simp_rw [cumsum, add_comm _ N, Finset.sum_range_add] ; ring
  rw [← summable_nat_add_iff N, summable_iff_bounded (fun n => hu _ <| Nat.le_add_left N n), e2]
  simp_rw [sub_eq_add_neg, BoundedAtFilter.add_const, BoundedAtFilter.comp_add]

lemma bounded_of_shift {u : ℕ → ℝ} (h : BoundedAtFilter atTop (shift u)) :
    BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, eventually_atTop] at h ⊢
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + 1, fun n hn => ?_⟩
  simp only [shift] at hC
  have r1 : n - 1 ≥ N := Nat.le_sub_one_of_lt hn
  have r2 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  simpa [r2] using hC (n - 1) r1

lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift] using! Finset.sum_nonneg' ha) (sub_nonneg.mpr hb)
  rw [summable_iff_bounded (mul_nonneg ha hb)]
  rw [summable_iff_bounded' l1] at h
  apply bounded_of_shift
  simpa only [summation_by_parts'', sub_eq_add_neg, neg_cumsum, ← mul_neg, neg_nabla]
    using hAb.add h

lemma exists_antitone_of_eventually {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n) :
    ∃ v : ℕ → ℝ, range v ⊆ range u ∧ Antitone v ∧ v =ᶠ[atTop] u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  let v (n : ℕ) := u (if n < N then N else n)
  refine ⟨v, ?_, ?_, ?_⟩
  · exact fun x ⟨n, hn⟩ => ⟨if n < N then N else n, hn⟩
  · refine antitone_nat_of_succ_le (fun n => ?_)
    by_cases h : n < N
    · by_cases h' : n + 1 < N <;> simp [v, h, h']
      have : n + 1 = N := by linarith
      simp [this]
    · have : ¬(n + 1 < N) := by linarith
      simp only [this, ↓reduceIte, h, ge_iff_le, v] ; apply hN ; linarith
  · have : ∀ᶠ n in atTop, ¬(n < N) := by simpa using ⟨N, fun b hb => by linarith⟩
    filter_upwards [this] with n hn ; simp [v, hn]

lemma summable_inv_mul_log_sq : Summable (fun n : ℕ => (n * (Real.log n) ^ 2)⁻¹) := by
  let u (n : ℕ) := (n * (Real.log n) ^ 2)⁻¹
  have l7 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    tendsto_atTop.mp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) 1
  have l8 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have l9 : ∀ᶠ n in atTop, u (n + 1) ≤ u n := by
    filter_upwards [l7, l8] with n l2 l8; dsimp [u]; gcongr <;> simp
  obtain ⟨v, l1, l2, l3⟩ := exists_antitone_of_eventually l9
  rw [summable_congr_ae l3.symm]
  have l4 (n : ℕ) : 0 ≤ v n := by obtain ⟨k, hk⟩ := l1 ⟨n, rfl⟩ ; rw [← hk] ; positivity
  apply (summable_condensed_iff_of_nonneg l4 (fun _ _ _ a ↦ l2 a)).mp
  suffices this : ∀ᶠ k : ℕ in atTop, 2 ^ k * v (2 ^ k) = ((k : ℝ) ^ 2)⁻¹ * ((Real.log 2) ^ 2)⁻¹ by
    exact (summable_congr_ae this).mpr <| (Real.summable_nat_pow_inv.mpr one_lt_two).mul_right _
  have l5 : ∀ᶠ k in atTop, v (2 ^ k) = u (2 ^ k) :=
    l3.comp_tendsto <| tendsto_pow_atTop_atTop_of_one_lt Nat.le.refl
  filter_upwards [l5, l8] with k l5 l8
  simp only [l5, mul_inv_rev, Nat.cast_pow, Nat.cast_ofNat, log_pow, u]
  field_simp

lemma tendsto_mul_add_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)

lemma isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]

lemma isLittleO_mul_add_sq (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left ; simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop _ <| tendsto_pow_atTop (by linarith)

lemma log_mul_add_isBigO_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ log x := tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b := tendsto_atTop.mp (tendsto_mul_add_atTop ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [(isLittleO_mul_add_sq a b).eventuallyLE, l5] with x r2 l5
    simpa [abs_eq_self.mpr (zero_le_one.trans l5)] using r2
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using
    Real.log_le_log (by linarith) l1

lemma isBigO_log_mul_add {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert! (log_mul_add_isBigO_log (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop (b := b) ha) using 1
  ext x
  simp only [Function.comp_apply]
  congr
  field_simp
  simp

lemma log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add (inv_pos.mpr hb) 0 using 1; simp only [add_zero]; field_simp

lemma Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g) := by
  rw [isLittleO_iff] at h ; specialize h (c := 2⁻¹) (by norm_num)
  rw [isBigO_iff'']
  refine ⟨2⁻¹, by norm_num, ?_⟩
  filter_upwards [h] with x h
  simp only [norm_eq_abs, Pi.add_apply] at h ⊢
  calc _ = |f x| - 2⁻¹ * |f x| := by ring
       _ ≤ |f x| - |g x| := by linarith
       _ ≤ |(|f x| - |g x|)| := le_abs_self _
       _ ≤ _ := by rw [← sub_neg_eq_add, ← abs_neg (g x)] ; exact abs_abs_sub_abs_le (f x) (-g x)

lemma Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) := by
  simpa [pow_two] using h.mul h

lemma log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply (log_isbigo_log_div hb).sq.trans ; simp_rw [add_comm a]
  refine IsBigO.add_isLittleO_right <| isLittleO_const_of_tendsto_atTop _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp <|
    tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

theorem log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x := by
  convert log_mul_add_isBigO_log (inv_pos.mpr hb) (a / b) using 3 ; ring

lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) : nabla Real.log x ≤ x⁻¹ := by
  have l1 : ContinuousOn Real.log (Icc x (x + 1)) := by
    apply continuousOn_log.mono ; intro t ⟨h1, _⟩ ; simp ; linarith
  have l2 t (ht : t ∈ Ioo x (x + 1)) : HasDerivAt Real.log t⁻¹ t :=
    Real.hasDerivAt_log (by linarith [ht.1])
  obtain ⟨t, ⟨ht1, _⟩, htx⟩ := exists_hasDerivAt_eq_slope Real.log (·⁻¹) (by linarith) l1 l2
  simp only [add_sub_cancel_left, div_one] at htx
  rw [nabla, ← htx, inv_le_inv₀ (by linarith) hx]
  exact ht1.le

lemma nabla_log_main : nabla Real.log =O[atTop] fun x ↦ 1 / x := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with x l1
  have l2 : log x ≤ log (x + 1) := log_le_log l1 (by linarith)
  simpa [nabla, abs_eq_self.mpr l1.le, abs_eq_self.mpr (sub_nonneg.mpr l2)] using
    log_add_one_sub_log_le l1

lemma nabla_log {b : ℝ} (hb : 0 < b) :
    nabla (fun x => Real.log (x / b)) =O[atTop] (fun x => 1 / x) := by
  refine EventuallyEq.trans_isBigO ?_ nabla_log_main
  filter_upwards [eventually_gt_atTop 0] with x l2
  rw [nabla, log_div (by linarith) (by linarith), log_div l2.ne.symm (by linarith), nabla] ; ring

lemma nnabla_mul_log_sq (a : ℝ) {b : ℝ} (hb : 0 < b) :
    nabla (fun x => x * (a + Real.log (x / b) ^ 2)) =O[atTop] (fun x => Real.log x ^ 2) := by

  have l1 : nabla (fun n => n * (a + Real.log (n / b) ^ 2)) = fun n =>
      a + Real.log ((n + 1) / b) ^ 2 +
        (n * (Real.log ((n + 1) / b) ^ 2 - Real.log (n / b) ^ 2)) := by
    ext n ; simp [nabla] ; ring
  have l2 := (isLittleO_const_of_tendsto_atTop a
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_log_atTop)).isBigO
  have l3 := (log_add_div_isBigO_log 1 hb).sq
  have l4 : (fun x => Real.log ((x + 1) / b) + Real.log (x / b)) =O[atTop] Real.log := by
    simpa using (log_add_div_isBigO_log _ hb).add (log_add_div_isBigO_log 0 hb)
  have e2 : (fun x : ℝ => x * (Real.log x * (1 / x))) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop 1] with x hx using by field_simp
  have l5 : (fun n ↦ n * (Real.log n * (1 / n))) =O[atTop] (fun n ↦ (Real.log n) ^ 2) :=
    e2.trans_isBigO
      (by simpa using! (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)

  simp_rw [l1, _root_.sq_sub_sq]
  exact ((l2.add l3).add (isBigO_refl (·) atTop |>.mul (l4.mul (nabla_log hb)) |>.trans l5))

lemma nnabla_bound_aux1 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_pow_atTop two_ne_zero).comp <| tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

lemma nnabla_bound_aux2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) :=
  (nnabla_bound_aux1 a hb).eventually (eventually_gt_atTop 0)

lemma Real.log_eventually_gt_atTop (a : ℝ) :
    ∀ᶠ x in atTop, a < Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)

/-- Should this be a gcongr lemma? -/
theorem norm_lt_norm_of_nonneg (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖x‖ ≤ ‖y‖ := by
  simp_rw [Real.norm_eq_abs]
  apply abs_le_abs hxy
  linarith

lemma nnabla_bound_aux {x : ℝ} (hx : 0 < x) :
    nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
    (fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2)) := by

  let d n : ℝ := n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2)
  change (fun x_1 ↦ nnabla (fun n ↦ 1 / d n) x_1) =O[atTop] _

  have l2 : ∀ᶠ n in atTop, 0 < d n := (nnabla_bound_aux2 ((2 * π) ^ 2) hx)
  have l3 : ∀ᶠ n in atTop, 0 < d (n + 1) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).eventually l2
  have l1 : ∀ᶠ n : ℝ in atTop,
      nnabla (fun n ↦ 1 / d n) n = (d (n + 1) - d n) * (d n)⁻¹ * (d (n + 1))⁻¹ := by
    filter_upwards [l2, l3] with n l2 l3
    rw [nnabla, one_div, one_div, inv_sub_inv l2.ne.symm l3.ne.symm, div_eq_mul_inv, mul_inv,
      mul_assoc]

  have l4 : (fun n => (d n)⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    apply IsBigO.inv_rev
    · refine (isBigO_refl _ _).mul <| (log_sq_isbigo_mul hx)
    · filter_upwards [Real.log_eventually_gt_atTop 0, eventually_gt_atTop 0] with x hx hx'
      rw [← not_imp_not]
      intro _
      positivity
  have l5 : (fun n => (d (n + 1))⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    refine IsBigO.trans ?_ l4
    rw [isBigO_iff]; use 1
    have e3 : ∀ᶠ n in atTop, d n ≤ d (n + 1) := by
      filter_upwards [eventually_ge_atTop x] with n hn
      have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
      have : 0 ≤ n := hx.le.trans hn
      simp only [d]
      gcongr <;> simp [Real.log_nonneg, *]
    filter_upwards [l2, l3, e3] with n e1 e2 e3
    simp_rw [one_mul]
    exact norm_lt_norm_of_nonneg _ _ (inv_nonneg.mpr e2.le) (inv_anti₀ e1 e3)

  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    simpa [d, nabla] using! (nnabla_mul_log_sq ((2 * π) ^ 2) hx)

  apply EventuallyEq.trans_isBigO l1

  apply ((l6.mul l4).mul l5).trans_eventuallyEq
  filter_upwards [eventually_ge_atTop 2, Real.log_eventually_gt_atTop 0] with n hn hn'
  field_simp

lemma nnabla_bound (C : ℝ) {x : ℝ} (hx : 0 < x) :
    nnabla (fun n => C / (1 + (Real.log (n / x) / (2 * π)) ^ 2) / n) =O[atTop]
    (fun n => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
  field_simp
  simp only [div_eq_mul_inv, mul_inv, nnabla_mul, one_mul]
  apply IsBigO.const_mul_left
  simpa [div_eq_mul_inv, mul_pow, mul_comm] using nnabla_bound_aux hx

def chebyWith (C : ℝ) (f : ℕ → ℂ) : Prop := ∀ n, cumsum (‖f ·‖) n ≤ C * n

def cheby (f : ℕ → ℂ) : Prop := ∃ C, chebyWith C f

lemma cheby.bigO (h : cheby f) : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ) := by
  have l1 : 0 ≤ cumsum (‖f ·‖) := cumsum_nonneg (fun _ => norm_nonneg _)
  obtain ⟨C, hC⟩ := h
  apply isBigO_of_le' (c := C) atTop
  intro n
  rw [Real.norm_eq_abs, abs_eq_self.mpr (l1 n)]
  simpa using hC n

lemma limiting_fourier_lim1_aux (hcheby : cheby f) (hx : 0 < x) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n ↦ ‖f n‖ / ↑n * (C / (1 + (1 / (2 * π) * Real.log (↑n / x)) ^ 2)) := by

  let a (n : ℕ) := (C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2) / ↑n)
  replace hcheby := hcheby.bigO

  have l1 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n : ℕ => (↑(n + 1) : ℝ)) :=
    hcheby.comp_tendsto <| tendsto_add_atTop_nat 1
  have l2 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n => (n : ℝ)) :=
    l1.trans
      (by simpa using (isBigO_refl _ _).add <| isBigO_iff.mpr ⟨1, by simpa using ⟨1, by tauto⟩⟩)
  have l5 : BoundedAtFilter atTop (fun n : ℕ => C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2)) := by
    simp only [BoundedAtFilter]
    field_simp
    apply isBigO_of_le' (c := C) ; intro n
    have : 0 ≤ 2 ^ 2 * π ^ 2 + Real.log (n / x) ^ 2 := by positivity
    simp only [norm_div, norm_mul, norm_eq_abs, abs_eq_self.mpr hC, norm_pow,
      abs_eq_self.mpr pi_nonneg, abs_eq_self.mpr this, Pi.one_apply, one_mem,
      CStarRing.norm_of_mem_unitary, mul_one, ge_iff_le, Nat.abs_ofNat]
    apply div_le_of_le_mul₀ this hC
    rw [mul_add, ← mul_assoc]
    apply le_add_of_le_of_nonneg le_rfl
    positivity
  have l3 : a =O[atTop] (fun n => 1 / (n : ℝ)) := by
    simpa [a] using! IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
  have l4 : nnabla a =O[atTop] (fun n : ℕ => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
    convert (nnabla_bound C hx).natCast ; simp [nnabla, a]

  simp_rw [div_mul_eq_mul_div, mul_div_assoc, one_mul]
  apply dirichlet_test'
  · intro n ; exact norm_nonneg _
  · intro n ; positivity
  · apply (l2.mul l3).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 1)
    intro x (hx : 1 ≤ x)
    have : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hx
    simp [this]
  · have : ∀ᶠ n : ℕ in atTop, x ≤ n := by simpa using eventually_ge_atTop ⌈x⌉₊
    filter_upwards [this] with n hn
    have e1 : 0 < (n : ℝ) := by linarith
    have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
    have e3 := Nat.le_succ n
    gcongr
    refine div_nonneg (Real.log_nonneg e2) (by norm_num [pi_nonneg])
  · apply summable_of_isBigO_nat summable_inv_mul_log_sq
    apply (l2.mul l4).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 2)
    intro x (hx : 2 ≤ x)
    have : (x : ℝ) ≠ 0 := by simp ; linarith
    have : Real.log x ≠ 0 := by
      have ll : 2 ≤ (x : ℝ) := by simp [hx]
      simp
      grind
    field_simp

theorem limiting_fourier_lim1 (hcheby : cheby f) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦
        ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  have : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine tendsto_tsum_of_dominated_convergence
    (limiting_fourier_lim1_aux hcheby hx C this) (fun n => ?_) ?_
  · apply Tendsto.mul_const
    by_cases h : n = 0 <;> simp only [term, h, ↓reduceIte, CharP.cast_eq_zero, div_zero,
      tendsto_const_nhds_iff]
    refine tendsto_const_nhds.div ?_ (by simp [h])
    simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
  · rw [eventually_nhdsWithin_iff]
    apply Eventually.of_forall
    intro σ' (hσ' : 1 < σ') n
    rw [norm_mul, ← nterm_eq_norm_term]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    by_cases h : n = 0 <;> simp only [nterm, h, ↓reduceIte, CharP.cast_eq_zero, div_zero, le_refl]
    have : 1 ≤ (n : ℝ) := by simpa using! Nat.pos_iff_ne_zero.mpr h
    refine div_le_div₀ (norm_nonneg _) le_rfl (by simpa [Nat.pos_iff_ne_zero]) ?_
    simpa using Real.rpow_le_rpow_of_exponent_le this hσ'.le

theorem limiting_fourier_lim2_aux (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
      (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div
    (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict

theorem limiting_fourier_lim2 (A : ℝ) (ψ : W21) (hx : 1 ≤ x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
        ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
      (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  apply Tendsto.mul
  · suffices h : Tendsto (fun σ' : ℝ ↦ ofReal (x ^ (1 - σ'))) (𝓝[>] 1) (𝓝 1) by
      simpa using h.const_mul ↑A
    suffices h : Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) from
      (continuous_ofReal.tendsto 1).comp h
    have : Tendsto (fun σ' : ℝ ↦ σ') (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl (zero_lt_one.trans_le hx).ne.symm)
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      (limiting_fourier_lim2_aux x C) ?_
    · apply Eventually.of_forall ; intro σ'
      apply Continuous.aestronglyMeasurable
      have := continuous_FourierIntegral ψ
      continuity
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsGT_of_mem ; simp
      · intro σ' ⟨h1, h2⟩
        rw [ae_restrict_iff' measurableSet_Ici]
        apply Eventually.of_forall
        intro t (ht : - Real.log x ≤ t)
        rw [norm_mul]
        have hdom_nonneg : 0 ≤ max |x| 1 := by
          exact (abs_nonneg x).trans (le_max_left _ _)
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) hdom_nonneg
        simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, norm_exp,
          neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im, sub_self, mul_zero,
          sub_zero]
        have : -Real.log x * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht (by linarith)
        have : -(t * (σ' - 1)) ≤ Real.log x * (σ' - 1) := by simpa using neg_le_neg this
        have := Real.exp_monotone this
        apply this.trans
        have l1 : σ' - 1 ≤ 1 := by linarith
        have : 0 ≤ Real.log x := Real.log_nonneg hx
        have := mul_le_mul_of_nonneg_left l1 this
        refine (Real.exp_monotone this).trans ?_
        have hxabs : |x| = x := abs_of_nonneg (zero_le_one.trans hx)
        calc
          Real.exp (Real.log x * 1) = |x| := by
            simpa [mul_one, hxabs] using (Real.exp_log (zero_lt_one.trans_le hx))
          _ ≤ max |x| 1 := le_max_left _ _
    · apply Eventually.of_forall
      intro x
      suffices h : Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by
        simpa using h.mul_const _
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices h : Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using h.tendsto 1
      continuity

theorem limiting_fourier_lim3 (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by

  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh

  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  have l3 : ContinuousOn (‖G ·‖) S := (hG.mono l2).norm
  have l4 : S.Nonempty := ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn l4 l3
  let MG := ‖G z‖
  let bound (a : ℝ) : ℝ := MG * ‖ψ a‖

  apply tendsto_integral_filter_of_dominated_convergence (bound := bound)
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp)) ; intro u hu
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous
    · apply Continuous.const_cpow (by fun_prop) ; simp ; linarith
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
    intro u hu
    apply Eventually.of_forall ; intro v
    by_cases h : v ∈ tsupport ψ
    · have r1 : u + v * I ∈ S := by simp [S, mem_reProdIm, hu.1, hu.2, h]
      have r2 := isMaxOn_iff.mp hmax _ r1
      have r4 : (x : ℂ) ≠ 0 := by simp ; linarith
      have r5 : arg x = 0 := by simp [arg_eq_zero_iff] ; linarith
      have r3 : ‖(x : ℂ) ^ (v * I)‖ = 1 := by simp [norm_cpow_of_ne_zero r4, r5]
      simp_rw [norm_mul, r3, mul_one]
      exact mul_le_mul_of_nonneg_right r2 (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp at this ; simp [this, bound]

  · suffices h : Continuous bound by exact h.integrable_of_hasCompactSupport ψ.h2.norm.mul_left
    have := ψ.h1.continuous ; fun_prop
  · apply Eventually.of_forall ; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) => by simp [hx.le])

lemma limiting_fourier (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by

  have l1 := limiting_fourier_lim1 hcheby ψ (by linarith)
  have l2 := limiting_fourier_lim2 A ψ hx
  have l3 := limiting_fourier_lim3 hG ψ hx
  apply tendsto_nhds_unique_of_eventuallyEq (l1.sub l2) l3
  simpa [eventuallyEq_nhdsWithin_iff] using! Eventually.of_forall (limiting_fourier_aux hG' hf ψ hx)




lemma limiting_cor_aux {f : ℝ → ℂ} : Tendsto (fun x : ℝ ↦ ∫ t, f t * x ^ (t * I)) atTop (𝓝 0) := by

  have l1 : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, x ^ (t * I) = exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx' t
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx'] ; ring_nf

  have l2 : ∀ᶠ x : ℝ in atTop, ∫ t, f t * x ^ (t * I) = ∫ t, f t * exp (log x * t * I) := by
    filter_upwards [l1] with x hx
    refine integral_congr_ae (Eventually.of_forall (fun x => by simp [hx]))

  simp_rw [tendsto_congr' l2]
  convert_to Tendsto (fun x => 𝓕 f (-Real.log x / (2 * π))) atTop (𝓝 0)
  · ext x
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1; ext t
    rw [smul_eq_mul, mul_comm (f t)]
    congr 2
    push_cast
    field_simp
  refine (Real.zero_at_infty_fourier f).comp <| Tendsto.mono_right ?_ _root_.atBot_le_cocompact
  exact (tendsto_neg_atBot_iff.mpr tendsto_log_atTop).atBot_mul_const (inv_pos.mpr two_pi_pos)

lemma limiting_cor (ψ : CS 2 ℂ) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  apply limiting_cor_aux.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx using
    limiting_fourier hcheby hG hG' hf ψ hx |>.symm





lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by

  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩



noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩

noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)

lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity

noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹

noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2

lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity

lemma hh_deriv (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 := mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    convert! l4.pow 2 using 1 ; ring
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    convert! (hasDerivAt_id' t).mul l2 using 1; field_simp; ring
  convert! l1.inv e1 using 1; simp only [hh', pp, hh]; field_simp; ring

lemma hh_continuous (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv a ht.ne.symm).continuousAt.continuousWithinAt

lemma hh'_nonpos {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity

lemma hh_antitone {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1
    (fun x _ => hh'_nonpos ha)

noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹

lemma gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  simp only [gg, hh]
  field_simp

lemma gg_le_one (i : ℕ) : gg x i ≤ 1 := by
  by_cases hi : i = 0 <;> simp only [gg, hi, CharP.cast_eq_zero, div_zero, one_div, mul_inv_rev,
    zero_div, Real.log_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, inv_one, mul_one, zero_le_one]
  have l1 : 1 ≤ (i : ℝ) := by simp ; omega
  have l2 : 1 ≤ 1 + (π⁻¹ * 2⁻¹ * Real.log (↑i / x)) ^ 2 := by
    simp only [le_add_iff_nonneg_right] ; positivity
  rw [← mul_inv] ; apply inv_le_one_of_one_le₀ ; simpa using mul_le_mul l1 l2 zero_le_one (by simp)

lemma one_div_two_pi_mem_Ioo : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  constructor
  · trans 0
    · linarith
    · positivity
  · rw [div_lt_iff₀ (by positivity)]
    convert_to! 1 * 1 < 2 * π
    · simp
    · simp
    apply mul_lt_mul one_lt_two ?_ zero_lt_one zero_le_two
    trans 2
    · exact one_le_two
    · exact two_le_pi

lemma cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by

  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa using! hf' (n + 1)) (Finset.sum_nonneg' hf) ?_
    simp only [sub_nonneg] ; apply hg' ; simp
  have l2 (x : ℕ) : C * (↑(x + 1) + 1) - C * (↑x + 1) = C := by simp ; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg' hf

  convert_to ∑ i ∈ Finset.range n, (g i) • (f i) ≤ _
  · simp [mul_comm]
  rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul, neg_sub, smul_eq_mul]
  apply _root_.add_le_add
  · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
  · apply Finset.sum_le_sum (fun n _ => l1 n) |>.trans
    convert_to! ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) ≤ _
    · congr ; ext i ; simp ; ring
    rw [Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]
    apply le_of_eq ; ring_nf

lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring

lemma cancel_aux' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤
        C * n * g (n - 1)
      + C * cumsum g (n - 1 - 1 + 1)
      - C * (↑(n - 1 - 1) + 1) * g (n - 1)
      := by
  have := cancel_aux hf hg hf' hg' n
  simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ] at this
  convert this using 1 ; unfold cumsum ; ring

lemma cancel_main' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hf0 : f 0 = 0) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  match n with
  | 0 => simp [cumsum]
  | 1 => specialize hg 0 ; specialize hf' 1 ; simp only [cumsum, Finset.range_one,
    Finset.sum_singleton, hf0, Nat.cast_one, mul_one, Pi.zero_apply, Pi.mul_apply, zero_mul,
    ge_iff_le] at hf' hg ⊢ ; positivity
  | n + 2 => convert! cancel_aux' hf hg hf' hg' (n + 2) using 1 ; simp [cumsum_succ] ; ring

theorem sum_le_integral {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ + n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by

  cases n with simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, add_zero,
      lt_self_iff_false, not_false_eq_true,
    Ioc_eq_empty, Finset.range_zero, Nat.cast_add, Nat.cast_one, Finset.sum_empty,
    intervalIntegral.integral_same, le_refl] at hf ⊢
  | succ n =>
  have : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
    ext i ; by_cases hi : i = 0 <;> simp [hi] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_true, not_false_eq_true,
    Finset.sum_insert, CharP.cast_eq_zero, zero_add, ge_iff_le]

  have l4 : IntervalIntegrable f volume x₀ (x₀ + 1) := by
    apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc le_rfl
    simp
  have l5 x (hx : x ∈ Ioc x₀ (x₀ + 1)) : (fun x ↦ f (x₀ + 1)) x ≤ f x := by
    rcases hx with ⟨hx1, hx2⟩
    refine hf ⟨hx1, by linarith⟩ ⟨by linarith, by linarith⟩ hx2
  have l6 : ∫ x in x₀..x₀ + 1, f (x₀ + 1) = f (x₀ + 1) := by simp

  have l1 : f (x₀ + 1) ≤ ∫ x in x₀..x₀ + 1, f x := by
    rw [← l6] ; apply intervalIntegral.integral_mono_ae_restrict (by linarith) (by simp) l4
    apply eventually_of_mem _ l5
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by simp [← sdiff_eq_compl_inter]
    rw [mem_ae_iff, Measure.restrict_apply measurableSet_Ioc.compl, this]
    simp

  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith

  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)

  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  convert! _root_.add_le_add l1 l3

  have := @intervalIntegral.integral_comp_mul_add ℝ _ _ 1 (n + 1) 1 f one_ne_zero x₀
  rw [intervalIntegral.integral_add_adjacent_intervals]
  · exact l4
  · apply IntegrableOn.intervalIntegrable
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, Nat.cast_nonneg, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc
    · linarith
    · simp

lemma hh_integrable_aux (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by

  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp only [hh]

  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹

  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have := @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _  (l3 (x / c) (by positivity)) (l4 x)
    convert! this using 1 ; field_simp
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    convert! (l1 x hx).const_mul (a * c / b) using 1
    simp only [g']
    field_simp
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]

  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id

  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp only [mem_Ioi] at hx1 ⊢ ; positivity
    · simp only [dist_zero_right, norm_eq_abs, norm_div, abs_eq_self.mpr hc.le] at hx2 ⊢
      rwa [div_lt_iff₀ hc, mul_comm]

  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    rw [Metric.tendsto_nhdsWithin_nhds] at k2
    peel k2 with ε hε δ hδ x h
    intro (hx : 0 ≤ x)
    have := le_iff_lt_or_eq.mp hx
    cases this with
    | inl hx => exact h hx
    | inr hx => simp [g₀, hx.symm, hε]

  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x) ; simp only [mul_inv_rev, inv_div, g'] ; positivity

  constructor
  · convert_to IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert this using 1 ; field_simp ; ring

lemma hh_integrable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  hh_integrable_aux ha hb hc |>.1

lemma hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π :=
  hh_integrable_aux ha hb hc |>.2

lemma hh_integral' : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  have := hh_integral (a := 1) (b := 1 / (2 * π)) (c := 1)
    (by positivity) (by positivity) (by positivity)
  convert this using 1 <;> simp ; ring

lemma bound_sum_log {C : ℝ} (hf0 : f 0 = 0) (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let ggg (i : ℕ) : ℝ := if i = 0 then 1 else gg x i

  have l0 : x ≠ 0 := by linarith
  have l1 i : 0 ≤ ggg i := by by_cases hi : i = 0 <;> simp only [gg, one_div, mul_inv_rev, hi,
    ↓reduceIte, zero_le_one, ggg] ; positivity
  have l2 : Antitone ggg := by
    intro i j hij ; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hj, ↓reduceIte, hi,
      le_refl, ggg]
    · exact gg_le_one _
    · omega
    · simp only [gg_of_hh l0]
      gcongr
      apply hh_antitone one_div_two_pi_mem_Ioo
      · simp only [mem_Ioi] ; positivity
      · simp only [mem_Ioi] ; positivity
      · gcongr
  have l3 : 0 ≤ C := by simpa [cumsum, hf0] using hf 1

  have l4 : 0 ≤ ∫ (t : ℝ) in Ioi 0, hh (π⁻¹ * 2⁻¹) t :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => hh_nonneg _ (LT.lt.le hx))

  have l5 {n : ℕ} : AntitoneOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioc 0 n) := by
    intro u ⟨hu1, _⟩ v ⟨hv1, _⟩ huv
    simp only
    apply mul_le_mul le_rfl ?_ (hh_nonneg _ (by positivity)) (by positivity)
    apply hh_antitone one_div_two_pi_mem_Ioo (by simp only [mem_Ioi] ; positivity)
      (by simp only [mem_Ioi] ; positivity)
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr huv

  have l6 {n : ℕ} : IntegrableOn (fun t ↦ x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (Icc 0 n) volume := by
    apply IntegrableOn.mono_set
      (hh_integrable (by positivity) (by positivity) (by positivity)) Icc_subset_Ici_self

  apply Real.tsum_le_of_sum_range_le (fun n => by positivity) ; intro n
  convert_to! ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [gg, hi, ↓reduceIte, ggg]
      field_simp

  apply cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n |>.trans
  gcongr ; simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]

  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  convert_to! ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) ≤ _
  · apply Finset.sum_congr rfl (fun i hi => ?_)
    simp at hi
    have : i ≠ 0 := by omega
    simp [this]
  simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
  have := @sum_le_integral 0 (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (n - 1)
    (by simpa using l5) (by simpa using l6)
  simp only [zero_add] at this
  apply this.trans
  rw [@intervalIntegral.integral_comp_div ℝ _ _ 0 ↑(n - 1) x (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t)) l0]
  simp only [zero_div, intervalIntegral.integral_const_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ l0, one_mul]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [this, ↓reduceIte, uIoc_of_le, smul_eq_mul, one_mul, ge_iff_le]
  apply integral_mono_measure
  · apply Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · apply eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
    intro x (hx : 0 < x)
    apply hh_nonneg _ hx.le
  · have := (@hh_integrable 1 (1 / (2 * π)) 1 (by positivity) (by positivity) (by positivity))
    simpa using! this.mono_set Ioi_subset_Ici_self

lemma bound_sum_log0 {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let f0 i := if i = 0 then 0 else f i
  have l1 : chebyWith C f0 := by
    intro n ; refine Finset.sum_le_sum (fun i _ => ?_) |>.trans (hf n)
    by_cases hi : i = 0 <;> simp [hi, f0]
  have l2 i : ‖f i‖ / i = ‖f0 i‖ / i := by by_cases hi : i = 0 <;> simp [hi, f0]
  simp_rw [l2] ; apply bound_sum_log rfl l1 hx

lemma bound_sum_log' {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + 2 * π ^ 2) := by
  simpa only [hh_integral'] using bound_sum_log0 hf hx

variable (f x) in
lemma summable_fourier_aux (ψ : W21) (i : ℕ) :
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
  convert! mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x)))
    (norm_nonneg (f i / i)) using 1
  · simp
  · change _ = _ * (W21.norm ψ * _)
    simp only [W21.norm, mul_inv_rev, one_div, Complex.norm_div, RCLike.norm_natCast]
    ring

lemma summable_fourier (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) l6
    (by simpa using l5.const_smul (W21.norm ψ))

lemma bound_I1 (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
    W21.norm ψ • ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ := by

  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  have l1 : Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
    exact summable_fourier x hx ψ hcheby
  apply (norm_tsum_le_tsum_norm l1).trans
  simpa only [← Summable.tsum_const_smul _ l5] using!
    Summable.tsum_mono l1 (by simpa using l5.const_smul (W21.norm ψ)) l6

lemma bound_I1' {C : ℝ} (x : ℝ) (hx : 1 ≤ x) (ψ : W21) (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
      W21.norm ψ * C * (1 + 2 * π ^ 2) := by

  apply bound_I1 x (by linarith) ψ ⟨_, hcheby⟩ |>.trans
  rw [smul_eq_mul, mul_assoc]
  apply mul_le_mul le_rfl (bound_sum_log' hcheby hx) ?_ W21.norm_nonneg
  apply tsum_nonneg (fun i => by positivity)

lemma bound_I2 (x : ℝ) (ψ : W21) :
    ‖∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤ W21.norm ψ * (2 * π ^ 2) := by

  have key a : ‖𝓕 (ψ : ℝ → ℂ) (a / (2 * π))‖ ≤ W21.norm ψ * (1 + (a / (2 * π)) ^ 2)⁻¹ :=
    decay_bounds_key ψ _
  have twopi : 0 ≤ 2 * π := by simp [pi_nonneg]
  have l3 : Integrable (fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div (by norm_num [pi_ne_zero])
  have l2 : IntegrableOn (fun i ↦ W21.norm ψ * (1 + (i / (2 * π)) ^ 2)⁻¹) (Ici (-Real.log x)) := by
    exact (l3.const_mul _).integrableOn
  have l1 : IntegrableOn (fun i ↦ ‖𝓕 (ψ : ℝ → ℂ) (i / (2 * π))‖) (Ici (-Real.log x)) := by
    refine ((l3.const_mul (W21.norm ψ)).mono' ?_ ?_).integrableOn
    · apply Continuous.aestronglyMeasurable ; have := continuous_FourierIntegral ψ ; fun_prop
    · simp only [norm_norm, key] ; simp
  have l5 : 0 ≤ᵐ[volume] fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹ := by
    apply Eventually.of_forall ; intro x ; positivity
  refine (norm_integral_le_integral_norm _).trans <| (setIntegral_mono l1 l2 key).trans ?_
  rw [integral_const_mul] ; gcongr
  · apply W21.norm_nonneg
  refine (setIntegral_le_integral l3 l5).trans ?_
  rw [Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) (2 * π)]
  simp [abs_eq_self.mpr twopi] ; ring_nf ; rfl

lemma bound_main {C : ℝ} (A : ℂ) (x : ℝ) (hx : 1 ≤ x) (ψ : W21)
    (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤
      W21.norm ψ * (C * (1 + 2 * π ^ 2) + ‖A‖ * (2 * π ^ 2)) := by

  have l1 := bound_I1' x hx ψ hcheby
  have l2 := mul_le_mul (le_refl ‖A‖) (bound_I2 x ψ) (by positivity) (by positivity)
  apply norm_sub_le _ _ |>.trans ; rw [norm_mul]
  convert _root_.add_le_add l1 l2 using 1 ; ring


lemma limiting_cor_W21 (ψ : W21) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  -- Shorter notation for clarity
  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)

  -- Build the truncation
  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'

  -- Choose the truncation radius
  obtain ⟨C, hcheby⟩ := hcheby
  have hC : 0 ≤ C := by
    have : ‖f 0‖ ≤ C := by simpa [cumsum] using hcheby 1
    have : 0 ≤ ‖f 0‖ := by positivity
    linarith
  have key2 : Tendsto (fun R ↦ W21.norm (ψ - Ψ R)) atTop (𝓝 0) := W21_approximation ψ g
  simp_rw [Metric.tendsto_nhds] at key key2 ⊢ ; intro ε hε
  let M := C * (1 + 2 * π ^ 2) + ‖(A : ℂ)‖ * (2 * π ^ 2)
  obtain ⟨R, hRψ⟩ := (key2 ((ε / 2) / (1 + M)) (by positivity)).exists
  simp only [dist_zero_right, Real.norm_eq_abs, abs_eq_self.mpr W21.norm_nonneg] at hRψ key

  -- Apply the compact support case
  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key

  -- Control the tail term
  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    have : ‖S x _‖ ≤ _ * M := @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply this.trans_lt
    apply (mul_le_mul (d := 1 + M) le_rfl (by simp) (by positivity) W21.norm_nonneg).trans_lt
    have : 0 < 1 + M := by positivity
    convert! (mul_lt_mul_iff_left₀ this).mpr hRψ using 1 ; field_simp

  -- Conclude the proof
  have S1_sub_1 x : 𝓕 (⇑ψ - ⇑(Ψ R)) x = 𝓕 (ψ : ℝ → ℂ) x - 𝓕 ⇑(Ψ R) x := by
    have l1 : AEStronglyMeasurable (fun x_1 : ℝ ↦ cexp (-(2 * ↑π * (↑x_1 * ↑x) * I))) volume := by
      refine (Continuous.mul ?_ continuous_const).neg.cexp.aestronglyMeasurable
      apply continuous_const.mul <| contDiff_ofReal.continuous.mul continuous_const
    simp only [Real.fourier_eq', neg_mul, RCLike.inner_apply', conj_trivial, ofReal_neg,
      ofReal_mul, ofReal_ofNat, Pi.sub_apply, smul_eq_mul, mul_sub]
    apply integral_sub
    · apply ψ.hf.bdd_mul (c := 1) l1 ; simp [Complex.norm_exp]
    · apply (Ψ R : W21) |>.hf |>.bdd_mul (c := 1) l1
      simp [Complex.norm_exp]

  have S1_sub : S1 x (ψ - Ψ R) = S1 x ψ - S1 x (Ψ R) := by
    simp only [one_div, mul_inv_rev, S1_sub_1, mul_sub, S1] ; apply Summable.tsum_sub
    · have := summable_fourier x (by positivity) ψ ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this
    · have := summable_fourier x (by positivity) (Ψ R) ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using! this

  have S2_sub : S2 x (ψ - Ψ R) = S2 x ψ - S2 x (Ψ R) := by
    simp only [S1_sub_1, S2] ; rw [integral_sub]
    · ring
    · exact ψ.integrable_fourier (by positivity) |>.restrict
    · exact (Ψ R : W21).integrable_fourier (by positivity) |>.restrict

  have S_sub : S x (ψ - Ψ R) = S x ψ - S x (Ψ R) := by simp [S, S1_sub, S2_sub] ; ring
  simpa [S_sub, Ψ] using norm_add_le _ _ |>.trans_lt (_root_.add_lt_add key3 key)

lemma limiting_cor_schwartz (ψ : 𝓢(ℝ, ℂ)) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) :=
  limiting_cor_W21 ψ hf hcheby hG hG'





-- just the surjectivity is stated here, as this is all that is needed for the current
-- application, but perhaps one should state and prove bijectivity instead

lemma fourier_surjection_on_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = f := by
  refine ⟨𝓕⁻ f, ?_⟩
  exact FourierTransform.fourier_fourierInv_eq f




noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2

@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl

lemma comp_exp_support0 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in 𝓝 0, Ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl 0 <| mem_Ioi.mp (hplus h))

lemma comp_exp_support1 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 :=
  Real.tendsto_exp_atBot <| comp_exp_support0 hplus

lemma comp_exp_support2 {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp
  exact Real.tendsto_exp_atTop hsupp.2

theorem comp_exp_support {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) : HasCompactSupport (Ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  exact ⟨comp_exp_support1 hplus, comp_exp_support2 hsupp⟩

lemma wiener_ikehara_smooth_aux (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by

  have l1 : ContinuousOn rexp (Ici (-Real.log x)) := by fun_prop
  have l2 : Tendsto rexp atTop atTop := Real.tendsto_exp_atTop
  have l3 t (_ : t ∈ Ioi (-log x)) : HasDerivWithinAt rexp (rexp t) (Ioi t) t :=
    (Real.hasDerivAt_exp t).hasDerivWithinAt
  have l4 : ContinuousOn Ψ (rexp '' Ioi (-Real.log x)) := by fun_prop
  have l5 : IntegrableOn Ψ (rexp '' Ici (-Real.log x)) volume :=
    (l0.integrable_of_hasCompactSupport hsupp).integrableOn
  have l6 : IntegrableOn (fun x ↦ rexp x • (Ψ ∘ rexp) x) (Ici (-Real.log x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_).integrableOn
    change HasCompactSupport (rexp • (Ψ ∘ rexp))
    exact (comp_exp_support hsupp hplus).smul_left
  have := MeasureTheory.integral_deriv_smul_comp_Ioi l1 l2 l3 l4 l5 l6
  simpa [Real.exp_neg, Real.exp_log hx] using this

theorem wiener_ikehara_smooth_sub (h1 : Integrable Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq ; filter_upwards [eventually_gt_atTop ε⁻¹] with x hxε

  have l1 : Integrable (indicator (Ioi x⁻¹) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  have l2 : Integrable (indicator (Ioi 0) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi

  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub, ← integral_sub l1 l2]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  apply MeasureTheory.integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro t
  simp only [Pi.zero_apply]

  have hε' : 0 < ε⁻¹ := by positivity
  have hx : 0 < x := by linarith
  have hx' : 0 < x⁻¹ := by positivity
  have hεx : x⁻¹ < ε := (inv_lt_comm₀ hε hx).mp hxε

  have l3 : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹ := by
    ext t ; simp only [mem_Ioi, mem_union, mem_Ioc] ; constructor <;> intro h
    · simp [h, le_or_gt]
    · cases h with
      | inl h => exact h.1
      | inr h => exact hx'.trans h
  have l4 : Disjoint (Ioc 0 x⁻¹) (Ioi x⁻¹) := by simp
  have l5 := Set.indicator_union_of_disjoint l4 Ψ
  rw [l3, l5]
  simp only
  rw [add_comm, sub_add_cancel_left]
  by_cases ht : t ∈ Ioc 0 x⁻¹
  · simp only [ht, indicator_of_mem, neg_eq_zero]
    apply hh ; simp only [mem_Ioc, dist_zero_right, norm_eq_abs] at ht ⊢
    apply hεx.trans_le'
    rw [abs_le] ; constructor <;> linarith
  simp [ht]



lemma wiener_ikehara_smooth (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x - A * ∫ y in Set.Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  let h (x : ℝ) : ℂ := rexp (2 * π * x) * Ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    simpa using! (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h1 h2)

  have l1 {y} (hy : 0 < y) : y * Ψ y = 𝓕 g (1 / (2 * π) * Real.log y) := by
    simp only [one_div, mul_inv_rev, hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat,
      toSchwartz_apply, ofReal_inv, h]
    field_simp
    norm_cast
    rw [Real.exp_log hy]

  have key := limiting_cor_schwartz g hf hcheby hG hG'

  have l2 : ∀ᶠ x in atTop, ∑' (n : ℕ), f n / ↑n * 𝓕 g (1 / (2 * π) * Real.log (↑n / x)) =
      ∑' (n : ℕ), f n * Ψ (↑n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr ; ext n
    by_cases hn : n = 0
    · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    simp only [ofReal_div, ofReal_natCast]
    field_simp

  have l3 : ∀ᶠ x in atTop, ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 g (u / (2 * π)) =
      ↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr 1
    simp only [hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat, toSchwartz_apply,
      ofReal_div, h]
    norm_cast ; field_simp; norm_cast
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx

  have l4 : Tendsto (fun x => (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
    exact wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus

  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4



lemma wiener_ikehara_smooth' (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) :=
  tendsto_sub_nhds_zero_iff.mp <| wiener_ikehara_smooth hf hcheby hG hG' hsmooth hsupp hplus

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

lemma wiener_ikehara_smooth_real {f : ℕ → ℝ} {Ψ : ℝ → ℝ}
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) := by

  let Ψ' := ofReal ∘ Ψ
  have l1 : ContDiff ℝ ∞ Ψ' := contDiff_ofReal.comp hsmooth
  have l2 : HasCompactSupport Ψ' := hsupp.comp_left rfl
  have l3 : closure (Function.support Ψ') ⊆ Ioi 0 := by rwa [Function.support_comp_eq] ; simp
  have key := (continuous_re.tendsto _).comp
    (@wiener_ikehara_smooth' A Ψ G f hf hcheby hG hG' l1 l2 l3)
  simp at key ; norm_cast at key

lemma interval_approx_inf (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        ψ ≤ indicator (Ico a b) 1 ∧ b - a - ε ≤ ∫ y in Ioi 0, ψ y := by

  have l1 : Iio ((b - a) / 3) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds <| by
    rw [← sub_pos] at hab
    positivity
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < (b - a) / 3)
  have l2 : a < a + ε / 2 := by simp [hε]
  have l3 : b - ε / 2 < b := by simp [hε]
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · simp [h5, hab.ne, Icc_subset_Ioi_iff hab.le, ha]
  · exact h4.trans <| indicator_le_indicator_of_subset Ioo_subset_Ico_self (by simp)
  · have l4 : 0 ≤ b - a - ε := by linarith
    have l5 : Icc (a + ε / 2) (b - ε / 2) ⊆ Ioi 0 := by
      intro t ht
      simp only [mem_Icc, mem_Ioi] at ht ⊢
      exact ha.trans <| l2.trans_le <| ht.1
    have l6 : Icc (a + ε / 2) (b - ε / 2) ∩ Ioi 0 = Icc (a + ε / 2) (b - ε / 2) :=
      inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Icc (a + ε / 2) (b - ε / 2)) 1 y = b - a - ε := by
      simp only [measurableSet_Icc, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Icc]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7] ; apply setIntegral_mono ?_ l8 h3
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma interval_approx_sup (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by

  have l1 : Iio (a / 2) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < a / 2)
  have l2 : a - ε / 2 < a := by linarith
  have l3 : b < b + ε / 2 := by linarith
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · have l4 : a - ε / 2 < b + ε / 2 := by linarith
    have l5 : ε / 2 < a := by linarith
    simp [h5, l4.ne, Icc_subset_Ioi_iff l4.le, l5]
  · apply le_trans ?_ h3
    apply indicator_le_indicator_of_subset Ico_subset_Icc_self (by simp)
  · have l4 : 0 ≤ b - a + ε := by linarith
    have l5 : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi 0 := by intro t ht ; simp at ht ⊢ ; linarith
    have l6 : Ioo (a - ε / 2) (b + ε / 2) ∩ Ioi 0 = Ioo (a - ε / 2) (b + ε / 2) := inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Ioo (a - ε / 2) (b + ε / 2)) 1 y = b - a + ε := by
      simp only [measurableSet_Ioo, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Ioo]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume := (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]
    refine setIntegral_mono l8 ?_ h4
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma WI_summable {f : ℕ → ℝ} {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable (fun n => f n * g (n / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold Function.HasFiniteSupport
  simp only [Function.support_mul] ; apply Finite.inter_of_right ; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi => by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩

lemma WI_sum_le {f : ℕ → ℝ} {g₁ g₂ : ℝ → ℝ} (hf : 0 ≤ f) (hg : g₁ ≤ g₂) (hx : 0 < x)
    (hg₁ : HasCompactSupport g₁) (hg₂ : HasCompactSupport g₂) :
    (∑' n, f n * g₁ (n / x)) / x ≤ (∑' n, f n * g₂ (n / x)) / x := by
  apply div_le_div_of_nonneg_right ?_ hx.le
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hg _) (hf _))
    (WI_summable hg₁ hx) (WI_summable hg₂ hx)

lemma WI_sum_Iab_le {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) (hxb : 2 / b < x) :
    (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  have hb' : 0 < 2 / b := by positivity
  have hx : 0 < x := by linarith
  have hxb' : 2 < x * b := (div_lt_iff₀ hb).mp hxb
  have l1 (i : ℕ) (hi : i ∉ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) = 0 := by
    simp_all [le_div_iff₀ hx]
  have l2 (i : ℕ) (_ : i ∈ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) ≤ |f i| := by
    rw [abs_eq_self.mpr (hpos _)]
    convert_to _ ≤ f i * 1
    · ring
    apply mul_le_mul_of_nonneg_left ?_ (hpos _)
    by_cases hi : (i / x) ∈ (Ico a b) <;> simp [hi]
  rw [tsum_eq_sum l1, div_le_iff₀ hx, mul_assoc, mul_assoc]
  apply Finset.sum_le_sum l2 |>.trans
  have := hcheby ⌈b * x⌉₊ ; simp only [norm_real, norm_eq_abs] at this ; apply this.trans
  have : 0 ≤ C := by have := hcheby 1 ; simp only [cumsum, Finset.range_one, norm_real,
    Finset.sum_singleton, Nat.cast_one, mul_one] at this ; exact (abs_nonneg _).trans this
  refine mul_le_mul_of_nonneg_left ?_ this
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  linarith

lemma WI_sum_Iab_le' {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  filter_upwards [eventually_gt_atTop (2 / b)] with x hx using WI_sum_Iab_le hpos hcheby hb hx

lemma le_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b := by
  apply le_of_forall_gt ; intro d hd
  have key : ∀ᶠ c in 𝓝[>] b, c < d := by
    apply eventually_of_mem (U := Iio d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Iio d, isOpen_Iio, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma ge_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[<] b, c ≤ a) : b ≤ a := by
  apply le_of_forall_lt ; intro d hd
  have key : ∀ᶠ c in 𝓝[<] b, c > d := by
    apply eventually_of_mem (U := Ioi d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Ioi d, isOpen_Ioi, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma WI_tendsto_aux (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => c / A - (b - a)) (𝓝[>] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [lt_div_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, Real.norm_eq_abs] at hx2 ⊢
    have : |x / A - (b - a)| = |x - A * (b - a)| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA]

lemma WI_tendsto_aux' (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => (b - a) - c / A) (𝓝[<] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [div_lt_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, norm_eq_abs] at hx2 ⊢
    have : |(b - a) - x / A| = |A * (b - a) - x| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA, ← neg_sub, abs_neg]

theorem residue_nonneg {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm (fun n ↦ ↑(f n)) σ')) (hcheby : cheby fun n ↦ ↑(f n))
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (hG' : EqOn G (fun s ↦ LSeries (fun n ↦ ↑(f n)) s - ↑A / (s - 1)) {s | 1 < s.re}) : 0 ≤ A := by
  let S (g : ℝ → ℝ) (x : ℝ) := (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact div_nonneg (tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))) hx
  obtain ⟨ε, ψ, h1, h2, h3, h4, -⟩ := (interval_approx_sup zero_lt_one one_lt_two).exists
  have key := @wiener_ikehara_smooth_real A G f ψ hf hcheby hG hG' h1 h2 h3
  have l2 : 0 ≤ ψ := by apply le_trans _ h4 ; apply indicator_nonneg ; simp
  have l1 : ∀ᶠ x in atTop, 0 ≤ S ψ x := hSnonneg l2
  have l3 : 0 ≤ A * ∫ (y : ℝ) in Ioi 0, ψ y := ge_of_tendsto key l1
  have l4 : 0 < ∫ (y : ℝ) in Ioi 0, ψ y := by
    have r1 : 0 ≤ᵐ[Measure.restrict volume (Ioi 0)] ψ := Eventually.of_forall l2
    have r2 : IntegrableOn (fun y ↦ ψ y) (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    have r3 : Ico 1 2 ⊆ Function.support ψ := by intro x hx ; have := h4 x ; simp [hx] at this ⊢ ; linarith
    have r4 : Ico 1 2 ⊆ Function.support ψ ∩ Ioi 0 := by
      simp only [subset_inter_iff, r3, true_and] ; apply Ico_subset_Icc_self.trans ; rw [Icc_subset_Ioi_iff] <;> linarith
    have r5 : 1 ≤ volume ((Function.support fun y ↦ ψ y) ∩ Ioi 0) := by convert! volume.mono r4 ; norm_num
    simpa [setIntegral_pos_iff_support_of_nonneg_ae r1 r2] using! zero_lt_one.trans_le r5
  have := div_nonneg l3 l4.le ; field_simp at this ; exact this



lemma WienerIkeharaInterval {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * (indicator (Ico a b) 1 (n / x))) / x) atTop (nhds (A * (b - a))) := by

  -- Take care of the trivial case `a = b`
  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab ; clear hab

  -- Notation to make the proof more readable
  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine div_nonneg ?_ hx
    refine tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))
  have hA : 0 ≤ A := residue_nonneg hpos hf hcheby hG hG'

  -- A few facts about the indicator function of `Icc a b`
  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) := by
    obtain ⟨C, hC⟩ := hcheby ; exact ⟨C * 2 * b, WI_sum_Iab_le' hpos hC (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le

  -- Bound from above by a smooth function
  have sup_le : limsup (S Iab) atTop ≤ A * (b - a) := by
    have l_sup : ∀ᶠ ε in 𝓝[>] 0, limsup (S Iab) atTop ≤ A * (b - a + ε) := by
      filter_upwards [interval_approx_sup ha hb] with ε ⟨ψ, h1, h2, h3, h4, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l6 : S Iab ≤ᶠ[atTop] S ψ := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h4 hx hIab h2
      have l5 : IsBoundedUnder (· ≤ ·) atTop (S ψ) := l1.isBoundedUnder_le
      have l3 : limsup (S Iab) atTop ≤ limsup (S ψ) atTop := limsup_le_limsup l6 Iab1 l5
      apply l3.trans ; rw [l1.limsup_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_sup
    apply le_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux a b key l_sup] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Bound from below by a smooth function
  have le_inf : A * (b - a) ≤ liminf (S Iab) atTop := by
    have l_inf : ∀ᶠ ε in 𝓝[>] 0, A * (b - a - ε) ≤ liminf (S Iab) atTop := by
      filter_upwards [interval_approx_inf ha hb] with ε ⟨ψ, h1, h2, h3, h5, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l2 : S ψ ≤ᶠ[atTop] S Iab := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h5 hx h2 hIab
      have l4 : IsBoundedUnder (· ≥ ·) atTop (S ψ) := l1.isBoundedUnder_ge
      have l3 : liminf (S ψ) atTop ≤ liminf (S Iab) atTop := liminf_le_liminf l2 l4 Iab0
      apply le_trans ?_ l3 ; rw [l1.liminf_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_inf
    apply ge_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux' a b key l_inf] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Combine the two bounds
  have : liminf (S Iab) atTop ≤ limsup (S Iab) atTop := liminf_le_limsup Iab2 Iab3
  refine tendsto_of_liminf_eq_limsup ?_ ?_ Iab2 Iab3 <;> linarith



lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]

lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]

lemma mem_Ico_iff_div (hx : 0 < x) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ n / x ∈ Ico a b := by
  rw [Finset.mem_Ico, mem_Ico, ceil_mul_le_iff hx, lt_ceil_mul_iff hx]

lemma tsum_indicator {f : ℕ → ℝ} (hx : 0 < x) :
    ∑' n, f n * (indicator (Ico a b) 1 (n / x)) = ∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  have l1 : ∀ n ∉ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n * indicator (Ico a b) 1 (↑n / x) = 0 := by
    simp [mem_Ico_iff_div hx] ; tauto
  rw [tsum_eq_sum l1] ; apply Finset.sum_congr rfl ; simp only [mem_Ico_iff_div hx] ; intro n hn ; simp [hn]

lemma WienerIkeharaInterval_discrete {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n) / x) atTop (nhds (A * (b - a))) := by
  apply (WienerIkeharaInterval hpos hf hcheby hG hG' ha hb).congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [tsum_indicator hx]

lemma WienerIkeharaInterval_discrete' {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Ico ⌈a * N⌉₊ ⌈b * N⌉₊, f n) / N) atTop (nhds (A * (b - a))) :=
  WienerIkeharaInterval_discrete hpos hf hcheby hG hG' ha hb |>.comp tendsto_natCast_atTop_atTop

-- TODO with `Ico`



/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/

lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds] ; intro δ hδ
  have l1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (δ / 2) := inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  have l2 : ∀ᶠ N : ℕ in atTop, 1 ≤ δ / 2 * N := by
    apply Tendsto.eventually_ge_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [l1.prod_mk l2] with (ε, N) ⟨⟨hε, h1⟩, h2⟩ ; dsimp only at *
  have l3 : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos, Nat.pos_iff_ne_zero] ; rintro rfl ; simp [zero_lt_one.not_ge] at h2
  have l5 : 0 ≤ ε * ↑N := by positivity
  have l6 : ε * N ≤ δ / 2 * N := mul_le_mul h1.le le_rfl (by positivity) (by positivity)
  simp only [dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
  convert (Nat.ceil_lt_add_one l5).trans_le (add_le_add l6 h2) using 1 ; ring

noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N

lemma S_sub_S {f : ℕ → 𝕜} {ε : ℝ} {N : ℕ} (hε : ε ≤ 1) : S f 0 N - S f ε N = cumsum f ⌈ε * N⌉₊ / N := by
  have hceilN : ⌈ε * N⌉₊ ≤ N := by
    simp only [Nat.ceil_le]
    exact mul_le_of_le_one_left N.cast_nonneg hε
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have r2 : Disjoint (Finset.range ⌈ε * N⌉₊) (Finset.Ico ⌈ε * N⌉₊ N) := by
    rw [Finset.range_eq_Ico] ; apply Finset.Ico_disjoint_Ico_consecutive
  simp [S, r1, Finset.sum_union r2, cumsum, add_div]

lemma tendsto_S_S_zero {f : ℕ → ℝ} (hpos : 0 ≤ f) (hcheby : cheby f) :
    TendstoUniformlyOnFilter (S f) (S f 0) (𝓝[>] 0) atTop := by
  rw [Metric.tendstoUniformlyOnFilter_iff] ; intro δ hδ
  obtain ⟨C, hC⟩ := hcheby
  have l1 : ∀ᶠ (p : ℝ × ℕ) in 𝓝[>] 0 ×ˢ atTop, C * ⌈p.1 * p.2⌉₊ / p.2 < δ := by
    have r1 := tendsto_mul_ceil_div.const_mul C
    simp only [mul_div_assoc', mul_zero] at r1 ; exact r1 (Iio_mem_nhds hδ)
  have : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
  filter_upwards [l1, Eventually.prod_inl this _] with (ε, N) h1 h2
  have l2 : ‖cumsum f ⌈ε * ↑N⌉₊ / ↑N‖ ≤ C * ⌈ε * N⌉₊ / N := by
    have r1 := hC ⌈ε * N⌉₊
    have r2 : 0 ≤ cumsum f ⌈ε * N⌉₊ := by apply cumsum_nonneg hpos
    simp only [norm_real, norm_of_nonneg (hpos _), norm_div,
      norm_of_nonneg r2, Real.norm_natCast] at r1 ⊢
    apply div_le_div_of_nonneg_right r1 (by positivity)
  simpa [← S_sub_S h2.2] using! l2.trans_lt h1

theorem WienerIkeharaTheorem' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) := by

  convert_to Tendsto (S f 0) atTop (𝓝 A) ; · ext N ; simp [S, cumsum]
  apply (tendsto_S_S_zero hpos hcheby).tendsto_of_eventually_tendsto
  · have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    · intro ε hε
      simpa using! WienerIkeharaInterval_discrete' hpos hf hcheby hG hG' hε.1 hε.2
  · have : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (this.const_sub 1).const_mul A

theorem vonMangoldt_cheby : cheby Λ := by
  use Real.log 4 + 4
  intro N
  by_cases! h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, norm_real, norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith



-- Proof extracted from the `EulerProducts` project so we can adapt it to the
-- version of the Wiener-Ikehara theorem proved above (with the `cheby`
-- hypothesis)

theorem WeakPNT : Tendsto (fun N ↦ cumsum Λ N / N) atTop (𝓝 1) := by
  let F := vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  have hnv := riemannZeta_ne_zero_of_one_le_re
  have l1 (n : ℕ) : 0 ≤ Λ n := vonMangoldt_nonneg
  have l2 s (hs : 1 < s.re) : F s = LSeries Λ s - 1 / (s - 1) := by
    have := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) isUnit_one hs
    simp only [F, this, vonMangoldt.residueClass, Nat.totient_one, Nat.cast_one, inv_one, one_div, sub_left_inj]
    apply LSeries_congr
    intro n _
    simp only [ofReal_inj, indicator_apply_eq_self, mem_ofPred_eq]
    exact fun hn ↦ absurd (Subsingleton.eq_one _) hn
  have l3 : ContinuousOn F {s | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have l4 : cheby Λ := vonMangoldt_cheby
  have l5 (σ' : ℝ) (hσ' : 1 < σ') : Summable (nterm Λ σ') := by
    simpa only [← nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt σ' hσ').norm
  apply WienerIkeharaTheorem' l1 l5 l4 l3 l2

end PNTX_Wiener

-- Ported from PrimeNumberTheoremAnd: Consequences.lean (selected lemmas up to chebyshev_asymptotic), followed by the new proof of H1
section PNTX_Conseq

section PNTConseq
open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

/-- If u ~ v and u-w = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact sub_isLittleO huv hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _

  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · intro N
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · intro N
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have := Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one
  simp only [rpow_one] at this
  exact Tendsto.comp this tendsto_natCast_atTop_atTop

/-- An alternate form of the Weak PNT. -/
theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
    rw [(by rfl : ψ = (fun x ↦ ψ x))]
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    · rw [isEquivalent_iff_tendsto_one]
      · convert! Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
        infer_instance
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
        Set.mem_ofPred_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [← isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop]
    use ε⁻¹
    intro b hb
    have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
    rw [abs_of_nonneg, abs_of_nonneg hb']
    · apply LE.le.trans _ ((inv_le_iff_one_le_mul₀' hε).mp hb)
      linarith [Nat.lt_floor_add_one b]
    rw [sub_nonneg]
    exact floor_le hb'

/-- `√x · log x = o(x)` as `x → ∞`. -/
lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert! isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2 with x
      rw [div_sqrt, sqrt_eq_rpow]
  exact this

theorem chebyshev_asymptotic : θ ~[atTop] id := by
  refine WeakPNT''.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)⟩
  · simpa only [mul_assoc] using! isLittleO_sqrt_mul_log.const_mul_left 2

end PNTConseq
end PNTX_Conseq

namespace Fact727AP
open Filter Real
open ArithmeticFunction hiding log
open scoped Topology
private theorem WeakPNT_AP {q a : ℕ} (hq : q ≥ 1) (ha : a.Coprime q) (ha' : a < q) :
    Tendsto (fun N ↦ cumsum (fun n ↦ if n % q = a then vonMangoldt n else 0) N / N)
      atTop (𝓝 (1 / q.totient)) := by
  have : NeZero q := ⟨by omega⟩
  let F := vonMangoldt.residueClass (a : ZMod q)
  have hpos : 0 ≤ F := fun n => vonMangoldt.residueClass_nonneg _ _
  have hle (n : ℕ) : F n ≤ vonMangoldt n := vonMangoldt.residueClass_le _ _
  have habs (n : ℕ) : ‖(F n : ℂ)‖ ≤ ‖(vonMangoldt n : ℂ)‖ := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hpos _),
      abs_of_nonneg vonMangoldt_nonneg] using hle n
  have hcheb : cheby (fun n => (F n : ℂ)) := by
    obtain ⟨C,hC⟩ := vonMangoldt_cheby
    exact ⟨C,fun N => (Finset.sum_le_sum fun n _ => habs n).trans (hC N)⟩
  have hsum (σ : ℝ) (hσ : 1 < σ) : Summable (nterm (fun n => (F n:ℂ)) σ) := by
    have hbase : Summable (nterm (fun n => (vonMangoldt n:ℂ)) σ) := by
      simpa only [← nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt σ hσ).norm
    apply Summable.of_nonneg_of_le _ _ hbase
    · intro n; simp only [nterm]; split <;> positivity
    · intro n; simp only [nterm]; split <;> first | exact le_rfl | exact div_le_div_of_nonneg_right (habs n) (by positivity)
  have hu := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hres : Set.EqOn (vonMangoldt.LFunctionResidueClassAux (a : ZMod q))
      (fun s : ℂ => LSeries (fun n => (F n:ℂ)) s - ((1 / (q.totient:ℝ):ℝ):ℂ) / (s-1))
      {s | 1 < s.re} := by
    simpa [F,one_div] using vonMangoldt.eqOn_LFunctionResidueClassAux hu
  have ht := WienerIkeharaTheorem' hpos hsum hcheb
    (vonMangoldt.continuousOn_LFunctionResidueClassAux (a : ZMod q)) hres
  have he (n : ℕ) : F n = (if n % q = a then vonMangoldt n else 0) := by
    simp [F,vonMangoldt.residueClass,Set.indicator_apply,ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha']
  simpa only [cumsum,he] using ht

open ArithmeticFunction hiding log
open _root_.Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

lemma tendsto_floor_add_one_div_self : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ + 1 : ℝ) / x) atTop (nhds 1) := by
  have h := Asymptotics.isEquivalent_nat_floor (R := ℝ)
  have h' : IsEquivalent atTop (fun x : ℝ ↦ (⌊x⌋₊ : ℝ) + 1) _root_.id :=
    h.add_isLittleO (isLittleO_const_id_atTop 1)
  rwa [isEquivalent_iff_tendsto_one
    (by filter_upwards [eventually_gt_atTop 0] with x hx a; simp only [_root_.id] at a; linarith)] at h'

/-- `x =Θ x / c` for nonzero constant `c`. -/
lemma isTheta_self_div_const {c : ℝ} (hc : c ≠ 0) : (fun x : ℝ ↦ x) =Θ[atTop] fun x ↦ x / c := by
  have : (fun x : ℝ ↦ x / c) = fun x ↦ c⁻¹ * x := by ext x; ring
  exact this ▸ (isTheta_const_mul_left (inv_ne_zero hc)).mpr (isTheta_refl ..) |>.symm

/-- Filtered sum over `Iic n` equals filtered sum over `Icc 1 n` for primes. -/
lemma filter_prime_Iic_eq_Icc (n : ℕ) : filter Prime (Iic n) = filter Prime (Icc 1 n) := by
  ext p; simp only [mem_filter, mem_Iic, mem_Icc, and_congr_left_iff]
  exact fun hp ↦ ⟨fun h ↦ ⟨hp.one_lt.le, h⟩, fun ⟨_, h⟩ ↦ h⟩

/-- `Icc 0 n = insert 0 (Icc 1 n)` -/
lemma Icc_zero_eq_insert (n : ℕ) : Icc 0 n = insert 0 (Icc 1 n) := by
  ext m; simp [mem_Icc]; omega


set_option maxHeartbeats 750000 in
theorem chebyshev_asymptotic_pnt
    {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : a.Coprime q) (ha' : a < q) :
    (fun x ↦ ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else 0) ~[atTop]
      fun x ↦ x / q.totient := by
  let ψ_aq : ℝ → ℝ := fun x ↦ ∑ n ∈ Icc 1 ⌊x⌋₊, if n % q = a then Λ n else 0
  have htot_pos : (0 : ℝ) < q.totient := cast_pos.mpr (totient_pos.mpr hq)
  have hψ_equiv : ψ_aq ~[atTop] fun x ↦ x / q.totient := by
    have hW := WeakPNT_AP hq ha ha'
    simp only [cumsum, ← Iio_eq_range] at hW
    have hψ_eq x : ψ_aq x = ∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0 := by
      simp only [ψ_aq, show Icc 1 ⌊x⌋₊ = (Iio (⌊x⌋₊ + 1)).filter (1 ≤ ·) by
        ext n; simp [mem_Icc, mem_filter]; tauto, sum_filter]
      refine sum_congr rfl fun n _ ↦ ?_
      by_cases hn : 1 ≤ n <;> simp only [hn, ↓reduceIte]
      push Not at hn; interval_cases n; simp
    refine (isEquivalent_iff_tendsto_one ?_).mpr ?_
    · filter_upwards [eventually_ge_atTop 1] with x hx; exact div_ne_zero (by linarith) htot_pos.ne'
    have hlim1 : Tendsto (fun x : ℝ ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) /
        (⌊x⌋₊ + 1 : ℝ)) atTop (nhds (1 / q.totient)) := by
      have heq : (fun x : ℝ ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) /
          (⌊x⌋₊ + 1 : ℝ)) = (fun N ↦ (∑ n ∈ Iio N, if n % q = a then Λ n else 0) / N) ∘
          (fun x : ℝ ↦ ⌊x⌋₊ + 1) := by ext x; simp [Function.comp_apply]
      exact heq ▸ hW.comp ((tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)
    have hgoal_eq : (ψ_aq / fun x ↦ x / (q.totient : ℝ)) =
        fun x ↦ ψ_aq x / x * q.totient := by ext x; simp only [Pi.div_apply, div_div_eq_mul_div]; ring
    rw [hgoal_eq, show (1 : ℝ) = 1 / q.totient * 1 * q.totient by field_simp]
    refine Tendsto.mul ?_ tendsto_const_nhds
    have heq' : (fun x ↦ ψ_aq x / x) =ᶠ[atTop]
        fun x ↦ (∑ n ∈ Iio (⌊x⌋₊ + 1), if n % q = a then Λ n else 0) / (⌊x⌋₊ + 1 : ℝ) * ((⌊x⌋₊ + 1 : ℝ) / x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      simp only [hψ_eq]; field_simp
    exact Tendsto.congr' heq'.symm (hlim1.mul tendsto_floor_add_one_div_self)
  refine hψ_equiv.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, eventually_atTop.mpr ⟨2, fun x hx ↦ ?_⟩⟩
    simp only [Pi.sub_apply, norm_eq_abs, one_mul]
    have hdiff_nonneg : 0 ≤ ψ_aq x - ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else 0 := by
      simp only [ψ_aq, sub_nonneg]
      calc (∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else (0 : ℝ))
          ≤ ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then Λ p else (0 : ℝ) :=
            sum_le_sum fun p hp ↦ by split_ifs <;> simp [vonMangoldt_apply_prime (mem_filter.mp hp).2]
        _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊, if n % q = a then Λ n else (0 : ℝ) :=
            sum_le_sum_of_subset_of_nonneg
              (fun p hp ↦ by simp only [mem_filter, mem_Iic, mem_Icc] at hp ⊢; exact ⟨hp.2.one_lt.le, hp.1⟩)
              (fun n _ _ ↦ by split_ifs <;> [exact vonMangoldt_nonneg; rfl])
    have hdiff_le : ψ_aq x - (∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), if p % q = a then log p else (0 : ℝ)) ≤ ψ x - θ x := by
      simp only [ψ_aq, Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
      conv_rhs => rw [Icc_zero_eq_insert, sum_insert (by simp : (0 : ℕ) ∉ Icc 1 ⌊x⌋₊),
        show Λ 0 = 0 by simp only [ArithmeticFunction.map_zero], zero_add,
        show filter Nat.Prime (insert 0 (Icc 1 ⌊x⌋₊)) = filter Nat.Prime (Icc 1 ⌊x⌋₊) by
          simp [filter_insert, Nat.not_prime_zero]]
      rw [filter_prime_Iic_eq_Icc, ← sum_filter_add_sum_filter_not (Icc 1 ⌊x⌋₊) Nat.Prime,
        show (∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), if p % q = a then log p else (0 : ℝ)) =
          ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), if p % q = a then Λ p else (0 : ℝ) from
          sum_congr rfl fun p hp ↦ by simp only [mem_filter] at hp; split_ifs <;> simp [vonMangoldt_apply_prime hp.2],
        ← sum_filter_add_sum_filter_not (Icc 1 ⌊x⌋₊) Nat.Prime,
        show (∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), Λ p) = ∑ p ∈ filter Nat.Prime (Icc 1 ⌊x⌋₊), log p from
          sum_congr rfl fun p hp ↦ vonMangoldt_apply_prime (mem_filter.mp hp).2]
      have h1 : (∑ n ∈ (Icc 1 ⌊x⌋₊).filter (¬Nat.Prime ·), if n % q = a then Λ n else (0 : ℝ)) ≤
          ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (¬Nat.Prime ·), Λ n :=
        sum_le_sum fun n _ ↦ by split_ifs <;> [exact le_refl _; exact vonMangoldt_nonneg]
      linarith
    rw [abs_of_nonneg hdiff_nonneg, abs_of_nonneg (by bound)]
    exact hdiff_le.trans ((le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith)))
  · simpa only [mul_assoc] using
      (isLittleO_sqrt_mul_log.const_mul_left 2).trans_isTheta (isTheta_self_div_const htot_pos.ne')

end Fact727AP

namespace OMA.SplitPrimes
open Finset Filter Real Asymptotics
open scoped Topology

private noncomputable def primesTo (x : ℝ) := (Iic ⌊x⌋₊).filter fun p : ℕ => p.Prime ∧ p % 3 = 1

private noncomputable def theta (x : ℝ) := ∑ p ∈ primesTo x, log (p : ℝ)

private lemma mem_primesTo {p : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    p ∈ primesTo x ↔ (p : ℝ) ≤ x ∧ p.Prime ∧ p % 3 = 1 := by
  simp only [primesTo, mem_filter, mem_Iic, Nat.le_floor_iff hx]

private lemma small_weight : ∀ᶠ x : ℝ in atTop,
    x ^ (3/4 : ℝ) * log x ≤ x / 100 := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : 0 < (1/4 : ℝ))).bound
    (show (0 : ℝ) < 1/100 by norm_num)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x h hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (log_nonneg hx),
    abs_of_nonneg (rpow_nonneg (by linarith) _)] at h
  have he : x ^ (3/4 : ℝ) * x ^ (1/4 : ℝ) = x := by
    rw [← rpow_add (by linarith : 0 < x)]
    norm_num
  calc
    _ ≤ x ^ (3/4 : ℝ) * (1/100 * x ^ (1/4 : ℝ)) :=
      mul_le_mul_of_nonneg_left h (rpow_nonneg (by linarith) _)
    _ = x / 100 := by linarith only [he]

/-- The primes below the cutoff contribute at most one count per positive integer.
Above the cutoff, each prime contributes at least three quarters of log x. -/
private lemma upper_count (x : ℝ) (hx : 1 ≤ x)
    (hsmall : x ^ (3/4 : ℝ) * log x ≤ x / 100) :
    ((primesTo x).card : ℝ) * (3/4 * log x) ≤ theta x + x / 100 := by
  classical
  let A := primesTo x
  let y := x ^ (3/4 : ℝ)
  let S : Finset ℕ := A.filter fun p : ℕ => (p : ℝ) ≤ y
  have hSA : S ⊆ A := filter_subset _ _
  have hy : 0 ≤ y := rpow_nonneg (by linarith) _
  have hS : S ⊆ Icc 1 ⌊y⌋₊ := by
    intro p hp
    obtain ⟨hpA, hpy⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨((mem_primesTo (by linarith : 0 ≤ x)).mp hpA).2.1.one_lt.le,
      Nat.le_floor hpy⟩
  have hScard : (S.card : ℝ) ≤ y := calc
    _ ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast (by simpa using card_le_card hS : S.card ≤ ⌊y⌋₊)
    _ ≤ y := Nat.floor_le hy
  have hlarge : ((A \ S).card : ℝ) * (3/4 * log x) ≤ theta x := calc
    _ = ∑ _p ∈ A \ S, 3/4 * log x := by simp
    _ ≤ ∑ p ∈ A \ S, log (p : ℝ) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpA, hpS⟩ := mem_sdiff.mp hp
      have hyp : y < p := lt_of_not_ge fun h => hpS (mem_filter.mpr ⟨hpA,h⟩)
      simpa [y, log_rpow (by linarith : 0 < x)] using log_le_log
        (rpow_pos_of_pos (by linarith : 0 < x) (3/4 : ℝ)) hyp.le
    _ ≤ theta x := sum_le_sum_of_subset_of_nonneg sdiff_subset fun p hp _ =>
      log_nonneg (by exact_mod_cast ((mem_primesTo (by linarith : 0 ≤ x)).mp hp).2.1.one_lt.le)
  have hc : ((A \ S).card : ℝ) + S.card = A.card := by
    exact_mod_cast card_sdiff_add_card_eq_card hSA
  have hSlog := mul_le_mul_of_nonneg_right hScard (log_nonneg hx)
  change (A.card : ℝ) * _ ≤ _
  have hs0 := mul_nonneg (Nat.cast_nonneg (α := ℝ) S.card) (log_nonneg hx)
  change y * log x ≤ x / 100 at hsmall
  rw [← hc, add_mul]
  linarith

private lemma interval_weight (x : ℝ) (hx : 1 ≤ x) :
    theta x - theta (x/2) ≤ ((primesTo x \ primesTo (x/2)).card : ℝ) * log x := by
  have hsub : primesTo (x/2) ⊆ primesTo x := by
    intro p hp
    obtain ⟨hh,hp,hm⟩ := (mem_primesTo (by linarith : 0 ≤ x/2)).mp hp
    exact (mem_primesTo (by linarith : 0 ≤ x)).mpr ⟨by linarith,hp,hm⟩
  have he := sum_sdiff hsub (f := fun p : ℕ => log (p : ℝ))
  unfold theta
  rw [← he, add_sub_cancel_right]
  calc
    _ ≤ ∑ _p ∈ primesTo x \ primesTo (x/2), log x := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hh,hpr,_⟩ := (mem_primesTo (by linarith : 0 ≤ x)).mp (mem_sdiff.mp hp).1
      exact log_le_log (by exact_mod_cast hpr.pos) hh
    _ = _ := by simp

private theorem dyadic (hθ : theta ~[atTop] fun x : ℝ => x / 2) :
    OMA.R_OeisA218585_conjecture_3_R1.H2 := by
  have h := hθ.isLittleO.bound (show (0 : ℝ) < 1/100 by norm_num)
  have hb : ∀ᶠ x : ℝ in atTop, 49/100 * x ≤ theta x ∧ theta x ≤ 51/100 * x := by
    filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hh hx
    simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x/2)] at hh
    obtain ⟨h₁,h₂⟩ := abs_le.mp hh
    constructor <;> linarith
  have hhalf : Tendsto (fun x : ℝ => x / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have hreal : ∀ᶠ x : ℝ in atTop,
      (primesTo x).card ≤ 3 * (primesTo x \ primesTo (x/2)).card := by
    filter_upwards [hb,hhalf.eventually hb,small_weight,eventually_gt_atTop (1 : ℝ)]
      with x hx hhalf hsmall hxone
    have hlow := interval_weight x hxone.le
    have hu := upper_count x hxone.le hsmall
    change 49/100 * (x/2) ≤ theta (x/2) ∧ theta (x/2) ≤ 51/100 * (x/2) at hhalf
    have hscaled : (primesTo x).card * log x ≤
        (3 * ((primesTo x \ primesTo (x/2)).card : ℝ)) * log x := by
      nlinarith only [hlow,hu,hx.1,hx.2,hhalf.2,le_of_lt hxone]
    exact_mod_cast (le_of_mul_le_mul_right hscaled (log_pos hxone))
  have htop : Tendsto (fun n : ℕ => (n : ℝ) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  filter_upwards [htop.eventually hreal, eventually_ge_atTop 2] with n hn hn2
  let P := (range n).filter fun p : ℕ => p.Prime ∧ p % 3 = 1
  have hpos : (0 : ℝ) ≤ (n : ℝ)-1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have he : primesTo (n-1 : ℝ) = P := by
    ext p
    rw [mem_primesTo hpos]
    simp only [P, mem_filter, mem_range]
    constructor <;> rintro ⟨hl, hp, hm⟩ <;> refine ⟨?_,hp,hm⟩
    · exact_mod_cast (by linarith : (p : ℝ) + 1 ≤ n)
    · have hh : (p : ℝ) + 1 ≤ n := by exact_mod_cast hl
      linarith
  have hd : primesTo (n-1 : ℝ) \ primesTo ((n-1 : ℝ)/2) = P.filter (fun p => n ≤ 2*p) := by
    ext p
    simp only [Finset.mem_sdiff, he, mem_filter, mem_primesTo (by linarith : 0 ≤ ((n:ℝ)-1)/2)]
    constructor
    · rintro ⟨hp, hn⟩
      refine ⟨hp, ?_⟩
      have hprime := (mem_filter.mp hp).2
      have hh : ¬ (p : ℝ) ≤ ((n:ℝ)-1)/2 := fun h => hn ⟨h,hprime⟩
      have hh' : ¬ 2 * p + 1 ≤ n := by
        intro h
        have hr : (2 : ℝ) * p + 1 ≤ n := by exact_mod_cast h
        exact hh (by linarith)
      omega
    · rintro ⟨hp, h⟩
      refine ⟨hp, ?_⟩
      rintro ⟨hle, -⟩
      linarith [show (n:ℝ) ≤ 2*p by exact_mod_cast h]
  change (primesTo (n-1 : ℝ)).card ≤ 3 * (primesTo (n-1 : ℝ) \ primesTo ((n-1 : ℝ)/2)).card at hn
  rwa [hd,he] at hn

end OMA.SplitPrimes

theorem OMA.splitDyadic : OMA.R_OeisA218585_conjecture_3_R1.H2 := by
  apply OMA.SplitPrimes.dyadic
  have ht := Fact727AP.chebyshev_asymptotic_pnt (q := 3) (a := 1)
    (by decide) (by decide) (by decide)
  have he (x : ℝ) : OMA.SplitPrimes.theta x =
      ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, if p % 3 = 1 then Real.log (p : ℝ) else 0 := by
    classical
    simp only [OMA.SplitPrimes.theta, OMA.SplitPrimes.primesTo, ← Finset.sum_filter, Finset.filter_filter]
  rw [funext he]
  simpa only [show Nat.totient 3 = 2 by decide, Nat.cast_ofNat] using ht
end

section
/- Integrated source: proofs/OeisA218585.conjecture_3.R1.H1.R1.H2 (shared AP prime-number theorem above) -/
namespace OMA.SplitPrimes
open Finset Filter Real Asymptotics
open scoped Topology
private theorem split_prime_log_mean (h : theta ~[atTop] (fun x : ℝ => x/2)) :
    Tendsto (fun N : ℕ =>
      (∑ p ∈ (range N).filter (fun p => p.Prime ∧ p % 3 = 1), log p) / N) atTop (𝓝 (1/2:ℝ)) := by
  have nz : ∀ᶠ x : ℝ in atTop, x/2 ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    positivity
  have realMean := (isEquivalent_iff_tendsto_one nz).mp h
  have shift : Tendsto (fun n : ℕ => (n:ℝ)-1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have ratio : Tendsto (fun n : ℕ => ((n:ℝ)-1)/n) atTop (𝓝 1) := by
    have h₀ : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h₁ := h₀.const_sub 1
    rw [sub_zero] at h₁
    apply h₁.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have nz : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have combined := ((realMean.comp shift).mul ratio).div_const 2
  rw [one_mul] at combined
  apply combined.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hp : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have seteq : primesTo ((n:ℝ)-1) = (range n).filter fun p => p.Prime ∧ p % 3 = 1 := by
    ext p
    rw [mem_primesTo (by linarith)]
    simp only [mem_filter,mem_range]
    constructor <;> rintro ⟨hl,hp,hm⟩ <;> refine ⟨?_,hp,hm⟩
    · exact_mod_cast (by linarith : (p:ℝ)+1 ≤ n)
    · have hh : (p:ℝ)+1 ≤ n := by exact_mod_cast hl
      linarith
  change theta ((n:ℝ)-1) / (((n:ℝ)-1)/2) * (((n:ℝ)-1)/n) / 2 = _
  rw [theta,seteq]
  field_simp [show (n:ℝ)-1 ≠ 0 by linarith]

end OMA.SplitPrimes

theorem OMA.splitMass : OMA.R_OeisA218585_conjecture_3_R1_H1_R1.H2 := by
  apply OMA.SplitPrimes.split_prime_log_mean
  have ht := Fact727AP.chebyshev_asymptotic_pnt (q := 3) (a := 1)
    (by decide) (by decide) (by decide)
  have he (x : ℝ) : OMA.SplitPrimes.theta x =
      ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, if p % 3 = 1 then Real.log (p:ℝ) else 0 := by
    classical
    simp only [OMA.SplitPrimes.theta, OMA.SplitPrimes.primesTo, ← Finset.sum_filter, Finset.filter_filter]
  rw [funext he]
  simpa only [show Nat.totient 3 = 2 by decide,Nat.cast_ofNat] using ht
end

section
/- Integrated source: proofs/OeisA218585.conjecture_4.R1.H2.R1.H1.R1.H2 (shared Wiener–Ikehara proof above) -/
open ArithmeticFunction Filter Finset
open scoped Topology

/- The Wiener–Ikehara theorem above is the port used in PR 4399.
Here domination by twice the von Mangoldt function supplies both of its growth bounds. -/
theorem OMA.angularTauberian : OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1.H2 := by
  intro f hf ⟨G,hG,heq⟩
  have hn (n : ℕ) : ‖(f n : ℂ)‖ ≤ 2*‖(Λ n : ℂ)‖ := by
    simpa only [Complex.norm_real,Real.norm_eq_abs, abs_of_nonneg (hf n).1,
      abs_of_nonneg vonMangoldt_nonneg] using (hf n).2
  have hc : cheby (fun n => (f n:ℂ)) := by
    obtain ⟨C,c⟩ := vonMangoldt_cheby
    refine ⟨2*C,fun N => ?_⟩
    calc
      _ ≤ ∑ n ∈ range N, 2*‖(Λ n:ℂ)‖ := sum_le_sum fun n _ => hn n
      _ = 2*cumsum (fun n => ‖(Λ n:ℂ)‖) N := (mul_sum ..).symm
      _ ≤ _ := by have h := c N; linarith
  have hs (s : ℝ) (hs : 1<s) : Summable (nterm (fun n => (f n:ℂ)) s) := by
    have base : Summable (nterm (fun n => (Λ n:ℂ)) s) := by
      simpa only [←nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt s hs).norm
    apply Summable.of_nonneg_of_le _ _ (base.mul_left 2)
    · intro n; simp only [nterm]; split <;> positivity
    · intro n
      simp only [nterm]
      split
      · simp
      · rw [mul_div_assoc']
        exact div_le_div_of_nonneg_right (hn n) (by positivity)
  have bound := WienerIkeharaTheorem' (f := f) (A := 1) (fun n => (hf n).1) hs hc hG
  apply bound
  simpa only [Complex.ofReal_one] using heq
end

section
/- Integrated source: reductions/OeisA218585.conjecture_4.R1.H2.R1.H1.R1 (exact weighted part) -/
namespace OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1
open Finset OeisA218585 Filter Real ArithmeticFunction
open scoped Topology

theorem log_modes : H1 → H2 → OMA.R_OeisA218585_conjecture_3_R1_H1_R1.H1 := by
  classical
  intro boundary tauberian k hk
  let z (p : ℕ) : ℂ := ⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩
  let u (n : ℕ) := cos ((k:ℝ)*(6*(z n).arg))
  let P (N : ℕ) := (range N).filter fun p => p.Prime ∧ p%3=1
  let w (n : ℕ) := if n.Prime ∧ n%3=1 then u n else 0
  let f (e : ℝ) (n : ℕ) := Λ n*(1+e*w n)
  have hw (n) : |w n| ≤ 1 := by dsimp [w]; split <;> simp [u,abs_cos_le_one]
  have mean (e : ℝ) (he : |e|=1) :
      Tendsto (fun N : ℕ => (∑ n ∈ range N, f e n)/N) atTop (𝓝 1) := by
    apply tauberian (f e) _ (boundary k hk e he)
    intro n
    have h : |e*w n| ≤ 1 := by simpa [abs_mul,he] using hw n
    obtain ⟨lo,hi⟩ := abs_le.mp h
    dsimp [f]
    exact ⟨mul_nonneg vonMangoldt_nonneg (by linarith),
      by simpa [mul_comm] using mul_le_mul_of_nonneg_left (by linarith : 1+e*w n≤2) (vonMangoldt_nonneg (n:=n))⟩
  let W (N : ℕ) := ∑ p ∈ P N, Real.log p*u p
  have canc : Tendsto (fun N : ℕ => W N/N) atTop (𝓝 0) := by
    have h := ((mean 1 (by norm_num)).sub (mean (-1) (by norm_num))).div_const 2
    rw [sub_self,zero_div] at h
    apply h.congr
    intro N
    rw [←sub_div,←sum_sub_distrib]
    have sumid : (∑ n ∈ range N, (f 1 n-f (-1) n)) = 2*W N := by
      dsimp only [W,P]
      rw [sum_filter,mul_sum]
      apply sum_congr rfl
      intro n _
      by_cases b : n.Prime ∧ n%3=1
      · simp [f,w,b,vonMangoldt_apply_prime b.1]; ring
      · simp [f,w,b]
    rw [sumid]; ring
  exact canc
end OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1
end

theorem OMA.solution : type_of% @OeisA218585.conjecture_3 :=
  OMA.R_OeisA218585_conjecture_3_R1.main (OMA.R_OeisA218585_conjecture_3_R1_H1_R1.main
    (OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1.log_modes
      (OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1.main
        (OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1_H1_R1.main OMA.angularHecke OMA.angularPositivity)
        OMA.angularPrimePowers) OMA.angularTauberian) OMA.splitMass) OMA.splitDyadic
