import OMAReductions.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1
import Mathlib

/-!
# Two neighboring logarithmic intervals

For every split point `r < x`, count primes in `(r-h,r]`, where `h = ⌈C log x⌉`.
The first estimate counts these primes with multiplicity when `(r,r+h]` is empty.
The second controls their unconditioned second moment. Cauchy–Schwarz gives a
positive density of distinct split points. Each possible last prime accounts for
at most `h` split points, and its successor is more than `h` away.

The adjacent-interval counting approach is also used in OpenAI's *Positive lower
density of large prime gaps*, `OAI/NumberTheory/PrimeGaps/Indices.lean`. Here `x`
is the endpoint prime itself and all gap indices are zero-based.
-/
namespace OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1_H1_R2

open Finset Filter Real
open scoped Classical

/-- Count the prime/split-point pairs for which the following interval is empty. -/
def H1 : Prop := ∀ C : ℝ, 0 < C → ∃ a : ℝ, 0 < a ∧ ∀ᶠ x : ℕ in atTop,
  let h := ⌈C * log (x : ℝ)⌉₊
  let left (r : ℕ) := (Ioc (r-h) r).filter Nat.Prime
  let starts := (range x).filter fun r => (left r).Nonempty ∧
    ∀ q ∈ Ioc r (r+h), ¬ Nat.Prime q
  a * x ≤ ∑ r ∈ starts, ((left r).card : ℝ)

/-- A second-moment upper bound for primes in an interval of logarithmic length. -/
def H2 : Prop := ∀ C : ℝ, 0 < C → ∃ b : ℝ, 0 < b ∧ ∀ᶠ x : ℕ in atTop,
  let h := ⌈C * log (x : ℝ)⌉₊
  ∑ r ∈ range x, (((Ioc (r-h) r).filter Nat.Prime).card : ℝ)^2 ≤ b * x

lemma count_support (s t : Finset ℕ) (hsub : t ⊆ s) (w : ℕ → ℝ)
    {x a b : ℝ} (hx : 0 < x) (ha : 0 < a) (hb : 0 < b)
    (hfirst : a*x ≤ ∑ r ∈ t, w r) (hsecond : ∑ r ∈ s, w r ^ 2 ≤ b*x) :
    a^2/b*x ≤ (t.card : ℝ) := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq t (fun _ => (1 : ℝ)) w
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at cs
  have small := (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => sq_nonneg (w r))).trans hsecond
  have bound := cs.trans (mul_le_mul_of_nonneg_left small (Nat.cast_nonneg _))
  have lhs := mul_self_le_mul_self (mul_pos ha hx).le hfirst
  rw [div_mul_eq_mul_div, div_le_iff₀ hb]
  apply (mul_le_mul_iff_left₀ hx).mp
  nlinarith only [bound, lhs]

/-- Cover all split points by length-`h` intervals indexed by qualifying gaps. -/
private lemma split_points_le (C : ℝ) (hC : 0 < C) (N h : ℕ)
    (hh : C * log (Nat.nth Nat.Prime N) ≤ (h : ℝ)) :
    let P := Nat.nth Nat.Prime
    let starts := (range (P N)).filter fun r => ((Ioc (r-h) r).filter Nat.Prime).Nonempty ∧
      ∀ q ∈ Ioc r (r+h), ¬ Nat.Prime q
    let gaps := (range N).filter fun i => C * log (P i) < (primeGap i : ℝ)
    starts.card ≤ gaps.card * h := by
  classical
  intro P starts gaps
  have mono : StrictMono P := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have cover : starts ⊆ gaps.biUnion (fun i => Ico (P i) (P i+h)) := by
    intro r hr
    obtain ⟨hrN, hne, hempty⟩ := mem_filter.mp hr
    let S := (Ioc (r-h) r).filter Nat.Prime
    let p := S.max' hne
    have hpm : p ∈ S := Finset.max'_mem _ _
    obtain ⟨hpr, hp⟩ := mem_filter.mp hpm
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hpr
    let i := Nat.count Nat.Prime p
    have hpi : P i = p := Nat.nth_count hp
    have hi : i < N := mono.lt_iff_lt.mp (hpi ▸ lt_of_le_of_lt hhi (mem_range.mp hrN))
    have hnext := Nat.prime_nth_prime (i+1)
    have hlt : p < P (i+1) := hpi ▸ mono (Nat.lt_succ_self i)
    have hright : r+h < P (i+1) := by
      by_contra! hle
      by_cases near : P (i+1) ≤ r
      · have hn : P (i+1) ∈ S := mem_filter.mpr ⟨mem_Ioc.mpr ⟨hlo.trans hlt, near⟩, hnext⟩
        exact hlt.not_ge (Finset.le_max' S _ hn)
      · exact hempty _ (mem_Ioc.mpr ⟨lt_of_not_ge near, hle⟩) hnext
    have hgap : h < primeGap i := by change h < P (i+1) - P i; omega
    have hlog := Real.log_le_log (by exact_mod_cast hp.pos : (0 : ℝ) < p)
      (by exact_mod_cast (hhi.trans (mem_range.mp hrN).le) : (p : ℝ) ≤ P N)
    apply mem_biUnion.mpr
    refine ⟨i, mem_filter.mpr ⟨mem_range.mpr hi, ?_⟩, mem_Ico.mpr ⟨by omega, by omega⟩⟩
    rw [hpi]
    exact ((mul_le_mul_of_nonneg_left hlog hC.le).trans hh).trans_lt (by exact_mod_cast hgap)
  calc
    _ ≤ _ := card_le_card cover
    _ ≤ ∑ i ∈ gaps, (Ico (P i) (P i+h)).card := card_biUnion_le
    _ = _ := by simp

private lemma index_width (C : ℝ) (hC : 0 < C) : ∃ D : ℝ, 0 < D ∧
    ∀ᶠ N : ℕ in atTop, (N : ℝ) * ⌈C * log (Nat.nth Nat.Prime N)⌉₊ ≤ D * Nat.nth Nat.Prime N := by
  let P := Nat.nth Nat.Prime
  have hp : Tendsto P atTop atTop := tendsto_atTop_mono
    (fun n => (Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n)) tendsto_id
  have bound := (tendsto_natCast_atTop_atTop.comp hp).eventually
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  refine ⟨C*(log 4+1)+1, by positivity, ?_⟩
  filter_upwards [bound] with N hn
  have hprime := Nat.prime_nth_prime N
  have more := Nat.add_two_le_nth_prime N
  have hlog : 0 < log (P N : ℝ) := log_pos (by exact_mod_cast hprime.one_lt)
  have idx : N ≤ Nat.primeCounting (P N) := by
    rw [Nat.primeCounting_eq_primeCounting'_succ]
    exact (Nat.primeCounting'_nth_eq N).ge.trans (Nat.monotone_primeCounting' (Nat.le_succ _))
  simp only [Function.comp_apply, Nat.floor_natCast] at hn
  have prod := (le_div_iff₀ hlog).mp ((show (N : ℝ) ≤ Nat.primeCounting (P N) by exact_mod_cast idx).trans hn)
  have ceil := Nat.ceil_lt_add_one (mul_nonneg hC.le hlog.le)
  have small : (N : ℝ) ≤ P N := by exact_mod_cast ((Nat.le_add_right N 2).trans more)
  change (N : ℝ) * (⌈C * log (P N : ℝ)⌉₊ : ℝ) ≤ _
  nlinarith [mul_le_mul_of_nonneg_left prod hC.le, mul_le_mul_of_nonneg_left ceil.le (Nat.cast_nonneg N : (0:ℝ) ≤ N)]

theorem main : H1 → H2 → OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1.H1 := by
  intro first second C hC
  obtain ⟨a, ha, hfirst⟩ := first C hC
  obtain ⟨b, hb, hsecond⟩ := second C hC
  obtain ⟨D, hD, hwidth⟩ := index_width C hC
  let P := Nat.nth Nat.Prime
  have hp : Tendsto P atTop atTop := tendsto_atTop_mono
    (fun n => (Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n)) tendsto_id
  refine ⟨(a^2/b)/D, by positivity, ?_⟩
  filter_upwards [hp.eventually hfirst, hp.eventually hsecond, hwidth] with N hf hs hw
  let h := ⌈C * log (P N)⌉₊
  let left (r : ℕ) := (Ioc (r-h) r).filter Nat.Prime
  let starts := (range (P N)).filter fun r => (left r).Nonempty ∧ ∀ q ∈ Ioc r (r+h), ¬ Nat.Prime q
  let gaps := (range N).filter fun i => C * log (P i) < (primeGap i : ℝ)
  have xp : (0 : ℝ) < P N := by exact_mod_cast (Nat.prime_nth_prime N).pos
  have mass := count_support (range (P N)) starts (filter_subset _ _) (fun r => ((left r).card : ℝ)) xp ha hb hf hs
  have lower := Nat.le_ceil (C * log (P N))
  have count : (starts.card : ℝ) ≤ (gaps.card : ℝ) * h := by
    exact_mod_cast split_points_le C hC N h lower
  have hpos : (0 : ℝ) < h := (mul_pos hC (log_pos (by exact_mod_cast (Nat.prime_nth_prime N).one_lt))).trans_le lower
  change (N : ℝ) * h ≤ D * P N at hw
  change (a^2/b)/D * N ≤ (gaps.card : ℝ)
  rw [div_mul_eq_mul_div, div_le_iff₀ hD]
  apply (mul_le_mul_iff_left₀ hpos).mp
  nlinarith only [mul_le_mul_of_nonneg_left hw (div_nonneg (sq_nonneg a) hb.le),
    mul_le_mul_of_nonneg_left (mass.trans count) hD.le]

end OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1_H1_R2
