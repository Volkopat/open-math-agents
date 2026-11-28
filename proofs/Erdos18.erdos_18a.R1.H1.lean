import OMAReductions.R_Erdos18_erdos_18a_R1
import Mathlib

-- BEGIN external module Arithmetic

/-!
# Arithmetic infrastructure for Erdős 18(c)

Arithmetic lemmas used by the complete proof in FinalBound.lean.

The definitions of subset sums and practicalH follow the Formal Conjectures
statement (Apache-2.0); the radix and carrying arguments are adapted from
Kohlmeyer--Kruer, "Short sums of factorial divisors and Erdős Problem 18(b)"
(16 September 2026), Sections 5--6, with explicit credit.
-/

open Finset

namespace Erdos18c

def subsetSums (D : Set ℕ) : Set ℕ :=
  {R | ∃ E : Finset ℕ, (↑E : Set ℕ) ⊆ D ∧ E.sum id = R}

noncomputable def practicalH (N : ℕ) : ℕ :=
  (Finset.Icc 1 N).sup fun R =>
    sInf {k | ∃ D : Finset ℕ, D ⊆ N.divisors ∧ D.card = k ∧
      R ∈ subsetSums (↑D : Set ℕ)}

def IsPractical (N : ℕ) : Prop :=
  ∀ R ≤ N, ∃ D : Finset ℕ, D ⊆ N.divisors ∧ D.sum id = R

def ShortSum (N R k : ℕ) : Prop :=
  ∃ D : Finset ℕ, D ⊆ N.divisors ∧ D.sum id = R ∧ D.card ≤ k

theorem shortSum_zero (N k : ℕ) : ShortSum N 0 k := by
  exact ⟨∅, by simp, by simp, by simp⟩

theorem shortSum_mono_count {N R k l : ℕ}
    (h : ShortSum N R k) (hkl : k ≤ l) : ShortSum N R l := by
  obtain ⟨D, hD, hsum, hcard⟩ := h
  exact ⟨D, hD, hsum, hcard.trans hkl⟩

theorem shortSum_mono_host {N M R k : ℕ}
    (hNM : N ∣ M) (hM : M ≠ 0) (h : ShortSum N R k) : ShortSum M R k := by
  obtain ⟨D, hD, hsum, hcard⟩ := h
  exact ⟨D, hD.trans (Nat.divisors_subset_of_dvd hM hNM), hsum, hcard⟩

theorem practicalH_le_of_shortSums (N k : ℕ)
    (h : ∀ R ∈ Finset.Icc 1 N, ShortSum N R k) : practicalH N ≤ k := by
  classical
  unfold practicalH
  apply Finset.sup_le
  intro R hR
  obtain ⟨D, hD, hsum, hcard⟩ := h R hR
  apply le_trans ?_ hcard
  apply Nat.sInf_le
  exact ⟨D, hD, rfl, D, Set.Subset.rfl, hsum⟩

theorem shortSum_of_practicalH {N R : ℕ}
    (hN : IsPractical N) (hR : R ≤ N) : ShortSum N R (practicalH N) := by
  classical
  by_cases hz : R = 0
  · subst R
    exact shortSum_zero _ _
  obtain ⟨A, hA, hAsum⟩ := hN R hR
  have hne : {k | ∃ D : Finset ℕ, D ⊆ N.divisors ∧ D.card = k ∧
      R ∈ subsetSums (↑D : Set ℕ)}.Nonempty :=
    ⟨A.card, A, hA, rfl, A, Set.Subset.rfl, hAsum⟩
  obtain ⟨D, hD, hcard, E, hED, hsum⟩ := Nat.sInf_mem hne
  have hsub : E ⊆ D := Finset.coe_subset.mp hED
  refine ⟨E, hsub.trans hD, hsum, ?_⟩
  calc
    E.card ≤ D.card := Finset.card_le_card hsub
    _ = sInf {k | ∃ D : Finset ℕ, D ⊆ N.divisors ∧ D.card = k ∧
      R ∈ subsetSums (↑D : Set ℕ)} := hcard
    _ ≤ practicalH N := Finset.le_sup (f := fun R =>
      sInf {k | ∃ D : Finset ℕ, D ⊆ N.divisors ∧ D.card = k ∧
        R ∈ subsetSums (↑D : Set ℕ)}) (Finset.mem_Icc.mpr ⟨by omega, hR⟩)

theorem shortSum_radix {M q a r k l : ℕ}
    (hM : 0 < M) (hq : 0 < q) (hrq : r < q)
    (ha : ShortSum M a k) (hr : ShortSum (q * M) r l) :
    ShortSum (q * M) (q * a + r) (k + l) := by
  classical
  obtain ⟨A, hA, hAsum, hAcard⟩ := ha
  obtain ⟨B, hB, hBsum, hBcard⟩ := hr
  have hinj : Function.Injective (fun d : ℕ => q * d) :=
    fun _ _ h => mul_left_cancel₀ (ne_of_gt hq) h
  have hdisj : Disjoint (A.image (fun d => q * d)) B := by
    apply Finset.disjoint_left.mpr
    intro x hx hxB
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos
      (Nat.dvd_of_mem_divisors (hA hd)) hM
    have hlow : q ≤ q * d := by nlinarith
    have hhigh : q * d ≤ r := by
      rw [← hBsum]
      exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hxB
    omega
  refine ⟨A.image (fun d => q * d) ∪ B, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
      exact Nat.mem_divisors.mpr
        ⟨mul_dvd_mul_left q (Nat.dvd_of_mem_divisors (hA hd)),
          ne_of_gt (Nat.mul_pos hq hM)⟩
    · exact hB hx
  · rw [Finset.sum_union hdisj, Finset.sum_image (fun x _ y _ h => hinj h)]
    change (∑ x ∈ A, q * x) + B.sum id = q * a + r
    rw [← Finset.mul_sum, show (∑ x ∈ A, x) = a from hAsum, hBsum]
  · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective A hinj]
    omega

theorem practicalH_radix {M q l : ℕ}
    (hM : IsPractical M) (hMpos : 0 < M) (hq : 0 < q)
    (hlocal : ∀ r < q, ShortSum (q * M) r l) :
    practicalH (q * M) ≤ practicalH M + l := by
  apply practicalH_le_of_shortSums
  intro R hR
  have hquot : R / q ≤ M :=
    Nat.div_le_of_le_mul (Finset.mem_Icc.mp hR).2
  have hrep := shortSum_radix hMpos hq (Nat.mod_lt R hq)
    (shortSum_of_practicalH hM hquot) (hlocal (R % q) (Nat.mod_lt R hq))
  simpa only [Nat.div_add_mod] using hrep

theorem positive_quotient {R S q : ℕ}
    (hq : 0 < q) (hSR : S < R) (hdvd : q ∣ R - S) :
    ∃ t : ℕ, 0 < t ∧ R = S + q * t ∧ t ≤ R / q := by
  refine ⟨(R - S) / q, ?_, ?_, ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd (Nat.sub_pos_of_lt hSR) hdvd) hq
  · rw [Nat.mul_div_cancel' hdvd]
    exact (Nat.add_sub_of_le hSR.le).symm
  · exact Nat.div_le_div_right (Nat.sub_le R S)

theorem factorial_power_dvd (m r : ℕ) :
    m.factorial ^ r ∣ (r * m).factorial := by
  simpa using Nat.prod_factorial_dvd_factorial_sum (Finset.range r) (fun _ => m)

theorem factorial_binary_reserve (m k : ℕ) :
    2 ^ k * m.factorial ∣ (m + 2 * k).factorial := by
  have hpow : 2 ^ k ∣ (2 * k).factorial := by
    simpa [Nat.factorial, Nat.mul_comm] using factorial_power_dvd 2 k
  exact (mul_dvd_mul hpow (dvd_refl m.factorial)).trans
    (by simpa [Nat.add_comm] using
      Nat.factorial_mul_factorial_dvd_factorial_add (2 * k) m)

theorem shifted_divisor_dvd_factorial {m k b d : ℕ}
    (hd : d ∣ m.factorial) (hb : b ≤ k) :
    2 ^ b * d ∣ (m + 2 * k).factorial :=
  (mul_dvd_mul (pow_dvd_pow 2 hb) hd).trans (factorial_binary_reserve m k)

theorem factorial_isPractical (n : ℕ) : IsPractical n.factorial := by
  induction n with
  | zero =>
    intro R hR
    simp only [Nat.factorial_zero] at hR
    have hcases : R = 0 ∨ R = 1 := by omega
    rcases hcases with rfl | rfl
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by simp, by simp⟩
  | succ n ih =>
    intro R hR
    let q := n + 1
    have hq : 0 < q := Nat.succ_pos n
    have hle : R / q ≤ n.factorial := by
      apply Nat.div_le_of_le_mul
      simpa [q, Nat.factorial_succ] using hR
    obtain ⟨A, hA, hAsum⟩ := ih (R / q) hle
    have hr : R % q < q := Nat.mod_lt R hq
    have hrepsum : ShortSum (q * n.factorial) (R % q) 1 := by
      by_cases hz : R % q = 0
      · simpa only [hz] using shortSum_zero (q * n.factorial) 1
      · refine ⟨{R % q}, ?_, by simp, by simp⟩
        intro d hd
        have hd' : d = R % q := Finset.mem_singleton.mp hd
        subst d
        exact Nat.mem_divisors.mpr ⟨
          (Nat.dvd_factorial (Nat.pos_of_ne_zero hz) (show R % q ≤ n + 1 from hr.le)),
          Nat.factorial_ne_zero (n + 1)⟩
    have hrep := shortSum_radix (Nat.factorial_pos n) hq hr
      (show ShortSum n.factorial (R / q) A.card from ⟨A,hA,hAsum,le_rfl⟩) hrepsum
    obtain ⟨D,hD,hDsum,_⟩ := hrep
    refine ⟨D, ?_, ?_⟩
    · simpa [q,Nat.factorial_succ] using hD
    · simpa only [Nat.div_add_mod] using hDsum

theorem distinctify_divisor_multiset (s : Multiset ℕ) {N : ℕ}
    (hN : N ≠ 0) (hs : ∀ d ∈ s, d ∣ N) :
    ShortSum (2 ^ s.card * N) s.sum s.card := by
  classical
  have aux : ∀ k : ℕ, ∀ t : Multiset ℕ, t.card = k →
      ∀ M : ℕ, M ≠ 0 → (∀ d ∈ t, d ∣ M) →
      ShortSum (2 ^ k * M) t.sum k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro t hk M hM ht
      by_cases hn : t.Nodup
      · refine ⟨t.toFinset, ?_, ?_, ?_⟩
        · intro d hd
          exact Nat.mem_divisors.mpr
            ⟨dvd_mul_of_dvd_right (ht d (Multiset.mem_toFinset.mp hd)) (2 ^ k),
             mul_ne_zero (pow_ne_zero _ (by decide)) hM⟩
        · change (t.toFinset.val.map id).sum = t.sum
          simp [hn.dedup]
        · exact le_of_eq ((Multiset.toFinset_card_of_nodup hn).trans hk)
      · rw [Multiset.nodup_iff_ne_cons_cons] at hn
        push Not at hn
        obtain ⟨a,u,rfl⟩ := hn
        have hc : (2 * a ::ₘ u).card < k := by
          simp only [Multiset.card_cons] at hk ⊢
          omega
        have hnew : ∀ d ∈ (2 * a ::ₘ u), d ∣ 2 * M := by
          intro d hd
          rcases Multiset.mem_cons.mp hd with rfl | hd
          · exact mul_dvd_mul_left 2 (ht a (by simp))
          · exact dvd_mul_of_dvd_right (ht d (by simp [hd])) 2
        have hrep := ih _ hc (2 * a ::ₘ u) rfl (2 * M)
          (mul_ne_zero (by decide) hM) hnew
        have hhost : 2 ^ (2 * a ::ₘ u).card * (2 * M) = 2 ^ k * M := by
          rw [← hk]
          simp only [Multiset.card_cons,pow_succ]
          ring
        have hsum : (2 * a ::ₘ u).sum = (a ::ₘ a ::ₘ u).sum := by
          simp [two_mul,add_assoc]
        have hrep' := shortSum_mono_count hrep hc.le
        simpa only [hhost,hsum] using hrep'
  exact aux s.card s rfl N hN hs

theorem distinctify_factorial_divisors (s : Multiset ℕ) (F : ℕ)
    (hs : ∀ d ∈ s, d ∣ F.factorial) :
    ShortSum (F + 2 * s.card).factorial s.sum s.card :=
  shortSum_mono_host (factorial_binary_reserve F s.card)
    (Nat.factorial_ne_zero _) (distinctify_divisor_multiset s (Nat.factorial_ne_zero F) hs)

theorem factorial_radix_recurrence {n m l : ℕ} (hmn : m ≤ n)
    (hlocal : ∀ r < n.factorial / m.factorial, ShortSum n.factorial r l) :
    practicalH n.factorial ≤ practicalH m.factorial + l := by
  have hdiv : m.factorial ∣ n.factorial := Nat.factorial_dvd_factorial hmn
  have heq : n.factorial / m.factorial * m.factorial = n.factorial :=
    Nat.div_mul_cancel hdiv
  have hq : 0 < n.factorial / m.factorial :=
    Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos n) hdiv) (Nat.factorial_pos m)
  have h := practicalH_radix (factorial_isPractical m) (Nat.factorial_pos m) hq
    (by simpa only [heq] using hlocal)
  simpa only [heq] using h


end Erdos18c
-- END external module Arithmetic

-- BEGIN external module FiniteLaw

/-!
Finite entropy and pushforward infrastructure adapted from Kohlmeyer--Kruer,
Erdos18b.lean, source SHA-256
4d6ee89617415288e9f127beb3c0e0211c011f891889fcb43d0e16373bd14088.
Only the selected elementary infrastructure is ported here; no result about
Erdos 18(b) is being used to assert the new 18(c) conclusion.
-/

open Finset
namespace Erdos18c

noncomputable def finiteEntropy {ι : Type*} (S : Finset ι) (p : ι → ℝ) : ℝ :=
  ∑ x ∈ S, Real.negMulLog (p x)

theorem sum_mul_log_le_log_bound {ι : Type*} (S : Finset ι) (p : ι → ℝ) {M : ℝ}
    (hp : ∀ x ∈ S, 0 ≤ p x) (hbound : ∀ x ∈ S, p x ≤ M) :
    (∑ x ∈ S, p x * Real.log (p x)) ≤ (∑ x ∈ S, p x) * Real.log M := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x hx
  by_cases hpx : p x = 0
  · simp [hpx]
  · exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (lt_of_le_of_ne (hp x hx) (Ne.symm hpx)) (hbound x hx)) (hp x hx)

theorem finite_entropy_fiber_defect {ι : Type*} (S : Finset ι) (p : ι → ℝ) {q M : ℝ}
    (hp : ∀ x ∈ S, 0 ≤ p x) (hq : 0 < q) (hM : 0 ≤ M) (hbound : ∀ x ∈ S, p x ≤ M) :
    Real.negMulLog (∑ x ∈ S, p x) + (∑ x ∈ S, p x) * Real.log q - finiteEntropy S p ≤
      q * M - ∑ x ∈ S, p x := by
  let s := ∑ x ∈ S, p x
  have hs : 0 ≤ s := Finset.sum_nonneg hp
  by_cases hMzero : M = 0
  · have hzero : ∀ x ∈ S, p x = 0 := fun x hx => le_antisymm (hMzero ▸ hbound x hx) (hp x hx)
    have hsumzero : ∑ x ∈ S, p x = 0 := Finset.sum_eq_zero hzero
    have hentropy : finiteEntropy S p = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp [hzero x hx, Real.negMulLog_def]
    simp [hsumzero, hentropy, hMzero, Real.negMulLog_def]
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
  have hlog := sum_mul_log_le_log_bound S p hp hbound
  have hentropy : finiteEntropy S p = -(∑ x ∈ S, p x * Real.log (p x)) := by
    simp [finiteEntropy, Real.negMulLog_def, neg_mul, Finset.sum_neg_distrib]
  change Real.negMulLog s + s * Real.log q - finiteEntropy S p ≤ q * M - s
  rw [hentropy]
  change -s * Real.log s + s * Real.log q - -(∑ x ∈ S, p x * Real.log (p x)) ≤ q * M - s
  change (∑ x ∈ S, p x * Real.log (p x)) ≤ s * Real.log M at hlog
  by_cases hszero : s = 0
  · have hlogzero : (∑ x ∈ S, p x * Real.log (p x)) ≤ 0 := by
      simpa only [hszero, zero_mul] using hlog
    simpa only [hszero, neg_zero, zero_mul, zero_add, sub_neg_eq_add, sub_zero] using
      hlogzero.trans (mul_nonneg hq.le hM)
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hszero)
  have hratio := Real.log_le_sub_one_of_pos (div_pos (mul_pos hq hMpos) hspos)
  rw [Real.log_div (mul_ne_zero hq.ne' hMpos.ne') hspos.ne', Real.log_mul hq.ne' hMpos.ne'] at hratio
  have hscaled := mul_le_mul_of_nonneg_left hratio hs
  have hcancel : s * (q * M / s) = q * M := by field_simp
  nlinarith

theorem finite_entropy_le_log_card {ι : Type*} (S : Finset ι) (p : ι → ℝ)
    (hp : ∀ x ∈ S, 0 ≤ p x) (hsum : ∑ x ∈ S, p x = 1) :
    finiteEntropy S p ≤ Real.log (S.card : ℝ) := by
  have hSne : S.Nonempty := by
    by_contra hS
    have he := Finset.not_nonempty_iff_eq_empty.mp hS
    norm_num [he] at hsum
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hSne
  have hpoint : ∀ x ∈ S,
      (S.card : ℝ) * Real.negMulLog (p x) ≤
        1 - (S.card : ℝ) * p x + p x * (S.card : ℝ) * Real.log (S.card : ℝ) := by
    intro x hx
    have hh := Real.negMulLog_le_one_sub_self (mul_nonneg hcard.le (hp x hx))
    rw [Real.negMulLog_mul] at hh
    change p x * (-(S.card : ℝ) * Real.log (S.card : ℝ)) +
      (S.card : ℝ) * Real.negMulLog (p x) ≤ 1 - (S.card : ℝ) * p x at hh
    nlinarith
  have htotal := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, mul_one, hsum, one_mul] at htotal
  apply (mul_le_mul_iff_of_pos_left hcard).mp
  simpa only [finiteEntropy, sub_self, zero_add] using htotal

noncomputable def finitePushforward {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (b : κ) : ℝ := ∑ a : ι with π a = b, p a

theorem finite_pushforward_sum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) : ∑ b : κ, finitePushforward p π b = ∑ a : ι, p a := by
  exact Finset.sum_fiberwise Finset.univ π p

theorem finite_entropy_projection_defect {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (M : κ → ℝ) {q : ℝ}
    (hp : ∀ a, 0 ≤ p a) (hq : 0 < q) (hM : ∀ b, 0 ≤ M b)
    (hbound : ∀ a, p a ≤ M (π a)) :
    finiteEntropy Finset.univ (finitePushforward p π) + (∑ a : ι, p a) * Real.log q -
      finiteEntropy Finset.univ p ≤ q * (∑ b : κ, M b) - ∑ a : ι, p a := by
  have hfiber : ∀ b : κ,
      Real.negMulLog (finitePushforward p π b) + finitePushforward p π b * Real.log q -
        finiteEntropy (Finset.univ.filter (fun a => π a = b)) p ≤ q * M b - finitePushforward p π b := by
    intro b
    apply finite_entropy_fiber_defect _ p (fun a _ => hp a) hq (hM b)
    intro a ha
    have heq := (Finset.mem_filter.mp ha).2
    simpa only [heq] using hbound a
  have htotal := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hfiber b)
  have hentropy : (∑ b : κ, finiteEntropy (Finset.univ.filter (fun a => π a = b)) p) =
      finiteEntropy Finset.univ p := Finset.sum_fiberwise Finset.univ π (fun a => Real.negMulLog (p a))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    hentropy, finite_pushforward_sum] at htotal
  exact htotal

theorem finite_pushforward_nonneg {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) (b : κ) :
    0 ≤ finitePushforward p π b := Finset.sum_nonneg (fun a _ => hp a)

theorem le_finite_pushforward {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) (a : ι) :
    p a ≤ finitePushforward p π (π a) := by
  exact Finset.single_le_sum (fun b _ => hp b) (by simp)

theorem finite_entropy_mono_projection {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) :
    finiteEntropy Finset.univ (finitePushforward p π) ≤ finiteEntropy Finset.univ p := by
  have hh := finite_entropy_projection_defect p π (finitePushforward p π) hp
    (show (0 : ℝ) < 1 by norm_num) (finite_pushforward_nonneg p π hp) (le_finite_pushforward p π hp)
  simp only [Real.log_one, mul_zero, add_zero, one_mul, finite_pushforward_sum, sub_self] at hh
  linarith

theorem finite_entropy_le_log_support {ι : Type*} [Fintype ι] (p : ι → ℝ) (S : Finset ι)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a : ι, p a = 1) (hzero : ∀ a, a ∉ S → p a = 0) :
    finiteEntropy Finset.univ p ≤ Real.log (S.card : ℝ) := by
  classical
  have hsum : ∑ a ∈ S, p a = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ S) (fun a _ ha => hzero a ha)]
    exact hmass
  have hentropy : finiteEntropy S p = finiteEntropy Finset.univ p := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro a _ ha
    simp [hzero a ha, Real.negMulLog_def]
  rw [← hentropy]
  exact finite_entropy_le_log_card S p (fun a _ => hp a) hsum

theorem finite_pushforward_comp {ι κ ν : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [DecidableEq ν] (p : ι → ℝ) (π : ι → κ) (σ : κ → ν) :
    finitePushforward (finitePushforward p π) σ = finitePushforward p (σ ∘ π) := by
  funext b
  unfold finitePushforward
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] using
    Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset ι)
      (Finset.univ.filter (fun a => σ a = b)) π p

theorem finite_entropy_pushforward_le_log_image {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (p : ι → ℝ) (π : ι → κ) (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a : ι, p a = 1) :
    finiteEntropy Finset.univ (finitePushforward p π) ≤
      Real.log ((Finset.univ.image π).card : ℝ) := by
  classical
  apply finite_entropy_le_log_support (finitePushforward p π) (Finset.univ.image π)
    (finite_pushforward_nonneg p π hp) (by rw [finite_pushforward_sum, hmass])
  intro b hb
  have he : Finset.univ.filter (fun a => π a = b) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, (Finset.mem_filter.mp ha).2⟩)
  simp only [finitePushforward, he, Finset.sum_empty]

def dyadicIndex (k n : ℕ) : Fin (2 ^ k) := ⟨n % 2 ^ k, Nat.mod_lt n (by positivity)⟩

noncomputable def dyadicDistribution {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (k : ℕ) :
    Fin (2 ^ k) → ℝ := finitePushforward p (fun a => dyadicIndex k (f a))

noncomputable def dyadicEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (k : ℕ) : ℝ :=
  finiteEntropy Finset.univ (dyadicDistribution p f k)

theorem dyadic_distribution_project {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    {u v : ℕ} (huv : u ≤ v) :
    finitePushforward (dyadicDistribution p f v) (fun a => dyadicIndex u a.val) = dyadicDistribution p f u := by
  rw [dyadicDistribution, finite_pushforward_comp]
  unfold dyadicDistribution
  congr 1
  funext a
  apply Fin.ext
  exact Nat.mod_mod_of_dvd (f a) (pow_dvd_pow 2 huv)

theorem weighted_sum_sq_le {ι : Type*} (S : Finset ι) (w t : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hmass : ∑ i ∈ S, w i = 1) :
    (∑ i ∈ S, w i * t i) ^ 2 ≤ ∑ i ∈ S, w i * (t i) ^ 2 := by
  have hleft : (∑ i ∈ S, Real.sqrt (w i) * (Real.sqrt (w i) * t i)) = ∑ i ∈ S, w i * t i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, Real.mul_self_sqrt (hw i hi)]
  have hfirst : (∑ i ∈ S, (Real.sqrt (w i)) ^ 2) = 1 := by
    calc
      _ = ∑ i ∈ S, w i := Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hw i hi))
      _ = _ := hmass
  have hsecond : (∑ i ∈ S, (Real.sqrt (w i) * t i) ^ 2) = ∑ i ∈ S, w i * (t i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * t i)
  rwa [hleft, hfirst, hsecond, one_mul] at hh


end Erdos18c
-- END external module FiniteLaw

-- BEGIN external module BinaryEntropy

/-!
Binary entropy estimates used in the harmonic-shift proof.  Finite-law
infrastructure is credited in FiniteLaw.lean; these analytic inequalities
are the scalar steps of the new manuscript.
-/

open Finset
namespace Erdos18c

theorem negMulLog_le_sqrt {p : ℝ} (hp : 0 ≤ p) :
    Real.negMulLog p ≤ (2 / Real.exp 1) * Real.sqrt p := by
  by_cases hp0 : p = 0
  · simp [hp0, Real.negMulLog_def]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  let t := -(Real.log p) / 2
  have he : Real.exp (-t) = Real.sqrt p := by
    apply (Real.log_injOn_pos (Real.exp_pos _) (Real.sqrt_pos.2 hp'))
    rw [Real.log_exp, Real.log_sqrt hp]
    dsimp [t]
    ring
  have hh := Real.mul_exp_neg_le_exp_neg_one t
  have ht : Real.negMulLog p = 2 * Real.sqrt p * (t * Real.exp (-t)) := by
    rw [he]
    dsimp [t]
    rw [Real.negMulLog_def]
    change -p * Real.log p = _
    calc
      -p * Real.log p = -(Real.sqrt p ^ 2) * Real.log p := by rw [Real.sq_sqrt hp]
      _ = _ := by ring
  rw [ht]
  have hscaled := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * Real.sqrt p)
  simpa only [Real.exp_neg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled

theorem binEntropy_le_two_sqrt_min {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.binEntropy p ≤ 2 * Real.sqrt (min p (1-p)) := by
  wlog hhalf : p ≤ 1 / 2 generalizing p
  · have h := this (sub_nonneg.mpr hp1) (by linarith : 1-p ≤ 1) (by linarith : 1-p ≤ 1/2)
    simpa [Real.binEntropy_one_sub, min_comm] using h
  have hmin : min p (1-p) = p := min_eq_left (by linarith)
  rw [hmin, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have hfirst := negMulLog_le_sqrt hp
  have hsecond : Real.negMulLog (1-p) ≤ p := by
    have := Real.negMulLog_le_one_sub_self (sub_nonneg.mpr hp1)
    linarith
  have hroot : p ≤ Real.sqrt p := by
    have hs := Real.sq_sqrt hp
    have hsn := Real.sqrt_nonneg p
    nlinarith [mul_nonneg hp (sub_nonneg.mpr hp1)]
  have hexp : 2 / Real.exp 1 ≤ 1 := (div_le_one (Real.exp_pos _)).mpr (le_of_lt Real.exp_one_gt_two)
  have hh := mul_le_mul_of_nonneg_right hexp (Real.sqrt_nonneg p)
  linarith

theorem two_min_le_binEntropy {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    2 * min p (1-p) * Real.log 2 ≤ Real.binEntropy p := by
  wlog hhalf : p ≤ 1 / 2 generalizing p
  · have h := this (sub_nonneg.mpr hp1) (by linarith : 1-p ≤ 1) (by linarith : 1-p ≤ 1/2)
    simpa [Real.binEntropy_one_sub, min_comm] using h
  have hconc := Real.strictConcave_binEntropy.concaveOn.2
    (show (0:ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (2:ℝ)⁻¹ ∈ Set.Icc 0 1 by norm_num)
    (show 0 ≤ 1 - 2*p by linarith)
    (show 0 ≤ 2*p by linarith)
    (show (1-2*p) + 2*p = 1 by ring)
  norm_num only [smul_eq_mul, mul_zero, zero_add, Real.binEntropy_zero, mul_zero,
    zero_add, Real.binEntropy_two_inv] at hconc
  have hhalfentropy : Real.binEntropy (1/2) = Real.log 2 := by
    convert Real.binEntropy_two_inv using 1
    norm_num
  rw [hhalfentropy] at hconc
  have harg : (2*p)*(1/2) = p := by ring
  rw [harg] at hconc
  rw [min_eq_left (by linarith : p ≤ 1-p)]
  exact hconc

noncomputable def pairEntropy (x y : ℝ) : ℝ :=
  Real.negMulLog x + Real.negMulLog y - Real.negMulLog (x+y)

theorem pairEntropy_eq (x y : ℝ) :
    pairEntropy x y = (x+y) * Real.binEntropy (x/(x+y)) := by
  by_cases hs : x+y = 0
  · have hy : y = -x := by linarith
    simp [pairEntropy, hy, Real.negMulLog_def, Real.log_neg_eq_log]
  have hxid := Real.negMulLog_mul (x+y) (x/(x+y))
  have hyid := Real.negMulLog_mul (x+y) (y/(x+y))
  rw [mul_div_cancel₀ _ hs] at hxid hyid
  have hratio : 1-x/(x+y) = y/(x+y) := by field_simp; ring
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hratio, mul_add]
  unfold pairEntropy
  have hsum : x/(x+y) + y/(x+y) = 1 := by field_simp
  have hsum' := congrArg (fun t : ℝ => t * Real.negMulLog (x+y)) hsum
  nlinarith

theorem binary_probability_bounds {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ x/(x+y) ∧ x/(x+y) ≤ 1 := by
  constructor
  · positivity
  · by_cases hs : x+y=0
    · simp [hs]
    · exact (div_le_one (lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hs))).mpr (by linarith)

theorem mass_mul_min_probability {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x+y) * min (x/(x+y)) (1-x/(x+y)) = min x y := by
  by_cases hs : x+y=0
  · have hx0 : x=0 := by linarith
    have hy0 : y=0 := by linarith
    simp [hx0,hy0]
  have hsp : 0 < x+y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hs)
  have hratio : 1-x/(x+y)=y/(x+y) := by field_simp; ring
  rw [hratio]
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy, min_eq_left ((div_le_div_iff_of_pos_right hsp).mpr hxy)]
    exact mul_div_cancel₀ _ hs
  · have hyx := le_of_not_ge hxy
    rw [min_eq_right hyx, min_eq_right ((div_le_div_iff_of_pos_right hsp).mpr hyx)]
    exact mul_div_cancel₀ _ hs

theorem pairEntropy_lower {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * min x y * Real.log 2 ≤ pairEntropy x y := by
  rw [pairEntropy_eq]
  have hp := binary_probability_bounds hx hy
  have hh := mul_le_mul_of_nonneg_left (two_min_le_binEntropy hp.1 hp.2) (add_nonneg hx hy)
  calc
    2 * min x y * Real.log 2 = (x+y) * (2 * min (x/(x+y)) (1-x/(x+y)) * Real.log 2) := by
      rw [← mass_mul_min_probability hx hy]
      ring
    _ ≤ _ := hh

theorem binary_entropy_sq_bound {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.binEntropy p ^ 2 ≤ 4 * min p (1-p) := by
  have hh := pow_le_pow_left₀ (Real.binEntropy_nonneg hp hp1)
    (binEntropy_le_two_sqrt_min hp hp1) 2
  have hm : 0 ≤ min p (1-p) := le_min hp (sub_nonneg.mpr hp1)
  nlinarith [Real.sq_sqrt hm]

theorem sum_pairEntropy_sq_le {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hmass : ∑ i, (x i+y i) = 1) :
    (∑ i, pairEntropy (x i) (y i)) ^ 2 ≤ 4 * ∑ i, min (x i) (y i) := by
  have hcs := weighted_sum_sq_le univ (fun i => x i+y i)
    (fun i => Real.binEntropy (x i/(x i+y i))) (fun i _ => add_nonneg (hx i) (hy i)) hmass
  simp_rw [← pairEntropy_eq] at hcs
  apply hcs.trans
  calc
    (∑ i, (x i+y i) * Real.binEntropy (x i/(x i+y i)) ^ 2) ≤
        ∑ i, (x i+y i) * (4 * min (x i/(x i+y i)) (1-x i/(x i+y i))) := by
      apply sum_le_sum
      intro i _
      have hp := binary_probability_bounds (hx i) (hy i)
      exact mul_le_mul_of_nonneg_left (binary_entropy_sq_bound hp.1 hp.2) (add_nonneg (hx i) (hy i))
    _ = 4 * ∑ i, min (x i) (y i) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      rw [← mass_mul_min_probability (hx i) (hy i)]
      ring

theorem sum_pairEntropy_lower {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    (2 * ∑ i, min (x i) (y i)) * Real.log 2 ≤ ∑ i, pairEntropy (x i) (y i) := by
  have hh := sum_le_sum (fun i (_ : i ∈ univ) => pairEntropy_lower (hx i) (hy i))
  simpa only [← sum_mul, ← mul_sum] using hh


end Erdos18c
-- END external module BinaryEntropy

-- BEGIN external module DivisorRepresentations

/-!
Adapted from Kohlmeyer--Kruer Erdos18b.lean (unchanged source SHA-256
4d6ee89617415288e9f127beb3c0e0211c011f891889fcb43d0e16373bd14088).
The definitions and elementary representation operations retain their source
names inside Erdos18c. The new logarithmic estimates are developed separately.
-/

open Finset Filter
namespace Erdos18c
def HasFactorialDivisorMultiset (F R u : ℕ) : Prop :=
  ∃ s : Multiset ℕ, (∀ d ∈ s, d ∣ F.factorial) ∧ s.sum = R ∧ s.card ≤ u

theorem factorial_multiset_zero (F u : ℕ) : HasFactorialDivisorMultiset F 0 u := by
  exact ⟨0, by simp, by simp, by simp⟩

theorem factorial_multiset_singleton {F R : ℕ} (hR : R ∣ F.factorial) :
    HasFactorialDivisorMultiset F R 1 := by
  exact ⟨{R}, by simpa using hR, by simp, by simp⟩

theorem factorial_multiset_mono {F G R u v : ℕ}
    (h : HasFactorialDivisorMultiset F R u) (hFG : F ≤ G) (huv : u ≤ v) :
    HasFactorialDivisorMultiset G R v := by
  obtain ⟨s, hs, hsum, hcard⟩ := h
  exact ⟨s, fun d hd => (hs d hd).trans (Nat.factorial_dvd_factorial hFG),
    hsum, hcard.trans huv⟩

theorem factorial_multiset_to_distinct {F R u : ℕ}
    (h : HasFactorialDivisorMultiset F R u) :
    ShortSum (F + 2 * u).factorial R u := by
  obtain ⟨s, hs, hsum, hcard⟩ := h
  have hrep := distinctify_factorial_divisors s F hs
  rw [hsum] at hrep
  exact shortSum_mono_count
    (shortSum_mono_host (Nat.factorial_dvd_factorial (by omega))
      (Nat.factorial_ne_zero (F + 2 * u)) hrep) hcard

theorem factorial_multiset_add {F R S u v : ℕ}
    (hR : HasFactorialDivisorMultiset F R u)
    (hS : HasFactorialDivisorMultiset F S v) :
    HasFactorialDivisorMultiset F (R + S) (u + v) := by
  obtain ⟨s, hs, hsum, hcard⟩ := hR
  obtain ⟨t, ht, htsum, htcard⟩ := hS
  refine ⟨s + t, ?_, ?_, ?_⟩
  · intro d hd
    rcases Multiset.mem_add.mp hd with hd | hd
    · exact hs d hd
    · exact ht d hd
  · simp only [Multiset.sum_add, hsum, htsum]
  · simpa only [Multiset.card_add] using Nat.add_le_add hcard htcard

theorem factorial_multiset_scale {F G q R u : ℕ}
    (hq : q ∣ F.factorial) (h : HasFactorialDivisorMultiset G R u) :
    HasFactorialDivisorMultiset (F + G) (q * R) u := by
  obtain ⟨s, hs, hsum, hcard⟩ := h
  refine ⟨s.map (fun d => q * d), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hx
    exact (mul_dvd_mul hq (hs d hd)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add F G)
  · have hmul := Multiset.sum_map_mul_left (s := s) (a := q) (f := id)
    simpa [hsum] using hmul
  · simpa only [Multiset.card_map] using hcard


def binaryLength (R : ℕ) : ℕ := Nat.log 2 R + 1

theorem binaryLength_pos (R : ℕ) : 0 < binaryLength R := by simp [binaryLength]

end Erdos18c
-- END external module DivisorRepresentations

-- BEGIN external module DivisorDigits

/-!
Factorial digits and disjoint binary blocks adapted from Kohlmeyer--Kruer,
Erdos18b.lean, SHA-256
4d6ee89617415288e9f127beb3c0e0211c011f891889fcb43d0e16373bd14088.
The original source proves (b). The linear-host quantitative count needed
for (c) is supplied separately in this development.
-/
open Finset Filter
namespace Erdos18c
def shortFactorialDigits (F l : ℕ) : Finset ℕ :=
  insert 0 (F.factorial.divisors.filter (fun d => d < 2 ^ l))

theorem mem_shortFactorialDigits {F l d : ℕ} :
    d ∈ shortFactorialDigits F l ↔ d < 2 ^ l ∧ (d = 0 ∨ d ∣ F.factorial) := by
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with hz | hd
    · exact ⟨by rw [hz]; positivity, Or.inl hz⟩
    · obtain ⟨hdiv, hlt⟩ := Finset.mem_filter.mp hd
      exact ⟨hlt, Or.inr (Nat.dvd_of_mem_divisors hdiv)⟩
  · rintro ⟨hlt, hz | hdvd⟩
    · exact Finset.mem_insert.mpr (Or.inl hz)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hdvd, Nat.factorial_ne_zero F⟩, hlt⟩))

theorem shortFactorialDigits_small_integers {F l : ℕ} :
    min (F + 1) (2 ^ l) ≤ (shortFactorialDigits F l).card := by
  have hsub : Finset.range (min (F + 1) (2 ^ l)) ⊆ shortFactorialDigits F l := by
    intro d hd
    have hdlt := Finset.mem_range.mp hd
    apply mem_shortFactorialDigits.mpr
    refine ⟨lt_of_lt_of_le hdlt (min_le_right _ _), ?_⟩
    by_cases hz : d = 0
    · exact Or.inl hz
    · exact Or.inr (Nat.dvd_factorial (by omega)
        (by have := min_le_left (F + 1) (2 ^ l); omega))
  simpa only [Finset.card_range] using Finset.card_le_card hsub

theorem prime_dvd_prime_product_iff {p : ℕ} (hp : Nat.Prime p)
    (s : Finset ℕ) (hs : ∀ q ∈ s, Nat.Prime q) :
    p ∣ s.prod id ↔ p ∈ s := by
  constructor
  · intro h
    obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp h
    have heq : q = p := (hs q hq).dvd_iff_eq hp.ne_one |>.mp hpq
    exact heq ▸ hq
  · exact Finset.dvd_prod_of_mem id

theorem prime_products_injective {s t : Finset ℕ}
    (hs : ∀ p ∈ s, Nat.Prime p) (ht : ∀ p ∈ t, Nat.Prime p)
    (heq : s.prod id = t.prod id) : s = t := by
  apply Finset.Subset.antisymm
  · intro p hp
    apply (prime_dvd_prime_product_iff (hs p hp) t ht).mp
    rw [← heq]
    exact Finset.dvd_prod_of_mem id hp
  · intro p hp
    apply (prime_dvd_prime_product_iff (ht p hp) s hs).mp
    rw [heq]
    exact Finset.dvd_prod_of_mem id hp

theorem prime_subset_product_dvd_factorial {F : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Nat.primesLE F) : s.prod id ∣ F.factorial := by
  rw [← Finset.prod_Ico_id_eq_factorial F]
  apply Finset.prod_dvd_prod_of_subset s (Finset.Ico 1 (F + 1)) id
  intro p hp
  obtain ⟨hpF, hprime⟩ := Nat.mem_primesLE.mp (hs hp)
  exact Finset.mem_Ico.mpr ⟨by have := hprime.two_le; omega, by omega⟩

theorem shortFactorialDigits_choose_lower {F l v : ℕ} (hheight : F ^ v < 2 ^ l) :
    (Nat.primeCounting F).choose v ≤ (shortFactorialDigits F l).card := by
  have hmap : Set.MapsTo (fun s : Finset ℕ => s.prod id)
      ((Nat.primesLE F).powersetCard v) (shortFactorialDigits F l) := by
    intro s hs
    obtain ⟨hs, hcard⟩ := Finset.mem_powersetCard.mp hs
    apply mem_shortFactorialDigits.mpr
    refine ⟨?_, Or.inr (prime_subset_product_dvd_factorial hs)⟩
    have hprod : s.prod id ≤ F ^ v := by
      calc
        s.prod id ≤ ∏ _ ∈ s, F := Finset.prod_le_prod (fun p hp => Nat.zero_le p) (fun p hp => Nat.le_of_mem_primesLE (hs hp))
        _ = F ^ v := by rw [Finset.prod_const, hcard]
    exact hprod.trans_lt hheight
  have hinj : Set.InjOn (fun s : Finset ℕ => s.prod id) ((Nat.primesLE F).powersetCard v) := by
    intro s hs t ht heq
    apply prime_products_injective _ _ heq
    · intro p hp
      exact Nat.prime_of_mem_primesLE ((Finset.mem_powersetCard.mp hs).1 hp)
    · intro p hp
      exact Nat.prime_of_mem_primesLE ((Finset.mem_powersetCard.mp ht).1 hp)
  simpa only [Finset.card_powersetCard, Nat.primesLE_card_eq_primeCounting] using
    Finset.card_le_card_of_injOn _ hmap hinj

theorem choose_lower_half_ratio {n v : ℕ} (hv : 0 < v) (hvn : 2 * v ≤ n) :
    ((n : ℝ) / 2 / (v : ℝ)) ^ v ≤ (n.choose v : ℝ) := by
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
  have hnsub : (n : ℝ) / 2 ≤ ((n + 1 - v : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : v ≤ n + 1), Nat.cast_add, Nat.cast_one]
    have hh : (2 : ℝ) * v ≤ n := by exact_mod_cast hvn
    linarith
  have hfac : (v.factorial : ℝ) ≤ (v : ℝ) ^ v := by exact_mod_cast Nat.factorial_le_pow v
  calc
    ((n : ℝ) / 2 / (v : ℝ)) ^ v = ((n : ℝ) / 2) ^ v / (v : ℝ) ^ v := div_pow _ _ _
    _ ≤ (((n + 1 - v : ℕ) : ℝ) ^ v) / (v : ℝ) ^ v := by
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hnsub v) (by positivity)
    _ ≤ (((n + 1 - v : ℕ) : ℝ) ^ v) / (v.factorial : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
    _ ≤ (n.choose v : ℝ) := Nat.pow_le_choose v n


theorem half_binaryLength_rpow_le {F : ℕ} (hF : 2 ≤ F) :
    (2 : ℝ) ^ ((binaryLength F : ℝ) / 2) ≤ (F : ℝ) := by
  have hlog : 1 ≤ Nat.log 2 F := Nat.le_log_of_pow_le (by decide) (by simpa using hF)
  have hlen : (binaryLength F : ℝ) / 2 ≤ (Nat.log 2 F : ℝ) := by
    simp only [binaryLength, Nat.cast_add, Nat.cast_one]
    have hh : (1 : ℝ) ≤ Nat.log 2 F := by exact_mod_cast hlog
    linarith
  calc
    (2 : ℝ) ^ ((binaryLength F : ℝ) / 2) ≤ (2 : ℝ) ^ (Nat.log 2 F : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hlen
    _ = ((2 ^ Nat.log 2 F : ℕ) : ℝ) := by simp
    _ ≤ (F : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : F ≠ 0)

theorem shortFactorialDigits_uniform_lower {F k : ℕ} {δ : ℝ}
    (hF : 2 ≤ F) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hprimes : (2 * (k : ℝ)) * (F : ℝ) ^ δ ≤ (Nat.primeCounting F : ℝ)) :
    ∀ l : ℕ, 1 ≤ l → l ≤ k →
      (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (shortFactorialDigits F l).card := by
  intro l hlpos hlk
  let a := binaryLength F
  have ha : 0 < a := binaryLength_pos F
  have hFa : (2 : ℝ) ^ ((a : ℝ) / 2) ≤ (F : ℝ) := half_binaryLength_rpow_le hF
  by_cases hsmall : l ≤ 4 * a
  · have hsmallreal : (l : ℝ) ≤ 4 * (a : ℝ) := by exact_mod_cast hsmall
    have hfirst : (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (F + 1 : ℕ) := by
      calc
        (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (2 : ℝ) ^ ((a : ℝ) / 2) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          nlinarith [mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
        _ ≤ (F : ℝ) := hFa
        _ ≤ (F + 1 : ℕ) := by exact_mod_cast Nat.le_succ F
    have hsecond : (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ ((2 ^ l : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
    have hmin : (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (min (F + 1) (2 ^ l) : ℕ) := by
      rw [Nat.cast_min]
      exact le_min hfirst hsecond
    exact hmin.trans (by exact_mod_cast shortFactorialDigits_small_integers (F := F) (l := l))
  · let v := l / (2 * a)
    have hvpos : 0 < v := Nat.div_pos (by omega) (by omega)
    have hvle : v ≤ k := (Nat.div_le_self l (2 * a)).trans hlk
    have hmul : 2 * a * v ≤ l := Nat.mul_div_le l (2 * a)
    have hupper : l < 2 * a * (v + 1) := Nat.lt_mul_div_succ l (by omega)
    have halower : l ≤ 4 * a * v := by nlinarith
    have hheight : F ^ v < 2 ^ l := by
      calc
        F ^ v ≤ (2 ^ a) ^ v := Nat.pow_le_pow_left
          (Nat.lt_pow_succ_log_self (by decide : 1 < 2) F).le v
        _ = 2 ^ (a * v) := (pow_mul _ _ _).symm
        _ < 2 ^ l := Nat.pow_lt_pow_right (by decide : 1 < 2) (by nlinarith)
    have hFpow : 1 ≤ (F : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ F by omega)) hδ.le
    have htwov : 2 * v ≤ Nat.primeCounting F := by
      have hkr : (v : ℝ) ≤ k := by exact_mod_cast hvle
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hreal : 2 * (v : ℝ) ≤ (Nat.primeCounting F : ℝ) := by nlinarith
      exact_mod_cast hreal
    have hratio : (F : ℝ) ^ δ ≤ (Nat.primeCounting F : ℝ) / 2 / (v : ℝ) := by
      apply (le_div_iff₀ (by exact_mod_cast hvpos : (0 : ℝ) < v)).mpr
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      have hkr : (v : ℝ) ≤ k := by exact_mod_cast hvle
      have hF0 : 0 ≤ (F : ℝ) ^ δ := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hkr hF0]
    have halowerreal : (l : ℝ) ≤ 4 * (a : ℝ) * (v : ℝ) := by exact_mod_cast halower
    calc
      (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (2 : ℝ) ^ (((a : ℝ) / 2 * δ) * (v : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_left halowerreal hδ.le]
      _ = (((2 : ℝ) ^ ((a : ℝ) / 2)) ^ δ) ^ v := by
        rw [Real.rpow_mul_natCast (by norm_num), Real.rpow_mul (by norm_num)]
      _ ≤ ((F : ℝ) ^ δ) ^ v :=
        pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by positivity) hFa hδ.le) v
      _ ≤ ((Nat.primeCounting F : ℝ) / 2 / (v : ℝ)) ^ v :=
        pow_le_pow_left₀ (by positivity) hratio v
      _ ≤ ((Nat.primeCounting F).choose v : ℝ) := choose_lower_half_ratio hvpos htwov
      _ ≤ (shortFactorialDigits F l).card := by exact_mod_cast shortFactorialDigits_choose_lower hheight


def binaryAppend (A D : Finset ℕ) (b : ℕ) : Finset ℕ :=
  (A ×ˢ D).image (fun p => p.1 + 2 ^ b * p.2)

def natResidueFiber (A : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  A.filter (fun x => Nat.ModEq q x r)

noncomputable def natResidueMass (A : Finset ℕ) (q r : ℕ) : ℝ :=
  ((natResidueFiber A q r).card : ℝ) / (A.card : ℝ)

theorem binary_append_injective {A D : Finset ℕ} {b : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 + 2 ^ b * p.2) (A ×ˢ D : Finset (ℕ × ℕ)) := by
  intro p hp s hs heq
  change p.1 + 2 ^ b * p.2 = s.1 + 2 ^ b * s.2 at heq
  have hpA := hA p.1 (Finset.mem_product.mp hp).1
  have hsA := hA s.1 (Finset.mem_product.mp hs).1
  have hmod := congrArg (fun n => n % (2 ^ b)) heq
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hpA, Nat.mod_eq_of_lt hsA] at hmod
  have hmul : 2 ^ b * p.2 = 2 ^ b * s.2 := by omega
  have hright := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ b) hmul
  exact Prod.ext hmod hright

theorem binary_append_card {A D : Finset ℕ} {b : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) : (binaryAppend A D b).card = A.card * D.card := by
  rw [binaryAppend, Finset.card_image_of_injOn (binary_append_injective hA), Finset.card_product]

theorem binary_append_nonempty {A D : Finset ℕ} {b : ℕ}
    (hA : A.Nonempty) (hD : D.Nonempty) : (binaryAppend A D b).Nonempty := by
  exact (hA.product hD).image _

theorem binary_append_lt {A D : Finset ℕ} {b l : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hD : ∀ d ∈ D, d < 2 ^ l) :
    ∀ x ∈ binaryAppend A D b, x < 2 ^ (b + l) := by
  intro x hx
  obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hx
  have ha := hA a (Finset.mem_product.mp had).1
  have hd := hD d (Finset.mem_product.mp had).2
  rw [pow_add]
  nlinarith [mul_le_mul_of_nonneg_left (show d + 1 ≤ 2 ^ l by omega) (Nat.zero_le (2 ^ b))]

theorem nat_residue_fiber_mono_modulus {A : Finset ℕ} {q Q r : ℕ} (hq : q ∣ Q) :
    natResidueFiber A Q r ⊆ natResidueFiber A q r := by
  intro x hx
  obtain ⟨hx, hmod⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx, hmod.of_dvd hq⟩

theorem nat_residue_fiber_card_le_one {A : Finset ℕ} {q r : ℕ}
    (hA : ∀ x ∈ A, x < q) : (natResidueFiber A q r).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxA, hxmod⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyA, hymod⟩ := Finset.mem_filter.mp hy
  have hxy := hxmod.trans hymod.symm
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt (hA x hxA), Nat.mod_eq_of_lt (hA y hyA)] using hxy

theorem binary_append_residue_fiber {A D : Finset ℕ} {b q r : ℕ} (hq : q ∣ 2 ^ b) :
    natResidueFiber (binaryAppend A D b) q r = binaryAppend (natResidueFiber A q r) D b := by
  have hequiv (a d : ℕ) : Nat.ModEq q (a + 2 ^ b * d) r ↔ Nat.ModEq q a r := by
    have hh : Nat.ModEq q (a + 2 ^ b * d) a := by
      simpa only [add_zero] using (Nat.ModEq.refl a).add ((hq.trans (dvd_mul_right _ _)).modEq_zero_nat)
    exact ⟨fun h => hh.symm.trans h, fun h => hh.trans h⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hm⟩ := Finset.mem_filter.mp hx
    obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨(a, d), Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨(Finset.mem_product.mp had).1, (hequiv a d).mp hm⟩,
        (Finset.mem_product.mp had).2⟩, rfl⟩
  · intro hx
    obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hd⟩ := Finset.mem_product.mp had
    obtain ⟨ha, hm⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(a, d), Finset.mem_product.mpr ⟨ha, hd⟩, rfl⟩,
      (hequiv a d).mpr hm⟩

theorem binary_append_residue_fiber_card {A D : Finset ℕ} {b q r : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hq : q ∣ 2 ^ b) :
    (natResidueFiber (binaryAppend A D b) q r).card = (natResidueFiber A q r).card * D.card := by
  rw [binary_append_residue_fiber hq]
  exact binary_append_card (fun x hx => hA x (Finset.mem_filter.mp hx).1)

theorem binary_append_residue_mass {A D : Finset ℕ} {b q r : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hD : D.Nonempty) (hq : q ∣ 2 ^ b) :
    natResidueMass (binaryAppend A D b) q r = natResidueMass A q r := by
  have hDc : (D.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hD
  unfold natResidueMass
  rw [binary_append_residue_fiber_card hA hq, binary_append_card hA, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ hDc

theorem binary_append_residue_mass_high {A D : Finset ℕ} {b j r : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hne : A.Nonempty) (hD : D.Nonempty) (hj : b ≤ j) :
    natResidueMass (binaryAppend A D b) (2 ^ j) r ≤ 1 / (A.card : ℝ) := by
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hne
  calc
    natResidueMass (binaryAppend A D b) (2 ^ j) r ≤
        natResidueMass (binaryAppend A D b) (2 ^ b) r := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast Finset.card_le_card (nat_residue_fiber_mono_modulus (pow_dvd_pow 2 hj))
    _ = natResidueMass A (2 ^ b) r := binary_append_residue_mass hA hD (dvd_refl _)
    _ ≤ 1 / (A.card : ℝ) := by
      apply div_le_div_of_nonneg_right _ hAc.le
      exact_mod_cast nat_residue_fiber_card_le_one hA

theorem nat_residue_fiber_range_card_le {q N r : ℕ} (hq : 0 < q) :
    (natResidueFiber (Finset.range (q * N)) q r).card ≤ N := by
  have hmap : Set.MapsTo (fun x : ℕ => x / q)
      (natResidueFiber (Finset.range (q * N)) q r) (Finset.range N) := by
    intro x hx
    have hxlt := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hq).mpr (by simpa only [mul_comm] using hxlt))
  have hinj : Set.InjOn (fun x : ℕ => x / q)
      (natResidueFiber (Finset.range (q * N)) q r) := by
    intro x hx y hy heq
    change x / q = y / q at heq
    have hmod := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    change x % q = y % q at hmod
    have hxdiv := Nat.mod_add_div x q
    have hydiv := Nat.mod_add_div y q
    rw [heq, hmod] at hxdiv
    omega
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn _ hmap hinj

theorem nat_residue_fiber_bounded_card_le {A : Finset ℕ} {b j r : ℕ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hj : j ≤ b) :
    (natResidueFiber A (2 ^ j) r).card ≤ 2 ^ (b - j) := by
  have hpow : 2 ^ b = 2 ^ j * 2 ^ (b - j) := by rw [← pow_add, Nat.add_sub_of_le hj]
  have hsub : natResidueFiber A (2 ^ j) r ⊆ natResidueFiber (Finset.range (2 ^ b)) (2 ^ j) r := by
    intro x hx
    obtain ⟨hxA, hmod⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hA x hxA), hmod⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [hpow]
  exact nat_residue_fiber_range_card_le (by positivity)

def initialOddDigits (b : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ (b - 1))).image (fun i => 2 * i + 1)

theorem initial_odd_digits_card (b : ℕ) : (initialOddDigits b).card = 2 ^ (b - 1) := by
  rw [initialOddDigits, Finset.card_image_of_injective]
  · exact Finset.card_range _
  · intro x y h
    change 2 * x + 1 = 2 * y + 1 at h
    omega

theorem initial_odd_digits_nonempty (b : ℕ) : (initialOddDigits b).Nonempty := by
  apply Finset.card_pos.mp
  rw [initial_odd_digits_card]
  positivity

theorem initial_odd_digits_lt {b : ℕ} (hb : 0 < b) :
    ∀ x ∈ initialOddDigits b, x < 2 ^ b := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have hi := Finset.mem_range.mp hi
  have hp : 2 ^ b = 2 * 2 ^ (b - 1) := by rw [← pow_succ', Nat.sub_add_cancel hb]
  rw [hp]
  omega

theorem initial_odd_digits_odd {b x : ℕ} (hx : x ∈ initialOddDigits b) : Odd x := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨i, by ring⟩

theorem initial_odd_digits_entropy {b : ℕ} {c : ℝ} (hb : 2 ≤ b) (hc : c ≤ 1 / 2) :
    (2 : ℝ) ^ (c * (b : ℝ)) ≤ (initialOddDigits b).card := by
  rw [initial_odd_digits_card, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
  have hbr : (2 : ℝ) ≤ b := by exact_mod_cast hb
  nlinarith [mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]

theorem initial_odd_digits_spread {b j r : ℕ} {c : ℝ}
    (hb : 2 ≤ b) (hj : 2 ≤ j) (hjb : j ≤ b) (hc : c ≤ 1) :
    natResidueMass (initialOddDigits b) (2 ^ j) r ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ)) := by
  have hcard := nat_residue_fiber_bounded_card_le (r := r)
    (initial_odd_digits_lt (by omega : 0 < b)) hjb
  unfold natResidueMass
  rw [initial_odd_digits_card]
  calc
    ((natResidueFiber (initialOddDigits b) (2 ^ j) r).card : ℝ) / ((2 ^ (b - 1) : ℕ) : ℝ) ≤
        ((2 ^ (b - j) : ℕ) : ℝ) / ((2 ^ (b - 1) : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ = (2 : ℝ) ^ (1 - (j : ℝ)) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
        ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Nat.cast_sub hjb,
        Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_one]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
      nlinarith [mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

theorem binary_append_entropy {A D : Finset ℕ} {b l : ℕ} {c : ℝ}
    (hA : ∀ x ∈ A, x < 2 ^ b)
    (hcA : (2 : ℝ) ^ (c * (b : ℝ)) ≤ A.card)
    (hcD : (2 : ℝ) ^ (c * (l : ℝ)) ≤ D.card) :
    (2 : ℝ) ^ (c * ((b + l : ℕ) : ℝ)) ≤ (binaryAppend A D b).card := by
  rw [binary_append_card hA, Nat.cast_mul, Nat.cast_add, mul_add, Real.rpow_add (by norm_num)]
  exact mul_le_mul hcA hcD (by positivity) (Nat.cast_nonneg _)

theorem binary_append_spread {A D : Finset ℕ} {b l : ℕ} {c : ℝ}
    (hA : ∀ x ∈ A, x < 2 ^ b) (hne : A.Nonempty) (hD : D.Nonempty)
    (hl : l ≤ b) (hc : 0 ≤ c)
    (hcA : (2 : ℝ) ^ (c * (b : ℝ)) ≤ A.card)
    (hspread : ∀ j : ℕ, 2 ≤ j → j ≤ b → ∀ r : ℕ,
      natResidueMass A (2 ^ j) r ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ))) :
    ∀ j : ℕ, 2 ≤ j → j ≤ b + l → ∀ r : ℕ,
      natResidueMass (binaryAppend A D b) (2 ^ j) r ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ)) := by
  intro j hj hjbl r
  by_cases hjb : j ≤ b
  · rw [binary_append_residue_mass hA hD (pow_dvd_pow 2 hjb)]
    exact hspread j hj hjb r
  · calc
      natResidueMass (binaryAppend A D b) (2 ^ j) r ≤ 1 / (A.card : ℝ) :=
        binary_append_residue_mass_high hA hne hD (by omega)
      _ ≤ 1 / (2 : ℝ) ^ (c * (b : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) hcA
      _ = (2 : ℝ) ^ (-(c * (b : ℝ))) := by rw [Real.rpow_neg (by norm_num), one_div]
      _ ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hltwo : (j : ℝ) ≤ 2 * (b : ℝ) := by exact_mod_cast (show j ≤ 2 * b by omega)
        nlinarith [mul_le_mul_of_nonneg_left hltwo hc]

theorem short_factorial_digits_nonempty (F l : ℕ) : (shortFactorialDigits F l).Nonempty := by
  exact ⟨0, Finset.mem_insert_self _ _⟩

theorem short_factorial_digits_entropy {F K : ℕ} {c : ℝ}
    (h : ∀ l : ℕ, 1 ≤ l → l ≤ K → (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card)
    {l : ℕ} (hl : l ≤ K) : (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card := by
  by_cases hz : l = 0
  · subst l
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero]
    exact_mod_cast Finset.card_pos.mpr (short_factorial_digits_nonempty F 0)
  · exact h l (by omega) hl

theorem binary_append_odd {A D : Finset ℕ} {b : ℕ} (hb : 0 < b)
    (hA : ∀ x ∈ A, Odd x) : ∀ x ∈ binaryAppend A D b, Odd x := by
  intro x hx
  obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hx
  exact (hA a (Finset.mem_product.mp had).1).add_even
    ((even_two.pow_of_ne_zero (Nat.ne_of_gt hb)).mul_right d)

theorem binary_append_representations {A : Finset ℕ} {F K b l u : ℕ} (hb : b ≤ K)
    (hA : ∀ x ∈ A, HasFactorialDivisorMultiset (F + 2 * K) x u) :
    ∀ x ∈ binaryAppend A (shortFactorialDigits F l) b,
      HasFactorialDivisorMultiset (F + 2 * K) x (u + 1) := by
  intro x hx
  obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨ha, hd⟩ := Finset.mem_product.mp had
  apply factorial_multiset_add (hA a ha)
  rcases (mem_shortFactorialDigits.mp hd).2 with hz | hdiv
  · rw [hz, mul_zero]
    exact factorial_multiset_zero _ _
  · exact factorial_multiset_singleton (shifted_divisor_dvd_factorial hdiv hb)

structure BinaryBlockProfile (F K b u : ℕ) (c : ℝ) (A : Finset ℕ) : Prop where
  nonempty : A.Nonempty
  bounded : ∀ x ∈ A, x < 2 ^ b
  odd : ∀ x ∈ A, Odd x
  representatives : ∀ x ∈ A, HasFactorialDivisorMultiset (F + 2 * K) x u
  entropy : (2 : ℝ) ^ (c * (b : ℝ)) ≤ A.card
  spread : ∀ j : ℕ, 2 ≤ j → j ≤ b → ∀ r : ℕ,
    natResidueMass A (2 ^ j) r ≤ (2 : ℝ) ^ (-(c / 2) * (j : ℝ))

theorem initial_odd_digits_profile {F K b : ℕ} {c : ℝ}
    (hb : 2 ≤ b) (hF : 2 ^ b ≤ F) (hc : c ≤ 1 / 2) :
    BinaryBlockProfile F K b 1 c (initialOddDigits b) := by
  refine ⟨initial_odd_digits_nonempty b, initial_odd_digits_lt (by omega),
    fun _ hx => initial_odd_digits_odd hx, ?_, initial_odd_digits_entropy hb hc, ?_⟩
  · intro x hx
    have hodd := initial_odd_digits_odd hx
    have hpos : 0 < x := by obtain ⟨t, ht⟩ := hodd; omega
    exact factorial_multiset_singleton (Nat.dvd_factorial hpos
      (by have := initial_odd_digits_lt (by omega : 0 < b) x hx; omega))
  · intro j hj hjb r
    exact initial_odd_digits_spread hb hj hjb (by linarith)

theorem binary_append_profile {F K b l u : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F K b u c A) (hb : 0 < b) (hbK : b ≤ K) (hl : l ≤ b) (hc : 0 ≤ c)
    (hD : (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card) :
    BinaryBlockProfile F K (b + l) (u + 1) c (binaryAppend A (shortFactorialDigits F l) b) := by
  refine ⟨binary_append_nonempty hA.nonempty (short_factorial_digits_nonempty F l),
    binary_append_lt hA.bounded (fun _ hd => (mem_shortFactorialDigits.mp hd).1),
    binary_append_odd hb hA.odd, binary_append_representations hbK hA.representatives,
    binary_append_entropy hA.bounded hA.entropy hD, ?_⟩
  exact binary_append_spread hA.bounded hA.nonempty (short_factorial_digits_nonempty F l)
    hl hc hA.entropy hA.spread

def binaryBlockEndpoint (K b₀ i : ℕ) : ℕ := min K (2 ^ i * b₀)

def binaryBlockWidth (K b₀ i : ℕ) : ℕ := binaryBlockEndpoint K b₀ (i + 1) - binaryBlockEndpoint K b₀ i

def binaryBlockSet (F K b₀ : ℕ) : ℕ → Finset ℕ
  | 0 => initialOddDigits b₀
  | i + 1 => binaryAppend (binaryBlockSet F K b₀ i)
      (shortFactorialDigits F (binaryBlockWidth K b₀ i)) (binaryBlockEndpoint K b₀ i)

theorem binary_block_endpoint_zero {K b₀ : ℕ} (hb : b₀ ≤ K) : binaryBlockEndpoint K b₀ 0 = b₀ := by
  simp only [binaryBlockEndpoint, pow_zero, one_mul, min_eq_right hb]

theorem binary_block_endpoint_bounds {K b₀ : ℕ} (hb : b₀ ≤ K) (i : ℕ) :
    b₀ ≤ binaryBlockEndpoint K b₀ i ∧ binaryBlockEndpoint K b₀ i ≤ K := by
  refine ⟨le_min hb ?_, min_le_left _ _⟩
  nlinarith [show 1 ≤ 2 ^ i from Nat.one_le_two_pow]

theorem binary_block_endpoint_mono (K b₀ i : ℕ) :
    binaryBlockEndpoint K b₀ i ≤ binaryBlockEndpoint K b₀ (i + 1) := by
  apply min_le_min_left
  exact Nat.mul_le_mul_right b₀ (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))

theorem binary_block_endpoint_succ_le_twice (K b₀ i : ℕ) :
    binaryBlockEndpoint K b₀ (i + 1) ≤ 2 * binaryBlockEndpoint K b₀ i := by
  unfold binaryBlockEndpoint
  by_cases h : 2 ^ i * b₀ ≤ K
  · rw [min_eq_right h]
    calc
      min K (2 ^ (i + 1) * b₀) ≤ 2 ^ (i + 1) * b₀ := min_le_right _ _
      _ = 2 * (2 ^ i * b₀) := by rw [pow_succ]; ring
  · rw [min_eq_left (by omega : K ≤ 2 ^ i * b₀)]
    exact (min_le_left _ _).trans (by omega)

theorem binary_block_width_add (K b₀ i : ℕ) :
    binaryBlockEndpoint K b₀ i + binaryBlockWidth K b₀ i = binaryBlockEndpoint K b₀ (i + 1) := by
  exact Nat.add_sub_of_le (binary_block_endpoint_mono K b₀ i)

theorem binary_block_width_le (K b₀ i : ℕ) :
    binaryBlockWidth K b₀ i ≤ binaryBlockEndpoint K b₀ i := by
  have := binary_block_endpoint_succ_le_twice K b₀ i
  unfold binaryBlockWidth
  omega

theorem binary_block_endpoint_top {K b₀ : ℕ} (hb : 1 ≤ b₀) :
    binaryBlockEndpoint K b₀ (binaryLength K) = K := by
  apply min_eq_left
  have hK : K < 2 ^ binaryLength K := Nat.lt_pow_succ_log_self (by decide : 1 < 2) K
  nlinarith

theorem binary_block_set_profile {F K b₀ : ℕ} {c : ℝ}
    (hb : 2 ≤ b₀) (hbK : b₀ ≤ K) (hF : 2 ^ b₀ ≤ F) (hc : 0 ≤ c) (hcsmall : c ≤ 1 / 2)
    (hD : ∀ l : ℕ, 1 ≤ l → l ≤ K → (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card) :
    ∀ i : ℕ, BinaryBlockProfile F K (binaryBlockEndpoint K b₀ i) (i + 1) c (binaryBlockSet F K b₀ i) := by
  intro i
  induction i with
  | zero =>
    rw [binary_block_endpoint_zero hbK]
    exact initial_odd_digits_profile hb hF hcsmall
  | succ i ih =>
    have hbds := binary_block_endpoint_bounds hbK i
    have hw := binary_block_width_le K b₀ i
    have hstep := binary_append_profile ih (by omega) hbds.2 hw hc
      (short_factorial_digits_entropy hD (hw.trans hbds.2))
    rw [binary_block_width_add] at hstep
    exact hstep

theorem binary_block_set_profile_top {F K b₀ : ℕ} {c : ℝ}
    (hb : 2 ≤ b₀) (hbK : b₀ ≤ K) (hF : 2 ^ b₀ ≤ F) (hc : 0 ≤ c) (hcsmall : c ≤ 1 / 2)
    (hD : ∀ l : ℕ, 1 ≤ l → l ≤ K → (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits F l).card) :
    BinaryBlockProfile F K K (binaryLength K + 1) c (binaryBlockSet F K b₀ (binaryLength K)) := by
  have h := binary_block_set_profile hb hbK hF hc hcsmall hD (binaryLength K)
  rwa [binary_block_endpoint_top (by omega : 1 ≤ b₀)] at h


theorem shortFactorialDigits_uniform_linear {F k : ℕ} {δ : ℝ}
    (hF : 2 ≤ F) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hprimes : (k : ℝ) * (F : ℝ) ^ δ ≤ (Nat.primeCounting F : ℝ) * (binaryLength F : ℝ)) :
    ∀ l : ℕ, 1 ≤ l → l ≤ k →
      (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (shortFactorialDigits F l).card := by
  intro l hlpos hlk
  let a := binaryLength F
  have ha : 0 < a := binaryLength_pos F
  have hFa : (2 : ℝ) ^ ((a : ℝ) / 2) ≤ (F : ℝ) := half_binaryLength_rpow_le hF
  by_cases hsmall : l ≤ 4 * a
  · have hsmallreal : (l : ℝ) ≤ 4 * (a : ℝ) := by exact_mod_cast hsmall
    have hfirst : (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (F + 1 : ℕ) := by
      calc
        (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (2 : ℝ) ^ ((a : ℝ) / 2) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          nlinarith [mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
        _ ≤ (F : ℝ) := hFa
        _ ≤ (F + 1 : ℕ) := by exact_mod_cast Nat.le_succ F
    have hsecond : (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ ((2 ^ l : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hδ1 (Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
    have hmin : (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (min (F + 1) (2 ^ l) : ℕ) := by
      rw [Nat.cast_min]
      exact le_min hfirst hsecond
    exact hmin.trans (by exact_mod_cast shortFactorialDigits_small_integers (F := F) (l := l))
  · let v := l / (2 * a)
    have hvpos : 0 < v := Nat.div_pos (by omega) (by omega)
    have hvle : v ≤ k := (Nat.div_le_self l (2 * a)).trans hlk
    have hmul : 2 * a * v ≤ l := Nat.mul_div_le l (2 * a)
    have hupper : l < 2 * a * (v + 1) := Nat.lt_mul_div_succ l (by omega)
    have halower : l ≤ 4 * a * v := by nlinarith
    have hheight : F ^ v < 2 ^ l := by
      calc
        F ^ v ≤ (2 ^ a) ^ v := Nat.pow_le_pow_left
          (Nat.lt_pow_succ_log_self (by decide : 1 < 2) F).le v
        _ = 2 ^ (a * v) := (pow_mul _ _ _).symm
        _ < 2 ^ l := Nat.pow_lt_pow_right (by decide : 1 < 2) (by nlinarith)
    have hFpow : 1 ≤ (F : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ F by omega)) hδ.le
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hmulR : 2 * (a : ℝ) * (v : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hmul.trans hlk
    have hcore : 2 * (v : ℝ) * (F : ℝ) ^ δ ≤ (Nat.primeCounting F : ℝ) := by
      have hh := (mul_le_mul_of_nonneg_right hmulR (Real.rpow_nonneg (Nat.cast_nonneg F) δ)).trans hprimes
      apply le_of_mul_le_mul_left (a := (a : ℝ)) _ haR
      change (a : ℝ) * (2 * (v : ℝ) * (F : ℝ) ^ δ) ≤ (a : ℝ) * (Nat.primeCounting F : ℝ)
      dsimp [a] at hh ⊢
      nlinarith
    have htwov : 2 * v ≤ Nat.primeCounting F := by
      have hh := mul_le_mul_of_nonneg_left hFpow (show (0:ℝ) ≤ 2*(v:ℝ) by positivity)
      have hr : 2*(v:ℝ) ≤ (Nat.primeCounting F : ℝ) := by nlinarith
      exact_mod_cast hr
    have hratio : (F : ℝ) ^ δ ≤ (Nat.primeCounting F : ℝ) / 2 / (v : ℝ) := by
      apply (le_div_iff₀ (by exact_mod_cast hvpos : (0 : ℝ) < v)).mpr
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      nlinarith
    have halowerreal : (l : ℝ) ≤ 4 * (a : ℝ) * (v : ℝ) := by exact_mod_cast halower
    calc
      (2 : ℝ) ^ (δ * (l : ℝ) / 8) ≤ (2 : ℝ) ^ (((a : ℝ) / 2 * δ) * (v : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_left halowerreal hδ.le]
      _ = (((2 : ℝ) ^ ((a : ℝ) / 2)) ^ δ) ^ v := by
        rw [Real.rpow_mul_natCast (by norm_num), Real.rpow_mul (by norm_num)]
      _ ≤ ((F : ℝ) ^ δ) ^ v :=
        pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by positivity) hFa hδ.le) v
      _ ≤ ((Nat.primeCounting F : ℝ) / 2 / (v : ℝ)) ^ v :=
        pow_le_pow_left₀ (by positivity) hratio v
      _ ≤ ((Nat.primeCounting F).choose v : ℝ) := choose_lower_half_ratio hvpos htwov
      _ ≤ (shortFactorialDigits F l).card := by exact_mod_cast shortFactorialDigits_choose_lower hheight


end Erdos18c
-- END external module DivisorDigits

-- BEGIN external module LinearDigitSupply

open Finset Filter
namespace Erdos18c
noncomputable section

theorem binaryLength_log_lower (F : ℕ) (hF : 0<F) : Real.log (F:ℝ) ≤ binaryLength F := by
  have hp : (F:ℝ) ≤ (2:ℝ)^binaryLength F := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1<2) F).le
  have hl := Real.log_le_log (by exact_mod_cast hF) hp
  rw [Real.log_pow] at hl
  have hlog : Real.log 2 ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
  exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (binaryLength F))])

theorem binaryLength_log_upper (F : ℕ) (hF : 2≤F) : (binaryLength F:ℝ) ≤ 4*Real.log (F:ℝ) := by
  have hp : (2:ℝ)^(Nat.log 2 F) ≤ (F:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : F≠0)
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2^(Nat.log 2 F)) hp
  rw [Real.log_pow] at hl
  have hhalf : (1/2:ℝ) ≤ Real.log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
  have hnlog : 0≤(Nat.log 2 F:ℝ) := Nat.cast_nonneg _
  have hFlog : Real.log 2 ≤ Real.log (F:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hF)
  have hmul := mul_le_mul_of_nonneg_left hhalf hnlog
  unfold binaryLength
  push_cast
  nlinarith

theorem eventually_primeCounting_lower : ∀ᶠ F : ℕ in atTop,
    (F:ℝ)/(2*Real.log (F:ℝ)) ≤ (Nat.primeCounting F:ℝ) := by
  have hsmall := (Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop (R:=ℝ))).def (by norm_num : (0:ℝ)<1/16)
  have hsucc : Tendsto (fun n : ℕ => n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  filter_upwards [hsucc.eventually hsmall, eventually_ge_atTop 2] with F hs hF
  have hpos : (0:ℝ)<F := by exact_mod_cast (show 0<F by omega)
  have hlogpos : 0<Real.log (F:ℝ) := Real.log_pos (by exact_mod_cast hF)
  have hnorm : |Real.log ((F+1:ℕ):ℝ)| ≤ (1/16) * (((F+1:ℕ):ℝ)) := by
    simp only [Function.comp_apply,id_eq,Real.norm_eq_abs] at hs
    rwa [abs_of_nonneg (show (0:ℝ)≤((F+1:ℕ):ℝ) by positivity)] at hs
  have hlogsmall : Real.log ((F+1:ℕ):ℝ) ≤ (F:ℝ)/8 := by
    have h := (le_abs_self _).trans hnorm
    have h1 : (1:ℝ)≤F := by exact_mod_cast (show 1≤F by omega)
    push_cast at h
    push_cast
    linarith
  have htwo : (5/8:ℝ) ≤ Real.log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
  have hnum : (F:ℝ)/2 ≤ (F:ℝ)*Real.log 2 - Real.log ((F+1:ℕ):ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left htwo hpos.le]
  have hprime := Chebyshev.pi_ge F
  have hh := div_le_div_of_nonneg_right hnum hlogpos.le
  calc
    (F:ℝ)/(2*Real.log (F:ℝ)) = ((F:ℝ)/2)/Real.log (F:ℝ) := by ring
    _ ≤ _ := hh
    _ ≤ _ := by simpa only [Nat.cast_add,Nat.cast_one] using hprime

def linearDigitHost (k : ℕ) : ℕ := 1000*k
def linearDigitDelta (k : ℕ) : ℝ := 1/Real.log (linearDigitHost k:ℝ)
def linearDigitRate (k : ℕ) : ℝ := linearDigitDelta k/8
def linearInputRate (k : ℕ) : ℝ := linearDigitDelta k/16

theorem linearDigitHost_tendsto : Tendsto linearDigitHost atTop atTop := by
  exact tendsto_atTop_mono (fun k => by dsimp [linearDigitHost]; omega) tendsto_id

theorem eventually_linear_digit_count : ∀ᶠ k : ℕ in atTop,
    0<linearDigitDelta k ∧ linearDigitDelta k≤1 ∧
    (∀ l, 1≤l → l≤k → (2:ℝ)^(linearDigitRate k*(l:ℝ)) ≤
      (shortFactorialDigits (linearDigitHost k) l).card) := by
  have hlog : Tendsto (fun k => Real.log (linearDigitHost k:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp linearDigitHost_tendsto)
  filter_upwards [linearDigitHost_tendsto.eventually eventually_primeCounting_lower,
    hlog.eventually_ge_atTop 1, eventually_ge_atTop 1] with k hprime hlog hk
  let F := linearDigitHost k
  have hF : 2≤F := by dsimp [F,linearDigitHost]; omega
  have hFp : (0:ℝ)<F := by exact_mod_cast (show 0<F by omega)
  have hlogp : 0<Real.log (F:ℝ) := lt_of_lt_of_le (by norm_num) hlog
  have hdpos : 0<linearDigitDelta k := one_div_pos.mpr hlogp
  have hdle : linearDigitDelta k≤1 := (div_le_one hlogp).mpr hlog
  have hpower : (F:ℝ)^linearDigitDelta k = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hFp]
    unfold linearDigitDelta
    change Real.exp (Real.log (F:ℝ) * (1/Real.log (F:ℝ))) = _
    rw [mul_one_div_cancel hlogp.ne']
  have hcapacity : (k:ℝ)*(F:ℝ)^linearDigitDelta k ≤ (Nat.primeCounting F:ℝ)*(binaryLength F:ℝ) := by
    have hlen := binaryLength_log_lower F (by omega)
    have hprod := mul_le_mul_of_nonneg_right hprime (show (0:ℝ)≤Real.log (F:ℝ) from hlogp.le)
    have hcancel : ((F:ℝ)/(2*Real.log (F:ℝ))) * Real.log (F:ℝ) = (F:ℝ)/2 := by field_simp
    rw [hcancel] at hprod
    have hprod2 := mul_le_mul_of_nonneg_left hlen
      (show (0:ℝ)≤(Nat.primeCounting F:ℝ) from Nat.cast_nonneg _)
    rw [hpower]
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hFval : (F:ℝ)=1000*(k:ℝ) := by simp [F,linearDigitHost]
    nlinarith [show (0:ℝ)≤k from Nat.cast_nonneg k]
  refine ⟨hdpos,hdle,?_⟩
  intro l hl hlk
  have hh := shortFactorialDigits_uniform_linear hF hdpos hdle hcapacity l hl hlk
  simpa only [linearDigitRate,div_mul_eq_mul_div] using hh

def linearInitialBits (k : ℕ) : ℕ := Nat.log 2 (linearDigitHost k)
def linearDigitSet (k : ℕ) : Finset ℕ :=
  binaryBlockSet (linearDigitHost k) k (linearInitialBits k) (binaryLength k)

theorem eventually_initial_bits_bounds : ∀ᶠ k : ℕ in atTop,
    2≤linearInitialBits k ∧ linearInitialBits k≤k ∧
    2^linearInitialBits k≤linearDigitHost k := by
  have hsmall := (Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop.comp linearDigitHost_tendsto)).def
    (by norm_num : (0:ℝ)<1/4000)
  filter_upwards [hsmall,linearDigitHost_tendsto.eventually_ge_atTop 4] with k hs hF
  let F := linearDigitHost k
  have hF2 : 2≤F := by omega
  have hlogp : 0≤Real.log (F:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤F by omega))
  have hbound : Real.log (F:ℝ) ≤ (1/4000)*(F:ℝ) := by
    simp only [Function.comp_apply,id_eq,Real.norm_eq_abs] at hs
    change |Real.log (F:ℝ)| ≤ (1/4000)*|(F:ℝ)| at hs
    rwa [abs_of_nonneg hlogp,abs_of_nonneg (show (0:ℝ)≤F from Nat.cast_nonneg F)] at hs
  have hlen := binaryLength_log_upper F hF2
  have hFk : (F:ℝ)=1000*(k:ℝ) := by simp [F,linearDigitHost]
  have hsmallNat : binaryLength F≤k := by
    have hr : (binaryLength F:ℝ)≤k := by linarith
    exact_mod_cast hr
  refine ⟨?_,?_,?_⟩
  · exact Nat.le_log_of_pow_le (by decide) (by change 2^2≤F; norm_num; omega)
  · change Nat.log 2 F≤k
    exact (Nat.le_succ _).trans hsmallNat
  · exact Nat.pow_log_le_self 2 (by omega : F≠0)

theorem eventually_linear_digit_profile : ∀ᶠ k : ℕ in atTop,
    0<linearDigitDelta k ∧ linearDigitDelta k≤1 ∧
    BinaryBlockProfile (linearDigitHost k) k k (binaryLength k+1)
      (linearDigitRate k) (linearDigitSet k) := by
  filter_upwards [eventually_linear_digit_count,eventually_initial_bits_bounds] with k hc hb
  refine ⟨hc.1,hc.2.1,?_⟩
  exact binary_block_set_profile_top hb.1 hb.2.1 hb.2.2
    (by unfold linearDigitRate; linarith [hc.1])
    (by unfold linearDigitRate; linarith [hc.2.1]) hc.2.2

end
end Erdos18c
-- END external module LinearDigitSupply

-- BEGIN external module EntropyEstimates

/-!
Finite numerical estimates used by the proposed entropy argument.
These do not yet formalize the chain rule for random variables or the
conditioning/carry argument, and do not prove the full covering lemma.
-/

open Finset

namespace Erdos18c

theorem sum_squares_control {ι : Type*} (S : Finset ι) (h u : ι → ℝ)
    (hhu : ∀ i ∈ S, h i ^ 2 ≤ 2 * u i) :
    (∑ i ∈ S, h i) ^ 2 ≤ 2 * (S.card : ℝ) * ∑ i ∈ S, u i := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S h (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  calc
    (∑ i ∈ S, h i) ^ 2 ≤ (∑ i ∈ S, h i ^ 2) * (S.card : ℝ) := hcs
    _ ≤ (∑ i ∈ S, 2 * u i) * (S.card : ℝ) :=
      mul_le_mul_of_nonneg_right (Finset.sum_le_sum hhu) (Nat.cast_nonneg _)
    _ = 2 * (S.card : ℝ) * ∑ i ∈ S, u i := by
      rw [← Finset.mul_sum]
      ring

theorem minority_mass_lower {ι : Type*} (S : Finset ι) (h u : ι → ℝ) (a : ℝ)
    (hcard : 0 < S.card) (ha : 0 ≤ a)
    (hhu : ∀ i ∈ S, h i ^ 2 ≤ 2 * u i)
    (hbudget : a * S.card ≤ ∑ i ∈ S, h i) :
    a ^ 2 * S.card / 2 ≤ ∑ i ∈ S, u i := by
  have hn : (0 : ℝ) < S.card := by exact_mod_cast hcard
  have hsum0 : 0 ≤ ∑ i ∈ S, h i := le_trans (mul_nonneg ha hn.le) hbudget
  have hsquare : (a * S.card) ^ 2 ≤ (∑ i ∈ S, h i) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg ha hn.le) hbudget 2
  have hcs := sum_squares_control S h u hhu
  have hdivide : (S.card : ℝ) * (a ^ 2 * S.card) ≤
      (S.card : ℝ) * (2 * ∑ i ∈ S, u i) := by nlinarith
  have hcancel := le_of_mul_le_mul_left hdivide hn
  linarith

theorem weighted_reciprocal_lower {ι : Type*} (S : Finset ι)
    (u d : ι → ℝ) (D H c : ℝ)
    (hD : 0 < D) (hH : 0 < H)
    (hu : ∀ i ∈ S, 0 ≤ u i)
    (hd : ∀ i ∈ S, 0 < d i ∧ d i ≤ D)
    (hmass : c * D ≤ ∑ i ∈ S, u i) :
    c / H ≤ (∑ i ∈ S, u i / d i) / H := by
  have hsum : (∑ i ∈ S, u i) / D ≤ ∑ i ∈ S, u i / d i := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    apply (div_le_div_iff₀ hD (hd i hi).1).mpr
    exact mul_le_mul_of_nonneg_left (hd i hi).2 (hu i hi)
  have hc : c ≤ (∑ i ∈ S, u i) / D := (le_div_iff₀ hD).mpr hmass
  exact div_le_div_of_nonneg_right (hc.trans hsum) hH.le

theorem harmonic_kernel_lower (j : ℕ) (u : ℕ → ℝ) (H c : ℝ)
    (hH : 0 < H)
    (hu : ∀ i ≤ j, 0 ≤ u i)
    (hmass : c * (j + 1 : ℕ) ≤ ∑ i ∈ Finset.range (j + 1), u i) :
    c / H ≤
      (∑ i ∈ Finset.range (j + 1), u i / (j + 1 - i : ℕ)) / H := by
  apply weighted_reciprocal_lower (Finset.range (j + 1)) u
    (fun i => (j + 1 - i : ℕ)) (j + 1 : ℕ) H c
  · positivity
  · exact hH
  · intro i hi
    exact hu i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  · intro i hi
    have hi' : i < j + 1 := Finset.mem_range.mp hi
    constructor
    · exact_mod_cast (show 0 < j + 1 - i by omega)
    · exact_mod_cast (show j + 1 - i ≤ j + 1 by omega)
  · exact hmass


end Erdos18c
-- END external module EntropyEstimates

-- BEGIN external module DyadicEntropy

/-! Entropy increments for finite lower-bit projections. -/

open Finset
namespace Erdos18c
noncomputable section

def dyadicSplitEquiv (j : ℕ) : Fin (2^j) ⊕ Fin (2^j) ≃ Fin (2^(j+1)) :=
  finSumFinEquiv.trans (finCongr (by omega : 2^j+2^j = 2^(j+1)))

def dyadicLower (j : ℕ) (i : Fin (2^j)) : Fin (2^(j+1)) := dyadicSplitEquiv j (.inl i)
def dyadicUpper (j : ℕ) (i : Fin (2^j)) : Fin (2^(j+1)) := dyadicSplitEquiv j (.inr i)

@[simp] theorem dyadicLower_val (j : ℕ) (i : Fin (2^j)) : (dyadicLower j i).val = i.val := rfl
@[simp] theorem dyadicUpper_val (j : ℕ) (i : Fin (2^j)) : (dyadicUpper j i).val = 2^j+i.val := rfl

theorem dyadic_split_sum (j : ℕ) (F : Fin (2^(j+1)) → ℝ) :
    ∑ z, F z = ∑ i, (F (dyadicLower j i) + F (dyadicUpper j i)) := by
  have h := Fintype.sum_equiv (dyadicSplitEquiv j)
    (fun z => F (dyadicSplitEquiv j z)) F (fun _ => rfl)
  simpa only [Fintype.sum_sum_type, dyadicLower, dyadicUpper, sum_add_distrib] using h.symm

@[simp] theorem dyadicLower_mod (j : ℕ) (i : Fin (2^j)) :
    dyadicIndex j (dyadicLower j i).val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

@[simp] theorem dyadicUpper_mod (j : ℕ) (i : Fin (2^j)) :
    dyadicIndex j (dyadicUpper j i).val = i := by
  apply Fin.ext
  simp [dyadicIndex, Nat.mod_eq_of_lt i.isLt]

theorem dyadic_parent_mass (j : ℕ) (p : Fin (2^(j+1)) → ℝ) (i : Fin (2^j)) :
    finitePushforward p (fun z => dyadicIndex j z.val) i =
      p (dyadicLower j i) + p (dyadicUpper j i) := by
  unfold finitePushforward
  rw [sum_filter, dyadic_split_sum]
  simp only [dyadicLower_mod, dyadicUpper_mod]
  rw [sum_add_distrib]
  simp

theorem dyadic_entropy_increment (j : ℕ) (p : Fin (2^(j+1)) → ℝ) :
    finiteEntropy univ p - finiteEntropy univ
      (finitePushforward p (fun z => dyadicIndex j z.val)) =
      ∑ i, pairEntropy (p (dyadicLower j i)) (p (dyadicUpper j i)) := by
  unfold finiteEntropy
  rw [dyadic_split_sum]
  simp_rw [dyadic_parent_mass]
  simp only [pairEntropy, sum_sub_distrib, sum_add_distrib]

theorem dyadic_entropy_zero {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hmass : ∑ a, p a = 1) : dyadicEntropy p f 0 = 0 := by
  have hi : ∀ a : ι, dyadicIndex 0 (f a) = (0 : Fin (2^0)) := by
    intro a
    apply Fin.ext
    simp [dyadicIndex]
  have hv : dyadicDistribution p f 0 0 = 1 := by
    simpa only [dyadicDistribution, finitePushforward, hi, filter_true] using hmass
  unfold dyadicEntropy finiteEntropy
  have hh : ∀ r : Fin (2^0), r=0 := by
    intro r
    apply Fin.ext
    have hr := r.isLt
    norm_num at hr
    omega
  simp_rw [hh, hv]
  simp [Real.negMulLog_def]

def dyadicMinority {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (j : ℕ) : ℝ :=
  2 * ∑ i, min (dyadicDistribution p f (j+1) (dyadicLower j i))
    (dyadicDistribution p f (j+1) (dyadicUpper j i))

def dyadicBitBias {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (j : ℕ) : ℝ :=
  ∑ i, |dyadicDistribution p f (j+1) (dyadicLower j i) -
    dyadicDistribution p f (j+1) (dyadicUpper j i)|

theorem dyadic_entropy_step_eq {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (j : ℕ) :
    dyadicEntropy p f (j+1) - dyadicEntropy p f j =
      ∑ i, pairEntropy (dyadicDistribution p f (j+1) (dyadicLower j i))
        (dyadicDistribution p f (j+1) (dyadicUpper j i)) := by
  have hh := dyadic_entropy_increment j (dyadicDistribution p f (j+1))
  rw [dyadic_distribution_project p f (Nat.le_succ j)] at hh
  exact hh

theorem dyadic_entropy_step_sq {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1) (j : ℕ) :
    (dyadicEntropy p f (j+1) - dyadicEntropy p f j)^2 ≤ 2 * dyadicMinority p f j := by
  rw [dyadic_entropy_step_eq]
  have hn := finite_pushforward_nonneg p (fun a => dyadicIndex (j+1) (f a)) hp
  have hs : ∑ i, (dyadicDistribution p f (j+1) (dyadicLower j i) +
      dyadicDistribution p f (j+1) (dyadicUpper j i)) = 1 := by
    rw [← dyadic_split_sum, dyadicDistribution, finite_pushforward_sum, hmass]
  have hh := sum_pairEntropy_sq_le _ _ (fun i => hn _) (fun i => hn _) hs
  convert hh using 1 <;> simp only [dyadicMinority, dyadicDistribution]
  ring

theorem dyadic_entropy_step_lower {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (j : ℕ) :
    dyadicMinority p f j * Real.log 2 ≤ dyadicEntropy p f (j+1) - dyadicEntropy p f j := by
  rw [dyadic_entropy_step_eq]
  exact sum_pairEntropy_lower _ _
    (fun i => finite_pushforward_nonneg p _ hp _) (fun i => finite_pushforward_nonneg p _ hp _)

theorem dyadic_entropy_telescope {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hmass : ∑ a, p a = 1) (L : ℕ) :
    ∑ j ∈ range L, (dyadicEntropy p f (j+1) - dyadicEntropy p f j) = dyadicEntropy p f L := by
  induction L with
  | zero => simp [dyadic_entropy_zero p f hmass]
  | succ L ih => rw [sum_range_succ, ih]; ring

theorem dyadic_prefix_minority {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1) (L : ℕ) (hL : 0<L)
    (g : ℝ) (hg : 0 ≤ g)
    (hbudget : g * L * Real.log 2 ≤ dyadicEntropy p f L) :
    g^2 * (Real.log 2)^2 / 2 * L ≤ ∑ j ∈ range L, dyadicMinority p f j := by
  have hh := minority_mass_lower (range L)
    (fun j => dyadicEntropy p f (j+1) - dyadicEntropy p f j)
    (dyadicMinority p f) (g*Real.log 2) (by simpa using hL)
    (mul_nonneg hg (Real.log_nonneg (by norm_num)))
    (fun j _ => dyadic_entropy_step_sq p f hp hmass j)
    (by rw [dyadic_entropy_telescope p f hmass]; simpa only [card_range, mul_assoc, mul_left_comm, mul_comm] using hbudget)
  convert hh using 1
  simp only [card_range]
  ring

end
end Erdos18c
-- END external module DyadicEntropy

-- BEGIN external module FiniteConvolution

/-!
Finite real convolution estimates. The summation/reindexing arguments adapt
the finite convolution infrastructure of the credited Kohlmeyer--Kruer 18(b)
source. The involution-bias contraction is used for the new dyadic mixing step.
-/

open Finset
namespace Erdos18c

noncomputable section
variable {G H : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
  [Fintype H] [AddCommGroup H] [DecidableEq H]

def realConvolution (f g : G → ℝ) (x : G) : ℝ := ∑ y, f y * g (x-y)
def realShift (h : G) (f : G → ℝ) (x : G) : ℝ := f (x+h)
def realDifference (h : G) (f : G → ℝ) (x : G) : ℝ := f x - f (x+h)
def finiteL1 (f : G → ℝ) : ℝ := ∑ x, |f x|
def involutionBias (h : G) (f : G → ℝ) : ℝ := finiteL1 (realDifference h f) / 2

omit [AddCommGroup G] [DecidableEq G] in
theorem finiteL1_nonneg (f : G → ℝ) : 0 ≤ finiteL1 f :=
  sum_nonneg fun _ _ => abs_nonneg _

omit [DecidableEq G] in
theorem finiteL1_shift (h : G) (f : G → ℝ) : finiteL1 (realShift h f) = finiteL1 f := by
  exact Fintype.sum_equiv (Equiv.addRight h) _ _ (fun _ => rfl)

omit [DecidableEq G] in
theorem sum_realConvolution (f g : G → ℝ) :
    ∑ x, realConvolution f g x = (∑ x, f x) * (∑ x, g x) := by
  simp only [realConvolution]
  rw [sum_comm]
  calc
    (∑ y, ∑ x, f y * g (x-y)) = ∑ y, f y * ∑ x, g x := by
      apply sum_congr rfl
      intro y _
      rw [← mul_sum]
      congr 1
      exact Fintype.sum_equiv (Equiv.subRight y) _ _ (fun _ => rfl)
    _ = _ := (sum_mul _ _ _).symm

omit [DecidableEq G] in
theorem realConvolution_nonneg {f g : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (x : G) :
    0 ≤ realConvolution f g x := sum_nonneg (fun y _ => mul_nonneg (hf y) (hg _))

omit [DecidableEq G] in
theorem finiteL1_convolution_le (f g : G → ℝ) :
    finiteL1 (realConvolution f g) ≤ finiteL1 f * finiteL1 g := by
  calc
    _ ≤ ∑ x, ∑ y, |f y| * |g (x-y)| := by
      apply sum_le_sum
      intro x _
      simpa only [realConvolution, abs_mul] using abs_sum_le_sum_abs (s := univ) (f := fun y => f y * g (x-y))
    _ = ∑ y, |f y| * ∑ x, |g x| := by
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      rw [← mul_sum]
      congr 1
      exact Fintype.sum_equiv (Equiv.subRight y) _ _ (fun _ => rfl)
    _ = _ := (sum_mul _ _ _).symm

omit [DecidableEq G] in
theorem convolution_shift_right (h : G) (f g : G → ℝ) :
    realConvolution f (realShift h g) = realShift h (realConvolution f g) := by
  funext x
  apply sum_congr rfl
  intro y _
  dsimp [realShift]
  congr 2
  abel

omit [DecidableEq G] in
theorem convolution_shift_left (h : G) (f g : G → ℝ) :
    realConvolution (realShift h f) g = realShift h (realConvolution f g) := by
  funext x
  refine Fintype.sum_equiv (Equiv.addRight h) _ _ ?_
  intro y
  dsimp [realShift]
  congr 2
  abel

omit [DecidableEq G] in
theorem convolution_difference_right (h : G) (f g : G → ℝ) :
    realConvolution f (realDifference h g) = realDifference h (realConvolution f g) := by
  funext x
  have hh := congrFun (convolution_shift_right h f g) x
  simpa only [realConvolution, realDifference, mul_sub, sum_sub_distrib,
    realShift] using congrArg (fun z => realConvolution f g x - z) hh

omit [DecidableEq G] in
theorem convolution_difference_left (h : G) (f g : G → ℝ) :
    realConvolution (realDifference h f) g = realDifference h (realConvolution f g) := by
  funext x
  have hh := congrFun (convolution_shift_left h f g) x
  simpa only [realConvolution, realDifference, sub_mul, sum_sub_distrib,
    realShift] using congrArg (fun z => realConvolution f g x - z) hh

theorem convolution_double_difference (h : G) (hh : h+h=0) (f g : G → ℝ) (x : G) :
    realConvolution (realDifference h f) (realDifference h g) x =
      2 * realDifference h (realConvolution f g) x := by
  rw [convolution_difference_left, convolution_difference_right]
  simp only [realDifference, add_assoc, hh, add_zero]
  ring

omit [DecidableEq G] in
theorem involutionBias_nonneg (h : G) (f : G → ℝ) : 0 ≤ involutionBias h f :=
  div_nonneg (finiteL1_nonneg _) (by norm_num)

omit [DecidableEq G] in
theorem involutionBias_le_l1 (h : G) (f : G → ℝ) : involutionBias h f ≤ finiteL1 f := by
  have hb : finiteL1 (realDifference h f) ≤ finiteL1 f + finiteL1 (realShift h f) := by
    calc
      _ ≤ ∑ x, (|f x| + |f (x+h)|) := sum_le_sum (fun x _ => abs_sub _ _)
      _ = _ := sum_add_distrib
  rw [finiteL1_shift] at hb
  unfold involutionBias
  linarith

theorem involutionBias_convolution_le (h : G) (hh : h+h=0) (f g : G → ℝ) :
    involutionBias h (realConvolution f g) ≤ involutionBias h f * involutionBias h g := by
  have hb := finiteL1_convolution_le (realDifference h f) (realDifference h g)
  have he : finiteL1 (realConvolution (realDifference h f) (realDifference h g)) =
      2 * finiteL1 (realDifference h (realConvolution f g)) := by
    simp only [finiteL1, convolution_double_difference h hh, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [mul_sum]
  rw [he] at hb
  unfold involutionBias
  nlinarith

def realConvolutionPow (f : G → ℝ) : ℕ → G → ℝ
  | 0 => fun x => if x=0 then 1 else 0
  | r+1 => realConvolution f (realConvolutionPow f r)

theorem involutionBias_convolutionPow_le (h : G) (hh : h+h=0) (f : G → ℝ) (r : ℕ) :
    involutionBias h (realConvolutionPow f r) ≤ involutionBias h f ^ r := by
  induction r with
  | zero =>
    have hb := involutionBias_le_l1 h (realConvolutionPow f 0)
    have hd : finiteL1 (realConvolutionPow f 0) = 1 := by
      calc
        _ = ∑ x : G, if x=0 then (1:ℝ) else 0 := by
          apply sum_congr rfl
          intro x _
          by_cases hx : x=0 <;> simp [realConvolutionPow,hx]
        _ = 1 := by simp
    simpa only [hd, pow_zero] using hb
  | succ r ih =>
    calc
      _ ≤ involutionBias h f * involutionBias h (realConvolutionPow f r) :=
        involutionBias_convolution_le h hh _ _
      _ ≤ involutionBias h f * involutionBias h f ^ r :=
        mul_le_mul_of_nonneg_left ih (involutionBias_nonneg _ _)
      _ = _ := by rw [pow_succ]; ring

theorem realConvolutionPow_probability {f : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hsum : ∑ x, f x = 1) (r : ℕ) :
    (∀ x, 0 ≤ realConvolutionPow f r x) ∧ ∑ x, realConvolutionPow f r x = 1 := by
  induction r with
  | zero => simp [realConvolutionPow]; intro x; split_ifs <;> norm_num
  | succ r ih => exact ⟨realConvolution_nonneg hf ih.1, by rw [realConvolutionPow, sum_realConvolution, hsum, ih.2, one_mul]⟩

theorem sum_test_pushforward {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (p : ι → ℝ) (T : ι → κ) (h : κ → ℝ) :
    (∑ b, h b * finitePushforward p T b) = ∑ a, h (T a) * p a := by
  simp only [finitePushforward, mul_sum, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [mul_ite, mul_zero]
  simp

omit [DecidableEq G] in
theorem sum_test_realConvolution (f g h : G → ℝ) :
    (∑ a, h a * realConvolution f g a) = ∑ x, ∑ y, h (x+y) * f x * g y := by
  simp only [realConvolution, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  refine Fintype.sum_equiv (Equiv.subRight x) _ _ ?_
  intro z
  simp only [Equiv.subRight_apply]
  have he : x+(z-x)=z := by abel
  rw [he]
  ring

theorem convolution_pushforward_left {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (T : ι → G) (g : G → ℝ) (a : G) :
    realConvolution (finitePushforward p T) g a = ∑ x, p x * g (a-T x) := by
  simpa only [realConvolution, mul_comm] using sum_test_pushforward p T (fun b => g (a-b))

omit [DecidableEq G] in
theorem pushforward_realConvolution (f g : G → ℝ) (T : G →+ H) :
    finitePushforward (realConvolution f g) T =
      realConvolution (finitePushforward f T) (finitePushforward g T) := by
  funext a
  calc
    _ = ∑ z : G, (if T z=a then (1:ℝ) else 0) * realConvolution f g z := by
      simp only [finitePushforward, sum_filter, ite_mul, one_mul, zero_mul]
    _ = ∑ x : G, ∑ y : G, (if T (x+y)=a then (1:ℝ) else 0) * f x * g y :=
      sum_test_realConvolution f g _
    _ = ∑ x : G, f x * finitePushforward g T (a-T x) := by
      apply sum_congr rfl
      intro x _
      simp only [finitePushforward, sum_filter, mul_sum]
      apply sum_congr rfl
      intro y _
      rw [map_add]
      by_cases hy : T y = a-T x
      · simp [hy]
      · have hxy : T x+T y ≠ a := by
          intro heq
          exact hy ((eq_sub_iff_add_eq').mpr heq)
        simp [hy,hxy]
    _ = _ := (convolution_pushforward_left f T _ a).symm

theorem pushforward_realConvolutionPow (f : G → ℝ) (T : G →+ H) (r : ℕ) :
    finitePushforward (realConvolutionPow f r) T =
      realConvolutionPow (finitePushforward f T) r := by
  induction r with
  | zero =>
    funext a
    simp only [realConvolutionPow, finitePushforward, sum_filter]
    have he (x : G) : (if T x=a then (if x=0 then (1:ℝ) else 0) else 0) =
        if x=0 then (if a=0 then 1 else 0) else 0 := by
      by_cases hx : x=0
      · subst x; simp [eq_comm]
      · simp [hx]
    simp_rw [he]
    simp
  | succ r ih => rw [realConvolutionPow, pushforward_realConvolution, ih, realConvolutionPow]

omit [DecidableEq G] [Fintype H] in
theorem pushforward_shift (f : G → ℝ) (T : G →+ H) (h : G) :
    finitePushforward (realShift h f) T = realShift (T h) (finitePushforward f T) := by
  funext b
  simp only [finitePushforward, realShift, sum_filter]
  refine Fintype.sum_equiv (Equiv.addRight h) _ _ ?_
  intro a
  simp [map_add]

omit [DecidableEq G] [Fintype H] in
theorem pushforward_difference (f : G → ℝ) (T : G →+ H) (h : G) :
    finitePushforward (realDifference h f) T = realDifference (T h) (finitePushforward f T) := by
  have he : finitePushforward (realDifference h f) T =
      fun b => finitePushforward f T b - finitePushforward (realShift h f) T b := by
    funext b
    simp only [finitePushforward, realDifference, realShift, sum_sub_distrib]
  rw [he, pushforward_shift]
  rfl

omit [AddCommGroup G] [AddCommGroup H] in
theorem finiteL1_pushforward_injective (f : G → ℝ) (T : G → H) (hT : Function.Injective T) :
    finiteL1 (finitePushforward f T) = finiteL1 f := by
  have he (b : H) : |finitePushforward f T b| = finitePushforward (fun a => |f a|) T b := by
    by_cases hx : ∃ a, T a=b
    · obtain ⟨a,rfl⟩ := hx
      simp [finitePushforward, hT.eq_iff, sum_filter]
    · have hn (a : G) : T a ≠ b := fun ha => hx ⟨a,ha⟩
      simp [finitePushforward, hn]
  unfold finiteL1
  simp_rw [he]
  exact finite_pushforward_sum _ _

theorem involutionBias_pushforward (f : G → ℝ) (T : G →+ H)
    (hT : Function.Injective T) (h : G) :
    involutionBias (T h) (finitePushforward f T) = involutionBias h f := by
  unfold involutionBias
  rw [← pushforward_difference, finiteL1_pushforward_injective _ T hT]

def finiteMixture {ι : Type*} [Fintype ι] (w : ι → ℝ) (F : ι → G → ℝ) (x : G) : ℝ :=
  ∑ i, w i * F i x

omit [AddCommGroup G] [DecidableEq G] in
theorem sum_finiteMixture {ι : Type*} [Fintype ι] (w : ι → ℝ) (F : ι → G → ℝ) :
    ∑ x, finiteMixture w F x = ∑ i, w i * ∑ x, F i x := by
  simp only [finiteMixture]
  rw [sum_comm]
  simp only [mul_sum]

omit [Fintype G] [AddCommGroup G] [DecidableEq G] in
theorem finiteMixture_nonneg {ι : Type*} [Fintype ι] (w : ι → ℝ) (F : ι → G → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hF : ∀ i x, 0 ≤ F i x) (x : G) : 0 ≤ finiteMixture w F x :=
  sum_nonneg fun i _ => mul_nonneg (hw i) (hF i x)

omit [AddCommGroup G] [DecidableEq G] [Fintype H] [AddCommGroup H] in
theorem pushforward_finiteMixture {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (F : ι → G → ℝ) (T : G → H) :
    finitePushforward (finiteMixture w F) T = finiteMixture w (fun i => finitePushforward (F i) T) := by
  funext b
  unfold finitePushforward finiteMixture
  rw [sum_comm]
  simp only [mul_sum]

omit [DecidableEq G] in
theorem involutionBias_finiteMixture {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (F : ι → G → ℝ) (hw : ∀ i, 0 ≤ w i) (h : G) :
    involutionBias h (finiteMixture w F) ≤ ∑ i, w i * involutionBias h (F i) := by
  have hinner (x : G) : realDifference h (finiteMixture w F) x =
      ∑ i, w i * realDifference h (F i) x := by
    simp only [finiteMixture, realDifference, mul_sub, sum_sub_distrib]
  have hb : finiteL1 (realDifference h (finiteMixture w F)) ≤
      ∑ i, w i * finiteL1 (realDifference h (F i)) := by
    unfold finiteL1
    simp_rw [hinner]
    calc
      _ ≤ ∑ x, ∑ i, |w i * realDifference h (F i) x| :=
        sum_le_sum fun x _ => abs_sum_le_sum_abs _ _
      _ = _ := by
        rw [sum_comm]
        simp only [abs_mul, abs_of_nonneg (hw _), mul_sum]
  unfold involutionBias
  simp_rw [← mul_div_assoc]
  rw [← sum_div]
  exact div_le_div_of_nonneg_right hb (by norm_num)

theorem twice_card_cover (B : Finset G) (hcard : Fintype.card G < 2*B.card) (x : G) :
    ∃ a∈B, ∃ b∈B, a+b=x := by
  by_contra hn
  have hd : Disjoint B (B.image (fun b => x-b)) := by
    apply disjoint_left.mpr
    intro a ha hb
    obtain ⟨b,hb,he⟩ := mem_image.mp hb
    exact hn ⟨a,ha,b,hb,by rw [← he]; abel⟩
  have hc := card_le_card (subset_univ (B ∪ B.image (fun b => x-b)))
  rw [card_union_of_disjoint hd, card_image_of_injective B (fun a b h => by
    rw [sub_eq_add_neg,sub_eq_add_neg] at h
    exact neg_injective (add_left_cancel h))] at hc
  simp only [card_univ] at hc
  omega

theorem convolutionPow_support (f : G → ℝ) (r : ℕ) (x : G)
    (hx : realConvolutionPow f r x ≠ 0) :
    ∃ L : List G, L.length=r ∧ (∀ a∈L, f a≠0) ∧ L.sum=x := by
  induction r generalizing x with
  | zero =>
    have hx0 : x=0 := by by_contra h; simp [realConvolutionPow,h] at hx
    subst x
    exact ⟨[],rfl,by simp,by simp⟩
  | succ r ih =>
    obtain ⟨a,_,ha⟩ := exists_ne_zero_of_sum_ne_zero hx
    have han : f a ≠ 0 := (mul_ne_zero_iff.mp ha).1
    have htail : realConvolutionPow f r (x-a)≠0 := (mul_ne_zero_iff.mp ha).2
    obtain ⟨L,hL,hf,hs⟩ := ih (x-a) htail
    refine ⟨a::L,by simp [hL],?_,by simp [hs]⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact han
    · exact hf b hb

end
end Erdos18c
-- END external module FiniteConvolution

-- BEGIN external module DyadicConvolution

open Finset
namespace Erdos18c
noncomputable section

def dyadicProject {u v : ℕ} (h : u ≤ v) : Fin (2^v) →+ Fin (2^u) where
  toFun x := dyadicIndex u x.val
  map_zero' := by apply Fin.ext; simp [dyadicIndex]
  map_add' x y := by
    apply Fin.ext
    change (x.val+y.val) % 2^v % 2^u = (x.val%2^u+y.val%2^u)%2^u
    rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 h)]
    exact Nat.add_mod _ _ _

def dyadicHalf (j : ℕ) : Fin (2^(j+1)) := ⟨2^j, by
  have hp : 0 < (2:ℕ)^j := pow_pos (by norm_num) _
  rw [pow_succ]
  omega⟩

theorem dyadicHalf_add_self (j : ℕ) : dyadicHalf j + dyadicHalf j = 0 := by
  apply Fin.ext
  change (2^j+2^j)%2^(j+1)=0
  have hh : 2^j+2^j=2^(j+1) := by rw [pow_succ]; omega
  rw [hh, Nat.mod_self]

@[simp] theorem dyadicLower_add_half (j : ℕ) (i : Fin (2^j)) :
    dyadicLower j i + dyadicHalf j = dyadicUpper j i := by
  apply Fin.ext
  change (i.val+2^j)%2^(j+1)=2^j+i.val
  have hi := i.isLt
  rw [Nat.mod_eq_of_lt (by rw [pow_succ]; omega)]
  omega

@[simp] theorem dyadicUpper_add_half (j : ℕ) (i : Fin (2^j)) :
    dyadicUpper j i + dyadicHalf j = dyadicLower j i := by
  apply Fin.ext
  change (2^j+i.val+2^j)%2^(j+1)=i.val
  have he : 2^j+i.val+2^j=2^(j+1)+i.val := by rw [pow_succ]; omega
  rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (i.isLt.trans_le (by rw [pow_succ]; omega))]

theorem dyadic_involutionBias (j : ℕ) (p : Fin (2^(j+1)) → ℝ) :
    involutionBias (dyadicHalf j) p = ∑ i, |p (dyadicLower j i)-p (dyadicUpper j i)| := by
  unfold involutionBias finiteL1 realDifference
  rw [dyadic_split_sum]
  simp only [dyadicLower_add_half, dyadicUpper_add_half,
    abs_sub_comm (p (dyadicUpper j _)) (p (dyadicLower j _))]
  rw [sum_add_distrib]
  ring

theorem dyadic_bitBias_eq_involution {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (f : ι → ℕ) (j : ℕ) :
    dyadicBitBias p f j = involutionBias (dyadicHalf j) (dyadicDistribution p f (j+1)) :=
  (dyadic_involutionBias j _).symm

theorem abs_sub_add_two_min (x y : ℝ) : |x-y|+2*min x y=x+y := by
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy, abs_of_nonpos (sub_nonpos.mpr hxy)]; ring
  · rw [min_eq_right hyx, abs_of_nonneg (sub_nonneg.mpr hyx)]; ring

theorem dyadic_bitBias_add_minority {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (f : ι → ℕ) (hmass : ∑ a, p a=1) (j : ℕ) :
    dyadicBitBias p f j + dyadicMinority p f j = 1 := by
  have hs := sum_congr (s₁ := univ) rfl (fun (i : Fin (2^j)) _ =>
    abs_sub_add_two_min (dyadicDistribution p f (j+1) (dyadicLower j i))
      (dyadicDistribution p f (j+1) (dyadicUpper j i)))
  rw [sum_add_distrib, ← mul_sum] at hs
  change dyadicBitBias p f j + dyadicMinority p f j = _ at hs
  rw [← dyadic_split_sum, dyadicDistribution, finite_pushforward_sum, hmass] at hs
  exact hs

theorem dyadicMinority_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (j : ℕ) : 0 ≤ dyadicMinority p f j := by
  unfold dyadicMinority
  apply mul_nonneg (by norm_num)
  apply sum_nonneg
  intro i _
  exact le_min (finite_pushforward_nonneg p _ hp _) (finite_pushforward_nonneg p _ hp _)

theorem dyadic_bitBias_convolutionPow {k j : ℕ} (hj : j+1 ≤ k)
    (p : Fin (2^k) → ℝ) (r : ℕ) :
    dyadicBitBias (realConvolutionPow p r) Fin.val j ≤ (dyadicBitBias p Fin.val j)^r := by
  rw [dyadic_bitBias_eq_involution, dyadic_bitBias_eq_involution]
  change involutionBias (dyadicHalf j)
    (finitePushforward (realConvolutionPow p r) (dyadicProject hj)) ≤ _
  rw [pushforward_realConvolutionPow]
  exact involutionBias_convolutionPow_le _ (dyadicHalf_add_self j) _ r

end
end Erdos18c
-- END external module DyadicConvolution

-- BEGIN external module DyadicDilations

open Finset
namespace Erdos18c
noncomputable section

def dyadicScale (a m : ℕ) : Fin (2^m) →+ Fin (2^(a+m)) where
  toFun x := ⟨2^a*x.val, by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_left x.isLt (by positivity)⟩
  map_zero' := by apply Fin.ext; simp
  map_add' x y := by
    apply Fin.ext
    change 2^a*((x.val+y.val)%2^m) = (2^a*x.val+2^a*y.val)%2^(a+m)
    rw [← Nat.mul_add, pow_add, Nat.mul_mod_mul_left]

theorem dyadicScale_injective (a m : ℕ) : Function.Injective (dyadicScale a m) := by
  intro x y h
  have hv := congrArg Fin.val h
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2:ℕ)^a) hv

theorem dyadicScale_half (a j : ℕ) :
    dyadicScale a (j+1) (dyadicHalf j) =
      (dyadicHalf (a+j) : Fin (2^(a+(j+1)))) := by
  apply Fin.ext
  change 2^a*2^j = 2^(a+j)
  exact (pow_add 2 a j).symm

def dyadicMultiplier (k a : ℕ) (x : Fin (2^k)) : Fin (2^k) :=
  dyadicIndex k (2^a*x.val)

def dyadicDilate (k a : ℕ) (p : Fin (2^k) → ℝ) : Fin (2^k) → ℝ :=
  finitePushforward p (dyadicMultiplier k a)

theorem dyadic_multiplier_project {k m a : ℕ} (hj : a+m ≤ k) :
    (fun x : Fin (2^k) => dyadicIndex (a+m) (dyadicMultiplier k a x).val) =
      fun x : Fin (2^k) => (dyadicScale a m) (dyadicIndex m x.val) := by
  funext x
  apply Fin.ext
  dsimp [dyadicIndex,dyadicMultiplier,dyadicScale]
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hj)]
  rw [pow_add, Nat.mul_mod_mul_left]

theorem dyadicDilate_project {k m a : ℕ} (hj : a+m ≤ k)
    (p : Fin (2^k) → ℝ) :
    dyadicDistribution (dyadicDilate k a p) Fin.val (a+m) =
      finitePushforward (dyadicDistribution p Fin.val m) (dyadicScale a m) := by
  unfold dyadicDistribution dyadicDilate
  rw [finite_pushforward_comp, finite_pushforward_comp]
  congr 1
  exact dyadic_multiplier_project hj

def dyadicScaleBit (a j : ℕ) : Fin (2^(j+1)) →+ Fin (2^(a+j+1)) where
  toFun x := ⟨2^a*x.val, by
    rw [show (2:ℕ)^(a+j+1)=2^a*2^(j+1) by rw [Nat.add_assoc, pow_add]]
    exact Nat.mul_lt_mul_of_pos_left x.isLt (by positivity)⟩
  map_zero' := by apply Fin.ext; simp
  map_add' x y := by
    apply Fin.ext
    change 2^a*((x.val+y.val)%2^(j+1)) = (2^a*x.val+2^a*y.val)%2^(a+j+1)
    rw [← Nat.mul_add, show (2:ℕ)^(a+j+1)=2^a*2^(j+1) by rw [Nat.add_assoc, pow_add], Nat.mul_mod_mul_left]

theorem dyadicScaleBit_injective (a j : ℕ) : Function.Injective (dyadicScaleBit a j) := by
  intro x y h
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2:ℕ)^a) (congrArg Fin.val h)

theorem dyadicScaleBit_half (a j : ℕ) :
    dyadicScaleBit a j (dyadicHalf j) = dyadicHalf (a+j) := by
  apply Fin.ext
  change 2^a*2^j=2^(a+j)
  exact (pow_add 2 a j).symm

theorem dyadicDilate_project_bit {k j a : ℕ} (hj : a+j+1 ≤ k)
    (p : Fin (2^k) → ℝ) :
    dyadicDistribution (dyadicDilate k a p) Fin.val (a+j+1) =
      finitePushforward (dyadicDistribution p Fin.val (j+1)) (dyadicScaleBit a j) := by
  unfold dyadicDistribution dyadicDilate
  rw [finite_pushforward_comp, finite_pushforward_comp]
  congr 1
  funext x
  apply Fin.ext
  dsimp [dyadicIndex,dyadicMultiplier,dyadicScaleBit]
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hj), Nat.add_assoc, pow_add, Nat.mul_mod_mul_left]

theorem dyadicDilate_bitBias_add {k a j : ℕ} (hj : a+(j+1) ≤ k)
    (p : Fin (2^k) → ℝ) :
    dyadicBitBias (dyadicDilate k a p) Fin.val (a+j) = dyadicBitBias p Fin.val j := by
  rw [dyadic_bitBias_eq_involution, dyadic_bitBias_eq_involution]
  rw [dyadicDilate_project_bit (by omega : a+j+1≤k)]
  have hh := involutionBias_pushforward (dyadicDistribution p Fin.val (j+1))
    (dyadicScaleBit a j) (dyadicScaleBit_injective _ _) (dyadicHalf j)
  rw [dyadicScaleBit_half] at hh
  exact hh

theorem dyadicDilate_bitBias {k a j : ℕ} (hj : j<k) (ha : a≤j)
    (p : Fin (2^k) → ℝ) :
    dyadicBitBias (dyadicDilate k a p) Fin.val j = dyadicBitBias p Fin.val (j-a) := by
  have he : a+(j-a)=j := Nat.add_sub_of_le ha
  have hh := dyadicDilate_bitBias_add (a:=a) (j:=j-a) (by omega : a+(j-a+1) ≤ k) p
  simpa only [he] using hh

theorem dyadicBitBias_le_one {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a=1) (j : ℕ) : dyadicBitBias p f j ≤ 1 := by
  rw [dyadic_bitBias_eq_involution]
  have hn := finite_pushforward_nonneg p (fun a => dyadicIndex (j+1) (f a)) hp
  have hs : finiteL1 (dyadicDistribution p f (j+1))=1 := by
    simp only [finiteL1, dyadicDistribution, abs_of_nonneg (hn _), finite_pushforward_sum, hsum]
  exact (involutionBias_le_l1 _ _).trans_eq hs

theorem dyadicDilate_nonneg {k a : ℕ} (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0 ≤ p x) (x : Fin (2^k)) : 0 ≤ dyadicDilate k a p x :=
  finite_pushforward_nonneg p _ hp x

theorem dyadicDilate_sum {k a : ℕ} (p : Fin (2^k) → ℝ) :
    ∑ x, dyadicDilate k a p x = ∑ x, p x := finite_pushforward_sum _ _

end
end Erdos18c
-- END external module DyadicDilations

-- BEGIN external module HarmonicMixing

open Finset
namespace Erdos18c
noncomputable section

def harmonicSum (k : ℕ) : ℝ := ∑ a ∈ range k, 1 / ((a:ℝ)+1)
def harmonicWeight (k a : ℕ) : ℝ := (1 / ((a:ℝ)+1)) / harmonicSum k
def harmonicLaw (k : ℕ) (p : Fin (2^k) → ℝ) : Fin (2^k) → ℝ :=
  finiteMixture (fun a : Fin k => harmonicWeight k a.val) (fun a => dyadicDilate k a.val p)

theorem harmonicSum_pos (k : ℕ) (hk : 0<k) : 0 < harmonicSum k := by
  have hb : (1:ℝ) ≤ harmonicSum k := by
    calc
      1 = 1 / ((0:ℝ)+1) := by norm_num
      _ ≤ _ := by
        simpa [harmonicSum] using single_le_sum (f := fun a : ℕ => 1/((a:ℝ)+1))
          (fun a _ => by positivity) (mem_range.mpr hk)
  linarith

theorem harmonicWeight_nonneg (k a : ℕ) : 0 ≤ harmonicWeight k a := by
  unfold harmonicWeight harmonicSum
  positivity

theorem harmonicWeight_sum (k : ℕ) (hk : 0<k) :
    ∑ a ∈ range k, harmonicWeight k a = 1 := by
  unfold harmonicWeight
  rw [← sum_div]
  change harmonicSum k / harmonicSum k = 1
  exact div_self (harmonicSum_pos k hk).ne'

theorem harmonicLaw_probability (k : ℕ) (hk : 0<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0≤p x) (hs : ∑ x, p x=1) :
    (∀ x, 0≤harmonicLaw k p x) ∧ ∑ x, harmonicLaw k p x=1 := by
  constructor
  · exact finiteMixture_nonneg _ _ (fun a => harmonicWeight_nonneg _ _)
      (fun a => dyadicDilate_nonneg p hp)
  · rw [harmonicLaw,sum_finiteMixture]
    simp_rw [dyadicDilate_sum, hs, mul_one]
    rw [Fin.sum_univ_eq_sum_range]
    exact harmonicWeight_sum k hk

def harmonicDefect (k j : ℕ) (p : Fin (2^k) → ℝ) : ℝ :=
  ∑ a ∈ range (j+1), harmonicWeight k a * dyadicMinority p Fin.val (j-a)

theorem harmonicDefect_lower (k j : ℕ) (hk : 0<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0≤p x) (c : ℝ)
    (hmass : c * (j+1:ℕ) ≤ ∑ t ∈ range (j+1), dyadicMinority p Fin.val t) :
    c / harmonicSum k ≤ harmonicDefect k j p := by
  have href : (∑ a ∈ range (j+1), dyadicMinority p Fin.val (j-a)) =
      ∑ t ∈ range (j+1), dyadicMinority p Fin.val t := by
    simpa using sum_range_reflect (dyadicMinority p Fin.val) (j+1)
  have hh := weighted_reciprocal_lower (range (j+1))
    (fun a => dyadicMinority p Fin.val (j-a)) (fun a => (a:ℝ)+1)
    (j+1:ℕ) (harmonicSum k) c (by positivity) (harmonicSum_pos k hk)
    (fun a _ => dyadicMinority_nonneg p Fin.val hp (j-a))
    (fun a ha => ⟨by positivity, by exact_mod_cast (mem_range.mp ha)⟩)
    (by rwa [href])
  apply hh.trans_eq
  unfold harmonicDefect harmonicWeight
  rw [sum_div]
  apply sum_congr rfl
  intro a _
  ring

theorem harmonicLaw_bias (k j : ℕ) (hj : j<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0≤p x) (hs : ∑ x,p x=1) :
    dyadicBitBias (harmonicLaw k p) Fin.val j ≤ 1 - harmonicDefect k j p := by
  have hk : 0<k := by omega
  let b := fun a : ℕ => dyadicBitBias (dyadicDilate k a p) Fin.val j
  have hble (a : ℕ) : b a ≤ 1 := by
    apply dyadicBitBias_le_one
    · exact dyadicDilate_nonneg p hp
    · rw [dyadicDilate_sum,hs]
  have hpos (a : ℕ) : 0 ≤ harmonicWeight k a * (1-b a) :=
    mul_nonneg (harmonicWeight_nonneg _ _) (sub_nonneg.mpr (hble a))
  have hpartial : harmonicDefect k j p ≤ ∑ a ∈ range k, harmonicWeight k a*(1-b a) := by
    calc
      _ = ∑ a ∈ range (j+1), harmonicWeight k a*(1-b a) := by
        apply sum_congr rfl
        intro a ha
        have haj : a≤j := by have := mem_range.mp ha; omega
        have hb := dyadicDilate_bitBias hj haj p
        have hu := dyadic_bitBias_add_minority p Fin.val hs (j-a)
        dsimp [b]
        rw [hb]
        congr 1
        linarith
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun a _ _ => hpos a)
  have htotal : (∑ a ∈ range k, harmonicWeight k a*(1-b a)) =
      1 - ∑ a ∈ range k, harmonicWeight k a*b a := by
    simp_rw [mul_sub, mul_one]
    rw [sum_sub_distrib,harmonicWeight_sum k hk]
  rw [htotal] at hpartial
  have hb : dyadicBitBias (harmonicLaw k p) Fin.val j ≤
      ∑ a ∈ range k, harmonicWeight k a*b a := by
    rw [dyadic_bitBias_eq_involution]
    change involutionBias (dyadicHalf j)
      (finitePushforward (harmonicLaw k p) (dyadicProject (Nat.succ_le_of_lt hj))) ≤ _
    rw [harmonicLaw,pushforward_finiteMixture]
    have hh := involutionBias_finiteMixture
      (fun a : Fin k => harmonicWeight k a.val)
      (fun a : Fin k => finitePushforward (dyadicDilate k a.val p) (dyadicProject (Nat.succ_le_of_lt hj)))
      (fun a => harmonicWeight_nonneg _ _) (dyadicHalf j)
    apply hh.trans_eq
    calc
      _ = ∑ a : Fin k, harmonicWeight k a.val * dyadicBitBias (dyadicDilate k a.val p) Fin.val j := by
        apply sum_congr rfl
        intro a _
        congr 1
        exact (dyadic_bitBias_eq_involution _ Fin.val j).symm
      _ = _ := Fin.sum_univ_eq_sum_range (fun a => harmonicWeight k a*b a) k
  linarith

theorem dyadicBitBias_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ) (f : ι → ℕ) (j : ℕ) :
    0 ≤ dyadicBitBias p f j := sum_nonneg fun _ _ => abs_nonneg _

theorem dyadic_entropy_lower_of_bias {k : ℕ} (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0≤p x) (hs : ∑ x,p x=1) (δ : ℝ)
    (hb : ∀ j<k, dyadicBitBias p Fin.val j ≤ δ) :
    (k:ℝ) * Real.log 2 * (1-δ) ≤ dyadicEntropy p Fin.val k := by
  have hlower : ∀ j∈range k, Real.log 2 * (1-δ) ≤
      dyadicEntropy p Fin.val (j+1)-dyadicEntropy p Fin.val j := by
    intro j hj
    have hbi := hb j (mem_range.mp hj)
    have he := dyadic_bitBias_add_minority p Fin.val hs j
    have hu : 1-δ ≤ dyadicMinority p Fin.val j := by linarith
    have hh := dyadic_entropy_step_lower p Fin.val hp j
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hu hlog]
  have hh := sum_le_sum hlower
  rw [dyadic_entropy_telescope p Fin.val hs] at hh
  simpa only [sum_const,card_range,nsmul_eq_mul,Nat.cast_id,mul_assoc] using hh

theorem harmonicLaw_power_entropy (k r : ℕ) (hk : 0<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x, 0≤p x) (hs : ∑ x,p x=1) (g : ℝ) (hg : 0≤g)
    (hprefix : ∀ L, 0<L → L≤k → g * L * Real.log 2 ≤ dyadicEntropy p Fin.val L) :
    (k:ℝ) * Real.log 2 *
      (1-Real.exp (-(r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k)) ≤
      dyadicEntropy (realConvolutionPow (harmonicLaw k p) r) Fin.val k := by
  let c := g^2*(Real.log 2)^2/2
  let t := c/harmonicSum k
  have hprob := harmonicLaw_probability k hk p hp hs
  have hout := realConvolutionPow_probability hprob.1 hprob.2 r
  apply dyadic_entropy_lower_of_bias _ hout.1 hout.2
  intro j hj
  have hm := dyadic_prefix_minority p Fin.val hp hs (j+1) (by omega) g hg
    (hprefix (j+1) (by omega) (by omega))
  have hdef := harmonicDefect_lower k j hk p hp c hm
  have hb0 := harmonicLaw_bias k j hj p hp hs
  have hb : dyadicBitBias (harmonicLaw k p) Fin.val j ≤ 1-t := by
    dsimp [t]
    linarith
  have hnonneg := dyadicBitBias_nonneg (harmonicLaw k p) Fin.val j
  have hbase : 0 ≤ 1-t := hnonneg.trans hb
  have hpwr := pow_le_pow_left₀ hnonneg hb r
  have hexp : 1-t ≤ Real.exp (-t) := by
    have hh := Real.add_one_le_exp (-t)
    linarith
  have hpowexp := pow_le_pow_left₀ hbase hexp r
  have hconv := dyadic_bitBias_convolutionPow (Nat.succ_le_of_lt hj) (harmonicLaw k p) r
  have hr := hconv.trans (hpwr.trans hpowexp)
  have he : Real.exp (-t) ^ r = Real.exp (-(r:ℝ)*c/harmonicSum k) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [t]
    ring
  rwa [he] at hr

theorem dyadicEntropy_full (k : ℕ) (p : Fin (2^k) → ℝ) :
    dyadicEntropy p Fin.val k = finiteEntropy univ p := by
  have hid (x : Fin (2^k)) : dyadicIndex k x.val = x := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt x.isLt
  have he : dyadicDistribution p Fin.val k = p := by
    funext x
    simp [dyadicDistribution,finitePushforward,hid,sum_filter]
  rw [dyadicEntropy,he]

def finiteSupport {ι : Type*} [Fintype ι] (p : ι → ℝ) : Finset ι :=
  univ.filter fun x => p x≠0

theorem harmonicLaw_support_large (k r : ℕ) (hk : 0<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x,0≤p x) (hs : ∑ x,p x=1) (g : ℝ) (hg : 0≤g)
    (hprefix : ∀ L,0<L → L≤k → g*L*Real.log 2 ≤ dyadicEntropy p Fin.val L)
    (hr : Real.log (2*(k:ℝ)) ≤ (r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k) :
    2^k < 2*(finiteSupport (realConvolutionPow (harmonicLaw k p) r)).card := by
  let P := realConvolutionPow (harmonicLaw k p) r
  let B := finiteSupport P
  have hprob := harmonicLaw_probability k hk p hp hs
  have hout := realConvolutionPow_probability hprob.1 hprob.2 r
  have hB : B.Nonempty := by
    by_contra hB
    have hz (x : Fin (2^k)) : P x=0 := by
      by_contra hx
      exact hB ⟨x,by simp [B,finiteSupport,hx]⟩
    have hzero : ∑ x,P x=0 := sum_eq_zero fun x _ => hz x
    have hone : ∑ x,P x=1 := hout.2
    linarith
  have hcardpos : (0:ℝ)<B.card := by exact_mod_cast card_pos.mpr hB
  have hb := finite_entropy_le_log_support P B hout.1 hout.2 (fun x hx => by
    by_contra hn
    exact hx (by simp [B,finiteSupport,hn]))
  have hmain := harmonicLaw_power_entropy k r hk p hp hs g hg hprefix
  rw [dyadicEntropy_full] at hmain
  change (k:ℝ)*Real.log 2*(1-Real.exp (-(r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k)) ≤ finiteEntropy univ P at hmain
  have hkp : (0:ℝ)<k := by exact_mod_cast hk
  have hexp := Real.exp_le_exp.mpr (neg_le_neg hr)
  have hrhs : Real.exp (-Real.log (2*(k:ℝ))) = (2*(k:ℝ))⁻¹ := by
    rw [Real.exp_neg,Real.exp_log (by positivity : (0:ℝ)<2*(k:ℝ))]
  rw [hrhs] at hexp
  have hdelta : (k:ℝ)*Real.exp (-(r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k) ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left hexp hkp.le
    have hid : (k:ℝ)*(2*(k:ℝ))⁻¹ = 1/2 := by field_simp
    have hneg : -((r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k) =
        -(r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k := by ring
    rwa [hid,hneg] at hh
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hdelta hlog.le
  have hlower : ((k:ℝ)-1/2)*Real.log 2 ≤ finiteEntropy univ P := by nlinarith
  by_contra hc
  have hc' : 2*B.card ≤ 2^k := Nat.le_of_not_gt hc
  have hcR : (B.card:ℝ) ≤ (2:ℝ)^k/2 := by
    have hh : (2:ℝ)*(B.card:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast hc'
    linarith
  have hlogB := Real.log_le_log hcardpos hcR
  rw [Real.log_div (by positivity : (2:ℝ)^k≠0) (by norm_num),Real.log_pow] at hlogB
  linarith

theorem harmonicLaw_covers (k r : ℕ) (hk : 0<k) (p : Fin (2^k) → ℝ)
    (hp : ∀ x,0≤p x) (hs : ∑ x,p x=1) (g : ℝ) (hg : 0≤g)
    (hprefix : ∀ L,0<L → L≤k → g*L*Real.log 2 ≤ dyadicEntropy p Fin.val L)
    (hr : Real.log (2*(k:ℝ)) ≤ (r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k)
    (x : Fin (2^k)) :
    ∃ a∈finiteSupport (realConvolutionPow (harmonicLaw k p) r),
    ∃ b∈finiteSupport (realConvolutionPow (harmonicLaw k p) r), a+b=x := by
  apply twice_card_cover
  simpa using harmonicLaw_support_large k r hk p hp hs g hg hprefix hr

end
end Erdos18c
-- END external module HarmonicMixing

-- BEGIN external module DigitInput

open Finset Filter
namespace Erdos18c
noncomputable section

def uniformDigitWeight (A : Finset ℕ) (_a : A) : ℝ := 1/(A.card:ℝ)
def uniformDigitProjection (A : Finset ℕ) (L : ℕ) : Fin (2^L) → ℝ :=
  dyadicDistribution (uniformDigitWeight A) (fun a => a.val) L
def positiveDigitWeight (A : Finset ℕ) (z : A × Fin 2) : ℝ := uniformDigitWeight A z.1 / 2
def positiveDigitValue (A : Finset ℕ) (z : A × Fin 2) : ℕ := z.1.val+z.2.val
def positiveDigitProjection (A : Finset ℕ) (L : ℕ) : Fin (2^L) → ℝ :=
  dyadicDistribution (positiveDigitWeight A) (positiveDigitValue A) L

theorem uniformDigitWeight_sum (A : Finset ℕ) (hA : A.Nonempty) :
    ∑ a : A, uniformDigitWeight A a = 1 := by
  have hc : (A.card:ℝ)≠0 := by exact_mod_cast (ne_of_gt (card_pos.mpr hA))
  simp only [uniformDigitWeight,sum_const,nsmul_eq_mul,card_univ,Fintype.card_coe]
  field_simp

theorem positiveDigitWeight_sum (A : Finset ℕ) (hA : A.Nonempty) :
    ∑ z : A × Fin 2, positiveDigitWeight A z = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [positiveDigitWeight,Fin.sum_univ_two]
  have he (a : A) : uniformDigitWeight A a / 2 + uniformDigitWeight A a / 2 = uniformDigitWeight A a := by ring
  simp_rw [he]
  exact uniformDigitWeight_sum A hA

theorem uniformDigitProjection_eq (A : Finset ℕ) (L : ℕ) (x : Fin (2^L)) :
    uniformDigitProjection A L x = natResidueMass A (2^L) x.val := by
  unfold uniformDigitProjection dyadicDistribution finitePushforward uniformDigitWeight
  rw [sum_filter,univ_eq_attach]
  change (∑ a ∈ A.attach, if dyadicIndex L a.val=x then 1/(A.card:ℝ) else 0) = _
  rw [sum_attach A (fun a : ℕ => if dyadicIndex L a=x then 1/(A.card:ℝ) else 0)]
  have he (a : ℕ) : dyadicIndex L a=x ↔ Nat.ModEq (2^L) a x.val := by
    simp only [Fin.ext_iff,dyadicIndex,Nat.ModEq,Nat.mod_eq_of_lt x.isLt]
  simp_rw [he]
  rw [← sum_filter]
  simp only [sum_const,nsmul_eq_mul,natResidueMass,natResidueFiber,div_eq_mul_inv,one_mul]

theorem dyadicIndex_add_one (L n : ℕ) :
    dyadicIndex L (n+1) = dyadicIndex L n + 1 := by
  apply Fin.ext
  simp [dyadicIndex,Fin.val_add,Nat.add_mod]

theorem positiveDigitProjection_smooth (A : Finset ℕ) (L : ℕ) (x : Fin (2^L)) :
    positiveDigitProjection A L x =
      (uniformDigitProjection A L x + uniformDigitProjection A L (x-1))/2 := by
  unfold positiveDigitProjection uniformDigitProjection dyadicDistribution finitePushforward
  rw [sum_filter,Fintype.sum_prod_type]
  have he (a : A) :
      (∑ e : Fin 2, if dyadicIndex L (positiveDigitValue A (a,e))=x then positiveDigitWeight A (a,e) else 0) =
      ((if dyadicIndex L a.val=x then uniformDigitWeight A a else 0) +
       (if dyadicIndex L a.val=x-1 then uniformDigitWeight A a else 0))/2 := by
    simp [Fin.sum_univ_two,positiveDigitValue,positiveDigitWeight,dyadicIndex_add_one,
      eq_sub_iff_add_eq,add_div]
    split_ifs <;> ring
  simp_rw [he]
  rw [← sum_div,sum_add_distrib]
  simp only [sum_filter]

theorem positiveDigitProjection_probability (A : Finset ℕ) (hA : A.Nonempty) (L : ℕ) :
    (∀ x,0≤positiveDigitProjection A L x) ∧ ∑ x,positiveDigitProjection A L x=1 := by
  refine ⟨finite_pushforward_nonneg _ _ (fun z => by unfold positiveDigitWeight uniformDigitWeight; positivity), ?_⟩
  rw [positiveDigitProjection,dyadicDistribution,finite_pushforward_sum,positiveDigitWeight_sum A hA]

theorem uniformDigitProjection_probability (A : Finset ℕ) (hA : A.Nonempty) (L : ℕ) :
    (∀ x,0≤uniformDigitProjection A L x) ∧ ∑ x,uniformDigitProjection A L x=1 := by
  refine ⟨finite_pushforward_nonneg _ _ (fun a => by unfold uniformDigitWeight; positivity), ?_⟩
  rw [uniformDigitProjection,dyadicDistribution,finite_pushforward_sum,uniformDigitWeight_sum A hA]

theorem odd_uniform_parity (A : Finset ℕ) (hA : A.Nonempty) (hodd : ∀ a∈A,Odd a) :
    uniformDigitProjection A 1 0=0 ∧ uniformDigitProjection A 1 1=1 := by
  have hzero : uniformDigitProjection A 1 0=0 := by
    rw [uniformDigitProjection_eq]
    have he : natResidueFiber A (2^1) 0=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨haA,haM⟩ := mem_filter.mp ha
      have hm : a%2=0 := by simpa [Nat.ModEq] using haM
      have ho : a%2=1 := Nat.odd_iff.mp (hodd a haA)
      omega
    norm_num only [pow_one] at he
    simp [natResidueMass,he]
  have hs := (uniformDigitProjection_probability A hA 1).2
  have hu : (univ : Finset (Fin (2^1)))={0,1} := by decide
  rw [hu,sum_pair (by decide),hzero,zero_add] at hs
  exact ⟨hzero,hs⟩

theorem positiveDigit_uniform_parity (A : Finset ℕ) (hA : A.Nonempty) (hodd : ∀ a∈A,Odd a)
    (x : Fin (2^1)) : positiveDigitProjection A 1 x=1/2 := by
  have h := odd_uniform_parity A hA hodd
  have hm1 : (-1 : Fin (2^1))=1 := by decide
  have hx : x=0 ∨ x=1 := by
    by_cases h0 : x=0
    · exact Or.inl h0
    · right
      apply Fin.ext
      change x.val=1
      have hn := x.isLt
      have hz : x.val≠0 := fun he => h0 (Fin.ext he)
      norm_num at hn
      omega
  rcases hx with rfl | rfl
  · rw [positiveDigitProjection_smooth,zero_sub,hm1,h.1,h.2]
    norm_num
  · rw [positiveDigitProjection_smooth,sub_self,h.1,h.2]
    norm_num

theorem positiveDigit_prefix_cap {F k u : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F k k u c A) (hc : c≤2)
    (L : ℕ) (hL : 0<L) (hLk : L≤k) (x : Fin (2^L)) :
    positiveDigitProjection A L x ≤ (2:ℝ)^(-(c/2)*(L:ℝ)) := by
  by_cases hL1 : L=1
  · subst L
    rw [positiveDigit_uniform_parity A hA.nonempty hA.odd]
    have hh : (2:ℝ)^(-1:ℝ) ≤ (2:ℝ)^(-(c/2)*(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    norm_num at hh ⊢
    exact hh
  · have hLL : 2≤L := by omega
    rw [positiveDigitProjection_smooth]
    have h1 := hA.spread L hLL hLk x.val
    have h2 := hA.spread L hLL hLk (x-1).val
    rw [← uniformDigitProjection_eq] at h1 h2
    linarith

theorem finiteEntropy_lower_of_cap {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ x,0≤p x) (hs : ∑ x,p x=1) (M : ℝ)
    (hcap : ∀ x,p x≤M) : -Real.log M ≤ finiteEntropy univ p := by
  have hh := sum_mul_log_le_log_bound univ p (fun x _ => hp x) (fun x _ => hcap x)
  rw [hs,one_mul] at hh
  have he : finiteEntropy univ p = -(∑ x,p x*Real.log (p x)) := by
    simp [finiteEntropy,Real.negMulLog_def,neg_mul,sum_neg_distrib]
  rw [he]
  linarith

theorem positiveDigit_entropy_prefix {F k u : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F k k u c A) (hc : c≤2)
    (L : ℕ) (hL : 0<L) (hLk : L≤k) :
    (c/2)*(L:ℝ)*Real.log 2 ≤ dyadicEntropy (positiveDigitProjection A k) Fin.val L := by
  have he : dyadicDistribution (positiveDigitProjection A k) Fin.val L = positiveDigitProjection A L :=
    dyadic_distribution_project (positiveDigitWeight A) (positiveDigitValue A) hLk
  unfold dyadicEntropy
  rw [he]
  have hp := positiveDigitProjection_probability A hA.nonempty L
  have hh := finiteEntropy_lower_of_cap _ hp.1 hp.2 _ (positiveDigit_prefix_cap hA hc L hL hLk)
  rw [Real.log_rpow (by norm_num : (0:ℝ)<2)] at hh
  linarith

end
end Erdos18c
-- END external module DigitInput

-- BEGIN external module LocalRepresentatives

open Finset Filter
namespace Erdos18c
noncomputable section

theorem finite_pushforward_support {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (p : ι → ℝ) (T : ι → κ) (x : κ) (hx : finitePushforward p T x≠0) :
    ∃ a,T a=x ∧ p a≠0 := by
  obtain ⟨a,ha,hpa⟩ := exists_ne_zero_of_sum_ne_zero hx
  exact ⟨a,(mem_filter.mp ha).2,hpa⟩

theorem dyadicIndex_add (k a b : ℕ) :
    dyadicIndex k (a+b) = dyadicIndex k a + dyadicIndex k b := by
  apply Fin.ext
  exact Nat.add_mod _ _ _

theorem dyadicIndex_scale (k a b : ℕ) :
    dyadicIndex k (2^a*b) = dyadicMultiplier k a (dyadicIndex k b) := by
  apply Fin.ext
  change (2^a*b)%2^k = (2^a*(b%2^k))%2^k
  simp [Nat.mul_mod]

theorem positiveDigitValue_repr {F k u : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F k k u c A) (z : A × Fin 2) :
    0<positiveDigitValue A z ∧ positiveDigitValue A z≤2^k ∧
      HasFactorialDivisorMultiset (F+2*k) (positiveDigitValue A z) (u+1) := by
  have hu := hA.representatives z.1.val z.1.property
  have hub := hA.bounded z.1.val z.1.property
  have huo : 0<z.1.val := by
    obtain ⟨t,ht⟩ := hA.odd z.1.val z.1.property
    omega
  have he := z.2.isLt
  refine ⟨by dsimp [positiveDigitValue]; omega,by dsimp [positiveDigitValue]; omega,?_⟩
  by_cases hz : z.2.val=0
  · have heq : positiveDigitValue A z=z.1.val := by dsimp [positiveDigitValue]; omega
    rw [heq]
    exact factorial_multiset_mono hu le_rfl (by omega)
  · have hz1 : z.2.val=1 := by omega
    have heq : positiveDigitValue A z=z.1.val+1 := by dsimp [positiveDigitValue]; omega
    rw [heq]
    exact factorial_multiset_add hu (factorial_multiset_singleton (one_dvd _))

theorem positiveDigit_support_repr {F k u : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F k k u c A) (x : Fin (2^k))
    (hx : positiveDigitProjection A k x≠0) :
    ∃ V,0<V ∧ V≤2^k ∧ dyadicIndex k V=x ∧
      HasFactorialDivisorMultiset (F+2*k) V (u+1) := by
  obtain ⟨z,hz,_⟩ := finite_pushforward_support (positiveDigitWeight A)
    (fun z => dyadicIndex k (positiveDigitValue A z)) x hx
  obtain ⟨hp,hbound,hr⟩ := positiveDigitValue_repr hA z
  exact ⟨positiveDigitValue A z,hp,hbound,hz,hr⟩

theorem factorial_multiset_shift {F k a R u : ℕ} (ha : a≤k)
    (h : HasFactorialDivisorMultiset F R u) :
    HasFactorialDivisorMultiset (F+2*k) (2^a*R) u := by
  obtain ⟨s,hs,hsum,hcard⟩ := h
  refine ⟨s.map (fun d => 2^a*d),?_,?_,?_⟩
  · intro x hx
    obtain ⟨d,hd,rfl⟩ := Multiset.mem_map.mp hx
    exact shifted_divisor_dvd_factorial (hs d hd) ha
  · simpa [hsum] using Multiset.sum_map_mul_left (s:=s) (a:=2^a) (f:=id)
  · simpa using hcard

theorem harmonic_support_repr {F k u : ℕ} {c : ℝ} {A : Finset ℕ}
    (hA : BinaryBlockProfile F k k u c A) (x : Fin (2^k))
    (hx : harmonicLaw k (positiveDigitProjection A k) x≠0) :
    ∃ V,0<V ∧ dyadicIndex k V=x ∧ HasFactorialDivisorMultiset (F+4*k) V (u+1) := by
  change (∑ a : Fin k, harmonicWeight k a.val * dyadicDilate k a.val (positiveDigitProjection A k) x)≠0 at hx
  obtain ⟨a,_,ha⟩ := exists_ne_zero_of_sum_ne_zero hx
  have hda : dyadicDilate k a.val (positiveDigitProjection A k) x≠0 := (mul_ne_zero_iff.mp ha).2
  obtain ⟨y,hy,hyp⟩ := finite_pushforward_support (positiveDigitProjection A k) (dyadicMultiplier k a.val) x hda
  obtain ⟨V,hV,_,heq,hrep⟩ := positiveDigit_support_repr hA y hyp
  refine ⟨2^a.val*V,by positivity,?_,?_⟩
  · rw [dyadicIndex_scale,heq]
    exact hy
  · have hh := factorial_multiset_shift (Nat.le_of_lt a.isLt) hrep
    convert hh using 1; omega

theorem convolutionPow_actual_repr {k F u : ℕ} (f : Fin (2^k) → ℝ)
    (hrep : ∀ x, f x≠0 → ∃ V,0<V ∧ dyadicIndex k V=x ∧ HasFactorialDivisorMultiset F V u)
    (r : ℕ) (x : Fin (2^k)) (hx : realConvolutionPow f r x≠0) :
    ∃ S, dyadicIndex k S=x ∧ HasFactorialDivisorMultiset F S (r*u) ∧ (0<r → 0<S) := by
  induction r generalizing x with
  | zero =>
    have hx0 : x=0 := by by_contra h; simp [realConvolutionPow,h] at hx
    subst x
    exact ⟨0,by simp [dyadicIndex],factorial_multiset_zero _ _,by omega⟩
  | succ r ih =>
    change (∑ a : Fin (2^k), f a * realConvolutionPow f r (x-a))≠0 at hx
    obtain ⟨a,_,ha⟩ := exists_ne_zero_of_sum_ne_zero hx
    obtain ⟨V,hV,heV,hVrep⟩ := hrep a (mul_ne_zero_iff.mp ha).1
    obtain ⟨S,heS,hSrep,_⟩ := ih (x-a) (mul_ne_zero_iff.mp ha).2
    refine ⟨V+S,?_,?_,by omega⟩
    · rw [dyadicIndex_add,heV,heS]
      abel
    · simpa only [Nat.succ_mul,Nat.add_comm] using factorial_multiset_add hVrep hSrep

theorem modular_representatives_of_profile {F k u r : ℕ} {c : ℝ} {A : Finset ℕ}
    (hk : 0<k) (hA : BinaryBlockProfile F k k u c A) (hc0 : 0≤c) (hc : c≤2)
    (hr : Real.log (2*(k:ℝ)) ≤ (r:ℝ)*((c/2)^2*(Real.log 2)^2/2)/harmonicSum k)
    (R : ℕ) :
    ∃ S,0<S ∧ dyadicIndex k S=dyadicIndex k R ∧
      HasFactorialDivisorMultiset (F+4*k) S (2*r*(u+1)) := by
  have hp := positiveDigitProjection_probability A hA.nonempty k
  have hpre := positiveDigit_entropy_prefix hA hc
  obtain ⟨a,ha,b,hb,heq⟩ := harmonicLaw_covers k r hk (positiveDigitProjection A k)
    hp.1 hp.2 (c/2) (by linarith) hpre hr (dyadicIndex k R)
  have hrepr := harmonic_support_repr hA
  obtain ⟨V,hV,hVrep,hVpos⟩ := convolutionPow_actual_repr _ hrepr r a (by simpa [finiteSupport] using ha)
  obtain ⟨W,hW,hWrep,_⟩ := convolutionPow_actual_repr _ hrepr r b (by simpa [finiteSupport] using hb)
  have hrpos : 0<r := by
    by_contra hn
    have hz : r=0 := by omega
    have hlog : 0<Real.log (2*(k:ℝ)) := Real.log_pos (by
      have hkR : (1:ℝ)≤k := by exact_mod_cast hk
      linarith)
    simp only [hz,Nat.cast_zero,zero_mul,zero_div] at hr
    linarith
  refine ⟨V+W,by have := hVpos hrpos; omega,?_,?_⟩
  · rw [dyadicIndex_add,hV,hW]
    exact heq
  · have hh := factorial_multiset_add hVrep hWrep
    convert hh using 1; ring

end
end Erdos18c
-- END external module LocalRepresentatives

-- BEGIN external module LocalBounds

open Finset Filter
namespace Erdos18c
noncomputable section

def localCopies (k : ℕ) : ℕ := ⌈32768*(Real.log (k:ℝ))^4⌉₊+1
def localCount (k : ℕ) : ℕ := 2*localCopies k*(binaryLength k+2)
def localHost (k : ℕ) : ℕ := linearDigitHost k+4*k
def localHeight (k : ℕ) : ℕ := localCount k*(localHost k).factorial

theorem factorial_multiset_height {F R u : ℕ} (h : HasFactorialDivisorMultiset F R u) :
    R≤u*F.factorial := by
  obtain ⟨s,hs,hsum,hcard⟩ := h
  have hh := Multiset.sum_le_card_nsmul s F.factorial
    (fun d hd => Nat.le_of_dvd (Nat.factorial_pos _) (hs d hd))
  rw [hsum] at hh
  exact hh.trans (by simpa using Nat.mul_le_mul_right F.factorial hcard)

theorem localCount_pos (k : ℕ) : 0<localCount k := by
  unfold localCount localCopies
  positivity

theorem localHeight_pos (k : ℕ) : 0<localHeight k :=
  Nat.mul_pos (localCount_pos k) (Nat.factorial_pos _)

theorem harmonicSum_le (k : ℕ) : harmonicSum k ≤ 1+Real.log (k:ℝ) := by
  have he : harmonicSum k = (harmonic k : ℝ) := by
    simp [harmonicSum,harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
  rw [he]
  exact harmonic_le_one_add_log k

theorem eventually_local_copy_condition : ∀ᶠ k : ℕ in atTop,
    Real.log (2*(k:ℝ)) ≤ (localCopies k:ℝ)*
      ((linearDigitRate k/2)^2*(Real.log 2)^2/2)/harmonicSum k := by
  have htend : Tendsto (fun k : ℕ => Real.log (k:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop (max 1 (Real.log 1000)), eventually_ge_atTop 2] with k ht hk
  let t := Real.log (k:ℝ)
  have ht1 : 1≤t := (le_max_left _ _).trans ht
  have ht1000 : Real.log 1000≤t := (le_max_right _ _).trans ht
  have hkp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hH : harmonicSum k≤2*t := (harmonicSum_le k).trans (by dsimp [t]; linarith)
  have hH0 := (harmonicSum_pos k (by omega)).le
  have hL : Real.log (linearDigitHost k:ℝ)≤2*t := by
    simp only [linearDigitHost,Nat.cast_mul,Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num) hkp.ne']
    dsimp [t] at *
    linarith
  have hLp : 0<Real.log (linearDigitHost k:ℝ) := Real.log_pos (by
    simp only [linearDigitHost,Nat.cast_mul,Nat.cast_ofNat]
    have h1 : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
    linarith)
  have hlog2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hhalf : (1/2:ℝ)≤Real.log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
  have h2t : Real.log (2*(k:ℝ))≤2*t := by
    rw [Real.log_mul (by norm_num) hkp.ne']
    have : Real.log 2≤1 := le_trans Real.log_two_lt_d9.le (by norm_num)
    dsimp [t] at *
    linarith
  have hlog2k0 : 0≤Real.log (2*(k:ℝ)) := Real.log_nonneg (by
    have : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
    linarith)
  have hden : 0<(linearDigitRate k/2)^2*(Real.log 2)^2 := by
    unfold linearDigitRate linearDigitDelta
    positivity
  have hreq : 2*harmonicSum k*Real.log (2*(k:ℝ)) /
      ((linearDigitRate k/2)^2*(Real.log 2)^2) ≤ (localCopies k:ℝ) := by
    calc
      _ = 512*harmonicSum k*Real.log (2*(k:ℝ)) * Real.log (linearDigitHost k:ℝ)^2 /
          (Real.log 2)^2 := by
        unfold linearDigitRate linearDigitDelta
        field_simp
        ring
      _ ≤ 512*(2*t)*(2*t)*(2*t)^2/((1/2:ℝ)^2) := by
        gcongr
      _ = 32768*t^4 := by ring
      _ ≤ _ := by
        have hh := Nat.le_ceil (32768*t^4)
        have hstep : (⌈32768*t^4⌉₊:ℝ) ≤ localCopies k := by
          dsimp [localCopies,t]
          exact_mod_cast (Nat.le_succ _)
        exact hh.trans hstep
  have hscaled := (div_le_iff₀ hden).mp hreq
  apply (le_div_iff₀ (harmonicSum_pos k (by omega))).mpr
  nlinarith

theorem eventually_local_count_bound : ∀ᶠ k : ℕ in atTop,
    (localCount k:ℝ)≤400000*(Real.log (k:ℝ))^5 := by
  have htend : Tendsto (fun k : ℕ => Real.log (k:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop 1,eventually_ge_atTop 2] with k ht hk
  let t := Real.log (k:ℝ)
  have ht4 : 1≤t^4 := one_le_pow₀ ht
  have hceil := (Nat.ceil_lt_add_one (show 0≤32768*t^4 by positivity)).le
  have hr : (localCopies k:ℝ)≤32770*t^4 := by
    dsimp [localCopies]
    push_cast
    dsimp [t] at *
    linarith
  have hb : (binaryLength k:ℝ)+2 ≤ 6*t := by
    have hh := binaryLength_log_upper k hk
    dsimp [t] at *
    linarith
  calc
    (localCount k:ℝ) = 2*(localCopies k:ℝ)*((binaryLength k:ℝ)+2) := by simp [localCount]
    _ ≤ 2*(32770*t^4)*(6*t) := by gcongr
    _ ≤ 400000*t^5 := by nlinarith [pow_nonneg (by linarith : 0≤t) 5]

theorem eventually_local_representatives : ∀ᶠ k : ℕ in atTop,
    ∀ R : ℕ, ∃ S,0<S ∧ dyadicIndex k S=dyadicIndex k R ∧
      HasFactorialDivisorMultiset (localHost k) S (localCount k) := by
  filter_upwards [eventually_linear_digit_profile,eventually_local_copy_condition,eventually_ge_atTop 1] with k hp hr hk
  intro R
  have hh := modular_representatives_of_profile hk hp.2.2
    (by unfold linearDigitRate; linarith [hp.1])
    (by unfold linearDigitRate; linarith [hp.2.1]) hr R
  exact hh

theorem eventually_local_height_bound : ∀ᶠ k : ℕ in atTop,
    Real.log (localHeight k:ℝ) ≤ 4096*(k:ℝ)*Real.log (k:ℝ) := by
  have htend : Tendsto (fun k : ℕ => Real.log (k:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_local_count_bound,htend.eventually_ge_atTop
    (max 1 (max (Real.log 400000) (Real.log 1004))),eventually_ge_atTop 2] with k hcount ht hk
  let t := Real.log (k:ℝ)
  have ht1 : 1≤t := (le_max_left _ _).trans ht
  have htC : Real.log 400000≤t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htF : Real.log 1004≤t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hkp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hCpos : (0:ℝ)<localCount k := by exact_mod_cast localCount_pos k
  have hlogC : Real.log (localCount k:ℝ)≤6*t := by
    have hh := Real.log_le_log hCpos hcount
    rw [Real.log_mul (by norm_num) (by positivity : t^5≠0),Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    have hlogt : Real.log t≤t := (Real.log_le_sub_one_of_pos (by linarith : 0<t)).trans (by linarith)
    linarith
  have hFval : (localHost k:ℝ)=1004*(k:ℝ) := by simp [localHost,linearDigitHost]; ring
  have hFpos : (0:ℝ)<localHost k := by rw [hFval]; positivity
  have hlogF : Real.log (localHost k:ℝ)≤2*t := by
    rw [hFval,Real.log_mul (by norm_num) hkp.ne']
    dsimp [t] at *
    linarith
  have hfact : Real.log ((localHost k).factorial:ℝ) ≤ (localHost k:ℝ)*Real.log (localHost k:ℝ) := by
    have hh : ((localHost k).factorial:ℝ) ≤ (localHost k:ℝ)^(localHost k) := by
      exact_mod_cast Nat.factorial_le_pow (localHost k)
    have hp : (0:ℝ)<(localHost k).factorial := by exact_mod_cast Nat.factorial_pos _
    have hl := Real.log_le_log hp hh
    rwa [Real.log_pow] at hl
  have hprod := mul_le_mul_of_nonneg_left hlogF hFpos.le
  have hk1 : (1:ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
  have hkt : 0≤((k:ℝ)-1)*t := mul_nonneg (by linarith) (by linarith)
  change Real.log ((localCount k*(localHost k).factorial:ℕ):ℝ) ≤ _
  rw [Nat.cast_mul,Real.log_mul hCpos.ne' (by exact_mod_cast Nat.factorial_ne_zero _)]
  rw [hFval] at hprod
  nlinarith

end
end Erdos18c
-- END external module LocalBounds


-- BEGIN optimized H1 digit-supply adapter

open Finset Filter
namespace Erdos18c

theorem choose_lower_sharp_ratio {n v : ℕ} (hv : 0 < v) (_hvn : v ≤ n+1) :
    (((n + 1 - v : ℕ) : ℝ) / (v : ℝ)) ^ v ≤ (n.choose v : ℝ) := by
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
  have hfac : (v.factorial : ℝ) ≤ (v : ℝ) ^ v := by exact_mod_cast Nat.factorial_le_pow v
  calc
    (((n + 1 - v : ℕ) : ℝ) / (v : ℝ)) ^ v =
        ((n + 1 - v : ℕ) : ℝ) ^ v / (v : ℝ) ^ v := div_pow _ _ _
    _ ≤ ((n + 1 - v : ℕ) : ℝ) ^ v / (v.factorial : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hfac
    _ ≤ (n.choose v : ℝ) := Nat.pow_le_choose v n

theorem eventually_primeCounting_two_thirds : ∀ᶠ F : ℕ in atTop,
    (2/3:ℝ)*(F:ℝ)/Real.log (F:ℝ) ≤ (Nat.primeCounting F : ℝ) := by
  have hsmall := (Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop (R:=ℝ))).def (by norm_num : (0:ℝ)<1/100)
  have hsucc : Tendsto (fun n : ℕ => n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  filter_upwards [hsucc.eventually hsmall, eventually_ge_atTop 2] with F hs hF
  have hpos : (0:ℝ)<F := by exact_mod_cast (show 0<F by omega)
  have hlogpos : 0<Real.log (F:ℝ) := Real.log_pos (by exact_mod_cast hF)
  have hnorm : |Real.log ((F+1:ℕ):ℝ)| ≤ (1/100) * (((F+1:ℕ):ℝ)) := by
    simp only [Function.comp_apply,id_eq,Real.norm_eq_abs] at hs
    rwa [abs_of_nonneg (show (0:ℝ)≤((F+1:ℕ):ℝ) by positivity)] at hs
  have hlogsmall : Real.log ((F+1:ℕ):ℝ) ≤ (((F+1:ℕ):ℝ))/100 := by
    exact (le_abs_self _).trans (by simpa [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hnorm)
  have hnum : (2/3:ℝ)*(F:ℝ) ≤ (F:ℝ)*Real.log 2 - Real.log ((F+1:ℕ):ℝ) := by
    have htwo := Real.log_two_gt_d9
    push_cast at hlogsmall
    have h1 : (1:ℝ)≤F := by exact_mod_cast (show 1≤F by omega)
    push_cast
    have hprod : (0.6931471803:ℝ)*(F:ℝ) ≤ (F:ℝ)*Real.log 2 := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left htwo.le hpos.le
    nlinarith
  have hprime := Chebyshev.pi_ge F
  have hh := div_le_div_of_nonneg_right hnum hlogpos.le
  calc
    (2/3:ℝ)*(F:ℝ)/Real.log (F:ℝ) = ((2/3:ℝ)*(F:ℝ))/Real.log (F:ℝ) := by ring
    _ ≤ _ := hh
    _ ≤ _ := by simpa only [Nat.cast_add,Nat.cast_one] using hprime

theorem two_rpow_fourteen_thirds_lt_twentyseven : (2:ℝ)^((14/3:ℝ)) < 27 := by
  have h1 : ((2:ℝ)^((14/3:ℝ)))^3 < (27:ℝ)^3 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2) (14/3:ℝ) 3]
    norm_num
  have ha : 0 ≤ (2:ℝ)^((14/3:ℝ)) := by positivity
  nlinarith [sq_nonneg ((27:ℝ) + (2:ℝ)^((14/3:ℝ))), sq_nonneg ((27:ℝ) - (2:ℝ)^((14/3:ℝ)))]


theorem shortFactorialDigits_host30_sharp {k l : ℕ}
    (hk : 2 ≤ k)
    (hklog3 : 3 ≤ Real.log (k : ℝ))
    (hklog30 : Real.log 30 ≤ (1/200 : ℝ) * Real.log (k : ℝ))
    (hklog1 : (1 : ℝ) ≤ (1/200 : ℝ) * Real.log (k : ℝ))
    (hkbig : 2 ^ 454 ≤ 30 * k + 1)
    (hprime : (2/3 : ℝ) * (30*k : ℕ) / Real.log ((30*k : ℕ) : ℝ) ≤
      (Nat.primeCounting (30*k) : ℝ))
    (hl : 1 ≤ l) (hlk : l ≤ k) :
    (2 : ℝ) ^ ((3 / Real.log (k : ℝ)) * (l : ℝ)) ≤
      (shortFactorialDigits (30*k) l).card := by
  let F : ℕ := 30*k
  let a : ℕ := binaryLength F
  have hF : 2 ≤ F := by dsimp [F]; omega
  have hFposNat : 0 < F := by omega
  have hFpos : (0:ℝ) < F := by exact_mod_cast hFposNat
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hklogpos : 0 < Real.log (k : ℝ) := by linarith
  have hlogFpos : 0 < Real.log (F : ℝ) := Real.log_pos (by exact_mod_cast hF)
  have hFval : (F : ℝ) = 30 * (k : ℝ) := by simp [F]
  have hlogFle : Real.log (F : ℝ) ≤ (201/200 : ℝ) * Real.log (k : ℝ) := by
    rw [hFval, Real.log_mul (by norm_num) hkpos.ne']
    linarith
  have haNat : 0 < a := binaryLength_pos F
  have haR : (0:ℝ) < a := by exact_mod_cast haNat
  by_cases hsmall : l ≤ 100 * a
  · have haEight : (a : ℝ) ≤ (121/80 : ℝ) * Real.log (k : ℝ) := by
      have hlog23 : (2/3 : ℝ) ≤ Real.log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
      have hlogFover : Real.log (F : ℝ) / Real.log 2 ≤ (3/2 : ℝ) * Real.log (F : ℝ) := by
        rw [div_le_iff₀ (by positivity : 0 < Real.log 2)]
        have hprod := mul_le_mul_of_nonneg_left hlog23 hlogFpos.le
        nlinarith only [hprod, hlogFpos]
      have hpowlog : (2:ℝ) ^ (Nat.log 2 F) ≤ (F : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega : F ≠ 0)
      have hlogpow := Real.log_le_log (by positivity : (0:ℝ) < 2^(Nat.log 2 F)) hpowlog
      rw [Real.log_pow] at hlogpow
      have hnle : (Nat.log 2 F : ℝ) ≤ Real.log (F : ℝ) / Real.log 2 :=
        (le_div_iff₀ (by positivity : 0 < Real.log 2)).mpr hlogpow
      have haub : (a : ℝ) ≤ Real.log (F : ℝ) / Real.log 2 + 1 := by
        dsimp [a,binaryLength]
        push_cast
        linarith
      have hscale := mul_le_mul_of_nonneg_left hlogFle (by norm_num : (0:ℝ) ≤ 3/2)
      calc
        (a : ℝ) ≤ Real.log (F : ℝ) / Real.log 2 + 1 := haub
        _ ≤ (3/2 : ℝ) * Real.log (F : ℝ) + 1 := add_le_add hlogFover le_rfl
        _ ≤ (3/2 : ℝ) * ((201/200 : ℝ) * Real.log (k : ℝ)) +
            (1/200 : ℝ) * Real.log (k : ℝ) := add_le_add hscale hklog1
        _ = (121/80 : ℝ) * Real.log (k : ℝ) := by ring
    have hexp : (3 / Real.log (k : ℝ)) * (l : ℝ) ≤ 454 := by
      have hlreal : (l : ℝ) ≤ 100 * (a : ℝ) := by exact_mod_cast hsmall
      have h1 : (3 / Real.log (k : ℝ)) * (l : ℝ) ≤
          (3 / Real.log (k : ℝ)) * (100 * (a : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hlreal (by positivity)
      have h2 : (3 / Real.log (k : ℝ)) * (100 * (a : ℝ)) ≤ 454 := by
        rw [show (3 / Real.log (k : ℝ)) * (100 * (a : ℝ)) =
          (300 * (a : ℝ)) / Real.log (k : ℝ) by ring]
        rw [div_le_iff₀ hklogpos]
        nlinarith only [haEight]
      exact h1.trans h2
    have hcoeffle : (3 / Real.log (k : ℝ)) ≤ 1 := by
      rw [div_le_one hklogpos]
      exact hklog3
    have hfirst : (2 : ℝ) ^ ((3 / Real.log (k : ℝ)) * (l : ℝ)) ≤ (F + 1 : ℕ) := by
      calc
        (2 : ℝ) ^ ((3 / Real.log (k : ℝ)) * (l : ℝ)) ≤ (2 : ℝ) ^ (454 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = ((2 ^ 454 : ℕ) : ℝ) := by
          norm_num only [Nat.cast_pow, Nat.cast_ofNat]
          exact Real.rpow_natCast 2 454
        _ ≤ (F + 1 : ℕ) := by
          have hb : 2 ^ 454 ≤ F + 1 := by
            change 2 ^ 454 ≤ 30 * k + 1
            exact hkbig
          exact_mod_cast hb
    have hsecond : (2 : ℝ) ^ ((3 / Real.log (k : ℝ)) * (l : ℝ)) ≤ ((2 ^ l : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hlnonneg : (0:ℝ) ≤ l := Nat.cast_nonneg l
      nlinarith only [hcoeffle, hlnonneg]
    have hmin : (2 : ℝ) ^ ((3 / Real.log (k : ℝ)) * (l : ℝ)) ≤
        (min (F + 1) (2 ^ l) : ℕ) := by
      rw [Nat.cast_min]
      exact le_min hfirst hsecond
    exact hmin.trans (by exact_mod_cast shortFactorialDigits_small_integers (F := F) (l := l))
  · let v : ℕ := (l - 1) / a
    have hla : a < l := by omega
    have hvpos : 0 < v := Nat.div_pos (by omega) (by omega)
    have hmul : a * v ≤ l - 1 := Nat.mul_div_le (l - 1) a
    have hheight : F ^ v < 2 ^ l := by
      calc
        F ^ v ≤ (2 ^ a) ^ v := Nat.pow_le_pow_left
          (Nat.lt_pow_succ_log_self (by decide : 1 < 2) F).le v
        _ = 2 ^ (a * v) := (pow_mul _ _ _).symm
        _ < 2 ^ l := Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    let n : ℕ := Nat.primeCounting F
    have hvposR : (0:ℝ) < v := by exact_mod_cast hvpos
    have hmulR : (a:ℝ) * (v:ℝ) ≤ (l:ℝ) := by
      have hh : (a:ℝ) * (v:ℝ) ≤ ((l-1:ℕ):ℝ) := by exact_mod_cast hmul
      have hcastl : ((l - 1 : ℕ) : ℝ) = (l:ℝ) - 1 := by
        simpa using Nat.cast_sub (R := ℝ) hl
      rw [hcastl] at hh
      linarith
    have hvupper_l : (v:ℝ) ≤ (l:ℝ)/(a:ℝ) :=
      (le_div_iff₀ haR).mpr (by nlinarith only [hmulR])
    have hvupper_k : (v:ℝ) ≤ (k:ℝ)/(a:ℝ) := by
      have hlkR : (l:ℝ) ≤ k := by exact_mod_cast hlk
      have hdiv : (l:ℝ)/(a:ℝ) ≤ (k:ℝ)/(a:ℝ) :=
        div_le_div_of_nonneg_right hlkR haR.le
      exact hvupper_l.trans hdiv
    have hFlt2a : (F:ℝ) < (2:ℝ)^a := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) F
    have hlogFlt : Real.log (F:ℝ) < (a:ℝ)*Real.log 2 := by
      have hh := Real.log_lt_log hFpos hFlt2a
      rwa [Real.log_pow] at hh
    have hlogF_lt_seven : Real.log (F:ℝ) < (7/10:ℝ)*(a:ℝ) := by
      have hlog2lt : Real.log 2 < (7/10:ℝ) := lt_trans Real.log_two_lt_d9 (by norm_num)
      have hh := mul_lt_mul_of_pos_right hlog2lt haR
      nlinarith only [hlogFlt, hh]
    have hprimeF : (2/3:ℝ)*(F:ℝ)/Real.log (F:ℝ) ≤ (n:ℝ) := by
      simpa [F,n] using hprime
    have hnvgt : (200/7:ℝ) < (n:ℝ)/(v:ℝ) := by
      have hvupper_natCast : (v:ℝ) ≤ (k:ℝ)/(a:ℝ) := hvupper_k
      have hApos : (0:ℝ) ≤ (2/3:ℝ)*(F:ℝ)/Real.log (F:ℝ) := by positivity
      have hstep1 : ((2/3:ℝ)*(F:ℝ)/Real.log (F:ℝ))/(v:ℝ) ≤ (n:ℝ)/(v:ℝ) :=
        div_le_div_of_nonneg_right hprimeF hvposR.le
      have hstep2 : ((2/3:ℝ)*(F:ℝ)/Real.log (F:ℝ))/((k:ℝ)/(a:ℝ)) ≤
          ((2/3:ℝ)*(F:ℝ)/Real.log (F:ℝ))/(v:ℝ) :=
        div_le_div_of_nonneg_left hApos hvposR hvupper_natCast
      have heq : ((2/3:ℝ)*(F:ℝ)/Real.log (F:ℝ))/((k:ℝ)/(a:ℝ)) =
          20*(a:ℝ)/Real.log (F:ℝ) := by
        rw [hFval]
        field_simp [hkpos.ne', haR.ne', hlogFpos.ne']
        ring
      have hcore : (200/7:ℝ) < 20*(a:ℝ)/Real.log (F:ℝ) := by
        have hmul : (10/7:ℝ)*Real.log (F:ℝ) < (a:ℝ) := by
          nlinarith only [hlogF_lt_seven]
        have hdiv : (10/7:ℝ) < (a:ℝ)/Real.log (F:ℝ) :=
          (lt_div_iff₀ hlogFpos).mpr (by nlinarith only [hmul])
        have hmul20 := mul_lt_mul_of_pos_right hdiv (by norm_num : (0:ℝ)<20)
        calc
          (200/7:ℝ) = (10/7:ℝ) * 20 := by norm_num
          _ < ((a:ℝ)/Real.log (F:ℝ)) * 20 := hmul20
          _ = 20*(a:ℝ)/Real.log (F:ℝ) := by ring
      rw [heq] at hstep2
      exact hcore.trans_le (hstep2.trans hstep1)
    have hvn1 : v ≤ n + 1 := by
      have hlt : (v:ℝ) < n := by
        have h1 : (1:ℝ) < (n:ℝ)/(v:ℝ) := by linarith
        have hh := (one_lt_div hvposR).mp h1
        exact hh
      have hnat : v < n := by exact_mod_cast hlt
      omega
    have hR : (27 : ℝ) ≤ (((n + 1 - v : ℕ) : ℝ) / (v : ℝ)) := by
      have hcast : ((n + 1 - v : ℕ) : ℝ) = (n:ℝ) + 1 - (v:ℝ) := by
        have hh : ((n + 1 - v : ℕ) : ℝ) = ((n+1:ℕ):ℝ) - (v:ℝ) := by
          simpa using Nat.cast_sub (R := ℝ) hvn1
        push_cast at hh
        exact hh
      have hshape : (((n + 1 - v : ℕ) : ℝ) / (v : ℝ)) = ((n:ℝ)+1)/(v:ℝ)-1 := by
        rw [hcast]
        field_simp [hvposR.ne'] <;> ring
      have hlt : (193/7:ℝ) < ((n:ℝ)+1)/(v:ℝ)-1 := by
        have hposinv : (0:ℝ) < 1/(v:ℝ) := by positivity
        have hrewrite : ((n:ℝ)+1)/(v:ℝ)-1 = (n:ℝ)/(v:ℝ)-1+1/(v:ℝ) := by
          field_simp [hvposR.ne'] <;> ring
        nlinarith only [hnvgt, hposinv, hrewrite]
      rw [hshape]
      linarith
    have hexpkey : (3 / Real.log (k : ℝ)) * (l : ℝ) ≤ (14/3 : ℝ) * (v : ℝ) := by
      have haSharp : (a : ℝ) ≤ (121/80 : ℝ) * Real.log (k : ℝ) := by
        have hlog23 : (2/3 : ℝ) ≤ Real.log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
        have hlogFover : Real.log (F : ℝ) / Real.log 2 ≤ (3/2 : ℝ) * Real.log (F : ℝ) := by
          rw [div_le_iff₀ (by positivity : 0 < Real.log 2)]
          have hprod := mul_le_mul_of_nonneg_left hlog23 hlogFpos.le
          nlinarith only [hprod, hlogFpos]
        have hpowlog : (2:ℝ) ^ (Nat.log 2 F) ≤ (F : ℝ) := by
          exact_mod_cast Nat.pow_log_le_self 2 (by omega : F ≠ 0)
        have hlogpow := Real.log_le_log (by positivity : (0:ℝ) < 2^(Nat.log 2 F)) hpowlog
        rw [Real.log_pow] at hlogpow
        have hnle : (Nat.log 2 F : ℝ) ≤ Real.log (F : ℝ) / Real.log 2 :=
          (le_div_iff₀ (by positivity : 0 < Real.log 2)).mpr hlogpow
        have haub : (a : ℝ) ≤ Real.log (F : ℝ) / Real.log 2 + 1 := by
          dsimp [a,binaryLength]
          push_cast
          linarith
        have hscale := mul_le_mul_of_nonneg_left hlogFle (by norm_num : (0:ℝ) ≤ 3/2)
        calc
          (a : ℝ) ≤ Real.log (F : ℝ) / Real.log 2 + 1 := haub
          _ ≤ (3/2 : ℝ) * Real.log (F : ℝ) + 1 := add_le_add hlogFover le_rfl
          _ ≤ (3/2 : ℝ) * ((201/200 : ℝ) * Real.log (k : ℝ)) +
              (1/200 : ℝ) * Real.log (k : ℝ) := add_le_add hscale hklog1
          _ = (121/80 : ℝ) * Real.log (k : ℝ) := by ring
      have hsucc : l - 1 < a * (v + 1) := Nat.lt_mul_div_succ (l - 1) haNat
      have hsuccR : (l:ℝ) < (a:ℝ)*((v:ℝ)+1)+1 := by
        have hh : ((l-1:ℕ):ℝ) < (a:ℝ)*((v:ℝ)+1) := by exact_mod_cast hsucc
        have hcastl : ((l - 1 : ℕ) : ℝ) = (l:ℝ) - 1 := by
          simpa using Nat.cast_sub (R := ℝ) hl
        rw [hcastl] at hh
        linarith
      have hlargeR : 100*(a:ℝ) < (l:ℝ) := by exact_mod_cast (show 100*a<l by omega)
      have hlowerav : (49/50:ℝ)*(l:ℝ) ≤ (a:ℝ)*(v:ℝ) := by
        have haOneR : (1:ℝ) ≤ a := by exact_mod_cast haNat
        have hlinear : (49/50:ℝ)*(l:ℝ) ≤ (l:ℝ) - (a:ℝ) - 1 := by
          nlinarith only [hlargeR, haOneR]
        have hshift : (l:ℝ) - (a:ℝ) - 1 ≤ (a:ℝ)*(v:ℝ) := by
          nlinarith only [hsuccR]
        exact hlinear.trans hshift
      have hvlower : (49/50:ℝ)*((l:ℝ)/(a:ℝ)) ≤ (v:ℝ) := by
        have hh : ((49/50:ℝ)*(l:ℝ))/(a:ℝ) ≤ (v:ℝ) :=
          (div_le_iff₀ haR).mpr (by nlinarith only [hlowerav])
        simpa [mul_div_assoc] using hh
      have haMul : (a:ℝ) ≤ (343/225:ℝ)*Real.log (k:ℝ) := by
        nlinarith only [haSharp]
      have hcoeff0 : (3*(a:ℝ))/Real.log (k:ℝ) ≤ (343/75:ℝ) := by
        rw [div_le_iff₀ hklogpos]
        nlinarith only [haMul]
      have hcoeff : (3/Real.log (k:ℝ))*(a:ℝ) ≤ (343/75:ℝ) := by
        rwa [show (3/Real.log (k:ℝ))*(a:ℝ)=(3*(a:ℝ))/Real.log (k:ℝ) by ring]
      have hbase : (3/Real.log (k:ℝ)) ≤ (343/75:ℝ)/(a:ℝ) :=
        (le_div_iff₀ haR).mpr hcoeff
      have hlnonneg : (0:ℝ) ≤ l := Nat.cast_nonneg l
      have hscale := mul_le_mul_of_nonneg_right hbase hlnonneg
      have hright : ((343/75:ℝ)/(a:ℝ))*(l:ℝ) ≤ (14/3:ℝ)*(v:ℝ) := by
        have hs := mul_le_mul_of_nonneg_left hvlower (by norm_num : (0:ℝ)≤14/3)
        have heq : ((343/75:ℝ)/(a:ℝ))*(l:ℝ) =
            (14/3:ℝ) * ((49/50:ℝ) * ((l:ℝ)/(a:ℝ))) := by ring
        rw [heq]
        exact hs
      exact hscale.trans hright
    calc
      (2 : ℝ) ^ ((3 / Real.log (k : ℝ)) * (l : ℝ)) ≤
          (2 : ℝ) ^ ((14/3 : ℝ) * (v : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexpkey
      _ = ((2 : ℝ) ^ ((14/3 : ℝ))) ^ v := by
        rw [Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2) (14/3:ℝ) v]
      _ ≤ (27 : ℝ) ^ v :=
        pow_le_pow_left₀ (by positivity) two_rpow_fourteen_thirds_lt_twentyseven.le v
      _ ≤ ((((n + 1 - v : ℕ) : ℝ) / (v : ℝ))) ^ v :=
        pow_le_pow_left₀ (by norm_num) hR v
      _ ≤ (n.choose v : ℝ) := choose_lower_sharp_ratio hvpos hvn1
      _ ≤ (shortFactorialDigits F l).card := by
        exact_mod_cast shortFactorialDigits_choose_lower hheight


theorem eventually_shortFactorialDigits_host30_sharp : ∀ᶠ k : ℕ in atTop,
    ∀ l : ℕ, 1 ≤ l → l ≤ k →
      (2 : ℝ) ^ ((3 / Real.log (k : ℝ)) * (l : ℝ)) ≤
        (shortFactorialDigits (30*k) l).card := by
  have htend : Tendsto (fun k : ℕ => Real.log (k:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hFtend : Tendsto (fun k : ℕ => 30*k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k (by norm_num)) tendsto_id
  filter_upwards [hFtend.eventually eventually_primeCounting_two_thirds,
    htend.eventually_ge_atTop (200 * max 1 (Real.log 30)),
    htend.eventually_ge_atTop 3,
    eventually_ge_atTop (2^454), eventually_ge_atTop 2]
    with k hprime hlogbig hlog3 hkHuge hk2
  intro l hl hlk
  have hklogpos : 0 < Real.log (k:ℝ) := by linarith
  have hklog30 : Real.log 30 ≤ (1/200 : ℝ) * Real.log (k:ℝ) := by
    have hm : Real.log 30 ≤ max 1 (Real.log 30) := le_max_right _ _
    have hs := mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤200)
    nlinarith
  have hklog1 : (1:ℝ) ≤ (1/200 : ℝ) * Real.log (k:ℝ) := by
    have hm : (1:ℝ) ≤ max 1 (Real.log 30) := le_max_left _ _
    have hs := mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤200)
    nlinarith
  have hkbig : 2^454 ≤ 30*k+1 := by
    calc
      2^454 ≤ k := hkHuge
      _ ≤ 30*k := Nat.le_mul_of_pos_left k (by norm_num)
      _ ≤ 30*k+1 := Nat.le_succ _
  exact shortFactorialDigits_host30_sharp hk2 (by linarith) hklog30 hklog1 hkbig
    (by simpa using hprime) hl hlk

def optimizedInitialBits (k : ℕ) : ℕ := Nat.log 2 k

def optimizedBlockSteps (k : ℕ) : ℕ :=
  Nat.log 2 (k / optimizedInitialBits k) + 1

def optimizedDigitSet (k : ℕ) : Finset ℕ :=
  binaryBlockSet (30*k) k (optimizedInitialBits k) (optimizedBlockSteps k)

theorem optimized_block_endpoint_top {k : ℕ}
    (hk4 : 4 ≤ optimizedInitialBits k) :
    binaryBlockEndpoint k (optimizedInitialBits k) (optimizedBlockSteps k) = k := by
  let b := optimizedInitialBits k
  let q := k / b
  have hb : 0 < b := by omega
  apply min_eq_left
  have hqpow : q + 1 ≤ 2 ^ optimizedBlockSteps k := by
    have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) q
    dsimp [optimizedBlockSteps,q]
    exact hh
  have hdiv : k < b * (q + 1) := Nat.lt_mul_div_succ k hb
  have hmul : (q + 1) * b ≤ 2 ^ optimizedBlockSteps k * b :=
    Nat.mul_le_mul_right b hqpow
  rw [Nat.mul_comm b (q+1)] at hdiv
  exact le_of_lt (lt_of_lt_of_le hdiv hmul)

theorem optimized_blockSteps_length_le {k : ℕ}
    (hk4 : 4 ≤ optimizedInitialBits k) :
    optimizedBlockSteps k + 2 ≤ Nat.log 2 k + 1 := by
  have hqle : k / optimizedInitialBits k ≤ k / 4 :=
    Nat.div_le_div_left hk4 (by norm_num)
  have hlogle := Nat.log_mono_right (b := 2) hqle
  have hlog4 : Nat.log 2 (k / 4) = Nat.log 2 k - 2 := by
    change Nat.log 2 (k / 2^2) = Nat.log 2 k - 2
    exact Nat.log_div_base_pow 2 k 2
  have hklog : 4 ≤ Nat.log 2 k := hk4
  dsimp [optimizedBlockSteps] at hlogle ⊢
  omega

theorem optimizedInitialBits_ge_four {k : ℕ} (hk : 16 ≤ k) :
    4 ≤ optimizedInitialBits k := by
  dsimp [optimizedInitialBits]
  apply Nat.le_log_of_pow_le (by decide : 1 < 2)
  exact (by norm_num : 2^4 ≤ 16).trans hk

theorem optimized_digit_profile_large {k : ℕ} (hk : 16 ≤ k)
    {c : ℝ} (hc0 : 0 ≤ c) (hcsmall : c ≤ 1/2)
    (hD : ∀ l : ℕ, 1 ≤ l → l ≤ k →
      (2 : ℝ) ^ (c * (l : ℝ)) ≤ (shortFactorialDigits (30*k) l).card) :
    BinaryBlockProfile (30*k) k k (optimizedBlockSteps k + 1) c (optimizedDigitSet k) := by
  have hb4 := optimizedInitialBits_ge_four hk
  have hb : 2 ≤ optimizedInitialBits k := by omega
  have hbK : optimizedInitialBits k ≤ k := by
    dsimp [optimizedInitialBits]
    exact Nat.log_le_self 2 k
  have hF : 2 ^ optimizedInitialBits k ≤ 30*k := by
    have hkpos : k ≠ 0 := by omega
    have hh := Nat.pow_log_le_self 2 hkpos
    exact hh.trans (Nat.le_mul_of_pos_left k (by norm_num))
  have hp := binary_block_set_profile hb hbK hF hc0 hcsmall hD (optimizedBlockSteps k)
  have hend := optimized_block_endpoint_top hb4
  dsimp [optimizedDigitSet]
  rwa [hend] at hp

theorem eventually_optimized_digit_profile : ∀ᶠ k : ℕ in atTop,
    BinaryBlockProfile (30*k) k k (optimizedBlockSteps k + 1)
      (3 / Real.log (k:ℝ)) (optimizedDigitSet k) := by
  have htend : Tendsto (fun k : ℕ => Real.log (k:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_shortFactorialDigits_host30_sharp,
    htend.eventually_ge_atTop 6, eventually_ge_atTop 16] with k hD hlog6 hk
  have hklogpos : 0 < Real.log (k:ℝ) := by linarith
  have hc0 : 0 ≤ 3 / Real.log (k:ℝ) := by positivity
  have hcsmall : 3 / Real.log (k:ℝ) ≤ 1/2 := by
    rw [div_le_iff₀ hklogpos]
    nlinarith
  exact optimized_digit_profile_large hk hc0 hcsmall hD


noncomputable def positiveDigitList (A : Finset ℕ) : List ℕ :=
  A.toList ++ A.toList.map (fun a => a + 1)

theorem positiveDigitList_length (A : Finset ℕ) :
    (positiveDigitList A).length = 2 * A.card := by
  simp [positiveDigitList, Finset.length_toList, two_mul]

theorem finset_filter_toList_length (A : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (A.toList.filter P).length = (A.filter P).card := by
  rw [← List.toFinset_card_of_nodup ((Finset.nodup_toList A).filter P)]
  congr 1
  ext x
  simp

theorem finset_filter_map_toList_length (A : Finset ℕ) (f : ℕ → ℕ)
    (P : ℕ → Prop) [DecidablePred P] :
    ((A.toList.map f).filter P).length = (A.filter fun a => P (f a)).card := by
  rw [List.filter_map, List.length_map]
  exact finset_filter_toList_length A (fun a => P (f a))

theorem dyadicIndex_eq_iff_modEq (L n : ℕ) (x : Fin (2^L)) :
    dyadicIndex L n = x ↔ Nat.ModEq (2^L) n x.val := by
  simp only [Fin.ext_iff, dyadicIndex, Nat.ModEq, Nat.mod_eq_of_lt x.isLt]

theorem dyadicIndex_add_one_iff (L n : ℕ) (x : Fin (2^L)) :
    dyadicIndex L (n+1) = x ↔ dyadicIndex L n = x - 1 := by
  rw [dyadicIndex_add_one]
  exact eq_sub_iff_add_eq.symm

theorem positiveDigitList_fiber_mass (A : Finset ℕ) (hA : A.Nonempty)
    (L : ℕ) (x : Fin (2^L)) :
    (((positiveDigitList A).filter fun n : ℕ => dyadicIndex L n = x).length : ℝ) /
        ((positiveDigitList A).length : ℝ) =
      positiveDigitProjection A L x := by
  have hcardpos : (A.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hA).ne'
  have hlen : (positiveDigitList A).length = 2 * A.card := positiveDigitList_length A
  have hfilter :
      ((positiveDigitList A).filter fun n : ℕ => dyadicIndex L n = x).length =
        (natResidueFiber A (2^L) x.val).card +
          (natResidueFiber A (2^L) (x-1).val).card := by
    unfold positiveDigitList
    rw [List.filter_append, List.length_append]
    have hfirst :
        (A.toList.filter fun n : ℕ => dyadicIndex L n = x).length =
          (natResidueFiber A (2^L) x.val).card := by
      rw [finset_filter_toList_length]
      congr 1
      ext a
      simp [natResidueFiber, dyadicIndex_eq_iff_modEq]
    have hsecond :
        ((A.toList.map fun a => a+1).filter fun n : ℕ => dyadicIndex L n = x).length =
          (natResidueFiber A (2^L) (x-1).val).card := by
      rw [finset_filter_map_toList_length]
      congr 1
      ext a
      constructor
      · intro ha
        obtain ⟨haA, hpred⟩ := Finset.mem_filter.mp ha
        apply Finset.mem_filter.mpr
        refine ⟨haA, ?_⟩
        have hd : dyadicIndex L a = x - 1 := (dyadicIndex_add_one_iff L a x).mp hpred
        exact (dyadicIndex_eq_iff_modEq L a (x-1)).mp hd
      · intro ha
        obtain ⟨haA, hpred⟩ := Finset.mem_filter.mp ha
        apply Finset.mem_filter.mpr
        refine ⟨haA, ?_⟩
        have hd : dyadicIndex L a = x - 1 := (dyadicIndex_eq_iff_modEq L a (x-1)).mpr hpred
        exact (dyadicIndex_add_one_iff L a x).mpr hd
    rw [hfirst, hsecond]
  rw [hfilter, hlen]
  have hu := uniformDigitProjection_eq A L x
  have hu1 := uniformDigitProjection_eq A L (x-1)
  rw [positiveDigitProjection_smooth, hu, hu1]
  unfold natResidueMass
  field_simp [hcardpos]
  push_cast
  ring


theorem factorial_multiset_to_list {F R u : ℕ}
    (h : HasFactorialDivisorMultiset F R u) :
    ∃ S : List ℕ, (∀ d ∈ S, d ∣ F.factorial) ∧ S.length ≤ u ∧ S.sum = R := by
  obtain ⟨s, hs, hsum, hcard⟩ := h
  refine ⟨s.toList, ?_, ?_, ?_⟩
  · intro d hd
    exact hs d (Multiset.mem_toList.mp hd)
  · rw [Multiset.length_toList]
    exact hcard
  · rw [Multiset.sum_toList, hsum]

theorem positiveDigitList_representations {k : ℕ} (hk : 16 ≤ k)
    (hA : BinaryBlockProfile (30*k) k k (optimizedBlockSteps k + 1)
      (3 / Real.log (k:ℝ)) (optimizedDigitSet k)) :
    ∀ x ∈ positiveDigitList (optimizedDigitSet k), x ≤ 2 ^ k ∧ ∃ S : List ℕ,
      (∀ d ∈ S, d ∣ (32 * k).factorial) ∧
      S.length ≤ Nat.log 2 k + 1 ∧ S.sum = x := by
  intro x hx
  unfold positiveDigitList at hx
  rw [List.mem_append] at hx
  have hb4 := optimizedInitialBits_ge_four hk
  have hlenbound := optimized_blockSteps_length_le hb4
  have hfinish (a : ℕ) (haA : a ∈ optimizedDigitSet k) (e : Fin 2)
      (hxeq : x = a + e.val) :
      x ≤ 2 ^ k ∧ ∃ S : List ℕ,
        (∀ d ∈ S, d ∣ (32 * k).factorial) ∧
        S.length ≤ Nat.log 2 k + 1 ∧ S.sum = x := by
    let z : optimizedDigitSet k × Fin 2 := ⟨⟨a, haA⟩, e⟩
    have hv := positiveDigitValue_repr hA z
    have hval : positiveDigitValue (optimizedDigitSet k) z = x := by
      simp [positiveDigitValue, z, hxeq]
    obtain ⟨hpos, hbound, hrepr⟩ := hv
    have hrepr32 : HasFactorialDivisorMultiset (32*k)
        (positiveDigitValue (optimizedDigitSet k) z) (optimizedBlockSteps k + 2) := by
      have hh : 30*k + 2*k = 32*k := by ring
      rwa [hh] at hrepr
    obtain ⟨S, hSdiv, hSlen, hSsum⟩ := factorial_multiset_to_list hrepr32
    rw [hval] at hbound hSsum
    exact ⟨hbound, S, hSdiv, hSlen.trans hlenbound, hSsum⟩
  rcases hx with hx | hx
  · have haA : x ∈ optimizedDigitSet k := Finset.mem_toList.mp hx
    exact hfinish x haA 0 (by simp)
  · obtain ⟨a, haA, rfl⟩ := List.mem_map.mp hx
    exact hfinish a (Finset.mem_toList.mp haA) 1 rfl

theorem zmod_eq_dyadicIndex_iff (L n : ℕ) (x : Fin (2^L)) :
    ((n : ZMod (2^L)) = (x.val : ZMod (2^L))) ↔ dyadicIndex L n = x := by
  rw [ZMod.natCast_eq_natCast_iff' n x.val (2^L), Nat.mod_eq_of_lt x.isLt]
  constructor
  · intro h
    apply Fin.ext
    exact h
  · intro h
    rw [← h]
    rfl

theorem list_filter_length_congr (xs : List ℕ) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ x, P x ↔ Q x) :
    (xs.filter P).length = (xs.filter Q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : P x
      · have hq : Q x := (h x).mp hx
        simp [hx, hq, ih]
      · have hq : ¬ Q x := fun hq => hx ((h x).mpr hq)
        simp [hx, hq, ih]

theorem positiveDigitList_cap {k : ℕ}
    (hA : BinaryBlockProfile (30*k) k k (optimizedBlockSteps k + 1)
      (3 / Real.log (k:ℝ)) (optimizedDigitSet k))
    (hc : 3 / Real.log (k:ℝ) ≤ 2)
    (L : ℕ) (hL : 0 < L) (hLk : L ≤ k) (z : ZMod (2^L)) :
    (((positiveDigitList (optimizedDigitSet k)).filter fun n : ℕ =>
        ((n : ZMod (2^L)) = z)).length : ℝ) /
      ((positiveDigitList (optimizedDigitSet k)).length : ℝ) ≤
        (2 : ℝ) ^ (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k:ℝ)) := by
  have : NeZero (2^L) := ⟨by positivity⟩
  let x : Fin (2^L) := ⟨z.val, z.val_lt⟩
  have hxz : (x.val : ZMod (2^L)) = z := by
    dsimp [x]
    exact ZMod.natCast_zmod_val z
  have hpred (n : ℕ) : ((n : ZMod (2^L)) = z) ↔ dyadicIndex L n = x := by
    rw [← hxz]
    exact zmod_eq_dyadicIndex_iff L n x
  have hcong := list_filter_length_congr (positiveDigitList (optimizedDigitSet k))
    (fun n : ℕ => ((n : ZMod (2^L)) = z)) (fun n : ℕ => dyadicIndex L n = x) hpred
  rw [hcong, positiveDigitList_fiber_mass _ hA.nonempty L x]
  have hcap := positiveDigit_prefix_cap hA hc L hL hLk x
  have hrw : -( (3 / Real.log (k:ℝ)) / 2) * (L:ℝ) =
      -(3 / 2 : ℝ) * (L : ℝ) / Real.log (k:ℝ) := by ring
  rwa [hrw] at hcap


theorem zmod_filter_length_eq (xs : List ℕ) (L : ℕ) (z : ZMod (2^L)) :
    ((xs.filter fun x => (x : ZMod (2^L)) = z).length) =
    ((xs.filter fun n : ℕ => ((n : ZMod (2^L)) = z)).length) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : ((x : ZMod (2^L)) = z)
      · simp [hx]
        exact ih
      · simp [hx]
        exact ih

theorem eventually_optimized_digit_law : ∀ᶠ k : ℕ in atTop,
    ∃ xs : List ℕ,
      0 < xs.length ∧
      (∀ x ∈ xs, x ≤ 2 ^ k ∧ ∃ S : List ℕ,
        (∀ d ∈ S, d ∣ (32 * k).factorial) ∧
        S.length ≤ Nat.log 2 k + 1 ∧ S.sum = x) ∧
      (∀ L : ℕ, 1 ≤ L → L ≤ k → ∀ z : ZMod (2 ^ L),
        (((xs.filter fun x => (x : ZMod (2 ^ L)) = z).length : ℝ) / (xs.length : ℝ)) ≤
          (2 : ℝ) ^ (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k : ℝ))) := by
  have htend : Tendsto (fun k : ℕ => Real.log (k:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_optimized_digit_profile, htend.eventually_ge_atTop 3,
    eventually_ge_atTop 16] with k hprofile hlog3 hk
  let xs := positiveDigitList (optimizedDigitSet k)
  have hklogpos : 0 < Real.log (k:ℝ) := by linarith
  have hc : 3 / Real.log (k:ℝ) ≤ 2 := by
    have h1 : 3 / Real.log (k:ℝ) ≤ 1 := by
      rw [div_le_one hklogpos]
      exact hlog3
    linarith
  refine ⟨xs, ?_, ?_, ?_⟩
  · have hcard : 0 < (optimizedDigitSet k).card := Finset.card_pos.mpr hprofile.nonempty
    dsimp [xs]
    rw [positiveDigitList_length]
    omega
  · exact positiveDigitList_representations hk hprofile
  · intro L hL hLk z
    rw [zmod_filter_length_eq xs L z]
    exact positiveDigitList_cap hprofile hc L (by omega) hLk z


-- BEGIN integrated H2 harmonic adapter
noncomputable section
def h2DigitWeight (xs : List ℕ) (_i : Fin xs.length) : ℝ := 1/(xs.length:ℝ)
def h2DigitValue (xs : List ℕ) (i : Fin xs.length) : ℕ := xs.get i
def h2DigitProjection (xs : List ℕ) (L : ℕ) : Fin (2^L) → ℝ :=
  dyadicDistribution (h2DigitWeight xs) (h2DigitValue xs) L

theorem h2DigitWeight_sum (xs : List ℕ) (hxs : 0 < xs.length) :
    ∑ i : Fin xs.length, h2DigitWeight xs i = 1 := by
  have hc : (xs.length:ℝ) ≠ 0 := by exact_mod_cast hxs.ne'
  simp only [h2DigitWeight, sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin]
  field_simp

theorem h2DigitProjection_probability (xs : List ℕ) (hxs : 0 < xs.length) (L : ℕ) :
    (∀ x, 0 ≤ h2DigitProjection xs L x) ∧ ∑ x, h2DigitProjection xs L x = 1 := by
  refine ⟨?_, ?_⟩
  · change ∀ x, 0 ≤ finitePushforward (h2DigitWeight xs) (fun i => dyadicIndex L (h2DigitValue xs i)) x
    exact finite_pushforward_nonneg _ _ (fun i => by
      have hc : (0:ℝ) < xs.length := by exact_mod_cast hxs
      exact div_nonneg zero_le_one hc.le)
  · rw [h2DigitProjection, dyadicDistribution, finite_pushforward_sum, h2DigitWeight_sum xs hxs]

theorem list_filter_length_eq_indicator_sum (xs : List ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((xs.filter P).length : ℝ) =
      ∑ i : Fin xs.length, if P (xs.get i) then (1 : ℝ) else 0 := by
  have hreal : ((xs.filter P).length : ℝ) =
      (xs.map (fun x => if P x then (1 : ℝ) else 0)).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        by_cases hx : P x <;> simp [hx, ih, Nat.add_comm]
  rw [hreal]
  exact (Fin.sum_univ_fun_getElem xs (fun x => if P x then (1 : ℝ) else 0)).symm



theorem h2DigitProjection_eq_count (xs : List ℕ) (hxs : 0 < xs.length)
    (L : ℕ) (x : Fin (2^L)) :
    h2DigitProjection xs L x =
      ((xs.filter fun n : ℕ => ((n : ZMod (2^L)) = (x.val : ZMod (2^L)))).length : ℝ) /
        (xs.length : ℝ) := by
  have hlen : (xs.length:ℝ) ≠ 0 := by exact_mod_cast hxs.ne'
  change (∑ i ∈ Finset.univ.filter (fun i => dyadicIndex L (h2DigitValue xs i) = x),
      h2DigitWeight xs i) = _
  rw [Finset.sum_filter]
  simp only [h2DigitWeight]
  have hfactor :
      (∑ i : Fin xs.length,
        if dyadicIndex L (h2DigitValue xs i) = x then (1/(xs.length:ℝ)) else 0) =
      (1/(xs.length:ℝ)) * ∑ i : Fin xs.length,
        if dyadicIndex L (h2DigitValue xs i) = x then (1:ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : dyadicIndex L (h2DigitValue xs i) = x <;> simp [h]
  rw [hfactor]
  have hcount := list_filter_length_eq_indicator_sum xs
    (fun n : ℕ => ((n : ZMod (2^L)) = (x.val : ZMod (2^L))))
  have hind :
      (∑ i : Fin xs.length,
        if ((xs.get i : ℕ) : ZMod (2^L)) = (x.val : ZMod (2^L)) then (1:ℝ) else 0) =
      (∑ i : Fin xs.length,
        if dyadicIndex L (xs.get i) = x then (1:ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    change (if (((xs.get i : ℕ) : ZMod (2^L)) = (x.val : ZMod (2^L))) then (1:ℝ) else 0) =
      if dyadicIndex L (xs.get i) = x then (1:ℝ) else 0
    by_cases hz : ((xs.get i : ZMod (2^L)) = (x.val : ZMod (2^L)))
    · have hd : dyadicIndex L (xs.get i) = x := (zmod_eq_dyadicIndex_iff L (xs.get i) x).mp hz
      rw [if_pos hz, if_pos hd]
    · have hd : ¬ dyadicIndex L (xs.get i) = x := by
        intro hd
        exact hz ((zmod_eq_dyadicIndex_iff L (xs.get i) x).mpr hd)
      rw [if_neg hz, if_neg hd]
  change (1/(xs.length:ℝ)) * (∑ i : Fin xs.length,
      if dyadicIndex L (xs.get i) = x then (1:ℝ) else 0) = _
  rw [← hind, ← hcount]
  field_simp [hlen]



theorem h2Digit_entropy_prefix (xs : List ℕ) (hxs : 0 < xs.length) (k : ℕ)
    (hklog : 0 < Real.log (k:ℝ))
    (hcap : ∀ L : ℕ, 1 ≤ L → L ≤ k → ∀ z : ZMod (2 ^ L),
      (((xs.filter fun n : ℕ => ((n : ZMod (2 ^ L)) = z)).length : ℝ) / (xs.length : ℝ)) ≤
        (2 : ℝ) ^ (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k:ℝ)))
    (L : ℕ) (hL : 0 < L) (hLk : L ≤ k) :
    ((3 / 2 : ℝ) / Real.log (k:ℝ)) * (L:ℝ) * Real.log 2 ≤
      dyadicEntropy (h2DigitProjection xs k) Fin.val L := by
  have he : dyadicDistribution (h2DigitProjection xs k) Fin.val L = h2DigitProjection xs L :=
    dyadic_distribution_project (h2DigitWeight xs) (h2DigitValue xs) hLk
  unfold dyadicEntropy
  rw [he]
  have hp := h2DigitProjection_probability xs hxs L
  have hcapatom : ∀ x : Fin (2^L),
      h2DigitProjection xs L x ≤
        (2 : ℝ) ^ (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k:ℝ)) := by
    intro x
    rw [h2DigitProjection_eq_count xs hxs L x]
    exact hcap L (by omega) hLk (x.val : ZMod (2^L))
  have hh := finiteEntropy_lower_of_cap _ hp.1 hp.2 _ hcapatom
  have hlogpow := Real.log_rpow (by norm_num : (0:ℝ)<2)
    (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k:ℝ))
  rw [hlogpow] at hh
  have hrw : -((-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k:ℝ)) * Real.log 2) =
      ((3 / 2 : ℝ) / Real.log (k:ℝ)) * (L:ℝ) * Real.log 2 := by
    field_simp [hklog.ne']
  rw [hrw] at hh
  exact hh


theorem h2Digit_harmonicLaw_support_repr (xs : List ℕ) (k : ℕ) (x : Fin (2^k))
    (hx : harmonicLaw k (h2DigitProjection xs k) x ≠ 0) :
    ∃ a : ℕ, a < k ∧ ∃ d ∈ xs, dyadicIndex k (2^a*d) = x := by
  change (∑ a : Fin k, harmonicWeight k a.val *
      dyadicDilate k a.val (h2DigitProjection xs k) x) ≠ 0 at hx
  obtain ⟨a, _, ha⟩ := exists_ne_zero_of_sum_ne_zero hx
  have hdilate : dyadicDilate k a.val (h2DigitProjection xs k) x ≠ 0 :=
    (mul_ne_zero_iff.mp ha).2
  change finitePushforward (h2DigitProjection xs k) (dyadicMultiplier k a.val) x ≠ 0 at hdilate
  obtain ⟨y, hymult, hpy⟩ := finite_pushforward_support
    (h2DigitProjection xs k) (dyadicMultiplier k a.val) x hdilate
  change finitePushforward (h2DigitWeight xs)
    (fun i => dyadicIndex k (h2DigitValue xs i)) y ≠ 0 at hpy
  obtain ⟨i, hi, _⟩ := finite_pushforward_support (h2DigitWeight xs)
    (fun i => dyadicIndex k (h2DigitValue xs i)) y hpy
  refine ⟨a.val, a.isLt, xs.get i, List.get_mem xs i, ?_⟩
  change dyadicIndex k (2^a.val * h2DigitValue xs i) = x
  have hscale := dyadicIndex_scale k a.val (h2DigitValue xs i)
  rw [hi, hymult] at hscale
  exact hscale


theorem convolutionPow_harmonicDigit_repr (xs : List ℕ) (k r : ℕ) (x : Fin (2^k))
    (hx : realConvolutionPow (harmonicLaw k (h2DigitProjection xs k)) r x ≠ 0) :
    ∃ w : List (ℕ × ℕ), w.length = r ∧
      (∀ p ∈ w, p.1 < k ∧ p.2 ∈ xs) ∧
      dyadicIndex k ((w.map fun p => 2 ^ p.1 * p.2).sum) = x := by
  induction r generalizing x with
  | zero =>
      have hx0 : x = 0 := by
        by_contra h
        simp [realConvolutionPow, h] at hx
      subst x
      exact ⟨[], by simp, by simp, by simp [dyadicIndex]⟩
  | succ r ih =>
      change (∑ a, harmonicLaw k (h2DigitProjection xs k) a *
        realConvolutionPow (harmonicLaw k (h2DigitProjection xs k)) r (x-a)) ≠ 0 at hx
      obtain ⟨a, _, ha⟩ := exists_ne_zero_of_sum_ne_zero hx
      obtain ⟨shift, hshift, digit, hdmem, hrep⟩ :=
        h2Digit_harmonicLaw_support_repr xs k a (mul_ne_zero_iff.mp ha).1
      obtain ⟨w, hwlen, hwvalid, hwcong⟩ := ih (x-a) (mul_ne_zero_iff.mp ha).2
      refine ⟨(shift,digit)::w, by simp [hwlen], ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hptail
        · exact ⟨hshift, hdmem⟩
        · exact hwvalid p hptail
      · rw [List.map_cons, List.sum_cons, dyadicIndex_add, hrep, hwcong]
        abel


theorem h2_copy_condition_large (k : ℕ) (hk : 8 ≤ k) :
    Real.log (2*(k:ℝ)) ≤ ((Nat.log 2 k+1:ℝ)^4) *
      ((((3/2:ℝ)/Real.log (k:ℝ))^2*(Real.log 2)^2/2)/harmonicSum k) := by
  set t := Real.log (k:ℝ)
  set q := (Nat.log 2 k+1:ℝ)
  have hkposNat : 0 < k := by omega
  have hkpos : (0:ℝ) < k := by exact_mod_cast hkposNat
  have hkR : (8:ℝ) ≤ k := by exact_mod_cast hk
  have ht2 : 2 ≤ t := by
    have hmono : Real.log 8 ≤ Real.log (k:ℝ) := Real.log_le_log (by norm_num) hkR
    have h8 : (2:ℝ) ≤ Real.log 8 := by
      rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
      have htwo := Real.log_two_gt_d9
      norm_num at htwo ⊢
      linarith
    exact h8.trans hmono
  have htpos : 0 < t := by linarith
  have hleft : Real.log (2*(k:ℝ)) ≤ (3/2)*t := by
    rw [Real.log_mul (by norm_num) hkpos.ne']
    have htwo := Real.log_two_lt_d9
    nlinarith [ht2]
  have hHpos : 0 < harmonicSum k := harmonicSum_pos k hkposNat
  have hHle : harmonicSum k ≤ (3/2)*t := by
    have hh := harmonicSum_le k
    nlinarith [ht2]
  have hpow : k < 2^(Nat.log 2 k+1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) k
  have hpowR : (k:ℝ) < ((2^(Nat.log 2 k+1) : ℕ):ℝ) := by exact_mod_cast hpow
  have hqpos : 0 < q := by positivity
  have hqlog : t ≤ q*Real.log 2 := by
    have hh := Real.log_le_log hkpos hpowR.le
    rw [Nat.cast_pow, Real.log_pow] at hh
    simpa [q, t] using hh
  have hu : (0:ℝ) < 0.6931471808 := by norm_num
  have hqmul : t < q*0.6931471808 := by
    have htwo := Real.log_two_lt_d9
    have hh := mul_lt_mul_of_pos_left htwo hqpos
    linarith
  have hqt : t/0.6931471808 ≤ q := by
    rw [div_le_iff₀ hu]
    exact hqmul.le
  have hrpow : (t/0.6931471808)^4 ≤ q^4 :=
    pow_le_pow_left₀ (div_nonneg htpos.le hu.le) hqt 4
  have hsq : (0.6931471803:ℝ)^2 ≤ (Real.log 2)^2 :=
    pow_le_pow_left₀ (by norm_num) Real.log_two_gt_d9.le 2
  have hg20 : 0 ≤ ((3/2:ℝ)/t)^2 := by positivity
  have hmulsq := mul_le_mul_of_nonneg_left hsq hg20
  have hAlower : ((3/2:ℝ)/t)^2*(0.6931471803)^2/2 ≤
      ((3/2:ℝ)/t)^2*(Real.log 2)^2/2 := by
    have hh := mul_le_mul_of_nonneg_right hmulsq (by norm_num : (0:ℝ) ≤ 1/2)
    nlinarith
  have hA_nonneg : 0 ≤ ((3/2:ℝ)/t)^2*(Real.log 2)^2/2 := by positivity
  have hdiv : (((3/2:ℝ)/t)^2*(Real.log 2)^2/2)/((3/2)*t) ≤
      (((3/2:ℝ)/t)^2*(Real.log 2)^2/2)/harmonicSum k :=
    div_le_div_of_nonneg_left hA_nonneg hHpos hHle
  have htDpos : 0 < (3/2)*t := mul_pos (by norm_num) htpos
  have hA0div_nonneg : 0 ≤ (((3/2:ℝ)/t)^2*(0.6931471803)^2/2)/((3/2)*t) := by
    exact div_nonneg (by positivity) htDpos.le
  have hqpow_nonneg : 0 ≤ q^4 := pow_nonneg hqpos.le 4
  have hmain :
      ((t/0.6931471808)^4) *
        ((((3/2:ℝ)/t)^2*(0.6931471803)^2/2)/((3/2)*t)) ≤
        q^4 * ((((3/2:ℝ)/t)^2*(Real.log 2)^2/2)/harmonicSum k) := by
    calc
      ((t/0.6931471808)^4) *
          ((((3/2:ℝ)/t)^2*(0.6931471803)^2/2)/((3/2)*t))
          ≤ q^4 * ((((3/2:ℝ)/t)^2*(0.6931471803)^2/2)/((3/2)*t)) :=
        mul_le_mul_of_nonneg_right hrpow hA0div_nonneg
      _ ≤ q^4 * ((((3/2:ℝ)/t)^2*(Real.log 2)^2/2)/((3/2)*t)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hAlower htDpos.le) hqpow_nonneg
      _ ≤ q^4 * ((((3/2:ℝ)/t)^2*(Real.log 2)^2/2)/harmonicSum k) :=
        mul_le_mul_of_nonneg_left hdiv hqpow_nonneg
  have hnum :
      ((t/0.6931471808)^4) *
        ((((3/2:ℝ)/t)^2*(0.6931471803)^2/2)/((3/2)*t)) =
        (3*(0.6931471803:ℝ)^2/(4*(0.6931471808)^4))*t := by
    field_simp [htpos.ne']
    ring
  rw [hnum] at hmain
  have hC : (3/2:ℝ) ≤ 3*(0.6931471803:ℝ)^2/(4*(0.6931471808)^4) := by norm_num
  have hleftC : Real.log (2*(k:ℝ)) ≤
      (3*(0.6931471803:ℝ)^2/(4*(0.6931471808)^4))*t := by
    nlinarith [hleft]
  exact hleftC.trans hmain

open Filter in

theorem h2_pair_shift_sum_bound (xs : List ℕ) (k : ℕ) (w : List (ℕ × ℕ))
    (hxbound : ∀ x ∈ xs, x ≤ 2^k) :
    (∀ p ∈ w, p.1 < k ∧ p.2 ∈ xs) →
    (w.map fun p : ℕ × ℕ => 2^p.1*p.2).sum ≤ w.length*2^(2*k) := by
  induction w with
  | nil =>
      intro hwvalid
      simp
  | cons p w ih =>
      intro hwvalid
      have hp : p.1 < k ∧ p.2 ∈ xs := hwvalid p (by simp)
      have htailvalid : ∀ q ∈ w, q.1 < k ∧ q.2 ∈ xs := by
        intro q hq
        exact hwvalid q (by simp [hq])
      have htail := ih htailvalid
      have hpow : 2^p.1 ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt hp.1)
      have hdigit : p.2 ≤ 2^k := hxbound p.2 hp.2
      have hterm : 2^p.1*p.2 ≤ 2^(2*k) := by
        calc
          2^p.1*p.2 ≤ 2^k*2^k := Nat.mul_le_mul hpow hdigit
          _ = 2^(2*k) := by
            rw [← pow_add]
            congr 1
            omega
      rw [List.map_cons,List.sum_cons,List.length_cons]
      exact (Nat.add_le_add hterm htail).trans_eq (by ring)

lemma pow_step16 (k : ℕ) (hk : 16 ≤ k) : (k+1)^4 ≤ 2*k^4 := by
  have hkR : (16:ℝ) ≤ k := by exact_mod_cast hk
  have hlin : ((k+1:ℕ):ℝ) ≤ (9/8:ℝ)*k := by
    norm_num
    nlinarith
  have hpow : ((k+1:ℕ):ℝ)^4 ≤ ((9/8:ℝ)*k)^4 := by
    exact pow_le_pow_left₀ (by positivity) hlin 4
  have hfactor : ((9/8:ℝ)^4) ≤ 2 := by norm_num
  have hreal : ((k+1:ℕ):ℝ)^4 ≤ 2*(k:ℝ)^4 := by
    calc
      ((k+1:ℕ):ℝ)^4 ≤ ((9/8:ℝ)*k)^4 := hpow
      _ = ((9/8:ℝ)^4)*(k:ℝ)^4 := by ring
      _ ≤ 2*(k:ℝ)^4 := mul_le_mul_of_nonneg_right hfactor (by positivity)
  exact_mod_cast hreal

theorem pow4_le_two_pow (k : ℕ) (hk : 16 ≤ k) : k^4 ≤ 2^k := by
  induction' k, hk using Nat.le_induction with k hk ih
  · norm_num
  · calc
      (k+1)^4 ≤ 2*k^4 := pow_step16 k hk
      _ ≤ 2*2^k := Nat.mul_le_mul_left 2 ih
      _ = 2^(k+1) := by rw [pow_succ]; ring

theorem pow4_le_two_pow_pred (k : ℕ) (hk : 32 ≤ k) : k^4 ≤ 2^(k-1) := by
  induction' k, hk using Nat.le_induction with k hk ih
  · norm_num
  · have hk16 : 16 ≤ k := by omega
    calc
      (k+1)^4 ≤ 2*k^4 := pow_step16 k hk16
      _ ≤ 2*2^(k-1) := Nat.mul_le_mul_left 2 ih
      _ = 2^((k-1)+1) := by
        rw [pow_succ]
        ring
      _ = 2^((k+1)-1) := by
        congr 1
        omega

theorem h2_height_bound_large (k : ℕ) (hk : 31 ≤ k) :
    (Nat.log 2 k+1)^4*2^(2*k) ≤ 2^(3*k) := by
  have hq : Nat.log 2 k+1 ≤ k+1 := Nat.succ_le_succ (Nat.log_le_self 2 k)
  have hpow : (Nat.log 2 k+1)^4 ≤ (k+1)^4 := Nat.pow_le_pow_left hq 4
  have hk32 : 32 ≤ k+1 := by omega
  have hpred := pow4_le_two_pow_pred (k+1) hk32
  have hpred' : (k+1)^4 ≤ 2^k := by
    simpa using hpred
  have hqpow : (Nat.log 2 k+1)^4 ≤ 2^k := hpow.trans hpred'
  calc
    (Nat.log 2 k+1)^4*2^(2*k) ≤ 2^k*2^(2*k) := Nat.mul_le_mul_right _ hqpow
    _ = 2^(3*k) := by
      rw [← pow_add]
      congr 1
      omega

open Filter in
theorem eventually_h2_copy_condition : ∀ᶠ k : ℕ in atTop,
    Real.log (2*(k:ℝ)) ≤ ((Nat.log 2 k+1:ℝ)^4) *
      ((((3/2:ℝ)/Real.log (k:ℝ))^2*(Real.log 2)^2/2)/harmonicSum k) := by
  filter_upwards [eventually_ge_atTop 8] with k hk
  exact h2_copy_condition_large k hk


def finToZModEmbedding (n : ℕ) [NeZero n] : Fin n ↪ ZMod n where
  toFun x := (x.val : ZMod n)
  inj' := by
    intro x y h
    rw [ZMod.natCast_eq_natCast_iff'] at h
    apply Fin.ext
    rwa [Nat.mod_eq_of_lt x.isLt,Nat.mod_eq_of_lt y.isLt] at h

theorem h2_construct_large (k : ℕ) (hk : 31 ≤ k) (xs : List ℕ)
    (hxs : 0 < xs.length)
    (hrep : ∀ x ∈ xs, x ≤ 2 ^ k ∧ ∃ S : List ℕ,
      (∀ d ∈ S, d ∣ (32 * k).factorial) ∧
      S.length ≤ Nat.log 2 k + 1 ∧ S.sum = x)
    (hcap : ∀ L : ℕ, 1 ≤ L → L ≤ k → ∀ z : ZMod (2 ^ L),
      (((xs.filter fun x => (x : ZMod (2 ^ L)) = z).length : ℝ) / (xs.length : ℝ)) ≤
        (2 : ℝ) ^ (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k : ℝ))) :
    ∃ B : Finset (ZMod (2 ^ k)),
      2 ^ k < 2 * B.card ∧ ∀ y ∈ B, ∃ w : List (ℕ × ℕ),
        w.length ≤ (Nat.log 2 k + 1) ^ 4 ∧
        (∀ p ∈ w, p.1 < k ∧ p.2 ∈ xs) ∧
        (w.map fun p => 2 ^ p.1 * p.2).sum ≤ 2 ^ (3 * k) ∧
        (((w.map fun p => 2 ^ p.1 * p.2).sum : ℕ) : ZMod (2 ^ k)) = y := by
  have hk8 : 8 ≤ k := by omega
  have hkpos : 0 < k := by omega
  have : NeZero (2^k) := ⟨by positivity⟩
  let r : ℕ := (Nat.log 2 k+1)^4
  let g : ℝ := (3/2:ℝ)/Real.log (k:ℝ)
  have hklog : 0 < Real.log (k:ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < k by omega)
  have hcapnat : ∀ L : ℕ, 1 ≤ L → L ≤ k → ∀ z : ZMod (2 ^ L),
      (((xs.filter fun n : ℕ => ((n : ZMod (2 ^ L)) = z)).length : ℝ) / (xs.length : ℝ)) ≤
        (2 : ℝ) ^ (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k : ℝ)) := by
    intro L hL hLk z
    rw [← zmod_filter_length_eq xs L z]
    exact hcap L hL hLk z
  have hprefix : ∀ L : ℕ, 0 < L → L ≤ k →
      g*(L:ℝ)*Real.log 2 ≤ dyadicEntropy (h2DigitProjection xs k) Fin.val L := by
    intro L hL hLk
    exact h2Digit_entropy_prefix xs hxs k hklog hcapnat L hL hLk
  have hp := h2DigitProjection_probability xs hxs k
  have hg : 0 ≤ g := by
    exact le_of_lt (div_pos (by norm_num) hklog)
  have hrcopy0 := h2_copy_condition_large k hk8
  have hcastpow : ((((Nat.log 2 k+1)^4 : ℕ) : ℝ)) = (Nat.log 2 k+1:ℝ)^4 := by norm_num
  have hrcopy : Real.log (2*(k:ℝ)) ≤ (r:ℝ)*(g^2*(Real.log 2)^2/2)/harmonicSum k := by
    rw [mul_div_assoc]
    simpa [r,g,hcastpow] using hrcopy0
  have hdense := harmonicLaw_support_large k r hkpos (h2DigitProjection xs k) hp.1 hp.2 g hg hprefix hrcopy
  let Bfin : Finset (Fin (2^k)) := finiteSupport (realConvolutionPow (harmonicLaw k (h2DigitProjection xs k)) r)
  let emb : Fin (2^k) ↪ ZMod (2^k) := finToZModEmbedding (2^k)
  refine ⟨Bfin.map emb, ?_, ?_⟩
  · simpa [Bfin] using hdense
  · intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨x,hxB,rfl⟩ := hy
    have hxne : realConvolutionPow (harmonicLaw k (h2DigitProjection xs k)) r x ≠ 0 := by
      have hxmem : x ∈ finiteSupport (realConvolutionPow (harmonicLaw k (h2DigitProjection xs k)) r) := by
        simpa [Bfin] using hxB
      exact (Finset.mem_filter.mp hxmem).2
    obtain ⟨w,hwlen,hwvalid,hwcong⟩ := convolutionPow_harmonicDigit_repr xs k r x hxne
    refine ⟨w, ?_, hwvalid, ?_, ?_⟩
    · rw [hwlen]
    · have hxbound : ∀ x ∈ xs, x ≤ 2^k := by
        intro x hx
        exact (hrep x hx).1
      have hsum := h2_pair_shift_sum_bound xs k w hxbound hwvalid
      rw [hwlen] at hsum
      exact hsum.trans (by simpa [r] using h2_height_bound_large k hk)
    · have hz := (zmod_eq_dyadicIndex_iff k ((w.map fun p => 2 ^ p.1 * p.2).sum) x).mpr hwcong
      change (((w.map fun p => 2 ^ p.1 * p.2).sum : ℕ) : ZMod (2 ^ k)) = (x.val : ZMod (2 ^ k))
      exact hz

open Filter in
theorem erdos18_h2_kernel :
    ∀ᶠ k : ℕ in atTop, ∀ xs : List ℕ,
    0 < xs.length →
    (∀ x ∈ xs, x ≤ 2 ^ k ∧ ∃ S : List ℕ,
      (∀ d ∈ S, d ∣ (32 * k).factorial) ∧
      S.length ≤ Nat.log 2 k + 1 ∧ S.sum = x) →
    (∀ L : ℕ, 1 ≤ L → L ≤ k → ∀ z : ZMod (2 ^ L),
      (((xs.filter fun x => (x : ZMod (2 ^ L)) = z).length : ℝ) / (xs.length : ℝ)) ≤
        (2 : ℝ) ^ (-(3 / 2 : ℝ) * (L : ℝ) / Real.log (k : ℝ))) →
    ∃ B : Finset (ZMod (2 ^ k)),
      2 ^ k < 2 * B.card ∧ ∀ y ∈ B, ∃ w : List (ℕ × ℕ),
        w.length ≤ (Nat.log 2 k + 1) ^ 4 ∧
        (∀ p ∈ w, p.1 < k ∧ p.2 ∈ xs) ∧
        (w.map fun p => 2 ^ p.1 * p.2).sum ≤ 2 ^ (3 * k) ∧
        (((w.map fun p => 2 ^ p.1 * p.2).sum : ℕ) : ZMod (2 ^ k)) = y := by
  filter_upwards [eventually_ge_atTop 31] with k hk
  intro xs hxs hrep hcap
  exact h2_construct_large k hk xs hxs hrep hcap

-- END integrated H2 harmonic adapter

-- BEGIN factorial shift arithmetic
theorem list_sum_map_mul_left (c : ℕ) : ∀ U : List ℕ,
    (U.map fun d => c * d).sum = c * U.sum := by
  intro U
  induction U with
  | nil => simp
  | cons d U ih =>
      simp [ih, Nat.mul_add]

theorem exists_shift_expansion {k : ℕ} {xs : List ℕ}
    (hrep : ∀ x ∈ xs, x ≤ 2 ^ k ∧ ∃ S : List ℕ,
      (∀ d ∈ S, d ∣ (32 * k).factorial) ∧
      S.length ≤ Nat.log 2 k + 1 ∧ S.sum = x) :
    ∀ w : List (ℕ × ℕ), (∀ p ∈ w, p.1 < k ∧ p.2 ∈ xs) →
      ∃ T : List ℕ,
        (∀ d ∈ T, d ∣ (36 * k).factorial) ∧
        T.length ≤ w.length * (Nat.log 2 k + 1) ∧
        T.sum = (w.map fun p => 2 ^ p.1 * p.2).sum := by
  intro w
  induction w with
  | nil =>
      intro _
      exact ⟨[], by simp, by simp, by simp⟩
  | cons p w ih =>
      intro hw
      have hp : p.1 < k ∧ p.2 ∈ xs := hw p (by simp)
      have htail : ∀ q ∈ w, q.1 < k ∧ q.2 ∈ xs := by
        intro q hq
        exact hw q (by simp [hq])
      obtain ⟨T, hTdiv, hTlen, hTsum⟩ := ih htail
      obtain ⟨hxbound, U, hUdiv, hUlen, hUsum⟩ := hrep p.2 hp.2
      refine ⟨(U.map fun d => 2 ^ p.1 * d) ++ T, ?_, ?_, ?_⟩
      · intro d hd
        rw [List.mem_append] at hd
        rcases hd with hdV | hdT
        · obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.mp hdV
          have hd0div : d₀ ∣ (32 * k).factorial := hUdiv d₀ hd₀
          have hshift : 2 ^ p.1 * d₀ ∣ (32 * k + 2 * k).factorial :=
            shifted_divisor_dvd_factorial hd0div (Nat.le_of_lt hp.1)
          have hhost : (32 * k + 2 * k).factorial ∣ (36 * k).factorial :=
            Nat.factorial_dvd_factorial (by omega)
          exact hshift.trans hhost
        · exact hTdiv d hdT
      · rw [List.length_append, List.length_map]
        calc
          U.length + T.length ≤
              (Nat.log 2 k + 1) + w.length * (Nat.log 2 k + 1) :=
            Nat.add_le_add hUlen hTlen
          _ = (w.length + 1) * (Nat.log 2 k + 1) := by ring
          _ = (p :: w).length * (Nat.log 2 k + 1) := by simp
      · rw [List.sum_append, list_sum_map_mul_left, hUsum, hTsum]
        simp

-- END factorial shift arithmetic


theorem erdos18_h1_kernel_unwrapped :
    ∀ᶠ k : ℕ in atTop, ∃ B : Finset (ZMod (2 ^ k)),
      2 ^ k < 2 * B.card ∧ ∀ y ∈ B, ∃ S : List ℕ,
        (∀ d ∈ S, d ∣ (36 * k).factorial) ∧ S.length ≤ (Nat.log 2 k + 1) ^ 5 ∧
        S.sum ≤ 2 ^ (3 * k) ∧ (S.sum : ZMod (2 ^ k)) = y := by
  filter_upwards [eventually_optimized_digit_law, erdos18_h2_kernel] with k hlawk hmixk
  obtain ⟨xs, hxne, hrep, hcap⟩ := hlawk
  obtain ⟨B, hdense, hwitness⟩ := hmixk xs hxne hrep hcap
  refine ⟨B, hdense, ?_⟩
  intro y hy
  obtain ⟨w, hwlen, hwvalid, hwheight, hwcong⟩ := hwitness y hy
  obtain ⟨T, hTdiv, hTlen, hTsum⟩ := exists_shift_expansion hrep w hwvalid
  refine ⟨T, hTdiv, ?_, ?_, ?_⟩
  · calc
      T.length ≤ w.length * (Nat.log 2 k + 1) := hTlen
      _ ≤ (Nat.log 2 k + 1) ^ 4 * (Nat.log 2 k + 1) :=
        Nat.mul_le_mul_right _ hwlen
      _ = (Nat.log 2 k + 1) ^ 5 := by ring
  · rw [hTsum]
    exact hwheight
  · rw [hTsum]
    exact hwcong

end
end Erdos18c
-- END optimized H1 digit-supply adapter scaffold

theorem OMA.solution : OMA.R_Erdos18_erdos_18a_R1.H1 :=
  Erdos18c.erdos18_h1_kernel_unwrapped
