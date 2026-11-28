import OMAReductions.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1_H1_R1_H2_R1
import Mathlib


/-! Adapted from OpenAI, openai/math 3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). Extracted from the PrimeGaps modules identified below. -/

-- OAI.NumberTheory.PrimeGaps.Indices

namespace OAI

namespace LargePrimeGaps

noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

noncomputable def largeGapIndices (C : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n =>
    C * Real.log (prime n : ℝ) < (prime (n + 1) : ℝ) - (prime n : ℝ)

def primeIndex (p : ℕ) : ℕ := Nat.primeCounting' p + 1

noncomputable def successor (p : ℕ) : ℕ := prime (primeIndex p + 1)

theorem prime_isPrime (n : ℕ) : Nat.Prime (prime n) :=
  Nat.prime_nth_prime _

theorem prime_primeIndex {p : ℕ} (hp : Nat.Prime p) : prime (primeIndex p) = p := by
  simpa [prime, primeIndex, Nat.primeCounting'] using Nat.nth_count hp

theorem primeIndex_pos (p : ℕ) : 0 < primeIndex p := by
  simp [primeIndex]

theorem primeIndex_prime {n : ℕ} (hn : 0 < n) : primeIndex (prime n) = n := by
  simp [primeIndex, prime, Nat.primeCounting'_nth_eq, Nat.sub_add_cancel hn]

theorem prime_lt_prime {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    prime m < prime n := by
  apply Nat.nth_strictMono Nat.infinite_setOfPred_prime
  omega

theorem lt_successor {p : ℕ} (hp : Nat.Prime p) : p < successor p := by
  calc
    p = prime (primeIndex p) := (prime_primeIndex hp).symm
    _ < successor p := prime_lt_prime (primeIndex_pos _) (Nat.lt_succ_self _)

theorem successor_isPrime (p : ℕ) : Nat.Prime (successor p) := prime_isPrime _

noncomputable def goodStarts (X h : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc X (2 * X)).filter fun m =>
    (∃ p, Nat.Prime p ∧ m < p ∧ p ≤ m + h) ∧
      ∀ q, m + h < q → q ≤ m + 2 * h → ¬ Nat.Prime q

noncomputable def gapPrimes (X h : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc X (2 * X + h)).filter fun p =>
    Nat.Prime p ∧ p + h < successor p

theorem exists_gapPrime_of_goodStart {X h m : ℕ} (hm : m ∈ goodStarts X h) :
    ∃ p ∈ gapPrimes X h, m ∈ Finset.Ico (p - h) p := by
  classical
  obtain ⟨hmrange, ⟨hex, hempty⟩⟩ := Finset.mem_filter.mp hm
  obtain ⟨hp, hpprime, hmp, hpend⟩ := hex
  let S := (Finset.Ioc m (m + h)).filter Nat.Prime
  have hSne : S.Nonempty := ⟨hp, by simp [S, hpprime, hmp, hpend]⟩
  let p := S.max' hSne
  have hpS : p ∈ S := Finset.max'_mem S hSne
  obtain ⟨hprange, hpprime⟩ := Finset.mem_filter.mp hpS
  obtain ⟨hmp, hpend⟩ := Finset.mem_Ioc.mp hprange
  have hn : m + 2 * h < successor p := by
    by_contra! hend
    have hnext := successor_isPrime p
    have hlt := lt_successor hpprime
    by_cases hsmall : successor p ≤ m + h
    · have hnS : successor p ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨lt_trans hmp hlt, hsmall⟩, hnext⟩
      have := Finset.le_max' S (successor p) hnS
      exact (not_le_of_gt hlt) this
    · exact hempty (successor p) (by omega) hend hnext
  refine ⟨p, ?_, ?_⟩
  · simp only [gapPrimes, Finset.mem_filter, Finset.mem_Ioc]
    obtain ⟨hmlo, hmhi⟩ := Finset.mem_Ioc.mp hmrange
    exact ⟨⟨by omega, by omega⟩, hpprime, by omega⟩
  · simp only [Finset.mem_Ico]
    omega

theorem goodStarts_card_le (X h : ℕ) :
    (goodStarts X h).card ≤ (gapPrimes X h).card * h := by
  classical
  calc
    (goodStarts X h).card ≤
        ((gapPrimes X h).biUnion fun p => Finset.Ico (p - h) p).card := by
      apply Finset.card_le_card
      intro m hm
      obtain ⟨p, hp, hmp⟩ := exists_gapPrime_of_goodStart hm
      exact Finset.mem_biUnion.mpr ⟨p, hp, hmp⟩
    _ ≤ ∑ p ∈ gapPrimes X h, (Finset.Ico (p - h) p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ gapPrimes X h, h := by
      apply Finset.sum_le_sum
      intro p _
      rw [Nat.card_Ico]
      omega
    _ = (gapPrimes X h).card * h := by simp

theorem primeIndex_injOn : Set.InjOn primeIndex {p | Nat.Prime p} := by
  intro p hp q hq h
  simpa [prime_primeIndex hp, prime_primeIndex hq] using congrArg prime h

theorem gapPrimes_card_le_largeGapIndices (C : ℝ) (X h N : ℕ) (hN : 0 < N)
    (hrange : 2 * X + h ≤ prime N)
    (hthreshold : ∀ p ∈ gapPrimes X h, C * Real.log (p : ℝ) ≤ (h : ℝ)) :
    (gapPrimes X h).card ≤ (largeGapIndices C N).card := by
  classical
  apply Finset.card_le_card_of_injOn primeIndex
  · intro p hp
    obtain ⟨hprange, hpprime, hgap⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hpupper⟩ := Finset.mem_Ioc.mp hprange
    have hipos := primeIndex_pos p
    have hiN : primeIndex p ≤ N := by
      by_contra! hi
      have := prime_lt_prime hN hi
      rw [prime_primeIndex hpprime] at this
      omega
    have hgapR : (p : ℝ) + (h : ℝ) < (successor p : ℝ) := by exact_mod_cast hgap
    change primeIndex p ∈ largeGapIndices C N
    simp only [largeGapIndices, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hipos, hiN⟩, ?_⟩
    rw [prime_primeIndex hpprime]
    have hth := hthreshold p hp
    change C * Real.log (p : ℝ) < (successor p : ℝ) - (p : ℝ)
    linarith
  · intro p hp q hq h
    exact primeIndex_injOn (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hq).2.1 h

noncomputable def blockLength (lam : ℝ) (X : ℕ) : ℕ :=
  ⌊lam * Real.log (X : ℝ)⌋₊

theorem log_pos_of_two_le {X : ℕ} (hX : 2 ≤ X) : 0 < Real.log (X : ℝ) :=
  Real.log_pos (by exact_mod_cast (show 1 < X by omega))

open Filter

theorem le_prime (n : ℕ) : n ≤ prime n := by
  have := Nat.add_two_le_nth_prime (n - 1)
  change n ≤ Nat.nth Nat.Prime (n - 1)
  omega

theorem tendsto_prime : Tendsto prime atTop atTop :=
  tendsto_atTop_mono le_prime tendsto_id

theorem primeCounting_prime {n : ℕ} (hn : 0 < n) : Nat.primeCounting (prime n) = n := by
  rw [Nat.primeCounting_eq_primeCounting'_succ]
  change Nat.count Nat.Prime (prime n + 1) = n
  rw [Nat.count_succ, if_pos (prime_isPrime n)]
  have := primeIndex_prime hn
  exact this

theorem eventually_index_log_prime_le :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * Real.log (prime n : ℝ) ≤ (Real.log 4 + 1) * (prime n : ℝ) := by
  have hcheb := (tendsto_natCast_atTop_atTop.comp tendsto_prime).eventually
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hcheb, eventually_ge_atTop 1] with n hn hnpos
  simp only [Function.comp_apply, Nat.floor_natCast, primeCounting_prime (by omega : 0 < n)] at hn
  exact (le_div_iff₀ (log_pos_of_two_le (prime_isPrime n).two_le)).mp hn

noncomputable def indexScale (N : ℕ) : ℕ := prime N / 3

theorem tendsto_indexScale : Tendsto indexScale atTop atTop :=
  (Nat.tendsto_div_const_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp tendsto_prime

theorem eventually_scale_comparison :
    ∀ᶠ N : ℕ in atTop, 2 ≤ indexScale N ∧
      (N : ℝ) * Real.log (indexScale N : ℝ) ≤
        (6 * (Real.log 4 + 1)) * (indexScale N : ℝ) := by
  filter_upwards [eventually_index_log_prime_le,
    tendsto_indexScale.eventually (eventually_ge_atTop 2)] with N hcheb hX
  refine ⟨hX, ?_⟩
  have hprime : indexScale N ≤ prime N := Nat.div_le_self _ _
  have hlog : Real.log (indexScale N : ℝ) ≤ Real.log (prime N : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < indexScale N by omega))
      (by exact_mod_cast hprime)
  have hsizeN : prime N ≤ 6 * indexScale N := by
    have hmod := Nat.mod_lt (prime N) (by norm_num : 0 < 3)
    have hdiv := Nat.div_add_mod (prime N) 3
    change 2 ≤ prime N / 3 at hX
    change prime N ≤ 6 * (prime N / 3)
    omega
  have hsize : (prime N : ℝ) ≤ 6 * (indexScale N : ℝ) := by exact_mod_cast hsizeN
  have hA : 0 ≤ Real.log 4 + 1 := by positivity
  calc
    (N : ℝ) * Real.log (indexScale N : ℝ) ≤
        (N : ℝ) * Real.log (prime N : ℝ) := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
    _ ≤ (Real.log 4 + 1) * (prime N : ℝ) := hcheb
    _ ≤ (6 * (Real.log 4 + 1)) * (indexScale N : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hsize hA]

theorem blockLength_le_mul_log {lam : ℝ} (hlam : 0 ≤ lam) {X : ℕ} (hX : 2 ≤ X) :
    (blockLength lam X : ℝ) ≤ lam * Real.log (X : ℝ) :=
  Nat.floor_le (mul_nonneg hlam (log_pos_of_two_le hX).le)

theorem eventually_blockLength_le (lam : ℝ) (hlam : 0 < lam) :
    ∀ᶠ X : ℕ in atTop, blockLength lam X ≤ X := by
  have he := tendsto_natCast_atTop_atTop.eventually (Real.isLittleO_log_id_atTop.bound
    (by positivity : 0 < 1 / lam))
  filter_upwards [he, eventually_ge_atTop 2] with X hbound hX
  have hlog := log_pos_of_two_le hX
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hlog.le,
    abs_of_nonneg (show (0 : ℝ) ≤ (X : ℝ) from Nat.cast_nonneg X)] at hbound
  have hmul : lam * Real.log (X : ℝ) ≤ (X : ℝ) := by
    calc
      lam * Real.log (X : ℝ) ≤ lam * ((1 / lam) * (X : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound hlam.le
      _ = (X : ℝ) := by field_simp
  exact_mod_cast (blockLength_le_mul_log hlam.le hX).trans hmul

theorem eventually_blockLength_threshold (C : ℝ) (hC : 0 < C) :
    ∀ᶠ X : ℕ in atTop, ∀ p : ℕ, 0 < p → p ≤ 3 * X →
      C * Real.log (p : ℝ) ≤ (blockLength (C + 1) X : ℝ) := by
  have hlim : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_ge_atTop (C * Real.log 3 + 1)),
    eventually_ge_atTop 2] with X hlog hX
  intro p hp hpX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hupper : Real.log (p : ℝ) ≤ Real.log (3 * (X : ℝ)) :=
    Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hpX)
  rw [Real.log_mul (by norm_num) hXpos.ne'] at hupper
  have hfloor := Nat.lt_floor_add_one ((C + 1) * Real.log (X : ℝ))
  change (C + 1) * Real.log (X : ℝ) < (blockLength (C + 1) X : ℝ) + 1 at hfloor
  nlinarith [mul_le_mul_of_nonneg_left hupper hC.le]

theorem index_bound_of_goodStarts {C delta lam A : ℝ} {X N : ℕ}
    (hdelta : 0 < delta) (hlam : 0 < lam) (hA : 0 < A)
    (hX : 2 ≤ X) (hN : 0 < N)
    (hrange : 2 * X + blockLength lam X ≤ prime N)
    (hthreshold : ∀ p ∈ gapPrimes X (blockLength lam X),
      C * Real.log (p : ℝ) ≤ (blockLength lam X : ℝ))
    (hcompare : (N : ℝ) * Real.log (X : ℝ) ≤ A * (X : ℝ))
    (hstarts : delta * (X : ℝ) ≤ ((goodStarts X (blockLength lam X)).card : ℝ)) :
    delta / (A * lam) * (N : ℝ) ≤ ((largeGapIndices C N).card : ℝ) := by
  have hcount := goodStarts_card_le X (blockLength lam X)
  have hindices := gapPrimes_card_le_largeGapIndices C X (blockLength lam X) N hN
    hrange hthreshold
  have hmul : delta * (X : ℝ) ≤
      ((largeGapIndices C N).card : ℝ) * (lam * Real.log (X : ℝ)) := by
    calc
      delta * (X : ℝ) ≤ ((goodStarts X (blockLength lam X)).card : ℝ) := hstarts
      _ ≤ ((gapPrimes X (blockLength lam X)).card : ℝ) * (blockLength lam X : ℝ) :=
        by exact_mod_cast hcount
      _ ≤ ((largeGapIndices C N).card : ℝ) * (blockLength lam X : ℝ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hindices) (Nat.cast_nonneg _)
      _ ≤ ((largeGapIndices C N).card : ℝ) * (lam * Real.log (X : ℝ)) :=
        mul_le_mul_of_nonneg_left (blockLength_le_mul_log hlam.le hX) (Nat.cast_nonneg _)
  have hcomp := mul_le_mul_of_nonneg_left hcompare hdelta.le
  have hmulA := mul_le_mul_of_nonneg_left hmul hA.le
  have hpos := log_pos_of_two_le hX
  apply (mul_le_mul_iff_left₀ hpos).mp
  apply (mul_le_mul_iff_right₀ (mul_pos hA hlam)).mp
  calc
    (A * lam) * (delta / (A * lam) * (N : ℝ) * Real.log (X : ℝ)) =
        delta * ((N : ℝ) * Real.log (X : ℝ)) := by field_simp [hA.ne', hlam.ne']
    _ ≤ A * (delta * (X : ℝ)) := by nlinarith
    _ ≤ (A * lam) * (((largeGapIndices C N).card : ℝ) * Real.log (X : ℝ)) := by
      nlinarith

end LargePrimeGaps

end OAI

open OAI.LargePrimeGaps Filter MeasureTheory

open scoped Classical ContDiff Topology

theorem OMA.solution : OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1_H1_R1_H2_R1.H3 := by
  intro hg C hC
  obtain ⟨delta,hd,hstarts⟩ := hg C hC
  change ∀ᶠ X : ℕ in atTop, delta*(X:ℝ)≤((goodStarts X (blockLength (C+1) X)).card:ℝ) at hstarts
  let A := 6*(Real.log 4+1)
  have hA : 0<A := by dsimp [A]; positivity
  have hL : 0<C+1 := by linarith
  refine ⟨delta/(A*(C+1)),div_pos hd (mul_pos hA hL),?_⟩
  apply eventually_atTop.mp
  filter_upwards [eventually_scale_comparison,eventually_ge_atTop 1,
    tendsto_indexScale.eventually (eventually_blockLength_le (C+1) hL),
    tendsto_indexScale.eventually (eventually_blockLength_threshold C hC),
    tendsto_indexScale.eventually hstarts] with N hcompare hN hblock hthreshold hcount
  apply index_bound_of_goodStarts hd hL hA hcompare.1 (by omega)
  · have hdiv := Nat.div_mul_le_self (prime N) 3
    change (prime N/3)*3≤prime N at hdiv
    change 2*indexScale N+blockLength (C+1) (indexScale N)≤prime N
    change (indexScale N)*3≤prime N at hdiv
    omega
  · intro p hp
    have hmem := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    exact hthreshold p (by omega) (by omega)
  · exact hcompare.2
  · exact hcount
