import OMAStatements.S_oeis_a382837

/-!
For an even integer the two largest divisors are the integer and its half.
Every remaining divisor is at most one third of the integer. Alternation
therefore gives a lower bound of one sixth for the proportion left after
subtracting the alternating sum. Euler's totient product and the divergent
sum of the reciprocals of the primes give two coprime moduli on whose even
multiples the totient is smaller. The Chinese remainder theorem realizes
any prescribed even gap between these multiples.

Shreyansh Jaiswal's Theorem 2 uses the first three divisors for multiples
of a fixed primorial: https://oeis.org/A382837/a382837.pdf. Here the bound
holds for all even integers, allowing two independent sets of prime factors.
-/

namespace EvenDivisorGaps

open Finset OMA.S_oeis_a382837

private lemma alternating_bounds (l : List ℕ) (hs : l.Pairwise (· ≥ ·)) (b : ℕ)
    (hb : ∀ d ∈ l, d ≤ b) :
    0 ≤ alternatingSum l ∧ alternatingSum l ≤ (b : ℤ) := by
  induction l generalizing b with
  | nil => simp [alternatingSum]
  | cons d rest ih =>
    obtain ⟨hd, hrest⟩ := List.pairwise_cons.mp hs
    obtain ⟨hlo, hhi⟩ := ih hrest d hd
    have hdb := hb d (by simp)
    simp only [alternatingSum]
    omega

private lemma alternating_gap (u : ℕ) (hu : 0 < u) :
    (2 * u : ℤ) ≤ 6 * ((2 * u : ℤ) - chi (2 * u)) := by
  let D := (2 * u).divisors
  let R := (D.erase (2 * u)).erase u
  have hn : 2 * u ≠ 0 := by omega
  have htop : 2 * u ∈ D := Nat.mem_divisors.mpr ⟨dvd_rfl, hn⟩
  have hhalf : u ∈ D.erase (2 * u) := mem_erase.mpr
    ⟨by omega, Nat.mem_divisors.mpr ⟨dvd_mul_left _ _, hn⟩⟩
  have small (d : ℕ) (hd : d ∈ R) : 3 * d ≤ 2 * u := by
    obtain ⟨hdu, hd'⟩ := mem_erase.mp hd
    obtain ⟨hdn, hdiv⟩ := mem_erase.mp hd'
    obtain ⟨q, hq⟩ := (Nat.mem_divisors.mp hdiv).1
    have hq3 : 3 ≤ q := by
      by_contra! h
      rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with h0 | h1 | h2
      · rw [h0, Nat.mul_zero] at hq
        omega
      · rw [h1, Nat.mul_one] at hq
        omega
      · rw [h2] at hq
        omega
    simpa [hq, Nat.mul_comm] using Nat.mul_le_mul_right d hq3
  have hR : D = insert (2 * u) (insert u R) := by
    rw [show insert u R = D.erase (2 * u) from insert_erase hhalf, insert_erase htop]
  have hfirst : ∀ d ∈ insert u R, d ≤ 2 * u := by
    intro d hd
    rcases mem_insert.mp hd with rfl | hd
    · omega
    · have := small d hd; omega
  have hsecond : ∀ d ∈ R, d ≤ u := by
    intro d hd
    have := small d hd
    omega
  have htop' : 2 * u ∉ insert u R := by
    change 2 * u ∉ insert u ((D.erase (2*u)).erase u)
    simp [show 2*u ≠ u by omega]
  have hu' : u ∉ R := notMem_erase _ _
  have hsort : D.sort (· ≥ ·) = (2 * u) :: u :: R.sort (· ≥ ·) := by
    conv_lhs => rw [hR, sort_insert (· ≥ ·) hfirst htop', sort_insert (· ≥ ·) hsecond hu']
  have hb := (alternating_bounds _ (R.pairwise_sort (· ≥ ·)) ((2*u)/3) (by
    intro d hd
    have := small d (by simpa only [Finset.mem_sort] using hd)
    omega)).2
  unfold chi
  change _ ≤ 6 * (_ - alternatingSum (D.sort (· ≥ ·)))
  rw [hsort]
  simp only [alternatingSum, Nat.cast_mul, Nat.cast_ofNat]
  omega

private noncomputable def recip (p : ℕ) : ℝ := (p : ℝ)⁻¹

private lemma recip_nonneg (p : ℕ) : 0 ≤ recip p := by unfold recip; positivity

/-- Discarding finitely many primes still leaves finite sets of arbitrarily
large reciprocal sum. Here a fixed bound suffices. -/
private lemma prime_set (F : Finset ℕ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧ Disjoint S F ∧ 6 < ∑ p ∈ S, recip p := by
  classical
  by_contra h
  apply not_summable_one_div_on_primes
  apply summable_of_sum_le (c := 6 + ∑ p ∈ F, recip p)
  · intro p
    exact Set.indicator_nonneg (fun k _ => by positivity) p
  · intro V
    let T := V.filter Nat.Prime
    have hd : Disjoint (T \ F) F := sdiff_disjoint
    have hbound : ∑ p ∈ T \ F, recip p ≤ 6 := by
      apply le_of_not_gt
      intro hsum
      exact h ⟨T \ F, fun p hp => (mem_filter.mp (mem_sdiff.mp hp).1).2, hd, hsum⟩
    calc
      ∑ p ∈ V, Set.indicator {p : ℕ | Nat.Prime p} (fun p => (1 : ℝ) / p) p
          = ∑ p ∈ T, recip p := by simp [T, sum_filter, Set.indicator, recip, one_div]
      _ ≤ ∑ p ∈ (T \ F) ∪ F, recip p := by
        apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => recip_nonneg p)
        intro p hp
        by_cases hf : p ∈ F <;> simp [hf, hp]
      _ = (∑ p ∈ T \ F, recip p) + ∑ p ∈ F, recip p := sum_union hd
      _ ≤ _ := by linarith

private lemma small_totient {m : ℕ} (hm : 0 < m)
    (hs : 6 < ∑ p ∈ m.primeFactors, recip p) : 6 * m.totient < m := by
  have hphi : (m.totient : ℝ) = m * ∏ p ∈ m.primeFactors, (1 - recip p) := by
    unfold recip
    have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors m)
    push_cast at h
    exact h
  have hprod : (∏ p ∈ m.primeFactors, (1 - recip p)) ≤
      Real.exp (-(∑ p ∈ m.primeFactors, recip p)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ h1)
    · intro p _
      linarith [Real.add_one_le_exp (-(recip p))]
  have hexp : 6 < Real.exp (∑ p ∈ m.primeFactors, recip p) := by
    linarith [Real.add_one_le_exp (∑ p ∈ m.primeFactors, recip p)]
  have hsmall : Real.exp (-(∑ p ∈ m.primeFactors, recip p)) < (1 : ℝ)/6 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) hexp
  have h := mul_lt_mul_of_pos_left (hprod.trans_lt hsmall) (show (0 : ℝ) < m by exact_mod_cast hm)
  rw [← hphi] at h
  exact_mod_cast (show 6 * (m.totient : ℝ) < m by linarith)

private lemma even_multiple_is_term (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hsum : 6 < ∑ p ∈ S, recip p) (u : ℕ) (hu : 0 < u) (hdiv : (∏ p ∈ S, p) ∣ u) :
    IsTerm (2 * u) := by
  have hm : 0 < 2*u := by omega
  have sub : S ⊆ (2*u).primeFactors := by
    intro p hp
    apply Nat.mem_primeFactors.mpr
    exact ⟨hprime p hp, (Finset.dvd_prod_of_mem (fun i : ℕ => i) hp).trans
      (hdiv.trans (dvd_mul_left _ _)), hm.ne'⟩
  have htot := small_totient hm (hsum.trans_le
    (sum_le_sum_of_subset_of_nonneg sub (fun p _ _ => recip_nonneg p)))
  refine ⟨hm, ?_⟩
  have := alternating_gap u hu
  push_cast
  omega

end EvenDivisorGaps

open Finset EvenDivisorGaps OMA.S_oeis_a382837

theorem OMA.solution : type_of% @OMA.S_oeis_a382837.main := by
  rintro n ⟨t, rfl⟩
  obtain ⟨S, hS, _, hs⟩ := prime_set ∅
  obtain ⟨T, hT, hTS, ht⟩ := prime_set S
  let A := ∏ p ∈ S, p
  let B := ∏ p ∈ T, p
  have ha : 0 < A := prod_pos (fun p hp => (hS p hp).pos)
  have hb : 0 < B := prod_pos (fun p hp => (hT p hp).pos)
  have co : A.Coprime B := by
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    apply (Nat.coprime_primes (hS p hp) (hT q hq)).mpr
    rintro rfl
    exact Finset.disjoint_left.mp hTS hq hp
  obtain ⟨x, hxA, hxB⟩ := Nat.chineseRemainder co 0 (B*t-t)
  have hAx : A ∣ x := Nat.modEq_zero_iff_dvd.mp hxA
  have hBt : t ≤ B*t := by simpa using Nat.mul_le_mul_right t (show 1 ≤ B by omega)
  have hBx : B ∣ x+t := by
    apply Nat.modEq_zero_iff_dvd.mp
    have e := hxB.add_right t
    rw [Nat.sub_add_cancel hBt] at e
    exact e.trans (dvd_mul_right B t).modEq_zero_nat
  apply Set.infinite_of_forall_exists_gt
  intro bound
  let shift := A*B*(bound+1)
  have hAs : A ∣ shift := (dvd_mul_right A B).trans (dvd_mul_right _ _)
  have hBs : B ∣ shift := (dvd_mul_left B A).trans (dvd_mul_right _ _)
  have big : bound < shift := by
    have hprod : 1 ≤ A*B := Nat.mul_pos ha hb
    have H := Nat.mul_le_mul_right (bound+1) hprod
    change bound < A*B*(bound+1)
    rw [one_mul] at H
    omega
  have first := even_multiple_is_term S hS hs (x+shift) (by omega) (dvd_add hAx hAs)
  have second := even_multiple_is_term T hT ht ((x+t)+shift) (by omega) (dvd_add hBx hBs)
  refine ⟨2*(x+shift), ⟨first, ?_⟩, by omega⟩
  rw [show 2*(x+shift)+(t+t) = 2*((x+t)+shift) by omega]
  exact second
