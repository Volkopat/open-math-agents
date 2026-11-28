import OMAStatements.S_mo_447657
import Mathlib

-- Problem: mo-447657, does the going down property imply that Spec B -> Spec A is open,
-- without finiteness hypotheses?
-- Credit: @ivillar, original merged proof #15733.
--
-- The principal-ideal zero criterion replaces the final explicit generator-membership argument.
-- No. The rationals are flat over the integers, so going down holds, but the image of
-- Spec Q in Spec Z is the generic point alone, which is not open: every nonempty open set of
-- Spec Z contains the ideal (p) for all but finitely many primes p.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_447657.main) := by
  intro h
  have hflat : Module.Flat ℤ ℚ := inferInstance
  have hgd : Algebra.HasGoingDown ℤ ℚ := Algebra.HasGoingDown.of_flat
  have hopen := (h ℤ ℚ hgd).isOpen_range
  rw [PrimeSpectrum.isOpen_iff] at hopen
  obtain ⟨s, hs⟩ := hopen
  have hbot : ∀ q : PrimeSpectrum ℚ,
      (PrimeSpectrum.comap (algebraMap ℤ ℚ) q).asIdeal = ⊥ := by
    intro q
    have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
    change Ideal.comap (algebraMap ℤ ℚ) q.asIdeal = ⊥
    rw [hq]
    ext x
    simp [Ideal.mem_comap]
  have hx0 : PrimeSpectrum.comap (algebraMap ℤ ℚ) ⟨⊥, Ideal.isPrime_bot⟩ ∉
      PrimeSpectrum.zeroLocus s := by
    rw [← hs]
    intro hmem
    exact hmem ⟨_, rfl⟩
  rw [PrimeSpectrum.mem_zeroLocus, Set.not_subset] at hx0
  obtain ⟨f, hfs, hf⟩ := hx0
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf (Ideal.zero_mem _)
  obtain ⟨p, hp, hpprime⟩ := Nat.exists_infinite_primes (f.natAbs + 1)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hpprime.ne_zero
  have hprime : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp hpprime)
  have hP : (⟨Ideal.span ({(p : ℤ)} : Set ℤ), hprime⟩ : PrimeSpectrum ℤ) ∈
      PrimeSpectrum.zeroLocus s := by
    rw [← hs]
    rintro ⟨q, hq⟩
    have h1 := hbot q
    rw [hq] at h1
    exact hp0 (Ideal.span_singleton_eq_bot.mp h1)
  rw [PrimeSpectrum.mem_zeroLocus] at hP
  have hfp : f ∈ Ideal.span ({(p : ℤ)} : Set ℤ) := hP hfs
  rw [Ideal.mem_span_singleton] at hfp
  have hdvd : p ∣ f.natAbs := Int.natCast_dvd.mp hfp
  have hle : p ≤ f.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hf0) hdvd
  omega
