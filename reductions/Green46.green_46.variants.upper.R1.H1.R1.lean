import OMAReductions.R_Green46_green_46_variants_upper_R1

-- Reduction Green46.green_46.variants.upper.R1.H1.R1 of step Green46.green_46.variants.upper.R1.H1
-- Credit: @JamesSlash

/-!
# Iwaniec's Jacobsthal bound from the strong prime number theorem

* `H1`: the prime number theorem with the de la Vallée Poussin error term, in the form
  `StrongPNT` of the PrimeNumberTheoremAnd project: `ψ(x) - x = O(x exp(-c √(log x)))`.
* `H2`: Iwaniec's theorem ([I78, Corollary], H. Iwaniec, *On the problem of Jacobsthal*,
  Demonstratio Math. 11 (1978)) conditional on the strong prime number theorem: if `m` consecutive
  integers are each divisible by one of `r ≥ 2` given primes, then `m ≤ C (r log r)²`.
  The Lean development jasondavies/iwaniec-linear-sieve derives it from `StrongPNT` through
  Iwaniec's linear sieve [I71].
* `main`: for `d` with `k ≥ 2` distinct prime factors, a block of `⌊C (k log k)²⌋ + 1`
  consecutive integers none coprime to `d` would be covered by the prime factors of `d`,
  contradicting `H2`.
-/

namespace OMA.R_Green46_green_46_variants_upper_R1_H1_R1

open Filter Finset Real

/-- The strong prime number theorem (`StrongPNT` in PrimeNumberTheoremAnd). -/
def H1 : Prop :=
  ∃ c > 0, Asymptotics.IsBigO Filter.atTop (Chebyshev.psi - id)
    (fun x : ℝ ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)))

/-- Iwaniec's bound for Jacobsthal's problem, assuming the strong prime number theorem. -/
def H2 : Prop :=
  (∃ c > 0, Asymptotics.IsBigO Filter.atTop (Chebyshev.psi - id)
    (fun x : ℝ ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)))) →
  ∃ C : ℝ, ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → 2 ≤ S.card →
    ∀ (x : ℤ) (m : ℕ), (∀ k < m, ∃ p ∈ S, (p : ℤ) ∣ x + k) →
      (m : ℝ) ≤ C * ((S.card : ℝ) * Real.log S.card) ^ 2

lemma one_le_mul_log {k : ℕ} (hk : 2 ≤ k) : 1 ≤ ((k : ℝ) * Real.log k) ^ 2 := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hl : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hk2
  have h1 : 1 ≤ (k : ℝ) * Real.log k := by nlinarith
  nlinarith

theorem main : H1 → H2 → OMA.R_Green46_green_46_variants_upper_R1.H1 := by
  intro h1 h2
  obtain ⟨C, hC⟩ := h2 h1
  refine ⟨|C| + 1, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with k hk
  have ht := one_le_mul_log hk
  set t := ((k : ℝ) * Real.log k) ^ 2 with htdef
  have hCt : 0 ≤ |C| * t := by positivity
  refine ⟨⌊|C| * t⌋₊ + 1, ?_, ?_⟩
  · have hfl : (⌊|C| * t⌋₊ : ℝ) ≤ |C| * t := Nat.floor_le hCt
    push_cast
    nlinarith
  · intro d hd hcard a
    by_contra hno
    push_neg at hno
    have hcov : ∀ j < ⌊|C| * t⌋₊ + 1, ∃ p ∈ d.primeFactors, (p : ℤ) ∣ a + j := by
      intro j hj
      have hnc := hno j hj
      obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
      refine ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hp2, hd.ne'⟩, ?_⟩
      exact Int.natCast_dvd.mpr hp1
    have hm := hC d.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) (by omega)
      a (⌊|C| * t⌋₊ + 1) hcov
    rw [hcard] at hm
    have hlt : |C| * t < ((⌊|C| * t⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      exact Nat.lt_floor_add_one _
    have hCabs : C * t ≤ |C| * t := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    rw [← htdef] at hm
    linarith

end OMA.R_Green46_green_46_variants_upper_R1_H1_R1
