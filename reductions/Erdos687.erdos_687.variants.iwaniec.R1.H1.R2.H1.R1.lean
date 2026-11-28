import OMAReductions.R_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2

-- Reduction Erdos687.erdos_687.variants.iwaniec.R1.H1.R2.H1.R1 of step Erdos687.erdos_687.variants.iwaniec.R1.H1.R2.H1
-- Credit: @JamesSlash

/-!
# Iwaniec's `x²` window theorem from the strong prime number theorem

* `H1`: the prime number theorem with the de la Vallée Poussin error term, in the form
  `StrongPNT` of the PrimeNumberTheoremAnd project: `ψ(x) - x = O(x exp(-c √(log x)))`.
* `H2`: Iwaniec's theorem ([I78, Corollary], H. Iwaniec, *On the problem of Jacobsthal*,
  Demonstratio Math. 11 (1978)) conditional on the strong prime number theorem: if `m` consecutive
  integers are each divisible by one of `r ≥ 2` given primes, then `m ≤ C (r log r)²`.
  The Lean development jasondavies/iwaniec-linear-sieve derives it from `StrongPNT` through
  Iwaniec's linear sieve [I71].
* `main`: for the `r = π(x)` primes `p ≤ x`, Chebyshev's bound `π(x) ≤ 8 x / log x` gives
  `r log r ≤ 8 x`, so a block of `⌊64 |C| x²⌋ + 1` consecutive integers cannot be covered.
-/

namespace OMA.R_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2_H1_R1

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

theorem main : H1 → H2 → OMA.R_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2.H1 := by
  intro h1 h2
  obtain ⟨C, hC⟩ := h2 h1
  refine ⟨64 * |C| + 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 3] with x hx M
  set S := (Finset.range (x + 1)).filter Nat.Prime with hSdef
  have hSP : S = Nat.primesLE x := (Nat.primesLE_eq_filter_range x).symm
  have hScard : S.card = Nat.primeCounting x := by
    rw [hSP, Nat.primesLE_card_eq_primeCounting]
  have h2S : 2 ≤ S.card := by
    have hsub : ({2, 3} : Finset ℕ) ⊆ S := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rw [hSdef, Finset.mem_filter, Finset.mem_range]
      rcases hp with rfl | rfl
      · exact ⟨by omega, Nat.prime_two⟩
      · exact ⟨by omega, Nat.prime_three⟩
    have := Finset.card_le_card hsub
    simpa using this
  have hx0 : (3 : ℝ) ≤ x := by exact_mod_cast hx
  have hlx : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  set r : ℝ := (S.card : ℝ) with hrdef
  have hr2 : (2 : ℝ) ≤ r := by rw [hrdef]; exact_mod_cast h2S
  have hrx : r ≤ (x : ℝ) := by
    rw [hrdef, hScard]
    exact_mod_cast OMA.R_Erdos687_erdos_687_variants_iwaniec_R1.primeCounting_le_self x
  have hr8 : r ≤ 8 * (x : ℝ) / Real.log (x : ℝ) := by
    rw [hrdef, hScard]
    exact OMA.R_Erdos687_erdos_687_variants_iwaniec_R1.primeCounting_le_eight_mul_div_log (by omega)
  have hlr0 : 0 ≤ Real.log r := Real.log_nonneg (by linarith)
  have hlr : Real.log r ≤ Real.log (x : ℝ) := Real.log_le_log (by linarith) hrx
  have hrl : r * Real.log r ≤ 8 * (x : ℝ) := by
    calc r * Real.log r ≤ (8 * (x : ℝ) / Real.log (x : ℝ)) * Real.log (x : ℝ) :=
          mul_le_mul hr8 hlr hlr0 (by positivity)
      _ = 8 * (x : ℝ) := by field_simp
  have hsq : (r * Real.log r) ^ 2 ≤ 64 * (x : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (mul_nonneg (by linarith) hlr0) hrl 2
    nlinarith
  set B : ℝ := 64 * |C| * (x : ℝ) ^ 2 with hBdef
  have hB0 : 0 ≤ B := by positivity
  by_contra hno
  push_neg at hno
  have hcov : ∀ k < ⌊B⌋₊ + 1, ∃ p ∈ S, (p : ℤ) ∣ ((M + 1 : ℕ) : ℤ) + k := by
    intro k hk
    have hkB : (k : ℝ) ≤ B := by
      have : k ≤ ⌊B⌋₊ := by omega
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le hB0)
    have hkA : (k : ℝ) < (64 * |C| + 2) * (x : ℝ) ^ 2 := by
      have : (0 : ℝ) < 2 * (x : ℝ) ^ 2 := by positivity
      rw [hBdef] at hkB
      nlinarith
    obtain ⟨p, hpx, hp, hpd⟩ := hno k hkA
    refine ⟨p, ?_, ?_⟩
    · rw [hSdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp⟩
    · have hd : ((p : ℕ) : ℤ) ∣ ((M + 1 + k : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hpd
      push_cast at hd ⊢
      exact hd
  have hm := hC S (fun p hp => (Finset.mem_filter.mp hp).2) h2S ((M + 1 : ℕ) : ℤ) (⌊B⌋₊ + 1) hcov
  rw [← hrdef] at hm
  have hlt : B < ((⌊B⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one _
  have hCabs : C * (r * Real.log r) ^ 2 ≤ |C| * (64 * (x : ℝ) ^ 2) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hsq (abs_nonneg C))
  rw [hBdef] at hlt
  linarith

end OMA.R_Erdos687_erdos_687_variants_iwaniec_R1_H1_R2_H1_R1
