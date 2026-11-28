import FormalConjectures.ErdosProblems.«205»

-- Problem: Erdős Problem 205, variant odd_counterexamples
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/205.lean
--   (declaration Erdos205.erdos_205.variants.odd_counterexamples)
-- Credit: @LordMike

/-!
# Reduction of Erdős 205 (odd counterexamples) to a covering statement

Target: infinitely many odd `n` such that no decomposition `n = 2 ^ k + m` has
`Ω m < log (log m)`.

* `H1` (OPEN, and STRONGER than the target: this is an upward reduction). A covering statement
  for the powers of two: there are arbitrarily large odd moduli `M` with a residue `r` such that
  for every `k` with `2 ^ k < 4 * M` the forced common divisor `gcd (M, r - 2 ^ k)` already has at
  least `log (log (4 * M))` prime factors, counted with multiplicity.
  For `M` squarefree this says: every `k` lies in at least `log log (4 M)` of the classes
  `{k | 2 ^ k ≡ r [MOD p]}`, `p ∣ M` prime, each a residue class modulo the order of `2` modulo
  `p`. This is the Erdős covering-congruence method for `2 ^ k + p`, with multiplicity.
* `H2` (elementary): `Ω` is monotone along divisibility of nonzero numbers.

`main` takes `M, r` from `H1`, picks the odd `n ≡ r [MOD M]` in `[M, 3 * M)`, and notes that
every `m = n - 2 ^ k` is a nonzero multiple of `gcd (M, r - 2 ^ k)`.
-/

namespace OMA.R_Erdos205_erdos_205_variants_odd_counterexamples_R1

open scoped ArithmeticFunction.Omega

/-- Covering of the exponents `k` by one residue class `r` modulo an odd `M`, with multiplicity
`log log`. OPEN. -/
def H1 : Prop :=
  ∀ N : ℕ, ∃ M r : ℕ, Odd M ∧ N ≤ M ∧
    ∀ k : ℕ, 2 ^ k < 4 * M →
      Real.log (Real.log ((4 * M : ℕ) : ℝ)) ≤ (Ω (Int.gcd (M : ℤ) ((r : ℤ) - 2 ^ k)) : ℝ)

/-- `Ω` is monotone along divisibility. Elementary. -/
def H2 : Prop :=
  ∀ a b : ℕ, b ≠ 0 → a ∣ b → Ω a ≤ Ω b

/-- An odd `n` in `[M, 3 M)` with `n ≡ r [MOD M]`. -/
lemma exists_odd_rep (M r : ℕ) (hM : Odd M) :
    ∃ n : ℕ, Odd n ∧ M ≤ n ∧ n < 3 * M ∧ (M : ℤ) ∣ (n : ℤ) - r := by
  have hMpos : 0 < M := hM.pos
  have hy : r % M < M := Nat.mod_lt _ hMpos
  have key : ∀ t : ℕ, (M : ℤ) ∣ ((r % M + t * M : ℕ) : ℤ) - r := by
    intro t
    have h := Nat.mod_add_div r M
    refine ⟨(t : ℤ) - (r / M : ℕ), ?_⟩
    have h2 : ((r % M : ℕ) : ℤ) + (M : ℤ) * ((r / M : ℕ) : ℤ) = (r : ℤ) := by exact_mod_cast h
    rw [Nat.cast_add, Nat.cast_mul]
    linear_combination h2
  by_cases hodd : Odd (r % M + 1 * M)
  · exact ⟨r % M + 1 * M, hodd, by omega, by omega, key 1⟩
  · refine ⟨r % M + 2 * M, ?_, by omega, by omega, key 2⟩
    rw [Nat.not_odd_iff_even] at hodd
    have : r % M + 2 * M = (r % M + 1 * M) + M := by ring
    rw [this]
    exact hodd.add_odd hM

theorem main : H1 → H2 →
    type_of% @Erdos205.erdos_205.variants.odd_counterexamples := by
  intro h1 h2
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨M, r, hModd, hN, hcov⟩ := h1 (N + 2)
  obtain ⟨n, hnodd, hMn, hn3, hres⟩ := exists_odd_rep M r hModd
  refine ⟨n, ⟨hnodd, ?_⟩, by omega⟩
  rintro ⟨k, m, hnm, hlt⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [add_zero] at hnm
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · omega
    · rw [hnm] at hnodd
      exact absurd hnodd (by
        rw [Nat.not_odd_iff_even]
        exact (Nat.even_pow.mpr ⟨even_two, by omega⟩))
  have h2k : 0 < 2 ^ k := by positivity
  have hk : 2 ^ k < 4 * M := by omega
  have hc := hcov k hk
  have hgdvd : Int.gcd (M : ℤ) ((r : ℤ) - 2 ^ k) ∣ m := by
    have h1' : ((Int.gcd (M : ℤ) ((r : ℤ) - 2 ^ k) : ℕ) : ℤ) ∣ (n : ℤ) - r :=
      (Int.gcd_dvd_left _ _).trans hres
    have h2' : ((Int.gcd (M : ℤ) ((r : ℤ) - 2 ^ k) : ℕ) : ℤ) ∣ (r : ℤ) - 2 ^ k :=
      Int.gcd_dvd_right _ _
    have h3 : (m : ℤ) = ((n : ℤ) - r) + ((r : ℤ) - 2 ^ k) := by
      rw [hnm]; push_cast; ring
    have h4 : ((Int.gcd (M : ℤ) ((r : ℤ) - 2 ^ k) : ℕ) : ℤ) ∣ (m : ℤ) := by
      rw [h3]; exact dvd_add h1' h2'
    exact_mod_cast h4
  have hcard : (Ω (Int.gcd (M : ℤ) ((r : ℤ) - 2 ^ k)) : ℝ) ≤ (Ω m : ℝ) := by
    exact_mod_cast h2 _ m hm0 hgdvd
  have hm4 : (m : ℝ) ≤ ((4 * M : ℕ) : ℝ) := by
    have : m ≤ 4 * M := by omega
    exact_mod_cast this
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have hloglog : Real.log (Real.log (m : ℝ)) ≤ (Ω m : ℝ) := by
    rcases (Nat.one_le_iff_ne_zero.mpr hm0).eq_or_lt with h1m | h1m
    · rw [← h1m]
      simp
    · have hlogpos : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast h1m)
      calc Real.log (Real.log (m : ℝ))
          ≤ Real.log (Real.log ((4 * M : ℕ) : ℝ)) :=
            Real.log_le_log hlogpos (Real.log_le_log hmpos hm4)
        _ ≤ Ω (Int.gcd (M : ℤ) ((r : ℤ) - 2 ^ k)) := hc
        _ ≤ Ω m := hcard
  exact absurd hlt (not_lt.mpr hloglog)

end OMA.R_Erdos205_erdos_205_variants_odd_counterexamples_R1
