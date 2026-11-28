import OMAStatements.S_oeis_a348598

open OMA.S_oeis_a348598

namespace A348598Counterexample

/-- A prime above 17 of the form k² + 1 has k ≥ 6: k = 5 gives 26. -/
lemma nextAt17 : nextSquarePrime 17 37 := by
  refine ⟨⟨by decide, 6, rfl⟩, by decide, ?_⟩
  rintro _ ⟨hp, k, rfl⟩ h
  by_cases h₆ : 6 ≤ k
  · have := Nat.pow_le_pow_left h₆ 2
    omega
  by_cases h₄ : k ≤ 4
  · have := Nat.pow_le_pow_left h₄ 2
    omega
  have : k = 5 := by omega
  subst k
  exact False.elim ((by decide : ¬ Nat.Prime (5 ^ 2 + 1)) hp)

/-- If k² + 1 < 42437 = 206² + 1 then k is in the finite search. -/
lemma rootBound (k : ℕ) (h : k ^ 2 + 1 < 42437) : k < 206 := by
  by_cases hk : 206 ≤ k
  · have := Nat.pow_le_pow_left hk 2
    omega
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
/-- Exhaust all possible pairs of smaller roots. The least-factor criterion
checks primality by trial division. Testing the congruence before testing
the modulus for primality keeps the computation small. -/
lemma noEarlier :
    ∀ i : Fin 206, let p := i.val ^ 2 + 1
      17 < p → p.minFac = p → ∀ j : Fin 206, let q := j.val ^ 2 + 1
        17 < q → p % q = 17 → q.minFac ≠ q := by decide +kernel

/-- 42437 = 206² + 1 = 17 + 420 · 101; 101 = 10² + 1. -/
lemma witness : qualifies 17 42437 101 := by
  exact ⟨⟨Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩, 206, rfl⟩,
    by decide, ⟨by decide, 10, rfl⟩, by decide, by decide⟩

/-- Any qualifying modulus q is at most p, since 17 < p and 17 < q.
Thus a smaller p would put the roots of both p and q in the search. -/
lemma leastWitness (p q : ℕ) (h : qualifies 17 p q) : 42437 ≤ p := by
  rcases h with ⟨⟨hp, k, rfl⟩, h₁, ⟨hq, m, rfl⟩, h₂, hmod⟩
  rw [Nat.mod_eq_of_lt h₂] at hmod
  by_cases hlt : k ^ 2 + 1 < 42437
  · have hle : m ^ 2 + 1 ≤ k ^ 2 + 1 := by
      by_cases hgt : k ^ 2 + 1 < m ^ 2 + 1
      · rw [Nat.mod_eq_of_lt hgt] at hmod
        omega
      omega
    exact False.elim (noEarlier ⟨k, rootBound k hlt⟩ h₁ hp.minFac_eq
      ⟨m, rootBound m (lt_of_le_of_lt hle hlt)⟩ h₂ hmod hq.minFac_eq)
  omega

end A348598Counterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a348598.main) := by
  intro claim
  have h := claim 17 37 42437 101 ⟨by decide, 4, rfl⟩
    A348598Counterexample.nextAt17 A348598Counterexample.witness
    A348598Counterexample.leastWitness
  exact (by decide : 101 ≠ 37) h
