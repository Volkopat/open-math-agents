import OMAStatements.S_oeis_a249541

-- Reduction oeis-a249541.R1 of A249541: Numbers m such that phi(m-2) divides m-1 where phi is Euler's totient function (A000010).
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a249541_R1

/-- Odd squarefree composite `k` prime to `3`: `3 φ(k) ≠ k + 1`. -/
def H1 : Prop :=
  ∀ k : ℕ, 5 ≤ k → Odd k → ¬ 3 ∣ k → ¬ k.Prime → Squarefree k → 3 * Nat.totient k ≠ k + 1

/-- Odd composite `k` prime to `3` that is not squarefree: `3 φ(k) ≠ k + 1`. -/
def H2 : Prop :=
  ∀ k : ℕ, 5 ≤ k → Odd k → ¬ 3 ∣ k → ¬ k.Prime → ¬ Squarefree k → 3 * Nat.totient k ≠ k + 1

/-- With `k = m - 2`: `k = 1` fails, `k = 2` is the solution `m = 4`, even `k ≥ 4` fails since
`φ(k)` is even and `k + 1` odd, `3 ∣ k` fails mod `3`, and prime `k` gives `3(k - 1) = k + 1`, so
`k = 2`. Odd composite `k` prime to `3` is split into squarefree (`H1`) and not (`H2`). -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a249541.main := by
  intro h1 h2 m hm
  constructor
  · intro h
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    rw [show k + 2 - 2 = k by omega, show k + 2 - 1 = k + 1 by omega] at h
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | rfl | hk3
    · simp at h
    · simp at h
    · rfl
    · exfalso
      by_cases he : Even k
      · obtain ⟨t, ht⟩ := Nat.totient_even (by omega : 2 < k)
        obtain ⟨s, hs⟩ := he
        omega
      have ho : Odd k := Nat.not_even_iff_odd.mp he
      by_cases h3 : 3 ∣ k
      · omega
      by_cases hpk : k.Prime
      · rw [Nat.totient_prime hpk] at h
        omega
      have hk5 : 5 ≤ k := by
        obtain ⟨s, hs⟩ := ho
        omega
      by_cases hsq : Squarefree k
      · exact h1 k hk5 ho h3 hpk hsq h
      · exact h2 k hk5 ho h3 hpk hsq h
  · rintro rfl
    simp [Nat.totient_two]

end OMA.R_oeis_a249541_R1
