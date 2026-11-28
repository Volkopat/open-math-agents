import OMAStatements.S_oeis_a401145

-- Reduction oeis-a401145.R1 of A401145: Number of partitions of n into distinct parts such that n plus the product of the parts is prime.
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a401145_R1

/-- Odd `n ≥ 3`: some set of distinct positive integers summing to `n` has `n + ∏` prime. -/
def H1 : Prop :=
  ∀ n : ℕ, 3 ≤ n → Odd n →
    ∃ s : Finset ℕ, (∀ x ∈ s, 0 < x) ∧ ∑ x ∈ s, x = n ∧ Nat.Prime (n + ∏ x ∈ s, x)

/-- Even `n ≥ 4`: some set of distinct positive integers summing to `n` has `n + ∏` prime. -/
def H2 : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n →
    ∃ s : Finset ℕ, (∀ x ∈ s, 0 < x) ∧ ∑ x ∈ s, x = n ∧ Nat.Prime (n + ∏ x ∈ s, x)

/-- The finite check for `n = 2`: the only admissible set is `{2}`, and `2 + 2 = 4`. -/
theorem two_check : ∀ t ∈ (Finset.Icc 1 2).powerset,
    ∑ x ∈ t, x = 2 → ¬ Nat.Prime (2 + ∏ x ∈ t, x) := by
  decide

/-- `n = 2` fails (finite check), `n = 1` works with `{1}`; the rest is split by parity. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a401145.main := by
  intro h1 h2 n hn
  constructor
  · rintro ⟨s, hs, hsum, hp⟩ rfl
    have hsub : s ⊆ Finset.Icc 1 2 := by
      intro x hx
      rw [Finset.mem_Icc]
      exact ⟨hs x hx, hsum ▸ Finset.single_le_sum (fun i _ => Nat.zero_le i) hx⟩
    exact two_check s (Finset.mem_powerset.mpr hsub) hsum hp
  · intro hn2
    rcases (show n = 1 ∨ 3 ≤ n by omega) with rfl | h3
    · exact ⟨{1}, by simp, by simp, by norm_num⟩
    · rcases Nat.even_or_odd n with he | ho
      · exact h2 n (by obtain ⟨t, ht⟩ := he; omega) he
      · exact h1 n h3 ho

end OMA.R_oeis_a401145_R1
