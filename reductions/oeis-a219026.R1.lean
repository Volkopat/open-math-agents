import OMAStatements.S_oeis_a219026

-- Reduction oeis-a219026.R1 of A219026: Number of primes p<=n such that 2n-p and 2n+p-2 are both prime.
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a219026_R1

/-- Odd `n > 150`: some prime `p ≤ n` has `2n - p` and `2n + p - 2` prime. -/
def H1 : Prop :=
  ∀ n : ℕ, 150 < n → Odd n →
    ∃ p : ℕ, p ≤ n ∧ Nat.Prime p ∧ Nat.Prime (2 * n - p) ∧ Nat.Prime (2 * n + p - 2)

/-- Even `n > 150`: some prime `p ≤ n` has `2n - p` and `2n + p - 2` prime. -/
def H2 : Prop :=
  ∀ n : ℕ, 150 < n → Even n →
    ∃ p : ℕ, p ≤ n ∧ Nat.Prime p ∧ Nat.Prime (2 * n - p) ∧ Nat.Prime (2 * n + p - 2)

/-- Every `n ≤ 150` is decided by computation: a witness exists exactly when `n` is not one of
the exceptions `1, 2, 4, 6, 10, 22, 57`. -/
theorem small : ∀ n ≤ 150, 0 < n →
    ((∃ p ≤ n, Nat.Prime p ∧ Nat.Prime (2 * n - p) ∧ Nat.Prime (2 * n + p - 2)) ↔
      n ∉ ({1, 2, 4, 6, 10, 22, 57} : Finset ℕ)) := by
  decide +kernel

/-- All `n ≤ 150`, which include every exception, are settled by computation; for `n > 150` the
forward implication is trivial and the existence of a witness is split by parity. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a219026.main := by
  intro h1 h2 n hn
  rcases (show n ≤ 150 ∨ 150 < n by omega) with hs | hl
  · have := small n hs hn
    constructor
    · rintro ⟨p, hpn, hp⟩
      exact this.mp ⟨p, hpn, hp⟩
    · intro h
      obtain ⟨p, hpn, hp⟩ := this.mpr h
      exact ⟨p, hpn, hp⟩
  · constructor
    · intro _ hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    · intro _
      rcases Nat.even_or_odd n with he | ho
      · exact h2 n hl he
      · exact h1 n hl ho

end OMA.R_oeis_a219026_R1
