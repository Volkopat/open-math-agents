import OMAStatements.S_oeis_a137996

-- Reduction oeis-a137996.R1 of A137996: Numbers which are not the sum of a triangular number and zero or a prime = 1 (mod 4).
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a137996_R1

open OMA.S_oeis_a137996

/-- Even `n > 216` is a prime or zero plus a triangular number. -/
def H1 : Prop := ∀ n : ℕ, 216 < n → Even n → IsPrimeOrZeroPlusTriangular n

/-- Odd `n > 216` is a prime or zero plus a triangular number. -/
def H2 : Prop := ∀ n : ℕ, 216 < n → Odd n → IsPrimeOrZeroPlusTriangular n

/-- `216 - k(k+1)/2` is never zero or prime for `k ≤ 20` (direct computation). -/
theorem key216 : ∀ k ≤ 20, ¬ (216 - k * (k + 1) / 2 = 0 ∨ (216 - k * (k + 1) / 2).Prime) := by
  decide +kernel

/-- Every `n < 216` is a prime or zero plus a triangular number `k(k+1)/2` with `k ≤ 20`. -/
theorem small : ∀ n < 216, ∃ k ≤ 20, k * (k + 1) / 2 ≤ n ∧
    (n - k * (k + 1) / 2 = 0 ∨ (n - k * (k + 1) / 2).Prime) := by
  decide +kernel

/-- `216` is the exception and every `n < 216` is representable (computation); `n > 216` is split
by parity. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a137996.main := by
  intro h1 h2 n
  constructor
  · rintro ⟨p, k, hp, h⟩ rfl
    have hk : k ≤ 20 := by
      by_contra hc
      have : 21 * 22 ≤ k * (k + 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hpe : p = 216 - k * (k + 1) / 2 := by omega
    exact key216 k hk (hpe ▸ hp)
  · intro hn
    rcases (show n < 216 ∨ 216 < n by omega) with hs | hl
    · obtain ⟨k, -, hkn, hk⟩ := small n hs
      exact ⟨n - k * (k + 1) / 2, k, hk, by omega⟩
    · rcases Nat.even_or_odd n with he | ho
      · exact h1 n hl he
      · exact h2 n hl ho

end OMA.R_oeis_a137996_R1
