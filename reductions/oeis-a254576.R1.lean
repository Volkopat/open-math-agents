import OMAStatements.S_oeis_a254576

-- Reduction oeis-a254576.R1 of A254576: Primes p such that phi(p-2) divides p-1 where phi is Euler's totient function (A000010).
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a254576_R1

/-- No prime `p` has `p - 1 = 3 φ(p - 2)`. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p - 1 ≠ Nat.totient (p - 2) * 3

/-- No prime `p` has `p - 1 = c φ(p - 2)` with `c ≥ 4`. -/
def H2 : Prop :=
  ∀ p c : ℕ, p.Prime → 4 ≤ c → p - 1 ≠ Nat.totient (p - 2) * c

/-- Write `p - 1 = c φ(p - 2)`. Here `c = 0` and `c = 1` are impossible (`φ(m) ≤ m`), `c = 2` is the
conclusion, and the remaining quotients `c = 3` and `c ≥ 4` are `H1` and `H2`. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a254576.main := by
  intro h1 h2 p hp
  have hp2 := hp.two_le
  constructor
  · rintro ⟨c, hc⟩
    have hle : Nat.totient (p - 2) ≤ p - 2 := Nat.totient_le _
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ 4 ≤ c by omega) with rfl | rfl | rfl | rfl | h4
    · omega
    · omega
    · omega
    · exact absurd hc (h1 p hp)
    · exact absurd hc (h2 p c hp h4)
  · intro h
    exact ⟨2, by omega⟩

end OMA.R_oeis_a254576_R1
