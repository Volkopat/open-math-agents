import OMAStatements.S_oeis_a092938

-- Reduction oeis-a092938.R1 of A092938: a(n) = least prime p such that 2*prime(n) - p is prime.
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a092938_R1

/-- Primes `q ≡ 1 (mod 6)`: some prime `p < q` has `2q - p` prime. -/
def H1 : Prop :=
  ∀ q : ℕ, q.Prime → q % 6 = 1 → ∃ p : ℕ, p.Prime ∧ p < q ∧ (2 * q - p).Prime

/-- Primes `q ≡ 5 (mod 6)`: some prime `p < q` has `2q - p` prime. -/
def H2 : Prop :=
  ∀ q : ℕ, q.Prime → q % 6 = 5 → ∃ p : ℕ, p.Prime ∧ p < q ∧ (2 * q - p).Prime

/-- `q = 2, 3` are checked directly; every prime `q ≥ 5` is `1` or `5 (mod 6)`, the cases `H1`, `H2`. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a092938.main := by
  intro h1 h2 q hq
  constructor
  · intro h
    by_contra hq3
    have h2q : ¬ 2 ∣ q := fun hd => by
      rcases hq.eq_one_or_self_of_dvd 2 hd with h | h <;> omega
    have h3q : ¬ 3 ∣ q := fun hd => by
      rcases hq.eq_one_or_self_of_dvd 3 hd with h | h <;> omega
    have hmod : q % 6 = 1 ∨ q % 6 = 5 := by omega
    rcases hmod with hm | hm
    · obtain ⟨p, hp, hpq, hr⟩ := h1 q hq hm
      exact h p hp hpq hr
    · obtain ⟨p, hp, hpq, hr⟩ := h2 q hq hm
      exact h p hp hpq hr
  · intro hq3 p hp hpq
    have h2 := hp.two_le
    have hq2 : q = 3 := by
      have := hq.two_le
      omega
    subst hq2
    have : p = 2 := by omega
    subst this
    decide

end OMA.R_oeis_a092938_R1
