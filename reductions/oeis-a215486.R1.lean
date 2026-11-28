import OMAStatements.S_oeis_a215486

-- Reduction oeis-a215486.R1 of A215486: n - 1 mod phi(n), where phi(n) is Euler's totient function.
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a215486_R1

/-- Odd composite `n` that is not squarefree: `φ(n) ∤ n - 1`. -/
def H1 : Prop :=
  ∀ n : ℕ, 3 ≤ n → Odd n → ¬ n.Prime → ¬ Squarefree n → (n - 1) % Nat.totient n ≠ 0

/-- Odd squarefree composite `n`: `φ(n) ∤ n - 1` (the core of Lehmer's totient problem). -/
def H2 : Prop :=
  ∀ n : ℕ, 3 ≤ n → Odd n → ¬ n.Prime → Squarefree n → (n - 1) % Nat.totient n ≠ 0

/-- `n = 1` and primes satisfy `φ(n) ∣ n - 1`; an even composite `n ≥ 4` does not, because `φ(n)` is
even and `n - 1` is odd. Odd composites are split into non-squarefree (`H1`) and squarefree (`H2`). -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a215486.main := by
  intro h1 h2 n hn
  unfold OMA.S_oeis_a215486.a
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h2n : 2 ≤ n := by omega
    have hn2 : n ≠ 2 := fun e => hc.2 (e ▸ Nat.prime_two)
    by_cases he : Even n
    · obtain ⟨t, ht⟩ := Nat.totient_even (by omega : 2 < n)
      obtain ⟨s, hs⟩ := he
      have hd := Nat.dvd_of_mod_eq_zero h
      rw [ht] at hd
      have h2d : 2 ∣ n - 1 := Nat.dvd_trans (Dvd.intro t (by ring)) hd
      omega
    · have ho : Odd n := Nat.not_even_iff_odd.mp he
      by_cases hsq : Squarefree n
      · exact h2 n (by omega) ho hc.2 hsq h
      · exact h1 n (by omega) ho hc.2 hsq h
  · rintro (rfl | hp)
    · simp
    · rw [Nat.totient_prime hp, Nat.mod_self]

end OMA.R_oeis_a215486_R1
