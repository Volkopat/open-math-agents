import OMAStatements.S_oeis_a055030

-- Reduction oeis-a055030.R1 of A055030: (Sum(m^(p-1),m=1..p-1)+1)/p as p runs through the primes.
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a055030_R1

/-- Composite `n` that is not squarefree never satisfies Giuga's divisibility. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ¬ n.Prime → ¬ Squarefree n → ¬ n ∣ ∑ m ∈ Finset.Icc 1 (n - 1), m ^ (n - 1) + 1

/-- Squarefree composite `n` never satisfies Giuga's divisibility (the core of Giuga's conjecture). -/
def H2 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ¬ n.Prime → Squarefree n → ¬ n ∣ ∑ m ∈ Finset.Icc 1 (n - 1), m ^ (n - 1) + 1

/-- For a prime `p`, Fermat gives `m^(p-1) ≡ 1` for `1 ≤ m ≤ p - 1`, so the sum is `p - 1 ≡ -1`. -/
theorem prime_dvd (p : ℕ) (hp : p.Prime) :
    p ∣ ∑ m ∈ Finset.Icc 1 (p - 1), m ^ (p - 1) + 1 := by
  have := Fact.mk hp
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ZMod p))]
  · simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    have h1 : 1 ≤ p := hp.one_le
    rw [show p - 1 + 1 - 1 = p - 1 by omega]
    rw [← Nat.cast_one (R := ZMod p), ← Nat.cast_add, Nat.sub_add_cancel h1, ZMod.natCast_self]
  · intro m hm
    rw [Finset.mem_Icc] at hm
    apply ZMod.pow_card_sub_one_eq_one
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact absurd (Nat.le_of_dvd (by omega) h0) (by omega)

/-- The reverse implication (`n = 1` or prime) is proved here by Fermat's little theorem; the open
forward implication is split into non-squarefree composites (`H1`) and squarefree ones (`H2`). -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a055030.main := by
  intro h1 h2 n hn
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have h2n : 2 ≤ n := by omega
    by_cases hsq : Squarefree n
    · exact h2 n h2n hc.2 hsq h
    · exact h1 n h2n hc.2 hsq h
  · rintro (rfl | hp)
    · exact one_dvd _
    · exact prime_dvd n hp

end OMA.R_oeis_a055030_R1
