import OMAStatements.S_oeis_a235363

-- Reduction oeis-a235363.R1 of A235363: (1 + Sum_{k=1..m-1} k^(m-1)) (mod m), for m = 1, 3, 5, 7, 9, ...
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a235363_R1

/-- Odd composite `m = 2n + 1` that is not squarefree fails the Agoh–Giuga congruence. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ¬ (2 * n + 1).Prime → ¬ Squarefree (2 * n + 1) →
    (1 + ∑ k ∈ Finset.Icc 1 (2 * n), k ^ (2 * n)) % (2 * n + 1) ≠ 0

/-- Odd squarefree composite `m = 2n + 1` fails the Agoh–Giuga congruence. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ¬ (2 * n + 1).Prime → Squarefree (2 * n + 1) →
    (1 + ∑ k ∈ Finset.Icc 1 (2 * n), k ^ (2 * n)) % (2 * n + 1) ≠ 0

/-- For a prime `p`, Fermat gives `k^(p-1) ≡ 1` for `1 ≤ k ≤ p - 1`, so the sum is `p - 1 ≡ -1`. -/
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

/-- `m = 1` and odd primes satisfy the congruence (Fermat); odd composites are split into
non-squarefree (`H1`) and squarefree (`H2`). -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a235363.main := by
  intro h1 h2 n
  unfold OMA.S_oeis_a235363.a
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have hn : 1 ≤ n := by omega
    by_cases hsq : Squarefree (2 * n + 1)
    · exact h2 n hn hc.2 hsq h
    · exact h1 n hn hc.2 hsq h
  · rintro (h | hp)
    · have : n = 0 := by omega
      subst this
      simp
    · have hd := prime_dvd (2 * n + 1) hp
      rw [show 2 * n + 1 - 1 = 2 * n by omega] at hd
      exact Nat.mod_eq_zero_of_dvd (by rw [add_comm 1]; exact hd)

end OMA.R_oeis_a235363_R1
