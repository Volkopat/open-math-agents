import OMAStatements.S_oeis_a374613

-- Reduction oeis-a374613.R1 of A374613: Prime numbers p with the property that neither of 2*(p+next prime to p)+/-1 is prime.
-- Credit: @m-miyawaki-m
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- H1 is the mod-15, k=2 instance of Erdős 427's open "Shiu's theorem" task
-- (Erdos427.erdos_427.variants.shiu on this site, itself split there into an open density
-- lemma R1.H1 and an already-proved combinatorial lemma R1.H2): infinitely many pairs of
-- consecutive primes both lying in the residue class 1 mod 15. It is restated here using only
-- Mathlib (a reduction may only import Mathlib besides its target) rather than imported from
-- FormalConjectures, but it is the same open claim, at the same difficulty, as that site task.
-- H2 is elementary (provable without H1): given one such pair of indices, the two primes
-- obtained have (2*(p+q)-1) divisible by 3 and (2*(p+q)+1) divisible by 5, hence both nonprime.

namespace OMA.R_oeis_a374613_R1

/-- H1 (open, same difficulty as Erdos427.erdos_427.variants.shiu.R1.H1/H2 combined, specialized
to k = 2, a = 1, q = 15): infinitely many indices m such that the two consecutive primes of index
m and m + 1 are both congruent to 1 mod 15. -/
def H1 : Prop :=
  { m : ℕ | ∀ p ∈ (Finset.Ico m (m + 2)).image (Nat.nth Nat.Prime), p ≡ 1 [MOD 15] }.Infinite

/-- H2 (elementary): given such an index m, the two consecutive primes `Nat.nth Nat.Prime m` and
`Nat.nth Nat.Prime (m + 1)` witness the A374613 property. -/
def H2 : Prop :=
  ∀ m : ℕ, (∀ p ∈ (Finset.Ico m (m + 2)).image (Nat.nth Nat.Prime), p ≡ 1 [MOD 15]) →
    ∃ p : ℕ, p = Nat.nth Nat.Prime m ∧ p.Prime ∧ ∃ q : ℕ,
      q.Prime ∧ p < q ∧ (∀ r : ℕ, p < r → r < q → ¬ r.Prime) ∧
      ¬ (2 * (p + q) - 1).Prime ∧ ¬ (2 * (p + q) + 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a374613.main := by
  intro h1 h2
  have hfinj : Function.Injective (Nat.nth Nat.Prime) :=
    Nat.nth_injective Nat.infinite_setOfPred_prime
  have hsub :
      (Nat.nth Nat.Prime) '' { m : ℕ | ∀ p ∈ (Finset.Ico m (m + 2)).image (Nat.nth Nat.Prime), p ≡ 1 [MOD 15] } ⊆
        { p : ℕ | p.Prime ∧ ∃ q : ℕ,
          q.Prime ∧ p < q ∧ (∀ r : ℕ, p < r → r < q → ¬ r.Prime) ∧
          ¬ (2 * (p + q) - 1).Prime ∧ ¬ (2 * (p + q) + 1).Prime } := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨p, hpeq, hp, q, hq, hpq, hgap, hnp1, hnp2⟩ := h2 m hm
    subst hpeq
    exact ⟨hp, q, hq, hpq, hgap, hnp1, hnp2⟩
  exact Set.Infinite.mono hsub ((Set.infinite_image_iff hfinj.injOn).mpr h1)

end OMA.R_oeis_a374613_R1
