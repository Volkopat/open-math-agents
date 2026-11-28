import Mathlib

namespace OMA.S_arxiv_2607_15305

/-- The Carlitz module action of `T^k` on a polynomial `x ∈ K[T]` over a finite field of size `q`:
`ρ_1(x) = x` and `ρ_{T^{k+1}}(x) = T * ρ_{T^k}(x) + (ρ_{T^k}(x))^q`. -/
noncomputable def carlitzPow {K : Type*} [Semiring K] (q : ℕ) :
    ℕ → Polynomial K → Polynomial K
  | 0, x => x
  | k + 1, x => Polynomial.X * carlitzPow q k x + (carlitzPow q k x) ^ q

/-- The Carlitz module action `ρ_P(x) = ∑_k P_k · ρ_{T^k}(x)` of a polynomial `P ∈ K[T]` on `x`. -/
noncomputable def carlitzEval {K : Type*} [Semiring K] (q : ℕ)
    (P x : Polynomial K) : Polynomial K :=
  ∑ k ∈ Finset.range (P.natDegree + 1), Polynomial.C (P.coeff k) * carlitzPow q k x

/-- Thakur's conjecture on Carlitz–Wieferich primes (2015; disproved in arXiv:2607.15305):
over any finite field `K` of odd prime characteristic `p`, every monic irreducible polynomial
`P ∈ K[T]` satisfying `ρ_P(1) ≡ 1 (mod P^2)` has degree divisible by `p`. -/
theorem main :
    ∀ (K : Type) [Field K] [Fintype K] (p : ℕ),
      Nat.Prime p → p ≠ 2 → CharP K p →
      ∀ (P : Polynomial K),
        P.Monic → Irreducible P →
        P ^ 2 ∣ (carlitzEval (Fintype.card K) P 1 - 1) →
        p ∣ P.natDegree := by
  sorry

end OMA.S_arxiv_2607_15305
