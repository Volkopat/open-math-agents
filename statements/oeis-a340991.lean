import Mathlib

/-!
# Kurkov's polynomial recursion for convolutions of prime numbers

The A340991 column k is the k-fold convolution of positive-index
weights. Here weight j is the j-th prime with first weight 2. The zeroth convolution is the unit mass
at zero. The alternative recursion uses indices (m,p) for R(m+1,p+1).
The conjecture relates the two constructions for every positive row.
Kurkov also proposes the same identity for an arbitrary weight sequence.

Source: https://oeis.org/A340991
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a340991
open Finset Polynomial

variable {S : Type} [CommSemiring S]

def convolution (w : ℕ → S) : ℕ → ℕ → S
  | 0, n => if n=0 then 1 else 0
  | k+1, n => ∑ i ∈ range n, convolution w k i * w (n-i)

noncomputable def rowPolynomial (w : ℕ → S) (n : ℕ) : S[X] :=
  ∑ k ∈ range (n+1), C (convolution w k n) * X^k

noncomputable def recursion (w : ℕ → S) : ℕ → ℕ → S[X]
  | 0, p => C (w (p+1))
  | m+1, p => recursion w m (p+1) + X*recursion w m 0*C (w (p+1))

noncomputable def givenWeight : ℕ → ℕ
  | 0 => 0
  | j+1 => Nat.nth Nat.Prime j

theorem main :
    (∀ m : ℕ, rowPolynomial givenWeight (m+1) = X*recursion givenWeight m 0) ∧
    (∀ (S : Type) [CommSemiring S] (w : ℕ → S) (m : ℕ),
      rowPolynomial w (m+1) = X*recursion w m 0) := by
  sorry

end OMA.S_oeis_a340991
