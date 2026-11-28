import Mathlib

/-!
# A matrix representation of the symmetric group with the Markov trace as character

Source: https://mathoverflow.net/questions/238897
Asked by MathOverflow user Everett You.

For `g` in the symmetric group `S_N` define the Markov trace `tr_k g = k ^ (number of cycles
of g)`, fixed points counted as cycles. For a positive integer `k` this is the character of
the permutation representation on the `N`-fold tensor power of a `k`-dimensional space. The
question considers an arbitrary positive real `k` and asks: is there a matrix representation
`D_k` of `S_N` whose matrix trace equals the Markov trace, `Tr D_k(g) = tr_k g`?
(The follow-up request for an explicit construction is not formalized.)

Translation choices.
* `S_N` is `Equiv.Perm (Fin N)`. The number of cycles of `g` (fixed points included) is
  the number of parts of the cycle-type partition `g.partition` of `N`.
* A matrix representation is a group homomorphism `D` from `S_N` to the group of invertible
  complex `d × d` matrices, for some dimension `d`; its trace is `Matrix.trace`.
* `main` is the affirmative answer: for every `N` and every real `k > 0` such a
  representation exists.
-/

namespace OMA.S_mo_238897

/-- The number of cycles of a permutation, fixed points included. -/
def numCycles {N : ℕ} (g : Equiv.Perm (Fin N)) : ℕ := g.partition.parts.card

theorem main :
    ∀ N : ℕ, ∀ k : ℝ, 0 < k →
      ∃ d : ℕ, ∃ D : Equiv.Perm (Fin N) →* Matrix.GeneralLinearGroup (Fin d) ℂ,
        ∀ g : Equiv.Perm (Fin N),
          Matrix.trace (D g : Matrix (Fin d) (Fin d) ℂ) = (k : ℂ) ^ numCycles g := by
  sorry

end OMA.S_mo_238897
