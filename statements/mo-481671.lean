import Mathlib

/-!
# Covering the majority multigraph of permutations by two permutations

Source: Karo, MathOverflow 481671, November 2, 2024, CC BY-SA 4.0.
https://mathoverflow.net/questions/481671/realized-graph-of-majority-of-permutations
Cross-post: https://math.stackexchange.com/questions/4940345

A ballot maps each object to its position in a one-line permutation. A list
retains the multiplicity of each ballot. For distinct objects a pair gets an
arc when at least half the ballots order it that way, and a second arc when
all ballots do. Multigraph containment compares the multiplicities pointwise.
-/

namespace OMA.S_mo_481671

def multiplicity {n : ℕ} (ballots : List (Equiv.Perm (Fin n))) (x y : Fin n) : ℕ :=
  if x = y then 0 else
    let count := ballots.countP (fun p => decide (p x < p y))
    (if ballots.length ≤ 2 * count then 1 else 0) +
      (if count = ballots.length then 1 else 0)

theorem main : ∀ n : ℕ, 0 < n → ∀ ballots : List (Equiv.Perm (Fin n)), ballots ≠ [] →
    ∃ p q : Equiv.Perm (Fin n), ∀ x y : Fin n,
      multiplicity ballots x y ≤ multiplicity [p, q] x y := by
  sorry

end OMA.S_mo_481671
