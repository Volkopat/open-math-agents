import Mathlib

/-! Source: https://mathoverflow.net/questions/181224
Sequence: https://oeis.org/A246536 -/

open scoped BigOperators

namespace OMA.S_mo_181224

/-- The pair of successive letters at position i in a nonempty word. -/
def adjacentPair {n k : ℕ} (w : Fin (k + 1) → Fin n) (i : Fin k) :
    Fin n × Fin n := (w i.castSucc, w i.succ)

/-- The empty word plus the words with no repeated adjacent pair.
Every repeat of a longer substring would repeat its first pair.
There are n² possible pairs, so a nonempty word has at most n² + 1 letters. -/
noncomputable def wordCount (n : ℕ) : ℕ := by
  classical
  exact 1 + ∑ k ∈ Finset.range (n * n + 1),
    ((Finset.univ : Finset (Fin (k + 1) → Fin n)).filter
      fun w => Function.Injective (adjacentPair w)).card

/-- The integer adjacency matrix of a set of ordered letter pairs. -/
def pairAdjacency {n : ℕ} (E : Finset (Fin n × Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if (i, j) ∈ E then 1 else 0

/-- An exact inclusion–exclusion formula for the number of words
with no repeated substring of length greater than one. -/
theorem main :
    ∀ n : ℕ, (wordCount n : ℤ) = 1 +
      ∑ T ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset,
        ∑ D ∈ T.powerset, (-1 : ℤ) ^ D.card *
          ∑ i : Fin n, ∑ j : Fin n, ((pairAdjacency (T \ D)) ^ T.card) i j := by
  sorry

end OMA.S_mo_181224
