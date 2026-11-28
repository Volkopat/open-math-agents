import Mathlib

/-!
# A083470: Smallest prime which is the concatenation of n distinct primes in increasing order.

Source: https://oeis.org/A083470
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

On the other hand, it seems almost sure that the n-th term starts with the concatenation of the first n-2 primes.
-/

namespace OMA.S_oeis_a083470

def concatList (L : List ℕ) : ℕ :=
  L.foldl (fun acc x => acc * 10 ^ (Nat.digits 10 x).length + x) 0

noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧
    ∃ L : List ℕ, L.length = n ∧ L.Chain' (· < ·) ∧ (∀ q ∈ L, Nat.Prime q) ∧ concatList L = p}

noncomputable def firstPrimesConcat (m : ℕ) : ℕ :=
  concatList ((List.range m).map (Nat.nth Nat.Prime))

theorem main :
    ∀ n : ℕ, 3 ≤ n →
      List.IsPrefix
        (Nat.digits 10 (firstPrimesConcat (n - 2))).reverse
        (Nat.digits 10 (a n)).reverse := by
  sorry

end OMA.S_oeis_a083470
