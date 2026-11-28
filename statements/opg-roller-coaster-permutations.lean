import Mathlib

/-!
# Roller Coaster permutations

Source: https://www.openproblemgarden.org/op/roller_coaster_permutations
(Ahmed and Snevily).

For a sequence of distinct numbers, `i + d` (the number of maximal increasing plus maximal
decreasing runs of contiguous entries) equals one plus the number of turning points.
For a permutation `π` of `Fin n` let `t π` be the sum of `i + d` over all subsequences of
length at least three. A Roller Coaster permutation is one that maximises `t`.

Conjecture: for `n ≥ 3`, if `n = 2k` there are exactly four Roller Coaster permutations,
and if `n = 2k + 1` their number is `2 ^ j` for some `j ≤ k + 1`.
-/

namespace OMA.S_opg_roller_coaster_permutations

/-- Number of turning points (local maxima or minima in the interior) of a list. -/
def turns : List ℕ → ℕ
  | a :: b :: c :: t => (if (a < b ∧ c < b) ∨ (b < a ∧ b < c) then 1 else 0) + turns (b :: c :: t)
  | _ => 0

/-- The subsequence of `π` on the index set `S`, read in increasing order of positions. -/
def subseq {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : List ℕ :=
  (S.sort (· ≤ ·)).map fun i => ((π i : Fin n) : ℕ)

/-- `t π`: total number of alternating runs over all subsequences of length at least three. -/
def totalRuns {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => 3 ≤ S.card),
    (1 + turns (subseq π S))

/-- The set of Roller Coaster permutations of `Fin n`. -/
noncomputable def RC (n : ℕ) : Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter fun π => ∀ τ : Equiv.Perm (Fin n), totalRuns τ ≤ totalRuns π

theorem main : ∀ n : ℕ, 3 ≤ n →
    (Even n → (RC n).card = 4) ∧
    (∀ k : ℕ, n = 2 * k + 1 → ∃ j : ℕ, j ≤ k + 1 ∧ (RC n).card = 2 ^ j) := by
  sorry

end OMA.S_opg_roller_coaster_permutations
