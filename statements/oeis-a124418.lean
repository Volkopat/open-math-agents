import Mathlib

namespace OMA.S_oeis_a124418

open BigOperators

/-- Predicate that `P` is a set partition of a finite set `S`:
all blocks are nonempty, pairwise disjoint, and their union is `S`. -/
def isSetPartition {α : Type*} [DecidableEq α] (S : Finset α) (P : Finset (Finset α)) : Prop :=
  (∀ B ∈ P, B.Nonempty) ∧
  (∀ B₁ ∈ P, ∀ B₂ ∈ P, B₁ ≠ B₂ → Disjoint B₁ B₂) ∧
  P.biUnion id = S

instance {α : Type*} [DecidableEq α] (S : Finset α) (P : Finset (Finset α)) :
    Decidable (isSetPartition S P) := by
  unfold isSetPartition
  infer_instance

/-- The finset of all set partitions of `S`. -/
def setPartitions {α : Type*} [DecidableEq α] (S : Finset α) : Finset (Finset (Finset α)) :=
  S.powerset.powerset.filter (isSetPartition S)

/-- A block of `{1, ..., n}` is mixed if it contains both an even and an odd integer. -/
def isMixedBlock (B : Finset ℕ) : Prop :=
  (∃ x ∈ B, Even x) ∧ (∃ y ∈ B, Odd y)

instance (B : Finset ℕ) : Decidable (isMixedBlock B) := by
  unfold isMixedBlock
  infer_instance

/-- OEIS A124418: `T(n, k)` is the number of set partitions of `{1, 2, ..., n}`
having exactly `k` blocks that contain both odd and even elements. -/
def a124418 (n k : ℕ) : ℕ :=
  ((setPartitions (Finset.Icc 1 n)).filter fun P =>
    (P.filter isMixedBlock).card = k).card

/-- Stirling numbers of the second kind `S2(n, k)` via the standard recurrence. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- OEIS A049020: `A049020(n, k) = ∑_{i=0}^n S2(n, i) * C(i, k)`. -/
def a049020 (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), stirling2 n i * Nat.choose i k

/-- Conjecture on OEIS A124418:
`T(n, k) = k! * A049020(⌊n / 2⌋, k) * A049020(⌊(n + 1) / 2⌋, k)` for all `n, k : ℕ`. -/
theorem main :
    ∀ n k : ℕ,
      a124418 n k = Nat.factorial k * a049020 (n / 2) k * a049020 ((n + 1) / 2) k := by
  sorry

end OMA.S_oeis_a124418
