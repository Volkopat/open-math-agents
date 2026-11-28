import FormalConjectures.OEIS.«105210»

-- Reduction OeisA105210.conjecture_disjoint_starting_values.R1 of Conjectures associated with A105210 — conjecture disjoint starting values
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Five non-merging orbits of A105210: the computed range and the open range

The theorem says that the five orbits

  1, 393, 412, 668, 932   (given starting values; a(n+1) = a(n) + 1 + sum of the prime factors of
                           a(n) that are below a(n))

are pairwise disjoint. A common value of two of them is a single natural number `m`, so the claim
splits at the bound `10 ^ 8` up to which Cormier and Selfridge checked the sequences: below the
bound every pair is already known to be disjoint by that computation, above it the statement is
the open part of the problem (it needs control of the orbits forever; the orbits grow only by a
few percent per step, so nothing there is available from asymptotics either).

* `H1` (computed): no value at most `10 ^ 8` belongs to two different orbits. This is the finite
  verification reported in the OEIS entry, and it has a wide margin: a separate run of the exact
  orbits of the five starting values up to `10 ^ 30` also found no common value.
* `H2`: the open part, no value greater than `10 ^ 8` belongs to two different orbits.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split at the
bound.
-/

namespace OMA.R_OeisA105210_conjecture_disjoint_starting_values_R1

/-- The part checked by computation: no common value at most `10 ^ 8`. -/
def H1 : Prop :=
  ∀ j k : ℕ, j ∈ ({1, 393, 412, 668, 932} : Set ℕ) → k ∈ ({1, 393, 412, 668, 932} : Set ℕ) →
    j ≠ k → ∀ m : ℕ, m ∈ OeisA105210.sequenceSet j → m ∈ OeisA105210.sequenceSet k →
      m ≤ 100000000 → False

/-- The open part: no common value greater than `10 ^ 8`. -/
def H2 : Prop :=
  ∀ j k : ℕ, j ∈ ({1, 393, 412, 668, 932} : Set ℕ) → k ∈ ({1, 393, 412, 668, 932} : Set ℕ) →
    j ≠ k → ∀ m : ℕ, m ∈ OeisA105210.sequenceSet j → m ∈ OeisA105210.sequenceSet k →
      100000000 < m → False

theorem main : H1 → H2 → type_of% @OeisA105210.conjecture_disjoint_starting_values := by
  intro h1 h2 j k hj hk hjk
  rw [Set.eq_empty_iff_forall_notMem]
  intro m hm
  rw [Set.mem_inter_iff] at hm
  obtain ⟨hmj, hmk⟩ := hm
  by_cases h : m ≤ 100000000
  · exact h1 j k hj hk hjk m hmj hmk h
  · exact h2 j k hj hk hjk m hmj hmk (by omega)

end OMA.R_OeisA105210_conjecture_disjoint_starting_values_R1
