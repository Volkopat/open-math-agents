import Mathlib

/-!
# Wide partition conjecture

Source: https://www.openproblemgarden.org/op/wide_partition_conjecture
(T. Y. Chow, B. D. Taylor; see Chow–Fan–Goemans–Vondrák, *Wide partitions, Latin tableaux, and
Rota's basis conjecture*)
Credit: @ishaanzee

**Conjecture.** An integer partition is wide if and only if it is Latin.

An integer partition `λ` is wide if `μ ≥ μ'` for every subpartition `μ` of `λ`. (Here `μ'` denotes
the conjugate of `μ`, `≥` denotes dominance or majorization order, and a subpartition of `λ` is a
submultiset of the parts of `λ`.) An integer partition `λ` is Latin if there exists a tableau `T`
of shape `λ` such that for every `i`, the `i`th row of `T` contains a permutation of
`{1, 2, …, λᵢ}`, and such that every column of `T` contains distinct integers. (Latin implies
wide; the converse is open.)

Formalization:
* A partition is a Mathlib `Nat.Partition n`; its parts form a multiset of positive integers, and
  `sortedParts` lists them in weakly decreasing order `λ₁ ≥ λ₂ ≥ ⋯`.
* The conjugate of `μ` has parts `μ'ⱼ = #{i | μᵢ ≥ j}` for `j = 1, …, μ₁`.
* Dominance `μ ≥ ν` (for partitions of the same number) means `ν₁ + ⋯ + νₖ ≤ μ₁ + ⋯ + μₖ` for
  every `k` (parts listed in decreasing order, missing parts counted as `0`, which `List.take`
  does automatically).
* A tableau of shape `λ` is a filling `T i j` of the cells `(i, j)` with `j < λᵢ` (rows indexed
  from `0`). Row `i` contains a permutation of `{1, …, λᵢ}` iff `j ↦ T i j` maps the `λᵢ` cells of
  the row injectively into `{1, …, λᵢ}`; columns contain distinct integers iff two different cells
  in the same column have different entries.
-/

namespace OMA.S_opg_wide_partition_conjecture

/-- The parts of a multiset in weakly decreasing order. -/
def sortedParts (m : Multiset ℕ) : List ℕ := m.sort (· ≥ ·)

/-- The conjugate partition: its `j`-th part (from `j = 1`) is the number of parts that are at
least `j`. -/
def conjugate (m : Multiset ℕ) : List ℕ :=
  (List.range m.sup).map fun j => m.countP fun p => j < p

/-- Dominance order on decreasingly sorted lists of parts: `μ ≥ ν`. -/
def Dominates (μ ν : List ℕ) : Prop := ∀ k : ℕ, (ν.take k).sum ≤ (μ.take k).sum

/-- `λ` is wide: every subpartition dominates its conjugate. -/
def IsWide (lam : Multiset ℕ) : Prop := ∀ μ ≤ lam, Dominates (sortedParts μ) (conjugate μ)

/-- The length `λᵢ` of row `i` (rows indexed from `0`; `0` beyond the last row). -/
def rowLen (lam : Multiset ℕ) (i : ℕ) : ℕ := (sortedParts lam).getD i 0

/-- `λ` is Latin: some tableau of shape `λ` has a permutation of `{1, …, λᵢ}` in each row `i` and
distinct entries in each column. -/
def IsLatin (lam : Multiset ℕ) : Prop :=
  ∃ T : ℕ → ℕ → ℕ,
    (∀ i : ℕ, (∀ j < rowLen lam i, T i j ∈ Finset.Icc 1 (rowLen lam i)) ∧
      Set.InjOn (T i) (Set.Iio (rowLen lam i))) ∧
    ∀ i i' j : ℕ, i ≠ i' → j < rowLen lam i → j < rowLen lam i' → T i j ≠ T i' j

/-- **Wide partition conjecture** (Chow–Taylor): a partition is wide if and only if it is Latin. -/
theorem main : ∀ (n : ℕ) (lam : Nat.Partition n), IsWide lam.parts ↔ IsLatin lam.parts := by
  sorry

end OMA.S_opg_wide_partition_conjecture
