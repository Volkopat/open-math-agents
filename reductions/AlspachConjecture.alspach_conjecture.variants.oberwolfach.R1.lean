import FormalConjectures.Wikipedia.AlspachConjecture
import Mathlib

-- Reduction AlspachConjecture.alspach_conjecture.variants.oberwolfach.R1 of the Oberwolfach
-- problem for odd n: for a 2-regular graph F on n vertices other than the two exceptions,
-- K_n decomposes into (n - 1)/2 spanning copies of F.
-- Credit: @marcusbuffett
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- This is a classical slice, not progress on the problem itself. H1 is Walecki's theorem
-- (1892): for odd n at least 3, K_n is the edge-disjoint union of (n - 1)/2 Hamilton cycles,
-- which settles the Oberwolfach problem when F is a single n-cycle. Walecki's construction
-- puts one vertex at infinity, runs the zigzag 0, 1, -1, 2, -2, ..., m on Z/2m and rotates it;
-- the i-th rotation takes exactly the finite edges whose endpoint sum is 2i or 2i + 1 mod 2m.
-- H2, the case where F has at least two components, carries the whole open difficulty.

namespace OMA.R_AlspachConjecture_alspach_conjecture_variants_oberwolfach_R1

open SimpleGraph AlspachConjecture

/-- Walecki's theorem: for odd `n ≥ 3`, `K_n` decomposes into `(n - 1)/2` Hamilton cycles. -/
def H1 : Prop :=
  ∀ (n : ℕ), Odd n → 3 ≤ n →
    ∃ D : Fin ((n - 1) / 2) → SimpleGraph (Fin n),
      (∀ i, Nonempty (D i ≃g cycleGraph n)) ∧
      ∀ u v, (completeGraph (Fin n)).Adj u v ↔ ∃! i, (D i).Adj u v

/-- The Oberwolfach problem for odd `n` when the 2-factor `F` is not a single `n`-cycle (open). -/
def H2 : Prop :=
  ∀ (n : ℕ), Odd n → 3 ≤ n →
    ∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj], (∀ v, F.degree v = 2) →
    IsEmpty (F ≃g oberwolfachException9) → IsEmpty (F ≃g oberwolfachException11) →
    IsEmpty (F ≃g cycleGraph n) →
    ∃ D : Fin ((n - 1) / 2) → SimpleGraph (Fin n),
      (∀ i, Nonempty (D i ≃g F)) ∧
      ∀ u v, (completeGraph (Fin n)).Adj u v ↔ ∃! i, (D i).Adj u v

theorem main : H1 → H2 → type_of% @AlspachConjecture.alspach_conjecture.variants.oberwolfach := by
  intro h1 h2 n hn h3 F _ hdeg h9 h11
  by_cases hc : Nonempty (F ≃g cycleGraph n)
  · obtain ⟨e⟩ := hc
    obtain ⟨D, hD, hdec⟩ := h1 n hn h3
    refine ⟨D, fun i => ?_, hdec⟩
    obtain ⟨f⟩ := hD i
    exact ⟨f.trans e.symm⟩
  · exact h2 n hn h3 F hdeg h9 h11 (not_nonempty_iff.mp hc)

end OMA.R_AlspachConjecture_alspach_conjecture_variants_oberwolfach_R1
