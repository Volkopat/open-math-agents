import Mathlib

/-!
# A002106: Number of transitive permutation groups of degree n.

Source: https://oeis.org/A002106
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

Reading decisions (see PLAN note):
* The assertible content of the page is the sequence DEFINITION — "Number of transitive
  permutation groups of degree n", counted up to conjugacy in S_n (matching the page's GAP
  program `AllTransitiveGroups(NrMovedPoints, n)`) — together with the listed values.
* The COMMENTS conjecture ("number of Galois groups for irreducible polynomials of order n")
  is explicitly a conjecture on the page, equivalent to the inverse Galois problem; it has
  no assertible precise quantifiers, so it is NOT part of `main`.
* `main` states the first 12 values a(1)..a(12) exactly as listed on the page
  (offset 1): 1, 1, 2, 5, 5, 16, 7, 50, 34, 45, 8, 301.
-/

namespace OMA.S_oeis_a002106

/-- A subgroup of the symmetric group on `Fin n` acts transitively on `Fin n`. -/
def TransitiveSubgroup (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∀ x y : Fin n, ∃ h ∈ H, h x = y

noncomputable instance (n : ℕ) : DecidablePred (TransitiveSubgroup n) :=
  Classical.decPred (TransitiveSubgroup n)

abbrev T (n : ℕ) := {H : Subgroup (Equiv.Perm (Fin n)) // TransitiveSubgroup n H}

/-- Conjugacy of transitive subgroups of `S_n` by an element of `S_n`. -/
def conjRel (n : ℕ) (p q : T n) : Prop :=
  ∃ g : Equiv.Perm (Fin n), Subgroup.map (MulAut.conj g) p.1 = q.1

/-- Conjugacy as a setoid on the transitive subgroups of `S_n`. -/
def conjSetoid (n : ℕ) : Setoid (T n) where
  r := conjRel n
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact ⟨1, by ext x; simp [Subgroup.mem_map]⟩
    · intro p q ⟨g, hg⟩
      exact ⟨g⁻¹, by
        rw [← hg]
        ext x
        simp [Subgroup.mem_map, MulAut.conj_apply, mul_assoc, inv_mul_cancel_left, mul_one]⟩
    · intro p q l ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩
      exact ⟨g₂ * g₁, by
        rw [← hg₂, ← hg₁, Subgroup.map_map]
        congr 1⟩

noncomputable instance (n : ℕ) :
    DecidableRel (@Setoid.r (T n) (conjSetoid n)) :=
  Classical.decRel _

/-- The number of conjugacy classes (under `S_n`) of transitive subgroups of `S_n`.
This is the precise meaning of "number of transitive permutation groups of degree n". -/
noncomputable def a (n : ℕ) : ℕ :=
  Fintype.card (Quotient (conjSetoid n))

theorem main :
    a 1 = 1 ∧ a 2 = 1 ∧ a 3 = 2 ∧ a 4 = 5 ∧ a 5 = 5 ∧ a 6 = 16 ∧
      a 7 = 7 ∧ a 8 = 50 ∧ a 9 = 34 ∧ a 10 = 45 ∧ a 11 = 8 ∧ a 12 = 301 := by
  sorry

end OMA.S_oeis_a002106
