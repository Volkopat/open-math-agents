import OMAStatements.S_oeis_a072567
import Mathlib.Data.Nat.Prime.Defs

-- Reduction of the all-order symmetry conjecture. H1 isolates five
-- nontrivial infinite families of projective-plane orders and their
-- principal deletions, including the four-deletion case of
-- Dybizbanski, Dzido and Radziszowski (arXiv:1303.5475, Conjecture 5).
-- H2 retains all other sizes. This is a partial reduction, not a claim
-- that the unrestricted conjecture has been solved.
-- Credit: @LDJAI

namespace OMA.R_oeis_a072567_R1

open OMA.S_oeis_a072567

def H1 : Prop :=
  ∀ p k h : ℕ, p.Prime → 0 < k → h ≤ 4 →
    let n := p^k*p^k+p^k+1-h
    ∃ B : Matrix (Fin n) (Fin n) Bool, B.IsSymm ∧ rectangleFree B ∧
      ∀ A : Matrix (Fin n) (Fin n) Bool, rectangleFree A → numberOfOnes A ≤ numberOfOnes B

def H2 : Prop :=
  ∀ n : ℕ, 0 < n →
    (¬ ∃ p k h : ℕ, p.Prime ∧ 0 < k ∧ h ≤ 4 ∧ n = p^k*p^k+p^k+1-h) →
    ∃ B : Matrix (Fin n) (Fin n) Bool, B.IsSymm ∧ rectangleFree B ∧
      ∀ A : Matrix (Fin n) (Fin n) Bool, rectangleFree A → numberOfOnes A ≤ numberOfOnes B

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a072567.main := by
  intro h1 h2 n hn
  classical
  by_cases h : ∃ p k h : ℕ, p.Prime ∧ 0 < k ∧ h ≤ 4 ∧ n = p^k*p^k+p^k+1-h
  · obtain ⟨p,k,j,hp,hk,hj,rfl⟩ := h
    exact h1 p k j hp hk hj
  · exact h2 n hn h

end OMA.R_oeis_a072567_R1
