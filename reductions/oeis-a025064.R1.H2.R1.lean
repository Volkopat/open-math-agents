import OMAReductions.R_oeis_a025064_R1
import Mathlib.Algebra.Squarefree.Basic

namespace OMA.R_oeis_a025064_R1_H2_R1

open OMA.S_oeis_a025064

-- Liang, On the Diophantine equation ab + bc + ca = N and Euler's idoneal numbers,
-- Proposition 2 and the even part of Proposition 3.
def H1 : Prop :=
  ∀ n : ℕ, 462 < n → n % 4 = 2 → Squarefree n → Representable n

def H2 : Prop :=
  ∀ n : ℕ, 1848 < n → n % 2 = 0 → ¬ Representable n →
    (n % 4 = 2 ∧ Squarefree n) ∨
      ∃ q : ℕ, n = 4 * q ∧ q % 4 = 2 ∧ Squarefree q

theorem main : H1 → H2 → OMA.R_oeis_a025064_R1.H2 := by
  intro squarefree_tail classify n hn he
  by_contra h
  rcases classify n hn he h with ⟨hmod, hsf⟩ | ⟨q, hq, hmod, hsf⟩
  · exact h (squarefree_tail n (by omega) hmod hsf)
  · obtain ⟨a, b, c, ha, hab, hbc, hrep⟩ :=
      squarefree_tail q (by omega) hmod hsf
    apply h
    refine ⟨2 * a, 2 * b, 2 * c, by omega, by omega, by omega, ?_⟩
    rw [hq, hrep]
    ring

end OMA.R_oeis_a025064_R1_H2_R1
