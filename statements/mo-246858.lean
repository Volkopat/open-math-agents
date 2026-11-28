import Mathlib

/-!
# First singular time of an integrated product of matrix exponentials

Source: nadia, https://mathoverflow.net/questions/246858 (CC BY-SA 3.0).
Credit: @connoranderson. The upper triangular block-exponential method for
exponential integrals is classical (C. F. Van Loan, 1978). Here one real
matrix exponential of order 2n yields the entire integral at every time,
including when the associated Sylvester map is singular. Its upper-right
minor gives a scalar root test. The integral is nonsingular on some positive
initial interval, and a first positive singular time exists whenever there
is any positive singular time.

Explicit noncommuting traceless nilpotent 6-by-6 examples with identical
individual characteristic polynomials have first singular time one or no
positive singular time at all.
-/

namespace OMA.S_mo_246858
open Matrix Set MeasureTheory
open scoped Matrix.Norms.Operator
abbrev Mat (I : Type) := Matrix I I ℝ
noncomputable def flow {I : Type} [Fintype I] [DecidableEq I] (A : Mat I) (t : ℝ) : Mat I :=
  NormedSpace.exp (t • A)
noncomputable def integrated {I : Type} [Fintype I] [DecidableEq I] (A B : Mat I) (T : ℝ) : Mat I :=
  ∫ t in (0:ℝ)..T, flow A t * flow B t
def generator {I : Type} [Fintype I] [DecidableEq I] (A B : Mat I) : Mat (I ⊕ I) :=
  Matrix.fromBlocks (-A) 1 0 B

abbrev Six := Fin 2 ⊕ Fin 4
def exampleA : Mat Six := fromBlocks (!![0,3;0,0] : Mat (Fin 2)) 0 0 0
def exampleB (k : ℝ) : Mat Six := fromBlocks (!![0,0;4*k,0] : Mat (Fin 2)) 0 0 0

theorem main :
    (∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Mat I) (T : ℝ),
      integrated A B T = flow A T * (flow (generator A B) T).toBlocks₁₂ ∧
      ((integrated A B T).det=0 ↔ (flow (generator A B) T).toBlocks₁₂.det=0) ∧
      A * integrated A B T + integrated A B T * B = flow A T * flow B T - 1) ∧
    (∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Mat I),
      (∃ ε : ℝ, 0<ε ∧ ∀ t : ℝ, 0<t → t<ε → (integrated A B t).det ≠ 0) ∧
      ((∃ t : ℝ, 0<t ∧ (integrated A B t).det=0) →
        ∃ t : ℝ, IsLeast {s : ℝ | 0<s ∧ (integrated A B s).det=0} t)) ∧
    (∀ k : ℝ, exampleA.trace=0 ∧ (exampleB k).trace=0 ∧ exampleA^2=0 ∧ (exampleB k)^2=0 ∧
      exampleA.charpoly=Polynomial.X^6 ∧ (exampleB k).charpoly=Polynomial.X^6) ∧
    (∀ k : ℝ, k≠0 → ¬ Commute exampleA (exampleB k)) ∧
    (∀ k T : ℝ, (integrated exampleA (exampleB k) T).det=T^6*(1+k*T^2)) ∧
    IsLeast {t : ℝ | 0<t ∧ (integrated exampleA (exampleB (-1)) t).det=0} 1 ∧
    (∀ t : ℝ, 0<t → (integrated exampleA (exampleB 1) t).det≠0) := by
  sorry
end OMA.S_mo_246858
