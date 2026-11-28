import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Order.Bounds.Basic

/-!
# Largest partial quotients for the square roots of 3ⁿ−1

For n≥1 the radicand is 2 modulo 3, so it is a positive nonsquare.
The ordinary continued fraction of its square root is periodic after
its initial integer part. In a complete quotient (√D+m)/d the digit is
(⌊√D⌋+m) div d. The transition below is the standard integer algorithm.
The set of all positive-index digits is exactly the set in the period.

The displayed comparison includes the even indices, the error bound
and Cloitre's conjectured list of exceptions. The examples 3, 9, 27
are taken to mean positive powers of three.

Source: https://oeis.org/A077627
Continued fractions: https://sites.millersville.edu/bikenaga/number-theory/continued-fractions-for-square-roots/continued-fractions-for-square-roots.html
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a077627

abbrev State := ℕ × ℕ

def step (D h : ℕ) : State → State
  | (m,d) =>
    let next := d*((h+m)/d)-m
    (next,(D-next^2)/d)

def state (D : ℕ) : ℕ → State
  | 0 => (0,1)
  | j+1 => step D (Nat.sqrt D) (state D j)

def partialQuotient (D j : ℕ) : ℤ :=
  ((Nat.sqrt D + (state D j).1)/(state D j).2 : ℕ)

def periodTerms (D : ℕ) : Set ℤ := Set.range (fun j : ℕ => partialQuotient D (j+1))

noncomputable def comparison (n : ℕ) : ℝ := 2*(Real.sqrt ((3:ℝ)^n)-1)

theorem main : ∀ n : ℕ, 0<n → ∃ z : ℤ,
    IsGreatest (periodTerms (3^n-1)) z ∧
    (Even n → z=2*((3:ℤ)^(n/2)-1)) ∧
    (0 ≤ (z:ℝ)-comparison n ∧ (z:ℝ)-comparison n < 2) ∧
    ((∃ k : ℕ, n=3^(k+1)) → z=⌈comparison n⌉+1) ∧
    ((¬ ∃ k : ℕ, n=3^(k+1)) → z=⌈comparison n⌉) := by
  sorry

end OMA.S_oeis_a077627
