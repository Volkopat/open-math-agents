import Mathlib

/-!
# OEIS A389148: the Erdős–Graham conjecture on semiprimes

Source: https://oeis.org/A389148
Reference: P. Erdős and R. L. Graham, On products of factorials (1976), p. 353.
Credit: @rkka02

This is the conjecture in the entry that almost all terms of A001358 lie in A389148.
Semiprimes include prime squares. The denominator counts semiprimes, and the numerator
counts those meeting the entry's definition with exactly five distinct positive indices.
-/

open Filter
open scoped Topology

namespace OMA.S_oeis_a389148

def semiprime (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q

def fiveFactorialSquare (e : ℕ) : Prop :=
  ∃ a b c d : ℕ, 0 < a ∧ a < b ∧ b < c ∧ c < d ∧ d < e ∧
    IsSquare (a.factorial * b.factorial * c.factorial * d.factorial * e.factorial)

def inSequence (n : ℕ) : Prop :=
  6 < n ∧ ¬ n.Prime ∧ ¬ fiveFactorialSquare n

noncomputable def countUpTo (P : ℕ → Prop) (X : ℕ) : ℕ :=
  open Classical in ((Finset.Icc 1 X).filter P).card

theorem main : Tendsto
    (fun X : ℕ => (countUpTo (fun n => semiprime n ∧ inSequence n) X : ℝ) /
      (countUpTo semiprime X : ℝ)) atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a389148
