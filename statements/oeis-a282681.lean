import Mathlib

/-!
# OEIS A282681: the x-axes of Rule 499 and Rule 497 agree from stage 2 on

Source: https://oeis.org/A282681 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A282681 (Robert Price, Feb 20 2017), offset 0: Decimal representation of the x-axis, from
the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular
automaton defined by Rule 499, based on the 5-celled von Neumann neighborhood. Comment:
Initialized with a single black (ON) cell at stage zero. Formula: Conjecture: a(n) = A282677(n)
for n>=2. - R. J. Mathar, Jun 21 2025.
Entry A282677 (Robert Price, Feb 20 2017), offset 0, is defined in the same words with Rule 497.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entries' program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell (so the background may change). The entries' program
  runs on a finite torus of side 2*128+1, which agrees with the plane for the stages listed.
* Counting convention: a(n) reads the cells (0,0), (1,0), ..., (n,0) of stage n as a binary
  number with the origin as the most significant digit, as the program does with FromDigits.
* Controls from the entries: the definitions give a(1) = 2 for Rule 499 and a(1) = 0 for Rule
  497, and a(13) = 768 and a(15) = 16128 for both rules.
-/

namespace OMA.S_oeis_a282681

/-- One step of the outer totalistic automaton with code rule on the von Neumann neighborhood. -/
def step (rule : ℕ) (s : ℤ × ℤ → Bool) (p : ℤ × ℤ) : Bool :=
  Nat.testBit rule ((s p).toNat + 2 * ((s (p.1 - 1, p.2)).toNat + (s (p.1 + 1, p.2)).toNat +
    (s (p.1, p.2 - 1)).toNat + (s (p.1, p.2 + 1)).toNat))

/-- Stage n of the automaton started from a single ON cell at the origin. -/
def state (rule : ℕ) : ℕ → ℤ × ℤ → Bool
  | 0 => fun p => decide (p.1 = 0 ∧ p.2 = 0)
  | n + 1 => step rule (state rule n)

/-- The x-axis of stage n from the origin to the right edge, read in binary, origin first. -/
def xaxis (rule n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state rule n ((i : ℤ), 0)).toNat * 2 ^ (n - i)

/-- Mathar's conjecture: A282681(n) = A282677(n) for n >= 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n → xaxis 499 n = xaxis 497 n := by
  sorry

end OMA.S_oeis_a282681
