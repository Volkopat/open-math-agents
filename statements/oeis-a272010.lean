import Mathlib

/-!
# OEIS A272010: Mathar's conjecture on the first differences of ON cells for Rule 413 and Rule 1

Source: https://oeis.org/A272010
Conjecture: R. J. Mathar, Apr 19 2016.
Formalization: @longling12 (drafted with AI assistance)

Entry A272010 (Robert Price, Apr 17 2016), offset 0: First differences of number of active (ON,
black) cells in n-th stage of growth of two-dimensional cellular automaton defined by Rule 413,
based on the 5-celled von Neumann neighborhood, initialized with a single black (ON) cell at
stage zero.
Formula: Conjecture: a(n) = A269909(n), n>0. - R. J. Mathar, Apr 19 2016.
Entry A269909 (Robert Price, Mar 07 2016), offset 0, is defined in the same words with Rule 1.

Modeling notes:
* Under outer-totalistic Rule r on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}), each cell of Z^2 updates synchronously to bit c + 2*s of r, where
  c is its current state and s is the number of ON orthogonal neighbors.
* Following the entries' Mathematica programs, onCount r t counts ON cells in [-t, t]^2 at stage t,
  and the n-th first difference is onCount r (n + 1) - onCount r n, reproducing 7, -3, 43, -43,
  115, -115, ... for Rule 413 (A272010) and 3, -3, 43, -43, 115, -115, ... for Rule 1 (A269909).
-/

namespace OMA.S_oeis_a272010

/-- One step of outer-totalistic Rule r on the 5-cell von Neumann neighborhood. -/
def step (r : ℕ) (g : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit r ((g x y).toNat + 2 *
    ((g (x - 1) y).toNat + (g (x + 1) y).toNat + (g x (y - 1)).toNat + (g x (y + 1)).toNat))

/-- Stage t of Rule r on Z^2 started from a single ON cell at the origin (0, 0). -/
def state (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | t + 1 => step r (state r t)

/-- Number of ON cells in [-t, t]^2 at stage t of Rule r. -/
def onCount (r t : ℕ) : ℤ :=
  (((Finset.range (2 * t + 1) ×ˢ Finset.range (2 * t + 1)).filter fun p : ℕ × ℕ =>
    state r t ((p.1 : ℤ) - t) ((p.2 : ℤ) - t)).card : ℤ)

/-- A272010(n): first difference onCount 413 (n + 1) - onCount 413 n. -/
def a (n : ℕ) : ℤ := onCount 413 (n + 1) - onCount 413 n

/-- A269909(n): first difference onCount 1 (n + 1) - onCount 1 n. -/
def A269909 (n : ℕ) : ℤ := onCount 1 (n + 1) - onCount 1 n

/-- Mathar's conjecture: A272010(n) = A269909(n) for n > 0. -/
theorem main : ∀ n : ℕ, 0 < n → a n = A269909 n := by
  sorry

end OMA.S_oeis_a272010
