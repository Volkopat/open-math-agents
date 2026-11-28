import Mathlib

/-!
# OEIS A272588: Mathar's conjecture on the first differences of ON cells for Rule 507 and Rule 505

Source: https://oeis.org/A272588
Conjecture: R. J. Mathar, May 20 2016.
Formalization: @longling12 (drafted with AI assistance)

Entry A272588 (Robert Price, May 03 2016), offset 0: First differences of number of active (ON,
black) cells in n-th stage of growth of two-dimensional cellular automaton defined by Rule 507,
based on the 5-celled von Neumann neighborhood, initialized with a single black (ON) cell at
stage zero.
Formula: Conjecture: a(n) = A272584(n), n>1. - R. J. Mathar, May 20 2016.
Entry A272584 (Robert Price, May 03 2016), offset 0, is defined in the same words with Rule 505.

Modeling notes:
* Under outer-totalistic Rule r on the 5-cell von Neumann neighborhood (kernel
  {{0,2,0},{2,1,2},{0,2,0}}), each cell of Z^2 updates synchronously to bit c + 2*s of r, where
  c is its current state and s is the number of ON orthogonal neighbors.
* Following the entries' Mathematica programs, onCount r t counts ON cells in [-t, t]^2 at stage t,
  and the n-th first difference is onCount r (n + 1) - onCount r n, reproducing 4, 8, 27, -11,
  71, -31, ... for Rule 507 (A272588) and 3, 9, 27, -11, 71, -31, ... for Rule 505 (A272584).
-/

namespace OMA.S_oeis_a272588

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

/-- A272588(n): first difference onCount 507 (n + 1) - onCount 507 n. -/
def a (n : ℕ) : ℤ := onCount 507 (n + 1) - onCount 507 n

/-- A272584(n): first difference onCount 505 (n + 1) - onCount 505 n. -/
def A272584 (n : ℕ) : ℤ := onCount 505 (n + 1) - onCount 505 n

/-- Mathar's conjecture: A272588(n) = A272584(n) for n > 1. -/
theorem main : ∀ n : ℕ, 1 < n → a n = A272584 n := by
  sorry

end OMA.S_oeis_a272588
