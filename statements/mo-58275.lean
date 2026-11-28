import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# Variance of an eigenfunction along a finite ergodic Markov chain

Source: https://mathoverflow.net/questions/58275
Question by John Jiang, 12 March 2011. Credit: @etaubman.

The intended variance is the variance of f(X_t) when X_0 is a fixed state,
as clarified in the preceding question https://mathoverflow.net/questions/58241.
The displayed P_t f in the question is understood in this probabilistic sense,
not as a deterministic number whose variance would be zero.

A finite state space is represented by Fin n. Row stochasticity, irreducibility,
and aperiodicity are stated separately. The period-one condition says that the
only common natural-number divisor of the positive return times is 1; this is
equivalent to their greatest common divisor being 1. No laziness or positivity
of all transition entries is imposed on the general assertion.

The eigenfunction equation is the one-step equation P f = lambda f, equivalent
to P^t f = lambda^t f for all natural t. The initial law is the point mass at
start, so its time-t law is precisely the start row of P^t. The variance is
the second moment minus the square of the first moment.
-/

namespace OMA.S_mo_58275

open scoped BigOperators

def rowStochastic {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

def irreducible {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, ∃ t : ℕ, 0 < t ∧ 0 < (P ^ t) i j

def aperiodic {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i (d : ℕ), (∀ t : ℕ, 0 < t → 0 < (P ^ t) i i → d ∣ t) → d = 1

def variance {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → ℝ) (start : Fin n) (t : ℕ) : ℝ :=
  (∑ j, (P ^ t) start j * (f j) ^ 2) - (∑ j, (P ^ t) start j * f j) ^ 2

theorem main : ∀ (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ),
    rowStochastic P → irreducible P → aperiodic P →
    ∀ (f : Fin n → ℝ) (lam : ℝ), f ≠ 0 →
      (∀ i, (∑ j, P i j * f j) = lam * f i) →
      ∀ start : Fin n, Monotone (variance P f start) := by
  sorry

end OMA.S_mo_58275
