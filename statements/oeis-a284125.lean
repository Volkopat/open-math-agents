import Mathlib

/-!
# A284125: Number of binary strings w of length n for which s, the longest proper suffix of w that appears at least twice in w, is of length 2

Source: https://oeis.org/A284125
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-28.
Offset 1 (data 0, 0, 2, 4, 12, 26, 52, 98, 178, 316, 556, ...).

Conventions:
* A binary string of length `n` is encoded as `w : Fin n → Fin 2`.
* A proper suffix of length `L` (`L < n`) appears at least twice in `w` iff there is an
  earlier starting position `i < n - L` such that the contiguous substring of length `L`
  beginning at `i` equals the suffix of length `L` (which begins at `n - L`).
* The longest proper suffix of `w` appearing at least twice has length 2 iff the proper
  suffix of length 2 appears at least twice and no proper suffix of length `L > 2` appears
  at least twice.
* `a 0 = 0` is a convention outside the offset; it does not affect the generating function,
  whose numerator is divisible by `x ^ 3`.
* The generating function is stated after multiplication by its denominator, whose constant
  term is one.

Conjecture from Colin Barker, Jun 07 2017:
G.f.: 2*x^3*(1 + x^2)*(1 - 4*x + 6*x^2 - 5*x^3 + x^4 + 2*x^5 + 2*x^6 - 2*x^7) / ((1 - x)^2*(1 - x - x^2)*(1 - 2*x + x^2 - x^3)*(1 - x - x^2 - x^3)) (conjectured).
-/

namespace OMA.S_oeis_a284125

open PowerSeries

/-- The proper suffix of `w` of length `L` appears at least twice as a contiguous substring
of `w`. -/
def sufAppearsTwice (n L : ℕ) (w : Fin n → Fin 2) : Prop :=
  ∃ hL : L < n, ∃ i : Fin n, ∃ hi : (i : ℕ) < n - L,
    ∀ k : Fin L, w ⟨(i : ℕ) + (k : ℕ), by omega⟩ = w ⟨n - L + (k : ℕ), by omega⟩

instance (n L : ℕ) (w : Fin n → Fin 2) : Decidable (sufAppearsTwice n L w) := by
  unfold sufAppearsTwice
  infer_instance

/-- The longest proper suffix of `w` appearing at least twice has length 2. -/
def valid (n : ℕ) (w : Fin n → Fin 2) : Prop :=
  sufAppearsTwice n 2 w ∧ ∀ L : Fin n, 2 < (L : ℕ) → ¬ sufAppearsTwice n L w

instance (n : ℕ) (w : Fin n → Fin 2) : Decidable (valid n w) := by
  unfold valid
  infer_instance

/-- A284125: number of binary strings of length `n` whose longest proper suffix appearing
at least twice has length 2. -/
def a : ℕ → ℕ
  | 0 => 0
  | n => (Finset.univ.filter (valid n)).card

theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - X) ^ 2 * (1 - X - X ^ 2) * (1 - 2 * X + X ^ 2 - X ^ 3) * (1 - X - X ^ 2 - X ^ 3)) =
    2 * X ^ 3 * (1 + X ^ 2) *
      (1 - 4 * X + 6 * X ^ 2 - 5 * X ^ 3 + X ^ 4 + 2 * X ^ 5 + 2 * X ^ 6 - 2 * X ^ 7) := by
  sorry

end OMA.S_oeis_a284125
