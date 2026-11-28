import Mathlib

/-!
# OEIS A212731: Kotesovec's recurrence and asymptotic for 0..2 arrays of length 2n+1 with every window of 2n consecutive entries summing to less than 2n

Source: https://oeis.org/A212731 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A212731 (R. H. Hardin, May 25 2012), offset 1: Number of 0..2 arrays of length 2*n+1 with sum less than 2*n in any length 2n subsequence (=less than 50% duty cycle).
Formula section:
From Vaclav Kotesovec, Jul 31 2013: (Start)
Empirical: n*(2*n-1)*(816*n^3 - 5572*n^2 + 11983*n - 8097)*a(n) = (31008*n^5 - 250088*n^4 + 727230*n^3 - 936367*n^2 + 518859*n - 93600)*a(n-1) - 9*(17952*n^5 - 157672*n^4 + 514566*n^3 - 767531*n^2 + 504861*n - 106650)*a(n-2) + 81*(n-3)*(2*n-5)*(816*n^3 - 3124*n^2 + 3287*n - 870)*a(n-3).
Conjecture: a(n) ~ 3/2*9^n. (End)

Formalization notes:
* An array of length 2n+1 with entries 0..2 is a map x : Fin (2 * n + 1) -> Fin 3. A length 2n
  subsequence is a block of 2n consecutive entries x(i), ..., x(i + 2n - 1) (`duty`); the
  condition is that each such block has sum less than 2n. Reading subsequence as any 2n entries,
  not necessarily consecutive, gives other numbers (4 instead of 5 at n = 1); the consecutive
  reading reproduces the entry's data and the duty-cycle remark.
* a(n) is defined for every n; the entry starts at n = 1. The block gives no range for the
  recurrence, so it is stated for every n >= 4, the smallest n for which a(n - 3) is a term of the
  entry, as an identity of integers.
* The asymptotic a(n) ~ (3/2) 9^n is `Asymptotics.IsEquivalent` along `Filter.atTop` for the real
  sequences.
* The definition reproduces the entry's data (5, 67, 690, 6681, 63052, 587036, ... from n = 1),
  checked by direct enumeration of the arrays for small n and through the formula of the proof for
  all 18 listed terms, which the proof file also proves as controls.
-/

namespace OMA.S_oeis_a212731

open Finset

/-- Every block of 2n consecutive entries of x has sum less than 2n. -/
def duty (n : ℕ) {L : ℕ} (x : Fin L → Fin 3) : Prop :=
  ∀ i : Fin (L + 1), (i : ℕ) + 2 * n ≤ L →
    ((univ.filter (fun t : Fin L => (i : ℕ) ≤ t ∧ (t : ℕ) < i + 2 * n)).sum fun t => (x t : ℕ)) < 2 * n

instance (n L : ℕ) : DecidablePred (@duty n L) := fun x => by unfold duty; infer_instance

/-- A212731: the number of 0..2 arrays of length 2n+1 with sum less than 2n in every block of 2n
consecutive entries. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (2 * n + 1) → Fin 3)).filter (duty n)).card

/-- Kotesovec's conjectures. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n →
      (n : ℤ) * (2 * (n : ℤ) - 1) * (816 * (n : ℤ) ^ 3 - 5572 * (n : ℤ) ^ 2 + 11983 * (n : ℤ) - 8097) * (a n : ℤ) =
          (31008 * (n : ℤ) ^ 5 - 250088 * (n : ℤ) ^ 4 + 727230 * (n : ℤ) ^ 3 - 936367 * (n : ℤ) ^ 2 + 518859 * (n : ℤ) - 93600) * (a (n - 1) : ℤ)
            - 9 * (17952 * (n : ℤ) ^ 5 - 157672 * (n : ℤ) ^ 4 + 514566 * (n : ℤ) ^ 3 - 767531 * (n : ℤ) ^ 2 + 504861 * (n : ℤ) - 106650) * (a (n - 2) : ℤ)
            + 81 * ((n : ℤ) - 3) * (2 * (n : ℤ) - 5) * (816 * (n : ℤ) ^ 3 - 3124 * (n : ℤ) ^ 2 + 3287 * (n : ℤ) - 870) * (a (n - 3) : ℤ)) ∧
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => 3 / 2 * (9 : ℝ) ^ n) := by
  sorry

end OMA.S_oeis_a212731
