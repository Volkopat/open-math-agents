import Mathlib

/-!
# OEIS A212730: Kotesovec's recurrence and asymptotic for 0..2 arrays of length 2n with every window of 2n consecutive entries summing to less than 2n

Source: https://oeis.org/A212730 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A212730 (R. H. Hardin, May 25 2012), offset 1: Number of 0..2 arrays of length 2*n with sum less than 2*n in any length 2n subsequence (=less than 50% duty cycle).
Formula section:
From Vaclav Kotesovec, Jul 31 2013: (Start)
Empirical: n*(2*n-1)*(16*n^2 - 60*n + 53)*a(n) = (608*n^4 - 3032*n^3 + 5050*n^2 - 3259*n + 660)*a(n-1) - 9*(352*n^4 - 2008*n^3 + 3986*n^2 - 3143*n + 750)*a(n-2) + 81*(n-2)*(2*n-5)*(16*n^2 - 28*n + 9)*a(n-3).
Conjecture: a(n) ~ 9^n/2. (End)

Formalization notes:
* An array of length 2n with entries 0..2 is a map x : Fin (2 * n) -> Fin 3. A length 2n
  subsequence is a block of 2n consecutive entries x(i), ..., x(i + 2n - 1) (`duty`, the
  definition used for the rows A212731-A212734 of the same table); the condition is that each such
  block has sum less than 2n. At length 2n the only such block is the whole array, so a(n) counts
  the arrays with sum less than 2n, as the duty-cycle remark says.
* a(n) is defined for every n; the entry starts at n = 1. The block gives no range for the
  recurrence, so it is stated for every n >= 4, the smallest n for which a(n - 3) is a term of the
  entry, as an identity of integers.
* The asymptotic a(n) ~ 9^n/2 is `Asymptotics.IsEquivalent` along `Filter.atTop` for the real
  sequences.
* The definition reproduces the entry's data (3, 31, 294, 2727, 25048, 228826, ... from n = 1),
  checked by direct enumeration of the arrays for small n and through the formula of the proof for
  all 19 listed terms, which the proof file also proves as controls.
-/

namespace OMA.S_oeis_a212730

open Finset

/-- Every block of 2n consecutive entries of x has sum less than 2n. -/
def duty (n : ℕ) {L : ℕ} (x : Fin L → Fin 3) : Prop :=
  ∀ i : Fin (L + 1), (i : ℕ) + 2 * n ≤ L →
    ((univ.filter (fun t : Fin L => (i : ℕ) ≤ t ∧ (t : ℕ) < i + 2 * n)).sum fun t => (x t : ℕ)) < 2 * n

instance (n L : ℕ) : DecidablePred (@duty n L) := fun x => by unfold duty; infer_instance

/-- A212730: the number of 0..2 arrays of length 2n with sum less than 2n in every block of 2n
consecutive entries. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (2 * n) → Fin 3)).filter (duty n)).card

/-- Kotesovec's conjectures. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n →
      (n : ℤ) * (2 * (n : ℤ) - 1) * (16 * (n : ℤ) ^ 2 - 60 * (n : ℤ) + 53) * (a n : ℤ) =
          (608 * (n : ℤ) ^ 4 - 3032 * (n : ℤ) ^ 3 + 5050 * (n : ℤ) ^ 2 - 3259 * (n : ℤ) + 660) * (a (n - 1) : ℤ)
            - 9 * (352 * (n : ℤ) ^ 4 - 2008 * (n : ℤ) ^ 3 + 3986 * (n : ℤ) ^ 2 - 3143 * (n : ℤ) + 750) * (a (n - 2) : ℤ)
            + 81 * ((n : ℤ) - 2) * (2 * (n : ℤ) - 5) * (16 * (n : ℤ) ^ 2 - 28 * (n : ℤ) + 9) * (a (n - 3) : ℤ)) ∧
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => (9 : ℝ) ^ n / 2) := by
  sorry

end OMA.S_oeis_a212730
