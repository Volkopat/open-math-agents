import Mathlib

/-!
# OEIS A212732: Kotesovec's recurrence and asymptotic for 0..2 arrays of length 2n+2 with every window of 2n consecutive entries summing to less than 2n

Source: https://oeis.org/A212732 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A212732 (R. H. Hardin, May 25 2012), offset 1: Number of 0..2 arrays of length 2*n+2 with sum less than 2*n in any length 2n subsequence (=less than 50% duty cycle).
Formula section:
From Vaclav Kotesovec, Jul 31 2013: (Start)
Empirical: n*(2*n-1)*(59040*n^4 - 630664*n^3 + 2419338*n^2 - 3925427*n + 2259783)*a(n) = (2243520*n^6 - 26740112*n^5 + 122386084*n^4 - 271040464*n^3 + 300314759*n^2 - 153351297*n + 26751060)*a(n-1) + 81*(n-3)*(2*n-7)*(59040*n^4 - 394504*n^3 + 881586*n^2 - 742583*n + 182070)*a(n-3) - 9*(1298880*n^6 - 16413328*n^5 + 81293588*n^4 - 199839104*n^3 + 252840847*n^2 - 150974403*n + 30574530)*a(n-2)
Conjecture: a(n) ~ 9/2*9^n. (End)

Formalization notes:
* An array of length 2n+2 with entries 0..2 is a map x : Fin (2 * n + 2) -> Fin 3. A length 2n
  subsequence is a block of 2n consecutive entries x(i), ..., x(i + 2n - 1) (`duty`); the
  condition is that each such block has sum less than 2n. Reading subsequence as any 2n entries,
  not necessarily consecutive, gives other numbers (4 instead of 5 at n = 1); the consecutive
  reading reproduces the entry's data and the duty-cycle remark.
* a(n) is defined for every n; the entry starts at n = 1. The block gives no range for the
  recurrence, so it is stated for every n >= 4, the smallest n for which a(n - 3) is a term of the
  entry, as an identity of integers.
* The asymptotic a(n) ~ (9/2) 9^n is `Asymptotics.IsEquivalent` along `Filter.atTop` for the real
  sequences.
* The definition reproduces the entry's data (8, 148, 1669, 16878, 163495, 1549297, ... from
  n = 1), checked by direct enumeration of the arrays for small n and through the formula of the
  proof for all 18 listed terms, which the proof file also proves as controls.
-/

namespace OMA.S_oeis_a212732

open Finset

/-- Every block of 2n consecutive entries of x has sum less than 2n. -/
def duty (n : ℕ) {L : ℕ} (x : Fin L → Fin 3) : Prop :=
  ∀ i : Fin (L + 1), (i : ℕ) + 2 * n ≤ L →
    ((univ.filter (fun t : Fin L => (i : ℕ) ≤ t ∧ (t : ℕ) < i + 2 * n)).sum fun t => (x t : ℕ)) < 2 * n

instance (n L : ℕ) : DecidablePred (@duty n L) := fun x => by unfold duty; infer_instance

/-- A212732: the number of 0..2 arrays of length 2n+2 with sum less than 2n in every block of 2n
consecutive entries. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (2 * n + 2) → Fin 3)).filter (duty n)).card

/-- Kotesovec's conjectures. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n →
      (n : ℤ) * (2 * (n : ℤ) - 1) * (59040 * (n : ℤ) ^ 4 - 630664 * (n : ℤ) ^ 3 + 2419338 * (n : ℤ) ^ 2 - 3925427 * (n : ℤ) + 2259783) * (a n : ℤ) =
          (2243520 * (n : ℤ) ^ 6 - 26740112 * (n : ℤ) ^ 5 + 122386084 * (n : ℤ) ^ 4 - 271040464 * (n : ℤ) ^ 3 + 300314759 * (n : ℤ) ^ 2 - 153351297 * (n : ℤ) + 26751060) * (a (n - 1) : ℤ)
            + 81 * ((n : ℤ) - 3) * (2 * (n : ℤ) - 7) * (59040 * (n : ℤ) ^ 4 - 394504 * (n : ℤ) ^ 3 + 881586 * (n : ℤ) ^ 2 - 742583 * (n : ℤ) + 182070) * (a (n - 3) : ℤ)
            - 9 * (1298880 * (n : ℤ) ^ 6 - 16413328 * (n : ℤ) ^ 5 + 81293588 * (n : ℤ) ^ 4 - 199839104 * (n : ℤ) ^ 3 + 252840847 * (n : ℤ) ^ 2 - 150974403 * (n : ℤ) + 30574530) * (a (n - 2) : ℤ)) ∧
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => 9 / 2 * (9 : ℝ) ^ n) := by
  sorry

end OMA.S_oeis_a212732
