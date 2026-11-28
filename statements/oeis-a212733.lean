import Mathlib

/-!
# OEIS A212733: Kotesovec's recurrence and asymptotic for 0..2 arrays of length 2n+3 with every window of 2n consecutive entries summing to less than 2n

Source: https://oeis.org/A212733 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A212733 (R. H. Hardin, May 25 2012), offset 1: Number of 0..2 arrays of length 2*n+3 with sum less than 2*n in any length 2n subsequence (=less than 50% duty cycle).
Formula section:
From Vaclav Kotesovec, Jul 31 2013: (Start)
Empirical: n*(2*n-1)*(641952*n^5 - 9661256*n^4 + 56355290*n^3 - 158324563*n^2 + 212843323*n - 108787536)*a(n) = (24394176*n^7 - 397299472*n^6 + 2605594692*n^5 - 8806725568*n^4 + 16309249503*n^3 - 16218569485*n^2 + 7794486684*n - 1330045920)*a(n-1) - 9*(14122944*n^7 - 240151568*n^6 + 1667254836*n^5 - 6073887920*n^4 + 12400532871*n^3 - 13948629407*n^2 + 7754485194*n - 1524164040)*a(n-2) + 81*(n-4)*(2*n-7)*(641952*n^5 - 6451496*n^4 + 24129786*n^3 - 40806709*n^2 + 29824803*n - 6932790)*a(n-3)
Conjecture: a(n) ~ 27/2*9^n. (End)

Formalization notes:
* An array of length 2n+3 with entries 0..2 is a map x : Fin (2 * n + 3) -> Fin 3. A length 2n
  subsequence is a block of 2n consecutive entries x(i), ..., x(i + 2n - 1) (`duty`); the
  condition is that each such block has sum less than 2n. Reading subsequence as any 2n entries,
  not necessarily consecutive, gives other numbers (4 instead of 5 at n = 1); the consecutive
  reading reproduces the entry's data and the duty-cycle remark.
* a(n) is defined for every n; the entry starts at n = 1. The block gives no range for the
  recurrence, so it is stated for every n >= 4, the smallest n for which a(n - 3) is a term of the
  entry, as an identity of integers.
* The asymptotic a(n) ~ (27/2) 9^n is `Asymptotics.IsEquivalent` along `Filter.atTop` for the real
  sequences.
* The definition reproduces the entry's data (13, 322, 4057, 43050, 428617, 4135249, ... from
  n = 1), checked by direct enumeration of the arrays for small n and through the formula of the
  proof for all 17 listed terms, which the proof file also proves as controls.
-/

namespace OMA.S_oeis_a212733

open Finset

/-- Every block of 2n consecutive entries of x has sum less than 2n. -/
def duty (n : ℕ) {L : ℕ} (x : Fin L → Fin 3) : Prop :=
  ∀ i : Fin (L + 1), (i : ℕ) + 2 * n ≤ L →
    ((univ.filter (fun t : Fin L => (i : ℕ) ≤ t ∧ (t : ℕ) < i + 2 * n)).sum fun t => (x t : ℕ)) < 2 * n

instance (n L : ℕ) : DecidablePred (@duty n L) := fun x => by unfold duty; infer_instance

/-- A212733: the number of 0..2 arrays of length 2n+3 with sum less than 2n in every block of 2n
consecutive entries. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (2 * n + 3) → Fin 3)).filter (duty n)).card

/-- Kotesovec's conjectures. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n →
      (n : ℤ) * (2 * (n : ℤ) - 1) * (641952 * (n : ℤ) ^ 5 - 9661256 * (n : ℤ) ^ 4 + 56355290 * (n : ℤ) ^ 3 - 158324563 * (n : ℤ) ^ 2 + 212843323 * (n : ℤ) - 108787536) * (a n : ℤ) =
          (24394176 * (n : ℤ) ^ 7 - 397299472 * (n : ℤ) ^ 6 + 2605594692 * (n : ℤ) ^ 5 - 8806725568 * (n : ℤ) ^ 4 + 16309249503 * (n : ℤ) ^ 3 - 16218569485 * (n : ℤ) ^ 2 + 7794486684 * (n : ℤ) - 1330045920) * (a (n - 1) : ℤ)
            - 9 * (14122944 * (n : ℤ) ^ 7 - 240151568 * (n : ℤ) ^ 6 + 1667254836 * (n : ℤ) ^ 5 - 6073887920 * (n : ℤ) ^ 4 + 12400532871 * (n : ℤ) ^ 3 - 13948629407 * (n : ℤ) ^ 2 + 7754485194 * (n : ℤ) - 1524164040) * (a (n - 2) : ℤ)
            + 81 * ((n : ℤ) - 4) * (2 * (n : ℤ) - 7) * (641952 * (n : ℤ) ^ 5 - 6451496 * (n : ℤ) ^ 4 + 24129786 * (n : ℤ) ^ 3 - 40806709 * (n : ℤ) ^ 2 + 29824803 * (n : ℤ) - 6932790) * (a (n - 3) : ℤ)) ∧
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => 27 / 2 * (9 : ℝ) ^ n) := by
  sorry

end OMA.S_oeis_a212733
