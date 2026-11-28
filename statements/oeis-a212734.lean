import Mathlib

/-!
# OEIS A212734: Kotesovec's recurrence and asymptotic for 0..2 arrays of length 2n+4 with every window of 2n consecutive entries summing to less than 2n

Source: https://oeis.org/A212734 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A212734 (R. H. Hardin, May 25 2012), offset 1: Number of 0..2 arrays of length 2*n+4 with sum less than 2*n in any length 2n subsequence (=less than 50% duty cycle).
Formula section:
From Vaclav Kotesovec, Jul 31 2013: (Start)
Empirical: n*(2*n-1)*(13283136*n^6 - 264953520*n^5 + 2147785772*n^4 - 9019996352*n^3 + 20594052913*n^2 - 24090888493*n + 11202753384)*a(n) = (504759168*n^8 - 10692541152*n^7 + 94303861048*n^6 - 448109760340*n^5 + 1240039075502*n^4 - 2015761359053*n^3 + 1843073445627*n^2 - 843009243120*n + 141051002400)*a(n-1) - 9*(292228992*n^8 - 6400152288*n^7 + 58931188760*n^6 - 296092883492*n^5 + 880725021838*n^4 - 1570768747177*n^3 + 1613191469925*n^2 - 846280196028*n + 162004328640)*a(n-2) + 81*(n-4)*(2*n-9)*(13283136*n^6 - 185254704*n^5 + 1022265212*n^4 - 2812725744*n^3 + 3970490329*n^2 - 2616697419*n + 582036840)*a(n-3)
Conjecture: a(n) ~ 81/2*9^n. (End)

Formalization notes:
* An array of length 2n+4 with entries 0..2 is a map x : Fin (2 * n + 4) -> Fin 3. A length 2n
  subsequence is a block of 2n consecutive entries x(i), ..., x(i + 2n - 1) (`duty`); the
  condition is that each such block has sum less than 2n. Reading subsequence as any 2n entries,
  not necessarily consecutive, gives other numbers (4 instead of 5 at n = 1); the consecutive
  reading reproduces the entry's data and the duty-cycle remark.
* a(n) is defined for every n; the entry starts at n = 1. The block gives no range for the
  recurrence, so it is stated for every n >= 4, the smallest n for which a(n - 3) is a term of the
  entry, as an identity of integers.
* The asymptotic a(n) ~ (81/2) 9^n is `Asymptotics.IsEquivalent` along `Filter.atTop` for the real
  sequences.
* The definition reproduces the entry's data (21, 677, 9807, 109995, 1128418, 11095332, ... from
  n = 1), checked by direct enumeration of the arrays for small n and through the formula of the
  proof for all 17 listed terms, which the proof file also proves as controls.
-/

namespace OMA.S_oeis_a212734

open Finset

/-- Every block of 2n consecutive entries of x has sum less than 2n. -/
def duty (n : ℕ) {L : ℕ} (x : Fin L → Fin 3) : Prop :=
  ∀ i : Fin (L + 1), (i : ℕ) + 2 * n ≤ L →
    ((univ.filter (fun t : Fin L => (i : ℕ) ≤ t ∧ (t : ℕ) < i + 2 * n)).sum fun t => (x t : ℕ)) < 2 * n

instance (n L : ℕ) : DecidablePred (@duty n L) := fun x => by unfold duty; infer_instance

/-- A212734: the number of 0..2 arrays of length 2n+4 with sum less than 2n in every block of 2n
consecutive entries. -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (2 * n + 4) → Fin 3)).filter (duty n)).card

/-- Kotesovec's conjectures. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n →
      (n : ℤ) * (2 * (n : ℤ) - 1) * (13283136 * (n : ℤ) ^ 6 - 264953520 * (n : ℤ) ^ 5 + 2147785772 * (n : ℤ) ^ 4 - 9019996352 * (n : ℤ) ^ 3 + 20594052913 * (n : ℤ) ^ 2 - 24090888493 * (n : ℤ) + 11202753384) * (a n : ℤ) =
          (504759168 * (n : ℤ) ^ 8 - 10692541152 * (n : ℤ) ^ 7 + 94303861048 * (n : ℤ) ^ 6 - 448109760340 * (n : ℤ) ^ 5 + 1240039075502 * (n : ℤ) ^ 4 - 2015761359053 * (n : ℤ) ^ 3 + 1843073445627 * (n : ℤ) ^ 2 - 843009243120 * (n : ℤ) + 141051002400) * (a (n - 1) : ℤ)
            - 9 * (292228992 * (n : ℤ) ^ 8 - 6400152288 * (n : ℤ) ^ 7 + 58931188760 * (n : ℤ) ^ 6 - 296092883492 * (n : ℤ) ^ 5 + 880725021838 * (n : ℤ) ^ 4 - 1570768747177 * (n : ℤ) ^ 3 + 1613191469925 * (n : ℤ) ^ 2 - 846280196028 * (n : ℤ) + 162004328640) * (a (n - 2) : ℤ)
            + 81 * ((n : ℤ) - 4) * (2 * (n : ℤ) - 9) * (13283136 * (n : ℤ) ^ 6 - 185254704 * (n : ℤ) ^ 5 + 1022265212 * (n : ℤ) ^ 4 - 2812725744 * (n : ℤ) ^ 3 + 3970490329 * (n : ℤ) ^ 2 - 2616697419 * (n : ℤ) + 582036840) * (a (n - 3) : ℤ)) ∧
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => 81 / 2 * (9 : ℝ) ^ n) := by
  sorry

end OMA.S_oeis_a212734
