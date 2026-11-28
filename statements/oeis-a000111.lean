import Mathlib

/-!
# A000111: Euler or up/down numbers: e.g.f. sec(x) + tan(x). Also for n >= 2, half the number of alternating permutations on n letters (A001250).

Source: https://oeis.org/A000111
Credit: @whtefox57-hash

Formalized claim (first complete continued-fraction identity on the OEIS page,
Sergei N. Gladkovskii, Nov 14 2011 - Dec 23 2013):

  E.g.f.: tan(x) + sec(x) = 1 + x/U(0);
  U(k) = 4k+1 - x/(2 - x/(4k+3 + x/(2 + x/U(k+1)))).

Standard reading (also noted above `main`): the infinite continued fraction U(0)
is the limit of its finite truncations, and sec(x) is 1/cos(x). The identity is
stated for every real x and every real L to which the truncations converge; where
they do not converge the statement is vacuous. No special case and no strengthening.

Do not prove it here: the theorem body stays `sorry`. A person reviews the
translation before merging.
-/

namespace OMA.S_oeis_a000111

-- Finite truncation at depth `n` of the continued fraction U(k).
-- U(0) is the limit of `Utrunc n 0 x` as n grows; the base case only fixes the tail.
noncomputable def Utrunc : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 0
  | n + 1, k, x =>
    4 * (k : ℝ) + 1 - x / (2 - x / (4 * (k : ℝ) + 3 + x / (2 + x / Utrunc n (k + 1) x)))

-- OEIS A000111 (Gladkovskii): tan(x) + sec(x) = 1 + x/U(0), read as: wherever the
-- truncations of U(0) converge to L, tan(x) + sec(x) equals 1 + x/L. sec(x) = 1/cos(x).
theorem main :
    ∀ x : ℝ, ∀ L : ℝ,
      Filter.Tendsto (fun n => Utrunc n 0 x) Filter.atTop (nhds L) →
      Real.tan x + 1 / Real.cos x = 1 + x / L := by
  sorry

end OMA.S_oeis_a000111
