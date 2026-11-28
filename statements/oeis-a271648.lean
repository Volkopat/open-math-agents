import Mathlib

/-!
# OEIS A271648: Barker's conjectures for the permutations containing 2143...(2n)(2n-1)

Source: https://oeis.org/A271648 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A271648 (Nathaniel Shar, Apr 11 2016), offset 0: Number of permutations in S_{2*n+3}
containing the pattern 2143...(2n)(2n-1).
Data: 6, 119, 2279, 18042, 83921, 284428, ...
Formula section:
Conjectures from Colin Barker, Apr 11 2016: (Start)
a(n) = 7*a(n-1)-21*a(n-2)+35*a(n-3)-35*a(n-4)+21*a(n-5)-7*a(n-6)+a(n-7) for n>6.
G.f.: (6+77*x+1572*x^2+4378*x^3+1531*x^4+137*x^5-22*x^6+x^8) / (1-x)^7.
(End)

Formalization notes:
* The pattern 2143...(2n)(2n-1) of length 2n, 0-based, sends j to j + 1 for even j and to j - 1
  for odd j (`pat`). A permutation s of Fin m contains a pattern p of length k when some strictly
  increasing f : Fin k -> Fin m makes s o f order-isomorphic to p (`Contains`).
* For n = 0 the pattern is empty and every permutation of S_3 contains it: a(0) = 6, as in the
  entry; a(1) = 119 = 5! - 1 (the permutations of S_5 containing 21).
* The statement is the conjunction of Barker's recurrence (for n > 6, in the integers) and g.f.;
  the identity A(x) = N/D is stated as A * D = N in the formal power series ring over the
  integers.
-/

namespace OMA.S_oeis_a271648

open PowerSeries

/-- The pattern 2143...(2n)(2n-1), 0-based. -/
def pat (n : ℕ) (j : Fin (2 * n)) : ℕ := if (j : ℕ) % 2 = 0 then j + 1 else j - 1

/-- s contains the pattern p (of length k). -/
def Contains {m k : ℕ} (s : Equiv.Perm (Fin m)) (p : Fin k → ℕ) : Prop :=
  ∃ f : Fin k → Fin m, StrictMono f ∧ ∀ a b : Fin k, p a < p b ↔ s (f a) < s (f b)

/-- A271648(n): the number of permutations of S_{2n+3} containing the pattern. -/
noncomputable def a (n : ℕ) : ℕ := {s : Equiv.Perm (Fin (2 * n + 3)) | Contains s (pat n)}.ncard

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 7) =
      (6 + 77 * X + 1572 * X ^ 2 + 4378 * X ^ 3 + 1531 * X ^ 4 + 137 * X ^ 5 - 22 * X ^ 6 + X ^ 8 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a271648
