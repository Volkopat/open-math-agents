import Mathlib

/-!
# OEIS A135909: Barker's conjectures for the clique number of the commuting graph of A_n

Source: https://oeis.org/A135909 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A135909 (N. J. A. Sloane, Mar 07 2008), offset 0: Clique number of commuting graph of
alternating group A_n.
Data: 0, 0, 0, 2, 3, 4, 8, 11, 15, 26, 35, 47, 80, ...
Comment: The graph is empty for n = 0, 1 and 2, so a(n) = 0 by convention.
Formula section:
Conjecture: a(n) = a(n-1)+3*a(n-3)-3*a(n-4) for n>6. G.f.: -x^3*(x^6-x^5+2*x^3-x^2-x-2) /
((x-1)*(3*x^3-1)). - Colin Barker, Jul 26 2013

Formalization notes:
* The commuting graph of A_n has the non-identity elements of A_n as vertices, two of them
  adjacent when they commute; this reading gives the listed terms (a(3) = 2, a(4) = 3, a(5) = 4:
  the non-identity elements of A_3, of the Klein group in A_4, of a 5-cycle group in A_5). A
  clique is a set of non-identity elements that commute pairwise, and a(n) is the largest size
  of one (`sSup`; the sizes are bounded by the order of the group). For n = 0, 1, 2 the group is
  trivial, there is no vertex and a(n) = 0, as in the entry.
* The statement is the conjunction of Barker's recurrence (for n > 6, in the integers) and g.f.;
  the identity A(x) = N/D is stated as A * D = N in the formal power series ring over the
  integers (D = (x - 1) (3 x^3 - 1) has constant term 1).
-/

namespace OMA.S_oeis_a135909

open PowerSeries

/-- k is the size of a set of pairwise commuting non-identity elements of A_n. -/
def IsCliqueSize (n k : ℕ) : Prop :=
  ∃ S : Finset (alternatingGroup (Fin n)), S.card = k ∧ (1 : alternatingGroup (Fin n)) ∉ S ∧
    ∀ x ∈ S, ∀ y ∈ S, x * y = y * x

/-- A135909(n): the clique number of the commuting graph of A_n. -/
noncomputable def a (n : ℕ) : ℕ := sSup {k : ℕ | IsCliqueSize n k}

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 6 < n → (a n : ℤ) = a (n - 1) + 3 * a (n - 3) - 3 * a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((X - 1) * (3 * X ^ 3 - 1)) =
      (- X ^ 3 * (X ^ 6 - X ^ 5 + 2 * X ^ 3 - X ^ 2 - X - 2) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a135909
