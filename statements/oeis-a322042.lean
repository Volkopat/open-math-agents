import Mathlib

/-!
# A322042: Maximum edge-distance of a point in the quotient graph E/nE from the origin (see A322041 for further information).

Source: https://oeis.org/A322042
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

The entry's FORMULA section states (offset 1):
  Conjectures from Colin Barker, Dec 06 2018: (Start)
  G.f. = x(1+x)/(1-x-x^3+x^4) [Simplified by N. J. A. Sloane, Dec 06 2018]
  a(n) = a(n-1) + a(n-3) - a(n-4) for n>4.
  (End)
  Conjecture: a(n) = n - ceiling(n/3) = A004523(n).
The last conjecture is unsigned in the entry; the revision history shows it was added by
N. J. A. Sloane on Dec 06 2018 (the cross-reference A004523 was added by R. J. Mathar on
Dec 11 2018). A322041 also says that the largest k with T(n,k) nonzero is A322042(n), which is
conjecturally n - ceiling(n/3).

Definition (from A322041): E is the standard triangular 6-valent grid in the plane, regarded as a
graph whose vertices are the Eisenstein integers r + s*omega (omega = exp(2*Pi*i/3)), two of
them adjacent when they differ by a unit. The units are +-1, +-omega, +-omega^2 = -+(1 + omega),
i.e. in coordinates (r, s) the six steps (+-1, 0), (0, +-1), +-(1, 1). The quotient graph E/nE
has as vertices the classes of E modulo nE, i.e. ZMod n × ZMod n, two classes adjacent when
their difference is the class of a unit. a(n) is the maximum, over all vertices, of the graph
distance from the class of 0 (the largest k with T(n,k) nonzero in A322041).

Modelling choices:
* The quotient graph is the Mathlib `SimpleGraph` obtained with `SimpleGraph.fromRel`, which drops
  loops and identifies multiple edges; neither affects graph distances.
* `a n` is the supremum over the finite vertex set (n >= 1) of `SimpleGraph.dist 0 v`. The value
  `a 0` (ZMod 0 = ℤ, an infinite graph) is never used: the recurrence is stated for n > 4 and the
  closed form for n >= 1, as in the source, and the g.f. below has constant coefficient 0.
* The g.f. With the entry's offset 1 the g.f. is Sum_{n>=1} a(n) x^n = x^2 + 2x^3 + 2x^4 + ...
  (a(1) = 0, a(2) = 1). The displayed simplified form x(1+x)/(1-x-x^3+x^4) expands to
  x + 2x^2 + 2x^3 + ..., i.e. it is the g.f. of the data list indexed from 0, and is off from
  the offset-1 g.f. by a factor x. The revision history shows how: Barker's original g.f.
  (Dec 06 2018) was x^2*(1 + x - 10*x^13 + x^14 + 9*x^16) / ((1 - x)^2*(1 + x + x^2)), computed
  while the DATA line still contained an erroneous repetition; after the data were corrected it
  was replaced by the simplified x(1+x)/(1-x-x^3+x^4), dropping the factor x. Since
  (1 - x)^2 (1 + x + x^2) = 1 - x - x^3 + x^4, Barker's x^2 factor with the corrected data gives
  x^2(1+x)/(1-x-x^3+x^4). This file states the g.f. with the entry's offset, as an identity
  of formal power series over ℚ:
  (Sum_{n>=1} a(n) x^n) * (1 - x - x^3 + x^4) = x^2 (1 + x).
  (Read literally with offset 1, the displayed x(1+x)/(...) would claim a(1) = 1, contradicting
  a(1) = 0 in the DATA line; equivalently, the displayed form is Sum_{n>=1} a(n) x^(n-1).)
* The recurrence is cast to ℤ because of the minus sign; ceiling(n/3) is `⌈(n : ℚ) / 3⌉`.
-/

namespace OMA.S_oeis_a322042

/-- The six Eisenstein units ±1, ±ω, ±ω² written in coordinates (r, s) for r + sω, reduced
modulo n. -/
def units (n : ℕ) : Set (ZMod n × ZMod n) :=
  {(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)}

/-- The quotient graph E/nE: classes are adjacent when they differ by the class of a unit. -/
def graph (n : ℕ) : SimpleGraph (ZMod n × ZMod n) :=
  SimpleGraph.fromRel fun x y => y - x ∈ units n

/-- A322042: the maximum edge-distance of a vertex of E/nE from the origin. -/
noncomputable def a (n : ℕ) : ℕ :=
  ⨆ v : ZMod n × ZMod n, (graph n).dist 0 v

/-- Barker's g.f. (with the entry's offset 1) and recurrence, and Sloane's conjectured closed
form n - ceiling(n/3). -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        (1 - PowerSeries.X - PowerSeries.X ^ 3 + PowerSeries.X ^ 4) =
      PowerSeries.X ^ 2 * (1 + PowerSeries.X) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = a (n - 1) + a (n - 3) - a (n - 4)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℤ) = n - ⌈(n : ℚ) / 3⌉) := by
  sorry

end OMA.S_oeis_a322042
