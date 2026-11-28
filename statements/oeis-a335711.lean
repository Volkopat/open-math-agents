import Mathlib

/-!
# A335711: The number of free polyominoes of width 2 and height n.

Source: https://oeis.org/A335711 (OEIS Foundation, CC BY-SA 4.0)
Credit: @marcusbuffett

Entry (R. J. Mathar, Jun 18 2020), offset 2. Data:
  2, 6, 12, 30, 65, 158, 362, 875, 2064, 4984, 11914, 28764, 69155, 166956, 402372, 971413,
  2343518, 5657754, 13654968, 32966010, 79577189, 192116330, 463786190, 1119678911,
  2703086892, 6525829036, 15754607062, 38034986040, 91824246215, 221683340568, 535190123592
Example: a(2) = 2, bounding box 2 X 2, counts the L-shaped 3-omino and the full block 4-omino.
The formula section states, as conjectures from Colin Barker, Jun 24 2020:
  G.f.: x^2*(2 - 8*x^2 + 2*x^3 - x^4 + x^5 + x^6) / ((1 - x)*(1 - 2*x - x^2)*(1 - 2*x^2 - x^4)).
  a(n) = 3*a(n-1) + a(n-2) - 7*a(n-3) + 3*a(n-4) - a(n-5) + a(n-6) + a(n-7) for n>8.

Conventions (as in statements/oeis-a000105.lean):
* A polyomino is a finite set of cells of `ℤ × ℤ` that is 4-connected: any two cells are
  joined by a chain of cells of the set, consecutive ones sharing an edge.
* It has width `w` when its cells occupy exactly the `w` consecutive columns
  `x₀, ..., x₀ + w - 1` (all cells have first coordinate in that range, and the first and the
  last column both contain a cell); height `h` is defined in the same way with rows.
* Free polyominoes are polyominoes up to lattice isometries: translations combined with
  rotations and reflections (the group `D_4`).
* `a n` is the number of free polyominoes with a representative of width 2 and height `n`,
  that is, the number of classes of such polyominoes under lattice isometries.
* Offset 2. The definition also gives a(0) = 0 and a(1) = 1 (the domino), while the g.f.
  starts at x^2, so the g.f. is stated for the sequence that is 0 below the offset, as an
  identity of formal power series over ℤ with the denominator cleared (the denominator has
  constant coefficient 1). The recurrence is stated over ℤ.
-/

namespace OMA.S_oeis_a335711

/-- Two cells share an edge. -/
def gridAdj (p q : ℤ × ℤ) : Prop :=
  (p.1 = q.1 ∧ Int.natAbs (p.2 - q.2) = 1) ∨
  (p.2 = q.2 ∧ Int.natAbs (p.1 - q.1) = 1)

/-- Any two cells of `S` are joined by a chain of edge-adjacent cells of `S`. -/
def IsConnected (S : Finset (ℤ × ℤ)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S,
    Relation.ReflTransGen (fun p q => p ∈ S ∧ q ∈ S ∧ gridAdj p q) a b

/-- The cells of `S` occupy exactly the `w` consecutive columns `x₀, ..., x₀ + w - 1`. -/
def HasWidth (S : Finset (ℤ × ℤ)) (w : ℕ) : Prop :=
  ∃ x₀ : ℤ, (∀ p ∈ S, x₀ ≤ p.1 ∧ p.1 < x₀ + w) ∧
    (∃ p ∈ S, p.1 = x₀) ∧ (∃ p ∈ S, p.1 = x₀ + w - 1)

/-- The cells of `S` occupy exactly the `h` consecutive rows `y₀, ..., y₀ + h - 1`. -/
def HasHeight (S : Finset (ℤ × ℤ)) (h : ℕ) : Prop :=
  ∃ y₀ : ℤ, (∀ p ∈ S, y₀ ≤ p.2 ∧ p.2 < y₀ + h) ∧
    (∃ p ∈ S, p.2 = y₀) ∧ (∃ p ∈ S, p.2 = y₀ + h - 1)

/-- `T` is the image of `S` under a lattice isometry (translation plus an element of `D_4`). -/
def GridSymEq (S T : Finset (ℤ × ℤ)) : Prop :=
  ∃ (dx dy sx sy : ℤ) (swap : Bool),
    (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧
    T = S.image (fun p =>
      if swap then (dx + sx * p.2, dy + sy * p.1)
      else (dx + sx * p.1, dy + sy * p.2))

/-- Polyominoes of width 2 and height `n`. -/
def WidthTwo (n : ℕ) : Type :=
  {S : Finset (ℤ × ℤ) // IsConnected S ∧ HasWidth S 2 ∧ HasHeight S n}

/-- The number of free polyominoes of width 2 and height `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card (Quot (fun (S T : WidthTwo n) => GridSymEq S.1 T.1))

/-- The conjectured recurrence and generating function of OEIS A335711. -/
theorem main :
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 3 * a (n - 1) + a (n - 2) - 7 * a (n - 3) + 3 * a (n - 4) - a (n - 5) +
        a (n - 6) + a (n - 7)) ∧
    (let x : PowerSeries ℤ := PowerSeries.X
     (1 - x) * (1 - 2 * x - x ^ 2) * (1 - 2 * x ^ 2 - x ^ 4) *
        PowerSeries.mk (fun n => if 2 ≤ n then (a n : ℤ) else 0) =
      x ^ 2 * (2 - 8 * x ^ 2 + 2 * x ^ 3 - x ^ 4 + x ^ 5 + x ^ 6)) := by
  sorry

end OMA.S_oeis_a335711
