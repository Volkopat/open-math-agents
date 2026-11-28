import Mathlib.Data.Nat.Factorization.Basic

/-!
# OEIS A400411 — two conjectures on cycles in winner-first War

Source: https://oeis.org/A400411
Daniel Okwor, *Endless Games of War*, Conjectures 6.14 and 6.9,
https://doi.org/10.5281/zenodo.22957685
Formalization: @pblivin0x.

The fronts of the two lists play. Ranks 1 through n occur once each, so there are no ties.
Any ordered pair of piles of the two specified sizes is obtained by an ordinary alternating deal.
The move fixes a terminal state, which is explicitly excluded from every cycle.

The source characterizes Theorem-3 type by turns won in alternating runs of one fixed
power-of-two length (Okwor, Section 2; Spivey, p. 752). The first assertion restricts
the sizes of non-Theorem-3 cycles entered from ordinary deals. The second uses all legal
live cycles, their least positive period, and the largest power of two dividing n.
-/

namespace OMA.S_oeis_a400411

abbrev Position := List ℕ × List ℕ

def legal (n : ℕ) (s : Position) : Prop :=
  let cards := s.1 ++ s.2
  cards.length = n ∧ (List.range' 1 n).all (fun x => cards.count x == 1) = true

def ordinary (n : ℕ) (s : Position) : Prop :=
  legal n s ∧ s.1.length = (n + 1) / 2 ∧ s.2.length = n / 2

def live (s : Position) : Bool := !s.1.isEmpty && !s.2.isEmpty

def leftWins (s : Position) : Bool := decide (s.1.headD 0 > s.2.headD 0)

def move : Position → Position
  | (a :: as, b :: bs) =>
    if a > b then (as ++ [a,b], bs) else (as, bs ++ [b,a])
  | s => s

def after : ℕ → Position → Position
  | 0, s => s
  | t+1, s => after t (move s)

/-- Determinism and absorbing terminal states make a live return a live cycle. -/
def returns (s : Position) (p : ℕ) : Prop := live s = true ∧ 0 < p ∧ after p s = s

def leastPeriod (s : Position) (p : ℕ) : Prop :=
  returns s p ∧ ∀ q : ℕ, 0 < q → q < p → after q s ≠ s

/-- A complete run beginning on move i+1, with the opposite winner on both sides. -/
def completeRun (s : Position) (i l : ℕ) : Prop :=
  let win := fun t => leftWins (after t s)
  0 < l ∧ win i ≠ win (i+1) ∧ (∀ j : Fin l, win (i+1+j.val) = win (i+1)) ∧
    win (i+1+l) ≠ win (i+1)

/-- On a live cycle this is independent of the phase at which the cycle is observed. -/
def spiveyType (s : Position) : Prop :=
  ∃ k : ℕ, ∀ i l : ℕ, completeRun s i l → l = 2^k

def listedSize (n : ℕ) : Prop :=
  ∃ m v : ℕ, 7 ≤ m ∧ m % 4 = 3 ∧ 1 ≤ v ∧ n = m * 2^v

theorem main :
    (∀ (n : ℕ) (d : Position) (t p : ℕ), ordinary n d → returns (after t d) p →
      ¬spiveyType (after t d) → listedSize n) ∧
    (∀ (n : ℕ) (s : Position) (p : ℕ), legal n s → leastPeriod s p →
      n + 2^(n.factorization 2) ∣ p) := by sorry

end OMA.S_oeis_a400411
