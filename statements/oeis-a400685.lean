import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# The exponential growth rate of equal-area, equal-perimeter square cuts

The source normalizes each cut to a bottom-to-top unit walk. Equal perimeters
give length 4n and antipodal endpoints. Closing along the left boundary makes
the signed sum of x times the vertical increment the area on the left.
In this normalization the surviving square symmetries are the identity,
half-turn, horizontal reflection and vertical reflection. The empty cut counts
once at n = 0.

Source: Felix Huber, https://oeis.org/A400685 (OEIS, CC BY-SA 4.0).
Formalization by @pmaster with Codex.
-/

namespace OMA.S_oeis_a400685

abbrev Point := ℤ × ℤ
abbrev Dir := Fin 4
abbrev Code (n : ℕ) := Fin (2*n+1) × (Fin (4*n) → Dir)

/-- Directions 0, 1, 2, and 3 mean up, right, down, and left. -/
def delta (d : Dir) : Point :=
  if d = 0 then (0, 1) else if d = 1 then (1, 0)
  else if d = 2 then (0, -1) else (-1, 0)

def finish (p : Point) (w : List Dir) : Point :=
  w.foldl (fun x d => x + delta d) p

def after (p : Point) : List Dir → List Point
  | [] => []
  | d :: w => (p + delta d) :: after (p + delta d) w

def trail (p : Point) (w : List Dir) : List Point := p :: after p w

def integral (p : Point) : List Dir → ℤ
  | [] => 0
  | d :: w => p.1 * (delta d).2 + integral (p + delta d) w

def inside (n : ℕ) (z : Point) : Prop :=
  0 < z.1 ∧ z.1 < 2*(n:ℤ) ∧ 0 < z.2 ∧ z.2 < 2*(n:ℤ)

def startPt (q : ℕ) : Point := ((q:ℤ), 0)
def endPt (n q : ℕ) : Point := (2*(n:ℤ) - q, 2*(n:ℤ))

def IsCut (n q : ℕ) (w : List Dir) : Prop :=
  0 < q ∧ q < 2*n ∧ w.length = 4*n ∧
  finish (startPt q) w = endPt n q ∧
  (trail (startPt q) w).Nodup ∧
  (∀ z ∈ trail (startPt q) w, z = startPt q ∨ z = endPt n q ∨ inside n z) ∧
  integral (startPt q) w = 2*(n:ℤ)^2

noncomputable def cuts (n : ℕ) : Finset (Code n) := by
  classical
  exact Finset.univ.filter (fun c => IsCut n c.1.val (List.ofFn c.2))

def mirrorDir (d : Dir) : Dir :=
  if d = 1 then 3 else if d = 3 then 1 else d

/-- After reorienting the reflected path bottom-to-top, the half-turn reverses
its word. Vertical reflection mirrors its steps. Horizontal reflection does both. -/
def orbit {n : ℕ} (c : Code n) : Finset (Code n) :=
  {c, (c.1, fun i => c.2 i.rev),
   (c.1.rev, fun i => mirrorDir (c.2 i)),
   (c.1.rev, fun i => mirrorDir (c.2 i.rev))}

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 1 else ((cuts n).image orbit).card

theorem main : ∃ c : ℝ, Filter.Tendsto
    (fun n : ℕ => (a n : ℝ) ^ ((1 : ℝ) / n)) Filter.atTop (nhds c) := by
  sorry

end OMA.S_oeis_a400685
