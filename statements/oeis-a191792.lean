import Mathlib

namespace A191792

abbrev Word := List Bool

/-- Concatenate two objects with a prescribed total length, using every possible cut. -/
def joinWords (n : ℕ) (left right : Fin (n+1) → List Word)
    (join : Word → Word → Word) : List Word :=
  (List.finRange (n+1)).flatMap fun i =>
    ((left i).product (right ⟨n-i.val, by omega⟩)).map fun uv => join uv.1 uv.2

/-- An initial long arch has nonempty interior. After the matching down-step any
avoiding excursion may follow. A long arch starts with UU and ends with DD. -/
def longTail (n : ℕ) (e : Fin (n+1) → List Word) : List Word :=
  joinWords n (fun i => if i.val = 0 then [] else e i) e
    (fun u v => true :: (u ++ false :: v))

/-- All length-n Dyck excursions avoiding UDUD, enumerated by their first-return
arches. There are four disjoint cases: empty, one short arch, an initial long arch,
or an initial short arch immediately followed by a long arch. Here true denotes U. -/
def excursions (n : ℕ) : List Word :=
  (if n = 0 then [[]] else []) ++
  (if n = 2 then [[true, false]] else []) ++
  (if h : 2 ≤ n then longTail (n-2) (fun i => excursions i.val) else []) ++
  (if h : 4 ≤ n then
    (longTail (n-4) (fun i => excursions i.val)).map (fun w => true :: false :: w)
   else [])
termination_by n
decreasing_by all_goals have := i.isLt; omega

/-- A prefix is complete, or has a unique first unmatched up-step, preceded
by an excursion and followed by a translated avoiding prefix. An unmatched up-step
cannot participate in UDUD. Every enumerated prefix extends to an avoiding excursion
by appending UU and then down-steps until it reaches zero. -/
def prefixes (n : ℕ) : List Word :=
  excursions n ++ (if _h : 1 ≤ n then
    joinWords (n-1) (fun i => excursions i.val) (fun i => prefixes i.val)
      (fun u v => u ++ true :: v)
  else [])
termination_by n
decreasing_by have := i.isLt; omega

noncomputable section

open PowerSeries

def wordSeries (f : ℕ → List Word) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((f n).length : ℚ)

def excSeries := wordSeries excursions

def prefixSeries := wordSeries prefixes

end
end A191792

namespace OMA.S_oeis_a191792

open A191792

/-- A rational power series is D-finite if it satisfies a homogeneous linear
differential equation over the rational polynomials with nonzero leading coefficient. -/
def DFinite (f : PowerSeries ℚ) : Prop :=
  ∃ (k : ℕ) (p : Fin (k+1) → Polynomial ℚ), p (Fin.last k) ≠ 0 ∧
    ∑ i, (p i : PowerSeries ℚ) * ((PowerSeries.derivative ℚ)^[i.val]) f = 0

/-- The path count is coerced before any signed arithmetic. -/
def a (n : ℕ) : ℚ := (prefixes n).length

/-- R. J. Mathar's conjecture for OEIS A191792. The length-eight recurrence is included. -/
theorem main :
    DFinite prefixSeries ∧
    (∀ n : ℕ, 8 ≤ n →
      ((n : ℚ) + 1) * a n - 2 * a (n-1) + 2 * (1-(n : ℚ)) * a (n-2)
        - 4 * a (n-3) + 5 * (3-(n : ℚ)) * a (n-4) + 4 * a (n-5)
        + 2 * (5-(n : ℚ)) * a (n-6) + 2 * a (n-7) + ((n : ℚ)-7) * a (n-8) = 0) := by
  sorry

end OMA.S_oeis_a191792
