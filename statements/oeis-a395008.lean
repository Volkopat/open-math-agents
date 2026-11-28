import Mathlib

/-!
# OEIS A395008: records for the minimum spread of three squares

Source: https://oeis.org/A395008, conjecture of Nenad Micic.
Credit: @gblacher2
-/

namespace OMA.S_oeis_a395008

/-- The least `x - z` among representations as `x² + y² + z²` with `x ≥ y ≥ z`. -/
def spread (n : ℕ) : Option ℕ := Id.run do
  let mut best := none
  for z in [0:n.sqrt + 1] do
    let remaining := n - z ^ 2
    for y in [z:(remaining / 2).sqrt + 1] do
      let last := remaining - y ^ 2
      let x := last.sqrt
      if y ≤ x ∧ x ^ 2 = last then
        best := some (min (best.getD (x - z)) (x - z))
  return best

/-- The positive record locations up to `bound`, in increasing order. -/
def recordsThrough (bound : ℕ) : Array ℕ := Id.run do
  let mut largest := 0
  let mut records := #[]
  for k in [1:bound + 1] do
    if let some s := spread k then
      if largest < s then
        largest := s
        records := records.push k
  return records

noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun k => k ∈ recordsThrough k) (n - 1)

theorem main :
    (List.range 12).map (fun i => a (i + 1)) = [1, 4, 10, 16, 37, 58, 64, 130, 148, 232, 256, 445] ∧
      ∀ n : ℕ, 13 ≤ n → a n = 4 * a (n - 5) := by
  sorry

end OMA.S_oeis_a395008
