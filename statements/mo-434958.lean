import Mathlib

/-!
# Conditional linear forms of independent uniform random signs

The finite expectation gives all sign vectors equal probabilities. The dot
product with a uniform sign vector is S below. The two-dimensional example
addresses the question about a positive lower bound for small positive
thresholds. The second assertion gives an explicit dimension-free lower
bound at every threshold smaller than one, and bounds the probability of
the conditioning event. At threshold one there remains a dimension-free lower
bound, obtained from the fourth moment of the centered square of the sign sum.
Above threshold one there is no finite dimension-free
lower bound at fixed correlation smaller than one.

Source: B Merlot, https://mathoverflow.net/questions/434958 (CC BY-SA 4.0).
Credit: @connoranderson (agent: Codex)
-/

namespace OMA.S_mo_434958
abbrev Cube (d : ℕ) := Fin d → Bool
def sign (b : Bool) : ℝ := if b then 1 else -1
def dot {d : ℕ} (u v : Fin d → ℝ) : ℝ := ∑ i, u i*v i
def S {d : ℕ} (u : Fin d → ℝ) (x : Cube d) : ℝ := ∑ i, u i*sign (x i)
noncomputable def avg {d : ℕ} (f : Cube d → ℝ) : ℝ := Finset.univ.expect f
noncomputable def event {d : ℕ} (u : Fin d → ℝ) (t : ℝ) (x : Cube d) : ℝ :=
  if t ≤ S u x then 1 else 0
noncomputable def probability {d : ℕ} (u : Fin d → ℝ) (t : ℝ) : ℝ := avg (event u t)
noncomputable def conditional {d : ℕ} (u v : Fin d → ℝ) (t : ℝ) : ℝ :=
  avg (fun x => S v x * event u t x) / probability u t

theorem main :
    (∃ u v : Fin 2 → ℝ, dot u u=1 ∧ dot v v=1 ∧ dot u v=16/65 ∧
      ∀ t : ℝ, 0<t → t≤1/5 → probability u t=1/2 ∧ conditional u v t= -5/13) ∧
    (∀ (d : ℕ) (u v : Fin d → ℝ) (c t : ℝ), dot u u=1 → dot v v=1 →
      0≤c → c≤dot u v → 0≤t → t<1 →
      (1-t^2)^2/6 ≤ probability u t ∧
      c*t-Real.sqrt (6*(1-c^2))/(1-t^2) ≤ conditional u v t) ∧
    (∀ (d : ℕ) (u v : Fin d → ℝ), dot u u=1 → dot v v=1 →
      1/864 ≤ probability u 1 ∧ -Real.sqrt 864 ≤ conditional u v 1) ∧
    (∀ c t L : ℝ, 0≤c → c<1 → 1<t → ∃ d : ℕ, ∃ u v : Fin d → ℝ,
      dot u u=1 ∧ dot v v=1 ∧ dot u v=c ∧ 0<probability u t ∧ conditional u v t<L) := by
  sorry

end OMA.S_mo_434958
