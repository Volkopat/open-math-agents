import Mathlib

/-!
# Orthogonal vectors on the real ℓᵖ unit sphere

Source: André Porto, MathOverflow 254006, https://mathoverflow.net/questions/254006
(CC BY-SA 4.0). Contribution by @connoranderson.

The vectors have unit ℓᵖ norm and are orthogonal for the usual Euclidean inner
product. In dimension d=m+1 the ℓ¹ distance minimum is 2/(1+√m), strictly below
the stated Schäffer constant 1 when m>1. For each fixed p≠2 the infimum in
dimension d is asymptotic to 2 d^(−|1/p−1/2|); the finite upper bound is attained
by an explicit pair. Porto’s comparison proof also gives the exact planar formula.
-/

namespace OMA.S_mo_254006
open Finset
abbrev V (d : ℕ) := Fin d → ℝ
noncomputable def lp {d : ℕ} (p : ℝ) (u : V d) : ℝ :=
  (∑ i, |u i|^p)^(1/p)
def perp {d : ℕ} (u v : V d) : Prop := ∑ i, u i * v i = 0
noncomputable def distances (d : ℕ) (p : ℝ) : Set ℝ :=
  {s | ∃ u v : V d, lp p u = 1 ∧ lp p v = 1 ∧ perp u v ∧ s = lp p (u-v)}

theorem main :
    (∀ p : ℝ, 1≤p → IsLeast (distances 2 p) (min ((2:ℝ)^(1/p)) ((2:ℝ)^(1-1/p)))) ∧
    (∀ m : ℕ, 0 < m → IsLeast (distances (m+1) 1) (2/(1+Real.sqrt m))) ∧
    (∀ m : ℕ, 1 < m → sInf (distances (m+1) 1) < 1) ∧
    (∀ m : ℕ, 0 < m → distances (m+1) 2 = {Real.sqrt 2}) ∧
    (∀ (m : ℕ) (p : ℝ), 0 < m → 1≤p →
      2/(1+((m+1:ℕ):ℝ)^|1/p-1/2|) ≤ sInf (distances (m+1) p) ∧
      2/(1+(m:ℝ)^|1-p/2|)^(1/p) ∈ distances (m+1) p) ∧
    (∀ p : ℝ, 1≤p → p≠2 → Filter.Tendsto
      (fun m : ℕ => ((m+1:ℕ):ℝ)^|1/p-1/2| * sInf (distances (m+1) p)) Filter.atTop (nhds 2) ∧
      Filter.Tendsto (fun m : ℕ => sInf (distances (m+1) p)) Filter.atTop (nhds 0)) := by
  sorry

end OMA.S_mo_254006
