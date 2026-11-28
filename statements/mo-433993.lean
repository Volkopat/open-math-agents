import Mathlib

/-!
# The average and the minimum enclosing ball of constant-weight binary vectors

Source: AspiringMat, https://mathoverflow.net/questions/433993 (CC BY-SA).
Anton Petrunin discussed sparse families concentrated near one pole and the
concentration phenomenon at positive density. Credit: @connoranderson.
The bound below quantifies the dense regime and is zero for the full layer.
-/
namespace OMA.S_mo_433993
open Finset
abbrev V (d : ℕ) := Fin d → ℝ
abbrev Family (d : ℕ) := Finset (Finset (Fin d))
def bit {d} (s : Finset (Fin d)) (i : Fin d) : ℝ := if i ∈ s then 1 else 0
def sqDist {d} (x y : V d) : ℝ := ∑ i, (x i-y i)^2
noncomputable def avg {d} (S : Family d) (i : Fin d) : ℝ := (∑ s ∈ S, bit s i)/(S.card:ℝ)
def Center {d} (S : Family d) (C : V d) : Prop := ∃ R : ℝ,
  (∀ s ∈ S, sqDist (bit s) C ≤ R) ∧
    ∀ x : V d, ∀ t : ℝ, (∀ s ∈ S, sqDist (bit s) x ≤ t) → R ≤ t

theorem main : ∀ (d k : ℕ) (S : Family d) (C : V d), k<d → S.Nonempty →
    (∀ s ∈ S, s.card=k) → Center S C →
    sqDist (avg S) C ≤ (k:ℝ)*(d-k)/d ∧
    sqDist (avg S) C ≤
      ((d.choose k : ℝ)/(S.card:ℝ)-1) * ((k:ℝ)*(d-k)/((d:ℝ)*(d-1))) := by
  sorry
end OMA.S_mo_433993
