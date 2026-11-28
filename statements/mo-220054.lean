import Mathlib

/-!
# Joint cumulants of characters of the binary cube

Source: R S, https://mathoverflow.net/questions/220054 (CC BY-SA 3.0).
Credit: @connoranderson.

Use the usual partition formula for a joint cumulant under the uniform law.
Only partitions into zero-XOR blocks contribute. For a nonempty tuple the
integer answer is odd exactly when the indices form a minimal zero-sum
family. Equivalently, after fixing any one index, its removal leaves no
nonempty zero-sum subset.
-/

namespace OMA.S_mo_220054

abbrev V (n : ℕ) := Fin n → ZMod 2

noncomputable def walsh {n} (a x : V n) : ℚ := if ∑ i, a i * x i = 0 then 1 else -1

noncomputable def moment {n k} (c : Fin k → V n) (s : Finset (Fin k)) : ℚ :=
  (∑ x : V n, ∏ i ∈ s, walsh (c i) x) / Fintype.card (V n)

def Partitions {k} (π : Finset (Finset (Fin k))) : Prop :=
  ∅ ∉ π ∧ ∀ i : Fin k, ∃! b : Finset (Fin k), b ∈ π ∧ i ∈ b

def Good {n k} (c : Fin k → V n) (π : Finset (Finset (Fin k))) : Prop :=
  Partitions π ∧ ∀ b ∈ π, ∑ i ∈ b, c i = 0

def weight (k : ℕ) : ℤ := (-1 : ℤ)^(k-1) * (k-1).factorial

noncomputable def cumulant {n k} (c : Fin k → V n) : ℚ := by
  classical
  exact ∑ π : Finset (Finset (Fin k)), if Partitions π then
    (weight π.card : ℚ) * ∏ b ∈ π, moment c b else 0

noncomputable def xorSum {n k} (c : Fin k → V n) : ℤ := by
  classical
  exact ∑ π : Finset (Finset (Fin k)), if Good c π then weight π.card else 0

theorem main : ∀ {n k : ℕ} (c : Fin k → V n) (a : Fin k),
    cumulant c = (xorSum c : ℚ) ∧ ((∑ i, c i) ≠ 0 → xorSum c = 0) ∧
    (Odd (xorSum c) ↔ (∑ i, c i) = 0 ∧
      ∀ b : Finset (Fin k), a ∉ b → (∑ i ∈ b, c i) = 0 → b = ∅) := by
  sorry

end OMA.S_mo_220054
