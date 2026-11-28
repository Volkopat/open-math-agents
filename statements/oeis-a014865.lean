import Mathlib

/-!
# A014865: Numbers k that divide s(k), where s(1)=1, s(j)=15*s(j-1)+j.

Source: https://oeis.org/A014865
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a014865

def s : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 15 * s (n + 1) + (n + 2)

def IsTerm (k : ℕ) : Prop :=
  0 < k ∧ k ∣ s k

theorem main :
    (∀ k : ℕ, IsTerm k → Odd k) ∧
    (∀ k : ℕ, IsTerm k → 7 < k → ¬ k.Prime) ∧
    (∀ k : ℕ, IsTerm k → 1 < k → 3 ∣ k ∨ 5 ∣ k ∨ 7 ∣ k) := by
  sorry

end OMA.S_oeis_a014865
