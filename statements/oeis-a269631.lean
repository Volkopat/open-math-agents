import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Basic

/-!
# Greedy permutation using the previous decimal length as a substring

Source: OEIS A269631, https://oeis.org/A269631, OEIS Foundation,
CC BY-SA 4.0. The zero-based function a below sends index 0 to the source's
a(1)=0. The digit list for zero is [0]. Mathlib places the least significant
digit first: reversing both words preserves the contiguous-substring test.
-/

namespace OMA.S_oeis_a269631

def digits (n : ℕ) := if n=0 then [0] else Nat.digits 10 n

def eligible (seen : Finset ℕ) (prev x : ℕ) : Prop :=
  x ∉ seen ∧ (digits (digits prev).length).IsInfix (digits x)

noncomputable def next (seen : Finset ℕ) (prev : ℕ) : ℕ := by
  classical
  exact if h : ∃ x, eligible seen prev x then Nat.find h else 0

noncomputable def state : ℕ → ℕ × Finset ℕ
  | 0 => (0,{0})
  | n+1 =>
    let (v,seen) := state n
    let w := next seen v
    (w,insert w seen)

noncomputable def a (n : ℕ) : ℕ := (state n).1

theorem main : Function.Bijective a := by
  sorry

end OMA.S_oeis_a269631
