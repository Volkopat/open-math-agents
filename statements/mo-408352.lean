import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Source: https://mathoverflow.net/questions/408352 -/

open scoped BigOperators

namespace OMA.S_mo_408352

def evenParity (L : ℕ) (bits : ℕ → ZMod 2) : ZMod 2 :=
  ∑ i ∈ Finset.range L, if i % 2 = 0 then bits i else 0

def reachable (L : ℕ) (bits : ℕ → ZMod 2) : Prop :=
  ∃ press : ℕ → ZMod 2, ∀ i : ℕ, i < L →
    bits i + (if i = 0 then 0 else press (i - 1)) +
      (if i + 1 < L then press (i + 1) else 0) = 1

theorem main :
    (∀ (n : ℕ) (bits : ℕ → ZMod 2), evenParity (4 * n + 1) bits = 1 →
      reachable (4 * n + 1) bits) ∧
    (∀ (n : ℕ) (bits : ℕ → ZMod 2), evenParity (4 * n + 3) bits = 0 →
      reachable (4 * n + 3) bits) := by
  sorry

end OMA.S_mo_408352
