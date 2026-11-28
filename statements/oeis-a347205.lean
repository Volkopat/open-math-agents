import Mathlib

namespace OMA.S_oeis_a347205

def a347205 : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      let m := n + 1
      if m % 2 = 1 then a347205 (m / 2)
      else
        let h := m / 2
        a347205 h + a347205 (h - 2 ^ padicValNat 2 h)
termination_by n => n
decreasing_by
  · omega
  · omega
  · have := Nat.sub_le ((n + 1) / 2) (2 ^ padicValNat 2 ((n + 1) / 2))
    omega

def wt : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + wt ((n + 1) / 2)

def T347205 : ℕ → ℕ → ℕ
  | 0, k => if k = 1 then 1 else 0
  | n + 1, k =>
      let m := n + 1
      let h := m / 2
      if m % 2 = 1 then
        if k = wt h + 2 then T347205 h (wt h + 1)
        else T347205 h k
      else
        ∑ i ∈ Finset.Icc 1 k, T347205 h i
termination_by n _ => n
decreasing_by
  · omega
  · omega
  · have := Nat.sub_le ((n + 1) / 2) (2 ^ padicValNat 2 ((n + 1) / 2))
    omega

theorem main :
    ∀ n : ℕ,
      a347205 n = T347205 n (wt n + 1) ∧
      a347205 (2 * n) = ∑ k ∈ Finset.Icc 1 (wt n + 1), T347205 n k := by
  sorry

end OMA.S_oeis_a347205
