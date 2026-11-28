import FormalConjectures.Mathoverflow.«75792»

/-! Selfridge: a number reachable with k ones satisfies m^3 ≤ 3^k. In the add case a summand 1
(or 2) is absorbed by `one`; otherwise x + y ≤ x * y. -/

open Mathoverflow75792

theorem OMA.solution : type_of% @Mathoverflow75792.complexity_three_pow := by
  intro n hn
  refine (Reachable.pow 3 n (by decide) hn).complexity_eq fun k hk hr => ?_
  have one (y B : ℕ) (h : (y + 1) ^ 3 ≤ B * 3) : (y + 2) ^ 3 ≤ B * 9 := by
    rcases y with _ | _ | y <;> first | omega | nlinarith [Nat.zero_le (y ^ 3), Nat.zero_le (y ^ 2)]
  have key : ∀ {m k}, Reachable m k → m ^ 3 ≤ 3 ^ k := by
    intro m k h
    induction h with
    | one => decide
    | mul _ _ h1 h2 => rw [mul_pow, pow_add]; exact Nat.mul_le_mul h1 h2
    | @add x y a b hx hy h1 h2 =>
      obtain ⟨x, a, rfl, rfl⟩ := hx.dec
      obtain ⟨y, b, rfl, rfl⟩ := hy.dec
      have := Nat.one_le_pow a 3 (by decide)
      have := Nat.one_le_pow b 3 (by decide)
      rw [pow_add 3 (a + 1), pow_succ 3 a, pow_succ 3 b] at *
      generalize 3 ^ a = A at *
      generalize 3 ^ b = B at *
      rcases x with _ | x
      · nlinarith [one y B h2]
      rcases y with _ | y
      · nlinarith [one _ A h1]
      nlinarith [Nat.mul_le_mul h1 h2, Nat.pow_le_pow_left (show x + 1 + 1 + (y + 1 + 1) ≤ (x + 1 + 1) * (y + 1 + 1) by nlinarith) 3]
  exact absurd (key hr) (by rw [← pow_mul]; exact not_le.2 (Nat.pow_lt_pow_right (by decide) (by omega)))
