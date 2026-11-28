import OMAStatements.S_oeis_a267270

namespace OMA.A267270Proof
open OMA.S_oeis_a267270

def P (t : ℕ) (x : ℤ) : Bool :=
  if t = 0 then (if x = 0 then true else false)
  else if t % 2 = 1 then (if 2 * x = 1 - t then false else true)
  else (if 2 * x = -t ∨ 2 * x = 2 - t then true else false)

theorem S (t : ℕ) : ∀ x, state t x = P t x := by
  induction t with
  | zero => intro x; simp [state, P]
  | succ t ih =>
    intro x
    simp only [state, ih, rule, P]
    push_cast
    split_ifs <;> first | rfl | (exfalso; omega)

theorem R (N : ℕ) : ∑ k ∈ Finset.range (N + 1), (10 : ℚ) ^ (N - k) = (10 ^ (N + 1) - 1) / 9 := by
  have := Finset.sum_range_reflect (fun k => (10 : ℚ) ^ k) (N + 1)
  simp only [Nat.add_sub_cancel] at this
  rw [this, geom_sum_eq (by norm_num)]
  norm_num

theorem O (n : ℕ) (h : Odd n) : (a n : ℚ) = (10 ^ (2 * n + 1) - 9 * 10 ^ ((3 * n - 1) / 2) - 1) / 9 := by
  obtain ⟨m, rfl⟩ := h
  simp only [a, S]
  push_cast
  rw [Finset.sum_congr rfl (g := fun k => (10 : ℚ) ^ (2 * (2 * m + 1) - k) - if k = m + 1 then 10 ^ (3 * m + 1) else 0),
    Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (by simp; omega), R,
    show (3 * (2 * m + 1) - 1) / 2 = 3 * m + 1 by omega]
  · ring
  · intro k _
    simp only [P]
    split_ifs <;> first | (exfalso; omega) | contradiction | simp | (rw [show 2 * (2 * m + 1) - k = 3 * m + 1 by omega]; ring)

theorem E (n : ℕ) (h : Even n) (hn : 0 < n) : a n = 1100 * 10 ^ (3 * n / 2 - 3) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = 2 * (p + 1) := ⟨n / 2 - 1, by have := Nat.even_iff.1 h; omega⟩
  simp only [a, S]
  rw [Finset.sum_eq_add (p + 1) (p + 2) (by omega)]
  · simp only [P]
    split_ifs <;> first | (exfalso; omega) | contradiction | skip
    rw [show 2 * (2 * (p + 1)) - (p + 1) = 3 * p + 3 by omega, show 2 * (2 * (p + 1)) - (p + 2) = 3 * p + 2 by omega,
      show 3 * (2 * (p + 1)) / 2 - 3 = 3 * p by omega]
    ring
  · intro k _ hk
    simp only [P]
    split_ifs <;> first | (exfalso; omega) | contradiction | rfl
  · intro h; simp at h; omega
  · intro h; simp at h; omega

end OMA.A267270Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a267270.main := ⟨OMA.A267270Proof.O, OMA.A267270Proof.E⟩
