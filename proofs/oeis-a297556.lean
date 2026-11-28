import OMAStatements.S_oeis_a297556

-- Original Lean proof: @bnb9001.
-- Two appended digits increase the variation by at most 3. Appending 03 attains 3,
-- and any suffix that attains 3 has numerical value at least 3.

namespace OMA_A297556_Proof

open OMA.S_oeis_a297556

def b : ℕ → ℕ
  | 0 => 1
  | 1 => 6
  | 2 => 7
  | n + 3 => 16 * b n + 3

theorem b_pos (n : ℕ) : 0 < b n := by
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | n + 3 => change 0 < 16 * b n + 3; omega

private theorem uv_append (y d : ℕ) (hy : 0 < y) (hd : d < 4) :
    uv (4 * y + d) = (d - y % 4) + uv y := by
  have digits : Nat.digits 4 (4 * y + d) = d :: Nat.digits 4 y := by
    rw [Nat.digits_def' (by decide) (by omega),
      show (4 * y + d) % 4 = d by omega, show (4 * y + d) / 4 = y by omega]
  unfold uv
  rw [digits, Nat.digits_def' (by decide) hy, uvList]

private theorem uv_step (y c d : ℕ) (hy : 0 < y) (hc : c < 4) (hd : d < 4) :
    uv (16 * y + (4 * c + d)) = (d - c) + ((c - y % 4) + uv y) := by
  rw [show 16 * y + (4 * c + d) = 4 * (4 * y + c) + d by omega,
    uv_append _ d (by omega) hd, uv_append y c hy hc, show (4 * y + c) % 4 = c by omega]

theorem uv_b (n : ℕ) : uv (b n) = n := by
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | n + 3 =>
    change uv (16 * b n + (4 * 0 + 3)) = n + 3
    rw [uv_step _ 0 3 (b_pos _) (by decide) (by decide), uv_b n]
    omega
termination_by structural n

private theorem small : ∀ x : Fin 16, 0 < x.val →
    uv x.val < 3 ∧ ∀ n : Fin 3, n.val ≤ uv x.val → b n.val ≤ x.val := by decide

theorem b_min (n x : ℕ) (hx : 0 < x) (hn : n ≤ uv x) : b n ≤ x := by
  rcases Nat.lt_or_ge x 16 with h | h
  · obtain ⟨hu, hm⟩ := small ⟨x, h⟩ hx
    exact hm ⟨n, hn.trans_lt hu⟩ hn
  match n with
  | 0 => change 1 ≤ x; omega
  | 1 => change 6 ≤ x; omega
  | 2 => change 7 ≤ x; omega
  | m + 3 =>
    set y := x / 16
    set c := x % 16 / 4
    set d := x % 4
    have hsplit : x = 16 * y + (4 * c + d) := by omega
    have hy : 0 < y := by omega
    have hstep := uv_step y c d hy (by omega) (by omega)
    rw [← hsplit] at hstep
    have hb := b_min m y hy (by omega)
    change 16 * b m + 3 ≤ x
    by_cases he : y = b m
    · rw [he, uv_b] at hstep
      omega
    · omega
termination_by structural n

theorem a_eq_b (n : ℕ) : a n = (b n : ℤ) := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => decide
  | n + 4 =>
    change a (n + 3) + 16 * a (n + 1) - 16 * a n = (b (n + 4) : ℤ)
    rw [a_eq_b (n + 3), a_eq_b (n + 1), a_eq_b n,
      show b (n + 4) = 16 * b (n + 1) + 3 from rfl, show b (n + 3) = 16 * b n + 3 from rfl]
    push_cast
    ring
termination_by structural n

end OMA_A297556_Proof

open OMA.S_oeis_a297556 OMA_A297556_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a297556.main := by
  intro n
  rw [a_eq_b, Int.toNat_natCast]
  exact ⟨⟨b_pos n, uv_b n⟩, fun x ⟨hx, huv⟩ => b_min n x hx huv.ge⟩
