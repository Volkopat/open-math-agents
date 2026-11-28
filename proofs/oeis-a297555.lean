import OMAStatements.S_oeis_a297555

-- Problem: A297555, least positive integer with base-4 down-variation n (Kimberling's conjecture).
-- b(n+3) = 16 b(n) + 12 (append digits 3,0); two appended digits add at most 3 to the down-variation.
-- Credit: @bnb9001

namespace OMA_A297555_Proof

open OMA.S_oeis_a297555

def b : ℕ → ℕ
  | 0 => 1
  | 1 => 4
  | 2 => 8
  | 3 => 12
  | (n + 4) => 16 * b (n + 1) + 12

theorem b_pos (n : ℕ) : 0 < b n := by
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | (n + 4) => show 0 < 16 * b (n + 1) + 12; omega

theorem b_mod (n : ℕ) (hn : 1 ≤ n) : b n % 4 = 0 := by
  match n, hn with
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | (n + 4), _ => show (16 * b (n + 1) + 12) % 4 = 0; omega

theorem digits_two (y c d : ℕ) (hy : 0 < y) (hc : c < 4) (hd : d < 4) :
    Nat.digits 4 (16 * y + (4 * c + d)) = d :: c :: Nat.digits 4 y := by
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (16 * y + (4 * c + d)) % 4 = d := by omega
  have h2 : (16 * y + (4 * c + d)) / 4 = 4 * y + c := by omega
  rw [h1, h2, Nat.digits_def' (by norm_num) (by omega)]
  have h3 : (4 * y + c) % 4 = c := by omega
  have h4 : (4 * y + c) / 4 = y := by omega
  rw [h3, h4]

theorem dv_step (y c d : ℕ) (hy : 0 < y) (hc : c < 4) (hd : d < 4) :
    dv (16 * y + (4 * c + d)) = (c - d) + ((y % 4 - c) + dv y) := by
  unfold dv
  rw [digits_two y c d hy hc hd, Nat.digits_def' (by norm_num) hy, dvList, dvList]

theorem dv_lt16 (x : ℕ) (h0 : 0 < x) (h16 : x < 16) : dv x = x / 4 - x % 4 := by
  unfold dv
  rcases Nat.lt_or_ge x 4 with h4 | h4
  · rw [Nat.digits_def' (by norm_num) h0, show x / 4 = 0 by omega, Nat.digits_zero, dvList]
    omega
  · rw [Nat.digits_def' (by norm_num) h0, Nat.digits_def' (by norm_num) (by omega : 0 < x / 4),
      show x / 4 / 4 = 0 by omega, Nat.digits_zero, dvList, dvList]
    rw [Nat.mod_eq_of_lt (show x / 4 < 4 by omega)]; omega

theorem dv_b (n : ℕ) : dv (b n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [show b 0 = 1 from rfl, dv_lt16 1 (by norm_num) (by norm_num)]
    | 1, _ => rw [show b 1 = 4 from rfl, dv_lt16 4 (by norm_num) (by norm_num)]
    | 2, _ => rw [show b 2 = 8 from rfl, dv_lt16 8 (by norm_num) (by norm_num)]
    | 3, _ => rw [show b 3 = 12 from rfl, dv_lt16 12 (by norm_num) (by norm_num)]
    | (n + 4), ih =>
      rw [show b (n + 4) = 16 * b (n + 1) + (4 * 3 + 0) from rfl,
        dv_step _ 3 0 (b_pos _) (by norm_num) (by norm_num), ih (n + 1) (by omega),
        b_mod (n + 1) (by omega)]
      omega

theorem b_min : ∀ n x, 0 < x → n ≤ dv x → b n ≤ x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx hn
    have b0 : b 0 = 1 := rfl
    have b1 : b 1 = 4 := rfl
    have b2 : b 2 = 8 := rfl
    have b3 : b 3 = 12 := rfl
    rcases Nat.lt_or_ge x 16 with hx16 | hx16
    · rw [dv_lt16 x hx hx16] at hn
      have : n ≤ 3 := by omega
      interval_cases n <;> omega
    · set y := x / 16 with hy
      set c := x % 16 / 4 with hc
      set d := x % 4 with hd
      have hxyd : x = 16 * y + (4 * c + d) := by omega
      have hy0 : 0 < y := by omega
      have hc4 : c < 4 := by omega
      have hd4 : d < 4 := by omega
      rcases Nat.lt_or_ge n 4 with hn4 | hn4
      · interval_cases n <;> omega
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
        have hstep := dv_step y c d hy0 hc4 hd4
        rw [← hxyd] at hstep
        have hy4 := Nat.mod_lt y (show 4 > 0 by norm_num)
        have hy_ge : m + 1 ≤ dv y := by omega
        have hb := ih (m + 1) (by omega) y hy0 hy_ge
        show 16 * b (m + 1) + 12 ≤ x
        rcases Nat.lt_or_ge (b (m + 1)) y with hlt | hge
        · omega
        · have hyeq : y = b (m + 1) := le_antisymm hge hb
          have hmod : y % 4 = 0 := by rw [hyeq]; exact b_mod _ (by omega)
          have hdvy : dv y = m + 1 := by rw [hyeq]; exact dv_b _
          rw [hmod, hdvy] at hstep
          omega

theorem a_eq_b : ∀ n, a n = (b n : ℤ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => decide
    | (n + 5), ih =>
      show a (n + 4) + 16 * a (n + 2) - 16 * a (n + 1) = (b (n + 5) : ℤ)
      rw [ih (n + 4) (by omega), ih (n + 2) (by omega), ih (n + 1) (by omega)]
      have h5 : b (n + 5) = 16 * b (n + 2) + 12 := rfl
      have h4 : b (n + 4) = 16 * b (n + 1) + 12 := rfl
      rw [h5, h4]; push_cast; ring

end OMA_A297555_Proof

open OMA.S_oeis_a297555 OMA_A297555_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a297555.main := by
  intro n
  rw [a_eq_b, Int.toNat_natCast]
  exact ⟨⟨b_pos n, dv_b n⟩, fun x ⟨hx, hdv⟩ => b_min n x hx hdv.ge⟩
