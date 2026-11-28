import OMAStatements.S_oeis_a297554

-- Problem: A297554, least positive integer with base-4 total variation n (Kimberling's conjecture).
-- b(n+4) = 4 b(n+1) + (3 if n even else 0) has total variation n, and any x with tv x >= n is >= b(n).
-- Credit: @bnb9001

namespace OMA_A297554_Proof

open OMA.S_oeis_a297554

def e (n : ℕ) : ℕ := if n % 2 = 0 then 3 else 0

def b : ℕ → ℕ
  | 0 => 1
  | 1 => 4
  | 2 => 7
  | 3 => 12
  | (n + 4) => 4 * b (n + 1) + e (n + 4)

theorem b_pos (n : ℕ) : 0 < b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | (n + 4), ih => show 0 < 4 * b (n + 1) + e (n + 4); have := ih (n + 1) (by omega); omega

theorem e_lt (n : ℕ) : e n < 4 := by unfold e; split_ifs <;> omega

theorem b_mod (n : ℕ) (hn : 1 ≤ n) : b n % 4 = e n := by
  match n, hn with
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | (n + 4), _ => show (4 * b (n + 1) + e (n + 4)) % 4 = e (n + 4); have := e_lt (n + 4); omega

theorem b_div (n : ℕ) : b (n + 4) / 4 = b (n + 1) := by
  show (4 * b (n + 1) + e (n + 4)) / 4 = b (n + 1); have := e_lt (n + 4); omega

theorem tv_step (y d : ℕ) (hy : 0 < y) (hd : d < 4) :
    tv (4 * y + d) = ((d - y % 4) + (y % 4 - d)) + tv y := by
  unfold tv
  have h1 : Nat.digits 4 (4 * y + d) = d :: Nat.digits 4 y := by
    rw [Nat.digits_def' (by norm_num) (by omega)]
    congr 1
    · omega
    · congr 1; omega
  have h2 : Nat.digits 4 y = (y % 4) :: Nat.digits 4 (y / 4) := Nat.digits_def' (by norm_num) hy
  rw [h1, h2, tvList]

theorem tv_small (x : ℕ) (h0 : 0 < x) (h4 : x < 4) : tv x = 0 := by
  unfold tv
  rw [Nat.digits_def' (by norm_num) h0, show x / 4 = 0 by omega, Nat.digits_zero, tvList]

theorem tv_le (y d : ℕ) (hy : 0 < y) (hd : d < 4) : tv (4 * y + d) ≤ 3 + tv y := by
  rw [tv_step y d hy hd]; have := Nat.mod_lt y (show 4 > 0 by norm_num); omega

theorem tv_b (n : ℕ) : tv (b n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rw [show b 0 = 1 from rfl, tv_small 1 (by norm_num) (by norm_num)]
    | 1, _ => rw [show b 1 = 4 * 1 + 0 from rfl, tv_step 1 0 (by norm_num) (by norm_num),
        tv_small 1 (by norm_num) (by norm_num)]
    | 2, _ => rw [show b 2 = 4 * 1 + 3 from rfl, tv_step 1 3 (by norm_num) (by norm_num),
        tv_small 1 (by norm_num) (by norm_num)]
    | 3, _ => rw [show b 3 = 4 * 3 + 0 from rfl, tv_step 3 0 (by norm_num) (by norm_num),
        tv_small 3 (by norm_num) (by norm_num)]
    | (n + 4), ih =>
      rw [show b (n + 4) = 4 * b (n + 1) + e (n + 4) from rfl,
        tv_step _ _ (b_pos _) (e_lt _), ih (n + 1) (by omega), b_mod (n + 1) (by omega)]
      unfold e
      split_ifs <;> omega

/-- minimality, in the stronger form `n ≤ tv x → b n ≤ x` -/
theorem b_min : ∀ n x, 0 < x → n ≤ tv x → b n ≤ x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx hn
    rcases Nat.lt_or_ge x 4 with hx4 | hx4
    · rw [tv_small x hx hx4] at hn
      have : n = 0 := by omega
      subst this; show 1 ≤ x; omega
    · -- x = 4y + d with y > 0
      set y := x / 4 with hy
      set d := x % 4 with hd
      have hxyd : x = 4 * y + d := by omega
      have hy0 : 0 < y := by omega
      have hd4 : d < 4 := Nat.mod_lt _ (by norm_num)
      rcases Nat.lt_or_ge n 4 with hn4 | hn4
      · -- small n: b n ≤ 12
        rcases Nat.lt_or_ge x 16 with hx16 | hx16
        · have hy4 : y < 4 := by omega
          have htv := tv_step y d hy0 hd4
          rw [tv_small y hy0 hy4, add_zero, Nat.mod_eq_of_lt hy4] at htv
          rw [hxyd, htv] at hn
          rw [hxyd]
          have b0 : b 0 = 1 := rfl
          have b1 : b 1 = 4 := rfl
          have b2 : b 2 = 7 := rfl
          have b3 : b 3 = 12 := rfl
          interval_cases n <;> interval_cases y <;> interval_cases d <;> omega
        · have b0 : b 0 = 1 := rfl
          have b1 : b 1 = 4 := rfl
          have b2 : b 2 = 7 := rfl
          have b3 : b 3 = 12 := rfl
          interval_cases n <;> omega
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
        have htv := tv_step y d hy0 hd4
        rw [← hxyd] at htv
        have hy_ge : m + 1 ≤ tv y := by
          have := Nat.mod_lt y (show 4 > 0 by norm_num); omega
        have hb := ih (m + 1) (by omega) y hy0 hy_ge
        show 4 * b (m + 1) + e (m + 4) ≤ x
        rcases Nat.lt_or_ge (b (m + 1)) y with hlt | hge
        · have := e_lt (m + 4); omega
        · have hyeq : y = b (m + 1) := le_antisymm hge hb
          -- then the last step is small
          have hmod : y % 4 = e (m + 1) := by rw [hyeq]; exact b_mod _ (by omega)
          have htvy : tv y = m + 1 := by rw [hyeq]; exact tv_b _
          rw [hmod, htvy] at htv
          unfold e at htv ⊢
          split_ifs at htv ⊢ with h1 h2 h2 <;> omega

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
    | 5, _ => decide
    | (n + 6), ih =>
      show a (n + 4) + 4 * a (n + 3) - 4 * a (n + 1) = (b (n + 6) : ℤ)
      rw [ih (n + 4) (by omega), ih (n + 3) (by omega), ih (n + 1) (by omega)]
      have h6 : b (n + 6) = 4 * b (n + 3) + e (n + 6) := rfl
      have h4 : b (n + 4) = 4 * b (n + 1) + e (n + 4) := rfl
      have he : e (n + 6) = e (n + 4) := by
        simp only [e, show (n + 6) % 2 = (n + 4) % 2 by omega]
      rw [h6, h4, he]; push_cast; ring

end OMA_A297554_Proof

open OMA.S_oeis_a297554 OMA_A297554_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a297554.main := by
  intro n
  rw [a_eq_b, Int.toNat_natCast]
  exact ⟨⟨b_pos n, tv_b n⟩, fun x ⟨hx, htv⟩ => b_min n x hx htv.ge⟩
