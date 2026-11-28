import OMAStatements.S_oeis_a267920

open PowerSeries
open OMA.S_oeis_a267920

-- Colin Barker's recurrence and generating function. Rule 243 has one moving
-- zero after the first step, so each crop is a repunit with its penultimate bit removed.
private def gap (p : ℤ) : Row := fun x => decide (x ≠ p)

private theorem rule_bool (l c r : Bool) : rule l c r = (l || !c) := by
  cases l <;> cases c <;> cases r <;> decide

private theorem state_gap (n : ℕ) : state (n + 1) = gap (n : ℤ) := by
  induction n with
  | zero =>
    funext x
    change rule (initial (x - 1)) (initial x) (initial (x + 1)) = gap 0 x
    by_cases h : x = 0
    · subst x
      decide
    · simp [rule_bool, initial, gap, h]
  | succ n ih =>
    funext x
    change step (state (n + 1)) x = gap ((n + 1 : ℕ) : ℤ) x
    rw [ih]
    simp only [step, rule_bool]
    by_cases h : x - 1 = (n : ℤ)
    · have h₂ : x = (n : ℤ) + 1 := by omega
      simp [gap, h₂]
    · have h₂ : x ≠ (n : ℤ) + 1 := by omega
      simp [gap, h, h₂]

private def repunit : ℕ → ℕ
  | 0 => 0
  | m + 1 => 10 * repunit m + 1

private theorem encode_ones (g : Row) (left : ℤ) (m : ℕ)
    (h : ∀ k < m, g (left + (k : ℤ)) = true) : encode g left m = repunit m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [encode, repunit, ih (fun k hk => h k (by omega)), h m (by omega)]
    rfl

private theorem a_formula (n : ℕ) : a (n + 1) = 100 * repunit (2 * n + 1) + 1 := by
  let left : ℤ := -((n + 1 : ℕ) : ℤ)
  have h₀ : gap (n : ℤ) (left + ((2 * n + 1 : ℕ) : ℤ)) = false := by
    have hx : left + ((2 * n + 1 : ℕ) : ℤ) = (n : ℤ) := by dsimp [left]; omega
    unfold gap
    rw [hx]
    simp
  have h₁ : gap (n : ℤ) (left + ((2 * n + 1 + 1 : ℕ) : ℤ)) = true := by
    have hx : left + ((2 * n + 1 + 1 : ℕ) : ℤ) ≠ (n : ℤ) := by dsimp [left]; omega
    unfold gap
    exact decide_eq_true hx
  have hp : encode (gap (n : ℤ)) left (2 * n + 1) = repunit (2 * n + 1) := by
    apply encode_ones
    intro k hk
    have hx : left + (k : ℤ) ≠ (n : ℤ) := by dsimp [left]; omega
    simp [gap, hx]
  rw [a, state_gap, show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by omega]
  calc
    _ = 10 * (10 * encode (gap (n : ℤ)) left (2 * n + 1) +
        bit (gap (n : ℤ) (left + ((2 * n + 1 : ℕ) : ℤ)))) +
        bit (gap (n : ℤ) (left + ((2 * n + 1 + 1 : ℕ) : ℤ))) := rfl
    _ = _ := by rw [hp, h₀, h₁]; simp [bit]; ring

private theorem a_jump (n : ℕ) : (a (n + 2) : ℤ) = 100 * (a (n + 1) : ℤ) + 1001 := by
  rw [show n + 2 = (n + 1) + 1 by rfl, a_formula (n + 1), a_formula n,
    show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by omega]
  simp only [repunit, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  ring

private theorem a_recurrence (n : ℕ) (hn : 2 < n) :
    (a n : ℤ) = 101 * (a (n-1) : ℤ) - 100 * (a (n-2) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 3 := ⟨n - 3, by omega⟩
  have h₀ := a_jump k
  have h₁ := a_jump (k + 1)
  change (a (k + 3) : ℤ) = 100 * (a (k + 2) : ℤ) + 1001 at h₁
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
  omega

private theorem generating :
    series * ((1 - X) * (1 - 100 * X)) =
      1 + 1000 * X ^ 2 := by
  have hd : series * ((1 - X) * (1 - 100 * X)) =
      series - (series * C (101 : ℤ)) * X ^ 1 +
        (series * C (100 : ℤ)) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  have hnum : (1 + 1000 * X ^ 2 : PowerSeries ℤ) =
      1 + C (1000 : ℤ) * X ^ 2 := by simp
  rw [hd, hnum]
  apply ext
  intro n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C,
    coeff_C, coeff_one, series, coeff_mk]
  by_cases hn : n < 3
  · interval_cases n <;> decide
  · have hr := a_recurrence n (by omega)
    simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_neg (show n ≠ 0 by omega), if_neg (show n - 2 ≠ 0 by omega)]
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a267920.main :=
  ⟨a_recurrence, generating⟩
