import OMAStatements.S_oeis_a297443

namespace OMA.S_oeis_a297443




/-! ## The explicit solution b -/

def cb (n : ℕ) : ℕ := if n % 4 = 1 ∨ n % 4 = 2 then 2 else 0

def b : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 6
  | n + 3 => 3 * b (n + 1) + cb (n + 1)

lemma b_rec (n : ℕ) (hn : 1 ≤ n) : b (n + 2) = 3 * b n + cb n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

lemma cb_alt (m : ℕ) : (cb m : ℤ) - cb (m + 1) + cb (m + 2) - cb (m + 3) = 0 := by
  unfold cb
  have : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h1 : (m + 1) % 4 = (m % 4 + 1) % 4 := by omega
  have h2 : (m + 2) % 4 = (m % 4 + 2) % 4 := by omega
  have h3 : (m + 3) % 4 = (m % 4 + 3) % 4 := by omega
  rw [h1, h2, h3]
  interval_cases (m % 4) <;> simp

lemma a_eq_b (n : ℕ) : a n = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 6 with h | h
    · interval_cases n <;> rfl
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      rw [a, ih (m + 5) (by omega), ih (m + 4) (by omega), ih (m + 3) (by omega),
        ih (m + 2) (by omega), ih (m + 1) (by omega)]
      have e6 := b_rec (m + 4) (by omega)
      have e5 := b_rec (m + 3) (by omega)
      have e4 := b_rec (m + 2) (by omega)
      have e3 := b_rec (m + 1) (by omega)
      have hc := cb_alt (m + 1)
      rw [show m + 4 + 2 = m + 6 by omega] at e6
      rw [show m + 3 + 2 = m + 5 by omega] at e5
      rw [show m + 2 + 2 = m + 4 by omega] at e4
      rw [show m + 1 + 2 = m + 3 by omega] at e3
      rw [show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega,
        show m + 1 + 3 = m + 4 by omega] at hc
      rw [e6, e5, e4, e3]
      push_cast
      linarith

lemma b_pos (n : ℕ) : 1 ≤ b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | n
    · simp [b]
    · simp [b]
    · simp [b]
    · rw [show n + 1 + 1 + 1 = (n + 1) + 2 by omega, b_rec _ (by omega)]
      have := ih (n + 1) (by omega)
      omega

/-! ## Total variation -/

lemma totVar_step (q r : ℕ) (hq : 1 ≤ q) (hr : r < 3) :
    totVar (3 * q + r) = ((r - q % 3) + (q % 3 - r)) + totVar q := by
  unfold totVar
  have h1 : Nat.digits 3 (3 * q + r) = r :: Nat.digits 3 q := by
    rw [Nat.digits_def' (by norm_num) (by omega)]
    congr 2 <;> omega
  have h2 : Nat.digits 3 q = q % 3 :: Nat.digits 3 (q / 3) := Nat.digits_def' (by norm_num) (by omega)
  rw [h1, h2, tvar]

lemma totVar_small (m : ℕ) (h1 : 1 ≤ m) (h3 : m < 3) : totVar m = 0 := by
  unfold totVar
  rw [Nat.digits_def' (by norm_num) (by omega), Nat.div_eq_of_lt h3]
  simp [tvar]

lemma b_mod3 (n : ℕ) (hn : 1 ≤ n) : b n % 3 = if n % 4 = 1 ∨ n % 4 = 2 then 0 else 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | n
    · omega
    · simp [b]
    · simp [b]
    · rw [show n + 1 + 1 + 1 = (n + 1) + 2 by omega, b_rec _ (by omega)]
      unfold cb
      have : (n + 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
      have e : (n + 1 + 2) % 4 = ((n + 1) % 4 + 2) % 4 := by omega
      rw [e]
      interval_cases h : (n + 1) % 4 <;> simp <;> omega

lemma totVar_b (n : ℕ) : totVar (b n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | _ | n
    · decide
    · decide
    · decide
    · have hb := b_pos (n + 1)
      have hm := b_mod3 (n + 1) (by omega)
      rw [show n + 1 + 1 + 1 = (n + 1) + 2 by omega, b_rec _ (by omega)]
      have hc : cb (n + 1) < 3 := by unfold cb; split_ifs <;> norm_num
      rw [totVar_step _ _ hb hc, ih (n + 1) (by omega), hm]
      unfold cb
      split_ifs <;> omega

/-! ## Lower bounds Phi(n, d) = 8 * (least m with TV(m) = n and last digit d) -/

/-- The correction term c(d, rho). -/
def c : ℕ → ℕ → ℤ
  | 0, _ => 6
  | 1, ρ => if ρ ≤ 1 then -2 else 10
  | _, _ => 2

/-- G0(rho, d) = 8 Phi... at n = 4 + rho, plus c(d, rho). -/
def G0 : ℕ → ℕ → ℤ
  | 0, 0 => 462
  | 1, 0 => 270
  | 2, 0 => 486
  | 3, 0 => 1134
  | 0, 1 => 270
  | 1, 1 => 486
  | 2, 1 => 810
  | 3, 1 => 1458
  | 0, _ => 162
  | 1, _ => 378
  | 2, _ => 1386
  | _, _ => 810

/-- Eight times the least m with TV(m) = n and m mod 3 = d, for n < 4 (0 for the impossible
pair n = 0, d = 0). -/
def T : ℕ → ℕ → ℤ
  | 0, 0 => 0
  | 0, 1 => 8
  | 0, _ => 16
  | 1, 0 => 24
  | 1, 1 => 56
  | 1, _ => 40
  | 2, 0 => 48
  | 2, 1 => 80
  | 2, _ => 184
  | _, 0 => 120
  | _, 1 => 152
  | _, _ => 88

def Phi (n d : ℕ) : ℤ :=
  if n < 4 then T n d else 9 ^ ((n - 4) / 4) * G0 ((n - 4) % 4) d - c d ((n - 4) % 4)

lemma Phi_big (j ρ d : ℕ) (hρ : ρ < 4) : Phi (4 + 4 * j + ρ) d = 9 ^ j * G0 ρ d - c d ρ := by
  unfold Phi
  rw [if_neg (by omega), show (4 + 4 * j + ρ - 4) / 4 = j by omega,
    show (4 + 4 * j + ρ - 4) % 4 = ρ by omega]

lemma step_big (X : ℤ) (hX : 1 ≤ X) (ρ d r : ℕ) (hρ : ρ < 4) (hd : d < 3) (hr : r < 3) :
    (if ρ + ((r - d) + (d - r)) < 4 then
        X * G0 (ρ + ((r - d) + (d - r))) r - c r (ρ + ((r - d) + (d - r)))
      else 9 * X * G0 (ρ + ((r - d) + (d - r)) - 4) r - c r (ρ + ((r - d) + (d - r)) - 4)) ≤
      3 * (X * G0 ρ d - c d ρ) + 8 * r := by
  interval_cases ρ <;> interval_cases d <;> interval_cases r <;> simp [G0, c] <;> omega

lemma step_small : ∀ k < 4, ∀ d < 3, ∀ r < 3, ¬ (k = 0 ∧ d = 0) →
    Phi (k + ((r - d) + (d - r))) r ≤ 3 * Phi k d + 8 * r := by
  decide

lemma step (k d r : ℕ) (hd : d < 3) (hr : r < 3) (h00 : ¬ (k = 0 ∧ d = 0)) :
    Phi (k + ((r - d) + (d - r))) r ≤ 3 * Phi k d + 8 * r := by
  rcases Nat.lt_or_ge k 4 with hk | hk
  · exact step_small k hk d hd r hr h00
  · obtain ⟨j, ρ, hρ, rfl⟩ : ∃ j ρ, ρ < 4 ∧ k = 4 + 4 * j + ρ :=
      ⟨(k - 4) / 4, (k - 4) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
    have hs := step_big (9 ^ j) (one_le_pow₀ (by norm_num)) ρ d r hρ hd hr
    rw [Phi_big j ρ d hρ]
    split_ifs at hs with h
    · rw [show 4 + 4 * j + ρ + ((r - d) + (d - r)) = 4 + 4 * j + (ρ + ((r - d) + (d - r))) by omega,
        Phi_big j _ r h]
      exact hs
    · have hρ' : ρ + ((r - d) + (d - r)) - 4 < 4 := by omega
      rw [show 4 + 4 * j + ρ + ((r - d) + (d - r)) =
          4 + 4 * (j + 1) + (ρ + ((r - d) + (d - r)) - 4) by omega,
        Phi_big (j + 1) _ r hρ', pow_succ]
      linarith

/-! ## b is below every bound -/

def cbb (ρ : ℕ) : ℤ := if ρ = 1 ∨ ρ = 2 then 6 else 2

def Gb0 : ℕ → ℤ
  | 0 => 162
  | 1 => 270
  | 2 => 486
  | _ => 810

lemma b_four (n : ℕ) (hn : 1 ≤ n) : (b (n + 4) : ℤ) = 9 * b n + cbb (n % 4) := by
  have e1 := b_rec (n + 2) (by omega)
  have e2 := b_rec n hn
  rw [show n + 2 + 2 = n + 4 by omega] at e1
  rw [e1, e2]
  unfold cb cbb
  have : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have e : (n + 2) % 4 = (n % 4 + 2) % 4 := by omega
  rw [e]
  interval_cases (n % 4) <;> simp <;> ring

lemma b_closed (j ρ : ℕ) (hρ : ρ < 4) :
    8 * (b (4 + 4 * j + ρ) : ℤ) + cbb ρ = 9 ^ j * Gb0 ρ := by
  induction j with
  | zero =>
    interval_cases ρ <;> simp [b, cb, cbb, Gb0]
  | succ j ih =>
    have h := b_four (4 + 4 * j + ρ) (by omega)
    rw [show 4 + 4 * j + ρ + 4 = 4 + 4 * (j + 1) + ρ by omega,
      show (4 + 4 * j + ρ) % 4 = ρ by omega] at h
    rw [h, pow_succ]
    linarith

lemma b_le_Phi (n d : ℕ) (hd : d < 3) (h00 : ¬ (n = 0 ∧ d = 0)) : 8 * (b n : ℤ) ≤ Phi n d := by
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> interval_cases d <;> simp_all [b, cb, Phi, T]
  · obtain ⟨j, ρ, hρ, rfl⟩ : ∃ j ρ, ρ < 4 ∧ n = 4 + 4 * j + ρ :=
      ⟨(n - 4) / 4, (n - 4) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
    have hb := b_closed j ρ hρ
    rw [Phi_big j ρ d hρ]
    have hX : (1 : ℤ) ≤ 9 ^ j := one_le_pow₀ (by norm_num)
    generalize (9 : ℤ) ^ j = X at hb hX ⊢
    interval_cases ρ <;> interval_cases d <;> simp [G0, c, cbb, Gb0] at hb ⊢ <;> omega

/-! ## The invariant -/

lemma totVar_zero_mod (q : ℕ) (hq : 1 ≤ q) (h0 : totVar q = 0) : q % 3 ≠ 0 := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hmod
    rcases Nat.lt_or_ge q 3 with h3 | h3
    · omega
    · have hq' : 1 ≤ q / 3 := by omega
      have e := totVar_step (q / 3) 0 hq' (by norm_num)
      rw [show 3 * (q / 3) + 0 = q by omega, h0] at e
      have h1 : totVar (q / 3) = 0 := by omega
      have h2 : q / 3 % 3 = 0 := by omega
      exact ih (q / 3) (by omega) hq' h1 h2

lemma Phi_le (m : ℕ) (hm : 1 ≤ m) : Phi (totVar m) (m % 3) ≤ 8 * m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · rw [totVar_small m hm h3]
      interval_cases m <;> decide
    · have hq : 1 ≤ m / 3 := by omega
      have hr : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have hm' : m = 3 * (m / 3) + m % 3 := by omega
      have ih' := ih (m / 3) (by omega) hq
      have h00 : ¬ (totVar (m / 3) = 0 ∧ m / 3 % 3 = 0) := fun h =>
        totVar_zero_mod (m / 3) hq h.1 h.2
      have hs := step (totVar (m / 3)) (m / 3 % 3) (m % 3) (Nat.mod_lt _ (by norm_num)) hr h00
      have e := totVar_step (m / 3) (m % 3) hq hr
      rw [← hm'] at e
      rw [e, show m % 3 - m / 3 % 3 + (m / 3 % 3 - m % 3) + totVar (m / 3) =
        totVar (m / 3) + (m % 3 - m / 3 % 3 + (m / 3 % 3 - m % 3)) by ring]
      have : (8 : ℤ) * m = 3 * (8 * ↑(m / 3)) + 8 * ↑(m % 3) := by
        conv_lhs => rw [hm']
        push_cast
        ring
      rw [this]
      linarith

/-- Kimberling's conjecture: a(n) is the least positive integer whose base-3 total variation
is n. -/
theorem conjecture (n : ℕ) :
    ∃ m : ℕ, (m : ℤ) = a n ∧ IsLeast {k : ℕ | 0 < k ∧ totVar k = n} m := by
  refine ⟨b n, (a_eq_b n).symm, ⟨b_pos n, totVar_b n⟩, ?_⟩
  rintro k ⟨hk, hkn⟩
  have h1 := Phi_le k hk
  rw [hkn] at h1
  have h00 : ¬ (n = 0 ∧ k % 3 = 0) := by
    rintro ⟨rfl, h⟩
    exact totVar_zero_mod k hk hkn h
  have h2 := b_le_Phi n (k % 3) (Nat.mod_lt _ (by norm_num)) h00
  have : (8 : ℤ) * b n ≤ 8 * k := le_trans h2 h1
  exact_mod_cast (by linarith : (b n : ℤ) ≤ k)

/-- Controls: a(0..9) = 1, 3, 6, 11, 20, 33, 60, 101, 182, 303 as in the entry. -/
lemma controls : (List.range 10).map a = [1, 3, 6, 11, 20, 33, 60, 101, 182, 303] := by decide

end OMA.S_oeis_a297443

theorem OMA.solution : type_of% @OMA.S_oeis_a297443.main :=
  fun n => OMA.S_oeis_a297443.conjecture n
