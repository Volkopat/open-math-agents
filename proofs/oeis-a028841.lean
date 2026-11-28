import OMAStatements.S_oeis_a028841

-- Original proof by @jleguina.

namespace OMA.S_oeis_a028841


theorem ds_lt (n : ℕ) (h : 10 ≤ n) : ds n < n := by
  unfold ds
  rw [Nat.digits_def' (by norm_num) (by omega), List.sum_cons]
  have := Nat.digit_sum_le 10 (n / 10)
  omega


theorem idr_of_lt (n : ℕ) (h : n < 10) : idr n = n := by
  rw [idr, dif_pos h]

theorem idr_of_ge (n : ℕ) (h : 10 ≤ n) : idr n = idr (ds n) := by
  rw [idr, dif_neg (by omega)]

theorem ds_pos (n : ℕ) (h : 0 < n) : 0 < ds n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold ds
    rw [Nat.digits_def' (by norm_num) h, List.sum_cons]
    by_cases hr : 0 < n % 10
    · omega
    · have hq : 0 < n / 10 := by omega
      have := ih (n / 10) (by omega) hq
      unfold ds at this
      omega

/-- Iterating the digit sum preserves the residue modulo nine and positivity. -/
theorem idr_properties (n : ℕ) :
    idr n < 10 ∧ idr n % 9 = n % 9 ∧ (0 < n → 0 < idr n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 10
    · simp [idr_of_lt n h, h]
    · obtain ⟨hlt, hmod, hpos⟩ := ih (ds n) (ds_lt n (by omega))
      rw [idr_of_ge n (by omega)]
      exact ⟨hlt, hmod.trans (Nat.modEq_nine_digits_sum n).symm, fun hn => hpos (ds_pos n hn)⟩

/-- The residue form. -/
def R (n : ℕ) : Prop := n % 9 = 1 ∨ n % 9 = 2 ∨ n % 9 = 3 ∨ n % 9 = 5 ∨ n % 9 = 8

instance : DecidablePred R := fun n => by unfold R; infer_instance

theorem fib_digit (d : ℕ) (hd : 1 ≤ d) (hd9 : d ≤ 9) :
    (∃ k, Nat.fib k = d) ↔ (d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 5 ∨ d = 8) := by
  constructor
  · rintro ⟨k, hk⟩
    by_cases hk7 : k < 7
    · interval_cases k <;> simp [Nat.fib_add_two] at hk <;> omega
    · have : Nat.fib 7 ≤ Nat.fib k := Nat.fib_mono (by omega)
      have h7 : Nat.fib 7 = 13 := by decide
      omega
  · rintro (h | h | h | h | h) <;> subst h
    exacts [⟨1, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨6, rfl⟩]

theorem P_iff (n : ℕ) : P n ↔ R n := by
  unfold P R
  by_cases hn : 0 < n
  · obtain ⟨hlt, hmod, hpos⟩ := idr_properties n
    rw [fib_digit _ (hpos hn) (by omega)]
    constructor
    · rintro ⟨-, h⟩
      omega
    · intro h
      refine ⟨hn, ?_⟩
      omega
  · have : n = 0 := by omega
    subst this
    simp

theorem P_eq : P = R := by
  funext n
  exact propext (P_iff n)


/-- The conjecture (the recurrence). -/
def Conjecture : Prop := ∀ n : ℕ, 6 < n → (a n : ℤ) = a (n - 1) + a (n - 5) - a (n - 6)

theorem R_periodic (m : ℕ) : R (m + 9) ↔ R m := by
  unfold R
  omega

theorem count_add_period {Q : ℕ → Prop} [DecidablePred Q] {T : ℕ}
    (hper : ∀ m, Q (m + T) ↔ Q m) : ∀ m, Nat.count Q (m + T) = Nat.count Q m + Nat.count Q T := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + T = (m + T) + 1 by omega, Nat.count_succ, ih, Nat.count_succ]
    simp [hper, Nat.add_right_comm]

theorem count_9 : Nat.count R 9 = 5 := by decide +kernel

theorem R_infinite : (Set.ofPred R).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  have : R (9 * N + 1) := Or.inl (by omega)
  have := hN (show 9 * N + 1 ∈ Set.ofPred R from this)
  omega

theorem nth_add_five (k : ℕ) : Nat.nth R (k + 5) = Nat.nth R k + 9 := by
  set x := Nat.nth R k
  have hx : R x := Nat.nth_mem_of_infinite R_infinite k
  have hcx : Nat.count R x = k := Nat.count_nth_of_infinite R_infinite k
  have hP : R (x + 9) := (R_periodic x).mpr hx
  have hc : Nat.count R (x + 9) = k + 5 := by
    rw [count_add_period R_periodic, hcx, count_9]
  rw [← hc, Nat.nth_count hP]

theorem conjecture_true : Conjecture := by
  intro n hn
  have h1 : a n = a (n - 5) + 9 := by
    unfold a
    rw [P_eq, show n - 1 = (n - 5 - 1) + 5 by omega, nth_add_five]
  have h2 : a (n - 1) = a (n - 6) + 9 := by
    unfold a
    rw [P_eq, show n - 1 - 1 = (n - 6 - 1) + 5 by omega, nth_add_five]
  rw [h1, h2]
  push_cast
  ring

theorem a_eq (n v : ℕ) (hv : R v) (hc : Nat.count R v = n - 1) : a n = v := by
  rw [a, P_eq, ← hc, Nat.nth_count hv]

/-- Control: `a(1..6) = 1, 2, 3, 5, 8, 10` as listed in the entry, and `idr 98 = 8` (the entry's
example `98 -> 17 -> 8`). -/
theorem first_terms : a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 3 ∧ a 4 = 5 ∧ a 5 = 8 ∧ a 6 = 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact a_eq _ _ (by decide) (by decide +kernel)

theorem idr_98 : idr 98 = 8 := by
  rw [idr_of_ge 98 (by norm_num), show ds 98 = 17 by decide, idr_of_ge 17 (by norm_num),
    show ds 17 = 8 by decide, idr_of_lt 8 (by norm_num)]

open PowerSeries in
/-- Barker's g.f. as an identity of formal power series: from `x^7` on the coefficients of the
product are the recurrence, below they are `a(1..6)`. -/
theorem gf_identity :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) ^ 2 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4)) =
      X * (1 + X + X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4 + X ^ 5) := by
  have hN : (X * (1 + X + X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4 + X ^ 5) : ℚ⟦X⟧) =
      C 1 * X ^ 1 + C 1 * X ^ 2 + C 1 * X ^ 3 + C 2 * X ^ 4 + C 3 * X ^ 5 + C 1 * X ^ 6 := by
    simp only [map_ofNat, map_one]
    ring
  have e : ∀ A : ℚ⟦X⟧, A * ((1 - X) ^ 2 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4)) =
      A - A * X ^ 1 - A * X ^ 5 + A * X ^ 6 := by
    intro A; ring
  rw [hN, e]
  ext n
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_mk, coeff_C]
  rcases Nat.lt_or_ge n 7 with hn | hn
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := first_terms
    interval_cases n <;> simp [h1, h2, h3, h4, h5, h6] <;> norm_num
  · have hr : (a n : ℚ) = a (n - 1) + a (n - 5) - a (n - 6) := by
      exact_mod_cast conjecture_true n hn
    simp (disch := omega) [if_pos, if_neg]
    linarith

end OMA.S_oeis_a028841

theorem OMA.solution : type_of% @OMA.S_oeis_a028841.main :=
  ⟨OMA.S_oeis_a028841.gf_identity, OMA.S_oeis_a028841.conjecture_true⟩
