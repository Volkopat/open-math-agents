import OMAStatements.S_oeis_a339532

namespace OMA.S_oeis_a339532




instance : DecidablePred Q := fun b => by unfold Q Wieferich Nat.ModEq; infer_instance
instance : DecidablePred P := fun b => by unfold P; infer_instance


/-- The conjecture (the recurrence). -/
def Conjecture : Prop := ∀ n : ℕ, 9 < n → (a n : ℤ) = a (n - 1) + a (n - 8) - a (n - 9)

theorem Q_periodic (b : ℕ) : Q (b + 900) ↔ Q b := by
  have h4 : b + 900 ≡ b [MOD 2 ^ 2] := by simp [Nat.ModEq, Nat.add_mod]
  have h9 : b + 900 ≡ b [MOD 3 ^ 2] := by simp [Nat.ModEq, Nat.add_mod]
  have h25 : b + 900 ≡ b [MOD 5 ^ 2] := by simp [Nat.ModEq, Nat.add_mod]
  unfold Q Wieferich
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(h4.pow _).symm.trans h1, (h9.pow _).symm.trans h2, (h25.pow _).symm.trans h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(h4.pow _).trans h1, (h9.pow _).trans h2, (h25.pow _).trans h3⟩

theorem count_add_period {R : ℕ → Prop} [DecidablePred R] {T : ℕ}
    (hper : ∀ m, R (m + T) ↔ R m) : ∀ m, Nat.count R (m + T) = Nat.count R m + Nat.count R T := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + T = (m + T) + 1 by omega, Nat.count_succ, ih, Nat.count_succ]
    by_cases h : R m
    · rw [if_pos ((hper m).mpr h), if_pos h]
      omega
    · rw [if_neg (fun h' => h ((hper m).mp h')), if_neg h]
      omega

theorem count_Q_900 : Nat.count Q 900 = 8 := by decide +kernel

theorem count_P (m : ℕ) (hm : 2 ≤ m) : Nat.count P m = Nat.count Q m - 1 := by
  induction m, hm using Nat.le_induction with
  | base => decide +kernel
  | succ m hm ih =>
    have hq1 : 1 ≤ Nat.count Q m := by
      have : Nat.count Q 2 ≤ Nat.count Q m := Nat.count_monotone Q hm
      have h2 : Nat.count Q 2 = 1 := by decide +kernel
      omega
    rw [Nat.count_succ, Nat.count_succ, ih]
    have hPQ : P m ↔ Q m := ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    by_cases h : Q m
    · rw [if_pos (hPQ.mpr h), if_pos h]
      omega
    · rw [if_neg (fun h' => h (hPQ.mp h')), if_neg h]
      omega

theorem P_449 (j : ℕ) : P (449 + 900 * j) := by
  induction j with
  | zero => decide
  | succ j ih =>
    refine ⟨by omega, ?_⟩
    rw [show 449 + 900 * (j + 1) = (449 + 900 * j) + 900 by ring]
    exact (Q_periodic _).mpr ih.2

theorem P_infinite : (Set.ofPred P).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨N, hN⟩
  have := hN (show 449 + 900 * N ∈ Set.ofPred P from P_449 N)
  omega

/-- The period: `a(n + 8) = a(n) + 900` for `n ≥ 1`. -/
theorem nth_add_eight (k : ℕ) : Nat.nth P (k + 8) = Nat.nth P k + 900 := by
  set x := Nat.nth P k
  have hx : P x := Nat.nth_mem_of_infinite P_infinite k
  have hcx : Nat.count P x = k := Nat.count_nth_of_infinite P_infinite k
  have hx2 : 2 ≤ x := hx.1
  have hP : P (x + 900) := ⟨by omega, (Q_periodic x).mpr hx.2⟩
  have hc : Nat.count P (x + 900) = k + 8 := by
    rw [count_P _ (by omega), count_add_period Q_periodic, count_Q_900]
    rw [count_P _ hx2] at hcx
    have : 1 ≤ Nat.count Q x := by
      have h2 : Nat.count Q 2 = 1 := by decide +kernel
      have := Nat.count_monotone Q hx2
      omega
    omega
  rw [← hc, Nat.nth_count hP]

theorem conjecture_true : Conjecture := by
  intro n hn
  have h1 : a n = a (n - 8) + 900 := by
    unfold a
    rw [show n - 1 = (n - 8 - 1) + 8 by omega, nth_add_eight]
  have h2 : a (n - 1) = a (n - 9) + 900 := by
    unfold a
    rw [show n - 1 - 1 = (n - 9 - 1) + 8 by omega, nth_add_eight]
  rw [h1, h2]
  push_cast
  ring

/-- Control: the first nine terms listed in the entry. -/
theorem first_terms : a 1 = 449 ∧ a 2 = 557 ∧ a 3 = 593 ∧ a 4 = 649 ∧ a 5 = 701 ∧ a 6 = 757 ∧
    a 7 = 793 ∧ a 8 = 901 ∧ a 9 = 1349 := by
  have key : ∀ n v : ℕ, P v → Nat.count P v = n - 1 → a n = v := fun n v hv hc => by
    rw [a, ← hc, Nat.nth_count hv]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact key _ _ (by decide) (by decide +kernel)

open PowerSeries in
/-- Wu's g.f. as an identity of formal power series: from `x^10` on the coefficients of the
product are the recurrence, below they are `a(1..9)`. -/
theorem gf_identity :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (X ^ 9 - X ^ 8 - X + 1) =
      X * (-X ^ 8 + 108 * X ^ 7 + 36 * X ^ 6 + 56 * X ^ 5 + 52 * X ^ 4 + 56 * X ^ 3 + 36 * X ^ 2 +
        108 * X + 449) := by
  have hN : (X * (-X ^ 8 + 108 * X ^ 7 + 36 * X ^ 6 + 56 * X ^ 5 + 52 * X ^ 4 + 56 * X ^ 3 +
      36 * X ^ 2 + 108 * X + 449) : ℚ⟦X⟧) =
      C 449 * X ^ 1 + C 108 * X ^ 2 + C 36 * X ^ 3 + C 56 * X ^ 4 + C 52 * X ^ 5 + C 56 * X ^ 6 +
        C 36 * X ^ 7 + C 108 * X ^ 8 - C 1 * X ^ 9 := by
    simp only [map_ofNat, map_one]
    ring
  have e : ∀ A : ℚ⟦X⟧, A * (X ^ 9 - X ^ 8 - X + 1) = A - A * X ^ 1 - A * X ^ 8 + A * X ^ 9 := by
    intro A; ring
  rw [hN, e]
  ext n
  simp only [map_sub, map_add, coeff_mul_X_pow', coeff_mk, coeff_C]
  rcases Nat.lt_or_ge n 10 with hn | hn
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := first_terms
    interval_cases n <;> simp [h1, h2, h3, h4, h5, h6, h7, h8, h9] <;> norm_num
  · have hr : (a n : ℚ) = a (n - 1) + a (n - 8) - a (n - 9) := by
      exact_mod_cast conjecture_true n hn
    simp only [show n ≠ 0 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega,
      show 8 ≤ n by omega, show 9 ≤ n by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega,
      show n - 6 ≠ 0 by omega, show n - 7 ≠ 0 by omega, show n - 8 ≠ 0 by omega,
      show n - 9 ≠ 0 by omega, if_true, if_false]
    linarith

end OMA.S_oeis_a339532

theorem OMA.solution : type_of% @OMA.S_oeis_a339532.main :=
  ⟨OMA.S_oeis_a339532.conjecture_true, OMA.S_oeis_a339532.gf_identity⟩
