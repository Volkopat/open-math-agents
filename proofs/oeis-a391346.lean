import OMAStatements.S_oeis_a391346

-- Problem: A391346: Numbers k such that Stern polynomial B(5*k,x) is a multiple of B(5,x).
-- Upstream: formal-conjectures statements/oeis-a391346.lean:0 (declaration OMA.S_oeis_a391346.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: B(k,2) = k by induction (2*m and m + (m+1) = 2m+1), and B(5,x) = 2x+1 has value 5
-- at x = 2. So B(k,x) = B(5,x)*Q(x) in Z[x] gives k = 5*Q(2), that is 5 divides k. Hence every
-- term of A391566 is a multiple of 5, and the map m -> 5m is a strictly increasing bijection from
-- the terms of A391346 onto the terms of A391566; Nat.nth_comp_of_strictMono then gives
-- A391566(n) = 5*A391346(n), that is A391346(n) = A391566(n)/5 in Q. Both sets are infinite, since B(5*2^j,x) = x^j*B(5,x).

namespace R07A391346

open OMA.S_oeis_a391346

theorem B_eq (n : ℕ) : B n = if _h0 : n = 0 then 0
    else if _h1 : n = 1 then 1
    else if _h2 : n % 2 = 0 then Polynomial.X * B (n / 2)
    else B (n / 2) + B (n / 2 + 1) := by
  rw [B]

theorem B_zero : B 0 = 0 := by
  rw [B_eq 0, dif_pos (show (0 : ℕ) = 0 from rfl)]

theorem B_one : B 1 = 1 := by
  rw [B_eq 1, dif_neg (show ¬ ((1 : ℕ) = 0) by omega), dif_pos (show (1 : ℕ) = 1 from rfl)]

theorem B_even (m : ℕ) (hm : 1 ≤ m) : B (2 * m) = Polynomial.X * B m := by
  rw [B_eq (2 * m), dif_neg (show ¬ (2 * m = 0) by omega), dif_neg (show ¬ (2 * m = 1) by omega),
    dif_pos (show 2 * m % 2 = 0 by omega), show 2 * m / 2 = m by omega]

theorem B_odd (m : ℕ) (hm : 1 ≤ m) : B (2 * m + 1) = B m + B (m + 1) := by
  rw [B_eq (2 * m + 1), dif_neg (show ¬ (2 * m + 1 = 0) by omega),
    dif_neg (show ¬ (2 * m + 1 = 1) by omega),
    dif_neg (show ¬ ((2 * m + 1) % 2 = 0) by omega), show (2 * m + 1) / 2 = m by omega]

theorem eval_two (n : ℕ) : (B n).eval 2 = (n : ℤ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · simp [B_zero]
      · simp [B_one]
    · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
      · rw [B_even m (by omega), Polynomial.eval_mul, Polynomial.eval_X, ih m (by omega)]
        omega
      · rw [B_odd m (by omega), Polynomial.eval_add, ih m (by omega), ih (m + 1) (by omega)]
        omega

theorem five_dvd (k : ℕ) (h : B 5 ∣ B k) : 5 ∣ k := by
  obtain ⟨Q, hQ⟩ := h
  have e := congrArg (Polynomial.eval (2 : ℤ)) hQ
  rw [Polynomial.eval_mul, eval_two, eval_two] at e
  exact Int.natCast_dvd_natCast.mp ⟨Polynomial.eval 2 Q, e⟩

theorem B_five_pow (j : ℕ) : B (5 * 2 ^ j) = Polynomial.X ^ j * B 5 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : 1 ≤ 5 * 2 ^ j := by
      have := pow_pos (show (0 : ℕ) < 2 by norm_num) j
      omega
    rw [pow_succ (2 : ℕ) j, show (5 : ℕ) * (2 ^ j * 2) = 2 * (5 * 2 ^ j) by ring,
      B_even (5 * 2 ^ j) h1, ih]
    ring

/-- The defining property of the terms of A391566 (named A391566 in the statement). -/
def P (k : ℕ) : Prop := 0 < k ∧ B 5 ∣ B k

theorem P_inf : (Set.ofPred P).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  refine ⟨5 * 2 ^ a, ?_, ?_⟩
  · show 0 < 5 * 2 ^ a ∧ B 5 ∣ B (5 * 2 ^ a)
    refine ⟨?_, ?_⟩
    · have := pow_pos (show (0 : ℕ) < 2 by norm_num) a
      omega
    · rw [B_five_pow a]
      exact dvd_mul_left (B 5) (Polynomial.X ^ a)
  · have := Nat.lt_two_pow_self (n := a)
    omega

theorem range5 : ∀ k, P k → k ∈ Set.range (fun x : ℕ => 5 * x) := by
  intro k hk
  have hk' : 0 < k ∧ B 5 ∣ B k := hk
  obtain ⟨c, rfl⟩ := five_dvd k hk'.2
  exact Set.mem_range_self c

theorem mono5 : StrictMono (fun x : ℕ => 5 * x) := by
  intro a b h
  show 5 * a < 5 * b
  omega

theorem pred_eq : (fun k => 0 < k ∧ B 5 ∣ B (5 * k)) = (fun i => P (5 * i)) := by
  funext i
  apply propext
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    show 0 < 5 * i ∧ B 5 ∣ B (5 * i)
    exact ⟨by omega, h2⟩
  · intro h
    have h' : 0 < 5 * i ∧ B 5 ∣ B (5 * i) := h
    obtain ⟨h1, h2⟩ := h'
    exact ⟨by omega, h2⟩

theorem nth_eq (n : ℕ) :
    Nat.nth P n = 5 * Nat.nth (fun k => 0 < k ∧ B 5 ∣ B (5 * k)) n := by
  have h : Nat.nth (fun k => 0 < k ∧ B 5 ∣ B (5 * k)) n = Nat.nth (fun i => P (5 * i)) n :=
    congrArg (fun q => Nat.nth q n) pred_eq
  rw [h]
  exact (Nat.nth_comp_of_strictMono (n := n) mono5 range5 (fun hfi => absurd hfi P_inf)).symm

end R07A391346

open OMA.S_oeis_a391346 R07A391346 in
theorem OMA.solution : type_of% @OMA.S_oeis_a391346.main := by
  intro n _hn
  have key : A391566 n = 5 * a n := nth_eq (n - 1)
  have keyQ : (A391566 n : ℚ) = 5 * (a n : ℚ) := by exact_mod_cast key
  rw [keyQ]
  ring
