import OMAStatements.S_oeis_a004735

-- Problem: A004735: Denominator of average distance traveled by n-dimensional fly.
-- Upstream: formal-conjectures statements/oeis-a004735.lean:0 (declaration OMA.S_oeis_a004735.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for even argument 2n the PARI expression is d(2n) = 4 E / O with
-- E = Product_{i<n} (2n - 2i) = 2^n n! and O = Product_{i<=n} (2n + 1 - 2i) = 1*3*...*(2n+1),
-- and O E = (2n+1)!. Hence q = (2n+1) binomial(2n,n)/4^n = O/E and d(2n) = 4/q.
-- O is odd, and the numerator of q divides O, so it is odd; then 4/q = (4 den q)/(num q)
-- is in lowest terms and its denominator is num q, which is A001803(n).

namespace R08A004735

open OMA.S_oeis_a004735

theorem E_eq (n : ℕ) : ∏ i ∈ Finset.range n, (((2 * n : ℕ) : ℚ) - 2 * (i : ℚ)) =
    2 ^ n * (n.factorial : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ']
    have h : ∏ i ∈ Finset.range n, (((2 * (n + 1) : ℕ) : ℚ) - 2 * ((i + 1 : ℕ) : ℚ)) =
        ∏ i ∈ Finset.range n, (((2 * n : ℕ) : ℚ) - 2 * (i : ℚ)) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      push_cast
      ring
    rw [h, ih, Nat.factorial_succ]
    push_cast
    ring

theorem O_eq (n : ℕ) : ∏ i ∈ Finset.range (n + 1), (((2 * n : ℕ) : ℚ) + 1 - 2 * (i : ℚ)) =
    ((∏ i ∈ Finset.range (n + 1), (2 * i + 1) : ℕ) : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ']
    have h : ∏ i ∈ Finset.range (n + 1), (((2 * (n + 1) : ℕ) : ℚ) + 1 - 2 * ((i + 1 : ℕ) : ℚ)) =
        ∏ i ∈ Finset.range (n + 1), (((2 * n : ℕ) : ℚ) + 1 - 2 * (i : ℚ)) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      push_cast
      ring
    rw [h, ih, Finset.prod_range_succ (fun i => 2 * i + 1) (n + 1),
      Nat.cast_mul (∏ i ∈ Finset.range (n + 1), (2 * i + 1)) (2 * (n + 1) + 1),
      Nat.cast_add_one (2 * (n + 1)), Nat.cast_zero, mul_zero, sub_zero]

theorem O_odd (n : ℕ) : (∏ i ∈ Finset.range (n + 1), (2 * i + 1)) % 2 = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Nat.mul_mod, ih]
    omega

theorem hA (n : ℕ) : (∏ i ∈ Finset.range (n + 1), (2 * i + 1)) * (2 ^ n * n.factorial) =
    (2 * n + 1).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring,
      Nat.factorial_succ (2 * n + 1 + 1), Nat.factorial_succ (2 * n + 1), Nat.factorial_succ n,
      ← ih]
    ring

theorem q_eq (n : ℕ) : ((2 * n + 1) * (Nat.choose (2 * n) n) : ℚ) / 4 ^ n =
    ((∏ i ∈ Finset.range (n + 1), (2 * i + 1) : ℕ) : ℚ) / (2 ^ n * (n.factorial : ℚ)) := by
  have hF : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hB : ((Nat.choose (2 * n) n : ℕ) : ℚ) * (n.factorial : ℚ) * (n.factorial : ℚ) =
      ((2 * n).factorial : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h
    exact_mod_cast h
  have hA' : ((∏ i ∈ Finset.range (n + 1), (2 * i + 1) : ℕ) : ℚ) * (2 ^ n * (n.factorial : ℚ)) =
      ((2 * n + 1).factorial : ℚ) := by
    exact_mod_cast hA n
  have hH : ((2 * n + 1).factorial : ℚ) = (2 * (n : ℚ) + 1) * ((2 * n).factorial : ℚ) := by
    exact_mod_cast Nat.factorial_succ (2 * n)
  have h4 : (4 : ℚ) ^ n = 2 ^ n * 2 ^ n := by
    rw [← mul_pow]
    norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  apply mul_right_cancel₀ hF
  linear_combination (2 * (n : ℚ) + 1) * 2 ^ n * hB -
    ((∏ i ∈ Finset.range (n + 1), (2 * i + 1) : ℕ) : ℚ) * (n.factorial : ℚ) * h4 -
    2 ^ n * hA' - 2 ^ n * hH

theorem den_four_div (O E : ℕ) (hO : O % 2 = 1) (hE : 0 < E) :
    (((4 : ℚ) / ((O : ℚ) / (E : ℚ))).den : ℤ) = ((O : ℚ) / (E : ℚ)).num := by
  obtain ⟨q, hq⟩ : ∃ q : ℚ, q = (O : ℚ) / (E : ℚ) := ⟨_, rfl⟩
  rw [← hq]
  have hOpos : 0 < O := by omega
  have hqpos : 0 < q := by
    rw [hq]
    exact div_pos (by exact_mod_cast hOpos) (by exact_mod_cast hE)
  have hnum : 0 < q.num := Rat.num_pos.mpr hqpos
  have hdvd : q.num ∣ (O : ℤ) := by
    have h := Rat.num_dvd (O : ℤ) (show (E : ℤ) ≠ 0 by exact_mod_cast hE.ne')
    rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast, ← hq] at h
    exact h
  have h2 : ¬ (2 : ℤ) ∣ q.num := by
    intro h2
    have h3 : (2 : ℤ) ∣ (O : ℤ) := dvd_trans h2 hdvd
    omega
  have hm2 : q.num.natAbs % 2 = 1 := by omega
  have h2c : Nat.Coprime 2 q.num.natAbs :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  have h4c : Nat.Coprime 4 q.num.natAbs := Nat.Coprime.pow_left 2 h2c
  have hcop : Nat.Coprime (((4 * q.den : ℕ) : ℤ)).natAbs q.num.natAbs := by
    rw [Int.natAbs_natCast]
    exact Nat.coprime_mul_iff_left.mpr ⟨h4c, q.reduced.symm⟩
  have hq' : (q.num : ℚ) / (q.den : ℚ) = q := Rat.num_div_den q
  have hrepr : (4 : ℚ) / q = (((4 * q.den : ℕ) : ℤ) : ℚ) / ((q.num : ℤ) : ℚ) := by
    calc (4 : ℚ) / q = 4 / ((q.num : ℚ) / (q.den : ℚ)) := by rw [hq']
      _ = (((4 * q.den : ℕ) : ℤ) : ℚ) / ((q.num : ℤ) : ℚ) := by
        rw [div_div_eq_mul_div, Int.cast_natCast, Nat.cast_mul, Nat.cast_ofNat]
  rw [hrepr]
  exact Rat.den_div_eq_of_coprime hnum hcop

end R08A004735

open OMA.S_oeis_a004735 R08A004735 in
theorem OMA.solution : type_of% @OMA.S_oeis_a004735.main := by
  intro n hn
  have hE0 : 0 < 2 ^ n * n.factorial := by positivity
  have hcast : (2 : ℚ) ^ n * (n.factorial : ℚ) = ((2 ^ n * n.factorial : ℕ) : ℚ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hd : d (2 * n) = (4 : ℚ) / (((∏ i ∈ Finset.range (n + 1), (2 * i + 1) : ℕ) : ℚ) /
      (2 ^ n * (n.factorial : ℚ))) := by
    rw [div_div_eq_mul_div, d, if_neg (show ¬ (2 * n % 2 = 1) by omega),
      show (2 * n - 1) / 2 + 1 = n by omega, show 2 * n / 2 + 1 = n + 1 by omega, E_eq n, O_eq n]
  rw [a, A001803, hd, q_eq n, hcast]
  exact den_four_div _ _ (O_odd n) hE0
