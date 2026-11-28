import OMAStatements.S_oeis_a027984

-- Problem: A027984: a(n) = Sum_{k=0..n} T(n, k)*T(n, n+k), T given by A027960.
-- Upstream: formal-conjectures statements/oeis-a027984.lean:0 (declaration OMA.S_oeis_a027984.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: T(n, k) = Lucas(k+1) for k <= n, and the right half of the array obeys Pascal's rule
-- T(n+1, n+1+(k+1)) = T(n, n+k+1) + T(n, n+k). For f : ℕ → ℤ let S_f(n) = sum_{k<=n} f(k) T(n, n+k);
-- then S_f(n+1) = S_f(n) + f(0) L(n) + S_g(n) with g(k) = f(k+1). With B = S for f(k) = L(k+1),
-- C for L(k+2) and D for L(k+3) = L(k+2) + L(k+1) this gives B(n+1) = B(n) + L(n) + C(n),
-- C(n+1) = B(n) + 2C(n) + 3L(n), and a = B. Eliminating C: B(n+2) = 3B(n+1) - B(n) + L(n+1) + L(n),
-- and three such lines with the Lucas recurrence give the order 4 recurrence; the g.f. follows by
-- comparing coefficients.

namespace P1A027984

open OMA.S_oeis_a027984

/-- The Lucas numbers 2, 1, 3, 4, 7, ... -/
def Luc : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => Luc (n + 1) + Luc n

theorem Luc_rec' (i j k : ℕ) (hj : j = i + 1) (hk : k = i + 1 + 1) : Luc k = Luc j + Luc i := by
  subst hj
  subst hk
  rfl

theorem T_zero_eq (k : ℕ) : T 0 k = if k = 0 then 1 else 0 := rfl

theorem T_succ (r k : ℕ) : T (r + 1) k =
    if 2 * (r + 1) < k then 0
    else if k = 0 ∨ k = 2 * (r + 1) then 1
    else if k = 1 then 3
    else T r (k - 1) + T r (k - 2) := rfl

theorem T_gen (r k : ℕ) (h1 : ¬ (2 * (r + 1) < k)) (h2 : ¬ (k = 0 ∨ k = 2 * (r + 1)))
    (h3 : ¬ (k = 1)) : T (r + 1) k = T r (k - 1) + T r (k - 2) := by
  rw [T_succ r k, if_neg h1, if_neg h2, if_neg h3]

theorem T_edge (r k : ℕ) (h1 : ¬ (2 * (r + 1) < k)) (h2 : k = 0 ∨ k = 2 * (r + 1)) :
    T (r + 1) k = 1 := by
  rw [T_succ r k, if_neg h1, if_pos h2]

theorem T_one (r : ℕ) : T (r + 1) 1 = 3 := by
  rw [T_succ r 1, if_neg (show ¬ (2 * (r + 1) < 1) by omega),
    if_neg (show ¬ (1 = 0 ∨ 1 = 2 * (r + 1)) by omega), if_pos (show (1 : ℕ) = 1 from rfl)]

theorem T_zero_of_lt (r k : ℕ) (h : 2 * r < k) : T r k = 0 := by
  cases r with
  | zero => rw [T_zero_eq k, if_neg (show ¬ (k = 0) by omega)]
  | succ r => rw [T_succ r k, if_pos h]

theorem T_top (r : ℕ) : T r (2 * r) = 1 := by
  cases r with
  | zero => rfl
  | succ r => exact T_edge r (2 * (r + 1)) (by omega) (Or.inr rfl)

theorem T_lucas : ∀ r k, k ≤ r → T r k = Luc (k + 1) := by
  intro r
  induction r with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by omega
    rfl
  | succ r ih =>
    intro k hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · rcases Nat.lt_or_ge k 1 with hk1 | hk1
      · obtain rfl : k = 0 := by omega
        exact (T_edge r 0 (by omega) (Or.inl rfl)).trans rfl
      · obtain rfl : k = 1 := by omega
        exact (T_one r).trans rfl
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      rw [T_gen r (j + 2) (by omega) (by omega) (by omega), show j + 2 - 1 = j + 1 by omega,
        show j + 2 - 2 = j by omega, ih (j + 1) (by omega), ih j (by omega),
        Luc_rec' (j + 1) (j + 1 + 1) (j + 2 + 1) (by omega) (by omega)]

theorem T_pascal (n k : ℕ) (hk : k ≤ n) :
    T (n + 1) (n + 1 + (k + 1)) = T n (n + (k + 1)) + T n (n + k) := by
  rcases Nat.lt_or_ge k n with h | h
  · rw [T_gen n (n + 1 + (k + 1)) (by omega) (by omega) (by omega),
      show n + 1 + (k + 1) - 1 = n + (k + 1) by omega, show n + 1 + (k + 1) - 2 = n + k by omega]
  · have h1 : T (n + 1) (n + 1 + (k + 1)) = 1 :=
      T_edge n (n + 1 + (k + 1)) (by omega) (Or.inr (by omega))
    have h2 : T n (n + (k + 1)) = 0 := T_zero_of_lt n (n + (k + 1)) (by omega)
    have h3 : T n (n + k) = 1 := by
      rw [show n + k = 2 * n by omega]
      exact T_top n
    omega

/-- S_f(n) = sum_{k <= n} f(k) T(n, n+k). -/
def Sf (f : ℕ → ℤ) (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), f k * (T n (n + k) : ℤ)

theorem Sf_succ (f : ℕ → ℤ) (n : ℕ) :
    Sf f (n + 1) = Sf f n + f 0 * (Luc n : ℤ) + Sf (fun k => f (k + 1)) n := by
  have hP : ∀ k ∈ Finset.range (n + 1), f (k + 1) * (T (n + 1) (n + 1 + (k + 1)) : ℤ) =
      f (k + 1) * (T n (n + (k + 1)) : ℤ) + f (k + 1) * (T n (n + k) : ℤ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [T_pascal n k (by omega), Nat.cast_add, mul_add]
  have h0n : T (n + 1) (n + 1 + 0) = T n (n + 0) + Luc n := by
    rw [T_lucas (n + 1) (n + 1 + 0) (by omega), T_lucas n (n + 0) (by omega)]
    exact Luc_rec' n (n + 0 + 1) (n + 1 + 0 + 1) (by omega) (by omega)
  have h0 : (T (n + 1) (n + 1 + 0) : ℤ) = (T n (n + 0) : ℤ) + (Luc n : ℤ) := by
    exact_mod_cast h0n
  have hz : (T n (n + (n + 1)) : ℤ) = 0 := by
    exact_mod_cast T_zero_of_lt n (n + (n + 1)) (by omega)
  unfold Sf
  rw [Finset.sum_range_succ' (fun k => f k * (T (n + 1) (n + 1 + k) : ℤ)) (n + 1),
    Finset.sum_congr rfl hP, Finset.sum_add_distrib,
    Finset.sum_range_succ' (fun k => f k * (T n (n + k) : ℤ)) n,
    Finset.sum_range_succ (fun k => f (k + 1) * (T n (n + (k + 1)) : ℤ)) n, hz, h0]
  ring

def Bs (n : ℕ) : ℤ := Sf (fun k => (Luc (k + 1) : ℤ)) n

def Cs (n : ℕ) : ℤ := Sf (fun k => (Luc (k + 1 + 1) : ℤ)) n

def Ds (n : ℕ) : ℤ := Sf (fun k => (Luc (k + 1 + 1 + 1) : ℤ)) n

theorem Bs_succ (n : ℕ) : Bs (n + 1) = Bs n + (Luc n : ℤ) + Cs n := by
  have h : Bs (n + 1) = Bs n + (Luc (0 + 1) : ℤ) * (Luc n : ℤ) + Cs n :=
    Sf_succ (fun k => (Luc (k + 1) : ℤ)) n
  have e : (Luc (0 + 1) : ℤ) = 1 := by
    exact_mod_cast (show Luc (0 + 1) = 1 from rfl)
  linear_combination h + (Luc n : ℤ) * e

theorem Cs_succ (n : ℕ) : Cs (n + 1) = Cs n + 3 * (Luc n : ℤ) + Ds n := by
  have h : Cs (n + 1) = Cs n + (Luc (0 + 1 + 1) : ℤ) * (Luc n : ℤ) + Ds n :=
    Sf_succ (fun k => (Luc (k + 1 + 1) : ℤ)) n
  have e : (Luc (0 + 1 + 1) : ℤ) = 3 := by
    exact_mod_cast (show Luc (0 + 1 + 1) = 3 from rfl)
  linear_combination h + (Luc n : ℤ) * e

theorem Ds_eq (n : ℕ) : Ds n = Bs n + Cs n := by
  show ∑ k ∈ Finset.range (n + 1), (Luc (k + 1 + 1 + 1) : ℤ) * (T n (n + k) : ℤ) =
    ∑ k ∈ Finset.range (n + 1), (Luc (k + 1) : ℤ) * (T n (n + k) : ℤ) +
      ∑ k ∈ Finset.range (n + 1), (Luc (k + 1 + 1) : ℤ) * (T n (n + k) : ℤ)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Luc_rec' (k + 1) (k + 1 + 1) (k + 1 + 1 + 1) rfl rfl, Nat.cast_add]
  ring

theorem a_eq (n : ℕ) : a n = Bs n := by
  show ∑ k ∈ Finset.range (n + 1), (T n k : ℤ) * (T n (n + k) : ℤ) =
    ∑ k ∈ Finset.range (n + 1), (Luc (k + 1) : ℤ) * (T n (n + k) : ℤ)
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [T_lucas n k (by omega)]

theorem Bs_rec2 (i j k : ℕ) (hj : j = i + 1) (hk : k = i + 1 + 1) :
    Bs k = 3 * Bs j - Bs i + (Luc j : ℤ) + (Luc i : ℤ) := by
  subst hj
  subst hk
  have e1 := Bs_succ (i + 1)
  have e2 := Cs_succ i
  have e3 := Ds_eq i
  have e0 := Bs_succ i
  linear_combination e1 + e2 + e3 - 2 * e0

theorem Bs_rec4 (m : ℕ) :
    Bs (m + 4) = 4 * Bs (m + 3) - 3 * Bs (m + 2) - 2 * Bs (m + 1) + Bs m := by
  have p0 := Bs_rec2 m (m + 1) (m + 2) (by omega) (by omega)
  have p1 := Bs_rec2 (m + 1) (m + 2) (m + 3) (by omega) (by omega)
  have p2 := Bs_rec2 (m + 2) (m + 3) (m + 4) (by omega) (by omega)
  have l2 : (Luc (m + 2) : ℤ) = (Luc (m + 1) : ℤ) + (Luc m : ℤ) := by
    rw [Luc_rec' m (m + 1) (m + 2) (by omega) (by omega), Nat.cast_add]
  have l3 : (Luc (m + 3) : ℤ) = (Luc (m + 2) : ℤ) + (Luc (m + 1) : ℤ) := by
    rw [Luc_rec' (m + 1) (m + 2) (m + 3) (by omega) (by omega), Nat.cast_add]
  linear_combination p2 - p1 - p0 + l3 + l2

end P1A027984

open OMA.S_oeis_a027984 P1A027984 in
theorem OMA.solution : type_of% @OMA.S_oeis_a027984.main := by
  have hrecZ : ∀ m, a (m + 4) = 4 * a (m + 3) - 3 * a (m + 2) - 2 * a (m + 1) + a m := by
    intro m
    rw [a_eq (m + 4), a_eq (m + 3), a_eq (m + 2), a_eq (m + 1), a_eq m]
    exact Bs_rec4 m
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
    exact hrecZ m
  · have hrec : ∀ m, (a (m + 4) : ℚ) = 4 * (a (m + 3) : ℚ) - 3 * (a (m + 2) : ℚ) -
        2 * (a (m + 1) : ℚ) + (a m : ℚ) := by
      intro m
      exact_mod_cast hrecZ m
    have a0 : (a 0 : ℚ) = 1 := by
      have h : a 0 = 1 := by decide
      exact_mod_cast h
    have a1 : (a 1 : ℚ) = 6 := by
      have h : a 1 = 6 := by decide
      exact_mod_cast h
    have a2 : (a 2 : ℚ) = 20 := by
      have h : a 2 = 20 := by decide
      exact_mod_cast h
    have a3 : (a 3 : ℚ) = 58 := by
      have h : a 3 = 58 := by decide
      exact_mod_cast h
    have e : PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - 3 * PowerSeries.X + PowerSeries.X ^ 2) * (1 - PowerSeries.X - PowerSeries.X ^ 2)) =
        PowerSeries.mk (fun n => (a n : ℚ))
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
          - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
      ring
    have e2 : ((1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 + 2 * PowerSeries.X) :
        PowerSeries ℚ) =
        PowerSeries.X ^ 0 + PowerSeries.X ^ 1 + PowerSeries.X ^ 1
          - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 - PowerSeries.X ^ 3 := by
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 4 with hm | hm
    · interval_cases m
      · norm_num [a0]
      · norm_num [a0, a1]
      · norm_num [a0, a1, a2]
      · norm_num [a0, a1, a2, a3]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      rw [if_pos (show 1 ≤ k + 4 by omega), if_pos (show 2 ≤ k + 4 by omega),
        if_pos (show 3 ≤ k + 4 by omega), if_pos (show 4 ≤ k + 4 by omega),
        if_neg (show ¬ (k + 4 = 0) by omega), if_neg (show ¬ (k + 4 = 1) by omega),
        if_neg (show ¬ (k + 4 = 2) by omega), if_neg (show ¬ (k + 4 = 3) by omega),
        show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
        show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega, hrec k]
      ring
