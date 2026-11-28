import OMAStatements.S_oeis_a243585

-- Problem: A243585: Expansion of x*log'(C(C(x)-1)-1), C(x) = (1-sqrt(1-4*x))/(2*x).
-- Upstream: formal-conjectures statements/oeis-a243585.lean:0 (declaration OMA.S_oeis_a243585.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: put n = m + 2 and u(k) = binomial(2k,k) binomial(2m+4, m+2-k). Then a(m+2), a(m+1), a(m)
-- are sums of u(k) times explicit rational factors (from binomial ratio identities), and with the
-- certificate G(k) = u(k) S(m,k), S a polynomial, every term of the recurrence for k <= m is
-- (up to the factor (2m+4)(2m+3)(2m+2)(2m+1)) G(k+1) - G(k); the sum telescopes, and the two
-- boundary terms k = m+1, m+2 cancel by a polynomial identity.

/-- The certificate polynomial S(x, y). -/
def Sq243585 (x y : ℚ) : ℚ :=
  y * (18 * x ^ 3 + 82 * x ^ 2 + 122 * x + 60) + y ^ 2 * (-9 * x ^ 3 + 62 * x + 62)
    + y ^ 3 * (-24 * x ^ 2 - 50 * x - 24) + y ^ 4 * (-15 * x - 20)

/-- The coefficients of the recurrence at n = m + 2, as functions of x = m. -/
def P0q (x : ℚ) : ℚ := 2 * (x + 2) * (2 * x + 3) * (3 * x + 1)

def P1q (x : ℚ) : ℚ := -123 * (x + 2) ^ 3 + 328 * (x + 2) ^ 2 - 249 * (x + 2) + 60

def P2q (x : ℚ) : ℚ := 50 * (x + 1) * (2 * x + 1) * (3 * x + 4)

/-- The base term binomial(2k,k) * binomial(2m+4, m+2-k). -/
def u243585 (m k : ℕ) : ℚ := (Nat.centralBinom k : ℚ) * ((2 * m + 4).choose (m + 2 - k) : ℚ)

theorem L1_243585 (N j : ℕ) :
    N.choose j * (N + 1) * (N + 2) = (N + 2).choose (j + 1) * (j + 1) * (N + 1 - j) := by
  have e1 : (N + 2) * (N + 1).choose j = (N + 2).choose (j + 1) * (j + 1) :=
    Nat.add_one_mul_choose_eq (N + 1) j
  have e2 : N.choose j * (N + 1) = (N + 1).choose j * (N + 1 - j) := Nat.choose_mul_succ_eq N j
  calc N.choose j * (N + 1) * (N + 2) = (N + 1).choose j * (N + 1 - j) * (N + 2) := by rw [e2]
    _ = (N + 2) * (N + 1).choose j * (N + 1 - j) := by ring
    _ = (N + 2).choose (j + 1) * (j + 1) * (N + 1 - j) := by rw [e1]

theorem iv243585 (m k : ℕ) (hk : k ≤ m) :
    u243585 m (k + 1) * (((k : ℚ) + 1) * ((m : ℚ) + 3 + k)) =
      u243585 m k * (2 * (2 * (k : ℚ) + 1) * ((m : ℚ) + 2 - k)) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
  unfold u243585
  rw [show k + j + 2 - (k + 1) = j + 1 by omega, show k + j + 2 - k = j + 2 by omega]
  have hc : ((k : ℚ) + 1) * ((k + 1).centralBinom : ℚ) =
      2 * (2 * (k : ℚ) + 1) * (k.centralBinom : ℚ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ k
  have hb0 : (2 * (k + j) + 4).choose (j + 1 + 1) * (j + 1 + 1) =
      (2 * (k + j) + 4).choose (j + 1) * (2 * (k + j) + 4 - (j + 1)) := Nat.choose_succ_right_eq _ _
  rw [show j + 1 + 1 = j + 2 by ring, show 2 * (k + j) + 4 - (j + 1) = 2 * k + j + 3 by omega] at hb0
  have hb : (((2 * (k + j) + 4).choose (j + 2) : ℕ) : ℚ) * ((j : ℚ) + 2) =
      (((2 * (k + j) + 4).choose (j + 1) : ℕ) : ℚ) * (2 * (k : ℚ) + j + 3) := by
    exact_mod_cast hb0
  push_cast
  linear_combination (((2 * (k + j) + 4).choose (j + 1) : ℕ) : ℚ) * (2 * (k : ℚ) + j + 3) * hc
    - 2 * (2 * (k : ℚ) + 1) * ((k.centralBinom : ℕ) : ℚ) * hb

theorem t1_243585 (m k : ℕ) (hk : k ≤ m) :
    (((2 * k).choose k : ℕ) : ℚ) * (((2 * (m + 1)).choose (m + 1 - k) : ℕ) : ℚ) *
        ((2 * (m : ℚ) + 4) * (2 * m + 3)) =
      u243585 m k * (((m : ℚ) + 2 - k) * ((m : ℚ) + 2 + k)) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
  unfold u243585
  rw [show k + j + 1 - k = j + 1 by omega, show k + j + 2 - k = j + 2 by omega,
    Nat.centralBinom_eq_two_mul_choose]
  have h0 := L1_243585 (2 * (k + j + 1)) (j + 1)
  rw [show 2 * (k + j + 1) + 2 = 2 * (k + j) + 4 by ring, show j + 1 + 1 = j + 2 by ring,
    show 2 * (k + j + 1) + 1 - (j + 1) = 2 * k + j + 2 by omega] at h0
  have h1 : (((2 * (k + j + 1)).choose (j + 1) : ℕ) : ℚ) * (2 * ((k : ℚ) + j + 1) + 1) *
      (2 * ((k : ℚ) + j) + 4) =
      (((2 * (k + j) + 4).choose (j + 2) : ℕ) : ℚ) * ((j : ℚ) + 2) * (2 * (k : ℚ) + j + 2) := by
    exact_mod_cast h0
  push_cast
  linear_combination (((2 * k).choose k : ℕ) : ℚ) * h1

theorem t0_243585 (m k : ℕ) (hk : k ≤ m) :
    (((2 * k).choose k : ℕ) : ℚ) * (((2 * m).choose (m - k) : ℕ) : ℚ) *
        ((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) =
      u243585 m k * (((m : ℚ) + 1 - k) * ((m : ℚ) + 2 - k) * ((m : ℚ) + 1 + k) * ((m : ℚ) + 2 + k)) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
  unfold u243585
  rw [show k + j - k = j by omega, show k + j + 2 - k = j + 2 by omega,
    Nat.centralBinom_eq_two_mul_choose]
  have h0 := L1_243585 (2 * (k + j)) j
  rw [show 2 * (k + j) + 1 - j = 2 * k + j + 1 by omega] at h0
  have h0' := L1_243585 (2 * (k + j) + 2) (j + 1)
  rw [show 2 * (k + j) + 2 + 2 = 2 * (k + j) + 4 by ring, show j + 1 + 1 = j + 2 by ring,
    show 2 * (k + j) + 2 + 1 - (j + 1) = 2 * k + j + 2 by omega] at h0'
  have h1 : (((2 * (k + j)).choose j : ℕ) : ℚ) * (2 * ((k : ℚ) + j) + 1) * (2 * ((k : ℚ) + j) + 2) =
      (((2 * (k + j) + 2).choose (j + 1) : ℕ) : ℚ) * ((j : ℚ) + 1) * (2 * (k : ℚ) + j + 1) := by
    exact_mod_cast h0
  have h2 : (((2 * (k + j) + 2).choose (j + 1) : ℕ) : ℚ) * (2 * ((k : ℚ) + j) + 2 + 1) *
      (2 * ((k : ℚ) + j) + 4) =
      (((2 * (k + j) + 4).choose (j + 2) : ℕ) : ℚ) * ((j : ℚ) + 2) * (2 * (k : ℚ) + j + 2) := by
    exact_mod_cast h0'
  push_cast
  linear_combination
    (((2 * k).choose k : ℕ) : ℚ) * (2 * ((k : ℚ) + j) + 3) * (2 * ((k : ℚ) + j) + 4) * h1
      + (((2 * k).choose k : ℕ) : ℚ) * ((j : ℚ) + 1) * (2 * (k : ℚ) + j + 1) * h2

open OMA.S_oeis_a243585 in
theorem sum2_243585 (m : ℕ) : (a (m + 2) : ℚ) = ∑ k ∈ Finset.range (m + 3), u243585 m k := by
  simp only [a, Nat.cast_sum, Nat.cast_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold u243585
  rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (m + 2) = 2 * m + 4 by ring]

open OMA.S_oeis_a243585 in
theorem sum1_243585 (m : ℕ) :
    (a (m + 1) : ℚ) * ((2 * (m : ℚ) + 4) * (2 * m + 3)) =
      ∑ k ∈ Finset.range (m + 1), u243585 m k * (((m : ℚ) + 2 - k) * ((m : ℚ) + 2 + k))
        + u243585 m (m + 1) * (2 * (m : ℚ) + 3) := by
  simp only [a, Nat.cast_sum, Nat.cast_mul]
  rw [Finset.sum_range_succ _ (m + 1)]
  have hs : ∑ k ∈ Finset.range (m + 1), (((2 * k).choose k : ℕ) : ℚ) *
        (((2 * (m + 1)).choose (m + 1 - k) : ℕ) : ℚ) * ((2 * (m : ℚ) + 4) * (2 * m + 3)) =
      ∑ k ∈ Finset.range (m + 1), u243585 m k * (((m : ℚ) + 2 - k) * ((m : ℚ) + 2 + k)) :=
    Finset.sum_congr rfl (fun k hk => t1_243585 m k (by have := Finset.mem_range.mp hk; omega))
  rw [← Finset.sum_mul] at hs
  have hb : (((2 * (m + 1)).choose (m + 1) : ℕ) : ℚ) *
        (((2 * (m + 1)).choose (m + 1 - (m + 1)) : ℕ) : ℚ) * ((2 * (m : ℚ) + 4) * (2 * m + 3)) =
      u243585 m (m + 1) * (2 * (m : ℚ) + 3) := by
    unfold u243585
    rw [Nat.sub_self, Nat.choose_zero_right, show m + 2 - (m + 1) = 1 by omega, Nat.choose_one_right,
      Nat.centralBinom_eq_two_mul_choose]
    push_cast
    ring
  linear_combination hs + hb

open OMA.S_oeis_a243585 in
theorem sum0_243585 (m : ℕ) :
    (a m : ℚ) * ((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) =
      ∑ k ∈ Finset.range (m + 1),
        u243585 m k * (((m : ℚ) + 1 - k) * ((m : ℚ) + 2 - k) * ((m : ℚ) + 1 + k) * ((m : ℚ) + 2 + k)) := by
  simp only [a, Nat.cast_sum, Nat.cast_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k hk => t0_243585 m k (by have := Finset.mem_range.mp hk; omega))

theorem hpoly243585 (x y : ℚ) :
    (y + 1) * (x + 3 + y) *
      (2 * (x + 2) * (2 * x + 3) * ((2 * x + 4) * (2 * x + 3) * (2 * x + 2) * (2 * x + 1)) * P0q x
        + 2 * (x + 2) * (2 * x + 3) * ((2 * x + 2) * (2 * x + 1)) * P1q x * ((x + 2 - y) * (x + 2 + y))
        + 2 * (x + 2) * (2 * x + 3) * P2q x *
          ((x + 1 - y) * (x + 2 - y) * (x + 1 + y) * (x + 2 + y))) =
      ((2 * x + 4) * (2 * x + 3) * (2 * x + 2) * (2 * x + 1)) *
        (2 * (2 * y + 1) * (x + 2 - y) * Sq243585 x (y + 1) - (y + 1) * (x + 3 + y) * Sq243585 x y) := by
  unfold P0q P1q P2q Sq243585
  ring

theorem tele243585 (m k : ℕ) (hk : k ≤ m) :
    2 * ((m : ℚ) + 2) * (2 * m + 3) * ((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) *
        P0q m * u243585 m k
      + 2 * ((m : ℚ) + 2) * (2 * m + 3) * ((2 * (m : ℚ) + 2) * (2 * m + 1)) * P1q m *
        (u243585 m k * (((m : ℚ) + 2 - k) * ((m : ℚ) + 2 + k)))
      + 2 * ((m : ℚ) + 2) * (2 * m + 3) * P2q m *
        (u243585 m k * (((m : ℚ) + 1 - k) * ((m : ℚ) + 2 - k) * ((m : ℚ) + 1 + k) * ((m : ℚ) + 2 + k))) =
      ((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) *
        (u243585 m (k + 1) * Sq243585 m ((k + 1 : ℕ) : ℚ) - u243585 m k * Sq243585 m k) := by
  have hiv := iv243585 m k hk
  have hp := hpoly243585 (m : ℚ) (k : ℚ)
  have hne : ((k : ℚ) + 1) * ((m : ℚ) + 3 + k) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  push_cast
  linear_combination (u243585 m k) * hp
    - ((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) * Sq243585 m ((k : ℚ) + 1) * hiv

theorem telesum243585 (m n : ℕ) :
    ∑ k ∈ Finset.range n,
        (u243585 m (k + 1) * Sq243585 m ((k + 1 : ℕ) : ℚ) - u243585 m k * Sq243585 m k) =
      u243585 m n * Sq243585 m n - u243585 m 0 * Sq243585 m 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem hZ243585 (m : ℕ) :
    ((m : ℚ) + 2) * (2 * (m : ℚ) + 4) *
        (((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) * Sq243585 m ((m + 1 : ℕ) : ℚ)
          + 2 * ((m : ℚ) + 2) * (2 * m + 3) *
            ((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) * P0q m
          + 2 * ((m : ℚ) + 2) * (2 * m + 3) * ((2 * (m : ℚ) + 2) * (2 * m + 1)) * P1q m * (2 * m + 3))
      + 2 * (2 * (m : ℚ) + 3) * (2 * ((m : ℚ) + 2) * (2 * m + 3)) *
          ((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) * P0q m = 0 := by
  unfold Sq243585 P0q P1q
  push_cast
  ring

theorem hU243585 (m : ℕ) :
    u243585 m (m + 1) = (Nat.centralBinom (m + 1) : ℚ) * ((2 * m + 4 : ℕ) : ℚ) := by
  unfold u243585
  rw [show m + 2 - (m + 1) = 1 by omega, Nat.choose_one_right]

theorem hUV243585 (m : ℕ) :
    u243585 m (m + 2) * ((m + 2 : ℕ) : ℚ) =
      2 * (2 * ((m + 1 : ℕ) : ℚ) + 1) * (Nat.centralBinom (m + 1) : ℚ) := by
  unfold u243585
  rw [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one]
  have h : (m + 2).centralBinom * (m + 2) = 2 * (2 * (m + 1) + 1) * (m + 1).centralBinom := by
    rw [mul_comm ((m + 2).centralBinom) (m + 2)]
    exact Nat.succ_mul_centralBinom_succ (m + 1)
  exact_mod_cast h

open OMA.S_oeis_a243585 in
theorem core243585 (m : ℕ) :
    P0q m * (a (m + 2) : ℚ) + P1q m * (a (m + 1) : ℚ) + P2q m * (a m : ℚ) = 0 := by
  have h2 := sum2_243585 m
  rw [Finset.sum_range_succ _ (m + 2), Finset.sum_range_succ _ (m + 1)] at h2
  have h1 := sum1_243585 m
  have h0 := sum0_243585 m
  have htel : ∑ k ∈ Finset.range (m + 1),
      (2 * ((m : ℚ) + 2) * (2 * m + 3) * ((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) *
          P0q m * u243585 m k
        + 2 * ((m : ℚ) + 2) * (2 * m + 3) * ((2 * (m : ℚ) + 2) * (2 * m + 1)) * P1q m *
          (u243585 m k * (((m : ℚ) + 2 - k) * ((m : ℚ) + 2 + k)))
        + 2 * ((m : ℚ) + 2) * (2 * m + 3) * P2q m *
          (u243585 m k * (((m : ℚ) + 1 - k) * ((m : ℚ) + 2 - k) * ((m : ℚ) + 1 + k) * ((m : ℚ) + 2 + k)))) =
      ∑ k ∈ Finset.range (m + 1), ((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) *
        (u243585 m (k + 1) * Sq243585 m ((k + 1 : ℕ) : ℚ) - u243585 m k * Sq243585 m k) :=
    Finset.sum_congr rfl (fun k hk => tele243585 m k (by have := Finset.mem_range.mp hk; omega))
  rw [← Finset.mul_sum, telesum243585, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at htel
  have hS0 : Sq243585 (m : ℚ) 0 = 0 := by simp [Sq243585]
  rw [hS0, mul_zero, sub_zero] at htel
  have hU := hU243585 m
  push_cast at hU
  have hUV := hUV243585 m
  push_cast at hUV
  have hZ := hZ243585 m
  have hmain : ((m : ℚ) + 2) * (2 * ((m : ℚ) + 2) * (2 * m + 3)) *
      ((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) *
      (P0q m * (a (m + 2) : ℚ) + P1q m * (a (m + 1) : ℚ) + P2q m * (a m : ℚ)) = 0 := by
    linear_combination
      ((m : ℚ) + 2) * (2 * ((m : ℚ) + 2) * (2 * m + 3)) *
          ((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) * P0q m * h2
      + ((m : ℚ) + 2) * (2 * ((m : ℚ) + 2) * (2 * m + 3)) * ((2 * (m : ℚ) + 2) * (2 * m + 1)) *
          P1q m * h1
      + ((m : ℚ) + 2) * (2 * ((m : ℚ) + 2) * (2 * m + 3)) * P2q m * h0
      + ((m : ℚ) + 2) * htel
      + ((m : ℚ) + 2) *
          (((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) * Sq243585 m ((m + 1 : ℕ) : ℚ)
            + 2 * ((m : ℚ) + 2) * (2 * m + 3) *
              ((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) * P0q m
            + 2 * ((m : ℚ) + 2) * (2 * m + 3) * ((2 * (m : ℚ) + 2) * (2 * m + 1)) * P1q m *
              (2 * m + 3)) * hU
      + 2 * ((m : ℚ) + 2) * (2 * m + 3) *
          ((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) * P0q m * hUV
      + (Nat.centralBinom (m + 1) : ℚ) * hZ
  have hne : ((m : ℚ) + 2) * (2 * ((m : ℚ) + 2) * (2 * m + 3)) *
      ((2 * (m : ℚ) + 4) * (2 * m + 3) * (2 * m + 2) * (2 * m + 1)) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hmain).resolve_left hne

open OMA.S_oeis_a243585 in
theorem OMA.solution : type_of% @OMA.S_oeis_a243585.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have hc := core243585 m
  unfold P0q P1q P2q at hc
  have key : ∀ z : ℤ, (z : ℚ) = 0 → z = 0 := fun z hz => by exact_mod_cast hz
  apply key
  push_cast
  linear_combination hc
