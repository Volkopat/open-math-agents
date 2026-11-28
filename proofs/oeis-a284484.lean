import OMAStatements.S_oeis_a284484

open OMA.S_oeis_a284484 PowerSeries

namespace OMA.P_a284484

def C0 (i j : ℤ) : Bool := decide (i = 0 ∧ j = 0)
def O0 (i j : ℤ) : Bool := decide ((i = 0 ∧ (j = 1 ∨ j = -1)) ∨ (j = 0 ∧ (i = 1 ∨ i = -1)))
def D0 (i j : ℤ) : Bool := decide ((i = 1 ∨ i = -1) ∧ (j = 1 ∨ j = -1))

def Q : ℕ → ℤ → ℤ → Bool
  | 0, i, j => C0 i j
  | 1, i, j => !(C0 i j || O0 i j)
  | 2, i, j => !(D0 i j)
  | 3, i, j => !(O0 i j)
  | _, i, j => !(D0 i j || C0 i j)

def phase (t : ℕ) : ℕ :=
  if t = 0 then 0 else if t = 1 then 1 else if t = 2 then 2 else if t % 2 = 1 then 3 else 4

def nxt : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | _ => 3

lemma phase_ge3 (t : ℕ) (h : 3 ≤ t) : phase t = if t % 2 = 1 then 3 else 4 := by
  unfold phase
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma phase_succ (t : ℕ) : phase (t + 1) = nxt (phase t) := by
  rcases Nat.lt_or_ge t 3 with h | h
  · interval_cases t <;> rfl
  · rw [phase_ge3 t h, phase_ge3 (t + 1) (by omega)]
    rcases Nat.mod_two_eq_zero_or_one t with h2 | h2
    · have h3 : (t + 1) % 2 = 1 := by omega
      rw [if_pos h3, if_neg (by omega)]; rfl
    · have h3 : ¬ (t + 1) % 2 = 1 := by omega
      rw [if_neg h3, if_pos h2]; rfl

lemma phase_lt (t : ℕ) : phase t < 5 := by
  unfold phase; split_ifs <;> omega

lemma far (a b : ℤ) (h : a ≤ -2 ∨ 2 ≤ a ∨ b ≤ -2 ∨ 2 ≤ b) :
    C0 a b = false ∧ O0 a b = false ∧ D0 a b = false := by
  simp only [C0, O0, D0, decide_eq_false_iff_not]
  omega

lemma stepQ (p : ℕ) (hp : p < 5) (i j : ℤ) :
    Nat.testBit 961 ((Q p i j).toNat + 2 * ((Q p (i + 1) j).toNat + (Q p (i - 1) j).toNat +
      (Q p i (j + 1)).toNat + (Q p i (j - 1)).toNat)) = Q (nxt p) i j := by
  by_cases h : -3 ≤ i ∧ i ≤ 3 ∧ -3 ≤ j ∧ j ≤ 3
  · obtain ⟨h1, h2, h3, h4⟩ := h
    interval_cases p <;> interval_cases i <;> interval_cases j <;> decide
  · obtain ⟨a1, a2, a3⟩ := far i j (by omega)
    obtain ⟨b1, b2, b3⟩ := far (i + 1) j (by omega)
    obtain ⟨c1, c2, c3⟩ := far (i - 1) j (by omega)
    obtain ⟨d1, d2, d3⟩ := far i (j + 1) (by omega)
    obtain ⟨e1, e2, e3⟩ := far i (j - 1) (by omega)
    interval_cases p <;> simp only [Q, nxt, a1, a2, a3, b1, b2, b3, c1, c2, c3, d1, d2, d3, e1, e2, e3] <;> decide

lemma cell_eq (t : ℕ) : ∀ i j : ℤ, cell 961 t i j = Q (phase t) i j := by
  induction t with
  | zero => intro i j; rfl
  | succ t ih =>
    intro i j
    simp only [cell, ih]
    rw [phase_succ, stepQ _ (phase_lt t)]

lemma phase_odd (m : ℕ) : phase (2 * m + 3) = 3 := by
  rw [phase_ge3 _ (by omega), if_pos (by omega)]

lemma phase_even (m : ℕ) : phase (2 * m + 4) = 4 := by
  rw [phase_ge3 _ (by omega), if_neg (by omega)]

lemma geom10 (n : ℕ) : ∑ k ∈ Finset.range n, (10 : ℚ) ^ k = ((10 : ℚ) ^ n - 1) / 9 := by
  rw [geom_sum_eq (by norm_num)]; norm_num

lemma a_split (m : ℕ) (hq : ∀ k : ℤ, 2 ≤ k → Q (phase (m + 2)) k 0 = true) :
    (a (m + 2) : ℚ) = (if Q (phase (m + 2)) 0 0 then (10 : ℚ) ^ (m + 2) else 0) +
      (if Q (phase (m + 2)) 1 0 then (10 : ℚ) ^ (m + 1) else 0) + ((10 : ℚ) ^ (m + 1) - 1) / 9 := by
  unfold a
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hs : ∀ k ∈ Finset.range (m + 1), (if cell 961 (m + 2) ((k + 1 + 1 : ℕ) : ℤ) 0 then (10 : ℤ) ^ (m + 2 - (k + 1 + 1)) else 0) = 10 ^ (m - k) := by
    intro k hk
    rw [cell_eq, if_pos (hq _ (by omega))]
    congr 1; omega
  rw [Finset.sum_congr rfl hs]
  have hr := Finset.sum_range_reflect (fun k => (10 : ℤ) ^ k) (m + 1)
  simp only [show ∀ j, m + 1 - 1 - j = m - j from fun j => by omega] at hr
  rw [hr]

  push_cast
  rw [geom10, cell_eq, cell_eq]
  have e1 : m + 2 - (0 + 1) = m + 1 := by omega
  try simp only [e1, Nat.sub_zero, zero_add, Nat.cast_zero, Nat.cast_one]
  split_ifs <;> push_cast <;> ring

lemma closed (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = (-20 - 81 * (-10 : ℚ) ^ n + 101 * (10 : ℚ) ^ n) / 180 := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m + 3 ∨ n = 2 * m + 4 := ⟨(n - 3) / 2, by omega⟩
  · have hp := phase_odd m
    rw [show 2 * m + 3 = (2 * m + 1) + 2 by ring] at hp ⊢
    rw [a_split _ (by intro k hk; rw [hp]; simp only [Q, (far k 0 (by omega)).2.1]; rfl)]
    rw [hp]
    have : Odd (2 * m + 1 + 2) := ⟨m + 1, by ring⟩
    rw [this.neg_pow]
    simp only [Q, C0, O0]
    norm_num
    rw [pow_succ]; ring
  · have hp := phase_even m
    rw [show 2 * m + 4 = (2 * m + 2) + 2 by ring] at hp ⊢
    rw [a_split _ (by intro k hk; rw [hp]; simp only [Q, (far k 0 (by omega)).1, (far k 0 (by omega)).2.2]; rfl)]
    rw [hp]
    have : Even (2 * m + 2 + 2) := ⟨m + 2, by ring⟩
    rw [this.neg_pow]
    simp only [Q, C0, O0, D0]
    norm_num
    rw [pow_succ]; ring

lemma a0 : a 0 = 1 := by decide +kernel
lemma a1 : a 1 = 0 := by decide +kernel
lemma a2 : a 2 = 111 := by decide +kernel

end OMA.P_a284484

open OMA.P_a284484

theorem OMA.solution : type_of% @OMA.S_oeis_a284484.main := by
  have hrec : ∀ n : ℕ, 6 ≤ n → (a n : ℚ) = a (n - 1) + 100 * a (n - 2) - 100 * a (n - 3) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    rw [closed _ (by omega), closed _ (by omega), closed _ (by omega), closed _ (by omega),
      show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega, show k + 6 - 3 = k + 3 by omega]
    ring
  refine ⟨?_, closed, hrec⟩
  have hp : ((1 - X) * (1 - 10 * X) * (1 + 10 * X) : PowerSeries ℚ) =
      1 - X - C (100 : ℚ) * X ^ 2 + C (100 : ℚ) * X ^ 3 := by
    simp only [map_ofNat]; ring
  have hr : (1 - X + 11 * X ^ 2 + 1000 * X ^ 3 - 11000 * X ^ 4 + 10000 * X ^ 5 : PowerSeries ℚ) =
      1 - X + C (11 : ℚ) * X ^ 2 + C (1000 : ℚ) * X ^ 3 - C (11000 : ℚ) * X ^ 4 + C (10000 : ℚ) * X ^ 5 := by
    simp only [map_ofNat]
  rw [hp, hr]
  ext n
  have e : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X - C (100 : ℚ) * X ^ 2 + C (100 : ℚ) * X ^ 3) =
      PowerSeries.mk (fun n => (a n : ℚ)) - (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        - C (100 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2)
        + C (100 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 3) := by ring
  rw [e]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_X_pow, coeff_X, coeff_one]
  rcases n with _ | _ | _ | _ | _ | _ | n
  · simp [a0]
  · simp [a0, a1]
  · simp [a0, a1, a2]; norm_num
  · simp [a0, a1, a2, closed]; norm_num
  · simp [a0, a1, a2, closed]; norm_num
  · simp [a0, a1, a2, closed]; norm_num
  · simp only [show 1 ≤ n + 6 by omega, show 2 ≤ n + 6 by omega, show 3 ≤ n + 6 by omega, if_true]
    rw [hrec (n + 6) (by omega)]
    simp
    ring_nf

