import OMAStatements.S_oeis_a228330
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: creative telescoping. With sm(n,k) = (k+1)^(p+2) C(2n+2,n-k)^2 and S(n) = sum_k sm(n,k)
-- = (n+1)^2 a(n), an explicit polynomial certificate Pc gives al(n) sm(n+1,k) - be(n) sm(n,k)
-- = G(n,k+1) - G(n,k) with G = Pc C(2n+3,n+1-k)^2, hence a first-order relation for S; the stated
-- recurrence follows by field_simp and ring. Certificate found by a computer linear solve.

namespace OMA.A228330Proof

open OMA.S_oeis_a228330

/-- Gosper-type certificate polynomial. -/
def Pc (n k : ℚ) : ℚ :=
    (-(n + 1) ^ 2 * (n + 2) ^ 4 * (40 * n ^ 2 + 89 * n + 46)) * k ^ 1 +
    (-2 * (n + 1) ^ 2 * (n + 2) ^ 3 * (40 * n ^ 2 + 89 * n + 46)) * k ^ 2 +
    ((n + 2) ^ 2 * (280 * n ^ 6 + 2175 * n ^ 5 + 6840 * n ^ 4 + 11188 * n ^ 3 + 10078 * n ^ 2 + 4760 * n + 924)) * k ^ 3 +
    (2 * (n + 2) ^ 2 * (280 * n ^ 5 + 1615 * n ^ 4 + 3650 * n ^ 3 + 4057 * n ^ 2 + 2228 * n + 485)) * k ^ 4 +
    (-(n + 2) ^ 2 * (840 * n ^ 6 + 5341 * n ^ 5 + 13548 * n ^ 4 + 17534 * n ^ 3 + 12286 * n ^ 2 + 4512 * n + 704)) * k ^ 5 +
    (-7 * (n + 2) ^ 3 * (8 * n ^ 2 + 5 * n + 2) * (15 * n ^ 3 + 60 * n ^ 2 + 76 * n + 30)) * k ^ 6 +
    (-2 * (n + 2) ^ 2 * (8 * n ^ 3 + 21 * n ^ 2 - 12 * n - 2) * (15 * n ^ 3 + 60 * n ^ 2 + 76 * n + 30)) * k ^ 7 +
    (9 * (n + 2) ^ 2 * (4 * n + 1) * (15 * n ^ 3 + 60 * n ^ 2 + 76 * n + 30)) * k ^ 8 +
    (2 * (n + 2) ^ 2 * (4 * n + 1) * (15 * n ^ 3 + 60 * n ^ 2 + 76 * n + 30)) * k ^ 9

/-- Left coefficient. -/
def al (n : ℚ) : ℚ := (n + 1) ^ 3 * (2 * n + 3) ^ 3 * (15 * n ^ 3 + 15 * n ^ 2 + n - 1)

/-- Right coefficient. -/
def be (n : ℚ) : ℚ :=
  2 * (n + 2) ^ 2 * (2 * n + 3) ^ 2 * (4 * n - 1) * (4 * n + 1) * (15 * n ^ 3 + 60 * n ^ 2 + 76 * n + 30)

/-- Summand. -/
def sm (n k : ℕ) : ℚ := ((k : ℚ) + 1) ^ 6 * (((2 * n + 2).choose (n - k) : ℕ) : ℚ) ^ 2

/-- Sum. -/
def S (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), sm n k

/-- Certificate. -/
def G (n k : ℕ) : ℚ := Pc n k * (((2 * n + 3).choose (n + 1 - k) : ℕ) : ℚ) ^ 2

lemma term (n k : ℕ) (hk : k ≤ n) :
    al n * sm (n + 1) k - be n * sm n k = G n (k + 1) - G n k := by
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  simp only [sm, G]
  rw [show 2 * (k + j + 1) + 2 = 2 * k + 2 * j + 4 by ring,
    show k + j + 1 - k = j + 1 by omega,
    show 2 * (k + j) + 2 = 2 * k + 2 * j + 2 by ring,
    show k + j - k = j by omega,
    show 2 * (k + j) + 3 = 2 * k + 2 * j + 3 by ring,
    show k + j + 1 - (k + 1) = j by omega]
  have h1 := Nat.add_one_mul_choose_eq (2 * k + 2 * j + 2) j
  have h2 := Nat.choose_mul_succ_eq (2 * k + 2 * j + 2) j
  have h3 := Nat.add_one_mul_choose_eq (2 * k + 2 * j + 3) j
  rw [show 2 * k + 2 * j + 2 + 1 - j = 2 * k + j + 3 by omega] at h2
  have e1 : (((2 * k + 2 * j + 3).choose (j + 1) : ℕ) : ℚ) =
      (2 * k + 2 * j + 3) * ((2 * k + 2 * j + 2).choose j : ℕ) / ((j : ℚ) + 1) := by
    rw [eq_div_iff (by positivity)]
    have := congrArg (fun x : ℕ => (x : ℚ)) h1
    push_cast at this
    linarith
  have e2 : (((2 * k + 2 * j + 3).choose j : ℕ) : ℚ) =
      (2 * k + 2 * j + 3) * ((2 * k + 2 * j + 2).choose j : ℕ) / (2 * (k : ℚ) + j + 3) := by
    rw [eq_div_iff (by positivity)]
    have := congrArg (fun x : ℕ => (x : ℚ)) h2
    push_cast at this
    linarith
  have e3 : (((2 * k + 2 * j + 4).choose (j + 1) : ℕ) : ℚ) =
      (2 * k + 2 * j + 4) * ((2 * k + 2 * j + 3).choose j : ℕ) / ((j : ℚ) + 1) := by
    rw [eq_div_iff (by positivity)]
    have := congrArg (fun x : ℕ => (x : ℚ)) h3
    push_cast at this
    linarith
  rw [e3, e1, e2]
  simp only [al, be, Pc]
  push_cast
  field_simp
  ring

lemma key (n : ℕ) : al n * S (n + 1) = be n * S n := by
  have hs : ∑ k ∈ Finset.range (n + 1), (al n * sm (n + 1) k - be n * sm n k) =
      G n (n + 1) - G n 0 := by
    rw [Finset.sum_congr rfl (fun k hk => term n k (by simp at hk; omega))]
    exact Finset.sum_range_sub (G n) (n + 1)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  simp only [S]
  rw [Finset.sum_range_succ, mul_add]
  have hG0 : G n 0 = 0 := by simp [G, Pc]
  have hlast : al n * sm (n + 1) (n + 1) + G n (n + 1) = 0 := by
    simp only [sm, G, Nat.sub_self, Nat.choose_zero_right, al, Pc]
    push_cast
    ring
  linear_combination hs + hlast - hG0

lemma aS (n : ℕ) : a n = S n / ((n : ℚ) + 1) ^ 2 := by
  rw [eq_div_iff (by positivity)]
  simp only [a, S, T, sm, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  field_simp

lemma qne (m : ℕ) : 15 * (m : ℚ) ^ 3 + 15 * (m : ℚ) ^ 2 + (m : ℚ) - 1 ≠ 0 := by
  rcases m with _ | m
  · norm_num
  · apply ne_of_gt
    have : (0 : ℚ) ≤ m := by positivity
    push_cast
    nlinarith [sq_nonneg (m : ℚ), mul_nonneg this (sq_nonneg (m : ℚ))]

lemma qne1 (m : ℕ) : 15 * (m : ℚ) ^ 3 + 60 * (m : ℚ) ^ 2 + 76 * (m : ℚ) + 30 ≠ 0 := by
  positivity

/-- Mathar's conjectured recurrence, for all `n ≥ 2`. -/
theorem mainP : type_of% @OMA.S_oeis_a228330.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 from rfl, show m + 2 - 2 = m from rfl]
  have k0 := key m
  have k1 := key (m + 1)
  rw [show m + 1 + 1 = m + 2 from rfl] at k1
  have q0 := qne m
  have q1 := qne1 m
  simp only [al, be] at k0 k1
  push_cast at k0 k1
  set x : ℚ := (m : ℚ) with hx
  have hx0 : 0 ≤ x := by positivity
  have hal : (x + 1) ^ 3 * (2 * x + 3) ^ 3 * (15 * x ^ 3 + 15 * x ^ 2 + x - 1) *
      ((x + 1 + 1) ^ 3 * (2 * (x + 1) + 3) ^ 3 *
        (15 * (x + 1) ^ 3 + 15 * (x + 1) ^ 2 + (x + 1) - 1)) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by positivity) q0) (mul_ne_zero (by positivity) ?_)
    have e : 15 * (x + 1) ^ 3 + 15 * (x + 1) ^ 2 + (x + 1) - 1 =
        15 * x ^ 3 + 60 * x ^ 2 + 76 * x + 30 := by ring
    rw [e]; exact q1
  have hT : (x + 2) * (2 * (x + 2) + 1) * (3467 * (x + 2) - 4029) * S (m + 2) *
        ((x + 2) ^ 2 * (x + 1) ^ 2) +
      8 * (-36721 * (x + 2) ^ 3 + 109040 * (x + 2) ^ 2 - 137926 * (x + 2) + 69822) * S (m + 1) *
        ((x + 3) ^ 2 * (x + 1) ^ 2) +
      4 * (4 * (x + 2) - 9) * (45706 * (x + 2) - 7907) * (4 * (x + 2) - 7) * S m *
        ((x + 3) ^ 2 * (x + 2) ^ 2) = 0 := by
    apply mul_left_cancel₀ hal
    rw [mul_zero]
    linear_combination
      ((x + 1) ^ 3 * (2 * x + 3) ^ 3 * (15 * x ^ 3 + 15 * x ^ 2 + x - 1) *
        ((x + 2) * (2 * (x + 2) + 1) * (3467 * (x + 2) - 4029) * ((x + 2) ^ 2 * (x + 1) ^ 2))) * k1 +
      ((x + 2) * (2 * (x + 2) + 1) * (3467 * (x + 2) - 4029) * ((x + 2) ^ 2 * (x + 1) ^ 2) *
          (2 * (x + 1 + 2) ^ 2 * (2 * (x + 1) + 3) ^ 2 * (4 * (x + 1) - 1) * (4 * (x + 1) + 1) *
            (15 * (x + 1) ^ 3 + 60 * (x + 1) ^ 2 + 76 * (x + 1) + 30)) +
        8 * (-36721 * (x + 2) ^ 3 + 109040 * (x + 2) ^ 2 - 137926 * (x + 2) + 69822) *
          ((x + 3) ^ 2 * (x + 1) ^ 2) *
          ((x + 1 + 1) ^ 3 * (2 * (x + 1) + 3) ^ 3 *
            (15 * (x + 1) ^ 3 + 15 * (x + 1) ^ 2 + (x + 1) - 1))) * k0
  rw [aS, aS, aS]
  push_cast
  rw [← hx]
  have d0 : (x + 1) ^ 2 ≠ 0 := by positivity
  have d1 : (x + 1 + 1) ^ 2 ≠ 0 := by positivity
  have d2 : (x + 2 + 1) ^ 2 ≠ 0 := by positivity
  have e : (x + 2) * (2 * (x + 2) + 1) * (3467 * (x + 2) - 4029) * (S (m + 2) / (x + 2 + 1) ^ 2) +
      8 * (-36721 * (x + 2) ^ 3 + 109040 * (x + 2) ^ 2 - 137926 * (x + 2) + 69822) *
        (S (m + 1) / (x + 1 + 1) ^ 2) +
      4 * (4 * (x + 2) - 9) * (45706 * (x + 2) - 7907) * (4 * (x + 2) - 7) * (S m / (x + 1) ^ 2) =
      ((x + 2) * (2 * (x + 2) + 1) * (3467 * (x + 2) - 4029) * S (m + 2) *
        ((x + 2) ^ 2 * (x + 1) ^ 2) +
      8 * (-36721 * (x + 2) ^ 3 + 109040 * (x + 2) ^ 2 - 137926 * (x + 2) + 69822) * S (m + 1) *
        ((x + 3) ^ 2 * (x + 1) ^ 2) +
      4 * (4 * (x + 2) - 9) * (45706 * (x + 2) - 7907) * (4 * (x + 2) - 7) * S m *
        ((x + 3) ^ 2 * (x + 2) ^ 2)) / ((x + 1) ^ 2 * (x + 1 + 1) ^ 2 * (x + 2 + 1) ^ 2) := by
    field_simp
    ring
  rw [e, hT, zero_div]


end OMA.A228330Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a228330.main := OMA.A228330Proof.mainP
