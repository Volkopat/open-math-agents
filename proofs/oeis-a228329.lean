import OMAStatements.S_oeis_a228329
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: creative telescoping. With sm(n,k) = (k+1)^4 C(2n+2,n-k)^2 and S(n) = sum_k sm(n,k)
-- = (n+1)^2 a(n), an explicit polynomial certificate Pc gives al(n) sm(n+1,k) - be(n) sm(n,k)
-- = G(n,k+1) - G(n,k), so al(n) S(n+1) = be(n) S(n) (a(n) = (3n+1)/(2n+1) C(4n,2n)); the stated
-- recurrence follows by field_simp and ring. Certificate found by a computer linear solve.

namespace OMA.A228329Proof

open OMA.S_oeis_a228329

/-- Gosper-type certificate polynomial. -/
def Pc (n k : ℚ) : ℚ :=
    ((88) + (372) * n ^ 1 + (642) * n ^ 2 + (579) * n ^ 3 + (288) * n ^ 4 + (75) * n ^ 5 + (8) * n ^ 6) * k ^ 1 +
    ((88) + (328) * n ^ 1 + (478) * n ^ 2 + (340) * n ^ 3 + (118) * n ^ 4 + (16) * n ^ 5) * k ^ 2 +
    ((-480) + (-2260) * n ^ 1 + (-4348) * n ^ 2 + (-4357) * n ^ 3 + (-2396) * n ^ 4 + (-686) * n ^ 5 + (-80) * n ^ 6) * k ^ 3 +
    ((-640) + (-3200) * n ^ 1 + (-6440) * n ^ 2 + (-6620) * n ^ 3 + (-3670) * n ^ 4 + (-1045) * n ^ 5 + (-120) * n ^ 6) * k ^ 4 +
    ((80) + (-244) * n ^ 1 + (-1456) * n ^ 2 + (-2137) * n ^ 3 + (-1384) * n ^ 4 + (-418) * n ^ 5 + (-48) * n ^ 6) * k ^ 5 +
    ((336) + (1036) * n ^ 1 + (1120) * n ^ 2 + (511) * n ^ 3 + (84) * n ^ 4) * k ^ 6 +
    ((96) + (296) * n ^ 1 + (320) * n ^ 2 + (146) * n ^ 3 + (24) * n ^ 4) * k ^ 7

/-- Left coefficient. -/
def al (n : ℚ) : ℚ := (2 * n + 3) ^ 3 * (3 * n + 1) * (n + 1) ^ 3

/-- Right coefficient. -/
def be (n : ℚ) : ℚ := 2 * (3 * n + 4) * (4 * n + 3) * (4 * n + 1) * (n + 2) ^ 2 * (2 * n + 3) ^ 2

/-- Summand. -/
def sm (n k : ℕ) : ℚ := ((k : ℚ) + 1) ^ 4 * (((2 * n + 2).choose (n - k) : ℕ) : ℚ) ^ 2

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

/-- Mathar's conjectured recurrence, for all `n ≥ 2`. -/
theorem mainP : type_of% @OMA.S_oeis_a228329.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 from rfl, show m + 2 - 2 = m from rfl]
  have k0 := key m
  have k1 := key (m + 1)
  have ha0 : al (m : ℚ) ≠ 0 := by simp only [al]; positivity
  have ha1 : al ((m + 1 : ℕ) : ℚ) ≠ 0 := by simp only [al]; positivity
  have s1 : S (m + 1) = be m * S m / al m := by rw [eq_div_iff ha0]; linarith
  have s2 : S (m + 2) = be (m + 1 : ℕ) * S (m + 1) / al (m + 1 : ℕ) := by
    rw [eq_div_iff ha1]; linarith
  rw [aS, aS, aS, s2, s1]
  simp only [al, be]
  push_cast
  field_simp
  ring


end OMA.A228329Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a228329.main := OMA.A228329Proof.mainP
