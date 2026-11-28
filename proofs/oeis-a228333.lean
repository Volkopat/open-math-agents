import OMAStatements.S_oeis_a228333
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: creative telescoping. With sm(n,k) = (k+1)^(p+2) C(2n+2,n-k)^2 and S(n) = sum_k sm(n,k)
-- = (n+1)^2 a(n), an explicit polynomial certificate Pc gives al(n) sm(n+1,k) - be(n) sm(n,k)
-- = G(n,k+1) - G(n,k) with G = Pc C(2n+3,n+1-k)^2, hence a first-order relation for S; the stated
-- recurrence follows by field_simp and ring. Certificate found by a computer linear solve.

namespace OMA.A228333Proof

open OMA.S_oeis_a228333

/-- Gosper-type certificate polynomial. -/
def Pc (n k : ℚ) : ℚ :=
    ((480) * n ^ 0 + (3584) * n ^ 1 + (11600) * n ^ 2 + (21328) * n ^ 3 + (24542) * n ^ 4 + (18340) * n ^ 5 + (8912) * n ^ 6 + (2720) * n ^ 7 + (474) * n ^ 8 + (36) * n ^ 9) * k ^ 2 +
    ((480) * n ^ 0 + (3344) * n ^ 1 + (9928) * n ^ 2 + (16364) * n ^ 3 + (16360) * n ^ 4 + (10160) * n ^ 5 + (3832) * n ^ 6 + (804) * n ^ 7 + (72) * n ^ 8) * k ^ 3 +
    ((-840) * n ^ 0 + (-6792) * n ^ 1 + (-23778) * n ^ 2 + (-47316) * n ^ 3 + (-58932) * n ^ 4 + (-47569) * n ^ 5 + (-24859) * n ^ 6 + (-8110) * n ^ 7 + (-1500) * n ^ 8 + (-120) * n ^ 9) * k ^ 4 +
    ((-960) * n ^ 0 + (-7088) * n ^ 1 + (-22328) * n ^ 2 + (-39196) * n ^ 3 + (-41902) * n ^ 4 + (-27874) * n ^ 5 + (-11252) * n ^ 6 + (-2520) * n ^ 7 + (-240) * n ^ 8) * k ^ 5 +
    ((240) * n ^ 0 + (2708) * n ^ 1 + (11960) * n ^ 2 + (28961) * n ^ 3 + (43158) * n ^ 4 + (41048) * n ^ 5 + (24848) * n ^ 6 + (9224) * n ^ 7 + (1908) * n ^ 8 + (168) * n ^ 9) * k ^ 6 +
    ((480) * n ^ 0 + (4120) * n ^ 1 + (14656) * n ^ 2 + (29054) * n ^ 3 + (35396) * n ^ 4 + (26936) * n ^ 5 + (12400) * n ^ 6 + (3144) * n ^ 7 + (336) * n ^ 8) * k ^ 7 +
    ((120) * n ^ 0 + (436) * n ^ 1 + (658) * n ^ 2 + (-733) * n ^ 3 + (-5962) * n ^ 4 + (-11749) * n ^ 5 + (-11405) * n ^ 6 + (-5982) * n ^ 7 + (-1626) * n ^ 8 + (-180) * n ^ 9) * k ^ 8 +
    ((-880) * n ^ 1 + (-2840) * n ^ 2 + (-4220) * n ^ 3 + (-6530) * n ^ 4 + (-9550) * n ^ 5 + (-8680) * n ^ 6 + (-4380) * n ^ 7 + (-1140) * n ^ 8 + (-120) * n ^ 9) * k ^ 9 +
    ((-660) * n ^ 1 + (-1404) * n ^ 2 + (267) * n ^ 3 + (2038) * n ^ 4 + (862) * n ^ 5 + (-746) * n ^ 6 + (-744) * n ^ 7 + (-228) * n ^ 8 + (-24) * n ^ 9) * k ^ 10 +
    ((-264) * n ^ 1 + (-456) * n ^ 2 + (606) * n ^ 3 + (1824) * n ^ 4 + (1512) * n ^ 5 + (540) * n ^ 6 + (72) * n ^ 7) * k ^ 11 +
    ((-44) * n ^ 1 + (-76) * n ^ 2 + (101) * n ^ 3 + (304) * n ^ 4 + (252) * n ^ 5 + (90) * n ^ 6 + (12) * n ^ 7) * k ^ 12

/-- Left coefficient. -/
def al (n : ℚ) : ℚ := n * (n - 1) * (2 * n + 3) * ((n + 1) ^ 4 * (6 * n ^ 3 + 6 * n ^ 2 - 1))

/-- Right coefficient. -/
def be (n : ℚ) : ℚ := n * (n - 1) * (2 * n + 3) *
  (4 * (n + 2) ^ 2 * (2 * n - 1) * (2 * n + 3) * (6 * n ^ 3 + 24 * n ^ 2 + 30 * n + 11))

/-- Reduced left coefficient. -/
def alA (n : ℚ) : ℚ := (n + 1) ^ 4 * (6 * n ^ 3 + 6 * n ^ 2 - 1)

/-- Reduced right coefficient. -/
def beA (n : ℚ) : ℚ := 4 * (n + 2) ^ 2 * (2 * n - 1) * (2 * n + 3) * (6 * n ^ 3 + 24 * n ^ 2 + 30 * n + 11)

/-- Summand. -/
def sm (n k : ℕ) : ℚ := ((k : ℚ) + 1) ^ 9 * (((2 * n + 2).choose (n - k) : ℕ) : ℚ) ^ 2

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

lemma alA_ne (n : ℕ) : alA (n : ℚ) ≠ 0 := by
  simp only [alA]
  rcases n with _ | n
  · norm_num
  · push_cast
    have : (0 : ℚ) < 6 * ((n : ℚ) + 1) ^ 3 + 6 * ((n : ℚ) + 1) ^ 2 - 1 := by
      have h0 : (0 : ℚ) ≤ n := by positivity
      nlinarith [sq_nonneg ((n : ℚ) + 1), mul_nonneg h0 (sq_nonneg ((n : ℚ) + 1))]
    positivity

lemma key2 (n : ℕ) : alA n * S (n + 1) = beA n * S n := by
  rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with h | h | h
  · subst h
    norm_num [alA, beA, S, sm, Finset.sum_range_succ, Nat.choose]
  · subst h
    norm_num [alA, beA, S, sm, Finset.sum_range_succ, Nat.choose]
  · have k := key n
    have hn : (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) + 3) ≠ 0 := by
      have : (2 : ℚ) ≤ n := by exact_mod_cast h
      have h1 : (0 : ℚ) < (n : ℚ) - 1 := by linarith
      positivity
    simp only [al, be, alA, beA] at k ⊢
    apply mul_left_cancel₀ hn
    linear_combination k

lemma aS (n : ℕ) : a n = S n / ((n : ℚ) + 1) ^ 2 := by
  rw [eq_div_iff (by positivity)]
  simp only [a, S, T, sm, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  field_simp

/-- Mathar's conjectured recurrence, for all `n ≥ 2`. -/
theorem mainP : type_of% @OMA.S_oeis_a228333.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 from rfl, show m + 2 - 2 = m from rfl]
  have k0 := key2 m
  have k1 := key2 (m + 1)
  have ha0 := alA_ne m
  have ha1 := alA_ne (m + 1)
  have s1 : S (m + 1) = beA m * S m / alA m := by rw [eq_div_iff ha0]; linarith
  have s2 : S (m + 2) = beA (m + 1 : ℕ) * S (m + 1) / alA (m + 1 : ℕ) := by
    rw [eq_div_iff ha1]; linarith
  rw [aS, aS, aS, s2, s1]
  field_simp
  simp only [alA, beA]
  push_cast
  ring



end OMA.A228333Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a228333.main := OMA.A228333Proof.mainP
